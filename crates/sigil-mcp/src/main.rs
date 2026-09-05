//! Sigil MCP server — exposes the Sigil compiler and runtime as Model
//! Context Protocol tools so an LLM agent can drive the compile-feedback
//! loop directly.
//!
//! Architecture: agent-driven loop. The server exposes verification
//! primitives (compile, execute, look up an error code) and the calling
//! agent harness (Claude Code, Claude Desktop, etc.) runs the iteration
//! loop in its own context. The server has no LLM access of its own.
//!
//! Transport: newline-delimited JSON-RPC 2.0 over stdin/stdout, per the
//! MCP stdio transport. Each request is one line of JSON, response is one
//! line of JSON. No Content-Length headers (that's LSP, not MCP).
//!
//! Tools:
//!   - `sigil_check(source)`           compile-only, returns diagnostics
//!   - `sigil_forge(source, ...)`      compile + ephemeral execution
//!   - `sigil_lookup_error(code)`      registry entry for a code
//!   - `sigil_inspect_uses(source)`    parsed `use` decls per module (for
//!     parse-aware verification — used by the bench's stdlib-usage check)

use std::io::{self, BufRead, Read, Write};
use std::path::PathBuf;
use std::time::Instant;

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sigil_compiler::diagnostics::{Diagnostic, codes, json as diag_json, registry};
use sigil_compiler::source::SourceFile;
use sigil_compiler::{
    CompileLimits, CompileOptions, CompilerContext, compile_named_module_with_context,
    compile_tool_with_limits_and_context, name_resolution, parser,
};
use sigil_runtime::{HttpMethod, IoGrants, NetGrant, execute_ephemeral};

const PROTOCOL_VERSION: &str = "2024-11-05";
const SERVER_NAME: &str = "sigil-mcp";
const SERVER_VERSION: &str = env!("CARGO_PKG_VERSION");

// ── JSON-RPC envelope types ────────────────────────────────────────────────

#[derive(Debug, Deserialize)]
struct Request {
    #[serde(default)]
    id: Option<Value>,
    method: String,
    #[serde(default)]
    params: Value,
}

#[derive(Debug, Serialize)]
struct Response {
    jsonrpc: &'static str,
    id: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    result: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<RpcError>,
}

#[derive(Debug, Serialize)]
struct RpcError {
    code: i32,
    message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    data: Option<Value>,
}

impl RpcError {
    fn method_not_found(method: &str) -> Self {
        Self {
            code: -32601,
            message: format!("method not found: {method}"),
            data: None,
        }
    }

    fn invalid_params(message: impl Into<String>) -> Self {
        Self {
            code: -32602,
            message: message.into(),
            data: None,
        }
    }

    fn internal_error(message: impl Into<String>) -> Self {
        Self {
            code: -32603,
            message: message.into(),
            data: None,
        }
    }
}

fn ok_response(id: Value, result: Value) -> Response {
    Response {
        jsonrpc: "2.0",
        id,
        result: Some(result),
        error: None,
    }
}

fn error_response(id: Value, error: RpcError) -> Response {
    Response {
        jsonrpc: "2.0",
        id,
        result: None,
        error: Some(error),
    }
}

// ── Request framing ─────────────────────────────────────────────────────────

/// Maximum size of a single newline-delimited JSON-RPC frame the server will
/// buffer. `stdin.lines()` grows a `String` for a whole line with no bound, so
/// a huge single-line request could exhaust memory BEFORE any of SIGIL's
/// downstream caps (the 5 MiB source cap) ever apply (finding P2). 8 MiB leaves
/// headroom above the 5 MiB source cap plus JSON/escaping overhead while still
/// bounding worst-case per-request memory.
const MAX_FRAME_BYTES: usize = 8 * 1024 * 1024;

/// One newline-delimited request frame, or a terminal/oversize signal.
enum Frame {
    /// A complete line within the size cap (newline stripped).
    Line(Vec<u8>),
    /// The line exceeded `MAX_FRAME_BYTES`; the stream has been resynchronised
    /// past it so the server can keep handling subsequent requests.
    TooLarge,
    /// End of input.
    Eof,
}

/// Read one newline-delimited frame, enforcing a maximum byte size. Reads at
/// most `max + 1` bytes looking for the newline: if none is found within that
/// window the frame is oversized, so the rest of the line is drained in bounded
/// chunks and `Frame::TooLarge` is returned — memory never grows past the cap.
fn read_frame<R: BufRead>(reader: &mut R, max: usize) -> io::Result<Frame> {
    let mut buf = Vec::new();
    let read = reader
        .by_ref()
        .take(max as u64 + 1)
        .read_until(b'\n', &mut buf)?;
    if read == 0 {
        return Ok(Frame::Eof);
    }
    if buf.last() == Some(&b'\n') {
        buf.pop();
        return Ok(Frame::Line(buf));
    }
    // No trailing newline. If we stopped at or below the cap, we hit EOF — this
    // is a complete final line. If we read the full max+1 bytes without a
    // newline, the line is oversized: drain the remainder so the next read
    // starts clean and never buffer the rest.
    if buf.len() <= max {
        return Ok(Frame::Line(buf));
    }
    drain_to_newline(reader)?;
    Ok(Frame::TooLarge)
}

/// Consume bytes up to and including the next newline (or EOF), in bounded
/// chunks so a pathologically long line cannot balloon memory while draining.
fn drain_to_newline<R: BufRead>(reader: &mut R) -> io::Result<()> {
    let mut scratch = Vec::new();
    loop {
        scratch.clear();
        let read = reader
            .by_ref()
            .take(64 * 1024)
            .read_until(b'\n', &mut scratch)?;
        if read == 0 || scratch.last() == Some(&b'\n') {
            return Ok(());
        }
    }
}

// ── Server entry point ─────────────────────────────────────────────────────

fn main() -> Result<()> {
    // The embedding chooses declarations once. RPC arguments never select a
    // provider profile or turn declarations into execution approval.
    let compiler_context = CompilerContext::default();
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = stdout.lock();
    let mut reader = stdin.lock();

    loop {
        let bytes = match read_frame(&mut reader, MAX_FRAME_BYTES).context("read stdin frame")? {
            Frame::Eof => break,
            Frame::TooLarge => {
                // Reject before parsing — the oversized bytes were never fully
                // buffered. Keep serving subsequent requests.
                let err_response = error_response(
                    Value::Null,
                    RpcError {
                        code: -32700,
                        message: format!(
                            "request frame exceeds maximum size of {MAX_FRAME_BYTES} bytes"
                        ),
                        data: None,
                    },
                );
                write_response(&mut out, &err_response)?;
                continue;
            }
            Frame::Line(bytes) => bytes,
        };
        let line = match String::from_utf8(bytes) {
            Ok(line) => line,
            Err(_) => {
                let err_response = error_response(
                    Value::Null,
                    RpcError {
                        code: -32700,
                        message: "request frame is not valid UTF-8".to_string(),
                        data: None,
                    },
                );
                write_response(&mut out, &err_response)?;
                continue;
            }
        };
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        let request: Request = match serde_json::from_str(trimmed) {
            Ok(req) => req,
            Err(e) => {
                // Malformed JSON — emit a parse error and keep running.
                let err_response = error_response(
                    Value::Null,
                    RpcError {
                        code: -32700,
                        message: format!("parse error: {e}"),
                        data: None,
                    },
                );
                write_response(&mut out, &err_response)?;
                continue;
            }
        };

        // Notifications (no `id`) per JSON-RPC 2.0 do not get a response.
        let id = match request.id.clone() {
            Some(id) => id,
            None => {
                // Acknowledge `notifications/initialized` silently;
                // ignore other notifications.
                continue;
            }
        };

        let response = match dispatch(&request, &compiler_context) {
            Ok(result) => ok_response(id, result),
            Err(err) => error_response(id, err),
        };
        write_response(&mut out, &response)?;
    }

    Ok(())
}

fn write_response(out: &mut impl Write, response: &Response) -> Result<()> {
    let json = serde_json::to_string(response).context("serialize response")?;
    writeln!(out, "{json}").context("write response")?;
    out.flush().context("flush stdout")?;
    Ok(())
}

// ── Method dispatch ────────────────────────────────────────────────────────

fn dispatch(request: &Request, context: &CompilerContext) -> Result<Value, RpcError> {
    match request.method.as_str() {
        "initialize" => Ok(handle_initialize()),
        "tools/list" => Ok(handle_tools_list()),
        "tools/call" => handle_tools_call(&request.params, context),
        // `shutdown` and `exit` are LSP-style; MCP closes the stdio stream
        // when the client disconnects, but we accept the methods for
        // forward compatibility.
        "shutdown" => Ok(Value::Null),
        "exit" => std::process::exit(0),
        other => Err(RpcError::method_not_found(other)),
    }
}

fn handle_initialize() -> Value {
    json!({
        "protocolVersion": PROTOCOL_VERSION,
        "capabilities": {
            "tools": {}
        },
        "serverInfo": {
            "name": SERVER_NAME,
            "version": SERVER_VERSION
        }
    })
}

fn handle_tools_list() -> Value {
    json!({
        "tools": [
            {
                "name": "sigil_check",
                "description": "Compile a Sigil source string and return a structured JSON diagnostic envelope. On success, `status` is `\"ok\"` and `data` carries compilation metadata. On failure, `status` is `\"error\"` and `diagnostics` is a non-empty array of structured errors with stable codes (T060, R001, etc.), titles, and fix recipes. Use this in a loop to drive iterative source generation.",
                "inputSchema": {
                    "type": "object",
                    "properties": {
                        "source": {
                            "type": "string",
                            "description": "Sigil source code, including the `module <name>;` declaration."
                        },
                        "host_profile": {
                            "type": "string",
                            "description": "Optional declared host profile to compile against: `ephemeral` is the built-in host this server runs tools under (its host operations are Internal-occurrence). Absent means the server's context."
                        }
                    },
                    "required": ["source"]
                }
            },
            {
                "name": "sigil_forge",
                "description": "Compile a Sigil tool module and execute it once in an ephemeral Wasmtime sandbox. The source must export `pub fn tool_main(input_ptr: i64, input_len: i64) -> i64`. Returns the same envelope shape as `sigil_check` but on success `data` includes `output_text` / `output_bytes` / `fuel_consumed`. Network and filesystem access require explicit grants — see `grants` below; without them, FFI calls return 403.",
                "inputSchema": {
                    "type": "object",
                    "properties": {
                        "source": {
                            "type": "string",
                            "description": "Sigil tool source. Must export `pub fn tool_main(input_ptr: i64, input_len: i64) -> i64`."
                        },
                        "host_profile": {
                            "type": "string",
                            "description": "Optional declared host profile to compile against: `ephemeral` is the built-in host this server runs tools under (its host operations are Internal-occurrence). Absent means the server's context."
                        },
                        "input": {
                            "type": "string",
                            "description": "Input bytes passed to the tool's input_ptr/input_len. Defaults to empty.",
                            "default": ""
                        },
                        "fuel": {
                            "type": "integer",
                            "description": "Fuel budget for ephemeral execution. Defaults to 100000.",
                            "default": 100000,
                            "minimum": 1
                        },
                        "grants": {
                            "type": "object",
                            "description": "Optional I/O grants. `fs` is a list of canonical filesystem roots the tool may read from; `net` is a list of host patterns (e.g. `\"api.github.com\"` or `\"*.example.com\"`) the tool may HTTP GET/POST.",
                            "properties": {
                                "fs": {
                                    "type": "array",
                                    "items": { "type": "string" }
                                },
                                "net": {
                                    "type": "array",
                                    "items": { "type": "string" }
                                }
                            },
                            "additionalProperties": false
                        }
                    },
                    "required": ["source"]
                }
            },
            {
                "name": "sigil_lookup_error",
                "description": "Look up a Sigil diagnostic code (e.g. `T060`, `R001`, `O001`) in the central registry and return its title, default fix recipe (`hint`), category, and `doc_url`. Use this when a `sigil_check` / `sigil_forge` diagnostic carries a code you want more context on without re-prompting the user.",
                "inputSchema": {
                    "type": "object",
                    "properties": {
                        "code": {
                            "type": "string",
                            "description": "A Sigil diagnostic code, e.g. `T060`."
                        }
                    },
                    "required": ["code"]
                }
            },
            {
                "name": "sigil_inspect_uses",
                "description": "Parse a Sigil source and return the resolved `use` declarations per module. Returns `{ modules: { <module_name>: [<imported_module_name>, ...] } }`. Used by the bench harness's parse-aware stdlib-usage verifier (Phase 5a-1.5 / I10) — comments and string literals containing `use sigil::...;` are correctly excluded; only real declarations parsed by the compiler appear.",
                "inputSchema": {
                    "type": "object",
                    "properties": {
                        "source": {
                            "type": "string",
                            "description": "Sigil source code, including module declarations."
                        }
                    },
                    "required": ["source"]
                }
            }
        ]
    })
}

#[derive(Debug, Deserialize)]
struct ToolsCallParams {
    name: String,
    #[serde(default)]
    arguments: Value,
}

fn handle_tools_call(params: &Value, context: &CompilerContext) -> Result<Value, RpcError> {
    let call: ToolsCallParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("tools/call params: {e}")))?;

    let result_text = match call.name.as_str() {
        "sigil_check" => tool_sigil_check(&call.arguments, context)?,
        "sigil_forge" => tool_sigil_forge(&call.arguments, context)?,
        "sigil_lookup_error" => tool_sigil_lookup_error(&call.arguments)?,
        "sigil_inspect_uses" => tool_sigil_inspect_uses(&call.arguments)?,
        other => {
            return Err(RpcError::invalid_params(format!("unknown tool: {other}")));
        }
    };

    Ok(json!({
        "content": [
            { "type": "text", "text": result_text }
        ],
        "isError": false
    }))
}

// ── Tool implementations ───────────────────────────────────────────────────

#[derive(Debug, Deserialize)]
struct CheckArgs {
    source: String,
    /// Name of the declared host profile to compile against (`"ephemeral"` for the built-in
    /// host); absent means the server's context.
    #[serde(default)]
    host_profile: Option<String>,
}

fn tool_sigil_check(args: &Value, context: &CompilerContext) -> Result<String, RpcError> {
    let args: CheckArgs = serde_json::from_value(args.clone())
        .map_err(|e| RpcError::invalid_params(format!("sigil_check args: {e}")))?;
    let bound_context;
    let context = match args.host_profile.as_deref() {
        Some(name) => {
            bound_context = CompilerContext::with_host_profile(
                sigil_runtime::host_profile_by_name(name).ok_or_else(|| {
                    RpcError::invalid_params(format!(
                        "unknown host_profile `{name}` (the built-in host is `ephemeral`)"
                    ))
                })?,
            );
            &bound_context
        }
        None => context,
    };
    let source_name = "<mcp>".to_owned();

    // P2: apply the same 64 KB tool-source cap `sigil_forge` enforces, before
    // running the full compile pipeline on untrusted source.
    if let Some(env) = oversized_source_error(&args.source, "check", &source_name) {
        return serialize_envelope(env);
    }

    // Phase 5a-1.5: per-call timing on every compile-tool envelope
    // (success AND error). Lets bench operators distinguish "compiler
    // slow" from "LLM slow" without strace.
    let start = Instant::now();

    // Pre-compile, count modules in the source (cheap parse for the metric).
    // On error envelopes we fall back to 0 if the parse itself failed.
    let envelope = match compile_named_module_with_context(
        source_name.clone(),
        args.source.clone(),
        CompileOptions::default(),
        context,
    ) {
        Ok(compilation) => {
            let elapsed_ms = start.elapsed().as_millis() as u64;
            json!({
                "schema_version": 2,
                "status": "ok",
                "command": "check",
                "data": {
                    "source_name": compilation.source_name,
                    "primary_module": compilation.primary_module_name(),
                    "wasm_inner_bytes": compilation.wasm_inner.len(),
                    "wasm_outer_bytes": compilation.wasm_outer.as_ref().map(|w| w.len()),
                    "air_function_count": compilation.air.functions.len(),
                    "fuel_budget": compilation.fuel_budget,
                    "timing": {
                        "check_ms": elapsed_ms,
                        "modules_seen": compilation.module_names.len(),
                        "sigs_built": compilation.air.functions.len(),
                        "partial": false,
                    }
                }
            })
        }
        Err(err) => {
            let elapsed_ms = start.elapsed().as_millis() as u64;
            let source = SourceFile::new(source_name, args.source);
            let diagnostics = diag_json::diagnostics_to_json(err.diagnostics(), &source);
            json!({
                "schema_version": 2,
                "status": "error",
                "command": "check",
                "diagnostics": diagnostics,
                "data": {
                    "timing": {
                        "check_ms": elapsed_ms,
                        "modules_seen": 0,
                        "sigs_built": 0,
                        "partial": true,
                    }
                }
            })
        }
    };
    serialize_envelope(envelope)
}

#[derive(Debug, Deserialize)]
struct ForgeArgs {
    source: String,
    #[serde(default)]
    host_profile: Option<String>,
    #[serde(default)]
    input: String,
    #[serde(default = "default_fuel")]
    fuel: u64,
    #[serde(default)]
    grants: Option<GrantArgs>,
}

#[derive(Debug, Deserialize, Default)]
struct GrantArgs {
    #[serde(default)]
    fs: Vec<String>,
    #[serde(default)]
    fs_write: Vec<String>,
    #[serde(default)]
    net: Vec<String>,
    /// Phase 5a-2: list of time grant kinds (e.g., `["wall"]`).
    /// Without these, `time_now()` returns 403.
    #[serde(default)]
    time: Vec<String>,
    /// Phase 5a-2: list of random grant kinds (e.g., `["secure"]`).
    /// Without these, `random_bytes()` returns 403.
    #[serde(default)]
    random: Vec<String>,
    /// KV read grants as `"NAMESPACE=DIR"` entries. Without one for the
    /// namespace, `kv_get()` returns 403.
    #[serde(default)]
    kv: Vec<String>,
    /// KV write grants as `"NAMESPACE=DIR"` entries — gates `kv_put()`
    /// and `kv_delete()`. Separate from read, mirroring fs/fs_write.
    #[serde(default)]
    kv_write: Vec<String>,
    /// Secret grants as `"NAME=VALUE"` entries — host-held secrets the
    /// `http_post_secret` shim substitutes for `{{secret:NAME}}`.
    #[serde(default)]
    secret: Vec<String>,
}

/// Parse a `"NAMESPACE=DIR"` kv grant descriptor. Returns `None` (grant
/// skipped, fail-closed) when the `=` separator or either half is
/// missing — malformed descriptors deny rather than widen.
fn parse_kv_descriptor(entry: &str) -> Option<(String, PathBuf)> {
    let (ns, dir) = entry.split_once('=')?;
    if ns.is_empty() || dir.is_empty() {
        return None;
    }
    let path = PathBuf::from(dir);
    let canonical = std::fs::canonicalize(&path).unwrap_or(path);
    Some((ns.to_owned(), canonical))
}

fn default_fuel() -> u64 {
    100_000
}

/// Enforce the compiler's tool-source cap (`CompileLimits::default()`, 64 KB)
/// at the MCP boundary (P2). `sigil_forge` gets this for free via
/// `compile_tool_with_limits`, but `sigil_check` / `sigil_inspect_uses` run the
/// same (or heavier) compiler work on the same untrusted `source`, so without
/// the same cap the limit is trivially side-stepped by picking a different
/// verb — an ~8 MiB frame (the only other bound) drives ~128x the intended
/// compiler work. Returns an S001 error envelope value when over the cap, else
/// `None`. The 8 MiB frame cap remains the coarse outer bound; this is the
/// per-tool-source bound the compiler advertises.
fn oversized_source_error(source: &str, command: &str, source_name: &str) -> Option<Value> {
    let max = CompileLimits::default().max_source_bytes;
    if source.len() <= max {
        return None;
    }
    let diag = Diagnostic::error(
        codes::S001,
        format!(
            "source exceeds maximum size ({} bytes > {} byte limit)",
            source.len(),
            max
        ),
        None,
    );
    let sf = SourceFile::new(source_name.to_owned(), source.to_owned());
    let diagnostics = diag_json::diagnostics_to_json(&[diag], &sf);
    Some(json!({
        "schema_version": 2,
        "status": "error",
        "command": command,
        "diagnostics": diagnostics,
        "data": {
            "timing": { "check_ms": 0, "modules_seen": 0, "sigs_built": 0, "partial": true }
        }
    }))
}

/// Whether the MCP forge gate must require solver verification before executing
/// a tool. Default `true` (fail closed); `SIGIL_ALLOW_UNVERIFIED_CERT=1` opts
/// out for dev/CI. Mirrors the sigil-cli helper of the same name so both entry
/// points share one override knob.
fn require_solver_verified_from_env() -> bool {
    !matches!(
        std::env::var("SIGIL_ALLOW_UNVERIFIED_CERT").as_deref(),
        Ok("1")
    )
}

fn tool_sigil_forge(args: &Value, context: &CompilerContext) -> Result<String, RpcError> {
    let args: ForgeArgs = serde_json::from_value(args.clone())
        .map_err(|e| RpcError::invalid_params(format!("sigil_forge args: {e}")))?;
    let bound_context;
    let context = match args.host_profile.as_deref() {
        Some(name) => {
            bound_context = CompilerContext::with_host_profile(
                sigil_runtime::host_profile_by_name(name).ok_or_else(|| {
                    RpcError::invalid_params(format!(
                        "unknown host_profile `{name}` (the built-in host is `ephemeral`)"
                    ))
                })?,
            );
            &bound_context
        }
        None => context,
    };
    let source_name = "<mcp>".to_owned();
    let start = Instant::now();

    // P2: enforce the advertised 64 KB tool-source cap at the MCP entry point.
    // `compile_tool` applies no size limit; the 8 MiB JSON frame cap is a
    // transport bound, NOT the compiler's intended source limit, so the cap has
    // to be wired in explicitly here (S001 on overflow).
    // Compile-time errors short-circuit with a check-shaped envelope.
    let compile_result = match compile_tool_with_limits_and_context(
        &args.source,
        &CompileLimits::default(),
        context,
    ) {
        Ok(result) => result,
        Err(err) => {
            let elapsed_ms = start.elapsed().as_millis() as u64;
            let source = SourceFile::new(source_name, args.source);
            let diagnostics = diag_json::diagnostics_to_json(err.diagnostics(), &source);
            return serialize_envelope(json!({
                "schema_version": 2,
                "status": "error",
                "command": "forge",
                "diagnostics": diagnostics,
                "data": {
                    "timing": {
                        "check_ms": elapsed_ms,
                        "modules_seen": 0,
                        "sigs_built": 0,
                        "partial": true,
                    }
                }
            }));
        }
    };
    let compile_ms = start.elapsed().as_millis() as u64;

    // P0: fail closed BEFORE executing an unverified artifact. A solver-off MCP
    // build (the default) skips the Z3 flow-sensitive obligations, so without
    // this gate `sigil_forge` executes tools whose refinement / capability-flow
    // checks never ran (e.g. a `Range { lo, hi } where lo <= hi` violated by
    // construction). Gate on the freshly-derived `solver_verified` — it comes
    // from this compile, not a caller-supplied cert, so it cannot be forged —
    // default-closed, with the same `SIGIL_ALLOW_UNVERIFIED_CERT=1` override the
    // CLI honors.
    if require_solver_verified_from_env() && !compile_result.solver_verified {
        return serialize_envelope(json!({
            "schema_version": 2,
            "status": "error",
            "command": "forge",
            "diagnostics": [{
                "severity": "error",
                "code": "R817",
                "title": "Artifact not solver-verified (Z3 proofs did not run)",
                "message": "refusing to execute: this sigil-mcp build was compiled without the `solver` feature, so the Z3 flow-sensitive proofs (capability flow, refinement discharge) were skipped, not discharged. The forge gate fails closed rather than run unchecked code. Rebuild sigil-mcp with the `solver` feature, or set SIGIL_ALLOW_UNVERIFIED_CERT=1 to proceed with a structural-only build deliberately.",
                "hint": "Build sigil-mcp with `--features solver` (requires the Z3 system library) for full verification, or set SIGIL_ALLOW_UNVERIFIED_CERT=1 to opt into structural-only checking.",
                "doc_url": "sigil://errors/R817",
                "location": null,
            }],
            "data": {
                "timing": {
                    "check_ms": compile_ms,
                    "modules_seen": 1,
                    "sigs_built": compile_result.function_count,
                    "partial": true,
                }
            }
        }));
    }

    // Build I/O grants from the agent-supplied descriptors.
    let grant_args = args.grants.unwrap_or_default();
    let grants = IoGrants {
        fs: grant_args
            .fs
            .iter()
            .map(|root| {
                let path = PathBuf::from(root);
                let canonical = std::fs::canonicalize(&path).unwrap_or(path);
                sigil_runtime::FsGrant { root: canonical }
            })
            .collect(),
        fs_write: grant_args
            .fs_write
            .iter()
            .map(|root| {
                let path = PathBuf::from(root);
                let canonical = std::fs::canonicalize(&path).unwrap_or(path);
                sigil_runtime::FsWriteGrant { root: canonical }
            })
            .collect(),
        net: grant_args
            .net
            .iter()
            .map(|host_pattern| NetGrant {
                host_pattern: host_pattern.clone(),
                methods: vec![HttpMethod::Get, HttpMethod::Post],
            })
            .collect(),
        kv: grant_args
            .kv
            .iter()
            .filter_map(|entry| {
                parse_kv_descriptor(entry)
                    .map(|(namespace, root)| sigil_runtime::KvGrant { namespace, root })
            })
            .collect(),
        kv_write: grant_args
            .kv_write
            .iter()
            .filter_map(|entry| {
                parse_kv_descriptor(entry)
                    .map(|(namespace, root)| sigil_runtime::KvWriteGrant { namespace, root })
            })
            .collect(),
        time: grant_args
            .time
            .iter()
            .filter_map(|kind| match kind.as_str() {
                "wall" => Some(sigil_runtime::TimeGrant::Wall),
                _ => None,
            })
            .collect(),
        random: grant_args
            .random
            .iter()
            .filter_map(|kind| match kind.as_str() {
                "secure" => Some(sigil_runtime::RandomGrant::Secure),
                _ => None,
            })
            .collect(),
        // Z3 solver capability: fail-closed. The MCP envelope exposes no
        // grant-arg surface for Z3 yet, so MCP-launched tools get no solver
        // access (an empty `z3` denies the `z3_check` shim).
        z3: Vec::new(),
        // Secret grants as `"NAME=VALUE"` — the host-held secrets the
        // `http_post_secret` shim substitutes for `{{secret:NAME}}`.
        secret: grant_args
            .secret
            .iter()
            .filter_map(|entry| {
                let (name, value) = entry.split_once('=')?;
                if name.is_empty() {
                    return None;
                }
                Some(sigil_runtime::SecretGrant {
                    name: name.to_owned(),
                    value: value.as_bytes().to_vec(),
                })
            })
            .collect(),
    };

    // Phase 5a-2 / I26 / R808: cap each grant category. Per-FFI-call
    // grant checks are linear scans; without a cap, an adversarial
    // task spec could degrade FFI latency to O(N).
    if let Err(validation_err) = grants.validate() {
        let elapsed_ms = start.elapsed().as_millis() as u64;
        return serialize_envelope(json!({
            "schema_version": 2,
            "status": "error",
            "command": "forge",
            "diagnostics": [{
                "severity": "error",
                "code": "R808",
                "title": "I/O grant set exceeds per-category cap",
                "message": validation_err.to_string(),
                "hint": "Each grant category (`fs`, `fs_write`, `kv`, `kv_write`, `net`, `time`, `random`) is capped at 256 entries. Reduce the grant list, or split the workload across multiple tool invocations with narrower grant sets.",
                "doc_url": "sigil://errors/R808",
                "location": null,
            }],
            "data": {
                "timing": {
                    "check_ms": compile_ms,
                    "forge_ms": elapsed_ms.saturating_sub(compile_ms),
                    "modules_seen": 1,
                    "sigs_built": compile_result.function_count,
                    "partial": true,
                }
            }
        }));
    }

    let envelope = match execute_ephemeral(
        &compile_result.wasm,
        args.input.as_bytes(),
        args.fuel,
        &grants,
    ) {
        Ok(tool_result) => {
            let total_ms = start.elapsed().as_millis() as u64;
            let output_text = std::str::from_utf8(&tool_result.output)
                .ok()
                .map(str::to_owned);
            json!({
                "schema_version": 2,
                "status": "ok",
                "command": "forge",
                "data": {
                    "wasm_bytes": compile_result.wasm.len(),
                    "function_count": compile_result.function_count,
                    "fuel_budget": args.fuel,
                    "fuel_consumed": tool_result.fuel_consumed,
                    "output_bytes": tool_result.output.len(),
                    "output_text": output_text,
                    "timing": {
                        "check_ms": compile_ms,
                        "forge_ms": total_ms.saturating_sub(compile_ms),
                        "modules_seen": 1,
                        "sigs_built": compile_result.function_count,
                        "partial": false,
                    }
                }
            })
        }
        Err(tool_err) => {
            let total_ms = start.elapsed().as_millis() as u64;
            // Map ToolError to a single diagnostic-shaped entry; mirrors the
            // CLI's tool_error_to_diagnostic helper but we re-implement here
            // to keep sigil-mcp from depending on sigil-cli.
            let (code, title) = match &tool_err {
                sigil_runtime::ToolError::FuelExhausted { .. } => ("R801", "Fuel exhausted"),
                sigil_runtime::ToolError::Trapped { .. } => {
                    ("R803", "Tool trapped during execution")
                }
                sigil_runtime::ToolError::NoEntryPoint => {
                    ("R804", "Tool module missing `tool_main` entry point")
                }
            };
            json!({
                "schema_version": 2,
                "status": "error",
                "command": "forge",
                "diagnostics": [{
                    "severity": "error",
                    "code": code,
                    "title": title,
                    "message": tool_err.to_string(),
                    "doc_url": format!("sigil://errors/{code}"),
                    "location": null,
                }],
                "data": {
                    "timing": {
                        "check_ms": compile_ms,
                        "forge_ms": total_ms.saturating_sub(compile_ms),
                        "modules_seen": 1,
                        "sigs_built": compile_result.function_count,
                        "partial": true,
                    }
                }
            })
        }
    };
    serialize_envelope(envelope)
}

// ── sigil_inspect_uses (Phase 5a-1.5 / I10 enabling) ─────────────────────

#[derive(Debug, Deserialize)]
struct InspectUsesArgs {
    source: String,
}

/// Parse-aware introspection of `use` declarations. Used by the bench
/// harness's stdlib-usage verifier to confirm an LLM-generated source
/// actually imports the stdlib modules its task requires.
///
/// Returns:
/// ```json
/// { "schema_version": 2, "status": "ok", "command": "inspect_uses",
///   "data": { "modules": { "main": ["fs", "json"], "helpers": [] } } }
/// ```
///
/// Comments and string literals containing `use sigil::...;` do NOT
/// appear in the output — only real `use` declarations parsed by the
/// compiler. This is what makes the verifier robust against the
/// regex-fooling cases that AP18 calls out.
fn tool_sigil_inspect_uses(args: &Value) -> Result<String, RpcError> {
    let args: InspectUsesArgs = serde_json::from_value(args.clone())
        .map_err(|e| RpcError::invalid_params(format!("sigil_inspect_uses args: {e}")))?;
    let source_name = "<mcp>".to_owned();
    let start = Instant::now();
    // P2: apply the same 64 KB tool-source cap `sigil_forge` enforces before the
    // parser runs on untrusted source (checked before the moves below).
    if let Some(env) = oversized_source_error(&args.source, "inspect_uses", &source_name) {
        return serialize_envelope(env);
    }
    let source = SourceFile::new(source_name, args.source);

    // We only need the parser pass; no need to run name resolution or
    // type checking. Inspect each module's UseDecl items directly.
    let (ast, parser_diagnostics) = parser::parse(&source);
    if !parser_diagnostics.is_empty() {
        let elapsed_ms = start.elapsed().as_millis() as u64;
        let diagnostics = diag_json::diagnostics_to_json(&parser_diagnostics, &source);
        return serialize_envelope(json!({
            "schema_version": 2,
            "status": "error",
            "command": "inspect_uses",
            "diagnostics": diagnostics,
            "data": {
                "timing": {
                    "check_ms": elapsed_ms,
                    "modules_seen": 0,
                    "sigs_built": 0,
                    "partial": true,
                }
            }
        }));
    }

    // For each module, collect the `use` paths' last-segment as the
    // alias-equals-module-name (per Phase 5a-1 / decision #2: module-only
    // imports). Function-level imports are deferred to v2.
    let mut modules_map = serde_json::Map::new();
    for module in &ast.modules {
        let mut imports: Vec<String> = Vec::new();
        for item in &module.items {
            if let sigil_compiler::ast::Item::UseDecl(decl) = item {
                let segments = &decl.path.segments;
                let target = match segments.as_slice() {
                    [name] => name.clone(),
                    [_crate, name] => name.clone(),
                    // 3+ segments: function-level imports (v2). For
                    // inspect-uses we still surface the module segment,
                    // because that's what the verifier wants to see.
                    [.., name] => name.clone(),
                    [] => continue,
                };
                imports.push(target);
            }
        }
        imports.sort();
        imports.dedup();
        modules_map.insert(
            module.name.clone(),
            Value::Array(imports.into_iter().map(Value::String).collect()),
        );
    }

    // Run name_resolution too so caller can detect malformed sources
    // (e.g. duplicate modules) but don't fail on it — diagnostics surface
    // via sigil_check; this tool is purely advisory.
    let _ = name_resolution::resolve(&ast);

    let elapsed_ms = start.elapsed().as_millis() as u64;
    serialize_envelope(json!({
        "schema_version": 2,
        "status": "ok",
        "command": "inspect_uses",
        "data": {
            "modules": Value::Object(modules_map),
            "timing": {
                "check_ms": elapsed_ms,
                "modules_seen": ast.modules.len(),
                "sigs_built": 0,
                "partial": false,
            }
        }
    }))
}

#[derive(Debug, Deserialize)]
struct LookupArgs {
    code: String,
}

fn tool_sigil_lookup_error(args: &Value) -> Result<String, RpcError> {
    let args: LookupArgs = serde_json::from_value(args.clone())
        .map_err(|e| RpcError::invalid_params(format!("sigil_lookup_error args: {e}")))?;

    // The registry stores codes as `&'static str` keyed by `DiagnosticCode`.
    // Walk the table and match by string for a stable lookup-by-string API.
    let entry = registry::CODES
        .iter()
        .find(|entry| entry.code.as_str() == args.code.as_str());

    let envelope = match entry {
        Some(entry) => json!({
            "schema_version": 1,
            "status": "ok",
            "command": "lookup_error",
            "data": {
                "code": entry.code.as_str(),
                "title": entry.title,
                "default_hint": entry.default_hint,
                "category": format!("{:?}", entry.category),
                "doc_url": format!("sigil://errors/{}", entry.code),
            }
        }),
        None => {
            let suggestions = registry::did_you_mean_codes(&args.code);
            let hint = if suggestions.is_empty() {
                format!(
                    "`{}` is not a known diagnostic code. Enumerate codes via the registry or docs/ERROR-CODES.md.",
                    args.code
                )
            } else {
                format!(
                    "`{}` is not a known diagnostic code. Did you mean: {}?",
                    args.code,
                    suggestions.join(", ")
                )
            };
            json!({
                "schema_version": 1,
                "status": "error",
                "command": "lookup_error",
                "did_you_mean": suggestions,
                "diagnostics": [{
                    "severity": "error",
                    "code": "R800",
                    "title": "Unknown diagnostic code",
                    "message": format!("no registry entry for code `{}`", args.code),
                    "hint": hint,
                    "doc_url": "sigil://errors/R800",
                    "location": null,
                }],
            })
        }
    };
    serialize_envelope(envelope)
}

fn serialize_envelope(envelope: Value) -> Result<String, RpcError> {
    serde_json::to_string_pretty(&envelope)
        .map_err(|e| RpcError::internal_error(format!("envelope serialization: {e}")))
}

#[cfg(test)]
mod compiler_context_tests {
    use super::*;
    use sigil_compiler::compiler_context::HostContractProfile;

    #[test]
    fn check_and_forge_keep_the_bootstrap_context_outside_rpc_arguments() {
        let args = json!({"source": "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }"});
        let ordinary: Value = serde_json::from_str(
            &tool_sigil_check(&args, &CompilerContext::default())
                .expect("ordinary source yields a check envelope"),
        )
        .expect("check envelope is JSON");
        assert_eq!(ordinary["status"], "ok");
        let configured = CompilerContext::with_host_profile(
            HostContractProfile::new("mcp-context".into(), 1, vec![], vec![])
                .expect("an empty named profile is structurally valid"),
        );
        let compiled = compile_named_module_with_context(
            "<mcp>".to_owned(),
            args["source"].as_str().expect("fixture source").to_owned(),
            CompileOptions::default(),
            &configured,
        )
        .expect("production v9 accepts the explicit bootstrap context");
        assert_eq!(compiled.formal_security_report.model_version, 9);

        let call = |name: &str| {
            let request: Request = serde_json::from_value(json!({
                "jsonrpc": "2.0", "id": 1, "method": "tools/call",
                "params": { "name": name, "arguments": args },
            }))
            .expect("the test request matches the RPC shape");
            let result = dispatch(&request, &configured).expect("the tool returns an envelope");
            serde_json::from_str::<Value>(
                result["content"][0]["text"]
                    .as_str()
                    .expect("tool response content carries a text envelope"),
            )
            .expect("tool envelope is JSON")
        };

        assert_eq!(call("sigil_check")["status"], "ok");
        let forge = call("sigil_forge");
        assert_eq!(forge["status"], "error");
        let expected = if cfg!(feature = "solver") {
            "R803"
        } else {
            "R817"
        };
        assert_eq!(forge["diagnostics"][0]["code"], expected);
    }
}

#[cfg(test)]
mod frame_tests {
    use super::{Frame, read_frame};

    #[test]
    fn reads_a_normal_line_within_the_cap() {
        let mut reader: &[u8] = b"hello world\n";
        match read_frame(&mut reader, 1024).unwrap() {
            Frame::Line(bytes) => assert_eq!(bytes, b"hello world"),
            _ => panic!("expected a line"),
        }
    }

    #[test]
    fn reads_multiple_lines_in_sequence() {
        let mut reader: &[u8] = b"one\ntwo\n";
        let a = read_frame(&mut reader, 1024).unwrap();
        let b = read_frame(&mut reader, 1024).unwrap();
        assert!(matches!(a, Frame::Line(ref v) if v == b"one"));
        assert!(matches!(b, Frame::Line(ref v) if v == b"two"));
        assert!(matches!(read_frame(&mut reader, 1024).unwrap(), Frame::Eof));
    }

    #[test]
    fn final_line_without_trailing_newline_is_returned() {
        let mut reader: &[u8] = b"no newline";
        assert!(
            matches!(read_frame(&mut reader, 1024).unwrap(), Frame::Line(ref v) if v == b"no newline")
        );
        assert!(matches!(read_frame(&mut reader, 1024).unwrap(), Frame::Eof));
    }

    #[test]
    fn empty_input_is_eof() {
        let mut reader: &[u8] = b"";
        assert!(matches!(read_frame(&mut reader, 1024).unwrap(), Frame::Eof));
    }

    #[test]
    fn oversized_frame_is_rejected_and_stream_resyncs() {
        // A 2000-byte line under a 100-byte cap, followed by a normal line.
        // The oversized line must be rejected WITHOUT buffering it all, and the
        // next read must cleanly return the following request.
        let mut input = vec![b'A'; 2000];
        input.push(b'\n');
        input.extend_from_slice(b"next\n");
        let mut reader: &[u8] = &input;

        assert!(
            matches!(read_frame(&mut reader, 100).unwrap(), Frame::TooLarge),
            "oversized line must be rejected"
        );
        assert!(
            matches!(read_frame(&mut reader, 100).unwrap(), Frame::Line(ref v) if v == b"next"),
            "stream must resync to the next line after an oversized frame"
        );
    }

    #[test]
    fn line_exactly_at_the_cap_is_accepted() {
        let mut input = vec![b'x'; 100];
        input.push(b'\n');
        let mut reader: &[u8] = &input;
        match read_frame(&mut reader, 100).unwrap() {
            Frame::Line(bytes) => assert_eq!(bytes.len(), 100),
            _ => panic!("a line exactly at the cap must be accepted"),
        }
    }
}
