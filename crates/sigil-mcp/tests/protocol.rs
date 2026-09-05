//! Integration tests for the sigil-mcp JSON-RPC protocol.
//!
//! Spawns the compiled `sigil-mcp` binary, drives it over stdio with
//! line-delimited JSON-RPC messages, and asserts the responses round-trip
//! the expected envelope shape — exactly what an MCP-speaking agent
//! harness will see.

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use serde_json::{Value, json};

fn binary() -> &'static str {
    env!("CARGO_BIN_EXE_sigil-mcp")
}

struct Server {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    next_id: u64,
}

impl Server {
    fn spawn() -> Self {
        // The MCP test binary is built solver-off, so `sigil_forge` now fails
        // closed by default (P0: refuse to execute an unverified artifact).
        // These protocol tests exercise forge/check MECHANICS, not the solver
        // policy, so they opt into the documented override.
        // `spawn_strict` (no override) covers the fail-closed gate itself.
        Self::spawn_with_override(true)
    }

    fn spawn_strict() -> Self {
        Self::spawn_with_override(false)
    }

    fn spawn_with_override(allow_unverified: bool) -> Self {
        let mut cmd = Command::new(binary());
        cmd.stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        if allow_unverified {
            cmd.env("SIGIL_ALLOW_UNVERIFIED_CERT", "1");
        } else {
            cmd.env_remove("SIGIL_ALLOW_UNVERIFIED_CERT");
        }
        let mut child = cmd.spawn().expect("failed to spawn sigil-mcp");
        let stdin = child.stdin.take().expect("child stdin");
        let stdout = BufReader::new(child.stdout.take().expect("child stdout"));
        Self {
            child,
            stdin,
            stdout,
            next_id: 1,
        }
    }

    fn request(&mut self, method: &str, params: Value) -> Value {
        let id = self.next_id;
        self.next_id += 1;
        let req = json!({
            "jsonrpc": "2.0",
            "id": id,
            "method": method,
            "params": params,
        });
        let line = serde_json::to_string(&req).unwrap();
        self.stdin
            .write_all(line.as_bytes())
            .expect("write request");
        self.stdin.write_all(b"\n").expect("write newline");
        self.stdin.flush().expect("flush stdin");

        let mut line = String::new();
        self.stdout.read_line(&mut line).expect("read response");
        let response: Value = serde_json::from_str(line.trim())
            .unwrap_or_else(|e| panic!("response was not valid JSON: {e}\nline: {line}"));
        assert_eq!(response["jsonrpc"], "2.0");
        assert_eq!(response["id"], id);
        response
    }

    fn call_tool(&mut self, name: &str, arguments: Value) -> Value {
        let response = self.request(
            "tools/call",
            json!({
                "name": name,
                "arguments": arguments,
            }),
        );
        let text = response["result"]["content"][0]["text"]
            .as_str()
            .unwrap_or_else(|| {
                panic!("tool {name} did not return a text content item: {response}")
            });
        serde_json::from_str(text)
            .unwrap_or_else(|e| panic!("tool {name} text was not valid JSON: {e}\ntext: {text}"))
    }

    fn shutdown(mut self) {
        // Closing stdin causes the server's read loop to exit cleanly.
        drop(self.stdin);
        let _ = self.child.wait();
    }
}

// ── initialize / tools/list ─────────────────────────────────────────────────

#[test]
fn initialize_returns_server_info() {
    let mut server = Server::spawn();
    let response = server.request("initialize", json!({}));
    let result = &response["result"];
    assert_eq!(result["protocolVersion"], "2024-11-05");
    assert_eq!(result["serverInfo"]["name"], "sigil-mcp");
    assert!(result["capabilities"]["tools"].is_object());
    server.shutdown();
}

#[test]
fn tools_list_returns_four_tools() {
    let mut server = Server::spawn();
    let response = server.request("tools/list", json!({}));
    let tools = response["result"]["tools"]
        .as_array()
        .expect("tools must be an array");
    let names: Vec<&str> = tools.iter().map(|t| t["name"].as_str().unwrap()).collect();
    assert_eq!(
        names,
        &[
            "sigil_check",
            "sigil_forge",
            "sigil_lookup_error",
            "sigil_inspect_uses",
        ]
    );
    // Each tool must have an inputSchema with `type: "object"`.
    for tool in tools {
        assert_eq!(tool["inputSchema"]["type"], "object");
    }
    server.shutdown();
}

// ── sigil_check ────────────────────────────────────────────────────────────

#[test]
fn sigil_check_success_envelope() {
    let mut server = Server::spawn();
    let envelope = server.call_tool(
        "sigil_check",
        json!({
            "source": "module sigil; fn boot() -> i64 { return 42; }"
        }),
    );
    // Phase 5a-1.5: schema bumped to v2 with timing field.
    assert_eq!(envelope["schema_version"], 2);
    assert_eq!(envelope["status"], "ok");
    assert_eq!(envelope["command"], "check");
    assert_eq!(envelope["data"]["primary_module"], "sigil");
    assert!(envelope["data"]["wasm_inner_bytes"].as_u64().unwrap() > 0);
    // I17: timing must be present on every compile-tool response.
    let timing = &envelope["data"]["timing"];
    assert!(
        timing["check_ms"].is_number(),
        "expected data.timing.check_ms"
    );
    assert!(timing["modules_seen"].is_number());
    assert!(timing["sigs_built"].is_number());
    assert_eq!(timing["partial"], false);
    server.shutdown();
}

#[test]
fn sigil_check_error_envelope_carries_timing_with_partial_true() {
    let mut server = Server::spawn();
    let envelope = server.call_tool(
        "sigil_check",
        json!({
            "source": "module sigil; fn boot() -> bool { return ready; }"
        }),
    );
    assert_eq!(envelope["status"], "error");
    // I17: error envelopes also carry timing, with partial: true.
    let timing = &envelope["data"]["timing"];
    assert!(timing["check_ms"].is_number());
    assert_eq!(timing["partial"], true);
    server.shutdown();
}

#[test]
fn sigil_inspect_uses_returns_real_use_decls_only() {
    let mut server = Server::spawn();
    let envelope = server.call_tool(
        "sigil_inspect_uses",
        json!({
            "source": r#"
module helpers; pub fn h() -> i64 { return 1; }
module main;
use sigil::helpers;
fn boot() -> i64 { return 0; }
"#,
        }),
    );
    assert_eq!(envelope["status"], "ok");
    assert_eq!(envelope["command"], "inspect_uses");
    let modules = &envelope["data"]["modules"];
    let main_imports = modules["main"].as_array().expect("main entry");
    assert_eq!(main_imports.len(), 1);
    assert_eq!(main_imports[0], "helpers");
    let helpers_imports = modules["helpers"].as_array().expect("helpers entry");
    assert!(helpers_imports.is_empty());
    server.shutdown();
}

#[test]
fn sigil_inspect_uses_ignores_commented_out_use() {
    // The classic regex-fooling case (AP18). A regex matcher would
    // accept this; the parse-aware tool does not.
    let mut server = Server::spawn();
    let envelope = server.call_tool(
        "sigil_inspect_uses",
        json!({
            "source": r#"
module helpers; pub fn h() -> i64 { return 1; }
module main;
// use sigil::helpers;
fn boot() -> i64 { return 0; }
"#,
        }),
    );
    assert_eq!(envelope["status"], "ok");
    let main_imports = envelope["data"]["modules"]["main"]
        .as_array()
        .expect("main entry");
    assert!(
        main_imports.is_empty(),
        "commented-out `use` must NOT appear; got: {main_imports:?}"
    );
    server.shutdown();
}

#[test]
fn sigil_check_error_envelope_carries_structured_diagnostics() {
    let mut server = Server::spawn();
    let envelope = server.call_tool(
        "sigil_check",
        json!({
            "source": "module sigil; fn boot() -> bool { return ready; }"
        }),
    );
    assert_eq!(envelope["status"], "error");
    let diagnostics = envelope["diagnostics"].as_array().unwrap();
    assert!(!diagnostics.is_empty());
    let first = &diagnostics[0];
    assert_eq!(first["code"], "T060");
    assert_eq!(first["title"], "Undefined local");
    assert!(first["hint"].is_string());
    assert_eq!(first["doc_url"], "sigil://errors/T060");
    assert!(first["location"]["line"].as_u64().unwrap() >= 1);
    server.shutdown();
}

// ── sigil_lookup_error ─────────────────────────────────────────────────────

#[test]
fn sigil_lookup_error_returns_registry_entry() {
    let mut server = Server::spawn();
    let envelope = server.call_tool("sigil_lookup_error", json!({ "code": "R001" }));
    assert_eq!(envelope["status"], "ok");
    assert_eq!(envelope["data"]["code"], "R001");
    assert_eq!(
        envelope["data"]["title"],
        "Outer-ring code cannot own capabilities"
    );
    assert!(envelope["data"]["default_hint"].is_string());
    assert_eq!(envelope["data"]["doc_url"], "sigil://errors/R001");
    assert_eq!(envelope["data"]["category"], "Ring");
    server.shutdown();
}

#[test]
fn sigil_lookup_error_unknown_code_returns_error_envelope() {
    let mut server = Server::spawn();
    let envelope = server.call_tool("sigil_lookup_error", json!({ "code": "X999" }));
    assert_eq!(envelope["status"], "error");
    let diagnostics = envelope["diagnostics"].as_array().unwrap();
    assert!(diagnostics[0]["message"].as_str().unwrap().contains("X999"));
    server.shutdown();
}

#[test]
fn sigil_lookup_error_suggests_near_codes_on_miss() {
    let mut server = Server::spawn();
    // `t071` is a case-typo of the real code T071 (edit distance 1); the miss
    // should return a Levenshtein-ranked did-you-mean list, not a dead end.
    let envelope = server.call_tool("sigil_lookup_error", json!({ "code": "t071" }));
    assert_eq!(envelope["status"], "error");
    let suggestions = envelope["did_you_mean"]
        .as_array()
        .expect("did_you_mean array present on a near-miss");
    let codes: Vec<&str> = suggestions.iter().filter_map(|v| v.as_str()).collect();
    assert!(
        codes.contains(&"T071"),
        "expected T071 in did_you_mean, got {codes:?}"
    );
    // A garbage code with no near neighbour returns an empty (but present) list.
    let far = server.call_tool("sigil_lookup_error", json!({ "code": "ZZZZZZ" }));
    assert_eq!(far["status"], "error");
    assert_eq!(
        far["did_you_mean"].as_array().expect("array present").len(),
        0
    );
    server.shutdown();
}

// ── sigil_forge ────────────────────────────────────────────────────────────

#[test]
fn sigil_forge_runs_a_trivial_tool() {
    let mut server = Server::spawn();
    let envelope = server.call_tool(
        "sigil_forge",
        json!({
            "source": "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }",
            "input": ""
        }),
    );
    assert_eq!(envelope["status"], "ok");
    assert_eq!(envelope["command"], "forge");
    assert_eq!(envelope["data"]["output_bytes"], 0);
    assert!(envelope["data"]["wasm_bytes"].as_u64().unwrap() > 0);
    server.shutdown();
}

#[test]
fn sigil_forge_rejects_oversized_source() {
    // P2: the advertised 64 KB tool-source cap must be enforced at the MCP entry
    // point (via compile_tool_with_limits), not merely bounded by the 8 MiB JSON
    // frame. A ~70 KB source must fail with S001 before compilation/execution.
    let mut server = Server::spawn();
    let big = format!(
        "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{ {} return 0; }}",
        "let _x: i64 = 0;\n".repeat(4200) // ~70 KB body, over the 64 KB cap
    );
    let envelope = server.call_tool("sigil_forge", json!({ "source": big, "input": "" }));
    assert_eq!(
        envelope["status"], "error",
        "oversized source must be rejected"
    );
    let diagnostics = envelope["diagnostics"].as_array().unwrap();
    assert!(
        diagnostics.iter().any(|d| d["code"] == "S001"),
        "expected S001 (source exceeds size cap); got {diagnostics:?}"
    );
    server.shutdown();
}

#[test]
fn sigil_check_rejects_oversized_source() {
    // P2 (post-512 review): the 64 KB cap must cover sigil_check too — otherwise
    // an ~8 MiB frame drives the full compile pipeline, side-stepping the cap by
    // choosing `check` instead of `forge`.
    let mut server = Server::spawn();
    let big = format!(
        "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{ {} return 0; }}",
        "let _x: i64 = 0;\n".repeat(4200) // ~70 KB, over the 64 KB cap
    );
    let envelope = server.call_tool("sigil_check", json!({ "source": big }));
    assert_eq!(
        envelope["status"], "error",
        "oversized check must be rejected"
    );
    let diagnostics = envelope["diagnostics"].as_array().unwrap();
    assert!(
        diagnostics.iter().any(|d| d["code"] == "S001"),
        "expected S001 from sigil_check; got {diagnostics:?}"
    );
    server.shutdown();
}

#[test]
fn sigil_inspect_uses_rejects_oversized_source() {
    // P2 (post-512 review): the same cap must cover sigil_inspect_uses (parser).
    let mut server = Server::spawn();
    let big = format!(
        "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{ {} return 0; }}",
        "let _x: i64 = 0;\n".repeat(4200)
    );
    let envelope = server.call_tool("sigil_inspect_uses", json!({ "source": big }));
    assert_eq!(
        envelope["status"], "error",
        "oversized inspect_uses must be rejected"
    );
    let diagnostics = envelope["diagnostics"].as_array().unwrap();
    assert!(
        diagnostics.iter().any(|d| d["code"] == "S001"),
        "expected S001 from sigil_inspect_uses; got {diagnostics:?}"
    );
    server.shutdown();
}

#[test]
fn sigil_forge_fails_closed_when_not_solver_verified() {
    // P0: a solver-off build must REFUSE to execute a tool rather than run code
    // whose Z3 flow-sensitive obligations were never discharged. `spawn_strict`
    // omits the SIGIL_ALLOW_UNVERIFIED_CERT override, so the gate is live. Even
    // a trivial, cleanly-compiling tool must be refused: a solver-off build
    // discharged NO capability-flow / refinement obligations, so
    // `solver_verified` is false regardless of the tool's content — which is
    // exactly why the audit's refinement-violating tool executed unchecked
    // before this gate existed.
    //
    // The gate's contract is a biconditional on the freshly-derived witness
    // (the server gates on `compile_result.solver_verified`), and which side
    // this build is on depends on feature resolution: CI's
    // `--no-default-features` lane is solver-off, but a plain local
    // `cargo test --workspace` unifies the workspace's default features and
    // links a solver-on compiler. Probe the SAME linked sigil-compiler the
    // server binary was built against — one cargo invocation resolves features
    // once for both binaries — and assert the branch the witness selects.
    let source =
        "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }";
    // Named to dodge the ET-M3 fence (`solver_verified_has_exactly_one_assignment_site`):
    // this is a READ of the witness, and the binding must not match the
    // fence's `solver_verified =` needle.
    let solver_verified_witness =
        sigil_compiler::compile_tool_with_limits(source, &sigil_compiler::CompileLimits::default())
            .expect("trivial tool must compile in the witness probe")
            .solver_verified;

    let mut server = Server::spawn_strict();
    let envelope = server.call_tool("sigil_forge", json!({ "source": source, "input": "" }));
    if solver_verified_witness {
        assert_eq!(
            envelope["status"], "ok",
            "a solver-verified build must forge without the override: {envelope}"
        );
    } else {
        assert_eq!(
            envelope["status"], "error",
            "solver-off forge must fail closed"
        );
        let diagnostics = envelope["diagnostics"].as_array().unwrap();
        assert!(
            diagnostics.iter().any(|d| d["code"] == "R817"),
            "expected R817 (not solver-verified); got {diagnostics:?}"
        );
    }
    server.shutdown();
}

#[test]
fn sigil_forge_compile_failure_returns_diagnostics() {
    let mut server = Server::spawn();
    let envelope = server.call_tool(
        "sigil_forge",
        json!({
            "source": "module tool; fn helper() -> i64 { return 0; }"
        }),
    );
    // Tool source is missing `pub fn tool_main` — should fail compile gate (S002).
    assert_eq!(envelope["status"], "error");
    let diagnostics = envelope["diagnostics"].as_array().unwrap();
    assert!(diagnostics.iter().any(|d| d["code"] == "S002"));
    server.shutdown();
}

// ── agent loop pattern ─────────────────────────────────────────────────────
//
// These tests don't exercise a single tool — they exercise the *sequence*
// an LLM agent harness runs over the lifetime of a single forge task:
//   1. agent generates initial source
//   2. agent calls sigil_check → reads diagnostics → fixes → loops
//   3. agent (optionally) calls sigil_lookup_error to learn more about a code
//   4. agent calls sigil_forge to actually execute under user-approved grants
//
// Treat them as worked examples for harness authors.

/// The full happy-path loop: broken source → diagnostic → fix → success → forge.
///
/// This mirrors what an agent harness does for one task: keep iterating on
/// the source using structured feedback until `sigil_check` returns
/// `status: ok`, then call `sigil_forge` to execute.
#[test]
fn agent_loop_iterates_from_diagnostic_to_forge() {
    let mut server = Server::spawn();

    // Attempt 1 — agent emits source with a typo (`ready` is not in scope).
    let attempt1 = server.call_tool(
        "sigil_check",
        json!({
            "source": r#"
                module tool;
                pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
                    return ready;
                }
            "#
        }),
    );
    assert_eq!(attempt1["status"], "error");
    let diag = &attempt1["diagnostics"][0];
    // Diagnostic code drives the agent's fix.
    assert_eq!(diag["code"], "T060");
    assert_eq!(diag["title"], "Undefined local");
    assert!(diag["hint"].is_string());

    // Attempt 2 — agent reads code + hint, replaces `ready` with `0`.
    let attempt2 = server.call_tool(
        "sigil_check",
        json!({
            "source": r#"
                module tool;
                pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
                    return 0;
                }
            "#
        }),
    );
    assert_eq!(attempt2["status"], "ok");

    // Now the agent forges (executes) the verified source.
    let forge = server.call_tool(
        "sigil_forge",
        json!({
            "source": r#"
                module tool;
                pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
                    return 0;
                }
            "#,
            "input": ""
        }),
    );
    assert_eq!(forge["status"], "ok");
    assert_eq!(forge["data"]["output_bytes"], 0);

    server.shutdown();
}

/// Ring-violation loop: agent gets R001, looks up the code for context,
/// rewrites with `grant`-shaped scaffolding (here just dropping ownership),
/// and verifies the rewrite passes.
///
/// This exercises the path an agent takes when it doesn't know what a code
/// means: call `sigil_lookup_error` for the title + canonical fix recipe,
/// then re-emit.
#[test]
fn agent_loop_uses_lookup_error_for_context() {
    let mut server = Server::spawn();

    let attempt1 = server.call_tool(
        "sigil_check",
        json!({
            "source": "#[ring(outer)] module ext; cap type Token {} fn bad(t: Token) -> i64 { return 0; }"
        }),
    );
    assert_eq!(attempt1["status"], "error");
    assert_eq!(attempt1["diagnostics"][0]["code"], "R001");

    // Agent looks up the code to confirm the fix recipe.
    let lookup = server.call_tool("sigil_lookup_error", json!({ "code": "R001" }));
    assert_eq!(lookup["status"], "ok");
    assert!(
        lookup["data"]["default_hint"]
            .as_str()
            .unwrap()
            .contains("inner ring")
    );

    // Agent rewrites: drop the cap parameter entirely (simplest fix that
    // resolves R001 in this synthetic example — a real agent would more
    // likely insert a `grant` block).
    let attempt2 = server.call_tool(
        "sigil_check",
        json!({
            "source": "#[ring(outer)] module ext; cap type Token {} fn bad() -> i64 { return 0; }"
        }),
    );
    assert_eq!(attempt2["status"], "ok");

    server.shutdown();
}

/// Forge with an actual byte-level transformation (reverse a small input)
/// to exercise the full compile + execute + readback path through the MCP.
///
/// Demonstrates that the `output_text` field round-trips through the
/// envelope correctly.
#[test]
fn agent_loop_forge_returns_output_bytes() {
    let mut server = Server::spawn();

    // A tool that copies its input through unchanged. Exercises alloc,
    // load8, store8, and the packed-pointer return ABI.
    let source = r#"
        module tool;
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
            let out_ptr = alloc(input_len);
            let mut i: i64 = 0;
            while i < input_len {
                let b = load8(input_ptr + i);
                store8(out_ptr + i, b);
                i = i + 1;
            }
            return out_ptr * 4294967296 + input_len;
        }
    "#;

    let forge = server.call_tool(
        "sigil_forge",
        json!({
            "source": source,
            "input": "hello"
        }),
    );
    assert_eq!(forge["status"], "ok", "envelope: {forge}");
    assert_eq!(forge["data"]["output_text"], "hello");
    assert_eq!(forge["data"]["output_bytes"], 5);
    assert!(forge["data"]["fuel_consumed"].as_u64().unwrap() > 0);

    server.shutdown();
}

// ── error handling ─────────────────────────────────────────────────────────

#[test]
fn unknown_method_returns_method_not_found() {
    let mut server = Server::spawn();
    let response = server.request("nope/nope", json!({}));
    let error = &response["error"];
    assert_eq!(error["code"], -32601);
    assert!(error["message"].as_str().unwrap().contains("nope/nope"));
    server.shutdown();
}

#[test]
fn malformed_tool_args_return_invalid_params() {
    let mut server = Server::spawn();
    // sigil_check requires `source: string` — pass an integer instead.
    let response = server.request(
        "tools/call",
        json!({
            "name": "sigil_check",
            "arguments": { "source": 42 }
        }),
    );
    let error = &response["error"];
    assert_eq!(error["code"], -32602);
    server.shutdown();
}
