//! The forge verb: compile a tool, gate it (base cert gate plus the
//! forge-specific bidirectional grant check in `cert_gate`), and
//! execute it ephemerally under explicit I/O grants. Forging a
//! registered template (`--template`) pulls its source from the
//! registry, applies `--patch` substitutions, and writes measured fuel
//! back afterwards (best-effort: a registry error never fails the
//! forge that already succeeded).

use anyhow::bail;
use serde_json::json;
use sigil_compiler::{
    CompileLimits, CompilerContext, compile_tool_with_limits_and_context, source::SourceFile,
};
use sigil_runtime::{
    FsGrant, HttpMethod, IoGrants, KvGrant, KvWriteGrant, NetGrant, RandomGrant, TimeGrant,
    execute_ephemeral,
};

use crate::json_envelope::{
    Envelope, OutputFormat, compile_error_to_json, tool_error_to_diagnostic,
};

use crate::args::{CommandKind, ForgeCommand};

use crate::cert_gate::{
    GateFailure, emit_gate_failure, gate_cert, gate_forge_grants, load_cert_file,
    require_solver_verified_from_env,
};

use crate::check_run::{print_wat, wasm_to_wat_string};

use crate::registry_cmd::open_registry;

// ---------------------------------------------------------------------------
// Forge
// ---------------------------------------------------------------------------

pub(crate) fn run_forge(
    command: &ForgeCommand,
    fmt: OutputFormat,
    context: &CompilerContext,
) -> anyhow::Result<()> {
    let source_text = if let Some(tid) = command.template_id {
        let store = open_registry()?;
        let record = store
            .get(tid)
            .map_err(|e| anyhow::anyhow!("registry error: {e}"))?
            .ok_or_else(|| anyhow::anyhow!("template id {tid} not found in registry"))?;

        let mut src = record.source.clone();
        for (find, replace) in &command.patches {
            src = src.replace(find.as_str(), replace.as_str());
        }
        src
    } else {
        command.source_text.clone()
    };

    let source_name = if command.template_id.is_some() {
        "<template>".to_owned()
    } else {
        command.source_name.clone()
    };

    // P2: enforce the advertised tool-source cap at the CLI entry point.
    // `compile_tool` itself applies no size limit; the 64 KB
    // `CompileLimits::default()` cap (S001) must be wired in here, not left to
    // the caller, so oversized adversarial sources are rejected at the door.
    let compile_result = match compile_tool_with_limits_and_context(
        &source_text,
        &CompileLimits::default(),
        context,
    ) {
        Ok(result) => result,
        Err(err) => {
            if fmt.is_json() {
                let source = SourceFile::new(source_name.clone(), source_text.clone());
                let diags = compile_error_to_json(&err, &source);
                Envelope::error(CommandKind::Forge.json_name(), diags).emit();
                bail!("forge compilation failed");
            }
            let source = SourceFile::new(source_name, source_text);
            let rendered = err
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.render(&source))
                .collect::<Vec<_>>()
                .join("\n\n");
            bail!("{rendered}");
        }
    };

    let label = if let Some(tid) = command.template_id {
        format!("template #{tid}")
    } else {
        format!("`{}`", command.source_name)
    };

    if !fmt.is_json() {
        println!(
            "Compiled tool from {label}. Wasm: {} bytes. Functions: {}. Fuel budget: {}.",
            compile_result.wasm.len(),
            compile_result.function_count,
            command.fuel,
        );
        if command.dump_wat {
            print_wat("tool module", &compile_result.wasm)?;
        }
    }

    // P0: fail closed on an unverified artifact BEFORE executing it, whether or
    // not a `--cert` was supplied. `forge` compiles AND runs the tool; on a
    // solver-off toolchain the Z3 flow-sensitive obligations (capability flow,
    // refinement discharge) are skipped, so without this gate `sigil forge`
    // silently executes a tool whose refinements were never checked (e.g. a
    // `Range { lo, hi } where lo <= hi` violated by construction). We gate on
    // the freshly-DERIVED `compile_result.solver_verified` (unforgeable),
    // default-closed, with the `SIGIL_ALLOW_UNVERIFIED_CERT=1` override.
    if require_solver_verified_from_env() && !compile_result.solver_verified {
        return emit_gate_failure(CommandKind::Forge, fmt, GateFailure::SolverUnverified);
    }

    // Iteration 38 of Spec A + E (axis-5 seventh touch): cert gate
    // on forge. Two-phase check: (a) gate_cert verifies the cert binds
    // to the compiled WASM (same as run-gate, with effects check
    // skipped — None — because forge has its own bidirectional grant
    // check). (b) gate_forge_grants performs the bidirectional check
    // on CLI-controlled effects ({FsIO, NetIO}) against the user's
    // --fs/--net flags.
    //
    // `compile_tool` selects the executable module from `tool_main`'s ring,
    // but certificates bind the complete inner/outer artifact pair. Pass the
    // retained pair here rather than mistaking an outer executable for the
    // inner artifact.
    match &command.cert_path {
        Some(cert_path) => {
            let cert = match load_cert_file(cert_path) {
                Ok(c) => c,
                Err(failure) => return emit_gate_failure(CommandKind::Forge, fmt, failure),
            };
            if let Err(failure) = gate_cert(
                &cert,
                source_text.as_bytes(),
                &compile_result.wasm_inner,
                compile_result.wasm_outer.as_deref(),
                None,
                require_solver_verified_from_env(),
                compile_result.solver_verified,
                &compile_result.formal_security_report,
            ) {
                return emit_gate_failure(CommandKind::Forge, fmt, failure);
            }
            if let Err(failure) = gate_forge_grants(
                &cert.effects_required,
                &command.fs_roots,
                &command.net_hosts,
            ) {
                return emit_gate_failure(CommandKind::Forge, fmt, failure);
            }
        }
        None => {
            if !fmt.is_json() {
                eprintln!(
                    "note: running without certificate gate; \
                     pass --cert <path> to enable verification"
                );
            }
        }
    }

    let grants = IoGrants {
        fs: command
            .fs_roots
            .iter()
            .map(|root| {
                let canonical = std::fs::canonicalize(root).unwrap_or_else(|_| root.clone());
                FsGrant { root: canonical }
            })
            .collect(),
        net: command
            .net_hosts
            .iter()
            .map(|host_pattern| NetGrant {
                host_pattern: host_pattern.clone(),
                methods: vec![HttpMethod::Get, HttpMethod::Post],
            })
            .collect(),
        kv: command
            .kv_grants
            .iter()
            .map(|(ns, dir)| {
                let canonical = std::fs::canonicalize(dir).unwrap_or_else(|_| dir.clone());
                KvGrant {
                    namespace: ns.clone(),
                    root: canonical,
                }
            })
            .collect(),
        kv_write: command
            .kv_write_grants
            .iter()
            .map(|(ns, dir)| {
                let canonical = std::fs::canonicalize(dir).unwrap_or_else(|_| dir.clone());
                KvWriteGrant {
                    namespace: ns.clone(),
                    root: canonical,
                }
            })
            .collect(),
        // Slot-registry addendum: deterministic Clock + Random grants.
        // Wall / Secure remain reachable via absence of the corresponding
        // flag (caller doesn't pass --frozen-time / --random-seed).
        time: command
            .frozen_time_ms
            .map_or_else(Vec::new, |ms| vec![TimeGrant::Frozen(ms)]),
        random: command
            .random_seed
            .map_or_else(Vec::new, |seed| vec![RandomGrant::Seeded(seed)]),
        // Phase 5a-2: CLI doesn't expose fs_write grants yet.
        // Tools that need them must use sigil-mcp (bench harness) or
        // direct execute_ephemeral calls with explicit grants.
        ..Default::default()
    };

    // Input bytes: prefer `--input-hex` (non-empty), else fall back to
    // `--input` text. Empty `--input-hex` value behaves identically to
    // absence (preserves the empty-input-equivalence invariant).
    let input_bytes: &[u8] = command
        .input_bytes_override
        .as_deref()
        .filter(|b| !b.is_empty())
        .unwrap_or(command.input.as_bytes());
    match execute_ephemeral(&compile_result.wasm, input_bytes, command.fuel, &grants) {
        Ok(result) => {
            if fmt.is_json() {
                emit_forge_success(command, &compile_result, &result, &label)?;
            } else {
                println!(
                    "Tool completed. Output: {} bytes. Fuel consumed: {}.",
                    result.output.len(),
                    result.fuel_consumed,
                );
                if !result.output.is_empty() {
                    match std::str::from_utf8(&result.output) {
                        Ok(text) => println!("Output text: {text}"),
                        Err(_) => println!("Output (hex): {:02x?}", result.output),
                    }
                }
            }

            if let Some(tid) = command.template_id
                && let Ok(store) = open_registry()
            {
                let _ = store.update_fuel(tid, result.fuel_consumed);
            }
        }
        Err(err) => {
            if fmt.is_json() {
                let diag = tool_error_to_diagnostic(&err);
                Envelope::error(CommandKind::Forge.json_name(), vec![diag]).emit();
                bail!("tool execution failed");
            }
            bail!("Tool execution failed: {err}");
        }
    }

    Ok(())
}

fn emit_forge_success(
    command: &ForgeCommand,
    compile_result: &sigil_compiler::CompileResult,
    tool_result: &sigil_runtime::ToolResult,
    label: &str,
) -> anyhow::Result<()> {
    let output_text = std::str::from_utf8(&tool_result.output)
        .ok()
        .map(str::to_owned);
    let output_hex: String = {
        use std::fmt::Write;
        let mut s = String::with_capacity(tool_result.output.len() * 2);
        for byte in &tool_result.output {
            let _ = write!(&mut s, "{byte:02x}");
        }
        s
    };
    let mut data = json!({
        "source_label": label,
        "wasm_bytes": compile_result.wasm.len(),
        "function_count": compile_result.function_count,
        "fuel_budget": command.fuel,
        "fuel_consumed": tool_result.fuel_consumed,
        "output_bytes": tool_result.output.len(),
        "output_text": output_text,
        "output_hex": output_hex,
        "template_id": command.template_id,
    });
    if command.dump_wat {
        let wat = wasm_to_wat_string(&compile_result.wasm)?;
        data["wat"] = json!({ "tool": wat });
    }
    Envelope::ok(CommandKind::Forge.json_name(), data).emit();
    Ok(())
}
