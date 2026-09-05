//! The check/run verb family: compile the input, emit diagnostics or
//! the success envelope, and for `run` gate the artifact through
//! `cert_gate`, execute it on the runtime, or serve it (`--serve`).
//! Also owns the wat rendering helpers `forge` borrows.

use std::fs;

use anyhow::{Context, bail};
use serde_json::json;
use sigil_compiler::{
    Compilation, CompileOptions, CompilerContext, compile_named_module_with_context,
    source::SourceFile,
};
use sigil_runtime::RuntimeHost;

use crate::json_envelope::{
    Envelope, OutputFormat, compile_error_to_json, runtime_error_to_diagnostic,
};

use crate::args::{CommandKind, CompileCommand};

use crate::cert_gate::{
    GateFailure, certificate_from_compilation, emit_gate_failure, gate_cert, load_cert_file,
    require_solver_verified_from_env,
};

use crate::translate::translate_command_source;

pub(crate) fn run_check_or_run(
    command: &CompileCommand,
    kind: CommandKind,
    fmt: OutputFormat,
    context: &CompilerContext,
) -> anyhow::Result<()> {
    if let Some(package_root) = &command.package_root {
        if kind != CommandKind::Check {
            bail!("--package is supported only by `sigil check`");
        }
        return run_package_check(command, package_root, fmt, context);
    }
    // Foreign-frontend: when `--from <lang>` is set, translate the source DSL
    // to SIGIL first, then compile the emitted SIGIL through the normal
    // pipeline. The translator is untrusted; the compiler is the verifier.
    let translated;
    let command = if let Some(lang) = command.from.clone() {
        translated = translate_command_source(command, &lang, kind, fmt)?;
        &translated
    } else {
        command
    };

    // Wall 5 Step 1 / commit #3: dispatch to project mode when more than
    // one source file was passed. Single-file invocations stay on the
    // legacy compile_named_module path (byte-equal wasm regression).
    let multi_file = !command.source_files.is_empty();

    // Build the SourceFile(s) once so we can render diagnostics against
    // them later. For single-file we render against the lone source;
    // for multi-file we render the first file we can locate by
    // source_name and emit a fallback for non-attributed diagnostics.
    let primary_source = if multi_file {
        // Use the first project-mode file as fallback render target;
        // diagnostics that carry source_name will resolve correctly via
        // render_in_project. The SourceId refactor (commit #5) makes
        // every diagnostic file-precise.
        let (name, text) = &command.source_files[0];
        SourceFile::new(name.clone(), text.clone())
    } else {
        SourceFile::new(command.source_name.clone(), command.source_text.clone())
    };
    let project_sources: Vec<SourceFile> = command
        .source_files
        .iter()
        .map(|(n, t)| SourceFile::new(n.clone(), t.clone()))
        .collect();

    let options = CompileOptions {
        build_deadline: command.build_deadline,
    };

    let compilation_result = if multi_file {
        sigil_compiler::compile_project_with_context(
            project_sources.clone(),
            command.entry_module.as_deref(),
            options,
            context,
        )
    } else {
        compile_named_module_with_context(
            command.source_name.clone(),
            command.source_text.clone(),
            options,
            context,
        )
    };

    let compilation = match compilation_result {
        Ok(compilation) => compilation,
        Err(err) => {
            if fmt.is_json() {
                let diags = compile_error_to_json(&err, &primary_source);
                Envelope::error(kind.json_name(), diags).emit();
                bail!("compilation failed");
            }
            // Wall 5 Step 1 + SourceId follow-up: CompileError::render
            // resolves every span's source_id against the attached
            // SourceMap. ALL diagnostic codes (T-, R-, N-, E- as well
            // as M-prefix) render against the right file in multi-file
            // mode. Falls back to primary_source for SYNTHETIC spans
            // or when no SourceMap is attached (legacy paths).
            let rendered = err.render(&primary_source);
            let _ = &project_sources; // kept available for JSON emitter
            bail!("{rendered}");
        }
    };
    // Multi-file verify-cert (`sigil run --cert` over a project) is a
    // future surface beyond Wall 5 Step 1 — the existing single-file
    // cert path reads command.source_text directly, which is the
    // "<project>" sentinel in multi-file mode. Out-of-scope per MC-S1-C.
    let _ = primary_source;

    if kind == CommandKind::Run {
        // P0: fail closed on an unverified artifact BEFORE executing it, whether
        // or not a `--cert` was supplied — the same unconditional gate `forge`
        // applies. `sigil run` instantiates and runs the guest actor; on a
        // solver-off toolchain the Z3 flow-sensitive obligations (capability
        // flow, refinement discharge) were skipped, not discharged. Previously
        // the solver gate was reachable ONLY inside the `--cert` arm, so
        // `sigil run prog.sigil` with no cert executed unchecked code — the gate
        // was bypassed simply by omitting `--cert`. Gate on the freshly-derived
        // `capability_report.solver_verified` (unforgeable), default-closed,
        // with the `SIGIL_ALLOW_UNVERIFIED_CERT=1` override.
        if require_solver_verified_from_env() && !compilation.capability_report.solver_verified {
            return emit_gate_failure(kind, fmt, GateFailure::SolverUnverified);
        }

        // Iteration 36 of Spec A + E (axis-5 sixth touch): cert gate.
        // With --cert <path>: load the cert (with file-shape guards),
        // gate against the freshly-compiled output, abort on any
        // mismatch with the appropriate R8xx code. Without --cert:
        // print a one-line stderr nudge so users discover the gate.
        match &command.cert_path {
            Some(cert_path) => {
                let cert = match load_cert_file(cert_path) {
                    Ok(c) => c,
                    Err(failure) => return emit_gate_failure(kind, fmt, failure),
                };
                // `run` has no grant-style flags; effects check is skipped
                // (cert.effects_required is informational). Iteration 38
                // adds the bidirectional effects check on `forge`.
                if let Err(failure) = gate_cert(
                    &cert,
                    command.source_text.as_bytes(),
                    &compilation.wasm_inner,
                    compilation.wasm_outer.as_deref(),
                    None,
                    require_solver_verified_from_env(),
                    compilation.capability_report.solver_verified,
                    &compilation.formal_security_report,
                ) {
                    return emit_gate_failure(kind, fmt, failure);
                }
            }
            None => {
                // Adversarial-review fix MC-8: opt-in stays optional in
                // this PR, but a stderr nudge makes the gate discoverable.
                // Suppressed in JSON mode (output is structured; nudges
                // would corrupt downstream parsers).
                if !fmt.is_json() {
                    eprintln!(
                        "note: running without certificate gate; \
                         pass --cert <path> to enable verification"
                    );
                }
            }
        }

        run_runtime_with_format(&compilation, command, kind, fmt)
    } else {
        emit_check_success(&compilation, command, kind, fmt)
    }
}

fn emit_check_success(
    compilation: &Compilation,
    command: &CompileCommand,
    kind: CommandKind,
    fmt: OutputFormat,
) -> anyhow::Result<()> {
    // Step 22 (axis 5): if --emit-wasm <path> was supplied, write the
    // emitted inner-module WASM to disk so the downstream
    // `verify-cert --wasm <path>` flow can re-verify the deployable
    // artifact. Done before envelope emission so failure to write
    // surfaces as a CLI error rather than a half-success.
    if let Some(out) = &command.wasm_out_path {
        fs::write(out, &compilation.wasm_inner)
            .with_context(|| format!("failed to write inner wasm to `{}`", out.display()))?;
    }

    // Iteration 36 of Spec A + E (axis-5 sixth touch): if --cert <path>
    // was supplied on `sigil check`, write the cert JSON to that path.
    // Pairs with `sigil run --cert <path>` (gate) and `sigil verify-cert
    // --cert <path>` (reporter), both of which READ a cert from <path>.
    // Same flag name, different read/write semantics per command kind.
    if let Some(out) = &command.cert_path {
        let cert = certificate_from_compilation(compilation, &command.source_text);
        let cert_json = serde_json::to_string_pretty(&cert)
            .context("failed to serialize certificate to JSON")?;
        fs::write(out, cert_json)
            .with_context(|| format!("failed to write cert to `{}`", out.display()))?;
    }

    if fmt.is_json() {
        // Step 11 (axis 5): the `--json` output of `sigil check` now
        // includes a verification certificate — a self-contained
        // summary of what the compiler proved, consumable by external
        // tools without re-running the compiler. See
        // sigil_compiler::certificate for the schema.
        let cert = certificate_from_compilation(compilation, &command.source_text);
        let mut data = json!({
            "source_name": compilation.source_name,
            "primary_module": compilation.primary_module_name(),
            "wasm_inner_bytes": compilation.wasm_inner.len(),
            "wasm_outer_bytes": compilation.wasm_outer.as_ref().map(|w| w.len()),
            "air_function_count": compilation.air.functions.len(),
            "fuel_budget": compilation.fuel_budget,
            // Solver witness introduced in cert v8 and retained in v9, surfaced top-level
            // so consumers needn't dig
            // into `certificate.capability` (the authoritative copy). false
            // means the Z3 flow-sensitive proofs did NOT run (solver-off
            // build); structural checks still did. ET-M5: the FIELD on
            // json stdout — never prose.
            "solver_verified": compilation.capability_report.solver_verified,
            "certificate": cert,
        });
        if command.dump_wat {
            let wat = wat_payload(compilation)?;
            data["wat"] = wat;
        }
        Envelope::ok(kind.json_name(), data).emit();
        return Ok(());
    }

    print_compile_summary(compilation);
    // ET-M5: the human-facing voice for the eight solver-off stubs. When
    // the Z3 flow-sensitive proofs did NOT run (a `--no-default-features`
    // / solver-off toolchain), say so — once, on stderr (suppressed in
    // json above, where the field carries it). Note-severity: solver-off
    // is a documented build mode, and the cert is the auditable artifact;
    // this is a discoverability nudge, mirroring the `--cert` nudge idiom.
    if !compilation.capability_report.solver_verified {
        eprintln!(
            "note: this build verified STRUCTURAL capability rules only \
             (forgery, linearity, exclusivity, taint). The Z3 \
             flow-sensitive proofs (capability flow, refinement \
             discharge) did NOT run — this toolchain was built without \
             the `solver` feature. The certificate records \
             `solver_verified: false`."
        );
    }
    if command.dump_wat {
        print_wat("inner module", &compilation.wasm_inner)?;
        if let Some(outer) = &compilation.wasm_outer {
            print_wat("outer module", outer)?;
        }
    }
    Ok(())
}

fn run_package_check(
    command: &CompileCommand,
    package_root: &std::path::Path,
    fmt: OutputFormat,
    context: &CompilerContext,
) -> anyhow::Result<()> {
    let options = CompileOptions {
        build_deadline: command.build_deadline,
    };
    let package = match sigil_compiler::package::compile_local_package_with_context(
        package_root,
        options,
        context,
    ) {
        Ok(package) => package,
        Err(sigil_compiler::package::PackageCompileError::Package(error))
            if error.code == "E_SOLVER_UNVERIFIED" =>
        {
            return emit_gate_failure(CommandKind::Check, fmt, GateFailure::SolverUnverified);
        }
        Err(sigil_compiler::package::PackageCompileError::Package(error)) => {
            if fmt.is_json() {
                Envelope::error_with_data(
                    CommandKind::Check.json_name(),
                    Vec::new(),
                    json!({
                        "code": error.code,
                        "message": error.message,
                        "severity": "error",
                    }),
                )
                .emit();
                bail!("package compilation failed");
            }
            bail!("{error}");
        }
        Err(sigil_compiler::package::PackageCompileError::Compiler(error)) => {
            let fallback = package_root.join("sigil-package.json");
            let source = SourceFile::new(fallback.display().to_string(), String::new());
            if fmt.is_json() {
                Envelope::error(
                    CommandKind::Check.json_name(),
                    compile_error_to_json(&error, &source),
                )
                .emit();
                bail!("package source compilation failed");
            }
            bail!("{}", error.render(&source));
        }
    };

    if let Some(out) = &command.wasm_out_path {
        fs::write(out, &package.compilation.wasm_inner)
            .with_context(|| format!("failed to write inner wasm to `{}`", out.display()))?;
    }
    let certificate = package.certificate();
    let certificate_json = serde_json::to_string_pretty(&certificate)
        .context("failed to serialize package certificate")?;
    if let Some(out) = &command.cert_path {
        fs::write(out, &certificate_json)
            .with_context(|| format!("failed to write package cert to `{}`", out.display()))?;
    }

    if fmt.is_json() {
        let mut data = json!({
            "package_root": package_root.display().to_string(),
            "root_package": package.graph.root_package,
            "package_graph_hash": package.graph.graph_hash,
            "source_framing_hash": package.graph.source_framing_hash,
            "wasm_inner_bytes": package.compilation.wasm_inner.len(),
            "wasm_outer_bytes": package.compilation.wasm_outer.as_ref().map(Vec::len),
            "certificate": certificate,
        });
        if command.dump_wat {
            data["wat"] = wat_payload(&package.compilation)?;
        }
        Envelope::ok(CommandKind::Check.json_name(), data).emit();
        return Ok(());
    }

    println!(
        "package check: OK ({}; graph {})",
        package.graph.root_package, package.graph.graph_hash
    );
    print_compile_summary(&package.compilation);
    if command.dump_wat {
        print_wat("inner module", &package.compilation.wasm_inner)?;
        if let Some(outer) = &package.compilation.wasm_outer {
            print_wat("outer module", outer)?;
        }
    }
    Ok(())
}

fn wat_payload(compilation: &Compilation) -> anyhow::Result<serde_json::Value> {
    let inner = wasm_to_wat_string(&compilation.wasm_inner)?;
    let outer = match &compilation.wasm_outer {
        Some(bytes) => Some(wasm_to_wat_string(bytes)?),
        None => None,
    };
    Ok(json!({
        "inner": inner,
        "outer": outer,
    }))
}

pub(crate) fn wasm_to_wat_string(wasm: &[u8]) -> anyhow::Result<String> {
    wasmprinter::print_bytes(wasm)
        .map_err(|e| anyhow::anyhow!("failed to convert wasm to wat: {e}"))
}

fn print_compile_summary(compilation: &Compilation) {
    let module_label = compilation
        .primary_module_name()
        .unwrap_or("<multi-module>");

    println!(
        "Compiled `{module_label}` from {}.",
        compilation.source_name
    );
    println!(
        "Wasm size: {} bytes. AIR functions: {}. Runtime fuel budget: {}.",
        compilation.wasm_inner.len(),
        compilation.air.functions.len(),
        compilation.fuel_budget
    );
}

pub(crate) fn print_wat(label: &str, wasm: &[u8]) -> anyhow::Result<()> {
    let wat = wasmprinter::print_bytes(wasm)
        .map_err(|e| anyhow::anyhow!("failed to convert wasm to wat for {label}: {e}"))?;
    println!("WAT for {label}:");
    println!("{wat}");
    Ok(())
}

// ---------------------------------------------------------------------------
// Runtime
// ---------------------------------------------------------------------------

fn run_runtime_with_format(
    compilation: &Compilation,
    command: &CompileCommand,
    kind: CommandKind,
    fmt: OutputFormat,
) -> anyhow::Result<()> {
    let mut host = RuntimeHost::new(compilation.fuel_budget);
    // PPS-4: apply the per-actor persistent-heap cap before bootstrap.
    if let Some(cap) = command.persistent_cap {
        host.set_persistent_cap(cap);
    }
    let report = match host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner) {
        Ok(r) => r,
        Err(err) => {
            if fmt.is_json() {
                let diag = runtime_error_to_diagnostic(&err);
                Envelope::error(kind.json_name(), vec![diag]).emit();
                bail!("runtime bootstrap failed");
            }
            bail!("{err}");
        }
    };
    let delivered = match host.drain_messages(32) {
        Ok(n) => n,
        Err(err) => {
            if fmt.is_json() {
                let diag = runtime_error_to_diagnostic(&err);
                Envelope::error(kind.json_name(), vec![diag]).emit();
                bail!("runtime message drain failed");
            }
            bail!("{err}");
        }
    };

    // ACTOR-LIVE AL-4: `--serve` turns `run` into a resident service — after the boot drain, feed
    // stdin lines to the entry actor's designated handler until EOF (docs/specs/actor-live.md).
    if kind == CommandKind::Run && command.serve {
        return run_serve(
            &mut host,
            compilation,
            report.entry_actor,
            command,
            kind,
            fmt,
        );
    }

    let entry_actor = report
        .entry_actor
        .map(|actor_id| actor_id.to_string())
        .unwrap_or_else(|| "none".to_owned());

    if fmt.is_json() {
        let data = json!({
            "source_name": compilation.source_name,
            "primary_module": compilation.primary_module_name(),
            "wasm_inner_bytes": compilation.wasm_inner.len(),
            "wasm_outer_bytes": compilation.wasm_outer.as_ref().map(|w| w.len()),
            "air_function_count": compilation.air.functions.len(),
            "fuel_budget": compilation.fuel_budget,
            "runtime": {
                "module_name": report.module_name,
                "entry_actor": entry_actor,
                "queued_messages": report.queued_messages,
                "delivered_messages": delivered,
                "actors_count": host.actors().len(),
                "pending_messages": host.pending_messages(),
                "audit_events": host.audit_log().len(),
                "capabilities": host.capability_table().len(),
            },
        });
        Envelope::ok(kind.json_name(), data).emit();
        return Ok(());
    }

    print_compile_summary(compilation);
    if command.dump_wat {
        print_wat("inner module", &compilation.wasm_inner)?;
        if let Some(outer) = &compilation.wasm_outer {
            print_wat("outer module", outer)?;
        }
    }
    println!(
        "Runtime bootstrapped `{}`. Entry actor: {}. Queued boot messages: {}. Delivered messages: {}.",
        report.module_name, entry_actor, report.queued_messages, delivered
    );
    println!(
        "Runtime state: actors={}, pending_messages={}, audit_events={}, capabilities={}.",
        host.actors().len(),
        host.pending_messages(),
        host.audit_log().len(),
        host.capability_table().len()
    );

    Ok(())
}

/// ACTOR-LIVE AL-4: run the host as a resident service, feeding stdin lines to the entry actor's
/// designated handler until EOF. The input source is HOST-side — each line becomes a typed
/// `Message` via the existing `enqueue_message` API, so the actor ABI gains NO new import (X-AL4).
fn run_serve(
    host: &mut RuntimeHost,
    compilation: &Compilation,
    entry_actor: Option<sigil_runtime::ActorId>,
    command: &CompileCommand,
    kind: CommandKind,
    fmt: OutputFormat,
) -> anyhow::Result<()> {
    let receiver =
        entry_actor.context("--serve requires an entry actor, but this project declares none")?;
    let handler = resolve_serve_handler(
        &compilation.runtime_module,
        command.serve_handler.as_deref(),
    )?;
    let stats = sigil_runtime::serve_loop(
        host,
        std::io::stdin().lock(),
        receiver,
        handler.handler_id,
        &handler.name,
        &handler.export_name,
        handler.params[0].clone(),
        256,
    )
    .map_err(|err| anyhow::anyhow!("serve loop failed: {err:?}"))?;

    if fmt.is_json() {
        let data = json!({
            "source_name": compilation.source_name,
            "primary_module": compilation.primary_module_name(),
            "serve": {
                "handler": handler.name,
                "lines_read": stats.lines_read,
                "dispatched": stats.dispatched,
                "skipped": stats.skipped,
                "delivered": stats.delivered,
            },
        });
        Envelope::ok(kind.json_name(), data).emit();
        return Ok(());
    }

    println!(
        "Served `{}` handler `{}`: {} line(s) read, {} dispatched, {} skipped, {} delivered.",
        compilation.primary_module_name().unwrap_or("<module>"),
        handler.name,
        stats.lines_read,
        stats.dispatched,
        stats.skipped,
        stats.delivered
    );
    Ok(())
}

/// Pick the entry actor's line-handler for `--serve`: `--on <name>` if given, else the sole
/// non-`Start` handler taking exactly one scalar (`i64`/`bool`) param. Fails loud on ambiguity or a
/// wrong shape — validated at startup, before any input is read.
fn resolve_serve_handler<'a>(
    module: &'a sigil_runtime::RuntimeModuleSpec,
    explicit: Option<&str>,
) -> anyhow::Result<&'a sigil_runtime::RuntimeHandlerSpec> {
    use sigil_runtime::RuntimeTypeSpec;
    let actor = module
        .entry_actor()
        .context("--serve requires an entry actor, but this project declares none")?;
    let is_scalar = |h: &sigil_runtime::RuntimeHandlerSpec| {
        h.params.len() == 1 && matches!(h.params[0], RuntimeTypeSpec::I64 | RuntimeTypeSpec::Bool)
    };

    if let Some(name) = explicit {
        let handler = actor
            .handlers
            .iter()
            .find(|h| h.name == name)
            .with_context(|| {
                format!(
                    "--serve: entry actor `{}` has no handler `{name}`",
                    actor.name
                )
            })?;
        if !is_scalar(handler) {
            bail!("--serve: handler `{name}` must take exactly one `i64` or `bool` param");
        }
        return Ok(handler);
    }

    let mut candidates = actor
        .handlers
        .iter()
        .filter(|h| h.name != "Start" && is_scalar(h));
    let first = candidates.next().with_context(|| {
        format!(
            "--serve: entry actor `{}` has no non-`Start` handler taking one `i64`/`bool` param; \
             add one or pass `--on <handler>`",
            actor.name
        )
    })?;
    if candidates.next().is_some() {
        bail!(
            "--serve: entry actor `{}` has multiple line handlers; disambiguate with `--on <handler>`",
            actor.name
        );
    }
    Ok(first)
}
