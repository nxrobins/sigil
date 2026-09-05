//! The `sigil` binary root: argv in, exit code out. `main` parses argv
//! into a typed `Command` (`args`), then `dispatch` routes it to its
//! verb module: `check_run` (check/run/--serve), `forge`,
//! `registry_cmd`, `cert_gate` (verify-cert plus the shared execution
//! gate), `translate`, and `info` (version/help/explain), with
//! `json_envelope` shaping all `--json` output.
//!
//! Failure discipline: handlers return `anyhow::Result`; under `--json`
//! a handler emits its one schema-versioned envelope before bailing,
//! and `dispatch` never double-emits. Success exits 0, a failed command
//! exits nonzero, an argv-parse failure exits 2 (R800 under `--json`).
//! Accepted gap: an I/O error escaping before a handler's emission
//! point gets only the nonzero exit, no envelope. End-to-end pins:
//! `crates/sigil-cli/tests/` (`json_output.rs`, `explain.rs`,
//! `translate_smoke.rs`).

use std::env;
use std::process::ExitCode;

use sigil_compiler::diagnostics::codes;

mod args;
mod cert_gate;
mod check_run;
mod forge;
mod info;
mod json_envelope;
mod registry_cmd;
mod translate;

use args::{Command, CommandKind, parse_args};
use cert_gate::run_verify_cert;
use check_run::run_check_or_run;
use forge::run_forge;
use info::{run_explain, run_help, run_version};
use registry_cmd::{run_registry_add, run_registry_list, run_registry_search};
use translate::run_translate;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    let command = match parse_args(&args) {
        Ok(c) => c,
        Err(e) => {
            // We don't yet know the format definitively (parse failed before
            // we could inspect the flag), so peek for --json in the raw args.
            if args.iter().any(|a| a == "--json") {
                // Arg-parse failures are emitted under R800 (generic runtime
                // error) since they prevent the compiler from even starting.
                json_envelope::emit_generic_error("<unknown>", codes::R800, e.to_string());
            } else {
                eprintln!("error: {e}");
            }
            return ExitCode::from(2);
        }
    };
    match dispatch(&command) {
        Ok(()) => ExitCode::SUCCESS,
        Err(()) => ExitCode::FAILURE,
    }
}

fn dispatch(command: &Command) -> Result<(), ()> {
    // A named profile was validated at parse time; the legacy context stays the default.
    let context = match command
        .host_profile()
        .and_then(sigil_runtime::host_profile_by_name)
    {
        Some(profile) => sigil_compiler::CompilerContext::with_host_profile(profile),
        None => sigil_compiler::CompilerContext::default(),
    };
    dispatch_with_context(command, &context)
}

/// Bootstrap-selected declarations are shared by compile and rederivation.
/// No command argument or certificate is interpreted as provider approval.
fn dispatch_with_context(
    command: &Command,
    context: &sigil_compiler::CompilerContext,
) -> Result<(), ()> {
    let fmt = command.output_format();
    let cmd_name = command.kind().json_name();

    let result: anyhow::Result<()> = match command {
        Command::Check(args) => run_check_or_run(args, CommandKind::Check, fmt, context),
        Command::Run(args) => run_check_or_run(args, CommandKind::Run, fmt, context),
        Command::Forge(args) => run_forge(args, fmt, context),
        Command::RegistryAdd(args) => run_registry_add(args, fmt, context),
        Command::RegistrySearch(args) => run_registry_search(args, fmt),
        Command::RegistryList { .. } => run_registry_list(fmt),
        Command::VerifyCert(args) => run_verify_cert(args, fmt, context),
        Command::Translate(args) => run_translate(args, fmt),
        Command::Explain(args) => run_explain(args, fmt),
        Command::Version { .. } => run_version(fmt),
        Command::Help { .. } => run_help(fmt),
    };

    match result {
        Ok(()) => Ok(()),
        Err(e) => {
            // In JSON mode, subcommand handlers emit their own structured
            // diagnostic envelope BEFORE bailing. We must not double-emit here.
            // The trade-off: I/O errors that escape before a handler reaches
            // its emission point (e.g. open_registry failure) won't get a
            // JSON envelope today — only a non-zero exit code. Accepted for
            // PR 1; future PR can wrap those call sites individually.
            if !fmt.is_json() {
                eprintln!("error: {e}");
            }
            let _ = cmd_name;
            Err(())
        }
    }
}
