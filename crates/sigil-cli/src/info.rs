//! The information verbs: `version`, `help`, and `explain` — what the
//! binary answers about itself and about a diagnostic code, without
//! compiling or executing anything.

use std::env;

use anyhow::bail;
use serde_json::json;
use sigil_compiler::diagnostics::{codes, registry};

use crate::json_envelope;
use crate::json_envelope::{Envelope, OutputFormat};

use crate::args::{CommandKind, ExplainCommand};

pub(crate) fn run_version(fmt: OutputFormat) -> anyhow::Result<()> {
    use sigil_compiler::certificate::{CERTIFICATE_SCHEMA_VERSION, COMPILER_VERSION};

    let cmd_name = CommandKind::Version.json_name();
    // Two versions because they are two packages. `version` is the release
    // artifact (sigil-cli); `compiler_version` is what lands in every cert
    // this binary emits and what `verify-cert` matches on. Pinned equal by
    // `version_matches_certificate_compiler_version`, reported separately
    // so a cert consumer never has to assume the pin held.
    let version = env!("CARGO_PKG_VERSION");
    let solver = sigil_compiler::SOLVER_ENABLED;
    let host = format!("{}-{}", env::consts::ARCH, env::consts::OS);

    if fmt.is_json() {
        let data = json!({
            "version": version,
            "compiler_version": COMPILER_VERSION,
            "host": host,
            "solver": solver,
            "cert_schema_version": CERTIFICATE_SCHEMA_VERSION,
        });
        Envelope::ok(cmd_name, data).emit();
    } else {
        println!("sigil {version}");
        println!("  host:        {host}");
        println!("  compiler:    {COMPILER_VERSION}");
        println!("  cert schema: v{CERTIFICATE_SCHEMA_VERSION}");
        // Stated plainly rather than left to be inferred from a cert field
        // or discovered by hitting R817 mid-task: a released binary builds
        // solver-off, so `check` verifies structurally and `run`/`forge`
        // refuse to execute at all. Someone who downloaded a binary should
        // not have to read `crates/sigil-cli/Cargo.toml` to learn that.
        if solver {
            println!("  solver:      on (Z3 linked; refinement obligations discharged)");
        } else {
            println!(
                "  solver:      off (structural checks only; emitted certs carry \
                 solver_verified: false, and `run`/`forge` fail closed at R817 \
                 unless SIGIL_ALLOW_UNVERIFIED_CERT=1)"
            );
        }
    }
    Ok(())
}

/// Top-level usage. Lists commands and their real flags — every flag named
/// here is one `parse_args` actually accepts. Per-command detail beyond this
/// lives in the README; this exists so a freshly downloaded binary answers
/// the first thing a new user types instead of exiting 2.
const HELP_TEXT: &str = "\
sigil — capability-secure language toolchain (compiles to WebAssembly)

USAGE:
  sigil <COMMAND> [OPTIONS]

COMMANDS:
  check <FILE...>        Compile and verify; emits no artifact by default
    --package <ROOT>       Check one explicit offline locked package root (no FILE args)
    --host-profile <NAME>  Compile against a declared host profile (`ephemeral` = the built-in host)
    --entry <MODULE>       Entry module for a multi-file compile
    --cert                 Emit the verification certificate as JSON
    --emit-wasm <FILE>     Write the inner-module WASM to FILE
    --wat                  Print the module as WebAssembly text
    --from <LANG>          Translate a foreign frontend first (see `translate`)
    --build-deadline <MS>  Reject parametric caps whose deadline has passed

  run <FILE...>          Compile, verify, then execute
  check-inline <SRC>     As `check`, with source given on the command line
  run-inline <SRC>       As `run`, with source given on the command line

  forge <FILE>           One-shot ephemeral execute: fresh store, then discard
    --input <TEXT>         Input bytes (also --input-hex <HEX>)
    --fuel <N>             Fuel budget for the run
    --fs <DIR>             Grant filesystem access rooted at DIR (repeatable)
    --net <HOST>           Grant network access to HOST (repeatable)
    --template <ID>        Forge from a registry template (with --patch FIND=REPLACE)
    --cert <FILE>          Refuse to run unless the cert matches
    --frozen-time <MS>     Pin the clock for a reproducible run
    --random-seed <N>      Pin the RNG (nonzero)

  verify-cert            Check a certificate against source, WASM, and policy
    --cert <FILE>          The certificate to verify (required)
    --source <FILE>        Re-derive from source
    --package <ROOT>       Re-resolve/recompile a package and verify its graph cert
    --wasm <FILE>          Compare against a built artifact
    --forbid-effect <NAME> / --allow-effect <NAME>   Effect policy gates

  translate <FILE>       Foreign DSL -> SIGIL source (--from <LANG>, --emit <FILE>)
  registry               Template store: `add` (--task, --tags), `search`, `list`
  explain <CODE>         Look up a diagnostic code (e.g. `sigil explain T199`)

  --version, -V          Version, host, and whether Z3 is linked in
  --help, -h             This message

GLOBAL:
  --json                 Machine-readable output envelope (accepted by every command)
";

pub(crate) fn run_help(fmt: OutputFormat) -> anyhow::Result<()> {
    if fmt.is_json() {
        Envelope::ok(CommandKind::Help.json_name(), json!({ "usage": HELP_TEXT })).emit();
    } else {
        print!("{HELP_TEXT}");
    }
    Ok(())
}

pub(crate) fn run_explain(command: &ExplainCommand, fmt: OutputFormat) -> anyhow::Result<()> {
    // a5 resolvability: human/CLI counterpart of the MCP `sigil_lookup_error`
    // tool. Renders exactly the registry entry (no invented prose) + the
    // generated `docs/errors/<CODE>.md` page path, with a fuzzy "did you mean?"
    // for unknown/typo'd codes via the shared `registry::did_you_mean_codes`.
    let cmd_name = CommandKind::Explain.json_name();
    let code = command.code.trim();

    if let Some(entry) = registry::lookup_str(code) {
        let category = format!("{:?}", entry.category);
        let doc_url = format!("sigil://errors/{}", entry.code);
        let doc_path = format!("docs/errors/{}.md", entry.code);
        if fmt.is_json() {
            let data = json!({
                "code": entry.code.as_str(),
                "title": entry.title,
                "category": category,
                "default_hint": entry.default_hint,
                "doc_url": doc_url,
                "doc_path": doc_path,
            });
            Envelope::ok(cmd_name, data).emit();
        } else {
            println!("{} — {}", entry.code, entry.title);
            println!("  category: {category}");
            println!("  hint: {}", entry.default_hint);
            println!("  doc:  {doc_path}  ({doc_url})");
        }
        return Ok(());
    }

    // Unknown code: fuzzy suggestions + non-zero exit (never a panic).
    let suggestions = registry::did_you_mean_codes(code);
    let detail = if suggestions.is_empty() {
        format!(
            "`{code}` is not a known diagnostic code. See docs/errors/ or run `sigil registry`-style enumeration."
        )
    } else {
        format!(
            "`{code}` is not a known diagnostic code. Did you mean: {}?",
            suggestions.join(", ")
        )
    };
    if fmt.is_json() {
        json_envelope::emit_generic_error_with_data(
            cmd_name,
            codes::R800,
            detail,
            json!({ "code": code, "did_you_mean": suggestions }),
        );
        // Envelope already emitted; signal a non-zero exit without double-printing.
        return Err(anyhow::anyhow!("unknown diagnostic code"));
    }
    bail!("{detail}");
}

#[cfg(test)]
mod version_help_tests {
    //! The distribution surface: what a downloaded binary answers when
    //! asked what it is.
    //!
    //! These exist because prebuilt binaries change who is asking. A
    //! developer running `cargo run` knows the version and knows the
    //! solver is off; someone who ran an install script knows neither,
    //! and an installer deciding whether to upgrade can only read what
    //! the binary prints.

    use super::*;

    use crate::args::parse_args;

    /// Every spelling an installer or a new user is likely to type
    /// resolves, and none of them fall through to the unknown-command
    /// bail. `sigil --version` returning exit 2 is the specific failure
    /// this guards against — an upgrade check cannot read a version out
    /// of an arg-parse error.
    #[test]
    fn version_and_help_spellings_parse() {
        for (spelling, expected) in [
            ("--version", CommandKind::Version),
            ("-V", CommandKind::Version),
            ("version", CommandKind::Version),
            ("--help", CommandKind::Help),
            ("-h", CommandKind::Help),
            ("help", CommandKind::Help),
        ] {
            let cmd = parse_args(&[spelling.to_string()])
                .unwrap_or_else(|e| panic!("`sigil {spelling}` must parse: {e}"));
            assert_eq!(cmd.kind(), expected, "`sigil {spelling}` kind");
            assert!(
                !cmd.output_format().is_json(),
                "`sigil {spelling}` defaults to human output"
            );
        }
    }

    /// `--json` composes; anything else is rejected rather than silently
    /// ignored.
    #[test]
    fn version_accepts_only_json_flag() {
        let cmd = parse_args(&["--version".to_string(), "--json".to_string()])
            .expect("--version --json parses");
        assert_eq!(cmd.kind(), CommandKind::Version);
        assert!(
            cmd.output_format().is_json(),
            "--json must set the JSON envelope"
        );

        let err = parse_args(&["--version".to_string(), "extra".to_string()])
            .expect_err("stray argument must be rejected");
        assert!(
            err.to_string().contains("unexpected argument `extra`"),
            "expected stray-argument error: {err}"
        );
    }

    /// The unknown-command bail points at `--help`. Without this, the
    /// first thing a new user types wrong gives them no way forward.
    #[test]
    fn unknown_command_points_at_help() {
        let err = parse_args(&["frobnicate".to_string()]).expect_err("unknown command");
        assert!(
            err.to_string().contains("sigil --help"),
            "unknown-command error must point at --help: {err}"
        );
    }

    /// The help text must name every command `parse_args` dispatches on.
    /// Pins help against silent drift as commands are added.
    #[test]
    fn help_text_names_every_command() {
        for command in [
            "check",
            "run",
            "check-inline",
            "run-inline",
            "forge",
            "registry",
            "verify-cert",
            "translate",
            "explain",
        ] {
            assert!(
                HELP_TEXT.contains(command),
                "help text is missing the `{command}` command"
            );
        }
    }

    /// `sigil-cli` and `sigil-compiler` are separate packages with
    /// separate `[package] version` fields, and a release tag has to move
    /// both. If they drift, a user reading `sigil --version` and a
    /// verifier reading a cert's `compiler_version` are quoting different
    /// numbers for the same binary. Cheap pin; fails the moment a release
    /// bumps one and forgets the other.
    #[test]
    fn version_matches_certificate_compiler_version() {
        assert_eq!(
            env!("CARGO_PKG_VERSION"),
            sigil_compiler::certificate::COMPILER_VERSION,
            "sigil-cli and sigil-compiler versions must be bumped together"
        );
    }
}
