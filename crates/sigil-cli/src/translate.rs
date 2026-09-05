//! The translate verb: run an untrusted `sigil-frontends` translator
//! over foreign source and emit the resulting SIGIL text (or its
//! frontend diagnostics), plus the shared frontend-diagnostic
//! rendering `check_run` reuses on translated input.

use std::fs;

use anyhow::{Context, bail};
use serde_json::json;
use sigil_compiler::diagnostics::codes;

use crate::json_envelope;
use crate::json_envelope::{Envelope, OutputFormat};

use crate::args::{CommandKind, CompileCommand, TranslateCommand};

use crate::args::read_project_root;

// ---------------------------------------------------------------------------
// Foreign frontends (`sigil translate --from <lang>` and `--from` on check).
// The translator is untrusted; it emits SIGIL text that the real compiler then
// verifies. See `crates/sigil-frontends` + `docs/specs/foreign-frontends.md`.
// ---------------------------------------------------------------------------

pub(crate) fn run_translate(command: &TranslateCommand, fmt: OutputFormat) -> anyhow::Result<()> {
    let lang = command.from.as_str();
    // SOL-XFILE project mode: resolve the import closure against the root's file-set
    // (the same output handling — --emit / json / stdout — as the single-file path).
    let translated = if let Some(root) = &command.project_root {
        let (files, entry_key) = read_project_root(root, &command.source_name)?;
        sigil_frontends::translate_solidity_project(&files, &entry_key)
    } else {
        let frontend = sigil_frontends::frontend_for(lang).ok_or_else(|| {
            anyhow::anyhow!("unknown frontend language `{lang}` (try `typescript`)")
        })?;
        frontend.translate(&command.source_text, &command.source_name)
    };
    match translated {
        Ok(emitted) => {
            if let Some(out) = &command.out_path {
                fs::write(out, &emitted.text)
                    .with_context(|| format!("failed to write `{}`", out.display()))?;
                if !fmt.is_json() {
                    eprintln!("translated {} -> {}", command.source_name, out.display());
                }
            } else if fmt.is_json() {
                Envelope::ok(
                    CommandKind::Translate.json_name(),
                    json!({ "source_name": emitted.source_name, "sigil": emitted.text }),
                )
                .emit();
            } else {
                print!("{}", emitted.text);
            }
            Ok(())
        }
        Err(diags) => {
            emit_frontend_diags(
                CommandKind::Translate.json_name(),
                &command.source_name,
                &diags,
                fmt,
            );
            bail!("translation failed");
        }
    }
}

/// Translate `command.source_text` (a foreign DSL) to SIGIL and return a clone
/// of `command` whose `source_text` is the emitted SIGIL. On translation
/// failure, emit the FE diagnostics and bail.
pub(crate) fn translate_command_source(
    command: &CompileCommand,
    lang: &str,
    kind: CommandKind,
    fmt: OutputFormat,
) -> anyhow::Result<CompileCommand> {
    let frontend = sigil_frontends::frontend_for(lang)
        .ok_or_else(|| anyhow::anyhow!("unknown frontend language `{lang}` (try `typescript`)"))?;
    match frontend.translate(&command.source_text, &command.source_name) {
        Ok(emitted) => {
            let mut c = command.clone();
            c.source_text = emitted.text;
            c.from = None; // consumed — avoid re-translating
            Ok(c)
        }
        Err(diags) => {
            emit_frontend_diags(kind.json_name(), &command.source_name, &diags, fmt);
            bail!("translation failed");
        }
    }
}

fn emit_frontend_diags(
    command_name: &'static str,
    source_name: &str,
    diags: &[sigil_frontends::FrontendDiag],
    fmt: OutputFormat,
) {
    if fmt.is_json() {
        let joined = diags
            .iter()
            .map(|d| format!("{}: {}", d.code, d.message))
            .collect::<Vec<_>>()
            .join("; ");
        json_envelope::emit_generic_error(
            command_name,
            codes::R800,
            format!("frontend translation failed for `{source_name}`: {joined}"),
        );
    } else {
        for d in diags {
            eprintln!(
                "error: {}: {} ({}: bytes {}..{})",
                d.code, d.message, source_name, d.span.start, d.span.end
            );
        }
    }
}
