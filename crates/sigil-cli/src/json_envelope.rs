//! JSON envelope assembly and emission for the CLI.
//!
//! The compiler crate owns the per-`Diagnostic` JSON wire shape (in
//! `sigil_compiler::diagnostics::json`). This module owns the outer envelope
//! that wraps diagnostics + success data into a single stable JSON object,
//! and the translation helpers that convert runtime errors into
//! diagnostic-shaped values.

use serde::Serialize;
use sigil_compiler::diagnostics::json::{DiagnosticJson, LocationJson, SeverityJson};
use sigil_compiler::diagnostics::{Diagnostic, codes, json as diag_json};
use sigil_compiler::source::SourceFile;
use sigil_compiler::{CompileError, DiagnosticCode};
use sigil_runtime::{RuntimeError, ToolError};

/// Schema version of the CLI envelope.
pub const SCHEMA_VERSION: u32 = 2;

// The envelope version is pinned EQUAL to the per-diagnostic wire version: a
// consumer that branches on `schema_version` must see one number across both
// surfaces, so they are bumped together. (a2 / diagnostics-axes loop.) The
// hand-built constructors below and the MCP literals are deliberately outside
// the v2 `suggested_edits` contract and never advertise edit support.
const _: () = assert!(SCHEMA_VERSION == diag_json::SCHEMA_VERSION);

#[derive(Debug, Clone, Copy)]
pub enum OutputFormat {
    Human,
    Json,
}

impl OutputFormat {
    pub fn is_json(self) -> bool {
        matches!(self, OutputFormat::Json)
    }
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    Ok,
    Error,
}

#[derive(Debug, Serialize)]
pub struct Envelope {
    pub schema_version: u32,
    pub status: Status,
    pub command: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<DiagnosticJson>,
}

impl Envelope {
    pub fn ok(command: &'static str, data: serde_json::Value) -> Self {
        Self {
            schema_version: SCHEMA_VERSION,
            status: Status::Ok,
            command,
            data: Some(data),
            diagnostics: Vec::new(),
        }
    }

    pub fn error(command: &'static str, diagnostics: Vec<DiagnosticJson>) -> Self {
        Self {
            schema_version: SCHEMA_VERSION,
            status: Status::Error,
            command,
            data: None,
            diagnostics,
        }
    }

    /// Error envelope with structured data attached. Used when a failure
    /// has machine-readable per-check results worth surfacing alongside
    /// the diagnostic. The verify-cert subcommand uses this so external
    /// audit pipelines can inspect which specific check failed without
    /// parsing a diagnostic message.
    pub fn error_with_data(
        command: &'static str,
        diagnostics: Vec<DiagnosticJson>,
        data: serde_json::Value,
    ) -> Self {
        Self {
            schema_version: SCHEMA_VERSION,
            status: Status::Error,
            command,
            data: Some(data),
            diagnostics,
        }
    }

    /// Emit the envelope as pretty-printed JSON to stdout.
    pub fn emit(&self) {
        match serde_json::to_string_pretty(self) {
            Ok(text) => println!("{text}"),
            Err(e) => {
                // JSON serialization failing is a programming bug; fall back
                // to a minimal hand-rolled envelope so the agent gets *something*
                // structured.
                eprintln!("error: failed to serialize JSON envelope: {e}");
                println!(
                    "{{\"schema_version\":{},\"status\":\"error\",\"command\":\"{}\",\"diagnostics\":[]}}",
                    SCHEMA_VERSION, self.command
                );
            }
        }
    }
}

/// Translate a [`CompileError`] into a vector of [`DiagnosticJson`].
///
/// When the error carries a [`SourceMap`](sigil_compiler::source::SourceMap)
/// (multi-file), each diagnostic is resolved to its OWNING file so `location`
/// offsets — and any `suggested_edits` — are validated against the file they
/// actually index, never the passed primary `source`. Single-file errors (no
/// map) render against `source`, which is the owning file.
pub fn compile_error_to_json(err: &CompileError, source: &SourceFile) -> Vec<DiagnosticJson> {
    match err.sources() {
        Some(map) => diag_json::diagnostics_to_json_in_map(err.diagnostics(), map, source),
        None => diag_json::diagnostics_to_json(err.diagnostics(), source),
    }
}

/// Translate a [`RuntimeError`] into a single diagnostic-shaped JSON object,
/// mapping each variant to a code in the reserved `R800-R899` range.
pub fn runtime_error_to_diagnostic(err: &RuntimeError) -> DiagnosticJson {
    let (code, title): (DiagnosticCode, &'static str) = match err {
        RuntimeError::FuelExhausted { .. } => (codes::R801, "Fuel exhausted"),
        RuntimeError::MissingExport(_) | RuntimeError::MissingMemoryExport => {
            (codes::R802, "Missing Wasm export")
        }
        RuntimeError::Capability { .. } => (codes::R806, "Capability table error"),
        RuntimeError::Wasm { .. } => (codes::R807, "Wasm runtime error"),
        RuntimeError::PersistentHeapExhausted { .. } => (codes::R818, "Persistent heap exhausted"),
        _ => (codes::R800, "Runtime error"),
    };
    diag_from_parts(code, title, err.to_string())
}

/// Translate a [`ToolError`] into a single diagnostic-shaped JSON object.
pub fn tool_error_to_diagnostic(err: &ToolError) -> DiagnosticJson {
    let (code, title): (DiagnosticCode, &'static str) = match err {
        ToolError::FuelExhausted { .. } => (codes::R801, "Fuel exhausted"),
        ToolError::Trapped { .. } => (codes::R803, "Tool trapped during execution"),
        ToolError::NoEntryPoint => (codes::R804, "Tool module missing `tool_main` entry point"),
    };
    diag_from_parts(code, title, err.to_string())
}

/// Build a spanless [`DiagnosticJson`] from raw parts. Used for runtime errors
/// that have no source location — the `location` field is `null`.
fn diag_from_parts(code: DiagnosticCode, title: &'static str, message: String) -> DiagnosticJson {
    // Construct a Diagnostic so the registry hint flows through automatically.
    let diag = Diagnostic::error(code, message, None);
    DiagnosticJson {
        severity: SeverityJson::Error,
        code: diag.code().as_str().to_owned(),
        title: Some(title),
        message: diag.message().to_owned(),
        hint: diag.hint().map(str::to_owned),
        doc_url: format!("sigil://errors/{}", diag.code()),
        location: Option::<LocationJson>::None,
        // Hand-built runtime-error path: outside the v2 suggested_edits contract.
        suggested_edits: None,
    }
}

/// Convenience: emit an envelope wrapping a single error message that doesn't
/// fit the compile/runtime error categories (e.g. arg parsing failures).
pub fn emit_generic_error(command: &'static str, code: DiagnosticCode, message: String) {
    let diag = build_generic_diagnostic(code, message);
    Envelope::error(command, vec![diag]).emit();
}

/// Like [`emit_generic_error`] but additionally attaches structured `data`
/// to the envelope. Used when a failure carries machine-readable per-check
/// results worth surfacing alongside the diagnostic.
pub fn emit_generic_error_with_data(
    command: &'static str,
    code: DiagnosticCode,
    message: String,
    data: serde_json::Value,
) {
    let diag = build_generic_diagnostic(code, message);
    Envelope::error_with_data(command, vec![diag], data).emit();
}

fn build_generic_diagnostic(code: DiagnosticCode, message: String) -> DiagnosticJson {
    let diag = Diagnostic::error(code, message, None);
    DiagnosticJson {
        severity: SeverityJson::Error,
        code: diag.code().as_str().to_owned(),
        title: diag.title(),
        message: diag.message().to_owned(),
        hint: diag.hint().map(str::to_owned),
        doc_url: format!("sigil://errors/{}", diag.code()),
        location: None,
        // Hand-built generic-error path: outside the v2 suggested_edits contract.
        suggested_edits: None,
    }
}
