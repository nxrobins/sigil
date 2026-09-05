//! JSON wire types for diagnostics.
//!
//! Exposes a stable, versioned schema for machine-readable diagnostic output
//! (see [`SCHEMA_VERSION`]; currently v2). The
//! envelope (`status` / `command` / `data` / `diagnostics`) is owned by the
//! CLI; this module only defines the per-diagnostic element and the
//! conversion from the in-memory `Diagnostic` type.
//!
//! Span offsets are UTF-8 byte offsets (matching `Span::start`/`Span::end`
//! semantics in the compiler). The `line` and `column` fields are 1-indexed
//! and computed via `SourceFile::line_col`.

use serde::Serialize;

use super::{Diagnostic, Severity};
use crate::source::{SourceFile, SourceMap};
use crate::span::Span;

/// Schema version of the diagnostic JSON wire format.
///
/// * v1: severity/code/title/message/hint/doc_url/location.
/// * v2 (a2 / diagnostics-axes loop): adds optional `suggested_edits` —
///   machine-applicable byte-range fixes — serialized only when present AND
///   validated against the rendered source. Purely additive; v1 consumers that
///   ignore unknown fields are unaffected. The CLI envelope's `SCHEMA_VERSION`
///   is pinned equal to this by a compile-time assert in `json_envelope.rs`.
pub const SCHEMA_VERSION: u32 = 2;

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum SeverityJson {
    Error,
    Warning,
    Note,
}

impl From<Severity> for SeverityJson {
    fn from(s: Severity) -> Self {
        match s {
            Severity::Error => Self::Error,
            Severity::Warning => Self::Warning,
            Severity::Note => Self::Note,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct SpanJson {
    pub start: usize,
    pub end: usize,
}

impl From<Span> for SpanJson {
    fn from(s: Span) -> Self {
        Self {
            start: s.start,
            end: s.end,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct LocationJson {
    pub file: String,
    pub span: SpanJson,
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct SuggestedEditJson {
    pub start: usize,
    pub end: usize,
    pub replacement: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct DiagnosticJson {
    pub severity: SeverityJson,
    pub code: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub title: Option<&'static str>,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hint: Option<String>,
    pub doc_url: String,
    pub location: Option<LocationJson>,
    /// v2: machine-applicable fix(es). Present only when the diagnostic carries
    /// edits AND every edit validated against the source rendered here.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suggested_edits: Option<Vec<SuggestedEditJson>>,
}

/// Convert an in-memory `Diagnostic` to its JSON wire form.
pub fn to_json(diagnostic: &Diagnostic, source: &SourceFile) -> DiagnosticJson {
    let location = diagnostic.span().map(|span| {
        let (line, column) = source.line_col(span.start);
        LocationJson {
            file: source.name().to_owned(),
            span: span.into(),
            line,
            column,
        }
    });
    DiagnosticJson {
        severity: diagnostic.severity().into(),
        code: diagnostic.code().as_str().to_owned(),
        title: diagnostic.title(),
        message: diagnostic.message().to_owned(),
        hint: diagnostic.hint().map(str::to_owned),
        doc_url: format!("sigil://errors/{}", diagnostic.code()),
        location,
        suggested_edits: suggested_edits_json(diagnostic, source),
    }
}

/// Validate the diagnostic's opt-in edits against `source` and convert to the
/// wire form. Returns `None` unless EVERY edit is safe to apply to `source`:
/// the diagnostic has a non-synthetic span, and each edit satisfies
/// `start <= end <= source.len()` with both offsets on UTF-8 char boundaries.
/// A single invalid edit drops the whole set (never emit a half-valid fix) — the
/// prose hint remains the floor. This is the a2 fail-fast: validate-and-drop,
/// never clamp, never emit offsets against an unverified buffer.
fn suggested_edits_json(
    diagnostic: &Diagnostic,
    source: &SourceFile,
) -> Option<Vec<SuggestedEditJson>> {
    let edits = diagnostic.suggested_edits()?;
    // Offsets only bind to `source` for a real (non-synthetic) span.
    let span_bindable = diagnostic.span().is_some_and(|s| !s.source.is_synthetic());
    if !span_bindable {
        debug_assert!(
            false,
            "suggested_edits present on a spanless/synthetic diagnostic ({})",
            diagnostic.code()
        );
        return None;
    }
    let text = source.text();
    let mut out = Vec::with_capacity(edits.len());
    for e in edits {
        let valid = e.start <= e.end
            && e.end <= text.len()
            && text.is_char_boundary(e.start)
            && text.is_char_boundary(e.end);
        if !valid {
            debug_assert!(
                false,
                "invalid SuggestedEdit {}..{} against `{}` (len {})",
                e.start,
                e.end,
                source.name(),
                text.len()
            );
            return None;
        }
        out.push(SuggestedEditJson {
            start: e.start,
            end: e.end,
            replacement: e.replacement.clone(),
        });
    }
    Some(out)
}

/// Convert a slice of diagnostics — convenience wrapper for the common
/// single-source path (the caller-passed `source` is the owning file).
pub fn diagnostics_to_json(diagnostics: &[Diagnostic], source: &SourceFile) -> Vec<DiagnosticJson> {
    diagnostics.iter().map(|d| to_json(d, source)).collect()
}

/// SourceMap-aware conversion for multi-file errors: resolve each diagnostic's
/// OWNING [`SourceFile`] via `map` (falling back to `fallback` for synthetic or
/// unresolved spans) and render against THAT file, so `location` offsets — and
/// any `suggested_edits` — are validated against the file they actually index,
/// never a caller-passed primary source. Mirrors `CompileError::render`'s
/// per-span resolution for the JSON path (closes the multi-file wrong-file gap).
pub fn diagnostics_to_json_in_map(
    diagnostics: &[Diagnostic],
    map: &SourceMap,
    fallback: &SourceFile,
) -> Vec<DiagnosticJson> {
    diagnostics
        .iter()
        .map(|d| {
            let owning = d.span().and_then(|s| map.get(s.source)).unwrap_or(fallback);
            to_json(d, owning)
        })
        .collect()
}
