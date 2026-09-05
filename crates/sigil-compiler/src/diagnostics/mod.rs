//! Compiler diagnostics: error reporting with stable codes and fix recipes.
//!
//! The core type is [`Diagnostic`], which carries a stable [`DiagnosticCode`],
//! a severity, an optional source [`Span`], and a free-form message. An optional
//! per-call-site `hint` may override the registry's default fix recipe; if no
//! override is set, the renderer/JSON emitter falls back to
//! [`registry::lookup`].
//!
//! Construction:
//! - [`Diagnostic::error(code, message, span)`] — preferred form for new code.
//! - [`Diagnostic::error_with_hint(code, message, span, hint)`] — when a
//!   context-specific hint is needed instead of the registry default.
//! - [`Diagnostic::error_in_file(code, message, span, source_name)`] —
//!   Wall 5 Step 1: attaches an explicit source-file attribution for
//!   multi-file projects, so [`Diagnostic::render_in_project`] can look
//!   up the right [`SourceFile`] when the diagnostic belongs to a
//!   non-primary file. Existing codes that don't set `source_name`
//!   continue to render against the renderer's default `SourceFile`
//!   (legacy single-source behavior).

use std::{error::Error, fmt, sync::Arc};

use crate::{
    source::{SourceFile, SourceMap},
    span::Span,
};

pub mod codes;
pub mod registry;

#[cfg(feature = "json")]
pub mod json;

#[cfg(feature = "json")]
pub mod certificate;

pub use codes::DiagnosticCode;

/// Severity level of a diagnostic. Most diagnostics are `Error`; `Warning` is
/// live (T252, the `@ReadOnly` partial-guarantee lint) and rides the `Err` path
/// alongside any errors, so consumers that count errors must filter on
/// `Severity::Error`. `Note` is reserved by the wire schema.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Note,
}

/// A machine-applicable fix: replace the bytes in `start..end` (UTF-8 byte
/// offsets into the diagnostic's source, end exclusive — matching [`Span`])
/// with `replacement`. Wire schema v2. Emitted only after per-edit validation
/// in [`json::to_json`]; an editor can apply it without parsing the prose hint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SuggestedEdit {
    pub start: usize,
    pub end: usize,
    pub replacement: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    code: DiagnosticCode,
    severity: Severity,
    message: String,
    hint: Option<String>,
    span: Option<Span>,
    /// Wall 5 Step 1: optional source-file attribution for multi-file
    /// projects. When `Some(name)`, [`Diagnostic::render_in_project`]
    /// looks up the matching [`SourceFile`] in the provided source set
    /// and renders against that file's text — fixing wrong-file
    /// attribution in multi-file mode. When `None`, the diagnostic
    /// renders against whichever [`SourceFile`] the caller passes
    /// (legacy single-source behavior, byte-equal for all existing
    /// callers). The M001-M010 multi-file diagnostics always populate
    /// this field; pre-existing T-, R-, N-, E- codes leave it `None`
    /// until commit #5's SourceId refactor (Option A) plumbs full
    /// attribution everywhere.
    source_name: Option<String>,
    /// Opt-in machine-applicable fix(es). Set only via
    /// [`Self::with_suggested_edits`], which normalizes an empty list to `None`
    /// and caps the count at 1 (the a2 contract). Serialized — after per-edit
    /// validation against the rendered source — by [`json::to_json`].
    suggested_edits: Option<Vec<SuggestedEdit>>,
}

impl Diagnostic {
    /// Construct a new error diagnostic with a known code.
    ///
    /// In debug builds, asserts that `code` is registered in
    /// [`registry::CODES`]. This catches typos at the first test run
    /// rather than in production.
    pub fn error(code: DiagnosticCode, message: impl Into<String>, span: Option<Span>) -> Self {
        debug_assert!(
            registry::lookup(code).is_some(),
            "Diagnostic constructed with unknown code `{}` — add it to crates/sigil-compiler/src/diagnostics/registry.rs::CODES",
            code
        );
        Self {
            code,
            severity: Severity::Error,
            message: message.into(),
            hint: None,
            span,
            source_name: None,
            suggested_edits: None,
        }
    }

    /// Construct a new WARNING diagnostic with a known code. Same registry
    /// debug-assert as [`Self::error`]; differs only in `severity`. Warnings are
    /// NON-BLOCKING — `type_check::check_with_warnings` aborts only on
    /// `Severity::Error`, so a warning-only program still compiles and the
    /// warnings are surfaced via `CompileResult::warnings` / `Compilation::warnings`.
    /// (T252, the `@ReadOnly` partial-guarantee lint, is SIGIL's first warning.)
    pub fn warning(code: DiagnosticCode, message: impl Into<String>, span: Option<Span>) -> Self {
        debug_assert!(
            registry::lookup(code).is_some(),
            "Diagnostic constructed with unknown code `{}` — add it to crates/sigil-compiler/src/diagnostics/registry.rs::CODES",
            code
        );
        Self {
            code,
            severity: Severity::Warning,
            message: message.into(),
            hint: None,
            span,
            source_name: None,
            suggested_edits: None,
        }
    }

    /// Construct a new error diagnostic with a per-call-site `hint` override
    /// that takes precedence over the registry default for this `code`.
    pub fn error_with_hint(
        code: DiagnosticCode,
        message: impl Into<String>,
        span: Option<Span>,
        hint: impl Into<String>,
    ) -> Self {
        let mut diagnostic = Self::error(code, message, span);
        diagnostic.hint = Some(hint.into());
        diagnostic
    }

    /// Attach opt-in machine-applicable fix(es) (a2 / wire schema v2). Normalizes
    /// an empty list to `None` and caps the count at 1 — the a2 contract leaves
    /// multi-edit ordering/overlap to the first site that needs it — so the wire
    /// carries exactly `None` XOR a one-element list, keeping the derived
    /// `PartialEq`/`Eq` and downstream dedup well-defined. Offsets are validated
    /// (bounds + UTF-8 char boundaries against the rendered source) at emission
    /// in [`json::to_json`]; an invalid edit is dropped there, never emitted.
    pub fn with_suggested_edits(mut self, edits: Vec<SuggestedEdit>) -> Self {
        debug_assert!(!edits.is_empty(), "with_suggested_edits called with []");
        debug_assert!(
            edits.len() <= 1,
            "a2 caps suggested_edits at 1 per diagnostic"
        );
        self.suggested_edits = if edits.is_empty() {
            None
        } else {
            Some(edits.into_iter().take(1).collect())
        };
        self
    }

    /// The opt-in machine-applicable fix(es), if any were attached. Validation
    /// and serialization happen in [`json::to_json`].
    pub fn suggested_edits(&self) -> Option<&[SuggestedEdit]> {
        self.suggested_edits.as_deref()
    }

    /// Prepend context to the message, keeping code, severity, span, hint, and
    /// suggested edits intact. For a check that runs the same body under several
    /// configurations (the taint checker's `@Flow` instantiations), this names
    /// WHICH one produced the diagnostic without each site having to thread that
    /// context through its own message.
    pub fn with_message_prefix(mut self, prefix: impl std::fmt::Display) -> Self {
        self.message = format!("{prefix}{}", self.message);
        self
    }

    /// Wall 5 Step 1: construct a new error diagnostic that attributes
    /// to a specific source file. Used by the multi-file driver (M001-M010)
    /// and, after commit #5's SourceId refactor, by every diagnostic that
    /// belongs to a non-primary source in a multi-file project.
    ///
    /// `source_name` should match a [`SourceFile`] passed to
    /// [`Self::render_in_project`]. If the renderer cannot find a match,
    /// it emits a fallback message AND an I010 internal diagnostic per
    /// N6-W5S1 — it never panics and never silently picks the wrong file.
    pub fn error_in_file(
        code: DiagnosticCode,
        message: impl Into<String>,
        span: Option<Span>,
        source_name: impl Into<String>,
    ) -> Self {
        let mut diagnostic = Self::error(code, message, span);
        diagnostic.source_name = Some(source_name.into());
        diagnostic
    }

    /// File-attributed WARNING — the severity-preserving sibling of
    /// `error_in_file`, needed since the parser gained its first warning-tier
    /// diagnostic (P031): the multi-file path's attribution re-wrap must not
    /// silently upgrade a warning to an error.
    pub fn warning_in_file(
        code: DiagnosticCode,
        message: impl Into<String>,
        span: Option<Span>,
        source_name: impl Into<String>,
    ) -> Self {
        let mut diagnostic = Self::warning(code, message, span);
        diagnostic.source_name = Some(source_name.into());
        diagnostic
    }

    pub fn code(&self) -> DiagnosticCode {
        self.code
    }

    pub fn severity(&self) -> Severity {
        self.severity
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn span(&self) -> Option<Span> {
        self.span
    }

    /// Wall 5 Step 1: file-attribution channel set by
    /// [`Self::error_in_file`]. `None` for diagnostics emitted via the
    /// legacy single-source constructors; consumed by
    /// [`Self::render_in_project`].
    pub fn source_name(&self) -> Option<&str> {
        self.source_name.as_deref()
    }

    /// Effective hint: per-call-site override if set, else the registry
    /// default for this code, else `None` (e.g. for the transitional sentinel).
    pub fn hint(&self) -> Option<&str> {
        if let Some(hint) = &self.hint {
            return Some(hint.as_str());
        }
        registry::lookup(self.code).map(|entry| entry.default_hint)
    }

    /// Title from the registry (`None` for unregistered codes such as the
    /// transitional sentinel).
    pub fn title(&self) -> Option<&'static str> {
        registry::lookup(self.code).map(|entry| entry.title)
    }

    pub fn render(&self, source: &SourceFile) -> String {
        match self.span {
            Some(span) => {
                let (line, col) = source.line_col(span.start);
                let line_text = source.line_text(line);
                let caret_width = span.len().clamp(1, 32);
                let padding = " ".repeat(col.saturating_sub(1));
                let carets = "^".repeat(caret_width);

                format!(
                    "error: {}\n --> {}:{}:{}\n  |\n{:>2} | {}\n  | {}{}",
                    self.message,
                    source.name(),
                    line,
                    col,
                    line,
                    line_text,
                    padding,
                    carets,
                )
            }
            None => format!("error: {}", self.message),
        }
    }

    /// Wall 5 Step 1: render this diagnostic against a project's source
    /// set. If `self.source_name` is `Some(name)` and `sources` contains
    /// a [`SourceFile`] whose `name()` matches, render against that
    /// file's text. Otherwise:
    ///
    /// - `source_name == None` → fall back to `default` (preserves
    ///   legacy single-source behavior; byte-equal output for existing
    ///   diagnostics not yet ported to `error_in_file`).
    /// - `source_name == Some(name)` but `name` not in `sources` →
    ///   render with a fallback message that includes the missing
    ///   `name` and the span numeric range. Per N6-W5S1: never panics,
    ///   never silently picks the wrong file. Callers that surface
    ///   diagnostics also produce an I010 internal diagnostic alongside
    ///   (the fallback render alone does not emit I010; the harness
    ///   appends it). The fallback's structure is stable so test
    ///   harnesses can detect it.
    pub fn render_in_project(&self, sources: &[SourceFile], default: &SourceFile) -> String {
        match self.source_name.as_deref() {
            None => self.render(default),
            Some(name) => match sources.iter().find(|s| s.name() == name) {
                Some(matched) => self.render(matched),
                None => match self.span {
                    Some(span) => format!(
                        "error: {}\n --> <unresolved source `{}`>:offset {}..{}\n  | (source-name attribution lost; cf. I010)",
                        self.message, name, span.start, span.end,
                    ),
                    None => format!(
                        "error: {}\n --> <unresolved source `{}`>\n  | (source-name attribution lost; cf. I010)",
                        self.message, name,
                    ),
                },
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct CompileError {
    diagnostics: Vec<Diagnostic>,
    /// Wall 5 Step 1 follow-up: the SourceMap the diagnostics' spans
    /// index into. `None` for errors emitted before a SourceMap is
    /// known (e.g., empty-input rejection in compile_project) or by
    /// legacy callers that haven't been migrated. When `Some(_)`, the
    /// renderer can resolve every span's `source` field back to a
    /// SourceFile and produce file-precise output for ALL diagnostic
    /// codes, not just the new M-prefix family.
    sources: Option<Arc<SourceMap>>,
}

impl CompileError {
    /// Legacy constructor — emits without SourceMap attribution. Spans
    /// inside still carry their `SourceId` from the lexer/parser, but
    /// without a SourceMap the renderer can't resolve them to files.
    /// New callers should use [`Self::with_sources`] when a SourceMap
    /// is available.
    pub fn new(diagnostics: Vec<Diagnostic>) -> Self {
        Self {
            diagnostics,
            sources: None,
        }
    }

    /// Wall 5 Step 1 follow-up: construct an error attached to a
    /// SourceMap. Consumers (CLI, tests) call [`Self::render`] which
    /// uses the map to produce file-precise output.
    pub fn with_sources(diagnostics: Vec<Diagnostic>, sources: Arc<SourceMap>) -> Self {
        Self {
            diagnostics,
            sources: Some(sources),
        }
    }

    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    pub fn into_diagnostics(self) -> Vec<Diagnostic> {
        self.diagnostics
    }

    /// The SourceMap this error's spans index into. `None` for errors
    /// from legacy paths that haven't been migrated.
    pub fn sources(&self) -> Option<&SourceMap> {
        self.sources.as_deref()
    }

    /// Wall 5 Step 1 follow-up: render every diagnostic against the
    /// error's SourceMap, producing file-precise output for ALL codes
    /// (not just the M-prefix family).
    ///
    /// `fallback` is the SourceFile to use when a span's `source` field
    /// is [`crate::span::SourceId::SYNTHETIC`] or when the error has no
    /// attached SourceMap (legacy path). Pass the primary source the
    /// caller has on hand; in single-file mode it's the user's source,
    /// in multi-file mode it's the entry module's source.
    ///
    /// When the SourceMap can resolve a span's `source`, the diagnostic
    /// renders against THAT file's text — fixing wrong-file attribution
    /// for cross-module diagnostics like T155 (cross-module private
    /// call), R004 (cross-ring), E001 (effect propagation).
    pub fn render(&self, fallback: &SourceFile) -> String {
        self.diagnostics
            .iter()
            .map(|d| self.render_one(d, fallback))
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    fn render_one(&self, diagnostic: &Diagnostic, fallback: &SourceFile) -> String {
        // Preferred path: span's source_id resolves in the map.
        if let Some(map) = &self.sources
            && let Some(span) = diagnostic.span()
            && let Some(source) = map.get(span.source)
        {
            return diagnostic.render(source);
        }
        // Legacy fallback: source_name attribution channel (the
        // pre-SourceId path used by the M-prefix codes).
        if let Some(map) = &self.sources
            && let Some(name) = diagnostic.source_name()
            && let Some(source) = map.files().iter().find(|s| s.name() == name)
        {
            return diagnostic.render(source);
        }
        // Final fallback: render against the caller-provided default.
        diagnostic.render(fallback)
    }
}

impl PartialEq for CompileError {
    fn eq(&self, other: &Self) -> bool {
        // Compare diagnostics only; SourceMap equality is identity-based
        // (Arc), which would make two errors with the same diagnostics
        // but different SourceMap instances appear unequal. Tests
        // assert on diagnostics, never on SourceMap identity.
        self.diagnostics == other.diagnostics
    }
}

impl Eq for CompileError {}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "compilation failed with {} diagnostic(s)",
            self.diagnostics.len()
        )
    }
}

impl Error for CompileError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coded_constructor_carries_code_and_registry_hint() {
        let d = Diagnostic::error(codes::T001, "boom", None);
        assert_eq!(d.code(), codes::T001);
        assert_eq!(d.message(), "boom");
        assert_eq!(d.severity(), Severity::Error);
        // T001 is in the registry, so a default hint flows through.
        assert!(d.hint().is_some());
        assert!(d.title().is_some());
    }

    #[test]
    fn per_call_site_hint_overrides_registry() {
        let d = Diagnostic::error_with_hint(codes::T001, "boom", None, "do the other thing");
        assert_eq!(d.hint(), Some("do the other thing"));
    }

    #[test]
    fn with_suggested_edits_stores_a_single_edit() {
        let edit = SuggestedEdit {
            start: 4,
            end: 8,
            replacement: "fuel".to_owned(),
        };
        let d =
            Diagnostic::error(codes::T001, "boom", None).with_suggested_edits(vec![edit.clone()]);
        assert_eq!(d.suggested_edits(), Some([edit].as_slice()));
    }

    #[test]
    #[should_panic(expected = "caps suggested_edits at 1")]
    fn with_suggested_edits_rejects_multiple() {
        // The a2 contract caps at one edit; a second trips the debug_assert.
        let two = vec![
            SuggestedEdit {
                start: 0,
                end: 1,
                replacement: "a".to_owned(),
            },
            SuggestedEdit {
                start: 2,
                end: 3,
                replacement: "b".to_owned(),
            },
        ];
        let _ = Diagnostic::error(codes::T001, "boom", None).with_suggested_edits(two);
    }

    // ── Wall 5 Step 1: source-name plumbing tests ──────────────────────────

    /// `error_in_file` sets the source_name field; bare `error` leaves it None.
    #[test]
    fn error_in_file_carries_source_name() {
        let d = Diagnostic::error_in_file(codes::T001, "boom", None, "lib.sigil");
        assert_eq!(d.source_name(), Some("lib.sigil"));

        let bare = Diagnostic::error(codes::T001, "boom", None);
        assert_eq!(bare.source_name(), None);
    }

    /// N6-W5S1: when `source_name` matches a SourceFile in the project
    /// set, render against THAT file (not the default).
    #[test]
    fn render_in_project_picks_matching_source() {
        let lib = SourceFile::new("lib.sigil", "AAA\nBBB\nCCC\n");
        let main = SourceFile::new("main.sigil", "111\n222\n");
        let span = crate::span::Span::new(4, 7); // spans "BBB" in lib.sigil
        let d = Diagnostic::error_in_file(codes::T001, "msg", Some(span), "lib.sigil");
        let rendered = d.render_in_project(&[lib.clone(), main.clone()], &main);
        assert!(rendered.contains("lib.sigil:2:1"), "rendered: {rendered}");
        assert!(rendered.contains("BBB"), "rendered: {rendered}");
    }

    /// N6-W5S1: bare diagnostics (no source_name) fall back to the
    /// default SourceFile — preserves legacy single-source behavior.
    #[test]
    fn render_in_project_falls_back_to_default_when_no_attribution() {
        let main = SourceFile::new("main.sigil", "abc\n");
        let span = crate::span::Span::new(0, 3);
        let d = Diagnostic::error(codes::T001, "msg", Some(span));
        let rendered = d.render_in_project(std::slice::from_ref(&main), &main);
        // Same output as legacy render(&main).
        assert_eq!(rendered, d.render(&main));
    }

    /// N6-W5S1: when source_name doesn't match any SourceFile in the
    /// set, render a fallback message that references the missing name.
    /// Never panics, never silently picks the wrong file.
    #[test]
    fn render_in_project_emits_fallback_on_unresolved_attribution() {
        let main = SourceFile::new("main.sigil", "abc\n");
        let span = crate::span::Span::new(0, 3);
        let d = Diagnostic::error_in_file(codes::T001, "msg", Some(span), "ghost.sigil");
        let rendered = d.render_in_project(std::slice::from_ref(&main), &main);
        assert!(
            rendered.contains("ghost.sigil"),
            "fallback must name the missing source: {rendered}"
        );
        assert!(
            rendered.contains("I010"),
            "fallback must reference I010 internal-diagnostic code: {rendered}"
        );
        // Span offsets surfaced for debuggability.
        assert!(
            rendered.contains("0..3"),
            "fallback must include span offsets: {rendered}"
        );
    }
}
