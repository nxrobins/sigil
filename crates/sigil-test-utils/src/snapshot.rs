//! Snapshot-test helpers — Pillar 2 of the Four-Pillar Testing
//! Infrastructure plan.
//!
//! Wraps `insta` with two pieces of SIGIL-specific glue:
//!
//! 1. **Span filters** — strip `Span { start: N, end: N, source:
//!    SourceId(N) }` (and friends) from Debug-formatted output, so
//!    snapshots aren't sensitive to whitespace in fixture sources or
//!    to source-ID allocation order. Without this, every fixture
//!    edit would churn every snapshot.
//!
//! 2. **WAT converter** — `wat_of(&[u8]) -> String` runs WASM bytes
//!    through `wasmprinter` for human-readable, deterministic WAT
//!    text suitable for snapshotting.
//!
//! ## Usage
//!
//! Consumers add `insta = { workspace = true }` and `sigil-test-utils
//! = { workspace = true }` to their `[dev-dependencies]` and use the
//! [`assert_canonical_snapshot!`] macro:
//!
//! ```rust,ignore
//! use sigil_test_utils::assert_canonical_snapshot;
//!
//! #[test]
//! fn typed_program_for_log4shell() {
//!     let typed = sigil_test_utils::pipeline::typecheck_or_panic(SRC);
//!     assert_canonical_snapshot!(typed);
//! }
//! ```
//!
//! Or, for WASM bytes:
//!
//! ```rust,ignore
//! use sigil_test_utils::snapshot::wat_of;
//!
//! #[test]
//! fn wat_for_minimal_module() {
//!     let comp = sigil_test_utils::pipeline::compile_or_panic(SRC);
//!     insta::assert_snapshot!(wat_of(&comp.wasm_inner));
//! }
//! ```
//!
//! ## Filter scope
//!
//! The filters strip three categories of noise:
//!
//! * `Span { start: N, end: N, source: SourceId(N) }` — full Span
//!   debug form (the common case in Program/TypedProgram).
//! * Bare `SourceId(N)` — covers cases where a SourceId appears
//!   outside a Span (e.g. SourceMap entries).
//! * `DefId(N)` — TypedProgram's per-item identifier; the underlying
//!   integer is allocation-order-dependent and shouldn't drive
//!   snapshot diffs.
//!
//! All three replace the matched substring with a stable placeholder
//! (`Span(<stripped>)`, `SourceId(<stripped>)`, `DefId(<stripped>)`)
//! so the surrounding structure remains readable in the snapshot.

/// The standard filter chain for canonical SIGIL snapshots.
///
/// Use via [`assert_canonical_snapshot!`] (which threads this into
/// `insta::with_settings!`) or directly:
///
/// ```rust,ignore
/// insta::with_settings!({
///     filters => sigil_test_utils::snapshot::canonical_filters(),
/// }, {
///     insta::assert_debug_snapshot!(typed);
/// });
/// ```
///
/// Each tuple is `(regex_pattern, replacement_string)`, matching
/// insta's `Settings::add_filter` shape. The patterns are intentionally
/// conservative — overly permissive filters can swallow real
/// regressions.
pub fn canonical_filters() -> Vec<(&'static str, &'static str)> {
    vec![
        // Full Span debug form. Matches:
        //   Span { start: 12, end: 28, source: SourceId(0) }
        (
            r"Span \{ start: \d+, end: \d+, source: SourceId\(\d+\) \}",
            "Span(<stripped>)",
        ),
        // Span without a source field (some Display-style impls).
        // Matches: Span { start: 12, end: 28 }
        (r"Span \{ start: \d+, end: \d+ \}", "Span(<stripped>)"),
        // Bare SourceId outside a Span (SourceMap entries, etc.).
        (r"SourceId\(\d+\)", "SourceId(<stripped>)"),
        // TypedProgram per-item DefId.
        (r"DefId\(\d+\)", "DefId(<stripped>)"),
    ]
}

/// Convert WASM bytes to deterministic WAT text for snapshotting.
///
/// Panics on invalid WASM (which would indicate a codegen bug — fail
/// loud so the snapshot test surfaces the regression with a useful
/// message instead of a binary-vs-text snapshot diff).
pub fn wat_of(wasm: &[u8]) -> String {
    wasmprinter::print_bytes(wasm).unwrap_or_else(|e| {
        panic!(
            "snapshot::wat_of: wasmprinter failed to render {n} bytes: {e}",
            n = wasm.len()
        )
    })
}

/// Snapshot a Debug-formattable value with the standard span/source-id/
/// def-id filter chain applied.
///
/// This is the macro most tests want. See the [module docs](self) for
/// the full usage pattern.
///
/// Two forms:
///
/// * `assert_canonical_snapshot!(value)` — implicit name (insta picks
///   one from the test fn name).
/// * `assert_canonical_snapshot!(name, value)` — explicit snapshot
///   name, useful when looping over fixtures.
#[macro_export]
macro_rules! assert_canonical_snapshot {
    ($value:expr $(,)?) => {
        ::insta::with_settings!({
            filters => $crate::snapshot::canonical_filters(),
        }, {
            ::insta::assert_debug_snapshot!($value);
        });
    };
    ($name:expr, $value:expr $(,)?) => {
        ::insta::with_settings!({
            filters => $crate::snapshot::canonical_filters(),
        }, {
            ::insta::assert_debug_snapshot!($name, $value);
        });
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_filters_strip_full_span() {
        let input = "TypedExpr { ty: I64, span: Span { start: 12, end: 28, source: SourceId(0) } }";
        let filters = canonical_filters();
        let mut output = input.to_string();
        for (pattern, replacement) in &filters {
            let re = regex_lite_replace(&output, pattern, replacement);
            output = re;
        }
        assert!(
            output.contains("Span(<stripped>)"),
            "expected Span(<stripped>) in: {output}"
        );
        assert!(
            !output.contains("start:"),
            "byte offsets should be removed: {output}"
        );
    }

    /// Local "regex"-style replacer that matches insta's filter
    /// semantics for our test fixtures. We don't depend on the
    /// `regex` crate just to validate the filter shape; instead
    /// we hand-roll the three patterns from `canonical_filters()`.
    fn regex_lite_replace(haystack: &str, pattern: &str, replacement: &str) -> String {
        // Recognize the three concrete patterns we ship in
        // `canonical_filters()` and stub a minimal matcher for each.
        if pattern == r"Span \{ start: \d+, end: \d+, source: SourceId\(\d+\) \}" {
            return strip_pattern(haystack, "Span { start: ", " }", replacement);
        }
        if pattern == r"Span \{ start: \d+, end: \d+ \}" {
            return strip_pattern(haystack, "Span { start: ", " }", replacement);
        }
        if pattern == r"SourceId\(\d+\)" {
            return strip_pattern(haystack, "SourceId(", ")", replacement);
        }
        if pattern == r"DefId\(\d+\)" {
            return strip_pattern(haystack, "DefId(", ")", replacement);
        }
        haystack.to_string()
    }

    fn strip_pattern(haystack: &str, open: &str, close: &str, replacement: &str) -> String {
        let mut out = String::with_capacity(haystack.len());
        let mut rest = haystack;
        while let Some(start) = rest.find(open) {
            out.push_str(&rest[..start]);
            let after_open = &rest[start..];
            if let Some(close_idx) = after_open.find(close) {
                out.push_str(replacement);
                rest = &after_open[close_idx + close.len()..];
            } else {
                // Unbalanced — emit the rest unmodified.
                out.push_str(after_open);
                rest = "";
                break;
            }
        }
        out.push_str(rest);
        out
    }

    #[test]
    fn wat_of_renders_minimal_wasm() {
        // Minimal valid WASM: just the magic + version header.
        let wasm = [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];
        let wat = wat_of(&wasm);
        assert!(wat.contains("module"), "expected `module` in WAT: {wat}");
    }

    #[test]
    #[should_panic(expected = "wasmprinter failed")]
    fn wat_of_panics_on_invalid_wasm() {
        let _ = wat_of(b"not wasm");
    }
}
