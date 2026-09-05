//! Integration tests for inclusive integer range patterns in `match`
//! arms (e.g. `match b { 48..=57 => ..., _ => ... }`).
//!
//! Range patterns are the axis-1 expressiveness add that closes the
//! byte-classification cascade in `stdlib::crypto::hex_decode` (see
//! the rewrite in this PR — went from 60+ lines of nested `if`/`else`
//! to 5 match arms). These tests pin three properties of the feature
//! end-to-end through the full compilation pipeline:
//!
//! 1. A range pattern parses, type-checks, lowers to AIR, and emits
//!    wasm cleanly when the bounds are well-formed integers matching
//!    the scrutinee type (compile success).
//! 2. Multiple non-overlapping ranges in the same match compile
//!    cleanly — the AIR layer must chain branch blocks correctly
//!    (the lowering emits two basic blocks per range arm).
//! 3. `lo > hi` is rejected with T190 — see
//!    `tests/fixtures/T190.sigil` for the regression-locked fixture;
//!    this file just sanity-checks that the diagnostic surfaces
//!    through the normal compile path too.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    let result = compile_named_module(format!("match_ranges_{label}.sigil"), source);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

#[test]
fn single_range_arm_compiles() {
    let source = r#"
module main;

fn is_digit(b: i64) -> i64 {
    match b {
        48..=57 => { return 1; },
        _ => { return 0; },
    }
}
"#;
    assert_compiles_clean(source, "single");
}

#[test]
fn multiple_non_overlapping_ranges_compile() {
    // The hex-digit classification pattern that motivated the feature.
    // Three range arms + catch-all; AIR has to chain three pairs of
    // bounds-check basic blocks correctly.
    let source = r#"
module main;

fn hex_nibble(b: i64) -> i64 {
    let mut v: i64 = 0 - 1;
    match b {
        48..=57 => { v = b - 48; },
        65..=70 => { v = b - 55; },
        97..=102 => { v = b - 87; },
        _ => {},
    }
    return v;
}
"#;
    assert_compiles_clean(source, "multiple");
}

#[test]
fn single_value_range_compiles() {
    // `lo == hi` is a degenerate but valid inclusive range — the
    // bounds check evaluates to `scrutinee >= 7 && scrutinee <= 7`,
    // i.e. equality. T190 only fires on `lo > hi`, not `lo == hi`.
    let source = r#"
module main;

fn is_seven(b: i64) -> i64 {
    match b {
        7..=7 => { return 1; },
        _ => { return 0; },
    }
}
"#;
    assert_compiles_clean(source, "single_value");
}

#[test]
fn lo_greater_than_hi_fires_t190() {
    // Sanity check that T190 surfaces through the compile entry point
    // (registry_wired.rs already pins the fixture, but this verifies
    // the diagnostic is emitted under the normal API surface, not
    // only via the registry harness).
    let source = r#"
module main;

fn classify(b: i64) -> i64 {
    match b {
        57..=48 => { return 1; },
        _ => { return 0; },
    }
}
"#;
    let err = compile_named_module("match_ranges_t190.sigil", source)
        .expect_err("57..=48 should be rejected");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"T190"),
        "expected T190 in diagnostics, got: {codes:?}"
    );
}

/// A range pattern's bounds must be integer literals.
///
/// The parser admits `BoolLit | IntLit | StrLit` on both sides of `..=`
/// (parser.rs, `parse_pattern`), but AIR lowers `lo..=hi` to a pair of
/// i64 comparisons and its bound extraction has no representation for a
/// non-integer literal — it coerced them to `0` via a `_ => 0` arm.
///
/// A `str` bound IS `type_compatible` with a `str` scrutinee, so nothing
/// upstream rejected it, and T190 could not help either: that check is
/// gated on `(Literal::Int, Literal::Int)`, so non-integer bounds skipped
/// it entirely.
///
/// What actually happened was NOT a wrong answer: the coerced bound left
/// a `Ptr >= I64` comparison that the wasm emitter refuses, so the build
/// died on `ICE: unsupported binary op GtEq for type Ptr` at
/// `wasm.rs:2349`. Fail-closed — but a compiler panic pointing at the
/// backend is the wrong diagnosis for a plain source-level type error,
/// and the house rule is that an ICE backstop should be UNREACHABLE
/// because some upstream pass fenced it. T282 is that fence.
#[test]
fn str_range_bounds_are_rejected() {
    let source = r#"
module main;

fn classify(s: str) -> i64 {
    match s {
        "a"..="z" => { return 1; },
        _ => { return 0; },
    }
}
"#;
    let err = compile_named_module("match_ranges_str.sigil", source)
        .expect_err(r#""a"..="z" should be rejected, not silently lowered to 0..=0"#);
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"T282"),
        "expected T282 for a str range bound, got: {codes:?}"
    );
}

/// The `bool` twin of `str_range_bounds_are_rejected`. Same parser arm,
/// same AIR fallthrough — `true..=false` became `x >= 0 && x <= 0`.
/// Fixing only the `str` spelling would leave this one live, so it is
/// pinned separately rather than folded into the test above.
#[test]
fn bool_range_bounds_are_rejected() {
    let source = r#"
module main;

fn classify(b: bool) -> i64 {
    match b {
        true..=false => { return 1; },
        _ => { return 0; },
    }
}
"#;
    let err = compile_named_module("match_ranges_bool.sigil", source)
        .expect_err("true..=false should be rejected");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"T282"),
        "expected T282 for a bool range bound, got: {codes:?}"
    );
}

/// A mixed range (`48..="z"`) must be rejected on the offending side
/// rather than sliding through because the *other* bound looks fine.
#[test]
fn mixed_int_and_str_range_bounds_are_rejected() {
    let source = r#"
module main;

fn classify(s: str) -> i64 {
    match s {
        48..="z" => { return 1; },
        _ => { return 0; },
    }
}
"#;
    let err = compile_named_module("match_ranges_mixed_bound.sigil", source)
        .expect_err(r#"48..="z" should be rejected"#);
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"T282"),
        "expected T282 for a mixed range bound, got: {codes:?}"
    );
}

/// Both bounds of `"a"..="z"` are bad, but they share a single span, so
/// the author gets exactly ONE diagnostic rather than two stacked on the
/// same caret. `tests/fixtures/T282.sigil` pins this through the
/// precision harness too; this states the property directly so a future
/// refactor back to per-bound reporting fails here with a readable
/// message instead of only in the multiset comparison.
#[test]
fn a_doubly_bad_range_reports_one_diagnostic_not_two() {
    let source = r#"
module main;

fn classify(s: str) -> i64 {
    match s {
        "a"..="z" => { return 1; },
        _ => { return 0; },
    }
}
"#;
    let err = compile_named_module("match_ranges_one_diag.sigil", source)
        .expect_err("should be rejected");
    let t282: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .filter(|c| *c == "T282")
        .collect();
    assert_eq!(
        t282.len(),
        1,
        "one bad range should yield one T282, got {}",
        t282.len()
    );
}

/// Positive control for the fix: the narrow and unsigned integer widths
/// must KEEP compiling. A fix that rejected every range whose scrutinee
/// is not literally `i64` would pass the three tests above while
/// silently amputating the feature — this is the test that would catch
/// that, so it is deliberately paired with them.
#[test]
fn non_i64_integer_widths_still_accept_ranges() {
    for ty in ["i32", "u32", "i64", "u64"] {
        let source = format!(
            r#"
module main;

fn classify(b: {ty}) -> i64 {{
    match b {{
        48..=57 => {{ return 1; }},
        _ => {{ return 0; }},
    }}
}}
"#
        );
        assert_compiles_clean(&source, &format!("width_{ty}"));
    }
}

#[test]
fn range_arm_after_literal_arm_compiles() {
    // Mixing literal arms and range arms in the same match — the
    // AIR lowering chains different kinds of bounds checks, so a
    // mixed shape exercises the dispatch.
    let source = r#"
module main;

fn classify(b: i64) -> i64 {
    match b {
        0 => { return 0 - 1; },
        48..=57 => { return 1; },
        _ => { return 2; },
    }
}
"#;
    assert_compiles_clean(source, "mixed");
}
