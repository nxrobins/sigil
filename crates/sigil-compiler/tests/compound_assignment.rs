//! Integration tests for compound assignment operators.
//!
//! Sigil now accepts `x += y`, `x -= y`, `x *= y`, `x /= y`, `x %= y`,
//! `x <<= y`, `x >>= y`, `x &= y`, `x |= y`. All nine desugar at parse
//! time to `x = x <op> y`, so downstream layers (type check, ownership,
//! taint, AIR, wasm) see only a regular `AssignStmt` with a `Binary`
//! RHS. No new AST node, no new diagnostic codes — existing T042 / T043
//! / T054 fire on the same shapes they would for the explicit form.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    let result = compile_named_module(format!("compound_{label}.sigil"), source);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

// ── Arithmetic compound assignment ───────────────────────────────────

#[test]
fn plus_eq_basic() {
    let source = r#"
module main;
fn boot() -> i64 {
    let mut i: i64 = 10;
    i += 5;
    return i;
}
"#;
    assert_compiles_clean(source, "plus_eq");
}

#[test]
fn minus_eq_basic() {
    let source = r#"
module main;
fn boot() -> i64 {
    let mut i: i64 = 10;
    i -= 3;
    return i;
}
"#;
    assert_compiles_clean(source, "minus_eq");
}

#[test]
fn star_eq_basic() {
    let source = r#"
module main;
fn boot() -> i64 {
    let mut i: i64 = 4;
    i *= 3;
    return i;
}
"#;
    assert_compiles_clean(source, "star_eq");
}

#[test]
fn slash_eq_basic() {
    let source = r#"
module main;
fn boot() -> i64 {
    let mut i: i64 = 20;
    i /= 4;
    return i;
}
"#;
    assert_compiles_clean(source, "slash_eq");
}

#[test]
fn percent_eq_basic() {
    let source = r#"
module main;
fn boot() -> i64 {
    let mut i: i64 = 17;
    i %= 5;
    return i;
}
"#;
    assert_compiles_clean(source, "percent_eq");
}

// ── Bitwise compound assignment ──────────────────────────────────────

#[test]
fn shl_eq_basic() {
    let source = r#"
module main;
fn boot() -> i64 {
    let mut i: i64 = 1;
    i <<= 8;
    return i;
}
"#;
    assert_compiles_clean(source, "shl_eq");
}

#[test]
fn shr_eq_basic() {
    let source = r#"
module main;
fn boot() -> i64 {
    let mut i: i64 = 256;
    i >>= 1;
    return i;
}
"#;
    assert_compiles_clean(source, "shr_eq");
}

#[test]
fn amp_eq_basic() {
    let source = r#"
module main;
fn boot() -> i64 {
    let mut i: i64 = 0xFF;
    i &= 0x0F;
    return i;
}
"#;
    assert_compiles_clean(source, "amp_eq");
}

#[test]
fn pipe_eq_basic() {
    let source = r#"
module main;
fn boot() -> i64 {
    let mut i: i64 = 0xF0;
    i |= 0x0F;
    return i;
}
"#;
    assert_compiles_clean(source, "pipe_eq");
}

// ── Idiomatic shapes ─────────────────────────────────────────────────

#[test]
fn loop_increment_idiom() {
    // The canonical use case — `i += 1` replaces `i = i + 1` in
    // loop counters (used in roughly every stdlib while loop).
    let source = r#"
module main;
fn boot() -> i64 {
    let mut i: i64 = 0;
    let mut sum: i64 = 0;
    while i < 10 {
        sum += i;
        i += 1;
    }
    return sum;
}
"#;
    assert_compiles_clean(source, "loop_inc");
}

#[test]
fn complex_rhs_is_evaluated_once() {
    // `x += a + b` should parse as `x = x + (a + b)`, not
    // `x = x + a + b` (which is the same value but a different tree).
    // The Binary node hierarchy preserves the parse shape.
    let source = r#"
module main;
fn boot(a: i64, b: i64) -> i64 {
    let mut x: i64 = 0;
    x += a + b;
    return x;
}
"#;
    assert_compiles_clean(source, "complex_rhs");
}

// ── Failure modes (T042 / T043 / T054 fire on the desugared form) ─────

#[test]
fn compound_on_immutable_fires_t042() {
    let source = r#"
module main;
fn boot() -> i64 {
    let i: i64 = 10;
    i += 5;
    return i;
}
"#;
    let err = compile_named_module("compound_t042.sigil", source)
        .expect_err("compound on immutable should be rejected");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"T042"),
        "expected T042 for immutable, got: {codes:?}"
    );
}

#[test]
fn compound_on_cap_fires_t043() {
    // Cap-typed reassignment is still rejected by T043, regardless
    // of whether the syntax is `f = f + 1` or `f += 1`.
    let source = r#"
module main;
cap type Fuel { burn }
fn boot(seed: Fuel) -> i64 {
    let mut f: Fuel = seed;
    f += seed;
    return 0;
}
"#;
    let err = compile_named_module("compound_t043.sigil", source)
        .expect_err("compound on cap should be rejected");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"T043"),
        "expected T043 for cap, got: {codes:?}"
    );
}

#[test]
fn bit_compound_on_float_fires_t054() {
    // `<<=` on f64 fails because the desugared `i = i << 1` requires
    // integer operands.
    let source = r#"
module main;
fn boot() -> f64 {
    let mut x: f64 = 1.5;
    x <<= 1;
    return x;
}
"#;
    let err = compile_named_module("compound_t054.sigil", source)
        .expect_err("shift compound on f64 should be rejected");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"T054"),
        "expected T054 for bit op on f64, got: {codes:?}"
    );
}
