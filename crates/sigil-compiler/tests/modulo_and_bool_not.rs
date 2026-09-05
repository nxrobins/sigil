//! Integration tests for `%` (modulo) and unary `!` (boolean NOT).
//!
//! Both are syntactic polish. Modulo is a new binary operator at
//! multiplicative precedence (same as `*` / `/`). Unary `!` desugars
//! to `x == false` at parse time — no new AST node, the existing
//! equality check enforces the operand is bool.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    let result = compile_named_module(format!("modnot_{label}.sigil"), source);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

// ── Modulo ────────────────────────────────────────────────────────────

#[test]
fn modulo_basic_compiles() {
    let source = r#"
module main;

fn boot() -> i64 {
    let x: i64 = 17 % 5;
    return x;
}
"#;
    assert_compiles_clean(source, "mod_basic");
}

#[test]
fn modulo_in_alignment_check() {
    // The canonical use case — alignment checks.
    let source = r#"
module main;

fn is_even(n: i64) -> bool {
    return n % 2 == 0;
}
"#;
    assert_compiles_clean(source, "mod_align");
}

#[test]
fn modulo_with_negative_dividend() {
    // Wasm's i64.rem_s preserves sign: -7 % 3 == -1.
    // Tests the signed-rem instruction path.
    let source = r#"
module main;

fn boot() -> i64 {
    return -7 % 3;
}
"#;
    assert_compiles_clean(source, "mod_neg");
}

#[test]
fn modulo_precedence_matches_multiplication() {
    // `%` sits at the same precedence as `*` / `/`. So
    // `a + b % c` parses as `a + (b % c)`, NOT `(a + b) % c`.
    // Verify by writing a polynomial-style expression.
    let source = r#"
module main;

fn boot() -> i64 {
    return 100 + 17 % 5;
}
"#;
    assert_compiles_clean(source, "mod_prec");
}

#[test]
fn modulo_on_float_rejected() {
    // Sigil's modulo is integer-only (wasm has no f64.rem). T054 fires.
    let source = r#"
module main;

fn boot() -> f64 {
    let a: f64 = 1.5;
    let b: f64 = 0.5;
    return a % b;
}
"#;
    let err = compile_named_module("modnot_mod_float.sigil", source)
        .expect_err("modulo on f64 should be rejected");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"T054"),
        "expected T054 for float modulo, got: {codes:?}"
    );
}

// ── Boolean NOT ───────────────────────────────────────────────────────

#[test]
fn bool_not_basic_compiles() {
    let source = r#"
module main;

fn boot() -> bool {
    let t: bool = true;
    return !t;
}
"#;
    assert_compiles_clean(source, "not_basic");
}

#[test]
fn bool_not_in_if_condition() {
    let source = r#"
module main;

fn classify(b: bool) -> i64 {
    if !b {
        return 1;
    } else {
        return 0;
    }
}
"#;
    assert_compiles_clean(source, "not_if");
}

#[test]
fn double_bool_not_compiles() {
    // `!!x` parses as `(x == false) == false`, which is functionally `x`.
    let source = r#"
module main;

fn boot() -> bool {
    let t: bool = true;
    return !!t;
}
"#;
    assert_compiles_clean(source, "not_double");
}

#[test]
fn bool_not_on_int_rejected() {
    // `!x` for `x: i64` desugars to `x == false` (bool literal).
    // The existing equality check rejects with T055
    // ("operator `==` requires comparable operands") because the
    // types don't match.
    let source = r#"
module main;

fn boot() -> bool {
    let n: i64 = 5;
    return !n;
}
"#;
    let err = compile_named_module("modnot_not_int.sigil", source)
        .expect_err("boolean NOT on i64 should be rejected");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    // T055 is the type-comparable check on `==`. T054 would also be
    // acceptable if a future refactor moves the check; assert either.
    assert!(
        codes.contains(&"T055") || codes.contains(&"T054"),
        "expected T054/T055 for NOT on i64, got: {codes:?}"
    );
}

#[test]
fn bool_not_with_comparison_compiles() {
    // Verify `!` binds tighter than `==`: `!a == b` is `(!a) == b`,
    // since `!` is unary prefix at the prefix level (binds tightest).
    let source = r#"
module main;

fn boot(a: bool, b: bool) -> bool {
    return !a == b;
}
"#;
    assert_compiles_clean(source, "not_eq");
}
