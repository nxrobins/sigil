//! Integration tests for parenthesized expressions and unary `-`
//! negation.
//!
//! Both are pure syntactic polish. Parens let users override the
//! precedence chain without naming an intermediate let binding;
//! unary `-` desugars to `0 - x` at parse time so the AIR / wasm
//! layers don't need a new node kind. Together they kill the two
//! most visible workarounds in the stdlib: parens-via-let-bindings
//! and the `0 - 400`-style negative error literal pattern.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    let result = compile_named_module(format!("parens_neg_{label}.sigil"), source);
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
fn parens_override_precedence() {
    // Without parens, `a + b * c` parses as `a + (b * c)`. With parens,
    // `(a + b) * c` flips the grouping. Verify both shapes compile.
    let source = r#"
module main;

fn boot() -> i64 {
    let a: i64 = 2;
    let b: i64 = 3;
    let c: i64 = 4;
    let natural: i64 = a + b * c;
    let grouped: i64 = (a + b) * c;
    return natural + grouped;
}
"#;
    assert_compiles_clean(source, "prec_override");
}

#[test]
fn nested_parens() {
    let source = r#"
module main;

fn boot() -> i64 {
    let x: i64 = ((1 + 2) * (3 + 4));
    return x;
}
"#;
    assert_compiles_clean(source, "nested");
}

#[test]
fn parens_around_bit_op() {
    // Real-world use case: `(p << 32) | l` to make the abi.sigil
    // packing read more explicitly even though the precedence
    // already gives the right grouping.
    let source = r#"
module main;

fn pack(p: i64, l: i64) -> i64 {
    return (p << 32) | l;
}
"#;
    assert_compiles_clean(source, "bitop_paren");
}

#[test]
fn unary_minus_on_literal() {
    let source = r#"
module main;

fn boot() -> i64 {
    let x: i64 = -5;
    let y: i64 = -400;
    return x + y;
}
"#;
    assert_compiles_clean(source, "neg_lit");
}

#[test]
fn unary_minus_on_variable() {
    let source = r#"
module main;

fn negate(x: i64) -> i64 {
    return -x;
}
"#;
    assert_compiles_clean(source, "neg_var");
}

#[test]
fn double_unary_minus() {
    // `--x` should parse as `0 - (0 - x)` == `x`. Verify the parser
    // doesn't choke on the recursive prefix.
    let source = r#"
module main;

fn boot(x: i64) -> i64 {
    return --x;
}
"#;
    assert_compiles_clean(source, "double_neg");
}

#[test]
fn unary_minus_with_arithmetic() {
    // Precedence: unary `-` binds tighter than `+` / `-`, so
    // `a - -b` parses as `a - (-b)` (which equals `a + b`).
    let source = r#"
module main;

fn boot(a: i64, b: i64) -> i64 {
    return a - -b;
}
"#;
    assert_compiles_clean(source, "neg_arith");
}

#[test]
fn negative_literal_pattern() {
    // Negative integer literals as match patterns. Without this, the
    // user had to write `match x { _ if x < 0 => ... }` for any
    // negative-handling shape.
    let source = r#"
module main;

fn classify(x: i64) -> i64 {
    match x {
        -1 => { return 100; },
        0 => { return 0; },
        _ => { return 1; },
    }
}
"#;
    assert_compiles_clean(source, "neg_pat");
}

#[test]
fn negative_range_pattern() {
    // `-5..=5` — negative lower bound, positive upper. Tests that
    // the helper `parse_pattern_literal` is used for both sides.
    let source = r#"
module main;

fn in_window(x: i64) -> i64 {
    match x {
        -5..=5 => { return 1; },
        _ => { return 0; },
    }
}
"#;
    assert_compiles_clean(source, "neg_range");
}

#[test]
fn fully_negative_range_pattern() {
    // Both bounds negative. The T190 lo > hi check should still
    // fire correctly on the actual signed values.
    let source = r#"
module main;

fn in_negative_window(x: i64) -> i64 {
    match x {
        -10..=-5 => { return 1; },
        _ => { return 0; },
    }
}
"#;
    assert_compiles_clean(source, "neg_neg_range");
}

#[test]
fn parens_in_match_arm() {
    // Parens inside an arm body. Just verifies the parser doesn't
    // get confused between the match's brace structure and primary
    // paren parsing.
    let source = r#"
module main;

fn boot(b: i64) -> i64 {
    match b {
        0 => { return (1 + 2) * 3; },
        _ => { return 0; },
    }
}
"#;
    assert_compiles_clean(source, "paren_arm");
}

#[test]
fn negative_lo_gt_hi_still_fires_t190() {
    // Sanity: the lo > hi check still works on negative ranges.
    // `-3..=-5` is unsatisfiable; should emit T190.
    let source = r#"
module main;

fn classify(x: i64) -> i64 {
    match x {
        -3..=-5 => { return 1; },
        _ => { return 0; },
    }
}
"#;
    let err = compile_named_module("parens_neg_t190.sigil", source)
        .expect_err("-3..=-5 should be rejected");
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
