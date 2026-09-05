//! Method calls and field access on ARBITRARY receiver expressions.
//!
//! `MethodCallExpr.receiver` and `FieldAccessExpr.object` have always been
//! `Box<Expr>`, and the type-checker's Path-specific routing is all guarded
//! `if let Expr::Path(..)` with a general fall-through. The restriction was
//! purely in the parser: `parse_postfix_expr` looped on `?` and `[..]` only,
//! and method calls were recognised earlier, at the PATH level — so the
//! receiver could only ever be a `Path`. A call was therefore never a legal
//! receiver, and `f(x).g()` did not parse.
//!
//! The cost was not theoretical. Across ~32k lines of hand-written SIGIL in
//! `selfhost/` there were ZERO method chains, and the stdlib advertised
//! pipelines in comments (`v.map(f).filter(g).sum()`) that the parser could
//! not accept. Every chain had to be spelled as a ladder of `let` bindings.
//!
//! These tests pin the receiver-position generalisation. They deliberately
//! use methods that already exist (`to_string` on the integer widths,
//! `concat` on `str`) so a failure means the RECEIVER is being rejected, not
//! that the method is missing.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    if let Err(err) = compile_named_module(format!("chain_{label}.sigil"), source) {
        let codes: Vec<String> = err
            .diagnostics()
            .iter()
            .map(|d| format!("{}: {}", d.code().as_str(), d.message()))
            .collect();
        panic!(
            "expected clean compile for {label}, got:\n  {}",
            codes.join("\n  ")
        );
    }
}

#[test]
fn method_call_on_a_call_result() {
    let source = r#"
module main;

fn bump(x: i64) -> i64 {
    return x + 1;
}

fn label() -> str {
    return bump(1).to_string();
}
"#;
    assert_compiles_clean(source, "call_receiver");
}

#[test]
fn two_step_chain() {
    // The shape the stdlib comments advertise: each step's receiver is the
    // previous step's result.
    let source = r#"
module main;

fn bump(x: i64) -> i64 {
    return x + 1;
}

fn label() -> str {
    return bump(1).to_string().concat("!");
}
"#;
    assert_compiles_clean(source, "two_step");
}

#[test]
fn chain_on_a_method_call_receiver() {
    let source = r#"
module main;

fn label(x: i64) -> str {
    return x.to_string().concat("!").concat("?");
}
"#;
    assert_compiles_clean(source, "three_step");
}

#[test]
fn field_access_on_a_call_result() {
    // `FieldAccessExpr.object` is a `Box<Expr>` for the same reason; the
    // parser could not produce a non-Path object either.
    let source = r#"
module main;

record Point { x: i64, y: i64 }

fn origin() -> Point {
    return Point { x: 3, y: 4 };
}

fn get_x() -> i64 {
    return origin().x;
}
"#;
    assert_compiles_clean(source, "field_on_call");
}

#[test]
fn chain_after_an_index() {
    // `[..]` already lived in `parse_postfix_expr`, so an index result must
    // compose with the new `.` arm in the same loop.
    let source = r#"
module main;

fn first_label(arr: [i64; 4]) -> str {
    return arr[0].to_string();
}
"#;
    assert_compiles_clean(source, "index_then_method");
}

/// The historical P001 shape from the Phase-7 iterator epic: `.method`
/// directly after a call whose LAST ARGUMENT is a closure block. The old
/// gotcha ("bind each step to a `let`") predates the receiver-position
/// generalisation; this pins that the closing `}` `)` of a closure-arg
/// call composes with the `.` arm like any other call result.
#[test]
fn chain_after_a_closure_block_argument() {
    let source = r#"
module main;

fn apply(x: i64, f: Fn(i64) -> i64) -> i64 {
    return f(x);
}

fn label() -> str {
    return apply(1, fn(n: i64) -> i64 { return n + 1; }).to_string();
}
"#;
    assert_compiles_clean(source, "closure_arg_then_method");
}

/// A plain (unchained) method call must keep working exactly as before —
/// the `.`-arm addition sits in the same loop as `?` and `[..]`, so a
/// regression here would mean the new arm is stealing receivers from the
/// established path-level parse.
#[test]
fn plain_method_calls_still_work() {
    let source = r#"
module main;

fn label(x: i64) -> str {
    let s = x.to_string();
    return s;
}
"#;
    assert_compiles_clean(source, "plain");
}
