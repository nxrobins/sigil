//! Compile-level tests for place-expression assignment (lvalues).
//!
//! PR-1a makes the left side of `=` a *place expression* — `place := ident
//! | place.field | place[index]` — rather than a bare local. This file
//! covers the type-checker's side of the feature: the lvalue whitelist
//! (T243), root-binding mutability (T042), linearity preservation (T043),
//! value/place type compatibility, and the parser's single-evaluation
//! contract (CM2). Runtime round-trips and the out-of-bounds write trap
//! (CM1) live in `crates/sigil-runtime/tests/place_assignment_runtime.rs`,
//! which can link the wasm executor.

use sigil_compiler::ast::{AssignStmt, BinaryOp, Expr, Item, Stmt};
use sigil_compiler::compile_named_module;
use sigil_test_utils::parse_program;

fn codes_of(source: &str, label: &str) -> Vec<String> {
    match compile_named_module(format!("place_{label}.sigil"), source) {
        Ok(_) => Vec::new(),
        Err(err) => err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn assert_compiles_clean(source: &str, label: &str) {
    let codes = codes_of(source, label);
    assert!(
        codes.is_empty(),
        "expected clean compile for {label}, got: {codes:?}"
    );
}

fn assert_rejected_with(source: &str, label: &str, code: &str) {
    let codes = codes_of(source, label);
    assert!(
        codes.iter().any(|c| c == code),
        "expected {code} for {label}, got: {codes:?}"
    );
}

// ── Positive: every place form compiles ──────────────────────────────

#[test]
fn record_field_write_compiles() {
    let source = r#"
module main;
record Point { x: i64, y: i64 }
fn boot() -> i64 {
    let mut p = Point { x: 3, y: 4 };
    p.x = 10;
    return p.x;
}
"#;
    assert_compiles_clean(source, "field_write");
}

#[test]
fn nested_field_write_compiles() {
    let source = r#"
module main;
record Inner { v: i64 }
record Outer { a: Inner, b: Inner }
fn boot() -> i64 {
    let mut o = Outer { a: Inner { v: 1 }, b: Inner { v: 2 } };
    o.a.v = 99;
    return o.a.v;
}
"#;
    assert_compiles_clean(source, "nested_field");
}

#[test]
fn array_element_write_compiles() {
    // The first-ever source-level producer of a `StoreDynamic` AIR op.
    let source = r#"
module main;
fn boot() -> i64 {
    let mut arr = [10, 20, 30];
    arr[1] = 99;
    return arr[1];
}
"#;
    assert_compiles_clean(source, "array_write");
}

#[test]
fn field_compound_assign_compiles() {
    let source = r#"
module main;
record Point { x: i64, y: i64 }
fn boot() -> i64 {
    let mut p = Point { x: 3, y: 4 };
    p.x += 7;
    return p.x;
}
"#;
    assert_compiles_clean(source, "field_compound");
}

#[test]
fn index_compound_assign_compiles() {
    let source = r#"
module main;
fn boot() -> i64 {
    let mut arr = [10, 20, 30];
    arr[1] += 5;
    return arr[1];
}
"#;
    assert_compiles_clean(source, "index_compound");
}

// ── CM3 / T243: the lvalue whitelist ─────────────────────────────────

#[test]
fn assign_to_call_result_rejected_t243() {
    let source = r#"
module main;
fn f() -> i64 { return 1; }
fn boot() -> i64 {
    f() = 5;
    return 0;
}
"#;
    assert_rejected_with(source, "call_lhs", "T243");
}

#[test]
fn assign_to_arithmetic_rejected_t243() {
    // `a + b` is parsed as the place (a Binary expr — `=` is not an
    // operator, so `parse_expr` stops before it), then the trailing `=`
    // makes it an assignment target. A Binary is not a place → T243.
    let source = r#"
module main;
fn boot(a: i64, b: i64) -> i64 {
    a + b = 5;
    return 0;
}
"#;
    assert_rejected_with(source, "arith_lhs", "T243");
}

#[test]
fn assign_to_literal_rejected_t243() {
    let source = r#"
module main;
fn boot() -> i64 {
    1 = 5;
    return 0;
}
"#;
    assert_rejected_with(source, "literal_lhs", "T243");
}

// ── CM4 / T043: linearity preserved by the rewritten check_assign ────

#[test]
fn cap_local_reassign_still_t043() {
    // A cap-typed local remains non-reassignable through the new place
    // path. (Cap-bearing *fields*/*elements* are unreachable here — T183
    // / T186 reject cap-typed record fields and array elements at
    // declaration — so the bare-local case is the live linearity test.)
    let source = r#"
module main;
cap type Fuel { burn }
fn boot(seed: Fuel) -> i64 {
    let mut f: Fuel = seed;
    f = seed;
    return 0;
}
"#;
    assert_rejected_with(source, "cap_reassign", "T043");
}

// ── T042: the root binding must be `let mut` ─────────────────────────

// ── T042 gates REBINDING, not write-through ──────────────────────────
//
// SIGIL records/arrays are heap pointers (reference semantics). A
// field/element store writes *through* the binding without re-pointing
// it, so it does NOT require `let mut` — only a bare-local reassignment
// (which re-points the name) does. (Opt-in immutability is a future
// `@Frozen`/`@ReadOnly` capability: caps gate mutation, `mut` gates
// rebinding.)

#[test]
fn field_write_through_immutable_binding_compiles() {
    // `p` is not `mut`, but writing *through* it (mutating the heap record
    // it points to) is not rebinding — so it is allowed.
    let source = r#"
module main;
record Point { x: i64, y: i64 }
fn boot() -> i64 {
    let p = Point { x: 3, y: 4 };
    p.x = 10;
    return p.x;
}
"#;
    assert_compiles_clean(source, "writethrough_field");
}

#[test]
fn index_write_through_immutable_binding_compiles() {
    let source = r#"
module main;
fn boot() -> i64 {
    let arr = [10, 20, 30];
    arr[1] = 99;
    return arr[1];
}
"#;
    assert_compiles_clean(source, "writethrough_index");
}

#[test]
fn bare_local_rebind_still_requires_mut_t042() {
    // The complement: re-pointing the NAME (not writing through it) still
    // needs `let mut`. This is what `mut` actually controls.
    let source = r#"
module main;
fn boot() -> i64 {
    let x: i64 = 5;
    x = 10;
    return x;
}
"#;
    assert_rejected_with(source, "rebind_immut", "T042");
}

// ── Value/place type compatibility ───────────────────────────────────

#[test]
fn field_type_mismatch_rejected() {
    let source = r#"
module main;
record Point { x: i64, y: i64 }
fn boot() -> i64 {
    let mut p = Point { x: 1, y: 2 };
    let b: bool = true;
    p.x = b;
    return 0;
}
"#;
    // bool assigned to an i64 field — the assignment-compatibility gate
    // fires (T045 class). We assert it is rejected at all and that the
    // place machinery did not silently accept a type-confused write.
    let codes = codes_of(source, "field_mismatch");
    assert!(
        codes.iter().any(|c| c == "T045"),
        "expected T045 for bool→i64 field write, got: {codes:?}"
    );
}

// ── CM2: parser single-evaluation contract ───────────────────────────
//
// A FIELD/INDEX compound `place op= rhs` must keep `op` and an un-cloned
// place `target` (load-op-store happens once at AIR). A LOCAL compound
// `x op= rhs` desugars to `x = x op rhs` (op = None, Binary value) — a
// local is free to re-read, so this stays byte-identical with history.

fn first_assign(source: &str) -> AssignStmt {
    let prog = parse_program!(source);
    for item in &prog.modules[0].items {
        if let Item::FnDef(f) = item {
            for stmt in &f.body.statements {
                if let Stmt::Assign(a) = stmt {
                    return a.clone();
                }
            }
        }
    }
    panic!("no assignment statement found in source");
}

#[test]
fn index_compound_is_not_desugared() {
    let a = first_assign(
        "module m;\nfn f() -> i64 {\n    let mut arr = [1, 2, 3];\n    let i: i64 = 0;\n    arr[i] += 1;\n    return 0;\n}\n",
    );
    assert_eq!(
        a.op,
        Some(BinaryOp::Add),
        "index compound must retain `op` (no parse-time desugar)"
    );
    assert!(
        matches!(a.target, Expr::Index(_)),
        "index compound target must stay an Index place, not a cloned Binary; got {:?}",
        a.target
    );
    // And the RHS is the bare operand, NOT `arr[i] + 1` — i.e. the
    // subscript appears exactly once in the AST.
    assert!(
        matches!(a.value, Expr::Literal(_)),
        "index compound value must be the bare rhs operand; got {:?}",
        a.value
    );
}

#[test]
fn field_compound_is_not_desugared() {
    let a = first_assign(
        "module m;\nrecord P { x: i64 }\nfn f() -> i64 {\n    let mut p = P { x: 0 };\n    p.x += 1;\n    return 0;\n}\n",
    );
    assert_eq!(a.op, Some(BinaryOp::Add), "field compound must retain `op`");
    assert!(
        matches!(a.target, Expr::Path(_) | Expr::FieldAccess(_)),
        "field compound target must stay a place; got {:?}",
        a.target
    );
}

#[test]
fn local_compound_is_desugared() {
    let a = first_assign(
        "module m;\nfn f() -> i64 {\n    let mut x: i64 = 0;\n    x += 1;\n    return x;\n}\n",
    );
    assert_eq!(
        a.op, None,
        "local compound must desugar to `x = x op rhs` (op = None)"
    );
    assert!(
        matches!(a.value, Expr::Binary(_)),
        "local compound value must be the desugared Binary; got {:?}",
        a.value
    );
}
