//! Demonstration: sub-tree parsing macros from `sigil-test-utils`.
//!
//! This is the canonical example of the shared sub-tree parsing pattern.
//!
//! ## Before / after
//!
//! **Before** (`crates/sigil-compiler/src/type_check/tests.rs` —
//! `classify_recognizes_path_int_neg_int`):
//!
//! ```rust,ignore
//! fn path_expr(name: &str) -> Expr { /* 9 lines */ }
//! fn int_lit(n: i64) -> Expr { /* 6 lines */ }
//! fn binary(lhs: Expr, op: BinaryOp, rhs: Expr) -> Expr { /* 7 lines */ }
//!
//! #[test]
//! fn classify_recognizes_path_int_neg_int() {
//!     // Each Expr requires manual construction:
//!     let x = path_expr("x");
//!     let seven = int_lit(7);
//!     let expr = binary(x, BinaryOp::Eq, seven);
//!     // ... finally the assertion.
//! }
//! ```
//!
//! **After** (this file):
//!
//! ```rust,ignore
//! use sigil_test_utils::parse_expr;
//!
//! #[test]
//! fn parse_expr_demo_binary() {
//!     let expr = parse_expr!("x == 7");
//!     // ... assertions directly on the produced AST.
//! }
//! ```
//!
//! The macro hands you a real [`Expr`] produced by the production
//! parser — no hand-rolled constructors to maintain, no risk of the
//! test's AST shape drifting from the parser's actual output. The
//! source-level intent ("a binary `==` of x and 7") reads at a glance.
//!
//! ## Coverage
//!
//! The tests below exercise the three macros against a representative
//! set of expression shapes the type-checker cares about, asserting
//! that the produced AST nodes have the expected structure. They are
//! NOT a substitute for the existing internal-helper unit tests
//! (which can stay private to the module under test); they are a
//! *demonstration* of how new tests should be authored.

use sigil_compiler::ast::{BinaryOp, Expr, Literal};
use sigil_test_utils::{parse_expr, parse_program, parse_type};

#[test]
fn parse_expr_demo_int_literal() {
    let expr = parse_expr!("42");
    match expr {
        Expr::Literal(lit) => assert!(matches!(lit.literal, Literal::Int(42))),
        other => panic!("expected Int literal, got {other:?}"),
    }
}

#[test]
fn parse_expr_demo_binary_equality() {
    let expr = parse_expr!("x == 7");
    match expr {
        Expr::Binary(bin) => assert_eq!(bin.op, BinaryOp::Eq),
        other => panic!("expected Binary `==`, got {other:?}"),
    }
}

#[test]
fn parse_expr_demo_nested_arithmetic() {
    // Operator precedence: `1 + 2 * 3` parses as `1 + (2 * 3)`.
    // Outermost expression is therefore Add.
    let expr = parse_expr!("1 + 2 * 3");
    match expr {
        Expr::Binary(bin) => assert_eq!(bin.op, BinaryOp::Add),
        other => panic!("expected Binary `+`, got {other:?}"),
    }
}

#[test]
fn parse_expr_demo_negative_int_literal() {
    // The parser folds a unary minus on an int literal into a
    // negative `Int` literal directly (no Binary(Sub, 0, ...)
    // desugaring at this position). parse_expr! gives the test
    // direct access to the canonical AST shape; if the parser ever
    // changes this folding, this assertion surfaces the change at
    // exactly one site.
    let expr = parse_expr!("-7");
    match expr {
        Expr::Literal(lit) => assert!(matches!(lit.literal, Literal::Int(-7))),
        other => panic!("expected Int(-7) literal, got {other:?}"),
    }
}

#[test]
fn parse_type_demo_machine_int() {
    let ty = parse_type!("i64");
    // TypeExpr internal shape is rich; for the demo we just confirm
    // a non-panic round-trip. Real consumers in PR 2+ will pattern-
    // match on the AST.
    let _ = ty;
}

#[test]
fn parse_type_demo_generic_application() {
    let ty = parse_type!("Result<i64, i64>");
    let _ = ty;
}

#[test]
fn parse_program_demo_minimal_module() {
    let prog = parse_program!(
        "module demo;\n\
         pub fn answer() -> i64 {\n    \
             return 42;\n\
         }\n"
    );
    assert_eq!(prog.modules.len(), 1);
    assert_eq!(prog.modules[0].name, "demo");
    assert_eq!(prog.modules[0].items.len(), 1, "expected one FnDef item");
}

#[test]
fn parse_program_demo_multi_item_module() {
    let prog = parse_program!(
        "module multi;\n\
         pub fn a() -> i64 { return 1; }\n\
         pub fn b() -> i64 { return 2; }\n"
    );
    assert_eq!(prog.modules.len(), 1);
    assert_eq!(prog.modules[0].items.len(), 2);
}
