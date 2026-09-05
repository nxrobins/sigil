//! Sub-tree parsing macros — Pillar 1 of the Four-Pillar Testing
//! Infrastructure plan.
//!
//! The problem these solve: writing a `#[test]` that exercises a single
//! type-check or refinement helper used to require 8+ lines of manual
//! AST construction:
//!
//! ```rust,ignore
//! let x = path_expr("x");
//! let seven = int_lit(7);
//! let expr = binary(x, BinaryOp::Eq, seven);
//! // ... finally call the function under test on `expr` ...
//! ```
//!
//! Every helper (`path_expr`, `int_lit`, `binary`) is its own
//! maintenance burden, and the test's intent is buried under setup.
//!
//! The three macros in this module let you write the SIGIL source
//! directly:
//!
//! ```rust,ignore
//! let expr = parse_expr!("x == 7");
//! ```
//!
//! and get back a real [`Expr`] produced by the production parser. No
//! manual constructors. Test failures point at the test file, not at
//! parser internals.
//!
//! ## Macros
//!
//! - [`parse_program!`] — parses an entire SIGIL program (top-level
//!   `module ...;` items). Returns [`Program`].
//! - [`parse_expr!`] — parses a single expression. Wraps the snippet
//!   in a minimal `module __test; pub fn _t() { let _v = $src; }` and
//!   extracts the let binding's value. Returns [`Expr`].
//! - [`parse_type!`] — parses a single type expression. Wraps the
//!   snippet in `module __test; pub fn _t(p: $src) {}` and extracts
//!   the parameter's declared type. Returns [`TypeExpr`].
//!
//! All three `panic!` if the wrapped source produces parse errors,
//! with a diagnostic-formatted message that surfaces the underlying
//! issue. Test failures appear at the macro invocation site.

use sigil_compiler::ast::{Expr, Item, Program, Stmt, TypeExpr};
use sigil_compiler::diagnostics::{Diagnostic, Severity};
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;

/// Parse a complete SIGIL program. Returns [`Program`] on success;
/// panics with a formatted diagnostic message on parse error.
///
/// This is the workhorse behind [`parse_program!`]; called directly
/// when a test needs to assert on parser diagnostics rather than
/// guarantee parser success.
///
/// Diagnostic-level warnings and notes are tolerated and discarded;
/// only `Severity::Error` triggers the panic.
pub fn parse_program_or_panic(src: &str) -> Program {
    let source = SourceFile::new("<parse_program! snippet>", src);
    let (program, diagnostics) = parser::parse(&source);
    panic_if_errors(&diagnostics, src);
    program
}

/// Parse a single expression. The snippet is wrapped in a minimal
/// containing function and the inner expression is extracted.
///
/// Panics on parse error (with the original snippet's source attached
/// to the diagnostic message) or if the wrapper assumptions break
/// (which would only happen if the AST shape changes — fix the
/// extractor, don't silently degrade).
pub fn parse_expr_or_panic(src: &str) -> Expr {
    // Wrap the expression as the value of a let binding inside a
    // public function inside a module. `let _v = <src>;` is the
    // minimal surrounding context that the parser accepts for an
    // arbitrary expression.
    //
    // Trailing semicolon on the let — `_v` is allocated to keep the
    // expression an rvalue.
    let wrapped = format!(
        "module __parse_expr_test;\n\
         pub fn __t() {{\n    \
             let _v = {src};\n\
         }}\n"
    );
    let program = parse_program_or_panic(&wrapped);
    let stmt = first_function_first_stmt(&program, src);
    match stmt {
        Stmt::Let(let_stmt) => let_stmt.value.clone(),
        other => panic!(
            "parse_expr!: wrapper assumption broke — expected first statement \
             to be `let _v = ...;` but found {:?}.\nOriginal snippet:\n{src}",
            std::mem::discriminant(other)
        ),
    }
}

/// Parse a single type expression. The snippet is wrapped as the
/// declared type of a function parameter and the inner [`TypeExpr`]
/// is extracted.
///
/// Same panic semantics as [`parse_expr_or_panic`].
pub fn parse_type_or_panic(src: &str) -> TypeExpr {
    // Wrap the type as the annotation on a single function parameter.
    // `fn __t(__p: <src>) {}` is the minimal surrounding context the
    // parser accepts for an arbitrary type expression.
    let wrapped = format!(
        "module __parse_type_test;\n\
         pub fn __t(__p: {src}) {{}}\n"
    );
    let program = parse_program_or_panic(&wrapped);
    let fn_def = first_function(&program, src);
    let param = fn_def.params.first().unwrap_or_else(|| {
        panic!(
            "parse_type!: wrapper assumption broke — expected `__t` to \
             have one parameter.\nOriginal snippet:\n{src}"
        )
    });
    param.ty.clone()
}

// ── Internal helpers ──────────────────────────────────────────────────────

fn panic_if_errors(diagnostics: &[Diagnostic], src: &str) {
    let errors: Vec<&Diagnostic> = diagnostics
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .collect();
    if !errors.is_empty() {
        let formatted: Vec<String> = errors
            .iter()
            .map(|d| format!("  - {}: {}", d.code().as_str(), d.message()))
            .collect();
        panic!(
            "parse macro: snippet failed to parse with {n} error(s):\n{joined}\n\n\
             Original snippet:\n{src}",
            n = errors.len(),
            joined = formatted.join("\n"),
        );
    }
}

fn first_function<'a>(program: &'a Program, src: &str) -> &'a sigil_compiler::ast::FnDef {
    let module = program.modules.first().unwrap_or_else(|| {
        panic!(
            "parse macro: wrapper produced no modules — parser may have \
             accepted a malformed source silently.\nOriginal snippet:\n{src}"
        )
    });
    for item in &module.items {
        if let Item::FnDef(fn_def) = item {
            return fn_def;
        }
    }
    panic!("parse macro: wrapper module contains no `FnDef` item.\nOriginal snippet:\n{src}");
}

fn first_function_first_stmt<'a>(program: &'a Program, src: &str) -> &'a Stmt {
    let fn_def = first_function(program, src);
    fn_def.body.statements.first().unwrap_or_else(|| {
        panic!(
            "parse_expr!: wrapper function body is empty — parser may have \
             swallowed the snippet.\nOriginal snippet:\n{src}"
        )
    })
}

// ── Public macros ─────────────────────────────────────────────────────────

/// Parse an entire SIGIL program. See [module docs](self) for usage.
#[macro_export]
macro_rules! parse_program {
    ($src:expr $(,)?) => {
        $crate::parse::parse_program_or_panic($src)
    };
}

/// Parse a single SIGIL expression. See [module docs](self) for usage.
#[macro_export]
macro_rules! parse_expr {
    ($src:expr $(,)?) => {
        $crate::parse::parse_expr_or_panic($src)
    };
}

/// Parse a single SIGIL type expression. See [module docs](self) for usage.
#[macro_export]
macro_rules! parse_type {
    ($src:expr $(,)?) => {
        $crate::parse::parse_type_or_panic($src)
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use sigil_compiler::ast::{BinaryOp, Expr, Literal};

    #[test]
    fn parse_program_accepts_minimal_module() {
        let prog = parse_program_or_panic("module demo;\npub fn f() -> i64 {\n    return 1;\n}\n");
        assert_eq!(prog.modules.len(), 1, "expected one module");
        assert_eq!(prog.modules[0].name, "demo");
        assert_eq!(
            prog.modules[0].items.len(),
            1,
            "expected one item (the FnDef)"
        );
    }

    #[test]
    fn parse_expr_returns_int_literal() {
        let expr = parse_expr_or_panic("42");
        match expr {
            Expr::Literal(lit_expr) => match lit_expr.literal {
                Literal::Int(v) => assert_eq!(v, 42),
                other => panic!("expected Int literal, got {other:?}"),
            },
            other => panic!("expected Literal expression, got {other:?}"),
        }
    }

    #[test]
    fn parse_expr_returns_binary_op() {
        let expr = parse_expr_or_panic("x == 7");
        match expr {
            Expr::Binary(bin) => assert_eq!(bin.op, BinaryOp::Eq),
            other => panic!("expected Binary expression, got {other:?}"),
        }
    }

    #[test]
    fn parse_expr_handles_nested_arithmetic() {
        let expr = parse_expr_or_panic("1 + 2 * 3");
        // 1 + (2 * 3) — outermost is Add
        match expr {
            Expr::Binary(bin) => assert_eq!(bin.op, BinaryOp::Add),
            other => panic!("expected Binary expression, got {other:?}"),
        }
    }

    #[test]
    fn parse_type_returns_named_type() {
        let ty = parse_type_or_panic("i64");
        // TypeExpr exact shape varies; for this smoke test, just confirm
        // that parsing didn't panic and we got something back.
        let _ = ty;
    }

    #[test]
    fn parse_type_handles_generic_type() {
        // Confirms multi-segment type parsing works through the wrapper.
        let ty = parse_type_or_panic("Result<i64, i64>");
        let _ = ty;
    }

    #[test]
    #[should_panic(expected = "parse macro: snippet failed to parse")]
    fn parse_program_panics_on_garbage() {
        parse_program_or_panic("this is not @@@ valid sigil !!!");
    }

    #[test]
    #[should_panic(expected = "parse macro: snippet failed to parse")]
    fn parse_expr_panics_on_garbage() {
        parse_expr_or_panic("@@@");
    }

    #[test]
    fn macro_form_parse_expr_works() {
        // Compile-time check that the macro re-exports correctly.
        let expr = crate::parse_expr!("1 + 1");
        let _ = expr;
    }

    #[test]
    fn macro_form_parse_program_works() {
        let prog = crate::parse_program!("module m;\npub fn f() {}\n");
        assert_eq!(prog.modules.len(), 1);
    }

    #[test]
    fn macro_form_parse_type_works() {
        let ty = crate::parse_type!("i64");
        let _ = ty;
    }
}
