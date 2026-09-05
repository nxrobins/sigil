//! `else if` chains.
//!
//! `parse_if_statement` consumed `else` and then demanded a braced block, so
//! `else if` did not parse at all — there were ZERO occurrences of it in any
//! `.sigil` source in the repository, and every multi-way branch was written
//! as a hand-nested `} else { if … } }` pyramid.
//!
//! It desugars to `else { if … }`: no new AST node, and the `IfStmt`
//! three-child shape the parser-differential flattener depends on is
//! unchanged.
//!
//! The depth test is the load-bearing one. The desugar recurses through
//! `parse_if_statement` directly rather than through `parse_braced_block`,
//! so without an explicit guard a long chain would recurse once per link and
//! overflow the native stack — reopening the O(N)-recursion parser DoS that
//! was already closed for if/while/match. `else if` is the most natural way
//! to write a very long chain, so it must not inherit that hole.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    if let Err(err) = compile_named_module(format!("elseif_{label}.sigil"), source) {
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
fn single_else_if_compiles() {
    let source = r#"
module main;

fn sign(n: i64) -> i64 {
    if n > 0 {
        return 1;
    } else if n < 0 {
        return 0 - 1;
    } else {
        return 0;
    }
}
"#;
    assert_compiles_clean(source, "single");
}

#[test]
fn else_if_chain_compiles() {
    let source = r#"
module main;

fn bucket(n: i64) -> i64 {
    if n < 10 {
        return 0;
    } else if n < 100 {
        return 1;
    } else if n < 1000 {
        return 2;
    } else if n < 10000 {
        return 3;
    } else {
        return 4;
    }
}
"#;
    assert_compiles_clean(source, "chain");
}

/// `else if` with no trailing `else` — the optional-else rule still applies
/// to the innermost link.
#[test]
fn else_if_without_trailing_else_compiles() {
    let source = r#"
module main;

fn classify(n: i64) -> i64 {
    let mut out = 0;
    if n < 0 {
        out = 1;
    } else if n > 0 {
        out = 2;
    }
    return out;
}
"#;
    assert_compiles_clean(source, "no_trailing");
}

/// A plain `else { … }` must be untouched by the new `at_if` branch.
#[test]
fn plain_else_still_compiles() {
    let source = r#"
module main;

fn pick(flag: bool) -> i64 {
    if flag {
        return 1;
    } else {
        return 0;
    }
}
"#;
    assert_compiles_clean(source, "plain_else");
}

/// A pathological `else if` chain must be REJECTED with the nesting-cap
/// diagnostic, not crash the process.
///
/// This is the security property, not an ergonomics one: the parser runs on
/// untrusted input, and a stack overflow aborts the whole process rather than
/// producing a diagnostic. `MAX_EXPR_DEPTH` is 128, so a few hundred links is
/// comfortably past the cap while staying far below the depth that would
/// actually smash the stack if the guard were missing — meaning this test
/// FAILS (rather than crashes the runner) if someone removes the guard.
#[test]
fn a_pathological_else_if_chain_is_rejected_not_overflowed() {
    let links = 300;
    let mut source = String::from(
        "module main;\n\nfn deep(n: i64) -> i64 {\n    if n == 0 {\n        return 0;\n    }",
    );
    for i in 1..=links {
        source.push_str(&format!(
            " else if n == {i} {{\n        return {i};\n    }}"
        ));
    }
    source.push_str(" else {\n        return 0 - 1;\n    }\n}\n");

    let err = compile_named_module("elseif_deep.sigil", &source)
        .expect_err("a 300-link else-if chain must exceed the nesting cap");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"S007"),
        "expected the nesting-cap diagnostic S007, got: {codes:?}"
    );
}
