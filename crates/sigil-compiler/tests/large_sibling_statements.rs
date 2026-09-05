//! Regression test for the sibling-statement stack-overflow DoS.
//!
//! The post-parse pipeline used to fold over a block's statement sequence
//! recursively in two places — AIR lowering (`lower_statements` tail-recursed
//! on the block remainder for every `if`/`match`/`while`/`for`) and wasm
//! codegen (`emit_block` recursed on each region's merge/continuation). Both
//! made native-stack depth grow with the number of sibling control-flow
//! statements in one function, so a hand-written function with a few hundred
//! sibling `if`s overflowed the stack and aborted the compiler (exit 127,
//! "thread 'main' has overflowed its stack") — a robustness/DoS bug that hit
//! hand-written SIGIL and any frontend that emits long flat blocks (e.g. the
//! Solidity frontend translating a large `if`-cascade) alike.
//!
//! Both folds are now iterative, so block-remainder lowering costs O(1) stack
//! regardless of sibling count. These tests compile functions with N=2000
//! sibling statements of each control-flow shape and assert success. If the
//! recursion is ever reintroduced, an N=2000-deep recursive walk overflows the
//! (smaller) cargo-test thread stack and crashes the test binary — a loud,
//! unmissable regression signal.

use sigil_compiler::compile_module;

/// Number of sibling statements. The original repro overflowed a debug build
/// at ~500; 2000 is the acceptance threshold and clears the iterative path
/// comfortably while staying well under the S006 function-count cap (this is
/// statements *inside one* function, not separate functions).
const N: usize = 2000;

fn assert_compiles(label: &str, src: &str) {
    match compile_module(src) {
        Ok(compilation) => {
            assert!(
                !compilation.wasm_inner.is_empty(),
                "{label}: compilation produced empty wasm"
            );
        }
        Err(e) => {
            let codes: Vec<_> = e
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_string())
                .collect();
            panic!("{label}: expected N={N}-sibling program to compile, got diagnostics {codes:?}");
        }
    }
}

#[test]
fn two_thousand_sibling_ifs_compile() {
    let mut body = String::from("    let mut acc: i64 = 0;\n");
    for _ in 0..N {
        body.push_str("    if a > 0 { acc = a; }\n");
    }
    body.push_str("    return acc;\n");
    let src = format!("module m;\nfn f(a: i64) -> i64 {{\n{body}}}\n");
    assert_compiles("sibling if", &src);
}

#[test]
fn two_thousand_sibling_whiles_compile() {
    let mut body = String::from("    let mut acc: i64 = 0;\n");
    for _ in 0..N {
        // Never actually loops at runtime (we only compile), but exercises the
        // `While` arm's block-remainder lowering 2000 times over.
        body.push_str("    while acc > a { acc = acc + 1; }\n");
    }
    body.push_str("    return acc;\n");
    let src = format!("module m;\nfn f(a: i64) -> i64 {{\n{body}}}\n");
    assert_compiles("sibling while", &src);
}

#[test]
fn two_thousand_sibling_matches_compile() {
    let mut body = String::from("    let mut acc: i64 = 0;\n");
    for _ in 0..N {
        // Each match is shallow (2 arms) — what scales here is the count of
        // sibling `match` *statements*. Each lowers to a flat `Dispatch` block, so
        // the chain stays O(1)-stack in both AIR lowering and wasm emission.
        body.push_str(
            "    match a {\n        0 => { acc = 1; },\n        _ => { acc = 2; }\n    }\n",
        );
    }
    body.push_str("    return acc;\n");
    let src = format!("module m;\nfn f(a: i64) -> i64 {{\n{body}}}\n");
    assert_compiles("sibling match", &src);
}

#[test]
fn single_match_with_two_thousand_arms_compiles() {
    // A single match with N literal arms lowers to ONE flat dispatch block (each
    // arm is `if (a == k) { … br }` at one nesting level), so neither the AIR arm
    // walk nor the wasm emitter recurses with arm count. Before the flat-dispatch
    // codegen this overflowed the native stack at a few hundred arms.
    let mut arms = String::new();
    for i in 0..N {
        arms.push_str(&format!("        {i} => {{ return {i}; }},\n"));
    }
    arms.push_str("        _ => { return -1; }\n");
    let src = format!("module m;\nfn f(a: i64) -> i64 {{\n    match a {{\n{arms}    }}\n}}\n");
    assert_compiles("single many-arm match", &src);
}

/// The exact shape from the bug report: a `record` + `impl` method whose body
/// is N sibling `if`s writing through a `@Mut` self field.
#[test]
fn reported_repro_record_impl_method_compiles() {
    let mut body = String::new();
    for _ in 0..N {
        body.push_str("        if a > 0 { self.b = a; }\n");
    }
    let src = format!(
        "module m;\nrecord C {{ b: i64 }}\nimpl C {{\n    pub fn f(self: C @Mut, a: i64) {{\n{body}    }}\n}}\n"
    );
    assert_compiles("record/impl sibling if", &src);
}
