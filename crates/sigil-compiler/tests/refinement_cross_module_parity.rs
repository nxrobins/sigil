//! Regression + invariant gate for the **cross-module discharge class** the
//! Phase-2 cutover surfaced.
//!
//! Refinement discharge at a call site must resolve the callee in the callee's
//! OWN module. v2 keyed the `fn_def` lookup by the CALLER's module, so a
//! cross-module call (`math::need_positive(0)` from `main`, `where x > 0`)
//! missed the lookup entirely and compiled clean — a silent soundness hole that
//! only bit once v2 became the sole discharge path. The fix derives the callee's
//! module from its qualified name (`<module>::<fn>`).
//!
//! The invariant: **refinement discharge is module-arrangement-invariant.** The
//! same violating refined call fires the same diagnostic (T224) whether the
//! callee is same-module or imported from another module, for any module names.
//!
//! `#![cfg(feature = "solver")]` — T224 is a Z3 discharge verdict.

#![cfg(feature = "solver")]

use proptest::prelude::*;
use sigil_compiler::source::SourceFile;
use sigil_compiler::{CompileError, CompileOptions, compile_project};

fn sf(name: &str, text: &str) -> SourceFile {
    SourceFile::new(name, text)
}

fn codes_of(err: &CompileError) -> Vec<String> {
    err.diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect()
}

/// Same-module: callee and caller in one file, unqualified violating call.
fn compile_same_module(arg: i64) -> Result<(), Vec<String>> {
    let src = format!(
        "module m;\n\
         pub fn need_positive(x: i64) where x > 0 -> i64 {{ return x; }}\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{ return need_positive({arg}); }}\n"
    );
    compile_project(vec![sf("m.sigil", &src)], None, CompileOptions::default())
        .map(|_| ())
        .map_err(|e| codes_of(&e))
}

/// Cross-module: callee in `callee_mod`, caller in `caller_mod` importing it and
/// calling `<callee_mod>::need_positive(arg)`.
fn compile_cross_module(callee_mod: &str, caller_mod: &str, arg: i64) -> Result<(), Vec<String>> {
    let callee = format!(
        "module {callee_mod};\n\
         pub fn need_positive(x: i64) where x > 0 -> i64 {{ return x; }}\n"
    );
    let caller = format!(
        "module {caller_mod};\n\
         use sigil::{callee_mod};\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{ return {callee_mod}::need_positive({arg}); }}\n"
    );
    compile_project(
        vec![
            sf(&format!("{callee_mod}.sigil"), &callee),
            sf(&format!("{caller_mod}.sigil"), &caller),
        ],
        None,
        CompileOptions::default(),
    )
    .map(|_| ())
    .map_err(|e| codes_of(&e))
}

#[test]
fn same_and_cross_module_violation_both_fire_t224() {
    // Parity: the identical violating call (`need_positive(0)`, `where x > 0`)
    // must fire T224 whether the callee is same-module or imported.
    let same = compile_same_module(0).expect_err("0 violates `where x > 0` (same module)");
    assert!(
        same.contains(&"T224".to_string()),
        "same-module violation must fire T224, got {same:?}"
    );

    let cross = compile_cross_module("math", "main", 0)
        .expect_err("0 violates `where x > 0` (cross module)");
    assert!(
        cross.contains(&"T224".to_string()),
        "cross-module violation must fire T224 (the exact cutover regression), got {cross:?}"
    );
}

#[test]
fn cross_module_satisfied_call_compiles() {
    // Negative control: a SATISFYING cross-module call compiles clean, so the
    // T224 above is a real discharge verdict, not a blanket cross-module reject.
    assert!(
        compile_cross_module("math", "main", 5).is_ok(),
        "5 satisfies `where x > 0` — cross-module call must compile"
    );
}

proptest! {
    // The bug was structural (wrong module component in the lookup key), so it
    // was name-independent — but fuzzing the module names guards against any
    // name-specific resolution edge case (a callee module whose name is a prefix
    // of the caller's, unusual-but-valid identifiers, etc.). Every violating
    // cross-module call must fire T224.
    #[test]
    fn cross_module_violation_fires_t224_for_any_module_names(
        callee_suffix in "[a-z0-9_]{1,6}",
        caller_suffix in "[a-z0-9_]{1,6}",
        arg in -1000_i64..=0,
    ) {
        // The `zc`/`zr` prefixes keep the two module names distinct (a project
        // can't declare two modules the same) AND guarantee neither is a SIGIL
        // keyword (`module`, `return`, `record`, ... would break the generated
        // source and spuriously fail this test — not the resolution property).
        let callee_mod = format!("zc{callee_suffix}");
        let caller_mod = format!("zr{caller_suffix}");
        let codes = compile_cross_module(&callee_mod, &caller_mod, arg)
            .err()
            .unwrap_or_default();
        prop_assert!(
            codes.contains(&"T224".to_string()),
            "violating cross-module call `{callee_mod}::need_positive({arg})` from \
             `{caller_mod}` did not fire T224 — the callee was likely resolved in the \
             wrong module. codes: {codes:?}"
        );
    }
}
