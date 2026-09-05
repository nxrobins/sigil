//! Regression gate for the **diagnostic-order class** the Phase-2 cutover
//! surfaced.
//!
//! `check_with_warnings` merges v2's refinement diagnostics into the diagnostic
//! stream that `check_collecting` produced. The invariant callers depend on:
//! the merge is **append-only** — v2's diagnostics go AFTER the structural
//! stream, and the structural stream keeps its original TYPE-CHECK EMISSION
//! order. It must NOT be globally re-sorted (e.g. by span).
//!
//! The bug: the cutover briefly sorted the merged stream by span "to restore
//! source order". But legacy's structural diagnostics are in emission order, not
//! span order — e.g. a non-exhaustive-match error is emitted BEFORE the
//! missing-return error it induces, even though its span is later. A span sort
//! flipped them, so `diagnostics()[0]` became the wrong error and
//! `reports_non_exhaustive_match_on_bool` regressed. The fix drops the sort and
//! appends. These tests pin both halves of the invariant.

use sigil_compiler::compile_named_module;

#[cfg(feature = "solver")]
fn error_codes(src: &str) -> Vec<String> {
    let err = compile_named_module("order.sigil", src).expect_err("program must fail");
    err.diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect()
}

#[test]
fn structural_emission_order_survives_the_v2_merge() {
    // `match flag { true => ... }` on a bool is non-exhaustive AND leaves a path
    // with no return. Legacy emits these in EMISSION order —
    // [non-exhaustive-match, missing-return] — though the missing-return span is
    // earlier. A global span sort of the merged stream would put missing-return
    // first. Pin that diagnostics()[0] stays the emission-first error.
    let err = compile_named_module(
        "order.sigil",
        "module m;\n\
         pub fn boot(flag: bool) -> bool { match flag { true => { return true; } } }\n",
    )
    .expect_err("non-exhaustive bool match must fail");
    let first = err.diagnostics()[0].message();
    assert!(
        first.contains("non-exhaustive"),
        "diagnostics()[0] must stay the emission-first non-exhaustive error \
         (a global span sort would reorder it); got: {first}"
    );
}

#[cfg(feature = "solver")] // T224 comes from Z3 discharge
#[test]
fn appended_refinement_error_follows_the_structural_error() {
    // A structural error (`let s: str = 5;` -> T041) appears in source BEFORE the
    // refinement violation (`need_positive(0)` -> T224). v2 appends its
    // refinement diagnostics after the structural stream, so T041 must precede
    // T224 in the merged output. (A span sort could interleave them differently.)
    let codes = error_codes(
        "module m;\n\
         pub fn need_positive(x: i64) where x > 0 -> i64 { return x; }\n\
         pub fn f() -> i64 { let s: str = 5; return need_positive(0); }\n",
    );
    let structural = codes.iter().position(|c| c == "T041");
    let refinement = codes.iter().position(|c| c == "T224");
    assert!(
        structural.is_some() && refinement.is_some(),
        "expected both the structural T041 and the refinement T224: {codes:?}"
    );
    assert!(
        structural < refinement,
        "structural T041 must precede the appended refinement T224: {codes:?}"
    );
}
