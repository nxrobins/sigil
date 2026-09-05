//! Refinement Quarantine — **mixed structural+refinement gate** (Phase-2 cutover).
//!
//! The v2 obligation pipeline is now the SOLE refinement-discharge path (the
//! legacy in-line walkers are deleted). This gate covers the case the cutover
//! actually turns on: a program carrying BOTH a structural type error AND a
//! refinement violation. Because a structural error leaves a partial program
//! (with `Type::Error` nodes), `check_with_warnings` runs v2 over that partial
//! program (Option B — the behavior-preserving choice: the alternative,
//! post-pass-on-success, would drop the refinement diagnostic until the
//! structural error is fixed).
//!
//! This is a BLACK-BOX gate: it compiles each program through the production
//! entry point (`compile_module` → `check_with_warnings`) and asserts the
//! combined error stream carries BOTH the structural code AND the refinement
//! code. It replaces the pre-cutover white-box oracle (which diffed the legacy
//! walker against v2 — meaningless once the walker is gone) and is durable: it
//! pins the property the cutover must preserve, on the real compiler output.
//!
//! `#![cfg(feature = "solver")]` — refinement rejections come from Z3.

#![cfg(feature = "solver")]

use sigil_compiler::compile_module;

/// Compile one source through the production path and return every error code.
fn error_codes(src: &str) -> Vec<String> {
    let err = compile_module(src).expect_err("mixed program must fail to compile");
    err.diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect()
}

/// Each program pairs a structural error (`let s: str = 5;` → T041) with a
/// refinement violation exercising a different discharge path.
fn mixed_programs() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![
        (
            "call-arg T224",
            "module m;\n\
             pub fn need_positive(x: i64) where x > 0 -> i64 { return x; }\n\
             pub fn f() -> i64 { let s: str = 5; return need_positive(0); }\n",
            "T224",
        ),
        (
            "return T225",
            "module m;\n\
             pub fn g() -> i64 where @ > 0 { let s: str = 5; return 0; }\n",
            "T225",
        ),
        (
            "record T210",
            "module m;\n\
             record R { v: i64 } where v > 0\n\
             pub fn f() -> i64 { let s: str = 5; let r: R = R { v: 0 }; return 1; }\n",
            "T210",
        ),
        (
            "structural in a different function",
            "module m;\n\
             pub fn need_positive(x: i64) where x > 0 -> i64 { return x; }\n\
             pub fn bad() -> i64 { let s: str = 5; return 1; }\n\
             pub fn f() -> i64 { return need_positive(0); }\n",
            "T224",
        ),
    ]
}

/// The cutover property: over a structurally-broken partial program, the
/// production compiler still reports the refinement violation ALONGSIDE the
/// structural error. A regression that dropped v2's pass on the error path (or
/// mis-merged its diagnostics) would surface here as a missing refinement code.
#[test]
fn mixed_structural_and_refinement_both_reported() {
    for (label, src, refinement_code) in mixed_programs() {
        let codes = error_codes(src);
        assert!(
            codes.iter().any(|c| c == "T041"),
            "{label}: expected the structural error T041, got: {codes:?}"
        );
        assert!(
            codes.iter().any(|c| c == refinement_code),
            "{label}: expected the refinement error {refinement_code}, got: {codes:?}"
        );
    }
}
