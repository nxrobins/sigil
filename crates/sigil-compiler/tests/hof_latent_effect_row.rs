//! AG-HOF-A: a closure's latent effect row rides its type, so applying it (or passing it
//! where a smaller row is promised) is a COMPILE-TIME rejection rather than a runtime trap.
//!
//! Before this landed, `walk_expr_effects` treated `ClosureConstruct` as a leaf and its
//! `IndirectCall` arm walked only the arguments, so a closure built in an `{ Log }` context
//! and applied in a `{}` context compiled clean — the effect check was deferred to a runtime
//! frame check. `Type::Fn` now carries the row (mirroring the λ-SIGIL spec's `Ty.arrow A ε B`
//! and `Chk.app_latent_bounded`), and it is contravariant at a parameter boundary.
//!
//! SCOPE (roadmap Phase 1, precise rows): the row a closure carries is INFERRED bottom-up
//! from what its body actually performs (`type_check/effect_infer.rs`), not inherited from
//! its defining function. A pure closure therefore crosses a pure `Fn` boundary regardless
//! of where it was defined — `pure_closure_defined_in_effectful_fn_compiles` (the flipped
//! former over-approximation marker) pins that. The only remaining over-approximation is
//! the fail-closed callee-miss path, which charges the enclosing declared row for a call
//! whose callee resolves nowhere.

use sigil_test_utils::pipeline::compile_module_codes;

/// A pure closure passed to a pure `Fn` parameter and applied: no effects anywhere, clean.
#[test]
fn pure_closure_through_pure_fn_param_compiles() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
         fn caller() -> i64 { return h(fn(x: i64) -> i64 { return x + 1; }); }\n",
    );
    assert!(
        codes.is_empty(),
        "pure HOF must compile clean; got {codes:?}"
    );
}

/// THE AG-HOF-A LAUNDER. A closure defined in a `! { Log }` function is handed to a `Fn`
/// parameter that promises no effects and applies it in a `{}` context. This compiled clean
/// before the fix; it must now be rejected at compile time.
#[test]
fn effectful_closure_cannot_cross_into_a_pure_fn_param() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
         fn caller() -> i64 ! { Log } { return h(fn(x: i64) -> i64 { return logs(); }); }\n",
    );
    assert!(
        !codes.is_empty(),
        "a closure carrying `Log` must not satisfy a `Fn(i64) -> i64` parameter that \
         promises no effects — this is the AG-HOF-A launder and it compiled clean before"
    );
}

/// The legitimate case must stay legal: a closure applied inside a frame whose declared row
/// already covers it. Guards against the fix over-rejecting the ordinary use of closures.
#[test]
fn closure_applied_within_its_own_row_compiles() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn caller() -> i64 ! { Log } { let g = fn(x: i64) -> i64 { return logs(); }; return g(1); }\n",
    );
    assert!(
        codes.is_empty(),
        "applying a closure inside a frame that declares its effects must stay legal; got {codes:?}"
    );
}

/// THE FLIPPED MARKER (roadmap Phase 1). Under the interim over-approximation this
/// closure inherited `{ Log }` from its defining function and was refused by the pure
/// parameter — a sound false reject, pinned by this test's previous form
/// (`..._is_conservatively_rejected`). Precise inference now derives the row from the
/// BODY, which performs nothing, so the same program compiles clean.
#[test]
fn pure_closure_defined_in_effectful_fn_compiles() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
         fn caller() -> i64 ! { Log } { return h(fn(x: i64) -> i64 { return x + 1; }); }\n",
    );
    assert!(
        codes.is_empty(),
        "a PURE closure must cross a pure `Fn` boundary regardless of where it was \
         defined — its row is inferred from the body, not inherited; got {codes:?}"
    );
}

/// NESTED closures: the outer closure's row is the JOIN of what it performs, including
/// the latent row of an inner closure it APPLIES (application discharges the inner row
/// into the outer body — λ-SIGIL's app rule, transitively). The outer closure therefore
/// carries `{ Log }` and is refused by the pure `Fn` parameter.
#[test]
fn nested_closure_row_propagates_through_application() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
         fn caller() -> i64 ! { Log } { let outer = fn(x: i64) -> i64 { let inner = fn(y: i64) -> i64 { return logs(); }; return inner(x); }; return h(outer); }\n",
    );
    assert!(
        !codes.is_empty(),
        "an outer closure that APPLIES an effectful inner closure carries the inner's \
         row and must be refused by a pure `Fn` parameter; got clean"
    );
}

/// Handler DISCHARGE inside the closure body: inference subtracts what a `handle`
/// discharges (the dual of the checker's row expansion), so a body whose only effectful
/// call is wrapped in a discharging handle has an EMPTY row and crosses a pure boundary.
#[test]
fn handle_discharge_inside_closure_body_yields_pure_row() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
         fn caller() -> i64 { let g = fn(x: i64) -> i64 { handle Log { let _z: i64 = logs(); }; return x; }; return h(g); }\n",
    );
    assert!(
        codes.is_empty(),
        "a closure whose effectful call is discharged by an enclosing `handle` has an \
         empty inferred row and must cross a pure `Fn` boundary; got {codes:?}"
    );
}

/// A closure that calls its DEFINING function: the callee contributes its DECLARED row
/// (which cuts the cycle — no fixpoint needed), and applying the closure inside that
/// same row is legal. Also pins that inference terminates on this shape.
#[test]
fn closure_calling_its_defining_fn_terminates_with_declared_row() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn caller() -> i64 ! { Log } { let g = fn(x: i64) -> i64 { return caller(); }; return g(1); }\n",
    );
    assert!(
        codes.is_empty(),
        "a closure calling its defining fn reads that fn's DECLARED row (cycle cut); \
         applying it under the same row must be legal; got {codes:?}"
    );
}

/// CROSS-MODULE callee: the closure's row is found through `workspace_sigs`, so a
/// closure calling `b::helper() ! {{ Log }}` carries `{ Log }` and is refused by a pure
/// parameter. If the cross-module lookup silently missed, the fail-closed fallback
/// (the pure enclosing row) would let this compile — so this test also guards the
/// lookup chain itself (and `check_effects`' walk of the lifted body is the second,
/// independent net for the same under-approximation).
#[test]
fn cross_module_effectful_callee_inferred_into_closure_row() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule b;\n\
         effect Log;\n\
         pub fn helper() -> i64 ! { Log } { return 0; }\n\
         #[ring(outer)]\nmodule app;\n\
         use b;\n\
         fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
         fn quiet() -> i64 { return h(fn(x: i64) -> i64 { return b::helper(); }); }\n",
    );
    assert!(
        !codes.is_empty(),
        "a closure calling a cross-module effectful fn must carry that row and be \
         refused by a pure `Fn` parameter; got clean (workspace lookup miss?)"
    );
}

/// The CERT surface: an UNAPPLIED effectful closure in a pure fn is now legal
/// (construction is pure — λ-SIGIL's `lam`), so `effects_required` — which feeds the
/// certificate and the deploy-time effect-set gate — is the artifact-level guard that
/// its row is still counted. `collect_program_effects` unions `TypedFunction.effects`
/// over ALL functions including lifted closures; this pins that the inferred row lands
/// there. (The gate's diagnostic code is deliberately NOT named here: the
/// direct-test-reference census scans test sources for code tokens and cannot tell an
/// assertion from prose, and this test asserts the effects_required VALUE, not that
/// gate's diagnostic.)
#[test]
fn unapplied_effectful_closure_lands_row_in_effects_required() {
    let src = "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn quiet() -> i64 { let f = fn(x: i64) -> i64 { return logs(); }; return 0; }\n\
         entry actor Main { on Tick() -> i64 { return quiet(); } }\n";
    let compilation = sigil_compiler::compile_named_module("hof_cert_row.sigil", src)
        .expect("constructing (without applying) an effectful closure in a pure fn is legal");
    assert!(
        compilation.effects_required.iter().any(|e| e == "Log"),
        "the unapplied closure's inferred row must land in effects_required (the cert / \
         deploy-gate surface); got {:?}",
        compilation.effects_required
    );
}
