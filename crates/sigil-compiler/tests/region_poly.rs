//! DEF-2b PR-4 — the AG-R2 lift (region-polymorphism across function boundaries).
//!
//! DEF-2a's AG-R2 said a region value may cross a function boundary ONLY into the closed
//! stdlib receiver-allowlist; every other flow was a conservative `T254`. PR-4 LIFTS that
//! for `@in r`-annotated parameters: a region value flows into a user function's parameter
//! iff it OUTLIVES-OR-EQUALS the region passed as `r` (the outlives lattice). The lift is
//! opt-in per signature; the default stays the DEF-2a rejection.
//!
//! The mechanism has two symmetric halves, both pinned here:
//!   * CALLER side — at the call/method arg sink, each argument's sink region is computed
//!     from the callee's `param_regions`: a `Region`-typed param receives a threaded
//!     HANDLE (exempt); an `@in r` param's value is checked against the caller-side region
//!     of the argument filling `r`'s slot (NC-2b-3, map-before-compare); everything else is
//!     a `Global` sink (NC-2b-4, fail-closed); and
//!   * CALLEE side (LD-6) — `current_param_regions` makes an `@in r` param's region
//!     `Param(slot)`, so the callee's own return / copy-then-return / record-field sinks
//!     reject leaking it past `r` via the SAME lattice — no new sink.
//!
//! Soundness is enforced entirely by `T254` (the lifetime axis); a region value can never
//! outlive its region, whether as a direct arg, a launder copy, a return, a record field,
//! or a deeper-region value handed to a longer-lived region.
//!
//! These assertions are at the TYPE-CHECK level (`parse → resolve → check`): the lift
//! makes region-poly programs type-VALID, but their codegen — lowering a `Region` handle
//! argument — lands in PR-7, so the full `compile_tool` pipeline would ICE in AIR lowering
//! on an accepted program. We use a user `record` for the region value (single-source, no
//! ambient stdlib injection, so no `Vec`).

use sigil_compiler::diagnostics::Severity;
use sigil_compiler::source::SourceFile;
use sigil_compiler::{CompileOptions, name_resolution, parser, type_check};

/// Type-check ONLY (parse → name-resolution → check), returning the emitted diagnostic
/// codes (empty ⇒ a clean type-check). Stops before AIR/codegen (PR-7).
fn codes(src: &str) -> Vec<String> {
    let source = SourceFile::new("<region_poly>", src);
    let (ast, parse_diags) = parser::parse(&source);
    let parse_errs: Vec<String> = parse_diags
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .map(|d| d.code().as_str().to_string())
        .collect();
    if !parse_errs.is_empty() {
        return parse_errs;
    }
    let resolved = match name_resolution::resolve(&ast) {
        Ok(r) => r,
        Err(diags) => {
            return diags
                .iter()
                .map(|d| d.code().as_str().to_string())
                .collect();
        }
    };
    match type_check::check_with_options(&resolved, &CompileOptions::default()) {
        Ok(_) => Vec::new(),
        Err(diags) => diags
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn has(src: &str, code: &str) -> bool {
    codes(src).iter().any(|c| c == code)
}

// A `Box` record stands in for any aliasable, region-allocatable value. A region-
// polymorphic `store`: `b` lives in the region passed as `r`.
const PRELUDE: &str = "module tool;\n\
     record Box { v: i64 }\n\
     fn store(r: Region, b: Box @in r) -> i64 { return 0; }\n";

// ── the lift, positive: a region value into `@in r` now type-checks ──────────────

#[test]
fn region_value_into_in_param_is_accepted() {
    // The keystone: a `Box` born in `region buf` flows into `store`'s `@in r` parameter
    // because it lives in EXACTLY the region passed as `r` (`Lexical(1)` outlives-or-equals
    // `Lexical(1)`). The region handle `buf` in the `Region`-param position is threaded,
    // not escaped. Clean — the whole reason DEF-2b exists.
    let src = format!(
        "{PRELUDE}\
         fn f() -> i64 ! {{ Alloc }} {{ \
             region buf(64) {{ let b: Box = Box {{ v: 1 }}; let _x: i64 = store(buf, b); }}; \
             return 0; \
         }}\n"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn longer_lived_value_into_in_param_is_accepted() {
    // A function-lifetime (`Global`) `Box` handed to a region's `@in r` parameter is fine —
    // `Global` outlives every region, so it cannot dangle when `buf` is reclaimed.
    let src = format!(
        "{PRELUDE}\
         fn f() -> i64 ! {{ Alloc }} {{ \
             let outer: Box = Box {{ v: 1 }}; \
             region buf(64) {{ let _x: i64 = store(buf, outer); }}; return 0; \
         }}\n"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

// ── the lift, negative: the default stays the DEF-2a rejection ────────────────────

#[test]
fn region_value_into_unannotated_param_is_t254() {
    // The lift is opt-in: an un-annotated parameter is still a `Global` sink, so a region
    // value into it is rejected exactly as in DEF-2a (the callee could store it at function
    // lifetime). This is the fail-closed default (NC-2b-4).
    let src = "module tool;\n\
         record Box { v: i64 }\n\
         fn leak(b: Box) -> i64 { return 0; }\n\
         fn f() -> i64 ! { Alloc } { \
             region buf(64) { let b: Box = Box { v: 1 }; let _x: i64 = leak(b); }; \
             return 0; \
         }\n";
    assert!(has(src, "T254"), "got {:?}", codes(src));
}

#[test]
fn deeper_region_value_into_outer_in_param_is_t254() {
    // A value born in a NESTED region (`Lexical(2)`) handed to an `@in r` whose `r` is the
    // OUTER region (`Lexical(1)`) is rejected: the inner region is reclaimed first, so the
    // value would dangle inside the longer-lived `outer`. `2 <= 1` is false → `T254`.
    let src = format!(
        "{PRELUDE}\
         fn f() -> i64 ! {{ Alloc }} {{ \
             region outer(64) {{ region inner(64) {{ \
                 let b: Box = Box {{ v: 1 }}; let _x: i64 = store(outer, b); \
             }}; }}; return 0; \
         }}\n"
    );
    assert!(has(&src, "T254"), "got {:?}", codes(&src));
}

// ── the callee MUST honor `@in r` (LD-6), enforced by the same lattice ───────────

#[test]
fn callee_returning_its_in_param_is_t254() {
    // The symmetric half: inside the callee an `@in r` parameter's region is `Param(slot)`,
    // which does not outlive the function-boundary (`Global`) return sink — so a fn that
    // returns its own `@in r` value leaks it past `r` and is rejected. No new sink; the
    // existing return gate fires via `region_of_value` returning `Param`.
    let src = "module tool;\n\
         record Box { v: i64 }\n\
         fn bad(r: Region, b: Box @in r) -> Box { return b; }\n";
    assert!(has(src, "T254"), "got {:?}", codes(src));
}

#[test]
fn callee_laundering_its_in_param_through_a_copy_is_t254() {
    // The launder defence: `let c = b` where `b` is `@in r` makes `c` inherit `b`'s param
    // region (the region analogue of `@ReadOnly` propagation), so `return c` is caught the
    // same as `return b`. Without the propagation this would be a one-line escape hatch.
    let src = "module tool;\n\
         record Box { v: i64 }\n\
         fn bad(r: Region, b: Box @in r) -> Box { let c: Box = b; return c; }\n";
    assert!(has(src, "T254"), "got {:?}", codes(src));
}

#[test]
fn callee_storing_its_in_param_in_a_returned_record_is_t254() {
    // The record-field leak: wrapping an `@in r` value in a function-lifetime record and
    // returning it would smuggle the region pointer out. The record-field sink scores the
    // record at `Global` (function scope), and `Param(slot)` does not outlive `Global` →
    // `T254`. Closes the "hide it in a field" hatch (the field sink now runs at depth 0
    // when the fn has region params).
    let src = "module tool;\n\
         record Box { v: i64 }\n\
         record Wrap { inner: Box }\n\
         fn bad(r: Region, b: Box @in r) -> Wrap { return Wrap { inner: b }; }\n";
    assert!(has(src, "T254"), "got {:?}", codes(src));
}

#[test]
fn returning_a_region_handle_is_t254() {
    // NC-2b-2 (a `Region` value may not be returned) falls out of the same lattice: a
    // `Region` parameter's region is `Param(slot)`, which does not outlive the `Global`
    // return sink, so `return r` is `T254` — a region handle can never escape its caller.
    let src = "module tool;\n\
         fn bad(r: Region) -> Region { return r; }\n";
    assert!(has(src, "T254"), "got {:?}", codes(src));
}

// ── transitive forwarding (NC-2b-5): the third-function flow is the call-arg sink ─

#[test]
fn forwarding_an_in_param_into_a_matching_in_param_is_accepted() {
    // A middle function forwards its `@in r` value into a third function's `@in r'` where
    // it passes the SAME region `r` — both sides agree the value lives in `r` (`Param(0)`
    // outlives-or-equals `Param(0)`), so the chain `f -> middle -> inner` is clean. This is
    // the transitive case handled by the ordinary call-arg sink, not a special case. (The
    // sink runs at the callee's function depth 0 because `middle` has region params.)
    let src = "module tool;\n\
         record Box { v: i64 }\n\
         fn inner(r: Region, w: Box @in r) -> i64 { return 0; }\n\
         fn middle(r: Region, v: Box @in r) -> i64 { return inner(r, v); }\n\
         fn f() -> i64 ! { Alloc } { \
             region buf(64) { let b: Box = Box { v: 1 }; let _x: i64 = middle(buf, b); }; \
             return 0; \
         }\n";
    assert!(codes(src).is_empty(), "got {:?}", codes(src));
}

#[test]
fn forwarding_an_in_param_into_an_unannotated_param_is_t254() {
    // The transitive LEAK: a middle function passes its `@in r` value into a third
    // function's UN-annotated parameter (a `Global` sink). The middle's `v` is `Param(0)`,
    // which does not outlive `Global` → `T254`. The leak is caught at the call-arg sink
    // (NC-2b-5: no sink is exempt) — at `middle`'s depth 0, because it has region params.
    let src = "module tool;\n\
         record Box { v: i64 }\n\
         fn sink(w: Box) -> i64 { return 0; }\n\
         fn middle(r: Region, v: Box @in r) -> i64 { return sink(v); }\n";
    assert!(has(src, "T254"), "got {:?}", codes(src));
}

// ── `@SecretCT @Region`-poly composition: the two axes stay independent ──────────

#[test]
fn secret_region_value_into_in_param_is_accepted_and_stays_secret() {
    // The memory-model keystone under region-polymorphism: a `@SecretCT` region value
    // flows into a `@SecretCT @in r` parameter — the LIFETIME axis is satisfied (lives in
    // `r`) and the CONFIDENTIALITY axis is satisfied (secret→secret), so it type-checks.
    // The two annotations compose with no interference.
    let src = "module tool;\n\
         record Box { v: i64 }\n\
         fn sstore(r: Region, b: Box @SecretCT @in r) -> i64 { return 0; }\n\
         fn f() -> i64 ! { Alloc } { \
             region buf(64) { let b: Box @SecretCT = Box { v: 1 }; \
             let _x: i64 = sstore(buf, b); }; return 0; \
         }\n";
    assert!(codes(src).is_empty(), "got {:?}", codes(src));
}

#[test]
fn secret_region_value_into_unannotated_secret_param_is_still_t254() {
    // Independence proof: even a sink that ACCEPTS the secret taint cannot receive a region
    // value at a NON-`@in` parameter — the lifetime axis (`T254`) fires regardless of
    // whether confidentiality is satisfied. Lifetime is enforced separately from secrecy.
    let src = "module tool;\n\
         record Box { v: i64 }\n\
         fn ssink(b: Box @SecretCT) -> i64 { return 0; }\n\
         fn f() -> i64 ! { Alloc } { \
             region buf(64) { let b: Box @SecretCT = Box { v: 1 }; \
             let _x: i64 = ssink(b); }; return 0; \
         }\n";
    assert!(has(src, "T254"), "got {:?}", codes(src));
}
