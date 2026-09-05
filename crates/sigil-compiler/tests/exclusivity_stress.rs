//! DEF-2c PR-5 — the capstone: DEF-1 flip-readiness (NC-4), orthogonality
//! (`@SecretCT` taint × the exclusivity axis), composition with the `@ReadOnly`
//! escape gate (T253) and DEF-2a regions (T254), and an adversarial stress matrix
//! (deep-nested same-root fields, generic-monomorph `alias_origin` isolation).
//!
//! No new enforcement lives here — every gate landed in PR-1..PR-4. This file proves
//! the axes COMPOSE, that the exclusivity gate is PREDICATE-DRIVEN so the DEF-1
//! default-flip (`bare ⇒ frozen`) is a one-line change at `ast.rs` `is_frozen` with
//! ZERO DEF-2c rework, and that the gate holds under cross-cutting combinations.

use sigil_compiler::ast::Mutability;
use sigil_compiler::compile_tool;

/// Wrap `defs` in a `tool` module with a trivial `tool_main`, compile, return the codes
/// (empty = clean). Functions in `defs` are type-checked even when uncalled, so a gate
/// fires on a `fn f` body without a dedicated call site.
fn codes(defs: &str) -> Vec<String> {
    let src = format!(
        "module tool;\n{defs}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{ return 0 - 1; }}\n"
    );
    match compile_tool(&src) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn rejects(defs: &str, code: &str) -> bool {
    codes(defs).iter().any(|c| c == code)
}

const BOX: &str = "record Box { v: i64 }\n";

// ── DEF-1 flip-readiness (NC-4): the exclusivity gate is predicate-driven ──────────

#[test]
fn is_frozen_is_the_def1_flip_point_now_flipped() {
    // The exclusivity partition keys frozen-ness on EXACTLY this predicate
    // (`param_mutability...is_some_and(Mutability::is_frozen)`). Since the DEF-1 flip at
    // `ast.rs` (`ReadOnly => ReadOnly | Default`) both `@ReadOnly` and bare freeze; only
    // `@Mut` is mutable — the one-line change auto-extended every gate, no DEF-2c rework.
    assert!(Mutability::ReadOnly.is_frozen(), "@ReadOnly freezes");
    assert!(
        Mutability::Default.is_frozen(),
        "bare is now frozen (the DEF-1 default-flip)"
    );
    assert!(!Mutability::Mut.is_frozen(), "@Mut is the mutable opt-up");
    assert_ne!(
        Mutability::Mut,
        Mutability::Default,
        "@Mut stays distinct from bare (NC-4) so the flip never disambiguates a collapsed state"
    );
}

#[test]
fn readonly_first_param_aliasing_mutable_is_t255_today() {
    // The frozen-today witness: an explicit `@ReadOnly` first param aliasing a mutable
    // second → T255. This is the behavior the DEF-1 flip will extend to bare params.
    assert!(rejects(
        &format!(
            "{BOX}fn sink(a: Box @ReadOnly, b: Box @Mut) -> i64 {{ return 0; }}\n\
             fn f() -> i64 ! {{ Alloc }} {{ let p: Box = Box {{ v: 1 }}; return sink(p, p); }}"
        ),
        "T255"
    ));
}

#[test]
fn bare_first_param_aliasing_mutable_is_now_t255() {
    // The flip LANDED (the mirror witness, now flipped): the SAME call with a BARE first
    // param now CONFLICTS — bare `a` is frozen (DEF-1), so `sink(p, p)` hands `p` to a
    // frozen `a` and a `@Mut` `b` → T255. Pre-flip this was clean; the one-line predicate
    // change turned it into a conflict through the UNCHANGED gate — the gate is purely
    // predicate-driven, exactly as the flip-readiness witness predicted.
    assert!(rejects(
        &format!(
            "{BOX}fn sink(a: Box, b: Box @Mut) -> i64 {{ return 0; }}\n\
             fn f() -> i64 ! {{ Alloc }} {{ let p: Box = Box {{ v: 1 }}; return sink(p, p); }}"
        ),
        "T255"
    ));
}

// ── Orthogonality: the @SecretCT taint axis is independent of exclusivity ───────────

#[test]
fn secret_ct_does_not_mask_exclusivity_either_order() {
    // The gate keys on mutability alone, so a `@SecretCT` taint on the frozen param does
    // not suppress T255 — both annotation orders still conflict.
    for ann in ["@SecretCT @ReadOnly", "@ReadOnly @SecretCT"] {
        assert!(
            rejects(
                &format!(
                    "{BOX}fn sink(a: Box {ann}, b: Box @Mut) -> i64 {{ return 0; }}\n\
                     fn f() -> i64 ! {{ Alloc }} {{ let p: Box = Box {{ v: 1 }}; return sink(p, p); }}"
                ),
                "T255"
            ),
            "order `{ann}` must still conflict"
        );
    }
}

#[test]
fn secret_ct_bare_is_now_frozen_for_exclusivity() {
    // Post-DEF-1, a BARE `@SecretCT` first param is frozen, so `sink(p, p)` hands `p` to a
    // frozen `a` and a `@Mut` `b` → T255. Taint stays orthogonal: it did not drive the
    // gate — bare-becoming-frozen did. (Pre-flip the bare `@SecretCT` `a` was mutable, so
    // two mutables aliasing was clean.)
    assert!(rejects(
        &format!(
            "{BOX}fn sink(a: Box @SecretCT, b: Box @Mut) -> i64 {{ return 0; }}\n\
             fn f() -> i64 ! {{ Alloc }} {{ let p: Box = Box {{ v: 1 }}; return sink(p, p); }}"
        ),
        "T255"
    ));
}

// ── Composition: T255 co-fires with the escape gate (T253) and regions (T254) ───────

#[test]
fn exclusivity_and_escape_gates_both_fire_on_one_call() {
    // NC-2c-8: AG-1's core needs BOTH gates, and they are independent codes. `g(p, p)`
    // with a `@ReadOnly` local `p` and `g(a @ReadOnly, b: Box)` trips T253 (the frozen
    // `p` ESCAPES into the mutable param `b`) AND T255 (the frozen `a` + mutable `b`
    // receive the same object). Distinct sub-threats, distinct codes, one call.
    let got = codes(&format!(
        "{BOX}fn g(a: Box @ReadOnly, b: Box @Mut) -> i64 {{ return 0; }}\n\
         fn f(p: Box @ReadOnly) -> i64 {{ return g(p, p); }}"
    ));
    assert!(
        got.iter().any(|c| c == "T253"),
        "expected T253 escape, got {got:?}"
    );
    assert!(
        got.iter().any(|c| c == "T255"),
        "expected T255 exclusivity, got {got:?}"
    );
}

#[test]
fn exclusivity_composes_with_region_escape() {
    // A region-born value passed as a frozen+mutable aliasing pair trips BOTH the region
    // escape gate (T254 — v1 forbids a region value reaching any function) and the
    // exclusivity gate (T255). The analyses are orthogonal: the param-keyed exclusivity
    // partition fires regardless of the argument's region.
    let got = codes(&format!(
        "{BOX}fn sink(a: Box @ReadOnly, b: Box @Mut) -> i64 {{ return 0; }}\n\
         fn f() -> i64 ! {{ Alloc }} {{ region buf(64) {{ let p: Box = Box {{ v: 1 }}; \
             let _r: i64 = sink(p, p); }}; return 0; }}"
    ));
    assert!(
        got.iter().any(|c| c == "T255"),
        "expected T255, got {got:?}"
    );
    assert!(
        got.iter().any(|c| c == "T254"),
        "expected T254 region escape, got {got:?}"
    );
}

// ── Adversarial stress: deep nesting + generic-monomorph isolation ──────────────────

#[test]
fn deep_nested_same_root_fields_conflict_t255() {
    // AG-2c-9 at depth: a frozen DEEP field `o.mid.inner` and the mutable whole `o` share
    // root `o`, so they conservatively overlap (a field store could alias them) → T255.
    assert!(rejects(
        "record Box { v: i64 }\nrecord Mid { inner: Box }\nrecord Outer { mid: Mid }\n\
         fn sink(a: Box @ReadOnly, b: Outer @Mut) -> i64 { return 0; }\n\
         fn f() -> i64 ! { Alloc } { let o: Outer = Outer { mid: Mid { inner: Box { v: 1 } } }; \
             return sink(o.mid.inner, o); }",
        "T255"
    ));
}

#[test]
fn generic_monomorph_reentry_preserves_caller_alias_origin() {
    // `alias_origin` is saved/restored (mem::take) at every `check_function_block`, incl.
    // the generic-monomorph re-entry — so a generic callee's internal aliasing cannot
    // corrupt the CALLER's alias map. Here `idu` aliases its param internally; the caller's
    // `let a = p` alias must survive the monomorphized `idu(p)` call, so the later
    // `sink(a, p)` still resolves both to root `p` → T255. A leaked alias map would wipe
    // `a → p` and MISS the conflict.
    assert!(rejects(
        "record Box { v: i64 }\n\
         fn idu<T>(x: T) -> i64 { let _y: T = x; return 0; }\n\
         fn sink(a: Box @ReadOnly, b: Box @Mut) -> i64 { return 0; }\n\
         fn f() -> i64 ! { Alloc } { let p: Box = Box { v: 1 }; let a: Box = p; \
             let _u: i64 = idu(p); return sink(a, p); }",
        "T255"
    ));
}
