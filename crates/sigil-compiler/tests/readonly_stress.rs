//! PR-5 of the mutation-as-capability epic — the capstone: `@Mut` flip-readiness
//! (NC-4), orthogonality (H7: taint × mutability are independent axes), and an
//! adversarial stress matrix over the closed launder set.
//!
//! No new enforcement lives here — every gate landed in PR-1..PR-3 and the lint
//! in PR-4. This file proves the axes COMPOSE, that `@Mut` is represented
//! distinctly so the DEF-1 default-flip is a one-line predicate change, and that
//! the gates hold under cross-cutting combinations.

use sigil_compiler::ast::Mutability;
use sigil_compiler::compile_tool;

/// Wrap `defs` in a module with a trivial `tool_main`, compile, return the codes.
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

fn rejects_t251(defs: &str) -> bool {
    codes(defs).iter().any(|c| c == "T251")
}

fn rejects_t253(defs: &str) -> bool {
    codes(defs).iter().any(|c| c == "T253")
}

fn compiles_clean(defs: &str) -> bool {
    codes(defs).is_empty()
}

const POINT: &str = "record Point { x: i64, y: i64 }\n";

// ── @Mut flip-readiness (NC-4): the predicate-swap semantics ──────────────────

#[test]
fn is_frozen_predicate_freezes_readonly_and_bare() {
    // The SINGLE predicate the gates (seed / call-arg / method / exclusivity) route
    // through. Since DEF-1 (the H5 default-flip, `ReadOnly => ReadOnly | Default`)
    // both `@ReadOnly` AND bare (`Default`) freeze; only `@Mut` is mutable.
    assert!(Mutability::ReadOnly.is_frozen(), "@ReadOnly freezes");
    assert!(
        Mutability::Default.is_frozen(),
        "bare is now frozen (the DEF-1 default-flip)"
    );
    assert!(!Mutability::Mut.is_frozen(), "@Mut is the mutable opt-up");
}

#[test]
fn mut_is_distinct_from_bare() {
    // NC-4: `@Mut` is NEVER collapsed into `Default`. The flip needs the bit to
    // distinguish "explicitly mutable" (`@Mut`, stays mutable post-flip) from
    // "bare" (`Default`, becomes frozen) — so the two states must compare unequal.
    assert_ne!(Mutability::Mut, Mutability::Default);
}

#[test]
fn mut_param_behaves_as_bare_today() {
    // `@Mut` compiles and is unrestricted exactly like a bare param (it carries
    // only the flip-readiness bit). A write through a `@Mut` param is allowed.
    assert!(compiles_clean(&format!(
        "{POINT}fn f(p: Point @Mut) -> i64 {{ p.x = 10; return p.x; }}"
    )));
}

// ── Orthogonality (H7): taint (@SecretCT) × mutability (@ReadOnly) ─────────────

#[test]
fn secret_ct_does_not_mask_readonly_either_order() {
    // The mutation gate keys on mutability alone, so `@ReadOnly` still rejects the
    // write whether the taint annotation precedes or follows it — the two axes are
    // independent and neither masks the other.
    assert!(rejects_t251(&format!(
        "{POINT}fn f(p: Point @SecretCT @ReadOnly) -> i64 {{ p.x = 10; return 0; }}"
    )));
    assert!(rejects_t251(&format!(
        "{POINT}fn f(p: Point @ReadOnly @SecretCT) -> i64 {{ p.x = 10; return 0; }}"
    )));
}

#[test]
fn secret_ct_bare_is_now_frozen_but_mut_still_writes() {
    // Post-DEF-1, a BARE `@SecretCT` param is frozen like any bare param, so a write
    // through it is rejected (T251) — default-frozen applies regardless of taint.
    assert!(rejects_t251(&format!(
        "{POINT}fn f(p: Point @SecretCT) -> i64 {{ p.x = 10; return 0; }}"
    )));
    // Taint stays ORTHOGONAL to mutability (H7): `@SecretCT @Mut` opts back up and the
    // write compiles — the taint never drove the gate, `@Mut` does.
    let mut_ct_codes = codes(&format!(
        "{POINT}fn f(p: Point @SecretCT @Mut) -> i64 {{ p.x = 10; return 0; }}"
    ));
    assert!(
        mut_ct_codes.is_empty(),
        "SecretCT taint must remain orthogonal to @Mut, got {mut_ct_codes:?}"
    );
}

// ── Adversarial stress: the closed launder set under cross-cutting combos ──────

#[test]
fn three_hop_let_launder_is_caught() {
    // NC-1 propagation is transitive across arbitrarily many `let` hops.
    assert!(rejects_t251(&format!(
        "{POINT}fn f(p: Point @ReadOnly) -> i64 {{ let a: Point = p; let b: Point = a; \
         let c: Point = b; c.x = 10; return 0; }}"
    )));
}

#[test]
fn readonly_vec_into_mutating_free_fn_is_t253() {
    // The re-widen launder via a free call: a frozen Vec passed to a `@Mut` Vec param.
    assert!(rejects_t253(
        "fn sink(v: Vec<i64> @Mut) -> i64 { return v.len(); }\n\
         fn f(v: Vec<i64> @ReadOnly) -> i64 { return sink(v); }"
    ));
}

#[test]
fn compound_index_store_on_readonly_array_is_t251() {
    // NC-2 op-agnostic gate, on an INDEX place: `a[0] += 1` is a write-through.
    assert!(rejects_t251(
        "fn f(a: [i64; 4] @ReadOnly) -> i64 { a[0] += 1; return 0; }"
    ));
}

#[test]
fn reading_then_mutating_a_readonly_vec_rejects_only_the_mutation() {
    // The read (`get`) is legal through the frozen receiver; the mutation (`push`)
    // is the T253. A legal read in the same body does not launder the write.
    assert!(rejects_t253(
        "fn f(v: Vec<i64> @ReadOnly) -> i64 ! { Alloc } { let x: i64 = v.get(0); return v.push(x); }"
    ));
}

#[test]
fn freeze_on_entry_chain_compiles() {
    // mutable → `@ReadOnly` (freeze on entry) is always allowed (H6), and the
    // callee reads through the frozen handle cleanly.
    assert!(compiles_clean(&format!(
        "{POINT}fn reader(p: Point @ReadOnly) -> i64 {{ return p.x; }}\n\
         fn f(p: Point) -> i64 {{ return reader(p); }}"
    )));
}

#[test]
fn mutating_a_copied_out_primitive_is_free() {
    // The gates exclude primitive copies: reading a readonly field into a local
    // i64 and mutating THAT local is fine — no aliasing of the frozen object.
    assert!(compiles_clean(&format!(
        "{POINT}fn f(p: Point @ReadOnly) -> i64 {{ let mut n: i64 = p.x; n = n + 1; return n; }}"
    )));
}
