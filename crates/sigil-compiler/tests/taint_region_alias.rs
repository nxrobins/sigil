//! M6 — region-based memory taint (intra-procedural pointer alias analysis).
//!
//! The oracle-side gate for the store8-launder / pointer-alias rule in
//! `taint_check.rs`: each `alloc` mints a fresh REGION; a pointer local carries
//! its source's region; `store8(p, secret)` taints p's region; and every read
//! folds the region's current taint in. So a pointer aliased BEFORE a secret
//! store still surfaces the secret (the name-based M5b gap), while rebinding a
//! pointer to a fresh alloc correctly drops the old region (no false positive).
//!
//! WHY THIS FILE EXISTS: the feature's parity coverage used to live only in the
//! self-host differential (`sigil-runtime/tests/taint_check_differential.rs`).
//! The agentic-bench merge (2026-07-29) took main's `selfhost/taint_check.sigil`
//! wholesale — which has no region model — so the two REJECT fixtures were
//! withdrawn from the differential (a REJECT asserts oracle==selfhost, which
//! cannot hold while the oracle is strictly stronger). This file keeps the
//! ORACLE feature gated so it cannot silently regress; restore the differential
//! rejects once the selfhost mirror carries the region model.

use sigil_test_utils::pipeline::compile_module_codes;

const HDR: &str = "#[ring(outer)] module ext;\n";

/// M5b store-launder: `store8` a @Secret into an alloc buffer, then return the
/// (offset) base pointer. Region tainting makes the returned pointer @Secret →
/// T001. The base local is reached through `out + i` address arithmetic, so
/// `region_of_expr` must walk the `+`.
#[test]
fn store8_secret_then_return_offset_pointer_is_t001() {
    let codes = compile_module_codes(&format!(
        "{HDR}fn f(s: i64 @Secret) -> i64 ! {{ Alloc }} {{\n\
         \x20   let out: i64 = alloc(8);\n\
         \x20   let i: i64 = 0;\n\
         \x20   store8(out + i, s);\n\
         \x20   return out;\n}}\n"
    ));
    assert!(
        codes.iter().any(|c| c == "T001"),
        "storing a @Secret through a pointer and returning it must be T001; got {codes:?}"
    );
}

/// M6 alias: copy the pointer BEFORE the secret store, then return the ALIAS.
/// Name-based tainting (M5b) missed this; the region model taints the alloc's
/// region so the alias `q` — same region — surfaces the secret → T001.
#[test]
fn aliased_pointer_before_secret_store_is_t001() {
    let codes = compile_module_codes(&format!(
        "{HDR}fn f(s: i64 @Secret) -> i64 ! {{ Alloc }} {{\n\
         \x20   let out: i64 = alloc(8);\n\
         \x20   let q: i64 = out;\n\
         \x20   store8(out, s);\n\
         \x20   return q;\n}}\n"
    ));
    assert!(
        codes.iter().any(|c| c == "T001"),
        "returning an alias of a secret-stored region must be T001; got {codes:?}"
    );
}

/// Clean twin (no over-tainting): the store raises the WRITTEN buffer's region,
/// so returning a DIFFERENT public local is clean.
#[test]
fn store8_secret_then_return_different_local_is_clean() {
    let codes = compile_module_codes(&format!(
        "{HDR}fn f(s: i64 @Secret) -> i64 ! {{ Alloc }} {{\n\
         \x20   let out: i64 = alloc(8);\n\
         \x20   let keep: i64 = 0;\n\
         \x20   store8(out, s);\n\
         \x20   return keep;\n}}\n"
    ));
    assert!(
        codes.is_empty(),
        "returning a different public local must stay clean; got {codes:?}"
    );
}

/// Clean twin (the region payoff): alias `out`, then REBIND `out` to a fresh
/// alloc and store the secret into the fresh region. The old alias `q` keeps
/// the original region (untainted), so returning it is clean — a name-based
/// tracker would false-positive here.
#[test]
fn rebind_to_fresh_alloc_drops_old_region_clean() {
    let codes = compile_module_codes(&format!(
        "{HDR}fn f(s: i64 @Secret) -> i64 ! {{ Alloc }} {{\n\
         \x20   let mut out: i64 = alloc(8);\n\
         \x20   let q: i64 = out;\n\
         \x20   out = alloc(8);\n\
         \x20   store8(out, s);\n\
         \x20   return q;\n}}\n"
    ));
    assert!(
        codes.is_empty(),
        "an alias to a pre-rebind region must stay clean; got {codes:?}"
    );
}
