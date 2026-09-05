//! DEF-2a PR-3 — `@SecretCT @Region` composition.
//!
//! The `docs/memory-model.md` keystone is *"secret material that physically cannot
//! outlive the request."* It is delivered by the COMPOSITION of two ORTHOGONAL passes,
//! each guarding the same value through a different mechanism:
//!
//!   * the **lifetime axis** — the region-escape gate (DEF-2a, `T254`, in the
//!     type-check region pass): a value heap-allocated inside a `region {}` may not
//!     flow to any longer-lived sink, so it is *physically* reclaimed at block exit; and
//!   * the **confidentiality axis** — information-flow taint (`T001`/CT rules, in the
//!     taint pass): a `@SecretCT` value may not be silently downgraded to `@Public`; a
//!     downgrade requires the explicit `declassify_ct` → `declassify` capability ladder.
//!
//! These passes are independent — neither annotation weakens the other. This suite
//! pins that independence:
//!
//!   1. the region gate fires on a `@SecretCT` aliasable value EXACTLY as on a public
//!      one (same `T254`), and even when the destination would ACCEPT the secret taint
//!      (a `@SecretCT`-parameter sink) — proving lifetime is enforced separately from
//!      confidentiality;
//!   2. a secret SCALAR copied within the region stays usable and stays secret (the
//!      lifetime gate correctly exempts copies; the taint is preserved by inference);
//!   3. the confidentiality axis fires on its own (`T001`), independent of any region;
//!      and
//!   4. the taint/declassify machinery behaves identically inside a region as outside —
//!      regions do not interfere with information flow.
//!
//! Per the epic plan this is a TC-only, byte-identical PR: region escape rides the same
//! sinks taint already guards, so no new compiler code is required — only the
//! composition is proven and documented (`docs/specs/regions.md`).

use sigil_compiler::{compile_named_module, compile_tool};

/// Region + taint harness: a `Point` record, a `sink` taking a `@Public` `Point`, and an
/// `ssink` taking — and returning — a `@SecretCT` `Point`. `body` is spliced into `f`.
/// Returns the emitted diagnostic codes (empty ⇒ clean compile).
fn codes(body: &str) -> Vec<String> {
    let src = format!(
        "module tool;\n\
         record Point {{ x: i64, y: i64 }}\n\
         fn sink(p: Point) -> i64 {{ return p.x; }}\n\
         fn ssink(p: Point @SecretCT) -> i64 @SecretCT {{ return p.x; }}\n\
         fn f() -> i64 ! {{ Alloc }} {{ {body} }}\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{ return f(); }}\n"
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

/// Declassify-ladder harness: declares the two declassification cap types and threads a
/// `@SecretCT` secret + both caps into `f`, which `body` may declassify. Mirrors
/// `taint_constant_time_phase_b.rs`. Returns the emitted diagnostic codes.
fn codes_caps(body: &str) -> Vec<String> {
    let src = format!(
        "module ext;\n\
         cap type DeclassifyCT {{}}\n\
         cap type Declassify {{}}\n\
         fn f(s: i64 @SecretCT, c: DeclassifyCT, d: Declassify) -> i64 @Public ! {{ Alloc }} {{ {body} }}\n"
    );
    match compile_named_module("region_secret_caps.sigil", &src) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn has(body_codes: &[String], code: &str) -> bool {
    body_codes.iter().any(|c| c == code)
}

// ── the lifetime axis (T254) guards secret material — the memory-model keystone ──

#[test]
fn secret_region_record_cannot_escape_to_public_sink() {
    // "Secret material that physically cannot outlive the request": a `@SecretCT` record
    // born in a region cannot escape via a call argument — `T254`, exactly as a public
    // record would (the region gate is taint-agnostic).
    assert!(has(
        &codes(
            "region buf(64) { let p: Point @SecretCT = Point { x: 1, y: 2 }; \
             let _r: i64 = sink(p); }; return 0;"
        ),
        "T254"
    ));
}

#[test]
fn secret_region_record_cannot_escape_even_into_a_secret_sink() {
    // The independence proof: even a sink that ACCEPTS the secret taint
    // (`ssink(p: Point @SecretCT)`) cannot receive a region-born secret — the LIFETIME
    // gate fires (`T254`) regardless of whether confidentiality would be satisfied.
    assert!(has(
        &codes(
            "region buf(64) { let p: Point @SecretCT = Point { x: 1, y: 2 }; \
             let _r: i64 @SecretCT = ssink(p); }; return 0;"
        ),
        "T254"
    ));
}

#[test]
fn public_region_record_escape_is_the_same_t254() {
    // Baseline: a NON-secret region record escaping yields the SAME code (`T254`) as the
    // secret one above — the region gate keys on birth-depth, never on taint.
    assert!(has(
        &codes(
            "region buf(64) { let p: Point = Point { x: 1, y: 2 }; \
             let _r: i64 = sink(p); }; return 0;"
        ),
        "T254"
    ));
}

// ── negative controls: a secret stays usable and secret INSIDE its region ────────

#[test]
fn secret_scalar_copied_within_region_compiles() {
    // A secret SCALAR read out of a region-born secret record and kept within the region
    // is fully usable: the lifetime gate exempts the copy (birth-depth 0), and the taint
    // is preserved by inference (no silent downgrade). Nothing escapes; clean.
    assert!(
        codes(
            "region buf(64) { let p: Point @SecretCT = Point { x: 1, y: 2 }; \
             let _n: i64 @SecretCT = p.x; }; return 0;"
        )
        .is_empty()
    );
}

#[test]
fn secret_record_constructed_and_discarded_in_region_compiles() {
    // The purest statement of the keystone: a `@SecretCT` record is allocated in the
    // region and never escapes — it is reclaimed at block exit. Compiles clean.
    assert!(
        codes("region buf(64) { let _p: Point @SecretCT = Point { x: 1, y: 2 }; }; return 0;")
            .is_empty()
    );
}

// ── the confidentiality axis (T001) is enforced independently of regions ─────────

#[test]
fn secret_downgraded_to_public_is_t001_without_any_region() {
    // The taint axis exists and fires on its own: returning a `@SecretCT` value as a
    // `@Public` result without declassification is `T001` — orthogonal to the region
    // gate (no region here). Composed with the lifetime tests above, this is the "both
    // axes, independent" guarantee.
    assert!(has(&codes("let s: i64 @SecretCT = 7; return s;"), "T001"));
}

// ── the taint/declassify machinery is unaffected by a region scope ───────────────

#[test]
fn declassify_ladder_inside_a_region_compiles_like_outside() {
    // The full `@SecretCT → @Secret → @Public` declassify ladder behaves identically
    // inside a `region {}` as at function scope — regions do not interfere with
    // information flow. (The scalar result is region-independent: a copy, birth-depth 0.)
    let inside = codes_caps(
        "region buf(64) { let mid: i64 @Secret = declassify_ct(s, c); \
         let _r: i64 @Public = declassify(mid, d); }; return 0;",
    );
    let outside =
        codes_caps("let mid: i64 @Secret = declassify_ct(s, c); return declassify(mid, d);");
    assert!(
        inside.is_empty(),
        "ladder in region should be clean, got {inside:?}"
    );
    assert!(
        outside.is_empty(),
        "ladder at fn scope should be clean, got {outside:?}"
    );
}
