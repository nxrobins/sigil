//! Owned-strings PR-4: the adversarial-ritual capstone — COMPILE-level gates.
//!
//! Pins the Constraint-Matrix invariants where owned construction meets the
//! capability gates:
//!   * default-frozen / T253 — a builder returns a FRESH value (clean); returning
//!     an input param is the rejected hazard.
//!   * ET-3 taint — `@SecretCT` survives a builder (the call-join lub), so it
//!     cannot be silently laundered to `@Public` (T001). No T025 timing leak.
//!   * ET-2 regions — an owned str built INSIDE a region is region-born, so its
//!     escape is rejected (T254), parity with any other in-region allocation.
//!
//! Runtime composition + UTF-8 preservation live in
//! `crates/sigil-runtime/tests/str_owned_compose.rs`.

use sigil_test_utils::pipeline::compile_module_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

fn clean(src: &str) -> bool {
    codes_of(src).is_empty()
}

// ── default-frozen / T253: build returns FRESH, returning an input is the hazard ──

#[test]
fn concat_result_is_fresh_no_t253() {
    // The builder returns `str_from_raw(...)`, a fresh value — NOT a frozen param
    // — so wrapping it in a user fn that returns the concat result is clean.
    let src = "module tool;\n\
        fn wrap(a: str, b: str) -> str ! { Alloc } { return a.concat(b); }\n";
    assert!(
        clean(src),
        "returning a fresh concat result must be clean: {:?}",
        codes_of(src)
    );
}

#[test]
fn returning_a_str_param_is_clean_str_is_immutable() {
    // The plan flagged a return-an-input fast-path as a T253 hazard — but
    // empirically, returning a `str` PARAM is CLEAN, and soundly so: `str` is not
    // in `is_aliasable_type`, because v1 `str` has NO mutators (only reads:
    // `byte_at`/`len`/`substr`). T253 exists to stop handing a MUTABLE handle to a
    // frozen value; with no str-mutation surface there is nothing to widen, so the
    // hazard is moot for `str` (it still fires for a mutable record/Vec — see
    // def1_flip). Owned construction returns fresh anyway; this pins the honest
    // boundary. (A FRESH return is also clean — see `concat_result_is_fresh`.)
    let src = "module tool;\n\
        fn passthru(a: str, b: str) -> str { return a; }\n";
    assert!(
        clean(src),
        "returning a frozen str param is clean (str is immutable): {:?}",
        codes_of(src)
    );
}

// ── ET-3 taint: @SecretCT survives a builder; laundering to @Public is rejected ──

#[test]
fn secretct_concat_requires_an_explicit_parameter_contract() {
    // `str_concat` has default-public parameters and SIGIL has no separate public-length
    // contract for strings. Passing @SecretCT through that erased/default contract would
    // let the helper branch or loop on data the body sees as public, so it fails closed.
    let src = "module tool;\n\
        fn f(s: str @SecretCT) -> str @SecretCT ! { Alloc } { return s.concat(\"x\"); }\n";
    assert!(
        has(src, "T001"),
        "secret concat through a public helper contract must be T001: {:?}",
        codes_of(src)
    );
}

#[test]
fn secret_concat_to_public_is_t001_no_laundering() {
    // THE ET-3 pin: the same secret concat, returned as `@Public`, is a taint
    // downgrade (T001). Owned construction is NOT a laundering channel — the
    // call-join carries the secret into the result, which `@Public` cannot accept.
    let src = "module tool;\n\
        fn f(s: str @SecretCT) -> str @Public ! { Alloc } { return s.concat(\"x\"); }\n";
    assert!(
        has(src, "T001"),
        "secret concat downgraded to @Public must be T001: {:?}",
        codes_of(src)
    );
}

#[test]
fn secretct_itoa_requires_an_explicit_parameter_contract() {
    // Integer formatting has value-dependent control and output length. The helper's
    // default-public parameter cannot accept @SecretCT merely because the caller
    // retains the result label.
    let src = "module tool;\n\
        fn f(n: i64 @SecretCT) -> str @SecretCT ! { Alloc } { return n.itoa(); }\n";
    assert!(
        has(src, "T001"),
        "secret itoa through a public helper contract must be T001: {:?}",
        codes_of(src)
    );
}

#[test]
fn secret_itoa_to_public_is_t001() {
    let src = "module tool;\n\
        fn f(n: i64 @SecretCT) -> str @Public ! { Alloc } { return n.itoa(); }\n";
    assert!(
        has(src, "T001"),
        "secret itoa downgraded to @Public must be T001: {:?}",
        codes_of(src)
    );
}

// ── ET-2 regions: an owned str built in a region is region-born → escape is T254 ──

#[test]
fn concat_built_in_region_escaping_is_t254() {
    // The ET-2 invariant applied to the BUILDER (not just str_from_raw): a concat
    // result allocated inside a `region {}` is region-born, so passing it to a
    // function (an escape) after the region would dangle → T254.
    let src = "module tool;\n\
        fn sink(s: str) -> i64 { return 0; }\n\
        fn f(a: str, b: str) -> i64 ! { Alloc } { \
            region buf(64) { let r: str = a.concat(b); let _x: i64 = sink(r); }; \
            return 0; }\n";
    assert!(
        has(src, "T254"),
        "an owned str built in a region escaping must be T254: {:?}",
        codes_of(src)
    );
}

#[test]
fn concat_used_inside_region_is_clean() {
    // The control: an owned str built AND read inside the region never escapes, so
    // it is clean — the gate does not over-reject in-region use. (A scalar `len`
    // could copy out, but here it is consumed in-region to keep the focus on the
    // str's own lifetime.)
    let src = "module tool;\n\
        fn f(a: str, b: str) -> i64 ! { Alloc } { \
            region buf(64) { let r: str = a.concat(b); let _len: i64 = r.len(); }; \
            return 0; }\n";
    assert!(
        clean(src),
        "an owned str used only inside its region must be clean: {:?}",
        codes_of(src)
    );
}
