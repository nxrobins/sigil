//! Owned-strings PR-1 / ET-1: the `str_from_raw` compile-time module gate (T257).
//!
//! The grep quarantine (`str_from_raw_quarantine.rs`) keeps the token out of
//! every stdlib `.sigil` but `string.sigil`. This suite proves the SECOND,
//! stronger layer: a compile-time gate that rejects the forge from any module
//! OTHER than `string` — so even a hand-written USER program (which the grep
//! never scans) cannot mint a `str` from raw memory. The boring limit is a
//! one-module allowlist; the fail-fast is T257, a hard error that aborts before
//! AIR.

/// Compile a full module `src` (with its own `module …;` header) and return the
/// diagnostic codes (empty = clean). Uncalled functions are still type-checked,
/// so the gate fires on a `fn` body without a dedicated call site.
use sigil_test_utils::pipeline::compile_module_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

// ── The gate: forging a `str` outside module `string` is T257 ───────────────

#[test]
fn str_from_raw_from_user_module_is_t257() {
    // The headline ET-1 fail-fast: a USER module forging a `str` from a raw
    // pointer + an attacker-chosen length is rejected before AIR.
    let src = "module tool;\n\
        fn forge() -> str ! { Alloc } { let b: i64 = alloc(2); return str_from_raw(b, 999999); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0; }\n";
    assert!(
        has(src, "T257"),
        "str_from_raw from `module tool` must be T257: {:?}",
        codes_of(src)
    );
}

#[test]
fn str_from_raw_from_another_stdlib_module_is_t257() {
    // The allowlist is EXACTLY `string` (singular). The borrowing `strings`
    // module builds views via `substr` (a method intrinsic) and never needs the
    // forge, so even it is rejected — the one-module limit is strict.
    let src = "module strings;\n\
        fn forge() -> str ! { Alloc } { let b: i64 = alloc(2); return str_from_raw(b, 2); }\n";
    assert!(
        has(src, "T257"),
        "str_from_raw from `module strings` must be T257: {:?}",
        codes_of(src)
    );
}

#[test]
fn str_from_raw_inside_string_module_is_not_t257() {
    // The sanctioned caller: inside `module string`, the forge is allowed (the
    // builders own the buffer they wrap). T257 must NOT fire.
    let src = "module string;\n\
        fn build() -> str ! { Alloc } { \
            let b: i64 = alloc(2); store8(b, 97); store8(b + 1, 98); return str_from_raw(b, 2); }\n";
    assert!(
        !has(src, "T257"),
        "str_from_raw inside `module string` must be clean of T257: {:?}",
        codes_of(src)
    );
}

// ── Shape checks: the forge is a 2-arg integer→str intrinsic ─────────────────

#[test]
fn str_from_raw_wrong_arity_is_rejected() {
    // One arg → arity error (T074). Checked inside `module string` so the arity
    // diagnostic is what surfaces, not the module gate.
    let src = "module string;\n\
        fn build() -> str ! { Alloc } { let b: i64 = alloc(2); return str_from_raw(b); }\n";
    assert!(
        has(src, "T074"),
        "str_from_raw with one arg must be an arity error: {:?}",
        codes_of(src)
    );
}

#[test]
fn str_from_raw_non_integer_arg_is_rejected() {
    // A `str` length argument is a type error (T075): the forge takes raw
    // integers, never a `str`.
    let src = "module string;\n\
        fn build(s: str) -> str ! { Alloc } { let b: i64 = alloc(2); return str_from_raw(b, s); }\n";
    assert!(
        has(src, "T075"),
        "str_from_raw with a `str` length must be a type error: {:?}",
        codes_of(src)
    );
}
