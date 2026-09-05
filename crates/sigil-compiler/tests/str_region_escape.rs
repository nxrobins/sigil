//! Owned-strings PR-1 / ET-2: the region-escape parity measurement.
//!
//! The adversarial teardown warned that owned strings could compose unsoundly
//! with regions: the bump arena DOES free at region exit (DEF-2a reclamation),
//! so a `str` built inside a `region {}` and escaped would dangle UNLESS the
//! region-escape gate (T254) tracks it. The ET-2 fail-fast is parity: an
//! owned-string allocation in a region must obey the SAME escape discipline as
//! any other `! { Alloc }` allocation (a `Vec::new()`), with NO string-specific
//! exemption.
//!
//! This suite MEASURES that parity directly: it escapes a region-born `Vec`
//! (the baseline) and a region-born owned `str` (built via `str_from_raw`) the
//! same way, and asserts the diagnostics match. Both programs are `module
//! string;` so the stdlib-private forge is permitted (T257).

use sigil_test_utils::pipeline::compile_module_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

/// Baseline: a region-born `Vec<i64>` escaping into a function argument.
const VEC_ESCAPE: &str = "module string;\n\
    fn consume_vec(v: Vec<i64>) -> i64 { return 0; }\n\
    fn test() -> i64 ! { Alloc } { \
        region buf(64) { let v: Vec<i64> = Vec::new(); let _r: i64 = consume_vec(v); }; \
        return 0; }\n";

/// The owned-string mirror: a region-born `str` (forged from a region `alloc`)
/// escaping into a function argument the SAME way.
const STR_ESCAPE: &str = "module string;\n\
    fn consume_str(s: str) -> i64 { return 0; }\n\
    fn test() -> i64 ! { Alloc } { \
        region buf(64) { let b: i64 = alloc(2); let s: str = str_from_raw(b, 2); \
            let _r: i64 = consume_str(s); }; \
        return 0; }\n";

#[test]
fn region_vec_escape_is_t254_baseline() {
    // Anchor: a region-allocated Vec escaping the region is T254 today.
    assert!(
        has(VEC_ESCAPE, "T254"),
        "baseline: a region `Vec` escape must be T254, got {:?}",
        codes_of(VEC_ESCAPE)
    );
}

#[test]
fn region_str_escape_has_parity_with_vec() {
    // ET-2: the owned-str escape must produce the SAME T254 verdict as the Vec
    // escape — the str built in the region is region-tracked exactly like the
    // buffer it wraps, so the dangling escape the teardown feared is rejected.
    assert_eq!(
        has(STR_ESCAPE, "T254"),
        has(VEC_ESCAPE, "T254"),
        "ET-2 parity broken — str escape codes={:?}, vec escape codes={:?}",
        codes_of(STR_ESCAPE),
        codes_of(VEC_ESCAPE)
    );
}
