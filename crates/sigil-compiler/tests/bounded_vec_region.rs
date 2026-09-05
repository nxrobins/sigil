//! BoundedVec PR-1 / ET-4: region-escape parity.
//!
//! A BoundedVec's `[i64; N]` backing is a `BumpAlloc`; if it is built inside a
//! `region {}` (where the arena frees at region exit, DEF-2a) and then escapes,
//! the backing would dangle UNLESS the region-escape gate (T254) tracks it. ET-4
//! is parity: a region-born BoundedVec must obey the SAME escape discipline as a
//! region-born `Vec` — no bounded-collection exemption. This works on the existing
//! machinery (`region_of_value` scores the array-backed record region-born); this
//! suite pins the parity so a future change can't silently break it.

use sigil_test_utils::pipeline::compile_tool_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

/// Baseline: a region-born `Vec<i64>` escaping into a function argument.
const VEC_ESCAPE: &str = "module tool;\n\
    fn consume_v(v: Vec<i64>) -> i64 { return 0; }\n\
    pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
    \x20   region buf(64) { let v: Vec<i64> = Vec::new(); let r: i64 = consume_v(v); };\n\
    \x20   return 0;\n\
    }\n";

/// The BoundedVec mirror: a region-born `BoundedVec_i64_8` escaping the same way.
const BVEC_ESCAPE: &str = "module tool;\n\
    fn consume_b(b: BoundedVec_i64_8) -> i64 { return 0; }\n\
    pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
    \x20   region buf(64) { let v: BoundedVec_i64_8 = BoundedVec_i64_8::new(); let r: i64 = consume_b(v); };\n\
    \x20   return 0;\n\
    }\n";

#[test]
fn region_vec_escape_is_t254_baseline() {
    assert!(
        has(VEC_ESCAPE, "T254"),
        "baseline: a region `Vec` escape must be T254, got {:?}",
        codes_of(VEC_ESCAPE)
    );
}

#[test]
fn region_bounded_vec_escape_has_parity_with_vec() {
    // ET-4: the BoundedVec escape must produce the SAME T254 verdict as the Vec
    // escape — the array-backed record is region-tracked exactly like the buffer
    // a Vec wraps, so the dangling escape the teardown feared is rejected.
    assert_eq!(
        has(BVEC_ESCAPE, "T254"),
        has(VEC_ESCAPE, "T254"),
        "ET-4 parity broken — bvec escape codes={:?}, vec escape codes={:?}",
        codes_of(BVEC_ESCAPE),
        codes_of(VEC_ESCAPE)
    );
}
