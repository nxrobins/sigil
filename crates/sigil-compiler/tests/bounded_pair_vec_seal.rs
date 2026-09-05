//! BoundedPairVec (Phase 2 zip/enumerate): construction-seal (T258). The seal is
//! STRUCTURAL — keyed on the `bounded_*` defining-module-name prefix — so the
//! `bounded_pair_vec_i64` records inherit it with no name list. The `count <= N`
//! invariant is only trustworthy because user code can never forge a
//! `BoundedPairVec_i64_i64_8 { count: 99 }` literal.

use sigil_compiler::compile_tool;

use sigil_test_utils::pipeline::compile_tool_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

#[test]
fn forging_bounded_pair_vec_is_t258() {
    // The killer: a forged `count: 99` over an 8-cell backing, lying about length.
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let p: BoundedPairVec_i64_i64_8 = BoundedPairVec_i64_i64_8 { fst: [0; 8], snd: [0; 8], count: 99 };\n\
        \x20   return 0 - p.len();\n\
        }\n";
    assert!(
        has(src, "T258"),
        "forging a BoundedPairVec literal must be T258: {:?}",
        codes_of(src)
    );
}

#[test]
fn forging_bounded_pair_vec_256_is_t258() {
    // Covers another size (the seal is per-record-name, structural).
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let p: BoundedPairVec_i64_i64_256 = BoundedPairVec_i64_i64_256 { fst: [0; 256], snd: [0; 256], count: 0 };\n\
        \x20   return 0 - p.len();\n\
        }\n";
    assert!(
        has(src, "T258"),
        "forging a BoundedPairVec_256 literal must be T258: {:?}",
        codes_of(src)
    );
}

#[test]
fn bounded_pair_vec_new_and_methods_allowed() {
    // ::new() + push + get + len compile clean (the public sealed API).
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let mut p: BoundedPairVec_i64_i64_8 = BoundedPairVec_i64_i64_8::new();\n\
        \x20   let _a: i64 = p.push(1, 2);\n\
        \x20   let o: Option<(i64, i64)> = p.get(0);\n\
        \x20   let pr: (i64, i64) = o.unwrap_or((0, 0));\n\
        \x20   let (x, y) = pr;\n\
        \x20   return 0 - (x + y);\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "::new() + methods must compile: {:?}",
        codes_of(src)
    );
}

#[test]
fn zip_enumerate_produce_pair_vec() {
    // zip/enumerate construct the (sealed, other-module) pair vec via its public API.
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let mut v: BoundedVec_i64_8 = BoundedVec_i64_8::new();\n\
        \x20   let _a: i64 = v.push(5);\n\
        \x20   let _b: i64 = v.push(6);\n\
        \x20   let p: BoundedPairVec_i64_i64_8 = v.enumerate();\n\
        \x20   return 0 - p.len();\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "zip/enumerate must construct a pair vec via the public API: {:?}",
        codes_of(src)
    );
}

#[test]
fn user_record_construction_unaffected() {
    let src = "module tool;\n\
        record Point { x: i64, y: i64 }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let p: Point = Point { x: 3, y: 4 };\n\
        \x20   return 0 - p.x;\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "a user's own record must still be constructible: {:?}",
        codes_of(src)
    );
}
