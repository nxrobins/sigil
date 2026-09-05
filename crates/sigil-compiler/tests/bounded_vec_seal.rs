//! BoundedVec PR-1 / ET-1: the construction-sealing gate (T258).
//!
//! A bounded collection's `count <= N` invariant is only TRUSTWORTHY if `count`
//! can't be forged. The fixed `[i64; N]` backing already makes any element access
//! memory-safe (a bad index traps), but a user could still write
//! `BoundedVec_i64_8 { count: 99 }` and LIE about the length — the killer the
//! adversarial teardown surfaced. The seal rejects it: a record defined in a
//! `bounded_*` stdlib module is constructible ONLY inside that module (via
//! `new()` / its methods), never via a direct record literal in user code.

use sigil_compiler::compile_tool;

/// Diagnostic codes from compiling a tool (empty = clean). `BoundedVec_i64_8`
/// tokens auto-inject `bounded_vec_i64.sigil` via the ambient pass.
use sigil_test_utils::pipeline::compile_tool_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

#[test]
fn forging_bounded_vec_in_user_module_is_t258() {
    // The killer: a direct record literal forging `count: 99` past the 8-cell
    // backing, lying about the length. Rejected before AIR.
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let v: BoundedVec_i64_8 = BoundedVec_i64_8 { data: [0, 0, 0, 0, 0, 0, 0, 0], count: 99 };\n\
        \x20   return 0 - v.len();\n\
        }\n";
    assert!(
        has(src, "T258"),
        "forging a BoundedVec literal in user code must be T258: {:?}",
        codes_of(src)
    );
}

#[test]
fn forging_with_zero_count_still_t258() {
    // Even a "well-formed-looking" forge is sealed — the gate is on the MODULE,
    // not the field values, so user code can never mint one directly.
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let v: BoundedVec_i64_8 = BoundedVec_i64_8 { data: [0, 0, 0, 0, 0, 0, 0, 0], count: 0 };\n\
        \x20   return 0 - v.len();\n\
        }\n";
    assert!(has(src, "T258"), "{:?}", codes_of(src));
}

#[test]
fn bounded_vec_new_is_allowed() {
    // The legit path: `::new()` (constructed INSIDE the sealed module) + the
    // methods compile clean from user code.
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let mut v: BoundedVec_i64_8 = BoundedVec_i64_8::new();\n\
        \x20   v.push(7);\n\
        \x20   return 0 - v.len();\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "BoundedVec_i64_8::new() + methods must compile: {:?}",
        codes_of(src)
    );
}

#[test]
fn bounded_vec_push_str_arg_is_t071() {
    // Method-arg soundness: `push`'s param is `val: i64`. A `str` literal where
    // an `i64` is expected was previously accepted (the method-arg check was
    // IntLit-only), then produced INVALID wasm at instantiation. It is now a
    // clean compile-time T071. Confirms the gap reproduces on a SHIPPED stdlib
    // method, not only on a user record.
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let mut v: BoundedVec_i64_8 = BoundedVec_i64_8::new();\n\
        \x20   let r: i64 = v.push(\"x\");\n\
        \x20   return r;\n\
        }\n";
    assert!(
        has(src, "T071"),
        "a str arg to BoundedVec_i64_8::push (param `val: i64`) must be T071, not invalid wasm: {:?}",
        codes_of(src)
    );
}

#[test]
fn user_record_construction_unaffected() {
    // The seal is scoped to `bounded_*` modules — a user's OWN record (in
    // `module tool`) is still freely constructible.
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

#[test]
fn forging_bounded_vec_64_is_t258() {
    // PR-2: the seal is keyed on the bounded_* MODULE, so it covers EVERY size in
    // the family. A forged `_64` literal (here built with the `[0; 64]` array-repeat
    // literal) is rejected exactly like the `_8` — the keystone doesn't weaken as
    // the family grows.
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let v: BoundedVec_i64_64 = BoundedVec_i64_64 { data: [0; 64], count: 99 };\n\
        \x20   return 0 - v.len();\n\
        }\n";
    assert!(
        has(src, "T258"),
        "forging a _64 literal in user code must be T258: {:?}",
        codes_of(src)
    );
}
