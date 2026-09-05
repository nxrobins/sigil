//! BoundedMap/Set (Phase 4): construction-seal (T258) + region-escape parity
//! (T254). Mirrors `bounded_vec_seal.rs` / `bounded_vec_region.rs`. The seal is
//! STRUCTURAL — keyed on the `bounded_*` defining-module-name prefix — so the
//! `bounded_map_*` / `bounded_set_*` records inherit it with no name list. The
//! `count <= N` invariant is only trustworthy because user code can never forge a
//! `BoundedMap_… { count: 99 }` literal.

use sigil_compiler::compile_tool;

use sigil_test_utils::pipeline::compile_tool_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

#[test]
fn forging_bounded_map_i64_is_t258() {
    // The killer: a forged `count: 99` over a 64-cell backing, lying about length.
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64 { keys: [0; 64], vals: [0; 64], count: 99 };\n\
        \x20   return 0 - m.len();\n\
        }\n";
    assert!(
        has(src, "T258"),
        "forging a BoundedMap literal must be T258: {:?}",
        codes_of(src)
    );
}

#[test]
fn forging_bounded_map_str_is_t258() {
    // Covers the str family + the `bounded_map_str` module (the seal is per-module).
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let m: BoundedMap_str_str_64 = BoundedMap_str_str_64 { keys: [\"\"; 64], vals: [\"\"; 64], count: 5 };\n\
        \x20   return 0 - m.len();\n\
        }\n";
    assert!(
        has(src, "T258"),
        "forging a str BoundedMap literal must be T258: {:?}",
        codes_of(src)
    );
}

#[test]
fn forging_bounded_set_is_t258() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let s: BoundedSet_i64_64 = BoundedSet_i64_64 { elems: [0; 64], count: 99 };\n\
        \x20   return 0 - s.len();\n\
        }\n";
    assert!(
        has(src, "T258"),
        "forging a BoundedSet literal must be T258: {:?}",
        codes_of(src)
    );
}

#[test]
fn bounded_map_new_is_allowed() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n\
        \x20   let _r: i64 = m.insert(1, 2);\n\
        \x20   return 0 - m.len();\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "::new() + methods must compile: {:?}",
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

// ── region-escape parity (T254) ──────────────────────────────────────────────

const MAP_ESCAPE: &str = "module tool;\n\
    fn consume_m(m: Map<str, i64>) -> i64 { return 0; }\n\
    pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
    \x20   region buf(64) { let m: Map<str, i64> = Map::new(); let r: i64 = consume_m(m); };\n\
    \x20   return 0;\n\
    }\n";

const BMAP_ESCAPE: &str = "module tool;\n\
    fn consume_b(b: BoundedMap_i64_i64_64) -> i64 { return 0; }\n\
    pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
    \x20   region buf(64) { let m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new(); let r: i64 = consume_b(m); };\n\
    \x20   return 0;\n\
    }\n";

#[test]
fn region_map_escape_baseline_is_t254() {
    assert!(
        has(MAP_ESCAPE, "T254"),
        "baseline: a region Map escape must be T254, got {:?}",
        codes_of(MAP_ESCAPE)
    );
}

#[test]
fn region_bounded_map_escape_parity_with_map() {
    // The array-backed sealed record is region-tracked exactly like the unbounded
    // Map's buffer — a region-born BoundedMap escape gets the SAME T254 verdict.
    // (AG-BM5: BoundedMap adds no element-lifetime tracking beyond this parity.)
    assert_eq!(
        has(BMAP_ESCAPE, "T254"),
        has(MAP_ESCAPE, "T254"),
        "region-escape parity broken — bmap={:?}, map={:?}",
        codes_of(BMAP_ESCAPE),
        codes_of(MAP_ESCAPE)
    );
}
