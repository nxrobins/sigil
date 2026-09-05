//! PR 1 of the borrowing-strings epic: the `substr` keystone.
//!
//! A `str` is an 8-byte fat-pointer header `[data_ptr: u32 @0, len: u32 @4]`
//! (identical layout to `Type::Slice`). `s.substr(start, end)` is a zero-copy
//! view: a new header with `data_ptr = src.data_ptr + start`, `len = end-start`,
//! pointing into the same bytes. Bounds are checked in the i64 domain BEFORE the
//! header is allocated (CF-S1), so an out-of-range or ≥2³² index traps rather
//! than silently truncating into a wrong-but-valid window.
//!
//! NOTE: a method call on a bare string LITERAL (`"x".substr(..)`) does not
//! parse today (P001) — a pre-existing grammar limit unrelated to substr; the
//! receiver must be a binding. Tests bind the literal to a `let` first.
//!
//! Convention: a tool returns `0 - <value>` (negative i64) recovered from the
//! trap message by `run_neg`; an out-of-bounds access is a genuine trap.

mod common;

use common::run_returning_negative as run_neg;

/// True iff the tool traps at runtime (an out-of-bounds / invalid access) rather
/// than returning a value. Used for the bounds-trap tests.
fn traps(source: &str) -> bool {
    common::tool_traps(source)
}

/// Wrap a `tool_main` body (str literals + intrinsics need no injection; a
/// `Vec<str>` body auto-injects vec.sigil).
fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    run_neg(&tool(body))
}

fn body_traps(body: &str) -> bool {
    traps(&tool(body))
}

// ── CF-S5: the Vec<str> verify-first gate ────────────────────────────────────

#[test]
fn vec_of_str_monomorphizes() {
    // CF-S5 gate: `Vec<str>` must monomorphize — a `str` is pointer-width,
    // stored in a Vec's i64 slot like any `T`. Push a literal `str`, read it
    // back, `byte_at` it. If this FAILS, STOP: a compiler monomorph gap to
    // surface, not to build substr/split on.
    let body = "    let v: Vec<str> = Vec::new();\n\
        \x20   let n: i64 = v.push(\"hello\");\n\
        \x20   let s: str = v.get(0);\n\
        \x20   return 0 - s.byte_at(0);";
    // 'h' == 104.
    assert_eq!(neg(body), 104);
}

#[test]
fn vec_of_str_two_elements_distinct() {
    // Two distinct literal strs in one Vec<str> keep their own bytes.
    let body = "    let v: Vec<str> = Vec::new();\n\
        \x20   let a: i64 = v.push(\"AB\");\n\
        \x20   let b: i64 = v.push(\"YZ\");\n\
        \x20   let s0: str = v.get(0);\n\
        \x20   let s1: str = v.get(1);\n\
        \x20   return 0 - (s0.byte_at(0) * 1000 + s1.byte_at(1));";
    // 'A'=65, 'Z'=90 → 65*1000 + 90 = 65090.
    assert_eq!(neg(body), 65090);
}

// ── substr: the keystone view ────────────────────────────────────────────────

#[test]
fn substr_round_trip() {
    // "hello"[1..4] == "ell"; byte_at(0)=='e'(101), len==3 — reads the view's
    // own header, proving data_ptr/len point at the right window.
    let body = "    let s: str = \"hello\";\n\
        \x20   let v: str = s.substr(1, 4);\n\
        \x20   return 0 - (v.byte_at(0) * 1000 + v.len());";
    assert_eq!(neg(body), 101_003);
}

#[test]
fn substr_consistency_oracle() {
    // EX-4 / MI-3 oracle: view.byte_at(i) == src.byte_at(start+i). "hello"[2..5]
    // == "llo"; v.byte_at(2)=='o' must equal s.byte_at(4).
    let body = "    let s: str = \"hello\";\n\
        \x20   let v: str = s.substr(2, 5);\n\
        \x20   return 0 - (v.byte_at(2) * 1000 + s.byte_at(4));";
    // 'o'==111 → equal halves → 111*1000 + 111 = 111111.
    assert_eq!(neg(body), 111_111);
}

#[test]
fn substr_empty_view() {
    // start==end → a len-0 view, total (no trap).
    let body = "    let s: str = \"hello\";\n\
        \x20   let v: str = s.substr(2, 2);\n\
        \x20   return 0 - (v.len() + 7000);";
    assert_eq!(neg(body), 7000);
}

#[test]
fn substr_full_view() {
    // [0..len] reproduces the whole string.
    let body = "    let s: str = \"hello\";\n\
        \x20   let n: i64 = s.len();\n\
        \x20   let v: str = s.substr(0, n);\n\
        \x20   return 0 - (v.len() * 1000 + v.byte_at(0));";
    // len 5, byte_at(0)=='h'(104) → 5104.
    assert_eq!(neg(body), 5104);
}

#[test]
fn substr_of_substr_nests() {
    // "hello"[1..4]=="ell"; "ell"[1..3]=="ll". The nested view bounds-checks
    // against ITS receiver's len, and its data_ptr is (base+1)+1.
    let body = "    let s: str = \"hello\";\n\
        \x20   let a: str = s.substr(1, 4);\n\
        \x20   let b: str = a.substr(1, 3);\n\
        \x20   return 0 - (b.byte_at(0) * 1000 + b.len());";
    // 'l'==108, len 2 → 108002.
    assert_eq!(neg(body), 108_002);
}

#[test]
fn empty_source_substr_is_total() {
    // CF-S8: substr("", 0, 0) == "" — no byte load, no trap.
    let body = "    let s: str = \"\";\n\
        \x20   let v: str = s.substr(0, 0);\n\
        \x20   return 0 - (v.len() + 50);";
    assert_eq!(neg(body), 50);
}

// ── EX-7: Vec<str> stores MIXED-PROVENANCE views (the hardened spike) ─────────

#[test]
fn vec_str_mixed_provenance() {
    // CF-S5 / EX-7: a literal AND a substr view (different data_ptr origins)
    // coexist in one Vec<str> and read back their own bytes — the payload split
    // actually stores.
    let body = "    let v: Vec<str> = Vec::new();\n\
        \x20   let lit: str = \"AB\";\n\
        \x20   let h: str = \"hello\";\n\
        \x20   let sub: str = h.substr(1, 3);\n\
        \x20   let x: i64 = v.push(lit);\n\
        \x20   let y: i64 = v.push(sub);\n\
        \x20   let s0: str = v.get(0);\n\
        \x20   let s1: str = v.get(1);\n\
        \x20   return 0 - (s0.byte_at(0) * 1000 + s1.byte_at(0));";
    // 'A'==65, "el".byte_at(0)=='e'(101) → 65101.
    assert_eq!(neg(body), 65_101);
}

// ── CF-S1: bounds traps (the security core) ──────────────────────────────────

#[test]
fn substr_start_gt_end_traps() {
    assert!(body_traps(
        "    let s: str = \"hello\";\n    let v: str = s.substr(4, 1);\n    return 0 - v.len();"
    ));
}

#[test]
fn substr_end_gt_len_traps() {
    assert!(body_traps(
        "    let s: str = \"hello\";\n    let v: str = s.substr(0, 99);\n    return 0 - v.len();"
    ));
}

#[test]
fn substr_negative_start_traps() {
    // -1 in the i64 domain → the start<0 guard traps (not a u32-wrap to huge).
    assert!(body_traps(
        "    let s: str = \"hello\";\n    let v: str = s.substr(0 - 1, 2);\n    return 0 - v.len();"
    ));
}

#[test]
fn substr_index_ge_2pow32_traps() {
    // MC-1 / CF-S1 crown jewel: 4294967296 (2³²) must NOT u32-wrap to 0 and
    // silently return "h..". The i64-domain `end > len` guard traps.
    assert!(body_traps(
        "    let s: str = \"hello\";\n    let v: str = s.substr(4294967296, 4294967297);\n    return 0 - v.len();"
    ));
}

#[test]
fn past_end_byte_at_on_view_traps() {
    // The view's len bounds byte_at — reading at the view's len (past its end,
    // though still inside the SOURCE) traps. Proves the view is properly bounded.
    assert!(body_traps(
        "    let s: str = \"hello\";\n    let v: str = s.substr(1, 3);\n    let b: i64 = v.byte_at(2);\n    return 0 - b;"
    ));
}

#[test]
fn substr_with_i32_param_indices() {
    // Regression for the type-check width stamp: an i32 index passed as a
    // function PARAMETER. The old AIR-side locals scan missed params (they live
    // in a separate list from `self.locals`) and defaulted to I64, mixing an
    // i32 value with i64 bounds constants. The type-check now stamps the index
    // width (I32) from the param type, so the AIR arm zero-extends correctly.
    let src = "module tool;\n\
        fn sub_first(s: str, i: i32, j: i32) -> i64 {\n\
        \x20   let v: str = s.substr(i, j);\n\
        \x20   return v.byte_at(0);\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let h: str = \"hello\";\n\
        \x20   return 0 - sub_first(h, 1, 3);\n\
        }\n";
    // "hello".substr(1, 3) == "el"; byte_at(0) == 'e' == 101.
    assert_eq!(run_neg(src), 101);
}
