//! Owned-strings PR-1: the `str_from_raw` round-trip spike (the ET-1 soundness
//! proof that the forged header is CORRECT).
//!
//! `str_from_raw(ptr, len)` mints a fresh `str` fat-pointer `[data_ptr, len]`
//! from raw memory. This suite builds strings BY HAND — `alloc` a buffer,
//! `store8` the bytes, wrap via `str_from_raw` — then reads the header back
//! through the public `len`/`byte_at`/`substr` surface. If the forged header's
//! `data_ptr`/`len` point at the bytes we wrote, the round-trip recovers them
//! exactly. The forge is stdlib-private (T257), so every program here is a
//! `module string;` tool — the one module the gate permits.
//!
//! Convention (mirrors `str_substr.rs`): a tool returns `0 - <value>` and the
//! magnitude is recovered from the trap message by `run_neg`.

mod common;

use common::run_returning_negative as run_neg;

/// Wrap a `tool_main` body in `module string;` so the stdlib-private
/// `str_from_raw` forge is permitted (the only module the T257 gate allows).
fn string_tool(body: &str) -> String {
    format!(
        "module string;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    run_neg(&string_tool(body))
}

#[test]
fn str_from_raw_round_trip_two_bytes() {
    // Build "ab": alloc 2, store 'a'/'b', wrap, read header back. data_ptr + len
    // must point at the bytes we wrote.
    let body = "    let buf: i64 = alloc(2);\n\
        \x20   store8(buf, 97);\n\
        \x20   store8(buf + 1, 98);\n\
        \x20   let s: str = str_from_raw(buf, 2);\n\
        \x20   return 0 - (s.len() * 1000000 + s.byte_at(0) * 1000 + s.byte_at(1));";
    // len=2, 'a'=97, 'b'=98 → 2_097_098.
    assert_eq!(neg(body), 2_097_098);
}

#[test]
fn str_from_raw_three_bytes_each_position() {
    // Build "XYZ": confirm every byte position reads back distinctly (not just
    // byte 0) and len is exact — rules out an off-by-one in the header stores.
    let body = "    let buf: i64 = alloc(3);\n\
        \x20   store8(buf, 88);\n\
        \x20   store8(buf + 1, 89);\n\
        \x20   store8(buf + 2, 90);\n\
        \x20   let s: str = str_from_raw(buf, 3);\n\
        \x20   return 0 - (s.byte_at(0) * 1000000 + s.byte_at(1) * 1000 + s.byte_at(2) + s.len());";
    // 'X'=88,'Y'=89,'Z'=90, len=3 → 88*1e6 + 89*1000 + 90 + 3 = 88_089_093.
    assert_eq!(neg(body), 88_089_093);
}

#[test]
fn str_from_raw_len_zero_is_empty() {
    // A zero-length forge is a valid empty `str`: len 0, is_empty true. (The
    // builders' `n=0` boundary — ET-4 — rides on this.)
    let body = "    let buf: i64 = alloc(0);\n\
        \x20   let s: str = str_from_raw(buf, 0);\n\
        \x20   return 0 - (s.len() + 100);";
    // len 0 → 0 + 100 = 100.
    assert_eq!(neg(body), 100);
}

#[test]
fn str_from_raw_interops_with_substr() {
    // The provenance payoff: an OWNED str (forged) flows through the BORROWING
    // surface for free. Build "XYZ", take substr(1,3)=="YZ", read the view.
    let body = "    let buf: i64 = alloc(3);\n\
        \x20   store8(buf, 88);\n\
        \x20   store8(buf + 1, 89);\n\
        \x20   store8(buf + 2, 90);\n\
        \x20   let s: str = str_from_raw(buf, 3);\n\
        \x20   let v: str = s.substr(1, 3);\n\
        \x20   return 0 - (v.byte_at(0) * 1000 + v.len());";
    // view "YZ": byte_at(0)=='Y'=89, len=2 → 89*1000 + 2 = 89_002.
    assert_eq!(neg(body), 89_002);
}
