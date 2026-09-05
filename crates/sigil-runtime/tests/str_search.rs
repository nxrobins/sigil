//! PR 2 of the borrowing-strings epic: the `strings.sigil` search layer,
//! exercised as METHODS through the ambient path. A bare `s.find(n)` /
//! `s.contains(n)` / `s.starts_with(p)` / `s.ends_with(p)` on a `str`:
//!   1. token-triggers injection of `strings.sigil` (+ transitive option/result)
//!   2. type-check-dispatches to `strings::str_<method>(s, ...)` with the
//!      receiver prepended as the implicit first arg.
//!
//! `str_find` returns the ABSOLUTE offset (CF-S3) as `Option<i64>` (never an
//! in-band sentinel); `str_contains` is `str_find(...).is_some()`;
//! starts/ends_with are length-first byte loops. All pure SIGIL over
//! `byte_at`/`len` — the only compiler addition is the method-dispatch arm.
//!
//! `find` results are encoded `0 - (o.unwrap_or(-1) + 10000)`: a present match
//! at position `p` reads back as `10000 + p`; an absent match as `9999`. (The
//! receiver must be a binding — `"x".find(..)` on a bare literal doesn't parse.)

mod common;

use common::run_returning_negative as run_neg;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    run_neg(&tool(body))
}

/// `0 - (s.find(n).unwrap_or(-1) + 10000)` → `10000 + pos` present, `9999` absent.
fn find_body(haystack: &str, needle: &str) -> String {
    format!(
        "    let h: str = \"{haystack}\";\n\
         \x20   let o: Option<i64> = h.find(\"{needle}\");\n\
         \x20   return 0 - (o.unwrap_or(0 - 1) + 10000);"
    )
}

// ── s.find: presence, absolute position, and the empty algebra ───────────────

#[test]
fn find_present_absolute_offset() {
    // CF-S3: "hello world"[6..11] == "world" → absolute offset 6.
    assert_eq!(neg(&find_body("hello world", "world")), 10006);
}

#[test]
fn find_at_start() {
    assert_eq!(neg(&find_body("hello", "he")), 10000); // pos 0
}

#[test]
fn find_at_end() {
    assert_eq!(neg(&find_body("hello", "lo")), 10003); // pos 3
}

#[test]
fn find_absent() {
    assert_eq!(neg(&find_body("hello", "xyz")), 9999);
}

#[test]
fn find_needle_longer_than_haystack() {
    assert_eq!(neg(&find_body("ab", "abc")), 9999);
}

#[test]
fn find_overlapping_returns_first_match() {
    // "aaa" contains "aa" at 0 and 1; find returns the FIRST (0).
    assert_eq!(neg(&find_body("aaa", "aa")), 10000);
}

#[test]
fn find_empty_needle_is_zero() {
    // CF-S8: the empty needle matches at position 0.
    assert_eq!(neg(&find_body("hello", "")), 10000);
}

#[test]
fn find_empty_haystack_nonempty_needle_is_none() {
    // CF-S8: find("", n≠"") == None → 9999.
    assert_eq!(neg(&find_body("", "x")), 9999);
}

#[test]
fn find_empty_both_is_zero() {
    // CF-S8: find("", "") == Some(0).
    assert_eq!(neg(&find_body("", "")), 10000);
}

#[test]
fn find_offset_points_at_the_match() {
    // CF-S3 oracle: the returned offset, indexed back into the haystack, is the
    // first byte of the needle. "xxhello".find("hello") → 2; h.byte_at(2)=='h'.
    let body = "    let h: str = \"xxhello\";\n\
        \x20   let o: Option<i64> = h.find(\"hello\");\n\
        \x20   let p: i64 = o.unwrap_or(0);\n\
        \x20   return 0 - (p * 1000 + h.byte_at(p));";
    // p=2, 'h'==104 → 2104.
    assert_eq!(neg(body), 2104);
}

// ── s.contains / s.starts_with / s.ends_with ─────────────────────────────────

#[test]
fn contains_present_and_absent() {
    let body = "    let s: str = \"hello\";\n\
        \x20   if s.contains(\"ell\") {\n\
        \x20       if s.contains(\"xyz\") { return 0 - 1; } else { return 0 - 7; }\n\
        \x20   } else { return 0 - 2; }";
    // contains "ell" true, "xyz" false → 7.
    assert_eq!(neg(body), 7);
}

#[test]
fn contains_empty_needle_is_true() {
    let body = "    let s: str = \"hello\";\n\
        \x20   if s.contains(\"\") { return 0 - 42; } else { return 0 - 1; }";
    assert_eq!(neg(body), 42);
}

#[test]
fn starts_with_present_and_absent() {
    let body = "    let s: str = \"hello\";\n\
        \x20   if s.starts_with(\"he\") {\n\
        \x20       if s.starts_with(\"lo\") { return 0 - 1; } else { return 0 - 8; }\n\
        \x20   } else { return 0 - 2; }";
    // starts "he" true, "lo" false → 8.
    assert_eq!(neg(body), 8);
}

#[test]
fn ends_with_present_and_absent() {
    let body = "    let s: str = \"hello\";\n\
        \x20   if s.ends_with(\"lo\") {\n\
        \x20       if s.ends_with(\"he\") { return 0 - 1; } else { return 0 - 9; }\n\
        \x20   } else { return 0 - 2; }";
    // ends "lo" true, "he" false → 9.
    assert_eq!(neg(body), 9);
}

// ── chaining: a search on a substr view (composition over the keystone) ───────

#[test]
fn find_on_a_substr_view() {
    // The borrowing layer composes: take a sub-view, then search it. "hello
    // world".substr(6, 11) == "world"; "world".find("rl") → 2.
    let body = "    let h: str = \"hello world\";\n\
        \x20   let w: str = h.substr(6, 11);\n\
        \x20   let o: Option<i64> = w.find(\"rl\");\n\
        \x20   return 0 - (o.unwrap_or(0 - 1) + 10000);";
    // "world".find("rl") → 2 → 10002.
    assert_eq!(neg(body), 10002);
}

// ── the dispatch is gated on Type::Str ───────────────────────────────────────

#[test]
fn user_type_find_is_not_hijacked() {
    // The str-method rewrite fires ONLY for a `str` receiver. A same-named
    // method on a user type resolves to the user's own impl — never to
    // `strings::str_find`. (The `.find(` token still injects strings.sigil, but
    // that's harmless: the module is present and unused.)
    let src = "module tool;\n\
        record Bag { n: i64 }\n\
        impl Bag {\n\
        \x20   pub fn find(self: Bag, x: i64) -> i64 { return self.n + x; }\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let b: Bag = Bag { n: 40 };\n\
        \x20   return 0 - b.find(2);\n\
        }\n";
    // Bag::find(40, 2) == 42, not a string op.
    assert_eq!(run_neg(src), 42);
}
