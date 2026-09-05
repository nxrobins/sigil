//! PR 3 of the borrowing-strings epic: `s.split_on(d)` / `s.trim()` /
//! `s.parse_i64()`, exercised as methods through the ambient path. These reuse
//! the PR-2 str-method dispatch (`split` is 1-arg; `trim`/`parse_i64` are 0-arg)
//! and are pure SIGIL over `byte_at`/`len`/`substr` (+ `Vec` for split).
//!
//! - `split` satisfies the partition law (CF-S4): EXACTLY occurrences+1 segments
//!   (leading/trailing/consecutive delims → empty-string segments), with an
//!   empty-delimiter guard (`[s]`, no scan).
//! - `trim` strips exactly the six ASCII whitespace bytes (CF-S6).
//! - `parse_i64` is strict whole-string `-?[0-9]+` (CF-S7).
//!
//! `parse` results are encoded `0 - (o.unwrap_or(-1) + 1_000_000)`: `Some(v)`
//! reads back as `1_000_000 + v`, `None` as `999_999`. (Receivers are bindings —
//! `"x".split_on(..)` on a bare literal doesn't parse.)

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

/// `s.split_on(delim).len()` — verifies the segment COUNT (the partition law's
/// `occurrences + 1`).
fn split_len(s: &str, delim: &str) -> i64 {
    neg(&format!(
        "    let s: str = \"{s}\";\n\
         \x20   let parts: Vec<str> = s.split_on(\"{delim}\");\n\
         \x20   return 0 - parts.len();"
    ))
}

// ── split: the partition law (CF-S4) ─────────────────────────────────────────

#[test]
fn split_segment_count_basic() {
    // "a,b,c" → ["a","b","c"]: 2 delims → 3 segments.
    assert_eq!(split_len("a,b,c", ","), 3);
}

#[test]
fn split_trailing_delim_keeps_empty_segment() {
    // "a,b," → ["a","b",""]: the trailing empty segment is NOT dropped.
    assert_eq!(split_len("a,b,", ","), 3);
}

#[test]
fn split_leading_delim_keeps_empty_segment() {
    // ",a" → ["","a"].
    assert_eq!(split_len(",a", ","), 2);
}

#[test]
fn split_consecutive_delims_yield_empty() {
    // "a,,b" → ["a","","b"].
    assert_eq!(split_len("a,,b", ","), 3);
}

#[test]
fn split_empty_string_is_one_segment() {
    // CF-S8: split("", d) == [""].
    assert_eq!(split_len("", ","), 1);
}

#[test]
fn split_empty_delim_guard() {
    // CF-S4: empty delimiter → the whole string as one element (no scan).
    assert_eq!(split_len("abc", ""), 1);
}

#[test]
fn split_no_match_is_whole_string() {
    assert_eq!(split_len("abc", ","), 1);
}

#[test]
fn split_multichar_delim_count() {
    // "aXXbXXc" on "XX" → ["a","b","c"]: multi-byte, non-overlapping delim.
    assert_eq!(split_len("aXXbXXc", "XX"), 3);
}

#[test]
fn split_content_byte_sum_reconstructs() {
    // Sum every byte of every segment — must equal the sum of the non-delim
    // bytes of the input. "ab,cd" → "ab"+"cd": a+b+c+d = 97+98+99+100 = 394.
    let body = "    let s: str = \"ab,cd\";\n\
        \x20   let parts: Vec<str> = s.split_on(\",\");\n\
        \x20   let np: i64 = parts.len();\n\
        \x20   let mut total: i64 = 0;\n\
        \x20   let mut pi: i64 = 0;\n\
        \x20   while pi < np {\n\
        \x20       let seg: str = parts.get(pi);\n\
        \x20       let sl: i64 = seg.len();\n\
        \x20       let mut bi: i64 = 0;\n\
        \x20       while bi < sl {\n\
        \x20           total = total + seg.byte_at(bi);\n\
        \x20           bi = bi + 1;\n\
        \x20       }\n\
        \x20       pi = pi + 1;\n\
        \x20   }\n\
        \x20   return 0 - total;";
    assert_eq!(neg(body), 394);
}

#[test]
fn split_then_index_a_segment() {
    // The segments are real views: "key=value".split_on("=")[1] == "value",
    // value.byte_at(0) == 'v'.
    let body = "    let s: str = \"key=value\";\n\
        \x20   let parts: Vec<str> = s.split_on(\"=\");\n\
        \x20   let v: str = parts.get(1);\n\
        \x20   return 0 - (v.len() * 1000 + v.byte_at(0));";
    // "value" len 5, 'v'==118 → 5118.
    assert_eq!(neg(body), 5118);
}

// ── trim: the fixed six-byte whitespace set (CF-S6) ───────────────────────────

#[test]
fn trim_spaces_both_sides() {
    let body = "    let s: str = \"  hi  \";\n\
        \x20   let t: str = s.trim();\n\
        \x20   return 0 - (t.len() * 1000 + t.byte_at(0));";
    // "hi" len 2, 'h'==104 → 2104.
    assert_eq!(neg(body), 2104);
}

#[test]
fn trim_strips_tabs_and_newlines() {
    // CF-S6: tab and newline are whitespace too (not just space). "\t hi\n" →
    // "hi". (The SIGIL lexer supports `\t`/`\n` escapes but not `\r`; CR/VT/FF
    // are covered by `str_is_ws`'s source, not constructible in a literal.)
    let body = "    let s: str = \"\\thi\\n\";\n\
        \x20   let t: str = s.trim();\n\
        \x20   return 0 - (t.len() * 1000 + t.byte_at(0));";
    assert_eq!(neg(body), 2104);
}

#[test]
fn trim_all_whitespace_is_empty() {
    let body = "    let s: str = \"   \";\n\
        \x20   let t: str = s.trim();\n\
        \x20   return 0 - (t.len() + 7000);";
    // len 0 → 7000.
    assert_eq!(neg(body), 7000);
}

#[test]
fn trim_no_whitespace_unchanged() {
    let body = "    let s: str = \"hi\";\n\
        \x20   let t: str = s.trim();\n\
        \x20   return 0 - (t.len() * 1000 + t.byte_at(0));";
    assert_eq!(neg(body), 2104);
}

#[test]
fn trim_interior_whitespace_preserved() {
    // Only LEADING/TRAILING ws is stripped; interior survives. " a b " → "a b"
    // (len 3).
    let body = "    let s: str = \" a b \";\n\
        \x20   let t: str = s.trim();\n\
        \x20   return 0 - t.len();";
    assert_eq!(neg(body), 3);
}

#[test]
fn trim_non_ws_byte_not_stripped() {
    // A non-whitespace byte (here 'x') is never stripped — only the six ASCII
    // ws bytes are. "xhix" → unchanged (len 4).
    let body = "    let s: str = \"xhix\";\n\
        \x20   let t: str = s.trim();\n\
        \x20   return 0 - t.len();";
    assert_eq!(neg(body), 4);
}

// ── parse_i64: strict whole-string -?[0-9]+ (CF-S7) ──────────────────────────

fn parse_body(s: &str) -> String {
    format!(
        "    let s: str = \"{s}\";\n\
         \x20   let o: Option<i64> = s.parse_i64();\n\
         \x20   return 0 - (o.unwrap_or(0 - 1) + 1000000);"
    )
}

#[test]
fn parse_positive() {
    assert_eq!(neg(&parse_body("123")), 1_000_123);
}

#[test]
fn parse_negative() {
    assert_eq!(neg(&parse_body("-45")), 999_955); // 1_000_000 + (-45)
}

#[test]
fn parse_zero() {
    assert_eq!(neg(&parse_body("0")), 1_000_000);
}

#[test]
fn parse_empty_is_none() {
    assert_eq!(neg(&parse_body("")), 999_999); // None → unwrap_or(-1)
}

#[test]
fn parse_lone_sign_is_none() {
    assert_eq!(neg(&parse_body("-")), 999_999);
}

#[test]
fn parse_leading_plus_is_none() {
    assert_eq!(neg(&parse_body("+5")), 999_999);
}

#[test]
fn parse_trailing_nondigit_is_none() {
    // Strict whole-string: a prefix-parse would wrongly return Some(12).
    assert_eq!(neg(&parse_body("12x")), 999_999);
}

#[test]
fn parse_leading_space_is_none() {
    assert_eq!(neg(&parse_body(" 5")), 999_999);
}

// ── the headline composition: parse a config line end to end ─────────────────

#[test]
fn split_find_parse_compose() {
    // The borrowing layer composes: split a line on ',', take the second entry,
    // split it on '=', and parse the value. "a=1,b=42" → entry "b=42" → "42".
    let body = "    let line: str = \"a=1,b=42\";\n\
        \x20   let entries: Vec<str> = line.split_on(\",\");\n\
        \x20   let second: str = entries.get(1);\n\
        \x20   let kv: Vec<str> = second.split_on(\"=\");\n\
        \x20   let val: str = kv.get(1);\n\
        \x20   let o: Option<i64> = val.parse_i64();\n\
        \x20   return 0 - o.unwrap_or(0 - 1);";
    // "b=42" → val "42" → 42.
    assert_eq!(neg(body), 42);
}
