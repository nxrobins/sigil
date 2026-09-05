//! PR 4 of the borrowing-strings epic: the adversarial stress capstone.
//!
//! No source change — these try to BREAK the borrowing string layer end to end
//! through the ambient/method path (a bare `s.split_on(..)` etc.), focusing on
//! the corruptions a happy-path suite would miss: the partition law at scale
//! (drop/duplicate a segment), view containment at DEPTH (a stale nested
//! substr), scan termination + correctness on worst-case near-misses, malformed
//! config input with DEFINED results (CF-S9), and the full split→get→split→parse
//! composition over a corpus.
//!
//! Large inputs are HOST-GENERATED literals (SIGIL has no itoa/concat, so a long
//! string can't be built at runtime); the SIGIL program then folds over them and
//! the result is recovered via the negative-sentinel convention.

mod common;

use common::run_returning_negative_with_fuel;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// This suite pins string-search/split SEMANTICS at scale. The str stdlib's
/// scan loops are data-dependent (input length), so `recommended_budget` is
/// honestly a straight-line FLOOR — under fuel ENFORCEMENT the at-scale scans
/// legitimately fuel-trap at the bare recommendation. Run at an explicit
/// POLICY budget (the str_from_bytes/bounded_map precedent): the scan
/// -termination properties these tests pin still hold — a non-advancing scan
/// burns this finite budget and traps loudly.
const SEMANTICS_FUEL: u64 = 10_000_000;

fn neg(body: &str) -> i64 {
    run_returning_negative_with_fuel(&tool(body), SEMANTICS_FUEL)
}

/// The i-th distinct single-char segment, cycling 'a'..='z'.
fn seg_char(i: i64) -> u8 {
    b'a' + (i % 26) as u8
}

// ── split: the partition law at scale ────────────────────────────────────────

#[test]
fn split_scale_count_and_content() {
    // N distinct single-char segments joined by ',' (so the map grows several
    // times). Recover BOTH the count and a content checksum (Σ of each
    // segment's byte): a dropped/duplicated/corrupted segment perturbs one or
    // the other. Encoded `len*100000 + Σbyte`.
    const N: i64 = 150;
    let joined: String = (0..N)
        .map(|i| (seg_char(i) as char).to_string())
        .collect::<Vec<_>>()
        .join(",");
    let body = format!(
        "    let s: str = \"{joined}\";\n\
         \x20   let parts: Vec<str> = s.split_on(\",\");\n\
         \x20   let np: i64 = parts.len();\n\
         \x20   let mut total: i64 = 0;\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < np {{\n\
         \x20       let seg: str = parts.get(i);\n\
         \x20       total = total + seg.byte_at(0);\n\
         \x20       i = i + 1;\n\
         \x20   }}\n\
         \x20   return 0 - (np * 100000 + total);"
    );
    let sum: i64 = (0..N).map(|i| seg_char(i) as i64).sum();
    assert_eq!(neg(&body), N * 100000 + sum);
}

#[test]
fn split_scale_every_segment_len_one() {
    // Every segment of a single-char split is length 1 — summing the lengths
    // must equal the segment count. A run-on (a missing delimiter match) would
    // make some segment longer and others vanish, changing this sum.
    const N: i64 = 120;
    let joined: String = (0..N)
        .map(|i| (seg_char(i) as char).to_string())
        .collect::<Vec<_>>()
        .join(",");
    let body = format!(
        "    let s: str = \"{joined}\";\n\
         \x20   let parts: Vec<str> = s.split_on(\",\");\n\
         \x20   let np: i64 = parts.len();\n\
         \x20   let mut lensum: i64 = 0;\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < np {{\n\
         \x20       let seg: str = parts.get(i);\n\
         \x20       lensum = lensum + seg.len();\n\
         \x20       i = i + 1;\n\
         \x20   }}\n\
         \x20   return 0 - lensum;"
    );
    assert_eq!(neg(&body), N); // N segments × len 1
}

#[test]
fn split_multichar_delim_at_scale() {
    // A 2-byte delimiter "XY" between N single-char segments. Non-overlapping
    // multi-byte scan at scale.
    const N: i64 = 100;
    let joined: String = (0..N)
        .map(|i| (seg_char(i) as char).to_string())
        .collect::<Vec<_>>()
        .join("XY");
    let body = format!(
        "    let s: str = \"{joined}\";\n\
         \x20   let parts: Vec<str> = s.split_on(\"XY\");\n\
         \x20   return 0 - parts.len();"
    );
    assert_eq!(neg(&body), N);
}

// ── substr: view containment at depth ────────────────────────────────────────

#[test]
fn deep_nested_substr_peel() {
    // Peel one byte off EACH side, D times, by reassigning to a sub-view of the
    // previous sub-view (a chain of D nested views). The innermost view must
    // still read the correct byte of the ORIGINAL — a stale/mis-homed nested
    // header would read garbage. M-char source, peel D ⇒ window [D, M-D).
    const M: i64 = 100;
    const D: i64 = 40;
    let s: String = (0..M).map(|i| seg_char(i) as char).collect();
    let body = format!(
        "    let s: str = \"{s}\";\n\
         \x20   let mut v: str = s;\n\
         \x20   let mut d: i64 = 0;\n\
         \x20   while d < {D} {{\n\
         \x20       let hi: i64 = v.len() - 1;\n\
         \x20       v = v.substr(1, hi);\n\
         \x20       d = d + 1;\n\
         \x20   }}\n\
         \x20   return 0 - (v.len() * 1000 + v.byte_at(0));"
    );
    // window [40, 60): len 20, first byte == original byte 40.
    let inner_len = M - 2 * D;
    let first = seg_char(D) as i64;
    assert_eq!(neg(&body), inner_len * 1000 + first);
}

// ── find: scan termination + correctness on worst cases ──────────────────────

#[test]
fn find_worst_case_near_miss_every_position() {
    // "aaa…aab" (M-1 'a's + 'b'). Searching "ab" near-misses at EVERY position
    // (matches the leading 'a', fails the second char) until the real match at
    // M-2. Stresses the inner-loop sentinel exit + the absolute-offset return.
    const M: i64 = 250;
    let s: String = "a".repeat((M - 1) as usize) + "b";
    let body = format!(
        "    let s: str = \"{s}\";\n\
         \x20   let o: Option<i64> = s.find(\"ab\");\n\
         \x20   return 0 - o.unwrap_or(0 - 1);"
    );
    assert_eq!(neg(&body), M - 2); // 'a' at M-2, 'b' at M-1
}

#[test]
fn find_no_match_full_scan_terminates() {
    // "aaa…a" (no 'b'): "ab" never matches — the scan must run the full length
    // and return None, not spin (CF-S2: fuel isn't enforced, termination is
    // structural).
    const M: i64 = 300;
    let s: String = "a".repeat(M as usize);
    let body = format!(
        "    let s: str = \"{s}\";\n\
         \x20   let o: Option<i64> = s.find(\"ab\");\n\
         \x20   return 0 - (o.unwrap_or(0 - 1) + 1000);"
    );
    assert_eq!(neg(&body), 999); // None → -1 + 1000
}

// ── CF-S9: malformed config input has DEFINED behavior ───────────────────────

#[test]
fn malformed_no_equals_is_single_segment() {
    // A bare key with no '=' → one segment.
    let body = "    let s: str = \"keyonly\";\n\
        \x20   let parts: Vec<str> = s.split_on(\"=\");\n\
        \x20   return 0 - parts.len();";
    assert_eq!(neg(body), 1);
}

#[test]
fn malformed_empty_value_parses_to_none() {
    // "k=" → ["k",""]; the empty value parses to None, not 0.
    let body = "    let s: str = \"k=\";\n\
        \x20   let kv: Vec<str> = s.split_on(\"=\");\n\
        \x20   let v: str = kv.get(1);\n\
        \x20   let o: Option<i64> = v.parse_i64();\n\
        \x20   return 0 - (o.unwrap_or(0 - 1) + 1000);";
    // empty value → None → -1 + 1000 = 999 (and the segment count is 2).
    assert_eq!(neg(body), 999);
}

#[test]
fn malformed_empty_key_keeps_both_segments() {
    // "=v" → ["","v"]: leading delimiter keeps the empty key segment.
    let body = "    let s: str = \"=v\";\n\
        \x20   let kv: Vec<str> = s.split_on(\"=\");\n\
        \x20   let k: str = kv.get(0);\n\
        \x20   return 0 - (kv.len() * 100 + k.len());";
    // 2 segments, empty key len 0 → 200.
    assert_eq!(neg(body), 200);
}

#[test]
fn malformed_multiple_equals() {
    // "k=v=w" → ["k","v","w"]: every '=' splits; not a special case.
    let body = "    let s: str = \"k=v=w\";\n\
        \x20   let parts: Vec<str> = s.split_on(\"=\");\n\
        \x20   return 0 - parts.len();";
    assert_eq!(neg(body), 3);
}

// ── trim + parse: pathological inputs ────────────────────────────────────────

#[test]
fn trim_huge_padding() {
    // P leading + P trailing spaces around one byte → just that byte.
    const P: usize = 120;
    let s: String = " ".repeat(P) + "X" + &" ".repeat(P);
    let body = format!(
        "    let s: str = \"{s}\";\n\
         \x20   let t: str = s.trim();\n\
         \x20   return 0 - (t.len() * 1000 + t.byte_at(0));"
    );
    // "X" len 1, 'X'==88 → 1088.
    assert_eq!(neg(&body), 1088);
}

#[test]
fn parse_large_number() {
    // A 10-digit value (well inside i64) round-trips exactly.
    let body = "    let s: str = \"1234567890\";\n\
        \x20   let o: Option<i64> = s.parse_i64();\n\
        \x20   return 0 - o.unwrap_or(0 - 1);";
    assert_eq!(neg(body), 1_234_567_890);
}

// ── the full composition over a corpus ───────────────────────────────────────

#[test]
fn compose_split_get_split_parse() {
    // The realistic self-hosting use: parse a `k=v,...` config, pick a NON-FIRST
    // entry, split it on '=', and parse the value. "a=10,b=20,c=30" → entry 2
    // "c=30" → value "30" → 30. Exercises the index-2 segment being correct.
    let body = "    let line: str = \"a=10,b=20,c=30\";\n\
        \x20   let entries: Vec<str> = line.split_on(\",\");\n\
        \x20   let third: str = entries.get(2);\n\
        \x20   let kv: Vec<str> = third.split_on(\"=\");\n\
        \x20   let val: str = kv.get(1);\n\
        \x20   let o: Option<i64> = val.parse_i64();\n\
        \x20   return 0 - o.unwrap_or(0 - 1);";
    assert_eq!(neg(body), 30);
}

#[test]
fn compose_trim_then_parse() {
    // Padded numeric value → trim → parse. "  42  " → "42" → 42. The borrowing
    // layer composes: trim returns a view, parse reads it.
    let body = "    let s: str = \"  42  \";\n\
        \x20   let t: str = s.trim();\n\
        \x20   let o: Option<i64> = t.parse_i64();\n\
        \x20   return 0 - o.unwrap_or(0 - 1);";
    assert_eq!(neg(body), 42);
}
