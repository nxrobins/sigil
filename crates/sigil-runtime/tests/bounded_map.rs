//! Runtime tests for the BOUNDED maps (Phase 4): `BoundedMap_i64_i64_64`,
//! `BoundedMap_str_str_64`, `BoundedMap_str_i64_64`. Mirrors the `bounded_vec.rs`
//! harness: `neg` decodes a `return 0 - K` trap sentinel; `body_traps` is the
//! rigorous positive-return-vs-trap detector for the force-trap tests. Each test
//! runs under a no-`! { Alloc }` `tool_main`, so it is ALSO an ET-2 Alloc-free proof.

mod common;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    common::run_returning_negative_with_min_fuel(&tool(body), 1_000_000_000)
}

/// True iff `body` GENUINELY traps (a positive packed-pointer return is NOT a trap).
fn body_traps(body: &str) -> bool {
    common::tool_traps_with_min_fuel(&tool(body), 1_000_000_000)
}

/// Body prefix: a fresh i64 map with `n` distinct entries (key=i*10, val=i*100).
fn fill_i64(n: i64) -> String {
    let mut s =
        String::from("    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n");
    for i in 0..n {
        s.push_str(&format!(
            "    let _r{i}: i64 = m.insert({}, {});\n",
            i * 10,
            i * 100
        ));
    }
    s
}

// ───────────────────────── i64 → i64 map ─────────────────────────

#[test]
fn m1_insert_get_roundtrip() {
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n    let _a: i64 = m.insert(7, 42);\n    let _b: i64 = m.insert(9, 99);\n    let o: Option<i64> = m.get(7);\n    return 0 - o.unwrap_or(0);"
        ),
        42
    );
}

#[test]
fn m2_get_absent_is_none() {
    // None → unwrap_or(999) → K=999.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n    let _a: i64 = m.insert(7, 42);\n    let o: Option<i64> = m.get(8);\n    return 0 - o.unwrap_or(999);"
        ),
        999
    );
}

#[test]
fn m3_get_or_default() {
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n    let _a: i64 = m.insert(7, 42);\n    return 0 - m.get_or(8, 77);"
        ),
        77
    );
}

#[test]
fn m4_overwrite_not_append() {
    // insert(7,1); insert(7,5) → get(7)==5 AND len()==1. Decode 5*1000 + 1 = 5001.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n    let _a: i64 = m.insert(7, 1);\n    let _b: i64 = m.insert(7, 5);\n    let o: Option<i64> = m.get(7);\n    return 0 - (o.unwrap_or(0) * 1000 + m.len());"
        ),
        5001
    );
}

#[test]
fn m5_contains_key_hit_miss() {
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n    let _a: i64 = m.insert(7, 42);\n    if m.contains_key(7) { if m.contains_key(8) { return 0 - 3; } else { return 0 - 1; } } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn m6_full_insert_existing_ok() {
    // Fill 64 distinct, re-insert an existing key (key 0) → clean, len stays 64.
    let body = format!(
        "{}    let _o: i64 = m.insert(0, 12345);\n    return 0 - m.len();",
        fill_i64(64)
    );
    assert_eq!(neg(&body), 64);
}

#[test]
fn m7_full_insert_new_traps() {
    // Fill 64 distinct, insert a 65th NEW key → backing force-trap.
    let body = format!(
        "{}    let _o: i64 = m.insert(99999, 1);\n    return 0 - 1;",
        fill_i64(64)
    );
    assert!(body_traps(&body), "full + insert NEW key must trap");
}

#[test]
fn m8_fill_exactly_n_clean() {
    // 64 distinct inserts: no trap; is_full true; len==capacity==64.
    let body = format!(
        "{}    if m.is_full() {{ return 0 - (m.len() * 100 + m.capacity()); }} else {{ return 0 - 1; }}",
        fill_i64(64)
    );
    assert_eq!(neg(&body), 6464);
}

#[test]
fn m9_empty_get_none_and_is_empty() {
    assert_eq!(
        neg(
            "    let m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n    let o: Option<i64> = m.get(0);\n    if m.is_empty() { return 0 - o.unwrap_or(555); } else { return 0 - 1; }"
        ),
        555
    );
}

#[test]
fn m10_capacity_exact() {
    assert_eq!(
        neg(
            "    let m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n    return 0 - m.capacity();"
        ),
        64
    );
}

#[test]
fn tm_try_insert_full_new_returns_false_no_trap() {
    // Fill 64, try_insert a NEW key → false (no trap), len unchanged. Decode:
    // false→2 branch returns len; true→1 branch. We assert the false path + len 64.
    let body = format!(
        "{}    let ok: bool = m.try_insert(99999, 1);\n    if ok {{ return 0 - 1; }} else {{ return 0 - m.len(); }}",
        fill_i64(64)
    );
    assert_eq!(neg(&body), 64);
}

#[test]
fn tm_try_insert_existing_overwrites_true() {
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n    let _a: i64 = m.insert(7, 1);\n    let ok: bool = m.try_insert(7, 9);\n    let o: Option<i64> = m.get(7);\n    if ok { return 0 - (o.unwrap_or(0) * 10 + m.len()); } else { return 0 - 1; }"
        ),
        91
    );
}

// ───────────────────────── str-keyed maps ─────────────────────────

#[test]
fn ms1_str_content_equality() {
    // Insert "ab"; look up a DISTINCT same-bytes "ab" built via concat → MUST collide
    // (proves content equality, not pointer identity). Some → 7.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_str_str_64 = BoundedMap_str_str_64::new();\n    let _a: i64 = m.insert(\"ab\", \"V\");\n    let pre: str = \"a\";\n    let k: str = pre.concat(\"b\");\n    match m.get(k) { Some(v) => { return 0 - 7; }, None => { return 0 - 9; }, }"
        ),
        7
    );
}

#[test]
fn ms2_str_overwrite() {
    // insert("k","a"); insert("k","b") → get("k")=="b" (len 1). Decode via byte_at:
    // "b".byte_at(0)=98; *10 + len(1) = 981.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_str_str_64 = BoundedMap_str_str_64::new();\n    let _a: i64 = m.insert(\"k\", \"a\");\n    let _b: i64 = m.insert(\"k\", \"b\");\n    match m.get(\"k\") { Some(v) => { return 0 - (v.byte_at(0) * 10 + m.len()); }, None => { return 0 - 1; }, }"
        ),
        981
    );
}

#[test]
fn bm_ek_empty_string_is_a_legal_key() {
    // The `[""; N]` fill must NOT alias a real "" key (scan is count-bounded). An
    // inserted "" key round-trips.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();\n    let _a: i64 = m.insert(\"\", 314);\n    let o: Option<i64> = m.get(\"\");\n    return 0 - o.unwrap_or(0);"
        ),
        314
    );
}

#[test]
fn str_i64_insert_get() {
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();\n    let _a: i64 = m.insert(\"score\", 100);\n    let _b: i64 = m.insert(\"lives\", 3);\n    let o: Option<i64> = m.get(\"score\");\n    return 0 - o.unwrap_or(0);"
        ),
        100
    );
}
