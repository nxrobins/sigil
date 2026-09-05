//! Runtime tests for the BOUNDED sets (Phase 4): `BoundedSet_i64_64`,
//! `BoundedSet_str_16`. Same harness as `bounded_map.rs`.

mod common;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    common::run_returning_negative_with_min_fuel(&tool(body), 1_000_000_000)
}

fn body_traps(body: &str) -> bool {
    common::tool_traps_with_min_fuel(&tool(body), 1_000_000_000)
}

fn fill_set_i64(n: i64) -> String {
    let mut s = String::from("    let mut s: BoundedSet_i64_64 = BoundedSet_i64_64::new();\n");
    for i in 0..n {
        s.push_str(&format!("    let _r{i}: bool = s.insert({});\n", i * 7));
    }
    s
}

#[test]
fn s1_membership_hit_miss() {
    assert_eq!(
        neg(
            "    let mut s: BoundedSet_i64_64 = BoundedSet_i64_64::new();\n    let _a: bool = s.insert(3);\n    if s.contains(3) { if s.contains(4) { return 0 - 3; } else { return 0 - 1; } } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn s2_idempotent_insert() {
    // insert(3)==true (added); insert(3)==false (present); len()==1. Decode: first
    // bool 1, second bool 0 → 1*100 + 0*10 + len(1) = 101.
    assert_eq!(
        neg(
            "    let mut s: BoundedSet_i64_64 = BoundedSet_i64_64::new();\n    let a: bool = s.insert(3);\n    let b: bool = s.insert(3);\n    let mut t: i64 = 0;\n    if a { t = t + 100; } else { }\n    if b { t = t + 10; } else { }\n    return 0 - (t + s.len());"
        ),
        101
    );
}

#[test]
fn s3_full_insert_new_traps() {
    let body = format!(
        "{}    let _o: bool = s.insert(99999);\n    return 0 - 1;",
        fill_set_i64(64)
    );
    assert!(body_traps(&body), "full + insert NEW element must trap");
}

#[test]
fn s4_fill_exactly_n_clean() {
    let body = format!(
        "{}    if s.is_full() {{ return 0 - (s.len() * 100 + s.capacity()); }} else {{ return 0 - 1; }}",
        fill_set_i64(64)
    );
    assert_eq!(neg(&body), 6464);
}

#[test]
fn str_set_membership_and_content_eq() {
    // insert "tag"; a distinct same-bytes "tag" (via concat) must be contained.
    assert_eq!(
        neg(
            "    let mut s: BoundedSet_str_16 = BoundedSet_str_16::new();\n    let _a: bool = s.insert(\"tag\");\n    let pre: str = \"ta\";\n    let k: str = pre.concat(\"g\");\n    if s.contains(k) { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn str_set_idempotent() {
    assert_eq!(
        neg(
            "    let mut s: BoundedSet_str_16 = BoundedSet_str_16::new();\n    let a: bool = s.insert(\"x\");\n    let b: bool = s.insert(\"x\");\n    let mut t: i64 = 0;\n    if a { t = t + 10; } else { }\n    if b { t = t + 1; } else { }\n    return 0 - (t + s.len() + 100);"
        ),
        // a=true→+10, b=false→+0, len 1, +100 → 111
        111
    );
}
