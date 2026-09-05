//! PR-B: Phase-3 string completion — `parse_u64`/`parse_i32`/`parse_u32`,
//! `to_string` (all int widths, incl. a u64 > i64::MAX), `eq_ignore_case`, and
//! `split_first` → `Option<(str, str)>`. Bool/Option-int results decode via the
//! negative-sentinel trap; str results via the `.as_output()` byte round-trip.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Sentinel harness (no effect clause — parse/eq are pure, Alloc-free).
fn neg(body: &str) -> i64 {
    let src = format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    );
    let result = compile_tool(&src).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            let s = message
                .find(p)
                .unwrap_or_else(|| panic!("no sentinel: {message}"))
                + p.len();
            let e = message[s..].find(')').unwrap();
            message[s..s + e].parse().unwrap()
        }
        other => panic!("expected sentinel trap, got {other:?}"),
    }
}

/// `.as_output()` byte round-trip for str results (with `! {{ Alloc }}`).
fn run_out(body: &str) -> String {
    let src = format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    );
    let result = compile_tool(&src).expect("str tool should compile");
    let exec = execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none())
        .expect("str tool executes");
    String::from_utf8(exec.output).expect("output is UTF-8")
}

// ───────────────────────── parse_u64 / parse_i32 / parse_u32 ─────────────────────────

fn parse_u64_body(s: &str) -> String {
    // Some(v) → 0 - (v + 1)  (always a negative sentinel, even for v == 0);
    // None → 0 - 999999.
    format!(
        "    let s: str = \"{s}\";\n\
         \x20   match s.parse_u64() {{\n\
         \x20       Some(v) => {{ let vi: i64 = v.as_i64(); return 0 - (vi + 1); }},\n\
         \x20       None => {{ return 0 - 999999; }},\n\
         \x20   }}"
    )
}

#[test]
fn parse_u64_ok() {
    assert_eq!(neg(&parse_u64_body("123")), 124); // 123 + 1
}

#[test]
fn parse_u64_zero() {
    assert_eq!(neg(&parse_u64_body("0")), 1); // 0 + 1
}

#[test]
fn parse_u64_empty_is_none() {
    assert_eq!(neg(&parse_u64_body("")), 999999);
}

#[test]
fn parse_u64_sign_is_none() {
    // Unsigned: a leading '-' is rejected.
    assert_eq!(neg(&parse_u64_body("-5")), 999999);
}

#[test]
fn parse_u64_nondigit_is_none() {
    assert_eq!(neg(&parse_u64_body("12x")), 999999);
}

fn parse_i32_branch(s: &str) -> i64 {
    // Some(v) → 0 - (v + 1000) so a parsed value is recoverable & always
    // negative-returning; None → 7.
    neg(&format!(
        "    let s: str = \"{s}\";\n\
         \x20   match s.parse_i32() {{\n\
         \x20       Some(v) => {{ let vi: i64 = v.as_i64(); return 0 - (vi + 1000000); }},\n\
         \x20       None => {{ return 0 - 7; }},\n\
         \x20   }}"
    ))
}

#[test]
fn parse_i32_in_range() {
    assert_eq!(parse_i32_branch("2147483647"), 1_000_000 + 2_147_483_647); // i32::MAX
}

#[test]
fn parse_i32_negative() {
    assert_eq!(parse_i32_branch("-100"), 1_000_000 - 100);
}

#[test]
fn parse_i32_overflow_is_none() {
    assert_eq!(parse_i32_branch("2147483648"), 7); // i32::MAX + 1 → None
}

fn parse_u32_branch(s: &str) -> i64 {
    neg(&format!(
        "    let s: str = \"{s}\";\n\
         \x20   match s.parse_u32() {{\n\
         \x20       Some(v) => {{ let vi: i64 = v.as_i64(); return 0 - (vi + 1); }},\n\
         \x20       None => {{ return 0 - 7; }},\n\
         \x20   }}"
    ))
}

#[test]
fn parse_u32_max() {
    assert_eq!(parse_u32_branch("4294967295"), 4_294_967_295 + 1); // u32::MAX
}

#[test]
fn parse_u32_overflow_is_none() {
    assert_eq!(parse_u32_branch("4294967296"), 7); // u32::MAX + 1 → None
}

// ───────────────────────── to_string (all widths) ─────────────────────────

#[test]
fn to_string_i64() {
    assert_eq!(
        run_out(
            "    let n: i64 = 12345;\n    let s: str = n.to_string();\n    return s.as_output();"
        ),
        "12345"
    );
}

#[test]
fn to_string_i64_negative() {
    assert_eq!(
        run_out(
            "    let n: i64 = 0 - 42;\n    let s: str = n.to_string();\n    return s.as_output();"
        ),
        "-42"
    );
}

#[test]
fn to_string_i32_negative() {
    // i32 → i64 (sign-extend) → itoa.
    assert_eq!(
        run_out(
            "    let neg5: i64 = 0 - 5;\n    let i: i32 = neg5.as_i32();\n    let s: str = i.to_string();\n    return s.as_output();"
        ),
        "-5"
    );
}

#[test]
fn to_string_u32_max() {
    // u32 → i64 (zero-extend) → itoa.
    assert_eq!(
        run_out(
            "    let neg1: i64 = 0 - 1;\n    let u: u32 = neg1.as_u32();\n    let s: str = u.to_string();\n    return s.as_output();"
        ),
        "4294967295"
    );
}

#[test]
fn to_string_u64_max() {
    // THE big one: u64::MAX > i64::MAX → str_utoa_u64 (unsigned div/mod, A1 fix).
    assert_eq!(
        run_out(
            "    let neg1: i64 = 0 - 1;\n    let big: u64 = neg1.as_u64();\n    let s: str = big.to_string();\n    return s.as_output();"
        ),
        "18446744073709551615"
    );
}

// ───────────────────────── eq_ignore_case ─────────────────────────

#[test]
fn eq_ignore_case_match() {
    assert_eq!(
        neg(
            "    let a: str = \"Hello\";\n    let b: str = \"hELLo\";\n    if a.eq_ignore_case(b) { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn eq_ignore_case_mismatch() {
    assert_eq!(
        neg(
            "    let a: str = \"Hello\";\n    let b: str = \"World\";\n    if a.eq_ignore_case(b) { return 0 - 1; } else { return 0 - 2; }"
        ),
        2
    );
}

#[test]
fn eq_ignore_case_length_differs() {
    assert_eq!(
        neg(
            "    let a: str = \"abc\";\n    let b: str = \"abcd\";\n    if a.eq_ignore_case(b) { return 0 - 1; } else { return 0 - 2; }"
        ),
        2
    );
}

// ───────────────────────── split_first → Option<(str, str)> ─────────────────────────

#[test]
fn split_first_head() {
    let out = run_out(
        "    let s: str = \"key=val\";\n    let d: str = \"=\";\n    match s.split_first(d) {\n        Some(p) => { let (h, r) = p; let _u: i64 = r.len(); return h.as_output(); },\n        None => { let n: str = \"NONE\"; return n.as_output(); },\n    }",
    );
    assert_eq!(out, "key");
}

#[test]
fn split_first_rest() {
    let out = run_out(
        "    let s: str = \"key=val=more\";\n    let d: str = \"=\";\n    match s.split_first(d) {\n        Some(p) => { let (h, r) = p; let _u: i64 = h.len(); return r.as_output(); },\n        None => { let n: str = \"NONE\"; return n.as_output(); },\n    }",
    );
    assert_eq!(out, "val=more"); // split at the FIRST delimiter only
}

#[test]
fn split_first_no_delim_is_none() {
    let out = run_out(
        "    let s: str = \"abc\";\n    let d: str = \"=\";\n    match s.split_first(d) {\n        Some(p) => { let (h, r) = p; let _u: i64 = h.len() + r.len(); let hs: str = \"HEAD\"; return hs.as_output(); },\n        None => { let n: str = \"NONE\"; return n.as_output(); },\n    }",
    );
    assert_eq!(out, "NONE");
}
