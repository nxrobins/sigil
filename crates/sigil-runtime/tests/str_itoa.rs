//! Owned-strings PR-3: `n.itoa()` — the i64 → decimal `str` builder.
//!
//! `n.itoa()` (an i64-receiver method — collision-safe, since i64 has no user
//! impls) desugars to `string::str_itoa(n)`. All digit math runs in NEGATIVE
//! space, so `i64::MIN` (whose magnitude is not a positive i64) is handled
//! without any negation or overflow. These tests execute the build and read the
//! ASCII back; the round-trip test composes the OWNED `itoa` with the BORROWING
//! `parse_i64`.

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

#[test]
fn itoa_zero() {
    // The 0 special case: a single '0'(48), len 1.
    let body = "    let n: i64 = 0;\n\
        \x20   let r: str = n.itoa();\n\
        \x20   return 0 - (r.len() * 1000 + r.byte_at(0));";
    // len 1, '0'=48 → 1048.
    assert_eq!(neg(body), 1048);
}

#[test]
fn itoa_positive_two_digits() {
    // 42 → "42": len 2, byte_at(0)=='4'(52), byte_at(1)=='2'(50).
    let body = "    let n: i64 = 42;\n\
        \x20   let r: str = n.itoa();\n\
        \x20   return 0 - (r.len() * 100000 + r.byte_at(0) * 100 + r.byte_at(1));";
    // 2*100000 + 52*100 + 50 = 205250.
    assert_eq!(neg(body), 205250);
}

#[test]
fn itoa_negative() {
    // -42 → "-42": len 3, byte_at(0)=='-'(45), byte_at(2)=='2'(50).
    let body = "    let n: i64 = 0 - 42;\n\
        \x20   let r: str = n.itoa();\n\
        \x20   return 0 - (r.len() * 100000 + r.byte_at(0) * 100 + r.byte_at(2));";
    // 3*100000 + 45*100 + 50 = 304550.
    assert_eq!(neg(body), 304550);
}

#[test]
fn itoa_i64_min_no_overflow() {
    // The headline: i64::MIN == -9223372036854775808, constructed as -MAX-1 so
    // the literal itself never overflows. itoa must NOT negate it. Expect a
    // 20-char "-9223372036854775808": len 20, byte0='-'(45), byte1='9'(57),
    // byte19='8'(56).
    let body = "    let n: i64 = 0 - 9223372036854775807 - 1;\n\
        \x20   let r: str = n.itoa();\n\
        \x20   return 0 - (r.len() * 1000000 + r.byte_at(0) * 10000 + r.byte_at(1) * 100 + r.byte_at(19));";
    // 20*1000000 + 45*10000 + 57*100 + 56 = 20455756.
    assert_eq!(neg(body), 20455756);
}

#[test]
fn itoa_max_length_and_first_digit() {
    // i64::MAX == 9223372036854775807: 19 digits, byte0=='9'(57), byte18=='7'(55).
    let body = "    let n: i64 = 9223372036854775807;\n\
        \x20   let r: str = n.itoa();\n\
        \x20   return 0 - (r.len() * 1000000 + r.byte_at(0) * 10000 + r.byte_at(18));";
    // 19*1000000 + 57*10000 + 55 = 19570055.
    assert_eq!(neg(body), 19570055);
}

#[test]
fn itoa_parse_round_trips() {
    // OWNED × BORROWING: itoa(n).parse_i64() == Some(n). Composes the owned
    // builder (string.sigil) with the borrowing parser (strings.sigil) — both
    // ambient-injected — over a representative value.
    let body = "    let n: i64 = 0 - 12345;\n\
        \x20   let s: str = n.itoa();\n\
        \x20   let p: Option<i64> = s.parse_i64();\n\
        \x20   return p.unwrap_or(0);";
    // n is negative, so a successful round-trip returns the negative sentinel
    // -12345 (run_neg → 12345). A parse failure (None → 0) would return a
    // non-negative value and make run_neg panic — so this also proves Some.
    assert_eq!(neg(body), 12345);
}
