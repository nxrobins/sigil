//! Execution-level correctness for native u256 checked arithmetic (PR-U1a:
//! comparisons + add/sub). These run the compiled wasm under the ephemeral
//! runtime and verify VALUES (not just that it compiled), which is the only way
//! to catch a carry/borrow bug — exactly the class of bug that, in a smart
//! contract, drains funds.
//!
//! Convention (mirrors `array_repeat.rs`): a tool returns a NEGATIVE i64
//! sentinel; the runtime reports it as "tool returned error (CODE)" with
//! CODE = -return. `decode` recovers CODE. By convention `return 0 - 1;` = PASS
//! (decode == 1), `return 0 - 2;` = FAIL. A CHECKED-arithmetic revert is a
//! genuine `unreachable` trap (NOT the sentinel), asserted by `expect_revert`.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

/// Decode the `return 0 - code;` negative sentinel into `code`.
fn decode(body: &str) -> i64 {
    let result = compile_tool(&tool(body)).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a negative-sentinel return, got a genuine trap: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap message: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse sentinel from {message:?}: {e}"))
        }
        Err(other) => panic!("tool failed with a non-trap error: {other:?}"),
        Ok(_) => panic!("tool returned a positive packed-pointer; expected a negative sentinel"),
    }
}

/// Assert the body REVERTS via a checked-arithmetic trap (a genuine
/// `unreachable`, distinct from the negative-sentinel return path).
fn expect_revert(body: &str) {
    let result = compile_tool(&tool(body)).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            assert!(
                !message.contains("tool returned error ("),
                "expected a genuine checked-arith revert, but got a sentinel return: {message}"
            );
        }
        Err(other) => panic!("expected a trap revert, got: {other:?}"),
        Ok(_) => panic!("expected a checked-arith revert, but the tool returned successfully"),
    }
}

// ── add / sub correctness ────────────────────────────────────────────────────

#[test]
fn add_no_carry() {
    let body = "    let a: u256 = u256_from_i64(5);\n    \
        let b: u256 = u256_from_i64(7);\n    \
        let c: u256 = a + b;\n    \
        let e: u256 = u256_from_i64(12);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(body), 1, "5 + 7 should equal 12");
}

#[test]
fn add_carry_into_limb1() {
    // 4 * 2^62 == 2^64 → limb0 wraps to 0 with a carry into limb1 (== 1).
    let body = "    let a: u256 = u256_from_i64(4611686018427387904);\n    \
        let s: u256 = a + a + a + a;\n    \
        let e: u256 = u256_make(0, 1, 0, 0);\n    \
        if s == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(
        decode(body),
        1,
        "4 * 2^62 should carry into limb1 (== 2^64)"
    );
}

#[test]
fn add_alias_self() {
    // `a + a` reads the SAME cell for both operands and allocates a fresh result
    // (E3 — pure, no in-place mutation), so it must equal 2*a.
    let body = "    let a: u256 = u256_from_i64(10);\n    \
        let c: u256 = a + a;\n    \
        let e: u256 = u256_from_i64(20);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(body), 1, "a + a should equal 2*a");
}

#[test]
fn sub_basic() {
    let body = "    let a: u256 = u256_from_i64(20);\n    \
        let b: u256 = u256_from_i64(8);\n    \
        let c: u256 = a - b;\n    \
        let e: u256 = u256_from_i64(12);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(body), 1, "20 - 8 should equal 12");
}

#[test]
fn sub_borrow_then_add_roundtrips() {
    // a = 2^64 (limb1 = 1). (a - 1) borrows out of limb1; adding 1 back must
    // carry it in again — round-trip recovers `a`. Tests borrow + carry together
    // without needing a >2^63 literal (deferred to U2).
    let body = "    let a: u256 = u256_make(0, 1, 0, 0);\n    \
        let one: u256 = u256_from_i64(1);\n    \
        let c: u256 = a - one;\n    \
        let back: u256 = c + one;\n    \
        if back == a { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(body), 1, "(a - 1) + 1 should round-trip to a");
}

// ── checked reverts (E1) ─────────────────────────────────────────────────────

#[test]
fn sub_underflow_reverts() {
    // 0 - 1 underflows (a < b) → checked revert (trap_if), not a wrapped value.
    let body = "    let a: u256 = u256_from_i64(0);\n    \
        let b: u256 = u256_from_i64(1);\n    \
        let c: u256 = a - b;\n    return 0 - 1;";
    expect_revert(body);
}

// ── comparison correctness ───────────────────────────────────────────────────

#[test]
fn lt_true_and_false() {
    let lt = "    let a: u256 = u256_from_i64(5);\n    let b: u256 = u256_from_i64(9);\n    \
        if a < b { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(lt), 1, "5 < 9 is true");
    let nlt = "    let a: u256 = u256_from_i64(9);\n    let b: u256 = u256_from_i64(5);\n    \
        if a < b { return 0 - 2; }\n    return 0 - 1;";
    assert_eq!(decode(nlt), 1, "9 < 5 is false");
}

#[test]
fn lt_uses_unsigned_high_limb() {
    // limb1 comparison must be UNSIGNED: 2^64 (limb1=1) > 5 (limb0=5). A signed
    // bug at the limb level would not change this case, but the most-significant
    // limb ordering is what this guards.
    let body = "    let big: u256 = u256_make(0, 1, 0, 0);\n    \
        let small: u256 = u256_from_i64(5);\n    \
        if small < big { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(
        decode(body),
        1,
        "5 < 2^64 must hold across the limb boundary"
    );
}

#[test]
fn ge_le_gt() {
    let ge = "    let a: u256 = u256_from_i64(7);\n    let b: u256 = u256_from_i64(7);\n    \
        if a >= b { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(ge), 1, "7 >= 7");
    let le = "    let a: u256 = u256_from_i64(3);\n    let b: u256 = u256_from_i64(7);\n    \
        if a <= b { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(le), 1, "3 <= 7");
    let gt = "    let a: u256 = u256_from_i64(9);\n    let b: u256 = u256_from_i64(7);\n    \
        if a > b { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(gt), 1, "9 > 7");
}

#[test]
fn eq_compares_value_not_pointer() {
    // E3: two INDEPENDENTLY-allocated cells holding the same value must compare
    // equal — `==` routes to u256_eq (limb-wise), never the default pointer-eq.
    let eq = "    let a: u256 = u256_from_i64(42);\n    let b: u256 = u256_from_i64(42);\n    \
        if a == b { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(eq), 1, "distinct cells with equal value must be ==");
    let ne = "    let a: u256 = u256_from_i64(42);\n    let b: u256 = u256_from_i64(42);\n    \
        if a != b { return 0 - 2; }\n    return 0 - 1;";
    assert_eq!(
        decode(ne),
        1,
        "distinct cells with equal value must NOT be !="
    );
}

#[test]
fn eq_false_for_distinct_values() {
    let body = "    let a: u256 = u256_from_i64(41);\n    let b: u256 = u256_from_i64(42);\n    \
        if a == b { return 0 - 2; }\n    return 0 - 1;";
    assert_eq!(decode(body), 1, "41 == 42 is false");
}

// ── multiply correctness (PR-U1b) ────────────────────────────────────────────

#[test]
fn mul_small() {
    let body = "    let a: u256 = u256_from_i64(1000);\n    let b: u256 = u256_from_i64(1000);\n    \
        let c: u256 = a * b;\n    let e: u256 = u256_from_i64(1000000);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(body), 1, "1000 * 1000 = 1_000_000");
}

#[test]
fn mul_by_zero_and_one() {
    let z = "    let a: u256 = u256_from_i64(7);\n    let zero: u256 = u256_from_i64(0);\n    \
        let c: u256 = a * zero;\n    if c == zero { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(z), 1, "a * 0 = 0");
    let o = "    let a: u256 = u256_from_i64(7);\n    let one: u256 = u256_from_i64(1);\n    \
        let c: u256 = a * one;\n    if c == a { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(o), 1, "a * 1 = a");
}

#[test]
fn mul_commutes() {
    let body = "    let a: u256 = u256_from_i64(123);\n    let b: u256 = u256_from_i64(456);\n    \
        if a * b == b * a { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(body), 1, "a*b == b*a");
}

#[test]
fn mul_equals_repeated_addition() {
    // 2^62 * 3 == 2^62 + 2^62 + 2^62 (cross-checks mul against add).
    let body = "    let a: u256 = u256_from_i64(4611686018427387904);\n    \
        let three: u256 = u256_from_i64(3);\n    let c: u256 = a * three;\n    \
        let s: u256 = a + a + a;\n    if c == s { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(body), 1, "a*3 == a+a+a");
}

#[test]
fn mul_cross_limb() {
    // 2^64 * 2^64 = 2^128 (limb1 * limb1 → limb2).
    let body = "    let a: u256 = u256_make(0, 1, 0, 0);\n    let c: u256 = a * a;\n    \
        let e: u256 = u256_make(0, 0, 1, 0);\n    if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(body), 1, "2^64 * 2^64 = 2^128");
}

#[test]
fn mul_distributes_over_add_with_all_ones_limb() {
    // a = 2^64 - 1 (limb0 = all ones) exercises mulhi; a*(b+c) == a*b + a*c
    // holds regardless of the (un-writable-as-a-literal) product value.
    let body = "    let two64: u256 = u256_make(0, 1, 0, 0);\n    let one: u256 = u256_from_i64(1);\n    \
        let a: u256 = two64 - one;\n    \
        let b: u256 = u256_from_i64(7);\n    let c: u256 = u256_from_i64(11);\n    \
        let left: u256 = a * (b + c);\n    let right: u256 = a * b + a * c;\n    \
        if left == right { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(body), 1, "a*(b+c) == a*b + a*c with a = 2^64-1");
}

#[test]
fn mul_all_ones_by_two_carries_via_mulhi() {
    // (2^64 - 1) * 2 == 2^65 - 2 == (2*2^64) - 2. The high bit of the partial
    // product must carry into limb1 — directly exercises mul64_hi.
    let body = "    let two64: u256 = u256_make(0, 1, 0, 0);\n    let one: u256 = u256_from_i64(1);\n    \
        let max64: u256 = two64 - one;\n    let two: u256 = u256_from_i64(2);\n    \
        let c: u256 = max64 * two;\n    \
        let two65: u256 = u256_make(0, 2, 0, 0);\n    let e: u256 = two65 - two;\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(body), 1, "(2^64-1)*2 == 2^65-2");
}

#[test]
fn mul_high_limb_no_overflow() {
    // 2^192 * 2^32 = 2^224 (limb3 = 2^32), fits in 256 bits — must NOT trap.
    let body = "    let a: u256 = u256_make(0, 0, 0, 1);\n    \
        let b: u256 = u256_from_i64(4294967296);\n    let c: u256 = a * b;\n    \
        let e: u256 = u256_make(0, 0, 0, 4294967296);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode(body), 1, "2^192 * 2^32 = 2^224 (no overflow)");
}

#[test]
fn mul_overflow_at_2_256_reverts() {
    // 2^128 * 2^128 = 2^256 → the smallest overflow → revert (E1).
    let body =
        "    let a: u256 = u256_make(0, 0, 1, 0);\n    let c: u256 = a * a;\n    return 0 - 1;";
    expect_revert(body);
}

#[test]
fn mul_overflow_far_over_reverts() {
    // 2^192 * 2^128 = 2^320 ≫ 2^256 → revert (high partial products are nonzero).
    let body = "    let a: u256 = u256_make(0, 0, 0, 1);\n    let b: u256 = u256_make(0, 0, 1, 0);\n    \
        let c: u256 = a * b;\n    return 0 - 1;";
    expect_revert(body);
}

// ── divide / modulo (PR-U1c) ─────────────────────────────────────────────────

// Long division runs 256 iterations of allocating helpers, so the static
// fuel estimate is far too low — run these with a generous explicit budget.
const DIV_FUEL: u64 = 4_000_000_000;

fn decode_fuel(body: &str, fuel: u64) -> i64 {
    let result = compile_tool(&tool(body)).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", fuel, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a negative-sentinel return, got a genuine trap: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap message: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse sentinel from {message:?}: {e}"))
        }
        Err(other) => panic!("tool failed with a non-trap error: {other:?}"),
        Ok(_) => panic!("tool returned a positive packed-pointer; expected a negative sentinel"),
    }
}

fn expect_revert_fuel(body: &str, fuel: u64) {
    let result = compile_tool(&tool(body)).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", fuel, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            assert!(
                !message.contains("tool returned error ("),
                "expected a genuine checked-arith revert, got a sentinel: {message}"
            );
        }
        Err(other) => panic!("expected a trap revert, got: {other:?}"),
        Ok(_) => panic!("expected a checked-arith revert, but the tool returned successfully"),
    }
}

#[test]
fn div_basic_quotient_and_remainder() {
    let q = "    let a: u256 = u256_from_i64(100);\n    let b: u256 = u256_from_i64(7);\n    \
        let c: u256 = a / b;\n    let e: u256 = u256_from_i64(14);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(q, DIV_FUEL), 1, "100 / 7 = 14");
    let m = "    let a: u256 = u256_from_i64(100);\n    let b: u256 = u256_from_i64(7);\n    \
        let c: u256 = a % b;\n    let e: u256 = u256_from_i64(2);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(m, DIV_FUEL), 1, "100 % 7 = 2");
}

#[test]
fn divmod_satisfies_q_times_b_plus_r_identity() {
    // The core oracle: (a/b)*b + (a%b) == a, and (a%b) < b — checked with the
    // already-verified mul/add/compare. Holds for any a,b (b != 0).
    let body = "    let a: u256 = u256_from_i64(1000000);\n    let b: u256 = u256_from_i64(777);\n    \
        let q: u256 = a / b;\n    let r: u256 = a % b;\n    \
        let recon: u256 = q * b + r;\n    \
        if recon == a { if r < b { return 0 - 1; } else {} } else {}\n    return 0 - 2;";
    assert_eq!(decode_fuel(body, DIV_FUEL), 1, "q*b + r == a and r < b");
}

#[test]
fn divmod_identity_with_high_limb_dividend() {
    // a = 2^128 + 12345, b = 2^64 + 99 — exercises division across limb
    // boundaries; verified by the same q*b + r == a identity.
    let body = "    let a: u256 = u256_make(0, 0, 1, 0) + u256_from_i64(12345);\n    \
        let b: u256 = u256_make(0, 1, 0, 0) + u256_from_i64(99);\n    \
        let q: u256 = a / b;\n    let r: u256 = a % b;\n    \
        let recon: u256 = q * b + r;\n    \
        if recon == a { if r < b { return 0 - 1; } else {} } else {}\n    return 0 - 2;";
    assert_eq!(
        decode_fuel(body, DIV_FUEL),
        1,
        "high-limb q*b + r == a and r < b"
    );
}

#[test]
fn div_by_larger_is_zero_remainder_is_dividend() {
    let q = "    let a: u256 = u256_from_i64(5);\n    let b: u256 = u256_from_i64(10);\n    \
        let c: u256 = a / b;\n    let z: u256 = u256_from_i64(0);\n    \
        if c == z { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(q, DIV_FUEL), 1, "5 / 10 = 0");
    let m = "    let a: u256 = u256_from_i64(5);\n    let b: u256 = u256_from_i64(10);\n    \
        let c: u256 = a % b;\n    let e: u256 = u256_from_i64(5);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(m, DIV_FUEL), 1, "5 % 10 = 5");
}

#[test]
fn div_by_one_and_self() {
    let one = "    let a: u256 = u256_from_i64(123456);\n    let b: u256 = u256_from_i64(1);\n    \
        let c: u256 = a / b;\n    if c == a { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(one, DIV_FUEL), 1, "a / 1 = a");
    let slf = "    let a: u256 = u256_from_i64(123456);\n    \
        let q: u256 = a / a;\n    let r: u256 = a % a;\n    \
        let one: u256 = u256_from_i64(1);\n    let z: u256 = u256_from_i64(0);\n    \
        if q == one { if r == z { return 0 - 1; } else {} } else {}\n    return 0 - 2;";
    assert_eq!(decode_fuel(slf, DIV_FUEL), 1, "a / a = 1, a % a = 0");
}

#[test]
fn div_cross_limb() {
    // 2^128 / 2^64 = 2^64.
    let body = "    let a: u256 = u256_make(0, 0, 1, 0);\n    let b: u256 = u256_make(0, 1, 0, 0);\n    \
        let c: u256 = a / b;\n    let e: u256 = u256_make(0, 1, 0, 0);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(body, DIV_FUEL), 1, "2^128 / 2^64 = 2^64");
}

#[test]
fn div_by_zero_reverts() {
    let dz = "    let a: u256 = u256_from_i64(7);\n    let b: u256 = u256_from_i64(0);\n    \
        let c: u256 = a / b;\n    return 0 - 1;";
    expect_revert_fuel(dz, DIV_FUEL);
    let mz = "    let a: u256 = u256_from_i64(7);\n    let b: u256 = u256_from_i64(0);\n    \
        let c: u256 = a % b;\n    return 0 - 1;";
    expect_revert_fuel(mz, DIV_FUEL);
}

// ── bitwise + shifts (PR-U1c-2) ──────────────────────────────────────────────

#[test]
fn bitwise_and_or() {
    let an = "    let a: u256 = u256_from_i64(255);\n    let b: u256 = u256_from_i64(15);\n    \
        let c: u256 = a & b;\n    let e: u256 = u256_from_i64(15);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(an, DIV_FUEL), 1, "255 & 15 = 15");
    let or = "    let a: u256 = u256_from_i64(240);\n    let b: u256 = u256_from_i64(15);\n    \
        let c: u256 = a | b;\n    let e: u256 = u256_from_i64(255);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(or, DIV_FUEL), 1, "240 | 15 = 255");
}

#[test]
fn shl_small_and_cross_limb() {
    let s8 = "    let a: u256 = u256_from_i64(1);\n    let n: u256 = u256_from_i64(8);\n    \
        let c: u256 = a << n;\n    let e: u256 = u256_from_i64(256);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(s8, DIV_FUEL), 1, "1 << 8 = 256");
    let s64 = "    let a: u256 = u256_from_i64(1);\n    let n: u256 = u256_from_i64(64);\n    \
        let c: u256 = a << n;\n    let e: u256 = u256_make(0, 1, 0, 0);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(s64, DIV_FUEL), 1, "1 << 64 = 2^64");
    // 1 << 100 = 2^100: limb1 bit 36 set (2^36 = 68719476736). bit_shift != 0.
    let s100 = "    let a: u256 = u256_from_i64(1);\n    let n: u256 = u256_from_i64(100);\n    \
        let c: u256 = a << n;\n    let e: u256 = u256_make(0, 68719476736, 0, 0);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(s100, DIV_FUEL), 1, "1 << 100 = 2^100");
}

#[test]
fn shr_small_and_cross_limb() {
    let r8 = "    let a: u256 = u256_from_i64(256);\n    let n: u256 = u256_from_i64(8);\n    \
        let c: u256 = a >> n;\n    let e: u256 = u256_from_i64(1);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(r8, DIV_FUEL), 1, "256 >> 8 = 1");
    let r64 = "    let a: u256 = u256_make(0, 1, 0, 0);\n    let n: u256 = u256_from_i64(64);\n    \
        let c: u256 = a >> n;\n    let e: u256 = u256_from_i64(1);\n    \
        if c == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(r64, DIV_FUEL), 1, "2^64 >> 64 = 1");
}

#[test]
fn shift_by_256_or_more_is_zero() {
    let shl = "    let a: u256 = u256_from_i64(1);\n    let n: u256 = u256_from_i64(256);\n    \
        let c: u256 = a << n;\n    let z: u256 = u256_from_i64(0);\n    \
        if c == z { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(shl, DIV_FUEL), 1, "1 << 256 = 0");
    let shr = "    let a: u256 = u256_make(0, 1, 0, 0);\n    let n: u256 = u256_from_i64(256);\n    \
        let c: u256 = a >> n;\n    let z: u256 = u256_from_i64(0);\n    \
        if c == z { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(shr, DIV_FUEL), 1, "2^64 >> 256 = 0");
}

#[test]
fn shl_then_shr_roundtrips() {
    // 123456789 << 40 fits well under 2^256, so >> 40 recovers it (logical shift).
    let body = "    let a: u256 = u256_from_i64(123456789);\n    let n: u256 = u256_from_i64(40);\n    \
        let up: u256 = a << n;\n    let back: u256 = up >> n;\n    \
        if back == a { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(body, DIV_FUEL), 1, "(a << 40) >> 40 == a");
}

// ── wide / small literals (PR-U2) ────────────────────────────────────────────

#[test]
fn small_literal_coerces_to_u256() {
    // E9: `let x: u256 = 1000;` (a literal fitting i64) builds the same cell as
    // u256_from_i64(1000).
    let body = "    let x: u256 = 1000;\n    let y: u256 = u256_from_i64(1000);\n    \
        if x == y { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(
        decode_fuel(body, DIV_FUEL),
        1,
        "small u256 literal coercion"
    );
}

#[test]
fn wide_literal_at_2pow64() {
    // 18446744073709551616 = 2^64 → limb1 == 1, limb0 == 0 (just past i64 range).
    let body = "    let x: u256 = 18446744073709551616;\n    let e: u256 = u256_make(0, 1, 0, 0);\n    \
        if x == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(
        decode_fuel(body, DIV_FUEL),
        1,
        "wide literal 2^64 lands in limb1"
    );
}

#[test]
fn wide_literal_value_via_mul_oracle() {
    // 10^20 (> i64::MAX) == 10^10 * 10^10 (10^10 fits i64) — cross-checks the
    // wide-literal decimal parse against the verified multiply.
    let body = "    let big: u256 = 100000000000000000000;\n    \
        let a: u256 = u256_from_i64(10000000000);\n    let e: u256 = a * a;\n    \
        if big == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(body, DIV_FUEL), 1, "10^20 literal == (10^10)^2");
}

#[test]
fn wide_literal_arithmetic() {
    // (2^64) + 5 → limb0 = 5, limb1 = 1.
    let body = "    let x: u256 = 18446744073709551616;\n    \
        let y: u256 = x + u256_from_i64(5);\n    let e: u256 = u256_make(5, 1, 0, 0);\n    \
        if y == e { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(decode_fuel(body, DIV_FUEL), 1, "2^64 + 5");
}

// ── wide HEX literals (PR-U2-b) ──────────────────────────────────────────────

#[test]
fn hex_wide_literal_equals_decimal() {
    // 0x10000000000000000 == 18446744073709551616 (both = 2^64) — cross-checks the
    // wide-hex parse against the verified wide-decimal parse.
    let body = "    let h: u256 = 0x10000000000000000;\n    \
        let d: u256 = 18446744073709551616;\n    \
        if h == d { return 0 - 1; }\n    return 0 - 2;";
    assert_eq!(
        decode_fuel(body, DIV_FUEL),
        1,
        "0x1_0000_0000_0000_0000 == 2^64"
    );
}

#[test]
fn hex_max_u256_plus_one_reverts() {
    // 0x<64 f's> is exactly 2^256-1 (max u256); adding 1 overflows and the checked
    // `+` reverts. The revert PROVES the 64-digit hex parsed to the true maximum
    // (a short/wrong parse would leave headroom and NOT overflow).
    let body = "    let max: u256 = \
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;\n    \
        let one: u256 = 1;\n    let r: u256 = max + one;\n    return 0 - 1;";
    expect_revert_fuel(body, DIV_FUEL);
}
