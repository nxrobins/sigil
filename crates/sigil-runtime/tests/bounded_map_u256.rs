//! Runtime tests for the BOUNDED `u256`→`u256` map (`BoundedMap_u256_u256_64`),
//! the Solidity-frontend `mapping(address => uint256)` target (SOL1). Mirrors the
//! `bounded_map.rs` harness: `neg` decodes a `return 0 - K` sentinel; `body_traps`
//! detects a genuine trap (for the force-trap test). Each test runs under a
//! no-`! { Alloc }` `tool_main`, so it is ALSO an ET-2 Alloc-free proof.
//!
//! u256 values are compared IN-SIGIL with `==` (which routes to `u256_eq`, a true
//! 32-byte value compare) and the body returns a constant pass/fail sentinel — the
//! same decode discipline as `u256_arithmetic.rs`, since a u256 cannot be returned
//! through the i64 `tool_main` ABI directly. The headline correctness property
//! (NC-L5 / LM9): a get returns the right value, an absent key reads as the
//! default, the 65th distinct key traps (never silent-drops), and key identity is
//! VALUE equality (a computed-fresh key collides), never pointer identity.

mod common;

use std::collections::HashMap;

use proptest::prelude::*;
use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

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

/// Body prefix: a fresh u256 map with `n` distinct entries (key=i, val=i*100). The
/// literals coerce to u256 in the `insert(u256, u256)` argument positions.
fn fill_u256(n: i64) -> String {
    let mut s =
        String::from("    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n");
    for i in 0..n {
        s.push_str(&format!(
            "    let _r{i}: i64 = m.insert({}, {});\n",
            i,
            i * 100
        ));
    }
    s
}

#[test]
fn mu1_insert_get_roundtrip() {
    // insert(7,42), insert(9,99); get(7) is Some(42). Some-and-equal → 1.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 42);\n    let _b: i64 = m.insert(9, 99);\n    match m.get(7) { Some(v) => { if v == 42 { return 0 - 1; } else { return 0 - 2; } }, None => { return 0 - 9; }, }"
        ),
        1
    );
}

#[test]
fn mu2_get_absent_is_none() {
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 42);\n    match m.get(8) { Some(v) => { return 0 - 2; }, None => { return 0 - 5; }, }"
        ),
        5
    );
}

#[test]
fn mu3_get_or_default() {
    // get_or(8, 77) on an absent key returns the default 77.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 42);\n    let r: u256 = m.get_or(8, 77);\n    if r == 77 { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn mu4_overwrite_not_append() {
    // insert(7,1); insert(7,5) → get(7)==5 AND len()==1.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 1);\n    let _b: i64 = m.insert(7, 5);\n    let r: u256 = m.get_or(7, 0);\n    if r == 5 { if m.len() == 1 { return 0 - 1; } else { return 0 - 3; } } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn mu5_contains_key_hit_miss() {
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 42);\n    if m.contains_key(7) { if m.contains_key(8) { return 0 - 3; } else { return 0 - 1; } } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn mu6_full_insert_existing_ok() {
    // Fill 64 distinct, re-insert an existing key (key 0) → clean, len stays 64.
    let body = format!(
        "{}    let _o: i64 = m.insert(0, 12345);\n    return 0 - m.len();",
        fill_u256(64)
    );
    assert_eq!(neg(&body), 64);
}

#[test]
fn mu7_full_insert_new_traps() {
    // Fill 64 distinct, insert a 65th NEW key → backing force-trap (NC-L1: loud,
    // never a silent drop).
    let body = format!(
        "{}    let _o: i64 = m.insert(99999, 1);\n    return 0 - 1;",
        fill_u256(64)
    );
    assert!(body_traps(&body), "full + insert NEW key must trap");
}

#[test]
fn mu8_fill_exactly_n_clean() {
    // 64 distinct inserts: no trap; is_full true; len==capacity==64.
    let body = format!(
        "{}    if m.is_full() {{ return 0 - (m.len() * 100 + m.capacity()); }} else {{ return 0 - 1; }}",
        fill_u256(64)
    );
    assert_eq!(neg(&body), 6464);
}

#[test]
fn mu9_empty_get_none_and_is_empty() {
    assert_eq!(
        neg(
            "    let m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    if m.is_empty() { match m.get(0) { Some(v) => { return 0 - 2; }, None => { return 0 - 5; }, } } else { return 0 - 1; }"
        ),
        5
    );
}

#[test]
fn mu10_capacity_exact() {
    assert_eq!(
        neg(
            "    let m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    return 0 - m.capacity();"
        ),
        64
    );
}

#[test]
fn mu_value_equality_not_pointer_identity() {
    // Insert key 100; look up a key built via u256 ARITHMETIC (99 + 1 → a fresh u256
    // object with value 100) — MUST collide. Proves `==` is u256_eq (value compare),
    // not pointer identity (two distinct 32-byte cells with equal bytes match).
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(100, 7);\n    let base: u256 = 99;\n    let k: u256 = base + 1;\n    match m.get(k) { Some(v) => { if v == 7 { return 0 - 11; } else { return 0 - 12; } }, None => { return 0 - 9; }, }"
        ),
        11
    );
}

#[test]
fn mu_try_insert_full_new_returns_false_no_trap() {
    // Fill 64, try_insert a NEW key → false (no trap), len unchanged at 64.
    let body = format!(
        "{}    let ok: bool = m.try_insert(99999, 1);\n    if ok {{ return 0 - 1; }} else {{ return 0 - m.len(); }}",
        fill_u256(64)
    );
    assert_eq!(neg(&body), 64);
}

#[test]
fn mu_try_insert_existing_overwrites_true() {
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 1);\n    let ok: bool = m.try_insert(7, 9);\n    let r: u256 = m.get_or(7, 0);\n    if ok { if r == 9 { if m.len() == 1 { return 0 - 1; } else { return 0 - 4; } } else { return 0 - 2; } } else { return 0 - 3; }"
        ),
        1
    );
}

// ───────────────────────── transfer (the SOL1b target) ─────────────────────────

#[test]
fn tr_basic_debit_credit() {
    // from=100, to=5; transfer 30 → from=70, to=35. Decode from*1000 + to = 70035.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 100);\n    let _b: i64 = m.insert(2, 5);\n    m.transfer(1, 2, 30);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    if f == 70 { if t == 35 { return 0 - 70035; } else { return 0 - 1; } } else { return 0 - 2; }"
        ),
        70035
    );
}

#[test]
fn tr_insufficient_balance_traps() {
    // from=10, transfer 50 → checked-underflow trap (the `bal[from] -= amount` revert).
    let body = "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 10);\n    m.transfer(1, 2, 50);\n    return 0 - 1;";
    assert!(body_traps(body), "insufficient balance must trap");
}

#[test]
fn tr_self_transfer_is_net_zero() {
    // from==to, balance 100, transfer 30 → net zero (sequential -30 then +30); stays 100.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 100);\n    m.transfer(1, 1, 30);\n    let f: u256 = m.get_or(1, 0);\n    if f == 100 { if m.len() == 1 { return 0 - 100; } else { return 0 - 2; } } else { return 0 - 1; }"
        ),
        100
    );
}

#[test]
fn tr_self_transfer_still_checks_balance() {
    // from==to but balance 10 < amount 50 → traps (matches the `-=` underflow even for
    // a self-transfer; the balance check precedes the from==to short-circuit).
    let body = "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 10);\n    m.transfer(1, 1, 50);\n    return 0 - 1;";
    assert!(body_traps(body), "self-transfer must still check balance");
}

#[test]
fn tr_credit_overflow_traps() {
    // to = 2^256-1 (max u256), transfer 1 → credit overflows → trap BEFORE any write.
    let max = "115792089237316195423570985008687907853269984665640564039457584007913129639935";
    let body = format!(
        "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 100);\n    let _b: i64 = m.insert(2, {max});\n    m.transfer(1, 2, 1);\n    return 0 - 1;"
    );
    assert!(body_traps(&body), "credit overflow must trap");
}

#[test]
fn tr_to_new_key_when_room() {
    // from=100 present, to=2 absent, room available → to is created with the amount.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 100);\n    m.transfer(1, 2, 40);\n    let t: u256 = m.get_or(2, 0);\n    if t == 40 { if m.len() == 2 { return 0 - 40; } else { return 0 - 2; } } else { return 0 - 1; }"
        ),
        40
    );
}

#[test]
fn tr_capacity_full_new_key_traps() {
    // Fill keys 0..63 (64 entries), give key 0 a balance, transfer from 0 to a NEW key
    // 99999 when the map is full → capacity reservation traps BEFORE any write (no
    // fund destruction). fill_u256(64) sets key 0's value to 0, so first top it up.
    let body = format!(
        "{}    let _t: i64 = m.insert(0, 500);\n    m.transfer(0, 99999, 10);\n    return 0 - 1;",
        fill_u256(64)
    );
    assert!(
        body_traps(&body),
        "transfer creating the 65th distinct key must trap"
    );
}

#[test]
fn tr_zero_amount_is_total_noop() {
    // amount==0 is a TOTAL no-op: no trap, no entry created for an absent `to`, balances
    // unchanged. Decode: to absent → len stays 1 (only `from`), get_or(to)=0.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 100);\n    let ok: bool = m.transfer(1, 2, 0);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    if ok { if f == 100 { if t == 0 { if m.len() == 1 { return 0 - 7; } else { return 0 - 4; } } else { return 0 - 3; } } else { return 0 - 2; } } else { return 0 - 1; }"
        ),
        7
    );
}

#[test]
fn tr_full_map_existing_keys_ok() {
    // Map full (64 keys), transfer between two EXISTING keys → no capacity trap (no new
    // key), debit/credit applied. keys 1 and 2 exist (from fill: key i has value i*100).
    let body = format!(
        "{}    let _t: i64 = m.insert(1, 1000);\n    m.transfer(1, 2, 600);\n    let f: u256 = m.get_or(1, 0);\n    if f == 400 {{ return 0 - 400; }} else {{ return 0 - 1; }}",
        fill_u256(64)
    );
    assert_eq!(neg(&body), 400);
}

// ──────────────── reserve1 (the SOL-MULTIMAP ≥2-map reservation) ────────────────

#[test]
fn rv1_room_available_is_noop() {
    // A non-full map, reserve1 a NEW key → no trap; commits NOTHING (len stays 1, the key
    // is NOT created). Returns true.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 42);\n    let ok: bool = m.reserve1(999);\n    if ok { if m.len() == 1 { if m.contains_key(999) { return 0 - 3; } else { return 0 - 1; } } else { return 0 - 2; } } else { return 0 - 4; }"
        ),
        1
    );
}

#[test]
fn rv1_full_existing_key_is_noop() {
    // Full map (64 keys), reserve1 an EXISTING key (0) → no trap (an existing-key insert
    // never needs a new slot). len stays 64.
    let body = format!(
        "{}    let ok: bool = m.reserve1(0);\n    if ok {{ return 0 - m.len(); }} else {{ return 0 - 1; }}",
        fill_u256(64)
    );
    assert_eq!(neg(&body), 64);
}

#[test]
fn rv1_full_new_key_traps() {
    // Full map (64 keys), reserve1 a NEW key → traps (a later insert of that key WOULD
    // trap; the reservation surfaces it up front, before any write).
    let body = format!(
        "{}    let _ok: bool = m.reserve1(99999);\n    return 0 - 1;",
        fill_u256(64)
    );
    assert!(
        body_traps(&body),
        "reserve1 of a NEW key on a full map must trap"
    );
}

#[test]
fn rv1_reserved_then_insert_is_safe() {
    // The reserve-then-write contract: reserve1 commits nothing, so after it the insert of
    // the SAME new key succeeds and is the write that actually creates the slot. 63 keys +
    // reserve(new) + insert(new) → len 64, value present.
    let body = format!(
        "{}    let _ok: bool = m.reserve1(5000);\n    let _i: i64 = m.insert(5000, 77);\n    let v: u256 = m.get_or(5000, 0);\n    if v == 77 {{ if m.len() == 64 {{ return 0 - 64; }} else {{ return 0 - 2; }} }} else {{ return 0 - 1; }}",
        fill_u256(63)
    );
    assert_eq!(neg(&body), 64);
}

// ─────────── transfer_split (SOL-MULTIMAP M-B): the fee-on-transfer aliasing exec-proof ───────────
// `transfer_split(from, amount, to, net, feeTo, fee)` = `M[from]-=amount; M[to]+=net; M[feeTo]+=fee;`
// applied sequentially, aliasing-correct across ALL 5 partitions of {from,to,feeTo}. Each test asserts
// the EXACT final balances (the correctness oracle EX-B2); the trap paths prove reserve-all-then-write.

/// Setup: `insert(1,100); insert(2,5);` (feeTo=3 absent → 0). Three distinct addresses.
fn ts_setup() -> String {
    String::from(
        "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 100);\n    let _b: i64 = m.insert(2, 5);\n",
    )
}

#[test]
fn ts_all_distinct() {
    // 1(100)/2(5)/3(0); split(1,30, 2,25, 3,5) → 1=70, 2=30, 3=5. Decode f*10000+t*100+e.
    let body = format!(
        "{}    m.transfer_split(1, 30, 2, 25, 3, 5);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    let e: u256 = m.get_or(3, 0);\n    if f == 70 {{ if t == 30 {{ if e == 5 {{ return 0 - 703005; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }} }} else {{ return 0 - 3; }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 703005);
}

#[test]
fn ts_from_eq_to() {
    // from==to==1(100), feeTo=3(0); split(1,30, 1,25, 3,5) → slot1 = 100-30+25 = 95, slot3 = 5.
    let body = format!(
        "{}    m.transfer_split(1, 30, 1, 25, 3, 5);\n    let f: u256 = m.get_or(1, 0);\n    let e: u256 = m.get_or(3, 0);\n    if f == 95 {{ if e == 5 {{ return 0 - 9505; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 9505);
}

#[test]
fn ts_from_eq_feeto() {
    // from==feeTo==1(100), to=2(5); split(1,30, 2,25, 1,5) → slot1 = 100-30+5 = 75, slot2 = 5+25 = 30.
    let body = format!(
        "{}    m.transfer_split(1, 30, 2, 25, 1, 5);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    if f == 75 {{ if t == 30 {{ return 0 - 7530; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 7530);
}

#[test]
fn ts_to_eq_feeto() {
    // to==feeTo==2(5), from=1(100); split(1,30, 2,25, 2,5) → slot1 = 70, slot2 = 5+25+5 = 35.
    // THE MC-B1 LOST-CREDIT CASE: an alias-blind pre-compute would clobber (slot2 = 5+5 = 10, losing net).
    let body = format!(
        "{}    m.transfer_split(1, 30, 2, 25, 2, 5);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    if f == 70 {{ if t == 35 {{ return 0 - 7035; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 7035);
}

#[test]
fn ts_all_equal() {
    // from==to==feeTo==1(100); split(1,30, 1,25, 1,5) → slot1 = 100-30+25+5 = 100.
    let body = format!(
        "{}    m.transfer_split(1, 30, 1, 25, 1, 5);\n    let f: u256 = m.get_or(1, 0);\n    if f == 100 {{ return 0 - 100; }} else {{ return 0 - 1; }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 100);
}

#[test]
fn ts_underflow_traps() {
    // from=1 has only 10, amount 30 → step-1 debit underflows → trap BEFORE any write.
    let body = "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 10);\n    m.transfer_split(1, 30, 2, 25, 3, 5);\n    return 0 - 1;";
    assert!(body_traps(body), "split debit underflow must trap");
}

#[test]
fn ts_credit_overflow_traps() {
    // to=2 = MAX u256; step-2 credit `to += net` overflows → trap BEFORE any write (atomicity: from's
    // debit is NOT committed, since all arithmetic precedes all writes).
    let max = "115792089237316195423570985008687907853269984665640564039457584007913129639935";
    let body = format!(
        "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 100);\n    let _b: i64 = m.insert(2, {max});\n    m.transfer_split(1, 30, 2, 25, 3, 5);\n    return 0 - 1;"
    );
    assert!(body_traps(&body), "split credit overflow must trap");
}

#[test]
fn ts_capacity_new_key_traps() {
    // Map full (64 keys, 0..63 with key i = i*100 so key 1 = 100). split moves from an EXISTING key to
    // an EXISTING key but the feeTo is a NEW key at capacity → reservation traps BEFORE any write.
    let body = format!(
        "{}    m.transfer_split(1, 30, 2, 25, 99999, 5);\n    return 0 - 1;",
        fill_u256(64)
    );
    assert!(
        body_traps(&body),
        "split creating a new distinct key on a full map must trap"
    );
}

#[test]
fn ts_full_map_all_existing_ok() {
    // Full map (64), split among three EXISTING keys (1,2,3) → no capacity trap. key i = i*100:
    // 1=100, 2=200, 3=300. split(1,30, 2,25, 3,5) → 1=70, 2=225, 3=305.
    let body = format!(
        "{}    m.transfer_split(1, 30, 2, 25, 3, 5);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    let e: u256 = m.get_or(3, 0);\n    if f == 70 {{ if t == 225 {{ if e == 305 {{ return 0 - 702; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }} }} else {{ return 0 - 3; }}",
        fill_u256(64)
    );
    assert_eq!(neg(&body), 702);
}

// ── SOL-UPDATE: `erc20_update(ts, from, to, value) -> new_ts` exec-proof ────────────────────────
// The trusted-primitive correctness oracle (EX-2): every `from ∈ {0, nonzero} × to ∈ {0, nonzero}`
// quadrant + the nonzero self-transfer + the degenerate double-zero, asserting EXACT final
// balances AND the returned totalSupply; every trap direction (mint ts-overflow, burn
// ts-underflow, debit underflow, credit overflow, capacity); and the zero-slot invariant —
// `balances[0]` is NEVER inserted (`contains_key(0)` stays false), the MC-3 pin. The u256 return
// is compared IN-SIGIL (it cannot cross the i64 tool ABI). Baseline ts = 1000; ts_setup: 1=100, 2=5.

#[test]
fn eu_transfer_all_distinct() {
    // transfer 1→2 of 30: bal1 100→70, bal2 5→35, ts unchanged 1000.
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 1, 2, 30);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    if nts == 1000 {{ if f == 70 {{ if t == 35 {{ return 0 - 7035; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }} }} else {{ return 0 - 3; }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 7035);
}

#[test]
fn eu_mint() {
    // from=0 MINTS: ts 1000→1030, bal2 5→35, bal1 untouched, balances[0] NEVER inserted.
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 0, 2, 30);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    let z: bool = m.contains_key(0);\n    if z {{ return 0 - 8; }} else {{ if nts == 1030 {{ if f == 100 {{ if t == 35 {{ return 0 - 1030; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }} }} else {{ return 0 - 3; }} }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 1030);
}

#[test]
fn eu_burn() {
    // to=0 BURNS: ts 1000→970, bal1 100→70, bal2 untouched, balances[0] NEVER inserted.
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 1, 0, 30);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    let z: bool = m.contains_key(0);\n    if z {{ return 0 - 8; }} else {{ if nts == 970 {{ if f == 70 {{ if t == 5 {{ return 0 - 970; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }} }} else {{ return 0 - 3; }} }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 970);
}

#[test]
fn eu_self_transfer_net_zero() {
    // from==to==1 (nonzero): debit then credit of the ONE slot → bal1 stays 100, ts stays 1000
    // (the alias-sync: the credit reads the DEBITED value; an alias-blind impl gets 130 or 70).
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 1, 1, 30);\n    let f: u256 = m.get_or(1, 0);\n    if nts == 1000 {{ if f == 100 {{ return 0 - 100; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 100);
}

#[test]
fn eu_degenerate_zero_zero() {
    // from==to==0: mint-add then burn-sub of the SAME value nets ts back to 1000; NO balance
    // write at all; balances[0] never inserted.
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 0, 0, 30);\n    let f: u256 = m.get_or(1, 0);\n    let z: bool = m.contains_key(0);\n    if z {{ return 0 - 8; }} else {{ if nts == 1000 {{ if f == 100 {{ return 0 - 11; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }} }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 11);
}

#[test]
fn eu_mint_to_new_key() {
    // Mint to an ABSENT address 3: the key is inserted (capacity-reserved), bal3 = 7, ts 1000→1007.
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 0, 3, 7);\n    let t: u256 = m.get_or(3, 0);\n    if nts == 1007 {{ if t == 7 {{ return 0 - 1007; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 1007);
}

#[test]
fn eu_burn_whole_balance() {
    // Burn the ENTIRE balance of address 2 (5): bal2 → 0 (exact boundary, no underflow), ts → 995.
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 2, 0, 5);\n    let t: u256 = m.get_or(2, 0);\n    if nts == 995 {{ if t == 0 {{ return 0 - 995; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 995);
}

#[test]
fn eu_full_map_all_existing_ok() {
    // Full map (64 keys, key i = i*100): a transfer between EXISTING keys needs no reservation →
    // no capacity trap. 1: 100→70, 2: 200→230, ts unchanged.
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 1, 2, 30);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    if nts == 1000 {{ if f == 70 {{ if t == 230 {{ return 0 - 70230; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }} }} else {{ return 0 - 3; }}",
        fill_u256(64)
    );
    assert_eq!(neg(&body), 70230);
}

#[test]
fn eu_mint_ts_overflow_traps() {
    // ts = MAX u256, mint 1 → the step-1 `ts + value` overflows → trap BEFORE any write.
    let max = "115792089237316195423570985008687907853269984665640564039457584007913129639935";
    let body = format!(
        "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(2, 5);\n    let nts: u256 = m.erc20_update({max}, 0, 2, 1);\n    return 0 - 1;"
    );
    assert!(body_traps(&body), "mint totalSupply overflow must trap");
}

#[test]
fn eu_burn_ts_underflow_traps() {
    // ts = 5, burn 30 → the step-1 `new_ts - value` underflows → trap BEFORE any write
    // (balances untouched: ts is computed before the debit even runs).
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(5, 1, 0, 30);\n    return 0 - 1;",
        ts_setup()
    );
    assert!(body_traps(&body), "burn totalSupply underflow must trap");
}

#[test]
fn eu_debit_underflow_traps() {
    // from=1 has only 10, transfer 30 → the debit `trap_if(fv < value)` fires (the
    // insufficient-balance revert) BEFORE any write.
    let body = "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 10);\n    let nts: u256 = m.erc20_update(1000, 1, 2, 30);\n    return 0 - 1;";
    assert!(body_traps(body), "debit underflow must trap");
}

#[test]
fn eu_credit_overflow_traps() {
    // to=2 = MAX u256 → the credit `tv + value` overflows → trap BEFORE any write (the
    // debit is NOT committed — all arithmetic precedes all inserts).
    let max = "115792089237316195423570985008687907853269984665640564039457584007913129639935";
    let body = format!(
        "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 100);\n    let _b: i64 = m.insert(2, {max});\n    let nts: u256 = m.erc20_update(1000, 1, 2, 30);\n    return 0 - 1;"
    );
    assert!(body_traps(&body), "credit overflow must trap");
}

#[test]
fn eu_capacity_new_key_traps() {
    // Full map (64 keys), mint to a NEW address → the reservation `trap_if(count + needed > 64)`
    // fires BEFORE any write (the 65th distinct holder).
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 0, 99999, 5);\n    return 0 - 1;",
        fill_u256(64)
    );
    assert!(
        body_traps(&body),
        "mint creating a new key on a full map must trap"
    );
}

#[test]
fn eu_self_transfer_insufficient_traps() {
    // from==to==1 with balance 10, transfer 30: net-zero, but Solidity still executes (and
    // reverts) the debit — the primitive's debit check runs even on a self-transfer.
    let body = "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 10);\n    let nts: u256 = m.erc20_update(1000, 1, 1, 30);\n    return 0 - 1;";
    assert!(
        body_traps(body),
        "a self-transfer exceeding the balance must still trap"
    );
}

#[test]
fn eu_zero_value_is_total_noop() {
    // Adversarial-review pin: a ZERO-VALUE update is a TOTAL no-op (the `transfer` zero-amount
    // precedent). Solidity `_update(1, 9, 0)` changes nothing; materializing a value-0 slot for
    // the absent key 9 would consume bounded capacity for a NON-holder (free slot griefing).
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 1, 9, 0);\n    let f: u256 = m.get_or(1, 0);\n    let z: bool = m.contains_key(9);\n    if z {{ return 0 - 8; }} else {{ if nts == 1000 {{ if f == 100 {{ return 0 - 90; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }} }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 90);
}

#[test]
fn eu_zero_value_transfer_full_map_fresh_key_ok() {
    // Adversarial-review pin: at 64 holders, a zero-value TRANSFER to a fresh address must
    // SUCCEED with unchanged state (Solidity does) — not trap on the capacity reservation.
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 1, 99999, 0);\n    let z: bool = m.contains_key(99999);\n    if z {{ return 0 - 8; }} else {{ if nts == 1000 {{ return 0 - 91; }} else {{ return 0 - 1; }} }}",
        fill_u256(64)
    );
    assert_eq!(neg(&body), 91);
}

#[test]
fn eu_zero_value_mint_full_map_fresh_key_ok() {
    // Adversarial-review pin: at 64 holders, a zero-value MINT to a fresh address must SUCCEED
    // with an unchanged supply (Solidity does) — not trap on the capacity reservation.
    let body = format!(
        "{}    let nts: u256 = m.erc20_update(1000, 0, 99999, 0);\n    let z: bool = m.contains_key(99999);\n    if z {{ return 0 - 8; }} else {{ if nts == 1000 {{ return 0 - 92; }} else {{ return 0 - 1; }} }}",
        fill_u256(64)
    );
    assert_eq!(neg(&body), 92);
}

// ── SOL-ZERO-SWEEP: transfer_split per-address zero-value faithfulness ──────────────────────────
// A leg with a ZERO delta on a FRESH address must be a no-op (Solidity `balances[k] += 0` neither
// grows storage nor traps): the primitive must NOT reserve capacity for, nor insert, that key —
// else it materializes a value-0 slot (bounded-capacity griefing) and traps at 64 holders where
// Solidity succeeds. An EXISTING key is updated as before; a NON-zero leg still inserts a fresh key.

#[test]
fn ts_zero_fee_fresh_feeto_no_slot() {
    // fee==0 with a FRESH feeTo (a real transfer): the feeTo leg is `+= 0` → no slot materialized.
    // 1: 100→90, 2: 5→15, 99999 stays ABSENT (len 2, not 3).
    let body = format!(
        "{}    m.transfer_split(1, 10, 2, 10, 99999, 0);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    let z: bool = m.contains_key(99999);\n    let n: i64 = m.len();\n    if z {{ return 0 - 8; }} else {{ if n == 2 {{ if f == 90 {{ if t == 15 {{ return 0 - 9015; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }} }} else {{ return 0 - 3; }} }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 9015);
}

#[test]
fn ts_zero_fee_full_map_fresh_feeto_ok() {
    // At 64 holders, fee==0 with a fresh feeTo must SUCCEED (Solidity `balances[feeTo] += 0`
    // consumes no storage) — not trap on the capacity reservation. 1: 100→90, 2: 200→210.
    let body = format!(
        "{}    m.transfer_split(1, 10, 2, 10, 99999, 0);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    let z: bool = m.contains_key(99999);\n    if z {{ return 0 - 8; }} else {{ if f == 90 {{ if t == 210 {{ return 0 - 90210; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }} }}",
        fill_u256(64)
    );
    assert_eq!(neg(&body), 90210);
}

#[test]
fn ts_all_zero_fresh_keys_no_slots() {
    // transfer_split(7,0,8,0,9,0) on an empty map: three zero legs on three fresh addresses →
    // NO slots materialized (Solidity: all three `+= 0`/`-= 0` are no-ops). len stays 0.
    let body = "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    m.transfer_split(7, 0, 8, 0, 9, 0);\n    let n: i64 = m.len();\n    if n == 0 { return 0 - 40; } else { return 0 - 1; }";
    assert_eq!(neg(body), 40);
}

#[test]
fn ts_zero_net_fresh_to_no_slot() {
    // net==0 (100% fee) with a fresh `to`: the `to` leg is `+= 0` → no `to` slot; feeTo (fresh,
    // fee 10) IS inserted. 1: 100→90, 88888 ABSENT, 3: →10.
    let body = format!(
        "{}    m.transfer_split(1, 10, 88888, 0, 3, 10);\n    let f: u256 = m.get_or(1, 0);\n    let e: u256 = m.get_or(3, 0);\n    let z: bool = m.contains_key(88888);\n    if z {{ return 0 - 8; }} else {{ if f == 90 {{ if e == 10 {{ return 0 - 9010; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }} }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 9010);
}

#[test]
fn ts_zero_fee_existing_feeto_updates() {
    // fee==0 with an EXISTING feeTo: the existing slot is updated (a no-op update to its current
    // value) — no capacity change, no divergence. Regression guard for the existing-key path.
    let body = "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 100);\n    let _b: i64 = m.insert(2, 5);\n    let _c: i64 = m.insert(3, 7);\n    m.transfer_split(1, 10, 2, 10, 3, 0);\n    let f: u256 = m.get_or(1, 0);\n    let t: u256 = m.get_or(2, 0);\n    let e: u256 = m.get_or(3, 0);\n    let n: i64 = m.len();\n    if n == 3 { if f == 90 { if t == 15 { if e == 7 { return 0 - 7; } else { return 0 - 1; } } else { return 0 - 2; } } else { return 0 - 3; } } else { return 0 - 4; }";
    assert_eq!(neg(body), 7);
}

#[test]
fn ts_nonzero_fee_fresh_feeto_still_inserts() {
    // Regression: a NON-zero fee to a fresh feeTo MUST still insert the slot (the zero-skip must
    // not over-fire). 1: 100→90, 2: 5→10, 99999: →5 (present).
    let body = format!(
        "{}    m.transfer_split(1, 10, 2, 5, 99999, 5);\n    let e: u256 = m.get_or(99999, 0);\n    let z: bool = m.contains_key(99999);\n    if z {{ if e == 5 {{ return 0 - 5; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }}",
        ts_setup()
    );
    assert_eq!(neg(&body), 5);
}

// ─────────── batch_transfer (SOL-AIRDROP Rung C): the N-ary atomic airdrop exec-proof ───────────
// `batch_transfer(from, recipients, amounts)` = debit `from` by each `amounts[i]`, credit each
// `recipients[i]`, via validate-on-a-deep-clone-then-BLIT (atomic without rollback). Aliasing-correct
// over N (a DUPLICATE recipient accumulates; `recipient==from` self-leg nets zero). Each test asserts
// EXACT final balances (the oracle); trap paths prove fail-closed. `bt_clone_isolation` pins the
// deep_copy independence (the atomicity foundation); `bt_max_atomic_at_recommended_budget` re-proves
// MI-FUEL at the RECOMMENDED budget with the injected stdlib (no fuel-trap mid-commit).

const U256_MAX: &str =
    "115792089237316195423570985008687907853269984665640564039457584007913129639935";

/// A fresh `BoundedVec_u256_64` local `name`, filled via `new()` + `push` (the sole sealed ctor).
fn mkvec(name: &str, elems: &[i64]) -> String {
    let mut s = format!("    let mut {name}: BoundedVec_u256_64 = BoundedVec_u256_64::new();\n");
    for (i, e) in elems.iter().enumerate() {
        s.push_str(&format!("    let _{name}p{i}: i64 = {name}.push({e});\n"));
    }
    s
}

/// A fresh map `m` seeded with (key,val) pairs.
fn bt_seed(pairs: &[(i64, i64)]) -> String {
    let mut s =
        String::from("    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n");
    for (i, (k, v)) in pairs.iter().enumerate() {
        s.push_str(&format!("    let _bs{i}: i64 = m.insert({k}, {v});\n"));
    }
    s
}

/// Assemble a batch_transfer body: seed → recips vec → amts vec → the call → `tail` (checks + return).
fn bt_body(seed: &[(i64, i64)], recips: &[i64], amts: &[i64], from: i64, tail: &str) -> String {
    let mut s = bt_seed(seed);
    s.push_str(&mkvec("recips", recips));
    s.push_str(&mkvec("amts", amts));
    s.push_str(&format!(
        "    let _ok: bool = m.batch_transfer({from}, recips, amts);\n"
    ));
    s.push_str(tail);
    s
}

/// Like `neg`, but runs at the RECOMMENDED fuel budget (NOT the 1e9 override) — the MI-FUEL check.
/// A `return 0 - K` arrives as the sentinel Trapped; a genuine FUEL trap panics (flags non-completion).
fn neg_at_recommended(body: &str) -> i64 {
    let result = compile_tool(&tool(body)).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            let s = message.find(p).unwrap_or_else(|| {
                panic!(
                    "NOT the sentinel (a FUEL trap?) at recommended budget {}: {message}",
                    result.fuel_budget
                )
            }) + p.len();
            let e = message[s..].find(')').unwrap();
            message[s..s + e].parse().unwrap()
        }
        other => panic!("expected sentinel, got {other:?}"),
    }
}

#[test]
fn bt_two_distinct() {
    let body = bt_body(
        &[(1, 1000)],
        &[2, 3],
        &[10, 20],
        1,
        "    let f: u256 = m.get_or(1, 0);\n    let r2: u256 = m.get_or(2, 0);\n    let r3: u256 = m.get_or(3, 0);\n    if f == 970 { if r2 == 10 { if r3 == 20 { return 0 - 210; } else { return 0 - 999; } } else { return 0 - 999; } } else { return 0 - 999; }",
    );
    assert_eq!(neg(&body), 210, "distinct airdrop: 1=970, 2=10, 3=20");
}

#[test]
fn bt_single() {
    let body = bt_body(
        &[(1, 100)],
        &[2],
        &[30],
        1,
        "    let f: u256 = m.get_or(1, 0);\n    let r2: u256 = m.get_or(2, 0);\n    if f == 70 { if r2 == 30 { return 0 - 211; } else { return 0 - 999; } } else { return 0 - 999; }",
    );
    assert_eq!(
        neg(&body),
        211,
        "single-recipient airdrop = a plain transfer"
    );
}

#[test]
fn bt_empty() {
    // N=0: total no-op (loop never runs); `from` unchanged.
    let body = bt_body(
        &[(1, 1000)],
        &[],
        &[],
        1,
        "    let f: u256 = m.get_or(1, 0);\n    if f == 1000 { return 0 - 212; } else { return 0 - 999; }",
    );
    assert_eq!(neg(&body), 212, "empty airdrop is a no-op");
}

#[test]
fn bt_duplicate_recipient() {
    // recipients [2,2] → credits ACCUMULATE (an alias-blind impl gives r2=20; the live-slot replay gives 30).
    let body = bt_body(
        &[(1, 1000)],
        &[2, 2],
        &[10, 20],
        1,
        "    let f: u256 = m.get_or(1, 0);\n    let r2: u256 = m.get_or(2, 0);\n    if f == 970 { if r2 == 30 { return 0 - 213; } else { return 0 - 999; } } else { return 0 - 999; }",
    );
    assert_eq!(
        neg(&body),
        213,
        "duplicate recipient must ACCUMULATE (10+20=30)"
    );
}

#[test]
fn bt_recipient_eq_from() {
    // recipients [1,2], from=1: leg0 self-leg nets zero (1 stays 1000), leg1 debits → 1=980, 2=20.
    let body = bt_body(
        &[(1, 1000)],
        &[1, 2],
        &[10, 20],
        1,
        "    let f: u256 = m.get_or(1, 0);\n    let r2: u256 = m.get_or(2, 0);\n    if f == 980 { if r2 == 20 { return 0 - 214; } else { return 0 - 999; } } else { return 0 - 999; }",
    );
    assert_eq!(
        neg(&body),
        214,
        "recipient==from self-leg nets zero, then leg1 debits"
    );
}

#[test]
fn bt_all_recipients_eq_from() {
    // recipients [1,1], from=1: every leg self-nets → 1 unchanged (still checked >= each amount).
    let body = bt_body(
        &[(1, 1000)],
        &[1, 1],
        &[10, 20],
        1,
        "    let f: u256 = m.get_or(1, 0);\n    if f == 1000 { return 0 - 215; } else { return 0 - 999; }",
    );
    assert_eq!(
        neg(&body),
        215,
        "all-recipients==from leaves `from` unchanged"
    );
}

#[test]
fn bt_zero_amount_leg() {
    // amounts [30,0]: leg1 (a=0) is SKIPPED → recipient 3 is NEVER materialized (NC-L1).
    let body = bt_body(
        &[(1, 1000)],
        &[2, 3],
        &[30, 0],
        1,
        "    let f: u256 = m.get_or(1, 0);\n    let r2: u256 = m.get_or(2, 0);\n    let c3: bool = m.contains_key(3);\n    if f == 970 { if r2 == 30 { if c3 { return 0 - 999; } else { return 0 - 216; } } else { return 0 - 999; } } else { return 0 - 999; }",
    );
    assert_eq!(
        neg(&body),
        216,
        "zero-amount leg materializes no slot (NC-L1)"
    );
}

#[test]
fn bt_amounts_longer_ignored() {
    // amounts longer than recipients: extra amounts are ignored (loop bound = recipients.len()).
    let body = bt_body(
        &[(1, 1000)],
        &[2],
        &[10, 20],
        1,
        "    let f: u256 = m.get_or(1, 0);\n    let r2: u256 = m.get_or(2, 0);\n    if f == 990 { if r2 == 10 { return 0 - 217; } else { return 0 - 999; } } else { return 0 - 999; }",
    );
    assert_eq!(
        neg(&body),
        217,
        "extra amounts (amounts.len > recipients.len) are ignored"
    );
}

#[test]
fn bt_clone_isolation() {
    // The atomicity FOUNDATION: deep_copy is INDEPENDENT — mutating the clone leaves self untouched.
    let mut body = bt_seed(&[(1, 100), (2, 200)]);
    body.push_str("    let mut c: BoundedMap_u256_u256_64 = m.deep_copy();\n");
    body.push_str("    let _x: i64 = c.insert(1, 555);\n");
    body.push_str("    let _y: i64 = c.insert(3, 777);\n");
    body.push_str("    let m1: u256 = m.get_or(1, 0);\n    let m3: u256 = m.get_or(3, 0);\n    let c1: u256 = c.get_or(1, 0);\n");
    body.push_str("    if m1 == 100 { if m3 == 0 { if c1 == 555 { return 0 - 218; } else { return 0 - 999; } } else { return 0 - 999; } } else { return 0 - 999; }");
    assert_eq!(
        neg(&body),
        218,
        "deep_copy must be independent (mutating the clone leaves self intact)"
    );
}

#[test]
fn bt_capacity_boundary_ok() {
    // 63 existing keys + 1 NEW recipient = exactly 64 (the boundary) → succeeds.
    let mut body = fill_u256(62); // keys 0..61 (62 keys)
    body.push_str("    let _from: i64 = m.insert(100, 1000);\n"); // 63 keys
    body.push_str(&mkvec("recips", &[200]));
    body.push_str(&mkvec("amts", &[10]));
    body.push_str("    let _ok: bool = m.batch_transfer(100, recips, amts);\n");
    body.push_str("    let n: i64 = m.len();\n    let f: u256 = m.get_or(100, 0);\n    let r: u256 = m.get_or(200, 0);\n    if n == 64 { if f == 990 { if r == 10 { return 0 - 219; } else { return 0 - 999; } } else { return 0 - 999; } } else { return 0 - 999; }");
    assert_eq!(
        neg(&body),
        219,
        "airdrop filling the map to exactly 64 keys succeeds"
    );
}

#[test]
fn bt_underflow_total_traps() {
    // from=50, amounts [30,30] (total 60 > 50): leg1 underflows (from=20 < 30) → trap.
    let body = bt_body(&[(1, 50)], &[2, 3], &[30, 30], 1, "    return 0 - 1;\n");
    assert!(
        body_traps(&body),
        "airdrop overrunning the balance must trap"
    );
}

#[test]
fn bt_underflow_self_leg_traps() {
    // from=5, recipients [2, 1(self)], amounts [3, 4]: non-self total (3) <= 5, yet leg1 (self) sees
    // from=2 < 4 → underflow trap. Proves PER-LEG discipline (a sum-shortcut would wrongly succeed).
    let body = bt_body(&[(1, 5)], &[2, 1], &[3, 4], 1, "    return 0 - 1;\n");
    assert!(
        body_traps(&body),
        "the self-leg underflow (sum-shortcut counterexample) must trap"
    );
}

#[test]
fn bt_credit_overflow_traps() {
    // recipient 2 holds u256::MAX; crediting +1 overflows → the checked u256 `+` traps.
    let body = format!(
        "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 1000);\n    let _b: i64 = m.insert(2, {U256_MAX});\n{}{}    let _ok: bool = m.batch_transfer(1, recips, amts);\n    return 0 - 1;\n",
        mkvec("recips", &[2]),
        mkvec("amts", &[1])
    );
    assert!(body_traps(&body), "credit overflow (MAX + 1) must trap");
}

#[test]
fn bt_capacity_new_key_traps() {
    // Map FULL at 64 keys; an airdrop to a NEW recipient (the 65th key) traps in Pass-1 (self untouched).
    let mut body = fill_u256(63); // keys 0..62 (63 keys)
    body.push_str("    let _from: i64 = m.insert(100, 1000);\n"); // 64 keys, FULL
    body.push_str(&mkvec("recips", &[200]));
    body.push_str(&mkvec("amts", &[10]));
    body.push_str("    let _ok: bool = m.batch_transfer(100, recips, amts);\n    return 0 - 1;\n");
    assert!(
        body_traps(&body),
        "airdrop to a NEW key at capacity 64 traps (65th key)"
    );
}

#[test]
fn bt_length_mismatch_traps() {
    // amounts SHORTER than recipients → the length guard traps up front.
    let body = bt_body(
        &[(1, 1000)],
        &[2, 3, 4],
        &[10, 20],
        1,
        "    return 0 - 1;\n",
    );
    assert!(
        body_traps(&body),
        "amounts shorter than recipients must trap (length guard)"
    );
}

#[test]
fn bt_atomicity_late_trap() {
    // A LATE leg traps (leg0 ok, leg1 overflows): the trap fires in Pass-1 (on the clone), so self is
    // never blitted. Directly observable here only as a fail-closed trap; the "self untouched" is
    // guaranteed structurally (Pass-1 on the discarded clone) + proven by bt_clone_isolation.
    let body = format!(
        "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let _a: i64 = m.insert(1, 1000);\n    let _b: i64 = m.insert(3, {U256_MAX});\n{}{}    let _ok: bool = m.batch_transfer(1, recips, amts);\n    return 0 - 1;\n",
        mkvec("recips", &[2, 3]),
        mkvec("amts", &[30, 1])
    );
    assert!(
        body_traps(&body),
        "a late-leg overflow must trap (fail-closed, no partial commit)"
    );
}

#[test]
fn bt_max_atomic_at_recommended_budget() {
    // MI-FUEL (Nigel: "guarantee it"): a MAX (N=60) airdrop must complete ATOMICALLY at the RECOMMENDED
    // fuel budget (not the 1e9 override) with the INJECTED stdlib — i.e. no fuel-trap mid-commit. If it
    // fuel-traps, `neg_at_recommended` panics naming the budget.
    let recips: Vec<i64> = (2..62).collect(); // 60 recipients
    let amts: Vec<i64> = vec![1; 60];
    let body = bt_body(
        &[(1, 1000)],
        &recips,
        &amts,
        1,
        "    let f: u256 = m.get_or(1, 0);\n    let last: u256 = m.get_or(61, 0);\n    if f == 940 { if last == 1 { return 0 - 226; } else { return 0 - 999; } } else { return 0 - 999; }",
    );
    assert_eq!(
        neg_at_recommended(&body),
        226,
        "max-N airdrop must complete atomically at the recommended budget"
    );
}

// ── Property-based airdrop oracle: random scenario vs a Rust reference model ──
// The `bt_*` cases hand-enumerate the aliasing/trap classes; this proptest EXHAUSTS
// the combinatorial (N × collision × underflow) space the enumeration cannot. A
// random (seed, from, legs) airdrop is simulated by a faithful Rust reference
// (live-slot sequential replay — the credit reads the JUST-debited slot, so a
// `recipient == from` self-leg and duplicate recipients are modeled exactly), then
// run through the REAL `batch_transfer`; the final 6-key state (or the underflow
// trap) must match. This is the primitive-correctness oracle under fuzz — the layer
// where the airdrop's real semantics (aliasing over variable N) live (the frontend
// fold is a fixed `batch_transfer(from, recips, amts)` emit, covered by the goldens).

#[derive(Debug, PartialEq)]
enum Out {
    Sentinel(i64),
    OtherTrap,
    Returned,
}

/// Compile+run `body`; classify the outcome. A `return 0 - K` arrives as a Sentinel(K)
/// trap; a genuine stdlib `trap()` (underflow/overflow/capacity) is `OtherTrap`; a plain
/// return is `Returned`. Runs at the generous budget — this pins CORRECTNESS, not fuel
/// (MI-FUEL is pinned separately by `bt_max_atomic_at_recommended_budget`).
fn run_outcome(body: &str) -> Out {
    let result = compile_tool(&tool(body)).expect("tool should compile");
    match execute_ephemeral(
        &result.wasm,
        b"",
        result.fuel_budget.max(1_000_000_000),
        &IoGrants::none(),
    ) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            if let Some(i) = message.find(p) {
                let s = i + p.len();
                let e = message[s..].find(')').unwrap();
                Out::Sentinel(message[s..s + e].parse().unwrap())
            } else {
                Out::OtherTrap
            }
        }
        Ok(_) => Out::Returned,
        Err(_) => Out::OtherTrap,
    }
}

proptest! {
    // Each case compiles + runs a wasm tool; keep the count modest for wall-clock.
    #![proptest_config(ProptestConfig { cases: 40, .. ProptestConfig::default() })]

    /// Keys 1..=4 are seeded (0..=300); recipients range 1..=6 (so keys 5/6 are
    /// newly-materialized, and dups + `recipient == from` collisions occur), amounts
    /// 0..=100, 0..=6 legs. amounts.len() == recipients.len() (the mismatch-trap is
    /// pinned by `bt_length_mismatch_traps`). No overflow (values stay < 2^13) and no
    /// capacity trap (≤ 6 distinct keys) by construction, so the reference traps IFF a
    /// leg underflows — the one nondeterministic axis the fuzz drives.
    #[test]
    fn prop_airdrop_matches_reference(
        seed in prop::collection::vec(0i64..=300i64, 4),
        from in 1i64..=4i64,
        legs in prop::collection::vec((1i64..=6i64, 0i64..=100i64), 0..=6usize),
    ) {
        let recips: Vec<i64> = legs.iter().map(|(r, _)| *r).collect();
        let amts: Vec<i64> = legs.iter().map(|(_, a)| *a).collect();

        // Reference: faithful live-slot sequential replay.
        let mut bal: HashMap<i64, i64> = (1..=4).map(|k| (k, seed[(k - 1) as usize])).collect();
        let mut trap = false;
        for i in 0..recips.len() {
            let a = amts[i];
            if a == 0 {
                continue;
            }
            let fb = *bal.get(&from).unwrap_or(&0);
            if fb < a {
                trap = true;
                break;
            }
            bal.insert(from, fb - a);
            let r = recips[i];
            let rb = *bal.get(&r).unwrap_or(&0); // reads the just-debited slot if r == from
            bal.insert(r, rb + a);
        }

        let seed_pairs: Vec<(i64, i64)> =
            (1..=4).map(|k| (k, seed[(k - 1) as usize])).collect();

        if trap {
            // A leg underflows ⇒ the whole airdrop must trap in Pass-1 (on the clone),
            // self untouched. The tail (`return 0 - 55`) must be UNREACHABLE — if the
            // primitive wrongly succeeds, it fires and we see Sentinel(55) ≠ OtherTrap.
            let body = bt_body(&seed_pairs, &recips, &amts, from, "    return 0 - 55;\n");
            prop_assert_eq!(
                run_outcome(&body),
                Out::OtherTrap,
                "reference underflow-traps; primitive must trap before the tail. from={} recips={:?} amts={:?} seed={:?}",
                from, recips, amts, seed
            );
        } else {
            // No underflow ⇒ the final 6-key state must equal the reference EXACTLY.
            let mut tail = String::new();
            for k in 1..=6 {
                tail.push_str(&format!("    let b{k}: u256 = m.get_or({k}, 0);\n"));
            }
            let mut chk = String::from("return 0 - 77;");
            for k in (1..=6).rev() {
                let e = *bal.get(&k).unwrap_or(&0);
                chk = format!("if b{k} == {e} {{ {chk} }} else {{ return 0 - {k}00; }}");
            }
            tail.push_str("    ");
            tail.push_str(&chk);
            tail.push('\n');
            let body = bt_body(&seed_pairs, &recips, &amts, from, &tail);
            let expect: Vec<i64> = (1..=6).map(|k| *bal.get(&k).unwrap_or(&0)).collect();
            prop_assert_eq!(
                run_outcome(&body),
                Out::Sentinel(77),
                "final-state mismatch. from={} recips={:?} amts={:?} seed={:?} expected(keys 1..6)={:?}",
                from, recips, amts, seed, expect
            );
        }
    }
}
