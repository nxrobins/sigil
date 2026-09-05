//! Runtime tests for the BOUNDED TWO-KEY `(u256,u256)`→`u256` map
//! (`BoundedMap2_u256_u256_u256_64`), the Solidity-frontend
//! `mapping(address => mapping(address => uint256))` (ERC20 `allowance`) target
//! (SOL-ERC20 M0). Mirrors the `bounded_map_u256.rs` harness: `neg` decodes a
//! `return 0 - K` sentinel; `body_traps` detects a genuine trap. The map type is
//! AMBIENT-INJECTED by its `BoundedMap2_u256_u256_u256_*` trigger (no inline defs).
//!
//! Headline properties: a two-key get returns the right value; key identity is the
//! PAIR (same k1 + different k2 is a distinct entry); the 65th distinct pair traps
//! (never silent-drops); and `transfer_from` (the ERC20 `transferFrom` target) is
//! atomic ACROSS the allowance map and the balances map — all checks before any
//! write, allowance decremented by exactly `amount`, conserving Σbalances.

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

/// A fresh two-key map with `n` distinct PAIRS (k1=i, k2=i, val=i*100).
fn fill2(n: i64) -> String {
    let mut s = String::from(
        "    let mut m: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n",
    );
    for i in 0..n {
        s.push_str(&format!(
            "    let _r{i}: i64 = m.insert({}, {}, {});\n",
            i,
            i,
            i * 100
        ));
    }
    s
}

// ───────────────────────────── map core ─────────────────────────────

#[test]
fn m2_insert_get_roundtrip() {
    // insert((7,8),42); get((7,8)) is Some(42).
    assert_eq!(
        neg(
            "    let mut m: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 8, 42);\n    match m.get(7, 8) { Some(v) => { if v == 42 { return 0 - 1; } else { return 0 - 2; } }, None => { return 0 - 9; }, }"
        ),
        1
    );
}

#[test]
fn m2_same_k1_diff_k2_is_distinct() {
    // (7,8)=42 and (7,9)=99 are DISTINCT entries (the key is the PAIR).
    assert_eq!(
        neg(
            "    let mut m: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 8, 42);\n    let _b: i64 = m.insert(7, 9, 99);\n    let x: u256 = m.get_or(7, 8, 0);\n    let y: u256 = m.get_or(7, 9, 0);\n    if x == 42 { if y == 99 { if m.len() == 2 { return 0 - 7; } else { return 0 - 3; } } else { return 0 - 2; } } else { return 0 - 1; }"
        ),
        7
    );
}

#[test]
fn m2_partial_key_miss_is_default() {
    // (7,8) present; get_or((7,9)) and get_or((6,8)) both miss → default. A
    // partial key match (only k1 OR only k2) must NOT hit.
    assert_eq!(
        neg(
            "    let mut m: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 8, 42);\n    let p: u256 = m.get_or(7, 9, 77);\n    let q: u256 = m.get_or(6, 8, 88);\n    if p == 77 { if q == 88 { return 0 - 5; } else { return 0 - 2; } } else { return 0 - 1; }"
        ),
        5
    );
}

#[test]
fn m2_overwrite_same_pair_not_append() {
    assert_eq!(
        neg(
            "    let mut m: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 8, 1);\n    let _b: i64 = m.insert(7, 8, 5);\n    let r: u256 = m.get_or(7, 8, 0);\n    if r == 5 { if m.len() == 1 { return 0 - 1; } else { return 0 - 3; } } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn m2_contains_key_pair() {
    assert_eq!(
        neg(
            "    let mut m: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 8, 42);\n    if m.contains_key(7, 8) { if m.contains_key(7, 9) { return 0 - 3; } else { return 0 - 1; } } else { return 0 - 2; }"
        ),
        1
    );
}

// ──────────────── reserve2 (the SOL-MULTIMAP ≥2-map reservation) ────────────────

#[test]
fn rv2_room_available_is_noop() {
    // Non-full map, reserve2 a NEW pair → no trap; commits NOTHING (len stays 1, pair not created).
    assert_eq!(
        neg(
            "    let mut m: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _a: i64 = m.insert(7, 8, 42);\n    let ok: bool = m.reserve2(9, 9);\n    if ok { if m.len() == 1 { if m.contains_key(9, 9) { return 0 - 3; } else { return 0 - 1; } } else { return 0 - 2; } } else { return 0 - 4; }"
        ),
        1
    );
}

#[test]
fn rv2_full_existing_pair_is_noop() {
    // Full map (64 pairs), reserve2 an EXISTING pair (0,0) → no trap. len stays 64.
    let body = format!(
        "{}    let ok: bool = m.reserve2(0, 0);\n    if ok {{ return 0 - m.len(); }} else {{ return 0 - 1; }}",
        fill2(64)
    );
    assert_eq!(neg(&body), 64);
}

#[test]
fn rv2_full_new_pair_traps() {
    // Full map (64 pairs), reserve2 a NEW pair → traps (surfaces the would-be insert trap up front).
    let body = format!(
        "{}    let _ok: bool = m.reserve2(9999, 9999);\n    return 0 - 1;",
        fill2(64)
    );
    assert!(
        body_traps(&body),
        "reserve2 of a NEW pair on a full map must trap"
    );
}

#[test]
fn m2_capacity_exact_and_full() {
    let body = format!(
        "{}    if m.is_full() {{ return 0 - (m.len() * 100 + m.capacity()); }} else {{ return 0 - 1; }}",
        fill2(64)
    );
    assert_eq!(neg(&body), 6464);
}

#[test]
fn m2_full_insert_new_pair_traps() {
    // 64 distinct pairs, insert a 65th NEW pair → backing force-trap (never silent).
    let body = format!(
        "{}    let _o: i64 = m.insert(99999, 1, 1);\n    return 0 - 1;",
        fill2(64)
    );
    assert!(body_traps(&body), "full + insert NEW pair must trap");
}

#[test]
fn m2_full_overwrite_existing_pair_ok() {
    // 64 full, overwrite an EXISTING pair (0,0) → clean, len stays 64.
    let body = format!(
        "{}    let _o: i64 = m.insert(0, 0, 12345);\n    return 0 - m.len();",
        fill2(64)
    );
    assert_eq!(neg(&body), 64);
}

// ─────────────────────── transfer_from (the ERC20 target) ───────────────────────

/// Standalone two-map fixture: balances + allowance, run `transfer_from`, then
/// decode. `bal[owner]=bo`, `allowance[owner][spender]=al`.
fn tf_setup(bo: i64, al: i64) -> String {
    format!(
        "    let mut bal: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let mut alw: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _b: i64 = bal.insert(1, {bo});\n    let _a: i64 = alw.insert(1, 2, {al});\n"
    )
}

#[test]
fn tf_basic_spend_and_move() {
    // bal[1]=100, allowance[1][2]=50. spender 2 moves 30 from owner 1 to 3.
    // → bal[1]=70, bal[3]=30, allowance[1][2]=20.
    let body = format!(
        "{}    let _ok: bool = alw.transfer_from(bal, 1, 2, 3, 30);\n    let f: u256 = bal.get_or(1, 0);\n    let t: u256 = bal.get_or(3, 0);\n    let a: u256 = alw.get_or(1, 2, 0);\n    if f == 70 {{ if t == 30 {{ if a == 20 {{ return 0 - 7; }} else {{ return 0 - 4; }} }} else {{ return 0 - 3; }} }} else {{ return 0 - 2; }}",
        tf_setup(100, 50)
    );
    assert_eq!(neg(&body), 7);
}

#[test]
fn tf_conserves_total_balance() {
    // Σbalances before == after (100 + 0 = 70 + 30). Decode f*1000 + t.
    let body = format!(
        "{}    let _ok: bool = alw.transfer_from(bal, 1, 2, 3, 30);\n    let f: u256 = bal.get_or(1, 0);\n    let t: u256 = bal.get_or(3, 0);\n    if f + t == 100 {{ return 0 - 100; }} else {{ return 0 - 1; }}",
        tf_setup(100, 50)
    );
    assert_eq!(neg(&body), 100);
}

#[test]
fn tf_allowance_exact_drains_to_zero() {
    // allowance == amount → decremented to exactly 0.
    let body = format!(
        "{}    let _ok: bool = alw.transfer_from(bal, 1, 2, 3, 50);\n    let a: u256 = alw.get_or(1, 2, 0);\n    if a == 0 {{ return 0 - 9; }} else {{ return 0 - 1; }}",
        tf_setup(100, 50)
    );
    assert_eq!(neg(&body), 9);
}

#[test]
fn tf_insufficient_allowance_traps() {
    // allowance 10 < amount 50 → traps BEFORE any write.
    let body = format!(
        "{}    let _ok: bool = alw.transfer_from(bal, 1, 2, 3, 50);\n    return 0 - 1;",
        tf_setup(100, 10)
    );
    assert!(body_traps(&body), "insufficient allowance must trap");
}

#[test]
fn tf_insufficient_balance_traps() {
    // allowance 100 ok, but bal[1]=10 < amount 50 → the balance move traps. The
    // allowance write is AFTER the balance move, so no allowance is spent (atomicity).
    let body = format!(
        "{}    let _ok: bool = alw.transfer_from(bal, 1, 2, 3, 50);\n    return 0 - 1;",
        tf_setup(10, 100)
    );
    assert!(body_traps(&body), "insufficient balance must trap");
}

#[test]
fn tf_self_transfer_owner_to_owner_decrements_allowance() {
    // to == owner: balance net-zero (stays 100), allowance still decremented by 30.
    let body = format!(
        "{}    let _ok: bool = alw.transfer_from(bal, 1, 2, 1, 30);\n    let f: u256 = bal.get_or(1, 0);\n    let a: u256 = alw.get_or(1, 2, 0);\n    if f == 100 {{ if a == 20 {{ return 0 - 6; }} else {{ return 0 - 2; }} }} else {{ return 0 - 1; }}",
        tf_setup(100, 50)
    );
    assert_eq!(neg(&body), 6);
}

#[test]
fn tf_zero_amount_noop_balance() {
    // amount 0: balances unchanged, allowance entry written as-is (still 50).
    let body = format!(
        "{}    let _ok: bool = alw.transfer_from(bal, 1, 2, 3, 0);\n    let f: u256 = bal.get_or(1, 0);\n    let a: u256 = alw.get_or(1, 2, 0);\n    if f == 100 {{ if a == 50 {{ return 0 - 8; }} else {{ return 0 - 2; }} }} else {{ return 0 - 1; }}",
        tf_setup(100, 50)
    );
    assert_eq!(neg(&body), 8);
}

#[test]
fn tf_balances_full_new_recipient_traps() {
    // balances map full (64 keys), allowance ok, `to` is a NEW balances key → the
    // balance move's capacity reservation traps; no allowance spent (write is later).
    let mut s = String::from(
        "    let mut bal: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let mut alw: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n",
    );
    for i in 0..64 {
        s.push_str(&format!(
            "    let _b{i}: i64 = bal.insert({}, {});\n",
            i,
            (i + 1) * 10
        ));
    }
    s.push_str("    let _a: i64 = alw.insert(0, 2, 100);\n");
    // owner 0 (balance 10), spender 2, to 99999 (NEW key) → balances capacity trap.
    s.push_str("    let _ok: bool = alw.transfer_from(bal, 0, 2, 99999, 5);\n    return 0 - 1;");
    assert!(
        body_traps(&s),
        "transfer to a new key on a full balances map must trap"
    );
}

// ── SOL-ZERO-SWEEP: transfer_from amount==0 total no-op (allowance side) ─────────────────────────
// The pre-existing tf_zero_amount_noop_balance covers an EXISTING (owner,spender) pair. A FRESH
// pair at amount 0 must NOT materialize a value-0 allowance slot (Solidity `transferFrom(.,.,0)` is
// a total no-op: _spendAllowance requires 0>=0 and writes the same value back — no storage growth),
// and at 64 pairs it must SUCCEED, not trap on the allowance capacity reservation.

#[test]
fn tf_zero_amount_fresh_pair_no_slot() {
    // No prior allowance for (1,2). transfer_from(bal, 1, 2, 3, 0): balances unchanged, and the
    // allowance pair (1,2) must stay ABSENT (not materialized as 0). len 0.
    let body = "    let mut bal: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let mut alw: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _b: i64 = bal.insert(1, 100);\n    let _ok: bool = alw.transfer_from(bal, 1, 2, 3, 0);\n    let f: u256 = bal.get_or(1, 0);\n    let z: bool = alw.contains_key(1, 2);\n    let n: i64 = alw.len();\n    if z { return 0 - 8; } else { if n == 0 { if f == 100 { return 0 - 100; } else { return 0 - 1; } } else { return 0 - 2; } }";
    assert_eq!(neg(body), 100);
}

#[test]
fn tf_zero_amount_full_alw_fresh_pair_ok() {
    // Allowance map full (64 pairs), a FRESH (owner,spender) at amount 0 must SUCCEED (Solidity
    // grows no storage), not trap on the allowance capacity reservation. Balance owner present.
    let mut s = String::from(
        "    let mut bal: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let mut alw: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _b: i64 = bal.insert(7, 100);\n",
    );
    for i in 0..64 {
        s.push_str(&format!(
            "    let _a{i}: i64 = alw.insert({}, {}, 50);\n",
            i, i
        ));
    }
    // owner 7 (present in bal), spender 999 (fresh pair (7,999)), to 8, amount 0.
    s.push_str("    let _ok: bool = alw.transfer_from(bal, 7, 999, 8, 0);\n    let z: bool = alw.contains_key(7, 999);\n    if z { return 0 - 8; } else { return 0 - 77; }");
    assert_eq!(neg(&s), 77);
}

#[test]
fn tf_zero_amount_existing_pair_unchanged() {
    // Regression (the pre-existing case, restated): amount 0 on an EXISTING (1,2)=50 pair leaves
    // the allowance at 50 and grows no storage.
    let body = format!(
        "{}    let _ok: bool = alw.transfer_from(bal, 1, 2, 3, 0);\n    let a: u256 = alw.get_or(1, 2, 0);\n    let n: i64 = alw.len();\n    if n == 1 {{ if a == 50 {{ return 0 - 50; }} else {{ return 0 - 1; }} }} else {{ return 0 - 2; }}",
        tf_setup(100, 50)
    );
    assert_eq!(neg(&body), 50);
}

// ── SOL-XFILE PR6/AC-2: erc20_transfer_from — OZ 5.x transferFrom (infinite-allowance + zero-guards) ──
// The correctness oracle for the composed primitive: like `transfer_from` but (a) a zero from/to
// TRAPS (never mint/burn) and (b) an allowance == 2^256-1 is INFINITE (skips the decrement). All
// balances/allowance asserts are exact; the trap paths run all checks before any write.

const U256_MAX: &str =
    "115792089237316195423570985008687907853269984665640564039457584007913129639935";

#[test]
fn ec_finite_spend_and_move() {
    // bal[1]=100, allowance[1][2]=50. spender 2 moves 30 (owner 1 → 3), spends 30 of allowance.
    let body = format!(
        "{}    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 3, 30);\n    let f: u256 = bal.get_or(1, 0);\n    let t: u256 = bal.get_or(3, 0);\n    let a: u256 = alw.get_or(1, 2, 0);\n    if f == 70 {{ if t == 30 {{ if a == 20 {{ return 0 - 7; }} else {{ return 0 - 4; }} }} else {{ return 0 - 3; }} }} else {{ return 0 - 2; }}",
        tf_setup(100, 50)
    );
    assert_eq!(neg(&body), 7);
}

#[test]
fn ec_infinite_allowance_not_spent() {
    // allowance[1][2] == MAX → the balance moves but the allowance is UNCHANGED (infinite approval).
    let body = format!(
        "    let mut bal: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let mut alw: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _b: i64 = bal.insert(1, 100);\n    let _a: i64 = alw.insert(1, 2, {U256_MAX});\n    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 3, 30);\n    let f: u256 = bal.get_or(1, 0);\n    let t: u256 = bal.get_or(3, 0);\n    let a: u256 = alw.get_or(1, 2, 0);\n    if f == 70 {{ if t == 30 {{ if a == {U256_MAX} {{ return 0 - 9; }} else {{ return 0 - 4; }} }} else {{ return 0 - 3; }} }} else {{ return 0 - 2; }}"
    );
    assert_eq!(neg(&body), 9);
}

#[test]
fn ec_max_minus_one_is_finite() {
    // The boundary: allowance == MAX-1 (= 2^256-2) is FINITE — the balance moves AND the allowance IS
    // decremented (to MAX-1-30). Pins the shift-built sentinel EXACTLY: this proves max_u256 > MAX-1,
    // and `ec_infinite_allowance_not_spent` proves max_u256 <= MAX, so together max_u256 == 2^256-1.
    let max_m1 = "115792089237316195423570985008687907853269984665640564039457584007913129639934";
    let max_m1_m30 =
        "115792089237316195423570985008687907853269984665640564039457584007913129639904";
    let body = format!(
        "    let mut bal: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let mut alw: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _b: i64 = bal.insert(1, 100);\n    let _a: i64 = alw.insert(1, 2, {max_m1});\n    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 3, 30);\n    let f: u256 = bal.get_or(1, 0);\n    let a: u256 = alw.get_or(1, 2, 0);\n    if f == 70 {{ if a == {max_m1_m30} {{ return 0 - 11; }} else {{ return 0 - 4; }} }} else {{ return 0 - 2; }}"
    );
    assert_eq!(neg(&body), 11);
}

#[test]
fn ec_from_zero_traps() {
    // from == 0 → transferFrom reverts (never a mint), before any read/write.
    let body = format!(
        "{}    let _ok: bool = alw.erc20_transfer_from(bal, 0, 2, 3, 30);\n    return 0 - 1;",
        tf_setup(100, 50)
    );
    assert!(body_traps(&body));
}

#[test]
fn ec_to_zero_traps() {
    // to == 0 → transferFrom reverts (never a burn), before any read/write.
    let body = format!(
        "{}    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 0, 30);\n    return 0 - 1;",
        tf_setup(100, 50)
    );
    assert!(body_traps(&body));
}

#[test]
fn ec_amount_zero_noop_existing_pair() {
    // amount==0: balances + allowance UNCHANGED, no new slots (NC-L1 total no-op).
    let body = format!(
        "{}    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 3, 0);\n    let f: u256 = bal.get_or(1, 0);\n    let a: u256 = alw.get_or(1, 2, 0);\n    let n: i64 = alw.len();\n    if f == 100 {{ if a == 50 {{ if n == 1 {{ return 0 - 8; }} else {{ return 0 - 5; }} }} else {{ return 0 - 2; }} }} else {{ return 0 - 1; }}",
        tf_setup(100, 50)
    );
    assert_eq!(neg(&body), 8);
}

#[test]
fn ec_amount_zero_fresh_pair_no_slot() {
    // amount==0 on a FRESH (1,2) pair: no allowance slot materialized (bounded-capacity faithfulness).
    let body = "    let mut bal: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let mut alw: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _b: i64 = bal.insert(1, 100);\n    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 3, 0);\n    let z: bool = alw.contains_key(1, 2);\n    let n: i64 = alw.len();\n    if z { return 0 - 8; } else { if n == 0 { return 0 - 100; } else { return 0 - 2; } }";
    assert_eq!(neg(body), 100);
}

#[test]
fn ec_insufficient_allowance_traps() {
    // allowance 10 < amount 50 (finite) → traps BEFORE any write.
    let body = format!(
        "{}    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 3, 50);\n    return 0 - 1;",
        tf_setup(100, 10)
    );
    assert!(body_traps(&body));
}

#[test]
fn ec_insufficient_balance_traps() {
    // bal 10 < amount 50 (allowance ample) → traps via bal.transfer; no allowance write commits.
    let body = format!(
        "{}    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 3, 50);\n    return 0 - 1;",
        tf_setup(10, 100)
    );
    assert!(body_traps(&body));
}

#[test]
fn ec_self_transfer_spends_allowance() {
    // from == to (self-transfer): balance net-zero (bal[1]=100 stays), allowance STILL spent (50→20).
    let body = format!(
        "{}    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 1, 30);\n    let f: u256 = bal.get_or(1, 0);\n    let a: u256 = alw.get_or(1, 2, 0);\n    if f == 100 {{ if a == 20 {{ return 0 - 6; }} else {{ return 0 - 2; }} }} else {{ return 0 - 1; }}",
        tf_setup(100, 50)
    );
    assert_eq!(neg(&body), 6);
}

#[test]
fn ec_infinite_self_transfer_all_unchanged() {
    // from==to AND allowance==MAX: bal[1] unchanged, allowance stays MAX.
    let body = format!(
        "    let mut bal: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let mut alw: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n    let _b: i64 = bal.insert(1, 100);\n    let _a: i64 = alw.insert(1, 2, {U256_MAX});\n    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 1, 30);\n    let f: u256 = bal.get_or(1, 0);\n    let a: u256 = alw.get_or(1, 2, 0);\n    if f == 100 {{ if a == {U256_MAX} {{ return 0 - 6; }} else {{ return 0 - 2; }} }} else {{ return 0 - 1; }}"
    );
    assert_eq!(neg(&body), 6);
}

#[test]
fn ec_allowance_exact_drains_to_zero() {
    // allowance == amount → decremented to exactly 0.
    let body = format!(
        "{}    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 3, 50);\n    let a: u256 = alw.get_or(1, 2, 0);\n    if a == 0 {{ return 0 - 9; }} else {{ return 0 - 1; }}",
        tf_setup(100, 50)
    );
    assert_eq!(neg(&body), 9);
}

#[test]
fn ec_balances_full_new_recipient_traps() {
    // balances map full (64 keys), allowance ample, `to` is a NEW balances key → the balance move's
    // capacity reservation traps; no allowance spent (the allowance write is later). from non-zero.
    let mut s = String::from(
        "    let mut bal: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n    let mut alw: BoundedMap2_u256_u256_u256_64 = BoundedMap2_u256_u256_u256_64::new();\n",
    );
    for i in 0..64 {
        s.push_str(&format!(
            "    let _b{i}: i64 = bal.insert({}, {});\n",
            i,
            (i + 1) * 10
        ));
    }
    s.push_str("    let _a: i64 = alw.insert(1, 2, 100);\n");
    // owner 1 (balance 20), spender 2, to 99999 (NEW key) → balances capacity trap; from != 0.
    s.push_str(
        "    let _ok: bool = alw.erc20_transfer_from(bal, 1, 2, 99999, 5);\n    return 0 - 1;",
    );
    assert!(
        body_traps(&s),
        "transferFrom to a new key on a full balances map must trap"
    );
}
