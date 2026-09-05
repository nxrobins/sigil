//! BoundedVec — bounded, stack-backed `i64` vectors (COMPLETENESS Phase 2).
//!
//! `BoundedVec_i64_8` is a monomorphized fixed-N record `{ data: [i64; 8], count }`
//! with no `cap Alloc`: the `[i64; 8]` backing is a statically-fuelled bounded
//! region, and overflow is a RUNTIME TRAP (a full `push` writes `self.data[8]`,
//! tripping the array bounds trap) rather than a refinement. The record is
//! construction-SEALED (T258, tested in `bounded_vec_seal.rs`) so its `count`
//! invariant cannot be forged.
//!
//! The tool template carries **NO `! { Alloc }`** — so every test here that
//! compiles + runs is also an ET-2 no-`Alloc` proof for the methods it exercises.
//! (SIGIL has no method chaining, so `Option` results are bound to a `let` before
//! `.unwrap_or` — the same idiom the string tests use.)

mod common;

/// Tool with NO `! { Alloc }` effect (BoundedVec is Alloc-free).
fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

/// Run a `0 - value` tool body and recover `value` from the negative sentinel.
/// Panics on a genuine wasm trap (the sentinel prefix is absent).
use common::run_returning_negative as run_neg;

fn neg(body: &str) -> i64 {
    run_neg(&tool(body))
}

/// True iff `body` GENUINELY traps. The body returns a POSITIVE value, so a clean
/// run is `Ok` and only a real wasm trap is `Err(Trapped)` (a `0 - x` body would
/// itself look "trapped" via the sentinel convention, hiding a missing trap).
fn body_traps(body: &str) -> bool {
    common::tool_traps(&tool(body))
}

/// `v.push(1)..v.push(n)` on a fresh vec of monomorph type `ty`.
fn fill_t(ty: &str, n: i64) -> String {
    let mut s = format!("    let mut v: {ty} = {ty}::new();\n");
    for k in 1..=n {
        s.push_str(&format!("    v.push({k});\n"));
    }
    s
}

/// `v.push(1)..v.push(n)` — fill a fresh `_8` vec with 1..=n (n <= 8).
fn fill(n: i64) -> String {
    fill_t("BoundedVec_i64_8", n)
}

// ── ET-2: the whole API is Alloc-free + round-trips ──────────────────────────

#[test]
fn no_alloc_proof_all_methods() {
    // new/push/get/pop/len/capacity, from a `tool_main` with NO `! { Alloc }`.
    // (is_empty/is_full are exercised Alloc-free by the tests below.)
    let body = "    let mut v: BoundedVec_i64_8 = BoundedVec_i64_8::new();\n\
        \x20   v.push(10);\n\
        \x20   let go: Option<i64> = v.get(0);\n\
        \x20   let g: i64 = go.unwrap_or(0);\n\
        \x20   let ho: Option<i64> = v.pop();\n\
        \x20   let h: i64 = ho.unwrap_or(0);\n\
        \x20   return 0 - (v.len() + v.capacity() + g + h);";
    // after pop: len 0, capacity 8, g=10, h=10 → 28.
    assert_eq!(neg(body), 28);
}

#[test]
fn construct_push_get_roundtrip() {
    let body = format!(
        "{}    let o0: Option<i64> = v.get(0);\n    let o1: Option<i64> = v.get(1);\n    return 0 - (o0.unwrap_or(0) * 1000 + o1.unwrap_or(0) * 10 + v.len());",
        fill(2)
    );
    // get(0)=1, get(1)=2, len=2 → 1*1000 + 2*10 + 2 = 1022.
    assert_eq!(neg(&body), 1022);
}

// ── ET-3 + ET-6: overflow traps; capacity/is_full pin the behavioral N ────────

#[test]
fn fill_to_capacity_is_clean() {
    // Push EXACTLY 8: clean, is_full, len == capacity == 8.
    let body = format!(
        "{}    if v.is_full() {{ return 0 - (v.len() * 100 + v.capacity()); }} else {{ return 0 - 1; }}",
        fill(8)
    );
    assert_eq!(neg(&body), 808); // len 8, capacity 8
}

#[test]
fn overflow_traps_on_ninth_push() {
    // Fill 8, push a 9th → `self.data[8]` trips the backing bounds trap. Rigorous
    // positive-return detector: a clean run (no trap) would be Ok, not Err.
    let body = format!("{}    v.push(99);\n    return v.len() + 1;", fill(8));
    assert!(body_traps(&body), "the 9th push must trap (backing OOB)");
}

#[test]
fn fill_exactly_eight_does_not_trap() {
    // The boundary the other side: 8 pushes are CLEAN (no premature trap).
    let body = format!("{}    return v.len() + 1;", fill(8));
    assert!(!body_traps(&body), "8 pushes must be clean");
}

// ── pop / is_empty / is_full ─────────────────────────────────────────────────

#[test]
fn pop_semantics() {
    let body = format!(
        "{}    let p: Option<i64> = v.pop();\n    return 0 - (p.unwrap_or(0) * 100 + v.len());",
        fill(3)
    );
    // pop → 3 (LIFO), len → 2 → 3*100 + 2 = 302.
    assert_eq!(neg(&body), 302);
}

#[test]
fn pop_empty_is_none() {
    let body = "    let mut v: BoundedVec_i64_8 = BoundedVec_i64_8::new();\n\
        \x20   let p: Option<i64> = v.pop();\n\
        \x20   return 0 - (p.unwrap_or(0 - 7) + 100);";
    // empty pop → None → unwrap_or(-7) → -7; -7 + 100 = 93.
    assert_eq!(neg(body), 93);
}

#[test]
fn is_empty_is_full_flip() {
    // Fresh: empty.
    assert_eq!(
        neg(
            "    let v: BoundedVec_i64_8 = BoundedVec_i64_8::new();\n    if v.is_empty() { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
    // After 1 push: not empty, not full.
    assert_eq!(
        neg(&format!(
            "{}    if v.is_empty() {{ return 0 - 9; }} else {{ if v.is_full() {{ return 0 - 8; }} else {{ return 0 - 5; }} }}",
            fill(1)
        )),
        5
    );
}

// ── ET-7: get is len-bounded — no uninitialized / out-of-range leak ──────────

#[test]
fn get_out_of_range_is_none() {
    // len 2; get(5)/get(-1) → None (clean, not a trap). unwrap_or(-7) decodes None.
    let over = format!(
        "{}    let o: Option<i64> = v.get(5);\n    return 0 - (o.unwrap_or(0 - 7) + 100);",
        fill(2)
    );
    assert_eq!(neg(&over), 93); // -7 + 100
    let under = format!(
        "{}    let o: Option<i64> = v.get(0 - 1);\n    return 0 - (o.unwrap_or(0 - 7) + 100);",
        fill(2)
    );
    assert_eq!(neg(&under), 93);
}

// ── set: LEN-bounded indexed write (the write counterpart of get) ────────────

#[test]
fn set_overwrites_live_cell() {
    // [1,2,3], set(1, 99) → get(1) == 99.
    let body = format!(
        "{}    v.set(1, 99);\n    let o1: Option<i64> = v.get(1);\n    return 0 - o1.unwrap_or(0);",
        fill(3)
    );
    assert_eq!(neg(&body), 99);
}

#[test]
fn set_preserves_other_cells_and_len() {
    // set(1, 99) leaves get(0)==1, get(2)==3, len==3 untouched.
    let body = format!(
        "{}    v.set(1, 99);\n    let o0: Option<i64> = v.get(0);\n    let o2: Option<i64> = v.get(2);\n    return 0 - (o0.unwrap_or(0) * 100 + o2.unwrap_or(0) * 10 + v.len());",
        fill(3)
    );
    // g0=1, g2=3, len=3 → 1*100 + 3*10 + 3 = 133.
    assert_eq!(neg(&body), 133);
}

#[test]
fn set_at_count_traps_len_bounded() {
    // len 2; set(2, _) — index == count is in the [count, 8) capacity tail: WITHIN
    // the 8-cell backing but NOT a live cell. A LEN-bounded set must TRAP (not
    // silently write the tail) — the exact property that separates it from a
    // capacity-bounded write, which would accept index 2 because 2 < 8.
    let body = format!("{}    v.set(2, 99);\n    return v.len() + 1;", fill(2));
    assert!(
        body_traps(&body),
        "set at index==count must trap (LEN-bounded, not CAP)"
    );
}

#[test]
fn set_past_range_traps() {
    let body = format!("{}    v.set(5, 99);\n    return v.len() + 1;", fill(2));
    assert!(body_traps(&body), "set past count must trap");
}

#[test]
fn set_negative_traps() {
    // The array's own `idx >= N` check does NOT catch i<0, so set's explicit
    // `i < 0` guard forces the trap — no negative-offset write past the backing.
    let body = format!("{}    v.set(0 - 1, 99);\n    return v.len() + 1;", fill(2));
    assert!(body_traps(&body), "set with negative index must trap");
}

// ── _64: a second monomorph size — the family scales ─────────────────────────

#[test]
fn bounded_vec_64_capacity_is_64() {
    let body =
        "    let v: BoundedVec_i64_64 = BoundedVec_i64_64::new();\n    return 0 - v.capacity();";
    assert_eq!(neg(body), 64);
}

#[test]
fn bounded_vec_64_push_get_roundtrip() {
    let body = format!(
        "{}    let o0: Option<i64> = v.get(0);\n    let o62: Option<i64> = v.get(62);\n    return 0 - (o0.unwrap_or(0) * 1000 + o62.unwrap_or(0) * 10 + v.len());",
        fill_t("BoundedVec_i64_64", 63)
    );
    // pushed 1..=63: get(0)=1, get(62)=63, len=63 → 1*1000 + 63*10 + 63 = 1693.
    assert_eq!(neg(&body), 1693);
}

#[test]
fn bounded_vec_64_fills_to_64_clean_overflows_at_65() {
    // ET-6: capacity() == 64 must match the BACKING. Fill 64 (clean), 65th traps.
    let full = fill_t("BoundedVec_i64_64", 64);
    assert!(
        !body_traps(&format!("{full}    return v.len() + 1;")),
        "64 pushes into a _64 must be clean"
    );
    assert!(
        body_traps(&format!("{full}    v.push(99);\n    return v.len() + 1;")),
        "the 65th push into a _64 must trap (data[64])"
    );
}

// ── _256: the large monomorph, built with the `[0; 256]` repeat literal ──────

#[test]
fn bounded_vec_256_capacity_is_256() {
    let body =
        "    let v: BoundedVec_i64_256 = BoundedVec_i64_256::new();\n    return 0 - v.capacity();";
    assert_eq!(neg(body), 256);
}

#[test]
fn bounded_vec_256_push_get_roundtrip() {
    let body = format!(
        "{}    let o0: Option<i64> = v.get(0);\n    let o4: Option<i64> = v.get(4);\n    return 0 - (o0.unwrap_or(0) * 100 + o4.unwrap_or(0) * 10 + v.len());",
        fill_t("BoundedVec_i64_256", 5)
    );
    // 1..=5: get(0)=1, get(4)=5, len=5 → 1*100 + 5*10 + 5 = 155.
    assert_eq!(neg(&body), 155);
}

#[test]
fn bounded_vec_256_fills_to_256_clean_overflows_at_257() {
    // ET-6 at the large size: the 256-cell backing fills clean and traps on 257 —
    // the direct proof that capacity()==256 matches the `[0; 256]` backing, with no
    // drift between the constant and the array length.
    let full = fill_t("BoundedVec_i64_256", 256);
    assert!(
        !body_traps(&format!("{full}    return v.len() + 1;")),
        "256 pushes into a _256 must be clean"
    );
    assert!(
        body_traps(&format!("{full}    v.push(99);\n    return v.len() + 1;")),
        "the 257th push into a _256 must trap (data[256])"
    );
}
