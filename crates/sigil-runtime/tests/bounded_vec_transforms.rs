//! Completeness Phase 2 — BoundedVec_i64 functional transforms (Rung A).
//!
//! Eager, i64-only, **Alloc-free** adapters/terminals on the sealed bounded family:
//! `map`/`filter`/`filter_map`/`take` return a FRESH `BoundedVec_i64_N`; `sum`/`fold`/
//! `any`/`all`/`find` fold to a scalar/bool/Option. The harness `tool_main` carries
//! NO `! { Alloc }`, so the WHOLE suite is the ET-2 Alloc-free proof (any allocating
//! transform would be a compile error here). Values via the negative-sentinel decode.
//! Test data is non-zero + distinct so an `unwrap_or(0)`-masked over-read (NC-P2-4)
//! would surface as a wrong sum. map/filter/take are covered on ALL THREE sizes with a
//! >8-element case (NC-P2-2: a size-constant transposition would trap or mis-len).

mod common;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    common::run_returning_negative_with_min_fuel(&tool(body), 1_000_000_000)
}

/// Build a `BoundedVec_i64_<ty>` holding 1..=n.
fn fill(ty: &str, n: i64) -> String {
    let mut s = format!("    let mut v: BoundedVec_i64_{ty} = BoundedVec_i64_{ty}::new();\n");
    for i in 1..=n {
        s.push_str(&format!("    let _p{i}: i64 = v.push({i});\n"));
    }
    s
}

// ───────────────────────── map / filter / filter_map ─────────────────────────

// map preserves length AND order. [1,2,3] *2 → [2,4,6]: get(0)=2, get(2)=6, len=3
// → 2*1000 + 6*10 + 3 = 2063.
#[test]
fn map_len_and_order() {
    let body = format!(
        "{}    let m: BoundedVec_i64_8 = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n    let ao: Option<i64> = m.get(0);\n    let a: i64 = ao.unwrap_or(0);\n    let co: Option<i64> = m.get(2);\n    let c: i64 = co.unwrap_or(0);\n    return 0 - (a * 1000 + c * 10 + m.len());",
        fill("8", 3)
    );
    assert_eq!(neg(&body), 2063);
}

// filter keeps only-passing, in order — asymmetric predicate (odd) over [1..5] → [1,3,5]:
// get(0)=1, get(2)=5, len=3 → 1053.
#[test]
fn filter_asymmetric_in_order() {
    let body = format!(
        "{}    let f: BoundedVec_i64_8 = v.filter(fn(x: i64) -> bool {{ let r: i64 = x - (x / 2) * 2; return r == 1; }});\n    let ao: Option<i64> = f.get(0);\n    let a: i64 = ao.unwrap_or(0);\n    let co: Option<i64> = f.get(2);\n    let c: i64 = co.unwrap_or(0);\n    return 0 - (a * 1000 + c * 10 + f.len());",
        fill("8", 5)
    );
    assert_eq!(neg(&body), 1053);
}

// filter_map drops None, keeps+unwraps Some. Even→Some(x*10), odd→None over [1..4]
// → [20,40]: sum 60, len 2 → 60*10 + 2 = 602.
#[test]
fn filter_map_drops_none() {
    let body = format!(
        "{}    let f: BoundedVec_i64_8 = v.filter_map(fn(x: i64) -> Option<i64> {{ let r: i64 = x - (x / 2) * 2; if r == 0 {{ return Some(x * 10); }} else {{ return None; }} }});\n    return 0 - (f.sum() * 10 + f.len());",
        fill("8", 4)
    );
    assert_eq!(neg(&body), 602);
}

// ───────────────────────── terminals ─────────────────────────

#[test]
fn sum_terminal() {
    assert_eq!(neg(&format!("{}    return 0 - v.sum();", fill("8", 4))), 10);
}

// fold left-to-right, seeded — non-commutative subtraction: 100-1-2-3 = 94.
#[test]
fn fold_left_seeded() {
    let body = format!(
        "{}    return 0 - v.fold(100, fn(a: i64, b: i64) -> i64 {{ return a - b; }});",
        fill("8", 3)
    );
    assert_eq!(neg(&body), 94);
}

#[test]
fn any_hit_miss() {
    let hit = format!(
        "{}    if v.any(fn(x: i64) -> bool {{ return x == 3; }}) {{ return 0 - 1; }} else {{ return 0 - 2; }}",
        fill("8", 4)
    );
    let miss = format!(
        "{}    if v.any(fn(x: i64) -> bool {{ return x == 9; }}) {{ return 0 - 1; }} else {{ return 0 - 2; }}",
        fill("8", 4)
    );
    assert_eq!(neg(&hit), 1);
    assert_eq!(neg(&miss), 2);
}

#[test]
fn all_true_false() {
    let t = format!(
        "{}    if v.all(fn(x: i64) -> bool {{ return x > 0; }}) {{ return 0 - 1; }} else {{ return 0 - 2; }}",
        fill("8", 4)
    );
    let f = format!(
        "{}    if v.all(fn(x: i64) -> bool {{ return x > 2; }}) {{ return 0 - 1; }} else {{ return 0 - 2; }}",
        fill("8", 4)
    );
    assert_eq!(neg(&t), 1);
    assert_eq!(neg(&f), 2);
}

#[test]
fn find_hit_miss() {
    let hit = format!(
        "{}    let o: Option<i64> = v.find(fn(x: i64) -> bool {{ return x > 2; }});\n    return 0 - o.unwrap_or(0);",
        fill("8", 4)
    );
    let miss = format!(
        "{}    let o: Option<i64> = v.find(fn(x: i64) -> bool {{ return x > 9; }});\n    return 0 - o.unwrap_or(777);",
        fill("8", 4)
    );
    assert_eq!(neg(&hit), 3);
    assert_eq!(neg(&miss), 777);
}

// ───────────────────────── take (min clamp) ─────────────────────────

// take yields min(n, count): n<count, n==count, n>count, n==0 — via collect-len + sum.
#[test]
fn take_min_clamp() {
    let lt = format!(
        "{}    let t: BoundedVec_i64_8 = v.take(2);\n    return 0 - (t.len() * 100 + t.sum());",
        fill("8", 5)
    ); // [1,2] → 2*100+3=203
    let eq = format!(
        "{}    let t: BoundedVec_i64_8 = v.take(5);\n    return 0 - (t.len() * 100 + t.sum());",
        fill("8", 5)
    ); // all 5 → 5*100+15=515
    let gt = format!(
        "{}    let t: BoundedVec_i64_8 = v.take(99);\n    return 0 - (t.len() * 100 + t.sum());",
        fill("8", 5)
    ); // clamp 5 → 515
    let zero = format!(
        "{}    let t: BoundedVec_i64_8 = v.take(0);\n    return 0 - (t.len() + 50);",
        fill("8", 5)
    ); // len 0 → 50
    assert_eq!(neg(&lt), 203);
    assert_eq!(neg(&eq), 515);
    assert_eq!(neg(&gt), 515);
    assert_eq!(neg(&zero), 50);
}

// ───────────────────────── composition + capture + freshness ─────────────────

// Eager composition: map(*2)=[2,4,6,8], filter(>4)=[6,8], sum=14.
#[test]
fn compose_map_filter_sum() {
    let body = format!(
        "{}    let m: BoundedVec_i64_8 = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n    let f: BoundedVec_i64_8 = m.filter(fn(x: i64) -> bool {{ return x > 4; }});\n    return 0 - f.sum();",
        fill("8", 4)
    );
    assert_eq!(neg(&body), 14);
}

// Capturing closure (PR #337): factor=10 captured. (1+2+3)*10 = 60.
#[test]
fn map_capturing_closure() {
    let body = format!(
        "{}    let factor: i64 = 10;\n    let m: BoundedVec_i64_8 = v.map(fn(x: i64) -> i64 {{ return x * factor; }});\n    return 0 - m.sum();",
        fill("8", 3)
    );
    assert_eq!(neg(&body), 60);
}

// NC-P2-6: the result is FRESH — mutating it does NOT touch the source. v=[1,2,3];
// m=v.map(*2)=[2,4,6]; m.set(0,999); v.get(0) must still be 1.
#[test]
fn map_result_is_fresh_not_aliased() {
    let body = format!(
        "{}    let mut m: BoundedVec_i64_8 = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n    let _w: i64 = m.set(0, 999);\n    let vo: Option<i64> = v.get(0);\n    return 0 - vo.unwrap_or(0);",
        fill("8", 3)
    );
    assert_eq!(neg(&body), 1); // v[0] unchanged → 1; an aliasing map would give 999 or 2
}

// ───────────────────────── per-size (NC-P2-2) ─────────────────────────

// _64 with 12 elements (>8): map*2 sum = 2*(1+…+12) = 156; a `_8`-result transposition traps.
#[test]
fn size_64_over_eight() {
    let body = format!(
        "{}    let m: BoundedVec_i64_64 = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n    return 0 - m.sum();",
        fill("64", 12)
    );
    assert_eq!(neg(&body), 156);
}

// _256 with 10 elements (>8): filter even = [2,4,6,8,10] sum 30; take(3) of that = [2,4,6] sum 12 → 30*100+12=3012.
#[test]
fn size_256_over_eight() {
    let body = format!(
        "{}    let f: BoundedVec_i64_256 = v.filter(fn(x: i64) -> bool {{ let r: i64 = x - (x / 2) * 2; return r == 0; }});\n    let t: BoundedVec_i64_256 = f.take(3);\n    return 0 - (f.sum() * 100 + t.sum());",
        fill("256", 10)
    );
    assert_eq!(neg(&body), 3012);
}

// map on a FULL _8 (count==8): full result, NO trap. sum 2*(1+…+8) = 72.
#[test]
fn map_on_full_eight_no_trap() {
    let body = format!(
        "{}    let m: BoundedVec_i64_8 = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n    return 0 - (m.len() * 1000 + m.sum());",
        fill("8", 8)
    );
    assert_eq!(neg(&body), 8072); // len 8 → 8000, sum 72
}

// ───────────────────────── unhappy: empty source ─────────────────────────

#[test]
fn empty_source_all_ops() {
    let base = "    let v: BoundedVec_i64_8 = BoundedVec_i64_8::new();\n";
    assert_eq!(
        neg(&format!(
            "{base}    let m: BoundedVec_i64_8 = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n    return 0 - (m.len() + 11);"
        )),
        11
    );
    assert_eq!(
        neg(&format!(
            "{base}    let f: BoundedVec_i64_8 = v.filter(fn(x: i64) -> bool {{ return x > 0; }});\n    return 0 - (f.len() + 22);"
        )),
        22
    );
    assert_eq!(neg(&format!("{base}    return 0 - (v.sum() + 33);")), 33);
    assert_eq!(
        neg(&format!(
            "{base}    return 0 - v.fold(44, fn(a: i64, b: i64) -> i64 {{ return a + b; }});"
        )),
        44
    );
    assert_eq!(
        neg(&format!(
            "{base}    if v.any(fn(x: i64) -> bool {{ return x > 0; }}) {{ return 0 - 1; }} else {{ return 0 - 55; }}"
        )),
        55
    );
    assert_eq!(
        neg(&format!(
            "{base}    if v.all(fn(x: i64) -> bool {{ return x > 0; }}) {{ return 0 - 66; }} else {{ return 0 - 1; }}"
        )),
        66
    ); // vacuous true
    assert_eq!(
        neg(&format!(
            "{base}    let o: Option<i64> = v.find(fn(x: i64) -> bool {{ return x > 0; }});\n    return 0 - o.unwrap_or(77);"
        )),
        77
    );
    assert_eq!(
        neg(&format!(
            "{base}    let t: BoundedVec_i64_8 = v.take(3);\n    return 0 - (t.len() + 88);"
        )),
        88
    );
    assert_eq!(
        neg(&format!(
            "{base}    let f: BoundedVec_i64_8 = v.filter_map(fn(x: i64) -> Option<i64> {{ return Some(x); }});\n    return 0 - (f.len() + 99);"
        )),
        99
    );
}

// filter that rejects everything → empty, not a trap.
#[test]
fn filter_all_out() {
    let body = format!(
        "{}    let f: BoundedVec_i64_8 = v.filter(fn(x: i64) -> bool {{ return x > 100; }});\n    return 0 - (f.len() + 7);",
        fill("8", 4)
    );
    assert_eq!(neg(&body), 7);
}

// ───────────────────────── adversarial survivors (folded in) ─────────────────

// NC-P2-6 for filter + take (complements the map freshness test): mutate the result,
// source unchanged.
#[test]
fn filter_and_take_results_are_fresh() {
    let filt = format!(
        "{}    let mut f: BoundedVec_i64_8 = v.filter(fn(x: i64) -> bool {{ let r: i64 = x - (x / 2) * 2; return r == 0; }});\n    let _w: i64 = f.set(0, 999);\n    let o: Option<i64> = v.get(0);\n    return 0 - o.unwrap_or(0);",
        fill("8", 4)
    );
    let take = format!(
        "{}    let mut t: BoundedVec_i64_8 = v.take(2);\n    let _w: i64 = t.set(0, 999);\n    let o: Option<i64> = v.get(0);\n    return 0 - o.unwrap_or(0);",
        fill("8", 5)
    );
    assert_eq!(neg(&filt), 1); // v[0] unchanged
    assert_eq!(neg(&take), 1);
}

// Reverse aliasing: mutating the SOURCE after a transform does not change the RESULT.
// v=[1,2,3]; m=v.map(*2)=[2,4,6]; v.set(0,999); m.get(0) must still be 2.
#[test]
fn mutating_source_after_map_leaves_result() {
    let body = format!(
        "{}    let m: BoundedVec_i64_8 = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n    let _w: i64 = v.set(0, 999);\n    let o: Option<i64> = m.get(0);\n    return 0 - o.unwrap_or(0);",
        fill("8", 3)
    );
    assert_eq!(neg(&body), 2);
}

// filter_map MUST distinguish Some(0) (a real kept value) from None (a drop).
// Every element → Some(0): result is [0,0,0], len 3, sum 0 → 3*100 + 0 = 300.
#[test]
fn filter_map_keeps_some_zero() {
    let body = format!(
        "{}    let f: BoundedVec_i64_8 = v.filter_map(fn(x: i64) -> Option<i64> {{ return Some(0); }});\n    return 0 - (f.len() * 100 + f.sum());",
        fill("8", 3)
    );
    assert_eq!(neg(&body), 300);
}

// take(negative) → empty (not a trap, not a huge read).
#[test]
fn take_negative_is_empty() {
    let body = format!(
        "{}    let t: BoundedVec_i64_8 = v.take(0 - 3);\n    return 0 - (t.len() + 40);",
        fill("8", 5)
    );
    assert_eq!(neg(&body), 40);
}

// The full-N boundary on a LARGER size: map on a FULL `_64` (count==64) → full result,
// no trap. len 64, sum 2*(1+…+64) = 4160 → 64*100000 + 4160 = 6404160.
#[test]
fn map_on_full_sixtyfour_no_trap() {
    let mut fill64 = String::from("    let mut v: BoundedVec_i64_64 = BoundedVec_i64_64::new();\n");
    for i in 1..=64 {
        fill64.push_str(&format!("    let _p{i}: i64 = v.push({i});\n"));
    }
    let body = format!(
        "{fill64}    let m: BoundedVec_i64_64 = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n    return 0 - (m.len() * 100000 + m.sum());"
    );
    assert_eq!(neg(&body), 6404160);
}
