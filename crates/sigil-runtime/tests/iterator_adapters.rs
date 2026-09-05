//! Phase 7 — iterator adapter pipelines (eager + lazy), i64 element type.
//!
//! Eager `Vec` adapters (`map`/`filter`) materialize a fresh `Vec<i64>` and so
//! chain on the result; the terminals (`sum`/`fold`/`any`/`all`/`find`) fold to a
//! scalar/bool/Option. Lazy adapters (`VecIter`→`MapIter`/`FilterIter`/`TakeIter`)
//! compose fluently (`v.iter().filter(g).map(f).take(n).collect()`), are for-in-
//! able by their `next` shape, and `take` pulls its inner iterator at most `n`
//! times. All run under a no-`! { Alloc }`-less tool_main (map/filter/collect
//! allocate). Values asserted via the negative-sentinel decode (the parser /
//! typecheck differentials check types & nodes, never runtime bytes).

mod common;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    common::run_returning_negative_with_min_fuel(&tool(body), 1_000_000_000)
}

/// Body prefix: a `Vec<i64>` holding 1..=n.
fn fill(n: i64) -> String {
    let mut s = String::from("    let mut v: Vec<i64> = Vec::new();\n");
    for i in 1..=n {
        s.push_str(&format!("    let _p{i}: i64 = v.push({i});\n"));
    }
    s
}

// ─────────────────────────── eager adapters ───────────────────────────

// INV-1: map preserves length AND order. [1,2,3] *2 → [2,4,6]; get(0)=2, get(2)=6,
// len=3 → 2*1000 + 6*10 + 3 = 2063.
#[test]
fn map_len_and_order() {
    let body = format!(
        "{}    let m: Vec<i64> = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n    let a: i64 = m.get(0);\n    let c: i64 = m.get(2);\n    return 0 - (a * 1000 + c * 10 + m.len());",
        fill(3)
    );
    assert_eq!(neg(&body), 2063);
}

// INV-2: filter keeps only-passing, in order — asymmetric predicate (odd) over
// mixed input [1..5] → [1,3,5]; get(0)=1, get(2)=5, len=3 → 1*1000 + 5*10 + 3 = 1053.
#[test]
fn filter_only_passing_in_order() {
    let body = format!(
        "{}    let f: Vec<i64> = v.filter(fn(x: i64) -> bool {{ let r: i64 = x - (x / 2) * 2; return r == 1; }});\n    let a: i64 = f.get(0);\n    let c: i64 = f.get(2);\n    return 0 - (a * 1000 + c * 10 + f.len());",
        fill(5)
    );
    assert_eq!(neg(&body), 1053);
}

#[test]
fn sum_terminal() {
    assert_eq!(neg(&format!("{}    return 0 - v.sum();", fill(4))), 10);
}

// INV-8: fold is left-to-right, seeded — non-commutative subtraction.
// 100 - 1 - 2 - 3 = 94.
#[test]
fn fold_left_seeded_subtraction() {
    let body = format!(
        "{}    return 0 - v.fold(100, fn(a: i64, b: i64) -> i64 {{ return a - b; }});",
        fill(3)
    );
    assert_eq!(neg(&body), 94);
}

// INV-9: any/all/find short-circuit + correctness.
#[test]
fn any_hit_and_miss() {
    let hit = format!(
        "{}    if v.any(fn(x: i64) -> bool {{ return x == 3; }}) {{ return 0 - 1; }} else {{ return 0 - 2; }}",
        fill(4)
    );
    let miss = format!(
        "{}    if v.any(fn(x: i64) -> bool {{ return x == 9; }}) {{ return 0 - 1; }} else {{ return 0 - 2; }}",
        fill(4)
    );
    assert_eq!(neg(&hit), 1);
    assert_eq!(neg(&miss), 2);
}

#[test]
fn all_true_and_false() {
    let t = format!(
        "{}    if v.all(fn(x: i64) -> bool {{ return x > 0; }}) {{ return 0 - 1; }} else {{ return 0 - 2; }}",
        fill(4)
    );
    let f = format!(
        "{}    if v.all(fn(x: i64) -> bool {{ return x > 2; }}) {{ return 0 - 1; }} else {{ return 0 - 2; }}",
        fill(4)
    );
    assert_eq!(neg(&t), 1);
    assert_eq!(neg(&f), 2);
}

#[test]
fn find_hit_and_miss() {
    let hit = format!(
        "{}    let o: Option<i64> = v.find(fn(x: i64) -> bool {{ return x > 2; }});\n    return 0 - o.unwrap_or(0);",
        fill(4)
    );
    let miss = format!(
        "{}    let o: Option<i64> = v.find(fn(x: i64) -> bool {{ return x > 9; }});\n    return 0 - o.unwrap_or(777);",
        fill(4)
    );
    assert_eq!(neg(&hit), 3);
    assert_eq!(neg(&miss), 777);
}

// Eager composition: map(*2)=[2,4,6,8], filter(>4)=[6,8], sum=14.
#[test]
fn eager_compose_map_filter_sum() {
    let body = format!(
        "{}    let m: Vec<i64> = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n    let f: Vec<i64> = m.filter(fn(x: i64) -> bool {{ return x > 4; }});\n    return 0 - f.sum();",
        fill(4)
    );
    assert_eq!(neg(&body), 14);
}

// A capturing closure (PR #337) used as a map function. factor=10 captured.
#[test]
fn map_with_capturing_closure() {
    let body = format!(
        "{}    let factor: i64 = 10;\n    let m: Vec<i64> = v.map(fn(x: i64) -> i64 {{ return x * factor; }});\n    return 0 - m.sum();",
        fill(3)
    );
    assert_eq!(neg(&body), 60); // (1+2+3)*10
}

// ─────────────────────────── lazy adapters ───────────────────────────

// Lazy filter consumed by for-in (the structural `next` shape). Evens of [1..6]
// = [2,4,6], sum 12.
#[test]
fn lazy_filter_for_in() {
    let body = format!(
        "{}    let it = v.iter();\n    let fi = it.filter(fn(x: i64) -> bool {{ let r: i64 = x - (x / 2) * 2; return r == 0; }});\n    let mut s: i64 = 0;\n    for x in fi {{ s = s + x; }}\n    return 0 - s;",
        fill(6)
    );
    assert_eq!(neg(&body), 12);
}

// INV-3: take yields min(n, len). n<len, n==len, n>len, n==0 — via collect().len().
#[test]
fn take_min_n_len() {
    let lt = format!(
        "{}    let it = v.iter();\n    let t = it.take(2);\n    let c: Vec<i64> = t.collect();\n    return 0 - c.len();",
        fill(5)
    );
    let eq = format!(
        "{}    let it = v.iter();\n    let t = it.take(5);\n    let c: Vec<i64> = t.collect();\n    return 0 - c.len();",
        fill(5)
    );
    let gt = format!(
        "{}    let it = v.iter();\n    let t = it.take(99);\n    let c: Vec<i64> = t.collect();\n    return 0 - c.len();",
        fill(5)
    );
    let zero = format!(
        "{}    let it = v.iter();\n    let t = it.take(0);\n    let c: Vec<i64> = t.collect();\n    return 0 - (c.len() + 50);",
        fill(5)
    );
    assert_eq!(neg(&lt), 2);
    assert_eq!(neg(&eq), 5);
    assert_eq!(neg(&gt), 5);
    assert_eq!(neg(&zero), 50); // len 0 → 0 + 50
}

// INV-5: collect conserves elements + order. map(+100) over [1,2,3] → [101,102,103];
// collect; assert len==3 AND sum==306.
#[test]
fn lazy_map_collect_conservation() {
    let body = format!(
        "{}    let it = v.iter();\n    let m = it.map(fn(x: i64) -> i64 {{ return x + 100; }});\n    let c: Vec<i64> = m.collect();\n    return 0 - (c.len() * 1000 + c.sum());",
        fill(3)
    );
    assert_eq!(neg(&body), 3306); // len 3 → 3000, sum 306
}

// The spec's literal pipeline: filter(even)=[2,4,6], map(*10)=[20,40,60],
// take(2)=[20,40], collect, sum=60.
#[test]
fn spec_filter_map_take_collect() {
    let body = format!(
        "{}    let it = v.iter();\n    let p = it.filter(fn(x: i64) -> bool {{ let r: i64 = x - (x / 2) * 2; return r == 0; }});\n    let m = p.map(fn(x: i64) -> i64 {{ return x * 10; }});\n    let t = m.take(2);\n    let c: Vec<i64> = t.collect();\n    return 0 - c.sum();",
        fill(6)
    );
    assert_eq!(neg(&body), 60);
}

// take then map (chaining the other direction): take(3)=[1,2,3], map(+100), sum 306.
#[test]
fn lazy_take_then_map() {
    let body = format!(
        "{}    let it = v.iter();\n    let t = it.take(3);\n    let m = t.map(fn(x: i64) -> i64 {{ return x + 100; }});\n    let c: Vec<i64> = m.collect();\n    return 0 - c.sum();",
        fill(6)
    );
    assert_eq!(neg(&body), 306);
}

// ─────────────────────────── unhappy paths ───────────────────────────

// Every op over an empty Vec.
#[test]
fn empty_vec_all_ops() {
    let base = "    let v: Vec<i64> = Vec::new();\n";
    // map → empty → sum 0 (+ a marker so the sentinel is non-zero).
    assert_eq!(
        neg(&format!(
            "{base}    let m: Vec<i64> = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n    return 0 - (m.sum() + 11);"
        )),
        11
    );
    // filter → empty.
    assert_eq!(
        neg(&format!(
            "{base}    let f: Vec<i64> = v.filter(fn(x: i64) -> bool {{ return x > 0; }});\n    return 0 - (f.sum() + 22);"
        )),
        22
    );
    // sum over empty = 0.
    assert_eq!(neg(&format!("{base}    return 0 - (v.sum() + 33);")), 33);
    // fold over empty = seed.
    assert_eq!(
        neg(&format!(
            "{base}    return 0 - v.fold(44, fn(a: i64, b: i64) -> i64 {{ return a + b; }});"
        )),
        44
    );
    // any over empty = false → else branch.
    assert_eq!(
        neg(&format!(
            "{base}    if v.any(fn(x: i64) -> bool {{ return x > 0; }}) {{ return 0 - 1; }} else {{ return 0 - 55; }}"
        )),
        55
    );
    // all over empty = true (vacuous) → then branch.
    assert_eq!(
        neg(&format!(
            "{base}    if v.all(fn(x: i64) -> bool {{ return x > 0; }}) {{ return 0 - 66; }} else {{ return 0 - 1; }}"
        )),
        66
    );
    // find over empty = None.
    assert_eq!(
        neg(&format!(
            "{base}    let o: Option<i64> = v.find(fn(x: i64) -> bool {{ return x > 0; }});\n    return 0 - o.unwrap_or(77);"
        )),
        77
    );
}

// filter that rejects everything → empty result, not a trap.
#[test]
fn filter_all_out() {
    let body = format!(
        "{}    let f: Vec<i64> = v.filter(fn(x: i64) -> bool {{ return x > 100; }});\n    return 0 - (f.len() + 88);",
        fill(4)
    );
    assert_eq!(neg(&body), 88); // len 0 → 0 + 88
}

// Lazy take over an empty source → collect empty, no trap.
#[test]
fn lazy_take_empty_source() {
    let body = "    let mut v: Vec<i64> = Vec::new();\n    let it = v.iter();\n    let t = it.take(3);\n    let c: Vec<i64> = t.collect();\n    return 0 - (c.len() + 99);";
    assert_eq!(neg(body), 99);
}
