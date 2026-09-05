//! Iterator protocol (PR-1): `for x in <it>` over a USER-DEFINED iterator — a type
//! with `next(self @Mut) -> Option<T>` — desugared to `while`+`match` over `it.next()`.
//! Zero stdlib coupling: the user's `Counter` writes its own `Some`/`None`, which
//! ambient-injects `option`. No `! { Alloc }` (records + the desugar are Alloc-free).
//!
//! Negative-sentinel convention: `tool_main` returns `0 - value`; the runtime reports
//! it as `Err(Trapped { "tool returned error (-value)" })`, decoded back to `value`.

mod common;

/// A `module tool;` program with a `Counter` iterator + the given `tool_main` body.
/// `Counter::next` yields `0..max` then `None`; `make_counter(n)` is a fresh counter.
fn prog(body: &str) -> String {
    format!(
        "module tool;\n\
         record Counter {{ cur: i64, max: i64 }}\n\
         impl Counter {{\n\
         \x20   pub fn next(self: Counter @Mut) -> Option<i64> {{\n\
         \x20       if self.cur < self.max {{\n\
         \x20           let v: i64 = self.cur;\n\
         \x20           self.cur = self.cur + 1;\n\
         \x20           return Some(v);\n\
         \x20       }} else {{\n\
         \x20           return None;\n\
         \x20       }}\n\
         \x20   }}\n\
         }}\n\
         fn make_counter(n: i64) -> Counter {{\n\
         \x20   return Counter {{ cur: 0, max: n }};\n\
         }}\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

use common::run_returning_negative as run_neg;

fn neg(body: &str) -> i64 {
    run_neg(&prog(body))
}

#[test]
fn counter_loop_sums() {
    // for x in make_counter(5): x = 0,1,2,3,4 → sum 10 (> 0, decodes directly).
    let body = "    let mut sum: i64 = 0;\n\
        \x20   for x in make_counter(5) {\n\
        \x20       sum = sum + x;\n\
        \x20   }\n\
        \x20   return 0 - sum;";
    assert_eq!(neg(body), 10);
}

#[test]
fn empty_iterator_runs_zero_times() {
    // make_counter(0): the FIRST next() is None → 0 iterations → sum stays 0.
    // (+7 base keeps the sentinel strictly negative so a clean 0 is distinguishable.)
    let body = "    let mut sum: i64 = 0;\n\
        \x20   for x in make_counter(0) {\n\
        \x20       sum = sum + x + 1000;\n\
        \x20   }\n\
        \x20   return 0 - (sum + 7);";
    assert_eq!(neg(body), 7);
}

#[test]
fn for_over_local_counter() {
    // The iterable is a LOCAL (the desugar's `$it` aliases it); 0+1+2 = 3.
    let body = "    let mut c: Counter = make_counter(3);\n\
        \x20   let mut sum: i64 = 0;\n\
        \x20   for x in c {\n\
        \x20       sum = sum + x;\n\
        \x20   }\n\
        \x20   return 0 - (sum + 100);";
    assert_eq!(neg(body), 103); // sum 3
}

#[test]
fn return_from_body_propagates() {
    // ET-4: a `return` inside the loop body returns from tool_main, NOT just the loop.
    // When x == 4 we return -(4+50); if `return` were swallowed we'd fall through to
    // the -999 tail.
    let body = "    for x in make_counter(9) {\n\
        \x20       if x == 4 {\n\
        \x20           return 0 - (x + 50);\n\
        \x20       } else {\n\
        \x20       }\n\
        \x20   }\n\
        \x20   return 0 - 999;";
    assert_eq!(neg(body), 54); // -(4+50) decoded
}

#[test]
fn nested_for_hygiene() {
    // ET-3: nested loops — the inner `$for_*` temps must not clobber the outer's.
    // Σ over x,y ∈ 0..2 of (x*10 + y) = 3 + 33 + 63 = 99.
    let body = "    let mut sum: i64 = 0;\n\
        \x20   for x in make_counter(3) {\n\
        \x20       for y in make_counter(3) {\n\
        \x20           sum = sum + x * 10 + y;\n\
        \x20       }\n\
        \x20   }\n\
        \x20   return 0 - sum;";
    assert_eq!(neg(body), 99);
}
