//! RANGE-FOR (RF-M0) runtime semantics: the `for v in a..b` loop EXECUTES
//! correctly — iteration count, exclusive end, signed/empty/negative ranges,
//! break/continue (the widened I64 `LoopFrame` increment), EVAL-ONCE bounds,
//! nesting, and the M0 memory-safety floor (an `arr[v]` body index keeps its
//! runtime trap; OOB traps, in-bounds runs). Mirrors the `tool`/`neg`/
//! `body_traps` harness of bounded_map_u256.rs (a `return 0 - K` sentinel
//! arrives as Trapped("tool returned error (K)")).

mod common;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    common::run_returning_negative_with_min_fuel(&tool(body), 1_000_000_000)
}

/// True iff `body` GENUINELY traps (fuel is generous, so a trap is a real trap).
fn body_traps(body: &str) -> bool {
    common::tool_traps_with_min_fuel(&tool(body), 1_000_000_000)
}

#[test]
fn rf_sum_range() {
    // sum 0..5 = 0+1+2+3+4 = 10 (exclusive end).
    assert_eq!(
        neg(
            "    let mut acc = 0;\n    for i in 0..5 {\n        acc = acc + i;\n    }\n    return 0 - acc;"
        ),
        10
    );
}

#[test]
fn rf_empty_range_is_noop() {
    // start >= end ⇒ zero iterations.
    assert_eq!(
        neg(
            "    let mut acc = 7;\n    for i in 5..2 {\n        acc = acc + 100;\n    }\n    return 0 - acc;"
        ),
        7
    );
}

#[test]
fn rf_negative_start() {
    // (0-2)..2 iterates -2,-1,0,1 — four iterations, signed semantics.
    assert_eq!(
        neg(
            "    let mut count = 0;\n    for i in 0 - 2..2 {\n        count = count + 1;\n    }\n    return 0 - count;"
        ),
        4
    );
}

#[test]
fn rf_break_exits() {
    // break at i==3 ⇒ acc = 0+1+2 = 3.
    assert_eq!(
        neg(
            "    let mut acc = 0;\n    for i in 0..100 {\n        if i == 3 {\n            break;\n        }\n        acc = acc + i;\n    }\n    return 0 - acc;"
        ),
        3
    );
}

#[test]
fn rf_continue_advances() {
    // continue must ADVANCE the I64 counter (the widened LoopFrame increment)
    // — a stuck counter would spin to fuel exhaustion, a U32-typed `__one`
    // would be width-mismatched. Skip even i in 0..6: acc = 1+3+5 = 9.
    assert_eq!(
        neg(
            "    let mut acc = 0;\n    for i in 0..6 {\n        if i == 0 {\n            continue;\n        }\n        if i == 2 {\n            continue;\n        }\n        if i == 4 {\n            continue;\n        }\n        acc = acc + i;\n    }\n    return 0 - acc;"
        ),
        9
    );
}

#[test]
fn rf_bounds_eval_once() {
    // THE eval-once pin: the end bound is hoisted into the pre-header, so a
    // body write to the bound variable does NOT change the trip count.
    assert_eq!(
        neg(
            "    let mut n = 3;\n    let mut count = 0;\n    for i in 0..n {\n        n = 100;\n        count = count + 1;\n    }\n    return 0 - count;"
        ),
        3
    );
}

#[test]
fn rf_nested_loops() {
    // 3 × 4 = 12 iterations; inner/outer counters independent.
    assert_eq!(
        neg(
            "    let mut count = 0;\n    for i in 0..3 {\n        for j in 0..4 {\n            count = count + 1;\n        }\n    }\n    return 0 - count;"
        ),
        12
    );
}

#[test]
fn rf_array_index_in_bounds_runs() {
    // M0 floor: `a[i]` keeps its runtime bounds check and RUNS in-bounds.
    assert_eq!(
        neg(
            "    let a = [10, 20, 30];\n    let mut acc = 0;\n    for i in 0..3 {\n        acc = acc + a[i];\n    }\n    return 0 - acc;"
        ),
        60
    );
}

#[test]
fn rf_array_index_oob_traps() {
    // M0 floor: `0..5` over `[i64; 3]` TRAPS at i == 3 (the runtime bounds
    // check is the memory-safety floor; nothing is elided in M0).
    assert!(body_traps(
        "    let a = [10, 20, 30];\n    let mut acc = 0;\n    for i in 0..5 {\n        acc = acc + a[i];\n    }\n    return 0 - acc;"
    ));
}

#[test]
fn rf_loop_var_scoped_to_body() {
    // The loop var does not leak past the loop: an outer same-name binding
    // is untouched after the loop ends.
    assert_eq!(
        neg(
            "    let i = 42;\n    let mut acc = 0;\n    for i in 0..3 {\n        acc = acc + i;\n    }\n    return 0 - (acc + i);"
        ),
        45
    );
}

#[test]
fn rf_len_bound_sum() {
    // RF-M2 headline: `for i in 0..a.len() { a[i] }` — the bound substitutes
    // the STATIC size (SC-4), the body index ELIDES its bounds check, and the
    // VALUE is identical to the checked version.
    assert_eq!(
        neg("    let a = [10, 20, 30];
    let mut acc = 0;
    for i in 0..a.len() {
        acc = acc + a[i];
    }
    return 0 - acc;"),
        60
    );
}

// ── RF-M1: the binding adversarial corpus ────────────────────────────────────
// Pins WHICH binding wins in every rebinding shape, BEFORE the RF-M2 fact
// channel exists. These are the exact shapes `body_rebinds_name` (the M2
// pre-scan) must refuse the bounds fact for — the values below are the ground
// truth proving the shadow really does capture the name (an elision keyed on
// the raw name would read the WRONG variable in each of these).

fn tool_mod(decls: &str, body: &str) -> String {
    format!(
        "module tool;\n{decls}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

fn neg_mod(decls: &str, body: &str) -> i64 {
    common::run_returning_negative_with_min_fuel(&tool_mod(decls, body), 1_000_000_000)
}

#[test]
fn rb_let_shadow_wins_inside_body() {
    // `let i = 100` SHADOWS the loop var for the rest of the iteration:
    // acc = 100 * 3, not 0+1+2.
    assert_eq!(
        neg(
            "    let mut acc = 0;\n    for i in 0..3 {\n        let i = 100;\n        acc = acc + i;\n    }\n    return 0 - acc;"
        ),
        300
    );
}

#[test]
fn rb_match_arm_binding_shadows() {
    // A match-arm ENUM binding named `i` shadows the loop var inside the arm:
    // each iteration adds the payload 50, never the counter.
    assert_eq!(
        neg_mod(
            "pub enum Maybe { None, Some(i64) }",
            "    let mut acc = 0;\n    for i in 0..3 {\n        let m = Maybe::Some(50);\n        match m {\n            Maybe::Some(i) => {\n                acc = acc + i;\n            },\n            Maybe::None => {\n                acc = acc + 1000;\n            },\n        }\n    }\n    return 0 - acc;"
        ),
        150
    );
}

#[test]
fn rb_closure_param_shadows() {
    // A closure whose PARAM is named `i` — inside the closure body, `i` is the
    // argument (100), never the enclosing loop counter. This is the exact
    // lambda-lifting hole the RF-M2 channel BARRIER exists for: the closure
    // body is a different function.
    assert_eq!(
        neg(
            "    let f = fn(i: i64) -> i64 {\n        return i * 2;\n    };\n    let mut acc = 0;\n    for i in 0..3 {\n        acc = acc + f(100);\n    }\n    return 0 - acc;"
        ),
        600
    );
}

#[test]
fn rb_let_tuple_shadows() {
    // `let (i, j) = …` rebinds `i` via the TUPLE binder (the easy-to-forget
    // binder form the M2 pre-scan must also refuse).
    assert_eq!(
        neg(
            "    let mut acc = 0;\n    for i in 0..3 {\n        let (i, j) = (7, 8);\n        acc = acc + i + j;\n    }\n    return 0 - acc;"
        ),
        45
    );
}

#[test]
fn rb_nested_same_name_loop() {
    // A nested range-for reusing the SAME name: the inner counter wins inside
    // the inner body — (0+1+2) per outer iteration, 2 outer iterations.
    assert_eq!(
        neg(
            "    let mut acc = 0;\n    for i in 0..2 {\n        for i in 0..3 {\n            acc = acc + i;\n        }\n    }\n    return 0 - acc;"
        ),
        6
    );
}

// ── Stdlib capped-scan shape pins (PR-1 of the loop-aware-budget arc) ────────
// The bounded_map stdlib rewrites its `while i < X` probe/copy loops to
// `for i in 0..64 { if i >= X { break; } .. }` so the trip bound 64 is
// syntactically static (a for-range with two literal bounds). These pin the
// exact shapes that rewrite relies on.

#[test]
fn rf_capped_scan_breaks_at_runtime_count() {
    // The capped-scan shape: literal capacity 64, runtime count n=5 — the body
    // must run exactly n times, the break arm eating the remaining 59.
    assert_eq!(
        neg(
            "    let n = 5;\n    let mut acc = 0;\n    for i in 0..64 {\n        if i >= n {\n            break;\n        }\n        acc = acc + 1;\n    }\n    return 0 - acc;"
        ),
        5
    );
}

#[test]
fn rf_capped_scan_early_return_from_probe() {
    // The probe shape (get/get_or/insert): early `return` from inside the
    // bounded loop, past the break guard.
    assert_eq!(
        neg(
            "    let n = 7;\n    for i in 0..64 {\n        if i >= n {\n            break;\n        }\n        if i == 4 {\n            return 0 - 42;\n        }\n    }\n    return 0 - 1;"
        ),
        42
    );
}

#[test]
fn rf_capped_scan_full_occupancy_never_breaks() {
    // count == capacity: the break guard never fires; all 64 iterations run.
    assert_eq!(
        neg(
            "    let n = 64;\n    let mut acc = 0;\n    for i in 0..64 {\n        if i >= n {\n            break;\n        }\n        acc = acc + 1;\n    }\n    return 0 - acc;"
        ),
        64
    );
}
