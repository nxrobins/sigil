//! WCC (worst-case-cost) recommended_budget: the loop-aware budget arc (PR-2).
//!
//! The property under test: for a program whose every fuel-decrement site has a
//! STATIC multiplicity (for-range loops with literal bounds, acyclic calls, no
//! indirect calls/sends), `recommended_budget` is a true workload CEILING —
//! measured consumption can never exceed it. Programs with unbounded loops keep
//! the old floor semantics and say so via `fuel_is_workload_ceiling == false`.
//!
//! TDD note: the ceiling assertions here were written RED against the pre-WCC
//! formula (`128 + 8×static-weight`), which a `for i in 0..5000` loop overruns
//! 37× (consumed 5001 vs budget 168). WCC turns them green.

use proptest::prelude::*;
use sigil_compiler::compile_tool;
use sigil_runtime::{IoGrants, execute_ephemeral};

/// Real measured cost of a tool (run at a huge budget so nothing saturates).
fn measured_cost(src: &str) -> (u64, u64, bool) {
    let compiled = compile_tool(src).expect("tool should compile");
    let r = execute_ephemeral(&compiled.wasm, b"", 1_000_000_000, &IoGrants::none())
        .expect("tool should run at the generous budget");
    (
        r.fuel_consumed,
        compiled.fuel_budget,
        compiled.fuel_is_workload_ceiling,
    )
}

// ── The headline red→green pins ─────────────────────────────────────────────

#[test]
fn bounded_loop_budget_is_a_ceiling() {
    // for-range 0..5000: one back-edge site, 5001 real cost. Pre-WCC budget 168.
    let (consumed, budget, ceiling) = measured_cost(
        r#"
module tool;
pub fn tool_main(a: i64, b: i64) -> i64 {
    let _ = a; let _ = b;
    let mut acc = 0;
    for i in 0..5000 {
        acc = acc + i;
    }
    let _ = acc;
    return 0;
}
"#,
    );
    assert!(ceiling, "all sites statically bounded -> ceiling flag");
    assert!(
        consumed <= budget,
        "WCC must cover the loop: consumed={consumed} > budget={budget}"
    );
}

#[test]
fn nested_bounded_loops_multiply() {
    // 12 × 9 inner back-edges + inner cond overhead — the multiplicative case.
    let (consumed, budget, ceiling) = measured_cost(
        r#"
module tool;
pub fn tool_main(a: i64, b: i64) -> i64 {
    let _ = a; let _ = b;
    let mut acc = 0;
    for i in 0..12 {
        for j in 0..9 {
            acc = acc + i + j;
        }
    }
    let _ = acc;
    return 0;
}
"#,
    );
    assert!(ceiling);
    assert!(consumed <= budget, "consumed={consumed} > budget={budget}");
}

#[test]
fn call_in_bounded_loop_multiplies_callee_cost() {
    // The cross-function multiplication (the airdrop's shape in miniature):
    // helper contains its own bounded loop; called from a bounded loop.
    let (consumed, budget, ceiling) = measured_cost(
        r#"
module tool;
fn helper(x: i64) -> i64 {
    let mut s = 0;
    for j in 0..7 {
        s = s + j;
    }
    return s + x;
}
pub fn tool_main(a: i64, b: i64) -> i64 {
    let _ = a; let _ = b;
    let mut acc = 0;
    for i in 0..11 {
        acc = acc + helper(i);
    }
    let _ = acc;
    return 0;
}
"#,
    );
    assert!(ceiling);
    assert!(consumed <= budget, "consumed={consumed} > budget={budget}");
}

// ── Floor semantics preserved for the unbounded world ────────────────────────

#[test]
fn while_loop_is_not_a_ceiling() {
    let compiled = compile_tool(
        r#"
module tool;
pub fn tool_main(a: i64, b: i64) -> i64 {
    let _ = a; let _ = b;
    let mut n = 5;
    while n > 0 {
        n = n - 1;
    }
    return 0;
}
"#,
    )
    .expect("compiles");
    assert!(
        !compiled.fuel_is_workload_ceiling,
        "a while loop has no static bound -> floor semantics, flag false"
    );
}

#[test]
fn recursion_is_not_a_ceiling() {
    let compiled = compile_tool(
        r#"
module tool;
fn f(n: i64) -> i64 {
    if n < 1 {
        return 0;
    }
    return f(n - 1);
}
pub fn tool_main(a: i64, b: i64) -> i64 {
    let _ = b;
    return f(a);
}
"#,
    )
    .expect("compiles");
    assert!(
        !compiled.fuel_is_workload_ceiling,
        "a call-graph cycle -> flag false"
    );
}

#[test]
fn runtime_start_static_end_is_not_bounded() {
    // `for i in s..64` with runtime s trips MORE than 64 on negative s —
    // finding 6 of the design review. Must stay unbounded.
    let compiled = compile_tool(
        r#"
module tool;
pub fn tool_main(a: i64, b: i64) -> i64 {
    let _ = b;
    let mut acc = 0;
    for i in a..64 {
        acc = acc + 1;
    }
    return 0 - acc;
}
"#,
    )
    .expect("compiles");
    assert!(!compiled.fuel_is_workload_ceiling);
}

// ── The WCC soundness property (property-based) ──────────────────────────────

/// Generate a random statically-bounded tool: nested for-range literal loops
/// (depth ≤ 3, K ≤ 12) with per-level accumulator work and an optional bounded
/// helper call. Every generated program must satisfy consumed ≤ budget.
fn bounded_tool(depth: usize, ks: &[u8], call_helper: bool) -> String {
    let mut body = String::from("    acc = acc + 1;\n");
    if call_helper {
        body = String::from("    acc = acc + helper(acc);\n");
    }
    for (level, k) in ks.iter().take(depth).enumerate() {
        let var = format!("i{level}");
        body = format!(
            "    for {var} in 0..{k} {{\n{}    }}\n",
            body.lines()
                .map(|l| format!("    {l}\n"))
                .collect::<String>()
        );
    }
    let helper = if call_helper {
        "fn helper(x: i64) -> i64 {\n    let mut s = 0;\n    for h in 0..5 {\n        s = s + h;\n    }\n    return s + x;\n}\n"
    } else {
        ""
    };
    format!(
        "module tool;\n{helper}pub fn tool_main(a: i64, b: i64) -> i64 {{\n    let _ = a; let _ = b;\n    let mut acc = 0;\n{body}    let _ = acc;\n    return 0;\n}}\n"
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]
    #[test]
    fn wcc_is_sound_for_bounded_programs(
        depth in 1usize..=3,
        ks in proptest::collection::vec(1u8..=12, 3),
        call_helper in any::<bool>(),
    ) {
        let src = bounded_tool(depth, &ks, call_helper);
        let compiled = compile_tool(&src).expect("generated tool should compile");
        prop_assert!(compiled.fuel_is_workload_ceiling, "generated program is fully bounded");
        let r = execute_ephemeral(&compiled.wasm, b"", 1_000_000_000, &IoGrants::none())
            .expect("generated tool should run");
        prop_assert!(
            r.fuel_consumed <= compiled.fuel_budget,
            "WCC soundness violated: consumed={} > budget={} for:\n{}",
            r.fuel_consumed, compiled.fuel_budget, src
        );
    }
}
