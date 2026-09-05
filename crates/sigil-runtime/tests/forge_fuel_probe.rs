//! Regression tests for forge/ephemeral fuel ENFORCEMENT.
//!
//! Before the fix, the ephemeral `sigil::fuel_decrement` host fn saturated at zero
//! instead of trapping, so (1) a tool could not be stopped by its declared fuel budget
//! — only by the coarse 10e9-instruction wasmtime backstop — and (2) an overrunning
//! tool reported `fuel_consumed == fuel_budget` EXACTLY, making the overrun
//! arithmetically invisible in the report/cert.

use sigil_compiler::compile_tool;
use sigil_runtime::{IoGrants, ToolError, execute_ephemeral};

/// A tool with a bounded loop whose real fuel cost (5001) far exceeds a small budget.
const LOOPING_TOOL: &str = r#"
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let _ = input_ptr;
    let _ = input_len;
    let mut n = 5000;
    let mut acc = 0;
    while n > 0 {
        acc = acc + n;
        n = n - 1;
    }
    let _ = acc;
    return 0;
}
"#;

/// The headline guarantee: a tool that overruns its DECLARED budget is stopped,
/// even though it is bounded and would otherwise complete well under the
/// 10e9-instruction wasmtime backstop.
#[test]
fn declared_fuel_budget_stops_an_overrunning_tool() {
    let compiled = compile_tool(LOOPING_TOOL).expect("tool should compile");
    const TINY_BUDGET: u64 = 10;

    match execute_ephemeral(&compiled.wasm, b"", TINY_BUDGET, &IoGrants::none()) {
        Err(ToolError::FuelExhausted { consumed }) => {
            assert_eq!(consumed, TINY_BUDGET);
        }
        other => panic!("expected FuelExhausted — fuel must be enforced, got: {other:?}"),
    }
}

/// A tool whose real cost fits its budget still runs to completion, and reports its
/// TRUE consumption — strictly less than the budget. This is the arm that would fail
/// if enforcement were implemented by trapping too eagerly.
#[test]
fn a_tool_within_its_budget_completes_and_reports_true_consumption() {
    let compiled = compile_tool(LOOPING_TOOL).expect("tool should compile");
    let generous = 1_000_000u64;

    let r = execute_ephemeral(&compiled.wasm, b"", generous, &IoGrants::none())
        .expect("a tool within its budget must complete");
    assert_eq!(r.fuel_consumed, 5001, "the loop's real, measured cost");
    assert!(
        r.fuel_consumed < generous,
        "consumption must be the TRUE figure, not saturated to the budget"
    );
}

/// The overrun must not be arithmetically invisible: the pre-fix bug reported
/// `consumed == budget` exactly, which is indistinguishable from a tool that
/// legitimately used its budget to the last unit.
#[test]
fn an_overrun_is_not_reported_as_an_exact_fit() {
    let compiled = compile_tool(LOOPING_TOOL).expect("tool should compile");
    // Budget the loop to 100 iterations' worth; the loop wants 5001.
    let res = execute_ephemeral(&compiled.wasm, b"", 100, &IoGrants::none());
    assert!(
        matches!(res, Err(ToolError::FuelExhausted { .. })),
        "an overrun must surface as an error, not as Ok(consumed==budget); got {res:?}"
    );
}

/// A tool with zero fuel sites never decrements, so even a budget of 1 completes.
/// Pins that enforcement did not become "trap on any small budget".
#[test]
fn a_tool_with_no_fuel_sites_completes_on_a_minimal_budget() {
    let source = r#"
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }
"#;
    let compiled = compile_tool(source).expect("tool should compile");
    let r = execute_ephemeral(&compiled.wasm, b"", 1, &IoGrants::none())
        .expect("a tool with no decrements must complete");
    assert_eq!(r.fuel_consumed, 0);
}

/// Task (d): the compiler's recommendation must cover the alloc fuel that
/// `memory::lower` inserts (`max(1, size/64)`), which it previously ignored.
#[test]
fn recommended_budget_covers_memory_pass_alloc_fuel() {
    // A record construct is the AirValue::RecordConstruct path (memory.rs:55-67).
    let source = r#"
module tool;
record Pt { x: i64, y: i64 }
pub fn tool_main(a: i64, b: i64) -> i64 ! { Alloc } {
    let _ = a; let _ = b;
    let p = Pt { x: 1, y: 2 };
    return p.x - 1;
}
"#;
    let compiled = compile_tool(source).expect("tool should compile");

    // Running AT the compiler's own recommendation must not trap: the recommendation
    // now accounts for the alloc decrement it previously left out.
    let r = execute_ephemeral(&compiled.wasm, b"", compiled.fuel_budget, &IoGrants::none())
        .expect("a straight-line program must run at its own recommended budget");
    assert!(r.fuel_consumed <= compiled.fuel_budget);
}
