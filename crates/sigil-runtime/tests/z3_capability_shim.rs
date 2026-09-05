//! Self-hosting Cap<Z3>: end-to-end proof tests for the `z3_check` host shim.
//!
//! Each test drives a compiled SIGIL tool through the PUBLIC `execute_ephemeral`
//! entry point and asserts the boundary's observable behavior. Per that return
//! contract, a NEGATIVE shim return (our error codes) surfaces as
//! `Err(ToolError::Trapped { message: "tool returned error (N)" })`; `packed`
//! `== 1` (sat) yields `Ok` with a 1-byte output (ptr=0, len=1); and `packed`
//! `== 0` (unsat) yields `Ok` with an empty output.
//!
//! The exact `{sat=1, unsat=0, malformed=-400, unknown=-408}` verdict mapping
//! is pinned at the solver level by `ephemeral.rs`'s `z3_shim_tests`; here we
//! prove the GRANT gating (NC2), input hardening (NC3), and determinism (NC4)
//! across the real WASM boundary.
//!
//! Solver-gated: the `z3_check` shim only exists under `--features solver`
//! (NC5), so this whole file compiles only then.
#![cfg(feature = "solver")]

use sigil_compiler::compile_tool;
use sigil_runtime::{IoGrants, ToolError, ToolResult, Z3Grant, execute_ephemeral};

const FUEL_BUDGET: u64 = 1_000_000;

// A tool that passes its input buffer straight through to `z3_check`: the
// SMT-LIB2 query arrives as the program input (the `task026` pattern). No
// `Alloc` — `z3_check` returns a scalar verdict, it writes no guest memory.
const PASSTHROUGH_TOOL: &str = r#"
#[ring(outer)] #[trusted]
module tool;

extern "C" fn z3_check(query_ptr: i32, query_len: i32) -> i64 ! { FFI, Unsafe };

pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { FFI, Unsafe } {
    return z3_check(input_ptr, input_len);
}
"#;

// SMT-LIB2 fixtures.
const SAT_QUERY: &[u8] = b"(declare-const x Int)(assert (> x 0))";
const UNSAT_QUERY: &[u8] = b"(declare-const x Int)(assert (> x 0))(assert (< x 0))";

fn z3_grants() -> IoGrants {
    IoGrants {
        z3: vec![Z3Grant::Solve],
        ..Default::default()
    }
}

fn run(source: &str, input: &[u8], grants: &IoGrants) -> Result<ToolResult, ToolError> {
    let compiled = compile_tool(source).expect("tool source should compile");
    execute_ephemeral(&compiled.wasm, input, FUEL_BUDGET, grants)
}

#[test]
fn sat_query_passes_through_the_boundary() {
    let r =
        run(PASSTHROUGH_TOOL, SAT_QUERY, &z3_grants()).expect("granted sat call should succeed");
    assert_eq!(r.output.len(), 1, "sat ⇒ packed 1 ⇒ 1-byte output");
}

#[test]
fn unsat_query_passes_through_the_boundary() {
    let r = run(PASSTHROUGH_TOOL, UNSAT_QUERY, &z3_grants())
        .expect("granted unsat call should succeed");
    assert!(r.output.is_empty(), "unsat ⇒ packed 0 ⇒ empty output");
}

#[test]
fn fail_closed_without_grant() {
    // NC2: no Z3 grant ⇒ -403, returned before any solver work.
    let err = run(PASSTHROUGH_TOOL, SAT_QUERY, &IoGrants::none())
        .expect_err("ungranted call must fail closed");
    assert!(
        err.to_string().contains("(403)"),
        "expected 403, got: {err}"
    );
}

#[test]
fn nul_byte_in_query_rejected_not_panicked() {
    // NC3: an interior NUL would panic z3's `from_string`; the shim rejects
    // it with -400 and the host does not abort (this test completing proves
    // no panic crossed the boundary).
    let mut q = b"(declare-const x Int)".to_vec();
    q.push(0);
    q.extend_from_slice(b"(assert (> x 0))");
    let err = run(PASSTHROUGH_TOOL, &q, &z3_grants()).expect_err("NUL query must be rejected");
    assert!(
        err.to_string().contains("(400)"),
        "expected 400, got: {err}"
    );
}

#[test]
fn invalid_utf8_query_rejected() {
    // NC3: non-UTF8 input ⇒ -400 (via the bounds-checked read's from_utf8).
    let err = run(PASSTHROUGH_TOOL, &[0xff, 0xfe, 0xfd], &z3_grants())
        .expect_err("bad utf8 must be rejected");
    assert!(
        err.to_string().contains("(400)"),
        "expected 400, got: {err}"
    );
}

#[test]
fn oversize_query_rejected() {
    // NC3: a query_len beyond the 1 MiB cap ⇒ -413, BEFORE any memory read.
    const BIG_LEN_TOOL: &str = r#"
#[ring(outer)] #[trusted]
module tool;
extern "C" fn z3_check(query_ptr: i32, query_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { FFI, Unsafe } {
    let big_len: i32 = 2000000;
    return z3_check(input_ptr, big_len);
}
"#;
    let err = run(BIG_LEN_TOOL, SAT_QUERY, &z3_grants()).expect_err("oversize must be rejected");
    assert!(
        err.to_string().contains("(413)"),
        "expected 413, got: {err}"
    );
}

#[test]
fn out_of_bounds_ptr_rejected_not_trapped() {
    // NC3: a wildly out-of-bounds pointer ⇒ -400 from the bounds-checked
    // read, never a host panic.
    const OOB_TOOL: &str = r#"
#[ring(outer)] #[trusted]
module tool;
extern "C" fn z3_check(query_ptr: i32, query_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { FFI, Unsafe } {
    let bad_ptr: i32 = 2000000000;
    return z3_check(bad_ptr, input_len);
}
"#;
    let err = run(OOB_TOOL, SAT_QUERY, &z3_grants()).expect_err("OOB ptr must be rejected");
    assert!(
        err.to_string().contains("(400)"),
        "expected 400, got: {err}"
    );
}

#[test]
fn deterministic_across_runs_through_boundary() {
    // NC4: identical verdict across repeated executions.
    for _ in 0..3 {
        let s = run(PASSTHROUGH_TOOL, SAT_QUERY, &z3_grants()).expect("sat");
        assert_eq!(s.output.len(), 1);
        let u = run(PASSTHROUGH_TOOL, UNSAT_QUERY, &z3_grants()).expect("unsat");
        assert!(u.output.is_empty());
    }
}
