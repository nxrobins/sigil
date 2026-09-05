//! Phase 5a-4.5 regression tests for the wasm `Br`-depth fix.
//!
//! The bug these tests pin: when an AIR `Jump(loop_header)` is emitted
//! from inside one or more nested `if`/`else` blocks, the wasm emitter
//! used to unconditionally emit `Br(0)` — which targets the innermost
//! `if` (exiting it), not the enclosing `loop` (continuing it). After
//! exiting the if, control fell off the bottom of the loop body, and
//! since wasm `loop` blocks don't re-iterate on fall-through, the loop
//! terminated after a single iteration regardless of its condition.
//!
//! The fix tracks the wasm-block depth from each emission point to the
//! loop label and emits `Br(depth)`. These tests assert the post-fix
//! behavior. They WILL fail on the pre-fix codegen — both the
//! `_inside_if` and `_inside_nested_if_else` cases hit the bug; the
//! `_top_level` case never did, and is here as a positive control
//! (any change that breaks the simple case shows up alongside).
//!
//! Tracked in `memory/project_loop_br_depth_fix.md`.

mod common;

/// Compile + execute a tool whose `tool_main` returns a negative i64
/// (we use that as a sentinel-encoded counter — see test bodies).
/// Returns the magnitude of the negative return.
///
/// `execute_ephemeral` raises `ToolError::Trapped { message }` for any
/// negative i64 return, formatting it as `tool returned error (N)`.
/// We parse N back out so the test can assert the iteration count
/// directly.
use common::run_returning_negative;

/// Positive control: top-level mutation. Always worked. If this fails,
/// the regression is bigger than the bug we're fixing.
#[test]
fn loop_continue_top_level_iterates_correctly() {
    let source = r#"
module tool;

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut acc: i64 = 0;
    let mut k: i64 = 0;
    while k < 10 {
        acc = acc + 7;
        k = k + 1;
    }
    return 0 - acc;
}
"#;
    let code = run_returning_negative(source);
    assert_eq!(
        code, 70,
        "10 iterations × 7 = 70; got {code} (loop terminated early?)"
    );
}

/// The smoking-gun case: loop-var increment lives inside an if-then.
/// Pre-fix this returned -1 (single iteration). Post-fix returns -10.
#[test]
fn loop_continue_inside_if_iterates_correctly() {
    let source = r#"
module tool;

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut acc: i64 = 0;
    let mut k: i64 = 0;
    while k < 10 {
        acc = acc + 1;
        let dummy: i64 = 5;
        if dummy == 5 {
            k = k + 1;
        } else {
            return 0 - 999;
        }
    }
    return 0 - acc;
}
"#;
    let code = run_returning_negative(source);
    assert_eq!(
        code, 10,
        "loop with if-then-mutation must iterate 10 times; got {code} \
         (regression of the Br-depth fix?)"
    );
}

/// Same shape, but the increment is buried two levels deep — inside an
/// `if` inside an `else`. Depth 0 is the innermost if, depth 1 is the
/// outer if/else; the loop label is at depth 2 from here. The fix
/// must compute the right depth, not just +1.
#[test]
fn loop_continue_inside_nested_if_else_iterates_correctly() {
    let source = r#"
module tool;

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut acc: i64 = 0;
    let mut k: i64 = 0;
    while k < 5 {
        acc = acc + 1;
        let outer: i64 = 2;
        if outer == 1 {
            return 0 - 998;
        } else {
            let inner: i64 = 9;
            if inner == 9 {
                k = k + 1;
            } else {
                return 0 - 997;
            }
        }
    }
    return 0 - acc;
}
"#;
    let code = run_returning_negative(source);
    assert_eq!(
        code, 5,
        "loop with twice-nested if/else mutation must iterate 5 times; got {code}"
    );
}

/// Nested loops: the inner loop's increment-in-if must continue the
/// inner loop, NOT the outer. The outer loop runs O times, inner runs
/// I times for each outer, total I × O increments to acc.
#[test]
fn nested_loops_continue_correct_inner_loop() {
    let source = r#"
module tool;

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut acc: i64 = 0;
    let mut o: i64 = 0;
    while o < 3 {
        let mut i: i64 = 0;
        while i < 4 {
            acc = acc + 1;
            let g: i64 = 1;
            if g == 1 {
                i = i + 1;
            } else {
                return 0 - 996;
            }
        }
        o = o + 1;
    }
    return 0 - acc;
}
"#;
    let code = run_returning_negative(source);
    assert_eq!(code, 12, "3 outer × 4 inner = 12; got {code}");
}
