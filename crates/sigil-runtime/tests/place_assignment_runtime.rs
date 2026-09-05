//! Runtime tests for place-expression assignment (PR-1a).
//!
//! These compile real Sigil tools that mutate a record field or an array
//! element in place, execute them on the ephemeral wasm runtime, and read
//! the result back — proving the new `StoreField` / `StoreDynamic`
//! producers actually write the right slot. The out-of-bounds and
//! negative-index write tests pin CM1: an element write is bounds-trapped
//! exactly like the read, so an OOB write is a clean wasm trap, never
//! out-of-buffer memory corruption.
//!
//! Convention (shared with `wasm_loop_codegen.rs`): a tool that returns a
//! negative i64 trips `ToolError::Trapped { message: "tool returned error
//! (N)" }`; we parse `N` back out to assert a computed value. A genuine
//! bounds trap surfaces as a `Trapped` whose message is a raw wasm trap
//! (no "tool returned error" prefix), which lets us distinguish a real
//! trap from the sentinel.

mod common;

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Compile + run a tool that returns `0 - value`; recover `value`.
use common::run_returning_negative;

/// Assert that executing `source` traps via a genuine wasm bounds check
/// (the element-write `TrapIf`), NOT the negative-return sentinel and NOT
/// a clean return.
fn expect_bounds_trap(source: &str) {
    let result = compile_tool(source).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => assert!(
            !message.contains("tool returned error"),
            "expected a wasm bounds trap from the element write, but got the \
             negative-return sentinel — the OOB write was NOT trapped: {message}"
        ),
        Err(other) => panic!("expected a bounds Trapped, got: {other:?}"),
        Ok(_) => panic!(
            "expected the out-of-bounds element write to trap, but execution returned Ok \
             (the write landed out-of-buffer — memory corruption)"
        ),
    }
}

// ── Round-trips: the write lands at the right slot ───────────────────

#[test]
fn record_field_write_round_trips() {
    let source = r#"
module tool;
record Point { x: i64, y: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut p = Point { x: 3, y: 4 };
    p.x = 10;
    return 0 - p.x;
}
"#;
    assert_eq!(
        run_returning_negative(source),
        10,
        "p.x should read back as 10"
    );
}

#[test]
fn other_field_untouched_by_write() {
    // Writing `p.x` must not disturb `p.y` — proves the offset is right.
    let source = r#"
module tool;
record Point { x: i64, y: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut p = Point { x: 3, y: 4 };
    p.x = 10;
    return 0 - p.y;
}
"#;
    assert_eq!(run_returning_negative(source), 4, "p.y must stay 4");
}

#[test]
fn nested_field_write_round_trips() {
    let source = r#"
module tool;
record Inner { v: i64 }
record Outer { a: Inner, b: Inner }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut o = Outer { a: Inner { v: 1 }, b: Inner { v: 2 } };
    o.a.v = 99;
    return 0 - o.a.v;
}
"#;
    assert_eq!(
        run_returning_negative(source),
        99,
        "o.a.v should read back as 99"
    );
}

#[test]
fn array_element_write_round_trips() {
    let source = r#"
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut arr = [10, 20, 30];
    arr[1] = 99;
    return 0 - arr[1];
}
"#;
    assert_eq!(
        run_returning_negative(source),
        99,
        "arr[1] should read back as 99"
    );
}

#[test]
fn array_neighbor_untouched_by_write() {
    let source = r#"
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut arr = [10, 20, 30];
    arr[1] = 99;
    return 0 - arr[2];
}
"#;
    assert_eq!(run_returning_negative(source), 30, "arr[2] must stay 30");
}

// ── Compound load-op-store (CM2 single-evaluation, runtime side) ─────

#[test]
fn field_compound_round_trips() {
    let source = r#"
module tool;
record Point { x: i64, y: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut p = Point { x: 3, y: 4 };
    p.x += 7;
    return 0 - p.x;
}
"#;
    assert_eq!(run_returning_negative(source), 10, "3 + 7 = 10");
}

#[test]
fn index_compound_round_trips() {
    let source = r#"
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut arr = [10, 20, 30];
    arr[1] += 5;
    return 0 - arr[1];
}
"#;
    assert_eq!(run_returning_negative(source), 25, "20 + 5 = 25");
}

// ── CM1: element writes are bounds-trapped, mirroring the read ───────

#[test]
fn out_of_bounds_write_traps() {
    // A DYNAMIC out-of-range index: a constant `arr[5]` is now rejected at
    // compile time (T278), so the *runtime* element-write trap is exercised via
    // a variable index the compiler cannot const-fold.
    let source = r#"
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut arr = [10, 20, 30];
    let i: i64 = 5;
    arr[i] = 99;
    return 0;
}
"#;
    expect_bounds_trap(source);
}

#[test]
fn negative_index_write_traps() {
    // A negative i64 index wraps to a large u32 in the bounds compare, so
    // it is `>= len` and traps — never an out-of-buffer (underflow) write.
    let source = r#"
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut arr = [10, 20, 30];
    let i: i64 = 0 - 1;
    arr[i] = 99;
    return 0;
}
"#;
    expect_bounds_trap(source);
}

#[test]
fn in_bounds_write_at_last_index_ok() {
    // The boundary that must NOT trap: index == len - 1.
    let source = r#"
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut arr = [10, 20, 30];
    arr[2] = 99;
    return 0 - arr[2];
}
"#;
    assert_eq!(
        run_returning_negative(source),
        99,
        "arr[2] (last slot) must write cleanly"
    );
}

// ── Reference semantics: write-through a (non-mut) param propagates ───
//
// The runtime proof of the heap-pointer mutation model that backs
// `Vec::push`: SIGIL records are heap pointers, so passing one to a
// function passes the pointer (by value), and a field store inside the
// callee mutates the SHARED header the caller still holds. If records
// were copied at the call boundary this would read back the original
// value instead — so this test pins that in-place mutation through a
// receiver actually reaches the caller (the "single header" invariant).

#[test]
fn field_write_through_param_propagates_to_caller() {
    let source = r#"
module tool;
record Counter { n: i64 }
fn bump(c: Counter @Mut) -> i64 {
    c.n = c.n + 5;
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let c = Counter { n: 10 };
    let ignore: i64 = bump(c);
    return 0 - c.n;
}
"#;
    assert_eq!(
        run_returning_negative(source),
        15,
        "bump() mutated c.n through the shared header; caller must observe 15 \
         (records are heap pointers — in-place mutation propagates)"
    );
}
