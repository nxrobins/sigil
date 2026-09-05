//! Runtime tests for the stdlib typed arena `Arena<T>` (parser PR-0; see
//! `docs/specs/parser-in-sigil.md` §3).
//!
//! Each test compiles a `module tool` that uses `Arena` BARE — exercising the
//! ambient injection path (arena + transitive vec/option/result) exactly as the
//! SIGIL parser will — runs it on the ephemeral runtime, and reads the result
//! back via the negative-sentinel convention (`return 0 - v;` →
//! `Trapped { "tool returned error (v)" }`).
//!
//! The two load-bearing patterns for the parser are pinned here:
//! - the arena THREADS through a helper fn (`@Mut` param) and the caller
//!   observes the allocations (reference semantics) — the parser passes its
//!   arena through dozens of mutually-recursive parse helpers;
//! - a TREE builds bottom-up via NodeId back-references (children allocated
//!   first, the parent stores their ids, readers walk ids) — the AST shape.
//!
//! Trap convention (CF4 — validation-gated, never prose-gated): the
//! out-of-bounds test pairs the OOB run with a byte-identical in-bounds
//! CONTROL that must reach execution and return its sentinel. The control
//! proves the shared module validates; the OOB variant differs only by an
//! index constant, so its `Trapped` result (LACKING the sentinel prefix) is a
//! genuine runtime bounds trap, asserted structurally.

mod common;

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const FUEL: u64 = 10_000_000;

/// Compile + run a tool that ends in `return 0 - <value>;`, returning the
/// recovered `<value>`. Panics if the module fails to validate (a validation
/// failure's trap message lacks the sentinel prefix).
fn run_returning_negative(source: &str) -> i64 {
    common::run_returning_negative_with_fuel(source, FUEL)
}

fn tool(body: &str) -> String {
    format!(
        "module tool;\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

#[test]
fn arena_new_is_empty() {
    let src = tool(
        "    let a: Arena<i64> = Arena::new();\n\
         \x20   return 0 - (a.len() + 100);",
    );
    assert_eq!(run_returning_negative(&src), 100, "a fresh arena has len 0");
}

#[test]
fn allocate_returns_dense_sequential_ids() {
    // The n-th allocate returns n-1: ids 0, 1, 2.
    let src = tool(
        "    let mut a: Arena<i64> = Arena::new();\n\
         \x20   let i0: i64 = a.allocate(10);\n\
         \x20   let i1: i64 = a.allocate(20);\n\
         \x20   let i2: i64 = a.allocate(30);\n\
         \x20   return 0 - (i0 * 100 + i1 * 10 + i2 + 1000);",
    );
    // 0*100 + 1*10 + 2 + 1000 = 1012
    assert_eq!(run_returning_negative(&src), 1012);
}

#[test]
fn get_round_trips_values() {
    let src = tool(
        "    let mut a: Arena<i64> = Arena::new();\n\
         \x20   let i0: i64 = a.allocate(11);\n\
         \x20   let i1: i64 = a.allocate(22);\n\
         \x20   let i2: i64 = a.allocate(33);\n\
         \x20   return 0 - (a.get(0) + a.get(1) * 100 + a.get(2));",
    );
    // 11 + 2200 + 33 = 2244
    assert_eq!(run_returning_negative(&src), 2244);
}

#[test]
fn interleaved_allocate_and_get() {
    let src = tool(
        "    let mut a: Arena<i64> = Arena::new();\n\
         \x20   let i0: i64 = a.allocate(5);\n\
         \x20   let first: i64 = a.get(0);\n\
         \x20   let i1: i64 = a.allocate(7);\n\
         \x20   return 0 - (first * 100 + a.get(1) * 10 + a.len());",
    );
    // 500 + 70 + 2 = 572
    assert_eq!(run_returning_negative(&src), 572);
}

#[test]
fn arena_threads_through_a_helper_fn() {
    // The parser pattern: the arena passes through a helper as `@Mut`; the
    // helper's allocations are visible to the caller (records are
    // reference-semantic — one shared header).
    let src = "module tool;\n\n\
        fn fill(a: Arena<i64> @Mut) -> i64 ! { Alloc } {\n\
        \x20   let i0: i64 = a.allocate(41);\n\
        \x20   let i1: i64 = a.allocate(42);\n\
        \x20   return i1;\n\
        }\n\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let mut a: Arena<i64> = Arena::new();\n\
        \x20   let last: i64 = fill(a);\n\
        \x20   return 0 - (a.len() * 100 + a.get(1) + last);\n\
        }\n";
    // 200 + 42 + 1 = 243
    assert_eq!(run_returning_negative(src), 243);
}

#[test]
fn tree_builds_via_nodeid_back_references() {
    // The AST shape: leaves allocated first, the parent stores their ids,
    // readers walk parent → child ids (ET-P4's back-reference discipline).
    let src = "module tool;\n\n\
        record TNode { kind: i64, a: i64, b: i64 }\n\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let mut ar: Arena<TNode> = Arena::new();\n\
        \x20   let l: i64 = ar.allocate(TNode { kind: 1, a: 11, b: 0 - 1 });\n\
        \x20   let r: i64 = ar.allocate(TNode { kind: 1, a: 22, b: 0 - 1 });\n\
        \x20   let p: i64 = ar.allocate(TNode { kind: 2, a: l, b: r });\n\
        \x20   let parent: TNode = ar.get(p);\n\
        \x20   let left: TNode = ar.get(parent.a);\n\
        \x20   let right: TNode = ar.get(parent.b);\n\
        \x20   return 0 - (left.a + right.a + parent.kind * 1000);\n\
        }\n";
    // 11 + 22 + 2000 = 2033
    assert_eq!(run_returning_negative(src), 2033);
}

#[test]
fn arena_of_records_with_str_fields() {
    // The parser's actual Node shape: a record with i64 fields AND a str field,
    // stored in the arena (the lexer proved Vec<record-with-str>; this pins the
    // same through the Arena wrapper).
    let src = "module tool;\n\n\
        record PNode { kind: i64, start: i64, end: i64, name: str }\n\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let mut a: Arena<PNode> = Arena::new();\n\
        \x20   let i0: i64 = a.allocate(PNode { kind: 7, start: 0, end: 3, name: \"foo\" });\n\
        \x20   let i1: i64 = a.allocate(PNode { kind: 9, start: 4, end: 10, name: \"barbaz\" });\n\
        \x20   let n0: PNode = a.get(0);\n\
        \x20   let n1: PNode = a.get(1);\n\
        \x20   return 0 - (n0.kind * 1000 + n1.kind * 100 + n1.name.len());\n\
        }\n";
    // 7000 + 900 + 6 = 7906
    assert_eq!(run_returning_negative(src), 7906);
}

#[test]
fn set_patches_an_element_in_place() {
    // The parser's literal-fold pattern: rewrite an allocated element without
    // allocating a replacement (no orphan, ET-P4). `set` echoes the id.
    let src = tool(
        "    let mut a: Arena<i64> = Arena::new();\n\
         \x20   let i0: i64 = a.allocate(11);\n\
         \x20   let i1: i64 = a.allocate(22);\n\
         \x20   let echoed: i64 = a.set(1, 99);\n\
         \x20   return 0 - (a.get(0) * 1000 + a.get(1) + echoed * 10 + a.len());",
    );
    // 11000 + 99 + 10 + 2 = 11111
    assert_eq!(run_returning_negative(&src), 11111);
}

#[test]
fn get_out_of_bounds_traps_with_in_bounds_control() {
    // CF4: the control (index 1, in-bounds) proves the module validates and
    // executes; the OOB variant differs ONLY by the index constant (2 == len),
    // so its non-sentinel Trapped is a genuine runtime bounds trap.
    let make = |idx: i64| {
        tool(&format!(
            "    let mut a: Arena<i64> = Arena::new();\n\
             \x20   let i0: i64 = a.allocate(11);\n\
             \x20   let i1: i64 = a.allocate(22);\n\
             \x20   return 0 - a.get({idx});"
        ))
    };
    // Control: in-bounds get returns its sentinel.
    assert_eq!(run_returning_negative(&make(1)), 22, "in-bounds control");
    // OOB: index 2 == len → the LEN-bounded read traps (no sentinel prefix).
    let compiled = compile_tool(&make(2)).expect("OOB variant compiles (differs by a constant)");
    match execute_ephemeral(&compiled.wasm, b"", FUEL, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            assert!(
                !message.contains("tool returned error ("),
                "OOB get must be a genuine bounds trap, not a sentinel return: {message}"
            );
        }
        other => panic!("OOB get must trap, got {other:?}"),
    }
}
