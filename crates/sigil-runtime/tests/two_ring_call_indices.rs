//! P2B-TWORING — end-to-end: a two-ring program whose calls live in the ring that does NOT
//! occupy the global-id prefix returns the value the source names. Before the per-ring index
//! map and the global-id-indexed table in `wasm::emit`, every one of these either failed to
//! instantiate, trapped, or (the two same-signature shapes) ran a DIFFERENT function than the
//! one named and returned its value. `crates/sigil-compiler/tests/wasm_two_ring_indices.rs`
//! holds the static call-index and table-slot checkers and their anti-stubs; this file is the
//! runtime witness.
//!
//! Result convention (shared with the other runtime suites): the tool ends in
//! `return 0 - <value>;`, which traps as `tool returned error (<value>)`.

mod common;

use sigil_compiler::compile_module;
use sigil_runtime::RuntimeHost;

/// Inner module first; the outer tool calls an outer helper.
#[test]
fn inner_first_outer_call_returns_the_named_callees_value() {
    let src = "module first;\n\
        fn dummy() -> i64 { return 0; }\n\
        #[ring(outer)]\nmodule tool;\n\
        fn helper(x: i64) -> i64 { return x + 40; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let v: i64 = helper(2); return 0 - v; }\n";
    assert_eq!(common::run_returning_negative(src), 42);
}

/// The same-signature neighbour: `plus_one(1)` must return 2, never `times_hundred`'s 100.
#[test]
fn inner_first_same_signature_neighbour_is_not_invoked() {
    let src = "module first;\n\
        fn dummy() -> i64 { return 0; }\n\
        #[ring(outer)]\nmodule tool;\n\
        fn plus_one(x: i64) -> i64 { return x + 1; }\n\
        fn times_hundred(x: i64) -> i64 { return x * 100; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let v: i64 = plus_one(1); return 0 - v; }\n";
    assert_eq!(common::run_returning_negative(src), 2);
}

/// A closure in the outer ring behind two inner functions: its stored global id is a slot of
/// the (program-sized) table and that slot holds the closure.
#[test]
fn inner_first_outer_closure_calls_through_the_ring_table() {
    let src = "module first;\n\
        fn dummy() -> i64 { return 0; }\n\
        fn dummy2() -> i64 { return 1; }\n\
        #[ring(outer)]\nmodule tool;\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { \
            let f = fn(x: i64) -> i64 { return x + 1; }; let v: i64 = f(41); return 0 - v; }\n";
    assert_eq!(common::run_returning_negative(src), 42);
}

/// The same-signature closure neighbour: `a(1)` must return 2, never `b`'s 100 (the old
/// compact outer table held `b` at `a`'s stored global id).
#[test]
fn inner_first_same_signature_closure_neighbour_is_not_invoked() {
    let src = "module first;\n\
        fn dummy() -> i64 { return 0; }\n\
        #[ring(outer)]\nmodule tool;\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { \
            let a = fn(x: i64) -> i64 { return x + 1; }; \
            let b = fn(x: i64) -> i64 { return x * 100; }; \
            let v: i64 = a(1); return 0 - v; }\n";
    assert_eq!(common::run_returning_negative(src), 2);
}

/// The mirror: outer module first, an inner tool calls an inner helper.
#[test]
fn outer_first_inner_call_returns_the_named_callees_value() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        fn dummy() -> i64 { return 0; }\n\
        module app;\n\
        fn helper(x: i64) -> i64 { return x + 40; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let v: i64 = helper(2); return 0 - v; }\n";
    assert_eq!(common::run_returning_negative(src), 42);
}

/// Actor handlers are inner-only; with an outer module first the boot `Start` must deliver
/// and its call to the inner helper must return the named value (a mismatch traps).
#[test]
fn outer_first_actor_handler_calls_the_named_inner_helper() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        fn dummy() -> i64 { return 0; }\n\
        module app;\n\
        fn helper(x: i64) -> i64 { return x + 40; }\n\
        entry actor Main {\n\
          on Start() -> i64 { let v: i64 = helper(2); if v != 42 { trap(); } return 0; }\n\
        }\n";
    let compilation = compile_module(src).unwrap_or_else(|e| panic!("compile: {e:?}"));
    assert!(compilation.wasm_outer.is_some(), "the fixture is two-ring");
    let mut host = RuntimeHost::new(compilation.fuel_budget);
    host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
        .unwrap_or_else(|e| panic!("bootstrap: {e:?}"));
    let delivered = host
        .drain_messages(32)
        .unwrap_or_else(|e| panic!("drain: {e:?}"));
    assert_eq!(delivered, 1, "the boot Start delivers without trapping");
}
