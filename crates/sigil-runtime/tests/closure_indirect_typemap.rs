//! Regression: `call_indirect` must reference the wasm type matching the
//! closure's signature.
//!
//! The wasm type section emits ONE entry per function at a sequential index,
//! but `type_map` (used ONLY for `call_indirect` type lookup) was built with a
//! dedup that DID NOT advance the index on a repeated signature — while the
//! section still grew. So as soon as a program had two functions with the same
//! signature, every later `type_map` index pointed one slot before its real
//! type entry, and a closure `call_indirect` resolved to the wrong type. A
//! bool-returning or 2-arg closure then produced a wasm `type mismatch`
//! ("expected i32, found i64") that wasmtime rejects at compile time.
//!
//! These programs are crafted to contain duplicate-signature functions BEFORE a
//! non-`(i64)->i64` closure call, so they reproduce the drift; each asserts the
//! exact runtime value (the three differentials check types/nodes, not bytes).

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

fn neg(src: &str) -> i64 {
    let result = compile_tool(src).expect("module should compile");
    match execute_ephemeral(
        &result.wasm,
        b"",
        result.fuel_budget.max(1_000_000_000),
        &IoGrants::none(),
    ) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            let s = message
                .find(p)
                .unwrap_or_else(|| panic!("no sentinel in: {message}"))
                + p.len();
            let e = message[s..].find(')').unwrap();
            message[s..s + e].parse().unwrap()
        }
        other => panic!("expected sentinel trap, got {other:?}"),
    }
}

// Two functions share signature `(i64)->i64` (the dedup trigger), THEN a
// bool-returning closure is invoked indirectly. Pre-fix: invalid wasm.
// 1 + 2 + 100 = 103.
#[test]
fn dup_sig_then_bool_closure() {
    let src = "module tool;\n\
        fn id_a(x: i64) -> i64 { return x; }\n\
        fn id_b(x: i64) -> i64 { return x + 0; }\n\
        fn apply_pred(p: Fn(i64) -> bool, x: i64) -> i64 {\n\
        \x20   if p(x) { return 100; } else { return 200; }\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let r1: i64 = id_a(1);\n\
        \x20   let r2: i64 = id_b(2);\n\
        \x20   let r3: i64 = apply_pred(fn(z: i64) -> bool { return z > 0; }, 5);\n\
        \x20   return 0 - (r1 + r2 + r3);\n\
        }\n";
    assert_eq!(neg(src), 103);
}

// Duplicate signature, THEN a 2-arg closure invoked indirectly. 10 - 3 = 7.
#[test]
fn dup_sig_then_two_arg_closure() {
    let src = "module tool;\n\
        fn id_a(x: i64) -> i64 { return x; }\n\
        fn id_b(x: i64) -> i64 { return x + 0; }\n\
        fn comb(g: Fn(i64, i64) -> i64, a: i64, b: i64) -> i64 { return g(a, b); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let _u: i64 = id_a(1) + id_b(2);\n\
        \x20   return 0 - comb(fn(a: i64, b: i64) -> i64 { return a - b; }, 10, 3);\n\
        }\n";
    assert_eq!(neg(src), 7);
}

// A capturing bool-closure after duplicate sigs (combines with the closure-env
// path). k=4 captured; 5 > 4 → true → 1.
#[test]
fn dup_sig_then_capturing_bool_closure() {
    let src = "module tool;\n\
        fn id_a(x: i64) -> i64 { return x; }\n\
        fn id_b(x: i64) -> i64 { return x + 0; }\n\
        fn apply_pred(p: Fn(i64) -> bool, x: i64) -> i64 {\n\
        \x20   if p(x) { return 1; } else { return 0; }\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let _u: i64 = id_a(1) + id_b(2);\n\
        \x20   let k: i64 = 4;\n\
        \x20   return 0 - apply_pred(fn(z: i64) -> bool { return z > k; }, 5);\n\
        }\n";
    assert_eq!(neg(src), 1);
}
