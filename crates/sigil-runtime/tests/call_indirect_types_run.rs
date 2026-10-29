//! The modules `wasm::emit` used to crash on, run under the real host.
//!
//! A module that calls a closure-typed parameter without building a closure of that signature made
//! the emitter panic (`ICE: call_indirect signature not found in type map`). It now appends the
//! signature to the type section, and `sigil-compiler/tests/wasm_call_indirect_types.rs` pins that
//! entry. Here the repaired module, in each ring, goes to `execute_ephemeral`: wasmtime compiles
//! it, the runtime links its imports, and its entry point runs and echoes its input.
//!
//! What runs is the module, not the `call_indirect`: no SIGIL caller can reach it. A closure value
//! comes only from a closure literal (a named function is not a value), and lifting one gives the
//! module the very signature the bug needs to be missing.

use sigil_compiler::compile_module;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// The reported module plus an entry point that returns its input: `(ptr << 32) | len`.
const TOOL: &str = "module tool;\n\
    pub fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
    pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return input_ptr * 4294967296 + input_len; }\n";

/// The same module in the outer ring, where agent tools live: production emits it as the outer
/// module, beside an inner module with no functions.
const TOOL_OUTER: &str = "#[ring(outer)]\nmodule tool;\n\
    pub fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
    pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return input_ptr * 4294967296 + input_len; }\n";

const FUEL: u64 = 1_000_000;

fn run(wasm: &[u8]) -> Vec<u8> {
    execute_ephemeral(wasm, b"echo", FUEL, &IoGrants::none())
        .unwrap_or_else(|err| panic!("the repaired module runs: {err}"))
        .output
}

#[test]
fn repaired_inner_module_runs_under_the_ephemeral_host() {
    let compilation =
        compile_module(TOOL).unwrap_or_else(|err| panic!("the program is accepted: {err:?}"));
    assert!(compilation.wasm_outer.is_none());
    assert_eq!(run(&compilation.wasm_inner), b"echo");
}

#[test]
fn repaired_outer_module_runs_under_the_ephemeral_host() {
    let compilation =
        compile_module(TOOL_OUTER).unwrap_or_else(|err| panic!("the program is accepted: {err:?}"));
    let outer = compilation
        .wasm_outer
        .as_deref()
        .expect("an outer-ring program emits an outer module");
    assert_eq!(run(outer), b"echo");
}
