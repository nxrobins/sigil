//! Cross-module runtime tests for `Vec<T>` (PR C2).
//!
//! Unlike `vec_runtime.rs` (which INLINES vec.sigil into `module tool;`),
//! these keep vec.sigil as a sibling `module vec;`, so `Vec::new()` (an
//! associated fn) and `v.push()`/`v.get()`/`v.len()` (methods) resolve ACROSS
//! the module boundary via C2's global dispatch fallback — then run end to end.

mod common;

use sigil_compiler::compile_tool;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const VEC: &str = include_str!("../../../stdlib/sigil/vec.sigil");

/// Two-module source: the verbatim stdlib `module vec;` + a sibling
/// `module tool;` (vec.sigil is NOT inlined). Resolution of `Vec`'s members
/// from `tool` therefore exercises the cross-module path.
fn xmod_tool(body: &str) -> String {
    format!(
        "{VEC}\n\nmodule tool;\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

use common::run_returning_negative;

#[test]
fn xmod_push_get_len_round_trip() {
    // CF-C6: cross-module Vec must produce the SAME value as the same-module
    // suite (320) — layout/mangling is invariant across the boundary.
    let src = xmod_tool(
        "    let v: Vec<i64> = Vec::new();\n\
         \x20   let a: i64 = v.push(10);\n\
         \x20   let b: i64 = v.push(20);\n\
         \x20   let c: i64 = v.push(30);\n\
         \x20   return 0 - (v.get(1) + v.len() * 100);",
    );
    assert_eq!(run_returning_negative(&src), 320);
}

#[test]
fn xmod_growth_across_realloc() {
    // CF-C6: growth value matches same-module (129) across the boundary.
    let src = xmod_tool(
        "    let v: Vec<i64> = Vec::with_capacity(2);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 9 {\n\
         \x20       let n: i64 = v.push(i * 10);\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return 0 - (v.get(0) + v.get(4) + v.get(8) + v.len());",
    );
    assert_eq!(run_returning_negative(&src), 129);
}

#[test]
fn xmod_fuel_consumed_matches_same_module() {
    // CF-C5 (parity). SIGIL's fuel model charges per-function static cost, not
    // per-iteration, so a bounded loop never trips FuelExhausted (the original
    // "tight budget → exhaust" fail-fast is inapplicable to this model). The
    // achievable, correct claim is PARITY: the SAME loop compiled same-module
    // vs cross-module must consume the EXACT same fuel — proving cross-module
    // mono'd bodies carry identical FuelDecrements with no bypass. Returns a
    // positive `len` so `ToolResult.fuel_consumed` is readable.
    let body = "    let v: Vec<i64> = Vec::new();\n\
        \x20   let mut i: i64 = 0;\n\
        \x20   while i < 1000 {\n\
        \x20       let n: i64 = v.push(i);\n\
        \x20       i = i + 1;\n\
        \x20   }\n\
        \x20   return v.len();";
    // same-module: inline vec.sigil (strip its `module vec;`).
    let same_module = format!(
        "module tool;\n{}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n",
        VEC.replace("\nmodule vec;\n", "\n")
    );
    let cross_module = xmod_tool(body);
    let consumed = |src: &str| -> u64 {
        let r = compile_tool(src).expect("tool should compile");
        match execute_ephemeral(&r.wasm, b"", 100_000_000, &IoGrants::none()) {
            Ok(res) => res.fuel_consumed,
            other => panic!("expected Ok(ToolResult), got: {other:?}"),
        }
    };
    assert_eq!(
        consumed(&same_module),
        consumed(&cross_module),
        "CF-C5: cross-module fuel consumption must exactly equal same-module"
    );
}
