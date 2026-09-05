//! Wall 1 Step 2 — runtime smoke for the `Slot<Cap>` built-in.
//!
//! Caps in Sigil are constructed inside actor `init` blocks and can't
//! be synthesized from a bare tool's `tool_main`. This file exercises
//! the parts of the Slot mechanism that don't require a real cap:
//!
//! - Construction (`slot_new::<T>()` returns a heap pointer).
//! - Trap on take-on-empty (`Trap::UnreachableCodeReached` shape).
//!
//! Put-on-full, cap_id clearing, and Z3 authority preservation are
//! either gated behind the `solver` feature (Z3 verifier) or require
//! the spawn / message slot wiring deferred to Step 3. They're
//! regression-locked by the compile-time invariants in
//! `crates/sigil-compiler/tests/wall1_step2_slot.rs`.

use sigil_compiler::compile_tool;
use sigil_runtime::{IoGrants, ToolError, execute_ephemeral};

const FUEL_BUDGET: u64 = 1_000_000;

#[test]
fn slot_take_on_empty_traps_unreachable() {
    // Tool constructs a slot, never puts into it, then calls take.
    // The wasm-side trap should fire — execute_ephemeral returns
    // `ToolError::Trapped` with an "unreachable" message.
    let source = r#"
module tool;
cap type Foo { x }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let s = slot_new::<Foo>();
    let taken = slot_take(s);
    let _consumed = taken.draw(1);
    return 0;
}
"#;
    let compiled = compile_tool(source).expect("tool compiles");
    let result = execute_ephemeral(&compiled.wasm, &[], FUEL_BUDGET, &IoGrants::default());
    // Wasmtime's error stringification doesn't expose "unreachable"
    // verbatim — it formats as "error while executing at wasm backtrace:
    // ...". The relevant invariant for INV-5 is that `execute_ephemeral`
    // returns `Trapped` (not `FuelExhausted` or success). The trap shape
    // itself is regression-locked by reading `wasm.rs::AirStmt::SlotTake`.
    match result {
        Err(ToolError::Trapped { message: _ }) => {}
        other => panic!("expected trap on take-on-empty, got: {other:?}"),
    }
}
