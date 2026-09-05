//! Runtime tests for the growable stdlib `Vec<T>` (PR B).
//!
//! Each test concatenates the real `stdlib/sigil/vec.sigil` with a small
//! `module tool` that uses it, compiles to wasm, runs it on the ephemeral
//! runtime, and reads the result back. This exercises the actual stdlib
//! source (not a reimplementation) end-to-end: the `vec_load`/`vec_store`
//! intrinsics, the bounds trap, growth-across-realloc, in-place header
//! mutation, and reference semantics across a call. (Element type scope is
//! `i64`; see the note above `push_through_non_mut_param_mutates_caller`.)
//!
//! Value convention (shared with `wasm_loop_codegen.rs`): a tool that
//! returns a negative i64 trips `ToolError::Trapped { "tool returned error
//! (N)" }`; `run_returning_negative` parses `N` back to assert a value.
//!
//! Trap convention (CF4 — validation-gated, never prose-gated): a bounds
//! trap is asserted by `assert_get_traps`, which pairs the out-of-bounds run
//! with a byte-identical in-bounds *control* that must reach execution and
//! return `Ok`. The control proves the shared module VALIDATES; the OOB
//! variant differs only by an index constant, so it validates too —
//! therefore its `Trapped` result is a genuine runtime trap, asserted
//! structurally (`matches!`) without reading any wasmtime error text.

mod common;

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const VEC: &str = include_str!("../../../stdlib/sigil/vec.sigil");

/// Inline the REAL vec.sigil definitions into `module tool` (strip its own
/// `module vec;` line) and wrap `body` in `tool_main`. This exercises the
/// actual stdlib source — record, constructors, impl methods, intrinsics,
/// growth — with same-module resolution. Cross-module / bare-`Vec`
/// availability (like Option/Result) is PR C's job (ambient auto-injection);
/// these tests isolate the vector's own behavior (AG1).
fn tool(body: &str) -> String {
    let defs = VEC.replace("\nmodule vec;\n", "\n");
    format!(
        "module tool;\n{defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// Compile + run a tool that ends in `return 0 - <value>;`, returning the
/// recovered `<value>`. Panics (not silently passes) if the module fails to
/// validate — the trap message of a validation failure lacks the
/// "tool returned error (" prefix, so the `find` below fires the panic.
use common::run_returning_negative;

/// CF4: assert that `v.get(oob_index)` traps at runtime, gated on validation
/// rather than on wasmtime's error prose.
///
/// `setup` builds and populates `v`. We then build two tool bodies that
/// differ ONLY in the index constant passed to `get`:
///   - control (`in_bounds_index`): must validate AND reach `return` → `Ok`.
///   - oob (`oob_index`): the module is structurally identical, so it
///     validates too; the `get` therefore traps at runtime → `Trapped`.
///
/// Because the control proves validation, a `Trapped` from the OOB run can
/// only be a runtime bounds trap — asserted via `matches!`, reading zero
/// bytes of the error message. `return probe - probe` yields 0 (a clean
/// `Ok`) when the `get` does NOT trap, so a missing trap fails the assert
/// instead of masquerading as the negative sentinel.
fn assert_get_traps(setup: &str, in_bounds_index: &str, oob_index: &str) {
    let body = |idx: &str| {
        format!("{setup}\n    let probe: i64 = v.get({idx});\n    return probe - probe;")
    };

    let control = compile_tool(&tool(&body(in_bounds_index))).expect("control should compile");
    let cres = execute_ephemeral(&control.wasm, b"", control.fuel_budget, &IoGrants::none());
    assert!(
        cres.is_ok(),
        "in-bounds control get({in_bounds_index}) must validate and reach execution, got: {cres:?}"
    );

    let oob = compile_tool(&tool(&body(oob_index))).expect("oob should compile");
    let ores = execute_ephemeral(&oob.wasm, b"", oob.fuel_budget, &IoGrants::none());
    assert!(
        matches!(ores, Err(ToolError::Trapped { .. })),
        "out-of-bounds get({oob_index}) must trap at runtime (control validated), got: {ores:?}"
    );
}

/// `Vec::set` analogue of `assert_get_traps`: the body ends in `v.set(idx, 7)`,
/// then a clean `return probe - probe` (== 0). The in-bounds control must
/// validate AND reach Ok; the oob variant differs only by the index constant,
/// so its `Trapped` is the runtime bound trap (`set` shares `get`'s
/// `emit_vec_bound_trap`, bound = `count`).
fn assert_set_traps(setup: &str, in_bounds_index: &str, oob_index: &str) {
    let body = |idx: &str| {
        format!(
            "{setup}\n    v.set({idx}, 7);\n    let probe: i64 = v.get(0);\n    return probe - probe;"
        )
    };
    let control = compile_tool(&tool(&body(in_bounds_index))).expect("control should compile");
    let cres = execute_ephemeral(&control.wasm, b"", control.fuel_budget, &IoGrants::none());
    assert!(
        cres.is_ok(),
        "in-bounds set({in_bounds_index}) must validate and reach execution, got: {cres:?}"
    );
    let oob = compile_tool(&tool(&body(oob_index))).expect("oob should compile");
    let ores = execute_ephemeral(&oob.wasm, b"", oob.fuel_budget, &IoGrants::none());
    assert!(
        matches!(ores, Err(ToolError::Trapped { .. })),
        "out-of-bounds set({oob_index}) must trap at runtime (control validated), got: {ores:?}"
    );
}

#[test]
fn push_get_len_round_trip() {
    let src = tool(
        "    let v: Vec<i64> = Vec::new();\n\
         \x20   let a: i64 = v.push(10);\n\
         \x20   let b: i64 = v.push(20);\n\
         \x20   let c: i64 = v.push(30);\n\
         \x20   return 0 - (v.get(1) + v.len() * 100);",
    );
    // v.get(1) == 20, v.len() == 3 → 20 + 300 = 320.
    assert_eq!(run_returning_negative(&src), 320);
}

#[test]
fn growth_across_realloc_preserves_data() {
    // CF5: start at capacity 2, push 9 → grows 2→4→8→16 (three reallocs).
    // Every earlier element must survive each copy + `self.buf` write-through.
    // Read the boundary indices 0, ⌊len/2⌋=4, len-1=8.
    let src = tool(
        "    let v: Vec<i64> = Vec::with_capacity(2);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 9 {\n\
         \x20       let n: i64 = v.push(i * 10);\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return 0 - (v.get(0) + v.get(4) + v.get(8) + v.len());",
    );
    // get(0)=0, get(4)=40, get(8)=80, len=9 → 0 + 40 + 80 + 9 = 129.
    assert_eq!(run_returning_negative(&src), 129);
}

// PR #132: `Vec<i32>` / `Vec<bool>` now work — a literal argument narrows to
// the element width at the call site. Values are checked via comparisons (not
// the i64 sentinel arithmetic), because an i32/bool `get` result can't be
// summed with the i64 `len`.

#[test]
fn push_get_i32_round_trip() {
    // A large i32 (> 16 bits) round-trips through the 4-byte slot.
    let src = tool(
        "    let v: Vec<i32> = Vec::new();\n\
         \x20   let a: i64 = v.push(1000000);\n\
         \x20   let b: i64 = v.push(7);\n\
         \x20   let x: i32 = v.get(0);\n\
         \x20   let y: i32 = v.get(1);\n\
         \x20   if x == 1000000 {\n\
         \x20       if y == 7 {\n\
         \x20           return 0 - 42;\n\
         \x20       } else {\n\
         \x20           return 0 - 1;\n\
         \x20       }\n\
         \x20   } else {\n\
         \x20       return 0 - 2;\n\
         \x20   }",
    );
    assert_eq!(run_returning_negative(&src), 42);
}

#[test]
fn growth_i32_preserves_values() {
    // cap 2, push 9 i32 values (three reallocs); read boundaries 0/4/8.
    let src = tool(
        "    let v: Vec<i32> = Vec::with_capacity(2);\n\
         \x20   let mut i: i32 = 0;\n\
         \x20   while i < 9 {\n\
         \x20       let n: i64 = v.push(i * 10);\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   let a: i32 = v.get(0);\n\
         \x20   let e: i32 = v.get(4);\n\
         \x20   let h: i32 = v.get(8);\n\
         \x20   if a == 0 {\n\
         \x20       if e == 40 {\n\
         \x20           if h == 80 {\n\
         \x20               return 0 - 55;\n\
         \x20           } else {\n\
         \x20               return 0 - 1;\n\
         \x20           }\n\
         \x20       } else {\n\
         \x20           return 0 - 2;\n\
         \x20       }\n\
         \x20   } else {\n\
         \x20       return 0 - 3;\n\
         \x20   }",
    );
    assert_eq!(run_returning_negative(&src), 55);
}

#[test]
fn push_get_bool_round_trip() {
    // AG-I3: bool is verified empirically. `true`/`false` are `Literal::Bool`
    // (never `IntLit`); the 8-byte slot stores the truth value.
    let src = tool(
        "    let v: Vec<bool> = Vec::new();\n\
         \x20   let a: i64 = v.push(true);\n\
         \x20   let b: i64 = v.push(false);\n\
         \x20   let x: bool = v.get(0);\n\
         \x20   let y: bool = v.get(1);\n\
         \x20   if x {\n\
         \x20       if y {\n\
         \x20           return 0 - 1;\n\
         \x20       } else {\n\
         \x20           return 0 - 77;\n\
         \x20       }\n\
         \x20   } else {\n\
         \x20       return 0 - 2;\n\
         \x20   }",
    );
    assert_eq!(run_returning_negative(&src), 77); // x=true, y=false
}

#[test]
fn push_through_mut_param_mutates_caller() {
    // Reference semantics: a Vec is a heap pointer, so pushing through a
    // `@Mut` `Vec` param mutates the caller's single shared header.
    // After fill() pushes two, the caller observes len 2 and the elements.
    let defs = VEC.replace("\nmodule vec;\n", "\n");
    let src = format!(
        "module tool;\n{defs}\n\n\
         fn fill(v: Vec<i64> @Mut) -> i64 ! {{ Alloc }} {{\n\
         \x20   let a: i64 = v.push(100);\n\
         \x20   let b: i64 = v.push(200);\n\
         \x20   return v.len();\n\
         }}\n\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         \x20   let v: Vec<i64> = Vec::new();\n\
         \x20   let n: i64 = fill(v);\n\
         \x20   return 0 - (v.len() + v.get(1));\n\
         }}\n"
    );
    // caller sees len 2 + get(1) 200 = 202.
    assert_eq!(run_returning_negative(&src), 202);
}

#[test]
fn get_out_of_bounds_traps() {
    // One element pushed (len 1); get(5) is past the buffer entirely.
    assert_get_traps(
        "    let v: Vec<i64> = Vec::new();\n    let a: i64 = v.push(7);",
        "0",
        "5",
    );
}

#[test]
fn get_at_len_traps_not_uninitialized() {
    // cap grows to 4 on first push, but len is 1 — get(1) is in-capacity yet
    // past len. It MUST trap (len-bounded), not return an uninitialized slot.
    assert_get_traps(
        "    let v: Vec<i64> = Vec::new();\n    let a: i64 = v.push(99);",
        "0",
        "1",
    );
}

// ── Suite hardening (post-#147): calling-convention + bound-edge probes ──
// Five scenarios that exercise code paths the round-trip/growth tests above
// don't: the empty (len==0) bound edge, the negative-index wrap, the Vec
// header crossing a call boundary in BOTH directions (arg + return), and the
// first realloc from an exactly-full buffer.

#[test]
fn empty_vec_get_traps() {
    // len==0 straight out of `Vec::new()` (no push): `get(0)` must trap —
    // the bound is `count`, and `0 >= 0` trips the u32 bound trap BEFORE any
    // load. Verified the same validation-gated way as `assert_get_traps`: the
    // control pushes one element so `get(0)` is in-bounds and returns Ok
    // (proving the module VALIDATES), and the no-push variant differs only by
    // the absent push — so its `Trapped` is a genuine runtime bound trap, not
    // a validation failure. (The shared helper needs an in-bounds index, which
    // an empty Vec has none of, hence the explicit control here.)
    let oob = compile_tool(&tool(
        "    let v: Vec<i64> = Vec::new();\n    let p: i64 = v.get(0);\n    return p - p;",
    ))
    .expect("empty-get module should compile");
    let ores = execute_ephemeral(&oob.wasm, b"", oob.fuel_budget, &IoGrants::none());
    assert!(
        matches!(ores, Err(ToolError::Trapped { .. })),
        "get(0) on an empty Vec must trap (len==0), got: {ores:?}"
    );

    let control = compile_tool(&tool(
        "    let v: Vec<i64> = Vec::new();\n    let a: i64 = v.push(7);\n    let p: i64 = v.get(0);\n    return p - p;",
    ))
    .expect("control should compile");
    let cres = execute_ephemeral(&control.wasm, b"", control.fuel_budget, &IoGrants::none());
    assert!(
        cres.is_ok(),
        "in-bounds control get(0) after one push must validate and return Ok, got: {cres:?}"
    );
}

#[test]
fn negative_index_get_traps() {
    // `get(-1)` must trap, NOT read `buf - 8`. `emit_vec_bound_trap`
    // (air.rs) WrapI64's both operands to u32, so the i64 `-1` becomes
    // 0xFFFFFFFF, which is `>= count` under the UNSIGNED compare — the trap
    // fires. The in-bounds `0` control proves validation, so the `0 - 1`
    // variant's `Trapped` is the runtime bound trap.
    assert_get_traps(
        "    let v: Vec<i64> = Vec::new();\n    let a: i64 = v.push(7);",
        "0",
        "0 - 1",
    );
}

#[test]
fn push_into_prepopulated_arg_appends_for_caller() {
    // Stronger than `push_through_mut_param`: the caller pushes FIRST,
    // then the callee appends through the `@Mut` param. The caller must
    // observe BOTH its own element and the callee's — proving the LIVE header
    // (buf + count, mid-mutation) round-trips through the call boundary, not
    // just a freshly-constructed empty Vec.
    let defs = VEC.replace("\nmodule vec;\n", "\n");
    let src = format!(
        "module tool;\n{defs}\n\n\
         fn append_two(v: Vec<i64> @Mut) -> i64 ! {{ Alloc }} {{\n\
         \x20   let a: i64 = v.push(20);\n\
         \x20   let b: i64 = v.push(30);\n\
         \x20   return v.len();\n\
         }}\n\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         \x20   let v: Vec<i64> = Vec::new();\n\
         \x20   let f: i64 = v.push(10);\n\
         \x20   let n: i64 = append_two(v);\n\
         \x20   return 0 - (v.len() * 100 + v.get(0) + v.get(2));\n\
         }}\n"
    );
    // caller sees len 3, get(0)=10 (its own), get(2)=30 (callee's 2nd) →
    // 300 + 10 + 30 = 340.
    assert_eq!(run_returning_negative(&src), 340);
}

#[test]
fn vec_returned_from_factory_survives_teardown() {
    // Factory pattern: a function creates, fills, and RETURNS a Vec. The heap
    // header pointer must survive the callee's stack-frame teardown and the
    // i64 return-value calling convention (a code path no other test covers —
    // every other test constructs the Vec in `tool_main`). Caller reads back
    // exactly what the factory pushed.
    let defs = VEC.replace("\nmodule vec;\n", "\n");
    let src = format!(
        "module tool;\n{defs}\n\n\
         fn make_vec() -> Vec<i64> ! {{ Alloc }} {{\n\
         \x20   let v: Vec<i64> = Vec::new();\n\
         \x20   let a: i64 = v.push(11);\n\
         \x20   let b: i64 = v.push(22);\n\
         \x20   let c: i64 = v.push(33);\n\
         \x20   return v;\n\
         }}\n\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         \x20   let v: Vec<i64> = make_vec();\n\
         \x20   return 0 - (v.len() * 100 + v.get(0) + v.get(2));\n\
         }}\n"
    );
    // len 3, get(0)=11, get(2)=33 → 300 + 11 + 33 = 344.
    assert_eq!(run_returning_negative(&src), 344);
}

#[test]
fn push_past_exact_capacity_reallocs_from_full() {
    // `with_capacity(4)`: push exactly 4 (count reaches slots WITHOUT a
    // realloc — the grow guard `count == slots` is checked BEFORE the store,
    // so it never fires while filling), then a 5th push hits count==slots==4
    // and forces the first doubling (4→8). All five values — the four copied
    // across the realloc and the freshly-stored fifth — must read back intact,
    // and capacity must reflect the single doubling.
    let src = tool(
        "    let v: Vec<i64> = Vec::with_capacity(4);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 5 {\n\
         \x20       let n: i64 = v.push(i * 11);\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return 0 - (v.get(0) + v.get(3) + v.get(4) + v.len() + v.capacity());",
    );
    // get(0)=0, get(3)=33, get(4)=44, len=5, cap=8 (doubled from 4) →
    // 0 + 33 + 44 + 5 + 8 = 90.
    assert_eq!(run_returning_negative(&src), 90);
}

// ── Vec::set (indexed write — the write-dual of get; Map prerequisite) ──

#[test]
fn set_overwrites_in_bounds() {
    // `set` overwrites a live cell in place; neighbours and len are untouched.
    // Also the first end-to-end exercise of a unit-returning generic method
    // called in statement position.
    let src = tool(
        "    let v: Vec<i64> = Vec::new();\n\
         \x20   let a: i64 = v.push(10);\n\
         \x20   let b: i64 = v.push(20);\n\
         \x20   let c: i64 = v.push(30);\n\
         \x20   v.set(1, 99);\n\
         \x20   return 0 - (v.get(0) + v.get(1) + v.get(2) + v.len());",
    );
    // get(0)=10, get(1)=99 (overwritten), get(2)=30, len=3 → 10+99+30+3 = 142.
    assert_eq!(run_returning_negative(&src), 142);
}

#[test]
fn set_at_len_traps() {
    // len 1 (cap 4 after one push); set(1) is past len → traps (write-dual of
    // get's len bound). set(0) is in-bounds and validates the module.
    assert_set_traps(
        "    let v: Vec<i64> = Vec::new();\n    let a: i64 = v.push(7);",
        "0",
        "1",
    );
}

#[test]
fn set_negative_index_traps() {
    // set(-1): the i64 -1 wraps to u32 0xFFFFFFFF >= count → traps (same u32
    // bound as get), never a buf-8 write. set(0) control validates.
    assert_set_traps(
        "    let v: Vec<i64> = Vec::new();\n    let a: i64 = v.push(7);",
        "0",
        "0 - 1",
    );
}
