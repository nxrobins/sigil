//! DEF-2b PR-7 — wasmtime round-trip for regions + `Vec::in_region(r)`.
//!
//! Compiles a `region NAME(LIMIT) { … }` block that builds a vector with
//! `Vec::in_region(NAME)` — exercising the PR-7 lexical-region-handle codegen (the handle
//! lowers to its inert `0` i64) end-to-end on the ephemeral runtime. Confirms the honesty
//! boundary AT RUNTIME: an in-region vector is an ordinary global-heap vector (it grows on
//! `push`, its elements read back correctly) that is reclaimed by its ENCLOSING lexical
//! region's `BUMP_PTR` save/restore (the DEF-2a PR-5 mechanism) — NOT a separate arena.
//!
//! A region value cannot escape its block and an outer `mut` cannot be assigned from inside
//! one, so the in-region computation is verified IN PLACE: each test reduces the vector to a
//! scalar `s` and then indexes `v.get((s - EXPECTED) * BIG)`, which is `get(0)` (valid) iff
//! `s == EXPECTED` and otherwise an out-of-bounds / negative index that TRAPS. The tool then
//! returns a fixed negative sentinel; recovering it proves both that the lexical handle
//! lowered + ran AND that the in-region vector's contents are correct.
//!
//! Harness mirrors `vec_runtime.rs`: inline the REAL `stdlib/sigil/vec.sigil` into
//! `module tool`, wrap `body` in `tool_main`, compile, run on the ephemeral runtime.

mod common;

const VEC: &str = include_str!("../../../stdlib/sigil/vec.sigil");

fn tool(body: &str) -> String {
    let defs = VEC.replace("\nmodule vec;\n", "\n");
    format!(
        "module tool;\n{defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// Compile + run a tool ending in `return 0 - <value>;`, recovering `<value>` from the
/// `ToolError::Trapped { "tool returned error (N)" }` negative sentinel. A runtime trap
/// from the in-place self-check has a DIFFERENT shape (no sentinel prefix) and panics here,
/// so an incorrect in-region computation fails the test rather than silently passing.
use common::run_returning_negative;

#[test]
fn in_region_vec_builds_pushes_and_reads_back() {
    // Build a vector with `Vec::in_region(buf)` inside `region buf`, push three values, and
    // sum them back through `get`. 10 + 20 + 12 == 42, verified in place: `get((s-42)*100)`
    // is `get(0)` iff the sum is 42, else a trap. Reaching the `-5` sentinel proves the
    // lexical handle `buf` lowered + ran and the in-region vector holds the right elements.
    let src = tool(
        "    region buf(256) {\n\
         \x20       let v: Vec<i64> = Vec::in_region(buf);\n\
         \x20       let a: i64 = v.push(10);\n\
         \x20       let b: i64 = v.push(20);\n\
         \x20       let c: i64 = v.push(12);\n\
         \x20       let s: i64 = v.get(0) + v.get(1) + v.get(2);\n\
         \x20       let _check: i64 = v.get((s - 42) * 100);\n\
         \x20   };\n\
         \x20   return 0 - 5;",
    );
    assert_eq!(
        run_returning_negative(&src),
        5,
        "in-region vec sum must be 42"
    );
}

#[test]
fn in_region_vec_grows_across_realloc() {
    // Push past the initial (zero) capacity so the in-region vector REALLOCATES its buffer
    // on the global heap (0 → 4 → 8 slots) — growth uses the global allocator exactly like
    // `new()`; the in_region `alloc` handle is inert. Pushes are UNROLLED because control
    // flow is not allowed inside a `region` body (T068). Sum of 1..=6 == 21, verified in
    // place.
    let src = tool(
        "    region buf(512) {\n\
         \x20       let v: Vec<i64> = Vec::in_region(buf);\n\
         \x20       let a: i64 = v.push(1);\n\
         \x20       let b: i64 = v.push(2);\n\
         \x20       let c: i64 = v.push(3);\n\
         \x20       let d: i64 = v.push(4);\n\
         \x20       let e: i64 = v.push(5);\n\
         \x20       let f: i64 = v.push(6);\n\
         \x20       let s: i64 = v.get(0) + v.get(1) + v.get(2) + v.get(3) + v.get(4) + v.get(5);\n\
         \x20       let _check: i64 = v.get((s - 21) * 100);\n\
         \x20   };\n\
         \x20   return 0 - 6;",
    );
    assert_eq!(run_returning_negative(&src), 6, "1..=6 summed must be 21");
}

#[test]
fn many_sequential_regions_run_under_reclamation() {
    // Open 100 regions in a loop, each building an in-region vector. Each `RegionEnd`
    // restores `BUMP_PTR` (DEF-2a PR-5), so the allocations are reclaimed and the loop runs
    // in BOUNDED memory; the in-region vector and the lexical handle behave identically
    // every iteration. Reaching the `-9` sentinel proves regions + in_region compose and
    // repeat. The loop driver is an OUTER literal-bounds for-range (control flow cannot
    // live inside a region body, T068; the region body is straight-line) — statically
    // bounded, so the WCC `recommended_budget` covers all 100 iterations and the test
    // runs at the compiler's own recommendation under fuel ENFORCEMENT (a `while` driver
    // keeps the floor budget and correctly fuel-traps here).
    let src = tool(
        "    for k in 0..100 {\n\
         \x20       region r(512) {\n\
         \x20           let v: Vec<i64> = Vec::in_region(r);\n\
         \x20           let _a: i64 = v.push(7);\n\
         \x20           let _b: i64 = v.push(9);\n\
         \x20           let _check: i64 = v.get((v.len() - 2) * 100);\n\
         \x20       };\n\
         \x20   }\n\
         \x20   return 0 - 9;",
    );
    assert_eq!(
        run_returning_negative(&src),
        9,
        "100 in-region loops must run to completion under reclamation"
    );
}
