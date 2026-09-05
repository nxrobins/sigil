//! Adversarial stress suite for the merged `Vec<T>` (post-PR-C).
//!
//! These tests try to BREAK Vec end-to-end through the ambient/cross-module
//! path (bare `Vec`, no inline) — the exact surface user code hits. Focus is
//! the subtle interactions: deep growth across many reallocs, reference-
//! semantics aliasing, growth-DURING-aliasing (an alias must observe the new
//! buffer after another binding triggers a realloc), multi-Vec
//! non-interference, interleaved get/push straddling a realloc, Vec stored in
//! a record field, full-width i64 values, and capacity edges.
//!
//! Convention: a tool returns `0 - <value>` (a negative i64) which the runtime
//! surfaces as `Trapped { "tool returned error (N)" }`; `neg` recovers `N`.

mod common;

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Wrap a `tool_main` body (bare `Vec` — ambient injection supplies vec.sigil).
fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// Wrap with extra top-level definitions (e.g. a record holding a Vec).
fn tool_with_defs(defs: &str, body: &str) -> String {
    format!(
        "module tool;\n{defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

use common::run_returning_negative as run_neg;

fn neg(body: &str) -> i64 {
    run_neg(&tool(body))
}

// ── deep growth ──────────────────────────────────────────────────────────

#[test]
fn deep_growth_sum_all_elements() {
    // Push 2000 elements (≈10 reallocations: 4→8→…→2048), then read EVERY
    // element back and sum. Any element dropped or corrupted across a realloc
    // changes the sum. Σ 0..2000 = 2000*1999/2 = 1_999_000.
    // Literal-bounds for-range drivers: statically bounded, so the WCC
    // `recommended_budget` covers all 4000 call-heavy iterations and the test
    // runs at the bare recommendation under fuel ENFORCEMENT (the old `while`
    // drivers kept the floor budget and correctly fuel-trapped).
    let body = "    let v: Vec<i64> = Vec::new();\n\
        \x20   for i in 0..2000 {\n\
        \x20       let n: i64 = v.push(i);\n\
        \x20   }\n\
        \x20   let mut s: i64 = 0;\n\
        \x20   for j in 0..2000 {\n\
        \x20       s = s + v.get(j);\n\
        \x20   }\n\
        \x20   return 0 - s;";
    assert_eq!(neg(body), 1_999_000);
}

// ── reference-semantics aliasing ─────────────────────────────────────────

#[test]
fn alias_sees_pushes_through_other_binding() {
    // `let b = a` shares the heap header. Pushing through `b` must be visible
    // through `a` (count + element).
    let body = "    let a: Vec<i64> = Vec::new();\n\
        \x20   let b: Vec<i64> = a;\n\
        \x20   let x: i64 = b.push(7);\n\
        \x20   let y: i64 = b.push(8);\n\
        \x20   return 0 - (a.len() + a.get(1));";
    assert_eq!(neg(body), 10); // len 2 + get(1) 8
}

#[test]
fn three_level_alias_chain() {
    // a → b → c all the same header; push through c, observe through a.
    let body = "    let a: Vec<i64> = Vec::new();\n\
        \x20   let b: Vec<i64> = a;\n\
        \x20   let c: Vec<i64> = b;\n\
        \x20   let n: i64 = c.push(42);\n\
        \x20   return 0 - a.get(0);";
    assert_eq!(neg(body), 42);
}

#[test]
fn growth_during_aliasing_repoints_all_holders() {
    // THE subtle one. `a` and `b` alias a cap-2 header. Pushing 5 through `b`
    // forces a realloc (2→4→8) and rewrites `self.buf`. Because the buf field
    // lives in the SHARED header, `a` must observe the NEW buffer — if `a` held
    // a stale buf, `a.get(4)` would read out-of-buffer (trap) or garbage.
    let body = "    let a: Vec<i64> = Vec::with_capacity(2);\n\
        \x20   let b: Vec<i64> = a;\n\
        \x20   let mut i: i64 = 0;\n\
        \x20   while i < 5 {\n\
        \x20       let n: i64 = b.push(i * 10);\n\
        \x20       i = i + 1;\n\
        \x20   }\n\
        \x20   return 0 - (a.get(0) + a.get(4));";
    assert_eq!(neg(body), 40); // 0 + 40, read through the aliasing binding
}

// ── non-interference ─────────────────────────────────────────────────────

#[test]
fn multiple_vecs_do_not_corrupt_each_other() {
    // Two independent Vecs, interleaved pushes; each must keep its own buffer.
    let body = "    let a: Vec<i64> = Vec::new();\n\
        \x20   let b: Vec<i64> = Vec::new();\n\
        \x20   let p: i64 = a.push(100);\n\
        \x20   let q: i64 = b.push(200);\n\
        \x20   let r: i64 = a.push(101);\n\
        \x20   let s: i64 = b.push(201);\n\
        \x20   return 0 - (a.get(0) + a.get(1) + b.get(0) + b.get(1));";
    assert_eq!(neg(body), 602); // 100+101+200+201
}

#[test]
fn many_vecs_growing_concurrently() {
    // Three Vecs growing in lockstep — exercises interleaved allocations so a
    // realloc of one cannot clobber another's live buffer.
    // Bounded for-range driver — see deep_growth_sum_all_elements.
    let body = "    let a: Vec<i64> = Vec::new();\n\
        \x20   let b: Vec<i64> = Vec::new();\n\
        \x20   let c: Vec<i64> = Vec::new();\n\
        \x20   for i in 0..50 {\n\
        \x20       let x: i64 = a.push(i);\n\
        \x20       let y: i64 = b.push(i * 2);\n\
        \x20       let z: i64 = c.push(i * 3);\n\
        \x20   }\n\
        \x20   return 0 - (a.get(49) + b.get(49) + c.get(49) + a.len() + b.len() + c.len());";
    // a.get(49)=49, b=98, c=147, lens 50+50+50 → 49+98+147+150 = 444
    assert_eq!(neg(body), 444);
}

// ── interleaving across a realloc ────────────────────────────────────────

#[test]
fn interleaved_get_push_straddling_realloc() {
    // Read element 0, then push past the initial capacity (realloc), then read
    // element 0 again + the new last — the pre-realloc read and post-realloc
    // reads must all agree.
    let body = "    let v: Vec<i64> = Vec::new();\n\
        \x20   let p: i64 = v.push(1);\n\
        \x20   let x: i64 = v.get(0);\n\
        \x20   let a: i64 = v.push(2);\n\
        \x20   let b: i64 = v.push(3);\n\
        \x20   let c: i64 = v.push(4);\n\
        \x20   let d: i64 = v.push(5);\n\
        \x20   return 0 - (x + v.get(0) + v.get(4));";
    assert_eq!(neg(body), 7); // 1 (pre) + 1 (post) + 5 (last)
}

// ── push return value ────────────────────────────────────────────────────

#[test]
fn push_returns_new_length_each_time() {
    let body = "    let v: Vec<i64> = Vec::new();\n\
        \x20   let a: i64 = v.push(10);\n\
        \x20   let b: i64 = v.push(20);\n\
        \x20   let c: i64 = v.push(30);\n\
        \x20   return 0 - (a + b + c);";
    assert_eq!(neg(body), 6); // 1 + 2 + 3
}

// ── capacity edges ───────────────────────────────────────────────────────

#[test]
fn with_capacity_zero_grows_on_first_push() {
    let body = "    let v: Vec<i64> = Vec::with_capacity(0);\n\
        \x20   let a: i64 = v.push(9);\n\
        \x20   return 0 - (v.len() + v.get(0));";
    assert_eq!(neg(body), 10); // len 1 + get(0) 9
}

#[test]
fn with_capacity_one_doubles_on_overflow() {
    // cap 1: first push fills it (count==slots), second push grows 1→2.
    let body = "    let v: Vec<i64> = Vec::with_capacity(1);\n\
        \x20   let a: i64 = v.push(5);\n\
        \x20   let b: i64 = v.push(6);\n\
        \x20   return 0 - (v.len() + v.get(0) + v.get(1));";
    assert_eq!(neg(body), 13); // len 2 + 5 + 6
}

// ── full-width values ────────────────────────────────────────────────────

#[test]
fn stores_full_width_i64_without_truncation() {
    // 9_000_000_000_000 > 2^32 — proves the 8-byte slot keeps the high bits.
    let body = "    let v: Vec<i64> = Vec::new();\n\
        \x20   let a: i64 = v.push(9000000000000);\n\
        \x20   let b: i64 = v.push(0 - 7000000000000);\n\
        \x20   return 0 - (v.get(0) + v.get(1));";
    assert_eq!(neg(body), 2_000_000_000_000); // 9e12 + (-7e12)
}

// ── Vec inside a record field ────────────────────────────────────────────

#[test]
fn vec_as_record_field() {
    // A user record holds a Vec; method dispatch on a field-access receiver
    // (`h.items.push(..)`) must mutate the shared buffer.
    // NOTE: `Holder { items: Vec::new() }` (assoc fn directly in field
    // position) currently hits T150 — the field's declared type is not
    // propagated as the expected type (AG-C2 boundary). The let-first idiom
    // supplies the annotation; this isolates the RUNTIME behaviour of a Vec
    // stored in a record field.
    let src = tool_with_defs(
        "record Holder { items: Vec<i64> }",
        "    let vv: Vec<i64> = Vec::new();\n\
         \x20   let h: Holder = Holder { items: vv };\n\
         \x20   let a: i64 = h.items.push(3);\n\
         \x20   let b: i64 = h.items.push(4);\n\
         \x20   return 0 - (h.items.len() + h.items.get(1));",
    );
    assert_eq!(run_neg(&src), 6); // len 2 + get(1) 4
}

// ── bounds traps (validation-gated, CF4-style) ───────────────────────────

fn assert_get_traps(setup: &str, in_bounds: &str, oob: &str) {
    // The in-bounds control must reach execution (proves the module validates);
    // the OOB variant differs only by the index constant, so a Trapped result
    // is a genuine runtime bounds trap.
    let body = |idx: &str| {
        format!("{setup}\n    let probe: i64 = v.get({idx});\n    return probe - probe;")
    };
    let control = compile_tool(&tool(&body(in_bounds))).expect("control compiles");
    assert!(
        execute_ephemeral(&control.wasm, b"", control.fuel_budget, &IoGrants::none()).is_ok(),
        "in-bounds control get({in_bounds}) must validate + run"
    );
    let oob_t = compile_tool(&tool(&body(oob))).expect("oob compiles");
    assert!(
        matches!(
            execute_ephemeral(&oob_t.wasm, b"", oob_t.fuel_budget, &IoGrants::none()),
            Err(ToolError::Trapped { .. })
        ),
        "out-of-bounds get({oob}) must trap at runtime"
    );
}

#[test]
fn get_past_count_traps_even_within_capacity() {
    // After one push the capacity is 4 but the length is 1 — get(3) is in-cap
    // yet past len and MUST trap (len-bounded read).
    assert_get_traps(
        "    let v: Vec<i64> = Vec::new();\n    let a: i64 = v.push(99);",
        "0",
        "3",
    );
}

#[test]
fn get_far_out_of_bounds_traps() {
    assert_get_traps(
        "    let v: Vec<i64> = Vec::with_capacity(2);\n    let a: i64 = v.push(1);",
        "0",
        "100000",
    );
}
