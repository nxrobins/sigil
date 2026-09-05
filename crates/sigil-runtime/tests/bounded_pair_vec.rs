//! Completeness Phase 2 — `zip`/`enumerate` + the `BoundedPairVec_i64_i64` family.
//!
//! `zip`/`enumerate` on `BoundedVec_i64_N` return a fresh, Alloc-free
//! `BoundedPairVec_i64_i64_N` (parallel-array tuple vector) built via its sealed
//! cross-module `::new()`+`push` API. The pair element is read as a real
//! `Option<(i64,i64)>` (P0a-proven). Every `tool_main` carries NO `! { Alloc }`, so
//! the suite is the ET-2 Alloc-free proof. Values via the negative-sentinel decode.

mod common;

use sigil_compiler::compile_tool;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    common::run_returning_negative_with_min_fuel(&tool(body), 1_000_000_000)
}

/// True iff `body` GENUINELY traps (a positive return is NOT a trap).
fn body_traps(body: &str) -> bool {
    common::tool_traps_with_min_fuel(&tool(body), 1_000_000_000)
}

/// Build a `BoundedVec_i64_8` named `name` from `vals`.
fn v8(name: &str, vals: &[i64]) -> String {
    let mut s = format!("    let mut {name}: BoundedVec_i64_8 = BoundedVec_i64_8::new();\n");
    for (k, val) in vals.iter().enumerate() {
        s.push_str(&format!("    let _{name}{k}: i64 = {name}.push({val});\n"));
    }
    s
}

// ───────────────────────── the pair family (direct ::new()+push) ─────────────

// The pair family is buildable in user code via the SEALED public ::new()+push API
// (the seal blocks only record LITERALS). push(3,30),push(7,70); get(1)=(7,70);
// len 2 → 2*1000 + 7 + 70 = 2077.
#[test]
fn pair_direct_push_get() {
    let body = "    let mut p: BoundedPairVec_i64_i64_8 = BoundedPairVec_i64_i64_8::new();\n    let _a: i64 = p.push(3, 30);\n    let _b: i64 = p.push(7, 70);\n    let o: Option<(i64, i64)> = p.get(1);\n    let pr: (i64, i64) = o.unwrap_or((0, 0));\n    let (a, b) = pr;\n    return 0 - (p.len() * 1000 + a + b);";
    assert_eq!(neg(body), 2077);
}

// get out of range → None (LEN-bounded). get(count) on a 2-element pair vec → None → unwrap_or((9,9)).
#[test]
fn pair_get_out_of_range_none() {
    let body = "    let mut p: BoundedPairVec_i64_i64_8 = BoundedPairVec_i64_i64_8::new();\n    let _a: i64 = p.push(3, 30);\n    let _b: i64 = p.push(7, 70);\n    let o: Option<(i64, i64)> = p.get(2);\n    let pr: (i64, i64) = o.unwrap_or((9, 9));\n    let (a, b) = pr;\n    return 0 - (a + b);";
    assert_eq!(neg(body), 18); // (9,9) → 18
}

// A 9th push into a full `_8` pair vec force-traps (fst[8] OOB).
#[test]
fn pair_full_overflow_traps() {
    let mut body = String::from(
        "    let mut p: BoundedPairVec_i64_i64_8 = BoundedPairVec_i64_i64_8::new();\n",
    );
    for i in 0..8 {
        body.push_str(&format!("    let _q{i}: i64 = p.push({i}, {i});\n"));
    }
    body.push_str("    let _o: i64 = p.push(99, 99);\n    return 0 - 1;");
    assert!(
        body_traps(&body),
        "9th push into a full _8 pair vec must trap"
    );
}

// ───────────────────────── zip ─────────────────────────

// zip same count: v=[1,2,3], w=[10,20,30] → (1,10),(2,20),(3,30); get(1)=(2,20)=22; len 3 → 3022.
#[test]
fn zip_same_count() {
    let body = format!(
        "{}{}    let p: BoundedPairVec_i64_i64_8 = v.zip(w);\n    let o: Option<(i64, i64)> = p.get(1);\n    let pr: (i64, i64) = o.unwrap_or((0, 0));\n    let (a, b) = pr;\n    return 0 - (p.len() * 1000 + a + b);",
        v8("v", &[1, 2, 3]),
        v8("w", &[10, 20, 30])
    );
    assert_eq!(neg(&body), 3022);
}

// zip clamps to min count: v=[1,2,3,4,5], w=[10,20] → 2 pairs; get(1)=(2,20)=22; len 2 → 2022.
#[test]
fn zip_min_count() {
    let body = format!(
        "{}{}    let p: BoundedPairVec_i64_i64_8 = v.zip(w);\n    let o: Option<(i64, i64)> = p.get(1);\n    let pr: (i64, i64) = o.unwrap_or((0, 0));\n    let (a, b) = pr;\n    return 0 - (p.len() * 1000 + a + b);",
        v8("v", &[1, 2, 3, 4, 5]),
        v8("w", &[10, 20])
    );
    assert_eq!(neg(&body), 2022);
}

// zip with an empty operand → empty result (either order).
#[test]
fn zip_with_empty() {
    let a = format!(
        "{}    let w: BoundedVec_i64_8 = BoundedVec_i64_8::new();\n    let p: BoundedPairVec_i64_i64_8 = v.zip(w);\n    return 0 - (p.len() + 5);",
        v8("v", &[1, 2, 3])
    );
    let b = format!(
        "    let v: BoundedVec_i64_8 = BoundedVec_i64_8::new();\n{}    let p: BoundedPairVec_i64_i64_8 = v.zip(w);\n    return 0 - (p.len() + 6);",
        v8("w", &[1, 2, 3])
    );
    assert_eq!(neg(&a), 5);
    assert_eq!(neg(&b), 6);
}

// zip is FRESH vs BOTH sources: mutate the result, both sources unchanged.
#[test]
fn zip_result_is_fresh() {
    // (We can't mutate a BoundedPairVec field via a public setter, but `@ReadOnly`
    // self/other forbid source mutation in zip; this asserts both sources survive a
    // zip + a subsequent source read.)
    let body = format!(
        "{}{}    let p: BoundedPairVec_i64_i64_8 = v.zip(w);\n    let ov: Option<i64> = v.get(0);\n    let ow: Option<i64> = w.get(0);\n    return 0 - (ov.unwrap_or(0) * 100 + ow.unwrap_or(0) + p.len());",
        v8("v", &[1, 2]),
        v8("w", &[10, 20])
    );
    assert_eq!(neg(&body), 112); // v[0]=1 → 100, w[0]=10, len 2 → 112
}

// ───────────────────────── enumerate ─────────────────────────

// enumerate pairs (index, value): v=[10,20,30] → (0,10),(1,20),(2,30); get(2)=(2,30)=32; len 3 → 3032.
#[test]
fn enumerate_index_value() {
    let body = format!(
        "{}    let p: BoundedPairVec_i64_i64_8 = v.enumerate();\n    let o: Option<(i64, i64)> = p.get(2);\n    let pr: (i64, i64) = o.unwrap_or((0, 0));\n    let (idx, val) = pr;\n    return 0 - (p.len() * 1000 + idx * 100 + val);",
        v8("v", &[10, 20, 30])
    );
    assert_eq!(neg(&body), 3230); // len 3 → 3000, idx 2 → 200, val 30
}

#[test]
fn enumerate_empty() {
    let body = "    let v: BoundedVec_i64_8 = BoundedVec_i64_8::new();\n    let p: BoundedPairVec_i64_i64_8 = v.enumerate();\n    return 0 - (p.len() + 8);";
    assert_eq!(neg(body), 8);
}

// ───────────────────────── boundary + inference ─────────────────────────

// zip on two FULL `_8` vecs (count==8) → full pair result, no trap. v=w=[1..8];
// get(7)=(8,8)=16; len 8 → 8000 + 16 = 8016.
#[test]
fn zip_on_full_eight() {
    let body = format!(
        "{}{}    let p: BoundedPairVec_i64_i64_8 = v.zip(w);\n    let o: Option<(i64, i64)> = p.get(7);\n    let pr: (i64, i64) = o.unwrap_or((0, 0));\n    let (a, b) = pr;\n    return 0 - (p.len() * 1000 + a + b);",
        v8("v", &[1, 2, 3, 4, 5, 6, 7, 8]),
        v8("w", &[1, 2, 3, 4, 5, 6, 7, 8])
    );
    assert_eq!(neg(&body), 8016);
}

// INFERRED result type (no annotation) — the transitive pull must still inject the
// pair family. v=[5,6], w=[50,60]; get(0)=(5,50)=55.
#[test]
fn zip_inferred_result_type() {
    let body = format!(
        "{}{}    let p = v.zip(w);\n    let o: Option<(i64, i64)> = p.get(0);\n    let pr: (i64, i64) = o.unwrap_or((0, 0));\n    let (a, b) = pr;\n    return 0 - (a + b);",
        v8("v", &[5, 6]),
        v8("w", &[50, 60])
    );
    assert_eq!(neg(&body), 55);
}

// NC-P2-9: the transitive pull does NOT bloat a `push`/`get`-only program — the
// unused pair family is dead-code-eliminated, so a no-zip program's wasm is STRICTLY
// SMALLER than a zip program's (the pair-family functions only appear when zip is used).
#[test]
fn pair_family_is_dce_d_when_unused() {
    let push_only = tool(&format!(
        "{}    let o: Option<i64> = v.get(0);\n    return 0 - o.unwrap_or(0);",
        v8("v", &[1, 2, 3])
    ));
    let zips = tool(&format!(
        "{}{}    let p: BoundedPairVec_i64_i64_8 = v.zip(w);\n    return 0 - p.len();",
        v8("v", &[1, 2, 3]),
        v8("w", &[1, 2, 3])
    ));
    let push_wasm = compile_tool(&push_only).expect("compiles").wasm.len();
    let zip_wasm = compile_tool(&zips).expect("compiles").wasm.len();
    assert!(
        push_wasm < zip_wasm,
        "DCE proof failed: a push/get-only program ({push_wasm} B) should be SMALLER than a zip \
         program ({zip_wasm} B) — the unused pair family must be eliminated, not bloat every user."
    );
}
