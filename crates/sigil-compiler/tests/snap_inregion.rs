//! DEF-2b PR-6 — the `Vec::in_region(r)` codegen golden (the honesty boundary).
//!
//! Pins the emitted WAT of `Vec::in_region(r)` to prove the honesty finding: v1 has a
//! SINGLE global bump allocator and `in_region` is type-level region association, NOT a
//! separate arena. The function therefore lowers to the SAME shape as `Vec::new()` — an
//! empty header `{ buf: 0, count: 0, slots: 0, alloc: 0 }` with NO buffer allocation (`buf`
//! stays `0`; the `alloc` field is the reserved-but-inert region handle, stored `0`). The
//! `r` parameter is consumed (it appears in the signature) but never dereferenced.
//!
//! Only the `in_region` function body is snapshotted (extracted by its export name), so the
//! golden is decoupled from unrelated monomorphized `vec.sigil` functions in the same
//! module — a `vec.sigil` change elsewhere does not move it.

use sigil_test_utils::pipeline::compile_or_panic;
use sigil_test_utils::snapshot::wat_of;

/// Extract the single `(func (;N;) …)` block exported under `export_name` from WAT text.
fn extract_func(wat: &str, export_name: &str) -> String {
    // `(export "<name>" (func N))` → N.
    let needle = format!("(export \"{export_name}\" (func ");
    let after = wat
        .split_once(&needle)
        .unwrap_or_else(|| panic!("export `{export_name}` not found in WAT:\n{wat}"))
        .1;
    let idx: usize = after
        .split([')', ' '])
        .next()
        .and_then(|d| d.trim().parse().ok())
        .expect("func index after export");

    // The matching `(func (;N;) …)` definition; collect until parens rebalance to 0.
    let start_marker = format!("(func (;{idx};)");
    let body_start = wat
        .find(&start_marker)
        .unwrap_or_else(|| panic!("func def `(;{idx};)` not found"));
    let mut depth = 0i32;
    let mut end = body_start;
    for (off, ch) in wat[body_start..].char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    end = body_start + off + 1;
                    break;
                }
            }
            _ => {}
        }
    }
    wat[body_start..end].to_string()
}

#[test]
fn snapshot_vec_in_region_is_an_empty_header_no_arena() {
    // A `Region` PARAMETER is a bound value, so the call lowers end-to-end (a lexical
    // region handle as an argument is the PR-7 codegen capstone).
    let src = "module m;\n\
         pub fn build(r: Region) -> i64 { let v: Vec<i64> = Vec::in_region(r); return v.len(); }\n";
    let comp = compile_or_panic(src);
    let wat = wat_of(&comp.wasm_inner);
    let in_region = extract_func(&wat, "vec::Vec__in_region__i64");
    insta::assert_snapshot!("vec_in_region__i64", in_region);
}
