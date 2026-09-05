//! DEF-2b PR-3 — the `@in r` region annotation (parse + resolve; still rejects).
//!
//! `@in r` (LD-4) declares that a parameter's value lives in the region passed as the
//! `Region` parameter `r`. This suite pins the PARSE + RESOLVE front-end (PR-3):
//! `parse_param_annotations` accepts `@in r`, validates that `r` names a `Region`
//! parameter of the same function (P024), and resolves it to a per-signature slot
//! (`FunctionSig.param_regions = In(slot)`). The BEHAVIORAL lift that reads those slots
//! (a region value into `@in r` accepted; the surrounding soundness) is exercised
//! separately in `region_poly.rs` (PR-4).

use sigil_compiler::compile_tool;

fn codes(src: &str) -> Vec<String> {
    match compile_tool(src) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn has(src: &str, code: &str) -> bool {
    codes(src).iter().any(|c| c == code)
}

const TOOL_MAIN: &str =
    "pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0; }\n";

// ── `@in r` parses + validates ──────────────────────────────────────────────────

#[test]
fn in_annotation_parses() {
    // `@in r` naming a `Region` parameter of the same fn is well-formed.
    let src = format!(
        "module tool;\n\
         fn store(r: Region, v: Vec<i64> @in r) -> i64 {{ return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn in_annotation_forward_reference_parses() {
    // The region parameter may be declared AFTER the `@in r` param — the full param list
    // is validated, so a forward reference is fine.
    let src = format!(
        "module tool;\n\
         fn store(v: Vec<i64> @in r, r: Region) -> i64 {{ return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn in_annotation_composes_with_other_annotations() {
    // `@in r` is orthogonal to taint/mutability — it composes with `@ReadOnly` etc.
    let src = format!(
        "module tool;\n\
         fn store(r: Region, v: Vec<i64> @in r @ReadOnly) -> i64 {{ return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

// ── validation (P024) ───────────────────────────────────────────────────────────

#[test]
fn in_on_nonexistent_param_is_p024() {
    // `@in bogus` where no parameter `bogus` exists → P024.
    let src = format!(
        "module tool;\n\
         fn store(v: Vec<i64> @in bogus) -> i64 {{ return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "P024"), "got {:?}", codes(&src));
}

#[test]
fn in_on_non_region_param_is_p024() {
    // `@in x` where `x` exists but is not a `Region` → P024 (the slot must be a region).
    let src = format!(
        "module tool;\n\
         fn store(x: i64, v: Vec<i64> @in x) -> i64 {{ return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "P024"), "got {:?}", codes(&src));
}

// NOTE: the behavioral lift — a region value passed into an `@in r` parameter is now
// ACCEPTED (DEF-2b PR-4), and the surrounding soundness (unannotated → T254, callee
// leak → T254, deeper-region → T254) — lives in `region_poly.rs`.
