//! DEF-2b PR-6 — `Vec::in_region(r)` / `Map::in_region(r)`.
//!
//! `Vec::in_region(r)` (LD-7) builds an empty vector ASSOCIATED with the region `r`. The
//! HONESTY boundary (the decisive finding): v1 has a SINGLE global bump allocator and NO
//! per-region arena, so the vector's buffer still grows on the global heap and is reclaimed
//! by its ENCLOSING lexical region — `r`'s handle is INERT (stored `0`; see the WAT golden
//! in `snap_inregion.rs`). Consequently the result's region is its ENCLOSING lexical scope
//! (the default `region_of_value`), which for the common `region r { Vec::in_region(r) }`
//! is exactly `r`; typing it as `r` when `r` outlives the enclosing scope would be unsound,
//! so the result is NOT specially re-regioned (the runtime-honest choice). `r` is consumed
//! only for the forward-compat type-level association + the reserved `alloc` field.
//!
//! These assertions go end-to-end through `compile_tool` (real WASM) by using a `Region`
//! PARAMETER, a bound value the call lowers cleanly. A LEXICAL region handle as a call
//! argument is the PR-7 codegen capstone, so the lexical cases here are the REJECTED ones
//! (they abort before AIR).

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

// ── it compiles + produces a usable vector (end-to-end WASM) ──────────────────────

#[test]
fn param_in_region_compiles_to_wasm() {
    // A `Region` parameter is a bound value, so `Vec::in_region(r)` lowers end-to-end, and
    // the result is an ordinary growable vector (`push` / `len` work).
    let src = format!(
        "module tool;\n\
         fn build(r: Region) -> i64 ! {{ Alloc }} {{ \
             let v: Vec<i64> = Vec::in_region(r); v.push(7); v.push(8); return v.len(); }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn map_in_region_compiles_to_wasm() {
    // `Map::in_region(r)` is symmetric — an empty map associated with `r`, usable via the
    // ordinary insert/get surface.
    let src = format!(
        "module tool;\n\
         fn build(r: Region) -> i64 ! {{ Alloc }} {{ \
             let m: Map<i64, i64> = Map::in_region(r); m.insert(1, 7); return m.len(); }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

// ── the result flows into `@in r` (region-polymorphic) ────────────────────────────

#[test]
fn in_region_result_into_in_param_is_accepted() {
    // A vector built with `Vec::in_region(r)` flows into a `@in r` parameter — the keystone
    // use of region-polymorphism + in-region construction. Compiles to WASM (`r` is a bound
    // parameter throughout).
    let src = format!(
        "module tool;\n\
         fn store(r: Region, v: Vec<i64> @in r) -> i64 {{ return 0; }}\n\
         fn build(r: Region) -> i64 ! {{ Alloc }} {{ \
             let v: Vec<i64> = Vec::in_region(r); v.push(7); return store(r, v); }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

// ── the result is region-tracked: it cannot escape its lexical region ─────────────

#[test]
fn lexical_in_region_value_into_unannotated_is_t254() {
    // Built inside `region buf`, the vector lives in `buf` (its enclosing lexical region);
    // handing it to an un-annotated function would let it outlive `buf` → `T254`. (Rejected
    // before AIR, so the lexical handle never reaches the deferred codegen.)
    let src = format!(
        "module tool;\n\
         fn leak(v: Vec<i64>) -> i64 {{ return 0; }}\n\
         fn f() -> i64 ! {{ Alloc }} {{ \
             region buf(64) {{ let v: Vec<i64> = Vec::in_region(buf); let _x: i64 = leak(v); }}; \
             return 0; \
         }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T254"), "got {:?}", codes(&src));
}

// (The `@SecretCT @Region`-polymorphism composition — a region-born secret value flowing
// into a `@SecretCT @in r` parameter — is pinned in `region_poly.rs`; the two axes are
// orthogonal. An in-region `Vec` cannot additionally carry `@SecretCT` because the
// constructor result is concretely `@Public` and SIGIL does not relabel a call result via a
// `let` annotation — that is a taint-system property, independent of regions.)

#[test]
fn lexical_in_region_value_used_within_its_region_then_escaping_is_t254() {
    // Using the in-region vector internally is fine; only ESCAPING it trips the gate. Here
    // the let-bound result escapes via `return` of an aliasing record — `T254`.
    let src = format!(
        "module tool;\n\
         record Holder {{ v: Vec<i64> }}\n\
         fn f() -> Holder ! {{ Alloc }} {{ \
             region buf(64) {{ let v: Vec<i64> = Vec::in_region(buf); v.push(1); \
                 return Holder {{ v: v }}; }}; \
         }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T254"), "got {:?}", codes(&src));
}
