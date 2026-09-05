//! Refinement-typed array bounds (v1) — constant-index elision + the T278
//! "provably out of bounds" compile error.
//!
//! v1 scope (SC-2 / SC-6): a LITERAL index on a fixed array `[T; N]` is decided
//! by a Z3-FREE constant comparison — in-bounds elides the runtime bounds check
//! (proven structurally by the `fixed_array_construct_and_index` snapshots in
//! snap_air / snap_wat), out-of-bounds is a hard T278 error (reject > runtime
//! trap). Dynamic / non-literal indices are untouched: they keep their runtime
//! trap and never fire T278.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    if let Err(err) = compile_named_module(format!("arr_bounds_{label}.sigil"), source) {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

fn assert_fires(source: &str, label: &str, code: &str) {
    let err = compile_named_module(format!("arr_bounds_{label}.sigil"), source)
        .err()
        .unwrap_or_else(|| panic!("expected {code} for {label}, but compile succeeded"));
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&code),
        "expected {code} in diagnostics for {label}, got: {codes:?}"
    );
}

const T278: &str = "T278";

#[test]
fn in_bounds_literal_compiles() {
    // `a[2]` on `[i64; 5]` — provably in bounds; the runtime `TrapIf` is elided
    // (see snap_air__fixed_array_construct_and_index). Here we pin that it
    // still compiles clean.
    assert_compiles_clean(
        r#"
module main;
fn third(a: [i64; 5]) -> i64 {
    return a[2];
}
"#,
        "in_bounds",
    );
}

#[test]
fn first_and_last_valid_indices_compile() {
    // `a[0]` and `a[3]` on `[i64; 4]` — the boundary in-bounds indices (0 and N-1).
    assert_compiles_clean(
        r#"
module main;
fn ends(a: [i64; 4]) -> i64 {
    let lo: i64 = a[0];
    let hi: i64 = a[3];
    return lo + hi;
}
"#,
        "boundaries",
    );
}

#[test]
fn index_equal_to_size_is_oob() {
    // `a[4]` on `[i64; 4]` — off-by-one past the end; provably OOB → T278.
    assert_fires(
        r#"
module main;
fn oob(a: [i64; 4]) -> i64 {
    return a[4];
}
"#,
        "eq_size",
        T278,
    );
}

#[test]
fn index_past_end_is_oob() {
    // `a[5]` on `[i64; 4]` — the canonical example.
    assert_fires(
        r#"
module main;
fn oob(a: [i64; 4]) -> i64 {
    return a[5];
}
"#,
        "past_end",
        T278,
    );
}

#[test]
fn index_into_empty_array_is_oob() {
    // `a[0]` on `[i64; 0]` — an empty array has no valid index → T278.
    assert_fires(
        r#"
module main;
fn empty(a: [i64; 0]) -> i64 {
    return a[0];
}
"#,
        "empty",
        T278,
    );
}

#[test]
fn dynamic_index_keeps_trap_and_never_fires_t278() {
    // `a[i]` with a variable index — NOT a constant, so v1 never proves or
    // elides it (SC-6): it compiles clean, keeps its runtime bounds check, and
    // must NOT spuriously fire T278.
    assert_compiles_clean(
        r#"
module main;
fn dyn_idx(a: [i64; 4], i: i64) -> i64 {
    return a[i];
}
"#,
        "dynamic",
    );
}
