//! Integration tests for array/slice destructuring patterns in `match` arms
//! (Phase 5 — collection patterns): `match arr { [] => .., [a] => .., [a, b,
//! ..rest] => .. }`. These pin the feature end-to-end through the compile
//! pipeline (parse → type-check → AIR → wasm) and the new diagnostics:
//!
//! - accept: fixed `[a, b]`, wildcard element `[a, _]`, named/anon/whole rest,
//!   on both an array `[T; N]` and a slice `&[T]`;
//! - exhaustiveness: a fixed-array `[a, b, c]` on `[T; 3]` is exhaustive without
//!   a `_`; the slice `[head, ..tail]` + `[]` pair is exhaustive (the spec's own
//!   example); a fixed-only slice match is NON-exhaustive → T088;
//! - T264: an array pattern on a non-array/slice scrutinee;
//! - T265: a fixed-array pattern whose length can never match `[T; N]`.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    if let Err(err) = compile_named_module(format!("match_arrays_{label}.sigil"), source) {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

fn assert_fires(source: &str, label: &str, code: &str) {
    let err = compile_named_module(format!("match_arrays_{label}.sigil"), source)
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

#[test]
fn fixed_array_exact_length_is_exhaustive() {
    // `[a, b, c]` covers the only possible length (3) of `[i64; 3]` — exhaustive
    // with NO `_` arm.
    assert_compiles_clean(
        r#"
module main;
fn sum3(arr: [i64; 3]) -> i64 {
    match arr {
        [a, b, c] => { return a + b + c; },
    }
}
"#,
        "fixed_exact",
    );
}

#[test]
fn array_rest_and_wildcard_elements_compile() {
    assert_compiles_clean(
        r#"
module main;
fn head_or(arr: [i64; 4]) -> i64 {
    match arr {
        [first, _, ..rest] => { return first; },
    }
}
"#,
        "rest_wild",
    );
}

#[test]
fn slice_head_tail_plus_empty_is_exhaustive() {
    // The completeness-spec's own example: `[head, ..tail]` (len >= 1) + `[]`
    // (len 0) together cover EVERY slice length — exhaustive without a `_`.
    assert_compiles_clean(
        r#"
module main;
fn first_or_zero(arr: [i64; 3]) -> i64 {
    let s: &[i64] = &arr[0..3];
    match s {
        [] => { return 0; },
        [head, ..tail] => { return head; },
    }
}
"#,
        "slice_exhaustive",
    );
}

#[test]
fn slice_whole_rest_is_exhaustive() {
    // A bare `[..rest]` matches every length → a catch-all on its own.
    assert_compiles_clean(
        r#"
module main;
fn always(arr: [i64; 2]) -> i64 {
    let s: &[i64] = &arr[0..2];
    match s {
        [..rest] => { return 0; },
    }
}
"#,
        "slice_whole",
    );
}

#[test]
fn slice_fixed_only_is_non_exhaustive_t088() {
    // `[a]` covers only length 1; a slice has runtime length, so without a rest
    // arm or `_` the match is non-exhaustive.
    assert_fires(
        r#"
module main;
fn only_one(arr: [i64; 2]) -> i64 {
    let s: &[i64] = &arr[0..2];
    match s {
        [a] => { return a; },
    }
}
"#,
        "slice_nonexh",
        "T088",
    );
}

#[test]
fn array_pattern_on_non_array_fires_t264() {
    assert_fires(
        r#"
module main;
fn bad(x: i64) -> i64 {
    match x {
        [a] => { return a; },
        _ => { return 0; },
    }
}
"#,
        "t264",
        "T264",
    );
}

#[test]
fn fixed_array_length_impossible_fires_t265() {
    // `[a, b, c, d]` (4 fixed) can never match `[i64; 3]`.
    assert_fires(
        r#"
module main;
fn bad(arr: [i64; 3]) -> i64 {
    match arr {
        [a, b, c, d] => { return a; },
    }
}
"#,
        "t265",
        "T265",
    );
}

#[test]
fn str_element_array_pattern_compiles() {
    assert_compiles_clean(
        r#"
module main;
fn first_len(arr: [str; 2]) -> i64 {
    match arr {
        [x, y] => { return x.len() + y.len(); },
    }
}
"#,
        "str_elems",
    );
}
