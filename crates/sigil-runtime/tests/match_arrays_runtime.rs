//! Runtime end-to-end tests for array/slice destructuring patterns (Phase 5).
//! Bindings + the `..rest` slice are decoded via the negative-sentinel trap
//! (`return 0 - K` → the harness recovers `K`). Covers array + slice scrutinees,
//! the rest slice's length AND element values, empty rest, str elements, and
//! first-match-wins arm order.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Wrap `body` in `tool_main -> i64`, run it, and recover the `K` from a
/// `return 0 - K` trap sentinel.
fn neg(body: &str) -> i64 {
    let src = format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    );
    let result = compile_tool(&src).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            let s = message
                .find(p)
                .unwrap_or_else(|| panic!("no sentinel: {message}"))
                + p.len();
            let e = message[s..].find(')').unwrap();
            message[s..s + e].parse().unwrap()
        }
        other => panic!("expected sentinel trap, got {other:?}"),
    }
}

#[test]
fn array_fixed_binds_all_elements() {
    // `[a, b, c]` on `[i64; 3]` binds each element by index.
    assert_eq!(
        neg(
            "    let arr: [i64; 3] = [10, 20, 30];\n    match arr {\n        [a, b, c] => { return 0 - (a + b + c); },\n    }"
        ),
        60
    );
}

#[test]
fn array_rest_length() {
    // `[first, ..rest]` on `[i64; 4]`: first = arr[0], rest = arr[1..4] (len 3).
    assert_eq!(
        neg(
            "    let arr: [i64; 4] = [1, 2, 3, 4];\n    match arr {\n        [first, ..rest] => { let rlu: u32 = rest.len(); let rl: i64 = rlu.as_i64(); return 0 - (first + rl); },\n    }"
        ),
        4
    );
}

#[test]
fn rest_slice_holds_correct_elements() {
    // THE data-correctness check: rest = [20, 30, 40], so rest[0]=20, rest[1]=30.
    assert_eq!(
        neg(
            "    let arr: [i64; 4] = [10, 20, 30, 40];\n    match arr {\n        [a, ..rest] => { let r0: i64 = rest[0]; let r1: i64 = rest[1]; return 0 - (r0 + r1); },\n    }"
        ),
        50
    );
}

#[test]
fn slice_empty_arm() {
    // `[]` matches a length-0 slice. Build one via `&arr[0..0]`.
    assert_eq!(
        neg(
            "    let arr: [i64; 3] = [5, 6, 7];\n    let s: &[i64] = &arr[0..0];\n    match s {\n        [] => { return 0 - 42; },\n        [head, ..tail] => { return 0 - head; },\n    }"
        ),
        42
    );
}

#[test]
fn slice_head_tail() {
    // Slice scrutinee, `[head, ..tail]`: head=5, tail=arr[1..3] (len 2).
    assert_eq!(
        neg(
            "    let arr: [i64; 3] = [5, 6, 7];\n    let s: &[i64] = &arr[0..3];\n    match s {\n        [] => { return 0 - 99; },\n        [head, ..tail] => { let tlu: u32 = tail.len(); let tl: i64 = tlu.as_i64(); return 0 - (head + tl); },\n    }"
        ),
        7
    );
}

#[test]
fn empty_rest_when_len_equals_prefix() {
    // `[x, ..rest]` on a length-1 slice → rest is empty (len 0), no trap.
    assert_eq!(
        neg(
            "    let arr: [i64; 1] = [42];\n    let s: &[i64] = &arr[0..1];\n    match s {\n        [] => { return 0 - 1; },\n        [x, ..rest] => { let rlu: u32 = rest.len(); let rl: i64 = rlu.as_i64(); return 0 - (x + rl + 1000); },\n    }"
        ),
        1042
    );
}

#[test]
fn first_match_wins_arm_order() {
    // A length-2 slice skips `[a]` (len 1) and matches `[a, b]`.
    assert_eq!(
        neg(
            "    let arr: [i64; 2] = [7, 8];\n    let s: &[i64] = &arr[0..2];\n    match s {\n        [a] => { return 0 - 1; },\n        [a, b] => { return 0 - (a + b); },\n        [..rest] => { return 0 - 999; },\n    }"
        ),
        15
    );
}

#[test]
fn str_element_binds() {
    // str elements bind correctly; `str.len()` is i64.
    assert_eq!(
        neg(
            "    let arr: [str; 2] = [\"ab\", \"cde\"];\n    match arr {\n        [x, y] => { return 0 - (x.len() + y.len()); },\n    }"
        ),
        5
    );
}

#[test]
fn str_rest_slice_element() {
    // A str `..rest`: rest[0] is read out of the slice.
    assert_eq!(
        neg(
            "    let arr: [str; 3] = [\"a\", \"bb\", \"ccc\"];\n    match arr {\n        [first, ..rest] => { let r0: str = rest[0]; return 0 - (first.len() + r0.len()); },\n    }"
        ),
        3
    );
}
