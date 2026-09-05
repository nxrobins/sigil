//! Phase-1 completion: `.contains(x)` on Array/Slice and slice `.first()` /
//! `.last()` — the RUNTIME round-trip (the type-check accept/reject lives in
//! `diagnostic_messages.rs`; this file COMPILES + EXECUTES the wasm and asserts
//! the actual result).
//!
//! Two decode mechanisms (per the plan's UP-uniformity finding):
//! - bool / int results → the negative-sentinel trap (`return 0 - v`), recovered
//!   from the trap message — works for `.contains` (bool→1/2) and i64 first/last.
//! - `str` results → the `.as_output()` byte round-trip (the `fstring_runtime`
//!   pattern) — the only way to assert a returned `str` (a fat-pointer).
//!
//! Allocation note: scalar ARRAY `.contains` reads the array in place (Alloc-free).
//! A SLICE (`&arr[lo..hi]`) materializes an 8-byte fat-pointer header, str
//! `.contains` synthesizes a `&recv` borrow (→ a slice header), and slice
//! `.first()`/`.last()` allocate the `Option` struct — so those tools declare
//! `! { Alloc }`.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Wrap `body` in a `tool_main` with the given effect clause (`""` or
/// `"! { Alloc }"`).
fn tool(effects: &str, body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {effects} {{\n{body}\n}}\n"
    )
}

/// Run a `return 0 - value;` body and recover `value` from the negative-sentinel
/// trap. (Mirrors `array_repeat.rs`.)
fn neg(effects: &str, body: &str) -> i64 {
    let result = compile_tool(&tool(effects, body)).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a clean negative-sentinel return, got a genuine trap: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse trap code from {message:?}: {e}"))
        }
        Err(other) => panic!("tool failed with non-trap error: {other:?}"),
        Ok(_) => panic!("tool returned a positive packed-pointer; expected negative sentinel"),
    }
}

/// Run a body that returns a `str` via `.as_output()` and read back the bytes.
fn run_out(body: &str) -> String {
    let result = compile_tool(&tool("! { Alloc }", body)).expect("str tool should compile");
    let exec = execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none())
        .expect("str tool executes");
    String::from_utf8(exec.output).expect("output is UTF-8")
}

// `.contains` returns bool → branch it to the 1 (found) / 2 (miss) sentinel.
const FOUND: &str = "    if found { return 0 - 1; } else { return 0 - 2; }";
// (effect clause passed to `neg` is interpolated as a value — use single braces)

// ───────────────────────── scalar ARRAY .contains (Alloc-free) ─────────────────────────

#[test]
fn array_contains_i64_hit() {
    let body = format!(
        "    let arr: [i64; 5] = [10, 20, 30, 40, 50];\n\
         \x20   let found: bool = arr.contains(30);\n{FOUND}"
    );
    assert_eq!(neg("", &body), 1, "30 is present");
}

#[test]
fn array_contains_i64_miss() {
    let body = format!(
        "    let arr: [i64; 5] = [10, 20, 30, 40, 50];\n\
         \x20   let found: bool = arr.contains(35);\n{FOUND}"
    );
    assert_eq!(neg("", &body), 2, "35 is absent");
}

#[test]
fn array_contains_i64_at_last_position() {
    // Off-by-one guard: the needle is the LAST element.
    let body = format!(
        "    let arr: [i64; 5] = [10, 20, 30, 40, 50];\n\
         \x20   let found: bool = arr.contains(50);\n{FOUND}"
    );
    assert_eq!(neg("", &body), 1, "the last element must be found");
}

#[test]
fn array_contains_empty_is_false() {
    // `[i64; 0]` → zero iterations → false (no element load).
    let body = format!(
        "    let arr: [i64; 0] = [];\n\
         \x20   let found: bool = arr.contains(1);\n{FOUND}"
    );
    assert_eq!(neg("", &body), 2, "an empty array contains nothing");
}

// Narrow-int (`i32`/`u32`) ARRAY `.contains` over an INTEGER-LITERAL array.
// These exercise the 4-byte scan path with a needle PAST index 0 — the regime
// that was corrupt before the narrow-int-array-stride fix (an all-int-literal
// `[i32; N]`/`[u32; N]` stored its `IntLit` elements at the i64 8-byte stride
// while every reader used the annotated 4-byte width, so idx > 0 read garbage).
// `resolve_int_literals_in_expr` now narrows the literal elements + `elem_type`
// to the annotated `T`, so storage and the scan agree at 4 bytes. The companion
// `narrow_int_array_stride.rs` covers raw indexing + for-in under the same fix.

#[test]
fn array_contains_i32_hit_past_index_zero() {
    // 40 sits at idx 3 — the exact slot the stride bug corrupted.
    let body = format!(
        "    let arr: [i32; 5] = [10, 20, 30, 40, 50];\n\
         \x20   let found: bool = arr.contains(40);\n{FOUND}"
    );
    assert_eq!(
        neg("", &body),
        1,
        "i32 array element at idx 3 must be found"
    );
}

#[test]
fn array_contains_i32_miss() {
    let body = format!(
        "    let arr: [i32; 5] = [10, 20, 30, 40, 50];\n\
         \x20   let found: bool = arr.contains(35);\n{FOUND}"
    );
    assert_eq!(neg("", &body), 2, "35 is absent");
}

#[test]
fn array_contains_i32_at_last_position() {
    let body = format!(
        "    let arr: [i32; 5] = [10, 20, 30, 40, 50];\n\
         \x20   let found: bool = arr.contains(50);\n{FOUND}"
    );
    assert_eq!(neg("", &body), 1, "the last i32 element must be found");
}

#[test]
fn array_contains_u32_hit_past_index_zero() {
    let body = format!(
        "    let arr: [u32; 5] = [10, 20, 30, 40, 50];\n\
         \x20   let found: bool = arr.contains(40);\n{FOUND}"
    );
    assert_eq!(
        neg("", &body),
        1,
        "u32 array element at idx 3 must be found"
    );
}

#[test]
fn array_contains_u32_miss() {
    let body = format!(
        "    let arr: [u32; 5] = [10, 20, 30, 40, 50];\n\
         \x20   let found: bool = arr.contains(35);\n{FOUND}"
    );
    assert_eq!(neg("", &body), 2, "35 is absent");
}

// The 4-byte scan path was *also* independently proven by the `bool` tests
// below: a `bool` element is 4 bytes and a `bool` literal is NOT an `IntLit`,
// so a `[bool; N]` literal always stored at its 4-byte width — those tests
// passed even before the int-literal fix.

#[test]
fn array_contains_bool_hit() {
    let body = format!(
        "    let arr: [bool; 3] = [true, false, true];\n\
         \x20   let found: bool = arr.contains(false);\n{FOUND}"
    );
    assert_eq!(neg("", &body), 1);
}

#[test]
fn array_contains_bool_miss() {
    let body = format!(
        "    let arr: [bool; 2] = [true, true];\n\
         \x20   let found: bool = arr.contains(false);\n{FOUND}"
    );
    assert_eq!(neg("", &body), 2);
}

#[test]
fn array_contains_f64_hit() {
    let body = format!(
        "    let arr: [f64; 3] = [1.5, 2.5, 3.5];\n\
         \x20   let found: bool = arr.contains(2.5);\n{FOUND}"
    );
    assert_eq!(neg("", &body), 1);
}

#[test]
fn array_contains_f64_miss() {
    let body = format!(
        "    let arr: [f64; 3] = [1.5, 2.5, 3.5];\n\
         \x20   let found: bool = arr.contains(9.5);\n{FOUND}"
    );
    assert_eq!(neg("", &body), 2);
}

// ───────────────────────── scalar SLICE .contains (Alloc: slice header) ─────────────────────────

#[test]
fn slice_contains_i64_hit() {
    // `&arr[1..4]` = [20, 30, 40]; the slice's data_ptr is `arr_base + 1*8`
    // (NOT past the array header), so this guards the offset-4 element-load math
    // for slices (a bug if the scan used offset 0).
    let body = format!(
        "    let arr: [i64; 5] = [10, 20, 30, 40, 50];\n\
         \x20   let s: &[i64] = &arr[1..4];\n\
         \x20   let found: bool = s.contains(30);\n{FOUND}"
    );
    assert_eq!(neg("! { Alloc }", &body), 1);
}

#[test]
fn slice_contains_i64_miss_element_outside_window() {
    // 10 is in the array but NOT in the [1..4) window — proves the slice bound
    // (not the backing array) governs the scan.
    let body = format!(
        "    let arr: [i64; 5] = [10, 20, 30, 40, 50];\n\
         \x20   let s: &[i64] = &arr[1..4];\n\
         \x20   let found: bool = s.contains(10);\n{FOUND}"
    );
    assert_eq!(neg("! { Alloc }", &body), 2);
}

// ───────────────────────── str .contains (content equality, NOT substring) ─────────────────────────

#[test]
fn array_contains_str_hit() {
    let body = format!(
        "    let arr: [str; 3] = [\"alpha\", \"beta\", \"gamma\"];\n\
         \x20   let found: bool = arr.contains(\"beta\");\n{FOUND}"
    );
    assert_eq!(neg("! { Alloc }", &body), 1);
}

#[test]
fn array_contains_str_miss() {
    let body = format!(
        "    let arr: [str; 3] = [\"alpha\", \"beta\", \"gamma\"];\n\
         \x20   let found: bool = arr.contains(\"delta\");\n{FOUND}"
    );
    assert_eq!(neg("! { Alloc }", &body), 2);
}

#[test]
fn array_contains_str_is_element_equality_not_substring() {
    // THE MC-1 guard: `"pha"` is a SUBSTRING of `"alpha"` but is NOT an element.
    // A naive reuse of `str_contains` (substring) would wrongly return true here.
    let body = format!(
        "    let arr: [str; 3] = [\"alpha\", \"beta\", \"gamma\"];\n\
         \x20   let found: bool = arr.contains(\"pha\");\n{FOUND}"
    );
    assert_eq!(
        neg("! { Alloc }", &body),
        2,
        "substring is NOT element membership"
    );
}

#[test]
fn slice_contains_str_hit() {
    let body = format!(
        "    let arr: [str; 3] = [\"alpha\", \"beta\", \"gamma\"];\n\
         \x20   let s: &[str] = &arr[0..3];\n\
         \x20   let found: bool = s.contains(\"gamma\");\n{FOUND}"
    );
    assert_eq!(neg("! { Alloc }", &body), 1);
}

// ───────────────────────── slice .first() / .last() → Option ─────────────────────────

#[test]
fn slice_first_some_returns_first_element() {
    let body = "    let arr: [i64; 3] = [11, 22, 33];\n\
         \x20   let s: &[i64] = &arr[0..3];\n\
         \x20   match s.first() {\n\
         \x20       Some(v) => { return 0 - v; },\n\
         \x20       None => { return 0 - 999; },\n\
         \x20   }";
    assert_eq!(neg("! { Alloc }", body), 11);
}

#[test]
fn slice_last_some_returns_last_element() {
    let body = "    let arr: [i64; 3] = [11, 22, 33];\n\
         \x20   let s: &[i64] = &arr[0..3];\n\
         \x20   match s.last() {\n\
         \x20       Some(v) => { return 0 - v; },\n\
         \x20       None => { return 0 - 999; },\n\
         \x20   }";
    assert_eq!(neg("! { Alloc }", body), 33);
}

#[test]
fn slice_first_on_subwindow() {
    // `&arr[2..5]` = [30,40,50]; first = 30, last = 50.
    let first = "    let arr: [i64; 5] = [10, 20, 30, 40, 50];\n\
         \x20   let s: &[i64] = &arr[2..5];\n\
         \x20   match s.first() {\n\
         \x20       Some(v) => { return 0 - v; },\n\
         \x20       None => { return 0 - 999; },\n\
         \x20   }";
    assert_eq!(neg("! { Alloc }", first), 30);
}

#[test]
fn slice_first_empty_is_none() {
    // `&arr[0..0]` is the empty slice → None branch (no element load).
    let body = "    let arr: [i64; 3] = [11, 22, 33];\n\
         \x20   let s: &[i64] = &arr[0..0];\n\
         \x20   match s.first() {\n\
         \x20       Some(v) => { return 0 - v; },\n\
         \x20       None => { return 0 - 999; },\n\
         \x20   }";
    assert_eq!(neg("! { Alloc }", body), 999, "empty slice first() is None");
}

#[test]
fn slice_last_empty_is_none() {
    let body = "    let arr: [i64; 3] = [11, 22, 33];\n\
         \x20   let s: &[i64] = &arr[0..0];\n\
         \x20   match s.last() {\n\
         \x20       Some(v) => { return 0 - v; },\n\
         \x20       None => { return 0 - 999; },\n\
         \x20   }";
    assert_eq!(neg("! { Alloc }", body), 999);
}

#[test]
fn slice_first_str_returns_element_bytes() {
    // str element: verify via the `.as_output()` byte round-trip (the sentinel
    // can't carry a str). first of ["foo","bar","baz"] = "foo".
    let out = run_out(
        "    let arr: [str; 3] = [\"foo\", \"bar\", \"baz\"];\n\
         \x20   let s: &[str] = &arr[0..3];\n\
         \x20   match s.first() {\n\
         \x20       Some(v) => { return v.as_output(); },\n\
         \x20       None => { let none_s: str = \"NONE\"; return none_s.as_output(); },\n\
         \x20   }",
    );
    assert_eq!(out, "foo");
}

#[test]
fn slice_last_str_returns_element_bytes() {
    let out = run_out(
        "    let arr: [str; 3] = [\"foo\", \"bar\", \"baz\"];\n\
         \x20   let s: &[str] = &arr[0..3];\n\
         \x20   match s.last() {\n\
         \x20       Some(v) => { return v.as_output(); },\n\
         \x20       None => { let none_s: str = \"NONE\"; return none_s.as_output(); },\n\
         \x20   }",
    );
    assert_eq!(out, "baz");
}
