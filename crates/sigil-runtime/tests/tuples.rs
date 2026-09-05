//! Tuples v1 — structural anonymous product types `(A, B, …)`: tuple literals,
//! multi-return, and `let (x, y) = …` destructuring. A tuple is a heap struct
//! (reuses the record lowering); v1 reads it ONLY via destructuring (`.0` is
//! deferred). These tests exercise the end-to-end construct → return →
//! destructure → use path through wasm.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// tool_main-only module.
fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

/// Module with extra top-level items (helper fns / records) before tool_main.
fn tool_with(items: &str, body: &str) -> String {
    format!(
        "module tool;\n{items}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

/// Decode the negative-sentinel return convention (`return 0 - value;` → the
/// runtime reports `Trapped` with a POSITIVE `value`).
fn decode(src: &str) -> i64 {
    let result = compile_tool(src).expect("tool should compile");
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

fn neg(body: &str) -> i64 {
    decode(&tool(body))
}

#[test]
fn tuple_literal_destructure_inline() {
    // Construct a 2-tuple and immediately destructure it.
    assert_eq!(neg("    let (a, b) = (3, 4);\n    return 0 - (a + b);"), 7);
}

#[test]
fn tuple_multi_return() {
    // The marquee use case: a function returns a tuple, the caller destructures.
    let src = tool_with(
        "fn split(x: i64) -> (i64, i64) { return (x + 1, x + 2); }",
        "    let (a, b) = split(10);\n    return 0 - (a + b);",
    );
    assert_eq!(decode(&src), 23); // 11 + 12
}

#[test]
fn tuple_destructure_order_is_positional() {
    // The first name binds element 0, the second element 1 — order matters.
    // (a - b) distinguishes correct (10-3=7) from swapped (3-10=-7).
    assert_eq!(neg("    let (a, b) = (10, 3);\n    return 0 - (a - b);"), 7);
}

#[test]
fn tuple_nested_construct_and_destructure() {
    // `((1, 2), 3)` — construct a nested tuple, destructure the outer, then the
    // inner (AG-2: nested patterns aren't supported, so the inner is a second
    // `let`). Exercises a tuple element that is itself a (pointer-width) tuple.
    let body = "    let (inner, c) = ((1, 2), 3);\n\
        \x20   let (a, b) = inner;\n\
        \x20   return 0 - (a + b + c);";
    assert_eq!(neg(body), 6); // 1 + 2 + 3
}

#[test]
fn tuple_mixed_types_bool_element() {
    // A non-int element (`bool`) alongside an `i64` — the heap layout packs both.
    let body = "    let (n, flag) = (5, true);\n\
        \x20   if flag { return 0 - n; } else { return 0 - 99; }";
    assert_eq!(neg(body), 5);
}

#[test]
fn tuple_mutable_binding() {
    // `let (mut a, b)` — per-binding `mut`: only `a` is mutable.
    let body = "    let (mut a, b) = (1, 2);\n\
        \x20   a = a + 10;\n\
        \x20   return 0 - (a + b);";
    assert_eq!(neg(body), 13); // 11 + 2
}

#[test]
fn tuple_three_elements() {
    assert_eq!(
        neg("    let (a, b, c) = (100, 20, 3);\n    return 0 - (a + b + c);"),
        123
    );
}

#[test]
fn tuple_intlit_defaulting_end_to_end() {
    // PIL: a `(1, 2)` literal carries Tuple([IntLit, IntLit]); the orphan
    // defaulter + default_int_lit_in_type's tuple arm resolve both to i64 so
    // lower_type never ICEs on a stray IntLit.
    assert_eq!(neg("    let (x, y) = (1, 2);\n    return 0 - (x + y);"), 3);
}

#[test]
fn tuple_param_round_trip() {
    // A tuple passed as a parameter, destructured in the callee.
    let src = tool_with(
        "fn sum_pair(p: (i64, i64)) -> i64 { let (a, b) = p; return a + b; }",
        "    let pair = (40, 2);\n    return 0 - sum_pair(pair);",
    );
    assert_eq!(decode(&src), 42);
}

#[test]
fn grouping_parens_unchanged() {
    // ET-8: a no-comma `(e)` stays plain grouping — the precedence override must
    // be byte-identical to the pre-tuple behavior.
    assert_eq!(neg("    let x = (1 + 2) * 3;\n    return 0 - x;"), 9);
}
