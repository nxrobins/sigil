//! Array-repeat expression literal `[elem; N]` (COMPLETENESS array ergonomics).
//!
//! `[elem; N]` desugars at PARSE time into an `N`-element array literal, mirroring
//! the type-position `[T; N]` grammar (a strict `IntLit` count in 0..=65535, T239
//! on deviation). The element must be a LITERAL so cloning it `N` times equals
//! evaluating it once — a side-effecting element is a parse error, not a silent
//! `N`-fold evaluation. An array literal carries NO `Alloc` effect, so these tools
//! compile with NO `! { Alloc }` (the same bounded-region thesis BoundedVec rests
//! on). This is the enabler that makes large `BoundedVec_i64_N` `new()` bodies
//! readable (`[0; 256]`) instead of a hand-counted 256-zero literal.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Tool with NO `! { Alloc }` effect — an array literal is Alloc-free.
fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

/// Run a `0 - value` tool body and recover `value` from the negative sentinel.
fn neg(body: &str) -> i64 {
    let result = compile_tool(&tool(body)).expect("tool should compile");
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

/// Diagnostic codes from compiling a tool (empty = clean).
fn codes_of(src: &str) -> Vec<String> {
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
    codes_of(src).iter().any(|c| c == code)
}

// ── the repeat form produces N copies of the element ─────────────────────────

#[test]
fn repeat_zeros_is_all_zero() {
    // Sum ALL eight slots plus a `1` base: a clean 1 proves every slot is 0
    // (and keeps the payload strictly positive for the negative-sentinel decode).
    let body = "    let a: [i64; 8] = [0; 8];\n\
        \x20   return 0 - (a[0] + a[1] + a[2] + a[3] + a[4] + a[5] + a[6] + a[7] + 1);";
    assert_eq!(neg(body), 1);
}

#[test]
fn repeat_nonzero_fills_every_slot() {
    // [7; 4] == [7, 7, 7, 7]: sum the four slots explicitly.
    let body = "    let a: [i64; 4] = [7; 4];\n    return 0 - (a[0] + a[1] + a[2] + a[3]);";
    assert_eq!(neg(body), 28);
}

#[test]
fn repeat_single_element() {
    let body = "    let a: [i64; 1] = [5; 1];\n    return 0 - a[0];";
    assert_eq!(neg(body), 5);
}

#[test]
fn repeat_large_256_runs_in_ephemeral() {
    // Pre-validates that a 256-slot backing (what BoundedVec_i64_256 needs) both
    // compiles and runs inside the ephemeral fuel/memory budget. Probe the ends.
    let body = "    let a: [i64; 256] = [3; 256];\n    return 0 - (a[0] * 10 + a[255]);";
    assert_eq!(neg(body), 33);
}

#[test]
fn repeat_matches_explicit_literal() {
    // `[9; 3]` and `[9, 9, 9]` must be indistinguishable downstream.
    let r = "    let a: [i64; 3] = [9; 3];\n    return 0 - (a[0] + a[1] + a[2]);";
    let e = "    let a: [i64; 3] = [9, 9, 9];\n    return 0 - (a[0] + a[1] + a[2]);";
    assert_eq!(neg(r), neg(e));
    assert_eq!(neg(r), 27);
}

// ── the grammar is strict: count range + literal element ─────────────────────

#[test]
fn repeat_count_out_of_range_is_t239() {
    // 70000 > 65535 — the same bound the type-position `[T; N]` enforces.
    let src = tool("    let a: [i64; 4] = [0; 70000];\n    return 0 - a[0];");
    assert!(
        has(&src, "T239"),
        "out-of-range repeat count: {:?}",
        codes_of(&src)
    );
}

#[test]
fn repeat_nonliteral_element_is_rejected() {
    // `[input_ptr; 4]`: a non-literal (side-effect-capable) element is a parse
    // error, NOT a silent 4-fold evaluation. (`input_ptr` is a param Path expr.)
    let src = tool("    let a: [i64; 4] = [input_ptr; 4];\n    return 0 - a[0];");
    assert!(
        has(&src, "P001"),
        "non-literal repeat element must be rejected: {:?}",
        codes_of(&src)
    );
}

// ── the comma form is untouched (regression guard for the parser refactor) ───

#[test]
fn comma_form_still_works() {
    assert_eq!(
        neg("    let a: [i64; 3] = [10, 20, 30];\n    return 0 - (a[0] + a[1] + a[2]);"),
        60
    );
}
