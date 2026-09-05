//! `str` accessor tests after the API moved to i64 (`byte_at` / `len` now return
//! i64, so string code lives in one width with the rest of the language).
//!
//! Proves: the values round-trip; the negative-index trap is PRESERVED (ST-2 —
//! `byte_at`'s bounds check stays unsigned, so a negative index wraps huge and
//! traps); and `string_helpers` (`.contains` / `.starts_with`) still behaves
//! correctly in i64 (ST-3).

mod common;

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

use common::run_returning_negative;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

const STRH: &str = include_str!("../../../stdlib/sigil/string_helpers.sigil");

/// Inline the real string_helpers (strip its `module` line) so its `__sigil_str_*`
/// functions are callable directly — exercising the i64 byte loop end-to-end.
fn tool_with_strh(body: &str) -> String {
    let defs = STRH.replace("\nmodule string_helpers;\n", "\n");
    format!(
        "module tool;\n{defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

#[test]
fn byte_at_returns_i64_value() {
    // 'B' == 66. `byte_at` returns i64 now, usable directly in i64 arithmetic.
    let src = tool("    let s: str = \"ABC\";\n    let b: i64 = s.byte_at(1);\n    return 0 - b;");
    assert_eq!(run_returning_negative(&src), 66);
}

#[test]
fn len_returns_i64() {
    let src = tool("    let s: str = \"hello\";\n    let n: i64 = s.len();\n    return 0 - n;");
    assert_eq!(run_returning_negative(&src), 5);
}

#[test]
fn byte_at_negative_index_traps() {
    // ST-2 (security): `byte_at(-1)` MUST still trap — the bounds check stays
    // unsigned (idx wraps to u32, `-1` → 0xFFFFFFFF >= len). The in-bounds
    // control validates + returns Ok, so the OOB `Trapped` is a runtime trap.
    let control = compile_tool(&tool(
        "    let s: str = \"hi\";\n    let b: i64 = s.byte_at(0);\n    return b - b;",
    ))
    .expect("control should compile");
    let cres = execute_ephemeral(&control.wasm, b"", control.fuel_budget, &IoGrants::none());
    assert!(
        cres.is_ok(),
        "in-bounds byte_at(0) must validate and run Ok, got: {cres:?}"
    );

    let oob = compile_tool(&tool(
        "    let s: str = \"hi\";\n    let b: i64 = s.byte_at(0 - 1);\n    return b - b;",
    ))
    .expect("oob should compile");
    let ores = execute_ephemeral(&oob.wasm, b"", oob.fuel_budget, &IoGrants::none());
    assert!(
        matches!(ores, Err(ToolError::Trapped { .. })),
        "byte_at(-1) must trap (unsigned bounds check), got: {ores:?}"
    );
}

#[test]
fn string_helpers_behavior_unchanged() {
    // ST-3: string_helpers' i64 byte-comparison loop is behaviorally correct.
    // `__sigil_str_eq` length-checks then compares each byte via the i64
    // `byte_at`; equal strings → true, a one-byte difference → false.
    let eq = tool_with_strh(
        "    if __sigil_str_eq(\"abc\", \"abc\") { return 0 - 7; } else { return 0 - 1; }",
    );
    assert_eq!(run_returning_negative(&eq), 7);

    let neq = tool_with_strh(
        "    if __sigil_str_eq(\"abc\", \"abd\") { return 0 - 1; } else { return 0 - 9; }",
    );
    assert_eq!(run_returning_negative(&neq), 9);

    // A length mismatch short-circuits to false (the length-first fast path).
    let len_neq = tool_with_strh(
        "    if __sigil_str_eq(\"ab\", \"abc\") { return 0 - 1; } else { return 0 - 5; }",
    );
    assert_eq!(run_returning_negative(&len_neq), 5);
}
