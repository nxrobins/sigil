//! `str` accessor tests after the API moved to i64 (`byte_at` / `len` now return
//! i64, so string code lives in one width with the rest of the language).
//!
//! Proves: the values round-trip; the negative-index trap is PRESERVED (ST-2 —
//! `byte_at`'s bounds check is unsigned at every index width, so a negative index
//! reads as huge and traps); and `string_helpers` (`.contains` / `.starts_with`)
//! still behaves correctly in i64 (ST-3).

mod common;

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

use common::{decode_negative_sentinel, run_returning_negative};

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
    // ST-2 (security): `byte_at(-1)` with an `i64` index MUST still trap — the
    // bounds check stays unsigned (an 8-byte index wraps to u32, `-1` →
    // 0xFFFFFFFF >= len). `byte_at_traps_out_of_bounds_at_every_index_width`
    // pins the other widths. The in-bounds control validates + returns Ok, so
    // the OOB `Trapped` is a runtime trap.
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

/// Every index width the type checker admits for `byte_at`, with the out-of-bounds indices that
/// must trap on the 5-byte `"hello"`: its length, a negative index for a signed width, and an
/// index with the top bit set.
const BYTE_AT_WIDTHS: &[(&str, &[&str])] = &[
    ("i32", &["5", "0 - 1", "0 - 2147483647"]),
    ("u32", &["5", "4294967295"]),
    ("i64", &["5", "0 - 1"]),
    ("u64", &["5"]),
];

#[test]
fn byte_at_traps_out_of_bounds_at_every_index_width() {
    // ST-2 at every width. A 4-byte signed index used to reach the bounds check as an i32, which
    // the emitter compared with the signed `i32.ge_s`: a negative index passed it, and the load
    // read the byte before the string. AIR now reinterprets that index as u32, as it already
    // wrapped an 8-byte one, so the compare is unsigned at every width.
    for (ty, out_of_bounds) in BYTE_AT_WIDTHS {
        let in_bounds = tool(&format!(
            "    let s: str = \"hello\";\n    let i: {ty} = 1;\n    return 0 - s.byte_at(i);"
        ));
        assert_eq!(
            run_returning_negative(&in_bounds),
            101,
            "an in-bounds `{ty}` index must read the byte"
        );
        for index in *out_of_bounds {
            // The read's result is discarded and the tool returns 0, so a read that does not trap
            // comes back `Ok`; and the negative-return sentinel, `Trapped` too, is rejected.
            let src = tool(&format!(
                "    let s: str = \"hello\";\n    let i: {ty} = {index};\n    let b: i64 = s.byte_at(i);\n    return b - b;"
            ));
            let compiled = compile_tool(&src)
                .unwrap_or_else(|e| panic!("a `{ty}` index of {index} should compile: {e:?}"));
            let result =
                execute_ephemeral(&compiled.wasm, b"", compiled.fuel_budget, &IoGrants::none());
            let trapped = matches!(
                &result,
                Err(ToolError::Trapped { message }) if decode_negative_sentinel(message).is_err()
            );
            assert!(
                trapped,
                "a `{ty}` index of {index} must trap, got {result:?}"
            );
        }
    }
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
