//! PR-E3a (ET-E1): the RUNTIME round-trip for string interpolation `f"…{e}…"`.
//!
//! The three differentials check TYPES and NODES, not bytes. This file compiles +
//! EXECUTES the wasm and asserts the exact output bytes — the only check that the
//! whole pipeline (lex → parse → Option-2b typecheck → `str_concat`-chain lowering →
//! AIR → wasm) actually produces the right string. The `FStrBegin` ambient trigger
//! injects `string.sigil` (so the lowered `str_concat` resolves); the enclosing fn
//! declares `! { Alloc }` because the lowered concat allocates.
//!
//! PR-E3a holes are `str` only; i64/bool auto-conversion arrives in PR-E3b.

use sigil_compiler::compile_tool;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Compile a `module tool` whose `tool_main` returns the f-string `body` builds, run
/// it, and return the emitted output as a `String`.
fn run_out(body: &str) -> String {
    let src = format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    );
    let result = compile_tool(&src).expect("f-string tool should compile");
    let exec = execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none())
        .expect("f-string tool executes");
    String::from_utf8(exec.output).expect("output is UTF-8")
}

#[test]
fn fstring_literal_and_hole() {
    // `f"hello {s}ld"` with s = "wor" → "hello world".
    let out = run_out(
        "    let s: str = \"wor\";\n\
         \x20   let r: str = f\"hello {s}ld\";\n\
         \x20   return r.as_output();",
    );
    assert_eq!(out, "hello world");
}

#[test]
fn fstring_empty() {
    // `f""` → "" (an empty str).
    let out = run_out(
        "    let r: str = f\"\";\n\
         \x20   return r.as_output();",
    );
    assert_eq!(out, "");
}

#[test]
fn fstring_hole_only_is_fresh_copy() {
    // `f"{s}"` → a fresh copy of s (ET-E4: never a bare alias of the hole).
    let out = run_out(
        "    let s: str = \"abc\";\n\
         \x20   let r: str = f\"{s}\";\n\
         \x20   return r.as_output();",
    );
    assert_eq!(out, "abc");
}

#[test]
fn fstring_adjacent_holes() {
    // `f"{a}{b}"` — empty chunk between adjacent holes (ET-E3) lowers cleanly.
    let out = run_out(
        "    let a: str = \"foo\";\n\
         \x20   let b: str = \"bar\";\n\
         \x20   let r: str = f\"{a}{b}\";\n\
         \x20   return r.as_output();",
    );
    assert_eq!(out, "foobar");
}

#[test]
fn fstring_utf8_chunks() {
    // ET-E6: multi-byte UTF-8 chunks survive whole around a hole.
    let out = run_out(
        "    let s: str = \"x\";\n\
         \x20   let r: str = f\"héllo {s} 日本\";\n\
         \x20   return r.as_output();",
    );
    assert_eq!(out, "héllo x 日本");
}

#[test]
fn fstring_leading_and_trailing_text() {
    // Literal runs before the first hole and after the last.
    let out = run_out(
        "    let n: str = \"42\";\n\
         \x20   let r: str = f\"id={n}!\";\n\
         \x20   return r.as_output();",
    );
    assert_eq!(out, "id=42!");
}

// ── PR-E3b: i64 / bool holes auto-convert (str_itoa / str_of_bool) ────────────

#[test]
fn fstring_i64_hole() {
    // An i64 hole renders via str_itoa.
    let out = run_out(
        "    let n: i64 = 42;\n\
         \x20   let r: str = f\"x={n}\";\n\
         \x20   return r.as_output();",
    );
    assert_eq!(out, "x=42");
}

#[test]
fn fstring_i64_negative_hole() {
    // Negative i64 (str_itoa's negative-space path) renders correctly.
    let out = run_out(
        "    let n: i64 = 0 - 7;\n\
         \x20   let r: str = f\"{n}\";\n\
         \x20   return r.as_output();",
    );
    assert_eq!(out, "-7");
}

#[test]
fn fstring_bool_holes() {
    // bool holes render via str_of_bool — both true and false.
    let out = run_out(
        "    let a: bool = true;\n\
         \x20   let b: bool = false;\n\
         \x20   let r: str = f\"{a} {b}\";\n\
         \x20   return r.as_output();",
    );
    assert_eq!(out, "true false");
}

#[test]
fn fstring_mixed_str_i64_bool() {
    // The full PR-E3b promise: str + i64 + bool holes interleaved with text.
    let out = run_out(
        "    let msg: str = \"go\";\n\
         \x20   let n: i64 = 7;\n\
         \x20   let b: bool = true;\n\
         \x20   let r: str = f\"line {n}: ok={b} — {msg}\";\n\
         \x20   return r.as_output();",
    );
    assert_eq!(out, "line 7: ok=true — go");
}
