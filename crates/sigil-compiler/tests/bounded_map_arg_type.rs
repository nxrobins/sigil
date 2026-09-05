//! BoundedMap/Set (Phase 4): method-argument TYPE checking. Companion to
//! `bounded_map_seal.rs`. The construction-seal (T258) guarantees the `count`
//! invariant cannot be forged; this file guards the orthogonal hole that a
//! method ARGUMENT of the wrong type (`m.insert(1, "x")` where the value is
//! declared `i64`) must be rejected at typecheck — NOT silently accepted and
//! then exploded as invalid wasm at instantiation.
//!
//! The pre-fix laxness was the documented "method-arg check is INT-LITERAL-only"
//! quirk: a NON-int argument (`str`/`bool`) supplied where `i64` was expected
//! escaped the per-arg check (whose inferred type was concrete `Str`/`Bool`,
//! never `IntLit`). The REVERSE — an int literal into a `str` param — was already
//! T071. The fix gives the ambient sealed bounded collections (defining module
//! `bounded_*`) the SAME strict per-arg type check the free-call path uses; the
//! general INT-LITERAL-only laxness for user impl methods (mirrored by the
//! self-hosted typechecker, pinned by the generics differential) is unchanged.

use sigil_compiler::compile_tool;

use sigil_test_utils::pipeline::compile_tool_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

/// Wrap a `tool_main` body, mirroring the seal test's harness.
fn wrap(body: &str) -> String {
    format!(
        "module tool;\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n\
         {body}\n\
         }}\n"
    )
}

// ── BoundedMap_i64_i64_64: str/bool where i64 is declared ────────────────────

#[test]
fn insert_str_value_into_i64_map_is_t071() {
    // The killer from the report: a str literal where the VALUE param is `i64`.
    let src = wrap(
        "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n\
         \x20   let _a: i64 = m.insert(1, \"x\");\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        has(&src, "T071"),
        "str value into an i64-value map must be T071, got {:?}",
        codes_of(&src)
    );
}

#[test]
fn insert_str_key_into_i64_map_is_t071() {
    // str literal where the KEY param is `i64`.
    let src = wrap(
        "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n\
         \x20   let _a: i64 = m.insert(\"k\", 5);\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        has(&src, "T071"),
        "str key into an i64-key map must be T071, got {:?}",
        codes_of(&src)
    );
}

#[test]
fn insert_bool_value_into_i64_map_is_t071() {
    let src = wrap(
        "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n\
         \x20   let _a: i64 = m.insert(1, true);\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        has(&src, "T071"),
        "bool value into an i64-value map must be T071, got {:?}",
        codes_of(&src)
    );
}

#[test]
fn get_str_key_into_i64_map_is_t071() {
    let src = wrap(
        "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n\
         \x20   let _o: Option<i64> = m.get(\"k\");\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        has(&src, "T071"),
        "str key into get() on an i64-key map must be T071, got {:?}",
        codes_of(&src)
    );
}

#[test]
fn contains_key_str_into_i64_map_is_t071() {
    let src = wrap(
        "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n\
         \x20   let _b: bool = m.contains_key(\"x\");\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        has(&src, "T071"),
        "str key into contains_key() on an i64-key map must be T071, got {:?}",
        codes_of(&src)
    );
}

#[test]
fn get_or_str_default_into_i64_map_is_t071() {
    // The DEFAULT (2nd arg) is `i64`; a str default must be rejected.
    let src = wrap(
        "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n\
         \x20   let _v: i64 = m.get_or(1, \"x\");\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        has(&src, "T071"),
        "str default into get_or() on an i64-value map must be T071, got {:?}",
        codes_of(&src)
    );
}

#[test]
fn try_insert_str_value_into_i64_map_is_t071() {
    let src = wrap(
        "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n\
         \x20   let _ok: bool = m.try_insert(1, \"x\");\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        has(&src, "T071"),
        "str value into try_insert() on an i64-value map must be T071, got {:?}",
        codes_of(&src)
    );
}

#[test]
fn insert_str_variable_value_into_i64_map_is_t071() {
    // Not just literals: a str VARIABLE where `i64` is declared also escaped
    // pre-fix (the inferred arg type was `Str`, concrete, never `IntLit`).
    let src = wrap(
        "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n\
         \x20   let s: str = \"x\";\n\
         \x20   let _a: i64 = m.insert(1, s);\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        has(&src, "T071"),
        "str VARIABLE value into an i64-value map must be T071, got {:?}",
        codes_of(&src)
    );
}

// ── BoundedMap_str_i64_64: the i64-VALUE positions ───────────────────────────

#[test]
fn insert_str_value_into_str_i64_map_is_t071() {
    // str key is CORRECT here; the VALUE param is `i64`, so a str value rejects.
    let src = wrap(
        "    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();\n\
         \x20   let _a: i64 = m.insert(\"k\", \"v\");\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        has(&src, "T071"),
        "str value into the i64-value position of a str->i64 map must be T071, got {:?}",
        codes_of(&src)
    );
}

#[test]
fn get_or_str_default_into_str_i64_map_is_t071() {
    let src = wrap(
        "    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();\n\
         \x20   let _v: i64 = m.get_or(\"k\", \"x\");\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        has(&src, "T071"),
        "str default into the i64-value position of get_or() must be T071, got {:?}",
        codes_of(&src)
    );
}

// ── BoundedSet (same defining-module family) ─────────────────────────────────

#[test]
fn set_insert_str_into_i64_set_is_t071() {
    let src = wrap(
        "    let mut s: BoundedSet_i64_64 = BoundedSet_i64_64::new();\n\
         \x20   let _a: bool = s.insert(\"x\");\n\
         \x20   return 0 - s.len();",
    );
    assert!(
        has(&src, "T071"),
        "str element into an i64 set must be T071, got {:?}",
        codes_of(&src)
    );
}

// ── Positive controls: correctly-typed args still compile ────────────────────

#[test]
fn correctly_typed_args_still_compile() {
    // i64->i64: i64 args.
    let ok_i64 = wrap(
        "    let mut m: BoundedMap_i64_i64_64 = BoundedMap_i64_i64_64::new();\n\
         \x20   let _a: i64 = m.insert(1, 2);\n\
         \x20   let _v: i64 = m.get_or(1, 0);\n\
         \x20   let _b: bool = m.contains_key(1);\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        compile_tool(&ok_i64).is_ok(),
        "well-typed i64 map calls must compile: {:?}",
        codes_of(&ok_i64)
    );

    // str->i64: str key + i64 value is correct.
    let ok_str_i64 = wrap(
        "    let mut m: BoundedMap_str_i64_64 = BoundedMap_str_i64_64::new();\n\
         \x20   let _a: i64 = m.insert(\"k\", 5);\n\
         \x20   let _v: i64 = m.get_or(\"k\", 0);\n\
         \x20   return 0 - m.len();",
    );
    assert!(
        compile_tool(&ok_str_i64).is_ok(),
        "well-typed str->i64 map calls must compile: {:?}",
        codes_of(&ok_str_i64)
    );
}
