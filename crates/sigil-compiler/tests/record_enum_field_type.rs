//! Record-construction and enum-variant-construction field/payload TYPE checking.
//!
//! A record literal `R { field: value }` and an enum-variant construction
//! `E::V(value)` must validate each supplied value against the DECLARED field /
//! payload type — exactly as the function-argument path (`infer_call_expr`) does
//! via `type_compatible`. Pre-fix, the record-construction arm only special-cased
//! the integer-LITERAL-overflow case (T071) and the variant arm only checked
//! ARITY (T072); a wrong-typed non-literal value — a `bool`/`str` into an `i64`
//! field, a differently-named record into a record-typed field, a `bool` into a
//! concretely-typed enum payload slot — landed silently in the typed slot with NO
//! diagnostic, then produced a mistyped field / invalid wasm downstream. The fix
//! adds the general field-value/field-type compatibility check to both arms,
//! guarded against unresolved generics (which would ICE `type_compatible`), the
//! `IntLit`→machine-int flex, and `Type::Error` cascade.

use sigil_compiler::compile_tool;

use sigil_test_utils::pipeline::compile_tool_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

/// Wrap a `tool_main` body with the given top-level declarations (records/enums).
fn wrap(decls: &str, body: &str) -> String {
    format!(
        "module tool;\n\
         {decls}\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n\
         {body}\n\
         }}\n"
    )
}

// ── Record construction: the reported repros ─────────────────────────────────

// `R { f: true }` — a bool into an i64 field. Pre-fix: silently ACCEPTED.
#[test]
fn record_bool_into_i64_field_is_t071() {
    let src = wrap(
        "record R { f: i64 }",
        "    let r = R { f: true };\n    return 0;",
    );
    assert!(
        has(&src, "T071"),
        "bool into an i64 field must be T071, got {:?}",
        codes_of(&src)
    );
}

// `R { f: "x" }` — a str into an i64 field. Pre-fix: silently ACCEPTED.
#[test]
fn record_str_into_i64_field_is_t071() {
    let src = wrap(
        "record R { f: i64 }",
        "    let r = R { f: \"x\" };\n    return 0;",
    );
    assert!(
        has(&src, "T071"),
        "str into an i64 field must be T071, got {:?}",
        codes_of(&src)
    );
}

// A differently-named record into a record-typed field — the on-branch analog of
// the reported `u256`-into-`i256` case (both are `Type::Named` mismatches, caught
// by the same `type_compatible` Named-vs-Named arm).
#[test]
fn record_wrong_named_into_named_field_is_t071() {
    let src = wrap(
        "record A { n: i64 }\n    record B { n: i64 }\n    record H { inner: A }",
        "    let b = B { n: 1 };\n    let h = H { inner: b };\n    return 0;",
    );
    assert!(
        has(&src, "T071"),
        "record `B` into a field declared `A` must be T071, got {:?}",
        codes_of(&src)
    );
}

// A concrete field of a GENERIC record (`b: i64`) is still checked — the subst
// machinery only owns the generic-parameter fields.
#[test]
fn generic_record_concrete_field_mismatch_is_t071() {
    let src = wrap(
        "record P<T> { a: T, b: i64 }",
        "    let p: P<i64> = P { a: 1, b: true };\n    return 0;",
    );
    assert!(
        has(&src, "T071"),
        "bool into the concrete `b: i64` field of `P<i64>` must be T071, got {:?}",
        codes_of(&src)
    );
}

// A generic-parameter field pinned by the annotation (`val: T` at `Wrap<i64>`) is
// rejected — and reported exactly ONCE. The pre-existing annotation-pinning fault
// owns this case; the new general check skips generic-original fields to avoid a
// duplicate T071.
#[test]
fn generic_record_pinned_field_mismatch_is_single_t071() {
    let src = wrap(
        "record Wrap<T> { val: T }",
        "    let w: Wrap<i64> = Wrap { val: true };\n    return 0;",
    );
    let n = codes_of(&src).iter().filter(|c| *c == "T071").count();
    assert_eq!(
        n,
        1,
        "annotation-pinned `val: T` = i64 given a bool must be exactly one T071, got {:?}",
        codes_of(&src)
    );
}

// ── Record construction: positive controls (no over-tightening) ──────────────

// A correctly-typed int literal into an i64 field must STILL compile.
#[test]
fn record_int_literal_into_i64_field_compiles() {
    let src = wrap(
        "record R { f: i64 }",
        "    let r = R { f: 5 };\n    return r.f;",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "a correctly-typed `R {{ f: 5 }}` must compile, got {:?}",
        codes_of(&src)
    );
}

// An int literal narrows to a NARROWER field type (i32) — the IntLit→machine-int
// flex must survive the new check.
#[test]
fn record_int_literal_into_i32_field_compiles() {
    let src = wrap(
        "record R { f: i32 }",
        "    let r = R { f: 5 };\n    return 0;",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "an int literal narrowing into an i32 field must compile, got {:?}",
        codes_of(&src)
    );
}

// Correctly-typed bool and str fields compile.
#[test]
fn record_correct_bool_and_str_fields_compile() {
    let src = wrap(
        "record R { flag: bool, name: str }",
        "    let r = R { flag: true, name: \"hi\" };\n    return 0;",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "correctly-typed bool/str fields must compile, got {:?}",
        codes_of(&src)
    );
}

// A well-typed generic record construction compiles (no false positive from the
// generic-field screen).
#[test]
fn generic_record_correct_field_compiles() {
    let src = wrap(
        "record Wrap<T> { val: T }",
        "    let w: Wrap<i64> = Wrap { val: 5 };\n    return 0;",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "a well-typed `Wrap<i64> {{ val: 5 }}` must compile, got {:?}",
        codes_of(&src)
    );
}

// ── Enum-variant construction ────────────────────────────────────────────────

// `E::V(true)` — a bool into a monomorphic enum's i64 payload slot. Pre-fix:
// silently ACCEPTED (only arity was checked).
#[test]
fn enum_bool_into_i64_payload_is_t071() {
    let src = wrap(
        "enum E { V(i64) }",
        "    let e = E::V(true);\n    return 0;",
    );
    assert!(
        has(&src, "T071"),
        "bool into an i64 enum payload must be T071, got {:?}",
        codes_of(&src)
    );
}

// A CONCRETE payload position of a GENERIC enum (`B(T, i64)`) is checked even when
// the generic position is fine.
#[test]
fn generic_enum_concrete_payload_mismatch_is_t071() {
    let src = wrap(
        "enum Both<T> { B(T, i64) }",
        "    let e: Both<i64> = Both::B(7, true);\n    return 0;",
    );
    assert!(
        has(&src, "T071"),
        "bool into the concrete `i64` payload position of `Both::B` must be T071, got {:?}",
        codes_of(&src)
    );
}

// ── Enum-variant construction: positive controls ────────────────────────────

// `E::V(5)` — a correctly-typed int literal payload compiles.
#[test]
fn enum_int_literal_payload_compiles() {
    let src = wrap("enum E { V(i64) }", "    let e = E::V(5);\n    return 0;");
    assert!(
        compile_tool(&src).is_ok(),
        "a correctly-typed `E::V(5)` must compile, got {:?}",
        codes_of(&src)
    );
}

// A generic enum's payload (`Option<T>`) determines `T` from the value — `Some(5)`
// and `Some(true)` must both compile (the generic payload position is skipped by
// the `type_mentions_generic` screen, so no false positive).
#[test]
fn generic_enum_payload_infers_and_compiles() {
    let src = wrap(
        "",
        "    let o: Option<i64> = Some(5);\n\
         \x20   let b: Option<bool> = Some(true);\n\
         \x20   return 0;",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "`Some(5)` / `Some(true)` (generic payloads) must compile, got {:?}",
        codes_of(&src)
    );
}

fn assert_unit_variant_twins_are_byte_equal(label: &str, qualified: &str, bare: &str) {
    let qualified = compile_tool(qualified)
        .unwrap_or_else(|e| panic!("{label}: qualified control must compile: {e:?}"));
    let bare =
        compile_tool(bare).unwrap_or_else(|e| panic!("{label}: bare variant must compile: {e:?}"));
    assert_eq!(
        bare.wasm, qualified.wasm,
        "{label}: bare and qualified unit variants must register the same concrete enum layout"
    );
}

#[test]
fn generic_unit_variant_layout_is_context_independent() {
    let declaration = "enum E<T> { V(T, i64), N }";
    let qualified_let = wrap(declaration, "    let e: E<i64> = E::N;\n    return 0;");
    let bare_let = wrap(declaration, "    let e: E<i64> = N;\n    return 0;");
    assert_unit_variant_twins_are_byte_equal("annotated let", &qualified_let, &bare_let);

    let qualified_return = wrap(
        &format!("{declaration}\nfn make() -> E<i64> {{ return E::N; }}"),
        "    let e: E<i64> = make();\n    return 0;",
    );
    let bare_return = wrap(
        &format!("{declaration}\nfn make() -> E<i64> {{ return N; }}"),
        "    let e: E<i64> = make();\n    return 0;",
    );
    assert_unit_variant_twins_are_byte_equal("return", &qualified_return, &bare_return);

    let qualified_arg = wrap(
        &format!("{declaration}\nfn take(e: E<i64>) -> i64 {{ return 0; }}"),
        "    return take(E::N);",
    );
    let bare_arg = wrap(
        &format!("{declaration}\nfn take(e: E<i64>) -> i64 {{ return 0; }}"),
        "    return take(N);",
    );
    assert_unit_variant_twins_are_byte_equal("call argument", &qualified_arg, &bare_arg);

    let multi_declaration = "enum Either<A, B> { L(A), R(B), N }";
    let qualified_multi = wrap(
        multi_declaration,
        "    let e: Either<i64, str> = Either::N;\n    return 0;",
    );
    let bare_multi = wrap(
        multi_declaration,
        "    let e: Either<i64, str> = N;\n    return 0;",
    );
    assert_unit_variant_twins_are_byte_equal(
        "multi-parameter annotated let",
        &qualified_multi,
        &bare_multi,
    );
}
