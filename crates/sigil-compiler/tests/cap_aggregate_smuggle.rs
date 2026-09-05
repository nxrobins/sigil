//! Capability cannot be SMUGGLED through a `Type::Tuple` or `Type::Fn`
//! aggregate slot — the structural companion to T183/T184/T186/T242.
//!
//! `type_contains_cap` (type_check/resolve.rs) is the single cap-containment
//! predicate behind all four cap-aggregate gates: T183 (record fields), T184
//! (enum payloads), T186 (array elements), T242 (generic-aggregate
//! instantiation). It recursed through `Array` and `Named` but FELL THROUGH
//! (`_ => false`) for `Type::Tuple` and `Type::Fn` — so a restricted capability
//! could ride through a tuple-typed or closure-typed slot, be destructured /
//! projected / call-returned out, and Z3's authority tracker would then treat
//! it as a fresh FULL-authority cap (the exact soundness hole documented in
//! tests/fixtures/T183.sigil). Fixed by adding the `Tuple` and `Fn` arms
//! (params AND return for `Fn`); `Ref`/`Slice`/`Ptr` stay excluded on purpose —
//! a `&Fuel` is a borrow tracked by the ownership system, not an owned cap.
//!
//! Each REJECT case asserts the EXACT gate code fires; each LEGIT case asserts
//! the program still compiles cleanly (no false positives — a cap-free closure
//! or tuple field, e.g. the `Fn(i64)->i64` fields the iterator adapters rely
//! on, must remain legal).

use sigil_compiler::compile_named_module;

const PRELUDE: &str =
    "module sigil;\ncap type Fuel { burn, query }\nfn boot(x: Fuel) -> i64 { return 1; }\n";

/// Compile `PRELUDE + body`; return the sorted, de-duplicated emitted codes
/// (empty = compiled cleanly).
fn codes(body: &str) -> Vec<String> {
    match compile_named_module("cap_smuggle.sigil", format!("{PRELUDE}{body}")) {
        Ok(_) => Vec::new(),
        Err(e) => {
            let mut cs: Vec<String> = e
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_owned())
                .collect();
            cs.sort();
            cs.dedup();
            cs
        }
    }
}

fn assert_rejects_with(body: &str, code: &str) {
    let cs = codes(body);
    assert!(
        cs.iter().any(|c| c == code),
        "expected {code} for `{body}`, got {cs:?}"
    );
}

fn assert_clean(body: &str) {
    let cs = codes(body);
    assert!(
        cs.is_empty(),
        "expected clean compile for `{body}`, got {cs:?}"
    );
}

// ── REJECT: cap smuggled through a TUPLE slot ───────────────────────────────

#[test]
fn tuple_record_field_with_cap_is_t183() {
    assert_rejects_with("record W { f: (Fuel, i64) }\n", "T183");
}

#[test]
fn nested_tuple_record_field_with_cap_is_t183() {
    // Tuple-in-tuple — the recursion must descend through both.
    assert_rejects_with("record W { f: ((Fuel, i64), i64) }\n", "T183");
}

#[test]
fn array_of_tuple_with_cap_record_field_is_t183() {
    // Array<Tuple<Cap>> — Array arm (already present) ∘ Tuple arm (new).
    assert_rejects_with("record W { f: [(Fuel, i64); 2] }\n", "T183");
}

#[test]
fn tuple_enum_payload_with_cap_is_t184() {
    assert_rejects_with("enum E { V((Fuel, i64)) }\n", "T184");
}

// ── REJECT: cap smuggled through a CLOSURE slot ─────────────────────────────

#[test]
fn fn_param_cap_record_field_is_t183() {
    // `Fn(Fuel) -> i64` — cap in a closure PARAMETER position.
    assert_rejects_with("record W { f: Fn(Fuel) -> i64 }\n", "T183");
}

#[test]
fn fn_return_cap_record_field_is_t183() {
    // `Fn(i64) -> Fuel` — cap in the closure RETURN position (the call yields
    // a fresh cap); the `Fn` arm must check the return type, not just params.
    assert_rejects_with("record W { f: Fn(i64) -> Fuel }\n", "T183");
}

#[test]
fn fn_param_cap_enum_payload_is_t184() {
    assert_rejects_with("enum E { V(Fn(Fuel) -> i64) }\n", "T184");
}

// ── REJECT: cap smuggled through a generic aggregate's tuple/closure arg ─────

#[test]
fn generic_record_tuple_cap_type_arg_is_t242() {
    let body = "record Box<T> { v: T }\n\
        fn use_it() -> i64 { let b: Box<(Fuel, i64)> = Box { v: (mk(), 0) }; return 1; }\n\
        fn mk() -> Fuel { return mk(); }\n";
    assert_rejects_with(body, "T242");
}

#[test]
fn generic_record_fn_cap_type_arg_is_t242() {
    let body = "record Box<T> { v: T }\n\
        fn use_it() -> i64 { let b: Box<Fn(Fuel) -> i64> = Box { v: g() }; return 1; }\n\
        fn g() -> Fn(Fuel) -> i64 { return g(); }\n";
    assert_rejects_with(body, "T242");
}

// ── LEGIT: cap-free aggregates must still compile (no false positives) ───────

#[test]
fn cap_free_closure_field_is_legal() {
    // The iterator-adapter / closure-as-field workhorse — must stay legal.
    assert_clean("record W { f: Fn(i64) -> i64 }\n");
}

#[test]
fn cap_free_tuple_field_is_legal() {
    assert_clean("record W { f: (i64, i64) }\n");
}

#[test]
fn cap_free_tuple_enum_payload_is_legal() {
    assert_clean("enum E { V((i64, i64)) }\n");
}

#[test]
fn cap_free_generic_tuple_instantiation_is_legal() {
    assert_clean(
        "record Box<T> { v: T }\n\
         fn use_it() -> i64 { let b: Box<(i64, i64)> = Box { v: (1, 2) }; return 1; }\n",
    );
}

#[test]
fn borrowed_cap_parameter_is_not_smuggling() {
    // `&Fuel` is a BORROW tracked by the ownership system, NOT an owned cap —
    // it is deliberately excluded from `type_contains_cap`, so a fn taking a
    // `&Fuel` (or a record field holding one, where allowed) must stay legal.
    assert_clean("fn use_borrow(f: &Fuel) -> i64 { return 1; }\n");
}
