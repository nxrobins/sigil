//! Return-type-directed generic inference (PR A).
//!
//! Free-function type args are inferred by unifying formals with argument
//! types; a type param that appears only in the RETURN (e.g. a constructor
//! `fn make<T>() -> Holder<T>`) was previously an unconditional `T150`
//! ("could not infer — use turbofish"). This PR adds a fill-unbound-only
//! fallback: when the arguments leave a param unbound AND there is an
//! expected type (the let-annotation context), unify the formal return
//! type against it. `unify` is `or_insert_with`, so arg-derived bindings
//! are never overwritten and genuine conflicts still surface at the normal
//! compatibility check.
//!
//! This makes `let v: Vec<i64> = Vec::new();` ergonomic (PR B/C) and is a
//! general win for any return-typed generic constructor.

use sigil_compiler::compile_named_module;

fn codes_of(source: &str, label: &str) -> Vec<String> {
    match compile_named_module(format!("rti_{label}.sigil"), source) {
        Ok(_) => Vec::new(),
        Err(err) => err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn assert_clean(source: &str, label: &str) {
    let codes = codes_of(source, label);
    assert!(
        codes.is_empty(),
        "expected clean compile for {label}, got: {codes:?}"
    );
}

fn assert_has(source: &str, label: &str, code: &str) {
    let codes = codes_of(source, label);
    assert!(
        codes.iter().any(|c| c == code),
        "expected {code} for {label}, got: {codes:?}"
    );
}

// A phantom-generic record: `T` appears in NO field (mirrors `Vec<T>`'s
// raw-buffer layout). Construction seeds `T` from the let-annotation.
const HOLDER: &str = "record Holder<T> { tag: i64 }\n\
fn make<T>() -> Holder<T> {\n    return Holder { tag: 0 };\n}\n";

#[test]
fn return_type_inferred_from_let_annotation() {
    // `make()` has no args binding `T`; `T` is filled from the annotation
    // `Holder<i64>` — no turbofish needed.
    let source = format!(
        "module main;\n{HOLDER}\nfn boot() -> i64 {{\n    let x: Holder<i64> = make();\n    return x.tag;\n}}\n"
    );
    assert_clean(&source, "inferred");
}

#[test]
fn no_annotation_still_requires_turbofish() {
    // Without an expected type there is nothing to fill from → T150 stands.
    let source = format!(
        "module main;\n{HOLDER}\nfn boot() -> i64 {{\n    let x = make();\n    return x.tag;\n}}\n"
    );
    assert_has(&source, "no_anno", "T150");
}

#[test]
fn turbofish_still_works() {
    let source = format!(
        "module main;\n{HOLDER}\nfn boot() -> i64 {{\n    let x: Holder<i64> = make::<i64>();\n    return x.tag;\n}}\n"
    );
    assert_clean(&source, "turbofish");
}

#[test]
fn arg_derived_inference_unchanged() {
    // The pre-existing path: `T` bound from the argument, no annotation
    // needed. The new fallback must not perturb this.
    let source = r#"
module main;
fn id<T>(x: T) -> T { return x; }
fn boot() -> i64 {
    let y: i64 = id(5);
    return y;
}
"#;
    assert_clean(source, "arg_derived");
}

#[test]
fn arg_vs_annotation_conflict_is_not_masked() {
    // `wrap(5)` binds `T = i64` from the argument (all params arg-bound),
    // so the return-type fallback is SKIPPED. The result `Holder<i64>`
    // against the `Holder<bool>` annotation is a genuine mismatch — it
    // must be rejected, not silently coerced to `bool`.
    let source = r#"
module main;
record Holder<T> { tag: i64 }
fn wrap<T>(x: T) -> Holder<T> {
    return Holder { tag: 0 };
}
fn boot() -> i64 {
    let h: Holder<bool> = wrap(5);
    return h.tag;
}
"#;
    // Some type-mismatch diagnostic must fire (the conflict is caught by
    // the normal value/annotation compatibility check, not masked).
    let codes = codes_of(source, "conflict");
    assert!(
        !codes.is_empty(),
        "arg-vs-annotation conflict must be rejected, but compiled clean"
    );
}
