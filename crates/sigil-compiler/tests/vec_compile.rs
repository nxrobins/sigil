//! Compile-level tests for the growable `Vec<T>` (PR B).
//!
//! Two jobs:
//!   * CF7 — the SHIPPED artifact is validated: `stdlib/sigil/vec.sigil`
//!     type-checks verbatim as a standalone `module vec;`.
//!   * T075 — `vec_load` / `vec_store` reject non-integer base/index/bound
//!     arguments (the address operands the bound-trap and pointer math
//!     depend on). These inline sources are NOT `.sigil` files on disk, so
//!     the privacy gate (`vec_quarantine.rs`) does not apply to them.

use sigil_compiler::compile_named_module;

fn codes_of(source: &str, label: &str) -> Vec<String> {
    match compile_named_module(format!("vec_{label}.sigil"), source.to_string()) {
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

/// CF7: the verbatim shipped stdlib vector type-checks as its own module.
#[test]
fn vec_sigil_type_checks_standalone() {
    let source = include_str!("../../../stdlib/sigil/vec.sigil");
    assert_clean(source, "stdlib");
}

// A local Vec-shaped record (field layout matches stdlib/sigil/vec.sigil) so
// the `vec_load` witness resolves without cross-module availability (PR C).
// The malformed calls sit in CONCRETE free functions — type-checked directly,
// no monomorphization needed — so the integer guard actually runs.
const REC: &str = "record V<T> { buf: i64, count: i64, slots: i64, alloc: i64 }";

#[test]
fn vec_store_rejects_non_integer_base() {
    // base must be an integer address; a bool is rejected.
    let source = format!(
        "module tool;\n{REC}\nfn evil(flag: bool, val: i64) -> i64 {{\n  vec_store(flag, 0, 1, val);\n  return 0;\n}}\n"
    );
    assert_has(&source, "store_base", "T075");
}

#[test]
fn vec_store_rejects_non_integer_index() {
    let source = format!(
        "module tool;\n{REC}\nfn evil(buf: i64, flag: bool, val: i64) -> i64 {{\n  vec_store(buf, flag, 1, val);\n  return 0;\n}}\n"
    );
    assert_has(&source, "store_index", "T075");
}

#[test]
fn vec_load_rejects_non_integer_bound() {
    // The 3rd arg (bound) gates the trap; a bool bound is rejected.
    let source = format!(
        "module tool;\n{REC}\nfn evil(buf: i64, index: i64, flag: bool, w: V) -> i64 {{\n  return vec_load(buf, index, flag, w);\n}}\n"
    );
    assert_has(&source, "load_bound", "T075");
}

// PR C1 — associated functions (`Type::func()`). A phantom-`T` record whose
// no-`self` `make()` is the construction site: `T` can ONLY be bound from the
// binding's annotation via the return type (return-type-directed inference).
const ASSOC: &str = "record Box<T> { v: i64 }\nimpl Box<T> {\n  pub fn make() -> Box<T> {\n    return Box { v: 0 };\n  }\n}";

#[test]
fn associated_fn_infers_type_param_from_annotation() {
    // `Box::make()` reroutes to the impl's no-self assoc fn; the annotation
    // `Box<i64>` binds `T` → clean compile.
    let source = format!(
        "module tool;\n{ASSOC}\nfn use_it() -> i64 {{\n  let b: Box<i64> = Box::make();\n  return 0;\n}}\n"
    );
    assert_clean(&source, "assoc_annotated");
}

#[test]
fn associated_fn_without_expected_type_is_t150() {
    // AG-C2: no annotation / expected type to bind `T` (and turbofish on an
    // associated fn does not parse) — fail closed with T150, not a silent bind.
    let source = format!(
        "module tool;\n{ASSOC}\nfn use_it() -> i64 {{\n  let b = Box::make();\n  return 0;\n}}\n"
    );
    assert_has(&source, "assoc_unannotated", "T150");
}

// ── PR #135: record-field expected-type propagation ──────────────────────

#[test]
fn record_field_vec_new_infers() {
    // #135: the field's declared `Vec<i64>` is the expected type for the value,
    // so `Vec::new()` infers `T=i64` (previously T150). `Vec<i64>` triggers
    // ambient injection so `Vec` resolves.
    let src = "module tool;\nrecord Holder { items: Vec<i64> }\nfn use_it() -> i64 ! { Alloc } {\n  let h: Holder = Holder { items: Vec::new() };\n  let a: i64 = h.items.push(5);\n  return h.items.len();\n}\n";
    assert_clean(src, "holder_field");
}

#[test]
fn record_field_i32_literal_narrows() {
    // A bare i32 field literal narrows to the declared width.
    let src = "module tool;\nrecord P { x: i32 }\nfn use_it() -> i64 {\n  let p: P = P { x: 11 };\n  return 0;\n}\n";
    assert_clean(src, "field_i32");
}

#[test]
fn record_field_i32_overflow_rejected() {
    // CF-I3: a literal that does NOT fit the field's concrete type is a hard
    // error, never a silent i64 default into an i32 slot.
    let src = "module tool;\nrecord P { x: i32 }\nfn use_it() -> i64 {\n  let p: P = P { x: 2147483648 };\n  return 0;\n}\n";
    let codes = codes_of(src, "field_overflow");
    assert!(
        !codes.is_empty(),
        "an oversized i32 field literal must be rejected, got clean compile"
    );
}

// ── PR #132: call-arg / assoc-fn literal width ───────────────────────────

#[test]
fn free_fn_i32_literal_narrows() {
    let src = "module tool;\nfn f(x: i32) -> i64 { return 0; }\nfn caller() -> i64 {\n  let r: i64 = f(11);\n  return r;\n}\n";
    assert_clean(src, "freefn_i32");
}

#[test]
fn free_fn_i32_overflow_rejected() {
    // CF-I3: the existing call-arg compat loop rejects a non-fitting literal.
    let src = "module tool;\nfn f(x: i32) -> i64 { return 0; }\nfn caller() -> i64 {\n  let r: i64 = f(2147483648);\n  return r;\n}\n";
    assert_has(src, "freefn_overflow", "T071");
}

#[test]
fn free_fn_vec_new_arg_infers() {
    // #136: `Vec::new()` as a call argument infers `T` from the parameter type
    // (the expected-type GUARD at free-fn call args). Previously T150.
    let src = "module tool;\nfn take(v: Vec<i64>) -> i64 ! { Alloc } { return v.len(); }\nfn caller() -> i64 ! { Alloc } {\n  let r: i64 = take(Vec::new());\n  return r;\n}\n";
    assert_clean(src, "freefn_vec_new");
}

#[test]
fn assoc_fn_i32_overflow_rejected() {
    // CF-I3: the assoc-fn path (1D) now has a per-arg width check.
    let src = "module tool;\nrecord Q<T> { v: i64 }\nimpl Q<T> {\n  pub fn mk(n: i32) -> Q<T> { return Q { v: 0 }; }\n}\nfn caller() -> i64 {\n  let q: Q<i64> = Q::mk(2147483648);\n  return 0;\n}\n";
    assert_has(src, "assoc_overflow", "T071");
}

// ── Generic-construction inference (GAP 1 + GAP 2) ────────────────────────

#[test]
fn generic_record_field_construction_infers() {
    // GAP 1 / Fix B: a generic record holding `Vec<V>`; `make()` constructs it
    // with a nested `Vec::new()` whose `T` must bind to the impl param `V` from
    // the monomorphized return type `W<i64>`. Previously T150.
    let src = "module tool;\nrecord W<V> { items: Vec<V> }\nimpl W<V> {\n  pub fn make() -> W<V> { return W { items: Vec::new() }; }\n}\nfn use_it() -> i64 ! { Alloc } {\n  let w: W<i64> = W::make();\n  let a: i64 = w.items.push(5);\n  return w.items.len();\n}\n";
    assert_clean(src, "generic_record_W");
}

#[test]
fn multi_generic_field_record_substitutes_each() {
    // CF-C1: a record with TWO distinct generic fields; each nested `Vec::new()`
    // binds to its OWN param (A→i64, B→i32) independently — proving the subst is
    // not single-param-special-cased.
    let src = "module tool;\nrecord Two<A, B> { xs: Vec<A>, ys: Vec<B> }\nimpl Two<A, B> {\n  pub fn make() -> Two<A, B> { return Two { xs: Vec::new(), ys: Vec::new() }; }\n}\nfn use_it() -> i64 ! { Alloc } {\n  let t: Two<i64, i32> = Two::make();\n  let a: i64 = t.xs.push(7);\n  let b: i64 = t.ys.push(11);\n  return t.xs.len() + t.ys.len();\n}\n";
    assert_clean(src, "two_generic_fields");
}

#[test]
fn concrete_none_binds_from_return_type() {
    // GAP 2 / Fix A (concrete): a bare `None` in a NON-generic function returning
    // `Option<i64>` must bind its param from the return type. Previously T049 even
    // for concrete code (the bug that blocked `get -> Option<i64>` for ANY map).
    let src = "module tool;\nfn f(x: i64) -> Option<i64> {\n  if x > 0 { return Some(x); } else { return None; }\n}\nfn use_it() -> i64 {\n  let o: Option<i64> = f(5);\n  return o.unwrap_or(0);\n}\n";
    assert_clean(src, "concrete_none");
}

#[test]
fn user_enum_bare_variant_binds_no_special_casing() {
    // CF-C1: Fix A is NOT special-cased to `Option`/`None`. A USER enum's bare
    // no-payload variant binds its param from the return type the same way — a
    // second enum, proving the fix reads `enum_name`/`type_params` generically.
    let src = "module tool;\nenum MyOpt<T> { Has(T), Empty }\nfn g(x: i64) -> MyOpt<i64> {\n  if x > 0 { return Has(x); } else { return Empty; }\n}\nfn use_it() -> i64 {\n  let m: MyOpt<i64> = g(5);\n  return 0;\n}\n";
    assert_clean(src, "user_enum_empty");
}

// ── Method-arg soundness: a machine-int (`i64`/`i32`/…) parameter must REJECT a
// concrete, non-int-literal, incompatible arg (`str`/`bool`/record). Before the
// fix the method-arg check was IntLit-only, so `bx.set("x")` (param `x: i64`)
// type-checked CLEAN and then produced invalid wasm at instantiation. The
// symmetric str-param direction was already rejected; this closes the
// machine-int direction. A plain USER record method reproduces it with no stdlib
// dependency — the gap is pre-existing, not specific to BoundedVec/BoundedMap. ──

// `set` mirrors the minimal repro: a `@Mut self` method whose only explicit
// param is `x: i64`.
const CELL: &str = "record Cell { v: i64 }\nimpl Cell {\n  pub fn set(self: Cell @Mut, x: i64) -> i64 {\n    self.v = x;\n    return x;\n  }\n}";

#[test]
fn method_i64_param_rejects_str_arg() {
    // The killer: a `str` literal where the method param is `i64`. Was clean →
    // invalid wasm; now T071 at compile time.
    let src = format!(
        "module tool;\n{CELL}\nfn use_it() -> i64 {{\n  let mut bx: Cell = Cell {{ v: 0 }};\n  let _r: i64 = bx.set(\"x\");\n  return 0;\n}}\n"
    );
    assert_has(&src, "method_i64_str", "T071");
}

#[test]
fn method_i64_param_rejects_bool_arg() {
    // `bool` is also a concrete, non-IntLit, i64-incompatible type → T071.
    let src = format!(
        "module tool;\n{CELL}\nfn use_it() -> i64 {{\n  let mut bx: Cell = Cell {{ v: 0 }};\n  let _r: i64 = bx.set(true);\n  return 0;\n}}\n"
    );
    assert_has(&src, "method_i64_bool", "T071");
}

#[test]
fn method_i64_param_accepts_int_literal() {
    // IntLit→machine-int flex is PRESERVED: a bare int literal still narrows to
    // the `i64` param and compiles clean.
    let src = format!(
        "module tool;\n{CELL}\nfn use_it() -> i64 {{\n  let mut bx: Cell = Cell {{ v: 0 }};\n  let _r: i64 = bx.set(5);\n  return 0;\n}}\n"
    );
    assert_clean(&src, "method_i64_intlit");
}

#[test]
fn method_i64_param_accepts_same_type_var() {
    // A same-typed `i64` variable is compatible — no false positive.
    let src = format!(
        "module tool;\n{CELL}\nfn use_it() -> i64 {{\n  let mut bx: Cell = Cell {{ v: 0 }};\n  let n: i64 = 3;\n  let _r: i64 = bx.set(n);\n  return 0;\n}}\n"
    );
    assert_clean(&src, "method_i64_same_var");
}

// The fix is scoped to the machine-int param family, not just `i64`. An `i32`
// param given a `str` arg is rejected the same way.
const CELL32: &str = "record Cell32 { v: i32 }\nimpl Cell32 {\n  pub fn set(self: Cell32 @Mut, x: i32) -> i32 {\n    self.v = x;\n    return x;\n  }\n}";

#[test]
fn method_i32_param_rejects_str_arg() {
    let src = format!(
        "module tool;\n{CELL32}\nfn use_it() -> i64 {{\n  let mut bx: Cell32 = Cell32 {{ v: 0 }};\n  let _r: i32 = bx.set(\"x\");\n  return 0;\n}}\n"
    );
    assert_has(&src, "method_i32_str", "T071");
}
