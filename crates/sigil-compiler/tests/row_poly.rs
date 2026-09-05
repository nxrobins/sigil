//! Row polymorphism (roadmap Phase 4): effect-row VARIABLES on generic fns.
//!
//! `fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 ! { e }` — `e` is declared in the
//! ordinary type-param list and classified effect-kinded BY USE (it occurs in a
//! row). Bindings are inferred per call site from the actual arguments' rows
//! (union across occurrences = least solution) and instantiated by
//! MONOMORPHIZATION: the mono key gains a `$!`-prefixed row component, the
//! instance's declared row and `Fn`-typed param/return rows are concrete, and
//! `check_effects` walks each instance against its own row. No abstract row
//! reasoning exists anywhere in the checker.
//!
//! THREE PINS OF RECORD:
//!
//! 1. THE FUSING LAUNDER STAYS DEAD. Two instantiations at different rows get
//!    DISTINCT mono keys (`h__$!Log` vs `h__$!`). Under the old row-blind key
//!    they would fuse via cache-before-check and the second caller would
//!    inherit the first caller's row.
//! 2. TD-1's ROW HALF IS CLOSED. The generic call path has no
//!    `type_compatible` argument loop, so row contravariance NEVER ran for
//!    generic calls — a concrete `! { }` formal accepted an effectful closure
//!    that nothing ever charged. `bind_and_check_effect_rows` now enforces
//!    `actual_row ⊆ concrete ∪ binding` for every Fn-typed formal. (The
//!    non-row half of that hole — no structural arg compat at all — is
//!    pre-existing and filed separately.)
//! 3. v1 BORING LIMITS FAIL CLOSED (E011): free fns only; occurrences only in
//!    the declared row / top-level param-Fn row (one variable each) / return
//!    type; no shadowing, no both-kind use, no duplicates, no turbofish, no
//!    body annotations.
//!
//! SELFHOST SHADOW: the parse shadow already parses `<e>` and `! { e }` (this
//! feature added ZERO grammar), but the selfhost effect/mono shadows have no
//! row-poly awareness — row-poly fixtures stay OUT of the SH-MONO / SH-EFFECT
//! differential corpora (uncovered-not-broken; the SH-EFFECT closure-leaf
//! precedent, see effect_infer.rs's selfhost note). A future selfhost mirror
//! lifts this.

use sigil_test_utils::pipeline::{compile_module_codes, typecheck_or_panic};

// ───────────────────────── acceptance ─────────────────────────

/// THE POINT: an effectful closure crosses a row-POLYMORPHIC boundary, and the
/// caller is charged for exactly the closure's row.
#[test]
fn effectful_closure_crosses_a_row_polymorphic_boundary() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 ! { e } { return f(1); }\n\
         fn caller() -> i64 ! { Log } { return h(fn(x: i64) -> i64 { return logs(); }); }\n",
    );
    assert!(
        codes.is_empty(),
        "an effectful closure must cross a `! {{ e }}` boundary with the caller \
         declaring the instantiated row; got {codes:?}"
    );
}

/// The launder regression (the Lean mutant twin's scenario, in Rust): a PURE
/// caller passing an effectful closure through the same boundary is E001 —
/// the instantiated callee row `{Log}` is not in the caller's empty row.
#[test]
fn pure_caller_of_an_effectful_instantiation_is_e001() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 ! { e } { return f(1); }\n\
         fn caller() -> i64 { return h(fn(x: i64) -> i64 { return logs(); }); }\n",
    );
    assert!(
        codes.iter().any(|c| c == "E001"),
        "a pure caller must be charged for the instantiated row; got {codes:?}"
    );
}

/// A pure closure still satisfies the variable row (binds to the empty set).
#[test]
fn pure_closure_binds_the_variable_to_empty() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 ! { e } { return f(1); }\n\
         fn caller() -> i64 { return h(fn(x: i64) -> i64 { return x; }); }\n",
    );
    assert!(
        codes.is_empty(),
        "a pure closure instantiates `e = {{}}` and a pure caller is legal; got {codes:?}"
    );
}

/// PIN 1 — the fusing launder: the two instantiations above must be DISTINCT
/// TypedFunctions with distinct row-keyed names, each carrying its own row.
#[test]
fn two_instantiations_get_distinct_row_keyed_monos() {
    let typed = typecheck_or_panic(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 ! { e } { return f(1); }\n\
         fn effectful_use() -> i64 ! { Log } { return h(fn(x: i64) -> i64 { return logs(); }); }\n\
         fn pure_use() -> i64 { return h(fn(x: i64) -> i64 { return x; }); }\n",
    );
    let names: Vec<&str> = typed
        .modules
        .iter()
        .flat_map(|m| m.functions.iter().map(|f| f.name.as_str()))
        .collect();
    assert!(
        names.iter().any(|n| n.ends_with("h__$!Log")),
        "the {{Log}} instantiation must be keyed `h__$!Log`; got {names:?}"
    );
    assert!(
        names.iter().any(|n| n.ends_with("h__$!")),
        "the {{}} instantiation must be keyed `h__$!` (distinct instance); got {names:?}"
    );
}

/// Row-free generics keep BYTE-IDENTICAL mono keys (no `$!` component) — the
/// guard for the SH-MONO / wasm / workload pins.
#[test]
fn row_free_generics_keep_byte_identical_keys() {
    let typed = typecheck_or_panic(
        "#[ring(outer)]\nmodule app;\n\
         fn id<T>(x: T) -> T { return x; }\n\
         fn caller() -> i64 { return id(7); }\n",
    );
    let names: Vec<&str> = typed
        .modules
        .iter()
        .flat_map(|m| m.functions.iter().map(|f| f.name.as_str()))
        .collect();
    assert!(
        names.contains(&"app::id__i64"),
        "a row-free generic's key must not gain any row component; got {names:?}"
    );
    assert!(
        !names.iter().any(|n| n.contains("$!")),
        "no `$!` component may appear without a row variable; got {names:?}"
    );
}

/// Union across occurrences: two `! {{ e }}` params with different actual rows
/// bind `e` to the UNION, and the caller owes both effects.
#[test]
fn union_binding_across_two_occurrences() {
    let base = "#[ring(outer)]\nmodule app;\n\
         effect EA;\n\
         effect EB;\n\
         fn does_a() -> i64 ! { EA } { return 0; }\n\
         fn does_b() -> i64 ! { EB } { return 0; }\n\
         fn h2<e>(f: Fn(i64) -> i64 ! { e }, g: Fn(i64) -> i64 ! { e }) -> i64 ! { e } \
         { let r: i64 = f(1); return g(r); }\n";
    let both = format!(
        "{base}fn caller() -> i64 ! {{ EA, EB }} {{ return h2(\
         fn(x: i64) -> i64 {{ return does_a(); }}, \
         fn(x: i64) -> i64 {{ return does_b(); }}); }}\n"
    );
    let codes = compile_module_codes(&both);
    assert!(
        codes.is_empty(),
        "a caller declaring the union {{EA, EB}} is legal; got {codes:?}"
    );
    let missing_one = format!(
        "{base}fn caller() -> i64 ! {{ EA }} {{ return h2(\
         fn(x: i64) -> i64 {{ return does_a(); }}, \
         fn(x: i64) -> i64 {{ return does_b(); }}); }}\n"
    );
    let codes = compile_module_codes(&missing_one);
    assert!(
        codes.iter().any(|c| c == "E001"),
        "a caller declaring only {{EA}} must be charged for EB; got {codes:?}"
    );
}

/// Mixed row `! {{ EA, e }}`: the binding subtracts the concrete part, so the
/// variable takes only the residual.
#[test]
fn mixed_row_binding_subtracts_the_concrete_part() {
    let typed = typecheck_or_panic(
        "#[ring(outer)]\nmodule app;\n\
         effect EA;\n\
         effect EB;\n\
         fn does_both() -> i64 ! { EA, EB } { return 0; }\n\
         fn h<e>(f: Fn(i64) -> i64 ! { EA, e }) -> i64 ! { EA, e } { return f(1); }\n\
         fn caller() -> i64 ! { EA, EB } { return h(fn(x: i64) -> i64 { return does_both(); }); }\n",
    );
    let names: Vec<&str> = typed
        .modules
        .iter()
        .flat_map(|m| m.functions.iter().map(|f| f.name.as_str()))
        .collect();
    assert!(
        names.iter().any(|n| n.ends_with("h__$!EB")),
        "`e` must bind to the residual {{EB}}, not the whole actual row; got {names:?}"
    );
}

/// Two variables on two params bind independently and the declared row unions
/// them.
#[test]
fn two_variables_bind_independently() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect EA;\n\
         effect EB;\n\
         fn does_a() -> i64 ! { EA } { return 0; }\n\
         fn does_b() -> i64 ! { EB } { return 0; }\n\
         fn compose<e1, e2>(f: Fn(i64) -> i64 ! { e1 }, g: Fn(i64) -> i64 ! { e2 }) \
         -> i64 ! { e1, e2 } { let r: i64 = f(1); return g(r); }\n\
         fn caller() -> i64 ! { EA, EB } { return compose(\
         fn(x: i64) -> i64 { return does_a(); }, \
         fn(x: i64) -> i64 { return does_b(); }); }\n",
    );
    assert!(
        codes.is_empty(),
        "independent variables must bind per-param and union in the declared row; \
         got {codes:?}"
    );
}

/// An UNCONSTRAINED variable (no Fn-typed param mentions it) defaults to the
/// empty row — and the body is checked against that: performing a concrete
/// effect under a `! {{ e }}`-only declared row is E001 inside the instance.
#[test]
fn unconstrained_variable_defaults_empty_and_body_is_checked() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h<e>() -> i64 ! { e } { return logs(); }\n\
         fn caller() -> i64 { return h(); }\n",
    );
    assert!(
        codes.iter().any(|c| c == "E001"),
        "an unconstrained `e` is the empty row, so the body's `logs()` call must be \
         E001; got {codes:?}"
    );
}

/// PIN of TD-3 — return-position rows: a returned closure carries the
/// INSTANTIATED row, and applying it in a pure caller is E001. Without the
/// return-site overlay the returned `Fn` is typed `{}` and discharges nothing.
#[test]
fn returned_closure_carries_the_instantiated_row() {
    let base = "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn mk<e>(f: Fn(i64) -> i64 ! { e }) -> (Fn(i64) -> i64 ! { e }) { return f; }\n";
    let laundering = format!(
        "{base}fn pure_use() -> i64 {{ \
         let g = mk(fn(x: i64) -> i64 {{ return logs(); }}); return g(5); }}\n"
    );
    let codes = compile_module_codes(&laundering);
    assert!(
        codes.iter().any(|c| c == "E001"),
        "applying a returned `{{Log}}` closure in a pure fn must be E001 (the TD-3 \
         launder); got {codes:?}"
    );
    let declared = format!(
        "{base}fn ok_use() -> i64 ! {{ Log }} {{ \
         let g = mk(fn(x: i64) -> i64 {{ return logs(); }}); return g(5); }}\n"
    );
    let codes = compile_module_codes(&declared);
    assert!(
        codes.is_empty(),
        "the same application under a declared {{Log}} row is legal; got {codes:?}"
    );
}

/// A concrete `handle` inside a row-poly body discharges a bound effect — the
/// instance's row can stay empty because the handler contains it.
#[test]
fn concrete_handle_inside_a_row_poly_body_discharges() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect EA;\n\
         fn does_a() -> i64 ! { EA } { return 0; }\n\
         fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 { \
         handle EA { let r: i64 = f(1); }; return 0; }\n\
         fn caller() -> i64 { return h(fn(x: i64) -> i64 { return does_a(); }); }\n",
    );
    assert!(
        codes.is_empty(),
        "a concrete `handle EA` must discharge the bound row inside the instance; \
         got {codes:?}"
    );
}

/// Recursive self-instantiation: same binding → same key → cache hit. Must
/// terminate and stay green.
#[test]
fn recursive_self_instantiation_terminates() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 ! { e } { return h(f); }\n\
         fn caller() -> i64 ! { Log } { return h(fn(x: i64) -> i64 { return logs(); }); }\n",
    );
    assert!(
        codes.is_empty(),
        "self-instantiation at the same row must cache-hit and terminate; got {codes:?}"
    );
}

// ───────────────────────── TD-1's row half ─────────────────────────

/// PIN 2 — the pre-existing generic-path row launder is CLOSED: a concrete
/// (variable-free) row on a generic fn's Fn-typed formal now rejects an
/// effectful closure. Before this check the program compiled clean and the
/// closure's effects were never charged anywhere.
#[test]
fn concrete_row_on_a_generic_formal_is_now_enforced() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h<T>(f: Fn(i64) -> i64 ! { }, x: T) -> i64 { return f(1); }\n\
         fn caller() -> i64 { return h(fn(x: i64) -> i64 { return logs(); }, 7); }\n",
    );
    assert!(
        codes.iter().any(|c| c == "E001"),
        "an effectful closure into a generic `! {{ }}` formal must be E001 (TD-1's \
         row half); got {codes:?}"
    );
}

/// The T069 generic-signature hole is CLOSED: an unknown effect name in a
/// generic fn's type row is now rejected at the declaration (it was silently
/// dropped — generic sigs never pass through `resolve_type`).
#[test]
fn unknown_row_name_in_a_generic_signature_is_t069() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn h<T>(f: Fn(i64) -> i64 ! { Bogus }, x: T) -> i64 { return 0; }\n\
         fn caller() -> i64 { return h(fn(x: i64) -> i64 { return x; }, 7); }\n",
    );
    assert!(
        codes.iter().any(|c| c == "T069"),
        "an unknown effect name in a GENERIC signature row must be T069 at the \
         declaration; got {codes:?}"
    );
}

// ───────────────────────── v1 boring limits (E011) ─────────────────────────

fn assert_e011(src: &str, what: &str) {
    let codes = compile_module_codes(src);
    assert!(
        codes.iter().any(|c| c == "E011"),
        "{what} must be E011 (v1 fail-closed); got {codes:?}"
    );
}

#[test]
fn shadowing_a_registered_effect_is_rejected() {
    assert_e011(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn h<Log>(f: Fn(i64) -> i64 ! { Log }) -> i64 { return f(1); }\n",
        "a binder shadowing a declared effect",
    );
}

/// Duplicate binders die in NAME RESOLUTION (N017) before the row-variable
/// pass ever runs — pinned here because every row structure downstream is
/// name-keyed and would silently merge duplicates if N017 ever regressed.
#[test]
fn duplicate_binder_names_are_rejected() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         fn h<e, e>(f: Fn(i64) -> i64 ! { e }) -> i64 { return f(1); }\n",
    );
    assert!(
        codes.iter().any(|c| c == "N017"),
        "duplicate binders must stay rejected upstream of the row pass; got {codes:?}"
    );
}

#[test]
fn both_kind_use_is_rejected() {
    assert_e011(
        "#[ring(outer)]\nmodule app;\n\
         fn h<e>(x: e, f: Fn(i64) -> i64 ! { e }) -> i64 { return f(1); }\n",
        "a binder used both as a type and in a row",
    );
}

#[test]
fn nested_contravariant_occurrence_is_rejected() {
    assert_e011(
        "#[ring(outer)]\nmodule app;\n\
         fn h<e>(f: Fn(Fn(i64) -> i64 ! { e }) -> i64) -> i64 { return 0; }\n",
        "a row variable nested inside a Fn param's own type",
    );
}

#[test]
fn generic_arg_nested_occurrence_is_rejected() {
    assert_e011(
        "#[ring(outer)]\nmodule app;\n\
         record Holder<T> { tag: i64 }\n\
         fn h<e>(v: Holder<Fn(i64) -> i64 ! { e }>) -> i64 { return 0; }\n",
        "a row variable under a generic arg of a param",
    );
}

#[test]
fn multiple_variables_in_one_binding_row_are_rejected() {
    assert_e011(
        "#[ring(outer)]\nmodule app;\n\
         fn h<e1, e2>(f: Fn(i64) -> i64 ! { e1, e2 }) -> i64 { return f(1); }\n",
        "two variables in one binding row",
    );
}

#[test]
fn body_annotation_occurrence_is_rejected() {
    assert_e011(
        "#[ring(outer)]\nmodule app;\n\
         fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 ! { e } { \
         let g: Fn(i64) -> i64 ! { e } = f; return g(1); }\n",
        "a row variable in a body `let` annotation",
    );
}

#[test]
fn turbofish_on_a_row_poly_fn_is_rejected() {
    assert_e011(
        "#[ring(outer)]\nmodule app;\n\
         fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 { return f(1); }\n\
         fn caller() -> i64 { return h::<i64>(fn(x: i64) -> i64 { return x; }); }\n",
        "turbofish on a fn with a row variable",
    );
}

#[test]
fn impl_method_row_binder_is_rejected() {
    assert_e011(
        "#[ring(outer)]\nmodule app;\n\
         record BoxI<T> { v: i64 }\n\
         impl BoxI<T> { fn m(self: BoxI<T>) -> i64 ! { T } { return 0; } }\n",
        "an impl binder used in a method's declared row",
    );
}

#[test]
fn record_field_row_binder_is_rejected() {
    assert_e011(
        "#[ring(outer)]\nmodule app;\n\
         record R<e> { f: Fn(i64) -> i64 ! { e } }\n",
        "a record binder used in a field row",
    );
}

#[test]
fn enum_payload_row_binder_is_rejected() {
    assert_e011(
        "#[ring(outer)]\nmodule app;\n\
         enum E<e> { V(Fn(i64) -> i64 ! { e }) }\n",
        "an enum binder used in a payload row",
    );
}

// ─────────────── already-closed shapes, converted to pins ───────────────

/// `handle e { .. }` of a VARIABLE is E011 at the DECLARATION. (The mono-time
/// T069 "unknown effect" would also fire — but only for fns somebody calls:
/// generic bodies are checked at instantiation, so an uncalled fn's
/// `handle e` was completely silent. The declaration-time check covers both.)
#[test]
fn handling_a_row_variable_is_rejected() {
    assert_e011(
        "#[ring(outer)]\nmodule app;\n\
         fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 { \
         handle e { let r: i64 = f(1); }; return 0; }\n",
        "handling a row variable",
    );
}

// ───────────────────────── the cert surface ─────────────────────────

/// A row variable's NAME never reaches `effects_required` (the deploy gate
/// compares that surface against runtime grants with bidirectional set
/// equality, so a stray binder name fails every deploy); the INSTANTIATION's
/// concrete row does reach it, via the mono's `TypedFunction.effects`. (The
/// gate's code is deliberately not named here — the direct-test-reference
/// census cannot tell an assertion from prose.)
#[test]
fn cert_effects_required_excludes_the_variable_name() {
    let src = "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 ! { e } { return f(1); }\n\
         fn caller() -> i64 ! { Log } { return h(fn(x: i64) -> i64 { return logs(); }); }\n\
         entry actor Main { on Tick() -> i64 { return 0; } }\n";
    let compilation = sigil_compiler::compile_named_module("row_poly_cert.sigil", src)
        .expect("a row-polymorphic program must compile");
    assert!(
        !compilation.effects_required.iter().any(|e| e == "e"),
        "the variable NAME must never ship in effects_required; got {:?}",
        compilation.effects_required
    );
    assert!(
        compilation.effects_required.iter().any(|e| e == "Log"),
        "the instantiated row must still be counted; got {:?}",
        compilation.effects_required
    );
}
