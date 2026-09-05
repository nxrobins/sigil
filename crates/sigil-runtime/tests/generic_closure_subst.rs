//! Generic-closure-type SUBSTITUTION — RUNTIME value-correctness.
//!
//! `apply_subst` (type_check/resolve.rs) had NO `Type::Fn` arm: a generic type
//! parameter appearing INSIDE a closure type — `f: Fn(T) -> U` on a generic
//! fn/method — was NOT substituted during monomorphization. The unsubstituted
//! `Type::Generic("T")` then reached `air::mangle_type` and ICEd. This was
//! latent because every SHIPPED closure-as-param (Option::map, Result::map, the
//! iterator adapters) uses a FULLY CONCRETE closure type (`Fn(i64)->i64`,
//! `Fn(i64)->bool`), where the previous `other => other.clone()` was correct.
//!
//! These tests pin the generic case by VALUE: each compiles a generic fn/method
//! whose closure param mentions the enclosing type parameter, monomorphizes it
//! at a concrete type, and asserts the run-to-completion result. Without the
//! `Type::Fn` arm in `apply_subst`, `compile_tool` ICEs (Generic reaches mangle)
//! and these panic at compile time. Harness mirrors `closure_capture.rs`.
//!
//! The NARROW-INT block at the foot pins a SECOND, distinct fix in the same
//! family: `unify` likewise had no `Type::Fn` arm, so a closure ARGUMENT failed
//! to bind the type parameter and a generic closure-param fn instantiated at
//! i32/u32 selected the wrong (i64) monomorphization → invalid wasm / an ICE.
//! Fixed in `unify` (Fn/Tuple arms + a nested-only literal-yields-to-concrete
//! rule) and `infer_call_expr` (re-narrow integer-literal args to the
//! substituted concrete parameter type).

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Compile + run a full module whose `tool_main` returns `0 - K`; decode K.
fn neg(src: &str) -> i64 {
    let result = compile_tool(src).expect("module should compile");
    match execute_ephemeral(
        &result.wasm,
        b"",
        result.fuel_budget.max(1_000_000_000),
        &IoGrants::none(),
    ) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            let s = message
                .find(p)
                .unwrap_or_else(|| panic!("no sentinel in: {message}"))
                + p.len();
            let e = message[s..].find(')').unwrap();
            message[s..s + e].parse().unwrap()
        }
        other => panic!("expected sentinel trap, got {other:?}"),
    }
}

// PRIMARY CASE (the task's example): a generic FREE fn whose closure param
// `f: Fn(T) -> T` mentions T in both param- and return-position, instantiated at
// T=i64. Both `T`s inside the Fn must substitute to i64 → mangles as Fn(i64)->i64.
// Doubling closure, x=5 → 10. Pre-fix: Generic("T") inside Fn reaches mangle → ICE.
#[test]
fn generic_free_fn_closure_param_i64() {
    let src = "module tool;\n\
        fn apply<T>(f: Fn(T) -> T, x: T) -> T { return f(x); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   return 0 - apply(fn(x: i64) -> i64 { return x + x; }, 5);\n\
        }\n";
    assert_eq!(neg(src), 10, "Fn(T)->T must substitute to Fn(i64)->i64");
}

// TWO DISTINCT instantiations of the SAME generic fn in ONE module (T=i64 and
// T=u64) — proves monomorphization produces a DISTINCT, correctly-substituted
// closure mangling per concrete type (not a collision, not a leftover Generic).
// a=double(5)=10 returned only if b=double(7)=14 first verifies. (Narrow-int
// instantiations are exercised separately further down.)
#[test]
fn generic_free_fn_closure_param_two_instantiations() {
    let src = "module tool;\n\
        fn apply<T>(f: Fn(T) -> T, x: T) -> T { return f(x); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let a: i64 = apply(fn(x: i64) -> i64 { return x + x; }, 5);\n\
        \x20   let b: u64 = apply(fn(x: u64) -> u64 { return x + x; }, 7);\n\
        \x20   if b == 14 { return 0 - a; } else { return 0 - 1; }\n\
        }\n";
    assert_eq!(
        neg(src),
        10,
        "i64 and u64 instantiations must mangle distinctly"
    );
}

// TWO type params: closure RETURN type is a DIFFERENT generic param `U`.
// `transform<T, U>(f: Fn(T) -> U, x: T) -> U` at T=i64, U=bool — the
// param-position T substitutes to i64 AND the return-position U substitutes to
// bool (a distinct concrete type), inside the same Fn. Predicate x>3, x=5 → true.
#[test]
fn generic_free_fn_closure_two_params() {
    let src = "module tool;\n\
        fn transform<T, U>(f: Fn(T) -> U, x: T) -> U { return f(x); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let b: bool = transform(fn(x: i64) -> bool { return x > 3; }, 5);\n\
        \x20   if b { return 0 - 55; } else { return 0 - 1; }\n\
        }\n";
    assert_eq!(neg(src), 55, "Fn(T)->U must substitute to Fn(i64)->bool");
}

// GENERIC IMPL METHOD whose closure param mentions the receiver's type param —
// the impl-method monomorphization path that `apply_subst`'s doc-comment cites
// (build_mono_impl_method_mangled_name + apply_subst over the method signature).
// `Wrap<T>::apply(f: Fn(T) -> T)` at T=i64, val=5, doubling closure → 10.
#[test]
fn generic_impl_method_closure_param_i64() {
    let src = "module tool;\n\
        record Wrap<T> { val: T }\n\
        impl Wrap<T> {\n\
        \x20   pub fn apply(self: Wrap<T>, f: Fn(T) -> T) -> T { return f(self.val); }\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let w: Wrap<i64> = Wrap { val: 5 };\n\
        \x20   return 0 - w.apply(fn(x: i64) -> i64 { return x + x; });\n\
        }\n";
    assert_eq!(
        neg(src),
        10,
        "method param Fn(T)->T must substitute at T=i64"
    );
}

// GENERIC RECORD FIELD whose type IS a closure mentioning the param —
// `record Box<T> { f: Fn(T) -> T }`. This routes through AIR's
// `build_field_registry`, the OTHER documented `apply_subst` caller: the
// per-instantiation field type `Fn(T)->T` must substitute to `Fn(i64)->i64`
// when registering the `Box<i64>` field layout. Store closure, retrieve, call:
// b.run(5) → 10. Like the impl-method case, this ICEs pre-fix.
#[test]
fn generic_record_field_closure_type_i64() {
    let src = "module tool;\n\
        record Box<T> { f: Fn(T) -> T }\n\
        impl Box<T> {\n\
        \x20   pub fn run(self: Box<T>, x: T) -> T { let g = self.f; return g(x); }\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let b: Box<i64> = Box { f: fn(x: i64) -> i64 { return x + x; } };\n\
        \x20   return 0 - b.run(5);\n\
        }\n";
    assert_eq!(
        neg(src),
        10,
        "generic-record closure field must substitute at T=i64"
    );
}

// ── NARROW-INT generic closure params (call-site inference fix) ─────────────
// The cases below instantiate a generic closure-param fn at a NARROW int
// (i32/u32). They exercised a SEPARATE bug from the apply_subst substitution
// above: `unify` had no `Type::Fn` arm, so a closure ARGUMENT `Fn(i32)->i32`
// failed to bind the type parameter; T then fell to the integer-LITERAL arg,
// which defaults to i64. The wrong instance (`apply__i64`, an i64-closure
// call) was selected for an i32 closure → the literal arg was emitted as
// `i64.const` into an i32 call slot → INVALID wasm (and, in the reversed arg
// order, an ICE in call_indirect type lookup). Fixed by: (1) a `Type::Fn`
// (+`Type::Tuple`) arm in `unify` so closure args bind type params; (2) a
// nested-only "literal yields to concrete" rule so argument order can't pick
// the wrong instance; (3) re-narrowing integer-literal args to the substituted
// concrete parameter type in `infer_call_expr`. For i64/u64 these defaulted
// correctly already (64-bit), which is why this stayed latent.

// Forward order (closure param first, literal value second) at T=i32.
// Doubling closure, x=5 → 10; r==10 ⇒ 77. Pre-fix: invalid wasm (i64→i32 slot).
#[test]
fn generic_free_fn_closure_param_i32() {
    let src = "module tool;\n\
        fn apply<T>(f: Fn(T) -> T, x: T) -> T { return f(x); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let r: i32 = apply(fn(x: i32) -> i32 { return x + x; }, 5);\n\
        \x20   if r == 10 { return 0 - 77; } else { return 0 - 1; }\n\
        }\n";
    assert_eq!(
        neg(src),
        77,
        "closure arg must bind T=i32 (not the literal's i64)"
    );
}

// Same at T=u32 — a distinct narrow type / mangling. r==10 ⇒ 88.
#[test]
fn generic_free_fn_closure_param_u32() {
    let src = "module tool;\n\
        fn apply<T>(f: Fn(T) -> T, x: T) -> T { return f(x); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let r: u32 = apply(fn(x: u32) -> u32 { return x + x; }, 5);\n\
        \x20   if r == 10 { return 0 - 88; } else { return 0 - 1; }\n\
        }\n";
    assert_eq!(
        neg(src),
        88,
        "closure arg must bind T=u32 (not the literal's i64)"
    );
}

// REVERSED argument order (literal value first, closure param second) at T=i32.
// The closure (nested inside `Fn`) must still pin T=i32 over the prior literal —
// this is the nested-only upgrade in `unify`. Pre-fix this ICEd in call_indirect
// type lookup. x=5 → 10; r==10 ⇒ 99.
#[test]
fn generic_free_fn_closure_param_i32_reversed_args() {
    let src = "module tool;\n\
        fn apply<T>(x: T, f: Fn(T) -> T) -> T { return f(x); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let r: i32 = apply(5, fn(x: i32) -> i32 { return x + x; });\n\
        \x20   if r == 10 { return 0 - 99; } else { return 0 - 1; }\n\
        }\n";
    assert_eq!(
        neg(src),
        99,
        "closure pins T=i32 regardless of argument order"
    );
}

// Generic IMPL METHOD at a narrow int — Wrap<i32>, doubling closure, literal
// field value + i32 result. Exercises the method-monomorphization path at i32.
#[test]
fn generic_impl_method_closure_param_i32() {
    let src = "module tool;\n\
        record Wrap<T> { val: T }\n\
        impl Wrap<T> {\n\
        \x20   pub fn apply(self: Wrap<T>, f: Fn(T) -> T) -> T { return f(self.val); }\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let w: Wrap<i32> = Wrap { val: 5 };\n\
        \x20   let r: i32 = w.apply(fn(x: i32) -> i32 { return x + x; });\n\
        \x20   if r == 10 { return 0 - 66; } else { return 0 - 1; }\n\
        }\n";
    assert_eq!(
        neg(src),
        66,
        "method-path closure must bind T=i32 at a narrow int"
    );
}

// ── CLOSURE-VALUE CALL with a narrow-int integer LITERAL ────────────────────
// A companion defect in the SAME PIL-narrowing family, surfaced by the
// adversarial sweep: calling a closure-typed VALUE `g(5)` where g: Fn(i32)->i32
// did not narrow the literal `5` to the closure's i32 parameter — it stayed
// IntLit and defaulted to i64, so AIR emitted an `i64.const` into a narrow
// `call_indirect` slot → invalid wasm. Independent of generics (it reproduces
// with a plain closure-typed local) and pre-existing. Fixed by narrowing
// integer-literal args to the closure's concrete param width in the HOF
// closure-call path of `infer_call_expr`.

// Plain closure-typed local called with a literal at i32. Doubling, 5 → 10.
#[test]
fn closure_value_call_literal_arg_i32() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let g: Fn(i32) -> i32 = fn(x: i32) -> i32 { return x + x; };\n\
        \x20   let r: i32 = g(5);\n\
        \x20   if r == 10 { return 0 - 77; } else { return 0 - 1; }\n\
        }\n";
    assert_eq!(
        neg(src),
        77,
        "literal arg to an i32 closure-value call must narrow to i32"
    );
}

// HIGHER-ORDER: a generic fn RETURNS a closure `Fn(i32)->i32`; the returned
// closure is then called with a literal. Combines generic monomorphization at a
// narrow int with the closure-value-call narrowing. apply()'s closure doubles;
// g(5) → 10. Pre-fix: invalid wasm at the indirect call.
#[test]
fn generic_returns_closure_called_with_literal_i32() {
    let src = "module tool;\n\
        fn apply<T>(f: Fn() -> Fn(T) -> T) -> Fn(T) -> T { return f(); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let g: Fn(i32) -> i32 = apply(fn() -> Fn(i32) -> i32 { return fn(x: i32) -> i32 { return x + x; }; });\n\
        \x20   let r: i32 = g(5);\n\
        \x20   if r == 10 { return 0 - 77; } else { return 0 - 1; }\n\
        }\n";
    assert_eq!(
        neg(src),
        77,
        "generic-returned i32 closure called with a literal must narrow"
    );
}
