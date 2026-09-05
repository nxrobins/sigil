//! Higher-kinded types — kind parsing (PR-HK0) + free-function monomorphization
//! (PR-HK1). Both rungs share this one integration-test binary deliberately: each
//! `tests/` file links the whole `sigil-compiler` lib, and the CI "Test JSON
//! path" step is memory-bound at link time (see PR #388), so HKT tests are kept
//! together rather than split across binaries.
//!
//! PR-HK0 — `<F: * -> *>` kind-annotation parsing (the `parse_kind` fork in
//! `parse_type_params`).
//!
//! A type-parameter's `:`-clause now forks on its first token: a `*` begins a
//! KIND annotation (`<F: * -> *>`), recorded on `TypeParam.kind` as
//! `ParamKind::Constructor { arity }` (arity = arrow count); anything else is the
//! ordinary trait-bound list (`<T: Hash>`), leaving `kind == Star`. The two
//! grammars are token-disjoint (`*` is never a trait-bound name). This PR is
//! representation + parse only — no instantiation — so a program that merely
//! DECLARES a higher-kinded parameter parses, resolves, and type-checks.
//!
//! Happy-path shape is asserted on the real AST via `parse_program!`; malformed
//! kinds and the declared-but-unused end-to-end check go through `compile_tool`.

use sigil_compiler::ast::{Item, ParamKind};
use sigil_compiler::compile_tool;
use sigil_test_utils::parse_program;

/// The `(name, kind, bounds)` of the first item's type-params (a `FnDef`).
fn fn_type_params(src: &str) -> Vec<(String, ParamKind, Vec<String>)> {
    let prog = parse_program!(src);
    let Item::FnDef(def) = &prog.modules[0].items[0] else {
        panic!("expected the first item to be a FnDef");
    };
    def.type_params
        .iter()
        .map(|p| (p.name.clone(), p.kind.clone(), p.bounds.clone()))
        .collect()
}

// ── happy-path AST shape ──────────────────────────────────────────────────────

#[test]
fn arity_one_kind() {
    // `* -> *` → one arrow → Constructor { arity: 1 }.
    let tp = fn_type_params("module m;\npub fn f<F: * -> *>(x: i64) -> i64 { return x; }\n");
    assert_eq!(
        tp,
        vec![("F".to_string(), ParamKind::Constructor { arity: 1 }, vec![])]
    );
}

#[test]
fn arity_two_kind() {
    // `* -> * -> *` → two arrows → Constructor { arity: 2 } (e.g. a `Map`-shape).
    let tp = fn_type_params("module m;\npub fn f<M: * -> * -> *>(x: i64) -> i64 { return x; }\n");
    assert_eq!(
        tp,
        vec![("M".to_string(), ParamKind::Constructor { arity: 2 }, vec![])]
    );
}

#[test]
fn kind_then_trait_bound() {
    // `<F: * -> * + Functor>` — a kind, then a `+`-separated bound list.
    let tp =
        fn_type_params("module m;\npub fn f<F: * -> * + Functor>(x: i64) -> i64 { return x; }\n");
    assert_eq!(
        tp,
        vec![(
            "F".to_string(),
            ParamKind::Constructor { arity: 1 },
            vec!["Functor".to_string()],
        )]
    );
}

#[test]
fn mixed_kinded_and_star_params() {
    // `<F: * -> *, A>` — F is higher-kinded, A is an ordinary `Star` param.
    let tp = fn_type_params("module m;\npub fn f<F: * -> *, A>(x: i64) -> i64 { return x; }\n");
    assert_eq!(
        tp,
        vec![
            ("F".to_string(), ParamKind::Constructor { arity: 1 }, vec![]),
            ("A".to_string(), ParamKind::Star, vec![]),
        ]
    );
}

#[test]
fn ordinary_bound_is_still_star() {
    // A non-`*` `:`-clause is unchanged: an ordinary `Star` param with bounds.
    let tp = fn_type_params("module m;\npub fn f<T: Hash + Eq>(x: T) -> T { return x; }\n");
    assert_eq!(
        tp,
        vec![(
            "T".to_string(),
            ParamKind::Star,
            vec!["Hash".to_string(), "Eq".to_string()],
        )]
    );
}

#[test]
fn record_higher_kinded_param() {
    // The kind fork parses on a `record` def too (same chokepoint).
    let prog = parse_program!("module m;\nrecord Holder<F: * -> *> { v: i64 }\n");
    let Item::RecordDef(def) = &prog.modules[0].items[0] else {
        panic!("expected a RecordDef");
    };
    assert_eq!(def.type_params.len(), 1);
    assert_eq!(def.type_params[0].name, "F");
    assert_eq!(def.type_params[0].kind, ParamKind::Constructor { arity: 1 });
}

// ── end-to-end: a DECLARED-but-uninstantiated HKT param compiles ───────────────

#[test]
fn declared_higher_kinded_param_compiles() {
    // PR-HK0 done-line: a program that DECLARES `<F: * -> *>` but never
    // instantiates it parses, resolves, and type-checks (the generic fn is
    // diverted, its body never monomorphized).
    let src = "module tool;\n\
        fn id<F: * -> *>(x: i64) -> i64 { return x; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 1; }\n";
    assert!(
        compile_tool(src).is_ok(),
        "a program merely declaring a higher-kinded parameter must compile"
    );
}

// ── malformed kinds are a clean parse error (P027), no hang ────────────────────

#[test]
fn bare_star_is_not_higher_kinded() {
    // `<F: *>` — arity 0 is not higher-kinded; P027.
    let src = "module tool;\n\
        fn f<F: *>(x: i64) -> i64 { return x; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 1; }\n";
    assert!(compile_tool(src).is_err(), "`<F: *>` must be a parse error");
}

#[test]
fn over_arity_kind_rejected() {
    // `* -> * -> * -> *` is arity 3 > MAX_KIND_ARITY (2); P027.
    let src = "module tool;\n\
        fn f<F: * -> * -> * -> *>(x: i64) -> i64 { return x; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 1; }\n";
    assert!(
        compile_tool(src).is_err(),
        "an over-arity kind (> 2) must be a parse error"
    );
}

#[test]
fn dangling_arrow_rejected() {
    // `<F: * ->>` — a `->` with no following `*`; P027.
    let src = "module tool;\n\
        fn f<F: * ->>(x: i64) -> i64 { return x; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 1; }\n";
    assert!(
        compile_tool(src).is_err(),
        "a dangling `->` in a kind must be a parse error"
    );
}

// ── PR-HK1: free-function HKT (arity 1) — unify + monomorphization + erasure ────
//
// A generic function over a higher-kinded parameter `F: * -> *` monomorphizes at
// a concrete call site: `unify` binds `F` to the actual constructor
// (`F |-> TypeCtor("Box")`) and `A` to its argument; `apply_subst` /
// `resolve_type_expr` erase `F<A>` to the concrete `Named("Box", [i64])` before
// AIR; the instance mangles to `count__Box_i64` and lowers to valid wasm. The
// constructor is a USER-DEFINED `record Box<T>` (not the stdlib `Vec`) so the
// test proves the path is genuinely generic over the constructor, not a special
// case. (Kept in this file rather than a separate `tests/` binary to avoid adding
// to the JSON-path link step's memory footprint — see PR #388.)
//
// NB on body shape: without an HKT-bounded trait (PR-HK2) a generic body cannot
// field-access or construct an opaque `F<A>`, and SIGIL's ownership rule forbids
// returning a heap `@ReadOnly` param (aliasing). So the realistic HK1 body takes
// `F<A>` in PARAMETER position and returns a concrete scalar — which still drives
// the whole machinery (resolve → `HktApp`, unify the constructor, monomorphize,
// erase the param to the concrete `Named`).

#[test]
fn param_position_hkt_over_user_constructor_monomorphizes() {
    // `count<F: * -> *, A>(xs: F<A>) -> i64`. Called on a `Box<i64>`, F binds to
    // Box and A to i64; `count__Box_i64` takes an erased `Box<i64>` param and
    // lowers to valid wasm. `b` survives the `@ReadOnly` borrow and reads back.
    let src = "module tool;\n\
        record Box<T> { val: T }\n\
        fn count<F: * -> *, A>(xs: F<A>) -> i64 { return 7; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let b: Box<i64> = Box { val: 5 };\n\
        \x20   let k: i64 = count(b);\n\
        \x20   let n: i64 = b.val;\n\
        \x20   return 0 - n - k;\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "a free-fn over `F: * -> *` applied to a user `Box<i64>` must monomorphize \
         (F=Box, A=i64), erase F<A> to Box<i64>, and lower to valid wasm"
    );
}

#[test]
fn turbofish_instantiation_compiles() {
    // Explicit constructor via turbofish: `count::<Box, i64>(b)`.
    let src = "module tool;\n\
        record Box<T> { val: T }\n\
        fn count<F: * -> *, A>(xs: F<A>) -> i64 { return 7; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let b: Box<i64> = Box { val: 7 };\n\
        \x20   let k: i64 = count::<Box, i64>(b);\n\
        \x20   return 0 - k;\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "turbofish `count::<Box, i64>` must instantiate the higher-kinded parameter"
    );
}

#[test]
fn arity_mismatch_at_call_site_is_rejected() {
    // `take<F: * -> *>(xs: F<i64>)` applied to a TWO-parameter constructor
    // `Pair<A, B>` — `F<i64>` (1 arg) cannot unify with `Pair<i64, str>` (2
    // args). The arity-gate leaves F unbound → T150. Compile MUST fail.
    let src = "module tool;\n\
        record Pair<A, B> { a: A, b: B }\n\
        fn take<F: * -> *>(xs: F<i64>) -> i64 { return 0; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let p: Pair<i64, str> = Pair { a: 1, b: \"x\" };\n\
        \x20   let r: i64 = take(p);\n\
        \x20   return 0 - r;\n\
        }\n";
    assert!(
        compile_tool(src).is_err(),
        "applying a `* -> *` parameter to a 2-arg constructor must be rejected (T150), \
         not silently monomorphized"
    );
}

// ── PR-HK3: multi-arg constructors `M<_, _>` (arity-2 `Self<A, B>`) + nesting ──
// These fell out of HK2's arity-GENERIC build (`trait_self_arity` /
// `constructor_satisfies` / the unify+erasure arms count args, they are not
// hard-wired to arity 1). These tests pin the arity-2 surface so a future change
// can't silently regress it. (Runtime correctness is in
// `sigil-runtime/tests/hkt_functor_runtime.rs`.)

#[test]
fn bifunctor_multi_arg_self_compiles() {
    // A 2-arg `Self<A, B>` trait (Bifunctor) + `impl Bifunctor for Pair` consumed
    // via a generic `bimap2<F: * -> * -> * + Bifunctor>` type-checks + lowers.
    let src = "module tool;\n\
        record Pair<A, B> { fst: A, snd: B }\n\
        trait Bifunctor { fn bimap<A, B, C, D>(self: Self<A, B>, f: Fn(A) -> C, g: Fn(B) -> D) -> Self<C, D>; }\n\
        impl Bifunctor for Pair { fn bimap<A, B, C, D>(self: Pair<A, B>, f: Fn(A) -> C, g: Fn(B) -> D) -> Pair<C, D> { return Pair { fst: f(self.fst), snd: g(self.snd) }; } }\n\
        fn bimap2<F: * -> * -> * + Bifunctor, A, B, C, D>(xs: F<A, B>, f: Fn(A) -> C, g: Fn(B) -> D) -> F<C, D> { return xs.bimap(f, g); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let p: Pair<i64, i64> = Pair { fst: 3, snd: 4 };\n\
        \x20   let q: Pair<i64, i64> = bimap2(p, fn(x: i64) -> i64 { return x + 1; }, fn(y: i64) -> i64 { return y * 2; });\n\
        \x20   return 0 - q.fst - q.snd;\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "a 2-arg `Self<A, B>` Bifunctor over `impl Bifunctor for Pair` must compile"
    );
}

#[test]
fn constructor_arity_mismatch_against_two_arg_trait_is_rejected() {
    // EX-2 arity gate at arity 2: a 1-arg `Box` bound where a `* -> * -> *`
    // (`Self<A, B>`) Bifunctor is required → T270 (constructor arity 1 ≠ Self
    // arity 2). The `F<A>` (arity 1) binds `F |-> Box` cleanly, so the failure is
    // the trait-conformance arity gate, not the unify gate.
    let src = "module tool;\n\
        record Box<T> { val: T }\n\
        trait Bifunctor { fn bimap<A, B, C, D>(self: Self<A, B>, f: Fn(A) -> C, g: Fn(B) -> D) -> Self<C, D>; }\n\
        fn bad<F: * -> * + Bifunctor, A>(xs: F<A>) -> i64 { return 0; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let b: Box<i64> = Box { val: 1 };\n\
        \x20   let n: i64 = bad(b);\n\
        \x20   return 0 - 1;\n\
        }\n";
    let err = compile_tool(src).expect_err("arity-1 Box vs arity-2 Bifunctor must be rejected");
    assert!(
        format!("{err:?}").contains("T270"),
        "the rejection must be T270 (constructor/Self arity mismatch), got: {err:?}"
    );
}

#[test]
fn two_arg_constructor_consumer_compiles() {
    // The plan's `keys<M: * -> * -> *, K, V>(m: M<K, V>)` shape: a free fn over a
    // 2-arg constructor variable, applied to a user `Entry<i64, i64>`.
    let src = "module tool;\n\
        record Entry<K, V> { key: K, value: V }\n\
        fn firstkey<M: * -> * -> *, K, V>(m: M<K, V>) -> K { return m.key; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let e: Entry<i64, i64> = Entry { key: 9, value: 2 };\n\
        \x20   let k: i64 = firstkey(e);\n\
        \x20   return 0 - k;\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "a free fn over `M: * -> * -> *` applied to a user `Entry<i64, i64>` must compile"
    );
}

// ── HK3 adversarial-sweep hardening: R1 (use-site arity gate), R2 (injective
// mangle), R3 (ill-typed method arg). These were confirmed COMPILER CRASHES /
// soundness holes found by the post-HK3 adversarial workflow; each test pins the
// clean-diagnostic behavior so the crash can't regress. None may PANIC.

#[test]
fn r1_turbofish_higher_kinded_param_with_field_access_compiles() {
    // R1a: `unwrap::<Box, i64>(b)` where the body reads `xs.val`. The turbofish
    // binds the higher-kinded `F` as a CONSTRUCTOR (`TypeCtor(Box)`), not a
    // malformed 0-arg `Named(Box, [])` — which used to ICE at path-substitution.
    let src = "module tool;\n\
        record Box<T> { val: T }\n\
        fn unwrap<F: * -> *, A>(xs: F<A>) -> i64 { return xs.val; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let b: Box<i64> = Box { val: 42 };\n\
        \x20   return 0 - unwrap::<Box, i64>(b);\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "turbofish-instantiating a higher-kinded param then reading a field must compile, not ICE"
    );
}

#[test]
fn r1_wrong_arity_record_positions_reject_with_t231_not_ice() {
    // R1b: a wrong-arity generic record (`Pair<i64>` against `record Pair<A, B>`)
    // at EVERY annotation position must be a clean T231 reject — never the
    // N10-PRDF debug_assert panic (debug) / silent Generic-leak (release).
    let positions = [
        // (label, program)
        "fn p(x: Pair<i64>) -> i64 { return 0; }",
        "record H { p: Pair<i64> } fn p(h: H) -> i64 { return h.p.fst; }",
        "fn p(x: (Pair<i64>, i64)) -> i64 { return 0; }",
        "fn p(x: [Pair<i64>; 3]) -> i64 { return 0; }",
        "fn p(f: Fn(Pair<i64>) -> i64) -> i64 { return 0; }",
        "fn p(x: Pair<i64, i64, bool>) -> i64 { return 0; }",
        "record W { x: i64 } impl W { fn m(self: W, p: Pair<i64>) -> i64 { return p.fst; } }",
    ];
    for body in positions {
        let src = format!(
            "module tool;\nrecord Pair<A, B> {{ fst: A, snd: B }}\n{body}\n\
             pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{ return 0; }}\n"
        );
        let err = compile_tool(&src)
            .err()
            .unwrap_or_else(|| panic!("wrong-arity `Pair` must be rejected, in: {body}"));
        let rendered = format!("{err:?}");
        assert!(
            rendered.contains("T231") || rendered.contains("type argument"),
            "wrong-arity `Pair` must be a clean arity diagnostic (T231), got: {rendered} in: {body}"
        );
    }
}

#[test]
fn r2_double_underscore_type_name_rejected_t271() {
    // R2: a user type named `Box__i64` would collide with the monomorphized
    // instance of `Box<i64>` (`mangle_type` → "Box__i64") in the type registry.
    // Reserve `__` for compiler names → T271.
    let src = "module tool;\n\
        record Box<T> { val: T }\n\
        record Box__i64 { a: i64 }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n";
    let err = compile_tool(src).expect_err("a `__`-infixed type name must be rejected (T271)");
    assert!(
        format!("{err:?}").contains("T271"),
        "double-underscore type name must be T271, got: {err:?}"
    );
}

#[test]
fn r2_mangle_collision_records_do_not_fuse() {
    // R2: `g<Foo_Bar, X>` and `g<Foo, Bar_X>` previously mangled to the SAME
    // `g__Foo_Bar_X` key, fusing the two instantiations — so the second body was
    // never type-checked. With the `$`-separated injective mangle the second
    // instantiation IS checked: reading a field present only on the first
    // instantiation's type must now be rejected.
    let src = "module tool;\n\
        record Foo_Bar { a: i64 }\n\
        record Bar_X { a: i64 }\n\
        record Foo { a: i64 }\n\
        record X { a: i64, only_in_x: i64 }\n\
        fn g<A, B>(p: A, q: B) -> i64 { return q.only_in_x; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let r1: i64 = g(Foo_Bar { a: 11 }, X { a: 44, only_in_x: 1 });\n\
        \x20   let r2: i64 = g(Foo { a: 77 }, Bar_X { a: 88 });\n\
        \x20   return 0 - r1 - r2;\n\
        }\n";
    assert!(
        compile_tool(src).is_err(),
        "the second (fused-away) instantiation reads a field absent from `Bar_X` — must reject, \
         not silently accept via a mangle collision"
    );
}

#[test]
fn r3_ill_typed_fn_arg_to_generic_method_is_clean_not_ice() {
    // R3: an undefined identifier in the Fn-argument slot of a generic method
    // left the result generic `B` unbound → `Generic escaped into
    // type_compatible` ICE. Must be a clean diagnostic.
    let src = "module tool;\n\
        record Box<T> { val: T }\n\
        trait Functor { fn fmap<A, B>(self: Self<A>, f: Fn(A) -> B) -> Self<B>; }\n\
        impl Functor for Box { fn fmap<A, B>(self: Box<A>, f: Fn(A) -> B) -> Box<B> { return Box { val: f(self.val) }; } }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let b: Box<i64> = Box { val: 5 };\n\
        \x20   let c: Box<i64> = b.fmap(zzz_undefined);\n\
        \x20   return c.val;\n\
        }\n";
    let err =
        compile_tool(src).expect_err("an undefined Fn-arg to a generic method must be rejected");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("undefined") && !rendered.contains("escaped"),
        "must be a clean `undefined local` diagnostic, not a Generic-escape ICE: {rendered}"
    );
}
