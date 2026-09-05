//! HK2 (higher-kinded `Self` traits) + generic-impl-method RUNTIME round-trip.
//!
//! The type-check/compile acceptance lives in the sigil-compiler tests; this file
//! COMPILES + EXECUTES the wasm and asserts the ACTUAL mapped value — proving a
//! user-defined `Functor` (its `fmap` consumed generically through `map`) really
//! applies the function, and that a generic impl method with its own type
//! parameters monomorphizes + runs correctly.
//!
//! Decode mechanism: `return 0 - value;` traps with a negative sentinel that the
//! runtime reports as `tool returned error (value)`; we recover `value` from it
//! (the `array_contains.rs` pattern).

mod common;

const FUEL: u64 = 100_000;

/// Compile + run a full tool whose `tool_main` ends `return 0 - value;`, and
/// recover `value` from the negative-sentinel trap.
fn run_neg(src: &str) -> i64 {
    common::run_returning_negative_with_fuel(src, FUEL)
}

const FUNCTOR_PRELUDE: &str = "module tool;\n\
    record Box<T> { val: T }\n\
    trait Functor { fn fmap<A, B>(self: Self<A>, f: Fn(A) -> B) -> Self<B>; }\n\
    impl Functor for Box { fn fmap<A, B>(self: Box<A>, f: Fn(A) -> B) -> Box<B> { return Box { val: f(self.val) }; } }\n\
    fn map<F: * -> * + Functor, A, B>(xs: F<A>, f: Fn(A) -> B) -> F<B> { return xs.fmap(f); }\n";

#[test]
fn functor_map_through_generic_consumer() {
    // The headline: a user `impl Functor for Box`, consumed via a generic
    // `map<F: * -> * + Functor>`, actually applies `+1` — Box{5} -> Box{6}.
    let src = format!(
        "{FUNCTOR_PRELUDE}\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
        \x20   let b: Box<i64> = Box {{ val: 5 }};\n\
        \x20   let c: Box<i64> = map(b, fn(x: i64) -> i64 {{ return x + 1; }});\n\
        \x20   return 0 - c.val;\n\
        }}\n"
    );
    assert_eq!(run_neg(&src), 6, "map(Box{{5}}, +1).val must be 6");
}

#[test]
fn functor_map_applies_the_actual_function() {
    // A different function (×3 + 1) proves the value isn't a coincidence: 5 -> 16.
    let src = format!(
        "{FUNCTOR_PRELUDE}\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
        \x20   let b: Box<i64> = Box {{ val: 5 }};\n\
        \x20   let c: Box<i64> = map(b, fn(x: i64) -> i64 {{ return x * 3 + 1; }});\n\
        \x20   return 0 - c.val;\n\
        }}\n"
    );
    assert_eq!(run_neg(&src), 16, "map(Box{{5}}, x*3+1).val must be 16");
}

#[test]
fn functor_fmap_called_directly() {
    // The same `impl Functor for Box::fmap` called directly (no generic consumer).
    let src = format!(
        "{FUNCTOR_PRELUDE}\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
        \x20   let b: Box<i64> = Box {{ val: 7 }};\n\
        \x20   let c: Box<i64> = b.fmap(fn(x: i64) -> i64 {{ return x + 10; }});\n\
        \x20   return 0 - c.val;\n\
        }}\n"
    );
    assert_eq!(run_neg(&src), 17, "Box{{7}}.fmap(+10).val must be 17");
}

#[test]
fn generic_impl_method_monomorphizes_and_runs() {
    // The prerequisite fix on its own: a generic impl method (`fn remap<B>` with
    // its OWN type parameter, inferred from the closure) monomorphizes + runs.
    let src = "module tool;\n\
        record Box<T> { val: T }\n\
        impl Box<T> { fn remap<B>(self: Box<T>, f: Fn(T) -> B) -> Box<B> { return Box { val: f(self.val) }; } }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let b: Box<i64> = Box { val: 4 };\n\
        \x20   let c: Box<i64> = b.remap(fn(x: i64) -> i64 { return x + 100; });\n\
        \x20   return 0 - c.val;\n\
        }\n";
    assert_eq!(run_neg(src), 104, "Box{{4}}.remap(+100).val must be 104");
}

// ---------------------------------------------------------------------------
// HK3: multi-arg `Self<A, B>` (Bifunctor) + nesting `F<G<A>>`. These fell out of
// HK2's arity-GENERIC build (no new lowering); these tests prove they RUN
// correctly at arity 2 and with a nested erased result type.
// ---------------------------------------------------------------------------

const BIFUNCTOR_PRELUDE: &str = "module tool;\n\
    record Pair<A, B> { fst: A, snd: B }\n\
    trait Bifunctor { fn bimap<A, B, C, D>(self: Self<A, B>, f: Fn(A) -> C, g: Fn(B) -> D) -> Self<C, D>; }\n\
    impl Bifunctor for Pair { fn bimap<A, B, C, D>(self: Pair<A, B>, f: Fn(A) -> C, g: Fn(B) -> D) -> Pair<C, D> { return Pair { fst: f(self.fst), snd: g(self.snd) }; } }\n\
    fn bimap2<F: * -> * -> * + Bifunctor, A, B, C, D>(xs: F<A, B>, f: Fn(A) -> C, g: Fn(B) -> D) -> F<C, D> { return xs.bimap(f, g); }\n";

#[test]
fn bifunctor_bimap_through_generic_consumer() {
    // A 2-arg `Self<A, B>` (Bifunctor) over `impl Bifunctor for Pair`, consumed
    // via a generic `bimap2<F: * -> * -> * + Bifunctor>`: Pair{3,4} |> (+1, *2) =
    // Pair{4, 8}, return 0 - 4 - 8.
    let src = format!(
        "{BIFUNCTOR_PRELUDE}\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
        \x20   let p: Pair<i64, i64> = Pair {{ fst: 3, snd: 4 }};\n\
        \x20   let q: Pair<i64, i64> = bimap2(p, fn(x: i64) -> i64 {{ return x + 1; }}, fn(y: i64) -> i64 {{ return y * 2; }});\n\
        \x20   return 0 - q.fst - q.snd;\n\
        }}\n"
    );
    assert_eq!(
        run_neg(&src),
        12,
        "bimap2(Pair{{3,4}}, +1, *2) = Pair{{4,8}}"
    );
}

#[test]
fn bifunctor_does_not_swap_the_two_sides() {
    // Distinguishable functions prove `f` maps `fst` and `g` maps `snd` (no
    // arg-position swap in the arity-2 erasure): fst 3 -> *10 = 30, snd 4 -> +1 =
    // 5; sum 35. (A swap would give 4*10 + 3+1 = 44.)
    let src = format!(
        "{BIFUNCTOR_PRELUDE}\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
        \x20   let p: Pair<i64, i64> = Pair {{ fst: 3, snd: 4 }};\n\
        \x20   let q: Pair<i64, i64> = bimap2(p, fn(x: i64) -> i64 {{ return x * 10; }}, fn(y: i64) -> i64 {{ return y + 1; }});\n\
        \x20   return 0 - q.fst - q.snd;\n\
        }}\n"
    );
    assert_eq!(
        run_neg(&src),
        35,
        "f->fst (30) + g->snd (5); a swap would be 44"
    );
}

#[test]
fn r2_colliding_mangle_instantiations_run_independently() {
    // R2 (HK3 adversarial-sweep): `g<A, B>` at `[Foo_Bar, X]` and `[Foo, Bar_X]`
    // previously mangled to the SAME `g__Foo_Bar_X` key, so the second call ran
    // the FIRST instantiation's body (wrong trait dispatch). Distinct `conv()`
    // impls make the fusion observable: r1 = 11*1000+44 = 11044 (Foo_Bar, X),
    // r2 = 33*1000+22 = 33022 (Foo, Bar_X); a fused build would run r2 as 11044.
    // The injective `$`-separated mangle keeps them apart → 0 - 11044 - 33022.
    let src = "module tool;\n\
        record Foo_Bar { a: i64 }\n\
        record Bar_X { a: i64 }\n\
        record Foo { a: i64 }\n\
        record X { a: i64 }\n\
        trait Conv { fn conv(self: Self) -> i64; }\n\
        impl Conv for Foo_Bar { fn conv(self: Foo_Bar) -> i64 { return 11; } }\n\
        impl Conv for Bar_X { fn conv(self: Bar_X) -> i64 { return 22; } }\n\
        impl Conv for Foo { fn conv(self: Foo) -> i64 { return 33; } }\n\
        impl Conv for X { fn conv(self: X) -> i64 { return 44; } }\n\
        fn g<A: Conv, B: Conv>(p: A, q: B) -> i64 { return p.conv() * 1000 + q.conv(); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let r1: i64 = g(Foo_Bar { a: 0 }, X { a: 0 });\n\
        \x20   let r2: i64 = g(Foo { a: 0 }, Bar_X { a: 0 });\n\
        \x20   return 0 - r1 - r2;\n\
        }\n";
    assert_eq!(
        run_neg(src),
        44066,
        "g(Foo_Bar,X)=11044 + g(Foo,Bar_X)=33022; a mangle fusion would mis-dispatch r2"
    );
}

#[test]
fn functor_with_nested_result_type() {
    // Nesting `F<G<A>>`: a functor `map` whose function returns `Box<i64>`, so the
    // result is `Box<Box<i64>>` — the nested erased type must lower and the doubly
    // nested field read must work: Box{5} |> (x -> Box{x+1}), then .val.val = 6.
    let src = format!(
        "{FUNCTOR_PRELUDE}\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
        \x20   let b: Box<i64> = Box {{ val: 5 }};\n\
        \x20   let c: Box<Box<i64> > = map(b, fn(x: i64) -> Box<i64> {{ return Box {{ val: x + 1 }}; }});\n\
        \x20   let inner: Box<i64> = c.val;\n\
        \x20   return 0 - inner.val;\n\
        }}\n"
    );
    assert_eq!(
        run_neg(&src),
        6,
        "map(Box{{5}}, x->Box{{x+1}}).val.val must be 6"
    );
}
