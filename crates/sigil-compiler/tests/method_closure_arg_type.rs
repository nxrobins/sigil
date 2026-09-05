//! Method-call CLOSURE-argument signature checking. Companion to
//! `bounded_map_arg_type.rs` (which closed the scalar half of the same hole).
//!
//! A `Fn(...)`-typed parameter passed to a METHOD must be validated against the
//! parameter's full `Type::Fn` signature — arity, param types, return type, and
//! linearity — exactly as the strict FREE-call path (`infer_call_expr`) does via
//! `type_compatible`. Pre-fix the method arg loop only checked IntLit-fit and
//! machine-int params (the "method-arg check is INT-LITERAL-only" quirk), so a
//! `Fn`-typed argument bypassed the structural check entirely: a closure with the
//! wrong return type, wrong param type, or wrong arity was either silently
//! ACCEPTED (then mis-lowered) or ICE'd the wasm backend at `call_indirect`
//! ("signature not found in type map"). This made the Phase-7 iterator adapters
//! (`.map`/`.filter`/`.fold`/…), whose every adapter takes a closure as a method
//! arg, the very reachable surface for the bug.
//!
//! The fix adds the `Type::Fn`-param arm to the method arg loop, scoped to
//! `Type::Fn` EXPECTED params so the IntLit/scalar method-arg flex (generics
//! epic, 102 differential tests) is untouched. iteration.md AG-6.

use sigil_compiler::compile_tool;

use sigil_test_utils::pipeline::compile_tool_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

/// Wrap a `tool_main` body. Declares `! { Alloc }` because `Vec::new`/`push`/
/// `map`/`filter` allocate — so the ONLY diagnostic a well-formed-but-mistyped
/// body produces is the closure-arg T071, never a spurious effect error.
fn wrap(body: &str) -> String {
    format!(
        "module tool;\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         {body}\n\
         }}\n"
    )
}

/// Body prefix: a `Vec<i64>` with one element pushed (enough for dispatch).
const FILL: &str = "    let mut v: Vec<i64> = Vec::new();\n\
                    \x20   let _p: i64 = v.push(1);\n";

// ── The four reported repros: each must be a clean T071, no ICE, no accept ────

// Repro 1: `Vec::map` wants `Fn(i64) -> i64`; the closure returns `bool`.
// Pre-fix: silently ACCEPTED.
#[test]
fn map_closure_wrong_return_bool_is_t071() {
    let src = wrap(&format!(
        "{FILL}    let m: Vec<i64> = v.map(fn(x: i64) -> bool {{ return x > 0; }});\n\
         \x20   return 0 - m.len();"
    ));
    assert!(
        has(&src, "T071"),
        "map closure returning bool (wants Fn(i64)->i64) must be T071, got {:?}",
        codes_of(&src)
    );
}

// Repro 2: `Vec::filter` wants `Fn(i64) -> bool`; the closure returns `i64`.
// Pre-fix: ICE at the wasm backend ("call_indirect signature not found").
#[test]
fn filter_closure_wrong_return_i64_is_t071_not_ice() {
    let src = wrap(&format!(
        "{FILL}    let f: Vec<i64> = v.filter(fn(x: i64) -> i64 {{ return x + 1; }});\n\
         \x20   return 0 - f.len();"
    ));
    // The key assertion is BOTH that this is T071 AND that `compile_tool` returns
    // an Err rather than panicking — `codes_of` would propagate any ICE panic.
    assert!(
        has(&src, "T071"),
        "filter closure returning i64 (wants Fn(i64)->bool) must be T071 (was a wasm ICE), got {:?}",
        codes_of(&src)
    );
}

// Repro 3: `Vec::fold` wants `Fn(i64, i64) -> i64`; the closure takes ONE param.
// Pre-fix: ICE (arity unchecked).
#[test]
fn fold_closure_wrong_arity_is_t071_not_ice() {
    let src = wrap(&format!(
        "{FILL}    let s: i64 = v.fold(0, fn(a: i64) -> i64 {{ return a; }});\n\
         \x20   return 0 - s;"
    ));
    assert!(
        has(&src, "T071"),
        "fold 1-arg closure (wants Fn(i64,i64)->i64) must be T071 (was an arity ICE), got {:?}",
        codes_of(&src)
    );
}

// Repro 4: `Vec::map` wants `Fn(i64) -> i64`; the closure param is `str`.
// Pre-fix: silently ACCEPTED.
#[test]
fn map_closure_wrong_param_str_is_t071() {
    let src = wrap(&format!(
        "{FILL}    let m: Vec<i64> = v.map(fn(s: str) -> i64 {{ return 0; }});\n\
         \x20   return 0 - m.len();"
    ));
    assert!(
        has(&src, "T071"),
        "map closure with a str param (wants Fn(i64)->i64) must be T071, got {:?}",
        codes_of(&src)
    );
}

// A non-closure arg in a closure slot (a scalar where `Fn` is expected) is also
// caught — and reported exactly ONCE (the IntLit arm handles the literal case;
// the new Fn arm excludes IntLit to avoid a duplicate diagnostic).
#[test]
fn scalar_where_closure_expected_is_single_t071() {
    let src = wrap(&format!(
        "{FILL}    let m: Vec<i64> = v.map(5);\n\
         \x20   return 0 - m.len();"
    ));
    let codes = codes_of(&src);
    let n = codes.iter().filter(|c| *c == "T071").count();
    assert_eq!(
        n, 1,
        "an int literal in a closure slot must be exactly one T071 (no duplicate), got {codes:?}"
    );
}

// ── Generic USER impl method (exercises the apply_subst Fn path) ──────────────

const GENERIC_WRAP: &str = "module tool;\n\
    record Wrap<T> { val: T }\n\
    impl Wrap<T> {\n\
    \x20   pub fn apply(self: Wrap<T>, f: Fn(T) -> T) -> T { return f(self.val); }\n\
    }\n";

// A generic impl method's `Fn(T) -> T` param substitutes to `Fn(i64) -> i64` at
// `Wrap<i64>`; a closure returning `bool` mismatches the substituted signature.
// Pre-fix this slipped through the method arg loop just like the stdlib cases.
#[test]
fn generic_impl_method_closure_mismatch_is_t071() {
    let src = format!(
        "{GENERIC_WRAP}\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n\
         \x20   let w: Wrap<i64> = Wrap {{ val: 5 }};\n\
         \x20   let r: i64 = w.apply(fn(x: i64) -> bool {{ return x > 0; }});\n\
         \x20   return 0 - r;\n\
         }}\n"
    );
    assert!(
        has(&src, "T071"),
        "generic method `Fn(T)->T` at T=i64 given a `Fn(i64)->bool` closure must be T071, got {:?}",
        codes_of(&src)
    );
}

// ── Free-call PARITY control: the same mismatch on a FREE fn already rejects ──

#[test]
fn free_call_closure_mismatch_is_t071_parity() {
    // This already worked pre-fix; it pins the parity the method path now matches.
    let src = "module tool;\n\
        fn takes_fn(f: Fn(i64) -> i64) -> i64 { return f(3); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   return 0 - takes_fn(fn(x: i64) -> bool { return x > 0; });\n\
        }\n";
    assert!(
        has(src, "T071"),
        "free-call closure return mismatch must be T071, got {:?}",
        codes_of(src)
    );
}

// ── Positive controls: correctly-typed closures must STILL compile ───────────

// The Phase-7 happy paths: a correct `map`/`filter`/`fold` closure compiles —
// guards against the new arm over-tightening (false-positive T071).
#[test]
fn correct_eager_adapter_closures_still_compile() {
    let src = wrap(&format!(
        "{FILL}    let m: Vec<i64> = v.map(fn(x: i64) -> i64 {{ return x * 2; }});\n\
         \x20   let f: Vec<i64> = m.filter(fn(x: i64) -> bool {{ return x > 0; }});\n\
         \x20   let s: i64 = f.fold(0, fn(a: i64, b: i64) -> i64 {{ return a + b; }});\n\
         \x20   return 0 - s;"
    ));
    assert!(
        compile_tool(&src).is_ok(),
        "well-typed map/filter/fold closures must compile, got {:?}",
        codes_of(&src)
    );
}

// The lazy spec chain with correct closures still composes. Each step is bound to
// a `let` — the codebase convention (mirroring `iterator_adapters.rs`), since a
// fluent `.filter(fn(){...}).map(...)` one-liner hits a parser limitation (P001).
#[test]
fn correct_lazy_chain_closures_still_compile() {
    let src = wrap(&format!(
        "{FILL}    let it = v.iter();\n\
         \x20   let p = it.filter(fn(x: i64) -> bool {{ return x > 0; }});\n\
         \x20   let m = p.map(fn(x: i64) -> i64 {{ return x + 1; }});\n\
         \x20   let t = m.take(2);\n\
         \x20   let c: Vec<i64> = t.collect();\n\
         \x20   return 0 - c.len();"
    ));
    assert!(
        compile_tool(&src).is_ok(),
        "well-typed lazy iterator chain must compile, got {:?}",
        codes_of(&src)
    );
}

// The generic impl method with a CORRECT closure compiles — proves the
// substituted `Fn(i64)->i64` param accepts a matching closure (no false positive
// from the `type_mentions_generic` screen + concrete substitution).
#[test]
fn generic_impl_method_correct_closure_compiles() {
    let src = format!(
        "{GENERIC_WRAP}\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n\
         \x20   let w: Wrap<i64> = Wrap {{ val: 5 }};\n\
         \x20   let r: i64 = w.apply(fn(x: i64) -> i64 {{ return x + x; }});\n\
         \x20   return 0 - r;\n\
         }}\n"
    );
    assert!(
        compile_tool(&src).is_ok(),
        "generic method `Fn(T)->T` at T=i64 given a matching `Fn(i64)->i64` closure must compile, got {:?}",
        codes_of(&src)
    );
}

// Int-literal flex is UNTOUCHED: a generic method's SCALAR param `x: T` receives
// an int literal whose width is inferred from T (the deliberate "method-arg check
// is INT-LITERAL-only" flex the generics epic relies on). The new arm is scoped
// to `Type::Fn` params, so this scalar-literal path is unaffected.
#[test]
fn int_literal_generic_scalar_method_arg_flex_preserved() {
    let src = "module tool;\n\
        record Box<T> { v: T }\n\
        impl Box<T> {\n\
        \x20   pub fn replace(self: Box<T>, x: T) -> T { return x; }\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let b: Box<i64> = Box { v: 1 };\n\
        \x20   return 0 - b.replace(5);\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "int literal into a generic scalar method param (T=i64) must still compile, got {:?}",
        codes_of(src)
    );
}
