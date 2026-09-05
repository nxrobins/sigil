//! PR-2 of the trait epic — `<T: Bound + Bound + …>` trait-bound parsing.
//!
//! The `parse_type_params` chokepoint now accepts an optional `: Bound + …`
//! list after each type-parameter name, collected by NAME onto
//! `TypeParam.bounds`. This PR is SYNTAX only: bounds are stored but never read
//! (unknown-trait + satisfaction checks are PR-3/PR-4, at type-check). So a
//! bounded generic that is otherwise valid compiles exactly as if unbounded —
//! the gate is snapshot-safe.
//!
//! Happy-path shape is asserted on the real AST via `parse_program!`; malformed
//! syntax and the compiles-and-ignores end-to-end check go through `compile_tool`.

use sigil_compiler::ast::Item;
use sigil_compiler::compile_tool;
use sigil_test_utils::parse_program;

/// The `(name, bounds)` of the first item's type-params, which must be a `FnDef`.
fn fn_type_params(src: &str) -> Vec<(String, Vec<String>)> {
    let prog = parse_program!(src);
    let Item::FnDef(def) = &prog.modules[0].items[0] else {
        panic!("expected the first item to be a FnDef");
    };
    def.type_params
        .iter()
        .map(|p| (p.name.clone(), p.bounds.clone()))
        .collect()
}

// ── happy-path AST shape ──────────────────────────────────────────────────────

#[test]
fn single_bound() {
    let tp = fn_type_params("module m;\npub fn f<T: Hash>(x: T) -> T { return x; }\n");
    assert_eq!(tp, vec![("T".to_string(), vec!["Hash".to_string()])]);
}

#[test]
fn composed_bounds() {
    // `+`-separated bounds, in declaration order.
    let tp = fn_type_params("module m;\npub fn f<K: Hash + Eq>(x: K) -> K { return x; }\n");
    assert_eq!(
        tp,
        vec![("K".to_string(), vec!["Hash".to_string(), "Eq".to_string()])]
    );
}

#[test]
fn no_bound_is_empty() {
    // The unbounded common case — bounds is an empty Vec, not absent.
    let tp = fn_type_params("module m;\npub fn f<T>(x: T) -> T { return x; }\n");
    assert_eq!(tp, vec![("T".to_string(), Vec::<String>::new())]);
}

#[test]
fn multi_param_each_with_its_own_bound() {
    // `<T: Hash, U: Eq>` — the comma ends one param's bound list, the next
    // param starts fresh.
    let tp = fn_type_params("module m;\npub fn f<T: Hash, U: Eq>(a: T, b: U) -> T { return a; }\n");
    assert_eq!(
        tp,
        vec![
            ("T".to_string(), vec!["Hash".to_string()]),
            ("U".to_string(), vec!["Eq".to_string()]),
        ]
    );
}

#[test]
fn mixed_bounded_and_unbounded_params() {
    let tp = fn_type_params("module m;\npub fn f<T: Hash, U>(a: T, b: U) -> T { return a; }\n");
    assert_eq!(
        tp,
        vec![
            ("T".to_string(), vec!["Hash".to_string()]),
            ("U".to_string(), Vec::<String>::new()),
        ]
    );
}

#[test]
fn record_type_param_bound() {
    // Bounds parse on a `record` def too (same chokepoint).
    let prog = parse_program!("module m;\nrecord Box<T: Hash> { v: T }\n");
    let Item::RecordDef(def) = &prog.modules[0].items[0] else {
        panic!("expected a RecordDef");
    };
    assert_eq!(def.type_params.len(), 1);
    assert_eq!(def.type_params[0].name, "T");
    assert_eq!(def.type_params[0].bounds, vec!["Hash".to_string()]);
}

// ── end-to-end: a SATISFIED bound compiles ────────────────────────────────────

#[test]
fn bound_compiles_when_satisfied() {
    // PR-3b ENFORCES the bound (this test originally asserted it was merely
    // "ignored"; 3b made it real). With `Hash`/`Eq` declared, `i64` satisfies
    // both via the built-in impls, so a bounded-but-satisfied generic compiles.
    // The args are bound to `i64` locals so `T` concretizes cleanly.
    let src = "module tool;\n\
        trait Hash { fn hash(self: Self) -> i64; }\n\
        trait Eq { fn eq(self: Self, other: Self) -> bool; }\n\
        fn pick<T: Hash + Eq>(a: T, b: T) -> T { return a; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let x: i64 = 3;\n\
        \x20   let y: i64 = 4;\n\
        \x20   let r: i64 = pick(x, y);\n\
        \x20   return 0 - r;\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "a bounded generic whose bound is satisfied (i64: Hash + Eq) compiles"
    );
}

// ── malformed bound syntax is a clean parse error (no hang) ────────────────────

#[test]
fn empty_bound_after_colon_is_error() {
    // `<T: >` — a colon with no trait name. The parser recovers (no infinite
    // loop) but emits a diagnostic, so compilation fails.
    let src = "module tool;\n\
        fn f<T: >(x: T) -> T { return x; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 1; }\n";
    assert!(compile_tool(src).is_err(), "`<T: >` must be a parse error");
}

#[test]
fn trailing_plus_in_bound_is_error() {
    // `<T: Hash +>` — a `+` with no following trait name.
    let src = "module tool;\n\
        fn f<T: Hash +>(x: T) -> T { return x; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 1; }\n";
    assert!(
        compile_tool(src).is_err(),
        "`<T: Hash +>` must be a parse error"
    );
}
