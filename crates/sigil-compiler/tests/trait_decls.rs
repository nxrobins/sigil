//! PR-3a of the trait epic — `trait` declarations (parse + register).
//!
//! A `trait Name { fn m(self: Self, …) -> Ty; … }` parses into an `Item::TraitDef`
//! and is registered into `TypeUniverse.traits` as a contract. v1 carries method
//! SIGNATURES only (no default body), no trait-level type params, and no
//! super-traits. NOTHING enforces the contract yet — the registry, satisfaction
//! check and bound enforcement are PR-3b — so a declared trait is inert and
//! compilation of existing (trait-free) programs is byte-identical.
//!
//! AST shape is asserted via `parse_program!`; inertness and the "no body" /
//! malformed rules go through `compile_tool`.

use sigil_compiler::ast::Item;
use sigil_compiler::compile_tool;
use sigil_test_utils::parse_program;

fn first_trait(src: &str) -> sigil_compiler::ast::TraitDef {
    let prog = parse_program!(src);
    let Item::TraitDef(def) = &prog.modules[0].items[0] else {
        panic!("expected the first item to be a TraitDef");
    };
    def.clone()
}

// ── AST shape ─────────────────────────────────────────────────────────────────

#[test]
fn single_method_trait() {
    let def = first_trait("module m;\ntrait Hash { fn hash(self: Self) -> i64; }\n");
    assert_eq!(def.name, "Hash");
    assert!(
        def.super_traits.is_empty(),
        "v1 traits have no super-traits"
    );
    assert_eq!(def.methods.len(), 1);
    assert_eq!(def.methods[0].name, "hash");
    assert_eq!(def.methods[0].params.len(), 1, "just `self`");
    assert!(def.methods[0].return_type.is_some());
}

#[test]
fn two_param_method_trait() {
    let def = first_trait("module m;\ntrait Eq { fn eq(self: Self, other: Self) -> bool; }\n");
    assert_eq!(def.name, "Eq");
    assert_eq!(def.methods[0].name, "eq");
    assert_eq!(def.methods[0].params.len(), 2, "`self` and `other`");
}

#[test]
fn multi_method_trait_preserves_order() {
    let def = first_trait(
        "module m;\ntrait Both {\n  fn hash(self: Self) -> i64;\n  fn eq(self: Self, other: Self) -> bool;\n}\n",
    );
    assert_eq!(def.methods.len(), 2);
    assert_eq!(def.methods[0].name, "hash");
    assert_eq!(def.methods[1].name, "eq");
}

#[test]
fn empty_marker_trait_parses() {
    let def = first_trait("module m;\ntrait Marker { }\n");
    assert_eq!(def.name, "Marker");
    assert!(def.methods.is_empty());
}

// ── end-to-end: a declared trait is inert ─────────────────────────────────────

#[test]
fn declaring_traits_compiles_and_is_inert() {
    // The contract is stored in the universe but enforced by nobody yet, so a
    // program that merely DECLARES traits must compile unchanged.
    let src = "module tool;\n\
        trait Hash { fn hash(self: Self) -> i64; }\n\
        trait Eq { fn eq(self: Self, other: Self) -> bool; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 7; }\n";
    assert!(
        compile_tool(src).is_ok(),
        "declaring traits must not break compilation"
    );
}

// ── the v1 rules: signatures only ─────────────────────────────────────────────

#[test]
fn trait_method_body_is_rejected() {
    // CM-T3 posture: v1 trait methods are signatures only. A default body is a
    // parse error (the `;` is expected after the signature).
    let src = "module tool;\n\
        trait Hash { fn hash(self: Self) -> i64 { return 0; } }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 1; }\n";
    assert!(
        compile_tool(src).is_err(),
        "a trait method with a body must be rejected (signatures only)"
    );
}

#[test]
fn non_fn_in_trait_body_is_rejected() {
    let src = "module tool;\n\
        trait Bad { let x: i64; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 1; }\n";
    assert!(
        compile_tool(src).is_err(),
        "only `fn` signatures are allowed inside a trait body"
    );
}
