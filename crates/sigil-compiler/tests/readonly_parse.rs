//! PR-0 of the mutation-as-capability epic — parsing `@ReadOnly` / `@Mut`.
//!
//! The param-annotation parser now recognizes a MUTABILITY marker alongside the
//! existing TAINT label, on an orthogonal axis (H7): `name: Type [@taint]
//! [@ReadOnly|@Mut]`, in any order and combination. This PR is REPRESENTATION
//! only — the bit is stored on `Param.mutability` (and threaded to
//! `FunctionSig.param_mutability`) but NO enforcement reads it yet, so an
//! annotated param compiles exactly like a bare one (snapshot-safe). Enforcement
//! is PR-1+ (NC-1/NC-2/NC-3). `@Mut` is parsed + stored DISTINCTLY (NC-4) even
//! though it is behaviorally a no-op today — it carries the bit the H5
//! default-flip will need.
//!
//! Happy-path shape is asserted on the real AST via `parse_program!`; the
//! inert-compiles and conflict checks go through `compile_tool`.

use sigil_compiler::ast::{Item, Mutability, TaintLabel};
use sigil_compiler::compile_tool;
use sigil_test_utils::parse_program;

/// `(name, taint, mutability)` of the first item's params; the first item must
/// be a `FnDef`.
fn fn_params(src: &str) -> Vec<(String, Option<TaintLabel>, Mutability)> {
    let prog = parse_program!(src);
    let Item::FnDef(def) = &prog.modules[0].items[0] else {
        panic!("expected the first item to be a FnDef");
    };
    def.params
        .iter()
        .map(|p| (p.name.clone(), p.taint, p.mutability))
        .collect()
}

// ── happy-path AST shape ──────────────────────────────────────────────────────

#[test]
fn readonly_parses_to_readonly() {
    let ps = fn_params("module m;\nfn f(p: Point @ReadOnly) -> i64 { return 0; }\n");
    assert_eq!(ps, vec![("p".to_string(), None, Mutability::ReadOnly)]);
}

#[test]
fn mut_parses_to_mut_distinctly() {
    // NC-4: `@Mut` is its own variant, NOT collapsed into `Default`.
    let ps = fn_params("module m;\nfn f(p: Point @Mut) -> i64 { return 0; }\n");
    assert_eq!(ps, vec![("p".to_string(), None, Mutability::Mut)]);
    assert_ne!(
        ps[0].2,
        Mutability::Default,
        "@Mut must be distinct from bare"
    );
}

#[test]
fn bare_param_is_default() {
    let ps = fn_params("module m;\nfn f(p: Point) -> i64 { return 0; }\n");
    assert_eq!(ps, vec![("p".to_string(), None, Mutability::Default)]);
}

#[test]
fn taint_and_mutability_compose_in_either_order() {
    // H7: the two axes are independent; both set, neither masks the other.
    let a = fn_params("module m;\nfn f(p: Point @SecretCT @ReadOnly) -> i64 { return 0; }\n");
    assert_eq!(
        a,
        vec![(
            "p".to_string(),
            Some(TaintLabel::SecretCT),
            Mutability::ReadOnly
        )]
    );
    // reverse order parses identically (no lookahead mis-routing).
    let b = fn_params("module m;\nfn f(p: Point @ReadOnly @SecretCT) -> i64 { return 0; }\n");
    assert_eq!(
        b,
        vec![(
            "p".to_string(),
            Some(TaintLabel::SecretCT),
            Mutability::ReadOnly
        )]
    );
}

#[test]
fn each_param_carries_its_own_mutability() {
    let ps = fn_params(
        "module m;\nfn f(a: Point @ReadOnly, b: Point, c: Point @Mut) -> i64 { return 0; }\n",
    );
    assert_eq!(
        ps,
        vec![
            ("a".to_string(), None, Mutability::ReadOnly),
            ("b".to_string(), None, Mutability::Default),
            ("c".to_string(), None, Mutability::Mut),
        ]
    );
}

// ── end-to-end: annotations are INERT in PR-0 (no enforcement yet) ────────────

#[test]
fn readonly_param_compiles_clean() {
    // @ReadOnly is stored but unread in PR-0, so it compiles exactly like bare.
    let src = "module tool;\n\
        record Point { x: i64, y: i64 }\n\
        fn read(p: Point @ReadOnly) -> i64 { return p.x; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let q: Point = Point { x: 5, y: 6 };\n\
        \x20   return 0 - read(q);\n\
        }\n";
    assert!(
        compile_tool(src).is_ok(),
        "@ReadOnly is inert in PR-0; compiles clean"
    );
}

#[test]
fn mut_param_is_a_noop_today() {
    // @Mut behaves identically to bare (it carries the flip bit, no behavior).
    let bare = "module tool;\n\
        record Point { x: i64, y: i64 }\n\
        fn f(p: Point) -> i64 { return p.x; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let q: Point = Point { x: 5, y: 6 };\n\
        \x20   return 0 - f(q);\n\
        }\n";
    let annotated = bare.replace("p: Point)", "p: Point @Mut)");
    assert!(compile_tool(bare).is_ok());
    assert!(
        compile_tool(&annotated).is_ok(),
        "@Mut compiles exactly like bare"
    );
}

// ── conflict + unknown: clean parse errors (H3, CM-spelling) ──────────────────

#[test]
fn readonly_and_mut_together_is_a_parse_error() {
    // H3: a param cannot hold contradictory mutation authority.
    let src = "module tool;\n\
        record Point { x: i64, y: i64 }\n\
        fn f(p: Point @ReadOnly @Mut) -> i64 { return p.x; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 1; }\n";
    match compile_tool(src) {
        Ok(_) => panic!("@ReadOnly @Mut on one param must be rejected"),
        Err(e) => assert!(
            format!("{e:?}").contains("P021"),
            "expected P021, got {e:?}"
        ),
    }
}

#[test]
fn unknown_annotation_is_a_parse_error() {
    // CM-spelling: `@Frozen` is not a recognized marker → rejected, not ignored.
    let src = "module tool;\n\
        record Point { x: i64, y: i64 }\n\
        fn f(p: Point @Frozen) -> i64 { return p.x; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 1; }\n";
    assert!(
        compile_tool(src).is_err(),
        "@Frozen is unknown → parse error"
    );
}
