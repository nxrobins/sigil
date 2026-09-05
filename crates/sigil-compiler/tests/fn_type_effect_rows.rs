//! `Fn(T) -> U ! { E }` — latent effect rows on function TYPES (roadmap Phase 3).
//!
//! Before this, an annotated `Fn` parameter always resolved to the EMPTY row, so an
//! effectful closure could not be passed to any higher-order function at all (the
//! interim contract #655 documented). The row suffix lifts that ceiling.
//!
//! TWO POLICY DECISIONS ARE PINNED HERE, both deliberate asymmetries:
//!
//! 1. STRICT NAMES. An unregistered effect name in a TYPE row is a hard T069 at the
//!    annotation site. Declaration rows keep their documented silent drop (the
//!    SH-EFFECT-pinned registration filter) — the new surface is born strict because
//!    it has no legacy corpus, while every expression-position surface (`perform`
//!    E006, `handle` T069) is already strict. A dropped TYPE row is sound (it can
//!    only over-reject) but its rejection lands at a CALLER, names neither the typo
//!    nor the annotation, and fires only if some caller happens to pass an effectful
//!    closure — so the failure is silent-until-conditional, which is the opposite of
//!    what an agent-facing compiler should do.
//!
//! 2. DECLARATION-RETURN BINDING. In `fn f() -> Fn(T) -> U ! { E }` the trailing row
//!    binds to the DECLARATION, exactly as before this syntax existed; parentheses
//!    opt into type-binding. A P031 WARNING marks the suppressed site so the choice is
//!    never silent. THE PARSER DIFFERENTIAL CANNOT ADJUDICATE THIS — both the Rust and
//!    selfhost sides would change meaning together — so the AST-level assertions below
//!    are the real pin.

use sigil_compiler::ast::Item;
use sigil_compiler::source::SourceFile;
use sigil_test_utils::pipeline::compile_module_codes;

/// THE POINT OF PHASE 3: an effectful closure crosses an annotated `Fn` boundary.
/// Before the row suffix this was impossible — the parameter always promised `{}`,
/// so contravariance rejected every effectful argument.
#[test]
fn effectful_closure_crosses_an_annotated_boundary() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h(f: Fn(i64) -> i64 ! { Log }) -> i64 ! { Log } { return f(42); }\n\
         fn caller() -> i64 ! { Log } { return h(fn(x: i64) -> i64 { return logs(); }); }\n",
    );
    assert!(
        codes.is_empty(),
        "an effectful closure must cross a boundary annotated with its effect; got {codes:?}"
    );
}

/// Contravariance the useful direction: a PURE closure still satisfies an
/// effect-annotated parameter (it performs no more than the arrow promises).
#[test]
fn pure_closure_satisfies_an_effectful_annotation() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn h(f: Fn(i64) -> i64 ! { Log }) -> i64 ! { Log } { return f(42); }\n\
         fn caller() -> i64 ! { Log } { return h(fn(x: i64) -> i64 { return x; }); }\n",
    );
    assert!(
        codes.is_empty(),
        "a pure closure performs no more than an effectful arrow promises; got {codes:?}"
    );
}

/// DISCHARGE IS STILL ENFORCED. The row is not decoration: applying an annotated
/// `! { Log }` parameter inside a function whose own row is empty is E001. This is
/// the property that makes the annotation load-bearing rather than documentation.
#[test]
fn applying_an_effectful_param_in_a_pure_fn_is_e001() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn h(f: Fn(i64) -> i64 ! { Log }) -> i64 { return f(42); }\n",
    );
    assert!(
        codes.iter().any(|c| c == "E001"),
        "applying a `! {{ Log }}` parameter in a row-less function must be E001; got {codes:?}"
    );
}

/// STRICT NAMES: an unregistered name in a TYPE row is a hard error at the
/// annotation, not a silent drop.
#[test]
fn unknown_effect_name_in_a_type_row_is_rejected() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn h(f: Fn(i64) -> i64 ! { Lgo }) -> i64 { return 0; }\n",
    );
    assert!(
        codes.iter().any(|c| c == "T069"),
        "a typo'd effect name in a `Fn` type row must be T069 at the annotation; got {codes:?}"
    );
}

/// The contrast that makes decision 1 a real asymmetry rather than an accident:
/// the SAME unregistered name in a DECLARATION row is still silently dropped, so
/// the legacy corpus (~150 `.sigil` files rely on this) is untouched.
#[test]
fn unknown_effect_name_in_a_declaration_row_still_drops() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         fn f() -> i64 ! { Lgo } { return 0; }\n",
    );
    assert!(
        codes.is_empty(),
        "declaration rows keep the documented silent drop (SH-EFFECT registration \
         filter); got {codes:?}"
    );
}

/// DECLARATION-RETURN BINDING, asserted on the AST — the real adjudicator, since the
/// parser differential structurally cannot catch a binding change (both sides would
/// move together). Unparenthesized: the row lands on the DECLARATION, and the
/// returned `Fn` type carries none.
#[test]
fn trailing_row_after_a_fn_return_type_binds_to_the_declaration() {
    let src = "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn make() -> Fn(i64) -> i64 ! { Log } { return make(); }\n";
    let (program, diags) = sigil_compiler::parser::parse_with_id(
        &SourceFile::new("bind.sigil", src),
        Default::default(),
    );
    let (decl_row, type_row) = fn_rows(&program, "make");
    assert_eq!(
        decl_row,
        Some(vec!["Log".to_string()]),
        "the trailing row must bind to the DECLARATION (pre-existing meaning)"
    );
    assert_eq!(
        type_row, None,
        "the returned `Fn` type must NOT capture the trailing row"
    );
    assert!(
        diags.iter().any(|d| d.code().as_str() == "P031"),
        "the suppressed binding must be announced (P031), never silent; got {:?}",
        diags.iter().map(|d| d.code().as_str()).collect::<Vec<_>>()
    );
}

/// PARENTHESES OPT IN: the same row inside `( … )` binds to the TYPE, and the
/// declaration is left row-less. No P031 — the grouping made it unambiguous.
#[test]
fn parenthesized_fn_type_captures_the_row() {
    let src = "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn make() -> (Fn(i64) -> i64 ! { Log }) { return make(); }\n";
    let (program, diags) = sigil_compiler::parser::parse_with_id(
        &SourceFile::new("bind_paren.sigil", src),
        Default::default(),
    );
    let (decl_row, type_row) = fn_rows(&program, "make");
    assert_eq!(
        decl_row, None,
        "the declaration must have no row of its own"
    );
    assert_eq!(
        type_row,
        Some(vec!["Log".to_string()]),
        "parentheses must attach the row to the returned `Fn` TYPE"
    );
    assert!(
        !diags.iter().any(|d| d.code().as_str() == "P031"),
        "no ambiguity warning when the grouping is explicit; got {:?}",
        diags.iter().map(|d| d.code().as_str()).collect::<Vec<_>>()
    );
}

/// A row in PARAMETER position is bounded by `)` and needs no parentheses — the
/// suppression must not leak into nested bounded positions.
#[test]
fn parameter_position_row_binds_to_the_type_without_parens() {
    let src = "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn h(f: Fn(i64) -> i64 ! { Log }, x: i64) -> i64 ! { Log } { return f(x); }\n";
    let (program, diags) = sigil_compiler::parser::parse_with_id(
        &SourceFile::new("bind_param.sigil", src),
        Default::default(),
    );
    assert!(
        diags.is_empty(),
        "a param-position row is unambiguous; got {:?}",
        diags.iter().map(|d| d.code().as_str()).collect::<Vec<_>>()
    );
    let param_row = program
        .modules
        .iter()
        .flat_map(|m| m.items.iter())
        .find_map(|item| match item {
            Item::FnDef(f) if f.name == "h" => f
                .params
                .first()
                .and_then(|p| p.ty.fn_type.as_ref())
                .map(|ft| ft.effects.clone()),
            _ => None,
        })
        .expect("fn `h` with a Fn-typed first param");
    assert_eq!(
        param_row,
        Some(vec!["Log".to_string()]),
        "the row must attach to the parameter's `Fn` type"
    );
}

/// Helper: `(declaration row, returned Fn type's row)` for a named fn.
fn fn_rows(
    program: &sigil_compiler::ast::Program,
    name: &str,
) -> (Option<Vec<String>>, Option<Vec<String>>) {
    program
        .modules
        .iter()
        .flat_map(|m| m.items.iter())
        .find_map(|item| match item {
            Item::FnDef(f) if f.name == name => Some((
                f.effects.clone(),
                f.return_type
                    .as_ref()
                    .and_then(|rt| rt.fn_type.as_ref())
                    .and_then(|ft| ft.effects.clone()),
            )),
            _ => None,
        })
        .unwrap_or_else(|| panic!("fn `{name}` not found"))
}
