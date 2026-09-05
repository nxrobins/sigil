//! Recovery-boundary regressions for taint analysis.
//!
//! Invalid source may produce a partial `TypedProgram` for diagnostic
//! aggregation, but the production severity gate must stop it before security
//! passes. If a malformed typed tree is inspected directly, taint analysis must
//! fail closed with I013 rather than panic or silently truncate a positional zip.

use proptest::prelude::*;
use sigil_compiler::source::SourceFile;
use sigil_compiler::{
    CompileOptions, compile_named_module, name_resolution, parser, taint_check, type_check,
};

fn generic_call_source(arg_count: usize) -> String {
    let args = (0..arg_count)
        .map(|value| value.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "module taint_recovery;\n\
         fn identity<T>(x: T) -> T {{ return x; }}\n\
         fn probe() -> u32 {{ return identity::<u32>({args}); }}\n"
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn every_wrong_generic_call_arity_is_i013_not_an_abort(
        arg_count in prop_oneof![Just(0_usize), 2_usize..=6],
    ) {
        let source = generic_call_source(arg_count);
        let error = compile_named_module("taint_recovery.sigil", &source)
            .expect_err("wrong generic-call arity must be rejected");
        let codes = error
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect::<Vec<_>>();

        prop_assert!(codes.contains(&"I013"), "arity {arg_count}: {codes:?}");
    }
}

#[test]
fn malformed_partial_typed_call_fails_closed_in_taint() {
    let source = SourceFile::new("taint_recovery.sigil", generic_call_source(0));
    let (ast, parse_diagnostics) = parser::parse(&source);
    assert!(parse_diagnostics.is_empty(), "{parse_diagnostics:?}");
    let resolved = name_resolution::resolve(&ast).expect("source names must resolve");
    let (typed, _registry, diagnostics) =
        type_check::check_collecting(&resolved, &CompileOptions::default());
    assert!(
        diagnostics.is_empty(),
        "generic arity remains a downstream integrity check: {diagnostics:?}"
    );

    let taint_diagnostics =
        taint_check::check_taints(&typed).expect_err("malformed typed call must fail closed");
    assert!(
        taint_diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code().as_str() == "I013"),
        "taint checker must reject its malformed input: {taint_diagnostics:?}"
    );
}

#[test]
fn taint_checker_source_has_no_release_abort_primitives() {
    let source = include_str!("../src/taint_check.rs");
    for forbidden in ["panic!(", "assert_eq!(", ".unwrap()", ".expect("] {
        assert!(
            !source.contains(forbidden),
            "taint analysis is a user-reachable compiler pass; use an I013 diagnostic instead of `{forbidden}`"
        );
    }
    assert!(
        source
            .lines()
            .all(|line| !line.trim_start().starts_with("assert!(")),
        "taint analysis must not add an always-on assertion; use an I013 diagnostic"
    );
}
