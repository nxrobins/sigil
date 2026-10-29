//! Pinned boundary: a build without the `solver` feature (the stock `sigil`, `sigil-mcp`,
//! `sigil-serve` and `sigil-corpus`, and this gating lane) treats every refinement obligation it
//! collects as holding, literal ones included, and refuses every construction-site subsumption with
//! T215; only the collector's refusal of a symbolic argument with no fact (T211) still runs. So,
//! read from the `z3_corpus` fixture headers, the fixtures that declare a violation and still
//! compile here, and the ones that declare themselves valid and are refused here, are exactly the
//! sets below. The certificate of such a build is not solver-verified, so running its artifact is
//! refused unless unverified certificates are explicitly allowed. Measured by the design-by-contract
//! spec (draft PR 761, section 3.2) and re-measured on `main` `e3a33349`; DBC-0b (2026-10-14) added
//! the two field-store fixtures whose literal store is an obligation this build collects and does
//! not decide (#106 into a local's field, #109 through an `@Mut` parameter), beside the stores it
//! refuses on its own (#107 T211, #108 T216). Written to fail when the boundary moves either way
//! (a fixture added or decided differently, or the spec's DBC-1, one decision procedure with a
//! solver-free backend): then `docs/RESIDUAL_RISKS.md` (SR-038) and `docs/SOUNDNESS_MATRIX.md`
//! SND-REFINE-001 move with it. In the `solver` lane this file is empty: `z3_corpus.rs` checks
//! every header there.

#![cfg(not(feature = "solver"))]

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use sigil_test_utils::pipeline::compile_module_codes;

/// What a fixture's leading comment block declares.
enum Declared {
    /// `// expect-ok`.
    Valid,
    /// `// expect-error: A, B`, as an exact code set.
    Violation(BTreeSet<String>),
    /// `// expect-shape: ...`: a proof-shape fixture, no accept/refuse verdict to compare.
    Shape,
}

fn declared(source: &str) -> Option<Declared> {
    for line in source.lines() {
        let line = line.trim();
        if let Some(codes) = line.strip_prefix("// expect-error:") {
            return Some(Declared::Violation(
                codes
                    .split(',')
                    .map(|code| code.trim().to_string())
                    .filter(|code| !code.is_empty())
                    .collect(),
            ));
        }
        if line.starts_with("// expect-ok") {
            return Some(Declared::Valid);
        }
        if line.starts_with("// expect-shape") {
            return Some(Declared::Shape);
        }
        if !line.starts_with("//") && !line.is_empty() {
            return None;
        }
    }
    None
}

#[test]
fn known_gap_solver_off_build_does_not_decide_refinement_contracts() {
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/z3_corpus");
    let mut fixtures = 0;
    let mut violations_accepted = BTreeMap::<String, BTreeSet<String>>::new();
    let mut valid_refused = BTreeMap::<String, BTreeSet<String>>::new();
    let mut entries = std::fs::read_dir(&corpus)
        .unwrap_or_else(|error| panic!("{} is readable: {error}", corpus.display()))
        .map(|entry| entry.expect("a corpus entry is readable").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "sigil"))
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        let name = path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .expect("a corpus file name is UTF-8")
            .to_string();
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("{name} is readable: {error}"));
        let Some(expectation) = declared(&source) else {
            panic!("{name}: no `// expect-ok`, `// expect-error:` or `// expect-shape:` header");
        };
        fixtures += 1;
        match expectation {
            Declared::Shape => {}
            Declared::Violation(solver_codes) => {
                if sigil_compiler::compile_module(&source).is_ok() {
                    violations_accepted.insert(name, solver_codes);
                }
            }
            Declared::Valid => {
                let refused_with = compile_module_codes(&source)
                    .into_iter()
                    .collect::<BTreeSet<_>>();
                if !refused_with.is_empty() {
                    valid_refused.insert(name, refused_with);
                }
            }
        }
    }
    assert!(
        fixtures >= 90,
        "read only {fixtures} z3_corpus fixtures; the corpus moved or the walk broke"
    );

    let code = |c: &str| BTreeSet::from([c.to_string()]);
    let expected_violations = BTreeMap::from([
        ("26_refinement_fail".to_string(), code("T210")),
        ("27_refinement_mutation_fail".to_string(), code("T210")),
        ("40_refinement_zero_boundary".to_string(), code("T224")),
        ("43_refinement_xfield_fail".to_string(), code("T210")),
        ("47_variant_refinement_fail".to_string(), code("T220")),
        ("53_fn_param_refinement_fail".to_string(), code("T224")),
        ("55_fn_return_refinement_fail".to_string(), code("T225")),
        ("59_if_narrow_then_arm_fail".to_string(), code("T224")),
        ("78_u256_refinement_fail".to_string(), code("T210")),
        ("79_u256_wide_refinement_fail".to_string(), code("T210")),
        (
            "106_dbc0_field_store_literal_fail".to_string(),
            code("T210"),
        ),
        (
            "109_dbc0_field_store_through_mut_param_fail".to_string(),
            code("T210"),
        ),
    ]);
    let expected_refused = BTreeMap::from([
        ("34_refinement_semantic_subset".to_string(), code("T215")),
        ("35_refinement_equivalent_op".to_string(), code("T215")),
        ("37_refinement_eq_subsumes_ge".to_string(), code("T215")),
    ]);
    // The refusals first: they show this harness surfaces codes from this corpus in this build, so
    // the accepted set below is this build's verdict, not a harness that drops diagnostics.
    assert_eq!(
        valid_refused, expected_refused,
        "the valid fixtures this build refuses moved: update SR-038 and SND-REFINE-001"
    );
    assert_eq!(
        violations_accepted, expected_violations,
        "the contract-breaking fixtures this build accepts (with the codes the solver build refuses \
         them with) moved: update SR-038 and SND-REFINE-001"
    );
}
