//! Acceptance: the build is byte-identical across runs (ET-C5), conserves its
//! ledger (ET-C6, asserted inside `build`), covers both PR-0/PR-1 extractors,
//! and emits only compiler-validated source idioms (ET-C1). `Kind` is total.

use std::collections::BTreeSet;

use sigil_corpus::extract::ExtractCtx;
use sigil_corpus::schema::{Kind, ValidationKind};
use sigil_corpus::{BuildResult, build, corpus_paths, emit};

fn ctx() -> ExtractCtx {
    // The real workspace root, so source_idiom can read selfhost/ + stdlib/.
    ExtractCtx {
        workspace_root: corpus_paths::workspace_root(),
        git_sha: "test-sha".to_string(),
        // offline: the deterministic test must not depend on `gh`/network.
        offline: true,
    }
}

fn serialized(r: &BuildResult) -> Vec<String> {
    r.records
        .values()
        .map(|x| serde_json::to_string(x).unwrap())
        .collect()
}

#[test]
fn build_is_deterministic_balanced_and_validated() {
    let a = build(&ctx()).expect("build a");
    let b = build(&ctx()).expect("build b");

    // ET-C5 — byte-identical records + manifest across runs.
    assert_eq!(
        serialized(&a),
        serialized(&b),
        "records must be byte-identical"
    );
    assert_eq!(
        serde_json::to_string(&emit::manifest(&a)).unwrap(),
        serde_json::to_string(&emit::manifest(&b)).unwrap(),
        "manifest must be deterministic",
    );

    // ET-C6 — conservation (build also asserts this internally).
    assert_eq!(a.proposed, a.records.len() + a.ledger.total());

    // error_corpus — a rejection reference per registry code.
    let refs: Vec<_> = a
        .records
        .values()
        .filter(|r| r.extractor == "error_corpus")
        .collect();
    assert!(
        refs.len() >= 200,
        "expected ~269 error-code references, got {}",
        refs.len()
    );
    assert!(refs.iter().all(|r| r.kind == Kind::Rejection));

    // source_idiom — every emitted idiom is compiler-validated (ET-C1), drawn
    // from both the selfhost trio and the stdlib.
    let idioms: Vec<_> = a
        .records
        .values()
        .filter(|r| r.extractor == "source_idiom")
        .collect();
    assert!(
        idioms.len() >= 50,
        "expected many source idioms, got {}",
        idioms.len()
    );
    assert!(
        idioms.iter().all(|r| r.validated.ok
            && matches!(r.validated.how, ValidationKind::ParsedTypechecked)),
        "every emitted source idiom must be compiler-validated",
    );
    assert!(
        idioms
            .iter()
            .any(|r| r.tags.iter().any(|t| t == "self-hosting")),
        "selfhost idioms present",
    );
    assert!(
        idioms.iter().any(|r| r.tags.iter().any(|t| t == "stdlib")),
        "stdlib idioms present",
    );

    // test_fixture — validated negatives (codes re-derived from the compiler,
    // ET-C2) + positives.
    let fixtures: Vec<_> = a
        .records
        .values()
        .filter(|r| r.extractor == "test_fixture")
        .collect();
    assert!(
        fixtures.len() >= 20,
        "expected many fixtures, got {}",
        fixtures.len()
    );
    assert!(
        fixtures.iter().all(|r| r.validated.ok),
        "every fixture is validated"
    );
    assert!(
        fixtures
            .iter()
            .any(|r| matches!(r.validated.how, ValidationKind::ReproducedCode { .. })),
        "fixture negatives present",
    );
    assert!(
        fixtures
            .iter()
            .any(|r| matches!(r.validated.how, ValidationKind::ParsedTypechecked)),
        "fixture positives present",
    );
    for r in &fixtures {
        for ne in &r.negative_examples {
            assert!(
                sigil_corpus::validate::is_registry_code(&ne.code),
                "fixture negative code `{}` is not a registry code",
                ne.code,
            );
        }
    }
}

#[test]
fn kind_all_is_total_and_distinct() {
    let names: BTreeSet<&str> = Kind::ALL.iter().map(|k| k.as_str()).collect();
    assert_eq!(names.len(), Kind::ALL.len(), "Kind::ALL has duplicates");
    assert_eq!(Kind::ALL.len(), 7, "Kind::ALL is out of sync with the enum");
}
