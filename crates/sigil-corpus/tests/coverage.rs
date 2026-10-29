//! The done-line gate (`docs/specs/training-corpus.md` §8 PR-5): the ET-C9
//! coverage floor (every registry diagnostic code has an error reference) and
//! the ET-C6 reconciliation identity, plus per-extractor presence.

use sigil_compiler::registry::CODES;
use sigil_corpus::extract::ExtractCtx;
use sigil_corpus::{BuildResult, build, corpus_paths};

fn ctx() -> ExtractCtx {
    ExtractCtx {
        workspace_root: corpus_paths::workspace_root(),
        git_sha: "test-sha".to_string(),
        offline: true, // pr_history's network path is excluded from the gate
    }
}

/// The corpus, built ONCE for the three tests below. Each used to call `build` itself, and a build
/// compiles every candidate program (about 3,700, nearly 30 s locally). `build` is deterministic
/// (`determinism.rs` builds twice and compares, so it keeps its own raw calls), so three builds
/// computed the same result three times. A build that panics leaves the cell empty, and the next
/// test builds again rather than inheriting a half-built value.
fn built() -> &'static BuildResult {
    static BUILT: std::sync::OnceLock<BuildResult> = std::sync::OnceLock::new();
    BUILT.get_or_init(|| build(&ctx()).expect("build"))
}

#[test]
fn every_registry_code_has_a_reference_record() {
    let b = built();
    for entry in CODES {
        let id = format!("error_corpus:{}", entry.code.as_str());
        assert!(
            b.records.contains_key(&id),
            "ET-C9 coverage floor: no error reference for {}",
            entry.code.as_str(),
        );
    }
}

#[test]
fn ledger_reconciles_and_extractors_are_present() {
    let b = built();
    // ET-C6 conservation (build also asserts this internally).
    assert_eq!(
        b.proposed,
        b.records.len() + b.ledger.total(),
        "proposed must equal emitted + dropped",
    );

    let count = |ex: &str| b.records.values().filter(|r| r.extractor == ex).count();
    assert_eq!(count("error_corpus"), CODES.len(), "every code covered");
    assert!(count("source_idiom") > 50, "source idioms present");
    assert!(count("test_fixture") > 20, "fixtures present");
    // The inline-program extractor mines the bulk of the harness corpus; a
    // regression that silently stopped finding them would breach this floor.
    assert!(
        count("inline_program") > 500,
        "inline programs present (got {})",
        count("inline_program"),
    );
    // pr_history is offline-skipped here (it shells out to gh); it is exercised
    // by `cargo run -p sigil-corpus -- build`.
}

#[test]
fn no_validated_intent_record_is_unvalidated() {
    use sigil_corpus::schema::ValidationKind;
    let b = built();
    for r in b.records.values() {
        if matches!(
            r.validated.how,
            ValidationKind::ParsedTypechecked | ValidationKind::ReproducedCode { .. }
        ) {
            assert!(r.validated.ok, "ET-C1: {} emitted unvalidated", r.id);
        }
    }
}
