//! Wall 4 Step 2 V25: diagnostic-output determinism cross-check.
//!
//! `determinism_lock.rs` guards WASM byte-equality across compile
//! invocations, but refinements are stripped at AIR lowering and never
//! reach codegen — meaning a refinement-attachment nondeterminism (e.g.
//! HashMap-keyed lookup ordering in `record_refinements`) would produce
//! byte-identical wasm AND DIFFERENT DIAGNOSTIC TEXT, silently.
//!
//! This test closes that gap: compile each Wall 4 Step 2 fixture twice
//! in the same process and assert the rendered diagnostic messages are
//! byte-identical across runs. Any difference is a determinism bug in
//! the refinement-attachment path.
//!
//! Covers fixtures 29-33 (Step 2 corpus). Fixtures that compile cleanly
//! (29, 32, 33) produce empty diagnostic lists — the test still asserts
//! both runs produce the same (empty) list. Fixtures that fire T211 or
//! T215 (30, 31) produce identical message text on both runs.

#![cfg(feature = "solver")]

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use sigil_compiler::{Diagnostic, compile_named_module};

const STEP2_FIXTURES: &[&str] = &[
    "29_refinement_preserved.sigil",
    "30_refinement_dropped_in_destructure.sigil",
    "31_refinement_mismatch.sigil",
    "32_refinement_preserved_via_reassignment.sigil",
    "33_refinement_nested_field_access.sigil",
    // Wall 4 Step 3 V40 extension: fixtures 34-37 exercise Z3-backed
    // subsumption. Byte-identical diagnostics across compiles requires
    // V44 + V45's cache shape — the counterexample is cached alongside
    // the verdict, so 2nd-compile cache hits don't lose the cex.
    "34_refinement_semantic_subset.sigil",
    "35_refinement_equivalent_op.sigil",
    "36_refinement_semantic_non_subset.sigil",
    "37_refinement_eq_subsumes_ge.sigil",
];

fn corpus_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("z3_corpus")
}

/// Returns the sorted list of (code, message) pairs from a compile
/// invocation. Sort by code so HashMap-iteration nondeterminism between
/// inserts (which we DON'T want this test to flag — that's a separate
/// concern) doesn't masquerade as a diagnostic order issue. The test's
/// goal is to detect content nondeterminism, not insertion-order
/// nondeterminism.
fn collect_diagnostics(source: &str, name: &str) -> Vec<(String, String)> {
    match compile_named_module(name, source) {
        Ok(_) => Vec::new(),
        Err(e) => {
            let mut diags: Vec<(String, String)> = e
                .diagnostics()
                .iter()
                .map(|d: &Diagnostic| (d.code().to_string(), d.message().to_string()))
                .collect();
            diags.sort();
            diags
        }
    }
}

#[test]
fn v25_step2_fixtures_produce_deterministic_diagnostics() {
    let dir = corpus_dir();
    let mut covered: BTreeSet<&str> = BTreeSet::new();

    for fixture_name in STEP2_FIXTURES {
        let path = dir.join(fixture_name);
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read {fixture_name}: {e}"));

        let run_a = collect_diagnostics(&source, fixture_name);
        let run_b = collect_diagnostics(&source, fixture_name);

        assert_eq!(
            run_a, run_b,
            "V25: fixture `{fixture_name}` produced different diagnostics across two \
             consecutive compile invocations. Refinement attachment must be deterministic — \
             a HashMap-keyed lookup in `record_refinements` or a sort-by-insert-order \
             would surface here.\n\
             Run A: {run_a:?}\n\
             Run B: {run_b:?}",
        );

        covered.insert(*fixture_name);
    }

    assert_eq!(
        covered.len(),
        STEP2_FIXTURES.len(),
        "V25: all Step 2 fixtures must be exercised in this test"
    );
}
