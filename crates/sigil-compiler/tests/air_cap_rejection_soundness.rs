//! AIR-Cap rejection-corpus soundness test (PR 4b, retargeted at PR 5).
//!
//! ## History
//!
//! Born as the legacy-vs-v2 REJECTION comparison that closed the shadow
//! window's blind spot (the shadow only ever compared on legacy SUCCESS,
//! so it proved "v2 doesn't over-reject" but not "v2 rejects what legacy
//! rejects"). It gated the PR-5 `[ONE-WAY-DELETION]`. At PR 5 the legacy
//! half of the comparison was deleted; the test now pins the SOLE
//! prover's rejection behavior directly against per-fixture expectations
//! (which carry the verdicts the legacy comparison certified).
//!
//! ## What this test does
//!
//! For every fixture the corpus declares a capability rejection
//! (`// expect-error: C00x`), drive parse → name-resolution → type-check
//! → AIR lowering, then run `air_capability_v2::verify_air_capabilities`
//! DIRECTLY on the `AirProgram` and assert it rejects with EXACTLY the
//! pinned C-code set. The full-pipeline witness for the same fixtures
//! (compile_module must fail with the annotated code) lives in
//! `z3_corpus.rs` — this test pins the prover layer in isolation, so a
//! future orchestrator change can't silently reroute around it.
//!
//! ## Solver gate
//!
//! `#![cfg(feature = "solver")]` — C-code rejections come from Z3.

#![cfg(feature = "solver")]

use std::fs;
use std::path::PathBuf;

use sigil_compiler::diagnostics::{Diagnostic, Severity};
use sigil_compiler::source::SourceFile;
use sigil_compiler::{CompileOptions, air, air_capability_v2, name_resolution, parser, type_check};

/// Fixtures the corpus declares as capability rejections, with the exact
/// C-code set the prover must emit (pinned from the legacy-vs-v2
/// byte-equality certified at PR 5). Hard-coded so a fixture silently
/// losing its annotation (and dropping out of the rejection set) is a
/// visible diff here, not an invisible coverage loss.
///
/// `19_multi_branch_meet` is load-bearing: it exercises the `SlotTake`
/// slot-meet authority fold, the one path where the collector's static
/// `actual_mask` diverges from Z3's solved authority. A bitwise-only
/// discharge would NOT reject it; the faithful port must.
const CAP_REJECTION_FIXTURES: &[(&str, &[&str])] = &[
    ("tests/z3_corpus/01_attenuation_at_call.sigil", &["C003"]),
    ("tests/z3_corpus/02_attenuation_at_spawn.sigil", &["C003"]),
    ("tests/z3_corpus/03_attenuation_at_send.sigil", &["C003"]),
    ("tests/z3_corpus/07_attenuation_at_return.sigil", &["C003"]),
    ("tests/z3_corpus/19_multi_branch_meet.sigil", &["C003"]),
];

/// Sorted, deduplicated capability C-codes (C0xx) among error diagnostics.
fn cap_codes(diags: &[Diagnostic]) -> Vec<String> {
    let mut codes: Vec<String> = diags
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .map(|d| d.code().as_str().to_string())
        .filter(|c| c.starts_with('C'))
        .collect();
    codes.sort();
    codes.dedup();
    codes
}

#[test]
fn the_sole_prover_rejects_every_capability_rejection_fixture() {
    let crate_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut exercised = 0usize;

    for (relpath, expected_codes) in CAP_REJECTION_FIXTURES {
        let path = crate_root.join(relpath);
        let src = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read fixture {path:?}: {e}"));

        // Pipeline to AIR. These fixtures pass parse/resolve/type-check —
        // C003 is a post-type-check, post-AIR-lowering capability-flow
        // diagnostic, not a type error — so each stage must succeed.
        let source = SourceFile::new(*relpath, &src);
        let (ast, parse_diags) = parser::parse(&source);
        assert!(
            !parse_diags.iter().any(|d| d.severity() == Severity::Error),
            "{relpath}: unexpected parse error (cap-rejection fixtures must parse cleanly)"
        );
        let resolved = name_resolution::resolve(&ast)
            .unwrap_or_else(|d| panic!("{relpath}: name resolution failed: {:?}", cap_codes(&d)));
        let (typed, registry) =
            type_check::check_with_options(&resolved, &CompileOptions::default()).unwrap_or_else(
                |d| {
                    panic!(
                        "{relpath}: type-check failed (cap-rejection fixtures must type-check; \
                     C003 is a later phase). Diagnostics: {:?}",
                        d.iter().map(|x| x.code().as_str()).collect::<Vec<_>>()
                    )
                },
            );
        let air = air::lower(&typed);

        // The sole prover, DIRECTLY — not through capability::verify, so
        // a future orchestrator change (structural pre-check reordering,
        // report plumbing) can't silently reroute around the Z3 layer
        // this test pins.
        let v2_codes = match air_capability_v2::verify_air_capabilities(&air, &registry) {
            Ok(_) => Vec::new(),
            Err(diags) => cap_codes(&diags),
        };

        let expected: Vec<String> = expected_codes.iter().map(|s| s.to_string()).collect();
        assert_eq!(
            v2_codes, expected,
            "{relpath}: the sole AIR-cap prover did not reject with the pinned \
             C-code set. expected={expected:?}, got={v2_codes:?}. (The pin carries \
             the verdicts the legacy-vs-v2 comparison certified at PR 5 — drift \
             here is a prover regression, not a fixture problem.)"
        );

        exercised += 1;
    }

    // Guard against the fixture list silently shrinking (e.g. a fixture
    // removed or renamed). If this drops, coverage of the rejection path
    // dropped with it.
    assert_eq!(
        exercised,
        CAP_REJECTION_FIXTURES.len(),
        "expected to exercise all {} capability-rejection fixtures, got {exercised}",
        CAP_REJECTION_FIXTURES.len()
    );
    assert!(
        exercised >= 5,
        "expected ≥5 capability-rejection fixtures (incl. the slot-meet case \
         19_multi_branch_meet); got {exercised}. This is the prover-layer \
         rejection coverage the PR-5 deletion was conditioned on."
    );
}
