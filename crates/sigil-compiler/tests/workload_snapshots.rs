#![cfg(feature = "solver")]

//! Pillar 3 — golden snapshots of the **v2 RefinementWorkload +
//! CapabilityWorkload** for every fixture in `cve_corpus/` and
//! `z3_corpus/`.
//!
//! **Solver-gated.** Several fixtures (e.g. `z3_corpus/26_refinement_fail`)
//! depend on Z3 to reject refinement violations. Without the `solver`
//! feature, those checks no-op and the fixture passes type-check — a
//! different outcome whose snapshots would conflict with the `solver`-
//! enabled ones. The `#![cfg(feature = "solver")]` gate at the crate
//! root keeps this test in the solver-enabled-only matrix slot, matching
//! `cache_determinism.rs`'s precedent for the same reason.
//!
//! ## What this catches
//!
//! The v2 (I/O Quarantine) pipeline splits into three phases:
//!
//!   1. **Pure** — `collect_refinement_obligations` and
//!      `collect_capability_obligations` walk a TypedProgram and emit
//!      obligation Vecs.
//!   2. **Discharge** — the only Z3 callers in the type_check tree
//!      route each obligation to its `z3_capability::check_*` site.
//!   3. **Token-gated codegen** — `DischargedRefinements` and
//!      `DischargedCapabilities` are private-constructor proof tokens
//!      that downstream codegen will consume by value (PR 3 of the
//!      Quarantine plan).
//!
//! This test pins the **output of Phase 1** for every CVE + Z3
//! fixture in the corpus. A regression where a new inferer forgets
//! to push an obligation — or where the collector silently drops one
//! — surfaces here as a localized snapshot diff, BEFORE Z3 runs.
//! Without this test, the same regression would only manifest as a
//! shadow-divergence failure deep in the pipeline, where bisection
//! is much harder.
//!
//! ## What this DOES NOT catch
//!
//! Verdict-routing bugs in `discharge_refinements` /
//! `discharge_capabilities` (e.g. mapping `Violated` to `Holds`).
//! Those are caught end-to-end by the corpus + precision gates
//! (`z3_corpus`, `diagnostic_precision`, `refinement_mixed_error`), which
//! compile fixtures through the production path, and by the orchestrator's
//! own unit tests in `type_check_v2/mod.rs`.
//!
//! ## Failing fixtures
//!
//! UNSAFE variants of CVE fixtures (e.g.
//! `01_cve_2021_44228_log4shell.sigil`) are EXPECTED to be rejected
//! by type-check — that's the whole point. For those, the workload
//! collector can't run (no TypedProgram). Instead of skipping, this
//! test snapshots a stable placeholder
//! (`<TYPE_CHECK_FAILED: [T155, T199]>`) constructed from the sorted
//! list of error codes. A regression where type-check STOPS
//! rejecting one of those patterns surfaces as the placeholder
//! changing to a workload snapshot — caught immediately.
//!
//! ## Snapshot naming
//!
//! `workload_snapshots__<corpus>__<filename_stem>.snap`. So
//! `tests/cve_corpus/01_cve_2021_44228_log4shell.sigil` →
//! `workload_snapshots__cve__01_cve_2021_44228_log4shell.snap`.

use std::fs;
use std::path::PathBuf;

use sigil_test_utils::assert_canonical_snapshot;
use sigil_test_utils::pipeline::collect_workloads_or_skip;

/// Test corpora. Stable names that become the `<corpus>` token in
/// snapshot filenames.
const CORPORA: &[(&str, &str)] = &[("cve", "tests/cve_corpus"), ("z3", "tests/z3_corpus")];

#[test]
fn snapshot_v2_workloads_for_corpus_fixtures() {
    // CARGO_MANIFEST_DIR points at `crates/sigil-compiler/`. The
    // corpora are under tests/ relative to that root.
    let crate_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    for (corpus_label, corpus_relpath) in CORPORA {
        let corpus_dir = crate_root.join(corpus_relpath);
        let entries: Vec<PathBuf> = fs::read_dir(&corpus_dir)
            .unwrap_or_else(|e| {
                panic!("failed to read corpus dir {corpus_dir:?}: {e}");
            })
            .filter_map(|entry| entry.ok())
            .map(|entry| entry.path())
            .filter(|path| {
                path.extension()
                    .and_then(|e| e.to_str())
                    .map(|s| s == "sigil")
                    .unwrap_or(false)
            })
            .collect();

        // Sort by path so iteration order is deterministic regardless
        // of filesystem dirent order. (HashMap-style determinism trap
        // even at the OS layer.)
        let mut entries = entries;
        entries.sort();

        assert!(
            !entries.is_empty(),
            "expected at least one .sigil fixture in {corpus_dir:?}"
        );

        for path in &entries {
            let src = fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("failed to read fixture {path:?}: {e}"));
            let stem = path
                .file_stem()
                .and_then(|s| s.to_str())
                .expect("fixture path has UTF-8 stem");
            let snapshot_name = format!("{corpus_label}__{stem}");

            // Try to collect the workload. On type-check failure,
            // snapshot a stable summary placeholder instead.
            match collect_workloads_or_skip(&src) {
                Ok(result) => {
                    assert_canonical_snapshot!(snapshot_name.as_str(), &result);
                }
                Err(failure) => {
                    let summary = failure.summary();
                    insta::assert_snapshot!(snapshot_name.as_str(), summary);
                }
            }
        }
    }
}
