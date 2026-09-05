//! Semantic evidence-preservation gates.
//!
//! Evidence is pinned by semantic case name, corpus cardinality, and claim coverage. New evidence
//! may grow freely; deleting or renaming an existing obligation requires an explicit manifest and
//! floor update. Structural details such as the number of Rust test functions are not evidence.

use std::collections::HashSet;

#[path = "support/air_case_manifest.rs"]
mod air_case_manifest;
#[path = "support/preservation_manifest.rs"]
mod preservation_manifest;
#[path = "support/test_source.rs"]
mod test_source;

/// PIN-5: required status-check names must still be produced by the workflows.
///
/// Branch protection itself lives on GitHub and cannot be inspected here. This pins the in-repo
/// half of that external contract and prevents a workflow rename from making every merge wait for
/// a context that can no longer report.
#[test]
fn pin5_required_check_names_match_workflow_jobs() {
    const CI_YML: &str = include_str!("../../../.github/workflows/ci.yml");
    const WORKFLOW_LINT_YML: &str = include_str!("../../../.github/workflows/workflow-lint.yml");
    let required = [
        // Release-evidence validation lives in `hygiene`. A pending template that starts making
        // completion claims must block the same merge as a compiler or proof regression.
        ("hygiene", CI_YML, "  hygiene:"),
        ("test", CI_YML, "  test:"),
        ("checks", CI_YML, "  checks:"),
        ("solver", CI_YML, "  solver:"),
        // `interp-ddc` carries claim 40's proof. It used to run inside `test` — which IS a
        // required check — and moving it to its own parallel lane silently un-gated it: a RED DDC
        // lane would not have blocked a merge. Gating is the difference between a proof and a
        // decoration, so the lane joins the required set here and on GitHub.
        ("interp-ddc", CI_YML, "  interp-ddc:"),
        ("workflows-parse", WORKFLOW_LINT_YML, "  workflows-parse:"),
    ];

    for (context, workflow, declaration) in required {
        assert!(
            workflow.contains(declaration),
            "PIN-5: required status check {context:?} is no longer declared as {declaration:?}; \
             update branch protection with any intentional rename"
        );
    }

    // The Lean lanes are pinned in `private_ci_pins.rs`: they run on a self-hosted host and
    // do not ship in the public tree yet (docs/specs/open-source-split.md, OSS-7).
    for (name, workflow) in [("CI", CI_YML), ("workflow lint", WORKFLOW_LINT_YML)] {
        let triggers = workflow
            .split_once("\non:")
            .map(|(_, rest)| rest.split("\njobs:").next().unwrap_or_default())
            .unwrap_or_default();
        assert!(
            !triggers.contains("paths:"),
            "PIN-5: a path-filtered {name} workflow cannot satisfy a required status check"
        );
        assert!(
            triggers.contains("  merge_group:\n    branches: [main]"),
            "PIN-5: {name} must run its required checks for the main merge queue"
        );
    }
}

/// PIN-3: achievement-critical evidence may grow but must never silently shrink.
#[test]
fn pin_semantic_evidence_manifests() {
    assert!(
        air_case_manifest::CORPUS_CASE_FLOOR > 0
            && !air_case_manifest::REQUIRED_EVIDENCE_TESTS.is_empty(),
        "PIN-3: AIR semantic evidence manifest is vacuous"
    );
    let air_source = include_str!("air_differential.rs");
    for name in air_case_manifest::REQUIRED_EVIDENCE_TESTS {
        assert!(
            air_source.contains(&format!("\nfn {name}(")),
            "PIN-3: required semantic AIR check {name:?} was removed"
        );
    }

    let mut seen_sources = HashSet::new();
    for block in preservation_manifest::CASES.trim().split("\n\n") {
        let (header, required_tests) = block
            .split_once('\n')
            .unwrap_or_else(|| panic!("PIN-3: malformed manifest block {block:?}"));
        let mut fields = header.split('|');
        let source_key = fields.next().unwrap_or_default();
        let suite_name = fields.next().unwrap_or_default();
        let case_floor: usize = fields
            .next()
            .unwrap_or_default()
            .parse()
            .unwrap_or_else(|_| panic!("PIN-3: malformed case floor in {header:?}"));
        assert!(
            !source_key.is_empty()
                && !suite_name.is_empty()
                && fields.next().is_none()
                && seen_sources.insert(source_key),
            "PIN-3: malformed or duplicate suite header {header:?}"
        );
        let source = preservation_manifest::SOURCES
            .iter()
            .find_map(|(key, source)| (*key == source_key).then_some(*source))
            .unwrap_or_else(|| panic!("PIN-3: unknown source key {source_key:?}"));

        let mut required = HashSet::new();
        for name in required_tests.split_ascii_whitespace() {
            assert!(
                required.insert(name),
                "PIN-3: {suite_name} repeats semantic label {name:?}"
            );
        }
        assert!(
            required.len() >= case_floor,
            "PIN-3: {suite_name} manifest fell to {} named cases (floor {case_floor})",
            required.len(),
        );

        let actual = test_source::test_fn_names_in(source);
        let mut missing: Vec<&str> = required
            .iter()
            .copied()
            .filter(|name| !actual.contains(*name))
            .collect();
        missing.sort_unstable();
        assert!(
            missing.is_empty(),
            "PIN-3: {suite_name} lost required semantic checks: {missing:?}"
        );
    }
    assert_eq!(
        seen_sources.len(),
        preservation_manifest::SOURCES.len(),
        "PIN-3: every protected source needs exactly one manifest block"
    );
}
