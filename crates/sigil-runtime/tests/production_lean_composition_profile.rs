//! Drift pins for the production Lean composition profile.
//!
//! The profile is the reviewable boundary between shipped Rust checkers, encoded
//! CSIR, linked Lean theorems, and executable canaries. It is intentionally a
//! source contract: if a theorem, canary, or gate token moves, the public claim
//! must move in the same patch.

use std::collections::BTreeSet;

#[path = "support/repo_test_inventory.rs"]
mod repo_test_inventory;
#[path = "support/test_source.rs"]
mod test_source;
use repo_test_inventory::all_test_fn_names;

const PROFILE: &str = include_str!("../../../docs/specs/production-lean-composition.md");
const ROWS: &str = include_str!("../../../docs/specs/production-lean-composition.tsv");
const MATRIX: &str = include_str!("../../../docs/SOUNDNESS_MATRIX.md");
const RISKS: &str = include_str!("../../../docs/RESIDUAL_RISKS.md");
const CLAIMS: &str = include_str!("../../../docs/CLAIMS.md");
const SECURITY_MODEL: &str = include_str!("../../../docs/SECURITY_MODEL.md");
const RELEASE_README: &str = include_str!("../../../docs/release-evidence/README.md");
const V9_EVIDENCE: &str = include_str!("../../../docs/release-evidence/csir-v9-dual-gate.toml");
const VALIDATE_EVIDENCE: &str = include_str!("../../../tools/validate_release_evidence.py");
const AXIOM_TARGETS: &str = include_str!("../../../proofs/lean/axiom-targets.txt");
const COMPILER: &str = include_str!("../../sigil-compiler/src/compiler.rs");
const FORMAL: &str = include_str!("../../sigil-compiler/src/formal.rs");
const V9_OCCURRENCE_KERNEL: &str =
    include_str!("../../../proofs/lean/LambdaSigil/V9OccurrenceKernel.lean");
const CI: &str = include_str!("../../../.github/workflows/ci.yml");

const PIN_PLC_PROFILE_ROWS: usize = 10;
const PIN_PLC_THEOREM_REFS: usize = 39;
const PIN_PLC_POSITIVE_CANARIES: usize = 25;
const PIN_PLC_NEGATIVE_CANARIES: usize = 39;
const PIN_PLC_GATE_TOKENS: usize = 30;

#[derive(Clone, Copy)]
struct ProfileRow<'a> {
    id: &'a str,
    production_abstraction: &'a str,
    lean_theorems: &'a str,
    positive_canaries: &'a str,
    negative_canaries: &'a str,
    gate_tokens: &'a str,
}

fn split_refs(cell: &str) -> Vec<&str> {
    cell.split(';')
        .map(str::trim)
        .filter(|entry| !entry.is_empty())
        .collect()
}

fn profile_rows() -> Vec<ProfileRow<'static>> {
    let mut lines = ROWS.lines();
    assert_eq!(
        lines.next(),
        Some(
            "obligation\tproduction_abstraction\tlean_theorems\tpositive_canaries\tnegative_canaries\tgate_tokens"
        ),
        "production Lean composition manifest header changed"
    );
    lines
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let cells = line.split('\t').collect::<Vec<_>>();
            assert_eq!(cells.len(), 6, "malformed PLC row: {line}");
            ProfileRow {
                id: cells[0],
                production_abstraction: cells[1],
                lean_theorems: cells[2],
                positive_canaries: cells[3],
                negative_canaries: cells[4],
                gate_tokens: cells[5],
            }
        })
        .collect()
}

fn residual_risk_row(id: &str) -> Vec<&'static str> {
    RISKS
        .lines()
        .filter(|line| line.starts_with("| SR-"))
        .map(|line| line.split('|').map(str::trim).collect::<Vec<_>>())
        .find(|cells| cells.get(1).copied() == Some(id))
        .unwrap_or_else(|| panic!("missing residual-risk row {id}"))
}

fn soundness_row(id: &str) -> &str {
    let marker = format!("### {id} ");
    let (_, tail) = MATRIX
        .split_once(&marker)
        .unwrap_or_else(|| panic!("missing soundness row {id}"));
    tail.split("\n### ").next().expect("soundness row body")
}

#[test]
fn production_lean_composition_profile_is_complete_and_drift_pinned() {
    let rows = profile_rows();
    assert_eq!(rows.len(), PIN_PLC_PROFILE_ROWS);
    let ids = rows.iter().map(|row| row.id).collect::<Vec<_>>();
    assert_eq!(
        ids.as_slice(),
        &[
            "PLC-PROJECTION-CHOKEPOINT",
            "PLC-AIR-TRANSFERS",
            "PLC-V8-SEMANTIC-TAINT",
            "PLC-V9-OCCURRENCE-PUBLIC",
            "PLC-SECRETCT-RAW-COMPOSITION",
            "PLC-CAPABILITY-AUTHORITY",
            "PLC-PATH-AFFINE",
            "PLC-QUANTITY-DIFFERENCE",
            "PLC-CSIR-ENCODING",
            "PLC-DUAL-GATE-RETIREMENT-BOUNDARY",
        ],
        "PLC obligation inventory changed without updating the profile gate"
    );
    assert_eq!(
        ids.iter().collect::<BTreeSet<_>>().len(),
        ids.len(),
        "PLC obligation ids must be unique"
    );

    for pin in [
        "PIN_PLC_PROFILE_ROWS = 10",
        "PIN_PLC_THEOREM_REFS = 39",
        "PIN_PLC_POSITIVE_CANARIES = 25",
        "PIN_PLC_NEGATIVE_CANARIES = 39",
        "PIN_PLC_GATE_TOKENS = 30",
    ] {
        assert!(PROFILE.contains(pin), "PLC profile lost pin {pin}");
    }

    let theorem_refs: Vec<&str> = rows
        .iter()
        .flat_map(|row| split_refs(row.lean_theorems))
        .collect();
    let positive_canaries: Vec<&str> = rows
        .iter()
        .flat_map(|row| split_refs(row.positive_canaries))
        .collect();
    let negative_canaries: Vec<&str> = rows
        .iter()
        .flat_map(|row| split_refs(row.negative_canaries))
        .collect();
    let gate_tokens: Vec<&str> = rows
        .iter()
        .flat_map(|row| split_refs(row.gate_tokens))
        .collect();
    assert_eq!(theorem_refs.len(), PIN_PLC_THEOREM_REFS);
    assert_eq!(positive_canaries.len(), PIN_PLC_POSITIVE_CANARIES);
    assert_eq!(negative_canaries.len(), PIN_PLC_NEGATIVE_CANARIES);
    assert_eq!(gate_tokens.len(), PIN_PLC_GATE_TOKENS);

    for row in &rows {
        assert!(
            row.production_abstraction.len() >= 80,
            "{} needs a concrete production abstraction, not a label",
            row.id
        );
        assert!(
            !split_refs(row.lean_theorems).is_empty()
                && !split_refs(row.positive_canaries).is_empty()
                && !split_refs(row.negative_canaries).is_empty()
                && !split_refs(row.gate_tokens).is_empty(),
            "{} must name theorem, canary, and gate evidence",
            row.id
        );
    }

    let axiom_targets = AXIOM_TARGETS.lines().collect::<BTreeSet<_>>();
    let missing_theorems: Vec<&str> = theorem_refs
        .iter()
        .copied()
        .filter(|name| !axiom_targets.contains(name))
        .collect();
    assert!(
        missing_theorems.is_empty(),
        "PLC profile cites Lean theorems outside the axiom-target census: {missing_theorems:?}"
    );

    let tests = all_test_fn_names();
    let missing_canaries: Vec<&str> = positive_canaries
        .iter()
        .chain(negative_canaries.iter())
        .copied()
        .filter(|name| !tests.contains(*name))
        .collect();
    assert!(
        missing_canaries.is_empty(),
        "PLC profile cites canaries that do not exist: {missing_canaries:?}"
    );

    let gate_sources = [
        COMPILER,
        FORMAL,
        V9_EVIDENCE,
        VALIDATE_EVIDENCE,
        V9_OCCURRENCE_KERNEL,
        CI,
    ]
    .join("\n");
    let missing_tokens: Vec<&str> = gate_tokens
        .iter()
        .copied()
        .filter(|token| !gate_sources.contains(token))
        .collect();
    assert!(
        missing_tokens.is_empty(),
        "PLC profile cites production gate tokens that are absent: {missing_tokens:?}"
    );
}

#[test]
fn production_lean_composition_profile_keeps_public_claims_bounded() {
    for required in [
        "PLC-2026-09-07",
        "production-lean-composition.tsv",
        "Rust source-to-CSIR projection",
        "old Rust/Z3 gates remain mandatory",
        "SR-017",
    ] {
        assert!(
            PROFILE.contains(required),
            "PLC profile lost boundary text {required:?}"
        );
    }

    let formal = soundness_row("SND-FORMAL-001");
    for required in [
        "PLC-2026-09-07",
        "- **Status:** `enforced`",
        "None for `PLC-2026-09-07`",
        "SR-017 remains open",
        "@test:production_lean_composition_profile_is_complete_and_drift_pinned",
        "@test:production_lean_composition_profile_keeps_public_claims_bounded",
    ] {
        assert!(
            formal.contains(required),
            "SND-FORMAL-001 lost PLC boundary marker {required:?}"
        );
    }
    assert!(
        !formal.contains("- **Residual risk:** SR-013"),
        "SND-FORMAL-001 still points at the closed checker-composition risk"
    );

    let sr013 = residual_risk_row("SR-013");
    assert_eq!(
        sr013[3], "Closed",
        "SR-013 should be closed by PLC-2026-09-07"
    );
    assert!(
        sr013[4].contains("PLC-2026-09-07")
            && sr013[5]
                .contains("production_lean_composition_profile_is_complete_and_drift_pinned"),
        "SR-013 closure must cite the machine-checked composition profile"
    );
    assert_eq!(
        sr013[8], "—",
        "Closed SR-013 must not retain an active tracking issue"
    );

    let sr017 = residual_risk_row("SR-017");
    assert_eq!(
        sr017[3], "Accepted",
        "SR-017 remains the explicit adequacy boundary"
    );
    for required in [
        "Rust source-to-CSIR projection",
        "Lean native generation/runtime",
        "Wasm",
    ] {
        assert!(
            sr017[4].contains(required),
            "SR-017 lost assumption {required:?}"
        );
    }

    for required in [
        "PLC-2026-09-07",
        "source/AIR/Wasm adequacy remains SR-017",
        "@test:production_lean_composition_profile_is_complete_and_drift_pinned",
    ] {
        assert!(
            CLAIMS.contains(required),
            "claims ledger lost PLC marker {required:?}"
        );
    }
    assert!(
        !CLAIMS.contains("remaining operational and rollout conditions stay in SR-013"),
        "claims ledger still leaves checker-composition closure in SR-013"
    );

    for required in [
        "production Lean composition profile",
        "PLC-2026-09-07",
        "SR-017",
    ] {
        assert!(
            SECURITY_MODEL.contains(required),
            "security model lost PLC boundary text {required:?}"
        );
    }

    assert!(
        V9_EVIDENCE.contains("unresolved_risks = [\"SR-017\"]"),
        "v9 evidence should leave only SR-017 unresolved"
    );
    assert!(
        !V9_EVIDENCE.contains("unresolved_risks = [\"SR-013\", \"SR-017\"]"),
        "v9 evidence still treats SR-013 as unresolved"
    );
    assert!(
        VALIDATE_EVIDENCE.contains("record[\"unresolved_risks\"] == [\"SR-017\"]"),
        "release-evidence validator did not learn the narrowed unresolved-risk list"
    );
    assert!(
        RELEASE_README.contains("exact unresolved-risk list containing SR-017"),
        "release-evidence README must describe the narrowed unresolved-risk list"
    );
}
