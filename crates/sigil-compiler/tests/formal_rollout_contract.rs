//! Anti-erosion checks for the long-lived CSIR v9 dual-gate rollout.
//!
//! These source contracts intentionally fail if a cleanup silently removes a
//! compatibility gate or turns the integration evidence template into a
//! retirement claim. Retirement is a separate schema-v10 product change.

const COMPILER: &str = include_str!("../src/compiler.rs");
const FORMAL: &str = include_str!("../src/formal.rs");
const CI: &str = include_str!("../../../.github/workflows/ci.yml");
const V8_EVIDENCE: &str = include_str!("../../../docs/release-evidence/csir-v8-dual-gate.toml");
const V9_EVIDENCE: &str = include_str!("../../../docs/release-evidence/csir-v9-dual-gate.toml");
const CONSTRUCTORS: &str = include_str!("../../../proofs/lean/csir-v8-constructor-manifest.tsv");

#[test]
fn v8_constructor_manifest_is_an_exact_numeric_inventory() {
    let rows = CONSTRUCTORS.lines().skip(1).collect::<Vec<_>>();
    let expected_records = [
        "semProgram",
        "semFunction",
        "semValue",
        "semBlock",
        "semInstruction",
        "semOperand",
        "semLabelContract",
        "semCapabilityType",
        "semPolicyClass",
        "semRefinementFact",
        "semRuntimeGuard",
    ];
    let expected_instructions = [
        "scalar",
        "aggregate",
        "project",
        "branch",
        "jump",
        "loop",
        "call",
        "closure",
        "actorBoundary",
        "stateRead",
        "stateWrite",
        "slotNew",
        "slotPut",
        "slotTake",
        "effect",
        "ffi",
        "allocation",
        "address",
        "capMint",
        "capRestrict",
        "capSplit",
        "capDraw",
        "capExercise",
        "release",
        "releaseCT",
        "ctEq",
        "ctSelect",
        "ctLt",
        "output",
        "trap",
        "halt",
        "range",
        "dispatch",
        "index",
        "divRem",
        "stringCompare",
        "abortiveEffect",
    ];
    let expected_policies = [
        ("branch", "T020"),
        ("loop", "T021"),
        ("range", "T022"),
        ("dispatch", "T023"),
        ("index", "T024"),
        ("address", "T025"),
        ("divRem", "T026"),
        ("ffi", "T027"),
        ("actorBoundary", "T028"),
        ("allocation", "T029"),
        ("ctSource", "T030"),
        ("release", "T031"),
        ("releaseCT", "T032"),
        ("stringCompare", "T033"),
        ("fixedCT", "-"),
        ("quantity", "T027"),
    ];

    let records = rows
        .iter()
        .filter_map(|row| row.strip_prefix("record\t"))
        .collect::<Vec<_>>();
    assert_eq!(records.len(), expected_records.len());
    for (offset, name) in expected_records.iter().enumerate() {
        assert_eq!(records[offset], format!("{}\t{name}\t-", offset + 33));
    }

    let instructions = rows
        .iter()
        .filter_map(|row| row.strip_prefix("instruction\t"))
        .collect::<Vec<_>>();
    assert_eq!(instructions.len(), expected_instructions.len());
    for (code, name) in expected_instructions.iter().enumerate() {
        assert_eq!(instructions[code], format!("{code}\t{name}\t-"));
    }

    let policies = rows
        .iter()
        .filter_map(|row| row.strip_prefix("policy\t"))
        .collect::<Vec<_>>();
    assert_eq!(policies.len(), expected_policies.len());
    for (code, (name, diagnostic)) in expected_policies.iter().enumerate() {
        assert_eq!(policies[code], format!("{code}\t{name}\t{diagnostic}"));
    }
    assert_eq!(
        rows.len(),
        records.len() + instructions.len() + policies.len()
    );
}

#[test]
fn v9_integration_cannot_silently_retire_the_dual_gates() {
    assert!(FORMAL.contains("pub const CSIR_MODEL_VERSION: u32 = 9;"));
    for gate in [
        "run_typed_security_passes(&typed)",
        "formal::verify_with_context(&typed_for_formal, &air, &authority_registry, context)",
        "capability::verify(&air, &authority_registry)",
        "ownership::verify(&air)",
        "formal_security_verdict.map_err(to_err)?",
    ] {
        assert!(
            COMPILER.contains(gate),
            "mandatory gate disappeared: {gate}"
        );
    }
    let formal_position = COMPILER
        .find("formal::verify_with_context(")
        .expect("formal verifier call must remain present");
    let capability_position = COMPILER
        .find("capability::verify(")
        .expect("capability compatibility gate must remain present");
    assert!(
        formal_position < capability_position,
        "the semantic verifier must run before retained compatibility gates"
    );

    for pin in [
        "model_version = 9",
        "certificate_schema = 9",
        "phase = \"dual-gate-integration\"",
        "retirement_eligible = false",
        "semantic_v9 = true",
        "historical_v8 = true",
        "obligations_v6 = true",
        "rust_taint = true",
        "rust_ownership = true",
        "z3_air_capability = true",
    ] {
        assert!(
            V9_EVIDENCE.contains(pin),
            "v9 rollout evidence pin disappeared: {pin}"
        );
    }

    for pin in [
        "model_version = 8",
        "certificate_schema = 9",
        "retirement_eligible = false",
        "semantic_v8 = true",
        "obligations_v6 = true",
        "rust_taint = true",
        "rust_ownership = true",
        "z3_air_capability = true",
        "constructor_manifest_complete = false",
    ] {
        assert!(
            V8_EVIDENCE.contains(pin),
            "historical v8 evidence pin disappeared: {pin}"
        );
    }
}

#[test]
fn required_ci_keeps_proof_scaling_and_solver_pressure() {
    for required in [
        "Formal verifier scaling canary",
        "selfhost_trio_completes_within_validation_budget",
        "CSIR v8 SSA and pc-join regressions",
        "taint_join_early_exit",
        "large_sibling_statements",
        "Lint (no default features)",
        "solver",
    ] {
        assert!(
            CI.contains(required),
            "required CI pressure disappeared: {required}"
        );
    }
}
