//! The production Rust codec, Lean evaluation, and linked native decoder must
//! agree on the same committed canonical and hostile declarations. Empty output
//! or a planted native-verdict mutation cannot count as passing this gate.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;

use sigil_abi::host_contract::HostContractProfile;
use sigil_formal_bridge::{validate_host_profile, verify};

const FIXTURE_COUNT: usize = 45;
const ACCEPT_COUNT: usize = 7;

fn fixtures() -> BTreeMap<String, Vec<u8>> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../proofs/lean");
    let paths = std::fs::read_dir(root.join("fixtures/host-profiles"))
        .expect("shared host-profile fixtures must exist");
    let mut fixtures = BTreeMap::new();
    for entry in paths {
        let path = entry.expect("fixture entry must be readable").path();
        assert_eq!(
            path.extension().and_then(|value| value.to_str()),
            Some("hex")
        );
        let name = path
            .file_name()
            .expect("fixture file name")
            .to_str()
            .expect("ASCII fixture name");
        assert!(name.starts_with("accept-") || name.starts_with("reject-"));
        let text = std::fs::read_to_string(&path).expect("fixture must be readable hex");
        let hex = text.split_ascii_whitespace().collect::<String>();
        assert_eq!(hex.len() % 2, 0);
        let bytes = hex
            .as_bytes()
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| {
                let pair = std::str::from_utf8(pair).expect("ASCII hex pair");
                u8::from_str_radix(pair, 16).expect("valid fixture hex pair")
            })
            .collect::<Vec<_>>();
        assert!(fixtures.insert(name.to_owned(), bytes).is_none());
    }
    assert_eq!(fixtures.len(), FIXTURE_COUNT, "fixture inventory drift");
    assert_eq!(
        fixtures
            .keys()
            .filter(|name| name.starts_with("accept-"))
            .count(),
        ACCEPT_COUNT
    );
    fixtures
}

fn verdicts_agree(expected: &BTreeMap<String, u64>, actual: &BTreeMap<String, u64>) -> bool {
    !expected.is_empty() && expected == actual
}

#[test]
fn every_project_import_is_pinned_to_this_native_build() {
    let parity = PathBuf::from(env!("SIGIL_HOST_PROFILE_PARITY_SETUP"));
    let directory = parity.parent().expect("build-owned setup directory");
    for (setup_name, module_names) in [
        ("CombinedKernel", vec![]),
        ("SemanticKernel", vec!["CombinedKernel"]),
        ("HostProfileKernel", vec!["CombinedKernel"]),
        (
            "HostProfileParity",
            vec!["CombinedKernel", "HostProfileKernel"],
        ),
    ] {
        let bytes = std::fs::read(directory.join(format!("{setup_name}.setup.json")))
            .expect("native build must generate every explicit import map");
        let setup: serde_json::Value = serde_json::from_slice(&bytes).expect("module setup JSON");
        assert_eq!(setup["name"], format!("LambdaSigil.{setup_name}"));
        let mut expected = serde_json::Map::new();
        for module in module_names {
            let artifact = directory.join(format!("{module}.olean"));
            assert!(
                artifact.is_file(),
                "missing freshly built import: {artifact:?}"
            );
            expected.insert(
                format!("LambdaSigil.{module}"),
                serde_json::json!([artifact]),
            );
        }
        assert_eq!(
            setup["importArts"],
            serde_json::Value::Object(expected),
            "project imports must never fall back to a stale .lake artifact"
        );
    }
}

#[test]
fn rust_lean_evaluation_and_linked_decoder_agree_on_every_fixture() {
    let fixtures = fixtures();
    let mut native = BTreeMap::new();
    let mut expected = BTreeMap::new();
    for (name, bytes) in &fixtures {
        let accepted = name.starts_with("accept-");
        assert_eq!(
            HostContractProfile::decode(bytes).is_ok(),
            accepted,
            "Rust: {name}"
        );
        expected.insert(name.clone(), u64::from(!accepted));
        native.insert(
            name.clone(),
            validate_host_profile(bytes).expect("linked Lean initialized"),
        );
        // A valid declaration must never be mistaken for a valid security program.
        assert_ne!(
            verify(bytes),
            Ok(0),
            "host profile authorized as CSIR: {name}"
        );
    }
    assert!(
        verdicts_agree(&expected, &native),
        "native decoder disagrees: {native:?}"
    );

    let lean_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../proofs/lean");
    let paths = fixtures
        .keys()
        .map(|name| format!("fixtures/host-profiles/{name}"));
    let output = Command::new("lake")
        .current_dir(&lean_root)
        .args([
            "env",
            "lean",
            "--setup",
            env!("SIGIL_HOST_PROFILE_PARITY_SETUP"),
            "--run",
            "LambdaSigil/HostProfileParity.lean",
        ])
        .args(paths)
        .output()
        .expect("pinned Lean evaluation must execute");
    assert!(
        output.status.success(),
        "Lean evaluation failed: {}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("Lean parity output is UTF-8");
    let mut evaluated = BTreeMap::new();
    for line in stdout.lines() {
        let fields = line.split('|').collect::<Vec<_>>();
        assert_eq!(fields.len(), 3, "unexpected Lean output: {line}");
        assert_eq!(fields[0], "HOSTPROFILE");
        let name = fields[1]
            .strip_prefix("fixtures/host-profiles/")
            .expect("exact fixture path");
        let verdict = fields[2].parse::<u64>().expect("numeric Lean verdict");
        assert!(
            evaluated.insert(name.to_owned(), verdict).is_none(),
            "duplicate report"
        );
    }
    assert!(
        verdicts_agree(&expected, &evaluated),
        "Lean evaluation disagrees: {evaluated:?}"
    );
}

#[test]
fn verdict_parity_gate_rejects_planted_corruption_and_missing_reports() {
    let expected = BTreeMap::from([
        ("accept-empty.hex".into(), 0),
        ("reject-version.hex".into(), 1),
    ]);
    assert!(verdicts_agree(&expected, &expected));
    let mut corrupted = expected.clone();
    corrupted.insert("reject-version.hex".into(), 0);
    assert!(!verdicts_agree(&expected, &corrupted));
    corrupted.remove("reject-version.hex");
    assert!(!verdicts_agree(&expected, &corrupted));
    assert!(!verdicts_agree(&BTreeMap::new(), &BTreeMap::new()));
}

#[test]
fn profile_and_csir_shims_reject_over_limit_before_copying() {
    let oversized = vec![0; 64 * 1024 * 1024 + 1];
    assert_eq!(validate_host_profile(&oversized), Ok(1));
    assert_eq!(verify(&oversized), Ok(1));
}
