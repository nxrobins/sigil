//! Declaration-only native parity. The shared compiler-generated fixtures are
//! checked separately by the compiler's Rust codec tests; this crate deliberately
//! does not depend on the compiler. No successful result here authorizes CSIR v9.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use sigil_formal_bridge::{validate_host_profile, validate_v9_declarations, verify};

const FIXTURE_COUNT: usize = 37;
const ACCEPT_COUNT: usize = 7;
const HEADER_BYTES: usize = 12;
const RECORD_BYTES: usize = 32;

fn lean_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs/lean")
}

fn fixtures() -> BTreeMap<String, Vec<u8>> {
    let mut fixtures = BTreeMap::new();
    for entry in std::fs::read_dir(lean_root().join("fixtures/csir-v9"))
        .expect("shared v9 declaration fixtures exist")
    {
        let path = entry.expect("fixture entry is readable").path();
        assert_eq!(
            path.extension().and_then(|extension| extension.to_str()),
            Some("hex")
        );
        let name = path
            .file_name()
            .expect("fixture filename")
            .to_str()
            .expect("ASCII filename");
        assert!(name.starts_with("accept-") || name.starts_with("reject-"));
        let text = std::fs::read_to_string(&path).expect("fixture hex is readable");
        let hex = text.split_ascii_whitespace().collect::<String>();
        assert_eq!(hex.len() % 2, 0, "whole hex bytes: {name}");
        let bytes = hex
            .as_bytes()
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| {
                u8::from_str_radix(std::str::from_utf8(pair).expect("ASCII hex pair"), 16)
                    .expect("valid fixture hex")
            })
            .collect();
        assert!(
            fixtures.insert(name.to_owned(), bytes).is_none(),
            "duplicate fixture name"
        );
    }
    assert_eq!(fixtures.len(), FIXTURE_COUNT, "v9 fixture inventory drift");
    assert_eq!(
        fixtures
            .keys()
            .filter(|name| name.starts_with("accept-"))
            .count(),
        ACCEPT_COUNT
    );
    fixtures
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Report {
    verdict: u64,
    version: u32,
    base_records: usize,
    profile_len: usize,
    ffi_count: usize,
    actor_count: usize,
    root_count: usize,
    profile_hex: String,
}

fn word(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(
        bytes[offset..offset + 4]
            .try_into()
            .expect("fixed-width word"),
    )
}

fn encoded_hex(bytes: &[u8]) -> String {
    use std::fmt::Write;

    let mut hex = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(hex, "{byte:02x}").expect("writing a String succeeds");
    }
    hex
}

fn rejected_report() -> Report {
    Report {
        verdict: 1,
        version: 0,
        base_records: 0,
        profile_len: 0,
        ffi_count: 0,
        actor_count: 0,
        root_count: 0,
        profile_hex: "-".into(),
    }
}

// Read retained metadata from known-good answer-key bytes, not from either
// decoder's report. This is not another security or general declaration decoder.
fn accepted_report(bytes: &[u8]) -> Report {
    assert_eq!(&bytes[..4], b"CSIR");
    assert_eq!(word(bytes, 4), 9);
    let payload = &bytes[HEADER_BYTES..];
    assert_eq!(payload.len() % RECORD_BYTES, 0);
    let records = payload.as_chunks::<RECORD_BYTES>().0;
    assert_eq!(word(bytes, 8) as usize, records.len());
    let base_records = records
        .iter()
        .position(|record| record[0] == 44)
        .expect("accepted fixture contains a v9 manifest");
    let manifest = &records[base_records];
    assert_eq!(word(manifest, 4) as usize, base_records);
    let profile_len = word(manifest, 8) as usize;
    let mut profile = Vec::with_capacity(profile_len.div_ceil(20) * 20);
    for record in records
        .iter()
        .skip(base_records + 1)
        .take(profile_len.div_ceil(20))
    {
        assert_eq!(&record[..4], &[45, 0, 0, 0]);
        profile.extend_from_slice(&record[4..24]);
    }
    assert!(profile.len() >= profile_len);
    assert!(profile[profile_len..].iter().all(|byte| *byte == 0));
    profile.truncate(profile_len);
    Report {
        verdict: 0,
        version: 9,
        base_records,
        profile_len,
        ffi_count: word(manifest, 12) as usize,
        actor_count: word(manifest, 16) as usize,
        root_count: word(manifest, 20) as usize,
        profile_hex: if profile.is_empty() {
            "-".into()
        } else {
            encoded_hex(&profile)
        },
    }
}

fn parse_reports(stdout: &str) -> Option<BTreeMap<String, Report>> {
    let mut reports = BTreeMap::new();
    for line in stdout.lines() {
        let fields = line.split('|').collect::<Vec<_>>();
        if fields.len() != 10 || fields[0] != "CSIRV9" {
            return None;
        }
        let name = fields[1].strip_prefix("fixtures/csir-v9/")?;
        let report = Report {
            verdict: fields[2].parse().ok()?,
            version: fields[3].parse().ok()?,
            base_records: fields[4].parse().ok()?,
            profile_len: fields[5].parse().ok()?,
            ffi_count: fields[6].parse().ok()?,
            actor_count: fields[7].parse().ok()?,
            root_count: fields[8].parse().ok()?,
            profile_hex: fields[9].into(),
        };
        if reports.insert(name.to_owned(), report).is_some() {
            return None;
        }
    }
    Some(reports)
}

fn reports_agree(expected: &BTreeMap<String, Report>, actual: &BTreeMap<String, Report>) -> bool {
    !expected.is_empty() && expected == actual
}

fn verdicts_agree(expected: &BTreeMap<String, u64>, actual: &BTreeMap<String, u64>) -> bool {
    !expected.is_empty() && expected == actual
}

#[test]
fn every_v9_project_import_is_pinned_to_this_native_build() {
    let parity = PathBuf::from(env!("SIGIL_CSIR_V9_PARITY_SETUP"));
    let directory = parity.parent().expect("build-owned setup directory");
    for (setup_name, module_names) in [
        ("CombinedKernel", vec![]),
        ("HostProfileKernel", vec!["CombinedKernel"]),
        (
            "OccurrenceWire",
            vec!["CombinedKernel", "HostProfileKernel"],
        ),
        (
            "OccurrenceWireParity",
            vec!["CombinedKernel", "HostProfileKernel", "OccurrenceWire"],
        ),
    ] {
        let bytes = std::fs::read(directory.join(format!("{setup_name}.setup.json")))
            .expect("native build generates explicit import maps");
        let setup: serde_json::Value = serde_json::from_slice(&bytes).expect("module setup JSON");
        assert_eq!(setup["name"], format!("LambdaSigil.{setup_name}"));
        let mut expected = serde_json::Map::new();
        for module in module_names {
            let artifact = directory.join(format!("{module}.olean"));
            assert!(artifact.is_file(), "missing fresh artifact: {artifact:?}");
            assert!(
                directory.join(format!("{module}.c")).is_file(),
                "missing fresh C module"
            );
            expected.insert(
                format!("LambdaSigil.{module}"),
                serde_json::json!([artifact]),
            );
        }
        assert_eq!(
            setup["importArts"],
            serde_json::Value::Object(expected),
            "v9 imports cannot fall back to cached .lake artifacts"
        );
    }
}

#[test]
fn lean_evaluation_and_linked_v9_decoder_agree_without_authorizing_programs() {
    let fixtures = fixtures();
    let mut expected = BTreeMap::new();
    let mut native = BTreeMap::new();
    for (name, bytes) in &fixtures {
        let report = if name.starts_with("accept-") {
            accepted_report(bytes)
        } else {
            rejected_report()
        };
        native.insert(
            name.clone(),
            validate_v9_declarations(bytes).expect("linked Lean initialized"),
        );
        expected.insert(name.clone(), report);
        assert_ne!(
            verify(bytes),
            Ok(0),
            "v9 declarations authorized by production v8: {name}"
        );
        assert_ne!(
            validate_host_profile(bytes),
            Ok(0),
            "v9 declarations mistaken for host profile: {name}"
        );
    }
    let expected_verdicts = expected
        .iter()
        .map(|(name, report)| (name.clone(), report.verdict))
        .collect();
    assert!(
        verdicts_agree(&expected_verdicts, &native),
        "native verdict disagreement: {native:?}"
    );

    let output = Command::new("lake")
        .current_dir(lean_root())
        .args([
            "env",
            "lean",
            "--setup",
            env!("SIGIL_CSIR_V9_PARITY_SETUP"),
            "--run",
            "LambdaSigil/OccurrenceWireParity.lean",
        ])
        .args(
            fixtures
                .keys()
                .map(|name| format!("fixtures/csir-v9/{name}")),
        )
        .output()
        .expect("pinned Lean evaluation executes");
    assert!(
        output.status.success(),
        "Lean evaluation failed: {}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("Lean output is UTF-8");
    let evaluated = parse_reports(&stdout).expect("exact, nonduplicate v9 report records");
    assert!(
        reports_agree(&expected, &evaluated),
        "Lean retained declaration mismatch: {evaluated:?}"
    );
}

#[test]
fn v9_declaration_initialization_is_repeatable_and_truncations_fail_closed() {
    for (name, bytes) in fixtures()
        .into_iter()
        .filter(|(name, _)| name.starts_with("accept-"))
    {
        for _ in 0..4 {
            assert_eq!(
                validate_v9_declarations(&bytes),
                Ok(0),
                "repeated call: {name}"
            );
        }
        for length in 0..bytes.len() {
            assert_eq!(
                validate_v9_declarations(&bytes[..length]),
                Ok(1),
                "truncation {length}: {name}"
            );
        }
        let mut trailing = bytes;
        trailing.push(0);
        assert_eq!(
            validate_v9_declarations(&trailing),
            Ok(1),
            "trailing byte: {name}"
        );
    }
    assert_eq!(validate_v9_declarations(b"not-csir"), Ok(1));
    let excessive_count = b"CSIR\x09\x00\x00\x00\x41\x42\x0f\x00";
    assert_eq!(word(excessive_count, 8), 1_000_001);
    assert_eq!(validate_v9_declarations(excessive_count), Ok(1));
}

#[test]
fn v9_parity_gate_rejects_planted_verdict_loss_and_report_corruption() {
    let expected = BTreeMap::from([
        ("accept-empty-framing.hex".into(), 0),
        ("reject-wrong-version.hex".into(), 1),
    ]);
    assert!(verdicts_agree(&expected, &expected));
    let mut corrupted = expected.clone();
    corrupted.insert("reject-wrong-version.hex".into(), 0);
    assert!(!verdicts_agree(&expected, &corrupted));
    corrupted.remove("reject-wrong-version.hex");
    assert!(!verdicts_agree(&expected, &corrupted));
    assert!(!verdicts_agree(&BTreeMap::new(), &BTreeMap::new()));

    let line = "CSIRV9|fixtures/csir-v9/reject-wrong-version.hex|1|0|0|0|0|0|0|-\n";
    let reports = parse_reports(line).expect("canonical planted report");
    assert!(reports_agree(&reports, &reports));
    assert!(!reports_agree(
        &reports,
        &parse_reports("").expect("empty parsed map")
    ));
    assert!(!reports_agree(&BTreeMap::new(), &BTreeMap::new()));
    assert!(parse_reports(&format!("{line}{line}")).is_none());
    assert!(parse_reports("CSIRV9|fixtures/csir-v9/x|1\n").is_none());
    for replacement in ["|0|0|0|0|0|0|0|-", "|1|9|0|0|0|0|0|-", "|1|0|0|1|0|0|0|00"] {
        let mutant = format!("CSIRV9|fixtures/csir-v9/reject-wrong-version.hex{replacement}\n");
        assert!(!reports_agree(
            &reports,
            &parse_reports(&mutant).expect("well-shaped mutant")
        ));
    }

    let accepted_name = "accept-declared-ffi.hex";
    let fixture_map = fixtures();
    let accepted = accepted_report(&fixture_map[accepted_name]);
    let expected = BTreeMap::from([(accepted_name.into(), accepted.clone())]);
    let mutations: [fn(&mut Report); 8] = [
        |report| report.verdict = 1,
        |report| report.version += 1,
        |report| report.base_records += 1,
        |report| report.profile_len += 1,
        |report| report.ffi_count += 1,
        |report| report.actor_count += 1,
        |report| report.root_count += 1,
        |report| report.profile_hex.push('0'),
    ];
    for mutate in mutations {
        let mut changed = accepted.clone();
        mutate(&mut changed);
        let actual = BTreeMap::from([(accepted_name.into(), changed)]);
        assert!(
            !reports_agree(&expected, &actual),
            "retained-field mutant escaped"
        );
    }
}

#[test]
fn v9_shim_rejects_oversized_input_before_copying() {
    let oversized = vec![0; 64 * 1024 * 1024 + 1];
    assert_eq!(validate_v9_declarations(&oversized), Ok(1));
}
