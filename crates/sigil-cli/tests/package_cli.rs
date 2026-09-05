use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

struct TestDir {
    path: PathBuf,
}

impl TestDir {
    fn new() -> Self {
        loop {
            let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "sigil-package-cli-test-{}-{sequence}",
                std::process::id()
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => return Self { path },
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!(
                    "failed to create test directory {}: {error}",
                    path.display()
                ),
            }
        }
    }

    fn path(&self) -> &std::path::Path {
        &self.path
    }
}

impl Drop for TestDir {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.path).unwrap_or_else(|error| {
            panic!(
                "failed to remove test directory {}: {error}",
                self.path.display()
            )
        });
    }
}

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../sigil-compiler/tests/fixtures/packages/neutral-boundaries")
}

fn solver_negative_fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../sigil-compiler/tests/fixtures/packages/solver-refinement-negative")
}

fn write_fresh_package_certificate(path: &std::path::Path) {
    let package = sigil_compiler::package::compile_local_package_structural(
        &fixture(),
        sigil_compiler::CompileOptions::default(),
    )
    .expect("neutral package fixture should compile");
    std::fs::write(
        path,
        serde_json::to_vec_pretty(&package.certificate())
            .expect("package certificate should serialize"),
    )
    .expect("package certificate should be writable");
}

#[cfg(feature = "solver")]
#[test]
fn explicit_package_check_and_verification_round_trip() {
    let temp = TestDir::new();
    let cert = temp.path().join("package-cert.json");
    let wasm = temp.path().join("package.wasm");
    let check = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["check", "--package"])
        .arg(fixture())
        .args(["--cert"])
        .arg(&cert)
        .args(["--emit-wasm"])
        .arg(&wasm)
        .arg("--json")
        .output()
        .unwrap();
    assert!(
        check.status.success(),
        "stderr={} stdout={}",
        String::from_utf8_lossy(&check.stderr),
        String::from_utf8_lossy(&check.stdout)
    );
    let envelope: serde_json::Value = serde_json::from_slice(&check.stdout).unwrap();
    assert_eq!(envelope["status"], "ok");
    assert_eq!(envelope["data"]["root_package"], "test/app");
    assert!(cert.is_file());
    assert!(wasm.is_file());

    let verify = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["verify-cert", "--cert"])
        .arg(&cert)
        .args(["--package"])
        .arg(fixture())
        .arg("--json")
        .output()
        .unwrap();
    assert!(
        verify.status.success(),
        "stderr={} stdout={}",
        String::from_utf8_lossy(&verify.stderr),
        String::from_utf8_lossy(&verify.stdout)
    );
    let envelope: serde_json::Value = serde_json::from_slice(&verify.stdout).unwrap();
    assert_eq!(envelope["data"]["verified"], true);
}

#[test]
fn package_mode_is_explicit_and_mutually_exclusive_with_files() {
    let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["check", "--package"])
        .arg(fixture())
        .arg("some-file.sigil")
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("mutually exclusive"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cfg(unix)]
#[test]
fn package_certificate_missing_graph_field_fails_closed() {
    let temp = TestDir::new();
    let cert = temp.path().join("package-cert.json");
    write_fresh_package_certificate(&cert);

    let mut value: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&cert).unwrap()).unwrap();
    value.as_object_mut().unwrap().remove("package_graph_hash");
    std::fs::write(&cert, serde_json::to_vec_pretty(&value).unwrap()).unwrap();
    let verify = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["verify-cert", "--cert"])
        .arg(&cert)
        .args(["--package"])
        .arg(fixture())
        .output()
        .unwrap();
    assert!(!verify.status.success());
    assert!(
        String::from_utf8_lossy(&verify.stderr).contains("R811"),
        "{}",
        String::from_utf8_lossy(&verify.stderr)
    );
}

#[cfg(unix)]
#[test]
fn package_certificate_nested_unknown_fields_fail_closed() {
    let temp = TestDir::new();
    let cert = temp.path().join("package-cert.json");
    write_fresh_package_certificate(&cert);
    let baseline: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&cert).unwrap()).unwrap();

    for pointer in [
        "/base_certificate",
        "/base_certificate/source_fingerprint",
        "/base_certificate/capability",
        "/base_certificate/ownership",
        "/base_certificate/formal",
    ] {
        let mut value = baseline.clone();
        value
            .pointer_mut(pointer)
            .and_then(serde_json::Value::as_object_mut)
            .expect("test pointer must address a certificate object")
            .insert(
                "unexpected_nested".to_owned(),
                serde_json::Value::Bool(true),
            );
        std::fs::write(&cert, serde_json::to_vec_pretty(&value).unwrap()).unwrap();

        let verify = Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args(["verify-cert", "--cert"])
            .arg(&cert)
            .args(["--package"])
            .arg(fixture())
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&verify.stderr);
        assert!(!verify.status.success(), "{pointer} unexpectedly verified");
        assert!(stderr.contains("R811"), "{pointer}: {stderr}");
        assert!(
            stderr.contains("unexpected_nested")
                && (stderr.contains("unknown field")
                    || stderr.contains("fields must match exactly")),
            "{pointer}: {stderr}"
        );
    }
}

#[cfg(unix)]
#[test]
fn package_certificate_duplicate_keys_fail_closed_at_every_depth() {
    let temp = TestDir::new();
    let cert = temp.path().join("package-cert.json");
    write_fresh_package_certificate(&cert);
    let baseline = std::fs::read_to_string(&cert).unwrap();

    for (label, duplicated) in [
        (
            "top-level",
            baseline.replacen(
                "\"schema_version\": \"1\",",
                "\"schema_version\": \"1\",\n  \"schema_version\": \"1\",",
                1,
            ),
        ),
        (
            "nested",
            baseline.replacen(
                "\"algorithm\": \"sha2-256\",",
                "\"algorithm\": \"sha2-256\",\n      \"algorithm\": \"sha2-256\",",
                1,
            ),
        ),
    ] {
        assert_ne!(duplicated, baseline, "{label} replacement must fire");
        std::fs::write(&cert, duplicated).unwrap();
        let verify = Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args(["verify-cert", "--cert"])
            .arg(&cert)
            .args(["--package"])
            .arg(fixture())
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&verify.stderr);
        assert!(
            !verify.status.success(),
            "{label} duplicate unexpectedly verified"
        );
        assert!(stderr.contains("R811"), "{label}: {stderr}");
        assert!(stderr.contains("duplicate JSON key"), "{label}: {stderr}");
    }
}

#[test]
fn package_certificate_read_is_bounded() {
    let temp = TestDir::new();
    let cert = temp.path().join("oversized-package-cert.json");
    std::fs::write(&cert, vec![b' '; 1_048_577]).unwrap();

    let verify = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["verify-cert", "--cert"])
        .arg(&cert)
        .args(["--package"])
        .arg(fixture())
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&verify.stderr);
    assert!(!verify.status.success());
    assert!(stderr.contains("R810"), "{stderr}");
    assert!(stderr.contains("exceeds"), "{stderr}");
}

#[cfg(all(unix, not(feature = "solver")))]
#[test]
fn solver_off_package_check_and_verify_fail_before_success_or_artifacts() {
    let temp = TestDir::new();
    let emitted_cert = temp.path().join("emitted-package-cert.json");
    let emitted_wasm = temp.path().join("emitted-package.wasm");
    let check = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["check", "--package"])
        .arg(fixture())
        .args(["--cert"])
        .arg(&emitted_cert)
        .args(["--emit-wasm"])
        .arg(&emitted_wasm)
        .arg("--json")
        .env("SIGIL_ALLOW_UNVERIFIED_CERT", "1")
        .output()
        .unwrap();
    assert!(!check.status.success());
    let check_envelope: serde_json::Value = serde_json::from_slice(&check.stdout)
        .unwrap_or_else(|error| panic!("solver-off check did not emit JSON: {error}"));
    assert_eq!(check_envelope["status"], "error");
    assert_eq!(check_envelope["diagnostics"][0]["code"], "R817");
    assert!(
        check_envelope.get("certificate").is_none()
            && check_envelope
                .get("data")
                .and_then(|data| data.get("certificate"))
                .is_none(),
        "solver-off package check emitted certificate data: {check_envelope}"
    );
    assert!(
        !emitted_cert.exists(),
        "solver-off package check wrote a certificate before rejecting"
    );
    assert!(
        !emitted_wasm.exists(),
        "solver-off package check wrote Wasm before rejecting"
    );

    let supplied_cert = temp.path().join("supplied-package-cert.json");
    write_fresh_package_certificate(&supplied_cert);
    let verify = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["verify-cert", "--cert"])
        .arg(&supplied_cert)
        .args(["--package"])
        .arg(fixture())
        .env("SIGIL_ALLOW_UNVERIFIED_CERT", "1")
        .output()
        .unwrap();
    let verify_stderr = String::from_utf8_lossy(&verify.stderr);
    assert!(!verify.status.success());
    assert!(verify_stderr.contains("R817"), "{verify_stderr}");
    assert!(
        !String::from_utf8_lossy(&verify.stdout).contains("verify-cert: OK"),
        "solver-off package verification reported success"
    );
}

#[cfg(feature = "solver")]
#[test]
fn solver_only_refinement_violation_is_rejected_by_package_check() {
    let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["check", "--package"])
        .arg(solver_negative_fixture())
        .arg("--json")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let envelope: serde_json::Value =
        serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
            panic!(
                "solver rejection did not emit JSON: {error}; stderr={}",
                String::from_utf8_lossy(&output.stderr)
            )
        });
    let codes: Vec<&str> = envelope["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|diagnostic| diagnostic["code"].as_str())
        .collect();
    assert!(
        codes.contains(&"T210"),
        "codes={codes:?}, envelope={envelope}"
    );
}

#[cfg(all(unix, not(feature = "solver")))]
#[test]
fn solver_only_refinement_cannot_escape_through_structural_package_mode() {
    let temp = TestDir::new();
    let cert = temp.path().join("solver-negative-cert.json");
    let wasm = temp.path().join("solver-negative.wasm");
    let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["check", "--package"])
        .arg(solver_negative_fixture())
        .args(["--cert"])
        .arg(&cert)
        .args(["--emit-wasm"])
        .arg(&wasm)
        .arg("--json")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let envelope: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(envelope["diagnostics"][0]["code"], "R817");
    assert!(!cert.exists() && !wasm.exists());

    let safe_compile = sigil_compiler::package::compile_local_package(
        &solver_negative_fixture(),
        sigil_compiler::CompileOptions::default(),
    )
    .expect_err("the accepting compiler API must reject solver-off package evidence");
    match safe_compile {
        sigil_compiler::package::PackageCompileError::Package(error) => {
            assert_eq!(error.code, "E_SOLVER_UNVERIFIED")
        }
        sigil_compiler::package::PackageCompileError::Compiler(error) => {
            panic!("expected solver gate, got compiler error: {error:?}")
        }
    }

    let package = sigil_compiler::package::compile_local_package_structural(
        &solver_negative_fixture(),
        sigil_compiler::CompileOptions::default(),
    )
    .expect("explicit structural API remains available for solver-off diagnostics");
    let certificate = package.certificate();
    sigil_compiler::package::verify_local_package_certificate_structural(
        &solver_negative_fixture(),
        &certificate,
        sigil_compiler::CompileOptions::default(),
    )
    .expect("the structural comparator should confirm its own exact re-derivation");
    let safe_verify = sigil_compiler::package::verify_local_package_certificate(
        &solver_negative_fixture(),
        &certificate,
        sigil_compiler::CompileOptions::default(),
    )
    .expect_err("the accepting verifier API must reject solver-off package evidence");
    match safe_verify {
        sigil_compiler::package::PackageCompileError::Package(error) => {
            assert_eq!(error.code, "E_SOLVER_UNVERIFIED")
        }
        sigil_compiler::package::PackageCompileError::Compiler(error) => {
            panic!("expected solver gate, got compiler error: {error:?}")
        }
    }
    std::fs::write(&cert, serde_json::to_vec_pretty(&certificate).unwrap()).unwrap();
    let verify = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["verify-cert", "--cert"])
        .arg(&cert)
        .args(["--package"])
        .arg(solver_negative_fixture())
        .output()
        .unwrap();
    assert!(!verify.status.success());
    assert!(String::from_utf8_lossy(&verify.stderr).contains("R817"));
}

/// Where fd-based secure traversal is unavailable, package compilation must refuse
/// loudly rather than fall back to insecure path walking. On unix the certificate
/// tests above exercise the working path; here the refusal itself is the contract.
#[cfg(not(unix))]
#[test]
fn package_compile_fails_closed_where_secure_traversal_is_unavailable() {
    let error = match sigil_compiler::package::compile_local_package_structural(
        &fixture(),
        sigil_compiler::CompileOptions::default(),
    ) {
        Err(sigil_compiler::package::PackageCompileError::Package(error)) => error,
        other => panic!("expected the platform fail-closed refusal, got {other:?}"),
    };
    assert_eq!(error.code, "E_UNSUPPORTED_PLATFORM");
}
