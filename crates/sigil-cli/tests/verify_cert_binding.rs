//! End-to-end pins for `sigil verify-cert --wasm` module BINDING (BUG-3).
//!
//! The certificate is an unsigned JSON file, so its `wasm_inner_fingerprint`
//! is attacker-writable. A `--wasm` verdict must therefore bind the shipped
//! bytes to a FRESH compilation of `--source`, never to the cert's own
//! field alone. These tests drive the real binary and assert the exact
//! diagnostic code set on the JSON envelope: R809 is the headline, and the
//! typed module-binding failure (R814 / R821) names which link broke.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::Value;

fn sigil_binary() -> &'static str {
    env!("CARGO_BIN_EXE_sigil")
}

fn run_cli(args: &[&str]) -> (i32, String, String) {
    let output = Command::new(sigil_binary())
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to spawn sigil binary");
    let exit = output.status.code().unwrap_or(-1);
    let stdout = String::from_utf8(output.stdout).expect("stdout was not UTF-8");
    let stderr = String::from_utf8(output.stderr).expect("stderr was not UTF-8");
    (exit, stdout, stderr)
}

fn scratch_dir(stem: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock must be after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("sigil_{stem}_{}_{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp directory");
    dir
}

fn arg(path: &Path) -> &str {
    path.to_str().expect("temp path is UTF-8")
}

/// `sigil check <source> --cert <cert> --emit-wasm <wasm>`; returns the
/// parsed cert JSON so a test can rebind one field and write it back.
fn check_with_artifacts(source: &Path, cert: &Path, wasm: &Path) -> Value {
    let (exit, _out, err) = run_cli(&[
        "check",
        arg(source),
        "--cert",
        arg(cert),
        "--emit-wasm",
        arg(wasm),
    ]);
    assert_eq!(exit, 0, "check must emit cert + wasm: {err}");
    serde_json::from_slice(&std::fs::read(cert).expect("read cert")).expect("cert is JSON")
}

fn verify(cert: &Path, source: &Path, wasm: &Path) -> (i32, Value) {
    let (exit, out, _err) = run_cli(&[
        "verify-cert",
        "--cert",
        arg(cert),
        "--source",
        arg(source),
        "--wasm",
        arg(wasm),
        "--json",
    ]);
    let envelope: Value =
        serde_json::from_str(out.trim()).expect("verify-cert --json stdout is an envelope");
    (exit, envelope)
}

/// The exact set of diagnostic codes an envelope carries. An OK envelope
/// omits `diagnostics` entirely (`json_envelope.rs` skips the empty vec),
/// so an ABSENT key is the empty set — that is the success shape, not an
/// error. Fails closed the other way: a key that is present but is not an
/// array of coded diagnostics panics rather than silently reporting an
/// empty set, which would make every `assert_eq!(code_set(..), ..)` below
/// vacuous.
fn code_set(envelope: &Value) -> BTreeSet<String> {
    let Some(diagnostics) = envelope.get("diagnostics") else {
        return BTreeSet::new();
    };
    diagnostics
        .as_array()
        .expect("diagnostics, when present, is an array")
        .iter()
        .map(|d| {
            d["code"]
                .as_str()
                .expect("diagnostic code is a string")
                .to_owned()
        })
        .collect()
}

fn set(codes: &[&str]) -> BTreeSet<String> {
    codes.iter().map(|c| (*c).to_owned()).collect()
}

const HAPPY: &str = "module sigil; fn boot() -> i64 { return 1; }\n";
const FOREIGN: &str = "module sigil; fn boot() -> i64 { return 2; }\n";

#[test]
fn verify_cert_wasm_binding_verdicts_are_typed_and_fail_closed() {
    let dir = scratch_dir("verify_cert_binding");
    let happy_src = dir.join("happy.sigil");
    let happy_cert = dir.join("happy.cert.json");
    let happy_wasm = dir.join("happy.wasm");
    let foreign_src = dir.join("foreign.sigil");
    let foreign_cert = dir.join("foreign.cert.json");
    let foreign_wasm = dir.join("foreign.wasm");
    std::fs::write(&happy_src, HAPPY).expect("write happy source");
    std::fs::write(&foreign_src, FOREIGN).expect("write foreign source");

    let mut happy = check_with_artifacts(&happy_src, &happy_cert, &happy_wasm);
    let foreign = check_with_artifacts(&foreign_src, &foreign_cert, &foreign_wasm);
    assert_ne!(
        std::fs::read(&happy_wasm).expect("read happy wasm"),
        std::fs::read(&foreign_wasm).expect("read foreign wasm"),
        "the two sources must compile to different modules"
    );

    // Accept: honest cert + its own module binds to the fresh compilation.
    let (exit, ok) = verify(&happy_cert, &happy_src, &happy_wasm);
    assert_eq!(exit, 0, "honest cert + own module must verify: {ok}");
    assert_eq!(ok["status"], "ok");
    assert_eq!(ok["data"]["wasm_inner_match"], true);
    assert_eq!(ok["data"]["wasm_binding_ok"], true);
    // Empty because the OK envelope carries no diagnostics — not because
    // `code_set` cannot read them: every rejection below asserts a NON-empty
    // exact set through this same helper, which is what keeps this line from
    // being vacuous.
    assert!(code_set(&ok).is_empty());

    // BUG-3: rebind ONLY the honest cert's inner fingerprint to the foreign
    // module (copy the foreign cert's field verbatim — no hashing needed),
    // then ship the foreign module. Before the fix this verified OK.
    happy["wasm_inner_fingerprint"] = foreign["wasm_inner_fingerprint"].clone();
    let rebound_cert = dir.join("rebound.cert.json");
    std::fs::write(
        &rebound_cert,
        serde_json::to_vec_pretty(&happy).expect("serialize rebound cert"),
    )
    .expect("write rebound cert");
    let (exit, rebound) = verify(&rebound_cert, &happy_src, &foreign_wasm);
    assert_ne!(exit, 0, "a cert rebound to foreign wasm must not verify OK");
    assert_eq!(rebound["status"], "error");
    assert_eq!(
        rebound["data"]["wasm_inner_match"], true,
        "the shipped bytes hash to the cert's own (rebound) field — that is the attack"
    );
    assert_eq!(rebound["data"]["wasm_binding_ok"], false);
    assert_eq!(rebound["data"]["rederivation_ok"], false);
    assert_eq!(code_set(&rebound), set(&["R809", "R814"]));

    // Control: the honest cert with a VALID foreign module shipped is a
    // typed inner mismatch — the cert names a module that is not this one.
    let (exit, swapped) = verify(&happy_cert, &happy_src, &foreign_wasm);
    assert_ne!(exit, 0);
    assert_eq!(swapped["data"]["wasm_inner_match"], false);
    assert_eq!(swapped["data"]["wasm_binding_ok"], false);
    assert_eq!(swapped["data"]["rederivation_ok"], true);
    assert_eq!(code_set(&swapped), set(&["R809", "R814"]));

    // Junk: bytes that are not a module are refused before hashing.
    let junk = dir.join("junk.bin");
    std::fs::write(&junk, b"this is not a wasm module at all").expect("write junk");
    let (exit, junked) = verify(&happy_cert, &happy_src, &junk);
    assert_ne!(exit, 0);
    assert_eq!(junked["data"]["wasm_inner_match"], false);
    assert_eq!(junked["data"]["wasm_binding_ok"], false);
    assert_eq!(code_set(&junked), set(&["R809", "R821"]));

    // Version skew: re-derivation is skipped, so the module binding cannot
    // be established and the --wasm verdict fails closed.
    let mut skewed: Value =
        serde_json::from_slice(&std::fs::read(&happy_cert).expect("read honest cert"))
            .expect("cert is JSON");
    skewed["compiler_version"] = Value::from("9.9.9-not-this-build");
    let skewed_cert = dir.join("skewed.cert.json");
    std::fs::write(
        &skewed_cert,
        serde_json::to_vec_pretty(&skewed).expect("serialize skewed cert"),
    )
    .expect("write skewed cert");
    let (exit, skew) = verify(&skewed_cert, &happy_src, &happy_wasm);
    assert_ne!(exit, 0, "a skewed --wasm verdict must fail closed: {skew}");
    assert_eq!(skew["data"]["compiler_version_match"], false);
    assert_eq!(skew["data"]["rederivation_attempted"], false);
    assert_eq!(skew["data"]["wasm_inner_match"], true);
    assert_eq!(skew["data"]["wasm_binding_ok"], false);
    assert_eq!(code_set(&skew), set(&["R809", "R821"]));

    let _ = std::fs::remove_dir_all(dir);
}
