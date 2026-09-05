//! a5 (resolvability): `sigil explain <CODE>` — the CLI/human counterpart of
//! the MCP `sigil_lookup_error` tool. Known code → registry entry; unknown →
//! fuzzy "did you mean?" + non-zero exit.

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
    let stdout = String::from_utf8(output.stdout).expect("stdout utf-8");
    let stderr = String::from_utf8(output.stderr).expect("stderr utf-8");
    (exit, stdout, stderr)
}

#[test]
fn explain_known_code_json() {
    let (exit, stdout, stderr) = run_cli(&["explain", "T060", "--json"]);
    assert_eq!(exit, 0, "stderr: {stderr}");
    let v: Value = serde_json::from_str(stdout.trim()).expect("stdout should be JSON");
    assert_eq!(v["status"], "ok");
    assert_eq!(v["command"], "explain");
    assert_eq!(v["data"]["code"], "T060");
    assert!(v["data"]["title"].is_string());
    assert!(v["data"]["default_hint"].is_string());
    assert_eq!(v["data"]["doc_url"], "sigil://errors/T060");
    assert_eq!(v["data"]["doc_path"], "docs/errors/T060.md");
}

#[test]
fn explain_known_code_human() {
    let (exit, stdout, stderr) = run_cli(&["explain", "T060"]);
    assert_eq!(exit, 0, "stderr: {stderr}");
    assert!(stdout.contains("T060"), "stdout: {stdout}");
    assert!(stdout.contains("docs/errors/T060.md"), "stdout: {stdout}");
}

#[test]
fn explain_formal_evidence_mismatch_r819() {
    let (exit, stdout, stderr) = run_cli(&["explain", "R819", "--json"]);
    assert_eq!(exit, 0, "stderr: {stderr}");
    let v: Value = serde_json::from_str(stdout.trim()).expect("stdout should be JSON");
    assert_eq!(v["data"]["code"], "R819");
    assert!(
        v["data"]["title"]
            .as_str()
            .is_some_and(|title| title.contains("Formal")),
        "R819 must remain discoverable as the formal-evidence gate"
    );
}

#[test]
fn explain_unknown_code_json_suggests_and_fails() {
    // `T06O` = letter O typo of digit-0 in the real code T060.
    let (exit, stdout, _stderr) = run_cli(&["explain", "T06O", "--json"]);
    assert_ne!(exit, 0, "unknown code should exit non-zero");
    let v: Value = serde_json::from_str(stdout.trim()).expect("stdout should be JSON");
    assert_eq!(v["status"], "error");
    assert_eq!(v["command"], "explain");
    let dym = v["data"]["did_you_mean"]
        .as_array()
        .expect("data.did_you_mean array");
    assert!(
        dym.iter().any(|c| c == "T060"),
        "expected T060 suggestion, got {dym:?}"
    );
}

#[test]
fn explain_unknown_code_human_exits_nonzero() {
    let (exit, _stdout, stderr) = run_cli(&["explain", "ZZZZ"]);
    assert_ne!(exit, 0);
    assert!(
        stderr.contains("not a known diagnostic code"),
        "stderr: {stderr}"
    );
}

#[test]
fn explain_missing_code_is_usage_error() {
    let (exit, _stdout, _stderr) = run_cli(&["explain"]);
    assert_ne!(exit, 0);
}
