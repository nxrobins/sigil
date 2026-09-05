//! End-to-end smoke test for the foreign-frontend CLI surface
//! (`sigil translate --from` and `sigil check --from`). Exercises the wiring
//! against the committed TypeScript fixtures.

use std::path::PathBuf;
use std::process::Command;

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_sigil")
}

fn fixture(rel: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/frontends/typescript")
        .join(rel)
}

#[test]
fn translate_emits_sigil() {
    let out = Command::new(bin())
        .args(["translate", "--from", "typescript"])
        .arg(fixture("compile/net_policy.ts"))
        .output()
        .expect("run sigil translate");
    assert!(out.status.success(), "translate should succeed");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("module net_policy;"), "stdout: {stdout}");
    assert!(
        stdout.contains("cap type Net(deadline_ms: i64) {}"),
        "stdout: {stdout}"
    );
}

#[test]
fn check_from_typescript_compiles() {
    let out = Command::new(bin())
        .args(["check", "--from", "typescript"])
        .arg(fixture("compile/net_policy.ts"))
        .output()
        .expect("run sigil check --from");
    assert!(
        out.status.success(),
        "check --from should compile; stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn check_from_typescript_enforces_stale_cap() {
    let out = Command::new(bin())
        .args(["check", "--from", "typescript", "--build-deadline", "2025"])
        .arg(fixture("enforce_stale.ts"))
        .output()
        .expect("run sigil check --from with build-deadline");
    assert!(!out.status.success(), "stale cap must fail the build");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("stale"),
        "expected T199 stale-cap; stderr: {stderr}"
    );
}

#[test]
fn translate_unknown_annotation_fails() {
    let out = Command::new(bin())
        .args(["translate", "--from", "typescript"])
        .arg(fixture("reject/unknown_annotation.ts"))
        .output()
        .expect("run sigil translate on a reject fixture");
    assert!(!out.status.success(), "unknown annotation must fail");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("FE010"), "expected FE010; stderr: {stderr}");
}

// ── FE1: @effects (effect-mode) ─────────────────────────────────────────────

#[test]
fn translate_effect_mode_emits_outer_ring() {
    let out = Command::new(bin())
        .args(["translate", "--from", "typescript"])
        .arg(fixture("compile/effect_policy.ts"))
        .output()
        .expect("run sigil translate (effect-mode)");
    assert!(out.status.success(), "effect-mode translate should succeed");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("#[ring(outer)]"), "stdout: {stdout}");
    assert!(stdout.contains("effect NetIO;"), "stdout: {stdout}");
}

#[test]
fn check_from_typescript_enforces_effect_leak() {
    let out = Command::new(bin())
        .args(["check", "--from", "typescript"])
        .arg(fixture("enforce_leak.ts"))
        .output()
        .expect("run sigil check --from on an effect-leak fixture");
    assert!(!out.status.success(), "effect leakage must fail the build");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("undeclared effect"),
        "expected E001 effect-leakage; stderr: {stderr}"
    );
}
