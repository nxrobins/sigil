//! Wall 2 Stage 2 — `--build-deadline` flag and `restrict_deadline` method.
//!
//! Stage 2 adds:
//!   * `CompileOptions.build_deadline: Option<i64>` (from `sigil check
//!     --build-deadline <N>`). When set, every parametric cap literal
//!     `Cap(D)` in the source must satisfy `D >= N`; `D < N` fires T199.
//!   * `cap.restrict_deadline(D')` method: narrows a parametric cap's
//!     declared deadline. `D' > D_orig` fires T200; the call is rejected
//!     on non-parametric caps with T200 as well.

use sigil_compiler::CompileError;
use sigil_compiler::CompileOptions;
use sigil_compiler::compile_named_module;
use sigil_compiler::compile_named_module_with_options;

fn assert_compiles_clean(source: &str, label: &str) {
    let result = compile_named_module(format!("wall2_step2_{label}.sigil"), source);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        let messages: Vec<&str> = err.diagnostics().iter().map(|d| d.message()).collect();
        panic!("expected clean compile for {label}; codes: {codes:?}; messages: {messages:?}");
    }
}

fn assert_compiles_clean_with(source: &str, label: &str, options: CompileOptions) {
    let result =
        compile_named_module_with_options(format!("wall2_step2_{label}.sigil"), source, options);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

fn assert_emits(source: &str, label: &str, expected_code: &str) -> CompileError {
    let err = compile_named_module(format!("wall2_step2_{label}.sigil"), source)
        .expect_err(&format!("expected {expected_code} for {label}"));
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&expected_code),
        "expected {expected_code} in diagnostics for {label}, got: {codes:?}"
    );
    err
}

fn assert_emits_with(
    source: &str,
    label: &str,
    expected_code: &str,
    options: CompileOptions,
) -> CompileError {
    let err =
        compile_named_module_with_options(format!("wall2_step2_{label}.sigil"), source, options)
            .expect_err(&format!("expected {expected_code} for {label}"));
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&expected_code),
        "expected {expected_code} in diagnostics for {label}, got: {codes:?}"
    );
    err
}

// ── --build-deadline ─────────────────────────────────────────────────

#[test]
fn no_build_deadline_legacy_default() {
    // Without --build-deadline, even a tiny D compiles fine.
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(1)) -> i64 { return 1; }
"#;
    assert_compiles_clean(source, "no_flag_default");
}

#[test]
fn build_deadline_lower_than_decl_compiles() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(2030)) -> i64 { return 1; }
"#;
    assert_compiles_clean_with(
        source,
        "decl_above_build",
        CompileOptions {
            build_deadline: Some(2025),
        },
    );
}

#[test]
fn build_deadline_equal_to_decl_compiles() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(2025)) -> i64 { return 1; }
"#;
    assert_compiles_clean_with(
        source,
        "decl_equal_build",
        CompileOptions {
            build_deadline: Some(2025),
        },
    );
}

#[test]
fn build_deadline_higher_than_decl_fires_t199() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(2024)) -> i64 { return 1; }
"#;
    assert_emits_with(
        source,
        "decl_below_build",
        "T199",
        CompileOptions {
            build_deadline: Some(2025),
        },
    );
}

#[test]
fn build_deadline_message_has_required_fields() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(2024)) -> i64 { return 1; }
"#;
    let err = compile_named_module_with_options(
        "wall2_step2_msg.sigil".to_owned(),
        source,
        CompileOptions {
            build_deadline: Some(2025),
        },
    )
    .expect_err("expected T199");
    let t199 = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T199")
        .expect("T199 in diagnostics");
    let msg = t199.message();
    assert!(
        msg.contains("2024"),
        "message must contain declared deadline: {msg}"
    );
    assert!(
        msg.contains("2025"),
        "message must contain build deadline: {msg}"
    );
    assert!(msg.contains("Approval"), "message must name the cap: {msg}");
}

#[test]
fn build_deadline_catches_state_field_literal() {
    // The check fires at every literal site, not just function params.
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_old(c: Approval(2024)) -> i64 { return 1; }

entry actor Main {
    state { auth: Approval(2024) }
    on Start() -> i64 {
        return use_old(auth);
    }
}
"#;
    let err = compile_named_module_with_options(
        "wall2_step2_state.sigil".to_owned(),
        source,
        CompileOptions {
            build_deadline: Some(2025),
        },
    )
    .expect_err("expected T199");
    // Should fire at multiple sites — the function param AND the state field
    // both declare 2024 which is < BUILD_NOW.
    let t199_count = err
        .diagnostics()
        .iter()
        .filter(|d| d.code().as_str() == "T199")
        .count();
    assert!(
        t199_count >= 2,
        "expected T199 at multiple sites, got {t199_count}"
    );
}

// ── restrict_deadline ────────────────────────────────────────────────

#[test]
fn restrict_deadline_narrows_compiles() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_2025(c: Approval(2025)) -> i64 { return 1; }
fn boot(c: Approval(2030)) -> i64 {
    let narrowed = c.restrict_deadline(2025);
    return use_2025(narrowed);
}
"#;
    assert_compiles_clean(source, "narrow");
}

#[test]
fn restrict_deadline_to_equal_compiles() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_2030(c: Approval(2030)) -> i64 { return 1; }
fn boot(c: Approval(2030)) -> i64 {
    let same = c.restrict_deadline(2030);
    return use_2030(same);
}
"#;
    assert_compiles_clean(source, "narrow_to_equal");
}

#[test]
fn restrict_deadline_extension_fires_t200() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(2025)) -> i64 {
    let extended = c.restrict_deadline(2030);
    let _ = extended;
    return 0;
}
"#;
    assert_emits(source, "extend", "T200");
}

#[test]
fn restrict_deadline_on_non_parametric_fires_t200() {
    let source = r#"
module main;
cap type Plain {}
fn boot(c: Plain) -> i64 {
    let narrowed = c.restrict_deadline(2025);
    let _ = narrowed;
    return 0;
}
"#;
    assert_emits(source, "non_param", "T200");
}

#[test]
fn restrict_deadline_then_pass_to_shorter_site() {
    // The narrowed cap is subtype-compatible with sites that expected
    // the narrowed deadline (or even shorter).
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_2020(c: Approval(2020)) -> i64 { return 1; }
fn boot(c: Approval(2030)) -> i64 {
    let narrowed = c.restrict_deadline(2025);
    // 2025 cap into 2020 site — covariance: 2025 >= 2020 OK.
    return use_2020(narrowed);
}
"#;
    assert_compiles_clean(source, "narrow_then_subtype");
}
