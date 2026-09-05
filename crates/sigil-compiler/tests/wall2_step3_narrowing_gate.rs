//! Wall 2 Stage 3 — close the `restrict_deadline` narrowing escape hatch.
//!
//! Stage 2's T199 fires on parametric cap LITERALS at type positions
//! (function params, state fields, spawn args, etc.). The
//! `restrict_deadline(D')` argument is a method-call argument, not a
//! type position, so Stage 2's check didn't see it. Stage 3 mirrors
//! the build-deadline check at the restrict_deadline call site —
//! `D' < BUILD_NOW` now fires T199 too.

use sigil_compiler::CompileError;
use sigil_compiler::CompileOptions;
use sigil_compiler::compile_named_module_with_options;

fn assert_emits_with(
    source: &str,
    label: &str,
    expected_code: &str,
    options: CompileOptions,
) -> CompileError {
    let err =
        compile_named_module_with_options(format!("wall2_step3_{label}.sigil"), source, options)
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

fn assert_compiles_clean_with(source: &str, label: &str, options: CompileOptions) {
    let result =
        compile_named_module_with_options(format!("wall2_step3_{label}.sigil"), source, options);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

#[test]
fn restrict_deadline_below_build_now_fires_t199() {
    // Without the Stage 3 close, the user could narrow past
    // `--build-deadline` because the restrict_deadline literal isn't
    // at a type position. Stage 3 closes the hole.
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(2030)) -> i64 {
    let _stale = c.restrict_deadline(2020);
    return 0;
}
"#;
    assert_emits_with(
        source,
        "narrow_past_build_now",
        "T199",
        CompileOptions {
            build_deadline: Some(2025),
        },
    );
}

#[test]
fn restrict_deadline_at_build_now_compiles() {
    // Boundary: restrict_deadline to EXACTLY BUILD_NOW is permitted.
    // Anything below would be stale; equality is fine.
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_2025(c: Approval(2025)) -> i64 { return 1; }
fn boot(c: Approval(2030)) -> i64 {
    let n = c.restrict_deadline(2025);
    return use_2025(n);
}
"#;
    assert_compiles_clean_with(
        source,
        "narrow_to_build_now",
        CompileOptions {
            build_deadline: Some(2025),
        },
    );
}

#[test]
fn restrict_deadline_above_build_now_compiles() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_2028(c: Approval(2028)) -> i64 { return 1; }
fn boot(c: Approval(2030)) -> i64 {
    let n = c.restrict_deadline(2028);
    return use_2028(n);
}
"#;
    assert_compiles_clean_with(
        source,
        "narrow_above_build_now",
        CompileOptions {
            build_deadline: Some(2025),
        },
    );
}

#[test]
fn restrict_deadline_below_build_now_message_has_required_fields() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(2030)) -> i64 {
    let _stale = c.restrict_deadline(2020);
    return 0;
}
"#;
    let err = compile_named_module_with_options(
        "wall2_step3_msg.sigil".to_owned(),
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
    // Message must name the narrowing target and the build-time
    // reference so the user can act on the fix.
    assert!(msg.contains("2020"), "must contain narrowing target: {msg}");
    assert!(msg.contains("2025"), "must contain build deadline: {msg}");
    assert!(
        msg.contains("restrict_deadline"),
        "must name the operation: {msg}"
    );
}

#[test]
fn no_build_deadline_allows_any_narrowing() {
    // With no --build-deadline, restrict_deadline accepts any literal
    // (subject to the existing T200 narrowing-only constraint).
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_one(c: Approval(1)) -> i64 { return 1; }
fn boot(c: Approval(2030)) -> i64 {
    let n = c.restrict_deadline(1);
    return use_one(n);
}
"#;
    assert_compiles_clean_with(
        source,
        "no_flag_allows_any",
        CompileOptions {
            build_deadline: None,
        },
    );
}

#[test]
fn restrict_deadline_extension_still_fires_t200_not_t199() {
    // Stage 2's T200 (narrowing-only) remains the FIRST check. Even
    // with --build-deadline set, an extension fires T200 (not T199).
    // This pins INV-7-style specificity for Stage 3.
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(2025)) -> i64 {
    let _wider = c.restrict_deadline(2030);
    return 0;
}
"#;
    let err = compile_named_module_with_options(
        "wall2_step3_t200_priority.sigil".to_owned(),
        source,
        CompileOptions {
            build_deadline: Some(2025),
        },
    )
    .expect_err("expected T200");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"T200"),
        "expected T200 for extension, got: {codes:?}"
    );
}
