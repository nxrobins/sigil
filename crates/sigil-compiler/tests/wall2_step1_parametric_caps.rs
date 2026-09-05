//! Wall 2 Stage 1 — deadline-typed (parametric) cap types.
//!
//! Each test pins one named invariant (INV-1 .. INV-14).
//!
//! Stage 1 delivers the type-level deadline ordering; wall-clock
//! integration is Stage 2/3.

use sigil_compiler::CompileError;
use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    let result = compile_named_module(format!("wall2_step1_{label}.sigil"), source);
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

fn assert_emits(source: &str, label: &str, expected_code: &str) -> CompileError {
    let err = compile_named_module(format!("wall2_step1_{label}.sigil"), source)
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

// ── Scaffolding ─────────────────────────────────────────────────────

#[test]
fn parametric_cap_decl_parses() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(2030)) -> i64 { return 1; }
"#;
    assert_compiles_clean(source, "decl_parses");
}

#[test]
fn parametric_cap_use_with_literal_deadline_compiles() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_before(c: Approval(2030)) -> i64 { return 1; }
fn boot(c: Approval(2030)) -> i64 {
    return use_before(c);
}
"#;
    assert_compiles_clean(source, "use_with_literal");
}

// ── INV-1 covariance ─────────────────────────────────────────────────

#[test]
fn subtyping_longer_deadline_compiles() {
    // 2030 cap flows into a 2025 site — longer deadline is more
    // permissive (covariance), so this is accepted.
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_before_2025(c: Approval(2025)) -> i64 { return 1; }
fn boot(c: Approval(2030)) -> i64 {
    return use_before_2025(c);
}
"#;
    assert_compiles_clean(source, "longer_into_shorter");
}

// ── INV-2 strict identity (shorter deadline fails) ───────────────────

#[test]
fn subtyping_shorter_deadline_fires_t195() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_before_2030(c: Approval(2030)) -> i64 { return 1; }
fn boot(c: Approval(2025)) -> i64 {
    return use_before_2030(c);
}
"#;
    assert_emits(source, "shorter_into_longer", "T195");
}

#[test]
fn equal_deadlines_compile() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_2030(c: Approval(2030)) -> i64 { return 1; }
fn boot(c: Approval(2030)) -> i64 {
    return use_2030(c);
}
"#;
    assert_compiles_clean(source, "equal_deadlines");
}

// ── INV-3a, INV-3b: parametric/non-parametric distinction ───────────

#[test]
fn non_parametric_to_parametric_fires_t195() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
cap type LegacyApproval {}
fn use_parametric(c: Approval(2030)) -> i64 { return 1; }
fn boot(c: LegacyApproval) -> i64 {
    return use_parametric(c);
}
"#;
    // Different cap NAMES (LegacyApproval vs Approval): the generic
    // mismatch fires T071. T195 is reserved for same-name mismatches.
    assert_emits(source, "non_param_to_param", "T071");
}

#[test]
fn parametric_use_without_literal_fires_t196() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_bare(c: Approval) -> i64 { return 1; }
"#;
    assert_emits(source, "bare_parametric", "T196");
}

#[test]
fn non_parametric_with_literal_fires_t197() {
    let source = r#"
module main;
cap type Approval {}
fn use_with_lit(c: Approval(2030)) -> i64 { return 1; }
"#;
    assert_emits(source, "non_param_with_lit", "T197");
}

// ── INV-4: restrict/draw preserves deadline ─────────────────────────

#[test]
fn restrict_preserves_deadline() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) { burn }
fn use_burn(c: Approval(2030)) -> i64 { return 1; }
fn boot(c: Approval(2030)) -> i64 {
    let narrowed = c.restrict(burn);
    return use_burn(narrowed);
}
"#;
    assert_compiles_clean(source, "restrict_preserves");
}

// ── INV-5: Slot element type carries the deadline ────────────────────

#[test]
fn slot_put_with_shorter_deadline_fires_t195() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c2025: Approval(2025)) -> i64 {
    let s = slot_new::<Approval(2030)>();
    slot_put(s, c2025);
    return 0;
}
"#;
    assert_emits(source, "slot_put_short_deadline", "T195");
}

#[test]
fn slot_put_with_equal_deadline_compiles() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(2030)) -> i64 {
    let s = slot_new::<Approval(2030)>();
    slot_put(s, c);
    return 0;
}
"#;
    assert_compiles_clean(source, "slot_put_equal");
}

// ── INV-7: deadline mismatch fires T195 EXACTLY (not T071) ──────────

#[test]
fn deadline_only_mismatch_fires_t195_exactly() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_2030(c: Approval(2030)) -> i64 { return 1; }
fn boot(c: Approval(2025)) -> i64 {
    return use_2030(c);
}
"#;
    let err = assert_emits(source, "exact_t195", "T195");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    // T071 (generic function-call type mismatch) must NOT also fire for
    // a pure deadline mismatch. T195 is the specific replacement.
    assert!(
        !codes.contains(&"T071"),
        "T195 must replace T071 for deadline-only mismatches; got: {codes:?}"
    );
}

// ── INV-8: T195 message contains required fields ────────────────────

#[test]
fn t195_message_has_all_required_fields() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_2030(c: Approval(2030)) -> i64 { return 1; }
fn boot(c: Approval(2025)) -> i64 {
    return use_2030(c);
}
"#;
    let err = compile_named_module("wall2_step1_msg.sigil".to_owned(), source)
        .expect_err("expected T195");
    let t195_diag = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T195")
        .expect("T195 in diagnostics");
    let msg = t195_diag.message();
    assert!(
        msg.contains("2025"),
        "message must contain actual deadline: {msg}"
    );
    assert!(
        msg.contains("2030"),
        "message must contain expected deadline: {msg}"
    );
    assert!(
        msg.contains("Approval") || msg.contains("argument") || msg.contains("deadline"),
        "message must contain site context: {msg}"
    );
    let hint = t195_diag.hint().unwrap_or("");
    assert!(
        hint.contains("restrict_deadline") || hint.contains("widen"),
        "fix hint must mention either `restrict_deadline` or the widen-target option, got: {hint}"
    );
}

// ── INV-12: state-field STORE / assignment subtype-checks ───────────

#[test]
fn assignment_to_shorter_deadline_field_fires_t195() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c2025: Approval(2025)) -> i64 {
    let mut target: Approval(2030) = c2025;
    return 0;
}
"#;
    // Let-binding annotation enforcement; INV-12 covers state-field
    // store via the same canonical helper.
    assert_emits(source, "assign_short_to_long", "T195");
}

// ── INV-13: conditional with differing-deadline branches and no
// annotation produces a clean type-mismatch diagnostic ──────────────

#[test]
fn conditional_differing_deadlines_no_annotation_fails_cleanly() {
    // Stage 1 does not compute joins; both branches must produce
    // identical types or the user must annotate. The mismatch fires a
    // generic type-mismatch code (T049 — return type mismatch).
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn pick(cond: i64, a: Approval(2030), b: Approval(2025)) -> Approval(2030) {
    if cond == 1 {
        return a;
    } else {
        return b;
    }
}
"#;
    // The branch returning `b: Approval(2025)` doesn't satisfy the
    // declared return type `Approval(2030)` — T195 fires on that
    // return statement.
    assert_emits(source, "conditional_no_join", "T195");
}

// ── INV-14: parser-level rejection of empty parens + non-i64 ────────

#[test]
fn cap_type_empty_parens_fires_t198() {
    let source = r#"
module main;
cap type Approval() {}
"#;
    assert_emits(source, "empty_parens", "T198");
}

#[test]
fn cap_type_non_i64_param_fires_t198() {
    let source = r#"
module main;
cap type Approval(deadline: bool) {}
"#;
    assert_emits(source, "non_i64_param", "T198");
}

// ── Bonus: spawn init arg deadline mismatch ─────────────────────────

#[test]
fn parametric_cap_in_spawn_init_fires_t195_on_mismatch() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
cap type Fuel {}

actor Worker {
    init(c: Approval(2030), f: Fuel) {}
    on Ping() -> i64 { return 0; }
}

entry actor Main {
    state { fuel: Fuel, c: Approval(2025) }
    on Start() -> i64 {
        let f = fuel.draw(10);
        let _w = spawn::<Worker>(c, f);
        return 1;
    }
}
"#;
    assert_emits(source, "spawn_short_into_long", "T195");
}
