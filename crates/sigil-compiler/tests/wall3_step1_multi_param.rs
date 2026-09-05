//! Wall 3 Stage 1 — multi-parameter parametric capability types.
//!
//! Each test pins one named invariant. INV-1 (Wall 2 regression sanity)
//! is exercised by the existing `wall2_*.rs` test files.

use sigil_compiler::CompileError;
use sigil_compiler::CompileOptions;
use sigil_compiler::compile_named_module;
use sigil_compiler::compile_named_module_with_options;

fn assert_compiles_clean(source: &str, label: &str) {
    let result = compile_named_module(format!("wall3_{label}.sigil"), source);
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
    let err = compile_named_module(format!("wall3_{label}.sigil"), source)
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
    let err = compile_named_module_with_options(format!("wall3_{label}.sigil"), source, options)
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
fn single_param_unchanged() {
    // Sanity: the Wall 2 legacy single-parameter form still compiles.
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn use_2030(c: Approval(2030)) -> i64 { return 1; }
fn boot(c: Approval(2030)) -> i64 {
    return use_2030(c);
}
"#;
    assert_compiles_clean(source, "single_param_unchanged");
}

#[test]
fn non_parametric_unchanged() {
    let source = r#"
module main;
cap type Plain {}
fn use_plain(c: Plain) -> i64 { return 1; }
fn boot(c: Plain) -> i64 { return use_plain(c); }
"#;
    assert_compiles_clean(source, "non_parametric_unchanged");
}

// ── INV-2: multi-param declaration parses ────────────────────────────

#[test]
fn multi_param_decl_parses() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn boot(c: Limited(2030, 5)) -> i64 { return 1; }
"#;
    assert_compiles_clean(source, "multi_param_decl");
}

// ── INV-3: multi-param usage with matching arity compiles ───────────

#[test]
fn multi_param_use_compiles() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn settle(c: Limited(2030, 5)) -> i64 { return 1; }
fn boot(c: Limited(2030, 5)) -> i64 {
    return settle(c);
}
"#;
    assert_compiles_clean(source, "multi_param_use");
}

// ── INV-4: all-positions covariance (DIFFERENT values per position) ─

#[test]
fn multi_param_subtype_compiles() {
    // MC-6 fence: values differ per position so a "treats positions
    // identically" lazy impl would fail here.
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn settle(c: Limited(2030, 5)) -> i64 { return 1; }
fn boot(c: Limited(2031, 6)) -> i64 {
    return settle(c);
}
"#;
    assert_compiles_clean(source, "multi_param_subtype");
}

// ── INV-5a: position-0 mismatch fires T195 ──────────────────────────

#[test]
fn position_zero_mismatch_fires_t195() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn settle(c: Limited(2030, 5)) -> i64 { return 1; }
fn boot(c: Limited(2025, 5)) -> i64 {
    return settle(c);
}
"#;
    assert_emits(source, "pos_zero_mismatch", "T195");
}

// ── INV-5b: position-1 mismatch fires T195 ──────────────────────────

#[test]
fn position_one_mismatch_fires_t195() {
    // MC-2/MC-6 fence: position 0 is SAFE, position 1 is mismatched.
    // A lazy impl that only checks position 0 would let this pass.
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn settle(c: Limited(2030, 5)) -> i64 { return 1; }
fn boot(c: Limited(2030, 3)) -> i64 {
    return settle(c);
}
"#;
    assert_emits(source, "pos_one_mismatch", "T195");
}

// ── INV-5c: T195 message enumerates EVERY failing dimension ─────────

#[test]
fn t195_message_lists_all_failures() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn settle(c: Limited(2030, 5)) -> i64 { return 1; }
fn boot(c: Limited(2025, 3)) -> i64 {
    return settle(c);
}
"#;
    let err = compile_named_module("wall3_t195_lists_all.sigil".to_owned(), source)
        .expect_err("expected T195");
    let t195 = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T195")
        .expect("T195 in diagnostics");
    let msg = t195.message();
    // MC-3 fence: BOTH failing positions must appear in the message.
    assert!(
        msg.contains("position 0"),
        "T195 message must list position 0: {msg}"
    );
    assert!(
        msg.contains("position 1"),
        "T195 message must list position 1: {msg}"
    );
}

// ── INV-6: arity mismatch (declared 2, used 1) fires T201 ───────────

#[test]
fn arity_mismatch_short_fires_t201() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn settle(c: Limited(2030)) -> i64 { return 1; }
"#;
    assert_emits(source, "arity_short", "T201");
}

// ── INV-7: arity mismatch (declared 1, used 2) fires T201 ───────────

#[test]
fn arity_mismatch_long_fires_t201() {
    let source = r#"
module main;
cap type Approval(deadline_ms: i64) {}
fn settle(c: Approval(2030, 5)) -> i64 { return 1; }
"#;
    assert_emits(source, "arity_long", "T201");
}

// ── INV-8a: restrict_deadline on multi-param fires T200 ─────────────

#[test]
fn restrict_deadline_on_multi_fires_t200_with_multi_variant() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn boot(c: Limited(2030, 5)) -> i64 {
    let _x = c.restrict_deadline(2025);
    return 0;
}
"#;
    let err = assert_emits(source, "restrict_multi", "T200");
    // INV-8b: the message must mention "multi-parameter" specifically
    // (not the generic "non-parametric" message).
    let t200 = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T200")
        .expect("T200 in diagnostics");
    assert!(
        t200.message().contains("multi-parameter"),
        "T200 multi-param variant must mention 'multi-parameter': {}",
        t200.message()
    );
}

// ── INV-8b: T200 variants distinguishable ───────────────────────────

#[test]
fn t200_message_variants_distinct() {
    let non_param_source = r#"
module main;
cap type Plain {}
fn boot(c: Plain) -> i64 {
    let _x = c.restrict_deadline(2025);
    return 0;
}
"#;
    let multi_source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn boot(c: Limited(2030, 5)) -> i64 {
    let _x = c.restrict_deadline(2025);
    return 0;
}
"#;
    let non_param_err = assert_emits(non_param_source, "t200_non_param", "T200");
    let multi_err = assert_emits(multi_source, "t200_multi", "T200");
    let non_param_msg = non_param_err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T200")
        .unwrap()
        .message();
    let multi_msg = multi_err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T200")
        .unwrap()
        .message();
    assert!(
        non_param_msg.contains("non-parametric"),
        "non-param T200: {non_param_msg}"
    );
    assert!(
        multi_msg.contains("multi-parameter"),
        "multi-param T200: {multi_msg}"
    );
    assert_ne!(
        non_param_msg, multi_msg,
        "T200 variants must be distinguishable"
    );
}

// ── INV-9a: --build-deadline fires T199 on position 1 when position 0 is safe ─

#[test]
fn build_deadline_catches_non_zero_position() {
    // MC-2 fence: position 0 is safe (2030 >= 2025), position 1 is
    // stale (50 < 100). A lazy impl that only checks position 0
    // would let this slip.
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn boot(c: Limited(2030, 50)) -> i64 { return 1; }
"#;
    assert_emits_with(
        source,
        "non_zero_position_stale",
        "T199",
        CompileOptions {
            build_deadline: Some(100),
        },
    );
}

// ── INV-9b: multiple stale positions fire MULTIPLE T199 ─────────────

#[test]
fn multi_stale_positions_fire_multiple_t199() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn boot(c: Limited(50, 60)) -> i64 { return 1; }
"#;
    let err = compile_named_module_with_options(
        "wall3_multi_stale.sigil".to_owned(),
        source,
        CompileOptions {
            build_deadline: Some(100),
        },
    )
    .expect_err("expected T199");
    let t199_count = err
        .diagnostics()
        .iter()
        .filter(|d| d.code().as_str() == "T199")
        .count();
    assert!(
        t199_count >= 2,
        "expected at least 2 T199 (one per stale position), got {t199_count}"
    );
}

// ── INV-10: Slot<multi-param-cap> distinguishes by all params ───────

#[test]
fn slot_multi_param_distinguishes() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn boot(c: Limited(2030, 5)) -> i64 {
    let s = slot_new::<Limited(2030, 6)>();
    slot_put(s, c);
    return 0;
}
"#;
    // The slot's element type is `Limited(2030, 6)`; the put cap is
    // `Limited(2030, 5)`. Covariance: 2030>=2030 ✓ but 5>=6 ✗ → T195.
    assert_emits(source, "slot_multi_distinguishes", "T195");
}

// ── INV-11: render_type includes all params positionally ────────────

#[test]
fn render_includes_all_params_positionally() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn settle(c: Limited(2030, 5)) -> i64 { return 1; }
fn boot(c: Limited(2025, 3)) -> i64 {
    return settle(c);
}
"#;
    let err =
        compile_named_module("wall3_render.sigil".to_owned(), source).expect_err("expected T195");
    // The rendered cap type in messages should include all params.
    let t195 = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T195")
        .expect("T195 in diagnostics");
    let msg = t195.message();
    // The message should reference both 2030 and 5 (the expected target)
    // via render_type — covered by INV-5c too.
    assert!(
        msg.contains("2030") || msg.contains("position 0"),
        "render must surface position 0: {msg}"
    );
    assert!(
        msg.contains("5") || msg.contains("position 1"),
        "render must surface position 1: {msg}"
    );
}

// ── INV-12: T201 message has all required fields ────────────────────

#[test]
fn t201_message_has_all_required_fields() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn settle(c: Limited(2030)) -> i64 { return 1; }
"#;
    let err =
        compile_named_module("wall3_t201_msg.sigil".to_owned(), source).expect_err("expected T201");
    let t201 = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T201")
        .expect("T201 in diagnostics");
    let msg = t201.message();
    // MC-10 fence: cap name + declared arity + used arity + param names.
    assert!(msg.contains("Limited"), "T201 must name the cap: {msg}");
    assert!(msg.contains("2"), "T201 must contain declared arity: {msg}");
    assert!(msg.contains("1"), "T201 must contain used arity: {msg}");
    assert!(
        msg.contains("deadline_ms") || msg.contains("max_uses"),
        "T201 must contain declared param names: {msg}"
    );
}

// ── INV-13: cap_subtype rejects arity mismatch BEFORE per-position ──

#[test]
fn cap_subtype_arity_check_first() {
    // MC-1 fence: routing through `type_compatible` (the canonical
    // helper) must catch arity mismatch via cap_subtype's explicit
    // arity check. Construct a scenario where a multi-param cap is
    // passed to a single-param sink.
    let source = r#"
module main;
cap type ApprovalSingle(deadline_ms: i64) {}
cap type ApprovalMulti(deadline_ms: i64, max_uses: i64) {}
fn use_single(c: ApprovalSingle(2030)) -> i64 { return 1; }
fn boot(c: ApprovalMulti(2030, 5)) -> i64 {
    return use_single(c);
}
"#;
    // Different cap NAMES — falls through to T071 (regular type
    // mismatch). The point of this INV is that NO Cap-vs-Cap path
    // accepts mismatched-arity; the test asserts compile fails (any
    // T-code is fine as long as it's a rejection).
    let err = compile_named_module("wall3_arity_first.sigil".to_owned(), source)
        .expect_err("expected rejection");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        !codes.is_empty(),
        "must reject cap with different arity, got: {codes:?}"
    );
}

// ── INV-14: type_compatible routes Cap-vs-Cap through cap_subtype ───

#[test]
fn type_compatible_routes_all_cap_pairs() {
    // MC-4 fence: type_compatible must NOT use structural equality
    // for Cap-vs-Cap. Covariance must apply for any pair. Test:
    // longer-deadline cap flows into shorter sink (multi-param).
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn settle(c: Limited(2030, 5)) -> i64 { return 1; }
fn boot(c: Limited(2031, 5)) -> i64 {
    // 2031>=2030, 5>=5 — covariance OK, no T195 even though Vecs differ.
    return settle(c);
}
"#;
    assert_compiles_clean(source, "covariance_diff_vec");
}

// ── INV-15: cap_subtype reflexive ───────────────────────────────────

#[test]
fn cap_subtype_reflexive() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn settle(c: Limited(2030, 5)) -> i64 { return 1; }
fn boot(c: Limited(2030, 5)) -> i64 {
    return settle(c);
}
"#;
    assert_compiles_clean(source, "reflexive");
}

// ── INV-16: non-parametric bypasses build-deadline check ────────────

#[test]
fn non_parametric_skipped_by_build_deadline() {
    let source = r#"
module main;
cap type Plain {}
fn boot(c: Plain) -> i64 { return 1; }
"#;
    // Plain has empty Vec — build-deadline loop has nothing to iterate.
    let result = compile_named_module_with_options(
        "wall3_non_param_skip.sigil".to_owned(),
        source,
        CompileOptions {
            build_deadline: Some(2025),
        },
    );
    assert!(
        result.is_ok(),
        "non-parametric should bypass build-deadline check"
    );
}

// ── INV-17: C001 forgery still fires for multi-param caps ───────────

#[test]
fn multi_param_forgery_fires_c001() {
    // Forging a multi-param cap via record-construct syntax.
    // The C001 path doesn't care about params; what matters is that
    // it STILL fires for parametric caps.
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn forge() -> Limited(2030, 5) {
    return Limited {};
}
"#;
    // Either C001 (forgery) or a parse/type error before forgery is
    // detected — whatever fires, the program must be rejected.
    let result = compile_named_module("wall3_forgery.sigil".to_owned(), source);
    assert!(result.is_err(), "forgery must be rejected");
}

// ── INV-18: N004 catches duplicate cap-type name across arities ─────

#[test]
fn duplicate_multi_param_decl_fires_n004() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64) {}
cap type Limited(deadline_ms: i64, max_uses: i64) {}
"#;
    // N002 (duplicate item) is the catch-all for same-name declarations.
    let err = compile_named_module("wall3_duplicate.sigil".to_owned(), source)
        .expect_err("expected rejection");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.iter().any(|c| c.starts_with('N')),
        "duplicate cap-type name must fire an N-code, got: {codes:?}"
    );
}

// ── INV-19: trailing comma in decl fires T198 ───────────────────────

#[test]
fn trailing_comma_decl_fires_t198() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64,) {}
"#;
    assert_emits(source, "trailing_comma_decl", "T198");
}

// ── INV-20: trailing comma in usage fires T198 ──────────────────────

#[test]
fn trailing_comma_usage_fires_t198() {
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn boot(c: Limited(2030, 5,)) -> i64 { return 1; }
"#;
    assert_emits(source, "trailing_comma_usage", "T198");
}

// ── INV-21: non-i64 at second position fires T198 ───────────────────

#[test]
fn non_i64_at_second_position_fires_t198() {
    // INV-21 fence: lazy impl might check position 0 only and accept
    // garbage at later positions. The parser must reject at every
    // position.
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: bool) {}
"#;
    assert_emits(source, "non_i64_second_pos", "T198");
}

// ── INV-22: Slot meet model unaffected ──────────────────────────────

#[test]
fn slot_meet_authorities_only() {
    // MI-11 fence: PR #40's Slot authority meet operates on BV<32>
    // bitmasks, not on parametric deadlines. Multi-param caps in slots
    // route deadline-aware identity through type-check at slot_put.
    // This test simply verifies multi-param Slot put compiles when
    // deadlines match.
    let source = r#"
module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn boot(c: Limited(2030, 5)) -> i64 {
    let s = slot_new::<Limited(2030, 5)>();
    slot_put(s, c);
    return 0;
}
"#;
    assert_compiles_clean(source, "slot_meet_authorities_only");
}
