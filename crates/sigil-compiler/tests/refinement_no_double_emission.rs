//! Regression + invariant gate for the **double-emission class** the Phase-2
//! cutover surfaced.
//!
//! Refinement responsibilities are split into two disjoint code sets:
//!
//!   * the DECLARATION-TIME VALIDATOR (`validate_refinement_shapes_at_decls`)
//!     owns SHAPE errors — a `where` clause whose fields have the wrong types:
//!     T120, T212, T213, T217, T219, T221, T222.
//!   * the v2 DISCHARGE pipeline (`type_check_v2`) owns the Z3-backed
//!     satisfiability verdicts: T210, T211, T215, T216, T220, T224, T225.
//!
//! The invariant: **a single mis-shaped refinement clause must produce exactly
//! one refinement error, and it must come from the validator — never a
//! validator SHAPE code AND a v2 DISCHARGE code for the same clause.** When the
//! validator rejects a clause at declaration, v2 must SKIP discharging it.
//!
//! The bug: v2's cross-field record collector emitted T216 ("symbolic
//! cross-field") for a clause whose field types the validator ALREADY rejected
//! (T212 non-i64 LHS / T219 non-i64 RHS), because it keyed off "the supplied
//! value isn't an int literal" rather than the declared field type. Result:
//! two errors where legacy's short-circuiting walker produced one. The fix gates
//! v2's cross-field discharge on the declared/​supplied field types, mirroring
//! the walker's shape gate. These fixtures pin that fix and generalise it.
//!
//! `#![cfg(feature = "solver")]` — the v2 DISCHARGE codes come from Z3, so the
//! double-emission can only be observed with the solver on.

#![cfg(feature = "solver")]

use proptest::prelude::*;
use sigil_compiler::compile_named_module;

/// SHAPE codes owned by the declaration-time validator.
const VALIDATOR_SHAPE_CODES: &[&str] = &["T120", "T212", "T213", "T217", "T219", "T221", "T222"];

/// DISCHARGE codes owned by the v2 obligation pipeline.
const V2_DISCHARGE_CODES: &[&str] = &["T210", "T211", "T215", "T216", "T220", "T224", "T225"];

fn refinement_error_codes(src: &str) -> Vec<String> {
    let err = compile_named_module("double_emit.sigil", src)
        .expect_err("a mis-shaped refinement clause must be rejected");
    err.diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .filter(|c| {
            VALIDATOR_SHAPE_CODES.contains(&c.as_str()) || V2_DISCHARGE_CODES.contains(&c.as_str())
        })
        .collect()
}

/// The core invariant: at most one refinement code, and it is NOT the case that
/// a validator shape code and a v2 discharge code both fire (the double-emission
/// the cutover introduced). Returns the codes for an informative message.
fn assert_single_owner(label: &str, src: &str, expected: &str) {
    let codes = refinement_error_codes(src);
    let shape: Vec<_> = codes
        .iter()
        .filter(|c| VALIDATOR_SHAPE_CODES.contains(&c.as_str()))
        .collect();
    let discharge: Vec<_> = codes
        .iter()
        .filter(|c| V2_DISCHARGE_CODES.contains(&c.as_str()))
        .collect();
    assert!(
        shape.is_empty() || discharge.is_empty(),
        "{label}: DOUBLE EMISSION — a validator shape code {shape:?} and a v2 \
         discharge code {discharge:?} both fired for the same mis-shaped clause. \
         v2 must skip discharging a clause the validator already rejects."
    );
    assert_eq!(
        codes.len(),
        1,
        "{label}: expected exactly one refinement error, got {codes:?}"
    );
    assert_eq!(
        codes[0], expected,
        "{label}: expected the validator's {expected}, got {codes:?}"
    );
}

#[test]
fn record_cross_field_non_i64_rhs_emits_only_the_validator_code() {
    // `value <= flag` — RHS field `flag` is bool, not i64. The validator owns
    // this as T219; v2 must NOT also emit T216. (This is the fixture-45 shape,
    // the exact case the cutover regressed.)
    assert_single_owner(
        "record cross-field non-i64 RHS",
        "module m;\n\
         record Mixed { value: i64, flag: bool } where value <= flag\n\
         pub fn f() -> i64 { let r: Mixed = Mixed { value: 5, flag: true }; return 1; }\n",
        "T219",
    );
}

#[test]
fn record_cross_field_non_i64_lhs_emits_only_the_validator_code() {
    // `flag <= value` — LHS field `flag` is bool, not i64. The validator owns
    // this as T212; v2 must NOT also emit T216. This is the SYMMETRIC case that
    // had no test before — the LHS half of the shape gate.
    assert_single_owner(
        "record cross-field non-i64 LHS",
        "module m;\n\
         record Mixed { flag: bool, value: i64 } where flag <= value\n\
         pub fn f() -> i64 { let r: Mixed = Mixed { flag: true, value: 5 }; return 1; }\n",
        "T212",
    );
}

/// All error codes from a compile, whether or not it succeeded (a satisfiable
/// well-shaped clause compiles clean → no codes). Unlike `refinement_error_codes`
/// this does NOT assume the program is rejected.
fn all_refinement_codes(src: &str) -> Vec<String> {
    match compile_named_module("double_emit_prop.sigil", src) {
        Ok(_) => Vec::new(),
        Err(err) => err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .filter(|c| {
                VALIDATOR_SHAPE_CODES.contains(&c.as_str())
                    || V2_DISCHARGE_CODES.contains(&c.as_str())
            })
            .collect(),
    }
}

/// A (field type, construction value) pair that is always type-valid for the
/// field, spanning the i64 / non-i64 and literal / symbolic axes that decide
/// which owner (validator shape code vs v2 discharge code) a clause routes to.
/// `n` is an in-scope `i64` parameter, so it is the symbolic-i64 case.
fn field_kind() -> impl Strategy<Value = (&'static str, &'static str)> {
    prop_oneof![
        Just(("i64", "3")),     // i64 literal
        Just(("i64", "n")),     // i64 symbolic (fn param)
        Just(("bool", "true")), // non-i64 field
    ]
}

proptest! {
    // The V9 short-circuit invariant, fuzzed: a record with a SINGLE cross-field
    // clause and a construction supplying both fields can produce at most ONE
    // refinement error — regardless of the field types, the operator, or whether
    // the supplied values are literal or symbolic. Because the validator's shape
    // codes and v2's discharge codes are disjoint, "at most one" is exactly the
    // property that forbids the cutover's validator+discharge double-emission:
    // no combination of inputs may make both fire for the one clause.
    #[test]
    fn single_clause_cross_field_record_emits_at_most_one_refinement_error(
        (lhs_ty, lhs_val) in field_kind(),
        (rhs_ty, rhs_val) in field_kind(),
        op in prop_oneof![Just("<="), Just("<"), Just(">="), Just(">"), Just("=="), Just("!=")],
    ) {
        let source = format!(
            "module m;\n\
             record R {{ a: {lhs_ty}, b: {rhs_ty} }} where a {op} b\n\
             pub fn f(n: i64) -> i64 {{ let r: R = R {{ a: {lhs_val}, b: {rhs_val} }}; return 1; }}\n"
        );
        let codes = all_refinement_codes(&source);
        prop_assert!(
            codes.len() <= 1,
            "more than one refinement error for a single cross-field clause \
             (a: {lhs_ty}={lhs_val}, b: {rhs_ty}={rhs_val}, `a {op} b`): {codes:?} — \
             a validator shape code and a v2 discharge code likely double-emitted"
        );
    }
}

#[test]
fn variant_cross_field_non_i64_does_not_double_emit() {
    // Defense: v2's VARIANT collector already skips cross-field / LengthOf-RHS
    // payload clauses (routing their shape errors to the decl validator), so it
    // never had the record collector's double-emission. Pin that it stays so:
    // a mis-shaped variant cross-field must not reach a v2 discharge code.
    let codes = all_refinement_codes(
        "module m;\n\
         enum E { V(a: i64, b: bool) where a <= b }\n\
         pub fn f() -> i64 { let e: E = V(5, true); return 1; }\n",
    );
    let discharge: Vec<_> = codes
        .iter()
        .filter(|c| V2_DISCHARGE_CODES.contains(&c.as_str()))
        .collect();
    assert!(
        codes.len() <= 1,
        "variant cross-field emitted more than one refinement error: {codes:?}"
    );
    assert!(
        discharge.is_empty(),
        "variant cross-field wrongly reached a v2 discharge code {discharge:?} on top of \
         the validator's shape error — the double-emission class leaked to variants"
    );
}

#[test]
fn owned_code_sets_are_disjoint() {
    // The whole "single owner per clause" argument rests on these two sets being
    // disjoint. If a future code is added to both (or moved without updating the
    // other set), this contract catches it.
    for code in VALIDATOR_SHAPE_CODES {
        assert!(
            !V2_DISCHARGE_CODES.contains(code),
            "{code} is in BOTH the validator-shape and v2-discharge sets; \
             refinement ownership must stay disjoint"
        );
    }
}

#[test]
fn well_shaped_symbolic_cross_field_still_emits_the_v2_discharge_code() {
    // The negative control: a WELL-shaped cross-field (both i64) with a symbolic
    // side is v2's to reject (T216). The shape gate must NOT over-suppress this —
    // otherwise the fix would silently drop a real conservative rejection.
    let codes = refinement_error_codes(
        "module m;\n\
         record Range { lo: i64, hi: i64 } where lo <= hi\n\
         pub fn f() -> i64 { let lo_val: i64 = 3; let r: Range = Range { lo: lo_val, hi: 5 }; return 1; }\n",
    );
    assert_eq!(
        codes,
        vec!["T216".to_string()],
        "a well-shaped but symbolic cross-field must still be v2's T216, got {codes:?}"
    );
}
