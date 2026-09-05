//! CT018 / T033 — `str` `==` / `!=` with a `@SecretCT` operand.
//!
//! `str` equality compares CONTENT with an early-exit byte loop. Its trip
//! count reveals the length of the common prefix, and so does the fuel it
//! consumes — which the runtime surfaces. Either is a timing oracle over
//! secret data.
//!
//! The gate has to live in `taint_check`, and it has to be a REJECTION.
//!
//! It lives there because taint runs on the typed AST, strictly before
//! `air::lower`; the byte loop is an AIR construct, so nothing downstream of
//! lowering can see a taint label. A gate placed any later would be looking at
//! the loop with the labels already gone.
//!
//! It is a rejection rather than a constant-time lowering for three reasons.
//! Taint results are not carried into lowering, so selecting a CT lowering
//! would need a new taint→AIR channel. A branch-free compare still leaks
//! `min(len_a, len_b)` through its trip count and its fuel. And the CT
//! intrinsics (`ct_eq` / `ct_select` / `ct_lt`) are integer-only, so there is
//! nothing to build a constant-time `str` compare out of today.
//!
//! These tests pin the gate AND its boundaries — the shapes it must NOT fire
//! on matter as much as the one it must.

use sigil_compiler::compile_named_module;

fn codes_for(label: &str, source: &str) -> Vec<String> {
    match compile_named_module(format!("ctstr_{label}.sigil"), source) {
        Ok(_) => Vec::new(),
        Err(err) => err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

/// The comparison result is bound to an unused local rather than branched on,
/// so a `@SecretCT` `if` condition (T020 / CT001) cannot fire and muddy the
/// assertion. What is under test is the comparison itself.
fn cmp_tool(ty: &str, op: &str) -> String {
    format!(
        "module main;\n\nfn cmp(a: {ty} @SecretCT, b: {ty} @SecretCT) -> i64 {{\n\
         \x20   let e = a {op} b;\n\
         \x20   return 0;\n}}\n"
    )
}

#[test]
fn str_eq_with_a_secret_operand_is_rejected() {
    let codes = codes_for("eq", &cmp_tool("str", "=="));
    assert!(
        codes.contains(&"T033".to_string()),
        "expected T033 for `str ==` on @SecretCT operands, got: {codes:?}"
    );
}

#[test]
fn str_neq_with_a_secret_operand_is_rejected() {
    // `!=` lowers as `==` then an inversion, so it shares the byte loop and
    // must share the gate. A fix that only matched `Eq` would leave the exact
    // same leak reachable through one extra character of source.
    let codes = codes_for("neq", &cmp_tool("str", "!="));
    assert!(
        codes.contains(&"T033".to_string()),
        "expected T033 for `str !=` on @SecretCT operands, got: {codes:?}"
    );
}

/// Integer `==` on secrets stays legal: it is a single `i32.eq`/`i64.eq`, with
/// no data-dependent control flow and nothing to time. Rejecting it would be a
/// false positive that pushes users toward worse constructions.
#[test]
fn integer_eq_with_a_secret_operand_is_still_allowed() {
    for ty in ["i64", "i32", "u32", "u64", "bool"] {
        let codes = codes_for("int", &cmp_tool(ty, "=="));
        assert!(
            !codes.contains(&"T033".to_string()),
            "T033 must not fire for `{ty} ==` (single instruction, no timing channel), got: {codes:?}"
        );
    }
}

/// Public strings are unaffected — the loop is only a problem over secrets.
#[test]
fn public_str_eq_is_unaffected() {
    let source = "module main;\n\nfn cmp(a: str, b: str) -> i64 {\n\
                  \x20   let e = a == b;\n\
                  \x20   return 0;\n}\n";
    let codes = codes_for("public", source);
    assert!(
        !codes.contains(&"T033".to_string()),
        "T033 must not fire on @Public operands, got: {codes:?}"
    );
}

/// A `@SecretCT` scrutinee in a `match` is already rejected by CT004 / T023,
/// which fires first and returns early. Pinning this keeps the two rules from
/// silently swapping places and leaving a gap between them: if a future change
/// made T023 stop covering `str` scrutinees, this test fails rather than the
/// leak reopening quietly.
#[test]
fn a_secret_match_scrutinee_is_t023_not_t033() {
    let source = "module main;\n\nfn pick(s: str @SecretCT) -> i64 {\n\
                  \x20   match s {\n\
                  \x20       \"fn\" => { return 1; },\n\
                  \x20       _ => { return 0; },\n\
                  \x20   }\n}\n";
    let codes = codes_for("match_scrut", source);
    assert!(
        codes.contains(&"T023".to_string()),
        "a @SecretCT match scrutinee must fire T023 (CT004), got: {codes:?}"
    );
}
