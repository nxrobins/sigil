//! High-confidence machine-applicable `suggested_edits` for the only two
//! edit-shaped codes the bench hits: P001 (insert the expected punctuation
//! token) and N007 (replace a typo'd module with the nearest one).
//!
//! Positive AND negative, enforcing the ritual gates:
//!   E1 — only the punctuation allowlist gets an insert edit; a class
//!        expectation (`expect_type`/`expect_ident`) gets none.
//!   E3 — N007 emits a replace edit only for a distance-≤1 typo; a genuinely
//!        absent module gets none.

use sigil_compiler::compile_named_module;

#[test]
fn p001_punctuation_carries_insert_edit() {
    // Missing `;` after `let x = 5` → `expect_semicolon` fires P001 with an
    // insert edit for the literal `;` (empty span = pure insertion).
    let err = compile_named_module(
        "p001_semi.sigil",
        "module sigil; fn boot() -> i64 { let x = 5 return x; }",
    )
    .expect_err("source should fail to parse");
    let diag = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "P001" && d.suggested_edits().is_some())
        .expect("a punctuation P001 carrying an insert edit");
    let edits = diag.suggested_edits().expect("edits present");
    assert_eq!(edits.len(), 1, "one edit per diagnostic");
    assert_eq!(edits[0].replacement, ";");
    assert_eq!(edits[0].start, edits[0].end, "insert edit is an empty span");
}

#[test]
fn p001_class_expectation_has_no_edit() {
    // `-> 99` expects a TYPE (a class, not a literal); the first P001 must
    // carry no edit — `expect_type` cannot reach `p001_expecting` (E1).
    let err = compile_named_module(
        "p001_type.sigil",
        "module sigil; fn boot() -> 99 { return 0; }",
    )
    .expect_err("source should fail to parse");
    let first_p001 = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "P001")
        .expect("expected a P001");
    assert!(
        first_p001.suggested_edits().is_none(),
        "a class-expectation P001 must carry no suggested edit (E1)"
    );
}

#[test]
fn n007_close_module_typo_carries_replace_edit() {
    // `fop` is a 1-edit typo of the present module `foo` → N007 carries a
    // replace edit to the corrected full path.
    let src = "module foo; fn a() -> i64 { return 0; }\n\
               module main; use sigil::fop; fn boot() -> i64 { return 0; }";
    let err = compile_named_module("n007_edit.sigil", src).expect_err("should fail");
    let diag = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "N007")
        .expect("expected N007");
    let edits = diag
        .suggested_edits()
        .expect("a close module typo carries a replace edit (E3)");
    assert_eq!(edits.len(), 1);
    assert_eq!(edits[0].replacement, "sigil::foo");
    assert!(edits[0].start < edits[0].end, "replace edit spans the path");
}

#[test]
fn n007_absent_module_has_no_edit() {
    // `nonexistent` is far from any present module → no rename anchor (E3).
    let src = "module main; use sigil::nonexistent; fn boot() -> i64 { return 0; }";
    let err = compile_named_module("n007_noedit.sigil", src).expect_err("should fail");
    let diag = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "N007")
        .expect("expected N007");
    assert!(
        diag.suggested_edits().is_none(),
        "a genuinely-absent module must get no edit (E3)"
    );
}
