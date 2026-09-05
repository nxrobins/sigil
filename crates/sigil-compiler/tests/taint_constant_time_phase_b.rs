//! Phase 2H Phase B — `declassify_ct` + CT intrinsics tests.
//!
//! Covers the @SecretCT → @Secret → @Public two-step declassification
//! ladder, the three branch-free CT intrinsics (`ct_eq`, `ct_select`,
//! `ct_lt`), and basic input-validation diagnostics.

use sigil_compiler::CompileError;
use sigil_compiler::compile_named_module;

fn assert_has_code(err: &CompileError, code: &str) {
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&code),
        "expected diagnostic {code} but got: {:?}",
        err.diagnostics()
    );
}

// ── declassify_ct two-step chain ──

#[test]
fn declassify_ct_chain_compiles() {
    // @SecretCT → @Secret → @Public via declassify_ct + declassify, each
    // consuming its own linear capability.
    let source = r#"module ext;
cap type DeclassifyCT {}
cap type Declassify {}
fn f(s: i64 @SecretCT, c: DeclassifyCT, d: Declassify) -> i64 @Public {
    let mid: i64 @Secret = declassify_ct(s, c);
    return declassify(mid, d);
}
"#;
    compile_named_module("phase_b_chain.sigil", source)
        .expect("declassify_ct then declassify should compile");
}

#[test]
fn declassify_ct_rejects_wrong_cap_type() {
    let source = r#"module ext;
cap type DeclassifyCT {}
cap type Declassify {}
fn f(s: i64 @SecretCT, c: Declassify) -> i64 @Secret {
    return declassify_ct(s, c);
}
"#;
    let err = compile_named_module("phase_b_wrong_cap.sigil", source)
        .expect_err("declassify_ct with wrong cap type should be rejected");
    // T110 is main's existing cap-type-mismatch code (shared with declassify).
    assert_has_code(&err, "T110");
}

#[test]
fn declassify_ct_rejects_non_secret_ct_input() {
    // declassify_ct on @Public/@Internal/@Secret is rejected (T032).
    // Users should use plain `declassify` for @Secret → @Public.
    let source = r#"module ext;
cap type DeclassifyCT {}
fn f(s: i64 @Secret, c: DeclassifyCT) -> i64 @Secret {
    return declassify_ct(s, c);
}
"#;
    let err = compile_named_module("phase_b_non_ct_input.sigil", source)
        .expect_err("declassify_ct on non-@SecretCT value should be rejected");
    assert_has_code(&err, "T032");
}

// ── CT011: declassify capability linearity (F002 regression) ──
//
// `declassify`/`declassify_ct` consume a LINEAR capability — spec
// `secret-ct.md` §3.4 ("one use per construction") and the CT011 attack row
// ("declassify_ct cap reused → O001"). Before F002 the AIR lowering dropped
// the cap operand entirely, so the ownership pass never saw it and a single
// owned cap could declassify unbounded secrets with a clean compile. These
// pin the reuse → O001 contract; `declassify_ct_chain_compiles` above is the
// paired positive (each cap used exactly once still compiles).

#[test]
fn declassify_cap_reuse_rejected() {
    // One owned `Declassify` cap, two `declassify` calls → O001.
    let source = r#"module ext;
cap type Declassify {}
fn f(s1: i64 @Secret, s2: i64 @Secret, d: Declassify) -> i64 @Public {
    let _a: i64 @Public = declassify(s1, d);
    return declassify(s2, d);
}
"#;
    let err = compile_named_module("f002_declassify_reuse.sigil", source)
        .expect_err("reusing one Declassify cap for two declassify calls must be rejected");
    assert_has_code(&err, "O001");
}

#[test]
fn declassify_ct_cap_reuse_rejected() {
    // One owned `DeclassifyCT` cap, two `declassify_ct` calls → O001.
    let source = r#"module ext;
cap type DeclassifyCT {}
fn f(s1: i64 @SecretCT, s2: i64 @SecretCT, c: DeclassifyCT) -> i64 @Secret {
    let _mid: i64 @Secret = declassify_ct(s1, c);
    return declassify_ct(s2, c);
}
"#;
    let err = compile_named_module("f002_declassify_ct_reuse.sigil", source)
        .expect_err("reusing one DeclassifyCT cap for two declassify_ct calls must be rejected");
    assert_has_code(&err, "O001");
}

#[test]
fn declassify_then_pass_cap_rejected() {
    // Sharper control: `declassify` must actually CONSUME its cap. After a
    // declassify, passing the same cap to any callee is a use-after-move.
    // Pre-F002 this compiled clean (declassify consumed nothing, so the call
    // looked like the first move).
    let source = r#"module ext;
cap type Declassify {}
fn take(d: Declassify) -> i64 @Public { return 0; }
fn f(s1: i64 @Secret, d: Declassify) -> i64 @Public {
    let _a: i64 @Public = declassify(s1, d);
    return take(d);
}
"#;
    let err = compile_named_module("f002_declassify_then_pass.sigil", source)
        .expect_err("using a Declassify cap after declassify consumed it must be rejected");
    assert_has_code(&err, "O001");
}

// ── CT017 reconfirmed under Phase B ──

#[test]
fn ct017_declassify_of_secret_ct_input_rejected() {
    // The existing `declassify` rejects @SecretCT inputs; the user
    // must run declassify_ct first (T031 / CT017).
    let source = r#"module ext;
cap type Declassify {}
fn f(s: i64 @SecretCT, c: Declassify) -> i64 @Public {
    return declassify(s, c);
}
"#;
    let err = compile_named_module("phase_b_ct017.sigil", source)
        .expect_err("declassify of @SecretCT input should be rejected (CT017 / T031)");
    assert_has_code(&err, "T031");
}

// ── CT intrinsics: positive ──

#[test]
fn ct_eq_on_secret_ct_compiles() {
    let source = r#"#[ring(outer)] module ext;
fn cmp(a: i64 @SecretCT, b: i64 @SecretCT) -> bool @SecretCT ! {} {
    return ct_eq(a, b);
}
"#;
    compile_named_module("phase_b_ct_eq.sigil", source).expect("ct_eq on @SecretCT should compile");
}

#[test]
fn ct_select_on_secret_ct_compiles() {
    let source = r#"#[ring(outer)] module ext;
fn pick(c: bool @SecretCT, t: i64 @SecretCT, f: i64 @SecretCT) -> i64 @SecretCT ! {} {
    return ct_select(c, t, f);
}
"#;
    compile_named_module("phase_b_ct_select.sigil", source)
        .expect("ct_select on @SecretCT should compile");
}

#[test]
fn ct_lt_on_secret_ct_compiles() {
    let source = r#"#[ring(outer)] module ext;
fn less(a: i64 @SecretCT, b: i64 @SecretCT) -> bool @SecretCT ! {} {
    return ct_lt(a, b);
}
"#;
    compile_named_module("phase_b_ct_lt.sigil", source).expect("ct_lt on @SecretCT should compile");
}

// ── CT intrinsics: negative ──

#[test]
fn ct_eq_wrong_arity_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(a: i64 @SecretCT) -> bool @SecretCT ! {} {
    return ct_eq(a);
}
"#;
    let err = compile_named_module("phase_b_ct_eq_arity.sigil", source)
        .expect_err("ct_eq with 1 arg should be rejected");
    // T074 is the existing arity-mismatch code for intrinsics.
    assert_has_code(&err, "T074");
}

#[test]
fn ct_select_wrong_cond_type_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(c: i64 @SecretCT, t: i64 @SecretCT, e: i64 @SecretCT) -> i64 @SecretCT ! {} {
    return ct_select(c, t, e);
}
"#;
    let err = compile_named_module("phase_b_ct_select_cond.sigil", source)
        .expect_err("ct_select with i64 cond should be rejected");
    // T075 is the existing per-intrinsic arg-type code.
    assert_has_code(&err, "T075");
}
