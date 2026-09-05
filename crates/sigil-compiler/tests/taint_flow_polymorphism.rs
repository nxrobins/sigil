//! Taint polymorphism (`@Flow`): a signature that quantifies over @Public,
//! @Internal and @Secret at once, so a codec can accept classified input and
//! return it at the SAME classification — never refusing it, never laundering it.
//!
//! The load-bearing claim is that skipping the call-site parameter check for a
//! `@Flow` position is sound. It is sound only because the callee's body is
//! re-verified once per admissible label, so the leak tests below are the real
//! subject of this file; the acceptance tests only show the feature does its job.

use sigil_compiler::{CompileError, compile_named_module};

fn assert_has_code(err: &CompileError, code: &str) {
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    assert!(
        codes.contains(&code),
        "expected diagnostic {code}, got {:?}",
        err.diagnostics()
    );
}

fn assert_mentions(err: &CompileError, needle: &str) {
    let found = err
        .diagnostics()
        .iter()
        .any(|d| d.message().contains(needle));
    assert!(
        found,
        "expected a diagnostic mentioning {needle:?}, got {:?}",
        err.diagnostics()
    );
}

// ── The feature ────────────────────────────────────────────────────────────

#[test]
fn flow_parameter_accepts_every_admissible_label() {
    let source = r#"#[ring(outer)] module ext;
fn passthrough(value: i64 @Flow) -> i64 @Flow {
    return value;
}
fn public_caller(value: i64) -> i64 {
    return passthrough(value);
}
fn internal_caller(value: i64 @Internal) -> i64 @Internal {
    return passthrough(value);
}
fn secret_caller(value: i64 @Secret) -> i64 @Secret {
    return passthrough(value);
}
"#;
    compile_named_module("flow_accepts_all.sigil", source)
        .expect("a @Flow parameter accepts @Public, @Internal and @Secret alike");
}

#[test]
fn flow_return_follows_the_argument_label() {
    // The result of a @Flow call is NOT laundered to @Public: an @Internal
    // argument must come back out @Internal, so a @Public return rejects it.
    let source = r#"#[ring(outer)] module ext;
fn passthrough(value: i64 @Flow) -> i64 @Flow {
    return value;
}
fn launder(value: i64 @Internal) -> i64 @Public {
    return passthrough(value);
}
"#;
    let err = compile_named_module("flow_return_follows.sigil", source)
        .expect_err("@Flow must propagate the argument's label to the result");
    assert_has_code(&err, "T001");
}

#[test]
fn flow_return_follows_the_secret_argument_label() {
    let source = r#"#[ring(outer)] module ext;
fn passthrough(value: i64 @Flow) -> i64 @Flow {
    return value;
}
fn launder(value: i64 @Secret) -> i64 @Internal {
    return passthrough(value);
}
"#;
    let err = compile_named_module("flow_return_follows_secret.sigil", source)
        .expect_err("@Flow must propagate @Secret to the result");
    assert_has_code(&err, "T001");
}

#[test]
fn flow_result_is_public_for_a_public_argument() {
    // The other direction: polymorphism must not UPGRADE a public value into a
    // permanently-classified one, or every caller would need declassification.
    let source = r#"#[ring(outer)] module ext;
fn passthrough(value: i64 @Flow) -> i64 @Flow {
    return value;
}
fn stays_public(value: i64) -> i64 @Public {
    return passthrough(value);
}
"#;
    compile_named_module("flow_public_stays_public.sigil", source)
        .expect("a @Public argument yields a @Public result");
}

#[test]
fn flow_joins_multiple_arguments() {
    // With one @Internal argument among several, the result is @Internal.
    let source = r#"#[ring(outer)] module ext;
fn combine(a: i64 @Flow, b: i64 @Flow) -> i64 @Flow {
    return a + b;
}
fn join(pubv: i64, secret: i64 @Internal) -> i64 @Public {
    return combine(pubv, secret);
}
"#;
    let err = compile_named_module("flow_join.sigil", source)
        .expect_err("the result must carry the join of the @Flow arguments");
    assert_has_code(&err, "T001");
}

// ── Why skipping the call-site parameter check is sound ────────────────────

#[test]
fn flow_body_that_leaks_into_a_public_callee_is_rejected() {
    // `sink` fixes its parameter at @Public. Passing a @Flow value to it is
    // fine at the @Public instantiation and a leak at the other two, so the
    // per-instantiation check must reject the definition itself.
    let source = r#"#[ring(outer)] module ext;
fn sink(value: i64 @Public) -> i64 @Public {
    return value;
}
fn leaky(value: i64 @Flow) -> i64 @Flow {
    return sink(value);
}
"#;
    let err = compile_named_module("flow_leak_public_callee.sigil", source)
        .expect_err("a @Flow body must not pass its polymorphic value to a @Public parameter");
    assert_has_code(&err, "T001");
    assert_mentions(&err, "@Internal instantiation");
}

#[test]
fn flow_body_that_launders_through_a_public_local_is_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn leaky(value: i64 @Flow) -> i64 @Flow {
    let laundered: i64 @Public = value;
    return laundered;
}
"#;
    let err = compile_named_module("flow_leak_public_local.sigil", source)
        .expect_err("an explicit @Public local must still be a sink inside a @Flow body");
    assert_has_code(&err, "T001");
    assert_mentions(&err, "@Internal instantiation");
}

#[test]
fn flow_parameter_with_public_return_is_rejected() {
    // Declaring `@Flow` inputs but a fixed `@Public` result is a laundering
    // signature; it must fail at the first non-public instantiation.
    let source = r#"#[ring(outer)] module ext;
fn launder(value: i64 @Flow) -> i64 @Public {
    return value;
}
"#;
    let err = compile_named_module("flow_public_return.sigil", source)
        .expect_err("@Flow input with a @Public return is laundering");
    assert_has_code(&err, "T001");
}

#[test]
fn leak_is_reported_once_not_once_per_instantiation() {
    let source = r#"#[ring(outer)] module ext;
fn sink(value: i64 @Public) -> i64 @Public {
    return value;
}
fn leaky(value: i64 @Flow) -> i64 @Flow {
    return sink(value);
}
"#;
    let err = compile_named_module("flow_leak_once.sigil", source)
        .expect_err("the leaky definition must be rejected");
    let t001s = err
        .diagnostics()
        .iter()
        .filter(|d| d.code().as_str() == "T001")
        .count();
    assert_eq!(
        t001s,
        1,
        "a leak should be reported for the first failing instantiation only, got {:?}",
        err.diagnostics()
    );
}

// ── @SecretCT is outside the quantifier ────────────────────────────────────

#[test]
fn flow_parameter_rejects_secretct_argument() {
    // @Flow quantifies over @Public/@Internal/@Secret. Constant-time is a
    // property of the callee's CODE, which a @Flow body was never checked for,
    // so a @SecretCT argument must be refused rather than silently accepted.
    let source = r#"#[ring(outer)] module ext;
fn passthrough(value: i64 @Flow) -> i64 @Flow {
    return value;
}
fn ct_caller(value: i64 @SecretCT) -> i64 @SecretCT ! {} {
    return passthrough(value);
}
"#;
    let err = compile_named_module("flow_rejects_ct.sigil", source)
        .expect_err("@Flow does not quantify over @SecretCT");
    assert_has_code(&err, "T030");
}

// ── Declaration-site rules ─────────────────────────────────────────────────

#[test]
fn flow_return_without_flow_parameter_is_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn nothing_flows(value: i64 @Internal) -> i64 @Flow {
    return value;
}
"#;
    let err = compile_named_module("flow_no_input.sigil", source)
        .expect_err("a @Flow return needs a @Flow parameter to follow");
    assert_has_code(&err, "P021");
}

#[test]
fn flow_and_concrete_label_on_one_parameter_is_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn contradiction(value: i64 @Flow @Secret) -> i64 @Flow {
    return value;
}
"#;
    let err = compile_named_module("flow_contradiction.sigil", source)
        .expect_err("a parameter carries one label contract, not two");
    assert_has_code(&err, "P021");
}

#[test]
fn flow_on_a_generic_function_is_rejected() {
    // Generic functions reach the taint checker through monomorphization,
    // which rebuilds their params and would drop the marker. Reject rather
    // than let the contract degrade silently to @Public.
    let source = r#"#[ring(outer)] module ext;
fn passthrough<T>(value: i64 @Flow, other: T) -> i64 @Flow {
    return value;
}
"#;
    let err = compile_named_module("flow_generic.sigil", source)
        .expect_err("@Flow is not supported on generic functions");
    assert_has_code(&err, "P021");
}

#[test]
fn flow_on_an_extern_declaration_is_rejected() {
    let source = r#"#[ring(outer)] #[trusted] module ext;
extern "C" fn host_call(value: i32 @Flow) -> i64 ! { FFI, Unsafe };
"#;
    let err = compile_named_module("flow_extern.sigil", source)
        .expect_err("@Flow needs a body to verify; an extern has none");
    assert_has_code(&err, "P021");
}

// ── The stdlib's actual use case ───────────────────────────────────────────

#[test]
fn internal_network_data_reaches_a_flow_codec_without_declassification() {
    // The shape that motivated all of this: an @Internal HTTP response parsed
    // by a @Flow codec, with the parsed field still @Internal afterwards and
    // no `declassify` anywhere in the data path.
    let source = r#"#[ring(outer)] #[trusted] module ext;
effect NetIO;
extern "C" fn http_get(url: i32, url_len: i32) -> i64 ! { FFI, Unsafe };

fn field_of(doc: i64 @Flow, len: i64 @Flow) -> i64 @Flow {
    let mut i: i64 = 0;
    while i < len {
        i += 1;
    }
    return doc + i;
}

pub fn fetch_and_parse(url: i32, url_len: i32) -> i64 @Internal ! { NetIO, FFI, Unsafe } {
    let packed: i64 @Internal = http_get(url, url_len);
    return field_of(packed, 8);
}
"#;
    compile_named_module("flow_network_codec.sigil", source)
        .expect("an @Internal response must reach a @Flow codec without declassification");
}
