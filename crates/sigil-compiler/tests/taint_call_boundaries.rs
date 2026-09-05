//! Compositional taint boundaries for ordinary calls and effect handlers.

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

#[test]
fn direct_call_rejects_secret_into_public_parameter() {
    let source = r#"#[ring(outer)] module ext;
fn identity(value: i64) -> i64 {
    return value;
}
fn leak(secret: i64 @Secret) -> i64 @Secret {
    return identity(secret);
}
"#;
    let err = compile_named_module("direct_call_public_param.sigil", source)
        .expect_err("a callee must not relabel a secret argument as public");
    assert_has_code(&err, "T001");
}

#[test]
fn direct_call_accepts_secret_into_secret_parameter() {
    let source = r#"#[ring(outer)] module ext;
fn identity(value: i64 @Secret) -> i64 @Secret {
    return value;
}
fn preserve(secret: i64 @Secret) -> i64 @Secret {
    return identity(secret);
}
"#;
    compile_named_module("direct_call_secret_param.sigil", source)
        .expect("matching caller and callee taint contracts should compile");
}

#[test]
fn direct_call_rejects_non_ct_secret_into_secretct_parameter() {
    let source = r#"#[ring(outer)] module ext;
fn constant_time(value: i64 @SecretCT) -> i64 @SecretCT ! {} {
    return value;
}
fn bad(secret: i64 @Secret) -> i64 @SecretCT ! {} {
    return constant_time(secret);
}
"#;
    let err = compile_named_module("direct_call_secretct_param.sigil", source)
        .expect_err("@Secret must not be upcast to a @SecretCT parameter");
    assert_has_code(&err, "T030");
}

#[test]
fn indirect_call_rejects_non_public_argument_without_taint_contract() {
    let source = r#"#[ring(outer)] module ext;
fn leak(secret: i64 @SecretCT) -> i64 @SecretCT ! {} {
    let choose = fn(value: i64) -> i64 {
        if value == 0 { return 1; } else { return 2; }
    };
    return choose(secret);
}
"#;
    let err = compile_named_module("indirect_call_erased_param.sigil", source)
        .expect_err("an erased closure parameter contract must accept only public arguments");
    assert_has_code(&err, "T001");
}

#[test]
fn closure_parameter_taint_is_enforced_inside_body() {
    let source = r#"#[ring(outer)] module ext;
fn define() -> i64 ! {} {
    let choose = fn(value: i64 @SecretCT) -> i64 {
        if value == 0 { return 1; } else { return 2; }
    };
    return 0;
}
"#;
    let err = compile_named_module("closure_param_secretct.sigil", source)
        .expect_err("a closure's declared @SecretCT parameter must remain @SecretCT in its body");
    assert_has_code(&err, "T020");
}

#[test]
fn extern_call_rejects_secret_argument() {
    let source = r#"#[ring(outer)] #[trusted] module ext;
extern "C" fn expose(value: i64) -> i64 ! { FFI, Unsafe };
fn leak(secret: i64 @Secret) -> i64 @Internal ! { FFI, Unsafe } {
    return expose(secret);
}
"#;
    let err = compile_named_module("extern_secret_arg.sigil", source)
        .expect_err("a secret value must not cross the @Internal FFI boundary");
    assert_has_code(&err, "T001");
}

#[test]
fn extern_call_accepts_internal_argument() {
    let source = r#"#[ring(outer)] #[trusted] module ext;
extern "C" fn expose(value: i64) -> i64 ! { FFI, Unsafe };
fn pass(value: i64 @Internal) -> i64 @Internal ! { FFI, Unsafe } {
    return expose(value);
}
"#;
    compile_named_module("extern_internal_arg.sigil", source)
        .expect("an @Internal value may cross the @Internal FFI boundary");
}

#[test]
fn legacy_handle_checks_every_nested_statement() {
    let source = r#"#[ring(outer)] module ext;
effect Audit;
fn leak(secret: i64 @Secret) -> i64 {
    handle Audit {
        let exposed: i64 @Public = secret;
    };
    return 0;
}
"#;
    let err = compile_named_module("handle_nested_taint.sigil", source)
        .expect_err("a handle block must not skip taint sinks before its final statement");
    assert_has_code(&err, "T001");
}

#[test]
fn region_checks_every_nested_statement() {
    let source = r#"#[ring(outer)] module ext;
fn leak(secret: i64 @Secret) -> i64 ! { Alloc } {
    region scratch(64) {
        let exposed: i64 @Public = secret;
    };
    return 0;
}
"#;
    let err = compile_named_module("region_nested_taint.sigil", source)
        .expect_err("a region block must not skip nested taint sinks");
    assert_has_code(&err, "T001");
}

#[test]
fn effect_perform_rejects_secret_into_public_parameter() {
    let source = r#"#[ring(outer)] module ext;
effect Echo { fn echo(value: i64) -> i64; }
fn source() -> i64 @Secret ! {} {
    return 7;
}
fn perform_echo() -> i64 @Secret ! { Echo } {
    let secret: i64 @Secret = source();
    return perform Echo.echo(secret);
}
fn run() -> i64 @Secret ! {} {
    return handle perform_echo() { Echo.echo(value) => resume value };
}
"#;
    let err = compile_named_module("effect_public_param.sigil", source)
        .expect_err("an effect operation must not relabel a secret payload as public");
    assert_has_code(&err, "T001");
}

#[test]
fn abortive_effect_clause_preserves_secret_parameter_taint() {
    let source = r#"#[ring(outer)] module ext;
effect Fail { fn raise(value: i64 @Secret) -> never; }
fn source() -> i64 @Secret ! {} {
    return 7;
}
fn fail() -> i64 ! { Fail } {
    let secret: i64 @Secret = source();
    perform Fail.raise(secret);
    return 0;
}
fn leak() -> i64 ! {} {
    return handle fail() { Fail.raise(value) => value };
}
"#;
    let err = compile_named_module("effect_clause_secret_param.sigil", source)
        .expect_err("a clause binder must retain the operation parameter's taint");
    assert_has_code(&err, "T001");
}

#[test]
fn abortive_effect_clause_checks_every_nested_statement() {
    let source = r#"#[ring(outer)] module ext;
effect Fail { fn raise(value: i64 @Secret) -> never; }
fn source() -> i64 @Secret ! {} {
    return 7;
}
fn fail() -> i64 ! { Fail } {
    let secret: i64 @Secret = source();
    perform Fail.raise(secret);
    return 0;
}
fn leak() -> i64 ! {} {
    return handle fail() {
        Fail.raise(value) => {
            let exposed: i64 @Public = value;
            0;
        }
    };
}
"#;
    let err = compile_named_module("effect_clause_nested_taint.sigil", source)
        .expect_err("an effect clause must not skip taint sinks before its final expression");
    assert_has_code(&err, "T001");
}

#[test]
fn abortive_effect_clause_accepts_matching_secret_return() {
    let source = r#"#[ring(outer)] module ext;
effect Fail { fn raise(value: i64 @Secret) -> never; }
fn source() -> i64 @Secret ! {} {
    return 7;
}
fn fail() -> i64 ! { Fail } {
    let secret: i64 @Secret = source();
    perform Fail.raise(secret);
    return 0;
}
fn preserve() -> i64 @Secret ! {} {
    return handle fail() { Fail.raise(value) => value };
}
"#;
    compile_named_module("effect_clause_secret_return.sigil", source)
        .expect("a secret clause result may flow to a secret return contract");
}
