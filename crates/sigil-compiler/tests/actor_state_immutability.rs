//! M2 (actor-state epic): state fields are a distinct `StateField` node —
//! writable ONLY in `init`, read-only in handlers, and a declared taint sink.
//!
//! These pin the type-check semantics; AIR/runtime persistence lands in later
//! milestones. See the plan `spicy-bubbling-lobster.md`.

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

// ── init is the sole write site ──

#[test]
fn init_may_assign_a_capability_state_field() {
    // `power = f` in `init` is the sanctioned construction-phase write — it
    // bypasses the T042 rebind gate and the T043 cap-linearity gate that reject
    // the same shape in ordinary code.
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { power: Fuel }
    init(f: Fuel) { power = f; }
    on Use() { let e: i64 = grant(&power, fn(c: &Fuel) -> i64 { return 1; }); }
}
"#;
    compile_named_module("state_init_cap.sigil", source)
        .expect("init assigning a cap state field should compile");
}

#[test]
fn init_may_assign_a_data_state_field_from_a_literal() {
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { n: i64 }
    init(f: Fuel) { n = 0; }
    on Get() -> i64 { return n; }
}
"#;
    compile_named_module("state_init_data.sigil", source)
        .expect("init assigning a data state field from a literal should compile");
}

// ── handlers are read-only (T123) ──

#[test]
fn handler_assigning_state_is_rejected() {
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { n: i64 }
    init(f: Fuel) { n = 0; }
    on Set(v: i64) { n = v; }
}
"#;
    let err = compile_named_module("state_handler_write.sigil", source)
        .expect_err("assigning state in a handler should fail T123");
    assert_has_code(&err, "T123");
}

#[test]
fn handler_may_read_state() {
    // A read is always fine — the same fixture minus the write compiles.
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { n: i64 }
    init(f: Fuel) { n = 0; }
    on Get() -> i64 { return n + 1; }
}
"#;
    compile_named_module("state_handler_read.sigil", source)
        .expect("reading state in a handler should compile");
}

// ── state is a declared taint sink (anti-laundering) ──

#[test]
fn init_storing_secret_into_public_state_is_rejected() {
    // The forced-audit hole: an actor state field is @Public (fields carry no
    // taint annotation) and handlers read it back at that label, so storing a
    // @Secret value into it in `init` would launder the secret across the
    // immutable-state boundary. Rejected as a T001 downgrade.
    let source = r#"module sigil;
cap type Fuel {}
actor Worker {
    state { n: i64 }
    init(s: i64 @Secret) { n = s; }
    on Get() -> i64 { return n; }
}
"#;
    let err = compile_named_module("state_launder.sigil", source)
        .expect_err("storing @Secret into @Public state should fail T001");
    assert_has_code(&err, "T001");
}

// ── a binding may not shadow a state field (N006) ──

#[test]
fn let_shadowing_a_state_field_is_rejected() {
    // Without this, a bare name after the shadowing `let` would ambiguously
    // denote the local or the field. Fail-closed, mirroring the param rule.
    let source = r#"module sigil;
cap type Fuel {}
actor Worker {
    state { n: i64 }
    init(f: Fuel) { n = 0; }
    on Get() -> i64 { let n = 99; return n; }
}
"#;
    let err = compile_named_module("state_shadow.sigil", source)
        .expect_err("a let shadowing a state field should fail N006");
    assert_has_code(&err, "N006");
}
