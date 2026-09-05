//! Phase 2H — Constant-time discipline (`@SecretCT`) attack inventory.
//!
//! Each test compiles a fixture that violates one CT rule and asserts the
//! correct `Txxx` (CT001–CT017) diagnostic fires. Positive tests confirm
//! the discipline accepts the legitimate shapes. See
//! `docs/specs/secret-ct.md` for the full discipline.
//!
//! Code mapping (spec name → main's `codes::` constant):
//!   CT001 → T020   CT002 → T021   CT003 → T022   CT004 → T023
//!   CT005 → T024   CT006 → T025   CT007 → T026   CT010 → T027
//!   CT014 → T028   CT015 → T029   CT016 → T030   CT017 → T031
//!   CT008/CT009 spec-reserved (no current language surface).

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

// ── Positive tests ──

#[test]
fn ct_parser_accepts_secret_ct_annotation() {
    let source = r#"#[ring(outer)] module ext;
fn f(a: i64 @SecretCT) -> i64 @SecretCT ! {} {
    return a;
}
"#;
    compile_named_module("ct_positive_basic.sigil", source)
        .expect("@SecretCT annotation should parse and pass-through should compile");
}

#[test]
fn ct_public_to_secret_ct_upcast_allowed() {
    // E1: @Public → @SecretCT is permitted (literals, constants, masks).
    let source = r#"#[ring(outer)] module ext;
fn f() -> i64 @SecretCT ! {} {
    let mask: i64 @SecretCT = 255;
    return mask;
}
"#;
    compile_named_module("ct_public_upcast.sigil", source)
        .expect("@Public → @SecretCT upcast should compile (E1)");
}

// ── CT001 — secret-dependent branch ──

#[test]
fn ct001_if_on_secret_ct_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(cond: bool @SecretCT) -> i64 ! {} {
    if cond { return 1; } else { return 0; }
}
"#;
    let err = compile_named_module("ct001_if.sigil", source)
        .expect_err("`if` on @SecretCT should be rejected (CT001 / T020)");
    assert_has_code(&err, "T020");
}

// ── CT002 — secret-dependent loop ──

#[test]
fn ct002_while_on_secret_ct_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(cond: bool @SecretCT) -> i64 ! {} {
    while cond { return 1; }
    return 0;
}
"#;
    let err = compile_named_module("ct002_while.sigil", source)
        .expect_err("`while` on @SecretCT should be rejected (CT002 / T021)");
    assert_has_code(&err, "T021");
}

#[test]
fn ct002_while_guard_tainted_inside_loop_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(secret: bool @SecretCT) -> i64 ! {} {
    let mut cond: bool = true;
    while cond {
        cond = secret;
    }
    return 0;
}
"#;
    let err = compile_named_module("ct002_loop_carried_guard.sigil", source).expect_err(
        "a loop-carried @SecretCT guard must be rejected on re-evaluation (CT002 / T021)",
    );
    assert_has_code(&err, "T021");
}

// ── CT005 — secret-dependent index ──

#[test]
fn ct005_index_by_secret_ct_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(i: i64 @SecretCT) -> i64 @SecretCT ! {} {
    let arr = [1, 2, 3, 4];
    return arr[i];
}
"#;
    let err = compile_named_module("ct005_index.sigil", source)
        .expect_err("arr[i] with i @SecretCT should be rejected (CT005 / T024)");
    assert_has_code(&err, "T024");
}

// ── CT006 — secret-dependent address ──

#[test]
fn ct006_load_from_secret_ct_pointer_rejected_without_formal_preemption() {
    let source = r#"#[ring(outer)] module ext;
fn f(ptr: i64 @SecretCT) -> i64 @SecretCT ! {} {
    return load8(ptr);
}
"#;
    let err = compile_named_module("ct006_address.sigil", source)
        .expect_err("load8(ptr) with ptr @SecretCT should be rejected (CT006 / T025)");
    assert_has_code(&err, "T025");
    assert!(
        err.diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.code().as_str() != "I013"),
        "the v8 address policy must agree with the established T025 diagnostic"
    );
}

// ── CT007 — variable-time division ──

#[test]
fn ct007_div_with_secret_ct_operand_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(a: i64 @SecretCT, b: i64) -> i64 @SecretCT ! {} {
    return a / b;
}
"#;
    let err = compile_named_module("ct007_div.sigil", source)
        .expect_err("`a / b` with @SecretCT operand should be rejected (CT007 / T026)");
    assert_has_code(&err, "T026");
}

// ── CT015 — secret-dependent allocation size ──

#[test]
fn ct015_alloc_with_secret_ct_size_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(n: i64 @SecretCT) -> i64 ! { Alloc } {
    let p = alloc(n);
    return p;
}
"#;
    let err = compile_named_module("ct015_alloc.sigil", source)
        .expect_err("alloc(n) with n @SecretCT should be rejected (CT015 / T029)");
    assert_has_code(&err, "T029");
}

#[test]
fn ct015_region_with_secret_ct_size_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(n: i64 @SecretCT) ! {} {
    region scratch(n) { let x: i64 = 0; };
    return;
}
"#;
    let err = compile_named_module("ct015_region.sigil", source)
        .expect_err("region(n) with n @SecretCT should be rejected (CT015 / T029)");
    assert_has_code(&err, "T029");
}

// ── CT016 — source-of-CT (E1) upcast block ──

#[test]
fn ct016_internal_to_secret_ct_upcast_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(x: i64 @Internal) -> i64 @SecretCT ! {} {
    let y: i64 @SecretCT = x;
    return y;
}
"#;
    let err = compile_named_module("ct016_internal.sigil", source)
        .expect_err("@Internal → @SecretCT upcast should be rejected (CT016 / T030)");
    assert_has_code(&err, "T030");
}

#[test]
fn ct016_secret_to_secret_ct_upcast_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(x: i64 @Secret) -> i64 @SecretCT ! {} {
    let y: i64 @SecretCT = x;
    return y;
}
"#;
    let err = compile_named_module("ct016_secret.sigil", source)
        .expect_err("@Secret → @SecretCT upcast should be rejected (CT016 / T030)");
    assert_has_code(&err, "T030");
}

// ── CT012 — closure capture CT propagation (E4 / §3.7) ──

#[test]
fn ct012_closure_capturing_secret_ct_branch_rejected() {
    // The closure body branches on a captured @SecretCT value. The CT pass
    // propagates capture taints into the synthesized closure's TypedFunction,
    // so the inner `if` fires CT001 (T020) — only possible if §3.7 ran.
    let source = r#"#[ring(outer)] module ext;
fn f(secret: bool @SecretCT) -> i64 ! {} {
    let g = fn() -> i64 { if secret { return 1; } else { return 0; } };
    return 0;
}
"#;
    let err = compile_named_module("ct012_closure.sigil", source)
        .expect_err("closure capturing @SecretCT and branching should be rejected (CT012 / T020)");
    assert_has_code(&err, "T020");
}

// ── Actor-param taint propagation (pre-existing limitation fix) ──

#[test]
fn actor_handler_honors_secret_ct_param_annotation() {
    // Verifies the fix at `type_check.rs` for actor handler params:
    // source-declared `@SecretCT` is now propagated, so an `if` on the
    // param fires CT001 (T020) — only possible if the source taint
    // wasn't downgraded to @Public during type checking.
    let source = r#"module sigil;
cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }
    init(f: Fuel) {}

    on Process(secret: bool @SecretCT) -> i64 {
        if secret { return 1; } else { return 0; }
    }
}
"#;
    let err = compile_named_module("actor_handler_taint.sigil", source)
        .expect_err("branching on @SecretCT handler param should fail CT001 / T020");
    assert_has_code(&err, "T020");
}

#[test]
fn actor_init_honors_secret_ct_param_annotation() {
    let source = r#"module sigil;
cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }
    init(f: Fuel, secret: bool @SecretCT) {
        if secret { let _ = 1; } else { let _ = 0; }
    }
}
"#;
    let err = compile_named_module("actor_init_taint.sigil", source)
        .expect_err("branching on @SecretCT init param should fail CT001 / T020");
    assert_has_code(&err, "T020");
}

// ── F007 — plain @Secret payload launder across the actor boundary (T001) ──
//
// `send`/`ask` deliver payload args to the receiving handler's params, which
// bind at their DECLARED taint (default @Public). Without a boundary check a
// @Secret arg sent to a @Public param is silently laundered. See
// `docs/bug-hunt/FINDINGS.md` (F007).

#[test]
fn f007_send_secret_to_public_handler_param_rejected() {
    // The T7c exploit: a @Secret value is `send`-delivered to a handler whose
    // param is @Public (the default), laundering it inside the receiver.
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>, secret: i64 @Secret) -> i64 {
        worker.send(Deposit(secret));
        return 0;
    }
}
actor Worker {
    state { power: Fuel }
    init(f: Fuel) {}
    on Deposit(amount: i64) {}
}
"#;
    let err = compile_named_module("f007_send_launder.sigil", source)
        .expect_err("sending @Secret to a @Public handler param should fail T001 (F007)");
    assert_has_code(&err, "T001");
}

#[test]
fn f007_ask_secret_to_public_handler_param_rejected() {
    // Same launder on the `ask` request path.
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>, secret: i64 @Secret) -> i64 {
        let r: i64 = worker.ask(Query(secret), 100);
        return 0;
    }
}
actor Worker {
    init(fuel: Fuel) {}
    on Query(q: i64) -> i64 { return q; }
}
"#;
    let err = compile_named_module("f007_ask_launder.sigil", source)
        .expect_err("asking with @Secret to a @Public handler param should fail T001 (F007)");
    assert_has_code(&err, "T001");
}

#[test]
fn f007_send_public_to_public_handler_param_accepted() {
    // Legitimate: a @Public payload flows to a @Public param — must compile.
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>, pub_val: i64) -> i64 {
        worker.send(Deposit(pub_val));
        return 0;
    }
}
actor Worker {
    state { power: Fuel }
    init(f: Fuel) {}
    on Deposit(amount: i64) {}
}
"#;
    compile_named_module("f007_send_public_ok.sigil", source)
        .expect("sending @Public to a @Public handler param should compile (F007)");
}

#[test]
fn f007_send_secret_to_secret_handler_param_accepted() {
    // Legitimate: a @Secret payload flows to a handler param DECLARED @Secret —
    // the label is preserved, no launder. Must compile.
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>, secret: i64 @Secret) -> i64 {
        worker.send(Deposit(secret));
        return 0;
    }
}
actor Worker {
    state { power: Fuel }
    init(f: Fuel) {}
    on Deposit(amount: i64 @Secret) {}
}
"#;
    compile_named_module("f007_send_secret_ok.sigil", source)
        .expect("sending @Secret to a @Secret handler param should compile (F007)");
}
