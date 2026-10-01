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
//!   CT008 → T034 (a @SecretCT shift AMOUNT; the shifted VALUE is exempt —
//!   see the CT008 section. Until 2026-09-30 this compiled clean: measured
//!   2026-09-20 on main ae026aec, closed by T034.)
//!   CT009 is spec-"reserved" but the operators EXIST (`&&` `||`): it is
//!   enforced by CT001's rule (T020, see the CT009 section).
//!   CT013 rejects at the CALL boundary (T001), never with a CT code — see
//!   the CT013 section for the measured mechanism.

use std::collections::BTreeSet;

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

/// The EXACT code set of a rejection. The CT013/CT014/CT009/CT007-`%` tests
/// below pin the whole set, so a program rejected for an unrelated reason, or by
/// one more rule than the narrative names, fails instead of satisfying a
/// `contains`. Compiling at all is reported as a soundness hole, never as a
/// mismatch, so the failure direction of a regression is unmistakable.
fn reject_with_exact_codes(name: &str, source: &str, expected: &[&str], why: &str) -> CompileError {
    let err = match compile_named_module(name, source) {
        Ok(_) => panic!("SOUNDNESS HOLE: {why} — the program compiled\n--- source ---\n{source}"),
        Err(err) => err,
    };
    let got: BTreeSet<String> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect();
    let want: BTreeSet<String> = expected.iter().map(|c| (*c).to_string()).collect();
    assert_eq!(
        got,
        want,
        "{why}: exact code set mismatch\ngot: {:?}\n--- source ---\n{source}",
        err.diagnostics()
    );
    err
}

fn assert_accepted(name: &str, source: &str, why: &str) {
    if let Err(err) = compile_named_module(name, source) {
        panic!(
            "{why}\ngot rejection: {:?}\n--- source ---\n{source}",
            err.diagnostics()
        );
    }
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

// ── CT014 — `send` / `ask` with a @SecretCT payload or timeout (T028) ──
//
// Until 2026-09-20 CT014 was tested only in its `spawn` form
// (spawn_taint_sink.rs); the `send`/`ask` arms in taint_check.rs emitted T028
// with no test. The handler params below are DECLARED @SecretCT so the F007
// flow check has nothing to say and the actor-boundary rule is the only thing
// that can fire — the set is exactly {T028}, not "contains T028".

#[test]
fn ct014_send_secret_ct_payload_rejected() {
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>, s: i64 @SecretCT) -> i64 {
        worker.send(Deposit(s));
        return 0;
    }
}
actor Worker {
    state { power: Fuel }
    init(f: Fuel) {}
    on Deposit(amount: i64 @SecretCT) {}
}
"#;
    reject_with_exact_codes(
        "ct014_send.sigil",
        source,
        &["T028"],
        "a @SecretCT payload crossed the `send` boundary (CT014)",
    );
}

#[test]
fn ct014_send_secret_ct_payload_to_public_param_is_a_single_t028() {
    // Same send into a @Public param. `check_message_payload_taint` skips its
    // T001 for a CT arg by design ("a single T028 rather than a redundant
    // T001"), so the set stays exactly {T028} — pinned so a future change to
    // that skip shows up here as review content.
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>, s: i64 @SecretCT) -> i64 {
        worker.send(Deposit(s));
        return 0;
    }
}
actor Worker {
    state { power: Fuel }
    init(f: Fuel) {}
    on Deposit(amount: i64) {}
}
"#;
    reject_with_exact_codes(
        "ct014_send_public_param.sigil",
        source,
        &["T028"],
        "a @SecretCT payload crossed the `send` boundary into a @Public param (CT014)",
    );
}

#[test]
fn ct014_ask_secret_ct_payload_rejected() {
    // The ask RESULT carries the payload taint (args ⊔ timeout), so it is bound
    // at @SecretCT here; binding it @Public would add T001s that are about the
    // binding, not the boundary.
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>, s: i64 @SecretCT) -> i64 {
        let r: i64 @SecretCT = worker.ask(Query(s), 100);
        return 0;
    }
}
actor Worker {
    init(fuel: Fuel) {}
    on Query(q: i64 @SecretCT) -> i64 { return 0; }
}
"#;
    reject_with_exact_codes(
        "ct014_ask_payload.sigil",
        source,
        &["T028"],
        "a @SecretCT payload crossed the `ask` boundary (CT014)",
    );
}

#[test]
fn ct014_ask_secret_ct_timeout_rejected() {
    // A @SecretCT TIMEOUT is its own channel: the wait length is observable.
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>, t: i64 @SecretCT) -> i64 {
        let r: i64 @SecretCT = worker.ask(Query(1), t);
        return 0;
    }
}
actor Worker {
    init(fuel: Fuel) {}
    on Query(q: i64) -> i64 { return q; }
}
"#;
    reject_with_exact_codes(
        "ct014_ask_timeout.sigil",
        source,
        &["T028"],
        "a @SecretCT timeout crossed the `ask` boundary (CT014)",
    );
}

#[test]
fn ct014_ask_public_payload_into_secret_ct_binding_accepted() {
    // Control for the two ask tests: the same shape with a @Public payload and
    // timeout must compile, so the rejections above are about the payload.
    let source = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>, s: i64) -> i64 {
        let r: i64 @SecretCT = worker.ask(Query(s), 100);
        return 0;
    }
}
actor Worker {
    init(fuel: Fuel) {}
    on Query(q: i64) -> i64 { return q; }
}
"#;
    assert_accepted(
        "ct014_ask_public_ok.sigil",
        source,
        "a @Public ask payload/timeout must compile (CT014 control)",
    );
}

// ── CT009 — short-circuit `&&` / `||` controlled by @SecretCT ──
//
// The spec row reads "Reserved; no current source operator", which is out of
// date: the parser builds `LogicalAnd`/`LogicalOr`, and the taint pass treats a
// @SecretCT LEFT operand as a secret-dependent branch (T020, CT001's code). A
// @SecretCT RIGHT operand is not a branch — only the public left operand decides
// whether it is evaluated — so it merely labels the result.

#[test]
fn ct009_short_circuit_with_secret_ct_left_operand_rejected() {
    for (name, op) in [("ct009_and.sigil", "&&"), ("ct009_or.sigil", "||")] {
        let source = format!(
            "#[ring(outer)] module ext;\n\
             fn g(c: bool @SecretCT, d: bool @SecretCT) -> bool @SecretCT ! {{}} {{\n\
                 return c {op} d;\n\
             }}\n"
        );
        reject_with_exact_codes(
            name,
            &source,
            &["T020"],
            "a @SecretCT left operand controlled a short-circuit (CT009)",
        );
    }
}

#[test]
fn ct009_short_circuit_with_secret_ct_right_operand_only_accepted() {
    let source = r#"#[ring(outer)] module ext;
fn g(c: bool, d: bool @SecretCT) -> bool @SecretCT ! {} {
    return c && d;
}
"#;
    assert_accepted(
        "ct009_rhs_only.sigil",
        source,
        "a public left operand decides the short-circuit; a @SecretCT right operand only labels the result (CT009 control)",
    );
}

// ── CT007 — `%` (Mod) with a @SecretCT operand is rejected by the FORMAL gate only ──
//
// The taint pass tests `b.op == Div`, so `%` on a @SecretCT operand yields no
// T026 even though the T026 registry hint promises "`/` and `%`". The program
// is still rejected: `formal::verify_with_context` queues a `DivRem` policy for
// `Div | Mod`, and the Lean-checked kernel refuses the CSIR. That refusal is
// surfaced as I013 — "internal compiler error … not a source policy
// diagnostic … please file an issue" — carrying `detail=26`, the DivRem
// policy's diagnostic number. Direction: CLOSED, wrong code. Pinned exactly so
// the day `%` gets its source-level T026 this set moves under review.

#[test]
fn ct007_rem_with_secret_ct_operand_rejected_only_by_formal_gate() {
    for (name, params) in [
        ("ct007_rem_lhs.sigil", "a: i64 @SecretCT, b: i64"),
        ("ct007_rem_rhs.sigil", "a: i64, b: i64 @SecretCT"),
        ("ct007_rem_u64.sigil", "a: u64 @SecretCT, b: u64"),
    ] {
        let ret = if params.starts_with("a: u64") {
            "u64"
        } else {
            "i64"
        };
        let source = format!(
            "#[ring(outer)] module ext;\n\
             fn h({params}) -> {ret} @SecretCT ! {{}} {{\n\
                 return a % b;\n\
             }}\n"
        );
        let err = reject_with_exact_codes(
            name,
            &source,
            &["I013"],
            "`%` with a @SecretCT operand compiled: the formal DivRem policy did not fire (CT007)",
        );
        // Tie the I013 to the DivRem policy (diagnostic number 26), not to
        // some other formal refusal that happens to share the code.
        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("detail=26")),
            "I013 was not the DivRem policy refusal: {:?}",
            err.diagnostics()
        );
    }
}

#[test]
fn ct007_rem_with_public_operands_accepted() {
    let source = r#"#[ring(outer)] module ext;
fn h(a: i64, b: i64) -> i64 ! {} {
    return a % b;
}
"#;
    assert_accepted(
        "ct007_rem_public.sigil",
        source,
        "`%` on @Public operands must compile (CT007 control: the DivRem policy is label-sensitive)",
    );
}

// ── CT013 — @SecretCT into a generic function: rejected at the CALL boundary ──
//
// Measured, not the spec's story. `type_check/expressions/calls.rs` rebuilds
// every parameter of a monomorphized instance with `taint: TaintLabel::Public`
// — the declared label is dropped, even a concrete `c: bool @SecretCT` — so the
// compositional call check rejects the @SecretCT argument with T001 before the
// instance body is ever checked with the label. Direction: CLOSED (no generic
// function can accept CT data at all), so nothing leaks; but the code is T001,
// never a T020–T031 CT code, and ATTACK-MATRIX.md's "monomorphization
// preserves taint" is not the mechanism that runs.

#[test]
fn ct013_generic_branch_on_secret_ct_argument_rejected_at_call_boundary() {
    // The body's `if c` would be CT001 if the label reached it; it does not.
    // The second T001 is the caller returning the @SecretCT-tainted result
    // from a @Public function — both are boundary diagnostics.
    let source = r#"#[ring(outer)] module ext;
fn br<T>(c: T @SecretCT) -> i64 ! {} {
    if c { return 1; } else { return 0; }
}
fn f(s: bool @SecretCT) -> i64 ! {} {
    return br(s);
}
"#;
    reject_with_exact_codes(
        "ct013_generic_branch.sigil",
        source,
        &["T001"],
        "a @SecretCT value reached a branch inside a monomorphized body (CT013)",
    );
}

#[test]
fn ct013_generic_concrete_secret_ct_param_label_is_dropped_at_monomorphization() {
    // The DETECTOR for the drop: the labelled param is CONCRETE (`bool`, not
    // `T`) and the body does nothing forbidden — it returns the value at the
    // same label. If monomorphization carried the declared label this would
    // compile; it is rejected because the instance declares `c` @Public.
    let source = r#"#[ring(outer)] module ext;
fn keep<T>(c: bool @SecretCT, x: T) -> bool @SecretCT ! {} {
    return c;
}
fn f(s: bool @SecretCT, p: i64) -> bool @SecretCT ! {} {
    return keep(s, p);
}
"#;
    reject_with_exact_codes(
        "ct013_generic_label_drop.sigil",
        source,
        &["T001"],
        "the instance carried the declared @SecretCT label (the drop in calls.rs was fixed — update the CT013 narrative)",
    );
}

#[test]
fn ct013_nongeneric_secret_ct_param_control_accepted() {
    // Control for the detector above: the SAME shape with no type parameter
    // compiles, so the T001 there is the monomorphization drop, not the
    // declared-@SecretCT parameter itself. If this ever fails, the detector's
    // T001 no longer isolates the generic path.
    let source = r#"#[ring(outer)] module ext;
fn keep(c: bool @SecretCT, x: i64) -> bool @SecretCT ! {} {
    return c;
}
fn f(s: bool @SecretCT, p: i64) -> bool @SecretCT ! {} {
    return keep(s, p);
}
"#;
    assert_accepted(
        "ct013_nongeneric_label_kept.sigil",
        source,
        "a non-generic fn keeps its declared @SecretCT parameter label (CT013 control)",
    );
}

#[test]
fn ct013_generic_passthrough_reaches_the_caller_ct_rule() {
    // The label survives the CALL (the result is @SecretCT), so a forbidden op
    // in the CALLER still fires its CT code on top of the two boundary T001s
    // (the pass and the @Public `let`). T020 for a branch, T024 for an index.
    let branch = r#"#[ring(outer)] module ext;
fn id<T>(x: T) -> T ! {} {
    return x;
}
fn f(s: bool @SecretCT) -> i64 ! {} {
    let c = id(s);
    if c { return 1; } else { return 0; }
}
"#;
    reject_with_exact_codes(
        "ct013_passthrough_branch.sigil",
        branch,
        &["T001", "T020"],
        "a @SecretCT value laundered through a generic identity reached a branch (CT013)",
    );
    let index = r#"#[ring(outer)] module ext;
fn id<T>(x: T) -> T ! {} {
    return x;
}
fn f(a: [i64; 4], i: i64 @SecretCT) -> i64 ! {} {
    let j = id(i);
    return a[j];
}
"#;
    reject_with_exact_codes(
        "ct013_passthrough_index.sigil",
        index,
        &["T001", "T024"],
        "a @SecretCT value laundered through a generic identity reached an index (CT013)",
    );
}

#[test]
fn ct013_generic_branch_on_public_argument_accepted() {
    // Control: the same generic shapes with @Public arguments compile, so the
    // T001s above are about the label, not the generics.
    let source = r#"#[ring(outer)] module ext;
fn br<T>(c: bool, x: T) -> i64 ! {} {
    if c { return 1; } else { return 0; }
}
fn id<T>(x: T) -> T ! {} {
    return x;
}
fn f(s: bool, p: i64) -> i64 ! {} {
    let c = id(s);
    if c { return br(c, p); } else { return 0; }
}
"#;
    assert_accepted(
        "ct013_generic_public_ok.sigil",
        source,
        "generic calls with @Public arguments must compile (CT013 control)",
    );
}

// ── CT008: variable shift by a @SecretCT AMOUNT (T034) ──
//
// A shift by a data-dependent count is variable-time on cores without a barrel
// shifter, so the AMOUNT (right operand) may not be @SecretCT. The VALUE being
// shifted is exempt: a shift by a @Public count has a count-only latency, and it
// is how constant-time code masks and rotates a secret. Until 2026-09-30 every
// rejection below compiled with an EMPTY diagnostic set (measured against main
// ae026aec with `sigil check --json`); the accepted controls were accepted on
// both binaries.

/// `fn f(a: T, n: T @SecretCT) -> T @SecretCT` returning `a <op> n`.
fn ct008_amount_secret_source(ty: &str, op: &str) -> String {
    format!(
        "#[ring(outer)] module ext;\nfn f(a: {ty}, n: {ty} @SecretCT) -> {ty} @SecretCT ! {{}} {{\n    return a {op} n;\n}}\n"
    )
}

#[test]
fn ct008_shl_by_secret_ct_amount_rejected() {
    reject_with_exact_codes(
        "ct008_shl_i64.sigil",
        &ct008_amount_secret_source("i64", "<<"),
        &["T034"],
        "a `<<` by a @SecretCT amount must be rejected (CT008)",
    );
}

#[test]
fn ct008_shr_by_secret_ct_amount_rejected() {
    reject_with_exact_codes(
        "ct008_shr_i64.sigil",
        &ct008_amount_secret_source("i64", ">>"),
        &["T034"],
        "a `>>` by a @SecretCT amount must be rejected (CT008)",
    );
}

#[test]
fn ct008_shift_by_secret_ct_amount_rejected_for_i32_and_u64() {
    // The rule is on the operator, not the width or signedness: every integer
    // type the type checker admits for `<<`/`>>` is covered.
    for ty in ["i32", "u64"] {
        for op in ["<<", ">>"] {
            reject_with_exact_codes(
                &format!(
                    "ct008_{ty}_{}.sigil",
                    if op == "<<" { "shl" } else { "shr" }
                ),
                &ct008_amount_secret_source(ty, op),
                &["T034"],
                &format!("a `{op}` on {ty} by a @SecretCT amount must be rejected (CT008)"),
            );
        }
    }
}

#[test]
fn ct008_shift_with_both_operands_secret_ct_rejected() {
    // Both operands secret is still exactly ONE T034: the value side adds no
    // second diagnostic, and no other rule fires.
    for op in ["<<", ">>"] {
        let source = format!(
            "#[ring(outer)] module ext;\nfn f(a: i64 @SecretCT, n: i64 @SecretCT) -> i64 @SecretCT ! {{}} {{\n    return a {op} n;\n}}\n"
        );
        reject_with_exact_codes(
            "ct008_both_secret.sigil",
            &source,
            &["T034"],
            &format!(
                "a `{op}` with both operands @SecretCT must be rejected once, for the amount (CT008)"
            ),
        );
    }
}

#[test]
fn ct008_secret_ct_value_shifted_by_public_amount_accepted() {
    // The exemption that makes the rule usable: masking/rotating a secret by a
    // public count is the constant-time idiom, and its latency depends on the
    // public count alone.
    for op in ["<<", ">>"] {
        let source = format!(
            "#[ring(outer)] module ext;\nfn f(a: i64 @SecretCT, n: i64) -> i64 @SecretCT ! {{}} {{\n    return a {op} n;\n}}\n"
        );
        assert_accepted(
            "ct008_value_secret_amount_public.sigil",
            &source,
            &format!(
                "a @SecretCT value shifted by a @Public amount must compile (CT008 exempts the value side, `{op}`)"
            ),
        );
    }
}

#[test]
fn ct008_public_shift_accepted() {
    for op in ["<<", ">>"] {
        let source = format!(
            "#[ring(outer)] module ext;\nfn f(a: i64, n: i64) -> i64 ! {{}} {{\n    return a {op} n;\n}}\n"
        );
        assert_accepted(
            "ct008_public_public.sigil",
            &source,
            &format!("a shift with @Public operands must compile (CT008 control, `{op}`)"),
        );
    }
}

#[test]
fn ct008_secret_non_ct_amount_is_not_a_ct_violation() {
    // Control for the lattice level: CT008 is a `@SecretCT` rule. A plain
    // `@Secret` amount is confidentiality-tracked, not timing-tracked, and
    // compiles (as on main).
    let source = r#"#[ring(outer)] module ext;
fn f(a: i64, n: i64 @Secret) -> i64 @Secret ! {} {
    return a << n;
}
"#;
    assert_accepted(
        "ct008_secret_non_ct_amount.sigil",
        source,
        "a `@Secret` (non-CT) shift amount is outside the constant-time discipline and must compile",
    );
}

#[test]
fn ct008_let_copied_secret_ct_amount_rejected() {
    // The check is on the LABEL, not the parameter syntax: a `let` copy of the
    // secret amount is rejected identically.
    let source = r#"#[ring(outer)] module ext;
fn f(a: i64, n: i64 @SecretCT) -> i64 @SecretCT ! {} {
    let k: i64 @SecretCT = n;
    return a << k;
}
"#;
    reject_with_exact_codes(
        "ct008_let_copied_amount.sigil",
        source,
        &["T034"],
        "a `let`-copied @SecretCT shift amount must be rejected (CT008)",
    );
}

#[test]
fn ct008_arithmetic_derived_secret_ct_amount_rejected() {
    // `n + 1` is lub(@SecretCT, @Public) = @SecretCT, so a derived amount is
    // rejected too; the `+` itself is a fixed-latency op and adds no code.
    let source = r#"#[ring(outer)] module ext;
fn f(a: i64, n: i64 @SecretCT) -> i64 @SecretCT ! {} {
    let k: i64 @SecretCT = n + 1;
    return a << k;
}
"#;
    reject_with_exact_codes(
        "ct008_arith_derived_amount.sigil",
        source,
        &["T034"],
        "an arithmetic-derived @SecretCT shift amount must be rejected (CT008)",
    );
}

#[test]
fn ct008_compound_shift_assign_by_secret_ct_amount_rejected() {
    // `x <<= n` desugars to the same `Binary` node (`compound_assign_op`), so
    // the compound spelling cannot bypass the rule.
    //
    // The shifted VALUE `x` is deliberately @Public (`let mut x: i64 = a;`)
    // so this pins the AMOUNT operand specifically: under the wrong-operand
    // mutation (`r.is_ct()` -> `l.is_ct()` in the CT008 arm) a @SecretCT
    // value would still trip the rule, and an earlier revision of this test
    // (`let mut x: i64 @SecretCT = a;`) survived exactly that mutation.
    //
    // Exact set is {T034} alone, no T001: the compound form writes `x << n`
    // — whose label joins the amount's @SecretCT — back into `x`, but an
    // assignment to a bare local is a flow-sensitive REBIND in the taint
    // pass (`TypedStmt::Assign`, `Local` arm: `env.bind`), not a sink
    // check, so `x` simply becomes @SecretCT and the `@SecretCT` return
    // type accepts it. (Measured 2026-09-30: this shape is `ok` on
    // `ae026aec` and exactly {T034} on this branch.) Under the operand
    // mutation nothing fires and the program compiles: this test goes red.
    for op in ["<<=", ">>="] {
        let source = format!(
            "#[ring(outer)] module ext;\nfn f(a: i64, n: i64 @SecretCT) -> i64 @SecretCT ! {{}} {{\n    let mut x: i64 = a;\n    x {op} n;\n    return x;\n}}\n"
        );
        reject_with_exact_codes(
            "ct008_compound_assign.sigil",
            &source,
            &["T034"],
            &format!(
                "a compound `{op}` of a @Public value by a @SecretCT amount must be rejected (CT008)"
            ),
        );
    }
}

#[test]
fn ct008_anti_stub_planted_secret_ct_amount_in_the_accepted_shape_is_detected() {
    // SC-P4: the two acceptance tests above are absence claims ("no T034 on the
    // value-side / public shapes"). This proves the detector they rely on
    // fires: plant the ONE change that makes the accepted public shape a CT008
    // violation — the amount's label — and the same harness must reject it with
    // exactly {T034}. If the rule were ever stubbed out, this test fails as a
    // SOUNDNESS HOLE while the acceptance tests would keep passing.
    let accepted =
        "#[ring(outer)] module ext;\nfn f(a: i64, n: i64) -> i64 ! {} {\n    return a << n;\n}\n";
    assert_accepted(
        "ct008_anti_stub_base.sigil",
        accepted,
        "the anti-stub's base shape must be the accepted public shift",
    );
    let planted = accepted
        .replace("n: i64)", "n: i64 @SecretCT)")
        .replace("-> i64 !", "-> i64 @SecretCT !");
    assert_ne!(planted, accepted, "the plant must change the source");
    reject_with_exact_codes(
        "ct008_anti_stub_planted.sigil",
        &planted,
        &["T034"],
        "SC-P4 anti-stub: the planted @SecretCT shift amount was not detected",
    );
}

#[test]
fn t034_message_and_hint_name_the_amount_and_the_sound_alternative() {
    let err = reject_with_exact_codes(
        "ct008_message.sigil",
        &ct008_amount_secret_source("i64", "<<"),
        &["T034"],
        "the message test's program must be the CT008 rejection",
    );
    let diagnostic = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T034")
        .expect("exactly one T034 is asserted above");
    let message = diagnostic.message();
    assert!(
        message.contains("shift amount") && message.contains("@SecretCT"),
        "message must name the AMOUNT operand and its label: {message}"
    );
    let hint = diagnostic.hint().unwrap_or_default();
    assert!(
        hint.contains("VALUE") && hint.contains("@Public") && hint.contains("ct_select"),
        "hint must state the value-side exemption and the public-count / ct_select alternative: {hint}"
    );
}
