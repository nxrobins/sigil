//! Mutable-state fences keep a `mut` field bounded to plain, reassignable data.
//!
//! F1 is the GO/NO-GO decider: a `mut` field whose type is capability-/reference-/borrow-/
//! Fn-/Ptr-bearing is rejected (C011), because overwriting a capability held in state would
//! drop it without linear accounting — an unbounded leak / double-spend (hazard H1). A bare
//! (non-`mut`) field keeps the immutable-after-init cap/ref discipline and is untouched.

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

// ── F1: a `mut` capability-bearing state field is rejected (C011) ─────────────────────────
#[test]
fn mut_capability_state_field_is_rejected() {
    let src = r#"module sigil;
cap type Fuel {}
actor Worker {
    state { mut power: Fuel }
    init(f: Fuel) { power = f; }
    on Tick() { let e: i64 = grant(&power, fn(c: &Fuel) -> i64 { return 1; }); }
}
"#;
    let err = compile_named_module("mut_cap_state.sigil", src)
        .expect_err("a `mut` cap-bearing state field must be rejected (C011)");
    assert_has_code(&err, "C011");
}

// ── F1: exactly ONE C011 per offending field (not doubled by the env/captures builds) ─────
#[test]
fn mut_capability_state_field_emits_c011_once() {
    let src = r#"module sigil;
cap type Fuel {}
actor Worker {
    state { mut power: Fuel }
    init(f: Fuel) { power = f; }
    on Tick() { let e: i64 = grant(&power, fn(c: &Fuel) -> i64 { return 1; }); }
}
"#;
    let err = compile_named_module("mut_cap_once.sigil", src)
        .expect_err("a `mut` cap state field must be rejected");
    let n = err
        .diagnostics()
        .iter()
        .filter(|d| d.code().as_str() == "C011")
        .count();
    assert_eq!(n, 1, "C011 must fire exactly once per field, got {n}");
}

// ── F1 (both sides): a `mut` PLAIN-DATA state field is allowed ────────────────────────────
#[test]
fn mut_plain_data_state_field_is_allowed() {
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut n: i64 }
    init(f: Fuel) { n = 0; }
    on Get() -> i64 { return n; }
}
"#;
    compile_named_module("mut_data_state.sigil", src)
        .expect("a `mut` plain-data (i64) state field must compile (F1 accepts plain data)");
}

// ── F1 (conservation): a NON-`mut` cap state field is UNAFFECTED (immutable-after-init) ───
#[test]
fn non_mut_capability_state_field_still_allowed() {
    // The same cap field WITHOUT `mut` keeps the M2/M4 immutable-after-init cap discipline —
    // F1 fires only on `mut` fields, so this must still compile exactly as before.
    let src = r#"module sigil;
cap type Fuel {}
actor Worker {
    state { power: Fuel }
    init(f: Fuel) { power = f; }
    on Tick() { let e: i64 = grant(&power, fn(c: &Fuel) -> i64 { return 1; }); }
}
"#;
    compile_named_module("non_mut_cap_state.sigil", src)
        .expect("a bare (non-mut) cap state field must still compile — F1 only gates `mut`");
}

// ── The relax: a handler write to a `mut` field is PERMITTED (T123 relaxed) ────────────────
#[test]
fn handler_write_to_mut_field_is_permitted() {
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut n: i64 }
    init(f: Fuel) { n = 0; }
    on Set(v: i64) { n = v; }
}
"#;
    compile_named_module("mut_write_ok.sigil", src)
        .expect("a handler write to a `mut` state field must be permitted (T123 relaxed)");
}

// ── The relax is TARGETED: a non-`mut` field in the SAME actor still fails T123 ────────────
#[test]
fn handler_write_to_non_mut_field_still_fails_t123() {
    // `n` is `mut` (writable), `m` is NOT — a write to `m` must still be rejected. This pins
    // that the relax keys on the specific field, not "any field in a mut-bearing actor".
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut n: i64, m: i64 }
    init(f: Fuel) { n = 0; m = 0; }
    on Set(v: i64) { m = v; }
}
"#;
    let err = compile_named_module("non_mut_write.sigil", src)
        .expect_err("a handler write to a NON-mut field must still fail T123");
    assert_has_code(&err, "T123");
}

// ── F2 (grammar-enforced): a refinement (`where`) on a `mut` state field is unexpressible ──
#[test]
fn refinement_on_a_mut_state_field_is_rejected() {
    // A state field's type carries no `where`-clause (the state-block grammar admits none),
    // so a refinement-typed `mut` field cannot be written — it fails to parse. F2 is enforced
    // by construction; no per-write Z3 preservation obligation is owed (H7-A stays out of scope).
    let src = r#"module sigil;
cap type Fuel {}
actor Worker {
    state { mut n: i64 where n > 0 }
    init(f: Fuel) { n = 1; }
    on Get() -> i64 { return n; }
}
"#;
    let err = compile_named_module("mut_refined_state.sigil", src).expect_err(
        "a refinement on a state field must be rejected (the grammar admits no `where`)",
    );
    // Any parser rejection is acceptable — the point is it does NOT silently accept a refined
    // mutable field (which would owe an unimplemented per-write preservation obligation).
    assert!(
        !err.diagnostics().is_empty(),
        "a `where` on a state field must produce a diagnostic"
    );
}

// ── F4 (taint stays firing): a handler writing @Secret into a @Public `mut` field is T001 ──
#[test]
fn handler_writing_secret_into_public_mut_field_is_t001() {
    // State fields are @Public (they carry no taint annotation) and are read back at that label.
    // With the S2 relax a handler can now WRITE a `mut` field — so the T001 downgrade sink-check
    // must fire in handler context, exactly as it does for an `init` write, or a @Secret payload
    // would launder across the (now mutable) state boundary. Pins that the relax did not create a
    // taint hole.
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut n: i64 }
    init(f: Fuel) { n = 0; }
    on Set(s: i64 @Secret) { n = s; }
}
"#;
    let err = compile_named_module("mut_taint_launder.sigil", src)
        .expect_err("a handler writing @Secret into a @Public mut field must fail T001");
    assert_has_code(&err, "T001");
}

// ── F5 (no borrow escape) — enforced by COMPOSITION of existing fences (H4 closed) ─────────
// The S2 design's F5 ("no borrow rooted at a state field escapes") turns out to need no new
// code: every escape vector for a `mut`-field borrow is already closed. These pin the vectors.

#[test]
fn a_reference_typed_mut_state_field_is_rejected_f1() {
    // A state field can never HOLD a borrow (a persisted alias of another field): a
    // reference-bearing type is not reassignable, so F1/C011 rejects it at the decl.
    let src = r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
actor Worker {
    state { d: Data, mut alias: &Data }
    init(f: Fuel) { d = Data { v: 0 }; alias = &d; }
    on Go() {}
}
"#;
    let err = compile_named_module("mut_ref_state.sigil", src)
        .expect_err("a reference-bearing `mut` state field must be rejected (C011)");
    assert_has_code(&err, "C011");
}

#[test]
fn sending_a_borrow_of_a_state_field_in_a_payload_is_rejected() {
    // The cross-dispatch escape: sending `&d` to another actor. Message args must be
    // runtime-serializable (bool/i64/ActorRef/cap) — a reference is rejected, so a state-field
    // borrow cannot travel in a payload and outlive the dispatch.
    let src = r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Take(other: ActorRef<Sink>) { other.send(Consume(&d)); }
}
actor Sink {
    init() {}
    on Consume(r: &Data) {}
}
"#;
    let err = compile_named_module("mut_payload_escape.sigil", src)
        .expect_err("sending a borrow of a state field must be rejected (Send args only)");
    assert!(
        !err.diagnostics().is_empty(),
        "a reference payload arg must produce a diagnostic"
    );
}

// ── F3 (definite-assignment): every state field assigned exactly once in init ──────────────
#[test]
fn double_init_of_a_state_field_is_t124() {
    // A field assigned twice in init is a double-init (T124) — "exactly once" is violated.
    let src = r#"module sigil;
cap type Fuel {}
actor Worker {
    state { mut n: i64 }
    init(f: Fuel) { n = 0; n = 1; }
    on Get() -> i64 { return n; }
}
"#;
    let err = compile_named_module("double_init.sigil", src)
        .expect_err("a state field assigned twice in init must fail T124");
    assert_has_code(&err, "T124");
}

#[test]
fn init_skipping_a_state_field_is_t125() {
    // An init that leaves a declared field unassigned would let the handler read a
    // zero-initialised (uninit) value — rejected T125.
    let src = r#"module sigil;
cap type Fuel {}
actor Worker {
    state { mut n: i64, mut m: i64 }
    init(f: Fuel) { n = 0; }
    on Get() -> i64 { return n + m; }
}
"#;
    let err = compile_named_module("skip_init.sigil", src)
        .expect_err("an init that skips a declared `mut` state field must fail T125");
    assert_has_code(&err, "T125");
}

#[test]
fn exactly_once_init_compiles() {
    // The sanctioned shape: each field assigned exactly once, unconditionally, in init.
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut n: i64, m: i64 }
    init(f: Fuel) { n = 0; m = 1; }
    on Get() -> i64 { return n + m; }
}
"#;
    compile_named_module("once_init.sigil", src)
        .expect("each field assigned exactly once in init must compile");
}

#[test]
fn conditional_init_of_a_state_field_is_t125() {
    // Definite assignment: a field assigned only inside an `if` is NOT definitely assigned on
    // every path, so it is rejected (the boring limit: top-level unconditional assignment only).
    let src = r#"module sigil;
cap type Fuel {}
actor Worker {
    state { mut n: i64 }
    init(f: Fuel, c: bool) { if c { n = 1; } else { } }
    on Get() -> i64 { return n; }
}
"#;
    let err = compile_named_module("cond_init.sigil", src)
        .expect_err("a conditionally-assigned state field is not definitely assigned (T125)");
    assert_has_code(&err, "T125");
}
