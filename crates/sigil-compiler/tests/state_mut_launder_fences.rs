//! MUTABLE-STATE S3 — the fences the adversarial sweep surfaced.
//!
//! Adversarial mutable-state cases that previously bypassed the declaration and write fences.
//! Each test now asserts the current boundary fires.
//!
//! Class A — F3 definite-assignment had NO reachability analysis (a pure syntactic
//! count of top-level assignments). A `return` before the counted assignment left the
//! `mut` field never assigned yet accepted (hazard H7-B: a handler reads the zero slot).
//! FIX: an `init` block must not `return` (T126) — the count is sound iff init runs to
//! completion; only `return` lets init finish while skipping a top-level assignment.
//!
//! Class B — the T123 immutability gate keyed on a *bare* `StateField` place, so a
//! PROJECTED place — `a[i]` (Index) or `d.f` (FieldAccess) — rooted at a NON-`mut` state
//! field escaped it, silently mutating immutable state (the F1 conservation claim was
//! false). This was a LATENT hole predating the epic. FIX: a projected place rooted at a
//! non-`mut` state field is immutability-gated (T123) against that root field.
//!
//! Class C — a `mut` record field read/written via a dotted path ICE'd AIR lowering. The
//! deeper cause (probed in sigil-runtime) is that an AGGREGATE state field's heap object
//! is NOT preserved across dispatches (a broad, pre-existing persistence gap that hits
//! non-`mut` aggregates too). FIX: `mut` is restricted to sound INLINE SCALARS (C012);
//! mutable aggregate fields are fenced at declaration until aggregate state is allocated
//! persistently. This also closes the `mut`-array taint/immutability launders at the decl.

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
        "expected diagnostic {code} but got: {codes:?}"
    );
}

// ── Class A: F3 reachability — an early `return` in `init` must be rejected (T126) ──────────

#[test]
fn unconditional_return_before_the_only_assignment_is_rejected() {
    // `init(f) { return; n = 5; }` — the counted `n = 5` is dead code after the
    // unconditional `return`; `n` is never assigned, so a handler reads the zero slot.
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut n: i64 }
    init(f: Fuel) { return; n = 5; }
    on Get() -> i64 { return n; }
}
"#;
    let err = compile_named_module("uncond_return_init.sigil", src)
        .expect_err("an early `return` in `init` before the assignment must be rejected (T126)");
    assert_has_code(&err, "T126");
}

#[test]
fn guarded_early_return_before_the_assignment_is_rejected() {
    // `init(f) { let c = true; if c { return; } n = 5; }` — a guarded return can skip the
    // counted assignment. Same H7-B hazard; T126 rejects any init `return`.
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut n: i64 }
    init(f: Fuel) { let c: bool = true; if c { return; } n = 5; }
    on Get() -> i64 { return n; }
}
"#;
    let err = compile_named_module("guarded_return_init.sigil", src)
        .expect_err("a guarded early `return` in `init` must be rejected (T126)");
    assert_has_code(&err, "T126");
}

#[test]
fn init_that_assigns_then_falls_off_the_end_is_permitted() {
    // The legitimate shape: assign unconditionally at the top level, no `return`.
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut n: i64 }
    init(f: Fuel) { n = 5; }
    on Get() -> i64 { return n; }
}
"#;
    compile_named_module("plain_init.sigil", src)
        .expect("an init that assigns unconditionally with no early return must compile");
}

#[test]
fn a_return_inside_a_grant_closure_in_init_is_not_an_init_return() {
    // The ban is on init's OWN control flow. A `return` inside a closure passed to `grant`
    // returns from the CLOSURE, not init — it must stay legal (T126 must not descend into
    // nested closure/lambda bodies).
    let src = r#"module sigil;
cap type Fuel { burn }
entry actor Main {
    state {}
    init(fuel: Fuel) {
        let result: i64 = grant(&fuel, fn(cap_ref: &Fuel) -> i64 { return 42; });
    }
}
"#;
    compile_named_module("grant_closure_return.sigil", src)
        .expect("a `return` inside a grant closure in init must stay legal (not an init return)");
}

// ── Class B: projected write-through into a NON-`mut` state field — immutability (T123) ─────

#[test]
fn write_through_into_a_non_mut_record_state_field_is_t123() {
    // `d.v = x` in a handler, `d` a NON-`mut` record state field. The write-through bypassed
    // the T123 immutability gate (bare-`StateField`-only), silently mutating immutable state
    // — falsifying the F1 conservation claim. Now T123 fires.
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
    on Set(x: i64) { d.v = x; }
    on Get() -> i64 { return d.v; }
}
"#;
    let err = compile_named_module("non_mut_write_through.sigil", src).expect_err(
        "a write-through into a NON-mut record state field in a handler must fail T123",
    );
    assert_has_code(&err, "T123");
}

#[test]
fn indexed_write_into_a_non_mut_array_state_field_is_t123() {
    // `a[0] = x` in a handler, `a` a NON-`mut` array state field. Same immutability launder
    // via an Index place.
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { a: [i64; 4] }
    init(f: Fuel) { a = [0, 0, 0, 0]; }
    on Set(x: i64) { a[0] = x; }
    on Get() -> i64 { return a[0]; }
}
"#;
    let err = compile_named_module("non_mut_index_write.sigil", src).expect_err(
        "an indexed write into a NON-mut array state field in a handler must fail T123",
    );
    assert_has_code(&err, "T123");
}

// ── AGG-2a: `mut` FLAT-FIXED aggregates persist via IN-PLACE mutation ────────────────────────

#[test]
fn a_mut_flat_record_state_field_mutated_in_place_is_permitted() {
    // AGG-2a: a `mut` flat record field (all-scalar) is init-allocated below the persistent floor
    // and mutated IN PLACE by a handler (`d.v = x` StoreField into that persistent object), so it
    // persists — permitted. (Runtime persistence: `mut_flat_record_state_field_mutated_in_place_-
    // persists` in sigil-runtime.)
    let src = r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Set(x: i64) { d.v = x; }
    on Get() -> i64 { return d.v; }
}
"#;
    compile_named_module("mut_record_state.sigil", src)
        .expect("a `mut` flat record field mutated in place must compile (AGG-2a)");
}

#[test]
fn a_mut_flat_array_state_field_mutated_in_place_is_permitted() {
    // AGG-2a: same for a `mut` flat array field mutated in place (`a[0] = x`).
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut a: [i64; 4] }
    init(f: Fuel) { a = [0, 0, 0, 0]; }
    on Set(s: i64) { a[0] = s; }
    on Get() -> i64 { return a[0]; }
}
"#;
    compile_named_module("mut_array_state.sigil", src)
        .expect("a `mut` flat array field mutated in place must compile (AGG-2a)");
}

#[test]
fn wholesale_reassign_of_a_mut_flat_aggregate_is_now_promoted() {
    // AGG-2a rejected this (T128): a wholesale reassignment allocated above the persistent floor
    // and the per-dispatch reset reclaimed it. PPS-1 added the PROMOTION primitive — a handler's
    // wholesale flat-aggregate store is lowered as allocate-persistent + field copy, so the field
    // addresses a persistent copy. The boundary moved; `pps1_promotion_fences.rs` owns the new
    // one (pointer-bearing shapes still T128/C012), and `pps1_promotion.rs` proves the
    // persistence end-to-end.
    let src = r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Reset() { d = Data { v: 0 }; }
    on Get() -> i64 { return d.v; }
}
"#;
    compile_named_module("mut_aggregate_wholesale.sigil", src)
        .expect("PPS-1 promotes a wholesale flat-aggregate store; it must compile");
}

#[test]
fn a_mut_nested_aggregate_state_field_is_rejected_c012() {
    // AGG-2a fences only FLAT aggregates. A `mut` NESTED aggregate (a record whose field is itself
    // a record) stays C012 — in-place mutation of the inner object persists, but the machinery for
    // that is the AGG-2b half; conservatively fenced until then.
    let src = r#"module sigil;
cap type Fuel {}
record Inner { x: i64 }
record Outer { inner: Inner }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut o: Outer }
    init(f: Fuel) { o = Outer { inner: Inner { x: 0 } }; }
    on Get() -> i64 { return o.inner.x; }
}
"#;
    let err = compile_named_module("mut_nested_state.sigil", src).expect_err(
        "a mut nested aggregate state field must be rejected (C012) — AGG-2b territory",
    );
    assert_has_code(&err, "C012");
}

// ── Positive controls: sound shapes must STAY permitted (the fences must not over-reject) ────

#[test]
fn a_mut_scalar_state_field_is_still_permitted() {
    // The demonstrator's actual shape — a `mut` INLINE scalar — is sound and must compile.
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut n: i64, mut flag: bool }
    init(f: Fuel) { n = 0; flag = false; }
    on Set(v: i64) { n = v; }
    on Get() -> i64 { return n; }
}
"#;
    compile_named_module("mut_scalar_ok.sigil", src).expect(
        "a `mut` inline-scalar state field must still compile (C012 fences only aggregates)",
    );
}

#[test]
fn a_non_mut_record_state_field_is_permitted() {
    // AGG-1 (persistent-aggregate-state): a NON-`mut` aggregate state field is written only in
    // `init`, whose allocation now sits below the persistent floor (the AL-2 reset floor is the
    // post-init cursor), so it PERSISTS across dispatches — it is permitted. (A `mut` aggregate
    // stays C012-fenced; see the mut tests below. Runtime persistence is proven by
    // `nonmut_aggregate_state_field_persists_across_dispatches` in sigil-runtime.)
    let src = r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { d: Data }
    init(f: Fuel) { d = Data { v: 7 }; }
    on Get() -> i64 { return d.v; }
}
"#;
    compile_named_module("nonmut_record_state.sigil", src)
        .expect("a non-mut record state field must compile (AGG-1: non-mut aggregates persist)");
}

#[test]
fn a_non_mut_scalar_or_capability_state_field_is_still_permitted() {
    // The fence is TARGETED: a non-`mut` inline scalar (persists inline) and a non-`mut` cap
    // (persists via the capability table — the borrow-only C010 state cap) must both still
    // compile. Only heap DATA AGGREGATES are fenced.
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { tag: i64, power: Fuel }
    init(f: Fuel) { tag = 7; power = f; }
    on Get() -> i64 { return tag; }
    on Tick() { let e: i64 = grant(&power, fn(c: &Fuel) -> i64 { return 1; }); }
}
"#;
    compile_named_module("nonmut_scalar_cap_ok.sigil", src).expect(
        "a non-mut scalar + a non-mut cap state field must compile (fence targets aggregates)",
    );
}
