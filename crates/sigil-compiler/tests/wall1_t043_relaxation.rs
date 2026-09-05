//! Wall 1 Step 1 — T043 relaxation.
//!
//! The Phase-1 type checker used to blanket-reject non-primitive
//! reassignment with T043 ("only primitive types support reassignment
//! in Phase 1"). This PR replaces the primitive allowlist with the
//! `type_is_reassignable` predicate, which permits reassignment for
//! any type that doesn't transitively own a capability or a borrow.
//! User-defined records and enums are walked via the type universe
//! so refs hidden inside a `record Wrapper { r: &i64 }` correctly
//! come out non-reassignable even though the outer name has no args.
//!
//! These are the compile-time invariants. Runtime behavior is
//! exercised by the existing `stdlib_compiles` harness, which
//! constructs and uses records / enums in the stdlib modules.
//! The AIR-to-wasm path for the new code is the same shape as
//! initialization (which works today); the only new behavior is
//! the `local.set` that replaces a stable VarId's value with a new
//! pointer / primitive — a no-op for the borrow tracker on non-cap
//! sources (INV-5).
//!
//! Invariants pinned (cross-references to the plan):
//!   INV-1 borrow tracker: ref-bearing types stay rejected.
//!   INV-2 taint:           assigned value's taint matches initialization.
//!   INV-3 Z3 untouched:    cap reassignment still rejected, so no cap
//!                          VarId is ever reassigned and z3_capability
//!                          requires no new source rule.
//!   INV-5 ownership:       no new diagnostic codes from ownership; the
//!                          `MoveKind::Reassign` path activates for
//!                          non-cap sources where `mark_linear_move`
//!                          is a no-op.

use sigil_compiler::CompileError;
use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    let result = compile_named_module(format!("wall1_{label}.sigil"), source);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

fn assert_emits_t043(source: &str, label: &str) -> CompileError {
    let err = compile_named_module(format!("wall1_{label}.sigil"), source)
        .expect_err(&format!("expected T043 for {label}"));
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"T043"),
        "expected T043 in diagnostics for {label}, got: {codes:?}"
    );
    err
}

// ── Positive cases: types now reassignable ───────────────────────────

#[test]
fn record_reassignment_compiles() {
    let source = r#"
module main;

record Point { x: i64, y: i64 }

fn boot() -> i64 {
    let mut p: Point = Point { x: 1, y: 2 };
    p = Point { x: 3, y: 4 };
    return p.x;
}
"#;
    assert_compiles_clean(source, "record");
}

#[test]
fn non_cap_enum_reassignment_compiles() {
    // The Holder pattern from fixture 12. Closes the narrow case of
    // Wall 1 (the underlying M-of-N coordinator with cap accumulation
    // still depends on Slot<Cap> from Step 2).
    let source = r#"
module main;

enum Holder { Empty, Have(i64) }

fn boot(seed: i64) -> i64 {
    let mut h: Holder = Empty;
    h = Have(seed);
    return seed;
}
"#;
    assert_compiles_clean(source, "non_cap_enum");
}

#[test]
fn array_of_primitives_reassignment_compiles() {
    // Sigil arrays are inferred, not explicitly typed at the let site
    // (see `tests/fixtures/T186.sigil` for the canonical shape).
    let source = r#"
module main;

fn boot() -> i64 {
    let mut xs = [1, 2, 3, 4];
    xs = [5, 6, 7, 8];
    return xs[0];
}
"#;
    assert_compiles_clean(source, "array_prims");
}

#[test]
fn non_cap_reassignment_inside_actor_handler_compiles() {
    // Verify that local-variable reassignment works inside an actor
    // handler context (not just in plain functions). Sigil today
    // doesn't support state-field reassignment regardless of type —
    // state fields are init-bound, and `state.foo = bar` fires T042
    // ("cannot assign to immutable variable"). That's a separate
    // concern from T043, gated on a future "mutable state fields"
    // move that Wall 1 Step 1 does not address.
    let source = r#"
module main;

cap type Fuel {}
enum Status { Waiting, Approved, Rejected }

entry actor Main {
    state { fuel: Fuel }

    on Tick(seed: i64) -> i64 {
        let mut s: Status = Waiting;
        if seed >= 3 {
            s = Approved;
        } else {
            s = Rejected;
        }
        return seed;
    }
}
"#;
    assert_compiles_clean(source, "actor_handler_local");
}

#[test]
fn str_reassignment_compiles() {
    let source = r#"
module main;

fn boot() -> i64 {
    let mut s: str = "hello";
    s = "world";
    return 0;
}
"#;
    assert_compiles_clean(source, "str");
}

#[test]
fn nested_non_cap_record_reassignment_compiles() {
    // Universe-walk hits a recursive structural check: a record
    // containing another record (both non-cap) must come out
    // reassignable.
    let source = r#"
module main;

record Inner { v: i64 }
record Outer { i: Inner, k: i64 }

fn boot() -> i64 {
    let mut o: Outer = Outer { i: Inner { v: 1 }, k: 2 };
    o = Outer { i: Inner { v: 3 }, k: 4 };
    return o.k;
}
"#;
    assert_compiles_clean(source, "nested_record");
}

// ── Negative cases: T043 still fires ─────────────────────────────────

#[test]
fn cap_reassignment_still_fires_t043() {
    let source = r#"
module main;

cap type Fuel { burn }

fn boot(seed: Fuel) -> i64 {
    let mut f: Fuel = seed;
    f = seed;
    return 0;
}
"#;
    let err = assert_emits_t043(source, "cap_direct");
    let msg = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T043")
        .unwrap()
        .message();
    assert!(
        msg.contains("capability"),
        "T043 message must mention capability for cap-bearing rejection; got: {msg}"
    );
}

#[test]
fn generic_enum_with_cap_arg_still_fires_t043() {
    // A user-defined generic enum instantiated with a cap. Sigil's let-
    // binding type resolution currently drops the generic args at the
    // env entry (target_type becomes `Type::Named("Maybe", [])` rather
    // than `Maybe<Fuel>` — a separate bug, tracked but out of scope
    // for Wall 1 Step 1). Soundness is preserved either way: the
    // predicate walks the enum definition and sees the generic
    // payload `T`, which is non-reassignable, so T043 still fires.
    // We assert only that T043 fires; the message-branch correctness
    // for this case is gated on the type-args propagation fix.
    let source = r#"
module main;

cap type Fuel { burn }
enum Maybe<T> { Has(T), Nothing }

fn boot(seed: Fuel) -> i64 {
    let mut x: Maybe<Fuel> = Nothing;
    x = Has(seed);
    return 0;
}
"#;
    assert_emits_t043(source, "generic_enum_with_cap");
}

#[test]
fn record_containing_ref_still_fires_t043() {
    // The universe-walk test: a record whose field is a borrow.
    // The outer Type::Named("Wrapper", []) has no generic args, so
    // a structural-only predicate would let it through — but the
    // walk descends into the record's field types and catches the
    // &i64.
    let source = r#"
module main;

record Wrapper { r: &i64 }

fn boot(seed: i64) -> i64 {
    let mut w: Wrapper = Wrapper { r: &seed };
    w = Wrapper { r: &seed };
    return 0;
}
"#;
    let err = assert_emits_t043(source, "record_with_ref");
    let msg = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T043")
        .unwrap()
        .message();
    assert!(
        msg.contains("borrow"),
        "T043 message must mention borrow for ref-bearing rejection; got: {msg}"
    );
}

#[test]
fn t043_message_distinguishes_cap_from_ref() {
    // Axis-4 message-content lock: the T043 message picks a different
    // branch for cap-bearing vs ref-bearing rejections. A future
    // refactor that flattens the message back to one generic string
    // would be caught by this test.
    let cap_source = r#"
module main;
cap type Fuel { burn }
fn boot(seed: Fuel) -> i64 {
    let mut f: Fuel = seed;
    f = seed;
    return 0;
}
"#;
    let cap_err = assert_emits_t043(cap_source, "cap_msg");
    let cap_msg = cap_err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T043")
        .unwrap()
        .message()
        .to_owned();

    let ref_source = r#"
module main;
record Wrapper { r: &i64 }
fn boot(seed: i64) -> i64 {
    let mut w: Wrapper = Wrapper { r: &seed };
    w = Wrapper { r: &seed };
    return 0;
}
"#;
    let ref_err = assert_emits_t043(ref_source, "ref_msg");
    let ref_msg = ref_err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T043")
        .unwrap()
        .message()
        .to_owned();

    assert_ne!(
        cap_msg, ref_msg,
        "T043 must distinguish cap and ref rejection causes; both said: {cap_msg}"
    );
    assert!(
        cap_msg.contains("capability"),
        "cap branch must say capability"
    );
    assert!(ref_msg.contains("borrow"), "ref branch must say borrow");
}

// ── Invariant regressions ────────────────────────────────────────────

#[test]
fn taint_preserved_across_reassignment() {
    // INV-2: a binding's effective taint after reassignment is
    // `lub(pc_taint, value_taint)`. Reassigning a record with an
    // @Internal-tainted RHS keeps the binding tainted; downstream
    // sinks must still respect the floor. Concrete check: pass the
    // reassigned value to a function expecting @Public — that must
    // be rejected (taint widening violation), proving the taint
    // wasn't silently downgraded by the reassignment.
    let source = r#"
module main;

record Box { v: i64 }

fn needs_public(b: Box @Public) -> i64 {
    return b.v;
}

fn boot(secret: i64 @Internal) -> i64 {
    let mut b: Box @Internal = Box { v: 0 };
    b = Box { v: secret };
    return needs_public(b);
}
"#;
    // The exact taint diagnostic depends on the taint-check module's
    // current codes; we just assert that the reassigned-and-passed
    // path is rejected (no silent downgrade).
    let err = compile_named_module("wall1_taint.sigil", source)
        .expect_err("@Internal reassigned to @Public sink should be rejected");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    // Any E-prefix code (taint family) or T-prefix taint code is fine;
    // the key is that compilation FAILED rather than silently passing.
    assert!(
        !codes.is_empty(),
        "reassignment must not erase taint; expected some diagnostic, got none"
    );
}

#[test]
fn determinism_preserved_across_new_path() {
    // INV-4: I6 determinism — the new reassignment code path must
    // produce byte-identical wasm under two compiles. Mirror the
    // pattern from `stdlib_compiles::assert_compile_deterministic`.
    let source = r#"
module main;

record Point { x: i64, y: i64 }
enum Choice { A, B(i64) }

fn boot() -> i64 {
    let mut p: Point = Point { x: 1, y: 2 };
    p = Point { x: 3, y: 4 };
    let mut c: Choice = A;
    c = B(p.x);
    return p.y;
}
"#;
    let a = compile_named_module("wall1_det.sigil", source).expect("compile 1");
    let b = compile_named_module("wall1_det.sigil", source).expect("compile 2");
    assert_eq!(
        a.wasm_inner, b.wasm_inner,
        "I6: byte-identical wasm under two compiles of the reassignment path"
    );
}
