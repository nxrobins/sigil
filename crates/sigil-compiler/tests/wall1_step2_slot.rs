//! Wall 1 Step 2 — `Slot<Cap>` built-in linear container.
//!
//! Compile-time invariants. Runtime traps + Z3 soundness are
//! exercised by `crates/sigil-runtime/tests/wall1_step2_runtime.rs`.
//!
//! Invariants pinned (cross-references to the plan):
//!   INV-2  T183-T186 unchanged
//!   INV-3  cap moved into slot is consumed (O001)
//!   INV-4  cap taken from slot is linear (O001 on double-use)
//!   INV-6  T043 still rejects slot reassignment
//!   INV-10 `Slot` is a reserved name (T193)

use sigil_compiler::CompileError;
use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    let result = compile_named_module(format!("wall1_step2_{label}.sigil"), source);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

fn assert_emits(source: &str, label: &str, expected_code: &str) -> CompileError {
    let err = compile_named_module(format!("wall1_step2_{label}.sigil"), source)
        .expect_err(&format!("expected {expected_code} for {label}"));
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&expected_code),
        "expected {expected_code} in diagnostics for {label}, got: {codes:?}"
    );
    err
}

// ── Positive cases: Slot works in local scope ────────────────────────

#[test]
fn slot_new_with_type_arg_compiles() {
    let source = r#"
module main;
cap type Fuel { burn }
fn boot(seed: Fuel) -> i64 {
    let s = slot_new::<Fuel>();
    slot_put(s, seed);
    let extracted: Fuel = slot_take(s);
    let _consumed = extracted.draw(1);
    return 0;
}
"#;
    assert_compiles_clean(source, "round_trip");
}

#[test]
fn slot_take_returns_cap_typed_value() {
    // The returned type from slot_take is the cap T, usable in cap-
    // demanding contexts.
    let source = r#"
module main;
cap type Fuel { burn }

fn consume(f: Fuel) -> i64 { return 1; }

fn boot(seed: Fuel) -> i64 {
    let s = slot_new::<Fuel>();
    slot_put(s, seed);
    return consume(slot_take(s));
}
"#;
    assert_compiles_clean(source, "typed_take");
}

// ── Negative cases: T191-T193 fire ───────────────────────────────────

#[test]
fn slot_t_must_be_cap_fires_t191() {
    let source = r#"
module main;
fn boot() -> i64 {
    let s = slot_new::<i64>();
    return 0;
}
"#;
    assert_emits(source, "t191", "T191");
}

#[test]
fn slot_new_without_type_arg_fires_t192() {
    let source = r#"
module main;
cap type Fuel { burn }
fn boot() -> i64 {
    let s = slot_new();
    return 0;
}
"#;
    assert_emits(source, "t192", "T192");
}

#[test]
fn user_enum_named_slot_fires_t193() {
    let source = r#"
module main;
enum Slot<T> { Empty, Full(T) }
fn boot() -> i64 { return 0; }
"#;
    assert_emits(source, "t193_enum", "T193");
}

#[test]
fn user_record_named_slot_fires_t193() {
    let source = r#"
module main;
record Slot { v: i64 }
fn boot() -> i64 { return 0; }
"#;
    assert_emits(source, "t193_record", "T193");
}

#[test]
fn user_cap_type_named_slot_fires_t193() {
    let source = r#"
module main;
cap type Slot { burn }
fn boot() -> i64 { return 0; }
"#;
    assert_emits(source, "t193_cap", "T193");
}

#[test]
fn multi_branch_slot_put_compiles() {
    // Wall 1 Step 4: T194 retired. Multi-branch puts to the same slot
    // compile cleanly — the Z3 source rule folds every SlotPut's
    // authority into a conservative meet at SlotTake. Soundness is
    // preserved without the structural rejection.
    let source = r#"
module main;
cap type Fuel { burn }
fn boot(cond: i64, c1: Fuel, c2: Fuel) -> i64 {
    let s = slot_new::<Fuel>();
    if cond == 1 {
        slot_put(s, c1);
    } else {
        slot_put(s, c2);
    }
    let _taken: Fuel = slot_take(s);
    return 0;
}
"#;
    assert_compiles_clean(source, "multi_branch_put");
}

#[test]
fn sequential_put_take_put_compiles() {
    // T194 also rejected the rotation pattern (put → take → put) even
    // though the intermediate take leaves the slot empty before the
    // second put. With the meet model, this compiles; the second
    // take sees the meet of both puts' authorities (conservative).
    let source = r#"
module main;
cap type Fuel { burn }
fn boot(c1: Fuel, c2: Fuel) -> i64 {
    let s = slot_new::<Fuel>();
    slot_put(s, c1);
    let _first: Fuel = slot_take(s);
    slot_put(s, c2);
    let _second: Fuel = slot_take(s);
    return 0;
}
"#;
    assert_compiles_clean(source, "rotation");
}

// ── INV-2: T183 / T184 / T186 unchanged (Slot in user aggregates still rejected) ──

#[test]
fn cap_in_record_still_fires_t183() {
    let source = r#"
module main;
cap type Fuel { burn }
record Holder { f: Fuel }
fn boot() -> i64 { return 0; }
"#;
    assert_emits(source, "t183_plain_cap", "T183");
}

#[test]
fn slot_in_record_still_fires_t183() {
    // Slot in user record is rejected in Step 2. Future PR will
    // carve this out alongside spawn-arg / message-payload support.
    let source = r#"
module main;
cap type Fuel { burn }
record Holder { s: Slot<Fuel> }
fn boot() -> i64 { return 0; }
"#;
    assert_emits(source, "t183_slot", "T183");
}

#[test]
fn cap_in_enum_payload_still_fires_t184() {
    let source = r#"
module main;
cap type Fuel { burn }
enum Holder { Empty, Have(Fuel) }
fn boot() -> i64 { return 0; }
"#;
    assert_emits(source, "t184", "T184");
}

// ── INV-6: T043 still rejects slot reassignment ──────────────────────

#[test]
fn slot_reassignment_fires_t043() {
    // Slot<Fuel> contains a cap per `type_contains_cap` (UNTOUCHED by
    // this PR). Wall 1 Step 1's `type_is_reassignable` rejects.
    let source = r#"
module main;
cap type Fuel { burn }
fn boot() -> i64 {
    let mut s: Slot<Fuel> = slot_new::<Fuel>();
    s = slot_new::<Fuel>();
    return 0;
}
"#;
    assert_emits(source, "t043", "T043");
}

// ── INV-3: cap moved into slot is consumed ───────────────────────────

#[test]
fn cap_after_slot_put_fires_o001() {
    let source = r#"
module main;
cap type Fuel { burn }

fn consume(f: Fuel) -> i64 { return 1; }

fn boot(seed: Fuel) -> i64 {
    let s = slot_new::<Fuel>();
    slot_put(s, seed);
    return consume(seed);
}
"#;
    assert_emits(source, "o001_post_put", "O001");
}

// ── INV-4: cap taken from slot is linear ─────────────────────────────

#[test]
fn cap_after_slot_take_fires_o001() {
    let source = r#"
module main;
cap type Fuel { burn }

fn consume(f: Fuel) -> i64 { return 1; }

fn boot(seed: Fuel) -> i64 {
    let s = slot_new::<Fuel>();
    slot_put(s, seed);
    let taken = slot_take(s);
    let _a = consume(taken);
    return consume(taken);
}
"#;
    assert_emits(source, "o001_post_take", "O001");
}
