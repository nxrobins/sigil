//! Refinement obligations over `u256` record fields. Wide values and bounds retain
//! all four limbs through the production discharge path. See
//! `docs/specs/u256-refinements-soundness.md`.

use sigil_compiler::compile_named_module;

fn codes(source: &str, label: &str) -> Vec<String> {
    match compile_named_module(format!("u256ref_{label}.sigil"), source) {
        Ok(_) => vec![],
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_owned())
            .collect(),
    }
}

// ── compile-gate (no solver): gate admission + fail-closed shapes ─────────────

#[test]
fn u256_refinement_field_is_admitted() {
    // NC-1: the single-field record LHS gate admits u256 (no T212). Type-shape
    // checks run without the solver; only the Z3 discharge is feature-gated.
    let src = "module main;\nrecord Balance { amount: u256 } where amount >= 100\n\
        pub fn mk() -> Balance { return Balance { amount: 5000 }; }\n";
    let got = codes(src, "admit");
    assert!(
        !got.contains(&"T212".to_string()),
        "u256 refinement field must be admitted (no T212), got: {got:?}"
    );
}

#[test]
fn i256_refinement_field_rejected_t212() {
    // NC-1: u256-ONLY. i256 stays T212 — admitting it would let the unsigned range
    // bound model a signed value, unsoundly.
    let src = "module main;\nrecord B { x: i256 } where x >= 0\n\
        pub fn mk(v: i256) -> B { return B { x: v }; }\n";
    let got = codes(src, "i256");
    assert!(
        got.contains(&"T212".to_string()),
        "i256 refinement field must stay T212, got: {got:?}"
    );
}

#[test]
fn wide_supplied_value_is_discharged_not_t211() {
    // A wide supplied value is carried at full width rather than treated as
    // symbolic. Solver-enabled tests below verify the actual discharge.
    let src = "module main;\nrecord Balance { amount: u256 } where amount >= 100\n\
        pub fn mk() -> Balance { return Balance { amount: 1000000000000000000000000 }; }\n";
    let got = codes(src, "wide");
    assert!(
        !got.contains(&"T211".to_string()),
        "a wide supplied value must no longer be T211 (U3-b carries it), got: {got:?}"
    );
}

// ── solver discharge (Z3): Holds / Violated ──────────────────────────────────

#[cfg(feature = "solver")]
#[test]
fn u256_refinement_satisfying_holds() {
    // 5000 >= 100 — Z3 discharges (Holds), clean compile.
    let src = "module main;\nrecord Balance { amount: u256 } where amount >= 100\n\
        pub fn mk() -> Balance { return Balance { amount: 5000 }; }\n";
    let got = codes(src, "holds");
    assert!(
        got.is_empty(),
        "5000 >= 100 must discharge (Holds), got: {got:?}"
    );
}

#[cfg(feature = "solver")]
#[test]
fn u256_refinement_violating_rejected_t210() {
    // 50 >= 100 is false — Z3 finds a counterexample → T210 (a real revert-by-
    // construction, the synergy payoff).
    let src = "module main;\nrecord Balance { amount: u256 } where amount >= 100\n\
        pub fn mk() -> Balance { return Balance { amount: 50 }; }\n";
    let got = codes(src, "violate");
    assert!(
        got.contains(&"T210".to_string()),
        "50 >= 100 must be Violated (T210), got: {got:?}"
    );
}

// ── U3-b1: WIDE supplied value (> i64::MAX), small bound ──────────────────────

#[cfg(feature = "solver")]
#[test]
fn wide_supplied_value_satisfies_small_bound_holds() {
    // 10^19 > i64::MAX — the wide value rides RefValue::Wide → Int::from_str (full
    // 256-bit), never narrowed. 10^19 >= 1000 → Holds.
    let src = "module main;\nrecord Balance { amount: u256 } where amount >= 1000\n\
        pub fn mk() -> Balance { return Balance { amount: 10000000000000000000 }; }\n";
    let got = codes(src, "wide_holds");
    assert!(got.is_empty(), "10^19 >= 1000 must Hold, got: {got:?}");
}

#[cfg(feature = "solver")]
#[test]
fn wide_supplied_value_violating_small_bound_t210() {
    // 10^19 <= 1000 is false → Violated.
    let src = "module main;\nrecord Cap { amount: u256 } where amount <= 1000\n\
        pub fn mk() -> Cap { return Cap { amount: 10000000000000000000 }; }\n";
    let got = codes(src, "wide_violate");
    assert!(
        got.contains(&"T210".to_string()),
        "10^19 <= 1000 must be Violated (T210), got: {got:?}"
    );
}

#[cfg(feature = "solver")]
#[test]
fn wide_value_truncation_witness_t210() {
    // NC-b2 positive-differential: 2^64 = limbs [0,1,0,0] against `amount <= 100`.
    // A low-limb (limbs[0]=0) truncation bug would yield 0 <= 100 → spurious Holds;
    // the CORRECT verdict is 2^64 <= 100 → Violated (T210). This fixture turns any
    // Wide→i64 truncation regression red.
    let src = "module main;\nrecord Cap { amount: u256 } where amount <= 100\n\
        pub fn mk() -> Cap { return Cap { amount: 18446744073709551616 }; }\n";
    let got = codes(src, "trunc_witness");
    assert!(
        got.contains(&"T210".to_string()),
        "2^64 <= 100 must be Violated (T210) — a truncation bug would spuriously pass; got: {got:?}"
    );
}

// ── U3-b2: WIDE RHS bound (record site only) ─────────────────────────────────

#[test]
fn wide_bound_on_i64_field_rejected_t213() {
    // NC-b4: a wide (> i64) bound is admitted ONLY on a u256 field. On an i64 field
    // it is a clean reject (T213) — the i64 discharge spine can't hold the bound.
    let src = "module main;\nrecord Bad { x: i64 } where x >= 10000000000000000000\n\
        pub fn mk(v: i64) -> Bad { return Bad { x: v }; }\n";
    let got = codes(src, "wide_bound_i64");
    assert!(
        got.contains(&"T213".to_string()),
        "a wide bound on an i64 field must be T213, got: {got:?}"
    );
}

#[cfg(feature = "solver")]
#[test]
fn wide_bound_satisfied_holds() {
    // The Solidity payoff: a wide cap (10^29 > i64::MAX, a LiteralWide bound). A
    // small balance (10^18) satisfies `amount <= 10^29` → Holds (Narrow value vs
    // Wide bound, both via Z3 Int).
    let src = "module main;\nrecord Balance { amount: u256 } where amount <= 100000000000000000000000000000\n\
        pub fn mk() -> Balance { return Balance { amount: 1000000000000000000 }; }\n";
    let got = codes(src, "wide_bound_holds");
    assert!(got.is_empty(), "10^18 <= 10^29 must Hold, got: {got:?}");
}

#[cfg(feature = "solver")]
#[test]
fn wide_bound_violated_t210() {
    // 10^18 >= 10^29 is false → Violated (Narrow value vs Wide bound).
    let src = "module main;\nrecord Floor { amount: u256 } where amount >= 100000000000000000000000000000\n\
        pub fn mk() -> Floor { return Floor { amount: 1000000000000000000 }; }\n";
    let got = codes(src, "wide_bound_violate");
    assert!(
        got.contains(&"T210".to_string()),
        "10^18 >= 10^29 must be Violated (T210), got: {got:?}"
    );
}

#[cfg(feature = "solver")]
#[test]
fn wide_bound_and_wide_value_holds() {
    // Both sides wide: 10^20 >= 10^19 → Holds (Wide value AND Wide bound).
    let src = "module main;\nrecord Floor { amount: u256 } where amount >= 10000000000000000000\n\
        pub fn mk() -> Floor { return Floor { amount: 100000000000000000000 }; }\n";
    let got = codes(src, "wide_both");
    assert!(got.is_empty(), "10^20 >= 10^19 must Hold, got: {got:?}");
}

// ── regression: reading a refined u256 field (adversarial-review find) ─────────

#[test]
fn reading_refined_u256_field_does_not_ice() {
    // Reading a refined u256 field must preserve the supported sidecar without an ICE.
    let src = "module main;\nrecord Src { amount: u256 } where amount >= 0\n\
        pub fn read(s: Src) -> u256 { return s.amount; }\n";
    let got = codes(src, "field_read");
    assert!(
        got.is_empty(),
        "reading a refined u256 field must not ICE/error, got: {got:?}"
    );
}

#[test]
fn reading_wide_refined_u256_field_does_not_ice() {
    // Same, with a WIDE (LiteralWide) bound — the wide clause must propagate
    // through the field read like a small one, not ICE.
    let src = "module main;\nrecord Src { amount: u256 } where amount <= 100000000000000000000000000000\n\
        pub fn read(s: Src) -> u256 { return s.amount; }\n";
    let got = codes(src, "wide_field_read");
    assert!(
        got.is_empty(),
        "reading a wide-refined u256 field must not ICE/error, got: {got:?}"
    );
}
