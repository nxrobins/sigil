//! Solver-lane witness for the slot-alias meet hole and its fix (C013).
//!
//! The Z3 `Slot<Cap>` authority meet ranges over the `slot_put`s made through
//! the TAKE's own AIR variable inside one function, so a restricted cap put
//! through an ALIAS of the slot (a callee parameter, a state field read in
//! another handler, `let s2 = s`) is outside the meet. If the taking function
//! also puts a full cap through its own name for the slot, the meet is
//! {full} and a full-authority sink accepts the narrow cap.
//!
//! Two layers are pinned, as exact code sets:
//!
//! * `prover_codes` runs the sole Z3 prover DIRECTLY on the lowered AIR
//!   (bypassing `capability::verify`), so its verdict is the meet's and
//!   nothing else's. The prover-alone acceptance of the two laundering
//!   programs is deliberately KEPT as a pinned fact: it is the reason the
//!   structural gate exists, and this test turns red the moment the meet
//!   itself starts seeing aliases (at which point the gate can be revisited).
//! * `pipeline_codes` runs the whole solver-on pipeline, where the escape
//!   gate (`slot_escape`, in `capability::verify`'s structural phase) rejects
//!   every alias put of a possibly-restricted cap with C013 BEFORE the prover
//!   runs. When the capability gate rejects, the pipeline reports its codes
//!   and drops the deferred formal verdict, so these sets never carry I013.
//!
//! Solver gate: `#![cfg(feature = "solver")]` — every C003 here is a Z3
//! verdict. This file rests on the CI solver lane; it cannot run on a
//! solver-off machine. Its default-lane twin is `slot_alias_escape.rs`.

#![cfg(feature = "solver")]

use sigil_compiler::diagnostics::{Diagnostic, Severity};
use sigil_compiler::source::SourceFile;
use sigil_compiler::{
    CompileOptions, air, air_capability_v2, compile_named_module, name_resolution, parser,
    type_check,
};

/// Alias through a CALLEE PARAMETER; restriction happens inside the callee so
/// no call sink ever sees the narrow cap. The caller's own full put makes the
/// meet keyed on `s` equal {full}: the prover alone accepts (the hole), the
/// pipeline rejects at the escape gate.
const CALLEE_RESTRICT: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
fn fill(s: Slot<Fuel>, c: Fuel) -> i64 {
    let n = c.restrict(burn);
    slot_put(s, n);
    return 0;
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let full1 = fuel.draw(10);
        let full2 = fuel.draw(10);
        let s = slot_new::<Fuel>();
        let _f = fill(s, full1);
        let taken: Fuel = slot_take(s);
        let r = use_full(taken);
        slot_put(s, full2);
        return r;
    }
}
"#;

/// Same shape WITHOUT the caller's full put: the meet keyed on `s` is empty,
/// the take is BV 0, and the prover rejects (fail-closed over-rejection).
/// The pipeline still rejects at the escape gate first.
const CALLEE_RESTRICT_NOPUT: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
fn fill(s: Slot<Fuel>, c: Fuel) -> i64 {
    let n = c.restrict(burn);
    slot_put(s, n);
    return 0;
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let full1 = fuel.draw(10);
        let s = slot_new::<Fuel>();
        let _f = fill(s, full1);
        let taken: Fuel = slot_take(s);
        return use_full(taken);
    }
}
"#;

/// Positive control: the callee puts the FULL parameter cap. Genuinely safe;
/// every layer accepts.
const CALLEE_NORESTRICT: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
fn fill(s: Slot<Fuel>, c: Fuel) -> i64 {
    slot_put(s, c);
    return 0;
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let full1 = fuel.draw(10);
        let full2 = fuel.draw(10);
        let s = slot_new::<Fuel>();
        let _f = fill(s, full1);
        let taken: Fuel = slot_take(s);
        let r = use_full(taken);
        slot_put(s, full2);
        return r;
    }
}
"#;

/// Negative control (no alias): narrow and full both put through `s` itself.
/// The meet is burn-only and the sink rejects with C003 (the fixture-19
/// shape); the escape gate is silent because `s` is confined.
const CONTROL_NOALIAS: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let raw = fuel.draw(10);
        let narrow = raw.restrict(burn);
        let full = fuel.draw(10);
        let s = slot_new::<Fuel>();
        slot_put(s, narrow);
        let taken: Fuel = slot_take(s);
        let r = use_full(taken);
        slot_put(s, full);
        return r;
    }
}
"#;

/// Local alias `let s2 = s`: the meet keyed on `s` is {full} (prover accepts,
/// the same weakness), the pipeline rejects at the escape gate.
const ALIAS_LOCAL: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let raw = fuel.draw(10);
        let narrow = raw.restrict(burn);
        let full = fuel.draw(10);
        let s = slot_new::<Fuel>();
        let s2 = s;
        slot_put(s2, narrow);
        let taken: Fuel = slot_take(s);
        let r = use_full(taken);
        slot_put(s, full);
        return r;
    }
}
"#;

/// Alias put of a FULL cap, take through the original. Safe; the escape gate
/// is silent (full cap). The meet keyed on `s` is empty, so the prover
/// over-rejects with C003 — fail-closed, not a hole, and pinned as such.
const ALIAS_ONLY: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let full = fuel.draw(10);
        let s = slot_new::<Fuel>();
        let s2 = s;
        slot_put(s2, full);
        let taken: Fuel = slot_take(s);
        return use_full(taken);
    }
}
"#;

/// The callee puts its (full) parameter; the CALLER passes a narrow cap to
/// it. The narrow cap crosses a call sink: C003 at every layer, no C013.
const ALIAS_CALLEE: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
fn fill(s: Slot<Fuel>, c: Fuel) -> i64 {
    slot_put(s, c);
    return 0;
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let raw = fuel.draw(10);
        let narrow = raw.restrict(burn);
        let full = fuel.draw(10);
        let s = slot_new::<Fuel>();
        let _f = fill(s, narrow);
        let taken: Fuel = slot_take(s);
        let r = use_full(taken);
        slot_put(s, full);
        return r;
    }
}
"#;

/// Cross-handler through an actor-state slot, restriction inside `Fill`.
/// `Settle`'s same-function full put makes its meet {full}: the prover alone
/// accepts (the hole), the pipeline rejects at the escape gate.
const STATE_RESTRICT: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
actor Vault {
    state { hold: Slot<Fuel>, fuel: Fuel }
    init(h: Slot<Fuel>, f: Fuel) {}
    on Fill(c: Fuel) -> i64 {
        let n = c.restrict(burn);
        slot_put(hold, n);
        return 1;
    }
    on Settle() -> i64 {
        let full = fuel.draw(10);
        let taken: Fuel = slot_take(hold);
        let r = use_full(taken);
        slot_put(hold, full);
        return r;
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let approval = fuel.draw(10);
        let vault_fuel = fuel.draw(100);
        let h = slot_new::<Fuel>();
        let v = spawn::<Vault>(h, vault_fuel);
        v.send(Fill(approval));
        v.send(Settle());
        return 1;
    }
}
"#;

/// Same across handlers with the narrowing in `Main`: the narrow cap crosses
/// a MESSAGE sink, so it is C003 at every layer and no C013.
const ALIAS_STATE: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
actor Vault {
    state { hold: Slot<Fuel>, fuel: Fuel }
    init(h: Slot<Fuel>, f: Fuel) {}
    on Fill(c: Fuel) -> i64 {
        slot_put(hold, c);
        return 1;
    }
    on Settle() -> i64 {
        let full = fuel.draw(10);
        let taken: Fuel = slot_take(hold);
        let r = use_full(taken);
        slot_put(hold, full);
        return r;
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let raw = fuel.draw(10);
        let narrow = raw.restrict(burn);
        let vault_fuel = fuel.draw(100);
        let h = slot_new::<Fuel>();
        let v = spawn::<Vault>(h, vault_fuel);
        v.send(Fill(narrow));
        v.send(Settle());
        return 1;
    }
}
"#;

fn cap_codes(diags: &[Diagnostic]) -> Vec<String> {
    let mut codes: Vec<String> = diags
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .map(|d| d.code().as_str().to_string())
        .filter(|c| c.starts_with('C'))
        .collect();
    codes.sort();
    codes.dedup();
    codes
}

/// The sole AIR-cap prover, DIRECTLY (the `air_cap_rejection_soundness.rs`
/// pipeline), so the verdict is the Z3 meet's and nothing else's.
fn prover_codes(label: &str, src: &str) -> Vec<String> {
    let source = SourceFile::new(format!("{label}.sigil"), src);
    let (ast, parse_diags) = parser::parse(&source);
    assert!(
        !parse_diags.iter().any(|d| d.severity() == Severity::Error),
        "{label}: unexpected parse error"
    );
    let resolved = name_resolution::resolve(&ast).expect("resolve");
    let (typed, registry) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .unwrap_or_else(|d| {
            panic!(
                "{label}: type-check failed: {:?}",
                d.iter().map(|x| x.code().as_str()).collect::<Vec<_>>()
            )
        });
    let air = air::lower(&typed);
    match air_capability_v2::verify_air_capabilities(&air, &registry) {
        Ok(_) => Vec::new(),
        Err(diags) => cap_codes(&diags),
    }
}

fn pipeline_codes(label: &str, src: &str) -> Vec<String> {
    match compile_named_module(format!("{label}.sigil"), src) {
        Ok(_) => Vec::new(),
        Err(err) => {
            let mut codes: Vec<String> = err
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_string())
                .collect();
            codes.sort();
            codes.dedup();
            codes
        }
    }
}

fn exactly(codes: &[&str]) -> Vec<String> {
    codes.iter().map(|c| c.to_string()).collect()
}

/// THE HOLE, prover-alone: accepted. THE FIX, pipeline: C013.
#[test]
fn slot_alias_through_callee_parameter_is_outside_the_meet_and_closed_by_c013() {
    assert_eq!(
        prover_codes("callee_restrict", CALLEE_RESTRICT),
        Vec::<String>::new()
    );
    assert_eq!(
        pipeline_codes("callee_restrict", CALLEE_RESTRICT),
        exactly(&["C013"])
    );
}

/// Same hole across actor handlers through a state slot.
#[test]
fn slot_alias_through_state_field_is_outside_the_meet_and_closed_by_c013() {
    assert_eq!(
        prover_codes("state_restrict", STATE_RESTRICT),
        Vec::<String>::new()
    );
    assert_eq!(
        pipeline_codes("state_restrict", STATE_RESTRICT),
        exactly(&["C013"])
    );
}

/// Fail-closed sibling: with no caller-side put the empty meet rejects at the
/// prover; the pipeline rejects earlier, at the escape gate.
#[test]
fn slot_alias_take_with_no_local_put_is_rejected_at_both_layers() {
    assert_eq!(
        prover_codes("callee_restrict_noput", CALLEE_RESTRICT_NOPUT),
        exactly(&["C003"])
    );
    assert_eq!(
        pipeline_codes("callee_restrict_noput", CALLEE_RESTRICT_NOPUT),
        exactly(&["C013"])
    );
}

/// Positive control: the safe program is accepted by every layer.
#[test]
fn slot_alias_through_callee_with_full_cap_is_accepted() {
    assert_eq!(
        prover_codes("callee_norestrict", CALLEE_NORESTRICT),
        Vec::<String>::new()
    );
    assert_eq!(
        pipeline_codes("callee_norestrict", CALLEE_NORESTRICT),
        Vec::<String>::new()
    );
}

/// Negative control: no alias, the meet sees the narrow put and rejects; the
/// escape gate is silent on a confined slot.
#[test]
fn slot_meet_without_alias_rejects_a_restricted_put() {
    assert_eq!(
        prover_codes("control_noalias", CONTROL_NOALIAS),
        exactly(&["C003"])
    );
    assert_eq!(
        pipeline_codes("control_noalias", CONTROL_NOALIAS),
        exactly(&["C003"])
    );
}

/// Local `let s2 = s` alias: prover alone accepts (the meet weakness), the
/// pipeline rejects at the escape gate.
#[test]
fn local_slot_alias_is_missed_by_the_prover_and_closed_by_c013() {
    assert_eq!(
        prover_codes("alias_local", ALIAS_LOCAL),
        Vec::<String>::new()
    );
    assert_eq!(
        pipeline_codes("alias_local", ALIAS_LOCAL),
        exactly(&["C013"])
    );
}

/// A full cap through a local alias: safe, gate silent, and the empty meet
/// over-rejects at the prover (fail-closed, pinned so it cannot flip to an
/// acceptance without review).
#[test]
fn full_cap_through_a_local_alias_is_an_empty_meet_over_rejection() {
    assert_eq!(prover_codes("alias_only", ALIAS_ONLY), exactly(&["C003"]));
    assert_eq!(pipeline_codes("alias_only", ALIAS_ONLY), exactly(&["C003"]));
}

/// The narrow cap crossing a CALL or MESSAGE sink is the ordinary sink
/// rejection; the escape gate does not fire on the callee's full put.
#[test]
fn narrow_cap_crossing_a_sink_into_a_filling_callee_or_handler_is_c003() {
    assert_eq!(
        prover_codes("alias_callee", ALIAS_CALLEE),
        exactly(&["C003"])
    );
    assert_eq!(
        pipeline_codes("alias_callee", ALIAS_CALLEE),
        exactly(&["C003"])
    );
    assert_eq!(prover_codes("alias_state", ALIAS_STATE), exactly(&["C003"]));
    assert_eq!(
        pipeline_codes("alias_state", ALIAS_STATE),
        exactly(&["C003"])
    );
}
