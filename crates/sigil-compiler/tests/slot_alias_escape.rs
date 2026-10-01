//! The slot escape gate (C013) end to end: `Slot<Cap>` aliasing through a
//! callee parameter, an actor-state field, and a `let s2 = s` copy.
//!
//! Both authority checkers key a slot's contents on the TAKING function's
//! own AIR variable (the Z3 meet over same-variable puts, the Lean at-ceiling
//! cell for a parameter or state slot), so a RESTRICTED capability put
//! through an alias was invisible to the take: `sigil check` accepted the
//! callee-restrict and state-restrict programs below and the runtime handed
//! the restricted cap to a full-authority sink. `slot_escape` closes this by
//! rejecting any possibly-restricted put into a slot that is not a confined
//! `slot_new` local of the same function.
//!
//! Every assertion is an EXACT code set over the whole default-lane pipeline
//! (`compile_named_module`, no solver): the four programs whose restricted
//! put goes through an alias reject with exactly C013; the shapes whose
//! narrowed cap reaches the slot through a call/message SINK instead keep
//! their pre-fix I013 (the linked-Lean sink check), and are C003 on the
//! solver lane (`slot_alias_meet.rs`); the two safe programs keep compiling.
//! Note that when the capability gate rejects, the pipeline reports its
//! diagnostics and the deferred formal verdict is not appended, so the
//! rejecting sets are {C013} rather than {C013, I013}.
//!
//! SC-P4: `anti_stub_a_planted_restrict_in_the_accepted_twin_is_detected`
//! plants the one-line violation into the accepted control and requires the
//! detector to fire; the accepted controls prove it stays silent on clean
//! programs.
//!
//! Solver gate: `#![cfg(not(feature = "solver"))]`. Every expected set here is
//! the SOLVER-OFF pipeline's (I013 from the linked Lean sink, and several
//! empty sets); with `solver` on, the Z3 prover also runs and the same
//! programs carry C003 instead (`slot_alias_meet.rs` pins those, e.g. the
//! full-cap local alias is an empty-meet C003 there). Running this file on the
//! solver lane would fail on verdicts that are correct for that lane, so it is
//! compiled out there. Failure direction: the solver lane loses this file's
//! solver-off assertions, nothing more; the gate itself runs on both lanes,
//! and `slot_alias_meet.rs` pins its C013 verdicts with the solver on.

#![cfg(not(feature = "solver"))]

use std::fs;
use std::path::PathBuf;

use sigil_compiler::compile_named_module;

/// Alias through a CALLEE PARAMETER; the restriction happens inside the
/// callee, so no call or message sink ever sees the narrow cap. The caller
/// takes through `s`, sinks the taken cap, and also puts a full cap through
/// `s` (which made the Z3 meet keyed on `s` equal {full}).
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

/// The same shape WITHOUT the caller's full put. The Z3 meet keyed on `s`
/// would be empty (fail-closed BV 0), but the default lane accepted it and
/// the runtime ran it to completion with the restricted cap consumed.
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

/// Positive control: the callee puts the FULL parameter cap. Genuinely safe
/// (a parameter arrives through a full-mask call sink); must keep compiling.
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

/// Cross-handler through an actor-state slot, restriction inside `Fill`.
/// `Settle` takes, sinks, and puts a full cap through its own read of `hold`.
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

/// The callee puts its (full) parameter; the CALLER passes an already
/// narrowed cap to it. The narrow cap crosses a call sink, which the linked
/// Lean gate rejects (I013) and the Z3 sink rejects (C003, solver lane); the
/// callee's put itself is a full put and is not a C013.
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

/// Same, across handlers: `Fill` puts its (full) payload parameter; the
/// narrowing happens in `Main`, and the narrow cap crosses a MESSAGE sink.
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

/// Local alias `let s2 = s`: the narrow put goes through the copy, the take
/// through the original. `s2` is not a `slot_new` local, so the put is C013.
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

/// Negative control (no alias): both puts go through the confined `s`, so
/// the gate is silent and the existing sink check rejects the narrow take
/// (I013 here, C003 on the solver lane).
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

/// Alias put of a FULL cap, take through the original: safe, and the gate
/// is silent because the cap is full. (The Z3 meet keyed on `s` is empty on
/// the solver lane, a fail-closed over-rejection there, not a hole.)
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

/// Sorted, de-duplicated codes of the whole default-lane pipeline; empty
/// means the program compiled.
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

#[test]
fn restricted_put_through_a_callee_slot_parameter_is_c013() {
    assert_eq!(
        pipeline_codes("callee_restrict", CALLEE_RESTRICT),
        exactly(&["C013"])
    );
}

#[test]
fn restricted_put_through_a_callee_slot_parameter_without_a_caller_put_is_c013() {
    assert_eq!(
        pipeline_codes("callee_restrict_noput", CALLEE_RESTRICT_NOPUT),
        exactly(&["C013"])
    );
}

#[test]
fn restricted_put_into_an_actor_state_slot_is_c013() {
    assert_eq!(
        pipeline_codes("state_restrict", STATE_RESTRICT),
        exactly(&["C013"])
    );
}

#[test]
fn restricted_put_through_a_copied_local_slot_is_c013() {
    assert_eq!(
        pipeline_codes("alias_local", ALIAS_LOCAL),
        exactly(&["C013"])
    );
}

/// The narrow cap reaches the callee through a CALL sink, so the sink check
/// (not the escape gate) rejects: unchanged from before the gate.
#[test]
fn narrow_cap_passed_to_a_filling_callee_keeps_the_sink_rejection() {
    assert_eq!(
        pipeline_codes("alias_callee", ALIAS_CALLEE),
        exactly(&["I013"])
    );
}

/// Same through a MESSAGE sink: unchanged from before the gate.
#[test]
fn narrow_cap_sent_to_a_filling_handler_keeps_the_sink_rejection() {
    assert_eq!(
        pipeline_codes("alias_state", ALIAS_STATE),
        exactly(&["I013"])
    );
}

/// No alias: the confined-slot meet is exact and the gate stays silent, so
/// the verdict is the pre-existing sink rejection.
#[test]
fn unaliased_confined_slot_keeps_the_meet_rejection() {
    assert_eq!(
        pipeline_codes("control_noalias", CONTROL_NOALIAS),
        exactly(&["I013"])
    );
}

#[test]
fn full_put_through_a_callee_slot_parameter_still_compiles() {
    assert_eq!(
        pipeline_codes("callee_norestrict", CALLEE_NORESTRICT),
        Vec::<String>::new()
    );
}

#[test]
fn full_put_through_a_copied_local_slot_still_compiles() {
    assert_eq!(
        pipeline_codes("alias_only", ALIAS_ONLY),
        Vec::<String>::new()
    );
}

/// SC-P4 anti-stub: the accepted control and the rejected program differ by
/// exactly one planted line (`let n = c.restrict(burn); slot_put(s, n);` for
/// `slot_put(s, c);`). Constructing the violation FROM the accepted twin
/// proves the detector reacts to the restriction and not to the shape.
#[test]
fn anti_stub_a_planted_restrict_in_the_accepted_twin_is_detected() {
    let planted = CALLEE_NORESTRICT.replace(
        "    slot_put(s, c);\n",
        "    let n = c.restrict(burn);\n    slot_put(s, n);\n",
    );
    assert_ne!(
        planted, CALLEE_NORESTRICT,
        "the plant must change the source"
    );
    assert_eq!(
        planted, CALLEE_RESTRICT,
        "the plant must be the rejected program"
    );
    assert_eq!(
        pipeline_codes("callee_norestrict", CALLEE_NORESTRICT),
        Vec::<String>::new()
    );
    assert_eq!(pipeline_codes("planted", &planted), exactly(&["C013"]));
}

fn repo_file(rel: &str) -> String {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("../..");
    path.push(rel);
    fs::read_to_string(&path).unwrap_or_else(|err| panic!("read {}: {err}", path.display()))
}

/// The documented cross-handler pattern — a handler putting its own message
/// payload PARAMETER into a state slot (z3 corpus fixture 18) and the tools
/// corpus demo of the same shape — is a full put and stays accepted. A
/// parameter arrives through a full-mask message sink, so the escape gate
/// must not fire on it.
#[test]
fn documented_cross_handler_state_slot_pattern_stays_accepted() {
    for rel in [
        "crates/sigil-compiler/tests/z3_corpus/18_inter_actor_3_of_3.sigil",
        "crates/sigil-compiler/tests/z3_corpus/17_m_of_n_quorum.sigil",
        "tools/slot_aggregation_demo.sigil",
    ] {
        assert_eq!(
            pipeline_codes("corpus", &repo_file(rel)),
            Vec::<String>::new(),
            "{rel} must keep compiling on the default lane"
        );
    }
}

/// The diagnostic names the sound alternative in its hint and the offending
/// put in its message, so an author can act on it without the module doc.
#[test]
fn c013_message_and_hint_name_the_put_and_the_sound_alternative() {
    let err = compile_named_module("callee_restrict.sigil", CALLEE_RESTRICT)
        .expect_err("the callee-restrict program rejects");
    let diagnostic = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "C013")
        .expect("exactly one C013 is asserted above");
    let message = diagnostic.message();
    assert!(
        message.contains("`slot_put(s, n)`") && message.contains("`sigil::fill`"),
        "message must name the put and the function: {message}"
    );
    assert!(
        message.contains("`s` is a parameter"),
        "message must say why the slot escapes: {message}"
    );
    let hint = diagnostic.hint().unwrap_or_default();
    assert!(
        hint.contains("slot_take") && hint.contains(".restrict("),
        "hint must state the restrict-after-take alternative: {hint}"
    );
}

// ── The gate's predicate is wider than its motive ──────────────────────────
//
// Everything above narrows a capability with `.restrict` and then relays it.
// The RULE is not "a restricted cap may not be relayed": it is "a cap with no
// recognised full-authority origin may not be put into an aliasable slot",
// and a `slot_take` result has no such origin. So the three programs below
// reject with no `.restrict` anywhere in them, and the ledgers
// (docs/RESIDUAL_RISKS.md SR-020, docs/SOUNDNESS_MATRIX.md SND-CAP-001) state
// that wider exclusion. Each rejecting source is asserted to contain no
// `restrict` at all, so the claim cannot rot into a restrict-only test.

/// Take-and-put-back through an ACTOR-STATE slot: the capability put back is
/// the very one just taken out, so no authority is lost and no facet exists.
/// The slot still aliases (every handler names the same cell), so the gate
/// cannot distinguish this from a narrowing relay and fails closed.
const CYCLE_STATE: &str = r#"
module sigil;
cap type Fuel { burn, query }
actor Vault {
    state { hold: Slot<Fuel>, fuel: Fuel }
    init(h: Slot<Fuel>, f: Fuel) {}
    on Cycle() -> i64 {
        let c: Fuel = slot_take(hold);
        slot_put(hold, c);
        return 1;
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let vault_fuel = fuel.draw(100);
        let h = slot_new::<Fuel>();
        let v = spawn::<Vault>(h, vault_fuel);
        v.send(Cycle());
        return 1;
    }
}
"#;

/// The same cycle through a `Slot<Fuel>` PARAMETER: the callee borrows the
/// caller's capability out and puts it straight back.
const CYCLE_PARAM: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn cycle(s: Slot<Fuel>) -> i64 {
    let borrowed: Fuel = slot_take(s);
    slot_put(s, borrowed);
    return 0;
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let full1 = fuel.draw(10);
        let s = slot_new::<Fuel>();
        slot_put(s, full1);
        let _c = cycle(s);
        let taken: Fuel = slot_take(s);
        let _b = taken.draw(1);
        return 1;
    }
}
"#;

/// A full capability relayed out of the callee's own confined local slot into
/// the caller's slot parameter. Full authority the whole way; the put is
/// rejected because its cap came out of a `slot_take`.
const RELAY_THROUGH_TWO_SLOTS: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn fill(s: Slot<Fuel>, c: Fuel) -> i64 {
    let local = slot_new::<Fuel>();
    slot_put(local, c);
    let back: Fuel = slot_take(local);
    slot_put(s, back);
    return 0;
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let full1 = fuel.draw(10);
        let s = slot_new::<Fuel>();
        let _f = fill(s, full1);
        let taken: Fuel = slot_take(s);
        let _b = taken.draw(1);
        return 1;
    }
}
"#;

/// The accepted twin of `CYCLE_STATE`/`CYCLE_PARAM`: the identical
/// take-and-put-back, but the slot is a confined `slot_new` local read only
/// by `slot_put`/`slot_take` here, so the variable-keyed meet IS exact.
const CYCLE_CONFINED_LOCAL: &str = r#"
module sigil;
cap type Fuel { burn, query }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let full1 = fuel.draw(100);
        let s = slot_new::<Fuel>();
        slot_put(s, full1);
        let c: Fuel = slot_take(s);
        slot_put(s, c);
        let last: Fuel = slot_take(s);
        let _b = last.draw(1);
        return 1;
    }
}
"#;

/// A relay helper that puts its own full parameter into the caller's slot:
/// a parameter arrives through a full-mask sink, so this is a full put and
/// stays accepted. The expressiveness question the exclusion raises is
/// "can I still write a relay at all", and the answer is yes for this shape.
const RELAY_FULL_PARAMETER: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn stash(s: Slot<Fuel>, c: Fuel) -> i64 {
    slot_put(s, c);
    return 0;
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let full1 = fuel.draw(10);
        let s = slot_new::<Fuel>();
        let _r = stash(s, full1);
        let taken: Fuel = slot_take(s);
        let _b = taken.draw(1);
        return 1;
    }
}
"#;

/// Guard for the three rejecting programs above: the point of this section is
/// that the rejection does NOT depend on a narrowing, so a source that grew a
/// `.restrict` would make the claim vacuous.
fn assert_no_restrict(label: &str, src: &str) {
    assert!(
        !src.contains("restrict"),
        "{label} must contain no `restrict` — that is the whole claim"
    );
}

#[test]
fn take_and_put_back_through_an_actor_state_slot_is_c013_with_no_restrict() {
    assert_no_restrict("CYCLE_STATE", CYCLE_STATE);
    assert_eq!(
        pipeline_codes("cycle_state", CYCLE_STATE),
        exactly(&["C013"])
    );
}

#[test]
fn take_and_put_back_through_a_slot_parameter_is_c013_with_no_restrict() {
    assert_no_restrict("CYCLE_PARAM", CYCLE_PARAM);
    assert_eq!(
        pipeline_codes("cycle_param", CYCLE_PARAM),
        exactly(&["C013"])
    );
}

#[test]
fn relaying_a_full_cap_out_of_a_local_slot_into_a_parameter_slot_is_c013() {
    assert_no_restrict("RELAY_THROUGH_TWO_SLOTS", RELAY_THROUGH_TWO_SLOTS);
    assert_eq!(
        pipeline_codes("relay_two_slots", RELAY_THROUGH_TWO_SLOTS),
        exactly(&["C013"])
    );
}

#[test]
fn take_and_put_back_through_a_confined_local_slot_still_compiles() {
    assert_eq!(
        pipeline_codes("cycle_confined", CYCLE_CONFINED_LOCAL),
        Vec::<String>::new()
    );
}

#[test]
fn a_relay_helper_putting_its_own_full_parameter_still_compiles() {
    assert_eq!(
        pipeline_codes("relay_full_parameter", RELAY_FULL_PARAMETER),
        Vec::<String>::new()
    );
}

/// The exclusion is a property of the SLOT, not of the cycle: `CYCLE_STATE`
/// and `CYCLE_CONFINED_LOCAL` perform the same take-and-put-back and land on
/// opposite verdicts, and moving the confined program's put onto an alias is
/// what flips it. This is the SC-P4 shape for the wider predicate: the
/// detector is shown firing on a planted positive built from the accepted
/// twin, so "the confined form is accepted" cannot be a silent always-accept.
#[test]
fn anti_stub_aliasing_the_confined_cycle_slot_is_what_makes_it_c013() {
    // One line, so the plant needs no newline escapes: `s2` aliases `s`, the
    // take still goes through `s`, and the put now goes through the alias.
    let planted = CYCLE_CONFINED_LOCAL.replace(
        "        slot_put(s, c);",
        "        let s2 = s; slot_put(s2, c);",
    );
    assert_ne!(
        planted, CYCLE_CONFINED_LOCAL,
        "the plant must change the source"
    );
    assert_no_restrict("planted", &planted);
    assert_eq!(
        pipeline_codes("cycle_confined", CYCLE_CONFINED_LOCAL),
        Vec::<String>::new()
    );
    assert_eq!(pipeline_codes("planted", &planted), exactly(&["C013"]));
}

// ── Idiomatic slot programs: what the gate costs in expressiveness ─────────
//
// The tracked corpus has almost no power for this rule: five tracked `.sigil`
// programs make a real `slot_put` call (a sixth names it only in a comment),
// and three of those five put a full handler parameter. So these are the
// idioms an author reaches for, each pinned at its measured verdict.

/// A refill cycle across dispatches: take the budget out of a state slot,
/// draw a unit, put the budget back for the next dispatch. The cap put back
/// came out of a `slot_take`, and the slot is an actor-state slot: C013, with
/// no `.restrict` anywhere.
const REFILL_STATE: &str = r#"
module sigil;
cap type Fuel { burn, query }
actor Meter {
    state { budget: Slot<Fuel>, fuel: Fuel }
    init(b: Slot<Fuel>, f: Fuel) {}
    on Load(c: Fuel) -> i64 {
        slot_put(budget, c);
        return 1;
    }
    on Spend() -> i64 {
        let c: Fuel = slot_take(budget);
        let _unit = c.draw(1);
        slot_put(budget, c);
        return 1;
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let b = slot_new::<Fuel>();
        let mf = fuel.draw(10);
        let m = spawn::<Meter>(b, mf);
        let c = fuel.draw(10);
        m.send(Load(c));
        m.send(Spend());
        return 1;
    }
}
"#;

/// Moving a capability from one state slot to another inside one actor
/// (promote a pending approval to the accepted slot): C013, no `.restrict`.
const MOVE_BETWEEN_STATE_SLOTS: &str = r#"
module sigil;
cap type Fuel { burn, query }
actor Desk {
    state { pending: Slot<Fuel>, accepted: Slot<Fuel>, fuel: Fuel }
    init(p: Slot<Fuel>, a: Slot<Fuel>, f: Fuel) {}
    on Submit(c: Fuel) -> i64 {
        slot_put(pending, c);
        return 1;
    }
    on Accept() -> i64 {
        let c: Fuel = slot_take(pending);
        slot_put(accepted, c);
        return 1;
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let p = slot_new::<Fuel>();
        let a = slot_new::<Fuel>();
        let df = fuel.draw(10);
        let d = spawn::<Desk>(p, a, df);
        let c = fuel.draw(10);
        d.send(Submit(c));
        d.send(Accept());
        return 1;
    }
}
"#;

/// `REFILL_STATE`'s put-back, but the take is done by a helper that RETURNS
/// the capability. A call result is a recognised full-authority origin (the
/// callee's `Return` is a full-mask sink), so the put back is a full put and
/// the gate is silent. This is the default-lane verdict; the solver lane's is
/// not pinned here (its Z3 meet for a take with no own put is the
/// fail-closed empty meet).
const PUT_BACK_VIA_CALL: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn borrow_out(s: Slot<Fuel>) -> Fuel {
    let c: Fuel = slot_take(s);
    return c;
}
actor Meter {
    state { budget: Slot<Fuel>, fuel: Fuel }
    init(b: Slot<Fuel>, f: Fuel) {}
    on Load(c: Fuel) -> i64 {
        slot_put(budget, c);
        return 1;
    }
    on Spend() -> i64 {
        let c: Fuel = borrow_out(budget);
        slot_put(budget, c);
        return 1;
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let b = slot_new::<Fuel>();
        let mf = fuel.draw(10);
        let m = spawn::<Meter>(b, mf);
        let c = fuel.draw(10);
        m.send(Load(c));
        m.send(Spend());
        return 1;
    }
}
"#;

#[test]
fn a_refill_cycle_through_an_actor_state_slot_is_c013_with_no_restrict() {
    assert_no_restrict("REFILL_STATE", REFILL_STATE);
    assert_eq!(
        pipeline_codes("refill_state", REFILL_STATE),
        exactly(&["C013"])
    );
}

#[test]
fn moving_a_cap_between_two_state_slots_is_c013_with_no_restrict() {
    assert_no_restrict("MOVE_BETWEEN_STATE_SLOTS", MOVE_BETWEEN_STATE_SLOTS);
    assert_eq!(
        pipeline_codes("move_state_slots", MOVE_BETWEEN_STATE_SLOTS),
        exactly(&["C013"])
    );
}

#[test]
fn a_put_back_of_a_call_result_still_compiles() {
    assert_eq!(
        pipeline_codes("put_back_via_call", PUT_BACK_VIA_CALL),
        Vec::<String>::new()
    );
}

/// The message states the PREDICATE, not the motive: on a take-and-put-back
/// with no `.restrict` in sight it names the `slot_take` origin, says a full
/// capability counts too, and spells out which origins are full and which
/// slots may take anything else. The hint says the same.
#[test]
fn c013_message_on_a_put_back_states_the_predicate_not_the_motive() {
    let err = compile_named_module("cycle_param.sigil", CYCLE_PARAM)
        .expect_err("the take-and-put-back program rejects");
    let diagnostic = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "C013")
        .expect("exactly one C013 is asserted above");
    let message = diagnostic.message();
    for needle in [
        "`slot_put(s, borrowed)`",
        "every `slot_take` result counts as possibly restricted",
        "even a full capability",
        "The rule: only a capability whose origin is a non-closure parameter, `mint`, an actor-state read or a direct call result",
    ] {
        assert!(
            message.contains(needle),
            "message must contain {needle:?}: {message}"
        );
    }
    let hint = diagnostic.hint().unwrap_or_default();
    assert!(
        hint.contains("EVERY `slot_take` result") && hint.contains("no `.restrict` in the program"),
        "hint must state that the rule is wider than restriction: {hint}"
    );
}
