//! The state-cap origin gate (C014) end to end: the premise "a capability
//! read from actor state is full" is ENFORCED at the store, not assumed.
//!
//! Every read of a cap-typed actor-state field is classified as full
//! authority — by the slot escape gate (C013's `StateRead => Full`), by the Z3
//! prover (a state-read cap variable gets the full mask) and by the Lean
//! verifier. Before C014 nothing checked what `init` STORED there: the type
//! checker makes a non-`mut` field writable only in `init` (T123) and forbids
//! a `mut` cap field (C011), but `init(f: Fuel) { fuel = f.restrict(burn); }`
//! compiled on `main`, every handler then read `fuel` as full, and
//! `use_full(fuel.draw(10))` — or a `slot_put(hold, fuel.draw(10))` the slot
//! gate waved through as a full put — handed a restricted capability to a
//! full-authority sink. `slot_escape::check_function` now rejects any
//! `StateWrite` of a capability whose origin is not one the same classifier
//! accepts (a bare `init` parameter, `mint`, a state read or a direct call
//! result, through `let`/`draw`/`split`).
//!
//! Every assertion is an EXACT code set over the whole default-lane pipeline
//! (`compile_named_module`). The rejecting sets are {C014} alone: the
//! structural capability phase fails the compile before the deferred formal
//! verdict is appended, and the same early-out holds with `solver` on, so this
//! file carries no `cfg` — its solver-lane run rests on CI.
//!
//! SC-P4: `anti_stub_a_planted_restrict_in_the_bare_parameter_init_is_detected`
//! plants the one-token violation into the accepted control and requires the
//! detector to fire; the accepted controls prove it stays silent on the
//! documented spellings (the bare parameter, a `draw` off it) and on the
//! corpus actors that populate a cap field positionally through an empty
//! `init`.

use std::fs;
use std::path::PathBuf;

use sigil_compiler::compile_named_module;

/// The b0a repro: `init` stores a `.restrict` result straight into the
/// cap-typed state field, and a handler sinks a `draw` off that field.
const INIT_RESTRICT: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
actor Vault {
    state { fuel: Fuel }
    init(f: Fuel) { fuel = f.restrict(burn); }
    on Use() -> i64 {
        let d = fuel.draw(10);
        return use_full(d);
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let vf = fuel.draw(100);
        let v = spawn::<Vault>(vf);
        v.send(Use());
        return 1;
    }
}
"#;

/// The b0b repro: the same store through a `let` (an `Inherit` edge whose
/// source is the `.restrict`).
const INIT_LET_RESTRICT: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
actor Vault {
    state { fuel: Fuel }
    init(f: Fuel) { let n = f.restrict(burn); fuel = n; }
    on Use() -> i64 {
        let d = fuel.draw(10);
        return use_full(d);
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let vf = fuel.draw(100);
        let v = spawn::<Vault>(vf);
        v.send(Use());
        return 1;
    }
}
"#;

/// The b1b repro: the narrowed state cap is drawn from and put into an
/// actor-state SLOT (silent for C013, whose `StateRead` is full), then taken
/// in another handler and sunk. C014 rejects the store in `init`, so the
/// slot never receives a narrow put.
const INIT_RESTRICT_THEN_STATE_SLOT: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
actor Vault {
    state { hold: Slot<Fuel>, fuel: Fuel }
    init(h: Slot<Fuel>, f: Fuel) { fuel = f.restrict(burn); }
    on Fill() -> i64 {
        let d = fuel.draw(10);
        slot_put(hold, d);
        return 1;
    }
    on Drain() -> i64 {
        let t: Fuel = slot_take(hold);
        return use_full(t);
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let vf = fuel.draw(100);
        let h = slot_new::<Fuel>();
        let v = spawn::<Vault>(h, vf);
        v.send(Fill());
        v.send(Drain());
        return 1;
    }
}
"#;

/// `init` stores a `slot_take` result: a `Taken` origin, only as wide as that
/// slot's puts, which nothing tracks across functions. `Main` fills the slot
/// with a FULL draw (a restricted put into a slot that then escapes to `spawn`
/// would be C013 as well) and the full parameter `f` is parked in the slot,
/// so the store is the only offence.
const INIT_SLOT_TAKE: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
actor Vault {
    state { fuel: Fuel }
    init(h: Slot<Fuel>, f: Fuel) {
        let t: Fuel = slot_take(h);
        fuel = t;
        slot_put(h, f);
    }
    on Use() -> i64 {
        let d = fuel.draw(10);
        return use_full(d);
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let vf = fuel.draw(100);
        let h = slot_new::<Fuel>();
        slot_put(h, vf);
        let spare = fuel.draw(5);
        let v = spawn::<Vault>(h, spare);
        v.send(Use());
        return 1;
    }
}
"#;

/// Positive control and the anti-stub's host: `init` stores its BARE
/// parameter — the documented spelling — and a handler narrows at the point
/// of use. Must keep compiling.
const INIT_BARE_PARAMETER: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
actor Vault {
    state { fuel: Fuel }
    init(f: Fuel) { fuel = f; }
    on Use() -> i64 {
        let d = fuel.draw(10);
        let n = d.restrict(burn);
        let _q = n.draw(1);
        return 1;
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let vf = fuel.draw(100);
        let v = spawn::<Vault>(vf);
        v.send(Use());
        return 1;
    }
}
"#;

/// Positive control: `init` stores a `draw` off its parameter (an `Inherit`
/// chain that bottoms out in a spawn-sink parameter). Must keep compiling.
const INIT_DRAW_OF_PARAMETER: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
actor Vault {
    state { fuel: Fuel }
    init(f: Fuel) { let d = f.draw(50); fuel = d; }
    on Use() -> i64 {
        let d = fuel.draw(10);
        return use_full(d);
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let vf = fuel.draw(100);
        let v = spawn::<Vault>(vf);
        v.send(Use());
        return 1;
    }
}
"#;

/// The handler-narrowing form on a non-`mut` field: the type checker's
/// immutability rule rejects the write before AIR exists, so the pipeline
/// verdict is exactly {T123}; the gate's own coverage of a handler
/// `StateWrite` is pinned at the AIR level in `slot_escape::tests`.
const HANDLER_NARROWS_NONMUT: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
actor Vault {
    state { fuel: Fuel }
    init(f: Fuel) { fuel = f; }
    on Narrow() -> i64 {
        fuel = fuel.restrict(burn);
        return 1;
    }
    on Use() -> i64 {
        let d = fuel.draw(10);
        return use_full(d);
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let vf = fuel.draw(100);
        let v = spawn::<Vault>(vf);
        v.send(Narrow());
        v.send(Use());
        return 1;
    }
}
"#;

/// The handler-narrowing form on a `mut` field: C011 (a `mut` state field
/// must be plain data) plus T128 (wholesale reassignment of a `mut`
/// aggregate field in a handler), both from the type checker.
const HANDLER_NARROWS_MUT: &str = r#"
module sigil;
cap type Fuel { burn, query }
fn use_full(f: Fuel) -> i64 { return 1; }
actor Vault {
    state { mut fuel: Fuel }
    init(f: Fuel) { fuel = f; }
    on Narrow() -> i64 {
        fuel = fuel.restrict(burn);
        return 1;
    }
    on Use() -> i64 {
        let d = fuel.draw(10);
        return use_full(d);
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let vf = fuel.draw(100);
        let v = spawn::<Vault>(vf);
        v.send(Narrow());
        v.send(Use());
        return 1;
    }
}
"#;

/// A CLOSURE call result (the full cap passed straight through) put into a
/// state slot. Only a DIRECT call result is a recognised full origin; a
/// `CallIndirect` result is `Unknown`, so this is C013 and the message must
/// say "direct".
const CLOSURE_CALL_RESULT_PUT: &str = r#"
module sigil;
cap type Fuel { burn, query }
actor Vault {
    state { hold: Slot<Fuel>, fuel: Fuel }
    init(h: Slot<Fuel>, f: Fuel) {}
    on Fill(c: Fuel) -> i64 {
        let pass = fn(x: Fuel) -> Fuel { return x; };
        let y = pass(c);
        slot_put(hold, y);
        return 1;
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let vf = fuel.draw(100);
        let h = slot_new::<Fuel>();
        let v = spawn::<Vault>(h, vf);
        let c = fuel.draw(10);
        v.send(Fill(c));
        return 1;
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

fn repo_file(rel: &str) -> String {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("../..");
    path.push(rel);
    fs::read_to_string(&path).unwrap_or_else(|err| panic!("read {}: {err}", path.display()))
}

#[test]
fn init_restricting_its_parameter_into_a_state_cap_is_c014() {
    assert_eq!(
        pipeline_codes("init_restrict", INIT_RESTRICT),
        exactly(&["C014"])
    );
}

#[test]
fn init_restricting_through_a_let_into_a_state_cap_is_c014() {
    assert_eq!(
        pipeline_codes("init_let_restrict", INIT_LET_RESTRICT),
        exactly(&["C014"])
    );
}

#[test]
fn a_state_cap_narrowed_in_init_cannot_reach_a_state_slot() {
    assert_eq!(
        pipeline_codes("init_restrict_state_slot", INIT_RESTRICT_THEN_STATE_SLOT),
        exactly(&["C014"])
    );
}

#[test]
fn init_storing_a_slot_take_result_into_a_state_cap_is_c014() {
    assert_eq!(
        pipeline_codes("init_slot_take", INIT_SLOT_TAKE),
        exactly(&["C014"])
    );
}

#[test]
fn a_handler_narrowing_a_state_cap_keeps_the_immutability_rejection() {
    assert_eq!(
        pipeline_codes("handler_narrows_nonmut", HANDLER_NARROWS_NONMUT),
        exactly(&["T123"])
    );
    assert_eq!(
        pipeline_codes("handler_narrows_mut", HANDLER_NARROWS_MUT),
        exactly(&["C011", "T128"])
    );
}

#[test]
fn init_storing_the_bare_parameter_still_compiles() {
    assert_eq!(
        pipeline_codes("init_bare_parameter", INIT_BARE_PARAMETER),
        Vec::<String>::new()
    );
}

#[test]
fn init_storing_a_draw_off_its_parameter_still_compiles() {
    assert_eq!(
        pipeline_codes("init_draw_of_parameter", INIT_DRAW_OF_PARAMETER),
        Vec::<String>::new()
    );
}

/// SC-P4 anti-stub: plant the one-token violation (`fuel = f;` becomes
/// `fuel = f.restrict(burn);`) into the accepted control and require the
/// detector to fire with exactly C014.
#[test]
fn anti_stub_a_planted_restrict_in_the_bare_parameter_init_is_detected() {
    let planted = INIT_BARE_PARAMETER.replace(
        "init(f: Fuel) { fuel = f; }",
        "init(f: Fuel) { fuel = f.restrict(burn); }",
    );
    assert_ne!(
        planted, INIT_BARE_PARAMETER,
        "the plant must change the source"
    );
    assert_eq!(
        pipeline_codes("planted_restrict", &planted),
        exactly(&["C014"])
    );
}

/// The diagnostic names the offending store and the function in its message,
/// and the sound alternative (store the bare parameter, restrict the value
/// read from the field) in its hint, so an author can act on it without the
/// module doc.
#[test]
fn c014_message_and_hint_name_the_store_and_the_sound_alternative() {
    let err = compile_named_module("init_restrict.sigil", INIT_RESTRICT)
        .expect_err("the init-restrict program rejects");
    let diagnostic = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "C014")
        .expect("exactly one C014 is asserted above");
    let message = diagnostic.message();
    assert!(
        message.contains("cap-typed actor-state field")
            && message.contains("may carry a `.restrict`ed authority set")
            && message.contains("counts as full authority"),
        "message must name the store, the origin and the premise: {message}"
    );
    let hint = diagnostic.hint().unwrap_or_default();
    assert!(
        hint.contains("bare `init` parameter") && hint.contains(".restrict("),
        "hint must state the store-the-parameter, restrict-at-use alternative: {hint}"
    );
}

/// Precision of the C013 rule text: only a DIRECT call result is a recognised
/// full origin. A closure-call (`CallIndirect`) result is `Unknown`, so the
/// closure pass-through put is C013, and the message must not claim that "a
/// call result" in general is recognised.
#[test]
fn c013_rule_names_a_direct_call_result_and_rejects_a_closure_call_result() {
    let err = compile_named_module("closure_call_result_put.sigil", CLOSURE_CALL_RESULT_PUT)
        .expect_err("the closure pass-through put rejects");
    let mut codes: Vec<String> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect();
    codes.sort();
    codes.dedup();
    assert_eq!(codes, exactly(&["C013"]));
    let diagnostic = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "C013")
        .expect("exactly one C013 is asserted above");
    let message = diagnostic.message();
    assert!(
        message.contains("a direct call result") && !message.contains("or a call result"),
        "the rule must qualify the recognised call result as direct: {message}"
    );
    let hint = diagnostic.hint().unwrap_or_default();
    assert!(
        hint.contains("a direct call result"),
        "the hint must qualify the recognised call result as direct: {hint}"
    );
}

/// The tracked corpus has no actor that assigns a cap-typed state field in
/// `init` and compiles (the one such assignment is the C011 fixture, rejected
/// for C011); the idiomatic actors populate the field POSITIONALLY through an
/// empty `init`, which the runtime writes and no `StateWrite` carries. They
/// must keep compiling on the default lane.
#[test]
fn the_empty_init_positional_corpus_actors_stay_accepted() {
    for rel in [
        "crates/sigil-compiler/tests/z3_corpus/13_reference_monitor.sigil",
        "crates/sigil-compiler/tests/z3_corpus/17_m_of_n_quorum.sigil",
        "crates/sigil-compiler/tests/z3_corpus/18_inter_actor_3_of_3.sigil",
    ] {
        assert_eq!(
            pipeline_codes("corpus", &repo_file(rel)),
            Vec::<String>::new(),
            "{rel} must keep compiling on the default lane"
        );
    }
}
