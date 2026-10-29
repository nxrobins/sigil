//! R009: outer-ring code cannot message, spawn, or restrict, split, draw or mint a capability.
//!
//! `wasm::emit` builds a two-ring program's outer module with a reduced host-import set that has
//! no import for any of these. Before R009, an outer-ring `send`, `ask`, or unbound `.split()`,
//! `.draw()`, `.restrict()` or `mint` passed every checker and then panicked the emitter (`ICE:
//! send import unavailable in current import set`, and the same for `ask`, `cap_split`,
//! `cap_restrict` and `cap_mint`). R009 refuses each such statement before emission.
//!
//! Most of those shapes now stop earlier: an actor cannot be declared in an outer-ring module
//! (R014), and outer-ring code cannot own a capability (R001). Two source shapes still reach
//! R009: a message (`send` or `ask`) from an outer-ring function to an inner-ring actor it is
//! handed an `ActorRef` to, and an unbound `mint` in a function that holds the minting authority.
//! Each shape below is pinned to the exact code set it gets, beside its inner-ring twin, the same
//! source without `#[ring(outer)]`, which compiles.
//!
//! Every operation is also covered on AIR, where R009 stands as the backstop whatever the source
//! checks catch first: each inner-ring program compiles, and the same AIR with its functions
//! flipped to the outer ring is refused once per function and operation. The emitter is shown to
//! panic on exactly the AIR the gate refuses, and to encode the AIR it passes.

use std::panic::{AssertUnwindSafe, catch_unwind};

use sigil_compiler::ast::Ring;
use sigil_compiler::{compile_named_module, ring_check, wasm};

const OUTER: &str = "#[ring(outer)] ";

/// The codes `source` is rejected with, sorted and de-duplicated; empty when it compiles.
fn codes(name: &str, source: &str) -> Vec<String> {
    match compile_named_module(name, source) {
        Ok(_) => Vec::new(),
        Err(err) => {
            let mut codes: Vec<String> = err
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_owned())
                .collect();
            codes.sort();
            codes.dedup();
            codes
        }
    }
}

/// `outer` is refused with exactly `code`, and its inner-ring twin compiles.
fn assert_refused_in_the_outer_ring_only(name: &str, outer: &str, code: &str) {
    assert!(
        outer.starts_with(OUTER),
        "{name}: the shape must be an outer-ring program"
    );
    assert_eq!(codes(name, outer), [code], "{name}: in the outer ring");
    let inner = outer.replacen(OUTER, "", 1);
    assert_eq!(
        codes(name, &inner),
        Vec::<String>::new(),
        "{name}: the inner-ring twin compiles"
    );
}

/// The reported reproduction, verbatim.
const ACTOR_SEND: &str = "#[ring(outer)] module tool;
entry actor Main {
    on Start(w: ActorRef<Worker>) -> i64 {
        w.send(Ping());
        return 0;
    }
}
actor Worker {
    on Ping() {}
}
";

/// The reported reproduction now stops at its actors' declarations (R014), before R009 is
/// reached; its inner-ring twin compiles and sends.
#[test]
fn outer_ring_actor_send_is_refused() {
    assert_refused_in_the_outer_ring_only("actor_send", ACTOR_SEND, "R014");
}

/// Messaging an OUTER-ring actor from outer-ring source stops at the actor's declaration (R014);
/// messaging an inner-ring actor from an outer-ring function still reaches R009
/// (`outer_ring_function_messaging_an_inner_actor_is_r009`).
#[test]
fn outer_ring_messaging_is_refused() {
    assert_refused_in_the_outer_ring_only(
        "fn_send",
        "#[ring(outer)] module tool;
fn poke(w: ActorRef<Worker>) -> i64 { w.send(Ping()); return 0; }
actor Worker {
    on Ping() {}
}
",
        "R014",
    );
    assert_refused_in_the_outer_ring_only(
        "actor_ask",
        "#[ring(outer)] module tool;
entry actor Main {
    on Start(w: ActorRef<Worker>) -> i64 {
        let r: i64 = w.ask(Query(1), 100);
        return r;
    }
}
actor Worker {
    on Query(x: i64) -> i64 { return x; }
}
",
        "R014",
    );
}

/// An outer-ring function handed an `ActorRef` to an INNER-ring actor. Nothing earlier refuses
/// it: the actor's declaration is in the inner ring, so R014 does not apply, and the reference
/// type-checks across the rings.
const CROSS_RING_SEND: &str = "module app;
entry actor Main {
    on Start() -> i64 { return 0; }
}
actor Worker {
    on Ping() {}
    on Query(x: i64) -> i64 { return x; }
}
#[ring(outer)] module ext;
pub fn poke(w: ActorRef<Worker>) -> i64 { w.send(Ping()); return 0; }
";

/// Messaging an inner-ring actor from an outer-ring function reaches R009 from source: `send`
/// and `ask` on the `ActorRef` the function is handed are each exactly R009, and the same
/// function in an inner-ring module compiles.
#[test]
fn outer_ring_function_messaging_an_inner_actor_is_r009() {
    let ask = CROSS_RING_SEND.replace(
        "w.send(Ping()); return 0;",
        "let r: i64 = w.ask(Query(1), 100); return r;",
    );
    assert_ne!(ask, CROSS_RING_SEND, "the rewrite must reach the call");
    for (name, source) in [
        ("cross_ring_send", CROSS_RING_SEND.to_string()),
        ("cross_ring_ask", ask),
    ] {
        assert_eq!(codes(name, &source), ["R009"], "{name}: in the outer ring");
        let inner = source.replace("#[ring(outer)] module ext;", "module ext;");
        assert_ne!(inner, source, "{name}: the rewrite must reach the module");
        assert_eq!(
            codes(name, &inner),
            Vec::<String>::new(),
            "{name}: the inner-ring twin compiles"
        );
    }
}

/// R001 refuses an outer-ring binding of an owned capability, so each operation's result is left
/// unbound here. A state capability belongs to an actor, which R014 refuses in the outer ring;
/// an unbound `mint` is the capability shape that reaches R009 from source.
#[test]
fn outer_ring_capability_operations_are_refused() {
    for (name, operation) in [
        ("split", "fuel.split(50);"),
        ("draw", "fuel.draw(10);"),
        ("restrict", "fuel.restrict(burn);"),
    ] {
        assert_refused_in_the_outer_ring_only(
            name,
            &format!(
                "#[ring(outer)] module tool;
cap type Fuel {{ burn, query }}
entry actor Main {{
    state {{ fuel: Fuel }}
    on Start() -> i64 {{
        {operation}
        return 1;
    }}
}}
"
            ),
            "R014",
        );
    }
    assert_refused_in_the_outer_ring_only("mint", OUTER_MINT, "R009");
}

/// An outer-ring function that mints a capability it never binds.
const OUTER_MINT: &str = "#[ring(outer)] module tool;
cap type Admin { mint_file }
cap type FileAccess mintable_by Admin { read, write }
record File { id: i64 }
fn make(f: File, admin: &Admin) -> i64 { mint FileAccess for f; return 0; }
";

/// Inner-ring programs that each use operations the outer module has no import for, with the
/// number of R009 diagnostics the same AIR gets in the outer ring: one per function and
/// operation.
const AIR_CASES: &[(&str, &str, usize)] = &[
    (
        "send",
        "module tool;
entry actor Main {
    on Start(w: ActorRef<Worker>) -> i64 {
        w.send(Ping());
        return 0;
    }
}
actor Worker {
    on Ping() {}
}
",
        1,
    ),
    (
        "ask",
        "module tool;
entry actor Main {
    on Start(w: ActorRef<Worker>) -> i64 {
        let r: i64 = w.ask(Query(1), 100);
        return r;
    }
}
actor Worker {
    on Query(x: i64) -> i64 { return x; }
}
",
        1,
    ),
    (
        "split_and_spawn",
        "module tool;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let child_fuel = fuel.split(50);
        let child = spawn::<Worker>(child_fuel);
        return 1;
    }
}
actor Worker {
    init(fuel: Fuel) {}
    on Ping(x: i64) -> i64 { return x + 1; }
}
",
        2,
    ),
    (
        "draw",
        "module tool;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        fuel.draw(10);
        return 1;
    }
}
",
        1,
    ),
    (
        "restrict",
        "module tool;
cap type Fuel { burn, query }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        fuel.restrict(burn);
        return 1;
    }
}
",
        1,
    ),
    (
        "mint",
        "module tool;
cap type Admin { mint_file }
cap type FileAccess mintable_by Admin { read, write }
record File { id: i64 }
fn make(f: File, admin: &Admin) -> i64 { mint FileAccess for f; return 0; }
",
        1,
    ),
    (
        "two_sends_and_an_ask",
        "module tool;
entry actor Main {
    on Start(w: ActorRef<Worker>) -> i64 {
        w.send(Ping());
        w.send(Ping());
        let r: i64 = w.ask(Query(1), 100);
        return r;
    }
}
actor Worker {
    on Ping() {}
    on Query(x: i64) -> i64 { return x; }
}
",
        2,
    ),
];

/// One diagnostic per function and operation: two `send`s and an `ask` in one handler are two,
/// and a function that splits a capability and spawns with it is two.
#[test]
fn outer_ring_refusal_is_reported_once_per_function_and_operation() {
    for name in ["two_sends_and_an_ask", "split_and_spawn"] {
        let (_, source, expected) = AIR_CASES
            .iter()
            .find(|(case, _, _)| *case == name)
            .expect("a named AIR case");
        let refused = ring_check::check_air_outer_ring_imports(&flipped_air(name, source))
            .expect_err("refused in the outer ring");
        assert_eq!(refused.len(), *expected, "{name}: one per operation");
    }
}

/// The program's compiled AIR with every function moved to the outer ring.
fn flipped_air(name: &str, source: &str) -> sigil_compiler::air::AirProgram {
    let compiled = compile_named_module(name, source).expect("the inner-ring program compiles");
    let mut flipped = compiled.air;
    for function in &mut flipped.functions {
        function.ring = Ring::Outer;
    }
    flipped
}

/// The gate on AIR, for every operation: each inner-ring program passes it, and the same AIR with
/// every function in the outer ring is refused with exactly R009, once per function and
/// operation. The gate is not vacuous: the emitter panics on the AIR it refuses and encodes the
/// AIR it passes.
#[test]
fn gate_refuses_exactly_the_air_the_emitter_cannot_encode() {
    for (name, source, expected) in AIR_CASES {
        let compiled =
            compile_named_module(*name, *source).expect("the inner-ring program compiles");
        assert!(
            ring_check::check_air_outer_ring_imports(&compiled.air).is_ok(),
            "{name}: the inner-ring AIR passes"
        );
        let emitted = wasm::emit(&compiled.air);
        assert!(
            emitted.outer.is_none(),
            "{name}: the AIR the gate passes is emitted, as one inner-ring module"
        );

        let flipped = flipped_air(name, source);
        let refused = ring_check::check_air_outer_ring_imports(&flipped)
            .expect_err("the same AIR in the outer ring is refused");
        let codes: Vec<&str> = refused.iter().map(|d| d.code().as_str()).collect();
        assert_eq!(codes, vec!["R009"; *expected], "{name}: in the outer ring");
        assert!(
            catch_unwind(AssertUnwindSafe(|| wasm::emit(&flipped))).is_err(),
            "{name}: anti-stub: the emitter cannot encode the AIR the gate refuses"
        );
    }
}
