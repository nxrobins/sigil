//! PPS-4 — the reclamation posture: restart-as-GC.
//!
//! Abandonment is bounded for monotone growth but UNBOUNDED for replace-heavy
//! state, so the v1 posture is: a per-actor persistent-heap byte cap
//! (host-configured, grant-shaped) → exhaustion traps clean and DISTINCT
//! (`PersistentHeapExhausted`, R818) → under `Restart(n)` supervision the
//! restart IS the collector — it discards the heap and REPLAYS a replay-safe
//! `init` with the retained argument handles, so growth restarts from birth.
//! "Let it crash" as memory management, Erlang's freed-on-death heap made
//! literal.
//!
//! The replay-safety line: the compiler marks an init `init_replay_safe` when
//! it performs no cap-table op and no outward effect (fail-closed walk +
//! effects-row gate). Replaying such an init with the SAME retained handles
//! moves no authority — nothing is re-spent or re-minted. An init that DERIVES
//! from its cap (`power = f.draw(10)`) is NOT replay-safe: replay would mint a
//! second sub-cap, so that actor keeps the AG-AL7 preserve-state path and its
//! heap is deliberately not reclaimed.

use sigil_compiler::compile_module;
use sigil_runtime::{ActorId, AuditEventKind, RuntimeError, RuntimeHost};

fn actor_id_of(host: &RuntimeHost, actor_type: &str) -> ActorId {
    *host
        .actors()
        .iter()
        .find(|(_, a)| a.actor_type() == actor_type)
        .unwrap_or_else(|| panic!("no `{actor_type}` actor spawned"))
        .0
}

fn restarts(host: &RuntimeHost) -> usize {
    host.audit_log()
        .events()
        .iter()
        .filter(|e| matches!(e.kind, AuditEventKind::ActorRestarted { .. }))
        .count()
}

/// The canonical PPS shape: cap-init (`init(f: Fuel)` stores the cap) + a
/// growing state vec. `Fill` grows the persistent buffer; the third `Fill`
/// runs after the second one exhausts the cap and triggers the collector.
const GROWING_LOG: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Log>(fuel, supervision: Restart(2));
        w.send(Fill());
        w.send(Fill());
        w.send(Fill());
        w.send(Check());
        return 0;
    }
}
actor Log {
    state { power: Fuel, mut v: Vec<i64> }
    init(f: Fuel) { power = f; let tmp: Vec<i64> = Vec::new(); v = tmp; }
    on Fill() {
        let mut i: i64 = 0;
        while i < 64 {
            let n: i64 = v.push(i * 3 + 1);
            i = i + 1;
        }
    }
    on Check() {
        if v.len() != 64 { trap(); }
        let first: i64 = v.get(0);
        if first != 1 { trap(); }
    }
}
"#;

#[test]
fn exhaustion_restarts_and_reclaims_the_heap() {
    let c = compile_module(GROWING_LOG).expect("compile");
    let mut host = RuntimeHost::new(c.fuel_budget);
    // Roomy enough for one Fill (init + doublings to 64 elements ≈ 1KB),
    // too small for two (the 128-element doubling adds ~1KB more). If the
    // stdlib Vec growth policy changes these constants, retune the cap — the
    // assertions below say which side broke.
    host.set_persistent_cap(2048);
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .expect("bootstrap");
    let delivered = host
        .drain_messages(16)
        .expect("the exhaustion trap must be absorbed by Restart supervision");
    assert_eq!(delivered, 5, "Start + 3 Fill + Check all deliver");
    assert_eq!(
        restarts(&host),
        1,
        "exactly the second Fill exhausts the cap and restarts the actor"
    );
    // Check ran clean (no trap): state was reset to birth by the replayed
    // init, so only the third Fill's 64 elements are present. The collector
    // collected.
    let bytes = host
        .persistent_bytes(actor_id_of(&host, "Log"))
        .expect("the spawned actor has a captured floor");
    assert!(
        bytes <= 2048,
        "post-restart persistent bytes ({bytes}) must sit back under the cap"
    );
}

#[test]
fn unsupervised_exhaustion_fails_loud_with_the_distinct_error() {
    // Same actor, no supervision: the trap must surface as the DISTINCT
    // PersistentHeapExhausted error (R818's runtime side), not a generic
    // arena message — the observable contract the posture is built on.
    let src = GROWING_LOG.replace(", supervision: Restart(2)", "");
    let c = compile_module(&src).expect("compile");
    let mut host = RuntimeHost::new(c.fuel_budget);
    host.set_persistent_cap(2048);
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .expect("bootstrap");
    let err = host
        .drain_messages(16)
        .expect_err("an unsupervised exhaustion must abort the drain");
    assert!(
        matches!(err, RuntimeError::PersistentHeapExhausted { .. }),
        "the trap must be the distinct exhaustion error; got {err:?}"
    );
}

/// The observability fixture has no `Check` and only two Fills: GROWING_LOG's
/// Check asserts the post-restart length and would TRAP here (no cap, no
/// restart), a trap would itself restart-and-reset the floor — masking exactly
/// the growth this test observes — and the whole-life fuel budget (only a
/// restart refills it) covers two Fill dispatches, not three.
const GROWING_LOG_NO_CHECK: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Log>(fuel);
        w.send(Fill());
        w.send(Fill());
        return 0;
    }
}
actor Log {
    state { power: Fuel, mut v: Vec<i64> }
    init(f: Fuel) { power = f; let tmp: Vec<i64> = Vec::new(); v = tmp; }
    on Fill() {
        let mut i: i64 = 0;
        while i < 64 {
            let n: i64 = v.push(i * 3 + 1);
            i = i + 1;
        }
    }
}
"#;

#[test]
fn persistent_bytes_are_observable_and_grow_with_the_heap() {
    let c = compile_module(GROWING_LOG_NO_CHECK).expect("compile");
    let mut host = RuntimeHost::new(c.fuel_budget);
    // Default cap (the whole arena): nothing exhausts, nothing restarts.
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .expect("bootstrap");
    host.drain_messages(1).expect("Start spawns the log actor");
    let log = actor_id_of(&host, "Log");
    let birth = host.persistent_bytes(log).expect("floor captured at spawn");
    host.drain_messages(16).expect("no cap, no trap");
    let grown = host.persistent_bytes(log).expect("floor still captured");
    assert!(
        grown > birth,
        "two Fills must raise the persistent floor ({birth} -> {grown})"
    );
    assert_eq!(restarts(&host), 0, "no cap pressure, no restart");
    assert_eq!(
        host.persistent_cap(),
        65536,
        "default cap is the arena size"
    );
}

/// An init that DERIVES from its cap is NOT replay-safe: replay would draw a
/// second sub-cap (a re-spend). Such an actor keeps the preserve-state path —
/// restart refills + resets to the floor, state survives, and the capability
/// table does NOT grow.
const DERIVING_INIT: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let sub = fuel.draw(50);
        let w = spawn::<Worker>(sub, supervision: Restart(1));
        w.send(Bump());
        w.send(Bump());
        w.send(Boom());
        w.send(Check());
        return 0;
    }
}
actor Worker {
    state { power: Fuel, mut n: i64 }
    init(f: Fuel) { power = f.draw(10); n = 0; }
    on Bump() { n = n + 1; }
    on Boom() -> i64 { trap(); }
    on Check() {
        if n != 2 { trap(); }
    }
}
"#;

#[test]
fn deriving_init_preserves_state_and_never_respends() {
    let c = compile_module(DERIVING_INIT).expect("compile");
    let spec = c
        .runtime_module
        .actors
        .iter()
        .find(|a| a.name == "Worker")
        .expect("Worker spec");
    assert!(
        !spec.init_replay_safe,
        "an init that draws from its cap must NOT be marked replay-safe"
    );
    let mut host = RuntimeHost::new(c.fuel_budget);
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .expect("bootstrap");
    let caps_before_drain = 0; // table populated during drain; counted after
    let _ = caps_before_drain;
    let delivered = host
        .drain_messages(16)
        .expect("the Boom trap is absorbed by Restart(1)");
    assert_eq!(delivered, 5, "Start + 2 Bump + Boom + Check all deliver");
    assert_eq!(restarts(&host), 1, "Boom triggers exactly one restart");
    // Check did not trap: `n == 2` SURVIVED the restart — the preserve-state
    // path, because replaying this init would re-draw. And the table holds
    // exactly the three legitimately-minted caps (fuel, the spawn's sub, the
    // init's drawn sub) — a fourth would be the cross-restart re-spend.
    assert_eq!(
        host.capability_table().len(),
        3,
        "restart must not replay a deriving init — no fourth cap may be minted"
    );
}

/// The compiler's replay-safety mark, checked directly on both shapes.
#[test]
fn replay_safety_mark_is_computed_from_the_init_body() {
    let store_only = compile_module(GROWING_LOG).expect("compile");
    let log = store_only
        .runtime_module
        .actors
        .iter()
        .find(|a| a.name == "Log")
        .expect("Log spec");
    assert!(
        log.init_replay_safe,
        "a store-only cap-init (power = f; collections built fresh) is replay-safe"
    );
    let deriving = compile_module(DERIVING_INIT).expect("compile");
    let worker = deriving
        .runtime_module
        .actors
        .iter()
        .find(|a| a.name == "Worker")
        .expect("Worker spec");
    assert!(
        !worker.init_replay_safe,
        "a deriving cap-init (power = f.draw(10)) is not replay-safe"
    );
}
