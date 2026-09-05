//! ACTOR-LIVE AL-1 — per-dispatch fuel refill (docs/specs/actor-live.md).
//!
//! An actor's SIGIL fuel is a per-DISPATCH grant, not a whole-life budget: the actor runtime's
//! `Store` is long-lived across handler calls, so before AL-1 a resident actor consumed its budget
//! cumulatively and died forever (the first ACTOR-LIVE wall). AL-1 restores the grant before every
//! TOP-LEVEL dispatch (`deliver_message`), mirroring the wasmtime backstop's per-dispatch
//! `set_fuel`. These tests pin: (1) a resident actor now survives unboundedly many dispatches;
//! (2) the per-dispatch bound still holds — an over-budget SINGLE dispatch traps; (3) the refill is
//! TOP-LEVEL-ONLY — a synchronous re-entrant call-tree (ask within a handler) shares ONE grant, so
//! it is not a hole through which an actor buys unbounded fuel mid-dispatch (X-AL2).

use sigil_abi::RuntimeTypeSpec;
use sigil_runtime::{
    RuntimeActorSpec, RuntimeHandlerSpec, RuntimeHost, RuntimeImportSpec, RuntimeModuleSpec,
};

/// Entry actor `Main` with a `Start` handler (id 0) and a `Sub` handler (id 1) for the re-entrant
/// test. `init_export: None`, zero-param handlers — the RT-CENSUS-style hand-WAT harness.
fn spec(budget: u64) -> RuntimeModuleSpec {
    RuntimeModuleSpec {
        module_name: "al1".to_owned(),
        fuel_budget: budget,
        imports: RuntimeImportSpec::phase_one(),
        actors: vec![RuntimeActorSpec {
            name: "Main".to_owned(),
            actor_type_id: 0,
            is_entry: true,
            init_export: None,
            init_params: vec![],
            handlers: vec![
                RuntimeHandlerSpec {
                    name: "Start".to_owned(),
                    handler_id: 0,
                    export_name: "Main__Start".to_owned(),
                    params: vec![],
                    ret: RuntimeTypeSpec::I64,
                },
                RuntimeHandlerSpec {
                    name: "Sub".to_owned(),
                    handler_id: 1,
                    export_name: "Main__Sub".to_owned(),
                    params: vec![],
                    ret: RuntimeTypeSpec::I64,
                },
            ],
            state_layout: vec![],
            state_size: 0,
            init_replay_safe: false,
        }],
    }
}

/// `Start` burns `burn` fuel then (if `self_send`) re-enqueues itself → another top-level dispatch.
/// `Sub` is present but unused here.
fn wat_self_send(burn: i32, self_send: bool) -> Vec<u8> {
    let send_seq = if self_send {
        // self target = ActorId(1) (entry), handler 0 (Start), empty payload.
        r#"(i32.const 1) (i32.const 0) (i32.const 0) (i32.const 0) (call $send)"#
    } else {
        ""
    };
    let src = format!(
        r#"(module
  (import "sigil" "fuel_decrement" (func $fd (param i32)))
  (import "sigil" "send" (func $send (param i32 i32 i32 i32)))
  (memory (export "memory") 1)
  (func (export "Main__Start") (param i32) (result i64)
    (i32.const {burn}) (call $fd)
    {send_seq}
    (i64.const 0))
  (func (export "Main__Sub") (param i32) (result i64)
    (i64.const 0)))"#
    );
    wat::parse_str(&src).expect("WAT parses")
}

/// `Start` burns `start_burn`, then synchronously `ask`s its own `Sub` handler, which burns
/// `sub_burn`. Both run inside ONE top-level dispatch, so under top-level-only refill they share a
/// single grant.
fn wat_reentrant(start_burn: i32, sub_burn: i32) -> Vec<u8> {
    let src = format!(
        r#"(module
  (import "sigil" "fuel_decrement" (func $fd (param i32)))
  (import "sigil" "ask" (func $ask (param i32 i32 i32 i32 i64) (result i64)))
  (memory (export "memory") 1)
  (func (export "Main__Start") (param i32) (result i64)
    (i32.const {start_burn}) (call $fd)
    (i32.const 1) (i32.const 1) (i32.const 0) (i32.const 0) (i64.const 0) (call $ask) (drop)
    (i64.const 0))
  (func (export "Main__Sub") (param i32) (result i64)
    (i32.const {sub_burn}) (call $fd)
    (i64.const 0)))"#
    );
    wat::parse_str(&src).expect("WAT parses")
}

fn drain(budget: u64, wasm: &[u8], limit: usize) -> Result<usize, sigil_runtime::RuntimeError> {
    let s = spec(budget);
    let mut host = RuntimeHost::new(s.fuel_budget);
    host.bootstrap(&s, wasm)?;
    host.drain_messages(limit)
}

// ── (1) the wall is down: a resident actor survives unboundedly many dispatches ──────────────
#[test]
fn resident_actor_survives_many_dispatches() {
    // Budget 256, burn 100/dispatch, self-send, ask for 1000 dispatches. Before AL-1 this died by
    // CUMULATIVE exhaustion on dispatch 3 (256 - 100 - 100 = 56 < 100); after AL-1 the grant is
    // restored each dispatch, so all 1000 are delivered.
    let delivered = drain(256, &wat_self_send(100, true), 1000)
        .expect("a resident actor must survive many dispatches after AL-1");
    assert_eq!(
        delivered, 1000,
        "the refill lets a resident actor run indefinitely; delivered {delivered}/1000"
    );
}

// ── (2) the per-dispatch bound still holds: an over-budget single dispatch traps ─────────────
#[test]
fn over_budget_single_dispatch_still_traps() {
    // burn 300 > budget 256 in ONE dispatch. The per-dispatch refill does NOT grant unbounded fuel
    // WITHIN a dispatch — an infinite/over-budget handler must still trap (MI-1). No self-send, so
    // exactly one dispatch is attempted.
    let r = drain(256, &wat_self_send(300, false), 4);
    assert!(
        r.is_err(),
        "an over-budget single dispatch must still trap after AL-1; got {r:?}"
    );
}

// ── (3) the refill is TOP-LEVEL-ONLY: a synchronous call-tree shares ONE grant (X-AL2) ───────
#[test]
fn reentrant_call_tree_shares_one_grant() {
    // Start burns 200, then asks Sub (re-entrant, same dispatch) which burns 100. If the refill
    // fired on the re-entrant `ask` path, Sub would get a fresh 256 and the tree would survive.
    // Because refill is top-level-only, the whole tree shares ONE grant of 256: 256 - 200 = 56 <
    // 100 → Sub traps. This proves a handler cannot buy unbounded fuel mid-dispatch via re-entrancy.
    let r = drain(256, &wat_reentrant(200, 100), 4);
    assert!(
        r.is_err(),
        "a re-entrant call-tree must share one grant (top-level-only refill); got {r:?}"
    );

    // Control: the SAME tree that FITS one grant (200 + 50 = 250 <= 256) completes — confirming the
    // trap above is the shared-grant bound, not an unrelated failure.
    let ok =
        drain(256, &wat_reentrant(200, 50), 4).expect("a call-tree within one grant must complete");
    assert_eq!(
        ok, 1,
        "the in-budget re-entrant tree delivers its one message"
    );
}
