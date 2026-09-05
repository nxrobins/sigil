//! ACTOR-LIVE AL-2 — per-dispatch arena reset (docs/specs/actor-live.md).
//!
//! The per-actor 64 KB bump arena (`arena_cursors`, used by the guest `alloc` host fn) is scratch
//! for a single dispatch, but the resident `Store` keeps it across handler calls — so before AL-2 a
//! resident actor's cursor grew monotonically and it died "arena exhausted" even with AL-1's fuel
//! refill (the second ACTOR-LIVE wall). AL-2 resets the cursor before every TOP-LEVEL dispatch
//! (`deliver_message`), the same discipline as AL-1. These tests pin: (1) a resident allocating
//! actor now survives unboundedly many dispatches; (2) the per-dispatch arena bound still holds — a
//! single dispatch allocating more than 64 KB traps; (3) the reset is TOP-LEVEL-ONLY — a synchronous
//! re-entrant call-tree (ask within a handler) shares ONE arena, so a callee never gets a fresh
//! arena and cannot stomp the caller's live allocations (X-AL2).

use sigil_abi::RuntimeTypeSpec;
use sigil_runtime::{
    RuntimeActorSpec, RuntimeHandlerSpec, RuntimeHost, RuntimeImportSpec, RuntimeModuleSpec,
};

fn spec() -> RuntimeModuleSpec {
    RuntimeModuleSpec {
        module_name: "al2".to_owned(),
        fuel_budget: 4096,
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

/// `Start` allocs `bytes` of scratch, then (if `self_send`) re-enqueues itself.
fn wat_self_send(bytes: i32, self_send: bool) -> Vec<u8> {
    let send_seq = if self_send {
        r#"(i32.const 1) (i32.const 0) (i32.const 0) (i32.const 0) (call $send)"#
    } else {
        ""
    };
    let src = format!(
        r#"(module
  (import "sigil" "alloc" (func $alloc (param i32) (result i32)))
  (import "sigil" "send" (func $send (param i32 i32 i32 i32)))
  (memory (export "memory") 1)
  (func (export "Main__Start") (param i32) (result i64)
    (i32.const {bytes}) (call $alloc) (drop)
    {send_seq}
    (i64.const 0))
  (func (export "Main__Sub") (param i32) (result i64)
    (i64.const 0)))"#
    );
    wat::parse_str(&src).expect("WAT parses")
}

/// `Start` allocs `start_bytes`, then synchronously `ask`s `Sub`, which allocs `sub_bytes`. Both run
/// in ONE top-level dispatch → under top-level-only reset they share a single 64 KB arena.
fn wat_reentrant(start_bytes: i32, sub_bytes: i32) -> Vec<u8> {
    let src = format!(
        r#"(module
  (import "sigil" "alloc" (func $alloc (param i32) (result i32)))
  (import "sigil" "ask" (func $ask (param i32 i32 i32 i32 i64) (result i64)))
  (memory (export "memory") 1)
  (func (export "Main__Start") (param i32) (result i64)
    (i32.const {start_bytes}) (call $alloc) (drop)
    (i32.const 1) (i32.const 1) (i32.const 0) (i32.const 0) (i64.const 0) (call $ask) (drop)
    (i64.const 0))
  (func (export "Main__Sub") (param i32) (result i64)
    (i32.const {sub_bytes}) (call $alloc) (drop)
    (i64.const 0)))"#
    );
    wat::parse_str(&src).expect("WAT parses")
}

fn drain(wasm: &[u8], limit: usize) -> Result<usize, sigil_runtime::RuntimeError> {
    let s = spec();
    let mut host = RuntimeHost::new(s.fuel_budget);
    host.bootstrap(&s, wasm)?;
    host.drain_messages(limit)
}

// ── (1) the wall is down: a resident allocating actor survives many dispatches ───────────────
#[test]
fn resident_allocating_actor_survives_many_dispatches() {
    // 10000 bytes/dispatch, self-send, ask for 100 dispatches. The 64 KB arena holds ~6 such allocs,
    // so before AL-2 it died "arena exhausted" around dispatch 7; after AL-2 the arena resets each
    // dispatch → all 100 delivered.
    let delivered = drain(&wat_self_send(10000, true), 100)
        .expect("a resident allocating actor must survive many dispatches after AL-2");
    assert_eq!(
        delivered, 100,
        "the arena reset lets a resident allocating actor run indefinitely; delivered {delivered}/100"
    );
}

// ── (2) the per-dispatch arena bound still holds: >64 KB in one dispatch traps ───────────────
#[test]
fn over_arena_single_dispatch_still_traps() {
    // 70000 > 65536 in ONE dispatch. The reset gives a fresh arena, but a single dispatch still
    // cannot exceed the 64 KB window (the per-dispatch bound holds). No self-send.
    let r = drain(&wat_self_send(70000, false), 4);
    assert!(
        r.is_err(),
        "a single dispatch allocating more than the 64 KB arena must still trap; got {r:?}"
    );
}

// ── (3) the reset is TOP-LEVEL-ONLY: a re-entrant call-tree shares ONE arena (X-AL2) ─────────
#[test]
fn reentrant_call_tree_shares_one_arena() {
    // Start allocs 40000, then asks Sub (re-entrant, same dispatch) which allocs 40000. If the reset
    // fired on the re-entrant `ask` path, Sub would get a fresh arena and the tree would fit. Because
    // the reset is top-level-only, the tree shares ONE 64 KB arena: 40000 + 40000 = 80000 > 65536 →
    // Sub traps. This proves a callee cannot stomp the caller's live allocations via a fresh reset.
    let r = drain(&wat_reentrant(40000, 40000), 4);
    assert!(
        r.is_err(),
        "a re-entrant call-tree must share one arena (top-level-only reset); got {r:?}"
    );

    // Control: the SAME tree that FITS one arena (40000 + 20000 = 60000 <= 65536) completes —
    // confirming the trap above is the shared-arena bound, not an unrelated failure.
    let ok =
        drain(&wat_reentrant(40000, 20000), 4).expect("a call-tree within one arena must complete");
    assert_eq!(
        ok, 1,
        "the in-budget re-entrant tree delivers its one message"
    );
}
