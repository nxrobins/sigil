//! ACTOR-LIVE AL-3 — real restart semantics (docs/specs/actor-live.md).
//!
//! The restart path is reachable ONLY for SPAWNED children with `supervision: Restart(n)` (the entry
//! actor is pinned `Stop`, runtime.rs:248). Before AL-3 the restart arm (runtime.rs:412-427) only
//! bumped `restart_count` + audited `ActorRestarted` + returned `Ok(0)` — it re-ran NOTHING, so guest
//! state written before the trap persisted as a "corpse". AL-3 makes it a real restart: refill fuel
//! (AL-1) + reset arena (AL-2) + re-run the init export (when faithfully replayable — no cap args;
//! cap-init is refill+reset only, AG-AL7). These tests pin: (1) a supervised actor with a replayable
//! init is REINITIALIZED on restart (state returns to its init value); (2) a cap-init supervised
//! actor still SURVIVES its trap (attack_14's contract — AL-3 must not fail-closed to "no restart"
//! for cap-init); (3) if the re-run init itself traps, the restart FAILS LOUD (X-AL3c fail-fast).

use sigil_abi::RuntimeTypeSpec;
use sigil_runtime::{
    RuntimeActorSpec, RuntimeHandlerSpec, RuntimeHost, RuntimeImportSpec, RuntimeModuleSpec,
};

const BUDGET: u64 = 1_000_000;

/// A two-actor-type module: an entry `Main` that spawns a supervised `Worker` and sends it a fixed
/// sequence of handlers. `worker_init_params` toggles the replayable (empty) vs cap-init shape;
/// `max_restarts` is the child's supervision bound; `sends` is the (handler_id) sequence Start emits.
fn spec(worker_init_params: Vec<RuntimeTypeSpec>) -> RuntimeModuleSpec {
    RuntimeModuleSpec {
        module_name: "al3".to_owned(),
        fuel_budget: BUDGET,
        imports: RuntimeImportSpec::phase_one(),
        actors: vec![
            RuntimeActorSpec {
                name: "Main".to_owned(),
                actor_type_id: 0,
                is_entry: true,
                init_export: Some("Main__init".to_owned()),
                init_params: vec![RuntimeTypeSpec::Cap("Fuel".to_owned())],
                handlers: vec![RuntimeHandlerSpec {
                    name: "Start".to_owned(),
                    handler_id: 0,
                    export_name: "Main__Start".to_owned(),
                    params: vec![],
                    ret: RuntimeTypeSpec::I64,
                }],
                state_layout: vec![],
                state_size: 0,
                init_replay_safe: false,
            },
            RuntimeActorSpec {
                name: "Worker".to_owned(),
                actor_type_id: 1,
                is_entry: false,
                init_export: Some("Worker__init".to_owned()),
                init_params: worker_init_params,
                handlers: vec![
                    RuntimeHandlerSpec {
                        name: "Corrupt".to_owned(),
                        handler_id: 0,
                        export_name: "Worker__Corrupt".to_owned(),
                        params: vec![],
                        ret: RuntimeTypeSpec::I64,
                    },
                    RuntimeHandlerSpec {
                        name: "Verify".to_owned(),
                        handler_id: 1,
                        export_name: "Worker__Verify".to_owned(),
                        params: vec![],
                        ret: RuntimeTypeSpec::I64,
                    },
                ],
                state_layout: vec![],
                state_size: 0,
                init_replay_safe: false,
            },
        ],
    }
}

/// `Main__Start` spawns Worker (type 1) with `supervision`, then `send`s each `handler_id` in `sends`
/// (FIFO, so they are delivered in order). `worker_init` / `corrupt` / `verify` are the Worker bodies.
/// `init_param` is `(param i32)` for the cap-init shape, empty for the replayable shape.
fn wat(
    supervision: i32,
    sends: &[i32],
    init_param: &str,
    worker_init: &str,
    corrupt: &str,
    verify: &str,
) -> Vec<u8> {
    let send_seq = sends
        .iter()
        .map(|h| {
            format!("(call $send (global.get $child) (i32.const {h}) (i32.const 0) (i32.const 0))")
        })
        .collect::<Vec<_>>()
        .join("\n    ");
    let src = format!(
        r#"(module
  (import "sigil" "spawn" (func $spawn (param i32 i32 i32 i32 i32) (result i32)))
  (import "sigil" "send" (func $send (param i32 i32 i32 i32)))
  (memory (export "memory") 1)
  (global $fuelcap (mut i32) (i32.const 0))
  (global $child (mut i32) (i32.const 0))
  (global $n (mut i32) (i32.const 0))

  (func (export "Main__init") (param i32 i32)
    (global.set $fuelcap (local.get 1)))
  (func (export "Main__Start") (param i32) (result i64)
    (global.set $child
      (call $spawn (i32.const 1) (i32.const 0) (i32.const 0) (global.get $fuelcap) (i32.const {supervision})))
    {send_seq}
    (i64.const 0))

  (func (export "Worker__init") (param i32) {init_param}
    {worker_init})
  (func (export "Worker__Corrupt") (param i32) (result i64)
    {corrupt})
  (func (export "Worker__Verify") (param i32) (result i64)
    {verify}))"#
    );
    wat::parse_str(&src).expect("WAT parses")
}

fn restart_events(host: &RuntimeHost) -> usize {
    host.audit_log()
        .events()
        .iter()
        .filter(|e| {
            matches!(
                e.kind,
                sigil_runtime::audit::AuditEventKind::ActorRestarted { .. }
            )
        })
        .count()
}

fn run(spec: RuntimeModuleSpec, wasm: Vec<u8>, limit: usize) -> (Result<usize, String>, usize) {
    let mut host = RuntimeHost::new(spec.fuel_budget);
    host.bootstrap(&spec, &wasm).expect("bootstrap runs");
    let drain = host.drain_messages(limit).map_err(|e| format!("{e:?}"));
    let restarts = restart_events(&host);
    (drain, restarts)
}

// ── (1) THE WALL: a replayable-init actor is REINITIALIZED on restart, not left a corpse ──────────
#[test]
fn restart_reinitializes_replayable_actor_state() {
    // Worker.init (no cap args → faithfully replayable) writes sentinel 42 to mem[0]. Corrupt
    // overwrites it with 999 and traps → restart #1. Verify completes iff mem[0] == 42. With
    // max_restarts = 1: before AL-3 the corpse (999) makes Verify trap, exceeding max_restarts →
    // the drain FAILS. After AL-3 the restart re-runs init (mem[0] → 42), so Verify completes and
    // all three dispatches (Start, Corrupt, Verify) are delivered.
    let (drain, restarts) = run(
        spec(vec![]),
        wat(
            1,
            &[0, 1],
            "",
            "(i32.store (i32.const 0) (i32.const 42))",
            "(i32.store (i32.const 0) (i32.const 999)) (unreachable)",
            "(if (result i64) (i32.eq (i32.load (i32.const 0)) (i32.const 42)) (then (i64.const 0)) (else (unreachable)))",
        ),
        3,
    );
    assert_eq!(
        drain,
        Ok(3),
        "AL-3: the restart must re-run init so Verify reads a CLEAN mem[0]=42; all 3 dispatches deliver"
    );
    assert_eq!(
        restarts, 1,
        "only Corrupt restarts (reinit fixes the corpse so Verify does NOT trap); got {restarts}"
    );
}

// ── (2) CONSERVATION: a cap-init supervised actor still survives its trap (attack_14 contract) ────
#[test]
fn cap_init_supervised_actor_survives_trap() {
    // Worker.init(fuel: Fuel) {} — the common cap-init shape (empty body, like attack_14). Corrupt
    // just traps. With max_restarts = 1 and one Corrupt send, the host must SURVIVE: the trap is
    // absorbed by Restart supervision (refill+reset+bump, NO reinit — AG-AL7 fenced, harmless
    // because the init is empty). Both dispatches (Start, Corrupt) deliver; exactly one restart.
    let (drain, restarts) = run(
        spec(vec![RuntimeTypeSpec::Cap("Fuel".to_owned())]),
        wat(
            1,
            &[0],
            "(param i32)",
            "", // empty init body
            "(unreachable)",
            "(i64.const 0)",
        ),
        2,
    );
    assert_eq!(
        drain,
        Ok(2),
        "AL-3 must NOT fail-closed to `no restart` for cap-init; the host survives the trap"
    );
    assert_eq!(
        restarts, 1,
        "the single trap is absorbed by one Restart; got {restarts}"
    );
}

// ── (3) X-AL3c FAIL-FAST: a re-run init that itself traps propagates loud, never a zombie Ok ──────
#[test]
fn reinit_trap_propagates() {
    // Worker.init (replayable) increments a global and traps on its SECOND run. Corrupt just traps →
    // restart re-runs init → the second init run traps. With max_restarts = 2 (so the Corrupt trap
    // itself is well within budget) the ONLY way the drain errors is the reinit trap. Before AL-3
    // there is no reinit, so the drain is Ok(2) (RED). After AL-3 the reinit trap propagates → Err.
    let (drain, restarts) = run(
        spec(vec![]),
        wat(
            2,
            &[0],
            "",
            "(global.set $n (i32.add (global.get $n) (i32.const 1))) \
             (if (i32.gt_u (global.get $n) (i32.const 1)) (then (unreachable)))",
            "(unreachable)",
            "(i64.const 0)",
        ),
        2,
    );
    assert!(
        drain.is_err(),
        "AL-3 X-AL3c: a re-run init that traps must FAIL LOUD, not be swallowed as Ok; got {drain:?}"
    );
    // `ActorRestarted` is audited only on a SUCCESSFUL restart — the reinit runs BEFORE the audit,
    // so a reinit trap propagates without recording a (false) successful restart.
    assert_eq!(
        restarts, 0,
        "a restart whose reinit trapped is NOT audited as successful; got {restarts}"
    );
}
