//! AGG2b-1 — the `alloc_persistent` runtime endpoint (the B1 floor-raise), tested in isolation via
//! a hand-built WAT actor (no compiler seam yet — that is AGG2b-2). The floor-raise is observable
//! only across an AL-2 per-dispatch reset, so the actor grows a buffer in one dispatch and reads it
//! back in the next. The differential: a buffer grown via `alloc_persistent` survives the reset (its
//! bytes sit BELOW the raised floor, and the next dispatch's alloc lands above it); a buffer grown
//! via plain `alloc` is reclaimed (the reset rewinds to the unraised floor, and the next dispatch's
//! alloc reuses that address, clobbering it). This is the runtime half of the Phase-0 dangle, fixed.

use sigil_abi::{
    RuntimeActorSpec, RuntimeHandlerSpec, RuntimeImportSpec, RuntimeModuleSpec, RuntimeTypeSpec,
};
use sigil_runtime::{Message, RuntimeError, RuntimeHost};

const BUDGET: u64 = 65_536;
/// The entry actor is `ActorId(1)`; its arena base is `1 * ARENA_SIZE` (65536). A stateless actor's
/// persistent floor starts at the arena base, so its first post-reset allocation returns this
/// address — where `Start` writes the sentinel and `Check` reads it back.
const ENTRY_ARENA_BASE: u32 = 65_536;

fn spec() -> RuntimeModuleSpec {
    RuntimeModuleSpec {
        module_name: "agg2b".to_owned(),
        fuel_budget: BUDGET,
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
                    name: "Check".to_owned(),
                    handler_id: 1,
                    export_name: "Main__Check".to_owned(),
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

/// `grow` is `"allocp"` (persistent) or `"alloc"` (transient control). `Start` grows a 1 KB buffer
/// and writes sentinel 0x1234 at its base (= the arena base for a stateless actor). `Check` allocs
/// its own 1 KB scratch and writes 0xDEAD at whatever address that alloc returned — so it clobbers
/// the sentinel ONLY if the reset reclaimed the grown buffer (transient) and the alloc reused the
/// base. Then it reads the sentinel back and traps (`unreachable`) on mismatch.
fn wat(grow: &str) -> Vec<u8> {
    let src = format!(
        r#"(module
  (import "sigil" "alloc" (func $alloc (param i32) (result i32)))
  (import "sigil" "alloc_persistent" (func $allocp (param i32) (result i32)))
  (memory (export "memory") 2)
  (func (export "Main__Start") (param i32) (result i64)
    (local $buf i32)
    (i32.const 1024) (call ${grow}) (local.set $buf)
    (i32.store (local.get $buf) (i32.const 0x1234))
    (i64.const 0))
  (func (export "Main__Check") (param i32) (result i64)
    (local $scratch i32)
    (i32.const 1024) (call $alloc) (local.set $scratch)
    (i32.store (local.get $scratch) (i32.const 0xDEAD))
    (if (i32.ne (i32.load (i32.const {addr})) (i32.const 0x1234))
      (then (unreachable)))
    (i64.const 0)))"#,
        addr = ENTRY_ARENA_BASE,
    );
    wat::parse_str(&src).expect("WAT parses")
}

/// Drive Start (grow + write sentinel) then Check (clobber + read-back). Returns the Check dispatch
/// result: `Ok` iff the sentinel survived, `Err(trap)` iff it was clobbered.
fn run(grow: &str) -> Result<usize, RuntimeError> {
    let spec = spec();
    let mut host = RuntimeHost::new(spec.fuel_budget);
    let report = host.bootstrap(&spec, &wat(grow)).expect("bootstrap");
    let entry = report.entry_actor.expect("entry actor");
    assert_eq!(
        entry.get(),
        1,
        "the test pins the entry arena base at {ENTRY_ARENA_BASE}; entry must be ActorId(1)"
    );
    host.drain_messages(1).expect("Start dispatch"); // grow + write sentinel
    host.enqueue_message(Message::system(entry, "Check", 1))
        .expect("enqueue Check");
    host.drain_messages(1) // clobber + read-back; traps on the transient dangle
}

#[test]
fn alloc_persistent_survives_reset_vs_transient_clobber() {
    // B1 floor-raise: the grown buffer sits below the raised floor, survives the AL-2 reset; Check's
    // clobber lands above it, so the sentinel reads back — no trap.
    assert!(
        run("allocp").is_ok(),
        "a buffer grown via alloc_persistent must survive the per-dispatch reset + a clobber"
    );
    // Transient control: the buffer is above the unraised floor, reclaimed by the reset; Check's
    // alloc reuses that address and clobbers the sentinel — read-back mismatch traps.
    assert!(
        run("alloc").is_err(),
        "a buffer grown via plain alloc must be clobbered after the reset (the Phase-0 dangle)"
    );
}
