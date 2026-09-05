//! AGG2b-3 — the end-to-end proof: a `mut Vec<i64>` actor-state field that GROWS in a handler now
//! PERSISTS across dispatches. This is the exact shape the AGG2b-0 Phase-0 measurement reproduced as
//! a dangle (the grow-alloc landed above the persistent floor, was reclaimed by the AL-2 reset, and
//! a later dispatch's scratch clobbered it → the read-back trapped). With AGG2b-1 (the
//! `alloc_persistent` B1 floor-raise) + AGG2b-2 (the state-backed `$state` mono instance whose
//! grow-`push` routes to it) + AGG2b-3 (the C012 un-fence), the grown buffer sits below the raised
//! floor and survives — so `CheckAll` reads back 10/20/30 even AFTER a clobbering dispatch, and all
//! six messages deliver.
use sigil_compiler::compile_module;
use sigil_runtime::RuntimeHost;

fn delivered(src: &str) -> Result<usize, String> {
    let c = compile_module(src).map_err(|e| format!("compile: {e:?}"))?;
    let mut host = RuntimeHost::new(c.fuel_budget);
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .map_err(|e| format!("bootstrap: {e:?}"))?;
    host.drain_messages(32).map_err(|e| format!("drain: {e:?}"))
}

// `v` starts empty; each Push in a HANDLER grows the buffer via `alloc_persistent` (routed through
// the state-backed `$state` push instance). Clobber allocates transient scratch from the floor
// upward — but now the floor is ABOVE the grown state buffer, so the scratch cannot reach it. CheckAll
// reads all three back; on persistence they are 10/20/30, no trap → all 6 messages deliver.
const GROWS_AND_PERSISTS: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Acc>(fuel);
        w.send(Push(10));
        w.send(Push(20));
        w.send(Push(30));
        w.send(Clobber());
        w.send(CheckAll());
        return 0;
    }
}
actor Acc {
    state { mut v: Vec<i64> }
    init(f: Fuel) { let tmp: Vec<i64> = Vec::new(); v = tmp; }
    on Push(x: i64) { let n: i64 = v.push(x); }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 32 {
            let n: i64 = junk.push(i * 7 + 1);
            i = i + 1;
        }
    }
    on CheckAll() {
        let a: i64 = v.get(0);
        let b: i64 = v.get(1);
        let c: i64 = v.get(2);
        if a != 10 { trap(); }
        if b != 20 { trap(); }
        if c != 30 { trap(); }
    }
}
"#;

#[test]
fn mut_state_vec_grown_in_handler_persists_across_dispatches() {
    // 6 sends (Start + Push*3 + Clobber + CheckAll). All deliver iff the handler-grown buffer
    // survived the AL-2 reset + the clobber — the AGG2b-0 dangle, flipped GREEN.
    assert_eq!(
        delivered(GROWS_AND_PERSISTS),
        Ok(6),
        "a `mut Vec<i64>` state field grown via push in a handler must persist across dispatches"
    );
}
