//! AGG2b-4 — the persistent-collection-heap capstone. (1) A DEMONSTRATOR: a `mut Vec<i64>` state
//! field grown across MANY handler dispatches (several buffer doublings) reads back correctly — the
//! "lasting software with a growing collection" scenario. (2) The X-LEAK CANARY: the documented B1
//! residual — a transient scratch alloc BEFORE a persistent push in the same handler is promoted
//! below the floor (a bounded leak), but it never CORRUPTS the persistent data; the state Vec still
//! reads back correctly. (Unbounded interleaving eventually hits the 64 KB arena trap — fail-closed,
//! never a dangle — which is a stress property, not asserted here.)
use sigil_compiler::compile_module;
use sigil_runtime::RuntimeHost;

fn delivered(src: &str) -> Result<usize, String> {
    let c = compile_module(src).map_err(|e| format!("compile: {e:?}"))?;
    let mut host = RuntimeHost::new(c.fuel_budget);
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .map_err(|e| format!("bootstrap: {e:?}"))?;
    host.drain_messages(64).map_err(|e| format!("drain: {e:?}"))
}

// Grow across 8 Add dispatches (0..8 → doublings 0→4→8), then verify length + several elements. All
// 13 messages deliver iff every grown buffer persisted across every dispatch's reset.
const DEMONSTRATOR: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Log>(fuel);
        let mut i: i64 = 0;
        while i < 8 { w.send(Add(i)); i = i + 1; }
        w.send(CheckLen(8));
        w.send(CheckAt(0, 0));
        w.send(CheckAt(5, 5));
        w.send(CheckAt(7, 7));
        return 0;
    }
}
actor Log {
    state { mut v: Vec<i64> }
    init(f: Fuel) { let tmp: Vec<i64> = Vec::new(); v = tmp; }
    on Add(x: i64) { let n: i64 = v.push(x); }
    on CheckLen(expected: i64) { if v.len() != expected { trap(); } }
    on CheckAt(idx: i64, expected: i64) { if v.get(idx) != expected { trap(); } }
}
"#;

#[test]
fn state_vec_grown_across_many_dispatches_persists() {
    // Start + 8 Add + CheckLen + 3 CheckAt = 13 messages.
    assert_eq!(
        delivered(DEMONSTRATOR),
        Ok(13),
        "a state Vec grown across many dispatches (multiple doublings) must read back correctly"
    );
}

// X-LEAK canary: every AddScratch dispatch allocates transient scratch BEFORE the persistent push,
// so the scratch is promoted below the floor (leaked). Drive several dispatches; the state Vec must
// still persist CORRECTLY (the leak is a bounded space cost, never data corruption).
const WATERMARK_LEAK_CANARY: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Acc>(fuel);
        w.send(AddScratch(100));
        w.send(AddScratch(200));
        w.send(AddScratch(300));
        w.send(CheckAt(0, 100));
        w.send(CheckAt(1, 200));
        w.send(CheckAt(2, 300));
        return 0;
    }
}
actor Acc {
    state { mut v: Vec<i64> }
    init(f: Fuel) { let tmp: Vec<i64> = Vec::new(); v = tmp; }
    on AddScratch(x: i64) {
        let mut scratch: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 8 { let n: i64 = scratch.push(i * 3 + 1); i = i + 1; }
        let m: i64 = v.push(x);
    }
    on CheckAt(idx: i64, expected: i64) { if v.get(idx) != expected { trap(); } }
}
"#;

#[test]
fn state_vec_persists_correctly_despite_watermark_leak() {
    // Start + 3 AddScratch + 3 CheckAt = 7 messages. All deliver iff the persistent Vec is
    // uncorrupted despite the transient-before-persistent watermark leak (X-LEAK residual).
    assert_eq!(
        delivered(WATERMARK_LEAK_CANARY),
        Ok(7),
        "a state Vec must persist correctly even when transient scratch is interleaved (the leak \
         is a bounded space cost, never corruption)"
    );
}
