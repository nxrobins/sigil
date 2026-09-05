//! PPS-0 — the end-to-end proof: a `mut Map<i64, i64>` actor-state field
//! that GROWS (including a rehash) in a handler PERSISTS across dispatches.
//!
//! The AGG-2b shape covered ONE allocation in the routed body (a `Vec`'s
//! grow-buffer). A `Map`'s interior is five `Vec`s allocated by the stdlib's
//! own methods — `ensure_buckets` → `filled` → `Vec::with_capacity`/`push`,
//! and `grow`'s replacement bucket arrays — so persistence here rests on the
//! transitive coloring (`state_mono_depth`) plus persistent record HEADERS
//! (`BumpAlloc { persistent: true }`), neither of which AGG-2b needed.

use sigil_compiler::compile_module;
use sigil_runtime::RuntimeHost;

fn delivered(src: &str) -> Result<usize, String> {
    let c = compile_module(src).map_err(|e| format!("compile: {e:?}"))?;
    let mut host = RuntimeHost::new(c.fuel_budget);
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .map_err(|e| format!("bootstrap: {e:?}"))?;
    host.drain_messages(64).map_err(|e| format!("drain: {e:?}"))
}

/// Three inserts (cold-map bucket allocation on the first), a clobbering
/// dispatch that allocates transient scratch from the floor upward, then a
/// read-back. On persistence all four values survive and every message
/// delivers; on a dangle the scratch overwrites the buckets and `Check`
/// traps.
const MAP_GROWS_AND_PERSISTS: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(Put(1, 10));
        w.send(Put(2, 20));
        w.send(Put(3, 30));
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Store {
    state { mut m: Map<i64, i64> }
    init(f: Fuel) { let tmp: Map<i64, i64> = Map::new(); m = tmp; }
    on Put(k: i64, v: i64) { let n: i64 = m.insert(k, v); }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 64 {
            let n: i64 = junk.push(i * 7 + 1);
            i = i + 1;
        }
    }
    on Check() {
        let a: i64 = m.get_or(1, 0);
        let b: i64 = m.get_or(2, 0);
        let c: i64 = m.get_or(3, 0);
        if a != 10 { trap(); }
        if b != 20 { trap(); }
        if c != 30 { trap(); }
    }
}
"#;

#[test]
fn mut_map_state_field_persists_across_dispatches() {
    assert_eq!(
        delivered(MAP_GROWS_AND_PERSISTS),
        Ok(6),
        "every message must deliver: the map's buckets, keys, and vals all survive the \
         per-dispatch arena reset"
    );
}

/// Enough inserts to force at least one REHASH (the 8-slot table grows at
/// the 70% load factor). Rehash builds three replacement bucket `Vec`s —
/// header record constructs plus their buffers — inside `grow`, a callee of
/// the routed `insert`. Every one must land on the persistent channel.
const MAP_REHASH_PERSISTS: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(Fill());
        w.send(Clobber());
        w.send(CheckAll());
        return 0;
    }
}
actor Store {
    state { mut m: Map<i64, i64> }
    init(f: Fuel) { let tmp: Map<i64, i64> = Map::new(); m = tmp; }
    on Fill() {
        let mut i: i64 = 0;
        while i < 24 {
            let n: i64 = m.insert(i, i * 100);
            i = i + 1;
        }
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 128 {
            let n: i64 = junk.push(i * 13 + 5);
            i = i + 1;
        }
    }
    on CheckAll() {
        let mut i: i64 = 0;
        while i < 24 {
            let got: i64 = m.get_or(i, 0 - 1);
            if got != i * 100 { trap(); }
            i = i + 1;
        }
        if m.len() != 24 { trap(); }
    }
}
"#;

#[test]
fn map_rehash_buckets_persist_across_dispatches() {
    assert_eq!(
        delivered(MAP_REHASH_PERSISTS),
        Ok(4),
        "a rehashed map (24 entries, 8-slot table grown repeatedly) must read back intact \
         after a clobbering dispatch"
    );
}

/// Inserts spread ACROSS dispatches, with a clobber between each — the
/// pattern a real session-table actor exhibits, and the one that fails if
/// any single interior allocation escapes the persistent channel.
const MAP_INTERLEAVED: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(Put(1, 11));
        w.send(Clobber());
        w.send(Put(2, 22));
        w.send(Clobber());
        w.send(Put(3, 33));
        w.send(Clobber());
        w.send(Put(4, 44));
        w.send(Check());
        return 0;
    }
}
actor Store {
    state { mut m: Map<i64, i64> }
    init(f: Fuel) { let tmp: Map<i64, i64> = Map::new(); m = tmp; }
    on Put(k: i64, v: i64) { let n: i64 = m.insert(k, v); }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 48 {
            let n: i64 = junk.push(i * 3 + 2);
            i = i + 1;
        }
    }
    on Check() {
        if m.get_or(1, 0) != 11 { trap(); }
        if m.get_or(2, 0) != 22 { trap(); }
        if m.get_or(3, 0) != 33 { trap(); }
        if m.get_or(4, 0) != 44 { trap(); }
        if m.len() != 4 { trap(); }
    }
}
"#;

#[test]
fn interleaved_inserts_and_clobbers_all_persist() {
    assert_eq!(
        delivered(MAP_INTERLEAVED),
        Ok(9),
        "inserts spread across dispatches, each followed by transient scratch, must all survive"
    );
}

/// TWO `mut Map` state fields in one actor. Both route through the SAME
/// `$state` monomorph instance (identical key/value types), so a coloring
/// bug that hoisted state into instance-level storage — rather than keeping
/// it per-receiver — would alias them. Each must keep its own entries across
/// dispatches.
const TWO_MAPS: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(PutA(1, 100));
        w.send(PutB(1, 200));
        w.send(PutA(2, 300));
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Store {
    state { mut a: Map<i64, i64>, mut b: Map<i64, i64> }
    init(f: Fuel) {
        let ta: Map<i64, i64> = Map::new();
        let tb: Map<i64, i64> = Map::new();
        a = ta;
        b = tb;
    }
    on PutA(k: i64, v: i64) { let n: i64 = a.insert(k, v); }
    on PutB(k: i64, v: i64) { let n: i64 = b.insert(k, v); }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 64 {
            let n: i64 = junk.push(i * 5 + 3);
            i = i + 1;
        }
    }
    on Check() {
        if a.get_or(1, 0) != 100 { trap(); }
        if a.get_or(2, 0) != 300 { trap(); }
        if a.len() != 2 { trap(); }
        if b.get_or(1, 0) != 200 { trap(); }
        if b.len() != 1 { trap(); }
    }
}
"#;

#[test]
fn two_state_maps_do_not_alias() {
    assert_eq!(
        delivered(TWO_MAPS),
        Ok(6),
        "two `mut Map` fields share one `$state` instance but must keep separate storage"
    );
}
