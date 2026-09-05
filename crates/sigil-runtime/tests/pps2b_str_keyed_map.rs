//! PPS-2b — string-KEYED maps in actor state. The session-table pattern.
//!
//! The promotion boundary here is new: a key's bytes must be promoted where
//! they enter persistent storage INSIDE the stdlib insert path, not at a
//! state store. The single correct point is the innermost storing call —
//! `Vec::push` within a colored instance — so `Map<str, V>::insert` promotes
//! exactly once, at `keys.push(key)`, rather than once per frame on the way
//! down.

use sigil_compiler::compile_module;
use sigil_runtime::RuntimeHost;

fn delivered(src: &str) -> Result<usize, String> {
    let c = compile_module(src).map_err(|e| format!("compile: {e:?}"))?;
    let mut host = RuntimeHost::new(c.fuel_budget);
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .map_err(|e| format!("bootstrap: {e:?}"))?;
    host.drain_messages(64).map_err(|e| format!("drain: {e:?}"))
}

/// The headline: a `Map<str, i64>` session table. Keys inserted across
/// dispatches, a clobber between, then every key looked up again. A
/// key whose bytes were not promoted would fail to compare equal after the
/// scratch overwrote them — so a miss here is a dangle, not a logic slip.
const SESSION_TABLE: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Sessions>(fuel);
        w.send(Login(1));
        w.send(Clobber());
        w.send(Login(2));
        w.send(Clobber());
        w.send(CheckAll());
        return 0;
    }
}
actor Sessions {
    state { mut m: Map<str, i64> }
    init(f: Fuel) { let tmp: Map<str, i64> = Map::new(); m = tmp; }
    on Login(n: i64) {
        if n == 1 {
            let k: str = "alice";
            let c: i64 = m.insert(k, 100);
        } else {
            let k: str = "bob";
            let c: i64 = m.insert(k, 200);
        }
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 48 {
            let n: i64 = junk.push(i * 7 + 1);
            i = i + 1;
        }
    }
    on CheckAll() {
        if m.len() != 2 { trap(); }
        if m.get_or("alice", 0) != 100 { trap(); }
        if m.get_or("bob", 0) != 200 { trap(); }
        if m.get_or("carol", 0) != 0 { trap(); }
    }
}
"#;

#[test]
fn str_keyed_session_table_persists() {
    assert_eq!(
        delivered(SESSION_TABLE),
        Ok(6),
        "string keys inserted across dispatches must still compare equal after a clobber"
    );
}

/// A key built at RUNTIME (a substring, so its payload points into another
/// buffer) — the case that fails if only the header is promoted.
const RUNTIME_BUILT_KEY: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Sessions>(fuel);
        w.send(Add());
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Sessions {
    state { mut m: Map<str, i64> }
    init(f: Fuel) { let tmp: Map<str, i64> = Map::new(); m = tmp; }
    on Add() {
        let whole: str = "xx-token-yy";
        let key: str = whole.substr(3, 8);
        let c: i64 = m.insert(key, 42);
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 48 {
            let n: i64 = junk.push(i * 5 + 2);
            i = i + 1;
        }
    }
    on Check() {
        if m.len() != 1 { trap(); }
        if m.get_or("token", 0) != 42 { trap(); }
    }
}
"#;

#[test]
fn runtime_built_substring_key_persists() {
    assert_eq!(
        delivered(RUNTIME_BUILT_KEY),
        Ok(4),
        "a substring key's payload must be promoted, not just its header"
    );
}

/// Both halves as strings: `Map<str, str>` promotes key AND value.
const STR_TO_STR: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Sessions>(fuel);
        w.send(Add());
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Sessions {
    state { mut m: Map<str, str> }
    init(f: Fuel) { let tmp: Map<str, str> = Map::new(); m = tmp; }
    on Add() {
        let c: i64 = m.insert("host", "example.test");
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 48 {
            let n: i64 = junk.push(i * 3 + 4);
            i = i + 1;
        }
    }
    on Check() {
        let got: str = m.get_or("host", "");
        if got.len() != 12 { trap(); }
        if got.byte_at(0) != 101 { trap(); }
        if got.byte_at(11) != 116 { trap(); }
    }
}
"#;

#[test]
fn str_to_str_map_promotes_both_halves() {
    assert_eq!(
        delivered(STR_TO_STR),
        Ok(4),
        "a `Map<str, str>` must promote key and value payloads alike"
    );
}

/// Enough string keys to force a REHASH, so the rehashed table's re-homed
/// entries still reference promoted keys.
const STR_KEYS_REHASH: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Sessions>(fuel);
        w.send(Fill());
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Sessions {
    state { mut m: Map<str, i64> }
    init(f: Fuel) { let tmp: Map<str, i64> = Map::new(); m = tmp; }
    on Fill() {
        let a: i64 = m.insert("k1", 1);
        let b: i64 = m.insert("k2", 2);
        let c: i64 = m.insert("k3", 3);
        let d: i64 = m.insert("k4", 4);
        let e: i64 = m.insert("k5", 5);
        let f2: i64 = m.insert("k6", 6);
        let g: i64 = m.insert("k7", 7);
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 64 {
            let n: i64 = junk.push(i * 11 + 6);
            i = i + 1;
        }
    }
    on Check() {
        if m.len() != 7 { trap(); }
        if m.get_or("k1", 0) != 1 { trap(); }
        if m.get_or("k4", 0) != 4 { trap(); }
        if m.get_or("k7", 0) != 7 { trap(); }
    }
}
"#;

#[test]
fn str_keys_survive_a_rehash() {
    assert_eq!(
        delivered(STR_KEYS_REHASH),
        Ok(4),
        "string keys must stay intact through a bucket rehash and a clobber"
    );
}
