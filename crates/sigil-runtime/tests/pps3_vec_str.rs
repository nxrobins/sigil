//! PPS-3 (first slice) — `mut Vec<str>` actor state. The event-log pattern.
//!
//! This resolves the trap PPS-2b recorded: admission and routing had
//! drifted. The C012 seam admitted `Vec<str>` but the routing gate still
//! required a scalar element, so a state `Vec<str>` was never routed to a
//! `$state` instance — its buffer grew transiently AND the storing-push
//! promotion never fired. One cause, two symptoms. Both gates now share
//! `is_persistable_scalar_vec`, so they cannot drift again.

use sigil_compiler::compile_module;
use sigil_runtime::RuntimeHost;

fn delivered(src: &str) -> Result<usize, String> {
    let c = compile_module(src).map_err(|e| format!("compile: {e:?}"))?;
    let mut host = RuntimeHost::new(c.fuel_budget);
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .map_err(|e| format!("bootstrap: {e:?}"))?;
    host.drain_messages(64).map_err(|e| format!("drain: {e:?}"))
}

/// The exact shape that trapped during PPS-2b, now expected to pass.
const EVENT_LOG: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Log>(fuel);
        w.send(Add(1));
        w.send(Clobber());
        w.send(Add(2));
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Log {
    state { mut v: Vec<str> }
    init(f: Fuel) { let tmp: Vec<str> = Vec::new(); v = tmp; }
    on Add(n: i64) {
        if n == 1 {
            let e: str = "first-entry";
            let c: i64 = v.push(e);
        } else {
            let e: str = "second";
            let c: i64 = v.push(e);
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
    on Check() {
        if v.len() != 2 { trap(); }
        let a: str = v.get(0);
        if a.len() != 11 { trap(); }
        if a.byte_at(0) != 102 { trap(); }
        let b: str = v.get(1);
        if b.len() != 6 { trap(); }
        if b.byte_at(0) != 115 { trap(); }
    }
}
"#;

#[test]
fn vec_str_event_log_persists() {
    assert_eq!(
        delivered(EVENT_LOG),
        Ok(6),
        "the PPS-2b trap shape: string elements pushed across dispatches must persist"
    );
}

/// Grow past the initial capacity so the buffer REALLOCATES — the grown
/// buffer holds promoted headers whose payloads must survive too.
const GROWS_PAST_CAPACITY: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Log>(fuel);
        w.send(Fill());
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Log {
    state { mut v: Vec<str> }
    init(f: Fuel) { let tmp: Vec<str> = Vec::new(); v = tmp; }
    on Fill() {
        let mut i: i64 = 0;
        while i < 12 {
            let c: i64 = v.push("evt");
            i = i + 1;
        }
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 64 {
            let n: i64 = junk.push(i * 5 + 3);
            i = i + 1;
        }
    }
    on Check() {
        if v.len() != 12 { trap(); }
        let first: str = v.get(0);
        let last: str = v.get(11);
        if first.len() != 3 { trap(); }
        if last.len() != 3 { trap(); }
        if last.byte_at(0) != 101 { trap(); }
    }
}
"#;

#[test]
fn vec_str_survives_buffer_growth() {
    assert_eq!(
        delivered(GROWS_PAST_CAPACITY),
        Ok(4),
        "reallocated buffers and their promoted element payloads must all persist"
    );
}

/// A substring-derived element — payload pointing into another buffer, the
/// header-only-promotion catcher, same as the PPS-2a/2b tests.
const SUBSTRING_ELEMENT: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Log>(fuel);
        w.send(Add());
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Log {
    state { mut v: Vec<str> }
    init(f: Fuel) { let tmp: Vec<str> = Vec::new(); v = tmp; }
    on Add() {
        let whole: str = "aa-payload-zz";
        let part: str = whole.substr(3, 10);
        let c: i64 = v.push(part);
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 48 {
            let n: i64 = junk.push(i + 2);
            i = i + 1;
        }
    }
    on Check() {
        let s: str = v.get(0);
        if s.len() != 7 { trap(); }
        if s.byte_at(0) != 112 { trap(); }
        if s.byte_at(6) != 100 { trap(); }
    }
}
"#;

#[test]
fn substring_elements_promote_their_payload() {
    assert_eq!(
        delivered(SUBSTRING_ELEMENT),
        Ok(4),
        "a pushed substring's payload must be promoted, not just its header"
    );
}
