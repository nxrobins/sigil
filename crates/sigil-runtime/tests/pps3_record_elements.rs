//! PPS-3 — record ELEMENTS in state collections. A pushed record is a
//! pointer; the storing push promotes it by the PPS-1 field copy, so the
//! stored pointer addresses a persistent copy. With PPS-2b's string keys
//! this completes the epic's capstone shape: `Map<str, Record>`.

use sigil_compiler::compile_module;
use sigil_runtime::RuntimeHost;

fn delivered(src: &str) -> Result<usize, String> {
    let c = compile_module(src).map_err(|e| format!("compile: {e:?}"))?;
    let mut host = RuntimeHost::new(c.fuel_budget);
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .map_err(|e| format!("bootstrap: {e:?}"))?;
    host.drain_messages(64).map_err(|e| format!("drain: {e:?}"))
}

/// `Vec<Point>` event log: helper-built records pushed across dispatches.
const VEC_OF_RECORDS: &str = r#"module sigil;
cap type Fuel {}
record Point { x: i64, y: i64 }
fn make(a: i64) -> Point ! { Alloc } {
    let p = Point { x: a, y: a * 10 };
    return p;
}
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
    state { mut v: Vec<Point> }
    init(f: Fuel) { let tmp: Vec<Point> = Vec::new(); v = tmp; }
    on Add(n: i64) { let built = make(n); let c: i64 = v.push(built); }
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
        let a: Point = v.get(0);
        if a.x != 1 { trap(); }
        if a.y != 10 { trap(); }
        let b: Point = v.get(1);
        if b.x != 2 { trap(); }
        if b.y != 20 { trap(); }
    }
}
"#;

#[test]
fn vec_of_records_persists() {
    assert_eq!(
        delivered(VEC_OF_RECORDS),
        Ok(6),
        "helper-built record elements must promote at the push and persist"
    );
}

/// THE CAPSTONE SHAPE: `Map<str, Record>` — string keys promoted at
/// `keys.push` (PPS-2b), record values promoted at `vals.push` (PPS-3),
/// both surviving clobbers. This is the session table the epic was scoped
/// around.
const SESSION_TABLE_WITH_RECORDS: &str = r#"module sigil;
cap type Fuel {}
record Session { hits: i64, level: i64 }
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
    state { mut m: Map<str, Session> }
    init(f: Fuel) { let tmp: Map<str, Session> = Map::new(); m = tmp; }
    on Login(n: i64) {
        if n == 1 {
            let s = Session { hits: 1, level: 10 };
            let c: i64 = m.insert("alice", s);
        } else {
            let s = Session { hits: 2, level: 20 };
            let c: i64 = m.insert("bob", s);
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
    on CheckAll() {
        if m.len() != 2 { trap(); }
        match m.get("alice") {
            Some(a) => {
                if a.hits != 1 { trap(); }
                if a.level != 10 { trap(); }
            },
            None => { trap(); },
        }
        match m.get("bob") {
            Some(b) => {
                if b.hits != 2 { trap(); }
                if b.level != 20 { trap(); }
            },
            None => { trap(); },
        }
    }
}
"#;

#[test]
fn str_keyed_record_valued_session_table_persists() {
    assert_eq!(
        delivered(SESSION_TABLE_WITH_RECORDS),
        Ok(6),
        "the capstone shape: Map<str, Record> with both halves promoted"
    );
}

/// Record KEYS: the map is trait-based (`key.hash()` / `stored.eq(key)`),
/// both content-hashing, so the promoted key COPY still matches later
/// probes built fresh from the same field values.
const RECORD_KEYED_MAP: &str = r#"module sigil;
cap type Fuel {}
record Pair { a: i64, b: i64 }
impl Hash for Pair { fn hash(self: Pair) -> i64 { return self.a * 31 + self.b; } }
impl Eq for Pair {
    fn eq(self: Pair, other: Pair) -> bool {
        if self.a == other.a { return self.b == other.b; } else { return false; }
    }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Tbl>(fuel);
        w.send(Put(1));
        w.send(Clobber());
        w.send(Put(2));
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Tbl {
    state { mut m: Map<Pair, i64> }
    init(f: Fuel) { let tmp: Map<Pair, i64> = Map::new(); m = tmp; }
    on Put(n: i64) {
        let k = Pair { a: n, b: n + 100 };
        let c: i64 = m.insert(k, n * 1000);
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 64 {
            let n: i64 = junk.push(i * 3 + 2);
            i = i + 1;
        }
    }
    on Check() {
        if m.len() != 2 { trap(); }
        let p1 = Pair { a: 1, b: 101 };
        let v1: i64 = m.get_or(p1, 0 - 1);
        if v1 != 1000 { trap(); }
        let p2 = Pair { a: 2, b: 102 };
        let v2: i64 = m.get_or(p2, 0 - 1);
        if v2 != 2000 { trap(); }
    }
}
"#;

#[test]
fn record_keyed_map_persists_and_matches_fresh_probes() {
    assert_eq!(
        delivered(RECORD_KEYED_MAP),
        Ok(6),
        "promoted record keys must hash/eq by contents, matching fresh probe records"
    );
}

/// In-place mutation of a STORED record element (AGG-2a semantics on a
/// promoted object): read it out, and because records are
/// reference-semantic, writes through the retrieved pointer hit the
/// persistent copy.
const MUTATE_STORED_ELEMENT: &str = r#"module sigil;
cap type Fuel {}
record Counter { n: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Log>(fuel);
        w.send(Add());
        w.send(Bump());
        w.send(Clobber());
        w.send(Bump());
        w.send(Check());
        return 0;
    }
}
actor Log {
    state { mut v: Vec<Counter> }
    init(f: Fuel) { let tmp: Vec<Counter> = Vec::new(); v = tmp; }
    on Add() { let c = Counter { n: 0 }; let x: i64 = v.push(c); }
    on Bump() {
        let stored: Counter = v.get(0);
        stored.n = stored.n + 1;
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 48 {
            let n: i64 = junk.push(i + 4);
            i = i + 1;
        }
    }
    on Check() {
        let stored: Counter = v.get(0);
        if stored.n != 2 { trap(); }
    }
}
"#;

#[test]
fn in_place_mutation_of_stored_elements_persists() {
    assert_eq!(
        delivered(MUTATE_STORED_ELEMENT),
        Ok(6),
        "writes through a retrieved element pointer must hit the persistent copy"
    );
}

/// Promotion at the push COPIES: mutating the transient original after the
/// push must not change the stored element.
const PUSH_COPIES: &str = r#"module sigil;
cap type Fuel {}
record Point { x: i64, y: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Log>(fuel);
        w.send(AddThenMutate());
        w.send(Check());
        return 0;
    }
}
actor Log {
    state { mut v: Vec<Point> }
    init(f: Fuel) { let tmp: Vec<Point> = Vec::new(); v = tmp; }
    on AddThenMutate() {
        let mut p = Point { x: 1, y: 2 };
        let c: i64 = v.push(p);
        p.x = 999;
    }
    on Check() {
        let stored: Point = v.get(0);
        if stored.x != 1 { trap(); }
        if stored.y != 2 { trap(); }
    }
}
"#;

#[test]
fn push_promotion_copies_rather_than_aliasing() {
    assert_eq!(
        delivered(PUSH_COPIES),
        Ok(3),
        "the stored element is an independent promoted copy"
    );
}
