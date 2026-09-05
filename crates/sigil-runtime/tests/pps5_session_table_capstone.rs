//! PPS-5 — the capstone: a RESIDENT session-table actor, proving "actor state
//! is USEFUL", not just "actor state persists". `mut Map<str, Record>` under
//! hundreds of dispatches of insert / in-place update / replace, interleaved
//! transient scratch, exhaustion handled by restart-as-GC (PPS-4), and
//! cross-actor isolation — every prior slice composed and load-tested.
//!
//! The slice also found and fixed a REAL hole on arrival: a map insert on an
//! EXISTING key overwrites via `vals.set(vidx, val)` — a storing call the
//! PPS-2b/3 promotion (armed only at `__push__`) never covered, so an
//! overwritten str/record value stored a TRANSIENT pointer and dangled. The
//! promotion gate now covers `__set__` too; `overwrite_of_pointer_valued_
//! entries_persists` is the distilled regression.

use sigil_compiler::compile_module;
use sigil_runtime::{AuditEventKind, RuntimeHost};

fn restarts(host: &RuntimeHost) -> usize {
    host.audit_log()
        .events()
        .iter()
        .filter(|e| matches!(e.kind, AuditEventKind::ActorRestarted { .. }))
        .count()
}

/// Bootstrap with a raised whole-life fuel budget: an actor's budget refills
/// only on restart, and the compilation default is sized for a handful of
/// dispatches, not hundreds.
fn host_with_fuel(c: &sigil_compiler::Compilation, fuel: u64) -> RuntimeHost {
    let mut rm = c.runtime_module.clone();
    rm.fuel_budget = fuel;
    let mut host = RuntimeHost::new(fuel);
    host.bootstrap(&rm, &c.wasm_inner).expect("bootstrap");
    host
}

/// The `__set__` regression, distilled: overwriting an EXISTING key's str and
/// record values must promote at the storing `vals.set`, surviving clobbers.
const OVERWRITE_PIN: &str = r#"module sigil;
cap type Fuel {}
record Session { hits: i64, level: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Tbl>(fuel);
        w.send(PutStr(1));
        w.send(Clobber());
        w.send(PutStr(2));
        w.send(Clobber());
        w.send(PutRec(1));
        w.send(Clobber());
        w.send(PutRec(2));
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Tbl {
    state { power: Fuel, mut names: Map<i64, str>, mut sess: Map<str, Session> }
    init(f: Fuel) {
        power = f;
        let tn: Map<i64, str> = Map::new();
        names = tn;
        let ts: Map<str, Session> = Map::new();
        sess = ts;
    }
    on PutStr(n: i64) {
        if n == 1 {
            let v: str = "first-value";
            let c: i64 = names.insert(7, v);
        } else {
            let whole: str = "xx-second-zz";
            let v: str = whole.substr(3, 9);
            let c: i64 = names.insert(7, v);
        }
    }
    on PutRec(n: i64) {
        if n == 1 {
            let s = Session { hits: 1, level: 10 };
            let c: i64 = sess.insert("alice", s);
        } else {
            let s = Session { hits: 2, level: 20 };
            let c: i64 = sess.insert("alice", s);
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
        if names.len() != 1 { trap(); }
        match names.get(7) {
            Some(s) => {
                if s.len() != 6 { trap(); }
                if s.byte_at(0) != 115 { trap(); }
                if s.byte_at(5) != 100 { trap(); }
            },
            None => { trap(); },
        }
        if sess.len() != 1 { trap(); }
        match sess.get("alice") {
            Some(a) => {
                if a.hits != 2 { trap(); }
                if a.level != 20 { trap(); }
            },
            None => { trap(); },
        }
    }
}
"#;

#[test]
fn overwrite_of_pointer_valued_entries_persists() {
    let c = compile_module(OVERWRITE_PIN).expect("compile");
    let mut host = host_with_fuel(&c, 1_000_000);
    let delivered = host.drain_messages(16).expect("all checks pass");
    assert_eq!(delivered, 10, "Start + 8 mutations/clobbers + Check");
    assert_eq!(restarts(&host), 0, "no traps, no restarts");
}

/// THE RESIDENT TABLE. 300 Ticks in three phases over 100 runtime-built
/// string keys (f-string rendered): insert -> in-place update through the
/// retrieved element pointer -> whole-value replace (the `__set__` path).
/// Every Tick builds transient scratch BEFORE the promoting store — the
/// adversarial order that strands the scratch below the raised floor (the
/// documented watermark residual), so 300 dispatches also budget-test that
/// leak against the 64KB arena. (16-element scratch per tick overflows the
/// arena by design of the math; 4 elements rides within it.)
const SUSTAINED_CHURN: &str = r#"module sigil;
cap type Fuel {}
record Session { hits: i64, level: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Sessions>(fuel);
        let mut i: i64 = 0;
        while i < 300 {
            w.send(Tick(i));
            i = i + 1;
        }
        w.send(CheckAll());
        return 0;
    }
}
actor Sessions {
    state { power: Fuel, mut m: Map<str, Session> }
    init(f: Fuel) { power = f; let tmp: Map<str, Session> = Map::new(); m = tmp; }
    on Tick(i: i64) {
        let mut junk: Vec<i64> = Vec::new();
        let mut j: i64 = 0;
        while j < 4 {
            let n: i64 = junk.push(i * 7 + j);
            j = j + 1;
        }
        if i < 100 {
            let key: str = f"{i}";
            let s = Session { hits: 1, level: i };
            let c: i64 = m.insert(key, s);
        } else {
            if i < 200 {
                let j: i64 = i - 100;
                let key: str = f"{j}";
                match m.get(key) {
                    Some(s) => { s.hits = s.hits + 1; },
                    None => { trap(); },
                }
            } else {
                let j: i64 = i - 200;
                let key: str = f"{j}";
                let s = Session { hits: 9, level: i };
                let c: i64 = m.insert(key, s);
            }
        }
    }
    on CheckAll() {
        if m.len() != 100 { trap(); }
        match m.get("0") {
            Some(a) => {
                if a.hits != 9 { trap(); }
                if a.level != 200 { trap(); }
            },
            None => { trap(); },
        }
        match m.get("50") {
            Some(b) => {
                if b.hits != 9 { trap(); }
                if b.level != 250 { trap(); }
            },
            None => { trap(); },
        }
        match m.get("99") {
            Some(c) => {
                if c.hits != 9 { trap(); }
                if c.level != 299 { trap(); }
            },
            None => { trap(); },
        }
    }
}
"#;

#[test]
fn resident_session_table_survives_sustained_churn() {
    let c = compile_module(SUSTAINED_CHURN).expect("compile");
    let mut host = host_with_fuel(&c, 100_000_000);
    let delivered = host
        .drain_messages(400)
        .expect("300 churn dispatches + CheckAll must all deliver clean");
    assert_eq!(delivered, 302, "Start + 300 Ticks + CheckAll");
    assert_eq!(restarts(&host), 0, "no trap anywhere in 300 dispatches");
}

/// Exhaustion mid-churn: replace-heavy traffic on ONE hot key abandons the
/// predecessor value every dispatch (the unbounded shape), hits the cap,
/// restarts (replay-safe store-only init), and the table keeps working —
/// last write wins whether or not a restart intervened.
const HOT_KEY_CHURN: &str = r#"module sigil;
cap type Fuel {}
record Session { hits: i64, level: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Sessions>(fuel, supervision: Restart(8));
        let mut i: i64 = 0;
        while i < 400 {
            w.send(Churn(i));
            i = i + 1;
        }
        w.send(Probe());
        return 0;
    }
}
actor Sessions {
    state { power: Fuel, mut m: Map<str, Session> }
    init(f: Fuel) { power = f; let tmp: Map<str, Session> = Map::new(); m = tmp; }
    on Churn(i: i64) {
        let s = Session { hits: i, level: i * 2 };
        let c: i64 = m.insert("hot", s);
    }
    on Probe() {
        match m.get("hot") {
            Some(s) => {
                if s.hits != 399 { trap(); }
                if s.level != 798 { trap(); }
            },
            None => { trap(); },
        }
    }
}
"#;

#[test]
fn exhaustion_mid_churn_restarts_and_the_table_keeps_working() {
    let c = compile_module(HOT_KEY_CHURN).expect("compile");
    let mut rm = c.runtime_module.clone();
    rm.fuel_budget = 100_000_000;
    let mut host = RuntimeHost::new(100_000_000);
    // Small cap: each overwrite promotes a fresh 16-byte record (+ header),
    // so a few hundred replacements must cross it at least once.
    host.set_persistent_cap(4096);
    host.bootstrap(&rm, &c.wasm_inner).expect("bootstrap");
    let delivered = host
        .drain_messages(500)
        .expect("exhaustion must be absorbed by Restart supervision");
    assert_eq!(delivered, 402, "Start + 400 Churns + Probe all deliver");
    let n = restarts(&host);
    assert!(
        (1..=8).contains(&n),
        "replace-heavy churn under a 4KB cap must restart at least once (got {n})"
    );
    // Probe delivered clean: the final write won and the promoted record was
    // readable after the last restart — the collector collects, the table
    // keeps serving.
}

/// Two resident tables, one host: separate arenas, separate floors, separate
/// caps' accounting. Same keys, different values — neither leaks into the
/// other across interleaved churn and clobbers.
const TWO_TABLES: &str = r#"module sigil;
cap type Fuel {}
record Session { hits: i64, level: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let sub = fuel.draw(1000000);
        let a = spawn::<Sessions>(sub);
        let b = spawn::<Sessions>(fuel);
        a.send(Put(1));
        b.send(Put(9));
        a.send(Clobber());
        b.send(Clobber());
        a.send(PutBob());
        a.send(CheckA());
        b.send(CheckB());
        return 0;
    }
}
actor Sessions {
    state { power: Fuel, mut m: Map<str, Session> }
    init(f: Fuel) { power = f; let tmp: Map<str, Session> = Map::new(); m = tmp; }
    on Put(n: i64) {
        let s = Session { hits: n, level: n * 10 };
        let c: i64 = m.insert("alice", s);
    }
    on PutBob() {
        let s = Session { hits: 2, level: 2 };
        let c: i64 = m.insert("bob", s);
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 48 {
            let n: i64 = junk.push(i * 3 + 1);
            i = i + 1;
        }
    }
    on CheckA() {
        if m.len() != 2 { trap(); }
        match m.get("alice") {
            Some(s) => {
                if s.hits != 1 { trap(); }
                if s.level != 10 { trap(); }
            },
            None => { trap(); },
        }
    }
    on CheckB() {
        if m.len() != 1 { trap(); }
        match m.get("alice") {
            Some(s) => {
                if s.hits != 9 { trap(); }
                if s.level != 90 { trap(); }
            },
            None => { trap(); },
        }
    }
}
"#;

#[test]
fn two_session_tables_stay_isolated() {
    let c = compile_module(TWO_TABLES).expect("compile");
    let mut host = host_with_fuel(&c, 10_000_000);
    let delivered = host.drain_messages(16).expect("isolation checks pass");
    assert_eq!(delivered, 8, "Start + 7 table operations/checks");
    assert_eq!(restarts(&host), 0);
}
