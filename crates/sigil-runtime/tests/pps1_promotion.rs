//! PPS-1 — the promotion primitive. A `mut` FLAT aggregate state field can
//! now be REPLACED wholesale in a handler: the store promotes the value into
//! the persistent heap (allocate-persistent + field copy), so the field
//! addresses a copy that outlives the per-dispatch arena reset.
//!
//! The spec's exit criterion is the helper-built case — a value constructed
//! by a callee, whose provenance the compiler cannot color — which is
//! exactly what distinguishes promotion from PPS-0's coloring.

use sigil_compiler::compile_module;
use sigil_runtime::RuntimeHost;

fn delivered(src: &str) -> Result<usize, String> {
    let c = compile_module(src).map_err(|e| format!("compile: {e:?}"))?;
    let mut host = RuntimeHost::new(c.fuel_budget);
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .map_err(|e| format!("bootstrap: {e:?}"))?;
    host.drain_messages(64).map_err(|e| format!("drain: {e:?}"))
}

/// Wholesale replacement from a value built INLINE in the handler.
const REPLACE_INLINE: &str = r#"module sigil;
cap type Fuel {}
record Point { x: i64, y: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(Set(3, 4));
        w.send(Clobber());
        w.send(Check(3, 4));
        w.send(Set(10, 20));
        w.send(Clobber());
        w.send(Check(10, 20));
        return 0;
    }
}
actor Store {
    state { mut p: Point }
    init(f: Fuel) { let seed = Point { x: 0, y: 0 }; p = seed; }
    on Set(a: i64, b: i64) { p = Point { x: a, y: b }; }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 64 {
            let n: i64 = junk.push(i * 9 + 1);
            i = i + 1;
        }
    }
    on Check(wx: i64, wy: i64) {
        if p.x != wx { trap(); }
        if p.y != wy { trap(); }
    }
}
"#;

#[test]
fn inline_built_record_replacement_persists() {
    assert_eq!(
        delivered(REPLACE_INLINE),
        Ok(7),
        "a wholesale record replacement must persist across dispatches"
    );
}

/// THE EXIT CRITERION: the replacement value is built by a HELPER, so its
/// allocation happened inside a callee the state-backed coloring never
/// touches. Only the promotion copy at the store boundary makes it persist.
const REPLACE_FROM_HELPER: &str = r#"module sigil;
cap type Fuel {}
record Point { x: i64, y: i64 }
fn make_point(a: i64, b: i64) -> Point ! { Alloc } {
    let scratch = Point { x: a * 2, y: b * 2 };
    return scratch;
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(Set(5, 6));
        w.send(Clobber());
        w.send(Check(10, 12));
        return 0;
    }
}
actor Store {
    state { mut p: Point }
    init(f: Fuel) { let seed = Point { x: 0, y: 0 }; p = seed; }
    on Set(a: i64, b: i64) { let built = make_point(a, b); p = built; }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 48 {
            let n: i64 = junk.push(i * 11 + 3);
            i = i + 1;
        }
    }
    on Check(wx: i64, wy: i64) {
        if p.x != wx { trap(); }
        if p.y != wy { trap(); }
    }
}
"#;

#[test]
fn helper_built_record_replacement_persists() {
    assert_eq!(
        delivered(REPLACE_FROM_HELPER),
        Ok(4),
        "a helper-built record stored into state must be promoted and persist"
    );
}

/// Promotion COPIES: after the store, mutating the transient original must
/// NOT change the state field. This pins the one semantic that differs from
/// the language's reference semantics everywhere else.
const PROMOTION_COPIES: &str = r#"module sigil;
cap type Fuel {}
record Point { x: i64, y: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(SetThenMutateOriginal());
        w.send(Check());
        return 0;
    }
}
actor Store {
    state { mut p: Point }
    init(f: Fuel) { let seed = Point { x: 0, y: 0 }; p = seed; }
    on SetThenMutateOriginal() {
        let mut tmp = Point { x: 1, y: 2 };
        p = tmp;
        tmp.x = 999;
        tmp.y = 888;
    }
    on Check() {
        if p.x != 1 { trap(); }
        if p.y != 2 { trap(); }
    }
}
"#;

#[test]
fn promotion_copies_rather_than_aliasing() {
    assert_eq!(
        delivered(PROMOTION_COPIES),
        Ok(3),
        "the promoted copy is independent of the transient original"
    );
}

/// Two state fields fed from ONE value promote independently — the
/// duplication the spec calls out, pinned as behavior.
const TWO_FIELDS_ONE_VALUE: &str = r#"module sigil;
cap type Fuel {}
record Point { x: i64, y: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(SetBoth());
        w.send(MutateA());
        w.send(Check());
        return 0;
    }
}
actor Store {
    state { mut a: Point, mut b: Point }
    init(f: Fuel) {
        let s1 = Point { x: 0, y: 0 };
        let s2 = Point { x: 0, y: 0 };
        a = s1;
        b = s2;
    }
    on SetBoth() {
        let v = Point { x: 7, y: 8 };
        a = v;
        b = v;
    }
    on MutateA() { a.x = 100; }
    on Check() {
        if a.x != 100 { trap(); }
        if b.x != 7 { trap(); }
        if b.y != 8 { trap(); }
    }
}
"#;

#[test]
fn one_value_into_two_fields_promotes_twice() {
    assert_eq!(
        delivered(TWO_FIELDS_ONE_VALUE),
        Ok(4),
        "each state field gets its own promoted copy; mutating one must not move the other"
    );
}

/// In-place mutation (the AGG-2a path) still works alongside replacement,
/// and survives a clobber.
const REPLACE_THEN_MUTATE: &str = r#"module sigil;
cap type Fuel {}
record Counter { hits: i64, last: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(Reset(5));
        w.send(Bump());
        w.send(Clobber());
        w.send(Bump());
        w.send(Check(2, 5));
        return 0;
    }
}
actor Store {
    state { mut c: Counter }
    init(f: Fuel) { let seed = Counter { hits: 0, last: 0 }; c = seed; }
    on Reset(l: i64) { c = Counter { hits: 0, last: l }; }
    on Bump() { c.hits = c.hits + 1; }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 48 {
            let n: i64 = junk.push(i + 7);
            i = i + 1;
        }
    }
    on Check(wh: i64, wl: i64) {
        if c.hits != wh { trap(); }
        if c.last != wl { trap(); }
    }
}
"#;

#[test]
fn replacement_and_in_place_mutation_compose() {
    assert_eq!(
        delivered(REPLACE_THEN_MUTATE),
        Ok(6),
        "in-place mutation of a PROMOTED object must persist like an init-allocated one"
    );
}
