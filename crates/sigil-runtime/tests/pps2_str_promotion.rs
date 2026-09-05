//! PPS-2a — owned `str` in actor state. A `str` is a fat pointer: an
//! 8-byte header over bytes allocated elsewhere. Promoting one therefore
//! means promoting BOTH halves — copy the payload into a persistent buffer
//! (runtime length, so `PromoteBytes` rather than a fixed field sequence),
//! then build a persistent header over the copy. Promoting only the header
//! would leave the field pointing at reclaimed bytes.

use sigil_compiler::compile_module;
use sigil_runtime::RuntimeHost;

fn delivered(src: &str) -> Result<usize, String> {
    let c = compile_module(src).map_err(|e| format!("compile: {e:?}"))?;
    let mut host = RuntimeHost::new(c.fuel_budget);
    host.bootstrap(&c.runtime_module, &c.wasm_inner)
        .map_err(|e| format!("bootstrap: {e:?}"))?;
    host.drain_messages(64).map_err(|e| format!("drain: {e:?}"))
}

/// Replace a `mut str` state field in a handler, clobber, then read it
/// back: length AND contents must survive.
const STR_REPLACE_PERSISTS: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(Set());
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Store {
    state { mut name: str }
    init(f: Fuel) { name = "seed"; }
    on Set() { name = "persisted-value"; }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 48 {
            let n: i64 = junk.push(i * 7 + 1);
            i = i + 1;
        }
    }
    on Check() {
        if name.len() != 15 { trap(); }
        if name.byte_at(0) != 112 { trap(); }
        if name.byte_at(14) != 101 { trap(); }
    }
}
"#;

#[test]
fn mut_str_state_replacement_persists() {
    assert_eq!(
        delivered(STR_REPLACE_PERSISTS),
        Ok(4),
        "a replaced `mut str` state field must keep its bytes across dispatches"
    );
}

/// Replaced on EVERY dispatch, with a clobber between — the spec's exit
/// criterion for this slice. Each promotion must be independent.
const STR_REPLACED_EVERY_DISPATCH: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(SetA());
        w.send(Clobber());
        w.send(ExpectA());
        w.send(SetB());
        w.send(Clobber());
        w.send(ExpectB());
        return 0;
    }
}
actor Store {
    state { mut s: str }
    init(f: Fuel) { s = "x"; }
    on SetA() { s = "alpha"; }
    on SetB() { s = "bravo-longer"; }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 32 {
            let n: i64 = junk.push(i + 3);
            i = i + 1;
        }
    }
    on ExpectA() {
        if s.len() != 5 { trap(); }
        if s.byte_at(0) != 97 { trap(); }
    }
    on ExpectB() {
        if s.len() != 12 { trap(); }
        if s.byte_at(0) != 98 { trap(); }
        if s.byte_at(11) != 114 { trap(); }
    }
}
"#;

#[test]
fn str_replaced_every_dispatch_persists() {
    assert_eq!(
        delivered(STR_REPLACED_EVERY_DISPATCH),
        Ok(7),
        "each dispatch's replacement must promote independently"
    );
}

/// A str built by a HELPER — provenance the compiler cannot color — and a
/// str derived by SLICING (whose payload points into another buffer). Both
/// must promote to independent persistent bytes.
const STR_FROM_HELPER_AND_SLICE: &str = r#"module sigil;
cap type Fuel {}
fn pick() -> str { return "helper-built"; }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(SetHelper());
        w.send(Clobber());
        w.send(ExpectHelper());
        w.send(SetSlice());
        w.send(Clobber());
        w.send(ExpectSlice());
        return 0;
    }
}
actor Store {
    state { mut s: str }
    init(f: Fuel) { s = "x"; }
    on SetHelper() { let built: str = pick(); s = built; }
    on SetSlice() {
        let whole: str = "abcdefghij";
        let part: str = whole.substr(2, 5);
        s = part;
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 32 {
            let n: i64 = junk.push(i + 5);
            i = i + 1;
        }
    }
    on ExpectHelper() {
        if s.len() != 12 { trap(); }
        if s.byte_at(0) != 104 { trap(); }
    }
    on ExpectSlice() {
        if s.len() != 3 { trap(); }
        if s.byte_at(0) != 99 { trap(); }
        if s.byte_at(2) != 101 { trap(); }
    }
}
"#;

#[test]
fn helper_built_and_sliced_strs_promote() {
    assert_eq!(
        delivered(STR_FROM_HELPER_AND_SLICE),
        Ok(7),
        "helper-returned and substring-derived strs must both promote their bytes"
    );
}

/// Two `mut str` fields fed from one value promote independently, and an
/// empty string is a legal payload (zero-length copy).
const TWO_STR_FIELDS_AND_EMPTY: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Store>(fuel);
        w.send(SetBoth());
        w.send(Clobber());
        w.send(Check());
        return 0;
    }
}
actor Store {
    state { mut a: str, mut b: str }
    init(f: Fuel) { a = "i"; b = "j"; }
    on SetBoth() {
        let v: str = "shared";
        a = v;
        b = "";
    }
    on Clobber() {
        let mut junk: Vec<i64> = Vec::new();
        let mut i: i64 = 0;
        while i < 32 {
            let n: i64 = junk.push(i + 9);
            i = i + 1;
        }
    }
    on Check() {
        if a.len() != 6 { trap(); }
        if a.byte_at(0) != 115 { trap(); }
        if b.len() != 0 { trap(); }
    }
}
"#;

#[test]
fn two_str_fields_and_empty_payload() {
    assert_eq!(
        delivered(TWO_STR_FIELDS_AND_EMPTY),
        Ok(4),
        "independent promotions, and an empty payload is legal"
    );
}
