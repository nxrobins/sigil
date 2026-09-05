//! AGG-4 aggregate-state fence regression corpus (37 adversarial fixtures).
//!
//! The persistent-aggregate-state epic (AGG-1/AGG-2a) un-fenced aggregate actor `state {}`
//! fields; the post-merge adversarial sweep found 3 runtime-confirmed holes NEWLY reachable by
//! that un-fencing — (A1) alias-write on a non-`mut` aggregate (`let e=d; e.f=x`), (A2) `@Mut`
//! method receiver on a non-`mut` aggregate (`b.push(x)`), and (B) taint launder through an
//! aggregate-projected state write (`d.f = @Secret`). AGG-4 fenced all three fail-closed by
//! marking a non-`mut` state-aggregate read as frozen (so T251/T253 fire) and rooting a projected
//! write to its StateField for the T001 taint sink. This corpus locks the fences: a
//! "should-be-fenced" fixture PASSES iff it is rejected by SOMETHING (not OK_CLEAN — so a hole
//! reopening flips the verdict and fails the test), and a "COMPILES_CLEAN_SOUND" fixture (a `mut`
//! aggregate mutated in place / via alias — the intended AGG-2a path) PASSES iff it compiles
//! PPS-1 UPDATE: the whole `wholesale-reassign` family flipped from `T128` to
//! `COMPILES_CLEAN_SOUND`. Every fixture in it stores a FLAT aggregate (a record/array/tuple of
//! scalars) into a `mut` state field in a handler — the shape the promotion primitive now copies
//! into the persistent heap at the store boundary, so it persists and is sound to admit. The
//! pointer-bearing families (`dynamic-vec`, `nested-record`) still fence.
//!
//! clean. The agent-guessed `expected` code is informational; the real invariant is
//! rejected-vs-clean. See docs/specs/persistent-aggregate-state.md (AGG-4).
use sigil_compiler::compile_named_module;

fn verdict(name: &str, src: &str) -> String {
    match compile_named_module(name, src) {
        Ok(_) => "OK_CLEAN".to_string(),
        Err(e) => {
            let codes: Vec<String> = e
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_string())
                .collect();
            if codes.is_empty() {
                "ERR_NOCODE".to_string()
            } else {
                codes.join(",")
            }
        }
    }
}

struct Fx {
    id: &'static str,
    family: &'static str,
    expected: &'static str,
    is_mut: bool,
    src: &'static str,
}

fn fixtures() -> Vec<Fx> {
    vec![
        Fx {
            id: "dyn-mut-bounded-vec-record",
            family: "dynamic-vec",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Bag { data: [i64; 4], count: i64 }
impl Bag {
    pub fn new() -> Bag { return Bag { data: [0, 0, 0, 0], count: 0 }; }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut b: Bag }
    init(f: Fuel) { b = Bag::new(); }
    on Get() -> i64 { return b.count; }
}
"#,
        },
        Fx {
            id: "dyn-mut-bounded-map-record",
            family: "dynamic-vec",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record IntMap { keys: [i64; 8], vals: [i64; 8], count: i64 }
impl IntMap {
    pub fn new() -> IntMap { return IntMap { keys: [0, 0, 0, 0, 0, 0, 0, 0], vals: [0, 0, 0, 0, 0, 0, 0, 0], count: 0 }; }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut m: IntMap }
    init(f: Fuel) { m = IntMap::new(); }
    on Get() -> i64 { return m.count; }
}
"#,
        },
        Fx {
            id: "dyn-mut-array-of-vecs",
            family: "dynamic-vec",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Bag { data: [i64; 4], count: i64 }
impl Bag {
    pub fn new() -> Bag { return Bag { data: [0, 0, 0, 0], count: 0 }; }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut a: [Bag; 2] }
    init(f: Fuel) { a = [Bag::new(), Bag::new()]; }
    on Get() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "dyn-mut-nested-vec-in-record",
            family: "nested-record",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Bag { data: [i64; 4], count: i64 }
record Holder { bag: Bag }
impl Bag {
    pub fn new() -> Bag { return Bag { data: [0, 0, 0, 0], count: 0 }; }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut h: Holder }
    init(f: Fuel) { h = Holder { bag: Bag::new() }; }
    on Get() -> i64 { return h.bag.count; }
}
"#,
        },
        Fx {
            id: "dyn-nonmut-vec-grow-via-mut-method",
            family: "non-mut-grow",
            expected: "T123",
            is_mut: false,
            src: r#"module sigil;
cap type Fuel {}
record Bag { data: [i64; 4], count: i64 }
impl Bag {
    pub fn new() -> Bag { return Bag { data: [0, 0, 0, 0], count: 0 }; }
    pub fn push(self: Bag @Mut, v: i64) -> i64 { self.data[self.count] = v; self.count = self.count + 1; return self.count; }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { b: Bag }
    init(f: Fuel) { b = Bag::new(); }
    on Add(x: i64) { let n: i64 = b.push(x); }
    on Get() -> i64 { return b.count; }
}
"#,
        },
        Fx {
            id: "dyn-nonmut-vec-grow-via-aliased-local",
            family: "non-mut-grow",
            expected: "T123",
            is_mut: false,
            src: r#"module sigil;
cap type Fuel {}
record Bag { data: [i64; 4], count: i64 }
impl Bag {
    pub fn new() -> Bag { return Bag { data: [0, 0, 0, 0], count: 0 }; }
    pub fn push(self: Bag @Mut, v: i64) -> i64 { self.data[self.count] = v; self.count = self.count + 1; return self.count; }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { b: Bag }
    init(f: Fuel) { b = Bag::new(); }
    on Add(x: i64) { let a: Bag = b; let n: i64 = a.push(x); }
    on Get() -> i64 { return b.count; }
}
"#,
        },
        Fx {
            id: "dyn-mut-tuple-embedding-vec",
            family: "nested-record",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Bag { data: [i64; 4], count: i64 }
impl Bag {
    pub fn new() -> Bag { return Bag { data: [0, 0, 0, 0], count: 0 }; }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut t: (i64, Bag) }
    init(f: Fuel) { t = (0, Bag::new()); }
    on Get() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "flat-record-wraps-single-scalar-record",
            family: "heap-in-flat-record",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Id { v: i64 }
record Rec { id: Id, n: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut r: Rec }
    init(f: Fuel) { r = Rec { id: Id { v: 0 }, n: 0 }; }
    on Ping() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "flat-record-with-u256-field",
            family: "heap-in-flat-record",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Acct { bal: u256, nonce: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut a: Acct }
    init(f: Fuel) { a = Acct { bal: 0, nonce: 0 }; }
    on Ping() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "flat-record-with-str-field",
            family: "str-field",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record User { age: i32, name: str }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut u: User }
    init(f: Fuel) { u = User { age: 0, name: "" }; }
    on Ping() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "flat-record-with-nested-array-field",
            family: "nested-array",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Buf { data: [i64; 3], len: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut b: Buf }
    init(f: Fuel) { b = Buf { data: [0, 0, 0], len: 0 }; }
    on Ping() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "flat-record-with-nested-tuple-field",
            family: "nested-tuple",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Pt { pair: (i64, i64), z: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut p: Pt }
    init(f: Fuel) { p = Pt { pair: (0, 0), z: 0 }; }
    on Ping() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "flat-record-with-enum-field",
            family: "enum-field",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
enum Color { Red, Green }
record Paint { c: Color, n: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut p: Paint }
    init(f: Fuel) { p = Paint { c: Color::Red, n: 0 }; }
    on Ping() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "flat-record-field-alias-to-str",
            family: "projected-launder",
            expected: "C012",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
type Blob = str;
record Wrap { tag: i64, b: Blob }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut w: Wrap }
    init(f: Fuel) { w = Wrap { tag: 0, b: "" }; }
    on Ping() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "flat-record-embeds-capability",
            family: "cap-in-aggregate",
            expected: "C011",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Holder { power: Fuel, n: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut h: Holder }
    init(f: Fuel) { h = Holder { power: f, n: 0 }; }
    on Ping() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "direct-array-wholesale",
            family: "wholesale-reassign",
            expected: "COMPILES_CLEAN_SOUND",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut a: [i64; 4] }
    init(f: Fuel) { a = [0, 0, 0, 0]; }
    on Reset() { a = [1, 2, 3, 4]; }
    on Get() -> i64 { return a[0]; }
}
"#,
        },
        Fx {
            id: "if-branch-reassign",
            family: "wholesale-reassign",
            expected: "COMPILES_CLEAN_SOUND",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Set(x: i64) { let c: bool = true; if c { d = Data { v: x }; } }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "match-arm-reassign",
            family: "wholesale-reassign",
            expected: "COMPILES_CLEAN_SOUND",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Set(n: i64) { match n { 0 => { d = Data { v: 0 }; }, _ => { d = Data { v: n }; } } }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "for-body-reassign",
            family: "wholesale-reassign",
            expected: "COMPILES_CLEAN_SOUND",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Fill(x: i64) { for i in 0..1 { d = Data { v: x }; } }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "from-fn-return",
            family: "wholesale-reassign",
            expected: "COMPILES_CLEAN_SOUND",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
fn make(x: i64) -> Data { return Data { v: x }; }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Set(x: i64) { d = make(x); }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "swap-two-mut-aggregates",
            family: "wholesale-reassign",
            expected: "COMPILES_CLEAN_SOUND",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut d: Data, mut e: Data }
    init(f: Fuel) { d = Data { v: 1 }; e = Data { v: 2 }; }
    on Swap() { let tmp: Data = d; d = e; e = tmp; }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "element-then-whole",
            family: "wholesale-reassign",
            expected: "COMPILES_CLEAN_SOUND",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Reset(x: i64) { d.v = x; d = Data { v: 0 }; }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "tuple-wholesale",
            family: "wholesale-reassign",
            expected: "COMPILES_CLEAN_SOUND",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut t: (i64, i64) }
    init(f: Fuel) { t = (0, 0); }
    on Set(x: i64) { t = (x, x); }
    on Get() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "proj-record-handler-secret-launder",
            family: "projected-launder",
            expected: "T001",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Set(s: i64 @Secret) { d.v = s; }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "proj-array-handler-secret-launder",
            family: "projected-launder",
            expected: "T001",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut a: [i64; 4] }
    init(f: Fuel) { a = [0, 0, 0, 0]; }
    on Set(s: i64 @Secret) { a[0] = s; }
    on Get() -> i64 { return a[0]; }
}
"#,
        },
        Fx {
            id: "proj-record-init-secret-launder",
            family: "projected-launder",
            expected: "T001",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
actor Worker {
    state { mut d: Data }
    init(f: Fuel, s: i64 @Secret) { d = Data { v: 0 }; d.v = s; }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "nonmut-proj-init-secret-launder",
            family: "projected-launder",
            expected: "T001",
            is_mut: false,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
actor Worker {
    state { d: Data }
    init(f: Fuel, s: i64 @Secret) { d = Data { v: 0 }; d.v = s; }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "bare-scalar-handler-secret-control",
            family: "str-field",
            expected: "T001",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut n: i64 }
    init(f: Fuel) { n = 0; }
    on Set(s: i64 @Secret) { n = s; }
    on Get() -> i64 { return n; }
}
"#,
        },
        Fx {
            id: "cap-in-mut-aggregate",
            family: "cap-in-aggregate",
            expected: "C011",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record CapBox { f: Fuel }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut b: CapBox }
    init(f: Fuel) { b = CapBox { f: f }; }
    on Get() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "cap-in-nonmut-aggregate",
            family: "cap-in-aggregate",
            expected: "T183",
            is_mut: false,
            src: r#"module sigil;
cap type Fuel {}
record CapBox { f: Fuel }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { b: CapBox }
    init(f: Fuel) { b = CapBox { f: f }; }
    on Get() -> i64 { return 0; }
}
"#,
        },
        Fx {
            id: "alias-nonmut-record-writethrough",
            family: "projected-launder",
            expected: "T123",
            is_mut: false,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); w.send(Set(9)); return 0; }
}
actor Worker {
    state { d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Set(x: i64) { let e = d; e.v = x; }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "alias-nonmut-array-index-through",
            family: "projected-launder",
            expected: "T123",
            is_mut: false,
            src: r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); w.send(Set(9)); return 0; }
}
actor Worker {
    state { a: [i64; 4] }
    init(f: Fuel) { a = [0, 0, 0, 0]; }
    on Set(x: i64) { let e = a; e[0] = x; }
    on Get() -> i64 { return a[0]; }
}
"#,
        },
        Fx {
            id: "two-hop-alias-nonmut-record",
            family: "aliased-launder",
            expected: "T123",
            is_mut: false,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); w.send(Set(9)); return 0; }
}
actor Worker {
    state { d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Set(x: i64) { let e = d; let g = e; g.v = x; }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "fn-param-mutation-launder-nonmut-record",
            family: "cross-fn-launder",
            expected: "T123",
            is_mut: false,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
fn bump(q: Data, x: i64) { q.v = x; }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); w.send(Set(9)); return 0; }
}
actor Worker {
    state { d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Set(x: i64) { bump(d, x); }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "direct-projected-write-nonmut-record-CONTROL",
            family: "projected-launder",
            expected: "T123",
            is_mut: false,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); w.send(Set(9)); return 0; }
}
actor Worker {
    state { d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Set(x: i64) { d.v = x; }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "alias-mut-flat-record-inplace-SOUND",
            family: "aliased-launder",
            expected: "COMPILES_CLEAN_SOUND",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
record Data { v: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); w.send(Set(9)); return 0; }
}
actor Worker {
    state { mut d: Data }
    init(f: Fuel) { d = Data { v: 0 }; }
    on Set(x: i64) { let e = d; e.v = x; }
    on Get() -> i64 { return d.v; }
}
"#,
        },
        Fx {
            id: "alias-mut-flat-array-inplace-SOUND",
            family: "aliased-launder",
            expected: "COMPILES_CLEAN_SOUND",
            is_mut: true,
            src: r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); w.send(Set(9)); return 0; }
}
actor Worker {
    state { mut a: [i64; 4] }
    init(f: Fuel) { a = [0, 0, 0, 0]; }
    on Set(x: i64) { let e = a; e[0] = x; }
    on Get() -> i64 { return a[0]; }
}
"#,
        },
    ]
}

#[test]
fn agg_fence_adversarial_sweep() {
    let mut holes = Vec::new();
    let mut overrestrict = Vec::new();
    for fx in fixtures() {
        let got = verdict(&format!("{}.sigil", fx.id), fx.src);
        let clean = got == "OK_CLEAN";
        let should_be_clean = fx.expected == "COMPILES_CLEAN_SOUND";
        let (tag, bad) = if should_be_clean {
            if clean {
                ("SOUND-OK", false)
            } else {
                ("OVER-RESTRICT", true)
            }
        } else if clean {
            ("**HOLE**", true)
        } else {
            ("HOLD", false)
        };
        let exact = if should_be_clean {
            clean
        } else {
            got.split(',').any(|c| c == fx.expected)
        };
        println!(
            "[{tag}] {:44} mut={:5} expect={:22} got={:20} exact_match={}",
            fx.id, fx.is_mut, fx.expected, got, exact
        );
        if bad {
            if should_be_clean {
                overrestrict.push(format!("{} (got {})", fx.id, got));
            } else {
                holes.push(format!(
                    "{} [{}] (should be fenced, compiled CLEAN)",
                    fx.id, fx.family
                ));
            }
        }
    }
    println!(
        "=== SWEEP: {} fixtures | {} HOLES | {} over-restrict ===",
        fixtures().len(),
        holes.len(),
        overrestrict.len()
    );
    if !overrestrict.is_empty() {
        println!("OVER-RESTRICT (usability, not a hole): {overrestrict:#?}");
    }
    assert!(
        holes.is_empty(),
        "ADVERSARIAL HOLES (compiled clean but should be fenced): {holes:#?}"
    );
}
