//! PPS-3 fences. Admitting record ELEMENTS (Vec elements, Map keys and
//! values) moves the C012 line again, so the Change rule applies: the taint
//! sink and dangle gates must cover record elements, and the shapes the
//! per-element promotion still cannot reach — records with POINTER-BEARING
//! interiors (str/Vec/record fields) and non-record aggregate elements —
//! stay closed. The storing push copies exactly the fields the registry
//! lists; a pointer field would be copied shallowly and dangle, so those
//! interiors are fenced at admission.

use sigil_compiler::compile_module;

fn codes(src: &str) -> Vec<String> {
    match compile_module(src) {
        Ok(_) => Vec::new(),
        Err(err) => err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn compiles(src: &str) -> bool {
    compile_module(src).is_ok()
}

const HEAD: &str = "module sigil;\ncap type Fuel {}\n\
entry actor Main { state { fuel: Fuel } on Start() -> i64 { let w = spawn::<Store>(fuel); return 0; } }\n";

// ---------------------------------------------------------------- admitted

#[test]
fn vec_of_flat_records_state_is_admitted() {
    let src = format!(
        "{HEAD}record Point {{ x: i64, y: i64 }}\n\
         actor Store {{\n\
         state {{ mut v: Vec<Point> }}\n\
         init(f: Fuel) {{ let tmp: Vec<Point> = Vec::new(); v = tmp; }}\n\
         on Add() {{ let p = Point {{ x: 1, y: 2 }}; let n: i64 = v.push(p); }}\n\
         }}\n"
    );
    assert!(
        compiles(&src),
        "a `mut Vec<Point>` state field must be admitted; got {:?}",
        codes(&src)
    );
}

#[test]
fn record_valued_map_state_is_admitted() {
    let src = format!(
        "{HEAD}record Sess {{ hits: i64 }}\n\
         actor Store {{\n\
         state {{ mut m: Map<i64, Sess> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, Sess> = Map::new(); m = tmp; }}\n\
         on Put(k: i64) {{ let s = Sess {{ hits: 1 }}; let n: i64 = m.insert(k, s); }}\n\
         }}\n"
    );
    assert!(
        compiles(&src),
        "a `mut Map<i64, Sess>` state field must be admitted; got {:?}",
        codes(&src)
    );
}

/// Record KEYS too: the map is trait-based (`key.hash()` / `stored.eq(key)`),
/// both content-hashing, so a promoted key COPY still matches later probes.
/// Hashability itself is the trait Wall's job (same as non-state maps).
#[test]
fn record_keyed_map_state_is_admitted() {
    let src = format!(
        "{HEAD}record Pair {{ a: i64, b: i64 }}\n\
         impl Hash for Pair {{ fn hash(self: Pair) -> i64 {{ return self.a * 31 + self.b; }} }}\n\
         impl Eq for Pair {{\n\
             fn eq(self: Pair, other: Pair) -> bool {{\n\
                 if self.a == other.a {{ return self.b == other.b; }} else {{ return false; }}\n\
             }}\n\
         }}\n\
         actor Store {{\n\
         state {{ mut m: Map<Pair, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<Pair, i64> = Map::new(); m = tmp; }}\n\
         on Put(n: i64) {{ let k = Pair {{ a: n, b: n }}; let c: i64 = m.insert(k, n); }}\n\
         }}\n"
    );
    assert!(
        compiles(&src),
        "a `mut Map<Pair, i64>` state field (Hash+Eq record key) must be admitted; got {:?}",
        codes(&src)
    );
}

/// The epic's capstone shape: string keys (PPS-2b) + record values (PPS-3).
#[test]
fn str_keyed_record_valued_map_state_is_admitted() {
    let src = format!(
        "{HEAD}record Sess {{ hits: i64, level: i64 }}\n\
         actor Store {{\n\
         state {{ mut m: Map<str, Sess> }}\n\
         init(f: Fuel) {{ let tmp: Map<str, Sess> = Map::new(); m = tmp; }}\n\
         on Put() {{ let s = Sess {{ hits: 1, level: 2 }}; let n: i64 = m.insert(\"k\", s); }}\n\
         }}\n"
    );
    assert!(
        compiles(&src),
        "the capstone `mut Map<str, Sess>` state field must be admitted; got {:?}",
        codes(&src)
    );
}

// ------------------------------------------------- the remaining fence line

/// A record element with a `str` field: the field copy would duplicate the
/// HEADER pointer, not the payload — a transitive walk PPS-3 does not do.
#[test]
fn vec_of_records_containing_str_stays_fenced() {
    let src = format!(
        "{HEAD}record Evt {{ tag: str, n: i64 }}\n\
         actor Store {{\n\
         state {{ mut v: Vec<Evt> }}\n\
         init(f: Fuel) {{ let tmp: Vec<Evt> = Vec::new(); v = tmp; }}\n\
         on Ping() {{ let n: i64 = v.len(); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"C012".to_string()),
        "a `Vec<Evt>` element with a str interior must stay fenced (C012); got {:?}",
        codes(&src)
    );
}

/// A record element with a `Vec` field dangles the same way.
#[test]
fn vec_of_records_containing_vec_stays_fenced() {
    let src = format!(
        "{HEAD}record Bag {{ items: Vec<i64> }}\n\
         actor Store {{\n\
         state {{ mut v: Vec<Bag> }}\n\
         init(f: Fuel) {{ let tmp: Vec<Bag> = Vec::new(); v = tmp; }}\n\
         on Ping() {{ let n: i64 = v.len(); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"C012".to_string()),
        "a `Vec<Bag>` element with a Vec interior must stay fenced (C012); got {:?}",
        codes(&src)
    );
}

/// A NESTED record element (record field pointing at another record).
#[test]
fn vec_of_nested_records_stays_fenced() {
    let src = format!(
        "{HEAD}record Inner {{ n: i64 }}\n\
         record Outer {{ inner: Inner, m: i64 }}\n\
         actor Store {{\n\
         state {{ mut v: Vec<Outer> }}\n\
         init(f: Fuel) {{ let tmp: Vec<Outer> = Vec::new(); v = tmp; }}\n\
         on Ping() {{ let n: i64 = v.len(); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"C012".to_string()),
        "a `Vec<Outer>` nested-record element must stay fenced (C012); got {:?}",
        codes(&src)
    );
}

/// Map values with pointer-bearing interiors are fenced identically.
#[test]
fn map_with_str_bearing_record_values_stays_fenced() {
    let src = format!(
        "{HEAD}record Sess {{ name: str }}\n\
         actor Store {{\n\
         state {{ mut m: Map<str, Sess> }}\n\
         init(f: Fuel) {{ let tmp: Map<str, Sess> = Map::new(); m = tmp; }}\n\
         on Ping() -> i64 {{ return 0; }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"C012".to_string()),
        "a map value with a str interior must stay fenced (C012); got {:?}",
        codes(&src)
    );
}

/// Non-record aggregate elements: `Vec<Vec<_>>` has no field registry to
/// copy from — a different promotion problem, not this slice's. (The
/// UNSPACED `Vec<Vec<i64>>` spelling doesn't even parse — the `>>` lexing
/// moat — so the spaced form is what exercises the admission line.)
#[test]
fn vec_of_vecs_stays_fenced() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut v: Vec<Vec<i64> > }}\n\
         init(f: Fuel) {{ let tmp: Vec<Vec<i64> > = Vec::new(); v = tmp; }}\n\
         on Ping() {{ let n: i64 = v.len(); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"C012".to_string()),
        "a `Vec<Vec<i64>>` state field must stay fenced (C012); got {:?}",
        codes(&src)
    );
}

#[test]
fn map_with_vec_values_stays_fenced() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<i64, Vec<i64> > }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, Vec<i64> > = Map::new(); m = tmp; }}\n\
         on Ping() -> i64 {{ return 0; }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"C012".to_string()),
        "a `Map<i64, Vec<i64>>` state field must stay fenced (C012); got {:?}",
        codes(&src)
    );
}

// -------------------------------------------------- Change-rule carryovers

/// Taint joins into a record at construction and must survive the field
/// copy: a record built from a @Secret scalar pushed into public state is a
/// launder.
#[test]
fn pushing_a_secret_bearing_record_launders_taint() {
    let src = format!(
        "{HEAD}record Point {{ x: i64, y: i64 }}\n\
         actor Store {{\n\
         state {{ mut v: Vec<Point> }}\n\
         init(f: Fuel) {{ let tmp: Vec<Point> = Vec::new(); v = tmp; }}\n\
         on Add(s: i64 @Secret) {{ let p = Point {{ x: s, y: 0 }}; let n: i64 = v.push(p); }}\n\
         on Leak() -> i64 {{ return v.len(); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T001".to_string()),
        "a @Secret-bearing record must not launder into public state (T001); got {:?}",
        codes(&src)
    );
}

/// The dangle gates carry over: pushing through an alias of a record-element
/// state vec is still T253.
#[test]
fn push_through_an_alias_of_a_record_vec_is_rejected() {
    let src = format!(
        "{HEAD}record Point {{ x: i64, y: i64 }}\n\
         actor Store {{\n\
         state {{ mut v: Vec<Point> }}\n\
         init(f: Fuel) {{ let tmp: Vec<Point> = Vec::new(); v = tmp; }}\n\
         on Add() {{ let alias = v; let p = Point {{ x: 1, y: 2 }}; let n: i64 = alias.push(p); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T253".to_string()),
        "an aliased push into a record-element state vec must be rejected (T253); got {:?}",
        codes(&src)
    );
}

/// Wholesale replacement of a record-element collection stays T128: the
/// collection's interior is pointer-bearing, so a shallow store would
/// dangle. Only the storing-push mutation path is promoted.
#[test]
fn wholesale_record_vec_replacement_stays_rejected() {
    let src = format!(
        "{HEAD}record Point {{ x: i64, y: i64 }}\n\
         actor Store {{\n\
         state {{ mut v: Vec<Point> }}\n\
         init(f: Fuel) {{ let tmp: Vec<Point> = Vec::new(); v = tmp; }}\n\
         on Reset() {{ let fresh: Vec<Point> = Vec::new(); v = fresh; }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T128".to_string()),
        "wholesale replacement of a record-element state vec must stay T128; got {:?}",
        codes(&src)
    );
}
