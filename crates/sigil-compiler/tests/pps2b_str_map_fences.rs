//! PPS-2b fences. Admitting `Map<str, V>` state moves the C012 line once
//! more, so the Change rule applies: the dangle gates and the taint sink
//! must cover string-keyed maps too, and the shapes promotion still cannot
//! reach must stay closed.

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

#[test]
fn str_keyed_map_state_is_admitted() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<str, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<str, i64> = Map::new(); m = tmp; }}\n\
         on Put(v: i64) {{ let n: i64 = m.insert(\"k\", v); }}\n\
         }}\n"
    );
    assert!(
        compiles(&src),
        "a `mut Map<str, i64>` state field must be admitted; got {:?}",
        codes(&src)
    );
}

#[test]
fn str_to_str_map_state_is_admitted() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<str, str> }}\n\
         init(f: Fuel) {{ let tmp: Map<str, str> = Map::new(); m = tmp; }}\n\
         on Put() {{ let n: i64 = m.insert(\"k\", \"v\"); }}\n\
         }}\n"
    );
    assert!(
        compiles(&src),
        "a `mut Map<str, str>` state field must be admitted; got {:?}",
        codes(&src)
    );
}

/// Taint must survive the byte promotion: a `@Secret` string KEY stored into
/// a public map is a launder.
#[test]
fn inserting_a_secret_str_key_launders_taint() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<str, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<str, i64> = Map::new(); m = tmp; }}\n\
         on Set(k: str @Secret) {{ let n: i64 = m.insert(k, 1); }}\n\
         on Leak() -> i64 {{ return m.len(); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T001".to_string()),
        "a @Secret string key must not launder into public state (T001); got {:?}",
        codes(&src)
    );
}

/// …and a `@Secret` string VALUE likewise.
#[test]
fn inserting_a_secret_str_value_launders_taint() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<str, str> }}\n\
         init(f: Fuel) {{ let tmp: Map<str, str> = Map::new(); m = tmp; }}\n\
         on Set(v: str @Secret) {{ let n: i64 = m.insert(\"k\", v); }}\n\
         on Leak() -> i64 {{ return m.len(); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T001".to_string()),
        "a @Secret string value must not launder into public state (T001); got {:?}",
        codes(&src)
    );
}

/// The dangle gates carry over: inserting through an alias of a string-keyed
/// state map is still T253.
#[test]
fn insert_into_a_str_keyed_map_through_an_alias_is_rejected() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<str, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<str, i64> = Map::new(); m = tmp; }}\n\
         on Put(v: i64) {{ let alias = m; let n: i64 = alias.insert(\"k\", v); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T253".to_string()),
        "an aliased insert into a string-keyed state map must be rejected (T253); got {:?}",
        codes(&src)
    );
}

/// Wholesale replacement of a string-keyed map is still T128 — the map's
/// interior is pointer-bearing, so a shallow store would dangle.
#[test]
fn wholesale_str_map_replacement_stays_rejected() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<str, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<str, i64> = Map::new(); m = tmp; }}\n\
         on Reset() {{ let fresh: Map<str, i64> = Map::new(); m = fresh; }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T128".to_string()),
        "replacing a whole string-keyed state map must stay rejected (T128); got {:?}",
        codes(&src)
    );
}

/// The PPS-2b tombstone, RESOLVED by PPS-3. The trap was admission/routing
/// drift, not a promotion gap: C012 admitted `Vec<str>` but the routing gate
/// in `methods.rs` still required a SCALAR element, so a state `Vec<str>`
/// never routed to a `$state` instance — its buffer grew transiently and the
/// storing-push promotion never fired. One cause, two symptoms. Both gates
/// now share `is_persistable_scalar_vec`, so they cannot drift again.
#[test]
fn vec_of_str_state_is_admitted_since_pps3() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut v: Vec<str> }}\n\
         init(f: Fuel) {{ let tmp: Vec<str> = Vec::new(); v = tmp; }}\n\
         on Ping() {{ let n: i64 = v.len(); }}\n\
         }}\n"
    );
    assert!(
        !codes(&src).contains(&"C012".to_string()),
        "PPS-3 admits `mut Vec<str>` state; got {:?}",
        codes(&src)
    );
}

/// FLAT record values were admitted by PPS-3 (the storing push copies the
/// registry-listed fields into persistent memory). The line moved to the
/// element's INTERIOR: pointer-bearing records stay fenced, tracked in
/// `pps3_record_element_fences.rs`.
#[test]
fn record_valued_map_state_is_admitted_since_pps3() {
    let src = format!(
        "{HEAD}record K {{ a: i64 }}\n\
         actor Store {{\n\
         state {{ mut m: Map<i64, K> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, K> = Map::new(); m = tmp; }}\n\
         on Ping() -> i64 {{ return 0; }}\n\
         }}\n"
    );
    assert!(
        !codes(&src).contains(&"C012".to_string()),
        "PPS-3 admits flat-record map values; got {:?}",
        codes(&src)
    );
}
