//! PPS-0 fences — the Change-rule half. Admitting `mut Map<scalar, scalar>`
//! state moves the C012 line, so every way a Map could escape its persistent
//! channel (or launder taint into it) needs an explicit negative before the
//! fence stays moved:
//!
//! - a grow through an ALIAS or a `@Mut` parameter reallocs into transient
//!   memory reclaimed after the dispatch (a dangling read) → T253;
//! - a `@Secret` key or value inserted into a `@Public` map and read back
//!   is a taint launder → T001;
//! - every shape NOT yet admitted (aggregate keys/values, `Map<str, _>`,
//!   nested maps) must still fail closed under C012.

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

/// The admitted shape itself must compile — the positive control that keeps
/// every negative below honest.
#[test]
fn mut_scalar_map_state_is_admitted() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<i64, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, i64> = Map::new(); m = tmp; }}\n\
         on Put(k: i64, v: i64) {{ let n: i64 = m.insert(k, v); }}\n\
         }}\n"
    );
    assert!(
        compiles(&src),
        "a `mut Map<i64, i64>` state field must be admitted; got {:?}",
        codes(&src)
    );
}

// ── Alias / parameter grows ─────────────────────────────────────────────────

/// Inserting through a LOCAL ALIAS of the state map: the alias is a frozen
/// (readonly-propagated) binding, so the `@Mut self` insert is rejected —
/// otherwise the interior reallocs would route through the transient
/// channel and dangle after the dispatch reset.
#[test]
fn insert_through_an_alias_is_rejected() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<i64, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, i64> = Map::new(); m = tmp; }}\n\
         on Put(k: i64, v: i64) {{ let alias = m; let n: i64 = alias.insert(k, v); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T253".to_string()),
        "growing a state Map through an alias must be rejected (T253); got {:?}",
        codes(&src)
    );
}

/// The transitive form — alias of an alias — must fail the same way.
#[test]
fn insert_through_a_transitive_alias_is_rejected() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<i64, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, i64> = Map::new(); m = tmp; }}\n\
         on Put(k: i64, v: i64) {{ let a = m; let b = a; let n: i64 = b.insert(k, v); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T253".to_string()),
        "a transitively-aliased state-Map insert must be rejected (T253); got {:?}",
        codes(&src)
    );
}

/// Passing the state map into a helper's `@Mut` parameter: the callee could
/// grow it through a non-state binding, so the HOLE-DANGLE gate rejects it.
#[test]
fn passing_state_map_to_a_mut_parameter_is_rejected() {
    let src = format!(
        "{HEAD}fn stuff(t: Map<i64, i64> @Mut, k: i64, v: i64) -> i64 ! {{ Alloc }} {{ return t.insert(k, v); }}\n\
         actor Store {{\n\
         state {{ mut m: Map<i64, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, i64> = Map::new(); m = tmp; }}\n\
         on Put(k: i64, v: i64) {{ let n: i64 = stuff(m, k, v); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T253".to_string()),
        "handing a state Map to a `@Mut` param must be rejected (T253); got {:?}",
        codes(&src)
    );
}

// ── Taint ───────────────────────────────────────────────────────────────────

/// A `@Secret` VALUE inserted into a `@Public` state map, then read back
/// clean, is a laundering path — the map is a taint sink like the Vec.
#[test]
fn inserting_a_secret_value_launders_taint() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<i64, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, i64> = Map::new(); m = tmp; }}\n\
         on Set(s: i64 @Secret) {{ let n: i64 = m.insert(1, s); }}\n\
         on Leak() -> i64 {{ return m.get_or(1, 0); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T001".to_string()),
        "inserting a @Secret value into public state must be blocked (T001); got {:?}",
        codes(&src)
    );
}

/// A `@Secret` KEY is equally laundering — key bytes reach the same storage.
#[test]
fn inserting_a_secret_key_launders_taint() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<i64, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, i64> = Map::new(); m = tmp; }}\n\
         on Set(s: i64 @Secret) {{ let n: i64 = m.insert(s, 1); }}\n\
         on Leak() -> i64 {{ return m.len(); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T001".to_string()),
        "inserting a @Secret key into public state must be blocked (T001); got {:?}",
        codes(&src)
    );
}

// ── Still-fenced shapes (C012 holds) ────────────────────────────────────────

/// `Map<str, i64>` was fenced when PPS-0 landed (string keys are heap pointers, which coloring
/// alone cannot persist). PPS-2b admits it — the key's bytes promote at the storing `push`.
/// `pps2b_str_map_fences.rs` owns the boundary now.
#[test]
fn mut_str_keyed_map_state_is_admitted_since_pps2b() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<str, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<str, i64> = Map::new(); m = tmp; }}\n\
         on Put(v: i64) {{ let n: i64 = m.insert(\"k\", v); }}\n\
         }}\n"
    );
    assert!(
        !codes(&src).contains(&"C012".to_string()),
        "PPS-2b admits `mut Map<str, i64>` state; got {:?}",
        codes(&src)
    );
}

/// `Vec<FLAT record>` got its per-element promotion in PPS-3: the storing
/// push copies the registry-listed fields into persistent memory. The line
/// moved to the element's INTERIOR — pointer-bearing records stay fenced,
/// tracked in `pps3_record_element_fences.rs`.
#[test]
fn mut_vec_of_records_state_is_admitted_since_pps3() {
    let src = format!(
        "{HEAD}record Point {{ x: i64, y: i64 }}\n\
         actor Store {{\n\
         state {{ mut v: Vec<Point> }}\n\
         init(f: Fuel) {{ let tmp: Vec<Point> = Vec::new(); v = tmp; }}\n\
         on Ping() {{ let n: i64 = v.len(); }}\n\
         }}\n"
    );
    assert!(
        !codes(&src).contains(&"C012".to_string()),
        "PPS-3 admits `mut Vec<Point>` state; got {:?}",
        codes(&src)
    );
}

/// A `mut str` state field was fenced when PPS-0 landed; PPS-2a admits it
/// (the store promotes payload bytes AND header). The boundary moved —
/// `pps2_str_fences.rs` owns it now.
#[test]
fn mut_str_state_is_admitted_since_pps2() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut s: str }}\n\
         init(f: Fuel) {{ s = \"init\"; }}\n\
         on Ping() {{ let n: i64 = s.len(); }}\n\
         }}\n"
    );
    assert!(
        !codes(&src).contains(&"C012".to_string()),
        "PPS-2a admits `mut str` state; got {:?}",
        codes(&src)
    );
}

/// A NON-`mut` Map state field is the AGG-1 shape (written once in `init`,
/// below the persistent floor) and was always allowed — admitting the `mut`
/// form must not disturb it.
#[test]
fn non_mut_map_state_still_compiles() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ m: Map<i64, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, i64> = Map::new(); m = tmp; }}\n\
         on Get(k: i64) -> i64 {{ return m.get_or(k, 0); }}\n\
         }}\n"
    );
    assert!(
        compiles(&src),
        "a non-`mut` Map state field must still compile; got {:?}",
        codes(&src)
    );
}
