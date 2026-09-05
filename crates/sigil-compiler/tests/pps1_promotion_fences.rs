//! PPS-1 fences. Relaxing T128 for promotable shapes moves a boundary, so
//! the Change rule applies: everything promotion does NOT yet reach must
//! still fail closed, and the shapes it does reach must be admitted for the
//! right reason.

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

// ── Admitted: flat aggregates ───────────────────────────────────────────────

#[test]
fn flat_record_replacement_is_admitted() {
    let src = format!(
        "{HEAD}record Point {{ x: i64, y: i64 }}\n\
         actor Store {{\n\
         state {{ mut p: Point }}\n\
         init(f: Fuel) {{ let s = Point {{ x: 0, y: 0 }}; p = s; }}\n\
         on Set(a: i64) {{ p = Point {{ x: a, y: a }}; }}\n\
         }}\n"
    );
    assert!(
        compiles(&src),
        "a flat record state field must be wholesale-reassignable (promoted); got {:?}",
        codes(&src)
    );
}

#[test]
fn flat_tuple_and_array_replacement_are_admitted() {
    let tuple_src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut t: (i64, i64) }}\n\
         init(f: Fuel) {{ t = (0, 0); }}\n\
         on Set(a: i64) {{ t = (a, a); }}\n\
         }}\n"
    );
    assert!(
        !codes(&tuple_src).contains(&"T128".to_string()),
        "a flat tuple state field must be wholesale-reassignable; got {:?}",
        codes(&tuple_src)
    );

    let array_src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut a: [i64; 3] }}\n\
         init(f: Fuel) {{ a = [0, 0, 0]; }}\n\
         on Set(x: i64) {{ a = [x, x, x]; }}\n\
         }}\n"
    );
    assert!(
        !codes(&array_src).contains(&"T128".to_string()),
        "a flat array state field must be wholesale-reassignable; got {:?}",
        codes(&array_src)
    );
}

/// In-place mutation — the AGG-2a path — must still be legal alongside
/// replacement (the relaxation must not have swapped one for the other).
#[test]
fn in_place_mutation_still_compiles() {
    let src = format!(
        "{HEAD}record Point {{ x: i64, y: i64 }}\n\
         actor Store {{\n\
         state {{ mut p: Point }}\n\
         init(f: Fuel) {{ let s = Point {{ x: 0, y: 0 }}; p = s; }}\n\
         on Bump() {{ p.x = p.x + 1; }}\n\
         }}\n"
    );
    assert!(
        compiles(&src),
        "in-place mutation must still compile; got {:?}",
        codes(&src)
    );
}

// ── Still fenced: pointer-bearing shapes (PPS-2/3) ──────────────────────────

/// A record holding a `Vec` needs TRANSITIVE promotion — the interior
/// buffer would still live in per-dispatch scratch after a shallow copy.
/// Its field type is not admitted as state at all yet (C012), and wholesale
/// replacement stays rejected.
#[test]
fn record_containing_a_vec_stays_fenced() {
    let src = format!(
        "{HEAD}record Bag {{ items: Vec<i64>, n: i64 }}\n\
         actor Store {{\n\
         state {{ mut b: Bag }}\n\
         init(f: Fuel) {{ let v: Vec<i64> = Vec::new(); let s = Bag {{ items: v, n: 0 }}; b = s; }}\n\
         on Ping() -> i64 {{ return 0; }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"C012".to_string()),
        "a `mut` record holding a Vec must stay fenced (C012); got {:?}",
        codes(&src)
    );
}

/// A NESTED record (record of records) is likewise not flat: a shallow copy
/// would leave the inner object transient.
#[test]
fn nested_record_replacement_stays_fenced() {
    let src = format!(
        "{HEAD}record Inner {{ v: i64 }}\n\
         record Outer {{ i: Inner, n: i64 }}\n\
         actor Store {{\n\
         state {{ mut o: Outer }}\n\
         init(f: Fuel) {{ let inner = Inner {{ v: 1 }}; let s = Outer {{ i: inner, n: 0 }}; o = s; }}\n\
         on Ping() -> i64 {{ return 0; }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"C012".to_string()),
        "a `mut` nested record must stay fenced (C012); got {:?}",
        codes(&src)
    );
}

/// Wholesale replacement of a `mut Vec<scalar>` state field — the PPS-0/AGG-2b
/// shape — is NOT promotion's business: the Vec's buffer is transient, so a
/// shallow header copy would dangle. T128 must still reject it.
#[test]
fn wholesale_vec_replacement_stays_rejected() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut v: Vec<i64> }}\n\
         init(f: Fuel) {{ let tmp: Vec<i64> = Vec::new(); v = tmp; }}\n\
         on Reset() {{ let fresh: Vec<i64> = Vec::new(); v = fresh; }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T128".to_string()),
        "replacing a whole state Vec must stay rejected (T128); got {:?}",
        codes(&src)
    );
}

/// Same for a `mut Map` state field (admitted by PPS-0 for GROWTH, not for
/// wholesale replacement).
#[test]
fn wholesale_map_replacement_stays_rejected() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<i64, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, i64> = Map::new(); m = tmp; }}\n\
         on Reset() {{ let fresh: Map<i64, i64> = Map::new(); m = fresh; }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T128".to_string()),
        "replacing a whole state Map must stay rejected (T128); got {:?}",
        codes(&src)
    );
}

/// A NON-`mut` aggregate state field is still write-once: the relaxation is
/// scoped to `mut` fields and must not have opened T123.
#[test]
fn non_mut_aggregate_replacement_still_rejected() {
    let src = format!(
        "{HEAD}record Point {{ x: i64, y: i64 }}\n\
         actor Store {{\n\
         state {{ p: Point }}\n\
         init(f: Fuel) {{ let s = Point {{ x: 0, y: 0 }}; p = s; }}\n\
         on Set(a: i64) {{ p = Point {{ x: a, y: a }}; }}\n\
         }}\n"
    );
    let got = codes(&src);
    assert!(
        got.contains(&"T123".to_string()) || got.contains(&"T128".to_string()),
        "a non-`mut` aggregate state field must stay write-once; got {got:?}"
    );
}
