//! PPS-2a fences. Admitting `mut str` state moves the C012/T128 boundary
//! again, so the Change rule applies: taint must survive promotion, the
//! non-`mut` and pointer-bearing shapes must stay closed, and the admitted
//! shape must be admitted for the right reason.

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
fn mut_str_state_is_admitted() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut s: str }}\n\
         init(f: Fuel) {{ s = \"a\"; }}\n\
         on Set() {{ s = \"b\"; }}\n\
         }}\n"
    );
    assert!(
        compiles(&src),
        "a `mut str` state field must be admitted (promoted at the store); got {:?}",
        codes(&src)
    );
}

/// THE taint fence: a `@Secret` str stored into a `@Public` state field and
/// read back is a launder. Promotion copies BYTES — it must not launder the
/// label along the way.
#[test]
fn storing_a_secret_str_into_public_state_is_rejected() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut s: str }}\n\
         init(f: Fuel) {{ s = \"a\"; }}\n\
         on Set(secret: str @Secret) {{ s = secret; }}\n\
         on Leak() -> i64 {{ return s.len(); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T001".to_string()),
        "storing a @Secret str into public state must be blocked (T001); got {:?}",
        codes(&src)
    );
}

/// A non-`mut` `str` state field stays write-once (the relaxation is scoped
/// to `mut`).
#[test]
fn non_mut_str_state_stays_write_once() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ s: str }}\n\
         init(f: Fuel) {{ s = \"a\"; }}\n\
         on Set() {{ s = \"b\"; }}\n\
         }}\n"
    );
    let got = codes(&src);
    assert!(
        got.contains(&"T123".to_string()) || got.contains(&"T128".to_string()),
        "a non-`mut` str state field must stay write-once; got {got:?}"
    );
}

/// A record CONTAINING a `str` is still not flat: promoting it would need
/// the transitive walk (PPS-3), so it stays fenced.
#[test]
fn record_containing_a_str_stays_fenced() {
    let src = format!(
        "{HEAD}record Named {{ name: str, n: i64 }}\n\
         actor Store {{\n\
         state {{ mut r: Named }}\n\
         init(f: Fuel) {{ let s = Named {{ name: \"a\", n: 0 }}; r = s; }}\n\
         on Ping() -> i64 {{ return 0; }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"C012".to_string()),
        "a `mut` record holding a str must stay fenced (C012); got {:?}",
        codes(&src)
    );
}

/// String-KEYED maps were this slice's deferred half; PPS-2b shipped them by promoting the key
/// at the innermost storing `push`. Kept here as the forward pointer — the live fences live in
/// `pps2b_str_map_fences.rs`.
#[test]
fn str_keyed_map_state_is_admitted_since_pps2b() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut m: Map<str, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<str, i64> = Map::new(); m = tmp; }}\n\
         on Ping() -> i64 {{ return 0; }}\n\
         }}\n"
    );
    assert!(
        !codes(&src).contains(&"C012".to_string()),
        "PPS-2b admits string-keyed map state; got {:?}",
        codes(&src)
    );
}

/// `Vec<str>` got its per-element promotion in PPS-3: admission and routing
/// now share `is_persistable_scalar_vec`, so the element's storing push both
/// routes to a `$state` instance AND promotes the string payload. The live
/// fences (pointer-bearing record interiors) are in
/// `pps3_record_element_fences.rs`.
#[test]
fn vec_of_str_state_is_admitted_since_pps3() {
    let src = format!(
        "{HEAD}actor Store {{\n\
         state {{ mut v: Vec<str> }}\n\
         init(f: Fuel) {{ let tmp: Vec<str> = Vec::new(); v = tmp; }}\n\
         on Ping() -> i64 {{ return 0; }}\n\
         }}\n"
    );
    assert!(
        !codes(&src).contains(&"C012".to_string()),
        "PPS-3 admits `mut Vec<str>` state; got {:?}",
        codes(&src)
    );
}
