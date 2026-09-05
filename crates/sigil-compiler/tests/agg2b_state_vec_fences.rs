//! AGG2b-3 compile-time fences for the newly-un-fenced `mut Vec<scalar>` actor-state field.
//! The un-fence (C012 relax) must NOT open a taint launder, and the scope stays `Vec<scalar>` only
//! (Map / Vec<aggregate> / str / 256-bit remain C012). The persistence behaviour is proved
//! end-to-end in `sigil-runtime/tests/agg2b_state_vec_persists.rs`.
use sigil_compiler::compile_module;

fn codes(src: &str) -> Vec<String> {
    match compile_module(src) {
        Ok(_) => vec!["OK_CLEAN".to_string()],
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn is_clean(src: &str) -> bool {
    compile_module(src).is_ok()
}

const HEAD: &str = "module sigil;\ncap type Fuel {}\n\
entry actor Main { state { fuel: Fuel } on Start() -> i64 { let w = spawn::<Acc>(fuel); return 0; } }\n";

/// The un-fence itself: a `mut Vec<i64>` state field pushed in a handler now COMPILES (its grow
/// routes to the persistent heap). Before AGG2b-3 this was C012-rejected at the declaration.
#[test]
fn mut_scalar_vec_state_field_is_permitted() {
    let src = format!(
        "{HEAD}actor Acc {{\n\
         state {{ mut v: Vec<i64> }}\n\
         init(f: Fuel) {{ let tmp: Vec<i64> = Vec::new(); v = tmp; }}\n\
         on Push(x: i64) {{ let n: i64 = v.push(x); }}\n\
         on Get() -> i64 {{ return v.get(0); }}\n\
         }}\n"
    );
    assert!(
        is_clean(&src),
        "a mut Vec<scalar> state field must now compile; got {:?}",
        codes(&src)
    );
}

/// The un-fence must NOT open a taint launder: pushing a `@Secret` element into a state `Vec` and
/// reading it back into a `@Public` position is rejected by the existing T001 sink.
#[test]
fn pushing_secret_into_state_vec_then_reading_back_is_a_taint_launder() {
    let src = format!(
        "{HEAD}actor Acc {{\n\
         state {{ mut v: Vec<i64> }}\n\
         init(f: Fuel) {{ let tmp: Vec<i64> = Vec::new(); v = tmp; }}\n\
         on Set(s: i64 @Secret) {{ let n: i64 = v.push(s); }}\n\
         on Leak() -> i64 {{ return v.get(0); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T001".to_string()),
        "pushing @Secret into a state Vec + reading it back must be a T001 launder; got {:?}",
        codes(&src)
    );
}

/// AGG-2b scoped itself to `Vec<scalar>` and pinned `mut Map<i64, i64>` as still-fenced. PPS-0
/// (the persistent-pointer-state epic's first slice) un-fenced exactly that shape — a `Map`'s five
/// interior `Vec`s are stdlib-allocated, so transitive monomorph coloring reaches every one of
/// them without needing the promotion primitive. The fence MOVED here; the assertion moves with
/// it, and `pps0_map_fences.rs` owns the new boundary (aggregate keys/values still C012).
#[test]
fn mut_scalar_map_state_field_is_now_permitted() {
    let src = format!(
        "{HEAD}actor Acc {{\n\
         state {{ mut m: Map<i64, i64> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, i64> = Map::new(); m = tmp; }}\n\
         on Ping() -> i64 {{ return 0; }}\n\
         }}\n"
    );
    assert!(
        !codes(&src).contains(&"C012".to_string()),
        "PPS-0 admits `mut Map<scalar, scalar>` state; got {:?}",
        codes(&src)
    );
}

/// …the scope kept narrowing forward: PPS-2b admitted `Map<str, _>` (keys promote at the
/// storing `push`), and PPS-3 admitted FLAT record keys/values/elements (the push copies the
/// registry-listed fields). This assertion tracks the current line — a map whose record value
/// has a POINTER-BEARING interior, which still needs the transitive walk; the full PPS-3 fence
/// matrix lives in `pps3_record_element_fences.rs`.
#[test]
fn mut_pointer_bearing_record_valued_map_state_field_stays_c012_fenced() {
    let src = format!(
        "{HEAD}record V {{ a: i64, tag: str }}\n\
         actor Acc {{\n\
         state {{ mut m: Map<i64, V> }}\n\
         init(f: Fuel) {{ let tmp: Map<i64, V> = Map::new(); m = tmp; }}\n\
         on Ping() -> i64 {{ return 0; }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"C012".to_string()),
        "a `mut Map<i64, V>` with a str-bearing record value must stay C012-fenced; got {:?}",
        codes(&src)
    );
}
