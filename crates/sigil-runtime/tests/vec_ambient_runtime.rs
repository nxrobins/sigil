//! Ambient-injection runtime test for `Vec<T>` (PR C3).
//!
//! A BARE-`Vec` tool — no inlined record/impl, no `module vec;` — must
//! auto-inject `stdlib/sigil/vec.sigil` (exactly like `Option`/`Result`) and
//! run end to end via C2's cross-module dispatch.

mod common;

use common::run_returning_negative;

#[test]
fn bare_vec_auto_injects_and_runs() {
    // No `module vec;`, no inlined record/impl — just bare `Vec`. The `Vec::`
    // and `Vec<` triggers pull `stdlib/sigil/vec.sigil` into the source set,
    // and C2 resolves the members cross-module. CF-C6: the result must equal
    // the same-module / cross-module value (320).
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let v: Vec<i64> = Vec::new();\n\
        \x20   let a: i64 = v.push(10);\n\
        \x20   let b: i64 = v.push(20);\n\
        \x20   let c: i64 = v.push(30);\n\
        \x20   return 0 - (v.get(1) + v.len() * 100);\n\
        }\n";
    assert_eq!(run_returning_negative(src), 320);
}

#[test]
fn bare_vec_growth_auto_injects() {
    // Growth across reallocs, bare-`Vec`. CF-C6: matches same-module (129).
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let v: Vec<i64> = Vec::with_capacity(2);\n\
        \x20   let mut i: i64 = 0;\n\
        \x20   while i < 9 {\n\
        \x20       let n: i64 = v.push(i * 10);\n\
        \x20       i = i + 1;\n\
        \x20   }\n\
        \x20   return 0 - (v.get(0) + v.get(4) + v.get(8) + v.len());\n\
        }\n";
    assert_eq!(run_returning_negative(src), 129);
}
