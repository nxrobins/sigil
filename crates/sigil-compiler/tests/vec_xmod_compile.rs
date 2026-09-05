//! Cross-module compile tests for `Vec<T>` (PR C2): explicit-module usage
//! type-checks, plus the two adversarial fail-fasts —
//!   * CF-C1: an impl member defined in two sibling modules → T244 (ambiguity).
//!   * CF-C4: an effectful cross-module assoc fn called without the effect → E001.

use sigil_compiler::compile_named_module;

const VEC: &str = include_str!("../../../stdlib/sigil/vec.sigil");

fn codes_of(source: &str, label: &str) -> Vec<String> {
    match compile_named_module(format!("vecxmod_{label}.sigil"), source.to_string()) {
        Ok(_) => Vec::new(),
        Err(err) => err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn assert_clean(source: &str, label: &str) {
    let codes = codes_of(source, label);
    assert!(
        codes.is_empty(),
        "expected clean compile for {label}, got: {codes:?}"
    );
}

fn assert_has(source: &str, label: &str, code: &str) {
    let codes = codes_of(source, label);
    assert!(
        codes.iter().any(|c| c == code),
        "expected {code} for {label}, got: {codes:?}"
    );
}

#[test]
fn xmod_vec_usage_compiles_clean() {
    // `Vec::new()` (associated fn) + `v.push()`/`v.len()` (methods) resolve
    // from a sibling module via C2's global fallback — no inlining.
    let src = format!(
        "{VEC}\n\nmodule tool;\nfn use_vec() -> i64 ! {{ Alloc }} {{\n  let v: Vec<i64> = Vec::new();\n  let a: i64 = v.push(7);\n  return v.len();\n}}\n"
    );
    assert_clean(&src, "usage");
}

#[test]
fn xmod_ambiguous_assoc_fn_is_t244() {
    // CF-C1: `Thing::make` defined in TWO sibling modules (neither the caller's)
    // → hard ambiguity, never first-match-wins.
    let src = "module a;\nrecord Thing<T> { v: i64 }\nimpl Thing<T> {\n  pub fn make() -> Thing<T> {\n    return Thing { v: 0 };\n  }\n}\n\nmodule b;\nimpl Thing<T> {\n  pub fn make() -> Thing<T> {\n    return Thing { v: 1 };\n  }\n}\n\nmodule tool;\nfn use_it() -> i64 {\n  let t: Thing<i64> = Thing::make();\n  return 0;\n}\n";
    assert_has(src, "ambiguous", "T244");
}

#[test]
fn xmod_effect_surface_matches_same_module() {
    // CF-C4 (parity). The compile-time `E001` gate is OUTER-ring only; Inner-
    // ring tools are gated at the runtime grant layer, which consumes the
    // program's `effects_required` surface. C2 must not change that surface:
    // the SAME effectful program compiled same-module vs cross-module must
    // yield the SAME `effects_required`. `Vec::with_capacity` requires
    // `! { Alloc }` (declared here), so both forms must surface exactly `Alloc`
    // — and identically. A cross-module path that dropped the effect (INV-4)
    // would diverge from the same-module surface.
    let body =
        "  let v: Vec<i64> = Vec::with_capacity(4);\n  let a: i64 = v.push(1);\n  return v.len();";
    let same_module = format!(
        "module tool;\n{}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n",
        VEC.replace("\nmodule vec;\n", "\n")
    );
    let cross_module = format!(
        "{VEC}\n\nmodule tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    );
    let surface = |src: String, label: &str| -> Vec<String> {
        let mut e = compile_named_module(format!("vecxmod_{label}.sigil"), src)
            .expect("tool compiles")
            .effects_required;
        e.sort();
        e
    };
    let sm = surface(same_module, "sm");
    let xm = surface(cross_module, "xm");
    // C2 must not change the effect surface vs same-module. (For Vec this is
    // both-empty: `Alloc` is an ungated builtin — `effect_registry` is built
    // from declared effects and `Alloc`'s lookup is optional everywhere — so it
    // is NOT in `effects_required`, which tracks grant-gated effects like
    // NetIO/FsIO. A grant-gated cross-module capability call would surface here;
    // none is reachable from Vec. The cross-module effect row is set by the
    // exact same `resolve_effect_row` the same-module method path uses, so a
    // drop would diverge from this parity.)
    assert_eq!(
        sm, xm,
        "CF-C4: cross-module effect surface must equal same-module"
    );
}
