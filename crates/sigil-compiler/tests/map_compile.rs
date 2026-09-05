//! Compile-level tests for the stdlib `Map<str, V>` (PR 2 skeleton).
//!
//! CF7: the SHIPPED `stdlib/sigil/map.sigil` type-checks verbatim as its own
//! `module map;` (with `vec.sigil` auto-injected by the `Vec` triggers). Plus a
//! monomorphization check: a `module tool` that instantiates `Map<str, i64>` and
//! calls the constructors + size accessors compiles clean — exercising the
//! generic-construction inference (#150) on `new()`'s `vals: Vec::new()`.

use sigil_compiler::compile_named_module;

const MAP: &str = include_str!("../../../stdlib/sigil/map.sigil");

fn codes_of(source: &str, label: &str) -> Vec<String> {
    match compile_named_module(format!("map_{label}.sigil"), source.to_string()) {
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

/// CF7: the verbatim shipped stdlib map type-checks as its own module.
#[test]
fn map_sigil_type_checks_standalone() {
    assert_clean(MAP, "stdlib");
}

/// Inline the real map.sigil into `module tool` (strip its own `module map;`
/// line) so `Map` resolves same-module (ambient injection is PR 4); `Vec` is
/// still auto-injected by the inlined `Vec` triggers.
fn tool(body: &str) -> String {
    let defs = MAP.replace("\nmodule map;\n", "\n");
    format!("module tool;\n{defs}\n\nfn use_it() -> i64 ! {{ Alloc }} {{\n{body}\n}}\n")
}

/// Monomorphization: `Map<str, i64>` constructors + size accessors type-check.
/// This is where the #150 generic-construction fix runs — `new()` builds
/// `Map { ..., vals: Vec::new(), ... }` and `vals: Vec<V>` must concretize to
/// `Vec<i64>` from the `Map<str, i64>` return type.
#[test]
fn map_i64_instantiation_typechecks() {
    let src = tool(
        "    let m: Map<str, i64> = Map::new();\n\
         \x20   let c: Map<str, i64> = Map::with_capacity(10);\n\
         \x20   return m.len() + c.capacity();",
    );
    assert_clean(&src, "instantiate_i64");
}
