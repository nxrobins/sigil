//! Lambda-lifted closures and monomorphized functions must be filed under the
//! module that DEFINED them, not under `modules.first()`.
//!
//! `type_check::mod`'s drain used to push every lifted function into
//! `modules.first_mut()`. Because `check_effects` skips `Ring::Inner` modules and
//! passes `module.trusted` as the E002 authority, that made the ring and
//! trustedness a closure was checked under depend on whichever module happened to
//! sort first — an inner-ring module anywhere in the project exempted EVERY lifted
//! closure in the program from effect checking. The same misfiling also emitted a
//! closure from a module whose type section never registered its signature,
//! panicking in `wasm.rs` with
//! `ICE: call_indirect signature not found in type map`.
//!
//! Both symptoms share one root cause and one fix (route by the module-qualified
//! name), so both are pinned here.

use sigil_compiler::{CompileOptions, compile_project, source::SourceFile};

fn sf(name: &str, text: &str) -> SourceFile {
    SourceFile::new(name, text)
}

fn codes(sources: Vec<SourceFile>) -> Vec<String> {
    match compile_project(sources, None, CompileOptions::default()) {
        Ok(_) => vec![],
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

/// An OUTER-ring module whose closure body calls an effectful `logs()` while the
/// enclosing function declares no effect row — an E001 leak inside a closure.
fn leaky_app() -> SourceFile {
    sf(
        "app.sigil",
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         pub fn logs() -> i64 ! { Log } { return 0; }\n\
         pub fn leak() -> i64 { let f = fn(x: i64) -> i64 { return logs(); }; return f(1); }\n\
         entry actor Main {\n\
           on Tick() -> i64 { return leak(); }\n\
         }\n",
    )
}

/// Baseline: with the offending module first, the leak is flagged.
#[test]
fn closure_effect_leak_is_flagged_when_definer_sorts_first() {
    let got = codes(vec![leaky_app()]);
    assert!(
        got.contains(&"E001".to_string()),
        "a closure body performing an undeclared effect must be E001; got {got:?}"
    );
}

/// REGRESSION: an unrelated `#[ring(inner)]` module sorting FIRST must not exempt
/// a closure defined in an outer-ring module from effect checking.
///
/// Before the routing fix this returned no E001 at all — the lifted closure was
/// filed under the inner-ring module and skipped wholesale.
#[test]
fn inner_ring_module_does_not_exempt_closures_defined_elsewhere() {
    let inner = sf(
        "aaa_inner.sigil",
        "#[ring(inner)]\nmodule aaa_inner;\npub fn noop() -> i64 { return 0; }\n",
    );
    let got = codes(vec![inner, leaky_app()]);
    assert!(
        got.contains(&"E001".to_string()),
        "an inner-ring module elsewhere in the project must not exempt a closure \
         defined in an outer-ring module from effect checking; got {got:?}"
    );
}

/// REGRESSION (codegen): the same misfiling emitted a closure from a module whose
/// type section lacked its signature, panicking in `wasm.rs`. A well-formed
/// multi-module project with a closure must compile without an ICE.
#[test]
fn closure_in_multi_module_project_emits_without_ice() {
    let inner = sf(
        "aaa_inner.sigil",
        "#[ring(inner)]\nmodule aaa_inner;\npub fn noop() -> i64 { return 0; }\n",
    );
    let app = sf(
        "app.sigil",
        "#[ring(outer)]\nmodule app;\n\
         pub fn apply() -> i64 { let f = fn(x: i64) -> i64 { return x + 1; }; return f(41); }\n\
         entry actor Main {\n\
           on Tick() -> i64 { return apply(); }\n\
         }\n",
    );
    let result = compile_project(vec![inner, app], None, CompileOptions::default());
    let compilation = result.expect("multi-module project with a closure must compile");
    assert!(
        !compilation.wasm_inner.is_empty(),
        "closure-bearing multi-module project must emit non-empty wasm"
    );
}
