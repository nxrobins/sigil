//! R014: an actor cannot be declared in an outer-ring module.
//!
//! `wasm::emit` places an outer-ring actor's init and handlers in the outer module, and every
//! actor runtime path bootstraps the inner module alone, so such an actor compiled and then failed
//! at bootstrap with a missing handler export (`missing Wasm export Main__Start`). It is now
//! refused at its declaration with exactly R014, one diagnostic per actor, each at its own actor.
//! Its inner-ring twin, the same source without `#[ring(outer)]`, compiles, and an outer-ring
//! module that declares no actor (a tool's `tool_main`, or functions beside an inner-ring actor)
//! is unaffected: the rule refuses the declaration, not the ring.

use sigil_compiler::compile_named_module;

/// Every error code `source` is rejected with, in report order; empty when it compiles.
fn codes(name: &str, source: &str) -> Vec<String> {
    match compile_named_module(name, source) {
        Ok(_) => Vec::new(),
        Err(err) => err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_owned())
            .collect(),
    }
}

/// An outer-ring actor that does nothing the outer ring forbids: it compiled before R014.
const QUIET_ACTOR: &str = "#[ring(outer)] module tool;
entry actor Main {
    on Start() -> i64 {
        return 7;
    }
}
";

#[test]
fn outer_ring_actor_is_refused_at_its_declaration() {
    assert_eq!(codes("quiet", QUIET_ACTOR), ["R014"]);
    let inner = QUIET_ACTOR.replacen("#[ring(outer)] ", "", 1);
    assert_eq!(
        codes("quiet_inner", &inner),
        Vec::<String>::new(),
        "the inner-ring twin compiles"
    );
}

/// Two actors in one outer-ring module are two diagnostics, each at its own actor's declaration.
#[test]
fn each_outer_ring_actor_is_refused_at_its_own_declaration() {
    let source = "#[ring(outer)] module tool;
entry actor Main {
    on Start() -> i64 { return 7; }
}
actor Worker {
    on Ping() {}
}
";
    let err = compile_named_module("two", source).expect_err("both actors are refused");
    let mut declarations = Vec::new();
    for diagnostic in err.diagnostics() {
        assert_eq!(diagnostic.code().as_str(), "R014");
        let span = diagnostic.span().expect("a source-anchored diagnostic");
        declarations.push(&source[span.start..span.end]);
    }
    assert_eq!(declarations.len(), 2, "one diagnostic per actor");
    assert!(declarations[0].starts_with("entry actor Main"));
    assert!(declarations[1].starts_with("actor Worker"));
}

/// The rule is the declaration's, not the ring's: an outer-ring tool and an outer-ring module of
/// functions beside an inner-ring actor both compile.
#[test]
fn outer_ring_module_without_an_actor_is_unaffected() {
    let tool = "#[ring(outer)] #[trusted] module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return input_len;
}
";
    assert_eq!(codes("tool", tool), Vec::<String>::new());
    let beside = "module app;
entry actor Main {
    on Start() -> i64 { return 7; }
}
#[ring(outer)] module ext;
pub fn helper(x: i64) -> i64 { return x + 1; }
";
    assert_eq!(codes("beside", beside), Vec::<String>::new());
}
