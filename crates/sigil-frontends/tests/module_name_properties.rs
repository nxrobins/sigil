use proptest::prelude::*;

use sigil_compiler::compile_named_module;
use sigil_frontends::{EmittedSigil, frontend_for, is_legal_identifier, is_sigil_keyword};

const TYPESCRIPT_SOURCE: &str = "function f(a: number): number { return a; }";
const RUST_SOURCE: &str = "fn f(a: i64) -> i64 { a }";
const SOLIDITY_SOURCE: &str = "pragma solidity ^0.8.0; contract C { function f(uint256 a) public pure returns (uint256) { return a; } }";

fn translate(frontend: &str, source: &str, source_name: &str) -> EmittedSigil {
    frontend_for(frontend)
        .unwrap_or_else(|| panic!("frontend `{frontend}` must be registered"))
        .translate(source, source_name)
        .unwrap_or_else(|diags| {
            panic!("frontend `{frontend}` rejected source name `{source_name}`: {diags:?}")
        })
}

fn assert_compiler_valid_module(emitted: EmittedSigil) {
    let module = emitted
        .source_name
        .strip_suffix(".sigil")
        .expect("frontends must emit a .sigil source name");
    assert!(
        is_legal_identifier(module),
        "emitted module name must be a legal identifier: {module:?}"
    );
    assert!(
        module
            .as_bytes()
            .first()
            .is_some_and(|b| b.is_ascii_lowercase() || *b == b'_'),
        "emitted module name must start with lowercase ASCII or underscore: {module:?}"
    );
    assert!(
        module
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_'),
        "emitted module name must use the compiler's lowercase charset: {module:?}"
    );
    assert!(
        !is_sigil_keyword(module),
        "module name is reserved: {module:?}"
    );
    assert!(
        !module.starts_with(sigil_frontends::limits::SYNTH_PREFIX),
        "module name uses the frontend-reserved prefix: {module:?}"
    );
    compile_named_module(emitted.source_name, emitted.text)
        .expect("a frontend-emitted module must pass the trusted compiler");
}

fn assert_all_frontends_accept_source_name(source_name: &str) {
    for (frontend, source) in [
        ("typescript", TYPESCRIPT_SOURCE),
        ("rust", RUST_SOURCE),
        ("solidity", SOLIDITY_SOURCE),
    ] {
        assert_compiler_valid_module(translate(frontend, source, source_name));
    }
}

#[test]
fn adversarial_source_names_produce_compiler_valid_modules() {
    let overlong = format!(
        "{}.src",
        "a".repeat(sigil_frontends::limits::MAX_IDENT_BYTES + 1)
    );
    for source_name in [
        "module.src",
        "Type.src",
        "__fe_hidden.src",
        "9lives.src",
        "a-b.src",
        "...",
        // A source stem that collides with a stdlib method-receiver LOCAL:
        // `u256.sigil` binds `let bi: i64 = ...; bi.as_u64()`, so an emitted
        // `module bi;` that uses u256 (the Solidity `uint256` path) used to
        // make that call ambiguous (local `bi` vs the user module `bi`) and
        // fire T156 in the co-compiled stdlib. Pins the exact CI-surfaced
        // failure (proptest shrank a random hit to `"bi"`). See the
        // local-shadows-module resolution fix in `expressions/methods.rs`.
        "bi.src",
        &overlong,
    ] {
        assert_all_frontends_accept_source_name(source_name);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn arbitrary_source_names_produce_compiler_valid_modules(
        source_name in "[A-Za-z0-9_./\\\\-]{0,96}"
    ) {
        assert_all_frontends_accept_source_name(&source_name);
    }
}
