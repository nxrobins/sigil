//! `const NAME: T = LIT;` as a usable VALUE. A const reference inlines its
//! declared literal (SIGIL `const` was previously declaration-only — a reference
//! was `undefined local`/T060, and no stdlib used it). This is the enabler for
//! named token tags / node-kinds in the self-hosted compiler; the lexer
//! (`selfhost/lexer.sigil`) dogfoods it.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

fn codes_of(src: &str) -> Vec<String> {
    match compile_tool(src) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

/// Negative-sentinel decode of a whole-module source.
fn neg(body: &str) -> i64 {
    let src = format!("module tool;\n{body}\n");
    let compiled = compile_tool(&src).expect("tool should compile");
    match execute_ephemeral(&compiled.wasm, b"", compiled.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            let s = message.find(p).expect("negative sentinel") + p.len();
            let e = message[s..].find(')').expect("malformed trap");
            message[s..s + e].parse::<i64>().expect("parse sentinel")
        }
        other => panic!("expected a negative sentinel, got {other:?}"),
    }
}

#[test]
fn const_resolves_to_its_value() {
    let body = "const ANSWER: i64 = 42;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   return 0 - ANSWER;\n}";
    assert_eq!(neg(body), 42);
}

#[test]
fn const_composes_in_expressions() {
    let body = "const BASE: i64 = 100;\n\
        const STEP: i64 = 7;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let x: i64 = BASE + STEP;\n\
        \x20   return 0 - x;\n}";
    assert_eq!(neg(body), 107);
}

#[test]
fn const_usable_in_a_helper_fn() {
    // The token-tag pattern: a helper returns a named const tag.
    let body = "const LPAREN: i64 = 10;\n\
        fn tag() -> i64 { return LPAREN; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   return 0 - tag();\n}";
    assert_eq!(neg(body), 10);
}

#[test]
fn undefined_name_is_still_t060() {
    // The const fallback must not swallow a genuinely undefined name.
    let src = "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0 - NOPE; }\n";
    assert!(
        codes_of(src).iter().any(|c| c == "T060"),
        "an undefined name must still be T060: {:?}",
        codes_of(src)
    );
}
