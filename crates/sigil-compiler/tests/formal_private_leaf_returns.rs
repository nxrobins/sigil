//! WHY THIS TEST EXISTS. Early returns in a genuinely private leaf computation
//! are not whole-machine halts. The exception must not admit a private return
//! that skips Public local writes, state changes, calls or boundary events.
//! Source witnesses complement the linked-byte mutants in formal's unit tests.

use sigil_compiler::{Compilation, compile_named_module};

fn compile(source: &str) -> Compilation {
    compile_named_module("private_leaf.sigil", source).unwrap_or_else(|error| {
        let diagnostics = error
            .diagnostics()
            .iter()
            .map(|diagnostic| (diagnostic.code(), diagnostic.message(), diagnostic.span()))
            .collect::<Vec<_>>();
        panic!("private leaf must compile through every retained gate: {diagnostics:?}");
    })
}

#[test]
fn private_leaf_whitespace_scan_retains_ordinary_early_returns() {
    let source = r#"
module private_leaf;
fn skip_ws(input_ptr: i64 @Flow, i_in: i64 @Flow, end: i64 @Flow) -> i64 @Flow {
    let mut i: i64 = i_in;
    while i < end {
        let b: i64 = load8(input_ptr + i);
        match b {
            32 => { i += 1; },
            9 => { i += 1; },
            10 => { i += 1; },
            13 => { i += 1; },
            _ => { return i; },
        }
    }
    return i;
}
"#;
    let compilation = compile(source);
    assert_eq!(compilation.formal_security_report.model_version, 9);
}

#[test]
fn json_library_retains_its_committed_acceptance() {
    compile(include_str!("../../../stdlib/sigil/json.sigil"));
}
