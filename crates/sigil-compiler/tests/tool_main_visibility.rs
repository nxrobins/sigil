//! WHY THIS TEST EXISTS. Export hygiene exports only externally callable
//! functions, and a free function is externally callable only when it is
//! `pub`. Before this diagnostic a private `tool_main` compiled cleanly into
//! a module with no entry point, and the failure surfaced at first use as the
//! runtime's `no tool_main entry point found`. T283 names the fix at the
//! declaration; the census in `duplicate_name_census.rs` style below keeps it
//! from silently regressing to that fail-open shape.

use sigil_compiler::compile_named_module;

fn codes(source: &str) -> Vec<String> {
    match compile_named_module("tool_main_visibility.sigil", source) {
        Ok(_) => Vec::new(),
        Err(err) => err
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str().to_owned())
            .collect(),
    }
}

#[test]
fn a_private_tool_main_is_refused_with_t283_at_its_declaration() {
    let source = "module t;\nfn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n";
    assert_eq!(codes(source), vec!["T283".to_owned()]);
    let err = compile_named_module("tool_main_visibility.sigil", source)
        .expect_err("a private entry point is refused");
    let diagnostic = &err.diagnostics()[0];
    let span = diagnostic
        .span()
        .expect("the refusal points at the declaration");
    assert_eq!(&source[span.start..span.start + 2], "fn");
    assert!(
        diagnostic.message().contains("not `pub`"),
        "the message names the fix: {}",
        diagnostic.message()
    );
}

#[test]
fn a_pub_tool_main_and_other_private_functions_are_untouched() {
    assert_eq!(
        codes(
            "module t;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\nfn helper() -> i64 { return 1; }\n"
        ),
        Vec::<String>::new()
    );
    // The rule is about the entry point only: a private function with another
    // name is an ordinary internal function.
    assert_eq!(
        codes("module t;\nfn main_tool(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n"),
        Vec::<String>::new()
    );
}
