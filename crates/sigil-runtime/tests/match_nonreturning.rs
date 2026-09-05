//! Regression: a `match` STATEMENT whose arms do NOT all `return` must produce valid
//! wasm and correct behavior. Every stdlib match arm currently `return`s (e.g.
//! option.sigil `map`/`and_then`), so this path was unexercised — and the wasm
//! backend's CFG structurer mis-computed the merge point (a `Some(x)` arm flows
//! arm→extract→body→exit while `None` flows arm→exit; the differing fallthroughs were
//! resolved by picking an arbitrary block), producing invalid wasm / wrong control flow.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

fn prog(body: &str) -> String {
    format!(
        "module tool;\n\
         fn opt(b: i64) -> Option<i64> {{ if b > 0 {{ return Some(b); }} else {{ return None; }} }}\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    let src = prog(body);
    let result = compile_tool(&src).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a clean negative-sentinel return, got a genuine trap: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse trap code from {message:?}: {e}"))
        }
        Err(other) => panic!("tool failed with non-trap error: {other:?}"),
        Ok(_) => panic!("tool returned a positive packed-pointer; expected negative sentinel"),
    }
}

#[test]
fn match_nonreturning_arms_some_path() {
    // Some(5) → a = 0 + 5 = 5; the None arm (a += 100) must NOT run.
    let body = "    let o: Option<i64> = opt(5);\n\
        \x20   let mut a: i64 = 0;\n\
        \x20   match o {\n\
        \x20       Some(x) => { a = a + x; },\n\
        \x20       None => { a = a + 100; }\n\
        \x20   }\n\
        \x20   return 0 - (a + 1000);";
    assert_eq!(neg(body), 1005); // a = 5
}

#[test]
fn match_nonreturning_arms_none_path() {
    // opt(0) → None → a = 0 + 100 = 100; the Some arm must NOT run.
    let body = "    let o: Option<i64> = opt(0);\n\
        \x20   let mut a: i64 = 0;\n\
        \x20   match o {\n\
        \x20       Some(x) => { a = a + x; },\n\
        \x20       None => { a = a + 100; }\n\
        \x20   }\n\
        \x20   return 0 - (a + 1000);";
    assert_eq!(neg(body), 1100); // a = 100
}

#[test]
fn match_nonreturning_arms_in_while_loop() {
    // The iterator-protocol shape: a non-returning match driving a `while` flag. Sums
    // opt(1)+opt(2)+opt(3) = 6 across exactly 3 iterations, then the None ends it.
    let body = "    let mut i: i64 = 1;\n\
        \x20   let mut sum: i64 = 0;\n\
        \x20   let mut go: bool = true;\n\
        \x20   while go {\n\
        \x20       let o: Option<i64> = opt(i);\n\
        \x20       match o {\n\
        \x20           Some(x) => { sum = sum + x; i = i + 1; if i > 3 { i = 0 - 1; } else {} },\n\
        \x20           None => { go = false; }\n\
        \x20       }\n\
        \x20   }\n\
        \x20   return 0 - (sum + 1000);";
    // i=1→sum1, i=2→sum3, i=3→sum6, then i set to -1 → opt(-1)=None → stop. sum=6.
    assert_eq!(neg(body), 1006);
}
