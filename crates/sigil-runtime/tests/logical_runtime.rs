use sigil_compiler::compile_tool;
use sigil_runtime::{ephemeral::ToolError, execute_ephemeral, grants::IoGrants};

fn run_negative(source: &str) -> i64 {
    let result = compile_tool(source).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message
                .find(prefix)
                .unwrap_or_else(|| panic!("unexpected runtime trap: {message}"))
                + prefix.len();
            let end = message[start..].find(')').expect("trap terminator");
            message[start..start + end].parse().expect("numeric return")
        }
        other => panic!("expected negative return trap, got {other:?}"),
    }
}

#[test]
fn and_or_skip_a_trapping_rhs() {
    let source = r#"
module tool;
fn explode() -> bool {
    let zero: i64 = 0;
    let value: i64 = 1 / zero;
    return value == 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: bool = false && explode();
    let b: bool = true || explode();
    if a || !b {
        return 0 - 1;
    }
    return 0 - 7;
}
"#;
    assert_eq!(run_negative(source), 7);
}

#[test]
fn logical_rhs_runs_when_required() {
    let source = r#"
module tool;
fn yes() -> bool { return true; }
fn no() -> bool { return false; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: bool = true && yes();
    let b: bool = false || no();
    if a && !b {
        return 0 - 9;
    }
    return 0 - 1;
}
"#;
    assert_eq!(run_negative(source), 9);
}

#[test]
fn false_match_guard_continues_to_the_next_arm() {
    let source = r#"
module tool;
const ONE: i64 = 1;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut result: i64 = 0;
    let value: i64 = 1;
    match value {
        ONE if false => { result = 3; },
        _ => { result = 11; }
    }
    return 0 - result;
}
"#;
    assert_eq!(run_negative(source), 11);
}
