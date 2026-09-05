//! break / continue — loop control across `while` and `for-in` (array + iterator).
//! `break` exits the innermost loop; `continue` skips to its next iteration (a for-in
//! `continue` still advances the cursor, so it never spins on the current element).

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Tool with NO `! { Alloc }` (while / array-for tests don't allocate).
fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

/// Tool WITH `! { Alloc }` (the `Vec::iter()` test allocates).
fn tool_alloc(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn decode(src: &str) -> i64 {
    let result = compile_tool(src).expect("tool should compile");
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

fn neg(body: &str) -> i64 {
    decode(&tool(body))
}

#[test]
fn while_break_exits_early() {
    // sum 0..4 then break at i==5.
    let body = "    let mut i: i64 = 0;\n\
        \x20   let mut sum: i64 = 0;\n\
        \x20   while i < 100 {\n\
        \x20       if i == 5 { break; } else { }\n\
        \x20       sum = sum + i;\n\
        \x20       i = i + 1;\n\
        \x20   }\n\
        \x20   return 0 - (sum + 1);";
    assert_eq!(neg(body), 11); // sum 10
}

#[test]
fn while_continue_skips_one() {
    // increment FIRST (so continue can't spin), skip adding when i==3.
    let body = "    let mut i: i64 = 0;\n\
        \x20   let mut sum: i64 = 0;\n\
        \x20   while i < 10 {\n\
        \x20       i = i + 1;\n\
        \x20       if i == 3 { continue; } else { }\n\
        \x20       sum = sum + i;\n\
        \x20   }\n\
        \x20   return 0 - sum;";
    assert_eq!(neg(body), 52); // 1+2+..+10 = 55, minus 3
}

#[test]
fn for_array_break() {
    let body = "    let mut sum: i64 = 0;\n\
        \x20   for x in [10, 20, 30, 40, 50] {\n\
        \x20       if x == 30 { break; } else { }\n\
        \x20       sum = sum + x;\n\
        \x20   }\n\
        \x20   return 0 - sum;";
    assert_eq!(neg(body), 30); // 10 + 20
}

#[test]
fn for_array_continue_advances() {
    // continue at x==3 must skip to the next element (not re-read 3 forever).
    let body = "    let mut sum: i64 = 0;\n\
        \x20   for x in [1, 2, 3, 4, 5] {\n\
        \x20       if x == 3 { continue; } else { }\n\
        \x20       sum = sum + x;\n\
        \x20   }\n\
        \x20   return 0 - sum;";
    assert_eq!(neg(body), 12); // 1 + 2 + 4 + 5
}

#[test]
fn for_vec_iter_break_and_continue() {
    // x=1 → +1; x=2 → continue; x=3 → +3; x=4 → break. sum = 4.
    let body = "    let mut v: Vec<i64> = Vec::new();\n\
        \x20   v.push(1); v.push(2); v.push(3); v.push(4); v.push(5);\n\
        \x20   let mut sum: i64 = 0;\n\
        \x20   for x in v.iter() {\n\
        \x20       if x == 4 { break; } else { }\n\
        \x20       if x == 2 { continue; } else { }\n\
        \x20       sum = sum + x;\n\
        \x20   }\n\
        \x20   return 0 - (sum + 1);";
    assert_eq!(decode(&tool_alloc(body)), 5); // sum 4
}

#[test]
fn nested_break_targets_innermost() {
    // The inner `break` exits only the inner loop; the outer continues.
    let body = "    let mut sum: i64 = 0;\n\
        \x20   let mut i: i64 = 0;\n\
        \x20   while i < 3 {\n\
        \x20       let mut j: i64 = 0;\n\
        \x20       while j < 3 {\n\
        \x20           if j == 1 { break; } else { }\n\
        \x20           sum = sum + i * 10 + j;\n\
        \x20           j = j + 1;\n\
        \x20       }\n\
        \x20       sum = sum + 100;\n\
        \x20       i = i + 1;\n\
        \x20   }\n\
        \x20   return 0 - sum;";
    // each i: inner adds i*10 (j=0 only, break at j=1), then +100. i=0,1,2.
    assert_eq!(neg(body), 330); // (0+100) + (10+100) + (20+100)
}

#[test]
fn dead_code_after_break_compiles() {
    // `break` terminates the block; the statement after it is dead (not lowered).
    let body = "    let mut sum: i64 = 0;\n\
        \x20   while sum < 100 {\n\
        \x20       break;\n\
        \x20       sum = sum + 999;\n\
        \x20   }\n\
        \x20   return 0 - (sum + 7);";
    assert_eq!(neg(body), 7); // broke immediately, sum 0
}
