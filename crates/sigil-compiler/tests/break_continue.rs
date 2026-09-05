//! break / continue compile-level gates: T260 (outside a loop), and that an
//! in-loop break/continue type-checks cleanly.

use sigil_compiler::compile_tool;

use sigil_test_utils::pipeline::compile_tool_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

#[test]
fn break_outside_loop_is_t260() {
    let src = tool("    break;\n    return 0;");
    assert!(
        has(&src, "T260"),
        "break outside a loop must be T260: {:?}",
        codes_of(&src)
    );
}

#[test]
fn continue_outside_loop_is_t260() {
    let src = tool("    continue;\n    return 0;");
    assert!(
        has(&src, "T260"),
        "continue outside a loop must be T260: {:?}",
        codes_of(&src)
    );
}

#[test]
fn break_in_if_outside_loop_is_t260() {
    // An `if` is not a loop — a `break` in its arm is still outside any loop.
    let src = tool("    if input_len > 0 { break; } else { }\n    return 0;");
    assert!(
        has(&src, "T260"),
        "break in a non-loop if must be T260: {:?}",
        codes_of(&src)
    );
}

#[test]
fn break_and_continue_in_while_compile() {
    let src = tool(
        "    let mut i: i64 = 0;\n\
         \x20   while i < 10 {\n\
         \x20       i = i + 1;\n\
         \x20       if i == 2 { continue; } else { }\n\
         \x20       if i == 5 { break; } else { }\n\
         \x20   }\n\
         \x20   return 0 - i;",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "break/continue inside a while must compile: {:?}",
        codes_of(&src)
    );
}

#[test]
fn break_in_for_array_compiles() {
    let src = tool(
        "    let mut s: i64 = 0;\n\
         \x20   for x in [1, 2, 3] {\n\
         \x20       if x == 2 { break; } else { }\n\
         \x20       s = s + x;\n\
         \x20   }\n\
         \x20   return 0 - s;",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "break inside a for-in must compile: {:?}",
        codes_of(&src)
    );
}
