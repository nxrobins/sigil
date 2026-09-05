//! Runtime correctness of the flat `match` dispatch (the codegen that replaced
//! the nested-if/else cascade to stop large matches overflowing the compiler's
//! native stack). The flat lowering wraps the whole match in ONE wasm `block`
//! and each arm body `br`s out of it — so the load-bearing properties are:
//!
//!   1. the FIRST matching arm runs (and binds the right payload), and
//!   2. once an arm runs, the REMAINING arm tests are skipped (the `br`-to-exit),
//!      i.e. no later arm's body also executes.
//!
//! These COMPILE + EXECUTE the wasm and assert the actual returned value, so a
//! mis-wired `br` depth or a fall-through bug shows up as a wrong result rather
//! than passing a compile-only check. Values are returned via the
//! negative-sentinel trap convention (`return 0 - v`), mirroring
//! `array_contains.rs`; tested values are >= 1 so 0 is never ambiguous with a
//! packed-pointer return.

mod common;

/// Compile a full `module tool { … }` source whose `tool_main` ends in
/// `return 0 - v;`, execute it, and recover `v`.
fn run_neg(src: &str) -> i64 {
    common::run_module_returning_negative(src)
}

/// `tool_main` that hardcodes `a` then matches it; returns `0 - <result>`.
fn match_i64_tool(a: i64, arms: &str) -> String {
    format!(
        "module tool;\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n\
         \x20   let a: i64 = {a};\n\
         \x20   let mut r: i64 = 0;\n\
         \x20   match a {{\n{arms}\n    }}\n\
         \x20   return 0 - r;\n\
         }}\n"
    )
}

const LITERAL_ARMS: &str = "        1 => { r = 11; },\n        2 => { r = 22; },\n        3 => { r = 33; },\n        _ => { r = 99; }";

#[test]
fn literal_match_first_arm() {
    assert_eq!(run_neg(&match_i64_tool(1, LITERAL_ARMS)), 11);
}

#[test]
fn literal_match_middle_arm() {
    assert_eq!(run_neg(&match_i64_tool(2, LITERAL_ARMS)), 22);
}

#[test]
fn literal_match_last_conditional_arm() {
    assert_eq!(run_neg(&match_i64_tool(3, LITERAL_ARMS)), 33);
}

#[test]
fn literal_match_default_arm() {
    assert_eq!(run_neg(&match_i64_tool(7, LITERAL_ARMS)), 99);
}

/// The load-bearing property: once an arm matches, NO later arm body runs. If the
/// `br`-out-of-block were wrong (fall-through), `a == 1` would run arm 1 AND the
/// wildcard, leaving r = 99 instead of 11.
#[test]
fn matched_arm_skips_the_rest() {
    let arms = "        1 => { r = 11; },\n        _ => { r = 99; }";
    assert_eq!(
        run_neg(&match_i64_tool(1, arms)),
        11,
        "first arm must win and skip the wildcard"
    );
    assert_eq!(
        run_neg(&match_i64_tool(5, arms)),
        99,
        "non-match falls to the wildcard"
    );
}

#[test]
fn range_match() {
    let arms =
        "        0 ..= 9 => { r = 1; },\n        10 ..= 99 => { r = 2; },\n        _ => { r = 3; }";
    assert_eq!(run_neg(&match_i64_tool(5, arms)), 1);
    assert_eq!(run_neg(&match_i64_tool(42, arms)), 2);
    assert_eq!(run_neg(&match_i64_tool(500, arms)), 3);
    assert_eq!(
        run_neg(&match_i64_tool(9, arms)),
        1,
        "inclusive upper bound"
    );
    assert_eq!(
        run_neg(&match_i64_tool(10, arms)),
        2,
        "inclusive lower bound"
    );
}

/// A chain of sibling `match` statements — each must dispatch independently and
/// the cumulative effect must be correct (exercises the flat block-per-match
/// emission back-to-back).
#[test]
fn sibling_matches_accumulate() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let a: i64 = 2;\n\
        \x20   let mut acc: i64 = 0;\n\
        \x20   match a { 1 => { acc = acc + 1; }, _ => { acc = acc + 10; } }\n\
        \x20   match a { 2 => { acc = acc + 100; }, _ => { acc = acc + 1000; } }\n\
        \x20   match a { 3 => { acc = acc + 7; }, _ => { acc = acc + 5; } }\n\
        \x20   return 0 - acc;\n\
        }\n";
    // a=2: first match → +10 (not 1), second → +100 (matches 2), third → +5 → 115.
    assert_eq!(run_neg(src), 115);
}

/// An enum match with a payload binding — proves the matched variant's payload is
/// extracted into the arm body (not a neighbouring arm's).
#[test]
fn enum_match_binds_payload() {
    let src = "module tool;\n\
        enum E { A(i64), B(i64), C }\n\
        fn pick(e: E) -> i64 {\n\
        \x20   match e {\n\
        \x20       E::A(x) => { return x + 1; },\n\
        \x20       E::B(y) => { return y + 100; },\n\
        \x20       E::C => { return 7; }\n\
        \x20   }\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let v: E = E::B(40);\n\
        \x20   let r: i64 = pick(v);\n\
        \x20   return 0 - r;\n\
        }\n";
    assert_eq!(run_neg(src), 140, "B(40) → 40 + 100");
}

/// Nested match (a match inside another match's arm). The inner dispatch opens
/// its own enclosing block; the inner arm `br`s to the INNER exit while the outer
/// arm `br`s to the OUTER exit. A wrong `dispatch_exit` depth would `br` to the
/// wrong block and corrupt control flow.
#[test]
fn nested_match() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let a: i64 = 1;\n\
        \x20   let b: i64 = 2;\n\
        \x20   let mut r: i64 = 0;\n\
        \x20   match a {\n\
        \x20       1 => {\n\
        \x20           match b { 2 => { r = 42; }, _ => { r = 7; } }\n\
        \x20       },\n\
        \x20       _ => { r = 99; }\n\
        \x20   }\n\
        \x20   return 0 - r;\n\
        }\n";
    assert_eq!(run_neg(src), 42, "outer arm 1 → inner arm 2");
}

/// A match inside a `while` loop body, where an arm runs `break`. Here the loop's
/// break target and the match's exit target are at DIFFERENT wasm depths that
/// both shift as the emitter opens the match block and the arm `if` — the case
/// most likely to expose a `Br`-depth bug. The loop runs until the match's arm
/// breaks; the accumulated value proves the break fired at the right iteration.
#[test]
fn match_in_loop_with_break() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let mut i: i64 = 0;\n\
        \x20   let mut acc: i64 = 0;\n\
        \x20   while i < 100 {\n\
        \x20       match i {\n\
        \x20           3 => { break; },\n\
        \x20           _ => { acc = acc + i; }\n\
        \x20       }\n\
        \x20       i = i + 1;\n\
        \x20   }\n\
        \x20   return 0 - (acc + 1);\n\
        }\n";
    // i=0,1,2 add to acc (0+1+2=3); i=3 → break. acc=3, return 0-(3+1) → 4.
    assert_eq!(run_neg(src), 4);
}

/// A large match must both compile (no stack overflow) AND dispatch to the right
/// arm at runtime — proving the flat chain stays correct at scale, not just that
/// it stops crashing. Picks a deep-in-the-chain arm.
#[test]
fn large_match_dispatches_to_correct_arm() {
    let mut arms = String::new();
    for i in 0..200 {
        // arm i returns i + 1 (so 0 is never the result).
        arms.push_str(&format!("        {i} => {{ r = {}; }},\n", i + 1));
    }
    arms.push_str("        _ => { r = 99999; }");
    assert_eq!(run_neg(&match_i64_tool(0, &arms)), 1, "first arm");
    assert_eq!(run_neg(&match_i64_tool(137, &arms)), 138, "deep arm");
    assert_eq!(
        run_neg(&match_i64_tool(199, &arms)),
        200,
        "last conditional arm"
    );
    assert_eq!(run_neg(&match_i64_tool(200, &arms)), 99999, "default");
}
