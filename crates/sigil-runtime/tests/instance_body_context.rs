//! SR-035: a function body is checked in a context of its own, and a range loop's bounds fact
//! reaches only its own variable. A generic function's body is checked once, by the call that
//! first creates its instance (cache-before-check), and that check ran inside the caller's body
//! with the caller's per-position context still set: the range-loop bounds facts, the refinement
//! frames, the loop depth and the immediate-borrow flag. Each applied by name inside a different
//! function, and every later call used the body that check produced. `check_function_block` now
//! empties all four for every function body and restores them after; closure and handle-clause
//! bodies, which already emptied the bounds facts, now start at loop depth 0 too, and the
//! immediate-borrow flag now marks only a borrow's direct child. Within one body, the pre-scan that
//! refuses a range loop's fact when the loop body rebinds its variable looked into no expression,
//! so a `let i` in a `region` or `handle` body kept the fact, and a closure parameter `i` kept the
//! loop's refinement frame; it now walks the whole subtree. Each test pins the broken form beside
//! its twin; before the fix the twin was right and the broken form was not. The last test pins an
//! open gap of the same kind within one function body, written to fail when it closes
//! (`tests/attack/KNOWN_GAPS.md`).

mod common;

use common::{run_returning_negative, tool_traps};
use sigil_test_utils::pipeline::compile_tool_codes as codes_of;

const MAIN: &str = "pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n";

/// `pre` and `post` sit beside `a` in memory, so a read past `a` that is not checked returns the
/// bits of one of their elements.
const ARRAYS: &str = "    let pre: [i64; 4] = [111, 222, 333, 444];\n    let a: [i64; 4] = [1, 2, 3, 4];\n    let post: [i64; 4] = [555, 666, 777, 888];\n";

/// A generic free function that reads `a[i]` with its own parameter `i`.
const GET: &str = "fn get<T>(a: [i64; 4], i: i64, t: T) -> i64 {\n    return a[i];\n}\n";

/// The loop that first creates an instance whose body's own parameter is also called `i`.
fn in_loop(call: &str) -> String {
    format!("    let mut s: i64 = 0;\n    for i in 0..4 {{\n        s = s + {call};\n    }}\n")
}

/// A program that runs `first`, then reads through `call` (which names `k`) at index `k`.
fn read_program(items: &str, first: &str, call: &str, k: &str) -> String {
    format!(
        "module tool;\n{items}{MAIN}{ARRAYS}{first}    let k: i64 = {k};\n    return 0 - ({call} + 1000);\n}}\n"
    )
}

/// A generic body that reads `a[i]` or writes `b[i]` with its own parameter `i`, first created
/// inside `for i in 0..4`, had the loop's fact `i in [0, 4)` match the name and elide its bounds
/// check, and every later call ran the elided body: `get(a, 6, 1)` returned 3337189589992, read
/// from beyond the array, and `put_at(5, 1)` wrote beyond its array. That held at every site that
/// creates an instance: a generic free function, a generic impl method, an associated function,
/// an instance created inside another instance's loop, and one created inside a generic method's
/// argument. Created first by a call outside the loop, with the loop after it, each trapped. Now
/// each out-of-bounds index traps in every form, and an in-bounds index reads and writes back.
#[test]
fn bounds_check_holds_in_an_instance_first_created_in_a_range_loop() {
    let bx_at = "record Bx<T> { v: T }\nimpl Bx<T> {\n    pub fn at(self: Bx<T>, a: [i64; 4], i: i64) -> i64 { return a[i]; }\n}\n";
    let bx_at2 = "record Bx<T> { v: T }\nimpl Bx<T> {\n    pub fn at2(a: [i64; 4], i: i64, t: T) -> i64 { return a[i]; }\n}\n";
    let outer = format!(
        "{GET}fn outer<T>(a: [i64; 4], t: T) -> i64 {{\n    let mut s: i64 = 0;\n    for i in 0..4 {{\n        s = s + get(a, i, t);\n    }}\n    return s;\n}}\n"
    );
    let reads: [(&str, String, String, &str); 6] = [
        (
            "free function, loop first",
            GET.to_string(),
            in_loop("get(a, i, 1)"),
            "get(a, k, 1)",
        ),
        (
            "free function, outside first",
            GET.to_string(),
            format!("    let r = get(a, 0, 1);\n{}", in_loop("get(a, i, 1)")),
            "get(a, k, 1)",
        ),
        (
            "generic method",
            bx_at.to_string(),
            format!(
                "    let b: Bx<i64> = Bx {{ v: 1 }};\n{}",
                in_loop("b.at(a, i)")
            ),
            "b.at(a, k)",
        ),
        (
            "associated function",
            bx_at2.to_string(),
            in_loop("Bx::at2(a, i, 1)"),
            "Bx::at2(a, k, 1)",
        ),
        (
            "created in another instance's loop",
            outer,
            "    let z = outer(a, 1);\n".to_string(),
            "get(a, k, 1)",
        ),
        (
            "created in a method argument in a loop",
            GET.to_string(),
            "    let mut v: Vec<i64> = Vec::new();\n    for i in 0..4 {\n        let n = v.push(get(a, i, 1));\n    }\n"
                .to_string(),
            "get(a, k, 1)",
        ),
    ];
    for (shape, items, first, call) in &reads {
        for k in ["4", "6", "0 - 1"] {
            assert!(
                tool_traps(&read_program(items, first, call, k)),
                "read, {shape}, k = {k}"
            );
        }
        assert_eq!(
            run_returning_negative(&read_program(items, first, call, "2")),
            1003,
            "read, {shape}"
        );
    }
    let write = |first: &str, k: &str| {
        format!(
            "module tool;\nfn put_at<T>(i: i64, t: T) -> i64 {{\n    let mut b: [i64; 4] = [10, 20, 30, 40];\n    b[i] = 77;\n    return b[0] + b[1] + b[2] + b[3];\n}}\n{MAIN}{first}    let k: i64 = {k};\n    return 0 - (put_at(k, 1) + 1000);\n}}\n"
        )
    };
    for (shape, first) in [
        ("loop first", in_loop("put_at(i, 1)")),
        (
            "outside first",
            format!("    let r = put_at(0, 1);\n{}", in_loop("put_at(i, 1)")),
        ),
    ] {
        for k in ["4", "5", "0 - 1"] {
            assert!(tool_traps(&write(&first, k)), "write, {shape}, k = {k}");
        }
        assert_eq!(
            run_returning_negative(&write(&first, "2")),
            1147,
            "write, {shape}"
        );
    }
}

/// Within one function: `for i in 0..4` keeps its fact only while nothing in its body rebinds
/// `i`, and the pre-scan that checks this looked into no expression. A `region` or bare `handle`
/// body is an expression inline in the same function, so a `let i` in one kept the loop's fact,
/// and `a[i]` on that inner `i` was not checked: a read past `a` returned 3337189589992, and a
/// write past `b` changed the next array, `c`, whose sum came back 330712481982 instead of 260.
/// Each now traps, as the same body does with no loop around it; `a[i]` on the loop variable
/// itself keeps its elision and reads back.
#[test]
fn bounds_check_holds_for_a_binding_that_shadows_the_loop_variable() {
    let program = |body: &str| format!("module tool;\neffect Mark;\n{MAIN}{ARRAYS}{body}}}\n");
    let looped = |inner: &str| {
        program(&format!(
            "    let mut s: i64 = 0;\n    for i in 0..4 {{\n{inner}    }}\n    return 0 - (s + 1000);\n"
        ))
    };
    for (shape, src) in [
        (
            "handle expression, read",
            looped(
                "        let v: i64 = handle Mark {\n            let i: i64 = 6;\n            a[i];\n        };\n        s = v;\n",
            ),
        ),
        (
            "handle statement, read",
            looped(
                "        handle Mark {\n            let i: i64 = 6;\n            let v: i64 = a[i];\n        };\n",
            ),
        ),
        (
            "region, read",
            looped(
                "        region buf(256) {\n            let i: i64 = 6;\n            let v: i64 = a[i];\n        };\n",
            ),
        ),
        (
            "region, write",
            looped(
                "        region buf(256) {\n            let mut b: [i64; 4] = [10, 20, 30, 40];\n            let i: i64 = 5;\n            b[i] = 77;\n        };\n",
            ),
        ),
        (
            "handle expression, write",
            looped(
                "        let v: i64 = handle Mark {\n            let mut b: [i64; 4] = [10, 20, 30, 40];\n            let c: [i64; 4] = [50, 60, 70, 80];\n            let i: i64 = 6;\n            b[i] = 77;\n            c[0] + c[1] + c[2] + c[3];\n        };\n        s = v;\n",
            ),
        ),
        (
            "handle expression, read, no loop",
            program(
                "    let v: i64 = handle Mark {\n        let i: i64 = 6;\n        a[i];\n    };\n    return 0 - (v + 1000);\n",
            ),
        ),
    ] {
        assert!(tool_traps(&src), "{shape}");
    }
    let own_variable = looped(
        "        let v: i64 = handle Mark {\n            a[i];\n        };\n        s = v;\n",
    );
    assert_eq!(run_returning_negative(&own_variable), 1004);
}

/// The same pre-scan gates the refinement frame the loop pushes, `i >= 0, i < 4`, which a closure
/// does not empty: a closure parameter `i` and a `let i` in a `handle` body each kept it, so
/// `idx(i)` with `where x < 4` was discharged for an `i` of 9, and `idx` ran with 9. Each is now
/// T211, as the same body is with no loop around it; `idx(i)` on the loop variable itself is still
/// discharged, and runs.
#[test]
fn range_loop_frame_does_not_reach_a_binding_that_shadows_its_variable() {
    let program = |body: &str| {
        format!(
            "module tool;\neffect Mark;\nfn idx(x: i64) where x < 4 -> i64 {{\n    return x;\n}}\n{MAIN}{body}}}\n"
        )
    };
    for (shape, body) in [
        (
            "closure parameter",
            "    let mut s: i64 = 0;\n    for i in 0..4 {\n        let f = fn(i: i64) -> i64 { return idx(i); };\n        s = s + f(9);\n    }\n    return 0 - s;\n",
        ),
        (
            "let in a handle body",
            "    let mut s: i64 = 0;\n    for i in 0..4 {\n        let v: i64 = handle Mark {\n            let i: i64 = 9;\n            idx(i);\n        };\n        s = v;\n    }\n    return 0 - s;\n",
        ),
        (
            "let in a handle body, no loop",
            "    let v: i64 = handle Mark {\n        let i: i64 = 9;\n        idx(i);\n    };\n    return 0 - v;\n",
        ),
    ] {
        assert_eq!(codes_of(&program(body)), ["T211"], "{shape}");
    }
    let own_variable = program(
        "    let mut s: i64 = 0;\n    for i in 0..4 {\n        s = s + idx(i);\n    }\n    return 0 - s;\n",
    );
    assert_eq!(run_returning_negative(&own_variable), 6);
}

/// `validate` requires `x > 0`, and `wrap<T>` passes it its own parameter `x`, which carries no
/// refinement: the call is T211 in `wrap`'s body. Created first inside the caller's `if x > 0`,
/// the caller's narrowing frame, which names `x` too, was still on the stack and discharged the
/// call, and `wrap(0 - 7, 1)` then ran `validate` with -7 (the program returned 98). Now the body
/// sees only its own frames: T211 in both orders. The caller's own `validate(x)` inside its own
/// `if x > 0` still discharges, and runs.
#[test]
fn refined_call_in_an_instance_body_sees_only_its_own_frames() {
    let items = "fn validate(x: i64) where x > 0 -> i64 {\n    return x;\n}\nfn wrap<T>(x: i64, t: T) -> i64 {\n    return validate(x);\n}\n";
    let narrowed = "    let mut a: i64 = 0;\n    if x > 0 {\n        a = wrap(x, 1);\n    }\n";
    let outside = "    let b = wrap(0 - 7, 1);\n";
    let program =
        |body: &str| format!("module tool;\n{items}{MAIN}    let x: i64 = 5;\n{body}}}\n");
    for (shape, body) in [
        (
            "narrowed first",
            format!("{narrowed}{outside}    return 0 - (a + b + 100);\n"),
        ),
        (
            "outside first",
            format!("{outside}{narrowed}    return 0 - (a + b + 100);\n"),
        ),
    ] {
        assert_eq!(codes_of(&program(&body)), ["T211"], "{shape}");
    }
    let direct = program(
        "    let mut a: i64 = 0;\n    if x > 0 {\n        a = validate(x);\n    }\n    return 0 - a;\n",
    );
    assert_eq!(run_returning_negative(&direct), 5);
}

/// A `break` in a body that has no loop of its own is T260, wherever that body is first reached
/// from: a generic body first created inside the caller's loop, a closure written inside a loop,
/// and a handle clause inside a loop, each a function of its own. The loop depth they inherited
/// let the `break` pass: the generic body and the closure stopped on an internal error (I013),
/// and the handle clause reached the gate for effect-handler lowering (E004 twice). Each twin
/// outside any loop was T260.
#[test]
fn break_with_no_loop_in_its_own_body_is_t260() {
    let generic = "fn brk<T>(t: T) -> i64 {\n    break;\n    return 1;\n}\n";
    let effect = "effect Reader { fn get() -> i64; }\nfn provider() -> i64 ! { Reader } { return perform Reader.get(); }\n";
    let program = |items: &str, body: &str| format!("module tool;\n{items}{MAIN}{body}}}\n");
    for (shape, items, body) in [
        (
            "generic, first created in a loop",
            generic,
            format!("{}    return 0 - s;\n", in_loop("brk(1)")),
        ),
        (
            "generic, first created outside",
            generic,
            format!("    let z = brk(1);\n{}    return 0 - s - z;\n", in_loop("brk(1)")),
        ),
        (
            "closure in a loop",
            "",
            "    let mut s: i64 = 0;\n    for i in 0..4 {\n        let f = fn(v: i64) -> i64 { break; return v; };\n        s = s + f(i);\n    }\n    return 0 - s;\n"
                .to_string(),
        ),
        (
            "closure outside any loop",
            "",
            "    let f = fn(v: i64) -> i64 { break; return v; };\n    return 0 - f(1);\n"
                .to_string(),
        ),
        (
            "handle clause in a loop",
            effect,
            format!(
                "{}    return 0 - s;\n",
                in_loop("handle provider() { Reader.get() => { break; } }")
            ),
        ),
        (
            "handle clause outside any loop",
            effect,
            "    let s = handle provider() { Reader.get() => { break; } };\n    return 0 - s;\n"
                .to_string(),
        ),
    ] {
        assert_eq!(codes_of(&program(items, &body)), ["T260"], "{shape}");
    }
}

/// A slice must be the direct child of a borrow (`&arr[1..3]`); anywhere else it is T238. The flag
/// that marks a borrow's direct child stayed set for everything beneath it, so a bare slice
/// passed, and its program ran, when it sat in a borrowed call's argument (`&g2(arr[1..3])`), in a
/// closure passed to a borrowed call, or in a generic body first created by one (`&g(1)`). Each is
/// now T238, as the same slice is with no borrow around it; a borrowed slice under a borrowed call
/// still runs.
#[test]
fn slice_nested_under_a_borrow_is_t238() {
    let program = |items: &str, body: &str| format!("module tool;\n{items}{MAIN}{body}}}\n");
    let generic = "fn g<T>(t: T) -> [i64; 2] {\n    let arr = [1, 2, 3, 4, 5];\n    let s = arr[1..3];\n    return [7, 8];\n}\n";
    let takes_slice = "fn g2(s: &[i64]) -> [i64; 2] {\n    return [s[0], 8];\n}\n";
    let takes_closure = "fn g3(f: Fn() -> i64) -> [i64; 2] {\n    return [f(), 8];\n}\n";
    for (shape, items, body) in [
        (
            "generic body, borrowed first",
            generic,
            "    let r = &g(1);\n    return 0 - r[0];\n",
        ),
        (
            "generic body, plain first",
            generic,
            "    let q = g(1);\n    let r = &g(1);\n    return 0 - r[0] - q[1];\n",
        ),
        (
            "argument of a borrowed call",
            takes_slice,
            "    let arr = [1, 2, 3, 4, 5];\n    let r = &g2(arr[1..3]);\n    return 0 - r[0];\n",
        ),
        (
            "closure under a borrowed call",
            takes_closure,
            "    let r = &g3(fn() -> i64 { let arr = [1, 2, 3, 4, 5]; let s = arr[1..3]; return 7; });\n    return 0 - r[0];\n",
        ),
        (
            "closure, no borrow",
            takes_closure,
            "    let r = g3(fn() -> i64 { let arr = [1, 2, 3, 4, 5]; let s = arr[1..3]; return 7; });\n    return 0 - r[0];\n",
        ),
    ] {
        assert_eq!(codes_of(&program(items, body)), ["T238"], "{shape}");
    }
    let borrowed = program(
        takes_slice,
        "    let arr = [1, 2, 3, 4, 5];\n    let r = &g2(&arr[1..3]);\n    return 0 - r[0];\n",
    );
    assert_eq!(run_returning_negative(&borrowed), 2);
}

// ── closed gaps (tests/attack/KNOWN_GAPS.md) ─────────────────────────────────

/// Closed by DBC-0a (found while fixing SR-035, and open until then): within one function body,
/// an `if x > 0` frame refines the `x` it narrowed and no binding that shadows it. `validate`
/// requires `x > 0`; a `let x` in the arm, a `match` binding `Some(x)` and a closure parameter
/// `x` each hold -7, and each is refused with exactly T211: the new binding carries no fact, so
/// the call cannot be discharged. Until DBC-0a the frame discharged each one, and the program
/// ran `validate` with -7 and returned 93.
#[test]
fn narrowing_stops_at_a_binding_that_shadows_its_name() {
    let items = "fn validate(x: i64) where x > 0 -> i64 {
    return x;
}
";
    let program = |arm: &str| {
        format!(
            "module tool;\n{items}{MAIN}    let x: i64 = 5;\n    let o: Option<i64> = Some(0 - 7);\n    let mut a: i64 = 0;\n    if x > 0 {{\n{arm}    }}\n    return 0 - (a + 100);\n}}\n"
        )
    };
    for (shape, arm) in [
        (
            "let",
            "        let x: i64 = 0 - 7;
        a = validate(x);
",
        ),
        (
            "match binding",
            "        match o {
            Some(x) => { a = validate(x); },
            None => { a = 1; },
        }
",
        ),
        (
            "closure parameter",
            "        let f = fn(x: i64) -> i64 { return validate(x); };
        a = f(0 - 7);
",
        ),
    ] {
        let mut got = codes_of(&program(arm));
        got.sort();
        got.dedup();
        assert_eq!(
            got,
            vec!["T211".to_string()],
            "{shape}: the narrowing's fact reached a binding that shadows its name (DBC-0a regressed)"
        );
    }
}
