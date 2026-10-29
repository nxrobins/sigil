//! SR-034: a generic method's arguments are typed twice (`type_check/expressions/methods.rs`).
//! The first pass types them into a sink that is discarded, only to bind the method's own type
//! parameters; the second types them for real against the bound parameters. The instance cache
//! is filled before an instance's body is checked, so an instance the first pass created had its
//! body checked into the sink, and the second pass hit the cache and checked nothing: a type error
//! in that body was never reported, and `compile_tool` returned a module the engine refused, or
//! one that ran with a wrong value. A work limit the first pass hit left its T151 in the sink and
//! every later expression typed as `Error` with no diagnostic. Now an instance the first pass makes
//! keeps its report until a real inference uses it, and the work limit's T151 is kept until the
//! first pass ends (`MonomorphTracker::begin_speculation`). The first six tests pin the exact code
//! set of a program whose error is first reached through a generic method's argument, beside a
//! twin: the program without the error, which runs and returns its value, or the same error
//! reached outside any argument. Before the fix each such program compiled, or stopped on an
//! internal error (I013). The next two pin programs that main compiled and that are now rejected,
//! each for a reason it states. The last three pin what the fix must not do: report an instance
//! only the first pass made, report one literal twice, or check a body twice.

mod common;

use sigil_compiler::compile_tool;

/// The exact code set of a program, empty if it compiled.
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

/// A generic receiver with two generic methods: `remap` takes a closure, `put` any value.
const BOX: &str = "module tool;
record Box<T> { val: T }
impl Box<T> {
    fn remap<B>(self: Box<T>, f: Fn(T) -> B) -> Box<B> { return Box { val: f(self.val) }; }
    fn put<B>(self: Box<T>, v: B) -> Box<B> { return Box { val: v }; }
}
";

/// A program over `BOX` whose `tool_main` binds `b` to `Box { val: 4 }` and runs `body`.
fn over_box(items: &str, body: &str) -> String {
    format!(
        "{BOX}{items}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n    let b: Box<i64> = Box {{ val: 4 }};\n{body}\n}}\n"
    )
}

/// `mk<X>`'s body holds a `let` that is a type error (T041) in the rejected form and well typed
/// in its twin. Each form reaches `mk`'s instance through a generic method's argument: as the
/// argument, inside a closure argument, inside a nested method's argument, inside the stdlib's
/// `Option::map`, and before or after a use outside any argument, which then creates it first.
/// One more form reaches an associated function's instance, `Holder::make`, as the argument.
/// Before the fix each rejected form compiled and the engine refused its module ("failed to
/// compile"), except the one whose first use is outside the argument, which reported T041. One
/// T041 each: the body is checked once, and its report is kept.
#[test]
fn body_error_first_reached_through_a_method_argument_is_reported() {
    let mk =
        |binding: &str| format!("fn mk<X>(x: X) -> i64 {{\n    {binding}\n    return 7;\n}}\n");
    let option_main = |items: &str| {
        format!(
            "module tool;\n{items}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n    let o: Option<i64> = Some(3);\n    let m: Option<i64> = o.map(fn(v: i64) -> i64 {{ return mk(v) + v; }});\n    match m {{\n        Some(v) => {{ return 0 - v; }},\n        None => {{ return 0 - 1; }},\n    }}\n}}\n"
        )
    };
    let (bad, good) = (mk("let y: i64 = true;"), mk("let y: i64 = 1;"));
    let mut uses: Vec<(&str, String, String, i64)> = [
        (
            "argument",
            "    let c: Box<i64> = b.put(mk(1));\n    return 0 - c.val;",
            7,
        ),
        (
            "closure argument",
            "    let c: Box<i64> = b.remap(fn(v: i64) -> i64 { return mk(v) + v; });\n    return 0 - c.val;",
            11,
        ),
        (
            "nested method argument",
            "    let c: Box<i64> = b.put(b.put(mk(1)).val);\n    return 0 - c.val;",
            7,
        ),
        (
            "argument, then outside",
            "    let c: Box<i64> = b.put(mk(1));\n    let g = mk(2);\n    return 0 - c.val - g;",
            14,
        ),
        (
            "outside, then argument",
            "    let g = mk(2);\n    let c: Box<i64> = b.put(mk(1));\n    return 0 - c.val - g;",
            14,
        ),
    ]
    .into_iter()
    .map(|(shape, body, value)| (shape, over_box(&bad, body), over_box(&good, body), value))
    .collect();
    uses.push(("Option::map", option_main(&bad), option_main(&good), 10));
    let holder = |binding: &str| {
        over_box(
            &format!(
                "record Holder<T> {{ v: T }}\nimpl Holder<T> {{\n    fn make(v: T) -> i64 {{\n        {binding}\n        return 3;\n    }}\n}}\n"
            ),
            "    let k: i64 = 3;\n    let c: Box<i64> = b.put(Holder::make(k));\n    return 0 - c.val;",
        )
    };
    uses.push((
        "associated function",
        holder("let y: i64 = true;"),
        holder("let y: i64 = 1;"),
        3,
    ));
    for (shape, rejected, twin, value) in uses {
        assert_eq!(codes_of(&rejected), ["T041"], "{shape}: {rejected}");
        assert_eq!(
            common::run_returning_negative(&twin),
            value,
            "{shape}: {twin}"
        );
    }
}

/// An out-of-range literal in such a body is the same lost error with a worse outcome: before the
/// fix the program ran and returned 705032704, `5000000000` cut to 32 bits. The twin's literal
/// fits and reads back.
#[test]
fn out_of_range_literal_first_reached_through_a_method_argument_is_reported() {
    let program = |literal: &str| {
        over_box(
            &format!(
                "fn over<X>(x: X) -> i64 {{\n    let y: i32 = {literal};\n    return y.as_i64();\n}}\n"
            ),
            "    let c: Box<i64> = b.put(over(1));\n    return 0 - c.val;",
        )
    };
    assert_eq!(codes_of(&program("5000000000")), ["T041"]);
    assert_eq!(common::run_returning_negative(&program("50")), 50);
}

/// `grow`'s type doubles on each recursion until the expanded-type limit stops it (T151). Reached
/// through a generic method's argument, the T151 went into the sink and the work-limit flag
/// stayed set, so the rest of `tool_main` typed as `Error` with no diagnostic, a later type error
/// included, and the program compiled. Reached outside an argument it is T151, as now in every
/// form. Through a nested method's argument, the inner speculation's caller buffer is the outer
/// one's sink, so the T151 is held until the outermost speculation ends. The twin recurses at one
/// type and runs.
#[test]
fn work_limit_first_reached_through_a_method_argument_is_reported() {
    let grow = |next: &str| {
        format!(
            "fn grow<T>(x: T, n: i64) -> i64 {{\n    if n == 0 {{ return 6; }}\n    return grow({next}, n - 1);\n}}\n"
        )
    };
    let doubling = grow("(x, x)");
    for (shape, body) in [
        (
            "argument",
            "    let c: Box<i64> = b.put(grow(1, 3));\n    return 0 - c.val;",
        ),
        (
            "argument, then a type error",
            "    let c: Box<i64> = b.put(grow(1, 3));\n    let q: i64 = true;\n    return 0 - c.val;",
        ),
        (
            "nested argument, then a type error",
            "    let c: Box<i64> = b.put(b.put(grow(1, 3)).val);\n    let q: i64 = true;\n    return 0 - c.val;",
        ),
        (
            "outside",
            "    let z = grow(1, 3);\n    let c: Box<i64> = b.put(z);\n    return 0 - c.val;",
        ),
    ] {
        let rejected = over_box(&doubling, body);
        assert_eq!(codes_of(&rejected), ["T151"], "{shape}: {rejected}");
    }
    let twin = over_box(
        &grow("x"),
        "    let c: Box<i64> = b.put(grow(1, 3));\n    return 0 - c.val;",
    );
    assert_eq!(common::run_returning_negative(&twin), 6);
}

/// The type checker recurses once per instance it creates, so a chain of instances that runs to
/// the depth limit (64) overflows the 2 MiB test-thread stack before the limit stops it.
fn codes_on_a_large_stack(src: String) -> Vec<String> {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || codes_of(&src))
        .expect("the compile thread spawns")
        .join()
        .expect("the compile thread does not panic")
}

/// `BOX` with one more method on the impl.
fn box_with(method: &str) -> String {
    BOX.replacen("impl Box<T> {\n", &format!("impl Box<T> {{\n{method}"), 1)
}

/// `over_box` with one more method on the impl.
fn over_box_with(method: &str, items: &str, body: &str) -> String {
    over_box(items, body).replacen("impl Box<T> {\n", &format!("impl Box<T> {{\n{method}"), 1)
}

/// `over_box` with one more generic method, `two<B>`, whose two arguments share one type `B`.
fn over_box_with_two(items: &str, body: &str) -> String {
    over_box_with(
        "    fn two<B>(self: Box<T>, v: B, w: B) -> i64 { return 5; }\n",
        items,
        body,
    )
}

/// A program over `box_with(method)` whose `tool_main` reaches `deep` through `put`'s argument
/// (`b.put(b.deep(1))`) or outside any argument (`let z = b.deep(1);`).
fn deep_forms(method: &str) -> [(&'static str, String); 2] {
    let program = |body: &str| {
        format!(
            "{}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n    let b: Box<i64> = Box {{ val: 4 }};\n{body}\n}}\n",
            box_with(method)
        )
    };
    [
        (
            "argument",
            program("    let c: Box<i64> = b.put(b.deep(1));\n    return 0 - c.val;"),
        ),
        (
            "outside",
            program(
                "    let z = b.deep(1);\n    let c: Box<i64> = b.put(z);\n    return 0 - c.val;",
            ),
        ),
    ]
}

/// `deep` calls itself at a type one tuple deeper, so its instances nest until the depth limit
/// fails one (T150). Reached through `put`'s argument, the whole chain was made inside the
/// speculation, and its T150, nested under the chain's first instance, which the real pass then
/// found in the cache, was lost: main stopped on an internal error from the taint checker (I013).
/// The enclosing instance's use of the failed one carries the report to the real use of the chain,
/// so the form reached through the argument reports what the form outside it reports.
#[test]
fn depth_limit_nested_in_an_instance_made_in_a_method_argument_is_reported() {
    let forms =
        deep_forms("    fn deep<B>(self: Box<T>, v: B) -> i64 { return self.deep((v, 1)); }\n");
    for (shape, program) in forms {
        assert_eq!(codes_on_a_large_stack(program), ["T150"], "{shape}");
    }
}

/// Here the recursion itself runs through `put`'s argument, at every level, so the creations that
/// meet the depth limit run inside speculations in both forms: one T150 at `self.deep(..)` and one
/// at `self.put(..)`, the two calls that meet the limit. `put`'s instance is the same at every
/// level: its first attempt, the deepest, fails, and a shallower one stands, so a report is kept
/// per attempt, not per name. Nothing is reported twice. Main reported neither, in either form,
/// and stopped on an internal error from the taint checker (I013).
#[test]
fn depth_limit_through_method_arguments_is_reported_once() {
    let forms = deep_forms(
        "    fn deep<B>(self: Box<T>, v: B) -> i64 {\n        let c: Box<i64> = self.put(self.deep((v, 1)));\n        return c.val;\n    }\n",
    );
    for (shape, program) in forms {
        assert_eq!(codes_on_a_large_stack(program), ["T150", "T150"], "{shape}");
    }
}

/// `f` and `g` call each other. Through `pick`'s argument, `f(1)` is first typed before `B` is
/// bound: the speculation makes `f<Error>`, whose body makes `g<i64>`, whose body makes `f<i64>`,
/// whose body calls back into `g<i64>` while `g<i64>`'s own body is still being checked. The real
/// pass uses `f<i64>`, and through it `g<i64>`, so `g<i64>`'s out-of-range literal must be
/// reported. Recorded only once a body ended, that back edge was lost, and the program ran and
/// returned 705032704, as on main. One T041, as outside the argument; the twin's literal fits.
#[test]
fn recursion_back_into_an_instance_still_being_checked_is_reported() {
    let program = |literal: &str, body: &str| {
        over_box_with(
            "    fn pick<B>(self: Box<T>, v: B, w: B) -> B { return w; }\n",
            &format!(
                "fn f<X>(n: i64) -> (i64, Option<X>) {{\n    if n > 0 {{\n        let z = g(n, n - 1);\n        return (z, None);\n    }}\n    return (0, None);\n}}\nfn g<Y>(y: Y, n: i64) -> i64 {{\n    let p: (i64, Option<i64>) = f(n);\n    let w: i32 = {literal};\n    return w.as_i64();\n}}\n"
            ),
            body,
        )
    };
    let argument = "    let s: (i64, Option<i64>) = (0, None);\n    let r = b.pick(s, f(1));\n    let (v, o) = r;\n    return 0 - v;";
    let outside = "    let s: (i64, Option<i64>) = (0, None);\n    let m: (i64, Option<i64>) = f(1);\n    let r = b.pick(s, m);\n    let (v, o) = r;\n    return 0 - v;";
    for (shape, body) in [("argument", argument), ("outside", outside)] {
        assert_eq!(codes_of(&program("5000000000", body)), ["T041"], "{shape}");
    }
    assert_eq!(common::run_returning_negative(&program("50", argument)), 50);
}

/// A body is checked in the context of the site that creates its instance. In a neutral context,
/// `mk`'s statement `none_of(1);` has nothing to bind `none_of`'s type parameter: T150, then T049
/// from the `none_of<Error>` it makes. The speculation types `mk(1)` against `B` before `B` is
/// bound, a neutral context, so the form through the argument is now rejected, as the form outside
/// it without an annotation is; main lost that report and ran it. Created under
/// `let m: Option<i32> = mk(1);` instead, the statement takes the `let`'s expected type, which
/// `check_function_block` does not reset, and the program runs: that dependence of a body on the
/// site that creates it is older than this fix, and outside it.
#[test]
fn body_that_fails_in_a_neutral_context_is_rejected_through_a_method_argument() {
    let program = |body: &str| {
        over_box_with_two(
            "fn none_of<X>(n: i64) -> Option<X> {\n    return None;\n}\nfn mk<X>(x: X) -> Option<i32> {\n    none_of(1);\n    return Some(7);\n}\n",
            body,
        )
    };
    for (shape, body) in [
        (
            "argument",
            "    let s: Option<i32> = Some(3);\n    let r = b.two(s, mk(1));\n    return 0 - r;",
        ),
        (
            "outside, no annotation",
            "    let s: Option<i32> = Some(3);\n    let m = mk(1);\n    let r = b.two(s, m);\n    return 0 - r;",
        ),
    ] {
        assert_eq!(codes_of(&program(body)), ["T150", "T049"], "{shape}");
    }
}

/// A local named like the module (`tool`) makes `tool.put(..)` a speculation of its own, kept only
/// if it reports no error (the module-shadow branch in `methods.rs`). The real use of `mk`'s
/// instance claims its T041 into that speculation's buffer, so the call falls back to the branch's
/// own error, T156, and the T041 is discarded with the buffer, as a T041 the branch reports itself
/// is. That fails closed: main lost the T041 and compiled a module the engine refused. The twin
/// runs.
#[test]
fn error_claimed_in_the_module_shadow_speculation_rejects_the_call() {
    let program = |binding: &str| {
        format!(
            "{BOX}fn mk<X>(x: X) -> i64 {{\n    {binding}\n    return 7;\n}}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n    let tool: Box<i64> = Box {{ val: 4 }};\n    let c: Box<i64> = tool.put(mk(1));\n    return 0 - c.val;\n}}\n"
        )
    };
    assert_eq!(codes_of(&program("let y: i64 = true;")), ["T156"]);
    assert_eq!(
        common::run_returning_negative(&program("let y: i64 = 1;")),
        7
    );
}

/// The speculation types each argument against the method's type parameter before it is bound,
/// so a call whose own type parameter is bound only by its expected type gets none:
/// `none_of(1)` is made as `none_of<Error>`, whose body then fails to check. The real pass types
/// it against `Option<i32>` and uses `none_of<i32>`. An instance no real inference uses is the
/// speculation's artifact, and its report is dropped, as on main: the program runs and returns 5.
/// Reporting every instance a speculation made, as this fix first did, rejected it (T049).
#[test]
fn instance_only_the_speculation_made_is_not_reported() {
    let program = |body: &str| {
        over_box_with_two(
            "fn none_of<X>(n: i64) -> Option<X> {\n    return None;\n}\n",
            body,
        )
    };
    for (shape, body) in [
        (
            "argument",
            "    let s: Option<i32> = Some(3);\n    let r = b.two(s, none_of(1));\n    return 0 - r;",
        ),
        (
            "outside",
            "    let s: Option<i32> = Some(3);\n    let n: Option<i32> = none_of(1);\n    let r = b.two(s, n);\n    return 0 - r;",
        ),
    ] {
        assert_eq!(common::run_returning_negative(&program(body)), 5, "{shape}");
    }
}

/// An out-of-range literal in a generic body is reported once, by `report_once`, however many
/// instances narrow it: two instances of one body checked into one buffer see each other's report.
/// A report a real use claims goes through `report_once` too, so `over<bool>` and `over<i64>` give
/// one T041 in every order. Main gave one T041 with the first use outside the argument, and
/// compiled the other two forms to a module the engine refused; this fix first gave two T041 in
/// all three.
#[test]
fn literal_error_in_two_instances_is_reported_once() {
    let program = |body: &str| {
        over_box_with_two(
            "fn over<X>(x: X) -> i64 {\n    let y: i32 = 0 - 2147483648;\n    return 1;\n}\n",
            body,
        )
    };
    for (shape, body) in [
        (
            "outside, then argument",
            "    let a = over(true);\n    let c: Box<i64> = b.put(over(1));\n    return 0 - c.val - a;",
        ),
        (
            "two arguments",
            "    let c: Box<i64> = b.put(over(true));\n    let d: Box<i64> = b.put(over(1));\n    return 0 - c.val - d.val;",
        ),
        (
            "one call",
            "    let r = b.two(over(true), over(1));\n    return 0 - r;",
        ),
        (
            "outside twice",
            "    let a = over(true);\n    let d = over(1);\n    return 0 - a - d;",
        ),
    ] {
        assert_eq!(codes_of(&program(body)), ["T041"], "{shape}");
    }
}

/// No body is checked twice: a chain of twelve generic functions, each reached through a method
/// argument in the one before, compiles and runs, as on main. Taking the speculation's instances
/// back and creating them again would check each link twice per level, 2^12 instances: measured,
/// that chain met the instance limit (T151) from nine links on.
#[test]
fn chain_of_generic_functions_through_method_arguments_compiles() {
    let links: String = (1..=12)
        .map(|i| {
            if i < 12 {
                format!(
                    "fn f{i}<X>(x: X) -> i64 {{\n    let b: Box<i64> = Box {{ val: 1 }};\n    let c: Box<i64> = b.put(f{}(x));\n    return c.val + 1;\n}}\n",
                    i + 1
                )
            } else {
                "fn f12<X>(x: X) -> i64 {\n    return 1;\n}\n".to_string()
            }
        })
        .collect();
    let chain = over_box(
        &links,
        "    let c: Box<i64> = b.put(f1(1));\n    return 0 - c.val;",
    );
    assert_eq!(common::run_returning_negative(&chain), 12);
}
