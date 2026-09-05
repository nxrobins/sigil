//! Iterator protocol (PR-1) compile-level gates: the shape-gated detection (ET-1 →
//! T259), the array-path regression (ET-5), and the non-iterator fallback (T052).

use sigil_compiler::compile_tool;

use sigil_test_utils::pipeline::compile_tool_codes as codes_of;

fn has(src: &str, code: &str) -> bool {
    codes_of(src).iter().any(|c| c == code)
}

/// A `Counter` whose `impl` body is `next_impl`, iterated by `loop_body`.
fn with_next(next_impl: &str, loop_body: &str) -> String {
    format!(
        "module tool;\n\
         record Counter {{ cur: i64, max: i64 }}\n\
         impl Counter {{\n{next_impl}\n}}\n\
         fn make_counter(n: i64) -> Counter {{ return Counter {{ cur: 0, max: n }}; }}\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{loop_body}\n}}\n"
    )
}

const VALID_NEXT: &str = "    pub fn next(self: Counter @Mut) -> Option<i64> { if self.cur < self.max { let v: i64 = self.cur; self.cur = self.cur + 1; return Some(v); } else { return None; } }";

#[test]
fn array_for_loop_still_compiles() {
    // ET-5 regression: the array path is untouched and still compiles clean.
    let src = "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let mut sum: i64 = 0;\n\
        \x20   for x in [1, 2, 3] { sum = sum + x; }\n\
        \x20   return 0 - sum;\n}\n";
    assert!(
        compile_tool(src).is_ok(),
        "array for-loop must compile: {:?}",
        codes_of(src)
    );
}

#[test]
fn valid_iterator_compiles() {
    let src = with_next(
        VALID_NEXT,
        "    let mut s: i64 = 0;\n    for x in make_counter(3) { s = s + x; }\n    return 0 - s;",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "a valid iterator must compile: {:?}",
        codes_of(&src)
    );
}

#[test]
fn misshaped_next_missing_mut_is_t259() {
    // ET-1: `next(self)` (bare/frozen self, no @Mut) is NOT an iterator — rejected AT
    // the loop, never silently iterated.
    let src = with_next(
        "    pub fn next(self: Counter) -> Option<i64> { return None; }",
        "    for x in make_counter(3) { return 0 - x; }\n    return 0 - 1;",
    );
    assert!(
        has(&src, "T259"),
        "missing @Mut must be T259: {:?}",
        codes_of(&src)
    );
}

#[test]
fn misshaped_next_non_option_is_t259() {
    // ET-1: a non-`Option` return is NOT an iterator.
    let src = with_next(
        "    pub fn next(self: Counter @Mut) -> i64 { return 0; }",
        "    for x in make_counter(3) { return 0 - x; }\n    return 0 - 1;",
    );
    assert!(
        has(&src, "T259"),
        "non-Option return must be T259: {:?}",
        codes_of(&src)
    );
}

#[test]
fn associated_next_is_not_an_iterator() {
    // An ASSOCIATED `next()` (no `self`) is `is_associated` → fails the shape predicate
    // → T259 (it is not a receiver method an iterator loop can drive).
    let src = with_next(
        "    pub fn next() -> Option<i64> { return None; }",
        "    for x in make_counter(3) { return 0 - x; }\n    return 0 - 1;",
    );
    assert!(
        has(&src, "T259"),
        "associated next must be T259: {:?}",
        codes_of(&src)
    );
}

#[test]
fn named_without_next_is_t052() {
    // A `Named` type with NO `next` is not an iterator → the pre-existing T052
    // (byte-identical message for any non-array iterable).
    let src = "module tool;\n\
        record Point { x: i64, y: i64 }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let p: Point = Point { x: 1, y: 2 };\n\
        \x20   for q in p { return 0 - q; }\n\
        \x20   return 0 - 1;\n}\n";
    assert!(
        has(src, "T052"),
        "named-without-next must be T052: {:?}",
        codes_of(src)
    );
}
