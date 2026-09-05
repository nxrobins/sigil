//! Tuples v1 — compile-level gates: T261 for malformed tuples (1-tuples, empty
//! `()` types, over-arity, non-tuple destructure, arity mismatch), plus the
//! ET-9 recursion guards (a tuple of generics exercises `apply_subst`; a tuple
//! type-annotation round-trips through `resolve_type_expr`).

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
fn arity_mismatch_is_t261() {
    // 3 names, a 2-tuple value.
    let src = tool("    let (x, y, z) = (1, 2);\n    return 0 - x;");
    assert!(
        has(&src, "T261"),
        "arity mismatch must be T261: {:?}",
        codes_of(&src)
    );
}

#[test]
fn destructure_non_tuple_is_t261() {
    let src = tool("    let (x, y) = 5;\n    return 0 - x;");
    assert!(
        has(&src, "T261"),
        "destructuring a non-tuple must be T261: {:?}",
        codes_of(&src)
    );
}

#[test]
fn one_tuple_literal_is_t261() {
    // `(1,)` — a 1-tuple literal is rejected at parse time.
    let src = tool("    let p = (1,);\n    return 0 - 1;");
    assert!(
        has(&src, "T261"),
        "a 1-tuple literal `(1,)` must be T261: {:?}",
        codes_of(&src)
    );
}

#[test]
fn one_name_destructure_is_t261() {
    // `let (x) = …` — a single-name parenthesized binding is not a destructure.
    let src = tool("    let (x) = (1, 2);\n    return 0 - 1;");
    assert!(
        has(&src, "T261"),
        "`let (x) = …` must be T261: {:?}",
        codes_of(&src)
    );
}

#[test]
fn empty_tuple_type_is_t261() {
    // `()` in type position is not a 0-tuple.
    let src = "module tool;\n\
        fn f(p: ()) -> i64 { return 0; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   return 0 - 1;\n}\n";
    assert!(
        has(src, "T261"),
        "an empty `()` tuple type must be T261: {:?}",
        codes_of(src)
    );
}

#[test]
fn over_arity_literal_is_t261() {
    // 13 elements — over MAX_TUPLE_ARITY (12).
    let src = tool("    let big = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);\n    return 0 - 1;");
    assert!(
        has(&src, "T261"),
        "a 13-element tuple must be T261: {:?}",
        codes_of(&src)
    );
}

#[test]
fn tuple_type_param_compiles() {
    // A `(i64, i64)` parameter type round-trips through resolve_type_expr, and
    // the callee destructures it.
    let src = "module tool;\n\
        fn sum_pair(p: (i64, i64)) -> i64 { let (a, b) = p; return a + b; }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let pair = (40, 2);\n\
        \x20   return 0 - sum_pair(pair);\n}\n";
    assert!(
        compile_tool(src).is_ok(),
        "a tuple-typed parameter must compile: {:?}",
        codes_of(src)
    );
}

#[test]
fn tuple_of_generic_compiles() {
    // ET-9 apply_subst guard: a generic impl method returning `(T, T)`. Without
    // the recursive `apply_subst` tuple arm, the `Type::Generic("T")` survives
    // into mangle_type and ICEs. With it, the i64 instantiation compiles.
    let src = "module tool;\n\
        record Box<T> { v: T }\n\
        impl Box<T> { fn pair(self: Box<T>) -> (T, T) { return (self.v, self.v); } }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let b: Box<i64> = Box { v: 7 };\n\
        \x20   let (x, y) = b.pair();\n\
        \x20   return 0 - (x + y);\n}\n";
    assert!(
        compile_tool(src).is_ok(),
        "a tuple of generics must compile (apply_subst recursion): {:?}",
        codes_of(src)
    );
}
