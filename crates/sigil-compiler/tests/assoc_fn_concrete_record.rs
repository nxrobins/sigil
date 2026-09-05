//! BoundedVec PR-0a: associated functions on CONCRETE (non-generic) records.
//!
//! `Vec::new()` worked because `Vec` is generic (its impl methods register in
//! `universe.generic_impl_methods`); a concrete record's no-`self` `::new()` hit
//! T060. The dispatch gate now keys on `FunctionSig::is_associated` (first param
//! ≠ `self`), so a concrete record's `R::make()` resolves — while the
//! records-only outer guard keeps enum-variant constructors and modules out.

use sigil_compiler::compile_tool;

fn tool(decls: &str, body: &str) -> String {
    format!(
        "module tool;\n{decls}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

#[test]
fn assoc_new_resolves_for_concrete_record() {
    // The new capability: a no-`self` associated fn on a NON-generic record.
    let src = tool(
        "record R { x: i64 }\nimpl R { pub fn make() -> R { return R { x: 7 }; } }",
        "    let r = R::make();\n    return 0 - r.x;",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "R::make() should resolve for a concrete record: {:?}",
        compile_tool(&src).err()
    );
}

#[test]
fn assoc_fn_with_arg_resolves_for_concrete_record() {
    // Multi-arg associated fn (the `with_capacity(n)` shape) on a concrete record.
    let src = tool(
        "record R { x: i64 }\nimpl R { pub fn of(v: i64) -> R { return R { x: v }; } }",
        "    let r = R::of(9);\n    return 0 - r.x;",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "R::of(9) should resolve: {:?}",
        compile_tool(&src).err()
    );
}

#[test]
fn self_method_on_concrete_record_still_dispatches() {
    // A `self`-receiver method (is_associated=false) is unaffected — `r.get()`.
    let src = tool(
        "record R { x: i64 }\nimpl R { pub fn new() -> R { return R { x: 3 }; } pub fn get(self: R) -> i64 { return self.x; } }",
        "    let r = R::new();\n    return 0 - r.get();",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "concrete record self-method should dispatch: {:?}",
        compile_tool(&src).err()
    );
}

#[test]
fn enum_variant_ctor_not_hijacked() {
    // ET-5: Color is an ENUM, not a record — the records-only outer guard must
    // exclude it, so `Color::Green` resolves as a variant, not an associated fn.
    let src = tool(
        "enum Color { Red, Green }",
        "    let c = Color::Green;\n    match c {\n        Color::Red => { return 0 - 1; },\n        Color::Green => { return 0 - 2; }\n    }",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "Color::Green enum ctor should still resolve: {:?}",
        compile_tool(&src).err()
    );
}
