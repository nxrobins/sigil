//! Generated characterization checks for user-method dispatch.

use proptest::prelude::*;
use sigil_compiler::compile_named_module;

proptest! {
    #[test]
    fn user_method_calls_report_argument_type_mismatches(
        expected in prop_oneof![Just("i32"), Just("u32"), Just("i64"), Just("u64")],
        bad_arg in prop_oneof![Just("true"), Just("\"not an integer\"")],
    ) {
        let source = format!(r#"
module method_diagnostic_property;

record Box {{ value: {expected} }}

impl Box {{
    fn keep(self: Box, value: {expected}) -> {expected} {{ return value; }}
}}

pub fn run() -> {expected} ! {{ Alloc }} {{
    let b: Box = Box {{ value: 0 }};
    return b.keep({bad_arg});
}}
"#);

        let error = compile_named_module("method_diagnostic_property.sigil", &source)
            .expect_err("generated method argument mismatch should be rejected");
        let codes = error
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect::<Vec<_>>();

        prop_assert!(codes.contains(&"T071"), "expected T071, found {codes:?}");
    }

    #[test]
    fn associated_function_dispatch_is_deterministic(
        ty in prop_oneof![Just("i32"), Just("u32"), Just("i64"), Just("u64")],
        value in 0_u32..10_000,
    ) {
        let source = format!(r#"
module associated_dispatch_property;

record Box {{ value: {ty} }}

impl Box {{
    fn keep(value: {ty}) -> {ty} {{ return value; }}
}}

pub fn run() -> {ty} {{
    return Box::keep({value});
}}
"#);

        let first = compile_named_module("associated_dispatch_property.sigil", &source)
            .expect("generated associated-function program should compile");
        let second = compile_named_module("associated_dispatch_property.sigil", &source)
            .expect("generated associated-function program should compile repeatedly");

        prop_assert_eq!(first.wasm_inner, second.wasm_inner);
        prop_assert_eq!(first.wasm_outer, second.wasm_outer);
    }
}
