//! Property checks spanning the free-call and method-call dispatch phases.

use proptest::prelude::*;
use sigil_compiler::compile_named_module;

proptest! {
    #[test]
    fn machine_int_dispatch_is_deterministic(
        ty in prop_oneof![Just("i32"), Just("u32"), Just("i64"), Just("u64")],
        value in 0_u32..10_000,
        use_method in any::<bool>(),
    ) {
        let call = if use_method {
            format!("b.keep({value})")
        } else {
            format!("keep_free({value})")
        };
        let source = format!(r#"
module dispatch_property;

record Box {{ value: {ty} }}

fn keep_free(value: {ty}) -> {ty} {{
    return value;
}}

impl Box {{
    fn keep(self: Box, value: {ty}) -> {ty} {{
        return value;
    }}
}}

pub fn run() -> {ty} ! {{ Alloc }} {{
    let b: Box = Box {{ value: 0 }};
    return {call};
}}
"#);

        let first = compile_named_module("dispatch_property.sigil", &source)
            .expect("generated dispatch program should compile");
        let second = compile_named_module("dispatch_property.sigil", &source)
            .expect("generated dispatch program should compile repeatedly");

        prop_assert_eq!(first.wasm_inner, second.wasm_inner);
        prop_assert_eq!(first.wasm_outer, second.wasm_outer);
    }

    #[test]
    fn resolved_free_calls_report_argument_type_mismatches(
        expected in prop_oneof![Just("i32"), Just("u32"), Just("i64"), Just("u64")],
        bad_arg in prop_oneof![Just("true"), Just("\"not an integer\"")],
    ) {
        let source = format!(r#"
module call_diagnostic_property;

fn keep(value: {expected}) -> {expected} {{
    return value;
}}

pub fn run() -> {expected} {{
    return keep({bad_arg});
}}
"#);

        let error = compile_named_module("call_diagnostic_property.sigil", &source)
            .expect_err("generated argument mismatch should be rejected");
        let codes = error
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect::<Vec<_>>();

        prop_assert!(codes.contains(&"T071"), "expected T071, found {codes:?}");
    }
}
