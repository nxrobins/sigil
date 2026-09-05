//! Property checks for built-in intrinsic call dispatch.

use proptest::prelude::*;
use sigil_compiler::compile_named_module;

#[derive(Clone, Copy, Debug)]
struct IntrinsicCase {
    callee: &'static str,
    arity: usize,
}

const INTRINSICS: &[IntrinsicCase] = &[
    IntrinsicCase {
        callee: "alloc",
        arity: 1,
    },
    IntrinsicCase {
        callee: "load8",
        arity: 1,
    },
    IntrinsicCase {
        callee: "store8",
        arity: 2,
    },
    IntrinsicCase {
        callee: "slot_new::<Fuel>",
        arity: 0,
    },
    IntrinsicCase {
        callee: "slot_put",
        arity: 2,
    },
    IntrinsicCase {
        callee: "slot_take",
        arity: 1,
    },
    IntrinsicCase {
        callee: "ct_eq",
        arity: 2,
    },
    IntrinsicCase {
        callee: "ct_select",
        arity: 3,
    },
    IntrinsicCase {
        callee: "ct_lt",
        arity: 2,
    },
    IntrinsicCase {
        callee: "vec_store",
        arity: 4,
    },
    IntrinsicCase {
        callee: "vec_load",
        arity: 4,
    },
    IntrinsicCase {
        callee: "str_from_raw",
        arity: 2,
    },
    IntrinsicCase {
        callee: "u256_from_i64",
        arity: 1,
    },
    IntrinsicCase {
        callee: "u256_make",
        arity: 4,
    },
    IntrinsicCase {
        callee: "u256_limb",
        arity: 2,
    },
    IntrinsicCase {
        callee: "trap_if",
        arity: 1,
    },
    IntrinsicCase {
        callee: "trap",
        arity: 0,
    },
];

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn every_intrinsic_reports_its_arity_for_generated_wrong_calls(
        wrong_arity_offset in 1_usize..=5,
        values in prop::collection::vec(any::<i16>(), 6),
    ) {
        for case in INTRINSICS {
            let arg_count = (case.arity + wrong_arity_offset) % 6;
            let args = values
                .iter()
                .take(arg_count)
                .map(i16::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            let source = format!(
                "module intrinsic_dispatch_property;\n\
                 cap type Fuel {{ burn }}\n\
                 fn probe() -> i64 {{\n\
                     {}({args});\n\
                     return 0;\n\
                 }}\n",
                case.callee,
            );

            let error = compile_named_module("intrinsic_dispatch_property.sigil", &source)
                .expect_err("a wrong-arity intrinsic call must be rejected");
            let codes = error
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code().as_str())
                .collect::<Vec<_>>();

            prop_assert!(
                codes.contains(&"T074"),
                "{} with {arg_count} args emitted {codes:?}",
                case.callee,
            );
        }
    }
}
