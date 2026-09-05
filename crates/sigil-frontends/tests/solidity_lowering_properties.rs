//! Property checks for post-check Solidity lowering.

use proptest::prelude::*;
use sigil_compiler::compile_named_module;
use sigil_frontends::{Frontend, frontend_for};

fn solidity() -> Box<dyn Frontend> {
    frontend_for("solidity").expect("solidity frontend registered")
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn narrow_integer_arithmetic_uses_the_operand_width_bound(
        width_step in 1_u16..=15,
        multiply in any::<bool>(),
    ) {
        let bits = width_step * 8;
        let (operator, helper) = if multiply {
            ("*", "__fe_mul_checked")
        } else {
            ("+", "__fe_add_checked")
        };
        let source = format!(
            "pragma solidity ^0.8.0;\n\
             contract C {{\n\
                 function f(uint{bits} a, uint{bits} b) public pure returns (uint{bits}) {{\n\
                     return a {operator} b;\n\
                 }}\n\
             }}\n"
        );

        let emitted = solidity()
            .translate(&source, "uintn_property.sol")
            .expect("generated narrow-integer contract should translate");
        let expected_call = format!("{helper}(a, b, {})", 1_u128 << bits);

        prop_assert!(
            emitted.text.contains(&expected_call),
            "uint{bits} lowering did not contain `{expected_call}`:\n{}",
            emitted.text,
        );
        prop_assert!(
            compile_named_module(&emitted.source_name, &emitted.text).is_ok(),
            "generated uint{bits} output did not compile:\n{}",
            emitted.text,
        );
    }
}
