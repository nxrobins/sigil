//! SOL-uintN M-spike: the EMITTED width-trap helper shape must compile AND trap at the
//! per-width bound under the trusted compiler + runtime. The Solidity frontend lowers a
//! `uintN` `+`/`*` to `__fe_add_checked`/`__fe_mul_checked(a, b, 2^N)` (emitted inline as
//! free fns). This proves that shape (a) type-checks, (b) TRAPS when the result reaches
//! `2^N`, and (c) runs and returns the right value below it. The `u256` carrier traps only
//! at `2^256`, so this per-`2^N` `trap_if` is the frontend's SOLE overflow gate — EX-1.
//! Permanent regression. Mirrors the `bounded_map_u256.rs` harness (no `! { Alloc }`).
mod common;

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// The two helpers EXACTLY as the frontend emits them, plus a `tool_main` body.
const HELPERS: &str = concat!(
    "fn __fe_add_checked(a: u256, b: u256, bound: u256) -> u256 { let r = (a + b); trap_if(r >= bound); return r; }\n",
    "fn __fe_mul_checked(a: u256, b: u256, bound: u256) -> u256 { let r = (a * b); trap_if(r >= bound); return r; }\n",
);

fn module(body: &str) -> String {
    format!(
        "module tool;\n{HELPERS}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

/// True iff `body` GENUINELY traps.
fn body_traps(body: &str) -> bool {
    common::tool_traps_with_min_fuel(&module(body), 1_000_000_000)
}

/// Decode a `return 0 - K` sentinel (a u256 can't cross the i64 `tool_main` ABI).
fn neg(body: &str) -> i64 {
    let result = compile_tool(&module(body)).expect("spike module should compile");
    match execute_ephemeral(
        &result.wasm,
        b"",
        result.fuel_budget.max(1_000_000_000),
        &IoGrants::none(),
    ) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            let s = message
                .find(p)
                .unwrap_or_else(|| panic!("no sentinel: {message}"))
                + p.len();
            let e = message[s..].find(')').unwrap();
            message[s..s + e].parse().unwrap()
        }
        other => panic!("expected sentinel trap, got {other:?}"),
    }
}

// uint128 bound and the two halves: 2^127 + 2^127 == 2^128 EXACTLY, so the add reaches the
// bound. Both are < 2^256, so the carrier's `u256_add` does NOT trap — the WIDTH `trap_if`
// is what fires, which is precisely what we must prove.
const B128: &str = "340282366920938463463374607431768211456"; // 2^128
const H127: &str = "170141183460469231731687303715884105728"; // 2^127
const H64: &str = "18446744073709551616"; // 2^64

#[test]
fn add_at_bound_traps() {
    // 2^127 + 2^127 = 2^128 = bound → width-trap fires (carrier would not).
    assert!(body_traps(&format!(
        "    let _r: u256 = __fe_add_checked({H127}, {H127}, {B128});\n    return 0 - 1;"
    )));
}

#[test]
fn add_below_bound_runs() {
    // 2 + 3 = 5 < bound → no trap; sentinel 1 iff the result is exactly 5.
    assert_eq!(
        neg(&format!(
            "    let r: u256 = __fe_add_checked(2, 3, {B128});\n    if r == 5 {{ return 0 - 1; }} else {{ return 0 - 2; }}"
        )),
        1
    );
}

#[test]
fn mul_at_bound_traps() {
    // 2^64 * 2^64 = 2^128 = bound → width-trap fires (product < 2^256, no carrier trap).
    assert!(body_traps(&format!(
        "    let _r: u256 = __fe_mul_checked({H64}, {H64}, {B128});\n    return 0 - 1;"
    )));
}

#[test]
fn mul_below_bound_runs() {
    // 3 * 4 = 12 < bound → no trap; sentinel 1 iff the result is exactly 12.
    assert_eq!(
        neg(&format!(
            "    let r: u256 = __fe_mul_checked(3, 4, {B128});\n    if r == 12 {{ return 0 - 1; }} else {{ return 0 - 2; }}"
        )),
        1
    );
}

// ── END-TO-END: translate a real Solidity `uint8` contract through the FRONTEND, wrap it
// with a `tool_main` that calls the method, and RUN it. This closes the EX-1 loop end to
// end: the frontend emits the helper with the right `2^8` bound AND it traps at runtime,
// on the actual translated artifact (not a hand-written helper). ───────────────────────

/// Translate a `uint8` adder contract and append a `tool_main` running `body`. The emitted
/// module already declares `module tool;` (source name `tool.sol`) + the `__fe_add_checked`
/// helper + `record C` + `impl C { new(); add8() }`; we append the free `tool_main`.
fn uint8_contract_tool(body: &str) -> String {
    use sigil_frontends::frontend_for;
    let src = "pragma solidity ^0.8.0;\ncontract C { function add8(uint8 a, uint8 b) public pure returns (uint8) { return a + b; } }\n";
    let emitted = frontend_for("solidity")
        .unwrap()
        .translate(src, "tool.sol")
        .expect("uint8 contract must translate")
        .text;
    assert!(
        emitted.contains("__fe_add_checked(a, b, 256)"),
        "the frontend must emit the uint8 add with the 2^8 bound:\n{emitted}"
    );
    format!("{emitted}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n")
}

#[test]
fn translated_uint8_overflow_traps() {
    // 200 + 100 = 300 >= 2^8 → the translated contract method TRAPS at runtime.
    let m = uint8_contract_tool(
        "    let c: C = C::new();\n    let _r: u256 = c.add8(200, 100);\n    return 0 - 1;",
    );
    let result = compile_tool(&m).expect("translated contract + tool_main must compile");
    assert!(
        matches!(
            execute_ephemeral(
                &result.wasm,
                b"",
                result.fuel_budget.max(1_000_000_000),
                &IoGrants::none()
            ),
            Err(ToolError::Trapped { .. })
        ),
        "uint8 200 + 100 must trap (Solidity reverts; SIGIL must too)"
    );
}

#[test]
fn translated_uint8_below_bound_runs() {
    // 2 + 3 = 5 < 2^8 → runs; sentinel 1 iff the result is exactly 5.
    let m = uint8_contract_tool(
        "    let c: C = C::new();\n    let r: u256 = c.add8(2, 3);\n    if r == 5 { return 0 - 1; } else { return 0 - 2; }",
    );
    let result = compile_tool(&m).expect("compile");
    match execute_ephemeral(
        &result.wasm,
        b"",
        result.fuel_budget.max(1_000_000_000),
        &IoGrants::none(),
    ) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            let s = message.find(p).expect("sentinel") + p.len();
            let e = message[s..].find(')').unwrap();
            assert_eq!(&message[s..s + e], "1", "2 + 3 must equal 5");
        }
        other => panic!("expected the sentinel, got {other:?}"),
    }
}
