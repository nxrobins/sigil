#![allow(dead_code)]

use sigil_compiler::{compile_module, compile_tool};
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const NEGATIVE_SENTINEL_PREFIX: &str = "tool returned error (";

pub fn decode_negative_sentinel(message: &str) -> Result<i64, String> {
    let start = message
        .find(NEGATIVE_SENTINEL_PREFIX)
        .map(|index| index + NEGATIVE_SENTINEL_PREFIX.len())
        .ok_or_else(|| "negative-sentinel prefix is absent".to_owned())?;
    let end = message[start..]
        .find(')')
        .map(|offset| start + offset)
        .ok_or_else(|| "negative-sentinel terminator is absent".to_owned())?;
    message[start..end]
        .parse::<i64>()
        .map_err(|error| format!("negative-sentinel value is not an i64: {error}"))
}

pub fn run_returning_negative(source: &str) -> i64 {
    let compiled = compile_tool(source).expect("tool should compile");
    expect_negative(execute_ephemeral(
        &compiled.wasm,
        b"",
        compiled.fuel_budget,
        &IoGrants::none(),
    ))
}

pub fn run_returning_negative_with_fuel(source: &str, fuel: u64) -> i64 {
    let compiled = compile_tool(source).expect("tool should compile");
    expect_negative(execute_ephemeral(
        &compiled.wasm,
        b"",
        fuel,
        &IoGrants::none(),
    ))
}

pub fn run_returning_negative_with_min_fuel(source: &str, min_fuel: u64) -> i64 {
    let compiled = compile_tool(source).expect("tool should compile");
    expect_negative(execute_ephemeral(
        &compiled.wasm,
        b"",
        compiled.fuel_budget.max(min_fuel),
        &IoGrants::none(),
    ))
}

pub fn run_module_returning_negative(source: &str) -> i64 {
    let compiled = compile_module(source).expect("module should compile");
    expect_negative(execute_ephemeral(
        &compiled.wasm_inner,
        b"",
        compiled.fuel_budget,
        &IoGrants::none(),
    ))
}

fn expect_negative<T>(result: Result<T, ToolError>) -> i64 {
    match result {
        Err(ToolError::Trapped { message }) => {
            decode_negative_sentinel(&message).unwrap_or_else(|reason| {
                panic!("expected a negative sentinel, got `{message}`: {reason}")
            })
        }
        Err(other) => panic!("tool failed with non-trap error: {other:?}"),
        Ok(_) => panic!("tool returned a packed pointer; expected a negative sentinel"),
    }
}

pub fn tool_traps(source: &str) -> bool {
    tool_traps_with_min_fuel(source, 0)
}

pub fn tool_traps_with_min_fuel(source: &str, min_fuel: u64) -> bool {
    let compiled = compile_tool(source).expect("tool should compile");
    match execute_ephemeral(
        &compiled.wasm,
        b"",
        compiled.fuel_budget.max(min_fuel),
        &IoGrants::none(),
    ) {
        Err(ToolError::Trapped { message }) => decode_negative_sentinel(&message).is_err(),
        Err(_) | Ok(_) => false,
    }
}
