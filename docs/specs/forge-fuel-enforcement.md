# Forge fuel enforcement

**Status:** Implemented. The ephemeral runtime traps on the first fuel decrement that cannot be
paid; forge fuel is an enforcement boundary rather than advisory accounting.

## Host contract

`link_sigil_imports` exposes `sigil::fuel_decrement` with Wasm type `(i32) -> ()`. Its host closure
returns `WasmtimeResult<()>`, so a Rust error becomes a Wasmtime trap without changing the guest ABI
or emitted Wasm.

For a requested decrement:

1. negative amounts trap;
2. an amount greater than `fuel_remaining` sets `fuel_exhausted` and traps; and
3. an affordable amount is subtracted exactly.

The runtime refuses an over-budget decrement. It does not saturate the counter, which would hide an
overrun as apparent exact-budget consumption.

Trap classification uses the explicit `fuel_exhausted` flag rather than
`fuel_remaining == 0`. A tool may legally spend its final unit and later trap for another reason;
that failure must not be reported as fuel exhaustion.

`ToolError::FuelExhausted { consumed }` reports the available budget because the rejected
decrement is the first unpaid operation. Ephemeral state is discarded after every execution, so a
fuel trap cannot publish a partially mutated forge store.

## Budget estimates

`FuelPlan::recommended_budget` is a proved workload ceiling only when
`FuelPlan::is_workload_ceiling` is true. That flag requires statically bounded decrements, an
acyclic direct-call graph, and no indirect calls or sends. Otherwise the recommendation is a floor;
a caller-selected policy budget may legitimately trap.

The `sigil forge` default remains a policy value and does not reinterpret every recommendation as a
proof. Dead or unreachable unbounded loops may conservatively keep `is_workload_ceiling` false
because the current analysis is program-text based.

## Runtime boundary

The actor runtime also traps on fuel exhaustion, but actors retain state across handler
invocations. This document does not claim transactional rollback for actor-hosted mutations. The
forge guarantee relies on discarding the entire ephemeral store after a trap.

## Evidence

- `crates/sigil-runtime/tests/forge_fuel_probe.rs` covers overrun, exact accounting,
  within-budget completion, and unrelated traps at zero remaining fuel.
- `crates/sigil-runtime/tests/fuel_wcc.rs` checks recommended ceilings over generated bounded
  programs.
- bounded-collection runtime tests execute their maximum workload at the recommended budget.
- self-host byte-equality tests ensure the host-side enforcement does not alter emitted Wasm.

Any change to fuel accounting must preserve ABI identity, distinguish exhaustion from unrelated
traps, and include both an overrun case and an exact-fit case.
