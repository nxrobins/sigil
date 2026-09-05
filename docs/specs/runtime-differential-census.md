# Runtime host differential contract

**Status:** Active and machine-checked.

SIGIL has two execution hosts: the ephemeral forge and the persistent actor runtime. They share
compiler-emitted guest checks, but host imports are separate implementations and can drift. The
runtime differential census compares those host decisions directly.

## Scope

The census unit is a host import and a concrete argument. Tests use hand-written Wasm text so the
result describes host behavior independently of what today's compiler happens to emit. Guest-side
bounds, overflow, and explicit `trap()` checks are outside this census because both hosts execute the
same emitted instructions.

Verdicts are normalized to semantic classes such as `Completed`, `FuelExhausted`, `GuestTrap`, and
`HostRejected`; message wording is not compared.

## Current convergence rows

| Row | Witness | Required verdict on both hosts |
|---|---:|---|
| `fuel_decrement/in_budget` | `1` under budget 128 | `Completed` |
| `fuel_decrement/overrun` | `200` under budget 128 | `FuelExhausted` |
| `fuel_decrement/negative` | `-8` | `GuestTrap` |
| `alloc/negative` | `-1` | `GuestTrap` |

Each row also runs a benign control. The test rejects a row whose witness cannot be distinguished
from its control, requires both host cells to execute, and requires each host column to produce more
than one verdict class. Error classifiers and the actor import manifest are matched exhaustively so
new variants or imports force an explicit decision.

## Allocation-size boundary

Both hosts route guest-controlled allocation sizes through `AllocBytes::checked_from_guest`. Its
inner value is private, so an allocator cannot accept an unchecked guest `i32` without changing the
shared gate. Negative sizes reject cleanly; the actor alignment step also uses checked arithmetic.
Host-originated lengths use the explicitly named `from_host_len` constructor.

The hosts retain different valid-allocation policies where intentional, including actor-side
alignment and per-actor arenas. The census claims convergence only for its named verdict rows.

## Actor/capability imports

The forge cannot execute actor or capability operations. Calls to `send`, `ask`, `spawn`,
`cap_restrict`, `cap_split`, and `cap_mint` trap rather than silently returning a plausible value.
At source level, `M011` rejects a tool project that also declares actors, including the single-file
and non-entry cases missed by project entry-point gates.

The actor host implements those operations. `rtc_actor_ops_reject_hostile_args` requires malformed
actor IDs, capability IDs, payload ranges, and lengths to return a clean runtime error rather than
panic or silently complete. The actor threat model still trusts compiler capability-ownership
verification; revalidating forged ownership in arbitrary hand-written Wasm is not claimed.

## Authorities

- `crates/sigil-runtime/tests/runtime_differential_census.rs` owns convergence rows, anti-vacuity,
  forge traps, and actor hostile-argument checks.
- `crates/sigil-runtime/src/alloc_size.rs` owns the shared allocation-size type boundary.
- `crates/sigil-compiler/tests/tool_actor_exclusion.rs` owns the `M011` source-model partition.
- `crates/sigil-runtime/tests/import_contract.rs` and `sigil-abi` own host-import manifest coverage.

## Change rule

A new or changed host import needs an explicit forge and actor disposition. A shared guarantee gets a
control/witness differential row; intentionally different models pin both sides in focused tests.
Silent no-ops, unchecked narrowing, host panics on guest input, and wildcard classification are not
valid dispositions.
