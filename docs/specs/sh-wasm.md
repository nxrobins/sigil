# Self-hosted Wasm emission contract

**Status:** Implemented and current. This document replaces the historical SH-WASM W0-W5
rollout journal.

## Purpose

`selfhost/air.sigil` emits complete Wasm modules for the exact self-hosted AIR surface. The
authority is differential: supported modules must be byte-identical to
`wasm::emit(&fuel::insert(memory::lower(lower_oracle(src))).0).inner`; unsupported modules must
return the explicit `!!` poison sentinel.

The Rust authorities are:

- `crates/sigil-compiler/src/air.rs`
- `crates/sigil-compiler/src/memory.rs`
- `crates/sigil-compiler/src/fuel.rs`
- `crates/sigil-compiler/src/wasm.rs`

The surrounding self-hosted AIR contract is documented in [sh-air.md](sh-air.md).

## Module contract

The covered inner-ring surface preserves these module-level invariants:

- Eight fixed SIGIL runtime imports precede local functions.
- A local function's Wasm index is `8 + FuncId`, where `FuncId` is its position in the complete
  function vector. Actor initializers and handlers occupy positions in that vector.
- Free functions export as `{module}__{function}`; actor functions export as
  `{actor}__{function}`. Export hygiene (oracle `wasm::emit`, 2026-09-01): only an externally
  callable function has an export entry. A free function is externally callable iff it is `pub`;
  impl methods (Public by default on both sides), actor initializers and handlers, and the
  synthesized module initializer always are; a monomorph instance inherits its generic's
  visibility. A withheld export never moves an index: the function keeps its type, code, and
  table entries, and the export section count drops by exactly the withheld entries.
- The type section contains the eight import signatures followed by one entry per local function
  in vector order. It does not deduplicate equal local signatures.
- The table covers every local function, memory starts at one page, and `BUMP_PTR` starts at the
  aligned end of static string data.
- String segments are discovered in emission order, deduplicated by contents, and packed from
  offset 1024 before the final eight-byte alignment.
- Unsupported expressions, statements, opcodes, actor-state operations, or module shapes taint
  the module. A tainted module cannot produce plausible Wasm bytes.

There is no synthetic `ModuleInit` on this surface. Introducing one is a contract change because
it shifts type, function, export, element, and code indices.

## Encoding contract

The emitter uses the same position-sensitive integer encodings as the Rust authority:

| Position | Encoding |
| --- | --- |
| section sizes, counts, indices, vector lengths, and name lengths | ULEB128 |
| `local.*`, `call`, `br`, and `br_if` operands | ULEB128 |
| memory alignment and offset operands | ULEB128 |
| `i32.const` and `i64.const` operands | SLEB128 |
| value types and opcodes | fixed single bytes |

The signed boundary cases 63, 64, 127, 128, and -1 remain pinned. All opcode mappings are derived
from oracle output and covered by byte comparison; an unrecognized mapping poisons emission.

Control-flow emission mirrors the Rust block walker, including loop back-edge fuel, branch-merge
selection, dispatch exits, unreachable tails, and typed return defaults. Memory lowering preserves
typed loads and stores, bounds checks, bump allocation, narrow-index wrapping, arrays, records,
and string data. Calls materialize arguments in order and use the complete function-vector index.

## Evidence map

The W0-W5 names remain stable test identifiers, not implementation phases:

| Identifier | Permanent evidence |
| --- | --- |
| W0 | pinned oracle modules, strict comparison diagnostics, and totality over the corpus |
| W1 | scalar bodies, constants, arithmetic, mangling, and signed-LEB boundaries |
| W2 | branches, loops, matches, traps, and control-flow joins |
| W3 | loads, stores, allocation, arrays, records, and static data |
| W4 | calls, recursion, multiple functions, actors, and a stdlib ABI module |
| W5 | execution through the production runtime plus determinism and fuel census |

The accompanying `X-W*` labels identify permanent fences:

- `X-W2`: position-specific ULEB/SLEB and oracle-derived opcode mappings;
- `X-W3`: section contents are assembled before their encoded headers;
- `X-W4`: strict hexadecimal decoding and `!!` poison propagation;
- `X-W5`: self-hosted emission stays below half of the configured fuel budget;
- `X-W6`: byte mismatches report the first offset, local hex windows, and best-effort WAT;
- `X-W7`: final Wasm evidence is restricted to a single inner-ring module;
- `X-W8`: independent runs produce identical bytes.

`crates/sigil-runtime/tests/air_differential.rs` owns these cases. The preservation manifest in
`tests/support/air_case_manifest.rs` pins the required checks so test repacking cannot silently
remove evidence.

## Execution boundary

The W5 corpus compiles tool-shaped programs through both emitters, requires byte equality, and
executes each module with `execute_ephemeral`. It covers arithmetic, loops, branches, calls,
matches, arrays, records, recursion, mutation, and nested loops.

Byte equality is the primary correctness criterion. Runtime execution is an additional end-to-end
check that the identical artifact is accepted and behaves as expected. Multi-module outer-ring
programs remain compared at the AIR boundary, and stateful actor forms remain explicit poison as
specified by [sh-air.md](sh-air.md).

## Required verification

Changes to self-hosted Wasm emission must keep these suites green:

```text
cargo test -p sigil-runtime --test air_differential
cargo test -p sigil-runtime --test pipeline_differential
cargo test -p sigil-runtime --test preserve_pins
cargo test -p sigil-runtime --test claims_ledger
cargo test -p sigil-runtime --test selfhost_self_census
```

Pinned module bytes, certified source digests, and corpus floors may move only with a deliberate
compiler change and the corresponding evidence update.
