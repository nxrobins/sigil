# Self-hosted AIR authority

**Status:** Implemented and current. This document replaces the historical SH-AIR slice plans.

## Purpose

`selfhost/air.sigil` is the self-hosted lowering authority used to compare SIGIL's compiler
pipeline with the Rust oracle. It builds operand-exact AIR, applies the memory and fuel passes,
and emits a complete Wasm module. Unsupported forms must be explicit poison; they must never
produce plausible divergent bytes.

The Rust authorities are:

- `crates/sigil-compiler/src/air.rs`
- `crates/sigil-compiler/src/memory.rs`
- `crates/sigil-compiler/src/fuel.rs`
- `crates/sigil-compiler/src/wasm.rs`

## Single implementation path

`ai_encode_cv_impl` is the only self-hosted implementation walk. Its public views are:

| Entry point | Stage | Contract |
| --- | --- | --- |
| `ai_encode_cv` | pre-memory AIR | Operand-exact compact projection |
| `ai_encode_cv_mem` | post-memory AIR | Exact AIR after allocation expansion |
| `ai_encode_cv_fuel` | post-fuel AIR | Exact AIR after fuel insertion |
| `ai_encode_wasm` | final module | Whole-module hex, or `!!` on poison |
| `ai_wasm_poison_census` | final diagnostics | Names of functions that poisoned emission |

The former `ai_encode` skeleton projection and `ai_encode_body` statement-kind projection were
independent partial implementations of the same lowering rules. They are retired. Their useful
evidence now runs through the exact AIR or final Wasm path rather than maintaining three lowering
authorities.

## Evidence accounting

`crates/sigil-runtime/tests/air_differential.rs` owns the semantic cases. The shared manifest in
`tests/support/air_case_manifest.rs` pins:

- at least 384 named corpus cases;
- 23 required semantic checks spanning exact AIR, memory, fuel, Wasm, execution, determinism,
  stdlib coverage, and negative canaries.

The preservation gate counts these cases and named checks, not Rust `#[test]` functions. Repacking
or parameterizing tests therefore cannot silently erase evidence.

The 98 labels from the retired projections remain in `RETIRED_LANE_CORPUS`. The permanent
`retired_lane_cases_are_exact_or_poisoned` check records their case-by-case disposition:

- 79 single-ring cases are final-Wasm byte exact;
- `multi-module free fns` and `multi-module impl` are outer-ring AIR exact;
- 17 explicitly listed boundary cases poison, covering unsupported string-match, closure, and
  stateful-actor forms.

The disposition lists are ratchets. A case may move from poison to exact when support is added,
but a new silent divergence fails before either list comparison.

## Soundness boundaries

- Stateful actor handlers and initializers currently poison final self-hosted Wasm emission. The
  parser preserves actor fields, but the exact emitter does not lower the oracle's implicit state
  pointer loads. Failing closed is required until that lowering is implemented exactly.
- Closures outside the exact surface poison rather than disappearing.
- Unsupported expression, statement, memory, fuel, or Wasm forms taint the owning function and
  force `ai_encode_wasm` to return `!!` for the module.
- Multi-module outer-ring programs are compared at the exact AIR boundary when the oracle does not
  expose a single inner Wasm module.

## Required verification

Changes to this authority must keep these suites green:

```text
cargo test -p sigil-runtime --test air_differential
cargo test -p sigil-runtime --test pipeline_differential
cargo test -p sigil-runtime --test preserve_pins
cargo test -p sigil-runtime --test claims_ledger
cargo test -p sigil-runtime --test selfhost_self_census
```

Certified source-size, module-size, and digest pins may move only when the compiler artifact
changes deliberately, with all related pins updated together.
