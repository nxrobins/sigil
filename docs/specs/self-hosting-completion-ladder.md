# SIGIL Self-Hosting Completion Record

**Status:** Implemented and current. The rung-driving backlog is retired; every achievable
self-hosting rung shipped by 2026-07-08. This file is now the canonical map of authorities,
evidence, and the remaining soundness boundary.

## Scope

SIGIL maintains a self-hosted compiler projection in `selfhost/` and compares it with the Rust
compiler. The projection covers the supported front end, verification shadows, AIR transforms,
Wasm emission, and the composed `sh_compile` pipeline. It is a differential implementation and
must fail closed outside its declared surface.

The historical completion loop and per-PR rung statuses are no longer authorities. Stable slice
labels remain in test names where they identify semantic cases, but their implementation journals
are retired.

## Authorities and evidence

| Stage | Self-hosted authority | Rust authority | Primary evidence |
| --- | --- | --- | --- |
| Lexing | `selfhost/lexer.sigil` | `lexer.rs` | `lexer_differential.rs` |
| Parsing | `selfhost/parser.sigil` | `parser.rs` | `parser_differential.rs`; [sh-name-resolution.md](sh-name-resolution.md) |
| Type checking | `selfhost/typecheck.sigil` | `type_check/` | `typecheck_differential.rs` |
| Name resolution | `selfhost/name_resolution.sigil` | `name_resolution.rs` | `name_resolution_differential.rs`; [sh-name-resolution.md](sh-name-resolution.md) |
| Ring checks | `selfhost/ring_check.sigil` | `ring_check.rs` | `ring_check_differential.rs`; [sh-security-checkers.md](sh-security-checkers.md) |
| Effect checks | `selfhost/effect_check.sigil` | `effect_check.rs` | `effect_check_differential.rs`; [sh-security-checkers.md](sh-security-checkers.md) |
| Taint checks | `selfhost/taint_check.sigil` | `taint_check.rs` | `taint_check_differential.rs`; [sh-security-checkers.md](sh-security-checkers.md) |
| Capability checks | `selfhost/cap_check.sigil` | `air_capability_v2/` | `cap_workload_differential.rs` |
| Ownership checks | `selfhost/own_check.sigil` | `ownership.rs` | `own_check_differential.rs` |
| Monomorphization | `selfhost/monomorph.sigil` | compiler monomorphization | `monomorph_differential.rs` |
| AIR through Wasm | `selfhost/air.sigil` | `air.rs`, `memory.rs`, `fuel.rs`, `wasm.rs` | `air_differential.rs`; [sh-wasm.md](sh-wasm.md) |
| Composition | `selfhost/pipeline.sigil` | compiler stage chain | `pipeline_differential.rs` |

The canonical AIR implementation and its exact/poison case disposition are documented in
[sh-air.md](sh-air.md), with final module invariants in [sh-wasm.md](sh-wasm.md). Parsing and name resolution are bounded in
[sh-name-resolution.md](sh-name-resolution.md), while the security pass projections are bounded in
[sh-security-checkers.md](sh-security-checkers.md). Generic-enum emission and executable closure are current in
[ag-6-full-emit.md](ag-6-full-emit.md) and
[stage3-thompson-closure.md](stage3-thompson-closure.md).

## Evidence accounting

`crates/sigil-runtime/tests/support/preservation_manifest.rs` names required checks by semantic
case. `preserve_pins.rs` validates that manifest, the AIR case manifest, claim coverage, and the
required workflow contexts. Evidence is not measured by the number of Rust `#[test]` functions,
so parameterization and test-body compression cannot silently reduce the covered corpus.

Changes must preserve:

- stable case labels and claim tags;
- positive and negative differential twins;
- explicit poison at unsupported boundaries;
- deterministic output and byte equality where exact parity is claimed;
- the corpus and claim floors enforced by `preserve_pins`, `claims_ledger`, and the suite-local
  manifests.

## Current boundary

The committed certified compiler source, including its real driver, emits byte-identically through
the self-hosted and Rust-oracle paths. An executable self-reproducing library fixed point and a
trusting-trust discrimination canary also ship. Those claims are bounded exactly in
[stage3-thompson-closure.md](stage3-thompson-closure.md): the executable proof retains fixed entry
glue, and the Rust oracle remains the comparison authority.

This does **not** claim universal source coverage or oracle independence. Unsupported forms must
remain rejected or poisoned until a new exact surface lands with differential evidence.

## Historical provenance

The completed arc landed incrementally: lexer/parser/type-checking, multi-module name resolution,
ring/effect/taint shadows, AIR and capability/ownership checks, memory/fuel/Wasm emission,
`sh_compile`, monomorphization, generic-enum full emit, and executable closure. Git history retains
the per-slice PR record; this document intentionally does not duplicate mutable counts or branch
state.

## Required verification

At minimum, changes to the self-hosted chain run the affected differential suite plus:

```text
cargo test -p sigil-runtime --test pipeline_differential
cargo test -p sigil-runtime --test preserve_pins
cargo test -p sigil-runtime --test claims_ledger
cargo test -p sigil-runtime --test selfhost_self_census
```
