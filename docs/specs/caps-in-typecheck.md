# Capabilities in the self-hosted type checker

**Status:** Implemented for the bounded C0/C1 surface. The former C2-C12 roadmap is retired;
downstream capability soundness is owned by the Rust type checker, AIR capability pass, and
ownership verifier rather than a second speculative self-hosted implementation.

## Purpose

`selfhost/typecheck.sigil` must preserve enough capability type information for the self-hosted
ring, effect, and taint stages to classify typed values faithfully. C0 and C1 provide that bridge:

- `cap type` declarations populate a deterministic source-order capability table;
- capability types use `TC_T_CAP = 10`, matching the Rust differential projection;
- cap-typed lets, parameters, returns, and variable references retain the bare capability name;
- ordinary records and pre-capability fixtures remain byte-identical;
- unsupported deadline-bearing and operational capability forms remain outside this projection.

This is a type-stream contract, not a claim that the self-hosted type checker reproduces every
capability diagnostic.

## Authorities

- Self-hosted representation: `selfhost/typecheck.sigil`
- Rust type authority: `crates/sigil-compiler/src/type_check/`
- Differential evidence: `crates/sigil-runtime/tests/typecheck_differential.rs`
- Downstream capability proof: `crates/sigil-compiler/src/air_capability_v2/`
- Ownership proof: `crates/sigil-compiler/src/ownership.rs`

## Required invariants

1. Tag 10 is distinct from scalar, record, and sentinel tags.
2. Capability declaration order is deterministic.
3. A capability annotation never falls through to the unknown-record T046 path.
4. Cap values are represented only at the admitted let/parameter/return/reference sites.
5. Out-of-surface forms stay filtered symmetrically or fail closed; they never manufacture a
   plausible capability type record.
6. Every extension adds a reject/accept differential twin before entering the covered code set.

## Boundary

Restrict, split, draw, grant, declassification, aggregate-smuggling, actor messaging, solver
discharge, authority masks, and linear ownership are not reimplemented here. Their production
authorities remain the Rust passes listed above. A future self-hosted extension must be justified
by a consumer that needs the additional typed fact and must land with exact differential evidence;
it must not revive the retired roadmap as scaffolding.
