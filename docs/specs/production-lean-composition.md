# Production Lean composition profile

**Profile:** `PLC-2026-09-07`  
**Status:** enforced for the shipped production Lean checker composition boundary.  
**Machine gate:** `crates/sigil-runtime/tests/production_lean_composition_profile.rs`.  
**Row manifest:** [`production-lean-composition.tsv`](production-lean-composition.tsv).

This profile defines the production-to-Lean correspondence for the shipped checker-composition boundary, without expanding the public guarantee past the shipped evidence. The relation starts after Rust parsing, name resolution, type checking, and desugaring have produced the typed program, resolved AIR, authority registry, and compiler context. It ends at the statically linked Lean verifier's accepted CSIR model-9 decision and the schema-v9 report that certificates and runtime gates re-derive.

It is not a whole-language adequacy theorem. Rust source-to-CSIR projection, security-only SSA versioning, phi placement, type-proved unreachable-edge facts, Lean native generation/runtime, Wasm emission, Wasmtime execution, actor scheduling, platform behavior, and hardware timing remain trusted assumptions tracked by SR-017. The old Rust/Z3 gates remain mandatory until SR-017's exit criteria are satisfied by tagged evidence.

```pins
PIN_PLC_PROFILE_ROWS = 10
PIN_PLC_THEOREM_REFS = 39
PIN_PLC_POSITIVE_CANARIES = 25
PIN_PLC_NEGATIVE_CANARIES = 39
PIN_PLC_GATE_TOKENS = 30
```

## Abstraction relation

For a production compilation tuple `(typed, air, authority_registry, context, csir9, report)`, the relation `PLC-2026-09-07` holds only when all of these conditions hold:

1. `typed` is the pre-desugar typed program supplied to `formal::verify_with_context`, and `air` is the resolved post-desugar AIR supplied to the same call at the shared compiler choke point.
2. The compiler encodes exactly one model-9 CSIR envelope. Its retained-v8 prefix contains the semantic manifest, function/value/block/instruction/operand records, v6 obligation records, taint seeds and edges, capability origins and authority transitions, slot meets, path-affine markers, quantity cells, guard links, sinks, CT uses, and release stages.
3. The retained-v8 semantic suffix supplies declarations only: labels, flow contracts, policy classes, capability type identities, refinement facts, and runtime guard declarations. It does not carry Rust-computed taint verdicts, capability-legitimacy bits, final authority masks, ownership verdicts, or relational policy certificates.
4. The model-9 envelope adds host, actor, FFI, and function-root declarations. The declaration decoder is non-authorizing; only the production `OccurrenceKernel.exportedVerify` zero verdict can construct `FormalSecurityReport`.
5. Certificates and runtime gates compare a freshly re-derived schema-v9 formal report, so source, CSIR bytes, checker sources, host profile, or model drift fails closed before execution.
6. A production-facing theorem obligation is public only if the row manifest names its Lean theorem, at least one positive canary, at least one negative canary, and the production gate tokens that keep the checker on the shipped path.

## Composition rule

Each manifest row is one composition obligation. The `production_abstraction` cell names the production state that is related to the Lean calculus. `lean_theorems` must name the exact public theorem census entries in `proofs/lean/axiom-targets.txt`. `positive_canaries` must be executable tests that still accept the intended good path, and `negative_canaries` must be executable tests that reject a drift, mutant, missing certificate field, or unsupported boundary. `gate_tokens` must appear in source, CI, or release-evidence files that are shipped with the compiler.

Changing a checker, CSIR constructor, policy class, certificate field, or public theorem obligation changes this profile. The same review must update the row manifest, the evidence pins, the soundness matrix, and the residual-risk register.

## Boundary retained in SR-017

### APC-1: AIR dataflow transfer validation

**Status:** implemented; required before a production formal report can be constructed.

**Date:** 2026-09-07.

**Authors:** SIGIL contributors.

APC-1 adds an independently implemented validator over resolved AIR, the SSA plan as an
untrusted witness, and the emitted CSIR instruction records. It checks the version inventory,
fresh definitions, per-statement read mappings, block-entry mappings, terminator targets, and
predecessor transfers. A transfer either keeps the same version or must appear as an actual
operand of the destination phi. The validator covers each AIR statement constructor in an
exhaustive match and follows CFG edges independently of the producer's reaching-definition
solver. It rejects disagreement and budget exhaustion; there is no skip or fallback path.

The compiler then passes the final model-9 bytes and the extracted non-identity transfers to
the linked `Projection.exportedValidate` kernel. Its result validates those transfers only;
the existing model-9 security verifier must also accept before report construction. The
certificate has a version word of 1, a count word, and five little-endian u32 words per transfer:
function, source version, target version, phi instruction ID, and operand record ID. Framing is
exact, with at most 1,000,000 transfers; unknown versions, truncation, excess records, or invalid
references reject. The Rust extraction has a whole-program budget of 16,000,000 charged work
units (record/variable visits and transfers), including block-environment construction.

`Combined.Projection.accepted_bytes_preserve_paths` proves that acceptance gives a decoded
program and certificate for which every finite extracted transfer path is a path through actual
CSIR phi dependencies, including graphs with cycles. `checked_path_rank_monotone` additionally
shows that any rank assignment closed under those dependencies preserves the extracted paths.
That closure is an explicit premise; this theorem does not itself establish a Public or SecretCT
execution guarantee. The kernel and proof sources are included in the checker fingerprint and
the full theorem/axiom census. The manifest row links acceptance, mutation, and framing tests.

Remaining premises are substantive: correctness and completeness of the Rust AIR read/write
classification and obligation extraction, the fixed-definition/dominance assumptions of valid
AIR, source typing/desugaring, and the semantic justification of unreachable-path annotations.
Checking an annotation against an emitted trap does not prove the path unreachable. APC-1 also
does not validate opcode semantics, literal payloads, label/policy metadata, the AIR scratch-state
abstraction, or Wasm behavior. Local reads are compared with emitted in-memory records; their
serialization remains trusted, while the Lean transfer checks use the final serialized bytes.
These limits remain in SR-017. Passing APC-1 is a bounded correspondence result, not closure of
the source-to-runtime proof project or eligibility to retire the existing Rust/Z3 gates.

`PLC-2026-09-07` closes the production checker/composition boundary for the current CSIR verifier stack. It does not prove that every Rust front-end transformation implements the source language semantics, that generated Lean native code is free of backend/runtime bugs, that emitted Wasm preserves the abstract machine, or that hosts and hardware preserve timing properties. Those remain explicit trusted assumptions under SR-017, and the v9 release evidence stays non-retirement-eligible.
