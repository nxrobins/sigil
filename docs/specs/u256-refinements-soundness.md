# `u256` refinement soundness

**Status:** Implemented. This document defines the current supported surface and the invariants
that prevent wide integer refinements from being narrowed or accepted without proof.

## Supported surface

Record declarations may refine a single `i64` or `u256` field with one comparison. A `u256`
record field supports:

- concrete values that fit `i64`;
- concrete values through `2^256 - 1`;
- literal bounds that fit `i64`; and
- literal bounds through `2^256 - 1`.

The six comparison operators are `<=`, `<`, `>=`, `>`, `==`, and `!=`. Record field reads retain
their refinement sidecar.

The wider language surface remains intentionally narrower:

- `i256` refinement fields are rejected with T212;
- a wide bound on an `i64` field is rejected with T213;
- cross-field refinements require `i64` on both sides;
- enum payload, function-parameter, and function-return refinements remain `i64`-only; and
- predicate subsumption involving a wide bound fails closed rather than narrowing the bound.

Symbolic values are accepted only when an existing supported refinement proves the required
predicate. Otherwise the normal T211, T215, T216, T224, or T225 path rejects the obligation.

## Representation

The parser stores integers wider than `i64` as four little-endian `u64` limbs. Refinement
discharge carries concrete values in:

```rust
enum RefValue {
    Narrow(i64),
    Wide([u64; 4]),
}
```

`type_check::refinement_value_for` is the only conversion from a typed literal to `RefValue`.
`z3_capability::encode_ref_value` is the only Z3 encoder:

- `Narrow` uses `Int::from_i64`;
- `Wide` uses `Int::from_str(u256_to_decimal(limbs))`.

The wide arm cannot reach an `i64` conversion by construction. `u256_to_decimal` is shared with
the lexer and pinned by known-answer and round-trip tests. The Z3 representation is one arbitrary-
precision integer numeral, not a 256-bit bitvector and not arithmetic assembled inside the query.

## Discharge

`type_check_v2` is the sole production refinement-discharge pipeline. Its pure collectors create
obligations without importing Z3; `type_check_v2/mod.rs` calls the three query primitives in
`z3_capability.rs`:

| Query | Supported values | Result |
| --- | --- | --- |
| Literal fit | narrow or wide concrete value; narrow or wide literal bound | Holds, Violated, or Timeout |
| Cross-field fit | two concrete `i64` values | Holds, Violated, or Timeout |
| Predicate subsumption | literal-bound `i64` predicates | Holds, Violated with optional counterexample, or Timeout |

Literal-fit queries bind `refine__value` to the exact supplied numeral and assert the negated
predicate. `Unsat` means the predicate holds; `Sat` means it is violated. Every query passes
through the fragment guard and deterministic solver cache. A fragment violation is an internal
compiler error, and `Unknown` is never converted to acceptance.

## Soundness invariants

1. **No narrowing.** A `Wide` value or bound never uses a low limb, `as i64`, or
   `Int::from_i64`. The source fence in `z3_guard_fences.rs` and the `2^64 <= 100` behavioral
   witness make truncation observable.
2. **One decimal encoder.** `lexer::u256_to_decimal` is the sole limbs-to-decimal conversion and
   is checked against external known answers.
3. **One wide Z3 encoder.** `encode_ref_value` creates exactly one `ANUM` numeral with
   `Int::from_str`. A permanent canary checks both fragment admission and magnitude at boundary
   values.
4. **Unsigned only.** Only `Type::U256` admits wide values or bounds. Signed `i256` does not reuse
   the unsigned interpretation.
5. **Fail closed outside the surface.** Unsupported symbolic, wide-subsumption, cross-field,
   parameter, return, and variant shapes reject; they do not skip an obligation.
6. **Honest solver-off certificates.** Solver-disabled builds record `solver_verified: false`.
   Runtime certificate gates do not present structural-only checking as a Z3 proof.

## Evidence

- `crates/sigil-compiler/tests/u256_refinements.rs` covers admission, Holds/Violated verdicts,
  narrow/wide combinations, wide field reads, and the truncation witness.
- `crates/sigil-compiler/tests/z3_guard_fences.rs` pins the non-narrowing source shape and the
  single `solver_verified` assignment.
- `crates/sigil-compiler/src/lexer.rs` contains decimal known-answer and round-trip tests.
- `crates/sigil-compiler/src/z3_capability.rs` contains the wide-numeral fragment and magnitude
  canary.
- `crates/sigil-compiler/tests/z3_corpus/78_u256_refinement_fail.sigil`,
  `79_u256_wide_refinement_fail.sigil`, and `80_u256_wide_refinement_pass.sigil` keep the paths in
  the solver corpus and workload snapshots.

## Change rule

Expanding the surface requires an exact representation, a fail-closed unsupported twin, a
known-violating witness, and fragment-guard coverage. In particular, symbolic `u256`, wide
subsumption, `i256`, or `BV<256>` support cannot reuse the current `i64` path or relax a guard
without replacement evidence.
