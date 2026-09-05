# Runtime Z3 Fragment Guard

**Status:** Implemented and required.

This document defines the runtime boundary that keeps every production Z3
query inside SIGIL's documented decidable fragment. The theory inventory and
proof live in [`../z3-theory-inventory.md`](../z3-theory-inventory.md).

## 1. Purpose

Review and static lints are useful but cannot prove that dynamically assembled
solver terms stay within a theory. The fragment guard inspects the assertions
that Z3 will actually decide. A query outside the contract is a compiler bug
and fails closed.

The guard covers both current query families:

- cached refinement queries built in `z3_capability`;
- cache-independent AIR capability queries built in `air_capability_v2`.

These are separate routing paths, not competing capability provers.

## 2. Enforcement model

Three layers make the boundary operational:

1. **Runtime guard:** walk every assertion immediately before a production
   solve and reject unsupported syntax.
2. **Lint and source fences:** prevent unsanctioned solver APIs, broad lint
   exemptions, and unguarded production checks.
3. **Required solver CI:** compile and exercise solver-gated code, the guard
   canaries, corpus, exactness manifest, and shadow checks.

No layer substitutes for another. The runtime guard is the semantic authority;
the other two keep its routing and coverage intact.

## 3. Guard contract

`z3_fragment_guard::check_fragment` is a pure function of a solver's assertion
set. It uses an iterative worklist and returns either a `FragmentReport` or the
first deterministic `FragmentViolation`.

It admits only:

- AST kinds `Numeral` and `App`;
- declaration kinds `EQ`, `NOT`, `LE`, `GE`, `LT`, `GT`, `ANUM`, `BAND`,
  `ULEQ`, `BNUM`, `TRUE`, `FALSE`, and arity-zero `UNINTERPRETED`;
- sorts `Bool`, `Int`, and exactly `BV<32>`.

It rejects:

- quantifiers and de Bruijn bound variables;
- operations not explicitly allowlisted;
- uninterpreted functions with positive arity;
- any other sort or bitvector width;
- an assertion containing both `Int` and `BV` subterms;
- assertion sets whose walk exceeds `NODE_CEILING` (100,000 nodes).

The declaration match defaults to rejection. New Z3 enum variants therefore
remain forbidden until deliberately inventoried.

`TRUE` and `FALSE` are admitted structural constants. The exactness manifest
pins them as the only allowed declaration kinds not currently observed in the
production corpus.

## 4. Wiring

### Cached refinement path

`z3_cache::check_cached_with_model` runs the guard before any L1 or L2 lookup,
then records the successful report. A cache miss reaches `fresh_check`, which
runs the guard again immediately before `.check()`. The second walk protects
against a callback adding assertions between lookup and solve.

Cache hits are still guarded and recorded. A rejected query performs no cache
lookup, statistics update, or write.

### AIR capability path

`air_capability_v2::check_direct` runs the guard, records the report, and calls
`.check()` in one function. This path intentionally bypasses verdict caching so
capability enforcement is independent of cache state.

### Observation boundary

`check_fragment` has no global side effects. Only production chokepoints call
`record_observations`. Canary tests can therefore construct invalid formulas
without contaminating the corpus exactness manifest.

## 5. Failure semantics

`FragmentViolation` distinguishes disallowed AST kinds, operations,
uninterpreted functions, sorts, bitvector widths, mixed theories, and oversized
queries. Error renderings are truncated; `TooLarge` carries no formula text.

AIR capability verification converts a violation to error diagnostic `C005`.
Refinement builders construct queries from closed compiler grammars, so a
violation there is an `ICE [C005]` panic. Neither path may accept a program
after a guard failure.

`SatResult::Unknown` is separate from a fragment violation and also fails
closed through `C004` or a refinement timeout diagnostic.

## 6. Lint fence

Workspace `clippy.toml` disallows:

- Z3 quantifier constructors;
- direct `Solver::check` and `check_assumptions`;
- optimize checks;
- model, proof, and unsat-core reads outside sanctioned handling.

Expression-level `#[allow(clippy::disallowed_methods)]` uses are permitted only
at the exact census pinned in `z3_guard_fences.rs`. File- or module-scoped
allows are forbidden. The sanctioned sites are:

- cache fresh evaluation and cache-hit verification;
- refinement model extraction and the raw rlimit self-test;
- AIR capability `check_direct`;
- the quantifier canary;
- the runtime `Cap<Z3>` shim in its separate trust domain.

Any new carve-out requires a local rationale and synchronized census update.

## 7. Tests and source fences

The guard suite includes exact negative canaries for:

| Input | Required rejection |
|---|---|
| Quantifier | Disallowed AST kind |
| Real comparison | Disallowed sort or preceding deterministic violation |
| Array select | Disallowed operation `SELECT` |
| Arity-one uninterpreted function | Uninterpreted function |
| `BV<16>` | Non-32-bit bitvector |
| Mixed integer/bitvector formula | Deterministic disallowed operation or mixed-theory rejection |
| Formula beyond 100,000 visited nodes | Too large |

Positive tests cover each production query family. Additional fences assert:

- every production `.check()` is guard-adjacent;
- no compiler production code catches panics;
- the guard imports only `std` and `z3`;
- the expression-level lint carve-out census is exact;
- the four AIR dispatch sites have theory comments;
- observed operation and sort sets equal the hand-written inventory;
- the allowlist equals observed operations plus `TRUE` and `FALSE`;
- `solver_verified` has one assignment authority.

The exactness test resets observations, drives the whole Z3 corpus, and compares
set equality. A newly observed operation requires a documentation-first update
and a fixture; a subset assertion is not an acceptable replacement.

## 8. CI solver lane

The required solver job installs the repository-pinned Z3 build and checksum,
then runs solver-feature clippy and tests. It must not be allowed to continue on
error. Solver-adjacent changes are not mergeable while this lane is red.

The lane runs with `SIGIL_Z3_CACHE_VERIFY=always` so cache hits are rechecked.
The ordinary non-solver lanes still run the feature-independent source fences.

## 9. Ownership

`z3_fragment_guard.rs` remains isolated from compiler internals so both query
families can call it without creating dependency cycles. It may import only
`std` and `z3` in production code.

The theory inventory owns the allowed semantic surface. The guard owns runtime
enforcement. `z3_guard_fences.rs` owns routing and exemption census checks.
`z3_corpus.rs` owns observed-fragment equality and AIR dispatch counts.

## 10. Limits and failure policy

- The guard makes no general Z3 performance claim. Its cost bound is the
  100,000-node iterative walk ceiling.
- It does not prove that a formula expresses the intended program semantics;
  domain tests and shadow checks own that property.
- It does not inspect solver internals or trust model provenance.
- Cache integrity is separately protected by canonical keys and hit
  verification; guard-before-lookup protects the fragment boundary.
- A Z3 dependency update must keep the pinned CI installation, Rust binding,
  allowlist, canaries, and exactness manifest synchronized.
- Any ambiguity resolves toward conservative rejection, never unverified
  acceptance.

## 11. Non-goals

The guard does not add new theories, support user-authored SMT, replace the
solver cache, merge the two query routers, or alter diagnostics for valid
programs. Expanding the fragment requires a separate soundness change with an
updated proof.

## Cross-references

- [`../z3-theory-inventory.md`](../z3-theory-inventory.md): operation inventory,
  decidability proof, solver-off witness, and update protocol.
- [`../../crates/sigil-compiler/src/z3_fragment_guard.rs`](../../crates/sigil-compiler/src/z3_fragment_guard.rs): implementation.
- [`../../crates/sigil-compiler/tests/z3_guard_fences.rs`](../../crates/sigil-compiler/tests/z3_guard_fences.rs): source fences.
- [`../../crates/sigil-compiler/tests/z3_fragment_guard_canaries.rs`](../../crates/sigil-compiler/tests/z3_fragment_guard_canaries.rs): runtime canaries.
- [`../../crates/sigil-compiler/tests/z3_corpus.rs`](../../crates/sigil-compiler/tests/z3_corpus.rs): corpus and exactness manifest.
