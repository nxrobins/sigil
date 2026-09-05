# Z3 Theory Inventory and Decidability Contract

**Status:** Active. This document describes the solver queries emitted by the
current compiler. It is an inventory and maintenance contract, not a delivery
journal.

SIGIL uses Z3 for two query families:

- AIR capability verification in `air_capability_v2`.
- Refinement discharge in `z3_capability` through `type_check_v2`.

The runtime fragment guard, source fences, exactness manifest, and solver CI
lane keep the implementation within the fragment documented here.

## 1. Solver configuration

Both query families use fresh Z3 contexts and deterministic `rlimit` budgets,
never wall-clock timeouts. SIGIL does not call `set_logic`; the builders and
fragment guard constrain the effective logic.

| Policy | Value | Owner |
|---|---:|---|
| Per-query `rlimit` | 1,000,000 | `z3_capability::Z3_RLIMIT`, `air_capability_v2::AIR_CAP_Z3_RLIMIT` |
| Per-program capability budget | 50,000,000 | `air_capability_v2::AIR_CAP_Z3_PROGRAM_RLIMIT` |

AIR capability verification owns one solver per program and isolates each
function with `push`/`pop`. It measures cumulative solver consumption and emits
`C004` when the program budget is exceeded. Refinement discharge owns one
solver per query and uses the verdict cache described in `z3_cache.rs`.

`SatResult::Unknown` is never interpreted as proof. Capability queries emit
`C004`; refinement queries return a timeout verdict that becomes the relevant
T-code diagnostic.

## 2. The four capability dispatch sites

The sole AIR capability prover calls Z3 at exactly four logical sites. Every
site routes through `air_capability_v2::check_direct`, which runs the fragment
guard immediately before `Solver::check`.

| # | Site | Query | Fragment |
|---:|---|---|---|
| 1 | Call, spawn, and serialization arguments | `(actual & required) != required`; SAT means authority may be insufficient | QF_BV<32> |
| 2 | Returned capability | Same authority counterexample query | QF_BV<32> |
| 3 | End-of-function consistency | All legitimacy, fuel, and authority constraints; UNSAT means inconsistent provenance | Disjoint QF_BV<32> and QF_LIA assertions plus Bool |
| 4 | Capability legitimacy | `not legitimate`; SAT means the value may be forged | Propositional Bool |

`z3_corpus::production_solver_check_count_matches_inventory` pins the count at
four. `every_solver_check_has_theory_comment` requires each dispatch to carry a
nearby `// theory:` annotation.

Refinement checks are separate from this count. They use the cached
`z3_cache::fresh_check` chokepoint and are inventoried in section 6a.

## 3. Operation and sort inventory

The runtime allowlist contains these declaration kinds:

| Family | Declaration kinds | Use |
|---|---|---|
| Shared | `EQ`, `NOT`, `UNINTERPRETED` with arity 0 | Equalities, negation, and free constants |
| Integer | `LE`, `GE`, `LT`, `GT`, `ANUM` | Fuel, split amounts, and refinements |
| Bitvector | `BAND`, `ULEQ`, `BNUM` | 32-bit authority masks |
| Structural constants | `TRUE`, `FALSE` | Admitted Bool constants |

The corpus exactness manifest pins the observed production set to
`ANUM`, `BAND`, `BNUM`, `EQ`, `GE`, `GT`, `LE`, `LT`, `NOT`, `ULEQ`, and
`UNINTERPRETED`. It pins the allowed set to that observed set plus only
`TRUE` and `FALSE`.

The only allowed sorts are:

- `Bool`
- `Int`
- `BV` of width exactly 32

Capability assertions are built from the following semantic forms. Source line
numbers are deliberately omitted because the source fences bind the live code
more reliably than line-number links.

| Constraint family | Form |
|---|---|
| Legitimate sources | `legitimate` |
| Forged record values | `not legitimate` |
| Restrict/split propagation | `dst_legitimate == src_legitimate` |
| Restrict attenuation | `dst_perms <= src_perms` |
| Fuel conservation | `dst_fuel == split_amount`, `src_fuel >= split_amount`, non-negativity |
| Authority restriction | `dst_auth == src_auth & mask`, `dst_auth <=u src_auth` |
| Authority propagation | `dst_auth == src_auth` |
| Slot meet | `dst_auth == auth_1 & ... & auth_n` |
| Default authority | `auth == full_mask` |
| Sink counterexample | `not ((actual & required) == required)` |

## 4. Decidability proof

The emitted formulas are in three decidable fragments:

- **QF_BV<32>.** Fixed-width bitvectors reduce to finite Boolean formulas.
  SIGIL uses equality, bitwise AND, unsigned less-than-or-equal, and literals.
- **QF_LIA.** Quantifier-free linear integer arithmetic is decidable. SIGIL
  uses equality and ordered comparisons against integer variables and
  numerals. It does not emit integer multiplication or nonlinear terms.
- **Propositional Bool.** SIGIL uses equality, negation, constants, and free
  Bool variables.

The capability solver can contain both integer and bitvector assertions, but
their signatures are disjoint. No single assertion may contain both `Int` and
`BV` subterms. Bool may serve as the propositional result sort for either
family. The fragment guard rejects a mixed assertion.

There are no explicit quantifiers, bound variables, uninterpreted functions,
arrays, reals, datatypes, bitvectors of other widths, or conversion operators.
Arity-zero uninterpreted declarations are free constants and are allowed.

## 5. Mechanical enforcement

The theory claim has three enforcement layers:

1. `z3_fragment_guard::check_fragment` iteratively walks every assertion at
   every production check. It defaults to rejection, enforces the operation and
   sort allowlists, rejects mixed `Int`/`BV` assertions, and stops after 100,000
   visited nodes.
2. `clippy.toml` forbids quantifier constructors, direct solver checks,
   assumption checks, optimize checks, and proof/model access outside a pinned
   expression-level carve-out census.
3. The required solver CI job runs clippy with the solver feature, guard
   canaries, the corpus, exactness manifests, shadow comparisons, and runtime
   solver proofs against the pinned Z3 installation.

Production check routing is also source-fenced:

- Cached refinement checks run the guard before lookup and again inside
  `z3_cache::fresh_check` on a real solve.
- AIR capability checks run the guard inside `check_direct` immediately before
  the real solve and intentionally bypass the cache.
- An unguarded production `.check()` fails `z3_guard_fences`.
- `catch_unwind` is forbidden in compiler production code so refinement guard
  failures cannot be swallowed.

The exactness manifest records production observations only. Canary queries do
not feed the accumulator.

## 5a. Solver-off builds and the certificate witness

The `solver` Cargo feature is optional. Without it, structural type,
capability, ownership, taint, ring, and effect checks still run, but Z3-backed
AIR capability and refinement discharge do not.

| Verification | Solver on | Solver off |
|---|---|---|
| Structural checks | Runs | Runs |
| AIR capability proof | Runs | Skipped |
| Refinement proof | Runs | Skipped or fail-closed where explicitly required |
| Fragment guard | Runs for every query | No query exists |

Certificate schema v8 introduced this distinction; schema v9 retains it as
`capability.solver_verified`. The value is true only when the solver-backed
capability path ran. It is deterministic for a build configuration and remains
part of certificate equality. `z3_guard_fences` pins its assignment to the
single `capability::verify` chokepoint.

## 6. Invalidation conditions

The proof in section 4 must be revisited before any of these changes land:

1. A new declaration kind or sort is emitted.
2. A bitvector width other than 32 is admitted, or the 32-authority bound is
   relaxed.
3. One assertion mixes integer and bitvector terms.
4. A quantifier, bound variable, or positive-arity uninterpreted function is
   introduced.
5. A production solver call bypasses `fresh_check` or `check_direct`.
6. An `Unknown` or fragment violation can produce acceptance.
7. Cache keys stop representing the complete canonical assertion set.

The runtime guard makes most such changes fail closed, but that does not remove
the obligation to update the theory proof and tests.

## 6a. Refinement query family

Refinement discharge uses QF_LIA and six comparison operators: `<`, `<=`,
`>`, `>=`, `==`, and `!=` (`!=` lowers to negated equality).

| Query | Encoding | Meaning of UNSAT |
|---|---|---|
| Literal fit | `value == supplied` and `not predicate(value)` | The supplied value satisfies the predicate |
| Cross-field fit | Bind `lhs` and `rhs`, then assert `not predicate(lhs, rhs)` | The concrete field pair satisfies the predicate |
| Predicate subsumption | `supplied(x)` and `not required(x)` | Every supplied value satisfies the required predicate |

Literal-fit queries use the free name `refine__value`; cross-field queries use
`refine__lhs` and `refine__rhs`; subsumption uses `refine__x`. Distinct names
keep canonical cache keys separated by query family.

Narrow values use `Int::from_i64`. Wide `u256` construction values and bounds
use one arbitrary-precision Z3 numeral built from the canonical decimal text;
they are never narrowed to `i64` or reconstructed with arithmetic operations.
Wide-bound subsumption is not encoded by the current literal subsumption path
and fails closed as non-subsuming.

Subsumption SAT results may carry an `i64` counterexample. The model is read
only during a fresh solve, then the optional counterexample is cached with the
verdict. A cache hit never reads a model from a solver that did not run.

The pure `type_check_v2` collector owns obligation discovery. Its single
discharge boundary routes literal, cross-field, and subsumption obligations to
these query builders. Unsupported symbolic cases produce diagnostics rather
than silently passing as proven.

## 6c. Flow-sensitive narrowing

An `if` condition narrows a variable only when its syntax is a bare identifier
compared with an integer literal, in either order. Reversed comparisons are
normalized (`5 < x` becomes `x > 5`). The then arm receives the predicate and
the else arm receives its logical comparison negation.

Nested narrowing for the same variable composes the nearest existing clauses
with the new clause. Narrowings for different variables remain visible through
the top-down frame lookup. The stack is lexical and is popped after each arm.

This mechanism is intentionally narrower than a general path-sensitive proof
system. It does not infer facts from identifier-to-identifier comparisons,
calls, loops, or arbitrary Boolean expressions. Reassignment of a narrowed
variable inside an arm does not currently invalidate its frame; callers must
not treat this syntactic narrowing layer as an independent runtime guarantee.
The limitation is explicit in `type_check/statements.rs` and covered as
residual soundness work rather than hidden in historical prose.

## 7. Update protocol

A solver change is complete only when all applicable items move together:

1. Update the semantic inventory and decidability argument in this document.
2. Update the fragment guard allowlist and its positive/negative canaries.
3. Update the hand-written operation/sort manifest in `z3_corpus.rs`.
4. Add a corpus fixture that exercises every newly observed operation or sort.
5. Update the four-site count and theory-comment fence if capability dispatch
   changes.
6. Update the clippy disallowed-method list and carve-out census if routing
   changes.
7. Run the solver CI lane with cache verification forced to `always`.

Do not weaken equality checks to subset checks. An allowed but unobserved
operation is unnecessary authority and must be removed or exercised.

## Appendix A. Certificate fingerprint canonicalization

Current certificates use `algorithm = "sha2-256"`, a lowercase 64-character
SHA-256 digest, and the exact hashed byte count.

WASM fingerprints hash the emitted module bytes directly. Inner and optional
outer modules have independent fingerprints.

Schema v7 and later source fingerprints hash a canonical framed source set:

1. Sort `(source_name, source_text)` pairs by UTF-8 source-name bytes using
   Rust `str::cmp`.
2. For each pair, append `NUL + name bytes + NUL + source bytes`.
3. SHA-256 the complete concatenation and record its length.

Single-file compilation is the same algorithm with one pair. Source names and
source text cannot contain NUL, so the framing is unambiguous. Golden tests in
`diagnostics/certificate.rs` pin framing, ordering, mutation sensitivity, empty
input behavior, and standard SHA-256 vectors.

Compatibility readers may parse older certificate schemas, but gating uses the
current schema and algorithm requirements.

## §M. Multi-file source canonicalization

`compile_project` binds a certificate to the complete compilation source set,
not only the primary module. Canonical name sorting makes the fingerprint
independent of caller argument order, while framing makes file boundaries and
names part of the hash. Changing any source name or byte changes the source
fingerprint.
