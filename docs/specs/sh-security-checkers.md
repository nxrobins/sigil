# Self-hosted security-checker contract

**Status:** Implemented as bounded differential projections. The production Rust passes remain
authoritative; the SIGIL implementations provide independent pressure on named subsets.

## Common differential model

The ring, effect, and taint tools compose the self-hosted lexer, parser, type checker, and one
security checker. Each emits a semicolon-delimited diagnostic-code stream. The Rust side parses,
resolves, type-checks, and invokes the production pass directly; the harness does not reimplement
the oracle.

Comparisons use sorted, deduplicated code sets on parse-clean fixtures. This establishes verdict
parity for the named corpus, not message/span parity, whole-language equivalence, or correctness of
both implementations.

Every suite includes reject and accept twins, non-stub coverage, deterministic repeated execution,
and a clean standard-library floor. The composed self-host pipeline treats an explicit unsupported
verdict as rejection rather than silently continuing.

## Ring checker

**Implementation:** `selfhost/ring_check.sigil`

**Compared codes:** R001 and R003.

- R001: outer-ring functions may not own capabilities. Direct capability parameters, returns, and
  bindings are covered; borrowed capabilities remain allowed.
- R003: inner-ring functions may not call declared extern functions. Declaring but not calling an
  extern is clean, and outer-ring extern calls are clean.

R002 is not part of the differential set because its candidate corpus is rejected earlier by T253.
R004 is enforced outside this self-host projection. Aggregate capability ownership, imported or
path-qualified extern calls, and closure lifting remain outside the declared ring corpus. These
limits do not weaken the production ring checker.

**Evidence:** `crates/sigil-runtime/tests/ring_check_differential.rs` and the SND-RING-001 row in
`docs/SOUNDNESS_MATRIX.md`.

## Effect checker

**Implementation:** `selfhost/effect_check.sigil`

**Compared codes:** E001 and E002.

- E001: a direct function call or `alloc` may not require an effect absent from the current
  declared/handled row.
- E002: an outer, non-trusted module may not handle `Unsafe`.

Effect names participate only when registered by a declaration or as the built-ins `FFI` and
`Unsafe`. An absent row and an explicit empty row both decode to the empty set. Handler effects are
scoped to the handler body and do not leak to siblings. Extern calls are walked for argument
effects but are not treated as ordinary function-row leakage.

The projection covers direct names and the curated handler surface. Method dispatch, qualified
calls, closure bodies, and the complete effect-handler diagnostic family remain production-only.

**Evidence:** `crates/sigil-runtime/tests/effect_check_differential.rs` and SND-EFFECT-001.

## Taint and constant-time checker

**Implementation:** `selfhost/taint_check.sigil`

**Compared codes:** T001, T020-T027, and T029-T032. T028 is actor-only and cannot be reached by a
type-clean fixture in this projection.

The covered corpus exercises scalar flow, per-field record flow, selected closure captures,
declassification, calls, returns, indexing, arithmetic, allocation sizes, and the algorithmic
constant-time restrictions represented by those codes. The self-host checker preserves the four
labels `Public < Internal < Secret < SecretCT` and mirrors the production ordering where multiple
covered diagnostics can fire.

The following shapes emit `SH_TAINT_UNSUPPORTED` and make the composed self-host pipeline reject:

- early exits whose continuation taint is not modeled;
- guarded matches and unsupported control-flow joins;
- actor handlers, spawn, and send/ask boundaries;
- closure values outside the covered capture cases; and
- unknown or unmapped syntax.

This explicit poison boundary is load-bearing. Production control-flow joins, actor boundaries,
and complete closure-value taint remain enforced by `taint_check.rs` but are not claimed as an
independent self-host model.

**Evidence:** `crates/sigil-runtime/tests/taint_check_differential.rs`,
`pipeline_differential.rs`, the `sh_taint_unsupported_shapes_are_explicit` canary, and the
SND-TAINT/constant-time rows in `docs/SOUNDNESS_MATRIX.md`.

## Change rule

Expanding a projection requires:

1. a production-oracle call over a parse- and type-clean fixture;
2. at least one firing reject case and one clean twin for each new code or shape;
3. a non-vacuity assertion proving the new path executed;
4. explicit poisoning for adjacent unsupported forms; and
5. updated soundness-matrix scope.

Stable SH-RING, SH-EFFECT, SH-TAINT, ET, and AG labels remain in executable test names where they
identify semantic cases. Git history retains the incremental design record; this document owns the
current contract.
