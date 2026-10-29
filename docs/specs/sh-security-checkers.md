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
type-clean fixture in this projection. T033 (CT018, `str` content compare) and T034 (CT008,
`@SecretCT` shift amount) are oracle-only: the shadow has neither rule, and the differential
filters both sides to the compared set, so the shadow lags the oracle on those two rather than
disagreeing with it.

The covered corpus exercises scalar flow, per-field record flow, selected closure captures,
declassification, calls, returns, indexing, arithmetic, allocation sizes, the algorithmic
constant-time restrictions represented by those codes, and, since SHP-5a, production's
control-flow join model (branch and arm merges, `break`/`continue`/`return` divergence, the
continuation taint, block shadow restores, the loop-head fixpoint) and its M6 region model
(`alloc` regions, aliases through `+`/`-` chains, raw stores through any operand), and, since
SHP-5c-1, the `split`/`draw` quantity rule and production's intraprocedural heap floors, and,
since SHP-5c-2, its call-site summaries (below).
Nonpublic bindings under control flow are therefore checked, not refused; the join model is
pinned exact against the oracle on hand-written fixtures and on a generated surface
(`joinmodel_surface_agrees_exactly`), the floors on a reject and a clean twin per rule. The
self-host checker preserves the four labels
`Public < Internal < Secret < SecretCT` and mirrors the production ordering where multiple
covered diagnostics can fire.

The following shapes emit `SH_TAINT_UNSUPPORTED` and make the composed self-host pipeline reject:

- a tuple let whose value carries a nonpublic pc;
- guarded matches;
- actor handlers, spawn, and send/ask boundaries;
- closure values outside the covered capture cases;
- a function naming more than 62 `alloc` regions (the region mask's width);
- a type alias, and any shape the heap-floor typing cannot classify at a non-public label
  (SHP-5c-1, below);
- a call whose callee the shadow cannot name, or whose summary carries a fact its typing
  cannot decide, while a label makes the summaries live (SHP-5c-2, below);
- a region body outside the scalar-only rule that stands in for production's escape lattice
  (SHP-5c-3, below); and
- unknown or unmapped syntax.

This explicit poison boundary is load-bearing. Actor boundaries and complete closure-value
taint remain enforced by `taint_check.rs` but are not claimed as an independent self-host
model.

Since SHP-5c-1 the shadow reads the amount of a `split` or `draw` (`@SecretCT` is T027, any
other non-public label T001; the capability itself is `@Public`, as are `restrict` and `mint`)
and carries production's intraprocedural heap floors: a function's raw-load and typed-read
floors, monotone and path-insensitive, raised by an extern call or a callee whose effect row
names FFI (S1), by a heap-resident value at a non-public label — a parameter at entry, any
materialisation thereafter (S2) — by a raw store at the join of its operands and the pc (S4,
S6) and by a projected-place write and its index taint (S6, S7), and joined into every raw load
and every typed read (an element, field or slice projection, a `?`, an intrinsic, a heap-typed
local, a `str` literal or f-string: S11). Production keys two of those rules on types; the
shadow recovers them from syntax (`tt_edesc`, a type descriptor per binding and expression)
and refuses, rather than guesses, what it cannot classify wherever a non-public label would
make a floor rule read it: a type alias (refused outright), a generic record's field, a call to
a function the program does not declare, an expression over a borrowed operand. At `@Public`
the typing is inert, so an all-public program — the self-compile — is neither typed nor
refused.

Since SHP-5c-2 the shadow carries production's call-site summaries. Every fn and impl-method
row of its table holds the summary of its body — whether a call to it can have written
linear memory at an existing address (a raw store, a slot write, a projected-place
assignment), built a heap-resident value into fresh cells, read memory raw or typed; the
bound on the labels it mints itself (every annotation in it, `@Internal` if it calls the
host); and the parameter slots a raw write reachable from it can go through — a syntactic
scan of the body (its rooted-slot map a fixpoint, as production's) closed over the call
graph within production's bound. A call site then joins the floors the callee reads into
its result (S8), raises the caller's floors by what the callee writes at the site's taint
joined with the callee's bound (S5) and taints the regions of the arguments it writes
through (S5, region side); a lowered method call — a user type's or the stdlib's impl
method, an associated function, a module's function, the `str` and int methods the type
checker routes to stdlib functions — resolves to its row, with each argument (the receiver
first) checked against its declared label; a `@Flow` parameter accepts every label but
`@SecretCT`. Two facts of the scan are three-valued (a materialisation and a typed read are
typed by the descriptors) and a row is reliable only when every callee it reaches is one the
shadow names; a site whose callee the shadow cannot name (a call through a local, a `grant`
of a closure held in a local), a site that consults an unreliable row, and an unknown fact
that would decide a floor all refuse — production applies its program-wide bound there,
which the shadow cannot reproduce. The pass runs only when a label (an effect operation's
parameter label included: production's bound folds it in, and the shadow reads it off the
operation's own parameter nodes), a flow signature, an extern, an FFI row or a
`declassify_ct` can make a value non-public; the all-public self-compile skips it. Nothing
production derives from the heap floors is oracle-only now (SR-022 keeps the mechanisation
gap).

Since SHP-5c-3 the shadow checks the slot intrinsics and region statements. `slot_put` and
`slot_take` are the checked write a slot is (`intrinsic_memory`), `slot_new` is inert, and each
call's value is the join of its operands, with a call's explicit type arguments skipped. A
`region name(limit) { body }` statement is checked as a block of its function at the same pc:
a `@SecretCT` limit is T029 (the allocation size is observable through the heap layout), the
name is bound to a public scalar handle, the body's environment is a copy of the enclosing one
(a write through an outer binding carries its label out; an outer name cannot be rebound there,
production's T042, which the type checker mirrors). Production's escape lattice (T254) is not
mirrored: the scalar-only rule stands in for it, admitting a body whose every let binds a
scalar and whose every expression constructs no heap value and hands no non-scalar to a call
(a bare name bound before the body is not born in the region, whatever its type), and refusing
every other body, so no region program reads clean where the lattice rejects it.

**Evidence:** `crates/sigil-runtime/tests/taint_check_differential.rs`,
`pipeline_differential.rs`, the `sh_taint_unsupported_shapes_are_explicit`,
`sh_taint_program_bound_sites_refuse_only_while_live` and
`sh_taint_region_overflow_is_explicit` canaries, and the SND-TAINT/constant-time rows in
`docs/SOUNDNESS_MATRIX.md`.

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
