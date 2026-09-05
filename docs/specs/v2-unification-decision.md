# The `_v2` unification decision

> **Status: decision, 2026-08-19.** Closes the last row of the `docs/STYLE.md`
> Appendix A backlog ("`_v2` unification — architecture debt, not style debt; needs its
> own decision doc"). Decision: **no unification, no rename.** The two-tree shape is the
> load-bearing quarantine architecture, not a superseded-copy problem; the actionable
> residue is smaller than the row implied and is enumerated as obligations V2D-1..V2D-6
> below, each marked done-in-this-PR or scheduled with its trigger. Sizes and
> reference counts are measured as landed by this PR unless a commit is named.

## 1 — What the `_v2` trees actually are (measured 2026-08-19)

Two module trees in `crates/sigil-compiler/src` carry the suffix:

| tree | lines | role | production caller |
|---|---|---|---|
| `type_check_v2/` (`mod.rs`, `obligations.rs`, `refinement.rs`) | 1,542 | the sole refinement-discharge pipeline: Pure collection (no Z3) → Discharge (the tree's only Z3 site) → Assembly with a private-constructor proof token | `type_check::check_with_warnings`, unconditionally |
| `air_capability_v2/` (`mod.rs`, `collector.rs`, `obligations.rs`) | 1,332 | the sole AIR capability flow prover: Pure collector → Z3 discharge (re-walks the program; a workload-only verdict would be unsound per its module doc) → single-mint proof token | `capability::verify`, after structural success, under `feature = "solver"` |

Neither is an experiment, a parked copy, or a replacement-in-waiting. Both module docs
open by declaring the production role, and `migration_hygiene.rs` fails the build if
that prose regresses to shadow-era phrasing.

**The `_v2` contrasts with deleted predecessors, not with the modules beside them.**
History (recovered from the remote; the local clone is shallow at 2026-07-20):

- `type_check_v2/` introduced 2026-05-27 ("I/O Quarantine PR 1") as a shadow pipeline
  beside the then-12,874-line `type_check.rs` monolith, whose three inline Z3 call
  sites were the stated motivation ("approaching a maintainability cliff"). Cutover
  commit `bdc0d708` (2026-07-15) promoted it to sole discharge path and deleted the
  legacy inline walkers plus the whole shadow-comparison harness.
- `air_capability_v2/` introduced 2026-05-29 ("AIR-Cap PR 2") to migrate the legacy
  Z3 AIR-cap walk out of `z3_capability.rs`. Deletion commit `934f3ba` (2026-06-12/13,
  titled `[ONE-WAY-DELETION]`) removed the legacy prover after a 138-merge-PR shadow
  byte-equality window (30 required); `z3_capability.rs` survives at 469 lines holding
  only the shared refinement queries.

The modules "beside" them are complementary phases, not old versions:

- `type_check/` owns structural checking, declaration-shape refinement validation, and
  flow-sensitive narrowing; `type_check_v2/` owns Z3-backed satisfiability discharge.
  Their diagnostic code sets are disjoint and that split is pinned by
  `refinement_no_double_emission.rs` (shape codes vs discharge codes T210/T211/T215/
  T216/T220/T224/T225).
- `capability.rs` is the structural half of the AIR gate (C001, R010–R013) and *calls*
  the `_v2` prover (C002–C005) — a phase boundary, not a version boundary.

`docs/STYLE.md` §2.9 already fixes the naming semantics: *"`_v2` means production
successor, nothing else."*

## 2 — Why the Appendix-A framing was wrong

The row read "`type_check_v2` + `air_capability_v2` beside their originals is
architecture debt". Measured, "beside their originals" is false in the sense implied:
the originals-as-old-versions were deleted in 2026-06/07; what ships beside the `_v2`
trees are different phases of the same gates. What *looked* like one big unification
debt decomposes into a shape question (§3) plus five small, nameable residues (§4).

## 3 — Options considered

**A. Merge each `_v2` tree into its neighbor (`type_check/`, `capability.rs`) —
REJECTED.** The separation IS the quarantine architecture: pure files physically
cannot import Z3 (`quarantine_grep.rs` pins the boundary by literal path), a CI shell
lint pins `type_check_v2/mod.rs` as the sole refinement-Z3 caller by path regex
(`ci.yml` "Lint — v2 is the sole refinement-Z3 caller"), and each tree's proof token
is unconstructible outside its orchestrator file — a private `_seal: ()` field;
compile-time privacy is the enforcement (the shadow-era CI grep that counted mint
sites retired with the harness). Merging collapses the boundary those instruments
enforce, for zero behavior gain. The retired AIR-cap journal records a seven-point
rationale for why the two trees deliberately have different shapes (input type, call
site, obligation kind, code family, SMT theory, discharge context, orchestrator-level
invariant) and concludes "Reusing `type_check_v2/mod.rs`'s orchestrator is wrong"
(recoverable locally: `git show 377f728^:docs/air-capability-quarantine.md`, section
"Why this needs a different shape than `type_check_v2/`"). Additionally, a merge
cannot be byte-proven behavior-neutral on the solver lane: the parity manifest is
compiled out under `feature = "solver"` (`parity_manifest.rs` pins the shipped no-solver
configuration), so solver-lane preservation would rest on the exact-verdict suites
alone — weaker evidence than the default lane's byte manifest, for a refactor with no
payoff.

**B. Rename to drop `_v2` (and the shadow-era type names) — REJECTED for now.**
Measured blast radius at this decision's base commit (`4e0b2bf`): `air_capability_v2`
on 70 lines across 32 files, `type_check_v2` on 35 lines across 21 files (the PR
landing this doc adds a few more citation lines by design) — including compile-breaking
`include_str!` paths (`cap_source_legitimacy_guard.rs`), grep-pinned literal paths in
`quarantine_grep.rs` and the `ci.yml` lint regex, ledger rows (`SOUNDNESS_MATRIX.md`
SND-CAP-001 enforcement leg, `RESIDUAL_RISKS.md` SR-002 owner), spec citations, a Lean
faithfulness anchor (`Authority.lean`), and `selfhost/cap_check.sigil` prose whose
certified source hash would need a repin. Two of those surfaces fail *silently* on a
rename: `soundness_contract.rs` checks the matrix's Enforcement field only for
non-emptiness, and nothing validates the Lean anchors' paths. The names are cosmetic
debt with a recorded meaning (§2.9) and truthful module docs; the churn is real and
the gain is not. Revisit trigger: the self-hosted type-checker bridge
(`docs/specs/type-checker-in-sigil.md` §"bridge" names `type_check_v2`'s obligation
model as its target) will touch most citation sites anyway — if that lands, rename
during it or drop the idea permanently.

**C. Keep the shape and the names; fix the enumerated residue — ADOPTED.**

## 4 — Obligations

- **V2D-1 (done in this PR): re-anchor the orphaned NC*/CM* contract citations.**
  The quarantine code cites engineering-contract IDs (CM4 single mint site, NC4/CM7
  sanctioned direct check, NC5 deterministic collection order, NC6/CM11 in-order
  discharge, NC1/CM1 type firewall) whose defining matrix lived in
  `docs/air-capability-quarantine.md` — deleted by the history-canonicalization commit
  `377f728` (its absence is now itself enforced by `migration_hygiene.rs`) — and, for
  the NC series, in an external plan file that was never in-tree. Worse, the surviving
  `docs/z3-runtime-capability.md` defines an unrelated NC1–NC4 for the runtime Z3
  shim: a namespace collision. §5 below is now the in-repo anchor for the quarantine
  IDs; the first use in each citing file glosses the ID and points here.
- **V2D-2 (done in this PR): fix the stale in-tree citations left by the migrations.**
  `air_capability_v2/mod.rs` cited `tests/air_cap_cache_bypass.rs` (retired with the
  shadow harness; nothing pins the cache bypass today — stated inline now instead of a
  phantom citation) and a wrong test name for the legitimacy-seeding gate (the real
  test is `every_cap_originating_stmt_is_legitimacy_seeded`); `capability.rs` still
  described `z3_rlimit_consumed` in terms of the deleted `verify_function_with_solver`
  and pointed the program budget at `z3_capability.rs` (it lives in
  `air_capability_v2::AIR_CAP_Z3_PROGRAM_RLIMIT`); `type_check/capability_tc.rs` said
  the AIR-time flow proof "lives in `crate::z3_capability`". All corrected.
- **V2D-3 (done in this PR): make the rlimit "sync test" real.** `z3_capability.rs`
  claimed its `Z3_RLIMIT` and the prover's `AIR_CAP_Z3_RLIMIT` "are kept equal by the
  sync test there" — no such test existed; the constants were equal by coincidence.
  `rlimit_constants_stay_in_sync` (in `air_capability_v2/mod.rs`'s solver-gated test
  module) now asserts the equality, and the comment names it.
- **V2D-4 (scheduled): the untracked consolidation follow-on.** The retired plan
  recorded, without scheduling: consolidate the shared `z3_capability.rs` remnant
  (`check_refinement*`, verdict enums, `check_cached_solver`, `make_solver`) into a
  dedicated `refinement_queries` module, and decide verdict-cache adoption for the sole
  prover (the discharge deliberately bypasses the cache today). That follow-on lost its
  tracking home when the plan doc was deleted; it is re-recorded here. Trigger: the
  next substantive edit to `z3_capability.rs` pays this alongside, or explicit user
  direction. It is refactoring, not soundness: both halves are prover-internal.
- **V2D-5 (accepted, guarded): the parallel typed-AST walkers.** `type_check_v2/`
  `refinement.rs` (`visit_expr_constructs`) and `type_check/residual.rs`
  (`scan_expr_children`) both walk the typed tree totally: each handles every one of
  `TypedExprKind`'s 34 variants explicitly, with no `_ =>` catch-all, so every new
  variant must be added to both. Accepted because the guard is compile-time totality —
  a new variant refuses to compile in each walker rather than silently skipping — and
  because the
  `_v2` walker is shared infrastructure (`effect_check` and `effect_desugar` import
  it), so folding it into one pass would recreate the coupling the quarantine removed.
- **V2D-6 (scheduled): the effect-handlers spec's Handle-site census has fully
  drifted.** `docs/specs/effect-handlers-in-sigil.md` ("The `Handle` node is
  destructured at 9 sites") cites nine file:line positions; measured today, all nine
  line numbers are stale and the live count of `Handle`-destructure/construct sites in
  those files is ten (`grep -n '::Handle('` over the spec's cited files,
  `ClauseHandle` excluded). Re-censusing means re-verifying the per-site "reads a single
  `.body`" claim, which is effect-handlers work, not `_v2` work. Trigger: the next
  change touching `TypedExprKind::Handle` or that spec re-censuses with grep anchors
  (function names) instead of line numbers, per the STYLE.md convention that quoted
  text, not line numbers, is the anchor.

Also noted, not new debt: on no-solver builds ordinary refinement obligations are
accepted undischarged (a documented decision in `type_check_v2/mod.rs`; T215
construction subsumption stays fail-closed) — bounded by the `solver_verified = false`
cert witness (ET-M3, single false-biased assignment site pinned by
`z3_guard_fences.rs`) and the CLI execution gate (R817) that refuses to run unverified
artifacts.

## 5 — The quarantine contract IDs (in-repo anchor)

What each ID demonstrably means at its use sites, reconstructed from the retired
journal's own summary (recoverable locally:
`git show 377f728^:docs/air-capability-quarantine.md`, "Constraints & Fallbacks
summary") and the in-tree comments; the original 22-entry matrix (one per
adversarial-compiler vulnerability, each with a numeric bound and fail-fast mode)
lived in an external plan file and is not recoverable. Two disambiguation warnings:
these IDs are **distinct from** the runtime-shim NC1–NC4 defined in
`docs/z3-runtime-capability.md`, and the same short IDs are reused by several other
unrelated in-tree note families (bounds-trap notes in `air.rs`, linearity notes in
`type_check/`, place-assignment notes in tests) — context plus this table
disambiguates the QUARANTINE family; the IDs are not globally unique.

| ID | contract | living enforcement |
|---|---|---|
| NC1 / CM1 | pure collector files must not name Z3 at type level (transitive leaks included) | `quarantine_grep.rs` type firewall |
| CM2 | no Z3 / `z3_capability` imports in the tree's PURE files (`collector.rs`, `obligations.rs`); `mod.rs` is the sanctioned orchestrator boundary (its solver-gated test module cites `z3_capability::Z3_RLIMIT` for the sync pin) | `quarantine_grep.rs` import scan |
| CM4 | exactly one `DischargedAirCapability` mint site | the private `_seal: ()` field — compile-time privacy (the shadow-era CI grep retired with the harness) |
| NC4 / CM7 | the prover checks the solver directly, bypassing the verdict cache | sanctioned `check_direct`; bypass itself unpinned (see V2D-2) |
| NC5 | deterministic collection order: functions → blocks → stmts | `collector.rs` comment + workload snapshot goldens |
| NC6 / CM11 | discharge iterates the workload Vec in order; no parallelism | `obligations.rs` contract comment |
| CM17 | every solver verdict maps to a diagnostic arm (no silent verdicts) | `air_cap_arm_coverage.rs` |
| CM9 / CM18 | one-way deletion ceremony for the legacy prover (historical; discharged 2026-06-12/13) | retired with the shadow harness |

## 6 — Revisit triggers, in one place

1. The self-hosted type-checker bridge lands → rename question reopens at zero
   marginal churn (option B).
2. A third quarantine migration is proposed → generalize the orchestrator pattern
   instead of growing a third bespoke tree; this doc is the prior art to cite.
3. `z3_capability.rs` gets a substantive edit → pay V2D-4 alongside.
4. Any new `_v2` module must satisfy STYLE.md §2.9: production successor, nothing
   else — never an experiment or a parked copy.
