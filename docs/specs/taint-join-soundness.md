# Taint soundness: control-flow joins and the spawn boundary

> **Status: spec, 2026-07-20.** Found by an independent blind review pass (tasks #252, #253).
> These are defects in what SIGIL **enforces**, not in how well it is documented — they outrank the
> remaining pin/ledger work.

## Landing status (2026-07-20)

**The DATA-flow control-flow join is FIXED and validated for `If`, `Match`, `While`, `ForIn`,
`ForRange`** (`crates/sigil-compiler/src/taint_check.rs`). `If`/`Match` snapshot the pre-bindings and
lub the *falling-through* branches/arms (`merge_branch_bindings`); the loops run a bounded fixpoint
(`loop_fixpoint`) over the zero-iteration join. Two rounds of ADVERSARIAL VERIFICATION (5 lenses + a
completeness critic each, 93 then 111 probes) drove the fix well past the original "merge the
branches" framing — the DATA-flow join now also handles:

- **Early exit** — `break`/`continue` capture the taint env into per-loop collectors (`break_envs`
  jump to the loop exit, `continue_envs` to the head); a `diverged` flag makes `check_block` stop at
  the first `break`/`continue`/`return` so the statements those exits skip are not applied on the
  exit path. Without this, a secret captured then `break`/`continue`d was lost when the checker
  wrongly applied the skipped reset (a leak that even bypassed `declassify`).
- **Divergence excluded from the merge** — a branch/arm that diverges does NOT reach the code after
  the construct, so its snapshot is filtered out of `merge_branch_bindings`; else the ubiquitous
  `if c { return err } else { x = <public> }` over-tainted `x` (a false reject).
- **Lexical shadows across every binding channel** — a name that shadows an outer variable is restored
  to the outer binding at block/arm/loop exit (and in any `break`/`continue` env captured during that
  scope), because the flat `TaintEnv` has no scope stack. Three channels were closed as the adversarial
  rounds found them: a `let x` inside a block, a match **pattern binding** `Some(x)` that collides with
  an outer `x`, and a **loop variable** `for x in … { … }` that shadows an outer `x`. Else the
  arm/loop-scoped taint corrupted the outer variable at the merge (all false rejects, never leaks — the
  `pre` floor keeps the accept direction sound).
- **Fixpoint bound scaled** to `pre.len()*4+4` so a long copy-chain loop body converges instead of
  panicking; **while-guard pc refreshed** from the fixpoint head each pass (the guard is re-evaluated
  every iteration), including a T021 rejection when a loop-carried assignment raises the guard to
  `SecretCT` after the first iteration.

Grounded by `taint_join_soundness.rs` (example + `if_join_equals_lub` / `match_join_equals_lub` /
`while_join_preserves_pre` property tests) and `taint_join_early_exit.rs` (every early-exit leak, the
divergence and shadow false-rejects, and the fixpoint-bound convergence). The 2026-07-21 follow-on
also activated the secret-guarded early-exit and match-guard canaries: `continuation_taint` preserves
one-sided early-exit dependence, and match-guard labels join the arm-selection pc.

**`spawn` taint exemption (D2 below) is fixed:** spawn args are visited, `SecretCT` payloads emit
T028, and each non-CT arg is checked against the actor init parameter label (T001 on downgrade).
`spawn_taint_sink.rs` grounds the boundary with six examples plus a property over the complete
`{Public, Internal, Secret}` lattice.

## The two defects

**D1 — no control-flow join.** `crates/sigil-compiler/src/taint_check.rs:271-275` saves and restores
only `env.pc_taint`, then runs `check_block(then_branch, env)` and `check_block(else_branch, env)`
against the **same** `&mut env`. `TaintEnv` is one flat `bindings: HashMap` per function (`:41-44`);
`check_block` never snapshots it (`:126-136`); `Assign → Local` is an unconditional strong update.
So **the last branch analysed wins**:

```sigil
if c { x = secret } else { x = 0 }   // x is @Public at the merge
return x                            // secret reaches a public sink — ACCEPTED
```

**D2 — historical: the spawn payload was never visited.** The old arm read
`TypedExprKind::Spawn(_) => Public`. The
`_` discards the payload. `Send`/`Ask` (`:920-990`) compute per-argument taints and call
`check_message_payload_taint`; `effect_check.rs:379` and `ring_check.rs:204` both destructure
`Spawn(s)` and walk it. Spawn is the **third message boundary**, and the original F007 fix covered
only two. The current `Spawn(s)` arm now checks all three boundaries consistently.

## Phase-0 findings that changed the scope

**① It is a CLASS, not one arm.** Every branching and looping construct has the same shape — save
`pc_taint`, run bodies against the shared env, restore `pc_taint`: `If` (:257), `While` (:277),
`ForIn` (:294), `ForRange` (:312), `Match` (:333, sequential arms). Fixing only `If` would leave a
walker-shaped hole — precisely the recurring "walker forgot an arm" class this project has fenced
before. **Scope is all five.**

**② The loop hazard runs the OTHER way.** For `while`, the unsound direction is the **zero-iteration
path**: `x = secret; while c { x = 0 }` ends with `x` @Public, but if the loop never runs `x` is
still @Secret. A loop must join its body result with the pre-loop state (and iterate to a fixpoint,
which terminates because the taint lattice is finite and small).

**③ The selfhost shadow has the SAME defect.** `selfhost/taint_check.sigil:954-970` calls
`tt_block` on the then-branch and the else-branch with the same `binds` — structurally identical.
Fixing the oracle therefore **creates an oracle/shadow divergence**, and the taint differential
asserts parity. See the decision below.

## Historical scope decision — oracle first, shadow tracked

**Fix the oracle now; record the shadow divergence as a named, pinned gap; fix the shadow as a
follow-on.** Rationale: the oracle is the security boundary that actually ships and rejects
programs. The shadow is a verification artifact. A soundness hole in what enforces should not wait
on hand-written SIGIL. The divergence is made **loud** (a test that pins it) rather than discovered
later.

This was a deliberate widening of the oracle/shadow gap. The production checker now also covers
continuation/guard implicit flow and spawn taint; the self-host difference remains explicit in
`docs/RESIDUAL_RISKS.md` (SR-003).

## Strict Constraints

- **SC-T1 — the join is a LUB, never an overwrite.** After any branching construct, a binding's
  taint MUST be the least-upper-bound over every path that reaches the merge, including the
  not-taken path. No path may lower another path's taint.
- **SC-T2 — bindings introduced inside a branch MUST NOT escape it.** A `let` inside a block is
  block-scoped; leaking it into the merge would be a different unsoundness (a name resolving to a
  taint from a scope that ended).
- **SC-T3 — loops join with the zero-iteration path** and iterate to a fixpoint.
- **SC-T4 — no construct in the class may be left unfixed.** The fix lands for `If`, `While`,
  `ForIn`, `ForRange` and `Match` together, with a test per construct.
- **SC-T5 — the byte capstones must stay byte-identical.** `oracle_compile` runs `taint_check` over
  the certified input; a new rejection there would break self-certification. Verified by running
  the capstones, not by reasoning that compiler source is all-Public.

## Verification plan (TDD + property-based)

**RED first, one failing test per defect**, before any fix:
1. `if/else` assigning @Secret on one path → must be REJECTED (currently accepted).
2. the same for `match` arms.
3. `x = secret; while c { x = 0 }` → must stay REJECTED (zero-iteration path).
4. `for` (both forms) — same shape.
5. spawn with a @Secret argument → must be REJECTED.

**Property-based (proptest — established here by 4 existing compiler property suites):**
- **P1 (the join IS the lub).** For labels `a`, `b` drawn from the taint lattice, the verdict for
  `if c { x = <a> } else { x = <b> }; sink(x)` MUST equal the verdict for `sink(<lub(a,b)>)`.
- **P2 (monotonicity / no lowering).** Adding a branch that assigns a *higher* taint can never make
  a program that was rejected become accepted.
- **P3 (scoping).** A `let` introduced inside a branch is never visible at the merge.

**Regression fences:** a test per construct in the class, so a future walker edit that drops an arm
fails by name.

## Constraints & Fallbacks (Boring-Limit / Fail-Fast)

| # | Boring limit | Fail-fast |
|---|---|---|
| X-T1 | the join is computed over the union of names bound BEFORE the construct; branch-introduced names are dropped | a name present in a branch map but not the pre-map is discarded, not merged (SC-T2) |
| X-T2 | loop fixpoint iterations bounded at `pre.len()*4+4` (each non-converging pass raises ≥1 binding by ≥1 level; ≤ pre.len() bindings × ≤3 levels), so a long copy-chain body converges | exceeding the bound is a `debug_assert!` + conservative top-taint, never a silent partial result |
| X-T3 | all five constructs fixed in one change | a per-construct test fails by name if an arm is dropped |
| X-T4 | the oracle/shadow divergence is pinned by a test that NAMES it | if the shadow is later fixed, that test fails and must be retired deliberately |
| Ambient | the standing gate: fmt + clippy (default/no-default-features/solver) + `cargo test --workspace` with an asserted ok-count, plus the three byte capstones green | CI-red on any missed lane |

## Explicit Anti-Goals

- **Whole-language noninterference.** The implemented policy covers explicit values, structured
  pc-taint, control-flow joins, match guards, and control-dependent early exits. It does not claim a
  whole-compiler theorem or treat termination itself as a low output. Timing/allocation/access
  channels beyond the `@SecretCT` checks remain outside the ordinary `Secret` policy.
- **The two former implicit-flow reproducers are no longer anti-goals.** The secret-guarded
  break/continue and secret match-guard tests are active and rejected. The analysis is deliberately
  conservative and can reject semantically equal path results.
- **Fixing the selfhost shadow in this production change.** Tracked as SR-003.
- **Reworking `TaintEnv` into a scoped structure.** A snapshot-and-merge at the branch points is the
  smallest change that restores soundness; a scope-stack refactor is a larger, separate design.
- **Path-sensitivity.** The join is deliberately path-INsensitive (a lub), which is conservative and
  may reject programs a smarter analysis would accept. That is the correct direction for a security
  property: [[fail-closed]].
