import LambdaSigil.Safety
import LambdaSigil.EffectRows

/-!
# λ-SIGIL — Differential correspondence corpus (Milestone M7)

This module is the **Lean half** of the M7 differential cross-check: for each headline SIGIL
violation pattern, a λ-SIGIL term whose **accept/reject verdict** is established here by a compiled
proof — `accept` = an inhabited `Typing` derivation (`∃ τ ε m U', Typing …`), `reject` = a proof of
**non-derivability** (`¬ ∃ …, Typing …`, by inversion to a real contradiction) or of operational
`Stuck`.  The **Rust half** (`crates/sigil-runtime/tests/lambda_sigil_differential.rs` +
`crates/sigil-compiler/tests/lambda_sigil_c003.rs`) asserts that the paired `.sigil` fixture gets
the corresponding `sigil_check` verdict (clean / the expected diagnostic code).

There is **no automatic Lean⇄Rust bridge** (no FFI, no surface-syntax parser into λ-SIGIL) — the
correspondence is two independently machine-checked halves tied by the reviewed table below. The
Rust harness classifies every ID as shared, Rust-only, or Lean-only with a required reason. The
relation is deliberately NOT 1:1: one Lean rule may represent several Rust sinks, and some language
mechanisms exist on only one side. This catches unexplained drift, not a shared-wrong semantic map.

## Correspondence table

| ID | pattern | SIGIL code | kind | λ-SIGIL obligation (this file) |
|---|---|---|---|---|
| `LSD-O001` | use-after-move (cap reused) | O001 | clean reject (cap sub-case) | `lsd_o001_reject` — 2nd `var_lin` fails (`U[i]? = some false`); over `Typing` |
| `LSD-T273` | mint without authority | T273 | mechanism-aligned (type gate) | `lsd_t273_reject` — `mint 0 .unit`: arg not `mintAuth` |
| `LSD-E001-hof` | apply an effectful closure under a declared row that omits its effect | E001 | clean reject (declared-row check `Chk`, higher-order) | `lsd_e001_hof_reject` (= `hof_latent_leak_rejected`, `EffectRows.lean`) — `hofProg` has no `Chk` derivation at row `∅` |
| `LSD-C003-call/spawn/send/return` | authority at sink | C003 | **clean reject** (wired sink rule) | `lsd_c003_reject` (typing) + `lsd_c003_stuck` (operational) |
| `LSD-ACC-mint` | mint then exercise | — | clean accept | `lsd_acc_mint` (= `demo_typed`) |
| `LSD-ACC-E001-hof` | the same closure application under a row that **declares** the effect | — | clean accept | `lsd_acc_e001_hof` (= `hof_declared_accepts`) — `hofProg` checks at row `{hofEff}` |
| `LSD-ACC-trap` | a function whose body is an explicit `trap`, then called | — | clean accept + abort | `lsd_acc_trap` (typed) + `lsd_acc_trap_aborts` (β-steps to the terminal `trap`) |
| `LSD-ACC-once` | single-use cap | — | clean accept | `lsd_acc_once` |
| `LSD-ACC-restr` | restrict to a proper subset, exercise a **held** bit | — | clean accept (observable) | `lsd_acc_restr` |
| `LSD-ACC-sink` | deliver a full cap to a full-mask sink | — | clean accept | `lsd_acc_sink` |
| `LSD-ACC-handle` | handler discharge | — | clean accept | `lsd_acc_handle` (= `demoHandled_typed`) |
| `LSD-RESTR-removed` | exercise a restricted-away bit | C003/over-restrict | clean reject | `lsd_restr_removed_reject` (shows `restrict` is load-bearing) |

### `Q3` — four sinks, one rule

SIGIL's C003 fires at four surface sinks (Call / Spawn / Send / Return; `z3_corpus/01,02,03,07`).
The check is **sink-uniform** (`sinkOk required actual := required ⊆ actual`, `Authority.lean`), so a
single λ-SIGIL `sink` rule (`Typing.sink` / `WT.sink`) models all four: the four `.sigil` fixtures
each assert `{C003}` on the Rust side and all map to the obligations below.  The `sink` term carries
the required authority `req`; `req ⊆ k` is exactly the C003 attenuation check, now **wired into a
real typing rule** (so C003 is a *literal* ⇔, not a representative analogy).

## Correspondences that are NOT literal ⇔ (honest scope — no fake fixtures)

* **`C001` (cap forgery) — by construction.**  There is no cap-forging `Term`: the only introducers of
  a `.cap` type are `mint`/`restrict`/`capVal` (`Syntax.lean`), and `capVal` requires `k ⊆ fullMask κ`.
  So forgery is impossible to even *write* in λ-SIGIL — a structural property of the grammar, not a
  per-fixture rejection.  On the SIGIL side a record literal coerced to a cap type is rejected by the
  **front end** (parse/type errors — empirically `P001`/`T049`, never reaching the AIR-level
  `capability.rs` C001 check, which is a defense-in-depth backstop exercised only by hand-built AIR).
  Both sides therefore make forgery *unconstructable from source*; the Rust
  `cap_forgery_rejected_by_frontend` test witnesses this rather than a coded `{C001}` fixture.
* **`E001` (undeclared effect) — mechanism gap, CLOSED on BOTH sides and now PAIRED BY ID for the
  higher-order case.**  The base judgment *synthesizes* the effect row rather than *checking* it
  against a declared annotation (the `callee ⊆ caller` test SIGIL runs); that content is
  **`effect_safety`** (`Preservation.lean`) + the witnesses `demoEff_escapes_in_row` /
  `demoHandled_safe` (`Safety.lean`).  `EffectRows.lean` adds the missing half: the checking
  judgment **`Chk`** (`ε ⊆ δ`), `Chk.effect_safety_declared`, and the annotation-mismatch
  *rejection* `hof_latent_leak_rejected` (paired with the accepting twin `hof_declared_accepts`).
  The Rust half followed (PR #655): `Type::Fn` now carries a latent `EffectSet`,
  `walk_expr_effects`'s `IndirectCall` arm discharges it (E001, fail-closed on a non-function
  callee), and `type_compatible` makes the row contravariant — so the higher-order case (AG-HOF-A)
  is a compile-time rejection rather than a runtime trap, witnessed by
  `crates/sigil-compiler/tests/hof_latent_effect_row.rs`.  The table rows `LSD-E001-hof` /
  `LSD-ACC-E001-hof` tie that pair to the `.sigil` spelling of **the same program** — a closure
  performing one effect, applied inside a function whose declared row omits / declares it — so
  the Rust harness classifies both ids as *shared*.  The older direct-call E001 fixtures stay
  Rust-only: λ-SIGIL has no named functions, so `boot` calling `expensive` has no same-shape term.
  **Scope, stated honestly:** this is a reviewed correspondence by identifier, not a mechanized
  bridge (the no-FFI caveat below applies).  The two interim SIGIL-side restrictions once listed
  here are both RETIRED: closure rows are now inferred bottom-up from the body (`effect_infer.rs`,
  PR #659), and the grammar has a fn-type row suffix (`Fn(T) -> U ! { E }`, PR #663; unannotated
  still means the empty row).  `Chk` quantifies over an arbitrary `δ` and so remains the more
  general statement.
* **`trap` / `Type::Never` — the explicit abort is paired; nothing else about traps can be.**
  `LSD-ACC-trap` is the only trap row: a function whose body is `trap`, applied — typed on both
  sides and aborting on both sides (Rust lowers the `Never`-typed statement to wasm `unreachable`;
  here `lsd_acc_trap_aborts` β-steps to the terminal `trap`, the fourth answer of `WT.progress`).
  Two things are deliberately NOT paired.  (1) The Rust harness carries a **Rust-only** reject for
  a *value-position* `trap()` (`let x = trap()`): SIGIL rejects binding the diverging value, while
  `Typing.trap` types `trap` at any type in any position (`demoTrap_typed` even puts it in function
  position) — a structural asymmetry, classified on the Rust side rather than mirrored by a fake
  Lean reject.  (2) **Fuel exhaustion and bounds failure cannot be paired**: the core calculus has
  no fuel counter and no arrays (`Term` has no loop, index, or host-denial constructor and `Config`
  carries no fuel), so those runtime traps have no λ-SIGIL analogue at all — they are covered by
  runtime tests (`SND-FUEL-001`, `SND-MEM-001` in `docs/SOUNDNESS_MATRIX.md`), not by this corpus.
* **`T272` (non-mintable cap) — out of model.**  λ-SIGIL's single `mintAuth κ` token conflates
  "the cap type is mintable" with "you hold the granting authority"; it has no `mintable_by` policy
  layer, so T272's policy-existence distinction is unmodeled.  `LSD-T273` covers the *type gate*
  (`mint` requires a `mintAuth`-typed argument), not the scope-search gate or the policy layer.
-/

namespace LambdaSigil

/-! ## Accept obligations (an inhabited `Typing` derivation = `sigil_check` accepts) -/

/-- `LSD-ACC-mint`. -/
theorem lsd_acc_mint : ∃ τ ε m U', Typing demoSig [] [] demoProg τ ε m U' :=
  ⟨_, _, _, _, demo_typed⟩

/-- `LSD-ACC-handle`. -/
theorem lsd_acc_handle : ∃ τ ε m U', Typing demoSig [] [] demoHandledProg τ ε m U' :=
  ⟨_, _, _, _, demoHandled_typed⟩

/-- `LSD-ACC-once`.  A capability minted and exercised **exactly once** — well-typed. -/
theorem lsd_acc_once :
    ∃ τ ε m U',
      Typing demoSig [] [] (.letIn (.mint 0 (.mintTok 0)) (.exercise 0 (.var 0))) τ ε m U' := by
  refine ⟨_, _, {0, 1}, _,
    Typing.letIn (Typing.mint Typing.mintTok)
      (Typing.exercise (Typing.var_lin rfl rfl rfl) ?_ (by decide))⟩
  decide

/-- `LSD-ACC-restr`.  Restrict the minted cap to the **proper** subset `{0}` (still containing the
    exercised bit `0`) and exercise `0` — well-typed.  Observably exercises the rule (not a no-op
    restrict to the full mask); its 1-mutation sibling `LSD-RESTR-removed` is rejected. -/
theorem lsd_acc_restr :
    ∃ τ ε m U',
      Typing demoSig [] [] (.exercise 0 (.restrict {0} (.mint 0 (.mintTok 0)))) τ ε m U' := by
  refine ⟨_, _, {0, 1}, _,
    Typing.exercise (Typing.restrict (Typing.mint Typing.mintTok)) ?_ (by decide)⟩
  -- `0 ∈ restrict (fullMask 0) {0} = fullMask 0 ∩ {0}` — split to two literal memberships.
  exact Finset.mem_inter.mpr ⟨by decide, by decide⟩

/-- `LSD-ACC-sink`.  Deliver an **un-attenuated** full cap to a full-mask sink (`req = {0,1} = k`) —
    well-typed (the accept sibling of `LSD-C003`). -/
theorem lsd_acc_sink :
    ∃ τ ε m U', Typing demoSig [] [] (.sink {0, 1} (.capVal 0 {0, 1})) τ ε m U' := by
  -- all three side-conditions are `{0,1} ⊆ {0,1}` (the cap's mask is the full mask), by `subset_rfl`.
  exact ⟨_, _, {0, 1}, _, Typing.sink (Typing.capVal subset_rfl) subset_rfl subset_rfl⟩

/-- `LSD-ACC-E001-hof`.  `hofProg` (an effectful closure, applied) **checks** against the declared
    row `{hofEff}` — the accept twin of `LSD-E001-hof`, one row-mutation away.  Stated over the
    declared-row judgment `Chk` (`EffectRows.lean`), which is what SIGIL's `! { E }` annotation
    promises; a plain `Typing` derivation would not express the annotation at all. -/
theorem lsd_acc_e001_hof {m : Authority} : Chk demoSig [] [] hofProg .unit {hofEff} m [] :=
  hof_declared_accepts

/-- `LSD-ACC-trap`'s program: a function whose whole body is the explicit abort `trap`, applied to
    `unit` — the λ-SIGIL spelling of SIGIL's `fn always_abort() -> i64 { trap(); }` followed by a
    call.  `trap` sits in **statement** position (it *is* the body), the shape SIGIL accepts. -/
def lsdTrapProg : Term := .app (.lam .unit .trap) .unit

/-- `LSD-ACC-trap` (typing).  Well-typed: `Typing.trap` types the body at any `τ`, `Typing.lam`
    closes it, and the application needs only `unit : unit`. -/
theorem lsd_acc_trap : ∃ τ ε m U', Typing demoSig [] [] lsdTrapProg τ ε m U' :=
  ⟨.unit, _, ∅, _, Typing.app (Typing.lam Typing.trap rfl) Typing.unit⟩

/-- `LSD-ACC-trap` (operational).  The abort actually fires: the β-step substitutes into the body
    `trap`, which is `trap` again — the terminal fourth answer of `WT.progress`, never a value and
    never stuck.  Rust's counterpart: the block lowers to wasm `unreachable`. -/
theorem lsd_acc_trap_aborts : Step demoSig ⟨lsdTrapProg, ∅, ∅⟩ ⟨.trap, ∅, ∅⟩ :=
  Step.beta Value.unit

/-! ## Reject obligations (no `Typing` derivation, or operationally `Stuck`) -/

/-- `LSD-O001` — **use-after-move**.  The capability `c` is exercised twice; the second use has no
    derivation because the first consumed it (`var_lin` requires `U[i]? = some true`, but `c`'s usage
    bit is `false` by then).  Stated over `Typing` (the affine judgment) — `WT` erases usage and would
    *accept* this term, so the obligation is `Typing`-only by construction. -/
theorem lsd_o001_reject :
    ¬ ∃ τ ε m U',
      Typing demoSig [] []
        (.letIn (.mint 0 (.mintTok 0)) (.letIn (.exercise 0 (.var 0)) (.exercise 0 (.var 1))))
        τ ε m U' := by
  rintro ⟨τ, ε, m, U', h⟩
  cases h with
  | letIn hmint hbody =>
    cases hmint with
    | mint htok =>
      cases htok with
      | mintTok =>
        cases hbody with
        | letIn hex0 hex1 =>
          cases hex0 with
          | exercise hv0 _ _ =>
            cases hv0 with
            | var_lin _ _ _ =>
              cases hex1 with
              | exercise hv1 _ _ =>
                cases hv1 with
                | var_lin _ _ hU1 => exact absurd hU1 (by decide)
                | var_unr _ hlin1 => simp [Ty.isLinear] at hlin1
            | var_unr _ hlin0 => simp [Ty.isLinear] at hlin0

/-- `LSD-T273` — **mint without authority**.  `mint 0 .unit` has no derivation: the `mint` rule
    requires its argument to type as `mintAuth 0`, but `.unit : .unit ≠ .mintAuth 0`.  (Models the
    `&Admin` *type* gate; cf. the T272/scope-search scope note above.) -/
theorem lsd_t273_reject :
    ¬ ∃ τ ε m U', Typing demoSig [] [] (.mint 0 .unit) τ ε m U' := by
  rintro ⟨τ, ε, m, U', h⟩
  cases h with
  | mint htok => cases htok

/-- `LSD-E001-hof` — **undeclared effect, higher-order**.  `hofProg` applies a closure whose latent
    row is `{hofEff}` while the context declares the EMPTY row: no `Chk` derivation, because
    `Chk.app_latent_bounded` forces `{hofEff} ⊆ ∅`.  The Rust twin fires E001 at the application
    (the `IndirectCall` discharge), not at the closure's construction. -/
theorem lsd_e001_hof_reject {m : Authority} {τ : Ty} :
    ¬ ∃ U', Chk demoSig [] [] hofProg τ ∅ m U' :=
  hof_latent_leak_rejected

/-- `LSD-C003` (typing) — **authority at a full-mask sink**.  Delivering a cap restricted to `{0}` to
    a sink demanding `{0,1}` has no derivation: the `sink` rule requires `req ⊆ k`, but
    `{0,1} ⊄ restrict {0,1} {0} = {0}`.  This is the *literal* inversion of the wired sink rule
    (Q2 = wire `sinkOk`), authored over a **restricted** cap to attack the same attenuation event as
    the `.sigil` `.restrict(...)` fixture. -/
theorem lsd_c003_reject :
    ¬ ∃ τ ε m U',
      Typing demoSig [] [] (.sink {0, 1} (.restrict {0} (.capVal 0 {0, 1}))) τ ε m U' := by
  rintro ⟨τ, ε, m, U', h⟩
  cases h with
  | sink hcap hsink _ =>
    cases hcap with
    | restrict hcv =>
      cases hcv with
      | capVal _ => simp only [restrict] at hsink; exact absurd hsink (by decide)

/-- `LSD-C003` (operational, **primary** per C7) — the same over-restricted sink delivery is
    `Stuck`: `sinkRed` cannot fire (`{0,1} ⊄ {0}`), the cap value cannot step, and it is neither a
    value nor a raise.  Reuses the `stuck_is_inhabited` shape; immune to any `Typing` refactor.  By
    `type_soundness` this state is unreachable from well-typed code — exactly what C003 protects. -/
theorem lsd_c003_stuck : Stuck demoSig ⟨.sink {0, 1} (.capVal 0 {0}), ∅, ∅⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hv; cases hv
  · rintro ⟨E, v, he, -⟩; simp at he
  · intro h; simp at h
  · rintro ⟨c', hs⟩
    cases hs with
    | sinkRed hsub => exact absurd hsub (by decide)
    | sink1 hstep => cases hstep

/-- `LSD-RESTR-removed` — the 1-mutation sibling of `LSD-ACC-restr` proving `restrict` is
    load-bearing: exercising bit `1`, which was attenuated away by `restrict {0}`, has no derivation
    (`exercise` requires `1 ∈ restrict {0,1} {0} = {0}`). -/
theorem lsd_restr_removed_reject :
    ¬ ∃ τ ε m U',
      Typing demoSig [] [] (.exercise 1 (.restrict {0} (.mint 0 (.mintTok 0)))) τ ε m U' := by
  rintro ⟨τ, ε, m, U', h⟩
  cases h with
  | exercise hcap ha _ =>
    cases hcap with
    | restrict hm =>
      cases hm with
      | mint _ => simp only [restrict, demoSig] at ha; exact absurd ha (by decide)

end LambdaSigil
