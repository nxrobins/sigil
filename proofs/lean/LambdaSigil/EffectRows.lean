import LambdaSigil.Safety

/-!
# λ-SIGIL — declared effect rows (E001) and latent rows through closures (AG-HOF-A)

The base development *synthesizes* an effect row and proves `effect_safety` about it
(`Preservation.lean`).  SIGIL's `effect_check.rs` instead *checks* a synthesized row against a
**declared** annotation (`callee ⊆ caller`), and `Differential.lean` records the difference honestly
as the **E001 mechanism gap**:

> `E001` (undeclared effect) — mechanism gap. λ-SIGIL *synthesizes* the effect row rather than
> *checking* a synthesized row against a declared annotation … There is no annotation-mismatch
> *rejection* to mirror.

This module closes the Lean side of that gap.  It adds a **checking judgment** `Chk` carrying a
declared row `δ`, proves it sound relative to the synthesizing judgment, lifts `effect_safety` to
declared rows, and proves the higher-order property that motivates the whole exercise:

**a callee's latent effect row is always contained in the declared row of the context that applies
it** (`Chk.app_latent_bounded`).  A closure constructed with latent row `{E}` therefore has *no
derivation* when applied under a declared row that omits `E` — a **compile-time rejection**
(`hof_latent_leak_rejected`), with the accepting twin `hof_declared_accepts` proving the rejection
is not mere over-restriction.

## Faithfulness and honest scope

* `Chk` is deliberately a *thin* subsumption layer over `Typing`: SIGIL's declared row is an
  annotation checked against what the body actually performs, which is exactly `ε ⊆ δ`.  Nothing
  about the operational semantics changes, so every existing theorem is untouched — this module is
  a pure ADD (no edits to `Syntax`/`Typing`/`Semantics`/`Preservation`).
* The **latent row rides the arrow type** (`Ty.arrow A ε B`, `Syntax.lean`) and `Typing.app` unions
  the callee's `εf` into the result row, so in λ-SIGIL a latent row is *structurally impossible to
  drop* at an application.
* **The shipped checker now has this property too** (AG-HOF-A, closed by PR #655).  `Type::Fn`
  carries a latent `EffectSet`; `walk_expr_effects`'s `IndirectCall` arm discharges it
  (`latent ⊆ caller_effects`, else E001) and fails *closed* if the callee is not a function type;
  and `type_compatible` makes the row **contravariant**, so an annotation cannot launder it back.
  Previously the gap was real: a closure built in an `{Alloc}` context and applied in a `{}` context
  was caught only by a *runtime* effect check.  Rust-side witnesses:
  `crates/sigil-compiler/tests/hof_latent_effect_row.rs`.
* **Honest scope, restated.**  This module and the Rust checker now agree on the *property*; that is
  a reviewed correspondence, NOT a mechanized bridge — there is no FFI and no surface parser into
  λ-SIGIL (the standing caveat in `Differential.lean`).  The two interim restrictions this section
  used to document are both RETIRED: SIGIL now derives a closure's row by **precise bottom-up
  inference** from the body (`type_check/effect_infer.rs`, PR #659 — the old over-approximation and
  its pin test are gone; the flipped pin is `pure_closure_defined_in_effectful_fn_compiles`), and
  the surface grammar now HAS an effect-row suffix on a function type (`Fn(T) -> U ! { E }`,
  PR #663, strict unknown-name rejection via T069; an *unannotated* `Fn(T) -> U` still means the
  empty row).  One asymmetry remains, and it is structural rather than interim: λ-SIGIL's rows are
  intrinsic to the arrow type, so it needs no inference pass at all, and `Chk` quantifies over an
  arbitrary declared row `δ` — still the *more general* statement of the two.
-/

namespace LambdaSigil

/-- **Checking** judgment: `e` checks against the *declared* effect row `δ`.

    One rule, mirroring what `effect_check.rs` does: synthesize the row the term actually performs,
    then demand it lie within the declared annotation (`effectsOk ε δ`, i.e. `ε ⊆ δ` — the
    `callee ⊆ caller` test of E001). -/
inductive Chk (S : Sig) : Ctx → Use → Term → Ty → EffectSet → Authority → Use → Prop where
  | sub {Γ U e τ ε δ m U'} :
      Typing S Γ U e τ ε m U' →
      effectsOk ε δ →
      Chk S Γ U e τ δ m U'

/-- **Relative soundness**: a checked term is typed, and everything it can perform lies within the
    declared row.  (The declared row over-approximates the synthesized one.) -/
theorem Chk.sound {S : Sig} {Γ U e τ δ m U'} (h : Chk S Γ U e τ δ m U') :
    ∃ ε, Typing S Γ U e τ ε m U' ∧ ε ⊆ δ := by
  cases h with
  | sub ht hsub => exact ⟨_, ht, hsub⟩

/-- Forgetting the annotation recovers the synthesizing judgment. -/
theorem Chk.toTyping {S : Sig} {Γ U e τ δ m U'} (h : Chk S Γ U e τ δ m U') :
    ∃ ε, Typing S Γ U e τ ε m U' := by
  obtain ⟨ε, ht, _⟩ := h.sound
  exact ⟨ε, ht⟩

/-- **Completeness w.r.t. the tightest annotation**: a synthesized row always checks against
    itself, so annotating a function with exactly what it performs is never a rejection. -/
theorem Chk.complete {S : Sig} {Γ U e τ ε m U'} (h : Typing S Γ U e τ ε m U') :
    Chk S Γ U e τ ε m U' :=
  .sub h (Finset.Subset.refl ε)

/-- Declared rows may only be **widened** — a function annotated with more effects than it performs
    still checks.  (Cashes `effectsOk_trans`, the E001 subset-transitivity lemma.) -/
theorem Chk.weaken {S : Sig} {Γ U e τ δ δ' m U'} (h : Chk S Γ U e τ δ m U') (hd : δ ⊆ δ') :
    Chk S Γ U e τ δ' m U' := by
  cases h with
  | sub ht hsub => exact .sub ht (effectsOk_trans hsub hd)

/-- **Effect safety for DECLARED rows** — the annotation-checked analogue of `effect_safety`.

    Only effects inside the *declared* row `δ` can escape a checked program as a terminal raise.
    This is the statement SIGIL's `! { E }` annotation actually promises. -/
theorem Chk.effect_safety_declared {S : Sig} {e τ δ m U'}
    (h : Chk S [] [] e τ δ m U') :
    ∀ c, StepStar S (initConfig e) c → ∀ E v, c.tm = .perform E v → Value v → E ∈ δ := by
  obtain ⟨ε, ht, hsub⟩ := h.sound
  intro c hstar E v hc hv
  exact hsub (effect_safety ht c hstar E v hc hv)

/-- **The higher-order theorem (AG-HOF-A).**  At an application checked against declared row `δ`,
    the *callee's latent row* `εf` is contained in `δ`.

    A closure cannot be constructed with latent effects and then applied in a context that declares
    fewer — the latent row rides the arrow type and `Typing.app` unions it in, so there is no
    derivation that drops it. -/
theorem Chk.app_latent_bounded {S : Sig} {Γ U f x B δ m U'}
    (h : Chk S Γ U (.app f x) B δ m U') :
    ∃ A εf ε1 Umid, Typing S Γ U f (.arrow A εf B) ε1 m Umid ∧ εf ⊆ δ := by
  cases h with
  | sub ht hsub =>
    cases ht with
    | app hf hx =>
      refine ⟨_, _, _, _, hf, ?_⟩
      intro a ha
      exact hsub (Finset.mem_union_right _ ha)

/-! ## Non-vacuity — the AG-HOF-A witness pair

`Safety.lean`'s convention: a theorem is only worth stating if a concrete program witnesses it.
Here the witness is the exact shape the Rust `IndirectCall` walker misses. -/

/-- The effect performed by the witness closure (any name works; `demoSig.effParam _ = .unit`). -/
def hofEff : EffName := 7

/-- A closure whose BODY performs `hofEff` — its latent row is `{hofEff}`, carried by its type
    `.arrow .unit {hofEff} τ`. -/
def hofClosure : Term := .lam .unit (.perform hofEff .unit)

/-- The AG-HOF-A shape: construct the effectful closure, then **apply** it. -/
def hofProg : Term := .app hofClosure .unit

/-- **The rejection.**  Applying the effectful closure while declaring the EMPTY row has no
    derivation — the latent `{hofEff}` cannot be laundered through the application.

    This is the compile-time rejection SIGIL currently lacks: the shipped checker defers this case
    to a runtime effect check at the construction-site frame. -/
theorem hof_latent_leak_rejected {m : Authority} {τ : Ty} :
    ¬ ∃ U', Chk demoSig [] [] hofProg τ ∅ m U' := by
  rintro ⟨U', h⟩
  cases h with
  | sub ht hsub =>
    cases ht with
    | app hf hx =>
      cases hf with
      | lam hbody _ =>
        cases hbody with
        | perform harg =>
          have hmem := hsub (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
          simp at hmem

/-- **The accepting twin.**  The SAME program checks fine once the row is declared honestly — so
    the rejection above is a genuine effect-discipline violation, not over-restriction. -/
theorem hof_declared_accepts {m : Authority} :
    Chk demoSig [] [] hofProg .unit {hofEff} m [] := by
  refine .sub (.app (.lam (.perform .unit) rfl) .unit) ?_
  decide

end LambdaSigil
