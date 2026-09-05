import LambdaSigil.CapabilitySafety
import LambdaSigil.Preservation

/-!
# λ-SIGIL — Soundness capstone

This module collects the proven soundness results and exercises them on a concrete program so the
theorems are demonstrably **non-vacuous** (they apply to a program that actually mints and exercises
a capability), and it exhibits a genuinely *stuck* ill-typed term so `type_soundness` is not
vacuously true.

## Proven, machine-checked (no proof gaps; axioms = `propext`, `Classical.choice`, `Quot.sound`)

* **Type soundness** — `type_soundness` (`Preservation.lean`): no configuration reachable from a
  well-typed program is stuck (progress + preservation, the latter via a usage-erased judgment `WT`
  and the de Bruijn substitution lemma).
* **Capability safety** — `capability_safety` (`CapabilitySafety.lean`): a well-typed program never
  exercises authority outside its static ceiling `m` (`∀` reachable `c`, `c.auth ⊆ m`).
* **Effect safety (VACUOUS here)** — `effect_safety_vacuous` (`CapabilitySafety.lean`): the effect
  trace stays within the declared row, but *vacuously* — no `perform`/`handle` typing rules yet, so
  the trace is empty and the typing hypothesis is unused.  The substantive version arrives with M6.
* **Progress** — `progress` (`Progress.lean`): a well-typed closed term is a value or steps.
* **Affine ownership** — `Typing.consumed_stays_consumed` / `Typing.usage_monotone`
  (`Substitution.lean`): a consumed linear capability can never be used again (no use-after-move /
  no duplication — ROADMAP item 8 (a),(b)).
* **No authority amplification** — `restrict_cannot_amplify`, `mint_attenuation_bounded`
  (`Authority.lean`): attenuation only ever shrinks authority (ROADMAP item 8 (c)).

## Not yet proven (next milestones)

* **Effect safety with handlers** (M6 — `perform`/`handle`) and the **differential cross-check** vs.
  the Rust `sigil_check` (M7).
-/

namespace LambdaSigil

/-- A concrete capability/effect signature: one cap type whose full authority mask is `{0,1}`. -/
def demoSig : Sig :=
  { fullMask := fun _ => {0, 1}, effParam := fun _ => .unit, effRet := fun _ => .unit }

/-- A concrete program: mint a full capability of type `0` (gated by its mint token), then exercise
    authority bit `0`.  Declared authority ceiling is `{0,1}`. -/
def demoProg : Term := .exercise 0 (.mint 0 (.mintTok 0))

/-- The demo program is well-typed at ceiling `{0,1}`. -/
theorem demo_typed :
    Typing demoSig [] [] demoProg .unit ∅ ({0, 1} : Authority) [] := by
  apply Typing.exercise
  · apply Typing.mint
    apply Typing.mintTok
  · decide
  · decide

/-- **Capability safety, instantiated.**  Every configuration reachable from the demo program keeps
    its exercised-authority trace within the declared ceiling `{0,1}` — a non-vacuous instance of
    `capability_safety`. -/
theorem demo_confined :
    ∀ c, StepStar demoSig (initConfig demoProg) c → c.auth ⊆ ({0, 1} : Authority) :=
  capability_safety demo_typed

/-- Progress, instantiated (M6 4-way): the demo program is a value, a raise, can step, or is the
    terminal abort `trap`. -/
theorem demo_progress :
    Value demoProg ∨ (∃ E' v, demoProg = .perform E' v ∧ Value v) ∨
      (∃ c', Step demoSig ⟨demoProg, ∅, ∅⟩ c') ∨ demoProg = .trap :=
  WT.progress ∅ ∅ demo_typed.toWT

/-- **Type soundness, instantiated.**  No configuration reachable from the demo program is stuck. -/
theorem demo_sound :
    ∀ c, StepStar demoSig (initConfig demoProg) c → ¬ Stuck demoSig c :=
  type_soundness demo_typed

/-- **Non-vacuity of `type_soundness` (C-VAC).**  `Stuck` is genuinely inhabited: the ill-typed
    term `exercise 0 ()` — exercising authority on a non-capability — is stuck (not a value, not a
    raise, and no reduction rule applies). -/
theorem stuck_is_inhabited : Stuck demoSig ⟨.exercise 0 .unit, ∅, ∅⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hv; cases hv
  · rintro ⟨E, v, he, -⟩; simp at he
  · intro h; simp at h
  · rintro ⟨c', hs⟩; cases hs with | exercise1 hsub => cases hsub

/-! ## M6 — effect handlers: `effect_safety` is non-vacuous (C-VAC) -/

/-- A program that **performs** effect `0` (`perform 0 ()`), declaring it in the row `{0}`. -/
def demoEffProg : Term := .perform 0 .unit

theorem demoEff_typed :
    Typing demoSig [] [] demoEffProg .unit (insert 0 ∅ : EffectSet) ∅ [] :=
  Typing.perform Typing.unit

/-- **Effect safety, instantiated — escaping.**  Every reachable terminal raise of `perform 0 ()`
    carries effect `0`, which is in its declared row `{0}`.  Non-vacuous: the program *is* such a
    raise. -/
theorem demoEff_escapes_in_row :
    ∀ c, StepStar demoSig (initConfig demoEffProg) c →
      ∀ E v, c.tm = .perform E v → Value v → E ∈ (insert 0 ∅ : EffectSet) :=
  effect_safety demoEff_typed

/-- A program that **performs and discharges** effect `0`: `handle 0 (λ_. ()) (perform 0 ())`.  The
    handler catches the effect, so it does **not** escape — the whole program is typed at row `∅`. -/
def demoHandledProg : Term := .handle 0 (.lam .unit .unit) (.perform 0 .unit)

theorem demoHandled_typed :
    Typing demoSig [] [] demoHandledProg .unit ((insert 0 ∅ : EffectSet).erase 0 ∪ ∅ ∪ ∅) ∅ [] := by
  apply Typing.handle (H := .unit) (εh := ∅)
  · exact Typing.lam Typing.unit rfl
  · exact Typing.perform Typing.unit

/-- **Effect safety, instantiated — discharged.**  The handled program's declared row erases `0`,
    so effect safety still holds (and `0` is discharged, never escaping). -/
theorem demoHandled_safe :
    ∀ c, StepStar demoSig (initConfig demoHandledProg) c →
      ∀ E v, c.tm = .perform E v → Value v → E ∈ ((insert 0 ∅ : EffectSet).erase 0 ∪ ∅ ∪ ∅) :=
  effect_safety demoHandled_typed

/-! ## PR#443 — the bottom type `trap`: an aborting program is sound (C-VAC for the 4th disjunct) -/

/-- A program that **aborts**: the bottom-typed `trap` applied to `()`.  `trap` is well-typed at the
    arrow `unit →[∅] unit`, so the application type-checks; operationally `trap` bubbles out of the
    frame (`trapApp1`), reducing the program to the terminal abort `trap` — never a value, never
    stuck.  This is the Lean mirror of the Rust `Type::Never` `trap()` (PR #443). -/
def demoTrapProg : Term := .app .trap .unit

theorem demoTrap_typed :
    Typing demoSig [] [] demoTrapProg .unit (∅ ∪ ∅ ∪ ∅ : EffectSet) (∅ : Authority) [] := by
  apply Typing.app (A := .unit) (εf := ∅) (ε1 := ∅) (ε2 := ∅)
  · exact Typing.trap
  · exact Typing.unit

/-- **Type soundness, instantiated on an aborting program.**  No configuration reachable from
    `app trap ()` is stuck — it bubbles to the terminal abort `trap`, which `type_soundness` admits
    via the refined 4-way progress (`value | raise | steps | trap`). -/
theorem demoTrap_sound :
    ∀ c, StepStar demoSig (initConfig demoTrapProg) c → ¬ Stuck demoSig c :=
  type_soundness demoTrap_typed

/-- The abort actually fires: `app trap () → trap` (the `trapApp1` bubble step). -/
theorem demoTrap_aborts :
    Step demoSig ⟨demoTrapProg, ∅, ∅⟩ ⟨.trap, ∅, ∅⟩ :=
  Step.trapApp1

/-- **Capability safety, instantiated on the aborting program.**  It exercises no authority, so its
    trace stays within any ceiling — here `∅`. -/
theorem demoTrap_confined :
    ∀ c, StepStar demoSig (initConfig demoTrapProg) c → c.auth ⊆ (∅ : Authority) :=
  capability_safety demoTrap_typed

end LambdaSigil
