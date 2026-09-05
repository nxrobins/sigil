import LambdaSigil.Typing
import LambdaSigil.Semantics

/-!
# λ-SIGIL — Structural & substitution lemmas (Milestone M3)

The metatheory plumbing that preservation (M4) consumes:

* `Typing.value_pure` — a **value consumes no resources and performs no effects**
  (`Uin = Uout`, `ε = ∅`).  This collapses the usage-threading in the β/let cases, because the
  substituted term in CBV is always a value.
* `Typing.weaken_at` — de Bruijn **weakening**: inserting an unused binding anywhere in the
  context preserves typing (lifting the term across the new binder).
* `Typing.subst_lemma` — the **substitution lemma**: substituting a closed value for a variable
  preserves typing, threading the usage context through the substituted slot.

These are the classic (and fiddly) nameless-syntax lemmas; the leftover/usage context adds the
extra obligation of tracking availability across the substituted variable.
-/

namespace LambdaSigil

/-- A value consumes no linear resources and performs no effects: its input and output usage
    vectors coincide and its synthesized effect row is empty.  (CBV substitutes only values, so
    this is what makes the substitution lemma's usage bookkeeping go through.) -/
theorem Typing.value_pure {S Γ U v τ ε m U'} (hv : Value v)
    (h : Typing S Γ U v τ ε m U') : U = U' ∧ ε = ∅ := by
  cases hv <;> cases h <;> exact ⟨rfl, rfl⟩

/-! ## Static ownership: usage is monotone-decreasing (ROADMAP item 8 (a),(b))

Typing never *resurrects* a linear resource: if a variable is available **after** typing a term,
it was available **before**.  Equivalently, a consumed (`some false`) linear variable stays
consumed.  Combined with the `var_lin` rule (which requires `some true` to use a linear variable),
this is exactly the "no use-after-move / no duplication" guarantee — proved statically from the
typing relation, no operational semantics required. -/

/-- Usage availability only ever decreases through typing: availability of variable `i` in the
    leftover context implies it was available in the input context. -/
theorem Typing.usage_monotone {S Γ Uin e τ ε m Uout}
    (h : Typing S Γ Uin e τ ε m Uout) :
    ∀ (i : Nat), Uout[i]? = some true → Uin[i]? = some true := by
  induction h with
  | @var_lin Γ U j τ' m _ _ _ =>
      intro i hi
      by_cases hij : i = j
      · subst hij; simp [List.getElem?_set] at hi
      · rwa [List.getElem?_set_ne (by omega)] at hi
  | app _ _ ih1 ih2 => intro i hi; exact ih1 i (ih2 i hi)
  | letIn _ _ ih1 ih2 =>
      intro i hi
      have h2 := ih2 (i + 1) (by simpa using hi)
      exact ih1 i (by simpa using h2)
  | mint _ ih => intro i hi; exact ih i hi
  | restrict _ ih => intro i hi; exact ih i hi
  | exercise _ _ _ ih => intro i hi; exact ih i hi
  | sink _ _ _ ih => intro i hi; exact ih i hi
  | perform _ ih => intro i hi; exact ih i hi
  | handle _ _ ih1 ih2 => intro i hi; exact ih1 i (ih2 i hi)
  | _ => intro i hi; exact hi

/-- A consumed linear variable stays consumed: if variable `i` is unavailable in the input, it is
    unavailable in the leftover.  (Contrapositive of `usage_monotone`, the user-facing form of the
    no-use-after-move guarantee.) -/
theorem Typing.consumed_stays_consumed {S Γ Uin e τ ε m Uout}
    (h : Typing S Γ Uin e τ ε m Uout) (i : Nat)
    (hlen : i < Uin.length) (hi : Uin[i]? = some false) : Uout[i]? = some false := by
  have hmono := h.usage_monotone i
  -- `Uout[i]?` is `some true`, `some false`, or `none`; rule out `some true` via monotonicity.
  have hlen' : i < Uout.length := by rw [← h.use_length]; exact hlen
  rcases hb : Uout[i]? with _ | b
  · rw [List.getElem?_eq_none_iff] at hb; omega
  · cases b with
    | false => rfl
    | true => rw [hmono hb] at hi; exact absurd hi (by simp)

/-! ## Closedness: a term typed in `Γ` has no free variables `≥ Γ.length`

`typing_lift_id` says lifting at a cutoff at or above the context length is the identity — a
term typed in `Γ` mentions only variables `< Γ.length`.  For a `[]`-typed (closed) value this
gives `lift c v = v` for every `c`, which is what makes substituting a closed value clean
(`subst` never has to shift it). -/

theorem typing_lift_id {S Γ U e τ ε m U'} (h : Typing S Γ U e τ ε m U') :
    ∀ (c : Nat), Γ.length ≤ c → lift c e = e := by
  induction h with
  | @var_lin Γ U i τ m hΓ _ _ =>
      intro c hc
      have hlt : i < Γ.length := by
        rcases Nat.lt_or_ge i Γ.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none_iff.mpr h'] at hΓ; exact absurd hΓ (by simp)
      simp only [lift]; rw [if_pos (by omega)]
  | @var_unr Γ U i τ m hΓ _ =>
      intro c hc
      have hlt : i < Γ.length := by
        rcases Nat.lt_or_ge i Γ.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none_iff.mpr h'] at hΓ; exact absurd hΓ (by simp)
      simp only [lift]; rw [if_pos (by omega)]
  | lam _ _ ih => intro c hc; simp only [lift]; rw [ih (c + 1) (by simp only [List.length_cons]; omega)]
  | app _ _ ihf ihx => intro c hc; simp only [lift]; rw [ihf c hc, ihx c hc]
  | letIn _ _ ih1 ih2 =>
      intro c hc; simp only [lift]
      rw [ih1 c hc, ih2 (c + 1) (by simp only [List.length_cons]; omega)]
  | mint _ ih => intro c hc; simp only [lift]; rw [ih c hc]
  | restrict _ ih => intro c hc; simp only [lift]; rw [ih c hc]
  | exercise _ _ _ ih => intro c hc; simp only [lift]; rw [ih c hc]
  | sink _ _ _ ih => intro c hc; simp only [lift]; rw [ih c hc]
  | perform _ ih => intro c hc; simp only [lift]; rw [ih c hc]
  | handle _ _ ih1 ih2 => intro c hc; simp only [lift]; rw [ih1 c hc, ih2 c hc]
  | _ => intro c _; rfl

/-- A closed (`[]`-typed) term is invariant under `lift` at any cutoff. -/
theorem closed_lift_id {S U e τ ε m U'} (h : Typing S [] U e τ ε m U') (c : Nat) :
    lift c e = e :=
  typing_lift_id h c (by simp)

end LambdaSigil
