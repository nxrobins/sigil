import LambdaSigil.Progress

/-!
# λ-SIGIL — Preservation and type soundness (Milestone M4, part 2)

`progress` is proven on the usage-tracking `Typing` judgment. For **preservation** we work over a
**usage-erased** judgment `WT` (well-typed, no linearity), because the substitution lemma then needs
no usage-vector bookkeeping — only de Bruijn context surgery, which `grind` discharges. This is the
plan's sanctioned plan B: exact-usage `weaken` would require hand-proved `set`/`insertIdx`/`eraseIdx`
commutation lemmas (`grind` does not close the `n ≤ i` case), whereas `WT` eliminates them entirely.

The split of concerns is clean and loses nothing:
* **Affine ownership** stays on `Typing` (`usage_monotone` / `consumed_stays_consumed`, M3).
* **Capability safety** stays on the structural `AuthBound` invariant (M5).
* **Type soundness** (no reachable stuck state) goes through `WT`: `Typing ⇒ WT` (erasure), then
  `WT` preservation + a re-derived `WT.progress`.

`WT` is strictly more permissive than `Typing` (it forgets the affine discipline), so progress is at
least as easy; and every `Typing`-well-typed program is `WT`-well-typed.
-/

namespace LambdaSigil

/-- Usage-erased typing: the `Typing` rules with the linearity/usage vector removed. -/
inductive WT (S : Sig) : Ctx → Term → Ty → EffectSet → Authority → Prop where
  | var {Γ i τ m} : Γ[i]? = some τ → WT S Γ (.var i) τ ∅ m
  | unit {Γ m} : WT S Γ .unit .unit ∅ m
  | tt {Γ m} : WT S Γ .true .bool ∅ m
  | ff {Γ m} : WT S Γ .false .bool ∅ m
  | lam {Γ A body B εb m} :
      WT S (A :: Γ) body B εb m → WT S Γ (.lam A body) (.arrow A εb B) ∅ m
  | app {Γ f x A εf B ε1 ε2 m} :
      WT S Γ f (.arrow A εf B) ε1 m → WT S Γ x A ε2 m → WT S Γ (.app f x) B (ε1 ∪ ε2 ∪ εf) m
  | letIn {Γ e1 A ε1 e2 B ε2 m} :
      WT S Γ e1 A ε1 m → WT S (A :: Γ) e2 B ε2 m → WT S Γ (.letIn e1 e2) B (ε1 ∪ ε2) m
  | mintTok {Γ κ m} : WT S Γ (.mintTok κ) (.mintAuth κ) ∅ m
  | mint {Γ κ tok εt m} :
      WT S Γ tok (.mintAuth κ) εt m → WT S Γ (.mint κ tok) (.cap κ (S.fullMask κ)) εt m
  | capVal {Γ κ k m} : k ⊆ S.fullMask κ → WT S Γ (.capVal κ k) (.cap κ k) ∅ m
  | restrict {Γ k e κ k0 εe m} :
      WT S Γ e (.cap κ k0) εe m → WT S Γ (.restrict k e) (.cap κ (LambdaSigil.restrict k0 k)) εe m
  | exercise {Γ a e κ k εe m} :
      WT S Γ e (.cap κ k) εe m → a ∈ k → a ∈ m → WT S Γ (.exercise a e) .unit εe m
  /-- M7: `sink req e` — the full-mask authority sink (C003).  `req ⊆ k` is the `sinkOk` check. -/
  | sink {Γ req e κ k εe m} :
      WT S Γ e (.cap κ k) εe m → req ⊆ k → req ⊆ m → WT S Γ (.sink req e) .unit εe m
  /-- M6: `perform E e` — result type is **any** `τ` (bottom / abortive; H-1). -/
  | perform {Γ E e εe m} {τ : Ty} :
      WT S Γ e (S.effParam E) εe m → WT S Γ (.perform E e) τ (insert E εe) m
  /-- M6: `handle E h body` (abortive) — **discharges** `E` from the body's row. -/
  | handle {Γ E h body H εh εb ρh m} :
      WT S Γ h (.arrow (S.effParam E) εh H) ρh m →
      WT S Γ body H εb m →
      WT S Γ (.handle E h body) H ((εb.erase E) ∪ εh ∪ ρh) m
  /-- PR#443: `trap` — the bottom type, any `τ`, no effects (`∅`). -/
  | trap {Γ m} {τ : Ty} : WT S Γ .trap τ ∅ m

/-- Every `Typing`-well-typed term is `WT`-well-typed (erase the usage vector). -/
theorem Typing.toWT {S Γ U e τ ε m U'} (h : Typing S Γ U e τ ε m U') : WT S Γ e τ ε m := by
  induction h with
  | var_lin hΓ _ _ => exact WT.var hΓ
  | var_unr hΓ _ => exact WT.var hΓ
  | unit => exact WT.unit
  | tt => exact WT.tt
  | ff => exact WT.ff
  | lam _ _ ih => exact WT.lam ih
  | app _ _ ih1 ih2 => exact WT.app ih1 ih2
  | letIn _ _ ih1 ih2 => exact WT.letIn ih1 ih2
  | mintTok => exact WT.mintTok
  | mint _ ih => exact WT.mint ih
  | capVal hk => exact WT.capVal hk
  | restrict _ ih => exact WT.restrict ih
  | exercise _ hak ham ih => exact WT.exercise ih hak ham
  | sink _ hsink hm ih => exact WT.sink ih hsink hm
  | perform _ ih => exact WT.perform ih
  | handle _ _ ih1 ih2 => exact WT.handle ih1 ih2
  | trap => exact WT.trap

/-! ## Closedness and weakening -/

/-- A `WT`-typed term has no free variable `≥ Γ.length`, so lifting above the context is identity. -/
theorem WT.lift_id {S Γ e τ ε m} (h : WT S Γ e τ ε m) :
    ∀ (c : Nat), Γ.length ≤ c → lift c e = e := by
  induction h with
  | @var Γ i τ m hΓ =>
      intro c hc
      have hlt : i < Γ.length := by
        rcases Nat.lt_or_ge i Γ.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none_iff.mpr h'] at hΓ; exact absurd hΓ (by simp)
      simp only [lift]; rw [if_pos (by omega)]
  | lam _ ih => intro c hc; simp only [lift]; rw [ih (c + 1) (by simp only [List.length_cons]; omega)]
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

/-- A closed (`[]`-typed) term is `lift`-invariant. -/
theorem WT.closed_lift_id {S v τ ε m} (h : WT S [] v τ ε m) (c : Nat) : lift c v = v :=
  WT.lift_id h c (by simp)

/-- Weakening: insert a binding anywhere and lift; no usage to thread, so `grind` closes the
    `getElem?_insertIdx` side goals. -/
theorem WT.weaken {S Γ e τ ε m} (h : WT S Γ e τ ε m) :
    ∀ (n : Nat) (B : Ty), WT S (Γ.insertIdx n B) (lift n e) τ ε m := by
  induction h with
  | @var Γ i τ m hΓ =>
      intro n B
      simp only [lift]
      by_cases hic : i < n
      · rw [if_pos hic]; exact WT.var (by rw [List.getElem?_insertIdx_of_lt hic]; exact hΓ)
      · rw [if_neg hic]
        exact WT.var (by rw [List.getElem?_insertIdx_of_gt (by omega)]; simpa using hΓ)
  | @lam Γ A body B' εb m _ ih =>
      intro n B; simp only [lift]
      refine WT.lam ?_
      have hb := ih (n + 1) B
      rwa [show (A :: Γ).insertIdx (n + 1) B = A :: Γ.insertIdx n B from by grind] at hb
  | @letIn Γ e1 A ε1 e2 B' ε2 m _ _ ih1 ih2 =>
      intro n B; simp only [lift]
      refine WT.letIn (ih1 n B) ?_
      have hb := ih2 (n + 1) B
      rwa [show (A :: Γ).insertIdx (n + 1) B = A :: Γ.insertIdx n B from by grind] at hb
  | app _ _ ihf ihx => intro n B; simp only [lift]; exact WT.app (ihf n B) (ihx n B)
  | mint _ ih => intro n B; simp only [lift]; exact WT.mint (ih n B)
  | restrict _ ih => intro n B; simp only [lift]; exact WT.restrict (ih n B)
  | exercise _ hak ham ih => intro n B; simp only [lift]; exact WT.exercise (ih n B) hak ham
  | sink _ hsink hm ih => intro n B; simp only [lift]; exact WT.sink (ih n B) hsink hm
  | perform _ ih => intro n B; simp only [lift]; exact WT.perform (ih n B)
  | handle _ _ ih1 ih2 => intro n B; simp only [lift]; exact WT.handle (ih1 n B) (ih2 n B)
  | @capVal Γ κ k m hk => intro n B; exact WT.capVal hk
  | trap => intro n B; simp only [lift]; exact WT.trap
  | _ => intro n B; first | exact WT.unit | exact WT.tt | exact WT.ff | exact WT.mintTok

/-- A closed term is typeable in any context. -/
theorem WT.closed_weaken {S v τ ε m} (h : WT S [] v τ ε m) : ∀ (Γ : Ctx), WT S Γ v τ ε m := by
  intro Γ
  induction Γ with
  | nil => exact h
  | cons B Γ ih =>
      have hw := WT.weaken ih 0 B
      rw [List.insertIdx_zero, WT.closed_lift_id h 0] at hw
      exact hw

/-! ## The substitution lemma -/

/-- **Substitution lemma.**  Substituting a closed value `v : A` for the variable at position
    `Δ.length` in a body typed under `Δ ++ A :: Γ` yields a term typed under `Δ ++ Γ`, preserving
    type and effect row.  Pure de Bruijn context surgery — no usage vector. -/
theorem WT.subst_lemma {S A Γ m v} (hv : WT S [] v A ∅ m) :
    ∀ (body : Term) (Δ : Ctx) (B : Ty) (ε : EffectSet),
      WT S (Δ ++ A :: Γ) body B ε m → WT S (Δ ++ Γ) (subst Δ.length v body) B ε m := by
  intro body
  induction body with
  | var i =>
      intro Δ B ε hb
      cases hb with
      | var hΓ =>
          simp only [subst]
          split
          · -- i = Δ.length : the substituted variable
            rename_i h1
            rw [h1] at hΓ
            simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
              List.getElem?_cons_zero] at hΓ
            obtain rfl : A = B := Option.some.inj hΓ
            exact WT.closed_weaken hv _
          · split
            · -- Δ.length < i : a variable from Γ, index shifts down by one
              rename_i h1 h2
              refine WT.var ?_
              rw [List.getElem?_append_right (by omega)] at hΓ
              rw [List.getElem?_append_right (by omega)]
              rw [show i - Δ.length = (i - 1 - Δ.length) + 1 by omega] at hΓ
              rwa [List.getElem?_cons_succ] at hΓ
            · -- i < Δ.length : a variable from Δ, unchanged
              rename_i h1 h2
              refine WT.var ?_
              rw [List.getElem?_append_left (by omega)] at hΓ
              rwa [List.getElem?_append_left (by omega)]
  | lam A' body' ih =>
      intro Δ B ε hb
      cases hb with
      | lam hbody =>
          simp only [subst, WT.closed_lift_id hv]
          exact WT.lam (ih (A' :: Δ) _ _ hbody)
  | app f x ihf ihx =>
      intro Δ B ε hb
      cases hb with
      | app hf hx => simp only [subst]; exact WT.app (ihf Δ _ _ hf) (ihx Δ _ _ hx)
  | letIn e1 e2 ih1 ih2 =>
      intro Δ B ε hb
      cases hb with
      | letIn h1 h2 =>
          simp only [subst, WT.closed_lift_id hv]
          exact WT.letIn (ih1 Δ _ _ h1) (ih2 (_ :: Δ) _ _ h2)
  | mint κ t ih =>
      intro Δ B ε hb
      cases hb with
      | mint ht => simp only [subst]; exact WT.mint (ih Δ _ _ ht)
  | restrict k t ih =>
      intro Δ B ε hb
      cases hb with
      | restrict ht => simp only [subst]; exact WT.restrict (ih Δ _ _ ht)
  | exercise a t ih =>
      intro Δ B ε hb
      cases hb with
      | exercise ht hak ham => simp only [subst]; exact WT.exercise (ih Δ _ _ ht) hak ham
  | sink req t ih =>
      intro Δ B ε hb
      cases hb with
      | sink ht hsink hm => simp only [subst]; exact WT.sink (ih Δ _ _ ht) hsink hm
  | capVal κ k =>
      intro Δ B ε hb; cases hb with | capVal hk => exact WT.capVal hk
  | unit => intro Δ B ε hb; cases hb with | unit => exact WT.unit
  | «true» => intro Δ B ε hb; cases hb with | tt => exact WT.tt
  | «false» => intro Δ B ε hb; cases hb with | ff => exact WT.ff
  | mintTok κ => intro Δ B ε hb; cases hb with | mintTok => exact WT.mintTok
  | perform E t ih =>
      intro Δ B ε hb
      cases hb with
      | perform ht => simp only [subst]; exact WT.perform (ih Δ _ _ ht)
  | handle E hh b ih1 ih2 =>
      intro Δ B ε hb
      cases hb with
      | handle hhh hbody =>
          simp only [subst]; exact WT.handle (ih1 Δ _ _ hhh) (ih2 Δ _ _ hbody)
  | trap =>
      intro Δ B ε hb
      cases hb with
      | trap => simp only [subst]; exact WT.trap

/-- Substitute a closed value for the innermost variable (the β/let contractum case). -/
theorem WT.subst0 {S A Γ m v body B ε} (hv : WT S [] v A ∅ m)
    (hbody : WT S (A :: Γ) body B ε m) : WT S Γ (subst0 v body) B ε m :=
  WT.subst_lemma hv body [] B ε hbody

/-! ## Progress (on `WT`) -/

/-- A value performs no effects under `WT`. -/
theorem WT.value_pure {S Γ v τ ε m} (hv : Value v) (h : WT S Γ v τ ε m) : ε = ∅ := by
  cases hv <;> cases h <;> rfl

theorem WT.canon_arrow {S Γ v A ε B ε' m} (hv : Value v) (h : WT S Γ v (.arrow A ε B) ε' m) :
    ∃ body, v = .lam A body := by cases hv <;> cases h; exact ⟨_, rfl⟩

theorem WT.canon_cap {S Γ v κ k ε' m} (hv : Value v) (h : WT S Γ v (.cap κ k) ε' m) :
    v = .capVal κ k := by cases hv <;> cases h; rfl

theorem WT.canon_mintAuth {S Γ v κ ε' m} (hv : Value v) (h : WT S Γ v (.mintAuth κ) ε' m) :
    v = .mintTok κ := by cases hv <;> cases h; rfl

/-- **Progress** (on `WT`).  A closed `WT`-well-typed term is a value, a **raise** (`perform E v`,
    `v` a value — a terminal escaping effect), or it steps.  The new disjunct is needed exactly for a
    top-level `perform E v`; `handle` always steps (return / catch / propagate / body-congruence). -/
theorem WT.progress {S : Sig} (A : Authority) (E : EffectSet) {e : Term} :
    ∀ {τ ε m}, WT S [] e τ ε m →
      (Value e ∨ (∃ E' v, e = .perform E' v ∧ Value v) ∨ (∃ c', Step S ⟨e, A, E⟩ c') ∨
        e = .trap) := by
  induction e with
  | var i => intro _ _ _ h; cases h with | var hΓ => simp at hΓ
  | unit => intro _ _ _ _; exact Or.inl Value.unit
  | «true» => intro _ _ _ _; exact Or.inl Value.true
  | «false» => intro _ _ _ _; exact Or.inl Value.false
  | lam A b _ => intro _ _ _ _; exact Or.inl Value.lam
  | mintTok κ => intro _ _ _ _; exact Or.inl Value.mintTok
  | capVal κ k => intro _ _ _ _; exact Or.inl Value.capVal
  | app f x ihf ihx =>
      intro _ _ _ h
      cases h with
      | app hf hx =>
          rcases ihf hf with hvf | ⟨E', v, rfl, hv⟩ | ⟨cf, hsf⟩ | htrapf
          · obtain ⟨body, rfl⟩ := WT.canon_arrow hvf hf
            rcases ihx hx with hvx | ⟨E2, w, rfl, hw⟩ | ⟨cx, hsx⟩ | htrapx
            · exact Or.inr (Or.inr (Or.inl ⟨_, Step.beta hvx⟩))
            · exact Or.inr (Or.inr (Or.inl ⟨_, Step.raiseApp2 hvf hw⟩))
            · obtain ⟨x', Ax, Ex⟩ := cx; exact Or.inr (Or.inr (Or.inl ⟨_, Step.app2 hvf hsx⟩))
            · subst htrapx; exact Or.inr (Or.inr (Or.inl ⟨_, Step.trapApp2 hvf⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨_, Step.raiseApp1 hv⟩))
          · obtain ⟨f', Af, Ef⟩ := cf; exact Or.inr (Or.inr (Or.inl ⟨_, Step.app1 hsf⟩))
          · subst htrapf; exact Or.inr (Or.inr (Or.inl ⟨_, Step.trapApp1⟩))
  | letIn e1 e2 ih1 _ =>
      intro _ _ _ h
      cases h with
      | letIn h1 h2 =>
          rcases ih1 h1 with hv1 | ⟨E', v, rfl, hv⟩ | ⟨c1, hs1⟩ | htrap1
          · exact Or.inr (Or.inr (Or.inl ⟨_, Step.letBeta hv1⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨_, Step.raiseLet hv⟩))
          · obtain ⟨e1', A1, E1⟩ := c1; exact Or.inr (Or.inr (Or.inl ⟨_, Step.let1 hs1⟩))
          · subst htrap1; exact Or.inr (Or.inr (Or.inl ⟨_, Step.trapLet⟩))
  | mint κ t ih =>
      intro _ _ _ h
      cases h with
      | mint ht =>
          rcases ih ht with hvt | ⟨E', v, rfl, hv⟩ | ⟨ct, hst⟩ | htrapt
          · obtain rfl := WT.canon_mintAuth hvt ht; exact Or.inr (Or.inr (Or.inl ⟨_, Step.mintRed⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨_, Step.raiseMint hv⟩))
          · obtain ⟨t', At, Et⟩ := ct; exact Or.inr (Or.inr (Or.inl ⟨_, Step.mint1 hst⟩))
          · subst htrapt; exact Or.inr (Or.inr (Or.inl ⟨_, Step.trapMint⟩))
  | restrict k t ih =>
      intro _ _ _ h
      cases h with
      | restrict ht =>
          rcases ih ht with hvt | ⟨E', v, rfl, hv⟩ | ⟨ct, hst⟩ | htrapt
          · obtain rfl := WT.canon_cap hvt ht; exact Or.inr (Or.inr (Or.inl ⟨_, Step.restrictRed⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨_, Step.raiseRestrict hv⟩))
          · obtain ⟨t', At, Et⟩ := ct; exact Or.inr (Or.inr (Or.inl ⟨_, Step.restrict1 hst⟩))
          · subst htrapt; exact Or.inr (Or.inr (Or.inl ⟨_, Step.trapRestrict⟩))
  | exercise a t ih =>
      intro _ _ _ h
      cases h with
      | exercise ht hak _ =>
          rcases ih ht with hvt | ⟨E', v, rfl, hv⟩ | ⟨ct, hst⟩ | htrapt
          · obtain rfl := WT.canon_cap hvt ht; exact Or.inr (Or.inr (Or.inl ⟨_, Step.exerciseRed hak⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨_, Step.raiseExercise hv⟩))
          · obtain ⟨t', At, Et⟩ := ct; exact Or.inr (Or.inr (Or.inl ⟨_, Step.exercise1 hst⟩))
          · subst htrapt; exact Or.inr (Or.inr (Or.inl ⟨_, Step.trapExercise⟩))
  | sink req t ih =>
      intro _ _ _ h
      cases h with
      | sink ht hsink _ =>
          rcases ih ht with hvt | ⟨E', v, rfl, hv⟩ | ⟨ct, hst⟩ | htrapt
          · obtain rfl := WT.canon_cap hvt ht; exact Or.inr (Or.inr (Or.inl ⟨_, Step.sinkRed hsink⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨_, Step.raiseSink hv⟩))
          · obtain ⟨t', At, Et⟩ := ct; exact Or.inr (Or.inr (Or.inl ⟨_, Step.sink1 hst⟩))
          · subst htrapt; exact Or.inr (Or.inr (Or.inl ⟨_, Step.trapSink⟩))
  | perform Eop t ih =>
      intro _ _ _ h
      cases h with
      | perform ht =>
          rcases ih ht with hvt | ⟨E', v, rfl, hv⟩ | ⟨ct, hst⟩ | htrapt
          · exact Or.inr (Or.inl ⟨Eop, t, rfl, hvt⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨_, Step.raisePerform hv⟩))
          · obtain ⟨t', At, Et⟩ := ct; exact Or.inr (Or.inr (Or.inl ⟨_, Step.perform1 hst⟩))
          · subst htrapt; exact Or.inr (Or.inr (Or.inl ⟨_, Step.trapPerform⟩))
  | handle Eh hh b _ ihb =>
      intro _ _ _ h
      cases h with
      | handle hhh hbody =>
          rcases ihb hbody with hvb | ⟨E', v, rfl, hv⟩ | ⟨cb, hsb⟩ | htrapb
          · exact Or.inr (Or.inr (Or.inl ⟨_, Step.handleReturn hvb⟩))
          · by_cases hEE : E' = Eh
            · subst hEE; exact Or.inr (Or.inr (Or.inl ⟨_, Step.handleCatch hv⟩))
            · exact Or.inr (Or.inr (Or.inl ⟨_, Step.handlePropagate hEE hv⟩))
          · obtain ⟨b', Ab, Eb⟩ := cb; exact Or.inr (Or.inr (Or.inl ⟨_, Step.handleBody hsb⟩))
          · subst htrapb; exact Or.inr (Or.inr (Or.inl ⟨_, Step.trapHandle⟩))
  | trap => intro _ _ _ _; exact Or.inr (Or.inr (Or.inr rfl))

/-! ## Preservation and type soundness -/

/-- **Preservation** (on `WT`).  Reduction preserves the type `τ` and a **shrinking** effect row
    (`∃ ε' ⊆ ε`).  Raise-propagation re-types the raise at the frame's type (H-1); `catch` shrinks
    the row because the abort discards the body's other effects.  The β/`let` cases use the
    substitution lemma. -/
theorem preservation {S : Sig} {c c' : Config} (hs : Step S c c') :
    ∀ {τ ε m}, WT S [] c.tm τ ε m → ∃ ε', ε' ⊆ ε ∧ WT S [] c'.tm τ ε' m := by
  induction hs with
  | beta hv =>
      intro τ ε m h
      cases h with
      | app hf hx => cases hf with
        | lam hbody => obtain rfl := WT.value_pure hv hx; exact ⟨_, by simp, WT.subst0 hx hbody⟩
  | app1 _ ih =>
      intro τ ε m h
      cases h with | app hf hx => obtain ⟨ε', hsub, wt⟩ := ih hf; exact ⟨_, by gcongr, WT.app wt hx⟩
  | app2 _ _ ih =>
      intro τ ε m h
      cases h with | app hf hx => obtain ⟨ε', hsub, wt⟩ := ih hx; exact ⟨_, by gcongr, WT.app hf wt⟩
  | letBeta hv =>
      intro τ ε m h
      cases h with
      | letIn h1 h2 => obtain rfl := WT.value_pure hv h1; exact ⟨_, by simp, WT.subst0 h1 h2⟩
  | let1 _ ih =>
      intro τ ε m h
      cases h with
      | letIn h1 h2 => obtain ⟨ε', hsub, wt⟩ := ih h1; exact ⟨_, by gcongr, WT.letIn wt h2⟩
  | mintRed =>
      intro τ ε m h
      cases h with | mint htok => cases htok; exact ⟨_, subset_rfl, WT.capVal subset_rfl⟩
  | mint1 _ ih =>
      intro τ ε m h
      cases h with | mint htok => obtain ⟨ε', hsub, wt⟩ := ih htok; exact ⟨_, hsub, WT.mint wt⟩
  | restrictRed =>
      intro τ ε m h
      cases h with
      | restrict hcap => cases hcap with
        | capVal hk =>
            exact ⟨_, subset_rfl, WT.capVal (Finset.Subset.trans (restrict_cannot_amplify _ _) hk)⟩
  | restrict1 _ ih =>
      intro τ ε m h
      cases h with | restrict hcap => obtain ⟨ε', hsub, wt⟩ := ih hcap; exact ⟨_, hsub, WT.restrict wt⟩
  | exerciseRed _ =>
      intro τ ε m h
      cases h with
      | exercise hcap _ _ => cases hcap with | capVal _ => exact ⟨_, subset_rfl, WT.unit⟩
  | exercise1 _ ih =>
      intro τ ε m h
      cases h with
      | exercise hcap ha hm => obtain ⟨ε', hsub, wt⟩ := ih hcap; exact ⟨_, hsub, WT.exercise wt ha hm⟩
  -- M7: the full-mask sink
  | sinkRed _ =>
      intro τ ε m h
      cases h with
      | sink hcap _ _ => cases hcap with | capVal _ => exact ⟨_, subset_rfl, WT.unit⟩
  | sink1 _ ih =>
      intro τ ε m h
      cases h with
      | sink hcap hsink hm => obtain ⟨ε', hsub, wt⟩ := ih hcap; exact ⟨_, hsub, WT.sink wt hsink hm⟩
  | raiseSink _ =>
      intro τ ε m h
      cases h with | sink ht _ _ => cases ht with | perform hp => exact ⟨_, subset_rfl, WT.perform hp⟩
  -- M6: effect handlers (bubbling)
  | perform1 _ ih =>
      intro τ ε m h
      cases h with
      | perform ht => obtain ⟨ε', hsub, wt⟩ := ih ht; exact ⟨_, by gcongr, WT.perform wt⟩
  | raiseApp1 _ =>
      intro τ ε m h
      cases h with | app hf hx => cases hf with
        | perform ht =>
            exact ⟨_, by intro x; simp only [Finset.mem_union]; tauto, WT.perform ht⟩
  | raiseApp2 _ _ =>
      intro τ ε m h
      cases h with | app hf hx => cases hx with
        | perform ht => refine ⟨_, ?_, WT.perform ht⟩; intro x hx; simp_all [Finset.mem_union]
  | raiseLet _ =>
      intro τ ε m h
      cases h with | letIn h1 h2 => cases h1 with
        | perform ht => exact ⟨_, Finset.subset_union_left, WT.perform ht⟩
  | raiseMint _ =>
      intro τ ε m h
      cases h with | mint ht => cases ht with | perform hp => exact ⟨_, subset_rfl, WT.perform hp⟩
  | raiseRestrict _ =>
      intro τ ε m h
      cases h with | restrict ht => cases ht with | perform hp => exact ⟨_, subset_rfl, WT.perform hp⟩
  | raiseExercise _ =>
      intro τ ε m h
      cases h with | exercise ht _ _ => cases ht with | perform hp => exact ⟨_, subset_rfl, WT.perform hp⟩
  | raisePerform _ =>
      intro τ ε m h
      cases h with | perform ht => cases ht with
        | perform hp => exact ⟨_, Finset.subset_insert _ _, WT.perform hp⟩
  | handleBody _ ih =>
      intro τ ε m h
      cases h with
      | handle hh hbody => obtain ⟨ε', hsub, wt⟩ := ih hbody; exact ⟨_, by gcongr, WT.handle hh wt⟩
  | handleCatch hv =>
      intro τ ε m h
      cases h with
      | handle hh hbody => cases hbody with
        | perform ht =>
            obtain rfl := WT.value_pure hv ht
            refine ⟨_, ?_, WT.app hh ht⟩
            intro x; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert]; aesop
  | handlePropagate hne hv =>
      intro τ ε m h
      cases h with
      | handle hh hbody => cases hbody with
        | perform ht =>
            obtain rfl := WT.value_pure hv ht
            refine ⟨_, ?_, WT.perform ht⟩
            intro x; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert]; aesop
  | handleReturn hv =>
      intro τ ε m h
      cases h with
      | handle hh hbody =>
          obtain rfl := WT.value_pure hv hbody
          exact ⟨_, Finset.empty_subset _, hbody⟩
  -- `trap`-bubble cases: each frame reduces to `.trap`, which re-types at any `τ` with an empty row
  -- (`WT.trap`, `∅ ⊆ ε`).  Exactly the polymorphic re-typing the `raise*` cases do, but nullary.
  | trapApp1 => intro τ ε m _; exact ⟨_, Finset.empty_subset _, WT.trap⟩
  | trapApp2 _ => intro τ ε m _; exact ⟨_, Finset.empty_subset _, WT.trap⟩
  | trapLet => intro τ ε m _; exact ⟨_, Finset.empty_subset _, WT.trap⟩
  | trapMint => intro τ ε m _; exact ⟨_, Finset.empty_subset _, WT.trap⟩
  | trapRestrict => intro τ ε m _; exact ⟨_, Finset.empty_subset _, WT.trap⟩
  | trapExercise => intro τ ε m _; exact ⟨_, Finset.empty_subset _, WT.trap⟩
  | trapSink => intro τ ε m _; exact ⟨_, Finset.empty_subset _, WT.trap⟩
  | trapPerform => intro τ ε m _; exact ⟨_, Finset.empty_subset _, WT.trap⟩
  | trapHandle => intro τ ε m _; exact ⟨_, Finset.empty_subset _, WT.trap⟩

/-- Every configuration reachable from a `WT`-well-typed start is `WT`-well-typed at a row `⊆ ε`. -/
theorem reachable_WT {S : Sig} {e τ ε m} (h : WT S [] e τ ε m) :
    ∀ {c : Config}, StepStar S ⟨e, ∅, ∅⟩ c → ∃ ε', ε' ⊆ ε ∧ WT S [] c.tm τ ε' m := by
  intro c hstar
  induction hstar with
  | refl => exact ⟨_, subset_rfl, h⟩
  | tail _ hstep ih =>
      obtain ⟨εm, hsubm, wtm⟩ := ih
      obtain ⟨ε', hsub', wt'⟩ := preservation hstep wtm
      exact ⟨_, hsub'.trans hsubm, wt'⟩

/-- **Type soundness.**  No configuration reachable from a well-typed program is stuck — every
    reachable term is a value, a raise, or can step.  (Combines `Typing ⇒ WT`, `WT` preservation,
    and `WT.progress`.) -/
theorem type_soundness {S : Sig} {e τ ε m U'} (h : Typing S [] [] e τ ε m U') :
    ∀ c, StepStar S (initConfig e) c → ¬ Stuck S c := by
  intro c hstar hstuck
  obtain ⟨ε', _, hwt⟩ := reachable_WT h.toWT hstar
  rcases WT.progress c.auth c.eff hwt with hv | ⟨E', v, he, hvv⟩ | ⟨c', hstep⟩ | htrap
  · exact hstuck.1 hv
  · exact hstuck.2.1 ⟨E', v, he, hvv⟩
  · exact hstuck.2.2.2 ⟨c', hstep⟩
  · exact hstuck.2.2.1 htrap

/-- **Effect safety.**  A well-typed program only ever lets effects in its declared row `ε` escape:
    any reachable terminal raise `perform E v` has `E ∈ ε` (handlers discharge the rest).  Falls out
    of preservation + the `perform` rule (`E ∈` the row), exactly as `capability_safety` falls out of
    `AuthBound`. -/
theorem effect_safety {S : Sig} {e τ ε m U'} (h : Typing S [] [] e τ ε m U') :
    ∀ c, StepStar S (initConfig e) c → ∀ E v, c.tm = .perform E v → Value v → E ∈ ε := by
  intro c hstar E v hcv hvv
  obtain ⟨ε', hsub, hwt⟩ := reachable_WT h.toWT hstar
  rw [hcv] at hwt
  cases hwt with
  | perform _ => exact hsub (Finset.mem_insert_self _ _)

end LambdaSigil
