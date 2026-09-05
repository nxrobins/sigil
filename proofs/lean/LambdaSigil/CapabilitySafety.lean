import LambdaSigil.Progress

/-!
# λ-SIGIL — Capability safety (Milestone M5)

The headline authority-confinement theorem:

  `capability_safety : ⊢ e : τ ! ε @ m → ∀ reachable c, c.auth ⊆ m`

i.e. a well-typed program never exercises authority outside its static ceiling `m`.

The proof goes through a **structural** predicate `AuthBound m e` ("every `exercise a _`
subterm of `e` satisfies `a ∈ m`") rather than full type preservation:

* typing implies `AuthBound` (`authBound_of_typing` — the `exercise` rule's `a ∈ m` premise);
* `AuthBound` is preserved by reduction (`step_authBound`), because `subst` only *copies*
  subterms and never invents a new authority — so no substitution-*typing* lemma is needed;
* every reduction step grows the authority trace by authorities already `∈ m`.

Threading the invariant `AuthBound m c.tm ∧ c.auth ⊆ m` along `StepStar` gives the theorem.
This mirrors `air_capability_v2`'s guarantee (the C003 sink check) at the level of the calculus.
-/

namespace LambdaSigil

/-- `AuthBound m e`: every authority exercised anywhere inside `e` lies within the ceiling `m`. -/
def AuthBound (m : Authority) : Term → Prop
  | .var _ => True
  | .unit => True
  | .true => True
  | .false => True
  | .lam _ b => AuthBound m b
  | .app f x => AuthBound m f ∧ AuthBound m x
  | .letIn a b => AuthBound m a ∧ AuthBound m b
  | .mintTok _ => True
  | .mint _ t => AuthBound m t
  | .capVal _ _ => True
  | .restrict _ t => AuthBound m t
  | .exercise a t => a ∈ m ∧ AuthBound m t
  | .sink req t => req ⊆ m ∧ AuthBound m t
  | .perform _ t => AuthBound m t
  | .handle _ h b => AuthBound m h ∧ AuthBound m b
  | .trap => True

/-- A well-typed term keeps all of its authority exercises within the ceiling `m` — directly from
    the `exercise` rule's `a ∈ m` premise. -/
theorem authBound_of_typing {S Γ U e τ ε m U'} (h : Typing S Γ U e τ ε m U') :
    AuthBound m e := by
  induction h with
  | exercise _ _ ham ih => exact ⟨ham, ih⟩
  | sink _ _ hm ih => exact ⟨hm, ih⟩
  | app _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letIn _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | lam _ _ ih => exact ih
  | mint _ ih => exact ih
  | restrict _ ih => exact ih
  | _ => trivial

/-- Lifting (shifting de Bruijn indices) preserves `AuthBound` — it does not touch authorities. -/
theorem authBound_lift {m : Authority} (e : Term) :
    ∀ (c : Nat), AuthBound m e → AuthBound m (lift c e) := by
  induction e with
  | lam A b ih => intro c h; exact ih (c + 1) h
  | app f x ihf ihx => intro c h; exact ⟨ihf c h.1, ihx c h.2⟩
  | letIn a b iha ihb => intro c h; exact ⟨iha c h.1, ihb (c + 1) h.2⟩
  | mint κ t ih => intro c h; exact ih c h
  | restrict k t ih => intro c h; exact ih c h
  | exercise a t ih => intro c h; exact ⟨h.1, ih c h.2⟩
  | sink req t ih => intro c h; exact ⟨h.1, ih c h.2⟩
  | perform E t ih => intro c h; exact ih c h
  | handle E hh b ihh ihb => intro c h; exact ⟨ihh c h.1, ihb c h.2⟩
  | var i => intro c _; simp only [lift]; split <;> trivial
  | _ => intro c _; trivial

/-- Substitution preserves `AuthBound`: `subst` only copies the (bounded) value `v` into `e`,
    never creating an authority exercise outside `m`.  This is the structural fact that replaces
    a substitution-*typing* lemma for the purposes of capability safety. -/
theorem authBound_subst {m : Authority} (e : Term) :
    ∀ (j : Nat) (v : Term), AuthBound m v → AuthBound m e → AuthBound m (subst j v e) := by
  induction e with
  | var i =>
      intro j v hv _
      simp only [subst]
      split_ifs <;> first | exact hv | trivial
  | lam A b ih =>
      intro j v hv h
      exact ih (j + 1) (lift 0 v) (authBound_lift v 0 hv) h
  | app f x ihf ihx => intro j v hv h; exact ⟨ihf j v hv h.1, ihx j v hv h.2⟩
  | letIn a b iha ihb => intro j v hv h; exact ⟨iha j v hv h.1, ihb (j + 1) (lift 0 v) (authBound_lift v 0 hv) h.2⟩
  | mint κ t ih => intro j v hv h; exact ih j v hv h
  | restrict k t ih => intro j v hv h; exact ih j v hv h
  | exercise a t ih => intro j v hv h; exact ⟨h.1, ih j v hv h.2⟩
  | sink req t ih => intro j v hv h; exact ⟨h.1, ih j v hv h.2⟩
  | perform E t ih => intro j v hv h; exact ih j v hv h
  | handle E hh b ihh ihb => intro j v hv h; exact ⟨ihh j v hv h.1, ihb j v hv h.2⟩
  | _ => intro j v _ _; trivial

/-- `subst0` preserves `AuthBound`. -/
theorem authBound_subst0 {m : Authority} {v e : Term}
    (hv : AuthBound m v) (he : AuthBound m e) : AuthBound m (subst0 v e) :=
  authBound_subst e 0 v hv he

/-- One reduction step preserves `AuthBound` and grows the authority trace only by authorities
    already within `m` (the effect trace is unchanged in this fragment). -/
theorem step_authBound {S : Sig} {m : Authority} :
    ∀ {c c' : Config}, Step S c c' → AuthBound m c.tm →
      AuthBound m c'.tm ∧ c'.auth ⊆ c.auth ∪ m ∧ c'.eff = c.eff := by
  intro c c' hs
  induction hs with
  | beta hv => intro hb; exact ⟨authBound_subst0 hb.2 hb.1, Finset.subset_union_left, rfl⟩
  | app1 _ ih => intro hb; obtain ⟨hb', hA, hE⟩ := ih hb.1; exact ⟨⟨hb', hb.2⟩, hA, hE⟩
  | app2 _ _ ih => intro hb; obtain ⟨hb', hA, hE⟩ := ih hb.2; exact ⟨⟨hb.1, hb'⟩, hA, hE⟩
  | letBeta hv => intro hb; exact ⟨authBound_subst0 hb.1 hb.2, Finset.subset_union_left, rfl⟩
  | let1 _ ih => intro hb; obtain ⟨hb', hA, hE⟩ := ih hb.1; exact ⟨⟨hb', hb.2⟩, hA, hE⟩
  | mintRed => intro _; exact ⟨trivial, Finset.subset_union_left, rfl⟩
  | mint1 _ ih => intro hb; obtain ⟨hb', hA, hE⟩ := ih hb; exact ⟨hb', hA, hE⟩
  | restrictRed => intro _; exact ⟨trivial, Finset.subset_union_left, rfl⟩
  | restrict1 _ ih => intro hb; obtain ⟨hb', hA, hE⟩ := ih hb; exact ⟨hb', hA, hE⟩
  | exerciseRed hak =>
      intro hb
      refine ⟨trivial, ?_, rfl⟩
      exact Finset.insert_subset (Finset.mem_union_right _ hb.1) Finset.subset_union_left
  | exercise1 _ ih => intro hb; obtain ⟨hb', hA, hE⟩ := ih hb.2; exact ⟨⟨hb.1, hb'⟩, hA, hE⟩
  -- M7: the full-mask sink emits `req ⊆ m`, so the authority trace stays within `m`.
  | sinkRed _ =>
      intro hb
      exact ⟨trivial,
        Finset.union_subset Finset.subset_union_left (hb.1.trans Finset.subset_union_right), rfl⟩
  | sink1 _ ih => intro hb; obtain ⟨hb', hA, hE⟩ := ih hb.2; exact ⟨⟨hb.1, hb'⟩, hA, hE⟩
  | raiseSink _ => intro hb; exact ⟨hb.2, Finset.subset_union_left, rfl⟩
  -- M6: effect-handler steps never exercise authority, so the trace bound is preserved.
  | perform1 _ ih => intro hb; obtain ⟨hb', hA, hE⟩ := ih hb; exact ⟨hb', hA, hE⟩
  | raiseApp1 _ => intro hb; exact ⟨hb.1, Finset.subset_union_left, rfl⟩
  | raiseApp2 _ _ => intro hb; exact ⟨hb.2, Finset.subset_union_left, rfl⟩
  | raiseLet _ => intro hb; exact ⟨hb.1, Finset.subset_union_left, rfl⟩
  | raiseMint _ => intro hb; exact ⟨hb, Finset.subset_union_left, rfl⟩
  | raiseRestrict _ => intro hb; exact ⟨hb, Finset.subset_union_left, rfl⟩
  | raiseExercise _ => intro hb; exact ⟨hb.2, Finset.subset_union_left, rfl⟩
  | raisePerform _ => intro hb; exact ⟨hb, Finset.subset_union_left, rfl⟩
  | handleBody _ ih => intro hb; obtain ⟨hb', hA, hE⟩ := ih hb.2; exact ⟨⟨hb.1, hb'⟩, hA, hE⟩
  | handleCatch _ => intro hb; exact ⟨⟨hb.1, hb.2⟩, Finset.subset_union_left, rfl⟩
  | handlePropagate _ _ => intro hb; exact ⟨hb.2, Finset.subset_union_left, rfl⟩
  | handleReturn _ => intro hb; exact ⟨hb.2, Finset.subset_union_left, rfl⟩
  -- `trap`-bubble steps: `.trap` exercises no authority (`AuthBound m .trap = True`), so the trace
  -- is unchanged — the bound is preserved trivially.
  | trapApp1 => intro _; exact ⟨trivial, Finset.subset_union_left, rfl⟩
  | trapApp2 _ => intro _; exact ⟨trivial, Finset.subset_union_left, rfl⟩
  | trapLet => intro _; exact ⟨trivial, Finset.subset_union_left, rfl⟩
  | trapMint => intro _; exact ⟨trivial, Finset.subset_union_left, rfl⟩
  | trapRestrict => intro _; exact ⟨trivial, Finset.subset_union_left, rfl⟩
  | trapExercise => intro _; exact ⟨trivial, Finset.subset_union_left, rfl⟩
  | trapSink => intro _; exact ⟨trivial, Finset.subset_union_left, rfl⟩
  | trapPerform => intro _; exact ⟨trivial, Finset.subset_union_left, rfl⟩
  | trapHandle => intro _; exact ⟨trivial, Finset.subset_union_left, rfl⟩

/-- The reachability invariant: from a `AuthBound` start, every reachable configuration keeps its
    authority trace within `m` (and stays `AuthBound`). -/
theorem reachable_invariant {S : Sig} {m : Authority} {e : Term}
    (hb0 : AuthBound m e) {c : Config} (hstar : StepStar S ⟨e, ∅, ∅⟩ c) :
    AuthBound m c.tm ∧ c.auth ⊆ m := by
  induction hstar with
  | refl => exact ⟨hb0, Finset.empty_subset m⟩
  | tail _ hstep ih =>
      obtain ⟨hbmid, hAmid⟩ := ih
      obtain ⟨hb', hA, _⟩ := step_authBound hstep hbmid
      refine ⟨hb', ?_⟩
      calc _ ⊆ _ ∪ m := hA
        _ = m := Finset.union_eq_right.mpr hAmid

/-- **Capability safety.**  A well-typed program never exercises authority outside its declared
    ceiling `m`: for every reachable configuration `c`, `c.auth ⊆ m`. -/
theorem capability_safety {S : Sig} {e : Term} {τ ε m U'}
    (h : Typing S [] [] e τ ε m U') :
    ∀ c, StepStar S (initConfig e) c → c.auth ⊆ m := by
  intro c hstar
  exact (reachable_invariant (authBound_of_typing h) hstar).2

-- (The vacuous `effect_safety_vacuous` of M1–M5 is superseded by the substantive `effect_safety`
-- in `Preservation.lean`, now that `perform`/`handle` have real typing + reduction rules.)

end LambdaSigil
