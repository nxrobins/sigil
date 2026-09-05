import LambdaSigil.Substitution

/-!
# λ-SIGIL — Progress (Milestone M4, part 1)

A well-typed closed term is either a value or can take a step.  No substitution lemma is needed
— progress follows from **canonical forms** (a value of a given type has the expected shape) plus
the typing premises.  Crucially, the `exercise` rule's premise `a ∈ k` is exactly what guarantees
`exerciseRed` can fire: a well-typed authority-exercise is never stuck for lack of authority.
-/

namespace LambdaSigil

/-! ## Canonical forms -/

theorem canon_arrow {S Γ U v A ε B ε' m U'} (hv : Value v)
    (h : Typing S Γ U v (.arrow A ε B) ε' m U') : ∃ body, v = .lam A body := by
  cases hv <;> cases h; exact ⟨_, rfl⟩

theorem canon_cap {S Γ U v κ k ε' m U'} (hv : Value v)
    (h : Typing S Γ U v (.cap κ k) ε' m U') : v = .capVal κ k := by
  cases hv <;> cases h; rfl

theorem canon_mintAuth {S Γ U v κ ε' m U'} (hv : Value v)
    (h : Typing S Γ U v (.mintAuth κ) ε' m U') : v = .mintTok κ := by
  cases hv <;> cases h; rfl

/-! ## Progress -/

-- Progress is proved on the usage-erased judgment as `WT.progress` (`Preservation.lean`), refined
-- in M6 to the 4-way answer "value / raise / steps / trap-abort" (the last for the bottom-typed
-- `trap`, PR #443).  The canonical-forms lemmas above are the `Typing`-level versions; their `WT`
-- analogues live in `Preservation.lean`.

end LambdaSigil
