import LambdaSigil.TaintJoin

/-!
# λ-SIGIL — definite initialization of actor state (T126)

SIGIL requires every declared state field to be assigned by the time an actor's `init` block
finishes, and the registry states the hazard verbatim:

> An early `return`, bare or guarded inside an `if`, can finish init while skipping the field's
> assignment.

(That is why T126 — *"An `init` block must not `return`"* — exists at all.)

This module mechanizes the underlying dataflow property. It is the **dual** of `TaintJoin.lean`:

| | direction | merge at an `if` | failure mode |
|---|---|---|---|
| taint (`TaintJoin.lean`) | **may** — what *could* be secret | `⊔` (**union** / lub) | too *small* a merge leaks (last-write-wins) |
| definite-init (here) | **must** — what is *certainly* assigned | `∩` (**intersection**) | too *large* a merge admits an unassigned field |

Getting the direction wrong at a merge is the entire bug class, in both directions — so each module
carries a **mutant twin** proving its merge operator is load-bearing.

## What is proven

* `DI.if_meet_lower_bound` — the set assigned after an `if` is a **lower bound** of both branches:
  a field counts as initialized only if *every* path assigns it.
* `DI.ret_requires_assigned` — the T126 rule itself: a path may `return` out of `init` only once
  every required field is already assigned.
* `one_sided_assign_incomplete` / `early_return_skips_field` — the two shapes the registry names are
  **rejected**, with the accepting twin `both_sided_assign_complete` proving the judgment is not
  simply refusing every `if`.
* `DIbad.one_sided_admitted` — the **mutant twin**: `DIbad` is this judgment with the merge weakened
  from intersection to **union** (a *may*-analysis, the classic wrong direction), and under it the
  one-sided assignment is accepted. So the intersection premise is what rejects it.

## Honest scope

Fields are opaque `Nat` ids and the statement language is `skip` / `assign` / `seq` / `if` /
`return` — enough to state definite assignment and the early-return hazard, and nothing more. There
are no loops (a loop body cannot *guarantee* an assignment without a trip-count argument, so a
must-analysis conservatively gains nothing from one), no field *types*, and no capability content:
this is a dataflow property, not a statement about what the fields hold. It is a leaf module — the
core calculus, `Taint.lean`, and `TaintJoin.lean` are all untouched.
-/

namespace LambdaSigil

/-- A set of state-field ids. -/
abbrev Fields := Finset Nat

/-- Statements of an actor `init` block. -/
inductive IStmt where
  | skip : IStmt
  | assignF : Nat → IStmt
  | seq : IStmt → IStmt → IStmt
  | ifS : IStmt → IStmt → IStmt
  /-- An early `return` out of `init` — the T126 hazard. -/
  | ret : IStmt
  deriving Repr

/-- **Definite-assignment judgment.**  `DI req before s after` : starting with `before` already
    assigned, `s` finishes with `after` assigned, where `after = none` means *this path returned*.

    `req` is the set of fields the actor declares and therefore must have assigned before `init`
    can finish — including via an early `return` (the `ret` rule). -/
inductive DI (req : Fields) : Fields → IStmt → Option Fields → Prop where
  | skip {b} : DI req b .skip (some b)
  | assignF {b f} : DI req b (.assignF f) (some (insert f b))
  | seqN {b s₁ s₂ b₁ r} : DI req b s₁ (some b₁) → DI req b₁ s₂ r → DI req b (.seq s₁ s₂) r
  /-- A returning prefix makes the tail unreachable. -/
  | seqD {b s₁ s₂} : DI req b s₁ none → DI req b (.seq s₁ s₂) none
  /-- **Must-merge: INTERSECTION.**  A field is assigned after the `if` only if *both* branches
      assign it. -/
  | ifBoth {b s₁ s₂ b₁ b₂} :
      DI req b s₁ (some b₁) → DI req b s₂ (some b₂) →
      DI req b (.ifS s₁ s₂) (some (b₁ ∩ b₂))
  | ifLeft {b s₁ s₂ b₁} : DI req b s₁ (some b₁) → DI req b s₂ none →
      DI req b (.ifS s₁ s₂) (some b₁)
  | ifRight {b s₁ s₂ b₂} : DI req b s₁ none → DI req b s₂ (some b₂) →
      DI req b (.ifS s₁ s₂) (some b₂)
  | ifDiv {b s₁ s₂} : DI req b s₁ none → DI req b s₂ none → DI req b (.ifS s₁ s₂) none
  /-- **T126.**  A path may leave `init` early only if everything required is already assigned. -/
  | ret {b} : req ⊆ b → DI req b .ret none

/-- **Merge soundness (must-direction).**  The set assigned after a two-branch `if` is a *lower*
    bound of both branches — a field counts as initialized only if every path assigns it. -/
theorem DI.if_meet_lower_bound {req b s₁ s₂ b₁ b₂}
    (h₁ : DI req b s₁ (some b₁)) (h₂ : DI req b s₂ (some b₂)) :
    DI req b (.ifS s₁ s₂) (some (b₁ ∩ b₂)) ∧ b₁ ∩ b₂ ⊆ b₁ ∧ b₁ ∩ b₂ ⊆ b₂ :=
  ⟨.ifBoth h₁ h₂, Finset.inter_subset_left, Finset.inter_subset_right⟩

/-- **The T126 rule.**  Leaving `init` early requires everything already assigned. -/
theorem DI.ret_requires_assigned {req b r} (h : DI req b .ret r) : req ⊆ b := by
  cases h with
  | ret hsub => exact hsub

/-! ## Non-vacuity — the two shapes the registry names -/

/-- The single state field used by the witnesses. -/
def f0 : Nat := 0

/-- The actor declares one field, so `init` must assign it. -/
def req0 : Fields := {0}

/-- **Shape 1** — a guarded assignment: `if c { self.f = v }` (else does nothing). -/
def oneSidedProg : IStmt := .ifS (.assignF f0) .skip

/-- The honest twin: both branches assign. -/
def bothSidedProg : IStmt := .ifS (.assignF f0) (.assignF f0)

/-- **Shape 2** — the registry's exact hazard: an early `return` guarded inside an `if`, taken
    *before* the field is assigned. -/
def earlyReturnProg : IStmt := .seq (.ifS .ret .skip) (.assignF f0)

/-- **Shape 1 rejected.**  A one-sided assignment does not definitely initialize the field: the
    intersection at the merge is empty, so the requirement cannot be discharged. -/
theorem one_sided_assign_incomplete :
    ¬ ∃ out, DI req0 ∅ oneSidedProg (some out) ∧ req0 ⊆ out := by
  rintro ⟨out, h, hreq⟩
  cases h with
  | ifBoth h₁ h₂ =>
    cases h₁
    cases h₂
    simp [req0, f0] at hreq
  | ifLeft h₁ h₂ => cases h₂
  | ifRight h₁ h₂ => cases h₁

/-- **Shape 2 rejected.**  The early-`return` path leaves `init` with nothing assigned, so the
    `ret` rule's premise `req ⊆ ∅` cannot be met — exactly the hazard T126 names. -/
theorem early_return_skips_field :
    ¬ ∃ r, DI req0 ∅ earlyReturnProg r := by
  rintro ⟨r, h⟩
  cases h with
  | seqN hif _ =>
    cases hif with
    -- `ret` never yields a normal exit, so the both-normal and left-normal merges are underivable.
    | ifBoth h₁ _ => cases h₁
    | ifLeft h₁ _ => cases h₁
    -- The surviving shape: the guard took the `return`, so the T126 premise is `req0 ⊆ ∅`.
    | ifRight h₁ _ => exact absurd (DI.ret_requires_assigned h₁) (by simp [req0])
  | seqD hif =>
    cases hif with
    | ifDiv h₁ _ => exact absurd (DI.ret_requires_assigned h₁) (by simp [req0])

/-- **The accepting twin.**  Assigning on *both* branches does initialize the field — so the
    rejections above are genuine incompleteness, not a judgment that refuses every `if`. -/
theorem both_sided_assign_complete :
    ∃ out, DI req0 ∅ bothSidedProg (some out) ∧ req0 ⊆ out :=
  ⟨_, .ifBoth .assignF .assignF, by simp [req0, f0]⟩

/-! ## The mutant twin — why the merge must be INTERSECTION

`DIbad` is `DI` with exactly one change: the two-branch `if` merges with **union** (a *may*-analysis
— the classic wrong direction for a must-property).  Under it the one-sided assignment is accepted,
which is precisely the uninitialized-field bug. -/

/-- The mutant: `ifBoth` merges with `∪` instead of `∩`. -/
inductive DIbad (req : Fields) : Fields → IStmt → Option Fields → Prop where
  | skip {b} : DIbad req b .skip (some b)
  | assignF {b f} : DIbad req b (.assignF f) (some (insert f b))
  | seqN {b s₁ s₂ b₁ r} : DIbad req b s₁ (some b₁) → DIbad req b₁ s₂ r → DIbad req b (.seq s₁ s₂) r
  | ifBoth {b s₁ s₂ b₁ b₂} :
      DIbad req b s₁ (some b₁) → DIbad req b s₂ (some b₂) →
      DIbad req b (.ifS s₁ s₂) (some (b₁ ∪ b₂))
  | ret {b} : req ⊆ b → DIbad req b .ret none

/-- **The mutant admits the bug.**  With a union merge, a field assigned on only *one* branch counts
    as initialized — so `DI`'s intersection premise is exactly what rejects it. -/
theorem DIbad.one_sided_admitted :
    ∃ out, DIbad req0 ∅ oneSidedProg (some out) ∧ req0 ⊆ out :=
  ⟨_, .ifBoth .assignF .skip, by simp [req0, f0]⟩

end LambdaSigil
