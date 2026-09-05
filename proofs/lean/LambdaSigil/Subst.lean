import LambdaSigil.Syntax

/-!
# λ-SIGIL — de Bruijn substitution (definitions; Milestone M2)

Standard nameless `lift` (shift free variables above a cutoff) and capture-avoiding `subst`
(substitute for a de Bruijn index, decrementing higher indices), used by the β/let reduction
rules in `Semantics.lean`.  The substitution **lemmas** (lift/subst commutation, the
substitution-typing lemma) are proved in M3 (`Substitution.lean`).

Binders in λ-SIGIL: only `lam` (binds in its body) and `letIn` (binds in `e₂`).  `handle E h b`
introduces no binder at this level — the operation-argument binder lives inside the handler `h`
(itself a `lam`).
-/

namespace LambdaSigil

/-- `lift c e` shifts every free variable of `e` with index `≥ c` up by one (used to move a term
    under one extra binder). -/
def lift (c : Nat) : Term → Term
  | .var i => if i < c then .var i else .var (i + 1)
  | .unit => .unit
  | .true => .true
  | .false => .false
  | .lam A b => .lam A (lift (c + 1) b)
  | .app f x => .app (lift c f) (lift c x)
  | .letIn a b => .letIn (lift c a) (lift (c + 1) b)
  | .mintTok κ => .mintTok κ
  | .mint κ t => .mint κ (lift c t)
  | .capVal κ k => .capVal κ k
  | .restrict k t => .restrict k (lift c t)
  | .exercise a t => .exercise a (lift c t)
  | .sink req t => .sink req (lift c t)
  | .perform E t => .perform E (lift c t)
  | .handle E h b => .handle E (lift c h) (lift c b)
  | .trap => .trap

/-- `subst j s e` replaces the free variable `j` of `e` by `s` (shifting `s` under binders) and
    decrements free variables `> j` (the binder at `j` is removed). -/
def subst (j : Nat) (s : Term) : Term → Term
  | .var i => if i = j then s else if j < i then .var (i - 1) else .var i
  | .unit => .unit
  | .true => .true
  | .false => .false
  | .lam A b => .lam A (subst (j + 1) (lift 0 s) b)
  | .app f x => .app (subst j s f) (subst j s x)
  | .letIn a b => .letIn (subst j s a) (subst (j + 1) (lift 0 s) b)
  | .mintTok κ => .mintTok κ
  | .mint κ t => .mint κ (subst j s t)
  | .capVal κ k => .capVal κ k
  | .restrict k t => .restrict k (subst j s t)
  | .exercise a t => .exercise a (subst j s t)
  | .sink req t => .sink req (subst j s t)
  | .perform E t => .perform E (subst j s t)
  | .handle E h b => .handle E (subst j s h) (subst j s b)
  | .trap => .trap

/-- Substitute for the innermost variable (index 0) — the β/let redex contractum. -/
def subst0 (s : Term) (e : Term) : Term := subst 0 s e

end LambdaSigil
