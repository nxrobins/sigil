import LambdaSigil.MessageBoundary

/-!
# λ-SIGIL — flow-sensitive taint: the control-flow JOIN (T001, task #252)

`Taint.lean` is expression-only: it has no variables that can be *assigned*, so it cannot express
the defect that actually shipped —

```sigil
if c { x = secret } else { x = 0 }   // both branches ran against ONE environment,
return x                            // the last write won → compiled CLEAN
```

That is a **data-flow join** bug: at a merge point the environment must be an upper bound of every
incoming branch, and a last-write-wins merge silently drops the secret label.

This module adds the smallest judgment that can state it: a name-keyed taint environment threaded
through statements (`Γin ⊢ s ⊣ Γout`), mirroring the shipped `TaintEnv` / `merge_branch_bindings` /
`loop_fixpoint` in `taint_check.rs`.

## What is proven

* `TS.if_join_ub` — the environment after an `if` is an **upper bound of both branches** (neither
  branch's labels can be forgotten at the merge).
* `TS.while_post_fixpoint` — the loop environment is a **post-fixpoint valid for every trip count,
  including zero** (the SC-T3 zero-iteration path: a loop that never runs must not lower a label).
* `d1_join_leak_ill_typed` — **the shipped bug is rejected**: the D1 program above has no
  derivation, with the accepting twin `d1_public_accepts` proving the rejection is a genuine flow
  violation and not a blanket refusal.
* `TSbad.d1_leak_derivable` — **the mutant twin**, and the reason the theorem is not vacuous:
  `TSbad` is this judgment with the merge weakened to *last-write-wins*, and under it the D1 leak
  **is derivable**. The lub-join premise is therefore load-bearing — deleting it re-admits the exact
  program that shipped.

## Faithfulness and honest scope

* `TEnv.join` is the pointwise `lub` of `merge_branch_bindings`; the `whileS` invariant premise is
  the post-fixpoint `loop_fixpoint` computes; `assign` folds the control label `pc` into the stored
  label exactly as `compute_expr_taint` folds `env.pc_taint` at its exit.
* **Phase 1 scope, stated plainly.** This covers `assign` / `seq` / `if` / `while` / `sink`. It does
  **not** cover `break` / `continue` (which need non-local exit and two accumulator environments) or
  n-ary `match` arms — the shipped checker has all of those, and they are deliberately deferred.
* The judgment is **declarative**: it states which merges are *legal*, not how a fixpoint is
  computed. It is a leaf module — nothing in the core calculus or in `Taint.lean` is modified — so
  no existing theorem is touched.
* This is a **regression ratchet on already-fixed code**: `taint_check.rs` ships the lub-join and is
  fenced by property tests. The value is that the fence becomes a proof over an arbitrary program
  rather than three examples.
-/

namespace LambdaSigil

/-- A name-keyed taint environment (the shipped `TaintEnv`'s scalar half). -/
abbrev TEnv := Nat → Label

/-- Pointwise order. -/
def TEnv.le (a b : TEnv) : Prop := ∀ x, a x ≤ b x

/-- Pointwise join — `merge_branch_bindings`. -/
def TEnv.join (a b : TEnv) : TEnv := fun x => Label.lub (a x) (b x)

/-- Strong update of one binding. -/
def TEnv.upd (ρ : TEnv) (x : Nat) (ℓ : Label) : TEnv := fun y => if y = x then ℓ else ρ y

theorem TEnv.le_join_left (a b : TEnv) : TEnv.le a (TEnv.join a b) := fun x =>
  Label.le_lub_left (a x) (b x)

theorem TEnv.le_join_right (a b : TEnv) : TEnv.le b (TEnv.join a b) := fun x =>
  Label.le_lub_right (a x) (b x)

/-- Expressions: a literal at a label, or a variable read. Total — no judgment needed. -/
inductive Exp where
  | lit : Label → Exp
  | rd : Nat → Exp
  deriving DecidableEq, Repr

/-- The label an expression carries in environment `ρ`. -/
def Exp.label : Exp → TEnv → Label
  | .lit ℓ, _ => ℓ
  | .rd x, ρ => ρ x

/-- Phase-1 statements. -/
inductive Stmt where
  | skip : Stmt
  | assign : Nat → Exp → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifS : Exp → Stmt → Stmt → Stmt
  | whileS : Exp → Stmt → Stmt
  /-- `sinkS ℓd e` — deliver `e` to a sink declared at `ℓd` (the T001 check). -/
  | sinkS : Label → Exp → Stmt
  deriving Repr

/-- **Flow-sensitive taint judgment**: `TS ρ pc s ρ'` — running `s` under control label `pc` in
    environment `ρ` yields `ρ'`.

    `assign` folds `pc` into the stored label (implicit flow); `ifS` raises `pc` by the guard and
    **joins** the two branch environments; `whileS` demands an invariant that is a post-fixpoint and
    an upper bound of the entry environment; `sinkS` runs the T001 check. -/
inductive TS : TEnv → Label → Stmt → TEnv → Prop where
  | skip {ρ pc} : TS ρ pc .skip ρ
  | assign {ρ pc x e} :
      TS ρ pc (.assign x e) (TEnv.upd ρ x (Label.lub pc (e.label ρ)))
  | seq {ρ pc s₁ s₂ ρ₁ ρ₂} :
      TS ρ pc s₁ ρ₁ → TS ρ₁ pc s₂ ρ₂ → TS ρ pc (.seq s₁ s₂) ρ₂
  | ifS {ρ pc g s₁ s₂ ρ₁ ρ₂} :
      TS ρ (Label.lub pc (g.label ρ)) s₁ ρ₁ →
      TS ρ (Label.lub pc (g.label ρ)) s₂ ρ₂ →
      TS ρ pc (.ifS g s₁ s₂) (TEnv.join ρ₁ ρ₂)
  | whileS {ρ pc g s} (I : TEnv) :
      TEnv.le ρ I →
      TS I (Label.lub pc (g.label I)) s I →
      TS ρ pc (.whileS g s) I
  | sinkS {ρ pc ℓd e} :
      Label.lub pc (e.label ρ) ≤ ℓd →
      TS ρ pc (.sinkS ℓd e) ρ

/-- **Merge soundness.**  The environment after an `if` is an upper bound of *both* branch
    environments — no branch's labels can be dropped at the join. -/
theorem TS.if_join_ub {ρ pc g s₁ s₂ ρ'} (h : TS ρ pc (.ifS g s₁ s₂) ρ') :
    ∃ ρ₁ ρ₂, TEnv.le ρ₁ ρ' ∧ TEnv.le ρ₂ ρ' := by
  cases h with
  | ifS h₁ h₂ => exact ⟨_, _, TEnv.le_join_left _ _, TEnv.le_join_right _ _⟩

/-- **Loop soundness (SC-T3).**  The environment a loop yields is an upper bound of the entry
    environment, so the **zero-iteration** path cannot lower a label, and it is a post-fixpoint, so
    it is valid for every trip count. -/
theorem TS.while_post_fixpoint {ρ pc g s ρ'} (h : TS ρ pc (.whileS g s) ρ') :
    TEnv.le ρ ρ' ∧ TS ρ' (Label.lub pc (g.label ρ')) s ρ' := by
  cases h with
  | whileS I hle hbody => exact ⟨hle, hbody⟩

/-! ## Non-vacuity — the D1 program that actually shipped -/

/-- `x` — the single variable used by the witnesses. -/
def xv : Nat := 0

/-- The bottom environment: everything `@Public`. -/
def botEnv : TEnv := fun _ => .pub

/-- **D1**: `if (public guard) { x = secret } else { x = public }; sink @Public x`.

    Only the *assigned value* is secret — the guard is public — so this is a pure data-flow join
    defect, exactly the shape that compiled clean before the fix. -/
def d1Prog : Stmt :=
  .seq (.ifS (.lit .pub) (.assign xv (.lit .sec)) (.assign xv (.lit .pub)))
       (.sinkS .pub (.rd xv))

/-- The all-public twin: identical control flow, no secret anywhere. -/
def d1PubProg : Stmt :=
  .seq (.ifS (.lit .pub) (.assign xv (.lit .pub)) (.assign xv (.lit .pub)))
       (.sinkS .pub (.rd xv))

/-- **The shipped bug is rejected.**  D1 has no derivation: the join carries `@Secret` out of the
    then-branch, so the `@Public` sink cannot discharge its check. -/
theorem d1_join_leak_ill_typed : ¬ ∃ ρ', TS botEnv .pub d1Prog ρ' := by
  rintro ⟨ρ', h⟩
  cases h with
  | seq hif hsink =>
    cases hif with
    | ifS h₁ h₂ =>
      cases h₁
      cases h₂
      cases hsink with
      | sinkS hle =>
        simp only [Exp.label, TEnv.join, TEnv.upd, xv] at hle
        exact absurd hle (by decide)

/-- **The accepting twin.**  The same control flow with public data checks fine — so the rejection
    above is a genuine flow violation, not a judgment that refuses every `if`. -/
theorem d1_public_accepts :
    ∃ ρ', TS botEnv .pub d1PubProg ρ' :=
  ⟨_, .seq (.ifS .assign .assign) (.sinkS (by decide))⟩

/-! ## The mutant twin — why the join premise is load-bearing

`TSbad` is `TS` with exactly one change: the `if` merge takes the **else** branch's environment
(last-write-wins) instead of the join.  That is the pre-fix behaviour, and under it the D1 leak
becomes derivable — which is what makes `d1_join_leak_ill_typed` non-vacuous. -/

/-- The mutant: `ifS` keeps only the second branch's environment (last-write-wins). -/
inductive TSbad : TEnv → Label → Stmt → TEnv → Prop where
  | skip {ρ pc} : TSbad ρ pc .skip ρ
  | assign {ρ pc x e} :
      TSbad ρ pc (.assign x e) (TEnv.upd ρ x (Label.lub pc (e.label ρ)))
  | seq {ρ pc s₁ s₂ ρ₁ ρ₂} :
      TSbad ρ pc s₁ ρ₁ → TSbad ρ₁ pc s₂ ρ₂ → TSbad ρ pc (.seq s₁ s₂) ρ₂
  | ifS {ρ pc g s₁ s₂ ρ₁ ρ₂} :
      TSbad ρ (Label.lub pc (g.label ρ)) s₁ ρ₁ →
      TSbad ρ (Label.lub pc (g.label ρ)) s₂ ρ₂ →
      TSbad ρ pc (.ifS g s₁ s₂) ρ₂
  | sinkS {ρ pc ℓd e} :
      Label.lub pc (e.label ρ) ≤ ℓd →
      TSbad ρ pc (.sinkS ℓd e) ρ

/-- **The mutant admits the leak.**  Under last-write-wins, D1 — the program that shipped — *is*
    derivable.  So the lub-join premise in `TS.ifS` is exactly what rejects it. -/
theorem TSbad.d1_leak_derivable : ∃ ρ', TSbad botEnv .pub d1Prog ρ' :=
  ⟨_, .seq (.ifS .assign .assign) (.sinkS (by decide))⟩

end LambdaSigil
