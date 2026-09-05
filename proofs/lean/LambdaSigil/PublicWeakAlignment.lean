import LambdaSigil.PublicFrameSecurity

/-!
# Independently sized Public trace alignment

This module is deliberately policy-neutral.  `FinitePublicAlignment` is proof evidence assembled
from actual raw steps: it permits either side to take a Public-silent step, or both sides to take
steps with equal Public boundary observations.  It never supplies events to the machine and it is
not an assumption accepted by the production claim.  The v9 region proof must derive it from
verifier acceptance, successful executions, and complete release-trace equality.
-/

namespace LambdaSigil.Combined.Semantic.PublicWeakAlignment

open PublicRegionSecurity

/-- Finite weak alignment with independent execution lengths.  The terminal rule admits arbitrary
    remaining fuel only for genuinely stopped states; `runPrefix` then produces no further events.
    No future-output equality is stored in a state relation. -/
inductive FinitePublicAlignment (p : SemanticProgram) : Nat → State → Nat → State → Prop
  | terminal {leftFuel rightFuel : Nat} {left right : State}
      (leftStopped : left.halted = true ∨ left.trapped = true)
      (rightStopped : right.halted = true ∨ right.trapped = true)
      (projection : publicProjection p left = publicProjection p right) :
      FinitePublicAlignment p leftFuel left rightFuel right
  | matched {leftFuel rightFuel : Nat} {left right : State}
      (observation : publicBoundaryTrace (Semantic.step p left).events =
        publicBoundaryTrace (Semantic.step p right).events)
      (tail : FinitePublicAlignment p leftFuel (Semantic.step p left).state
        rightFuel (Semantic.step p right).state) :
      FinitePublicAlignment p (leftFuel + 1) left (rightFuel + 1) right
  | silentLeft {leftFuel rightFuel : Nat} {left right : State}
      (silent : publicBoundaryTrace (Semantic.step p left).events = [])
      (tail : FinitePublicAlignment p leftFuel (Semantic.step p left).state rightFuel right) :
      FinitePublicAlignment p (leftFuel + 1) left rightFuel right
  | silentRight {leftFuel rightFuel : Nat} {left right : State}
      (silent : publicBoundaryTrace (Semantic.step p right).events = [])
      (tail : FinitePublicAlignment p leftFuel left rightFuel (Semantic.step p right).state) :
      FinitePublicAlignment p leftFuel left (rightFuel + 1) right

theorem FinitePublicAlignment.result {p : SemanticProgram} {leftFuel rightFuel : Nat}
    {left right : State}
    (h : FinitePublicAlignment p leftFuel left rightFuel right) :
    publicProjection p (runPrefix p leftFuel left).state =
        publicProjection p (runPrefix p rightFuel right).state ∧
      publicBoundaryTrace (runPrefix p leftFuel left).events =
        publicBoundaryTrace (runPrefix p rightFuel right).events := by
  induction h with
  | terminal leftStopped rightStopped projection =>
      rw [PublicRegionSecurity.runPrefix_of_stopped p _ _ leftStopped,
        PublicRegionSecurity.runPrefix_of_stopped p _ _ rightStopped]
      exact ⟨projection, rfl⟩
  | matched observation _ ih =>
      constructor
      · simpa only [runPrefix] using ih.1
      · simp only [runPrefix, publicBoundaryTrace_append]
        exact congrArg₂ (fun head tail => head ++ tail) observation ih.2
  | silentLeft silent _ ih =>
      constructor
      · simpa only [runPrefix] using ih.1
      · simp only [runPrefix, publicBoundaryTrace_append, silent, List.nil_append]
        exact ih.2
  | silentRight silent _ ih =>
      constructor
      · simpa only [runPrefix] using ih.1
      · simp only [runPrefix, publicBoundaryTrace_append, silent, List.nil_append]
        exact ih.2

/-- The generic composition layer already enforces separate fuels: no common bound or equal-step
    premise is present in its type. -/
theorem independent_fuels_are_not_collapsed {p : SemanticProgram} {leftFuel rightFuel : Nat}
    {left right : State}
    (h : FinitePublicAlignment p leftFuel left rightFuel right) :
    publicBoundaryTrace (runPrefix p leftFuel left).events =
      publicBoundaryTrace (runPrefix p rightFuel right).events :=
  h.result.2

/-- Prepend an actual independently sized left segment whose every raw step is Public-silent.
    The endpoint is definitionally the state reached by `runPrefix`; no summary transition is
    substituted for execution. -/
theorem FinitePublicAlignment.prependSilentLeft {p : SemanticProgram}
    {leftTail rightFuel segmentLength : Nat} {left right : State}
    (hsilent : ∀ elapsed, elapsed < segmentLength →
      publicBoundaryTrace
          (Semantic.step p (runPrefix p elapsed left).state).events = [])
    (tail : FinitePublicAlignment p leftTail (runPrefix p segmentLength left).state
      rightFuel right) :
    FinitePublicAlignment p (segmentLength + leftTail) left rightFuel right := by
  induction segmentLength generalizing left with
  | zero => simpa only [Nat.zero_add, runPrefix] using tail
  | succ segmentLength ih =>
      have hhead := hsilent 0 (by omega)
      have htailSilent : ∀ elapsed, elapsed < segmentLength →
          publicBoundaryTrace
            (Semantic.step p (runPrefix p elapsed (Semantic.step p left).state).state).events = [] := by
        intro elapsed helapsed
        have hrow := hsilent (elapsed + 1) (by omega)
        simpa only [runPrefix] using hrow
      have htail : FinitePublicAlignment p (segmentLength + leftTail)
          (Semantic.step p left).state rightFuel right := by
        apply ih htailSilent
        simpa only [runPrefix] using tail
      simpa only [runPrefix, Nat.succ_add, Nat.add_assoc, Nat.add_one] using
        (FinitePublicAlignment.silentLeft
          (leftFuel := segmentLength + leftTail) (rightFuel := rightFuel) hhead htail)

/-- Symmetric independently sized Public-silent right segment. -/
theorem FinitePublicAlignment.prependSilentRight {p : SemanticProgram}
    {leftFuel rightTail segmentLength : Nat} {left right : State}
    (hsilent : ∀ elapsed, elapsed < segmentLength →
      publicBoundaryTrace
          (Semantic.step p (runPrefix p elapsed right).state).events = [])
    (tail : FinitePublicAlignment p leftFuel left rightTail
      (runPrefix p segmentLength right).state) :
    FinitePublicAlignment p leftFuel left (segmentLength + rightTail) right := by
  induction segmentLength generalizing right with
  | zero => simpa only [Nat.zero_add, runPrefix] using tail
  | succ segmentLength ih =>
      have hhead := hsilent 0 (by omega)
      have htailSilent : ∀ elapsed, elapsed < segmentLength →
          publicBoundaryTrace
            (Semantic.step p (runPrefix p elapsed (Semantic.step p right).state).state).events = [] := by
        intro elapsed helapsed
        have hrow := hsilent (elapsed + 1) (by omega)
        simpa only [runPrefix] using hrow
      have htail : FinitePublicAlignment p leftFuel left (segmentLength + rightTail)
          (Semantic.step p right).state := by
        apply ih htailSilent
        simpa only [runPrefix] using tail
      simpa only [runPrefix, Nat.succ_add, Nat.add_assoc, Nat.add_one] using
        (FinitePublicAlignment.silentRight
          (leftFuel := leftFuel) (rightFuel := segmentLength + rightTail) hhead htail)

end LambdaSigil.Combined.Semantic.PublicWeakAlignment
