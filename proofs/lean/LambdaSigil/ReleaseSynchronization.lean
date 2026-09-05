import LambdaSigil.SemanticSecurity

/-!
# Release occurrence alignment across independent raw executions

The records here are observations of `runPrefix`, never replacement inputs to the machine.
Complete trace equality aligns releases by occurrence even when the two executions reach those
occurrences at different steps. A cursor stores only an elapsed-step bound; all payloads, sites,
stages, and suffixes are derived from the actual execution. No equal-fuel, equal-intermediate-count,
termination, verifier acceptance, or Public noninterference conclusion is assumed or proved here.

This is the release-accounting layer for the future structured-region proof. It cannot establish
that a matching release occurrence is reached at a reusable Public cut point, or that the Public
state relation is restored there; those remain semantic preservation obligations.
-/

namespace LambdaSigil.Combined.ReleaseSynchronization

open Semantic

/-- Occurrence is the position in the list, not a set membership or a unique site. Repeated
    executions of one site remain separate entries. Static payload labels are not release data. -/
structure ReleaseObservation where
  site : UInt32
  stage : UInt8
  payload : Int
  deriving Repr, BEq, DecidableEq

def releaseTrace (events : List Event) : List ReleaseObservation :=
  (releaseEvents events).map fun event => ⟨event.site, event.stage, event.payload⟩

@[simp] theorem releaseTrace_append (left right : List Event) :
    releaseTrace (left ++ right) = releaseTrace left ++ releaseTrace right := by
  simp [releaseTrace, releaseEvents, List.filter_append]

theorem runPrefix_add (p : SemanticProgram) (before after : Nat) (start : State) :
    runPrefix p (before + after) start =
      let first := runPrefix p before start
      let rest := runPrefix p after first.state
      ⟨rest.state, first.events ++ rest.events⟩ := by
  induction before generalizing start with
  | zero => simp [runPrefix]
  | succ before ih =>
      simp only [Nat.succ_add, runPrefix]
      rw [ih]
      simp only [List.append_assoc]

/-- Proof-only progress. The machine is never passed this record. In particular it cannot supply
    a release payload or claim that a release happened without executing its prefix. -/
structure ReleaseProgress (total : Nat) where
  steps : Nat
  within : steps ≤ total

def ReleaseProgress.consumed {total : Nat} (cursor : ReleaseProgress total)
    (p : SemanticProgram) (start : State) : List ReleaseObservation :=
  releaseTrace (runPrefix p cursor.steps start).events

def ReleaseProgress.remaining {total : Nat} (cursor : ReleaseProgress total)
    (p : SemanticProgram) (start : State) : List ReleaseObservation :=
  releaseTrace (runPrefix p (total - cursor.steps)
    (runPrefix p cursor.steps start).state).events

theorem releaseProgress_partition (p : SemanticProgram) (start : State) {total : Nat}
    (cursor : ReleaseProgress total) :
    releaseTrace (runPrefix p total start).events =
      cursor.consumed p start ++ cursor.remaining p start := by
  have htotal : total = cursor.steps + (total - cursor.steps) :=
    (Nat.add_sub_of_le cursor.within).symm
  conv_lhs => rw [htotal, runPrefix_add]
  exact releaseTrace_append _ _

theorem consumed_is_actual_prefix (p : SemanticProgram) (start : State) {total : Nat}
    (cursor : ReleaseProgress total) :
    cursor.consumed p start =
      (releaseTrace (runPrefix p total start).events).take
        (cursor.consumed p start).length := by
  rw [releaseProgress_partition p start cursor]
  simp

theorem remaining_is_actual_suffix (p : SemanticProgram) (start : State) {total : Nat}
    (cursor : ReleaseProgress total) :
    cursor.remaining p start =
      (releaseTrace (runPrefix p total start).events).drop
        (cursor.consumed p start).length := by
  rw [releaseProgress_partition p start cursor]
  simp

/-- Equal complete traces align every occurrence, including occurrences not yet consumed on one
    side. There is deliberately no assertion that the executions reached it at the same step. -/
theorem complete_release_equality_aligns_occurrence (p : SemanticProgram)
    (left right : State) (leftFuel rightFuel occurrence : Nat)
    (hcomplete : releaseTrace (runPrefix p leftFuel left).events =
      releaseTrace (runPrefix p rightFuel right).events) :
    (releaseTrace (runPrefix p leftFuel left).events)[occurrence]? =
      (releaseTrace (runPrefix p rightFuel right).events)[occurrence]? := by
  rw [hcomplete]

/-- Once both proof cursors have consumed the same number of releases, equality of their consumed
    payloads and their entire remaining release suffix is derived, not an extra alignment premise.
    The elapsed step counts and the complete execution lengths remain independent. -/
theorem equal_occurrence_counts_synchronize_prefix_and_suffix (p : SemanticProgram)
    (left right : State) {leftFuel rightFuel : Nat}
    (leftCursor : ReleaseProgress leftFuel) (rightCursor : ReleaseProgress rightFuel)
    (hcomplete : releaseTrace (runPrefix p leftFuel left).events =
      releaseTrace (runPrefix p rightFuel right).events)
    (hcount : (leftCursor.consumed p left).length =
      (rightCursor.consumed p right).length) :
    leftCursor.consumed p left = rightCursor.consumed p right ∧
      leftCursor.remaining p left = rightCursor.remaining p right := by
  constructor
  · calc
      leftCursor.consumed p left = _ := consumed_is_actual_prefix p left leftCursor
      _ = (releaseTrace (runPrefix p rightFuel right).events).take
          (rightCursor.consumed p right).length := by rw [hcomplete, hcount]
      _ = rightCursor.consumed p right :=
        (consumed_is_actual_prefix p right rightCursor).symm
  · calc
      leftCursor.remaining p left = _ := remaining_is_actual_suffix p left leftCursor
      _ = (releaseTrace (runPrefix p rightFuel right).events).drop
          (rightCursor.consumed p right).length := by rw [hcomplete, hcount]
      _ = rightCursor.remaining p right :=
        (remaining_is_actual_suffix p right rightCursor).symm

theorem complete_release_equality_preserves_count (p : SemanticProgram)
    (left right : State) (leftFuel rightFuel : Nat)
    (hcomplete : releaseTrace (runPrefix p leftFuel left).events =
      releaseTrace (runPrefix p rightFuel right).events) :
    (releaseTrace (runPrefix p leftFuel left).events).length =
      (releaseTrace (runPrefix p rightFuel right).events).length :=
  congrArg List.length hcomplete

end LambdaSigil.Combined.ReleaseSynchronization
