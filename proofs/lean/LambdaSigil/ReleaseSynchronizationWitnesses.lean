import LambdaSigil.ReleaseSynchronization

/-!
# Raw release-accounting witnesses and mutants

These execute the raw machine with four alternating release stages after unequal private paths.
They test the accounting lemmas, not production acceptance: the small hand-constructed program
does not carry CSIR capability obligations. It cannot stand in for the required decoded v9,
capability-gated, verifier-accepted relational witnesses.
-/

namespace LambdaSigil.Combined.ReleaseSynchronizationWitnesses

open Semantic ReleaseSynchronization

private def instruction (op : InstrOp) (site first count : UInt32)
    (destination : UInt32 := 0) (label : Label := .pub) : Instruction :=
  { op, id := site, functionId := 1, blockId := 1, destination,
    firstOperand := first, operandCount := count, target := 0,
    resultLabel := label, aux := 0 }

private def valueOperand (owner value : UInt32) : OperandRecord :=
  { owner, position := 0, value }

def alternatingProgram : SemanticProgram :=
  { functions := #[{ id := 1, entry := 1, firstInstruction := 0, instructionCount := 8 }],
    instructions := #[
      { instruction .branch 100 0 1 with target := 1, alternate := 3, merge := 3 },
      instruction .scalar 101 1 0,
      { instruction .jump 102 1 0 with target := 3 },
      instruction .releaseCT 103 1 1 3 .secret,
      instruction .release 104 2 1 4 .pub,
      instruction .releaseCT 105 3 1 3 .secret,
      instruction .release 106 4 1 4 .pub,
      instruction .output 107 5 1],
    operands := #[valueOperand 100 1, valueOperand 103 2, valueOperand 104 3,
      valueOperand 105 2, valueOperand 106 3, valueOperand 107 4],
    valueLabels := #[.pub, .secret, .secretCT, .secret, .pub] }

def alternatingState (selector : Int) : State :=
  { pc := 0, values := #[⟨.pub, 0⟩, ⟨.secret, selector⟩, ⟨.secretCT, 37⟩,
      ⟨.secret, 0⟩, ⟨.pub, 0⟩], aggregates := Array.replicate 5 [],
    capabilityBalances := #[] }

def fourReleases : List ReleaseObservation :=
  [⟨103, 2, 37⟩, ⟨104, 1, 37⟩, ⟨105, 2, 37⟩, ⟨106, 1, 37⟩]

theorem unequal_raw_lengths_complete_four_alternating_releases :
    (runPrefix alternatingProgram 6 (alternatingState 0)).state.halted = true ∧
    (runPrefix alternatingProgram 8 (alternatingState 1)).state.halted = true ∧
    (runPrefix alternatingProgram 6 (alternatingState 0)).state.trapped = false ∧
    (runPrefix alternatingProgram 8 (alternatingState 1)).state.trapped = false ∧
    releaseTrace (runPrefix alternatingProgram 6 (alternatingState 0)).events = fourReleases ∧
    releaseTrace (runPrefix alternatingProgram 8 (alternatingState 1)).events = fourReleases := by
  decide +kernel

theorem equal_complete_releases_do_not_imply_equal_intermediate_counts :
    releaseTrace (runPrefix alternatingProgram 6 (alternatingState 0)).events =
      releaseTrace (runPrefix alternatingProgram 8 (alternatingState 1)).events ∧
    (releaseTrace (runPrefix alternatingProgram 2 (alternatingState 0)).events).length = 1 ∧
    (releaseTrace (runPrefix alternatingProgram 2 (alternatingState 1)).events).length = 0 := by
  decide +kernel

theorem unequal_progress_synchronizes_without_replacing_payloads :
    let leftCursor : ReleaseProgress 6 := ⟨2, by decide⟩
    let rightCursor : ReleaseProgress 8 := ⟨4, by decide⟩
    leftCursor.consumed alternatingProgram (alternatingState 0) =
      rightCursor.consumed alternatingProgram (alternatingState 1) ∧
    leftCursor.remaining alternatingProgram (alternatingState 0) =
      rightCursor.remaining alternatingProgram (alternatingState 1) := by
  exact equal_occurrence_counts_synchronize_prefix_and_suffix alternatingProgram
    (alternatingState 0) (alternatingState 1) ⟨2, by decide⟩ ⟨4, by decide⟩
    (by decide +kernel) (by decide +kernel)

theorem equal_fuel_mutant_cannot_capture_both_first_completions :
    (runPrefix alternatingProgram 6 (alternatingState 1)).state.halted = false ∧
    (runPrefix alternatingProgram 6 (alternatingState 0)).state.halted = true := by
  decide +kernel

private def release (site : UInt32) (stage : UInt8) (payload : Int) : Event :=
  { kind := .release, site, stage, payload }

theorem repeated_site_occurrences_are_not_deduplicated :
    releaseTrace [release 7 1 9, release 7 1 9] = [⟨7, 1, 9⟩, ⟨7, 1, 9⟩] ∧
    releaseTrace [release 7 1 9, release 7 1 9] ≠ releaseTrace [release 7 1 9] := by
  decide +kernel

theorem ignored_site_mutant_loses_a_release_difference :
    (releaseTrace [release 7 1 9]).map ReleaseObservation.payload =
      (releaseTrace [release 8 1 9]).map ReleaseObservation.payload ∧
    releaseTrace [release 7 1 9] ≠ releaseTrace [release 8 1 9] := by
  decide +kernel

theorem ignored_stage_mutant_loses_a_release_difference :
    (releaseTrace [release 7 1 9]).map ReleaseObservation.payload =
      (releaseTrace [release 7 2 9]).map ReleaseObservation.payload ∧
    releaseTrace [release 7 1 9] ≠ releaseTrace [release 7 2 9] := by
  decide +kernel

theorem ignored_order_mutant_loses_a_release_difference :
    let left := releaseTrace [release 7 1 9, release 8 2 10]
    let right := releaseTrace [release 8 2 10, release 7 1 9]
    left.Perm right ∧ left ≠ right := by
  constructor
  · exact List.Perm.swap _ _ []
  · decide +kernel

theorem first_release_only_mutant_loses_later_payload_difference :
    let left := releaseTrace [release 7 2 9, release 8 1 9]
    let right := releaseTrace [release 7 2 9, release 8 1 10]
    left.take 1 = right.take 1 ∧ left ≠ right := by
  decide +kernel

end LambdaSigil.Combined.ReleaseSynchronizationWitnesses
