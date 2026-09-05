import LambdaSigil.PublicMatchedProgressSecurity
import LambdaSigil.PublicPrivateReleaseSecurity

/-!
# Release-step progress packaging

This leaf is the downgrade portion of the production Public dispatcher.  A release at a
verifier-Public occurrence consumes the next exact `(site, stage, payload)` observation from the
filtered Public-release trace.  A release at any other occurrence is a matching raw step whose
real release event remains in `ReleaseSynchronization.releaseTrace`, while its filtered Public
head is empty.  Neither case assumes equal fuel or supplies a replacement payload.
-/

namespace LambdaSigil.Combined.V9.PublicReleaseProgressSecurity

open Semantic OccurrenceDataflowInvocation OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity Semantic.PublicReleaseSynchronization
open PublicLocalSecurity PublicMatchingSecurity PublicExecutionSecurity
open PublicNonpublicStepSecurity PublicMatchedProgressSecurity
open PublicPrivateReleaseSecurity

/-- A private downgrade retains its exact unsanitized raw release head even though the
    occurrence-aware Public filter removes that head.  This theorem is deliberately stated next
    to the progress rule so future composition work cannot confuse filtered silence with removal
    from the machine trace. -/
theorem verified_private_release_raw_head_and_public_filter
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {state : State} {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hoperation : instruction.op = .release ∨ instruction.op = .releaseCT)
    (hnonpublic : instruction.blockLabel ≠ .pub) :
    ((ReleaseSynchronization.releaseTrace
          (step (rawSemanticProgram program analysis) state).events =
        [⟨instruction.id, 1,
          (operandValue (rawSemanticProgram program analysis) state instruction).payload⟩]) ∨
      (ReleaseSynchronization.releaseTrace
          (step (rawSemanticProgram program analysis) state).events =
        [⟨instruction.id, 2,
          (operandValue (rawSemanticProgram program analysis) state instruction).payload⟩])) ∧
      publicReleaseTrace (rawSemanticProgram program analysis)
        (step (rawSemanticProgram program analysis) state).events = [] := by
  constructor
  · rcases hoperation with hrelease | hreleaseCT
    · exact Or.inl (complete_releaseTrace_step_release hlookup
        ⟨hactive.notHalted, hactive.notTrapped⟩ hrelease)
    · exact Or.inr (complete_releaseTrace_step_releaseCT hlookup
        ⟨hactive.notHalted, hactive.notTrapped⟩ hreleaseCT)
  · exact raw_publicReleaseTrace_step_private_release hanalysis hlookup
      hoperation hnonpublic

/-- A shared release or releaseCT at a verifier-Public occurrence becomes one exact matched
    progress case.  Equality of the complete remaining filtered trace determines the current
    unsanitized payload equality and preserves every later Public release occurrence. -/
theorem publicExecutionProgress_of_verified_public_release_step
    {program : V9.Program}
    (_hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {leftTail rightTail : Nat} {left right : State}
    {leftResult rightResult : StepResult} {instruction : Instruction}
    (hleftSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root left)
    (hrightSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hoperation : instruction.op = .release ∨ instruction.op = .releaseCT)
    (hpublic : instruction.blockLabel = .pub)
    (hleftExecution : SuccessfulExecution (rawSemanticProgram program analysis) root
      (leftTail + 1) left leftResult)
    (hrightExecution : SuccessfulExecution (rawSemanticProgram program analysis) root
      (rightTail + 1) right rightResult)
    (hrelease : publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (leftTail + 1) left).events =
      publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (rightTail + 1) right).events) :
    PublicExecutionProgress (rawSemanticProgram program analysis) root
      (leftTail + 1) left (rightTail + 1) right := by
  have hmatching := matching_public_release_of_remaining_traces hanalysis hlow hlookup
    hoperation hpublic
    ⟨hleftSync.active.notHalted, hleftSync.active.notTrapped⟩
    ⟨hrightSync.active.notHalted, hrightSync.active.notTrapped⟩ hrelease
  exact publicExecutionProgress_of_reachable_matching_step hleftSync.reachable
    hrightSync.reachable hleftExecution hrightExecution hmatching.1.1 hmatching.1.2
    hmatching.2

/-- A shared downgrade at a non-Public occurrence advances by one actual raw step on both sides.
    The local verifier proof preserves the full Public projection and control relation.  Its raw
    release singleton is retained (see `verified_private_release_raw_head_and_public_filter`),
    while two empty filtered heads expose equality of the independently sized suffixes. -/
theorem publicExecutionProgress_of_verified_nonpublic_release_step
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {leftTail rightTail : Nat} {left right : State}
    {leftResult rightResult : StepResult} {instruction : Instruction}
    (hleftSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root left)
    (hrightSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hoperation : instruction.op = .release ∨ instruction.op = .releaseCT)
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (hleftExecution : SuccessfulExecution (rawSemanticProgram program analysis) root
      (leftTail + 1) left leftResult)
    (hrightExecution : SuccessfulExecution (rawSemanticProgram program analysis) root
      (rightTail + 1) right rightResult)
    (hrelease : publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (leftTail + 1) left).events =
      publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (rightTail + 1) right).events) :
    PublicExecutionProgress (rawSemanticProgram program analysis) root
      (leftTail + 1) left (rightTail + 1) right := by
  let machine := rawSemanticProgram program analysis
  have hnotCall : instruction.op ≠ .call := by
    rcases hoperation with hrelease | hreleaseCT <;> simp_all
  have hnotClosure : instruction.op ≠ .closure := by
    rcases hoperation with hrelease | hreleaseCT <;> simp_all
  have hnotOutput : instruction.op ≠ .output := by
    rcases hoperation with hrelease | hreleaseCT <;> simp_all
  have hnotTrap : instruction.op ≠ .trap := by
    rcases hoperation with hrelease | hreleaseCT <;> simp_all
  have hnotBranch : instruction.op ≠ .branch := by
    rcases hoperation with hrelease | hreleaseCT <;> simp_all
  have hnotLoop : instruction.op ≠ .loop := by
    rcases hoperation with hrelease | hreleaseCT <;> simp_all
  have hnotRange : instruction.op ≠ .range := by
    rcases hoperation with hrelease | hreleaseCT <;> simp_all
  have hnotDispatch : instruction.op ≠ .dispatch := by
    rcases hoperation with hrelease | hreleaseCT <;> simp_all
  have hnextPc := nextPc_eq_of_nonbranching hlow instruction hnotBranch hnotLoop
    hnotRange hnotDispatch
  have hnextLow : PublicLowEquivalent machine (step machine left).state
      (step machine right).state := by
    exact verified_nonpublic_noncall_same_control_step hverified hanalysis
      hleftSync.reachable hrightSync.reachable hleftSync.active hrightSync.active hlow
      hlookup hnonpublic hnotCall hnotClosure hnotOutput hnotTrap hnextPc
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    simpa [machine] using hlookup
  have hobservation : publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events := by
    rw [nonpublic_step_has_no_public_boundary_observation machine left instruction
        (by simpa [machine] using hlookup) hnonpublic,
      nonpublic_step_has_no_public_boundary_observation machine right instruction
        hrightLookup hnonpublic]
  have hleftHead := raw_publicReleaseTrace_step_private_release hanalysis hlookup
    hoperation hnonpublic
  have hrightHead := raw_publicReleaseTrace_step_private_release hanalysis
    (by simpa [machine] using hrightLookup) hoperation hnonpublic
  have hreleaseTail := public_release_tail_eq_of_matching_heads hrelease (by
    rw [hleftHead, hrightHead])
  exact publicExecutionProgress_of_reachable_matching_step hleftSync.reachable
    hrightSync.reachable hleftExecution hrightExecution hnextLow hobservation hreleaseTail

/-- Unified downgrade bridge used by the final dispatcher.  Public and private occurrences are
    separated by the verifier-derived block label; both consume exact independent successful
    executions and the same complete filtered release-trace equality. -/
theorem publicExecutionProgress_of_verified_release_step
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {leftTail rightTail : Nat} {left right : State}
    {leftResult rightResult : StepResult} {instruction : Instruction}
    (hleftSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root left)
    (hrightSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hoperation : instruction.op = .release ∨ instruction.op = .releaseCT)
    (hleftExecution : SuccessfulExecution (rawSemanticProgram program analysis) root
      (leftTail + 1) left leftResult)
    (hrightExecution : SuccessfulExecution (rawSemanticProgram program analysis) root
      (rightTail + 1) right rightResult)
    (hrelease : publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (leftTail + 1) left).events =
      publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (rightTail + 1) right).events) :
    PublicExecutionProgress (rawSemanticProgram program analysis) root
      (leftTail + 1) left (rightTail + 1) right := by
  by_cases hpublic : instruction.blockLabel = .pub
  · exact publicExecutionProgress_of_verified_public_release_step hverified hanalysis
      hleftSync hrightSync hlow hlookup hoperation hpublic hleftExecution hrightExecution hrelease
  · exact publicExecutionProgress_of_verified_nonpublic_release_step hverified hanalysis
      hleftSync hrightSync hlow hlookup hoperation hpublic hleftExecution hrightExecution hrelease

end LambdaSigil.Combined.V9.PublicReleaseProgressSecurity
