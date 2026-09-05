import LambdaSigil.PublicMatchedProgressSecurity

/-!
# Same-control progress packaging

This leaf module is the shared-successor portion of the production Public dispatcher.  It
combines exact successful executions, one decoded current instruction, and equality of the
remaining filtered release trace with the already-proved constructor-local matching results.
Downgrades, calls/closures, and unequal controller successors are intentionally outside it.
-/

namespace LambdaSigil.Combined.V9.PublicSameControlProgressSecurity

open Semantic OccurrenceDataflowInvocation OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity Semantic.PublicReleaseSynchronization
open PublicLocalSecurity PublicMatchingSecurity PublicExecutionSecurity
open PublicNonpublicStepSecurity PublicMatchedProgressSecurity

/-- A verified Public, non-downgrade raw step with a shared successor becomes one exact progress
    case.  Calls and closures are explicit exclusions even though the underlying local matcher is
    more general; their activation-spanning proof belongs to the private-frame dispatcher layer.
    The closure-callee equality remains explicit because it is a load-bearing input of the local
    constructor-complete matcher. -/
theorem publicExecutionProgress_of_verified_public_same_control_noncall_step
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
    (hpublic : instruction.blockLabel = .pub)
    (_hnotCall : instruction.op ≠ .call)
    (_hnotClosure : instruction.op ≠ .closure)
    (hnotRelease : instruction.op ≠ .release)
    (hnotReleaseCT : instruction.op ≠ .releaseCT)
    (hnextPc : nextPc (rawSemanticProgram program analysis) left instruction
        (operandValue (rawSemanticProgram program analysis) left instruction) =
      nextPc (rawSemanticProgram program analysis) right instruction
        (operandValue (rawSemanticProgram program analysis) right instruction))
    (hclosureCallee : instruction.op = .closure →
      instructionCallee? (rawSemanticProgram program analysis) left instruction =
        instructionCallee? (rawSemanticProgram program analysis) right instruction)
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
  have hleftNext := successfulExecution_first_successor_not_trapped hleftExecution
  have hrightNext := successfulExecution_first_successor_not_trapped hrightExecution
  have hmatching := matching_verified_same_control_step
    (v9_occurrence_verifier_sound hverified) hanalysis hleftSync.active hrightSync.active
    hlow hlookup hpublic hnextPc hclosureCallee hnotRelease hnotReleaseCT
    hleftNext hrightNext
  have hreleaseTail := public_release_tail_of_shared_nonrelease hlow hlookup
    hnotRelease hnotReleaseCT hrelease
  exact publicExecutionProgress_of_reachable_matching_step hleftSync.reachable
    hrightSync.reachable hleftExecution hrightExecution hmatching.1 hmatching.2 hreleaseTail

/-- A verified non-Public ordinary/trap constructor with a shared raw successor becomes one
    matching progress case.  `.trap` uses the stronger successful-tail rule with both actual
    successors known nontrapping; all other constructors use the general non-Public local rule.
    Output and call/closure behavior remain separate. -/
theorem publicExecutionProgress_of_verified_nonpublic_same_control_noncall_step
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
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (hnotCall : instruction.op ≠ .call)
    (hnotClosure : instruction.op ≠ .closure)
    (hnotOutput : instruction.op ≠ .output)
    (hnotRelease : instruction.op ≠ .release)
    (hnotReleaseCT : instruction.op ≠ .releaseCT)
    (hnextPc : nextPc (rawSemanticProgram program analysis) left instruction
        (operandValue (rawSemanticProgram program analysis) left instruction) =
      nextPc (rawSemanticProgram program analysis) right instruction
        (operandValue (rawSemanticProgram program analysis) right instruction))
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
  have hleftNext := successfulExecution_first_successor_not_trapped hleftExecution
  have hrightNext := successfulExecution_first_successor_not_trapped hrightExecution
  have hnextLow : PublicLowEquivalent machine (step machine left).state
      (step machine right).state := by
    by_cases htrap : instruction.op = .trap
    · exact (verified_nonpublic_trap_same_control_nontrapping_step hverified hanalysis
        hleftSync.reachable hrightSync.reachable hleftSync.active hrightSync.active hlow
        hlookup hnonpublic htrap hnextPc hleftNext hrightNext).2.2
    · exact verified_nonpublic_noncall_same_control_step hverified hanalysis
        hleftSync.reachable hrightSync.reachable hleftSync.active hrightSync.active hlow
        hlookup hnonpublic hnotCall hnotClosure hnotOutput htrap hnextPc
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    simpa [machine] using hlookup
  have hobservation : publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events := by
    rw [nonpublic_step_has_no_public_boundary_observation machine left instruction
        (by simpa [machine] using hlookup) hnonpublic,
      nonpublic_step_has_no_public_boundary_observation machine right instruction
        hrightLookup hnonpublic]
  have hreleaseTail := public_release_tail_of_shared_nonrelease hlow hlookup
    hnotRelease hnotReleaseCT hrelease
  exact publicExecutionProgress_of_reachable_matching_step hleftSync.reachable
    hrightSync.reachable hleftExecution hrightExecution hnextLow hobservation hreleaseTail

/-- A verified non-Public output uses its frame-aware paired classification.  The actual
    nontrapping guards and the filtered release suffix are recovered from the successful
    executions, so callers cannot supply a fabricated return-flow verdict or cursor. -/
theorem publicExecutionProgress_of_verified_nonpublic_output_step
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
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (houtput : instruction.op = .output)
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
  have hleftNext := successfulExecution_first_successor_not_trapped hleftExecution
  have hrightNext := successfulExecution_first_successor_not_trapped hrightExecution
  have houtcome := verified_nonpublic_output_pair_outcome hverified hanalysis
    hleftSync.reachable hrightSync.reachable hleftSync.active hrightSync.active hlow
    hlookup hnonpublic houtput hleftNext hrightNext
  have hnotRelease : instruction.op ≠ .release := by simp [houtput]
  have hnotReleaseCT : instruction.op ≠ .releaseCT := by simp [houtput]
  have hreleaseTail := public_release_tail_of_shared_nonrelease hlow hlookup
    hnotRelease hnotReleaseCT hrelease
  exact publicExecutionProgress_of_nonpublic_output_pair_outcome hleftSync.reachable
    hrightSync.reachable hlow hleftExecution hrightExecution houtcome hreleaseTail

/-- Unified shared-control dispatcher bridge for every non-downgrade, non-call/closure raw
    constructor.  Public occurrences use the constructor-complete Public matcher; private output
    uses frame-aware return/terminal classification; every remaining private constructor uses the
    non-Public ordinary/trap package. -/
theorem publicExecutionProgress_of_verified_same_control_noncall_step
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
    (hnotCall : instruction.op ≠ .call)
    (hnotClosure : instruction.op ≠ .closure)
    (hnotRelease : instruction.op ≠ .release)
    (hnotReleaseCT : instruction.op ≠ .releaseCT)
    (hnextPc : nextPc (rawSemanticProgram program analysis) left instruction
        (operandValue (rawSemanticProgram program analysis) left instruction) =
      nextPc (rawSemanticProgram program analysis) right instruction
        (operandValue (rawSemanticProgram program analysis) right instruction))
    (hclosureCallee : instruction.op = .closure →
      instructionCallee? (rawSemanticProgram program analysis) left instruction =
        instructionCallee? (rawSemanticProgram program analysis) right instruction)
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
  · exact publicExecutionProgress_of_verified_public_same_control_noncall_step
      hverified hanalysis hleftSync hrightSync hlow hlookup hpublic hnotCall hnotClosure
      hnotRelease hnotReleaseCT hnextPc hclosureCallee hleftExecution hrightExecution hrelease
  · by_cases houtput : instruction.op = .output
    · exact publicExecutionProgress_of_verified_nonpublic_output_step
        hverified hanalysis hleftSync hrightSync hlow hlookup hpublic houtput
        hleftExecution hrightExecution hrelease
    · exact publicExecutionProgress_of_verified_nonpublic_same_control_noncall_step
        hverified hanalysis hleftSync hrightSync hlow hlookup hpublic hnotCall hnotClosure
        houtput hnotRelease hnotReleaseCT hnextPc hleftExecution hrightExecution hrelease

end LambdaSigil.Combined.V9.PublicSameControlProgressSecurity
