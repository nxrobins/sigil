import LambdaSigil.PublicNonpublicStepSecurity

/-!
# Matched-step progress packaging

This leaf module turns already-proved raw matching facts into the strictly decreasing progress
objects used by the independent-length Public dispatcher.  It adds no semantic classification:
controller regions and private call/closure activations remain the responsibility of their
dedicated convergence layers.
-/

namespace LambdaSigil.Combined.V9.PublicMatchedProgressSecurity

open Semantic
open Semantic.PublicRegionSecurity Semantic.PublicReleaseSynchronization
open PublicExecutionSecurity PublicNonpublicStepSecurity

/-- Every successful execution's actual first successor is nontrapping.  When the suffix is
    nonempty this follows from active-prefix provenance; when the first step completes the run it
    follows from the successful result itself. -/
theorem successfulExecution_first_successor_not_trapped
    {machine : SemanticProgram} {root : UInt32} {tail : Nat}
    {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution machine root (tail + 1) start result) :
    (step machine start).state.trapped = false := by
  cases tail with
  | zero =>
      have hstep : step machine start = result := by
        simpa [runPrefix] using hexecution.run
      rw [hstep]
      exact hexecution.notTrapped
  | succ tail =>
      have hactive := hexecution.reached_active (elapsed := 1) (by omega)
      simpa only [runPrefix] using hactive.notTrapped

/-- If the actual first successor already halted, a successful execution cannot have a positive
    suffix.  This is the terminal half of first-step progress, stated independently of any
    relational theorem. -/
theorem successfulExecution_tail_eq_zero_of_first_successor_halted
    {machine : SemanticProgram} {root : UInt32} {tail : Nat}
    {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution machine root (tail + 1) start result)
    (hhalted : (step machine start).state.halted = true) :
    tail = 0 := by
  by_contra hnonzero
  have hpositive : 0 < tail := Nat.pos_of_ne_zero hnonzero
  have hactive := hexecution.reached_active (elapsed := 1) (by omega)
  have hnotHalted : (step machine start).state.halted = false := by
    simpa only [runPrefix] using hactive.notHalted
  rw [hhalted] at hnotHalted
  contradiction

/-- Reachability and the two real successful executions discharge the synchronization callbacks
    of `publicExecutionProgress_of_matching_step`.  Callers supply only facts established by the
    constructor-local matcher and the exact filtered release tails. -/
theorem publicExecutionProgress_of_reachable_matching_step
    {machine : SemanticProgram} {root : UInt32}
    {leftTail rightTail : Nat} {left right : State}
    {leftResult rightResult : StepResult}
    (hleftReachable : ReachableFromRoot machine root left)
    (hrightReachable : ReachableFromRoot machine root right)
    (hleftExecution : SuccessfulExecution machine root (leftTail + 1) left leftResult)
    (hrightExecution : SuccessfulExecution machine root (rightTail + 1) right rightResult)
    (hnextLow : PublicLowEquivalent machine (step machine left).state
      (step machine right).state)
    (hobservation : publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events)
    (hreleaseTail : publicReleaseTrace machine
        (runPrefix machine leftTail (step machine left).state).events =
      publicReleaseTrace machine
        (runPrefix machine rightTail (step machine right).state).events) :
    PublicExecutionProgress machine root (leftTail + 1) left (rightTail + 1) right := by
  exact publicExecutionProgress_of_matching_step hleftExecution hrightExecution hnextLow
    hobservation
    (fun hpositive => verifiedSynchronizationPoint_after_successful_step
      hleftReachable hleftExecution hpositive)
    (fun hpositive => verifiedSynchronizationPoint_after_successful_step
      hrightReachable hrightExecution hpositive)
    hreleaseTail

/-- A verified non-Public output is now directly consumable by the final dispatcher.  Internal
    returns use the matching-step constructor.  A top-level private output must consume both
    executions in exactly one step and is therefore packaged as a complete private terminal,
    preserving its intentionally silent boundary behavior rather than reclassifying it as a
    Public matched output. -/
theorem publicExecutionProgress_of_nonpublic_output_pair_outcome
    {machine : SemanticProgram} {root : UInt32}
    {leftTail rightTail : Nat} {left right : State}
    {leftResult rightResult : StepResult}
    (hleftReachable : ReachableFromRoot machine root left)
    (hrightReachable : ReachableFromRoot machine root right)
    (hstartLow : PublicLowEquivalent machine left right)
    (hleftExecution : SuccessfulExecution machine root (leftTail + 1) left leftResult)
    (hrightExecution : SuccessfulExecution machine root (rightTail + 1) right rightResult)
    (houtcome : VerifiedNonpublicOutputPairOutcome machine left right)
    (hreleaseTail : publicReleaseTrace machine
        (runPrefix machine leftTail (step machine left).state).events =
      publicReleaseTrace machine
        (runPrefix machine rightTail (step machine right).state).events) :
    PublicExecutionProgress machine root (leftTail + 1) left (rightTail + 1) right := by
  cases houtcome with
  | internalReturn evidence =>
      exact publicExecutionProgress_of_reachable_matching_step hleftReachable hrightReachable
        hleftExecution hrightExecution evidence.successorLow evidence.boundaryMatch hreleaseTail
  | completeTerminal evidence =>
      have hleftZero := successfulExecution_tail_eq_zero_of_first_successor_halted
        hleftExecution evidence.leftHalted
      have hrightZero := successfulExecution_tail_eq_zero_of_first_successor_halted
        hrightExecution evidence.rightHalted
      subst leftTail
      subst rightTail
      have hleftResultState : (step machine left).state = leftResult.state := by
        have hrun := congrArg StepResult.state hleftExecution.run
        simpa [runPrefix] using hrun
      have hrightResultState : (step machine right).state = rightResult.state := by
        have hrun := congrArg StepResult.state hrightExecution.run
        simpa [runPrefix] using hrun
      have hleftSegment : PublicSilentSegment machine 1 left leftResult.state := by
        rw [← hleftResultState]
        exact evidence.leftSilent
      have hrightSegment : PublicSilentSegment machine 1 right rightResult.state := by
        rw [← hrightResultState]
        exact evidence.rightSilent
      exact publicExecutionProgress_of_complete_private_segments hstartLow
        hleftSegment hrightSegment (by simpa using hleftExecution)
        (by simpa using hrightExecution)

end LambdaSigil.Combined.V9.PublicMatchedProgressSecurity
