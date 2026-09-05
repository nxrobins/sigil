import LambdaSigil.PublicDispatcherSecurity
import LambdaSigil.PublicControllerSegmentSecurity
import LambdaSigil.PublicPrivateInvocationSecurity
import LambdaSigil.PublicSyntheticReturnSecurity

/-!
# Verifier-derived Public weak bisimulation

This module is the production composition boundary.  It instantiates the constructor-complete
dispatcher solely from V9 verifier facts, actual independently sized successful executions, and
the complete release trace supplied by the theorem caller.  The internal induction carries the
occurrence-filtered Public release suffix; no equal-fuel premise or caller-provided alignment is
present on either exported claim.
-/

namespace LambdaSigil.Combined.V9.PublicBisimulationSecurity

open Semantic OccurrenceRegions OccurrenceTransfer
open OccurrenceDataflowInvocation OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity Semantic.PublicReleaseSynchronization
open PublicExecutionSecurity PublicStepClassification
open PublicSameControlProgressSecurity PublicDispatcherSecurity
open PublicControllerSegmentSecurity PublicPrivateInvocationSecurity
open PublicSyntheticReturnSecurity

/-- Controller-only composition before the synthetic-return eliminator is applied.  The callback
    is private to this proof module and receives the fully verifier-derived residual package; it
    never appears in either production theorem signature. -/
private theorem publicExecutionProgress_of_verified_controller_with_synthetic
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {leftTail rightTail : Nat} {left right : State}
    {leftResult rightResult : StepResult} {instruction : Instruction}
    (hleftSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root left)
    (hrightSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2))
    (hleftExecution : SuccessfulExecution (rawSemanticProgram program analysis) root
      (leftTail + 1) left leftResult)
    (hrightExecution : SuccessfulExecution (rawSemanticProgram program analysis) root
      (rightTail + 1) right rightResult)
    (hrelease : publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (leftTail + 1) left).events =
      publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (rightTail + 1) right).events)
    (hsynthetic :
      SyntheticPrivateControllerSegments (rawSemanticProgram program analysis)
          analysis.localAnalysis.frontiers root (leftTail + 1) (rightTail + 1) left right →
        PublicExecutionProgress (rawSemanticProgram program analysis) root
          (leftTail + 1) left (rightTail + 1) right) :
    PublicExecutionProgress (rawSemanticProgram program analysis) root
      (leftTail + 1) left (rightTail + 1) right := by
  have hjudgment := v9_occurrence_verifier_sound hverified
  rcases verified_controller_selector_classification hjudgment hanalysis hlookup hcontrol with
    hpublic | ⟨lane, hlane, hselector, _⟩
  · have hnextPc := controller_nextPc_eq_of_public_selector hjudgment hanalysis
      hlow hlookup hcontrol hpublic
    apply publicExecutionProgress_of_verified_same_control_noncall_step
      hverified hanalysis hleftSync hrightSync hlow hlookup
    · rcases hcontrol with hbranch | hloop | hrange | hdispatch <;> simp_all
    · rcases hcontrol with hbranch | hloop | hrange | hdispatch <;> simp_all
    · rcases hcontrol with hbranch | hloop | hrange | hdispatch <;> simp_all
    · rcases hcontrol with hbranch | hloop | hrange | hdispatch <;> simp_all
    · exact hnextPc
    · intro hclosure
      rcases hcontrol with hbranch | hloop | hrange | hdispatch <;> simp_all
    · exact hleftExecution
    · exact hrightExecution
    · exact hrelease
  · have hsegments := v9_verified_successful_private_controller_segments
      hverified hanalysis hleftSync hrightSync hlow hleftExecution hrightExecution
      hlookup hcontrol hselector hlane
    have hreleaseResult : publicReleaseTrace (rawSemanticProgram program analysis)
          leftResult.events =
        publicReleaseTrace (rawSemanticProgram program analysis) rightResult.events := by
      rw [← hleftExecution.run, ← hrightExecution.run]
      exact hrelease
    rcases publicExecutionProgress_or_synthetic_of_private_controller_segments hsegments
      hleftExecution hrightExecution hreleaseResult with hprogress | hresidual
    · exact hprogress
    · exact hsynthetic hresidual

/-- Constructor-complete dispatcher with the one honest synthetic-return seam still explicit.
    The next theorem closes that seam from V9 acceptance; separating the two makes the exhaustive
    instruction split independently reviewable. -/
private theorem v9_publicExecutionProgressDispatcher_from_synthetic
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32}
    (hsynthetic : ∀ {leftSteps rightSteps : Nat} {left right : State}
        {leftResult rightResult : StepResult},
      VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root left →
      VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root right →
      PublicLowEquivalent (rawSemanticProgram program analysis) left right →
      SuccessfulExecution (rawSemanticProgram program analysis) root
        leftSteps left leftResult →
      SuccessfulExecution (rawSemanticProgram program analysis) root
        rightSteps right rightResult →
      publicReleaseTrace (rawSemanticProgram program analysis) leftResult.events =
        publicReleaseTrace (rawSemanticProgram program analysis) rightResult.events →
      SyntheticPrivateControllerSegments (rawSemanticProgram program analysis)
          analysis.localAnalysis.frontiers root leftSteps rightSteps left right →
      PublicExecutionProgress (rawSemanticProgram program analysis) root
        leftSteps left rightSteps right) :
    PublicExecutionProgressDispatcher (rawSemanticProgram program analysis) root := by
  intro leftSteps rightSteps left right leftResult rightResult
    hleftSync hrightSync hlow hleftExecution hrightExecution hreleaseResult
  cases leftSteps with
  | zero =>
      exact False.elim (by have := hleftExecution.positive; omega)
  | succ leftTail =>
      cases rightSteps with
      | zero =>
          exact False.elim (by have := hrightExecution.positive; omega)
      | succ rightTail =>
          change SuccessfulExecution (rawSemanticProgram program analysis) root
            (leftTail + 1) left leftResult at hleftExecution
          change SuccessfulExecution (rawSemanticProgram program analysis) root
            (rightTail + 1) right rightResult at hrightExecution
          obtain ⟨instruction, hlookup, _⟩ := hleftSync.active.currentInstruction
          have hreleaseRun : publicReleaseTrace (rawSemanticProgram program analysis)
                (runPrefix (rawSemanticProgram program analysis) (leftTail + 1) left).events =
              publicReleaseTrace (rawSemanticProgram program analysis)
                (runPrefix (rawSemanticProgram program analysis) (rightTail + 1) right).events := by
            rw [hleftExecution.run, hrightExecution.run]
            exact hreleaseResult
          apply publicExecutionProgress_of_structured_callbacks hverified hanalysis
            hleftSync hrightSync hlow hlookup hleftExecution hrightExecution hreleaseRun
          · intro hcontrol
            apply publicExecutionProgress_of_verified_controller_with_synthetic
              hverified hanalysis hleftSync hrightSync hlow hlookup hcontrol
              hleftExecution hrightExecution hreleaseRun
            intro hresidual
            exact hsynthetic hleftSync hrightSync hlow hleftExecution hrightExecution
              hreleaseResult hresidual
          · intro hoperation
            exact publicExecutionProgress_of_verified_call_or_closure hverified hanalysis
              hleftSync hrightSync hlow hlookup hoperation hleftExecution hrightExecution
              hreleaseRun

/-- The production V9 dispatcher.  Every progress case is obtained from the decoded program,
    verifier acceptance, and the two actual successful executions.  In particular, the
    synthetic function-return case executes the real `.output` instructions and proves either a
    genuine paired internal continuation or a genuine paired terminal result. -/
theorem v9_publicExecutionProgressDispatcher
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} :
    PublicExecutionProgressDispatcher (rawSemanticProgram program analysis) root := by
  apply v9_publicExecutionProgressDispatcher_from_synthetic hverified hanalysis
  intro leftSteps rightSteps left right leftResult rightResult
    hleftSync hrightSync hlow hleftExecution hrightExecution hrelease hsegments
  exact publicExecutionProgress_of_verified_synthetic_private_controller_segments
    hverified hanalysis hleftSync hrightSync hlow hleftExecution hrightExecution
    hrelease hsegments

/-- Verifier-derived, independently sized Public weak bisimulation for the raw V9 machine.
    `FinitePublicAlignment` is constructed internally by strong induction over the two exact
    successful execution lengths.  The caller supplies only the complete raw release trace;
    filtering to Public release occurrences is a proved consequence of that equality. -/
theorem raw_public_weak_bisimulation_of_v9_verified :
    RawPublicWeakBisimulationV9Contract := by
  intro program analysis root leftSteps rightSteps left right leftResult rightResult
    hverified hanalysis hleftCut hrightCut _hleftWellFormed _hrightWellFormed hlow
    _hstreams hleftExecution hrightExecution hcompleteRelease
  have hpublicRelease : publicReleaseTrace (rawSemanticProgram program analysis)
        leftResult.events =
      publicReleaseTrace (rawSemanticProgram program analysis) rightResult.events :=
    complete_release_equality_implies_public_release_equality
      (rawSemanticProgram program analysis) hcompleteRelease
  exact finitePublicAlignment_of_progress_dispatcher_at_public_cuts
    (v9_publicExecutionProgressDispatcher hverified hanalysis)
    hleftCut hrightCut hlow hleftExecution hrightExecution hpublicRelease

/-- Full termination-insensitive Public noninterference for the raw V9 machine.  Successful runs
    may use unrelated fuel budgets; each is normalized to its own exact successful length.  The
    conclusion is the complete `publicProjection` together with the ordered Public output and
    boundary trace, rather than an exported-result approximation. -/
theorem raw_public_delimited_release_noninterference_of_v9_verified :
    RawPublicDelimitedReleaseNoninterferenceV9Contract :=
  rawPublicDelimitedReleaseContract_of_weakBisimulation
    raw_public_weak_bisimulation_of_v9_verified

end LambdaSigil.Combined.V9.PublicBisimulationSecurity
