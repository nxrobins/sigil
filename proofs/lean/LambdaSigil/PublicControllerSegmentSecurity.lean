import LambdaSigil.PublicContinuationSecurity
import LambdaSigil.PublicPrivateReleaseSecurity
import LambdaSigil.PublicStepClassification

/-!
# Verified controller-to-continuation segments

This module packages the exact operational seam used by the Public weak-bisimulation dispatcher:
the real controller step followed by the independently long raw execution of its selected
Internal/Secret arm.  Both parts remain in `runPrefix`; no summarized branch transition is used.

The endpoint is classified by `PublicContinuationSecurity` as either a matching current
continuation or a paired synthetic function return.  The latter is never reified as an ordinary
instruction or forced to share a program counter.
-/

namespace LambdaSigil.Combined.V9.PublicControllerSegmentSecurity

open Semantic OccurrenceRegions OccurrenceTransfer
open OccurrenceDataflowInvocation OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity Semantic.PublicRegionConvergence
open Semantic.PublicReleaseSynchronization
open PublicLocalSecurity PublicMatchingSecurity PublicStepClassification
open PublicPrivateSegmentSecurity PublicPrivateReleaseSecurity
open PublicExecutionSecurity PublicContinuationSecurity

private theorem controller_nonrelease {instruction : Instruction}
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2)) :
    instruction.op ≠ .release ∧ instruction.op ≠ .releaseCT := by
  rcases hcontrol with hbranch | hloop | hrange | hdispatch <;> simp_all

private theorem controller_cells_public_of_public_result
    {program : V9.Program} {analysis : Analysis} {machine : SemanticProgram}
    {instruction : Instruction}
    (hsafe : PublicResultDependenciesSafe program analysis machine instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2))
    (hdestination : instruction.destination ≠ 0)
    (hresult : instruction.resultLabel = .pub) :
    CellsPublic machine (valueOperandCells machine instruction) := by
  have hbody := hsafe hdestination hresult
  apply cellsPublic_of_cellsPublicB
  rcases hcontrol with hbranch | hloop | hrange | hdispatch
  · simpa [publicResultDependencyBodyOK, hbranch] using hbody
  · simpa [publicResultDependencyBodyOK, hloop] using hbody
  · simpa [publicResultDependencyBodyOK, hrange] using hbody
  · simpa [publicResultDependencyBodyOK, hdispatch.1] using hbody

private theorem operandValue_label_public_of_cellsPublic
    {machine : SemanticProgram} {state : State} {instruction : Instruction}
    (hcells : CellsPublic machine (valueOperandCells machine instruction)) :
    (operandValue machine state instruction).label = .pub := by
  cases hhead : (valueOperandCells machine instruction).head? with
  | none => simp [operandValue, operandValues, hhead, defaultValue]
  | some cell =>
      obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp hhead
      have hmem : cell ∈ valueOperandCells machine instruction := by
        rw [htail]
        simp
      have hpublic := hcells cell hmem
      simp [operandValue, operandValues, hhead, readProgramValue, hpublic]

/-- A verified controller whose selector is Internal/Secret cannot mutate the Public projection
    in its entry step.  If its destination were nonzero and Public, the result-dependency check
    would force every value operand—and hence the exact selector operand—to be Public, contrary
    to the verifier-derived lane. -/
theorem verified_private_controller_step_preserves_publicProjection
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {state : State} {instruction : Instruction} {lane : Label}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2))
    (hselector : analysis.localAnalysis.selectors.getD state.pc .pub = lane)
    (hlane : lane = .internal ∨ lane = .secret) :
    publicProjection (rawSemanticProgram program analysis)
        (step (rawSemanticProgram program analysis) state).state =
      publicProjection (rawSemanticProgram program analysis) state := by
  let machine := rawSemanticProgram program analysis
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hwell := instruction_well_formed_of_raw_static_safe hstatic hlookup
  have hdependencies := returned_public_result_dependencies_safe hjudgment hanalysis hlookup
  have hisolated : instruction.destination = 0 ∨ instruction.resultLabel ≠ .pub := by
    by_cases hzero : instruction.destination = 0
    · exact Or.inl hzero
    · refine Or.inr ?_
      intro hpublic
      have hcells := controller_cells_public_of_public_result hdependencies hcontrol hzero hpublic
      have hoperandPublic := operandValue_label_public_of_cellsPublic
        (state := state) hcells
      have hselectorOperand :=
        analyzed_controller_selector_eq_operand_label hjudgment hanalysis hlookup hcontrol
      have hlanePublic : lane = .pub := by
        rw [← hselector, hselectorOperand]
        exact hoperandPublic
      rcases hlane with rfl | rfl <;> cases hlanePublic
  have hwrite := writeDestination_preserves_publicProjection state instruction
    (instructionPayload machine state instruction) hwell hisolated
  have hordinary : publicProjection (rawSemanticProgram program analysis)
        (ordinaryStep (rawSemanticProgram program analysis) state instruction).state =
      publicProjection (rawSemanticProgram program analysis) state := by
    rcases hcontrol with hbranch | hloop | hrange | hdispatch
    · simpa [ordinaryStep, hbranch, publicProjection] using hwrite
    · simpa [ordinaryStep, hloop, publicProjection] using hwrite
    · simpa [ordinaryStep, hrange, publicProjection] using hwrite
    · simpa [ordinaryStep, hdispatch.1, publicProjection] using hwrite
  rcases hcontrol with hbranch | hloop | hrange | hdispatch
  · simpa [machine, step, hactive.notHalted, hactive.notTrapped, hlookup, hbranch] using hordinary
  · simpa [machine, step, hactive.notHalted, hactive.notTrapped, hlookup, hloop] using hordinary
  · simpa [machine, step, hactive.notHalted, hactive.notTrapped, hlookup, hrange] using hordinary
  · simpa [machine, step, hactive.notHalted, hactive.notTrapped, hlookup, hdispatch.1]
      using hordinary

/-- The actual controller entry is one Public-boundary-silent, Public-projection-preserving raw
    step.  Its filtered release trace is empty because no controller is a downgrade. -/
theorem verified_private_controller_entry_segments
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {state : State} {instruction : Instruction} {lane : Label}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2))
    (hselector : analysis.localAnalysis.selectors.getD state.pc .pub = lane)
    (hlane : lane = .internal ∨ lane = .secret) :
    PublicSilentSegment (rawSemanticProgram program analysis) 1 state
        (step (rawSemanticProgram program analysis) state).state ∧
      PublicReleaseSilentSegment (rawSemanticProgram program analysis) 1 state := by
  let machine := rawSemanticProgram program analysis
  have hprojection := verified_private_controller_step_preserves_publicProjection
    hjudgment hanalysis hactive hlookup hcontrol hselector hlane
  have hinstructionBoundary :
      publicBoundaryTrace (instructionEvents machine state instruction) = [] := by
    rcases hcontrol with hbranch | hloop | hrange | hdispatch
    all_goals simp [instructionEvents, *,
      publicBoundaryTrace_eventsForObserved_nonobserved]
  have hordinaryBoundary :
      publicBoundaryTrace (ordinaryStep machine state instruction).events = [] := by
    simpa only [ordinaryStep] using hinstructionBoundary
  have hboundary : publicBoundaryTrace (step machine state).events = [] := by
    rcases hcontrol with hbranch | hloop | hrange | hdispatch
    all_goals simpa [machine, step, hactive.notHalted, hactive.notTrapped, hlookup, *]
      using hordinaryBoundary
  have hsegment : PublicSilentSegment machine 1 state (step machine state).state :=
    publicSilentSegment_one hboundary hprojection
  have hnonrelease := controller_nonrelease hcontrol
  refine ⟨hsegment, ?_⟩
  intro elapsed helapsed
  have helapsedZero : elapsed = 0 := by omega
  subst elapsed
  simpa only [runPrefix] using
    publicReleaseTrace_step_nonrelease machine state instruction hlookup
      hnonrelease.1 hnonrelease.2

/-! ## Independently sized controller regions -/

/-- Two concrete controller/private-arm prefixes together with their honest shared-continuation
    classification.  The lengths are actual raw step counts and may differ. -/
def PairedPrivateControllerSegments (machine : SemanticProgram) (frontiers : ThresholdFrontiers)
    (root : UInt32)
    (leftSteps rightSteps : Nat) (left right : State) : Prop :=
  ∃ leftLength rightLength leftFinish rightFinish parent,
    0 < leftLength ∧ 0 < rightLength ∧
      leftLength < leftSteps ∧ rightLength < rightSteps ∧
      PublicSilentSegment machine leftLength left leftFinish ∧
      PublicSilentSegment machine rightLength right rightFinish ∧
      PublicReleaseSilentSegment machine leftLength left ∧
      PublicReleaseSilentSegment machine rightLength right ∧
      (parent = functionReturn machine (activeFunctionId root left.callStack) →
        ∃ instruction, machine.instructions[leftFinish.pc]? = some instruction ∧
          localOccurrenceAt frontiers leftFinish.pc ≠ .pub) ∧
      (parent = functionReturn machine (activeFunctionId root right.callStack) →
        ∃ instruction, machine.instructions[rightFinish.pc]? = some instruction ∧
          localOccurrenceAt frontiers rightFinish.pc ≠ .pub) ∧
      PairedContinuationOutcome machine root parent left.callStack right.callStack
        leftFinish rightFinish

/-- Honest residual package for the synthetic-return branch.  Downstream composition must
    execute the two real output/halt instructions; this proposition does not turn them into a
    shared current pc. -/
def SyntheticPrivateControllerSegments (machine : SemanticProgram) (frontiers : ThresholdFrontiers)
    (root : UInt32)
    (leftSteps rightSteps : Nat) (left right : State) : Prop :=
  ∃ leftLength rightLength leftFinish rightFinish parent,
    0 < leftLength ∧ 0 < rightLength ∧
      leftLength < leftSteps ∧ rightLength < rightSteps ∧
      PublicSilentSegment machine leftLength left leftFinish ∧
      PublicSilentSegment machine rightLength right rightFinish ∧
      PublicReleaseSilentSegment machine leftLength left ∧
      PublicReleaseSilentSegment machine rightLength right ∧
      (∃ instruction, machine.instructions[leftFinish.pc]? = some instruction ∧
        localOccurrenceAt frontiers leftFinish.pc ≠ .pub) ∧
      (∃ instruction, machine.instructions[rightFinish.pc]? = some instruction ∧
        localOccurrenceAt frontiers rightFinish.pc ≠ .pub) ∧
      PairedSyntheticReturnContinuation machine root parent left.callStack right.callStack
        leftFinish rightFinish

/-- Unary production package used to assemble the paired result.  The endpoint is the exact
    verifier continuation for the controller occurrence at `start.pc`. -/
def PrivateControllerSegment (program : V9.Program) (analysis : Analysis)
    (root : UInt32) (steps : Nat) (start : State) : Prop :=
  ∃ length finish,
    0 < length ∧ length < steps ∧
      PublicSilentSegment (rawSemanticProgram program analysis) length start finish ∧
      PublicReleaseSilentSegment (rawSemanticProgram program analysis) length start ∧
      ReachableFromRoot (rawSemanticProgram program analysis) root finish ∧
      (analysis.localAnalysis.regions.index.parentAt start.pc =
          functionReturn (rawSemanticProgram program analysis)
            (activeFunctionId root start.callStack) →
        ∃ instruction,
          (rawSemanticProgram program analysis).instructions[finish.pc]? = some instruction ∧
          localOccurrenceAt analysis.localAnalysis.frontiers finish.pc ≠ .pub) ∧
      finish.callStack = start.callStack ∧
      ActivationContinuationAt (rawSemanticProgram program analysis) root
        start.callStack (analysis.localAnalysis.regions.index.parentAt start.pc) finish

private theorem publicReleaseSilentSegment_append {machine : SemanticProgram}
    {firstLength secondLength : Nat} {start middle : State}
    (hfirstFinish : (runPrefix machine firstLength start).state = middle)
    (hfirst : PublicReleaseSilentSegment machine firstLength start)
    (hsecond : PublicReleaseSilentSegment machine secondLength middle) :
    PublicReleaseSilentSegment machine (firstLength + secondLength) start := by
  intro elapsed helapsed
  by_cases hbefore : elapsed < firstLength
  · exact hfirst elapsed hbefore
  · have hafter : elapsed - firstLength < secondLength := by omega
    have hdecompose := congrArg StepResult.state
      (ReleaseSynchronization.runPrefix_add machine firstLength
        (elapsed - firstLength) start)
    have hsum : firstLength + (elapsed - firstLength) = elapsed := by omega
    rw [hsum] at hdecompose
    dsimp only at hdecompose
    rw [hfirstFinish] at hdecompose
    rw [hdecompose]
    exact hsecond (elapsed - firstLength) hafter

/-- A controller cannot itself be the successful execution's final top-level output/halt step.
    Hence its successful suffix contains at least one real raw step after the controller. -/
private theorem successful_controller_has_strict_tail {machine : SemanticProgram} {root : UInt32}
    {steps : Nat} {start : State} {result : StepResult} {instruction : Instruction}
    (hexecution : SuccessfulExecution machine root steps start result)
    (hlookup : machine.instructions[start.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2)) :
    1 < steps := by
  by_contra hnot
  have hpositive := hexecution.positive
  have hsteps : steps = 1 := by omega
  have hlast := hexecution.lastTopLevel
  simp only [hsteps, Nat.reduceSub, runPrefix] at hlast
  obtain ⟨_, terminal, hterminalLookup, hterminal⟩ := hlast
  have hsame : terminal = instruction := by
    rw [hlookup] at hterminalLookup
    exact Option.some.inj hterminalLookup.symm
  subst terminal
  rcases hcontrol with hbranch | hloop | hrange | hdispatch <;> simp_all

/-- A raw controller step selects exactly `nextPc`, preserves the call stack, and remains live.
    These are operational equalities, not merge certificates supplied by Rust. -/
private theorem controller_step_shape {machine : SemanticProgram} {root : UInt32}
    {state : State} {instruction : Instruction}
    (hactive : ActiveState machine root state)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2)) :
    (step machine state).state.pc =
        nextPc machine state instruction (operandValue machine state instruction) ∧
      (step machine state).state.callStack = state.callStack ∧
      (step machine state).state.halted = false ∧
      (step machine state).state.trapped = false := by
  rcases hcontrol with hbranch | hloop | hrange | hdispatch
  all_goals simp [step, hactive.notHalted, hactive.notTrapped, hlookup, *, ordinaryStep] <;>
    decide

/-- Production unary bridge: execute the real controller, then the independently long selected
    private arm, stopping at the verifier's exact first continuation.  The controller and arm are
    both proved silent in the Public boundary and filtered Public-release traces. -/
theorem v9_verified_successful_private_controller_segment
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {steps : Nat} {start : State} {result : StepResult}
    {instruction : Instruction} {lane : Label}
    (hreachable : ReachableFromRoot (rawSemanticProgram program analysis) root start)
    (hexecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root steps start result)
    (hlookup : (rawSemanticProgram program analysis).instructions[start.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2))
    (hselector : analysis.localAnalysis.selectors.getD start.pc .pub = lane)
    (hlane : lane = .internal ∨ lane = .secret) :
    PrivateControllerSegment program analysis root steps start := by
  let machine := rawSemanticProgram program analysis
  let base := OccurrenceDataflow.semanticProgram program analysis.dataflow
  let arm := nextPc machine start instruction (operandValue machine start instruction)
  have hjudgment := v9_occurrence_verifier_sound hverified
  have hactive := hexecution.start_active
  have htailBound := successful_controller_has_strict_tail hexecution
    (by simpa [machine] using hlookup) hcontrol
  have hshape := controller_step_shape hactive (by simpa [machine] using hlookup) hcontrol
  have htailExecution : SuccessfulExecution machine root (steps - 1)
      (step machine start).state
      (runPrefix machine (steps - 1) (step machine start).state) := by
    simpa only [runPrefix] using hexecution.drop (elapsed := 1) htailBound
  have hcontrollerRaw : start.pc < machine.instructions.size :=
    (Array.getElem?_eq_some_iff.mp (by simpa [machine] using hlookup)).1
  have hcontroller : start.pc < base.instructions.size := by
    simpa [machine, base] using hcontrollerRaw
  have hedgeRaw := controller_nextPc_mem_decoded_successors
    (machine := machine) (state := start) (instruction := instruction)
    (by simpa [machine] using hlookup) hcontrol
  have hedge : arm ∈ (decodedControlGraph base).successors.getD start.pc [] := by
    rw [← decodedControlGraph_rawSemanticProgram program analysis]
    simpa [machine, arm] using hedgeRaw
  have hlaneProof := privateControllerLane_of_selector hanalysis hlookup hcontrol
    hselector hlane
  have hentry := verified_private_controller_entry_segments hjudgment hanalysis hactive
    hlookup hcontrol hselector hlane
  obtain ⟨elapsed, helapsed, hcontinuation, hreachEnd, hendpointPrivate,
      hendStack, hendProjection, hanchors, hboundary⟩ :=
    v9_verified_successful_private_activation_prefix_preservation hverified hanalysis
      (root := root) (controller := start.pc) (arm := arm)
      (spine := start.callStack) hreachable.step htailExecution
      hshape.2.1 (by simpa [arm] using hshape.1) hcontroller hedge hlaneProof
  have hactivationRelease : PublicReleaseSilentSegment machine elapsed
      (step machine start).state := by
    apply verified_private_activation_publicReleaseSilentSegment hanalysis
    simpa [machine] using hanchors
  let finish := (runPrefix machine elapsed (step machine start).state).state
  have hactivation : PublicSilentSegment machine elapsed (step machine start).state finish := by
    refine ⟨rfl, ?_, ?_⟩
    · simpa [machine] using hboundary
    · simpa [machine, finish] using hendProjection
  have hfullSegment : PublicSilentSegment machine (1 + elapsed) start finish :=
    hentry.1.append hactivation
  have hfullRelease : PublicReleaseSilentSegment machine (1 + elapsed) start :=
    publicReleaseSilentSegment_append hentry.1.finish_eq hentry.2 hactivationRelease
  refine ⟨1 + elapsed, finish, by omega, by omega, hfullSegment, hfullRelease,
    ?_, ?_, ?_, ?_⟩
  · simpa [machine, finish] using hreachEnd
  · intro hparent
    simpa [machine, finish] using hendpointPrivate (by simpa [machine] using hparent)
  · simpa [machine, finish] using hendStack
  · simpa [machine, finish] using hcontinuation

/-- Paired production bridge for an Internal/Secret controller.  Each side takes its actual arm
    for its own exact number of raw steps.  The endpoints are classified as either the same
    current verifier continuation or two genuine synthetic-return states; no common pc is
    fabricated in the latter case. -/
theorem v9_verified_successful_private_controller_segments
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {leftSteps rightSteps : Nat}
    {left right : State} {leftResult rightResult : StepResult}
    (hleftSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root left)
    (hrightSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hleftExecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root leftSteps left leftResult)
    (hrightExecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root rightSteps right rightResult)
    {instruction : Instruction} {lane : Label}
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2))
    (hselector : analysis.localAnalysis.selectors.getD left.pc .pub = lane)
    (hlane : lane = .internal ∨ lane = .secret) :
    PairedPrivateControllerSegments (rawSemanticProgram program analysis)
      analysis.localAnalysis.frontiers root
      leftSteps rightSteps left right := by
  let machine := rawSemanticProgram program analysis
  have hpc : left.pc = right.pc := hlow.1
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hpc]
    simpa [machine] using hlookup
  have hrightSelector : analysis.localAnalysis.selectors.getD right.pc .pub = lane := by
    rw [← hpc]
    exact hselector
  have hleftPackage := v9_verified_successful_private_controller_segment
    hverified hanalysis hleftSync.reachable hleftExecution hlookup hcontrol hselector hlane
  have hrightPackage := v9_verified_successful_private_controller_segment
    hverified hanalysis hrightSync.reachable hrightExecution
      (by simpa [machine] using hrightLookup) hcontrol hrightSelector hlane
  change ∃ length finish,
      0 < length ∧ length < leftSteps ∧
        PublicSilentSegment machine length left finish ∧
        PublicReleaseSilentSegment machine length left ∧
        ReachableFromRoot machine root finish ∧
        (analysis.localAnalysis.regions.index.parentAt left.pc =
            functionReturn machine (activeFunctionId root left.callStack) →
          ∃ instruction, machine.instructions[finish.pc]? = some instruction ∧
            localOccurrenceAt analysis.localAnalysis.frontiers finish.pc ≠ .pub) ∧
        finish.callStack = left.callStack ∧
        ActivationContinuationAt machine root left.callStack
          (analysis.localAnalysis.regions.index.parentAt left.pc) finish at hleftPackage
  change ∃ length finish,
      0 < length ∧ length < rightSteps ∧
        PublicSilentSegment machine length right finish ∧
        PublicReleaseSilentSegment machine length right ∧
        ReachableFromRoot machine root finish ∧
        (analysis.localAnalysis.regions.index.parentAt right.pc =
            functionReturn machine (activeFunctionId root right.callStack) →
          ∃ instruction, machine.instructions[finish.pc]? = some instruction ∧
            localOccurrenceAt analysis.localAnalysis.frontiers finish.pc ≠ .pub) ∧
        finish.callStack = right.callStack ∧
        ActivationContinuationAt machine root right.callStack
          (analysis.localAnalysis.regions.index.parentAt right.pc) finish at hrightPackage
  obtain ⟨leftLength, leftFinish, hleftPositive, hleftBound, hleftSegment,
      hleftRelease, hleftReach, hleftEndpointPrivate, hleftStack,
      hleftContinuation⟩ := hleftPackage
  obtain ⟨rightLength, rightFinish, hrightPositive, hrightBound, hrightSegment,
      hrightRelease, hrightReach, hrightEndpointPrivate, hrightStack,
      hrightContinuation⟩ := hrightPackage
  have hrightContinuation' : ActivationContinuationAt machine root right.callStack
      (analysis.localAnalysis.regions.index.parentAt left.pc) rightFinish := by
    simpa [hpc] using hrightContinuation
  have hleftActiveEnd : ActiveState machine root leftFinish := by
    have hactive := hleftExecution.reached_active hleftBound
    rw [hleftSegment.finish_eq] at hactive
    exact hactive
  have hrightActiveEnd : ActiveState machine root rightFinish := by
    have hactive := hrightExecution.reached_active hrightBound
    rw [hrightSegment.finish_eq] at hactive
    exact hactive
  have hleftStreams : leftFinish.externalInputs = left.externalInputs := by
    have hstreams := runPrefix_preserves_external_inputs machine leftLength left
    rw [hleftSegment.finish_eq] at hstreams
    exact hstreams
  have hrightStreams : rightFinish.externalInputs = right.externalInputs := by
    have hstreams := runPrefix_preserves_external_inputs machine rightLength right
    rw [hrightSegment.finish_eq] at hstreams
    exact hstreams
  have houtcome : PairedContinuationOutcome machine root
      (analysis.localAnalysis.regions.index.parentAt left.pc)
      left.callStack right.callStack leftFinish rightFinish := by
    exact paired_activation_continuation_outcome hlow rfl rfl hleftStack hrightStack
      hleftSegment.endProjection hrightSegment.endProjection hleftStreams hrightStreams
      hleftReach hrightReach hleftActiveEnd hrightActiveEnd hleftContinuation
      hrightContinuation'
  exact ⟨leftLength, rightLength, leftFinish, rightFinish,
    analysis.localAnalysis.regions.index.parentAt left.pc,
    hleftPositive, hrightPositive, hleftBound, hrightBound, hleftSegment,
    hrightSegment, hleftRelease, hrightRelease, hleftEndpointPrivate, (by
      intro hparent
      apply hrightEndpointPrivate
      simpa [hpc] using hparent), houtcome⟩

/-- The ordinary-current branch of the paired controller theorem is immediately a decreasing
    `PublicExecutionProgress` case.  Filtered release suffix equality is cancelled across the two
    independently sized private prefixes; complete release equality is converted to the filtered
    premise by the production dispatcher before calling this lemma. -/
theorem publicExecutionProgress_of_private_controller_current
    {machine : SemanticProgram} {root : UInt32}
    {leftSteps rightSteps leftLength rightLength parent : Nat}
    {left right leftFinish rightFinish : State}
    {leftResult rightResult : StepResult}
    (hleftPositive : 0 < leftLength) (hrightPositive : 0 < rightLength)
    (hleftBound : leftLength < leftSteps) (hrightBound : rightLength < rightSteps)
    (hleftSegment : PublicSilentSegment machine leftLength left leftFinish)
    (hrightSegment : PublicSilentSegment machine rightLength right rightFinish)
    (hleftRelease : PublicReleaseSilentSegment machine leftLength left)
    (hrightRelease : PublicReleaseSilentSegment machine rightLength right)
    (hcurrent : MatchingCurrentContinuation machine root parent leftFinish rightFinish)
    (hleftExecution : SuccessfulExecution machine root leftSteps left leftResult)
    (hrightExecution : SuccessfulExecution machine root rightSteps right rightResult)
    (hrelease : publicReleaseTrace machine leftResult.events =
      publicReleaseTrace machine rightResult.events) :
    PublicExecutionProgress machine root leftSteps left rightSteps right := by
  have hactualRelease : publicReleaseTrace machine (runPrefix machine leftSteps left).events =
      publicReleaseTrace machine (runPrefix machine rightSteps right).events := by
    rw [hleftExecution.run, hrightExecution.run]
    exact hrelease
  have hleftSum : leftLength + (leftSteps - leftLength) = leftSteps :=
    Nat.add_sub_of_le (Nat.le_of_lt hleftBound)
  have hrightSum : rightLength + (rightSteps - rightLength) = rightSteps :=
    Nat.add_sub_of_le (Nat.le_of_lt hrightBound)
  have hsplitRelease : publicReleaseTrace machine
        (runPrefix machine (leftLength + (leftSteps - leftLength)) left).events =
      publicReleaseTrace machine
        (runPrefix machine (rightLength + (rightSteps - rightLength)) right).events := by
    simpa only [hleftSum, hrightSum] using hactualRelease
  have htailRelease := public_release_suffix_eq_after_private_regions
    hleftSegment hrightSegment hleftRelease hrightRelease hsplitRelease
  exact publicExecutionProgress_of_private_segments hleftPositive hrightPositive
    hleftBound hrightBound hleftSegment hrightSegment
    ⟨hcurrent.leftReachable, hcurrent.leftActive⟩
    ⟨hcurrent.rightReachable, hcurrent.rightActive⟩ hcurrent.low
    hleftExecution hrightExecution htailRelease

/-- Eliminate the paired controller package without concealing the synthetic case.  Ordinary
    continuations immediately produce decreasing progress; synthetic function returns remain an
    explicit obligation to execute the genuine terminal/internal-return instructions. -/
theorem publicExecutionProgress_or_synthetic_of_private_controller_segments
    {machine : SemanticProgram} {root : UInt32}
    {leftSteps rightSteps : Nat} {left right : State}
    {leftResult rightResult : StepResult}
    {frontiers : ThresholdFrontiers}
    (hsegments : PairedPrivateControllerSegments machine frontiers root
      leftSteps rightSteps left right)
    (hleftExecution : SuccessfulExecution machine root leftSteps left leftResult)
    (hrightExecution : SuccessfulExecution machine root rightSteps right rightResult)
    (hrelease : publicReleaseTrace machine leftResult.events =
      publicReleaseTrace machine rightResult.events) :
    PublicExecutionProgress machine root leftSteps left rightSteps right ∨
      SyntheticPrivateControllerSegments machine frontiers root
        leftSteps rightSteps left right := by
  obtain ⟨leftLength, rightLength, leftFinish, rightFinish, parent,
    hleftPositive, hrightPositive, hleftBound, hrightBound,
    hleftSegment, hrightSegment, hleftRelease, hrightRelease,
    hleftEndpointPrivate, hrightEndpointPrivate, houtcome⟩ := hsegments
  cases houtcome with
  | current hcurrent =>
      exact Or.inl (publicExecutionProgress_of_private_controller_current
        hleftPositive hrightPositive hleftBound hrightBound hleftSegment hrightSegment
        hleftRelease hrightRelease hcurrent hleftExecution hrightExecution hrelease)
  | synthetic hsynthetic =>
      exact Or.inr ⟨leftLength, rightLength, leftFinish, rightFinish, parent,
        hleftPositive, hrightPositive, hleftBound, hrightBound,
        hleftSegment, hrightSegment, hleftRelease, hrightRelease,
        hleftEndpointPrivate hsynthetic.leftParent,
        hrightEndpointPrivate hsynthetic.rightParent, hsynthetic⟩

end LambdaSigil.Combined.V9.PublicControllerSegmentSecurity
