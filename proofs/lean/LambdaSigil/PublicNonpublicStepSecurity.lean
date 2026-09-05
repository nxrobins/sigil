import LambdaSigil.PublicExecutionSecurity

/-!
# Non-Public one-step packaging

This leaf module packages the constructor-local V9 facts into the exact one-step objects consumed
by independent-length Public execution composition.  It changes neither the executable checker
nor its acceptance language.
-/

namespace LambdaSigil.Combined.V9.PublicNonpublicStepSecurity

open Semantic OccurrenceDataflowInvocation OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity
open PublicLocalSecurity PublicMatchingSecurity PublicPrivateSegmentSecurity
open PublicExecutionSecurity

/-- A reachable active accepted instruction at a non-Public occurrence is a concrete one-step
    Public-silent segment whenever it is not a call, closure, or return/output.  State-write sink
    isolation is derived from the production judgment over the exact runtime immediate. -/
theorem verified_nonpublic_noncall_step_publicSilentSegment
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {state : State} {instruction : Instruction}
    (_hreachable : ReachableFromRoot (rawSemanticProgram program analysis) root state)
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (hnotCall : instruction.op ≠ .call)
    (hnotClosure : instruction.op ≠ .closure)
    (hnotOutput : instruction.op ≠ .output) :
    PublicSilentSegment (rawSemanticProgram program analysis) 1 state
      (step (rawSemanticProgram program analysis) state).state := by
  let machine := rawSemanticProgram program analysis
  have hjudgment := v9_occurrence_verifier_sound hverified
  have hstate : instruction.op = .stateWrite →
      let offset := (immediateOperands machine instruction).head?.getD 0
      0 ≤ offset → stateLabelAt machine (UInt32.ofNat offset.toNat) ≠ .pub := by
    intro hwrite
    exact verified_private_stateWrite_runtime_sink hjudgment hanalysis hlookup
      hwrite hnonpublic
  have hlocal := verified_nonoutput_noncall_nonpublic_step_preserves_prefix
    hjudgment hanalysis hactive hlookup hnonpublic hnotCall hnotClosure hnotOutput
    ([] : List CallFrame) state.callStack (by simp) (by simpa [machine] using hstate)
  have hprojection : publicProjection machine (step machine state).state =
      publicProjection machine state := by
    simpa [machine] using hlocal.2.1
  have hboundary : publicBoundaryTrace (step machine state).events = [] := by
    simpa [machine] using hlocal.2.2
  exact publicSilentSegment_one hboundary hprojection

private theorem nonoutput_noncall_step_pc
    {machine : SemanticProgram} {state : State} {instruction : Instruction}
    (hactive : state.halted = false ∧ state.trapped = false)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hnotCall : instruction.op ≠ .call)
    (hnotClosure : instruction.op ≠ .closure)
    (hnotOutput : instruction.op ≠ .output) :
    (step machine state).state.pc =
      nextPc machine state instruction (operandValue machine state instruction) := by
  generalize hop : instruction.op = operation at *
  cases operation
  case call => exact False.elim (hnotCall rfl)
  case closure => exact False.elim (hnotClosure rfl)
  case output => exact False.elim (hnotOutput rfl)
  case actorBoundary =>
    by_cases hdestination : instruction.destination = 0 <;>
      simp [step, hactive.1, hactive.2, hlookup, hop, hdestination, nextPc]
  all_goals simp [step, hactive.1, hactive.2, hlookup, hop, ordinaryStep, nextPc]

private theorem nonoutput_noncall_nontrap_step_halted
    {machine : SemanticProgram} {left right : State} {instruction : Instruction}
    (hleftActive : left.halted = false ∧ left.trapped = false)
    (hrightActive : right.halted = false ∧ right.trapped = false)
    (hleftLookup : machine.instructions[left.pc]? = some instruction)
    (hrightLookup : machine.instructions[right.pc]? = some instruction)
    (hnotCall : instruction.op ≠ .call)
    (hnotClosure : instruction.op ≠ .closure)
    (hnotOutput : instruction.op ≠ .output) :
    (step machine left).state.halted = (step machine right).state.halted := by
  generalize hop : instruction.op = operation at *
  cases operation
  case call => exact False.elim (hnotCall rfl)
  case closure => exact False.elim (hnotClosure rfl)
  case output => exact False.elim (hnotOutput rfl)
  case actorBoundary =>
    by_cases hdestination : instruction.destination = 0 <;>
      simp [step, hleftActive.1, hleftActive.2, hrightActive.1,
        hrightActive.2, hleftLookup, hrightLookup, hop, hdestination]
  all_goals simp [step, hleftActive.1, hleftActive.2, hrightActive.1,
    hrightActive.2, hleftLookup, hrightLookup, hop, ordinaryStep]

private theorem nonoutput_noncall_nontrap_step_trapped
    {machine : SemanticProgram} {left right : State} {instruction : Instruction}
    (hleftActive : left.halted = false ∧ left.trapped = false)
    (hrightActive : right.halted = false ∧ right.trapped = false)
    (hleftLookup : machine.instructions[left.pc]? = some instruction)
    (hrightLookup : machine.instructions[right.pc]? = some instruction)
    (hnotCall : instruction.op ≠ .call)
    (hnotClosure : instruction.op ≠ .closure)
    (hnotOutput : instruction.op ≠ .output)
    (hnotTrap : instruction.op ≠ .trap) :
    (step machine left).state.trapped = (step machine right).state.trapped := by
  generalize hop : instruction.op = operation at *
  cases operation
  case call => exact False.elim (hnotCall rfl)
  case closure => exact False.elim (hnotClosure rfl)
  case output => exact False.elim (hnotOutput rfl)
  case trap => exact False.elim (hnotTrap rfl)
  case actorBoundary =>
    by_cases hdestination : instruction.destination = 0 <;>
      simp [step, hleftActive.1, hleftActive.2, hrightActive.1,
        hrightActive.2, hleftLookup, hrightLookup, hop, hdestination]
  all_goals simp [step, hleftActive.1, hleftActive.2, hrightActive.1,
    hrightActive.2, hleftLookup, hrightLookup, hop, ordinaryStep]

private theorem verified_nonpublic_noncall_same_control_step_of_trap_agreement
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {left right : State} {instruction : Instruction}
    (hleftReachable : ReachableFromRoot (rawSemanticProgram program analysis) root left)
    (hrightReachable : ReachableFromRoot (rawSemanticProgram program analysis) root right)
    (hleftActive : ActiveState (rawSemanticProgram program analysis) root left)
    (hrightActive : ActiveState (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (hnotCall : instruction.op ≠ .call)
    (hnotClosure : instruction.op ≠ .closure)
    (hnotOutput : instruction.op ≠ .output)
    (hnextPc : nextPc (rawSemanticProgram program analysis) left instruction
        (operandValue (rawSemanticProgram program analysis) left instruction) =
      nextPc (rawSemanticProgram program analysis) right instruction
        (operandValue (rawSemanticProgram program analysis) right instruction))
    (htrapped :
      (step (rawSemanticProgram program analysis) left).state.trapped =
        (step (rawSemanticProgram program analysis) right).state.trapped) :
    PublicLowEquivalent (rawSemanticProgram program analysis)
      (step (rawSemanticProgram program analysis) left).state
      (step (rawSemanticProgram program analysis) right).state := by
  let machine := rawSemanticProgram program analysis
  have hjudgment := v9_occurrence_verifier_sound hverified
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    simpa [machine] using hlookup
  have hleftSegment := verified_nonpublic_noncall_step_publicSilentSegment hverified hanalysis
    hleftReachable hleftActive hlookup hnonpublic hnotCall hnotClosure hnotOutput
  have hrightSegment := verified_nonpublic_noncall_step_publicSilentSegment hverified hanalysis
    hrightReachable hrightActive (by simpa [machine] using hrightLookup) hnonpublic
    hnotCall hnotClosure hnotOutput
  have hstartProjection : publicProjection machine left = publicProjection machine right :=
    (publicLowEquivalent_iff_projection machine left right).mp hlow |>.2.2.2.2.2.2.2
  have hleftProjection : publicProjection machine (step machine left).state =
      publicProjection machine left := by
    simpa [machine] using hleftSegment.endProjection
  have hrightProjection : publicProjection machine (step machine right).state =
      publicProjection machine right := by
    simpa [machine] using hrightSegment.endProjection
  have hprojection : publicProjection machine (step machine left).state =
      publicProjection machine (step machine right).state :=
    hleftProjection.trans (hstartProjection.trans hrightProjection.symm)
  have hleftLive : left.halted = false ∧ left.trapped = false :=
    ⟨hleftActive.notHalted, hleftActive.notTrapped⟩
  have hrightLive : right.halted = false ∧ right.trapped = false :=
    ⟨hrightActive.notHalted, hrightActive.notTrapped⟩
  have hleftPc := nonoutput_noncall_step_pc hleftLive (by simpa [machine] using hlookup)
    hnotCall hnotClosure hnotOutput
  have hrightPc := nonoutput_noncall_step_pc hrightLive hrightLookup
    hnotCall hnotClosure hnotOutput
  have hpc : (step machine left).state.pc = (step machine right).state.pc := by
    rw [hleftPc, hrightPc]
    simpa [machine] using hnextPc
  have hhalted := nonoutput_noncall_nontrap_step_halted hleftLive hrightLive
    (by simpa [machine] using hlookup) hrightLookup hnotCall hnotClosure hnotOutput
  have hleftStack := nonoutput_noncall_step_preserves_stack machine left instruction
    (by simpa [machine] using hlookup) hleftLive.1 hleftLive.2 hnotCall hnotClosure hnotOutput
  have hrightStack := nonoutput_noncall_step_preserves_stack machine right instruction
    hrightLookup hrightLive.1 hrightLive.2 hnotCall hnotClosure hnotOutput
  have hstack : CallStackPublicEquivalent machine (step machine left).state.callStack
      (step machine right).state.callStack := by
    rw [hleftStack, hrightStack]
    exact hlow.2.2.2.1
  have hevents : publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events := by
    rw [nonpublic_step_has_no_public_boundary_observation machine left instruction
        (by simpa [machine] using hlookup) hnonpublic,
      nonpublic_step_has_no_public_boundary_observation machine right instruction
        hrightLookup hnonpublic]
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  exact (matching_step_of_projection hstatic hleftActive.wellFormed hrightActive.wellFormed
    hlow hprojection hpc hhalted (by simpa [machine] using htrapped) hstack hevents).1

/-- Two Public-low states taking the same raw successor remain Public-low across every accepted
    non-Public, non-call/non-return constructor except `trap`.  The exclusion is load-bearing:
    equal `nextPc` does not determine the secret-dependent trap predicate. -/
theorem verified_nonpublic_noncall_same_control_step
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {left right : State} {instruction : Instruction}
    (hleftReachable : ReachableFromRoot (rawSemanticProgram program analysis) root left)
    (hrightReachable : ReachableFromRoot (rawSemanticProgram program analysis) root right)
    (hleftActive : ActiveState (rawSemanticProgram program analysis) root left)
    (hrightActive : ActiveState (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (hnotCall : instruction.op ≠ .call)
    (hnotClosure : instruction.op ≠ .closure)
    (hnotOutput : instruction.op ≠ .output)
    (hnotTrap : instruction.op ≠ .trap)
    (hnextPc : nextPc (rawSemanticProgram program analysis) left instruction
        (operandValue (rawSemanticProgram program analysis) left instruction) =
      nextPc (rawSemanticProgram program analysis) right instruction
        (operandValue (rawSemanticProgram program analysis) right instruction)) :
    PublicLowEquivalent (rawSemanticProgram program analysis)
      (step (rawSemanticProgram program analysis) left).state
      (step (rawSemanticProgram program analysis) right).state := by
  let machine := rawSemanticProgram program analysis
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    simpa [machine] using hlookup
  have hleftLive : left.halted = false ∧ left.trapped = false :=
    ⟨hleftActive.notHalted, hleftActive.notTrapped⟩
  have hrightLive : right.halted = false ∧ right.trapped = false :=
    ⟨hrightActive.notHalted, hrightActive.notTrapped⟩
  have htrapped := nonoutput_noncall_nontrap_step_trapped hleftLive hrightLive
    (by simpa [machine] using hlookup) hrightLookup hnotCall hnotClosure hnotOutput hnotTrap
  exact verified_nonpublic_noncall_same_control_step_of_trap_agreement hverified hanalysis
    hleftReachable hrightReachable hleftActive hrightActive hlow hlookup hnonpublic
    hnotCall hnotClosure hnotOutput hnextPc (by simpa [machine] using htrapped)

/-- The raw `.trap` constructor joins the same package once both actual successors are known not
    to trap, as they are on successful execution tails.  Both one-step silent segments are
    retained explicitly for independent-length alignment. -/
theorem verified_nonpublic_trap_same_control_nontrapping_step
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {left right : State} {instruction : Instruction}
    (hleftReachable : ReachableFromRoot (rawSemanticProgram program analysis) root left)
    (hrightReachable : ReachableFromRoot (rawSemanticProgram program analysis) root right)
    (hleftActive : ActiveState (rawSemanticProgram program analysis) root left)
    (hrightActive : ActiveState (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (htrap : instruction.op = .trap)
    (hnextPc : nextPc (rawSemanticProgram program analysis) left instruction
        (operandValue (rawSemanticProgram program analysis) left instruction) =
      nextPc (rawSemanticProgram program analysis) right instruction
        (operandValue (rawSemanticProgram program analysis) right instruction))
    (hleftNext : (step (rawSemanticProgram program analysis) left).state.trapped = false)
    (hrightNext : (step (rawSemanticProgram program analysis) right).state.trapped = false) :
    PublicSilentSegment (rawSemanticProgram program analysis) 1 left
        (step (rawSemanticProgram program analysis) left).state ∧
      PublicSilentSegment (rawSemanticProgram program analysis) 1 right
        (step (rawSemanticProgram program analysis) right).state ∧
      PublicLowEquivalent (rawSemanticProgram program analysis)
        (step (rawSemanticProgram program analysis) left).state
        (step (rawSemanticProgram program analysis) right).state := by
  have hnotCall : instruction.op ≠ .call := by simp [htrap]
  have hnotClosure : instruction.op ≠ .closure := by simp [htrap]
  have hnotOutput : instruction.op ≠ .output := by simp [htrap]
  have hleftSegment := verified_nonpublic_noncall_step_publicSilentSegment hverified hanalysis
    hleftReachable hleftActive hlookup hnonpublic hnotCall hnotClosure hnotOutput
  have hrightLookup : (rawSemanticProgram program analysis).instructions[right.pc]? =
      some instruction := by
    rw [← hlow.1]
    exact hlookup
  have hrightSegment := verified_nonpublic_noncall_step_publicSilentSegment hverified hanalysis
    hrightReachable hrightActive hrightLookup hnonpublic hnotCall hnotClosure hnotOutput
  have htrapped :
      (step (rawSemanticProgram program analysis) left).state.trapped =
        (step (rawSemanticProgram program analysis) right).state.trapped :=
    hleftNext.trans hrightNext.symm
  refine ⟨hleftSegment, hrightSegment, ?_⟩
  exact verified_nonpublic_noncall_same_control_step_of_trap_agreement hverified hanalysis
    hleftReachable hrightReachable hleftActive hrightActive hlow hlookup hnonpublic
    hnotCall hnotClosure hnotOutput hnextPc htrapped

/-! ## Private output/return classification -/

/-- A non-Public internal output is a paired return, rather than unary stuttering: the returned
    value may legitimately update a Public destination in the caller.  The actual frame witnesses
    are retained so execution composition cannot confuse it with top-level completion. -/
structure MatchingPrivateInternalReturn (machine : SemanticProgram) (left right : State) : Prop
    where
  leftStackNonempty : left.callStack ≠ []
  rightStackNonempty : right.callStack ≠ []
  successorLow : PublicLowEquivalent machine (step machine left).state
    (step machine right).state
  boundaryMatch : publicBoundaryTrace (step machine left).events =
    publicBoundaryTrace (step machine right).events

/-- A non-Public top-level output is a successful private terminal on both sides.  Each real step
    is independently Public-silent and the paired terminal states retain the complete Public-low
    relation; no private output payload is promoted into the Public boundary trace. -/
structure CompletePrivateOutputTerminal (machine : SemanticProgram) (left right : State) : Prop
    where
  leftStack : left.callStack = []
  rightStack : right.callStack = []
  leftSilent : PublicSilentSegment machine 1 left (step machine left).state
  rightSilent : PublicSilentSegment machine 1 right (step machine right).state
  successorLow : PublicLowEquivalent machine (step machine left).state
    (step machine right).state
  leftHalted : (step machine left).state.halted = true
  rightHalted : (step machine right).state.halted = true
  leftNotTrapped : (step machine left).state.trapped = false
  rightNotTrapped : (step machine right).state.trapped = false
  leftEmptyStack : (step machine left).state.callStack = []
  rightEmptyStack : (step machine right).state.callStack = []

/-- Constructor-complete paired outcome for a non-Public raw `.output`. -/
inductive VerifiedNonpublicOutputPairOutcome (machine : SemanticProgram) (left right : State) :
    Prop where
  | internalReturn (evidence : MatchingPrivateInternalReturn machine left right)
  | completeTerminal (evidence : CompletePrivateOutputTerminal machine left right)

/-- Exact unary terminal algebra for a non-Public top-level output. -/
theorem nonpublic_topLevel_output_publicSilentSegment
    {machine : SemanticProgram} {state : State} {instruction : Instruction}
    (hlive : state.halted = false ∧ state.trapped = false)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (houtput : instruction.op = .output)
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (hstack : state.callStack = []) :
    PublicSilentSegment machine 1 state (step machine state).state ∧
      (step machine state).state.halted = true ∧
      (step machine state).state.trapped = false ∧
      (step machine state).state.callStack = [] := by
  have hboundary := nonpublic_step_has_no_public_boundary_observation
    machine state instruction hlookup hnonpublic
  have hprojection : publicProjection machine (step machine state).state =
      publicProjection machine state := by
    simp [step, hlive.1, hlive.2, hlookup, houtput, hstack, publicProjection]
  refine ⟨publicSilentSegment_one hboundary hprojection, ?_, ?_, ?_⟩
  · simp [step, hlive.1, hlive.2, hlookup, houtput, hstack]
  · simp [step, hlive.1, hlive.2, hlookup, houtput, hstack]
  · simp [step, hlive.1, hlive.2, hlookup, houtput, hstack]

/-- Production v9 classification for a private output pair.  A nonempty verified frame produces
    a genuine matching internal return (including any Public caller destination).  Empty stacks
    produce two complete private terminals.  Nontrapping successor premises are explicit because
    the internal return-label guard is checked by the raw reducer, and successful tails supply
    exactly these facts. -/
theorem verified_nonpublic_output_pair_outcome
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {left right : State} {instruction : Instruction}
    (_hleftReachable : ReachableFromRoot (rawSemanticProgram program analysis) root left)
    (_hrightReachable : ReachableFromRoot (rawSemanticProgram program analysis) root right)
    (hleftActive : ActiveState (rawSemanticProgram program analysis) root left)
    (hrightActive : ActiveState (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (houtput : instruction.op = .output)
    (hleftNext : (step (rawSemanticProgram program analysis) left).state.trapped = false)
    (hrightNext : (step (rawSemanticProgram program analysis) right).state.trapped = false) :
    VerifiedNonpublicOutputPairOutcome (rawSemanticProgram program analysis) left right := by
  let machine := rawSemanticProgram program analysis
  have hjudgment := v9_occurrence_verifier_sound hverified
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hleftLive : left.halted = false ∧ left.trapped = false :=
    ⟨hleftActive.notHalted, hleftActive.notTrapped⟩
  have hrightLive : right.halted = false ∧ right.trapped = false :=
    ⟨hrightActive.notHalted, hrightActive.notTrapped⟩
  have hleftLookup : machine.instructions[left.pc]? = some instruction := by
    simpa [machine] using hlookup
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hleftLookup
  cases hleftStack : left.callStack with
  | nil =>
      have hrightStack : right.callStack = [] := by
        have hstack := hlow.2.2.2.1
        rw [hleftStack] at hstack
        cases hright : right.callStack with
        | nil => rfl
        | cons frame rest => simp [CallStackPublicEquivalent, hright] at hstack
      have hleftTerminal := nonpublic_topLevel_output_publicSilentSegment hleftLive
        hleftLookup houtput hnonpublic hleftStack
      have hrightTerminal := nonpublic_topLevel_output_publicSilentSegment hrightLive
        hrightLookup houtput hnonpublic hrightStack
      have hstartProjection : publicProjection machine left = publicProjection machine right :=
        publicProjection_eq_of_low hlow
      have hprojection : publicProjection machine (step machine left).state =
          publicProjection machine (step machine right).state :=
        hleftTerminal.1.endProjection.trans
          (hstartProjection.trans hrightTerminal.1.endProjection.symm)
      have hpc : (step machine left).state.pc = (step machine right).state.pc := by
        simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
          hleftLookup, hrightLookup, houtput, hleftStack, hrightStack] using hlow.1
      have hstack : CallStackPublicEquivalent machine
          (step machine left).state.callStack (step machine right).state.callStack := by
        simp [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
          hleftLookup, hrightLookup, houtput, hleftStack, hrightStack,
          CallStackPublicEquivalent]
      have hevents : publicBoundaryTrace (step machine left).events =
          publicBoundaryTrace (step machine right).events := by
        rw [nonpublic_step_has_no_public_boundary_observation machine left instruction
            hleftLookup hnonpublic,
          nonpublic_step_has_no_public_boundary_observation machine right instruction
            hrightLookup hnonpublic]
      have hmatching := matching_step_of_projection hstatic hleftActive.wellFormed
        hrightActive.wellFormed hlow hprojection hpc
        (hleftTerminal.2.1.trans hrightTerminal.2.1.symm)
        (hleftTerminal.2.2.1.trans hrightTerminal.2.2.1.symm) hstack hevents
      exact .completeTerminal {
        leftStack := hleftStack
        rightStack := hrightStack
        leftSilent := hleftTerminal.1
        rightSilent := hrightTerminal.1
        successorLow := hmatching.1
        leftHalted := hleftTerminal.2.1
        rightHalted := hrightTerminal.2.1
        leftNotTrapped := hleftTerminal.2.2.1
        rightNotTrapped := hrightTerminal.2.2.1
        leftEmptyStack := hleftTerminal.2.2.2
        rightEmptyStack := hrightTerminal.2.2.2 }
  | cons leftFrame leftRest =>
      cases hrightStack : right.callStack with
      | nil =>
          have hstack := hlow.2.2.2.1
          simp [CallStackPublicEquivalent, hleftStack, hrightStack] at hstack
      | cons rightFrame rightRest =>
          have hleftFlow := nontrapping_internal_output_flow
            hleftLookup houtput hleftLive hleftStack
            (by simpa [machine] using hleftNext)
          have hrightFlow := nontrapping_internal_output_flow hrightLookup houtput hrightLive
            hrightStack (by simpa [machine] using hrightNext)
          have hmatching := matching_internal_return_of_wellFormed hstatic
            hleftActive.wellFormed hrightActive.wellFormed hlow
            hleftLookup houtput hleftLive hrightLive hleftStack
            hrightStack hleftFlow hrightFlow
          exact .internalReturn {
            leftStackNonempty := by simp [hleftStack]
            rightStackNonempty := by simp [hrightStack]
            successorLow := hmatching.1
            boundaryMatch := hmatching.2 }

end LambdaSigil.Combined.V9.PublicNonpublicStepSecurity
