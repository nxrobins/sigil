import LambdaSigil.PublicControllerSegmentSecurity
import LambdaSigil.PublicMatchedProgressSecurity
import LambdaSigil.PublicPrivateInvocationSecurity

/-!
# Synthetic private-controller return closure

This leaf executes the two genuine decoded return instructions left by a private controller
segment.  The endpoints need not share a program counter or an instruction: the verifier-owned
occurrence facts establish that each real return remains outside the Public boundary, while
coherent corresponding frames restore the relational Public projection.
-/

namespace LambdaSigil.Combined.V9.PublicSyntheticReturnSecurity

open Semantic DecodedOccurrence OccurrenceRegions OccurrenceTransfer
open OccurrenceDataflowInvocation OccurrenceKernel
open OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity Semantic.PublicRegionConvergence
open Semantic.PublicReleaseSynchronization
open PublicLocalSecurity PublicTraceSecurity PublicMatchingSecurity PublicPrivateSegmentSecurity
open PublicPrivateInvocationSecurity
open PublicExecutionSecurity PublicContinuationSecurity PublicControllerSegmentSecurity
open PublicNonpublicStepSecurity PublicMatchedProgressSecurity

private theorem label_flow_trans {first middle last : Label}
    (hfirst : first.flowsTo middle = true) (hlast : middle.flowsTo last = true) :
    first.flowsTo last = true := by
  cases first <;> cases middle <;> cases last <;>
    simp_all [Label.flowsTo, Label.rank]

private theorem local_flows_effective
    (analysis : OccurrenceDataflowInvocation.Analysis) (instruction : Instruction)
    (pc : Nat) :
    (localOccurrenceAt analysis.localAnalysis.frontiers pc).flowsTo
      (effectiveOccurrence analysis instruction pc) = true := by
  unfold effectiveOccurrence
  cases labelAt analysis.labels instruction.functionId <;>
    cases localOccurrenceAt analysis.localAnalysis.frontiers pc <;> decide

private theorem lub_right_flows_of_lub_flow {left right sink : Label}
    (hflow : (left.lub right).flowsTo sink = true) : right.flowsTo sink = true := by
  cases left <;> cases right <;> cases sink <;>
    simp_all [Label.flowsTo, Label.rank, Label.lub]

private theorem nonpublic_of_flows_from_nonpublic {source sink : Label}
    (hsource : source ≠ .pub) (hflow : source.flowsTo sink = true) : sink ≠ .pub := by
  intro hsink
  subst sink
  cases source <;> simp_all [Label.flowsTo, Label.rank]

private theorem analyzed_functionById_indexed_local
    {program : V9.Program} {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {id : UInt32} {callee : Function}
    (hcallee : functionById? (rawSemanticProgram program analysis) id = some callee) :
    (rawSemanticProgram program analysis).functions[id.toNat - 1]? = some callee := by
  let machine := rawSemanticProgram program analysis
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  have hrootChecks :=
    (V9.OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).2.2.2.1
  simp only [V9.OccurrenceDataflowInvocation.rootEntryChecks,
    Bool.and_eq_true] at hrootChecks
  have hrootLayout := hrootChecks.1.1
  simp only [V9.OccurrenceDataflowInvocation.rootLayoutChecks,
    Bool.and_eq_true] at hrootLayout
  have hfunctionLayout : OccurrenceInvocation.functionLayoutB base = true := by
    simpa [base] using hrootLayout.1.1.1
  have hmemberRaw : callee ∈ machine.functions := Array.mem_of_find?_eq_some hcallee
  have hmember : callee ∈ base.functions := by
    simpa [machine, rawSemanticProgram, base] using hmemberRaw
  obtain ⟨position, hposition, heq⟩ := Array.mem_iff_getElem.mp hmember
  simp only [OccurrenceInvocation.functionLayoutB, Bool.and_eq_true,
    List.all_eq_true] at hfunctionLayout
  have hrow := hfunctionLayout.2 position (List.mem_range.mpr hposition)
  simp only [Array.getElem?_eq_getElem hposition, heq, beq_iff_eq] at hrow
  have hid := Array.find?_some
    (p := fun function : Function => function.id == id)
    (xs := machine.functions) (a := callee) hcallee
  have hid' : callee.id = id := beq_iff_eq.mp hid
  have hpositionEq : id.toNat - 1 = position := by
    rw [← hid']
    omega
  rw [hpositionEq]
  simpa [machine, rawSemanticProgram, base] using
    (Array.getElem?_eq_some_iff.mpr ⟨hposition, heq⟩)

/-- At a genuine internal output, the same local occurrence fact reaches the checked function
    return sink.  Coherent frame provenance identifies that sink with the top frame's return
    label, and state well-formedness then prevents the frame from writing into Public storage.
-/
theorem verified_local_nonpublic_output_top_frame_isolated
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {state : State} {instruction : Instruction}
    {frame : CallFrame} {rest : List CallFrame}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? = some instruction)
    (houtput : instruction.op = .output)
    (hnonpublic : localOccurrenceAt analysis.localAnalysis.frontiers state.pc ≠ .pub)
    (hstack : state.callStack = frame :: rest) :
    frame.destination = 0 ∨
      labelAt (rawSemanticProgram program analysis).valueLabels frame.destination ≠ .pub := by
  let machine := rawSemanticProgram program analysis
  obtain ⟨source, hsourceLookup, _, ⟨sink, hsink, hreturnFlow⟩, _⟩ :=
    returned_output_root_return_safe hjudgment hanalysis hlookup houtput
  obtain ⟨decoded, hdecodedLookup, hraised⟩ := rawInstructionSource_of_lookup hlookup
  have hsourceEq : source = decoded := Option.some.inj (hsourceLookup.symm.trans hdecodedLookup)
  subst decoded
  have hsourceFunction : source.functionId = instruction.functionId := by
    rw [hraised]
    simp [raiseInstructionResultLabel, raiseInstructionOccurrence]
  have heffectiveToSink :
      (effectiveOccurrence analysis source state.pc).flowsTo sink = true :=
    lub_right_flows_of_lub_flow hreturnFlow
  have hlocalToSink :
      (localOccurrenceAt analysis.localAnalysis.frontiers state.pc).flowsTo sink = true :=
    label_flow_trans (local_flows_effective analysis source state.pc) heffectiveToSink
  have hsinkNonpublic : sink ≠ .pub :=
    nonpublic_of_flows_from_nonpublic hnonpublic hlocalToSink
  obtain ⟨current, hcurrentLookup, hcurrentFunction⟩ := hactive.currentInstruction
  have hcurrentEq : current = instruction := by
    rw [hlookup] at hcurrentLookup
    exact Option.some.inj hcurrentLookup.symm
  subst current
  have hsourceFrame : source.functionId = frame.calleeId := by
    have hinstructionFrame : instruction.functionId = frame.calleeId := by
      rw [hstack] at hcurrentFunction
      simpa [activeFunctionId] using hcurrentFunction
    exact hsourceFunction.trans hinstructionFrame
  have hchain := hactive.frameChain
  rw [hstack] at hchain
  obtain ⟨_, callee, _, _, _, hcallee, _, _, _, _, _, _, _, _, hframeReturn, _⟩ := hchain.1
  have hcalleeIndexed := analyzed_functionById_indexed_local hanalysis hcallee
  have hcalleeId : callee.id = frame.calleeId := by
    have hid := Array.find?_some
      (p := fun function : Function => function.id == frame.calleeId)
      (xs := machine.functions) (a := callee)
      (by simpa [functionById?, machine] using hcallee)
    exact beq_iff_eq.mp hid
  have hcalleeReturn : callee.returnLabel = sink := by
    unfold functionReturnLabel? at hsink
    rw [hsourceFrame, hcalleeIndexed] at hsink
    simpa [hcalleeId] using hsink
  have hframeReturnSink : frame.returnLabel = sink := hframeReturn.trans hcalleeReturn
  have hframeReturnNonpublic : frame.returnLabel ≠ .pub := by
    simpa [hframeReturnSink] using hsinkNonpublic
  by_cases hdestination : frame.destination = 0
  · exact Or.inl hdestination
  · right
    have hframeWellFormed := hactive.wellFormed.2.2.2.2 frame (by
      rw [hstack]
      simp)
    have hreturnToDestination : frame.returnLabel.flowsTo
        (labelAt machine.valueLabels frame.destination) = true := by
      have hchecked := hframeWellFormed.2.2.2.1
      simpa [machine, rawSemanticProgram_valueLabels, hdestination] using hchecked
    exact nonpublic_of_flows_from_nonpublic hframeReturnNonpublic hreturnToDestination

/-- The synthetic continuation admits `.halt` only at an empty activation spine.  Production
    acceptance makes every halt occurrence Public, so a verifier-derived non-Public endpoint
    rules that alternative out. -/
theorem verified_local_nonpublic_synthetic_return_is_output
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {pc : Nat} {spine : List CallFrame} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hnonpublic : localOccurrenceAt analysis.localAnalysis.frontiers pc ≠ .pub)
    (hreturn : instruction.op = .output ∨ (spine = [] ∧ instruction.op = .halt)) :
    instruction.op = .output := by
  rcases hreturn with houtput | ⟨_, hhalt⟩
  · exact houtput
  · have hnonoutput : instruction.op ≠ .output := by
      rw [hhalt]
      decide
    have hrawFlow := local_occurrence_flows_to_raw_block_of_lookup hlookup hnonoutput
    have hrawNonpublic := nonpublic_of_flows_from_nonpublic hnonpublic hrawFlow
    have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
    have hmem : instruction ∈
        (rawSemanticProgram program analysis).instructions.toList := by
      exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hlookup)
    have hpublic := hstatic.2 instruction hmem hhalt
    exact False.elim (hrawNonpublic hpublic)

/-- Two genuine synthetic internal returns may sit at different output instructions.  Their
    coherent corresponding frames nevertheless return to the same continuation.  The local
    occurrence checks isolate both return destinations, so arbitrary private payload differences
    cannot alter the paired Public projection. -/
theorem verified_paired_synthetic_internal_returns
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {left right : State}
    {leftInstruction rightInstruction : Instruction}
    {leftFrame rightFrame : CallFrame} {leftRest rightRest : List CallFrame}
    (hleftActive : ActiveState (rawSemanticProgram program analysis) root left)
    (hrightActive : ActiveState (rawSemanticProgram program analysis) root right)
    (hprojection : publicProjection (rawSemanticProgram program analysis) left =
      publicProjection (rawSemanticProgram program analysis) right)
    (hexternalInputs : left.externalInputs = right.externalInputs)
    (hstacks : CallStackPublicEquivalent (rawSemanticProgram program analysis)
      left.callStack right.callStack)
    (hleftLookup : (rawSemanticProgram program analysis).instructions[left.pc]? =
      some leftInstruction)
    (hrightLookup : (rawSemanticProgram program analysis).instructions[right.pc]? =
      some rightInstruction)
    (hleftOutput : leftInstruction.op = .output)
    (hrightOutput : rightInstruction.op = .output)
    (hleftNonpublic : localOccurrenceAt analysis.localAnalysis.frontiers left.pc ≠ .pub)
    (hrightNonpublic : localOccurrenceAt analysis.localAnalysis.frontiers right.pc ≠ .pub)
    (hleftStack : left.callStack = leftFrame :: leftRest)
    (hrightStack : right.callStack = rightFrame :: rightRest)
    (hleftNext : (step (rawSemanticProgram program analysis) left).state.trapped = false)
    (hrightNext : (step (rawSemanticProgram program analysis) right).state.trapped = false) :
    PairedPublicSilentSegments (rawSemanticProgram program analysis) 1 1 left right
        (step (rawSemanticProgram program analysis) left).state
        (step (rawSemanticProgram program analysis) right).state ∧
      PublicLowEquivalent (rawSemanticProgram program analysis)
        (step (rawSemanticProgram program analysis) left).state
        (step (rawSemanticProgram program analysis) right).state := by
  let machine := rawSemanticProgram program analysis
  have hleftLive : left.halted = false ∧ left.trapped = false :=
    ⟨hleftActive.notHalted, hleftActive.notTrapped⟩
  have hrightLive : right.halted = false ∧ right.trapped = false :=
    ⟨hrightActive.notHalted, hrightActive.notTrapped⟩
  have hstackEquivalent :
      CallStackPublicEquivalent machine (leftFrame :: leftRest) (rightFrame :: rightRest) := by
    simpa [machine, hleftStack, hrightStack] using hstacks
  rcases hstackEquivalent with ⟨hframe, hrest⟩
  have hleftFlow := nontrapping_internal_output_flow
    (by simpa [machine] using hleftLookup) hleftOutput hleftLive hleftStack
    (by simpa [machine] using hleftNext)
  have hrightFlow := nontrapping_internal_output_flow
    (by simpa [machine] using hrightLookup) hrightOutput hrightLive hrightStack
    (by simpa [machine] using hrightNext)
  have hleftIsolated := verified_local_nonpublic_output_top_frame_isolated
    hjudgment hanalysis hleftActive hleftLookup hleftOutput hleftNonpublic hleftStack
  have hrightIsolated := verified_local_nonpublic_output_top_frame_isolated
    hjudgment hanalysis hrightActive hrightLookup hrightOutput hrightNonpublic hrightStack
  have hreturnedProjection := internalReturnStorage_preserves_publicProjection_eq
    (machine := machine)
    (leftPayload := (operandValue machine left leftInstruction).payload)
    (rightPayload := (operandValue machine right rightInstruction).payload)
    hprojection hframe (by
      intro hdestination hpublic
      have hprivate := hleftIsolated.resolve_left hdestination
      exact False.elim (hprivate (by simpa [machine] using hpublic)))
  have hstepProjection : publicProjection machine (step machine left).state =
      publicProjection machine (step machine right).state := by
    simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hleftLookup, hrightLookup, hleftOutput, hrightOutput, hleftStack, hrightStack,
      hleftFlow, hrightFlow, machine, publicProjection] using hreturnedProjection
  have hboundaryLeft : publicBoundaryTrace (step machine left).events = [] := by
    simp [step, hleftLive.1, hleftLive.2, hleftLookup, hleftOutput, hleftStack,
      hleftFlow, machine, publicBoundaryTrace]
  have hboundaryRight : publicBoundaryTrace (step machine right).events = [] := by
    simp [step, hrightLive.1, hrightLive.2, hrightLookup, hrightOutput, hrightStack,
      hrightFlow, machine, publicBoundaryTrace]
  have hpaired : PairedPublicSilentSegments machine 1 1 left right
      (step machine left).state (step machine right).state := by
    refine ⟨by simp [runPrefix], by simp [runPrefix], ?_, ?_, hstepProjection⟩
    · intro elapsed helapsed
      have : elapsed = 0 := by omega
      subst elapsed
      simpa only [runPrefix] using hboundaryLeft
    · intro elapsed helapsed
      have : elapsed = 0 := by omega
      subst elapsed
      simpa only [runPrefix] using hboundaryRight
  have hpc : (step machine left).state.pc = (step machine right).state.pc := by
    simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hleftLookup, hrightLookup, hleftOutput, hrightOutput, hleftStack, hrightStack,
      hleftFlow, hrightFlow, machine] using hframe.1
  have hleftHalted : (step machine left).state.halted = false := by
    by_cases hdestination : leftFrame.destination = 0 <;>
      simp [step, hleftLive.1, hleftLive.2, hleftLookup, hleftOutput, hleftStack,
        hleftFlow, machine, hdestination]
  have hrightHalted : (step machine right).state.halted = false := by
    by_cases hdestination : rightFrame.destination = 0 <;>
      simp [step, hrightLive.1, hrightLive.2, hrightLookup, hrightOutput, hrightStack,
        hrightFlow, machine, hdestination]
  have hhalted : (step machine left).state.halted =
      (step machine right).state.halted := hleftHalted.trans hrightHalted.symm
  have hstack : CallStackPublicEquivalent machine
      (step machine left).state.callStack (step machine right).state.callStack := by
    simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hleftLookup, hrightLookup, hleftOutput, hrightOutput, hleftStack, hrightStack,
      hleftFlow, hrightFlow, machine] using hrest
  have hleftSize : (step machine left).state.values.size = machine.valueLabels.size := by
    by_cases hdestination : leftFrame.destination = 0 <;>
      simpa [step, hleftLive.1, hleftLive.2, hleftLookup, hleftOutput, hleftStack,
        hleftFlow, machine, hdestination] using hleftActive.wellFormed.1
  have hrightSize : (step machine right).state.values.size = machine.valueLabels.size := by
    by_cases hdestination : rightFrame.destination = 0 <;>
      simpa [step, hrightLive.1, hrightLive.2, hrightLookup, hrightOutput, hrightStack,
        hrightFlow, machine, hdestination] using hrightActive.wellFormed.1
  have hstreams : (step machine left).state.externalInputs =
      (step machine right).state.externalInputs := by
    rw [step_preserves_external_inputs, step_preserves_external_inputs]
    exact hexternalInputs
  have hlow : PublicLowEquivalent machine (step machine left).state
      (step machine right).state := by
    apply (publicLowEquivalent_iff_projection machine _ _).2
    exact ⟨hpc, hhalted, hleftNext.trans hrightNext.symm, hstack,
      hleftSize, hrightSize, hstreams, hstepProjection⟩
  exact ⟨by simpa [machine] using hpaired, by simpa [machine] using hlow⟩

/-- The raw output payload occurrence is the verifier-derived local occurrence at the exact
    instruction position.  It is not supplied by Rust or recovered from a runtime label. -/
theorem raw_output_payload_occurrence_eq_local
    {program : V9.Program} {analysis : OccurrenceDataflowInvocation.Analysis}
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (houtput : instruction.op = .output) :
    instruction.outputPayloadOccurrence =
      localOccurrenceAt analysis.localAnalysis.frontiers pc := by
  obtain ⟨source, _, hraised⟩ := rawInstructionSource_of_lookup hlookup
  have hsourceOutput : source.op = .output := by
    rw [hraised] at houtput
    simpa [raiseInstructionResultLabel, raiseInstructionOccurrence] using houtput
  rw [hraised]
  simp [raiseInstructionResultLabel, raiseInstructionOccurrence, hsourceOutput]

/-- Two genuine top-level synthetic outputs halt independently and emit one matching declaration-
    owned output occurrence. Their raw instruction identifiers may differ, but the function root
    site is stable, and a non-Public local occurrence hides each payload without erasing the event. -/
theorem verified_paired_synthetic_top_outputs
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {left right : State}
    {leftInstruction rightInstruction : Instruction}
    (hleftActive : ActiveState (rawSemanticProgram program analysis) root left)
    (hrightActive : ActiveState (rawSemanticProgram program analysis) root right)
    (hprojection : publicProjection (rawSemanticProgram program analysis) left =
      publicProjection (rawSemanticProgram program analysis) right)
    (hleftLookup : (rawSemanticProgram program analysis).instructions[left.pc]? =
      some leftInstruction)
    (hrightLookup : (rawSemanticProgram program analysis).instructions[right.pc]? =
      some rightInstruction)
    (hleftOutput : leftInstruction.op = .output)
    (hrightOutput : rightInstruction.op = .output)
    (hleftNonpublic : localOccurrenceAt analysis.localAnalysis.frontiers left.pc ≠ .pub)
    (hrightNonpublic : localOccurrenceAt analysis.localAnalysis.frontiers right.pc ≠ .pub)
    (hleftStack : left.callStack = []) (hrightStack : right.callStack = []) :
    publicBoundaryTrace (step (rawSemanticProgram program analysis) left).events =
        publicBoundaryTrace (step (rawSemanticProgram program analysis) right).events ∧
      publicProjection (rawSemanticProgram program analysis)
          (step (rawSemanticProgram program analysis) left).state =
        publicProjection (rawSemanticProgram program analysis)
          (step (rawSemanticProgram program analysis) right).state ∧
      (step (rawSemanticProgram program analysis) left).state.halted = true ∧
      (step (rawSemanticProgram program analysis) right).state.halted = true := by
  let machine := rawSemanticProgram program analysis
  have hleftMachineLookup : machine.instructions[left.pc]? = some leftInstruction := by
    simpa [machine] using hleftLookup
  have hrightMachineLookup : machine.instructions[right.pc]? = some rightInstruction := by
    simpa [machine] using hrightLookup
  have hleftReady : ¬(left.halted || left.trapped) := by
    simp [hleftActive.notHalted, hleftActive.notTrapped]
  have hrightReady : ¬(right.halted || right.trapped) := by
    simp [hrightActive.notHalted, hrightActive.notTrapped]
  obtain ⟨leftCurrent, hleftCurrentLookup, hleftFunction⟩ := hleftActive.currentInstruction
  have hleftCurrentEq : leftCurrent = leftInstruction := by
    rw [hleftLookup] at hleftCurrentLookup
    exact Option.some.inj hleftCurrentLookup.symm
  subst leftCurrent
  obtain ⟨rightCurrent, hrightCurrentLookup, hrightFunction⟩ := hrightActive.currentInstruction
  have hrightCurrentEq : rightCurrent = rightInstruction := by
    rw [hrightLookup] at hrightCurrentLookup
    exact Option.some.inj hrightCurrentLookup.symm
  subst rightCurrent
  have hleftFunctionRoot : leftInstruction.functionId = root := by
    rw [hleftStack] at hleftFunction
    simpa [activeFunctionId] using hleftFunction
  have hrightFunctionRoot : rightInstruction.functionId = root := by
    rw [hrightStack] at hrightFunction
    simpa [activeFunctionId] using hrightFunction
  obtain ⟨leftSource, hleftSourceLookup, hleftRaised⟩ :=
    rawInstructionSource_of_lookup hleftLookup
  obtain ⟨rightSource, hrightSourceLookup, hrightRaised⟩ :=
    rawInstructionSource_of_lookup hrightLookup
  have hleftSourceOutput : leftSource.op = .output := by
    rw [hleftRaised] at hleftOutput
    simpa [raiseInstructionResultLabel, raiseInstructionOccurrence] using hleftOutput
  have hrightSourceOutput : rightSource.op = .output := by
    rw [hrightRaised] at hrightOutput
    simpa [raiseInstructionResultLabel, raiseInstructionOccurrence] using hrightOutput
  have hleftSourceFunction : leftSource.functionId = root := by
    have : leftSource.functionId = leftInstruction.functionId := by
      rw [hleftRaised]
      simp [raiseInstructionResultLabel, raiseInstructionOccurrence]
    exact this.trans hleftFunctionRoot
  have hrightSourceFunction : rightSource.functionId = root := by
    have : rightSource.functionId = rightInstruction.functionId := by
      rw [hrightRaised]
      simp [raiseInstructionResultLabel, raiseInstructionOccurrence]
    exact this.trans hrightFunctionRoot
  have hrootReturnEq : rootReturnOccurrence?
      (OccurrenceDataflow.semanticProgram program analysis.dataflow) analysis leftSource =
      rootReturnOccurrence?
        (OccurrenceDataflow.semanticProgram program analysis.dataflow) analysis rightSource := by
    simp [rootReturnOccurrence?, rootContract?, functionReturnLabel?,
      hleftSourceFunction, hrightSourceFunction]
  have hblockEq : leftInstruction.blockLabel = rightInstruction.blockLabel := by
    rw [hleftRaised, hrightRaised]
    simp [raiseInstructionResultLabel, raiseInstructionOccurrence, hleftSourceOutput,
      hrightSourceOutput, hrootReturnEq]
  obtain ⟨leftCheckedSource, hleftCheckedLookup, _, _, ⟨leftRoot, hleftRoot, _⟩⟩ :=
    returned_output_root_return_safe hjudgment hanalysis hleftLookup hleftOutput
  have hleftCheckedEq : leftCheckedSource = leftSource :=
    Option.some.inj (hleftCheckedLookup.symm.trans hleftSourceLookup)
  subst leftCheckedSource
  obtain ⟨rightCheckedSource, hrightCheckedLookup, _, _, ⟨rightRoot, hrightRoot, _⟩⟩ :=
    returned_output_root_return_safe hjudgment hanalysis hrightLookup hrightOutput
  have hrightCheckedEq : rightCheckedSource = rightSource :=
    Option.some.inj (hrightCheckedLookup.symm.trans hrightSourceLookup)
  subst rightCheckedSource
  have hleftRootIndex : analysis.dataflow.contracts.roots[root.toNat - 1]? = some leftRoot := by
    unfold rootContract? at hleftRoot
    rw [hleftSourceFunction] at hleftRoot
    cases hindex : analysis.dataflow.contracts.roots[root.toNat - 1]? with
    | none => simp [hindex] at hleftRoot
    | some candidate =>
        have hcandidatEq : candidate = leftRoot := by
          have hpair : candidate.functionId = root ∧ candidate = leftRoot := by
            simpa [hindex] using hleftRoot
          exact hpair.2
        simpa [hcandidatEq] using hindex
  have hrightRootIndex : analysis.dataflow.contracts.roots[root.toNat - 1]? = some rightRoot := by
    unfold rootContract? at hrightRoot
    rw [hrightSourceFunction] at hrightRoot
    cases hindex : analysis.dataflow.contracts.roots[root.toNat - 1]? with
    | none => simp [hindex] at hrightRoot
    | some candidate =>
        have hcandidatEq : candidate = rightRoot := by
          have hpair : candidate.functionId = root ∧ candidate = rightRoot := by
            simpa [hindex] using hrightRoot
          exact hpair.2
        simpa [hcandidatEq] using hindex
  have hrootsEq : leftRoot = rightRoot := by
    rw [hleftRootIndex] at hrightRootIndex
    exact Option.some.inj hrightRootIndex
  subst rightRoot
  have hsiteLeft : outputBoundarySite machine leftInstruction = leftRoot.nodeId := by
    simp [outputBoundarySite, machine, rawSemanticProgram, rawSemanticProgramFromDecoded,
      hleftFunctionRoot, hleftRootIndex]
  have hsiteRight : outputBoundarySite machine rightInstruction = leftRoot.nodeId := by
    simp [outputBoundarySite, machine, rawSemanticProgram, rawSemanticProgramFromDecoded,
      hrightFunctionRoot, hleftRootIndex]
  have hleftPayloadOccurrence :=
    raw_output_payload_occurrence_eq_local hleftLookup hleftOutput
  have hrightPayloadOccurrence :=
    raw_output_payload_occurrence_eq_local hrightLookup hrightOutput
  have hleftPayloadHidden : outputObservationPayload leftInstruction
      (operandValue machine left leftInstruction) = none := by
    unfold outputObservationPayload
    rw [hleftPayloadOccurrence]
    cases hoperand : (operandValue machine left leftInstruction).label <;>
      cases hlocal : localOccurrenceAt analysis.localAnalysis.frontiers left.pc <;>
      simp_all [outputObservationPayload, Label.lub, Label.rank, Label.eqb]
  have hrightPayloadHidden : outputObservationPayload rightInstruction
      (operandValue machine right rightInstruction) = none := by
    unfold outputObservationPayload
    rw [hrightPayloadOccurrence]
    cases hoperand : (operandValue machine right rightInstruction).label <;>
      cases hlocal : localOccurrenceAt analysis.localAnalysis.frontiers right.pc <;>
      simp_all [outputObservationPayload, Label.lub, Label.rank, Label.eqb]
  have hobservation : publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events := by
    have hleftTrace : publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (instructionEvents machine left leftInstruction) := by
      rw [step, if_neg hleftReady, hleftMachineLookup]
      simp [hleftOutput, hleftStack]
    have hrightTrace : publicBoundaryTrace (step machine right).events =
        publicBoundaryTrace (instructionEvents machine right rightInstruction) := by
      rw [step, if_neg hrightReady, hrightMachineLookup]
      simp [hrightOutput, hrightStack]
    rw [hleftTrace, hrightTrace]
    by_cases hpublic : leftInstruction.blockLabel = .pub
    · have hrightPublic : rightInstruction.blockLabel = .pub := hblockEq.symm.trans hpublic
      rw [public_output_instruction_observation machine left leftInstruction hleftOutput hpublic,
        public_output_instruction_observation machine right rightInstruction hrightOutput
          hrightPublic, hsiteLeft, hsiteRight, hleftPayloadHidden, hrightPayloadHidden]
    · have hrightNonpublic : rightInstruction.blockLabel ≠ .pub := by
        simpa [hblockEq] using hpublic
      rw [nonpublic_instruction_has_no_public_boundary_observation machine left
          leftInstruction hpublic,
        nonpublic_instruction_has_no_public_boundary_observation machine right
          rightInstruction hrightNonpublic]
  have hendpoint : publicProjection machine (step machine left).state =
      publicProjection machine (step machine right).state :=
    by
      rw [step, if_neg hleftReady, hleftMachineLookup, step, if_neg hrightReady,
        hrightMachineLookup]
      simp only [hleftOutput, hrightOutput, hleftStack, hrightStack]
      simpa [machine, publicProjection] using hprojection
  have hleftHalted : (step machine left).state.halted = true := by
    rw [step, if_neg hleftReady, hleftMachineLookup]
    simp [hleftOutput, hleftStack]
  have hrightHalted : (step machine right).state.halted = true := by
    rw [step, if_neg hrightReady, hrightMachineLookup]
    simp [hrightOutput, hrightStack]
  exact ⟨by simpa [machine] using hobservation, by simpa [machine] using hendpoint,
    by simpa [machine] using hleftHalted, by simpa [machine] using hrightHalted⟩

/-- Append a relationally restoring pair of raw segments to two unary silent prefixes. -/
theorem pairedPublicSilentSegments_append
    {machine : SemanticProgram}
    {leftFirst rightFirst leftSecond rightSecond : Nat}
    {leftStart rightStart leftMiddle rightMiddle leftFinish rightFinish : State}
    (hleftPrefix : PublicSilentSegment machine leftFirst leftStart leftMiddle)
    (hrightPrefix : PublicSilentSegment machine rightFirst rightStart rightMiddle)
    (hsuffix : PairedPublicSilentSegments machine leftSecond rightSecond
      leftMiddle rightMiddle leftFinish rightFinish) :
    PairedPublicSilentSegments machine (leftFirst + leftSecond) (rightFirst + rightSecond)
      leftStart rightStart leftFinish rightFinish := by
  refine ⟨?_, ?_, ?_, ?_, hsuffix.endpointProjection⟩
  · rw [ReleaseSynchronization.runPrefix_add]
    simpa only [hleftPrefix.finish_eq] using hsuffix.leftFinish_eq
  · rw [ReleaseSynchronization.runPrefix_add]
    simpa only [hrightPrefix.finish_eq] using hsuffix.rightFinish_eq
  · intro elapsed helapsed
    by_cases hbefore : elapsed < leftFirst
    · exact hleftPrefix.silent elapsed hbefore
    · have hafter : elapsed - leftFirst < leftSecond := by omega
      have hstate := congrArg StepResult.state
        (ReleaseSynchronization.runPrefix_add machine leftFirst
          (elapsed - leftFirst) leftStart)
      have hsum : leftFirst + (elapsed - leftFirst) = elapsed := by omega
      rw [hsum] at hstate
      dsimp only at hstate
      rw [hleftPrefix.finish_eq] at hstate
      rw [hstate]
      exact hsuffix.leftSilent (elapsed - leftFirst) hafter
  · intro elapsed helapsed
    by_cases hbefore : elapsed < rightFirst
    · exact hrightPrefix.silent elapsed hbefore
    · have hafter : elapsed - rightFirst < rightSecond := by omega
      have hstate := congrArg StepResult.state
        (ReleaseSynchronization.runPrefix_add machine rightFirst
          (elapsed - rightFirst) rightStart)
      have hsum : rightFirst + (elapsed - rightFirst) = elapsed := by omega
      rw [hsum] at hstate
      dsimp only at hstate
      rw [hrightPrefix.finish_eq] at hstate
      rw [hstate]
      exact hsuffix.rightSilent (elapsed - rightFirst) hafter

private theorem publicReleaseSilentSegment_append_local {machine : SemanticProgram}
    {firstLength secondLength : Nat} {start middle : State}
    (hfirstFinish : (runPrefix machine firstLength start).state = middle)
    (hfirst : PublicReleaseSilentSegment machine firstLength start)
    (hsecond : PublicReleaseSilentSegment machine secondLength middle) :
    PublicReleaseSilentSegment machine (firstLength + secondLength) start := by
  intro elapsed helapsed
  by_cases hbefore : elapsed < firstLength
  · exact hfirst elapsed hbefore
  · have hafter : elapsed - firstLength < secondLength := by omega
    have hstate := congrArg StepResult.state
      (ReleaseSynchronization.runPrefix_add machine firstLength
        (elapsed - firstLength) start)
    have hsum : firstLength + (elapsed - firstLength) = elapsed := by omega
    rw [hsum] at hstate
    dsimp only at hstate
    rw [hfirstFinish] at hstate
    rw [hstate]
    exact hsecond (elapsed - firstLength) hafter

private theorem public_release_suffix_eq_after_raw_prefixes {machine : SemanticProgram}
    {leftLength rightLength leftTail rightTail : Nat}
    {leftStart rightStart leftFinish rightFinish : State}
    (hleftFinish : (runPrefix machine leftLength leftStart).state = leftFinish)
    (hrightFinish : (runPrefix machine rightLength rightStart).state = rightFinish)
    (hleftRelease : PublicReleaseSilentSegment machine leftLength leftStart)
    (hrightRelease : PublicReleaseSilentSegment machine rightLength rightStart)
    (hrelease : publicReleaseTrace machine
        (runPrefix machine (leftLength + leftTail) leftStart).events =
      publicReleaseTrace machine
        (runPrefix machine (rightLength + rightTail) rightStart).events) :
    publicReleaseTrace machine (runPrefix machine leftTail leftFinish).events =
      publicReleaseTrace machine (runPrefix machine rightTail rightFinish).events := by
  rw [ReleaseSynchronization.runPrefix_add, ReleaseSynchronization.runPrefix_add,
    publicReleaseTrace_append, publicReleaseTrace_append,
    publicReleaseTrace_eq_nil_of_silentSegment hleftRelease,
    publicReleaseTrace_eq_nil_of_silentSegment hrightRelease,
    List.nil_append, List.nil_append] at hrelease
  simpa only [hleftFinish, hrightFinish] using hrelease

/-- Production bridge for the synthetic-return branch of two independently sized verified
    private-controller segments.  The proof executes both genuine endpoint instructions.  An
    internal return yields a reusable paired private continuation; a top-level output consumes
    both successful executions as a paired private terminal. -/
theorem publicExecutionProgress_of_verified_synthetic_private_controller_segments
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {leftSteps rightSteps : Nat} {left right : State}
    {leftResult rightResult : StepResult}
    (_hleftSync : VerifiedSynchronizationPoint
      (rawSemanticProgram program analysis) root left)
    (_hrightSync : VerifiedSynchronizationPoint
      (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hleftExecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root leftSteps left leftResult)
    (hrightExecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root rightSteps right rightResult)
    (hrelease : publicReleaseTrace (rawSemanticProgram program analysis) leftResult.events =
      publicReleaseTrace (rawSemanticProgram program analysis) rightResult.events)
    (hsegments : SyntheticPrivateControllerSegments
      (rawSemanticProgram program analysis) analysis.localAnalysis.frontiers root
      leftSteps rightSteps left right) :
    PublicExecutionProgress (rawSemanticProgram program analysis) root
      leftSteps left rightSteps right := by
  let machine := rawSemanticProgram program analysis
  have hjudgment := v9_occurrence_verifier_sound hverified
  obtain ⟨leftLength, rightLength, leftFinish, rightFinish, parent,
    hleftPositive, hrightPositive, hleftBound, hrightBound,
    hleftSegment, hrightSegment, hleftRelease, hrightRelease,
    hleftEndpoint, hrightEndpoint, hsynthetic⟩ := hsegments
  obtain ⟨leftInstruction, hleftLookup, hleftNonpublic⟩ := hleftEndpoint
  obtain ⟨rightInstruction, hrightLookup, hrightNonpublic⟩ := hrightEndpoint
  obtain ⟨leftReturnInstruction, hleftReturnLookup, _, hleftReturn⟩ :=
    hsynthetic.leftReturn
  obtain ⟨rightReturnInstruction, hrightReturnLookup, _, hrightReturn⟩ :=
    hsynthetic.rightReturn
  have hleftInstructionEq : leftReturnInstruction = leftInstruction := by
    rw [hleftLookup] at hleftReturnLookup
    exact Option.some.inj hleftReturnLookup.symm
  have hrightInstructionEq : rightReturnInstruction = rightInstruction := by
    rw [hrightLookup] at hrightReturnLookup
    exact Option.some.inj hrightReturnLookup.symm
  subst leftReturnInstruction
  subst rightReturnInstruction
  have hleftOutput := verified_local_nonpublic_synthetic_return_is_output
    hjudgment hanalysis hleftLookup hleftNonpublic hleftReturn
  have hrightOutput := verified_local_nonpublic_synthetic_return_is_output
    hjudgment hanalysis hrightLookup hrightNonpublic hrightReturn
  have hstartProjection : publicProjection machine left = publicProjection machine right := by
    simpa [machine] using publicProjection_eq_of_low hlow
  have hfinishProjection : publicProjection machine leftFinish =
      publicProjection machine rightFinish :=
    hleftSegment.endProjection.trans
      (hstartProjection.trans hrightSegment.endProjection.symm)
  have hfinishStacks : CallStackPublicEquivalent machine
      leftFinish.callStack rightFinish.callStack := by
    have hstartStacks := hlow.2.2.2.1
    simpa [machine, hsynthetic.leftStack, hsynthetic.rightStack] using hstartStacks
  have hleftStreams : leftFinish.externalInputs = left.externalInputs := by
    have h := runPrefix_preserves_external_inputs machine leftLength left
    rw [hleftSegment.finish_eq] at h
    exact h
  have hrightStreams : rightFinish.externalInputs = right.externalInputs := by
    have h := runPrefix_preserves_external_inputs machine rightLength right
    rw [hrightSegment.finish_eq] at h
    exact h
  obtain ⟨_, _, _, _, _, _, hstartStreams, _⟩ :=
    (publicLowEquivalent_iff_projection machine left right).mp (by simpa [machine] using hlow)
  have hfinishStreams : leftFinish.externalInputs = rightFinish.externalInputs :=
    hleftStreams.trans (hstartStreams.trans hrightStreams.symm)
  have hleftDrop := hleftExecution.drop hleftBound
  have hrightDrop := hrightExecution.drop hrightBound
  rw [hleftSegment.finish_eq] at hleftDrop
  rw [hrightSegment.finish_eq] at hrightDrop
  have hleftRemainingPositive : 0 < leftSteps - leftLength := by omega
  have hrightRemainingPositive : 0 < rightSteps - rightLength := by omega
  have hleftRemainingShape : leftSteps - leftLength =
      (leftSteps - leftLength - 1) + 1 := by omega
  have hrightRemainingShape : rightSteps - rightLength =
      (rightSteps - rightLength - 1) + 1 := by omega
  rw [hleftRemainingShape] at hleftDrop
  rw [hrightRemainingShape] at hrightDrop
  have hleftNext := successfulExecution_first_successor_not_trapped hleftDrop
  have hrightNext := successfulExecution_first_successor_not_trapped hrightDrop
  have hleftOneRelease : PublicReleaseSilentSegment machine 1 leftFinish := by
    intro elapsed helapsed
    have helapsedZero : elapsed = 0 := by omega
    subst elapsed
    simpa only [runPrefix] using publicReleaseTrace_step_nonrelease machine leftFinish
      leftInstruction (by simpa [machine] using hleftLookup) (by simp [hleftOutput])
      (by simp [hleftOutput])
  have hrightOneRelease : PublicReleaseSilentSegment machine 1 rightFinish := by
    intro elapsed helapsed
    have helapsedZero : elapsed = 0 := by omega
    subst elapsed
    simpa only [runPrefix] using publicReleaseTrace_step_nonrelease machine rightFinish
      rightInstruction (by simpa [machine] using hrightLookup) (by simp [hrightOutput])
      (by simp [hrightOutput])
  have hleftFullRelease : PublicReleaseSilentSegment machine (leftLength + 1) left :=
    publicReleaseSilentSegment_append_local hleftSegment.finish_eq hleftRelease hleftOneRelease
  have hrightFullRelease : PublicReleaseSilentSegment machine (rightLength + 1) right :=
    publicReleaseSilentSegment_append_local hrightSegment.finish_eq hrightRelease hrightOneRelease
  cases hleftSpine : left.callStack with
  | nil =>
      have hrightSpine : right.callStack = [] := by
        have hstack := hlow.2.2.2.1
        rw [hleftSpine] at hstack
        cases hrightStack : right.callStack with
        | nil => rfl
        | cons frame rest => simp [CallStackPublicEquivalent, hrightStack] at hstack
      have hleftFinishStack : leftFinish.callStack = [] :=
        hsynthetic.leftStack.trans hleftSpine
      have hrightFinishStack : rightFinish.callStack = [] :=
        hsynthetic.rightStack.trans hrightSpine
      have htop := verified_paired_synthetic_top_outputs
        hjudgment hanalysis hsynthetic.leftActive hsynthetic.rightActive hfinishProjection
        hleftLookup hrightLookup hleftOutput hrightOutput
        hleftNonpublic hrightNonpublic hleftFinishStack hrightFinishStack
      have hleftTailZero := successfulExecution_tail_eq_zero_of_first_successor_halted
        hleftDrop htop.2.2.1
      have hrightTailZero := successfulExecution_tail_eq_zero_of_first_successor_halted
        hrightDrop htop.2.2.2
      have hleftTotal : leftLength + 1 = leftSteps := by omega
      have hrightTotal : rightLength + 1 = rightSteps := by omega
      rw [← hleftTotal, ← hrightTotal]
      exact .privateMatchedTerminal hleftSegment hrightSegment htop.1 htop.2.1
        htop.2.2.1 htop.2.2.2
  | cons leftFrame leftRest =>
      cases hrightSpine : right.callStack with
      | nil =>
          have hstack := hlow.2.2.2.1
          simp [CallStackPublicEquivalent, hleftSpine, hrightSpine] at hstack
      | cons rightFrame rightRest =>
          have hleftFinishStack : leftFinish.callStack = leftFrame :: leftRest :=
            hsynthetic.leftStack.trans hleftSpine
          have hrightFinishStack : rightFinish.callStack = rightFrame :: rightRest :=
            hsynthetic.rightStack.trans hrightSpine
          have hinternal := verified_paired_synthetic_internal_returns hjudgment hanalysis
            hsynthetic.leftActive hsynthetic.rightActive hfinishProjection hfinishStreams
            hfinishStacks hleftLookup hrightLookup hleftOutput hrightOutput
            hleftNonpublic hrightNonpublic hleftFinishStack hrightFinishStack
            hleftNext hrightNext
          have hfullSegments := pairedPublicSilentSegments_append
            hleftSegment hrightSegment hinternal.1
          have hleftStepNotHalted : (step machine leftFinish).state.halted = false := by
            have hlive : leftFinish.halted = false ∧ leftFinish.trapped = false :=
              ⟨hsynthetic.leftActive.notHalted, hsynthetic.leftActive.notTrapped⟩
            have hflow := nontrapping_internal_output_flow
              (by simpa [machine] using hleftLookup) hleftOutput hlive hleftFinishStack
              (by simpa [machine] using hleftNext)
            by_cases hdestination : leftFrame.destination = 0 <;>
              simp [step, hlive.1, hlive.2, hleftLookup, hleftOutput,
                hleftFinishStack, hflow, machine, hdestination]
          have hrightStepNotHalted : (step machine rightFinish).state.halted = false := by
            have hlive : rightFinish.halted = false ∧ rightFinish.trapped = false :=
              ⟨hsynthetic.rightActive.notHalted, hsynthetic.rightActive.notTrapped⟩
            have hflow := nontrapping_internal_output_flow
              (by simpa [machine] using hrightLookup) hrightOutput hlive hrightFinishStack
              (by simpa [machine] using hrightNext)
            by_cases hdestination : rightFrame.destination = 0 <;>
              simp [step, hlive.1, hlive.2, hrightLookup, hrightOutput,
                hrightFinishStack, hflow, machine, hdestination]
          have hleftFullBound : leftLength + 1 < leftSteps := by
            by_contra hnot
            have heq : leftLength + 1 = leftSteps := by omega
            have hfinish := hfullSegments.leftFinish_eq
            rw [heq, hleftExecution.run] at hfinish
            have : leftResult.state.halted = false := by
              rw [hfinish]
              exact hleftStepNotHalted
            rw [hleftExecution.halted] at this
            contradiction
          have hrightFullBound : rightLength + 1 < rightSteps := by
            by_contra hnot
            have heq : rightLength + 1 = rightSteps := by omega
            have hfinish := hfullSegments.rightFinish_eq
            rw [heq, hrightExecution.run] at hfinish
            have : rightResult.state.halted = false := by
              rw [hfinish]
              exact hrightStepNotHalted
            rw [hrightExecution.halted] at this
            contradiction
          have hleftAfterSync : VerifiedSynchronizationPoint machine root
              (step machine leftFinish).state := by
            refine ⟨hsynthetic.leftReachable.step, ?_⟩
            have hactive := hleftExecution.reached_active hleftFullBound
            rw [hfullSegments.leftFinish_eq] at hactive
            exact hactive
          have hrightAfterSync : VerifiedSynchronizationPoint machine root
              (step machine rightFinish).state := by
            refine ⟨hsynthetic.rightReachable.step, ?_⟩
            have hactive := hrightExecution.reached_active hrightFullBound
            rw [hfullSegments.rightFinish_eq] at hactive
            exact hactive
          have hactualRelease : publicReleaseTrace machine
                (runPrefix machine leftSteps left).events =
              publicReleaseTrace machine (runPrefix machine rightSteps right).events := by
            rw [hleftExecution.run, hrightExecution.run]
            simpa [machine] using hrelease
          have hleftSum : leftLength + 1 + (leftSteps - (leftLength + 1)) = leftSteps :=
            Nat.add_sub_of_le (Nat.le_of_lt hleftFullBound)
          have hrightSum : rightLength + 1 + (rightSteps - (rightLength + 1)) = rightSteps :=
            Nat.add_sub_of_le (Nat.le_of_lt hrightFullBound)
          have hsplitRelease : publicReleaseTrace machine
                (runPrefix machine
                  ((leftLength + 1) + (leftSteps - (leftLength + 1))) left).events =
              publicReleaseTrace machine
                (runPrefix machine
                  ((rightLength + 1) + (rightSteps - (rightLength + 1))) right).events := by
            simpa only [hleftSum, hrightSum] using hactualRelease
          have htailRelease := public_release_suffix_eq_after_raw_prefixes
            hfullSegments.leftFinish_eq hfullSegments.rightFinish_eq
            hleftFullRelease hrightFullRelease hsplitRelease
          exact publicExecutionProgress_of_paired_private_segments
            (by omega) (by omega) hleftFullBound hrightFullBound hfullSegments
            hleftAfterSync hrightAfterSync hinternal.2
            (by simpa [machine] using hleftExecution)
            (by simpa [machine] using hrightExecution) htailRelease

end LambdaSigil.Combined.V9.PublicSyntheticReturnSecurity
