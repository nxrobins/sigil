import LambdaSigil.PublicContinuationSecurity
import LambdaSigil.PublicMatchedProgressSecurity
import LambdaSigil.PublicPrivateReleaseSecurity
import LambdaSigil.PublicStepClassification

/-!
# Successful private invocations as Public-silent call segments

This module packages an actual nontrapping call or closure entry, the independently sized
invocation-private execution selected by `PublicRegionConvergence`, and its genuine raw return.
The resulting segment starts in the caller, ends at that caller's real `pc + 1` continuation,
emits no Public boundary observation, and contributes no statically Public release occurrence.

The return is not assumed harmless.  V9's checked invocation influence reaches the callee's
internal-return contract; a non-Public invocation therefore has a non-Public return label.  The
genuine coherent frame and `StateWellFormed` then force its destination to be zero or non-Public.
This is the load-bearing fact that permits unary frame-restored projection preservation through
the final output step.  Actual release and releaseCT events remain in the complete trace.
-/

namespace LambdaSigil.Combined.V9.PublicPrivateInvocationSecurity

open Semantic BoundaryContracts OccurrenceRegions OccurrenceTransfer
open OccurrenceDataflowInvocation OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity Semantic.PublicFrameSecurity
open Semantic.PublicRegionConvergence Semantic.PublicReleaseSynchronization
open PublicLocalSecurity PublicMatchingSecurity PublicContinuationSecurity
open PublicPrivateSegmentSecurity PublicPrivateReleaseSecurity PublicExecutionSecurity
open PublicStepClassification PublicMatchedProgressSecurity

private theorem eq_public_of_flowsTo_public {label : Label}
    (hflow : label.flowsTo .pub = true) : label = .pub := by
  cases label <;> simp_all [Label.flowsTo, Label.rank]

private theorem labelFlows_trans {first middle last : Label}
    (hfirst : first.flowsTo middle = true) (hlast : middle.flowsTo last = true) :
    first.flowsTo last = true := by
  cases first <;> cases middle <;> cases last <;>
    simp_all [Label.flowsTo, Label.rank]

private theorem labelFlows_lub_left (left right : Label) :
    left.flowsTo (left.lub right) = true := by
  cases left <;> cases right <;> decide

private theorem labelFlows_lub_right (left right : Label) :
    right.flowsTo (left.lub right) = true := by
  cases left <;> cases right <;> decide

private theorem lub_right_component_of_flow {left right sink : Label}
    (hflow : (left.lub right).flowsTo sink = true) : right.flowsTo sink = true := by
  cases left <;> cases right <;> cases sink <;>
    simp_all [Label.flowsTo, Label.lub, Label.rank]

private theorem ffiContract_impossible_of_output_decode
    {program : V9.Program} {sourceIndex : BindingIndex} {owner : Node}
    {position : Nat} {contract : FfiContract}
    (hdecode : decodeSemanticInstrOp? owner.aux = some .output)
    (hffi : ffiContract? program sourceIndex owner position = some contract) : False := by
  have haux : owner.aux ≠ 15 := by
    intro heq
    simp [heq, decodeSemanticInstrOp?] at hdecode
  have hbne : (owner.aux != 15) = true := bne_iff_ne.mpr haux
  simp [ffiContract?, hbne] at hffi

private theorem actorContract_impossible_of_output_decode
    {program : V9.Program} {owner : Node} {position : Nat} {contract : ActorContract}
    (hdecode : decodeSemanticInstrOp? owner.aux = some .output)
    (hactor : actorContract? program owner position = some contract) : False := by
  have haux : owner.aux ≠ 8 := by
    intro heq
    simp [heq, decodeSemanticInstrOp?] at hdecode
  have hbne : (owner.aux != 8) = true := bne_iff_ne.mpr haux
  simp [actorContract?, hbne] at hactor

/-- Production site extraction cannot hide an output behind an FFI or actor site kind.  Thus the
    accepted instruction exposes its checked internal-return contract. -/
theorem returned_output_root_return_safe
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (houtput : instruction.op = .output) :
    RootReturnSafe program (rawSemanticProgram program analysis) analysis instruction pc := by
  have hsiteSafe :=
    (returned_instruction_occurrence_safe hjudgment hanalysis hlookup).2.2.2.2
  unfold SiteOccurrenceSafe at hsiteSafe
  cases hsite : site? analysis.dataflow.contracts instruction.id with
  | none => simp [hsite] at hsiteSafe
  | some site =>
      simp only [hsite] at hsiteSafe
      obtain ⟨source, hsourceMem, _, hdecode, hid, _, _, _, _⟩ :=
        raw_instruction_source_shape hlookup
      have hdecodeOutput : decodeSemanticInstrOp? source.aux = some .output := by
        simpa [houtput] using hdecode
      have hdataflow :=
        (OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).1
      have hcomponents := V9.OccurrenceDataflowSecurity.analyzed_components hdataflow
      have hcanonical := V9.OccurrenceDataflowSecurity.extracted_base_has_canonical_node_ids
        hcomponents.1
      have hsourceLookup := canonical_node_lookup_of_mem_id hcanonical hsourceMem hid
      have hextract := hcomponents.1
      obtain ⟨sourceIndex, owner, _, howner, _, hmatches⟩ :=
        BoundaryContracts.returned_site_has_actual_record hextract hsite
      have hownerEq : owner = source := Option.some.inj (howner.symm.trans hsourceLookup)
      subst owner
      have hkindSafe := hsiteSafe.2.2
      cases hkind : site.kind with
      | ordinary operation =>
          simp only [hkind] at hkindSafe
          rcases hkindSafe with ⟨hoperation, hoperationSafe⟩
          rw [houtput] at hoperation
          subst operation
          exact hoperationSafe
      | ffi position contract =>
          have hffi : ffiContract? program sourceIndex source position = some contract := by
            have hm := hmatches
            simp [siteMatches, hkind] at hm
            exact hm.2
          exact False.elim (ffiContract_impossible_of_output_decode hdecodeOutput hffi)
      | actor position contract =>
          have hactor : actorContract? program source position = some contract := by
            have hm := hmatches
            simp [siteMatches, hkind] at hm
            exact hm.2
          exact False.elim (actorContract_impossible_of_output_decode hdecodeOutput hactor)

/-- The checked one-based V9 function layout turns a genuine `functionById?` result into the
    exact indexed row used by `functionReturnLabel?`. -/
private theorem analyzed_functionById_indexed
    {program : V9.Program} {analysis : Analysis}
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

private theorem activeFunctionId_append_suffix (root : UInt32)
    (privateFrames suffix : List CallFrame) :
    activeFunctionId root (privateFrames ++ suffix) =
      activeFunctionId (activeFunctionId root suffix) privateFrames := by
  cases privateFrames <;> simp [activeFunctionId]

/-- Raw occurrence raising changes only the instruction block label.  For a closure, the
    invocation analyzer's actual-callee theorem therefore applies to the same selector value and
    resolved callee.  This projection is deliberately closure-specific: direct calls have no
    state-dependent selector and are handled separately. -/
theorem analyzed_raw_closure_callee_receives_selector_influence
    {program : V9.Program} {analysis : Analysis}
    (hjudgment : V9OccurrenceJudgment program)
    (hanalysis : analyze? program = some analysis)
    {state : State} {instruction : Instruction} {callee : Function}
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? = some instruction)
    (hclosure : instruction.op = .closure)
    (hcallee : instructionCallee? (rawSemanticProgram program analysis) state instruction =
      some callee) :
    (operandValue (rawSemanticProgram program analysis) state instruction).label.flowsTo
      (labelAt analysis.labels callee.id) = true := by
  let machine := rawSemanticProgram program analysis
  have hsafe := returned_closure_target_occurrence_safe hjudgment hanalysis hlookup
  unfold ClosureTargetOccurrenceSafe closureTargetOccurrenceOK at hsafe
  cases hcell : (valueOperandCells machine instruction).head? with
  | none =>
      simp [machine, hclosure, hcell, instructionCallee?, operandValues] at hcallee
  | some cell =>
      have hall : machine.functions.toList.all (fun function =>
          (labelAt machine.valueLabels cell).flowsTo
            (labelAt analysis.labels function.id)) = true := by
        simpa [machine, hclosure, hcell] using hsafe
      have hmember : callee ∈ machine.functions.toList :=
        Array.mem_toList_iff.mpr (instructionCallee_mem_functions hcallee)
      have hflow := List.all_eq_true.mp hall callee hmember
      have hoperandLabel : (operandValue machine state instruction).label =
          labelAt machine.valueLabels cell := by
        simp [operandValue, operandValues, hcell]
      simpa [machine, hoperandLabel] using hflow

private theorem ValueListPublicEquivalent.head_label_eq {left right : List Value}
    (h : ValueListPublicEquivalent left right) :
    (left.head?.getD defaultValue).label = (right.head?.getD defaultValue).label := by
  cases left with
  | nil => cases right <;> simp_all [ValueListPublicEquivalent]
  | cons leftHead leftRest =>
      cases right with
      | nil => simp [ValueListPublicEquivalent] at h
      | cons rightHead rightRest => exact h.1

/-- If a closure resolves to different actual callees in two Public-low states, its selector was
    necessarily Internal or Secret, and the checked dynamic-target fan-out makes both selected
    invocation labels non-Public.  Direct calls cannot enter this case. -/
theorem different_resolved_call_callees_are_private
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {left right : State} {instruction : Instruction} {leftCallee rightCallee : Function}
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hoperation : instruction.op = .call ∨ instruction.op = .closure)
    (hleftCallee : instructionCallee? (rawSemanticProgram program analysis) left instruction =
      some leftCallee)
    (hrightCallee : instructionCallee? (rawSemanticProgram program analysis) right instruction =
      some rightCallee)
    (hdifferent : leftCallee ≠ rightCallee) :
    labelAt analysis.labels leftCallee.id ≠ .pub ∧
      labelAt analysis.labels rightCallee.id ≠ .pub := by
  let machine := rawSemanticProgram program analysis
  rcases hoperation with hcall | hclosure
  · have hsame : instructionCallee? machine left instruction =
        instructionCallee? machine right instruction := by
      simp [instructionCallee?, hcall]
    rw [hleftCallee, hrightCallee] at hsame
    exact False.elim (hdifferent (Option.some.inj hsame))
  · have hselectorClass := verified_closure_selector_classification hjudgment hanalysis
      hlookup hclosure
    rcases hselectorClass with hpublic | hinternal | hsecret
    · have hsame := instructionCallee_eq_of_public_closure_selector hjudgment hanalysis
        hlow hlookup hclosure hpublic
      rw [hleftCallee, hrightCallee] at hsame
      exact False.elim (hdifferent (Option.some.inj hsame))
    · have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
      have hwell := instruction_well_formed_of_raw_static_safe hstatic hlookup
      have hvalues := operandValues_publicEquivalent hlow.2.2.2.2 hwell
      have hrightSelector : (operandValue machine right instruction).label = .internal := by
        have hlabels := ValueListPublicEquivalent.head_label_eq hvalues
        have heq : (operandValue machine right instruction).label =
            (operandValue machine left instruction).label := by
          simpa [operandValue] using hlabels.symm
        exact heq.trans hinternal
      have hleftSelectorFlow :=
        analyzed_raw_closure_callee_receives_selector_influence hjudgment hanalysis hlookup hclosure
          hleftCallee
      have hrightLookup : machine.instructions[right.pc]? = some instruction := by
        rw [← hlow.1]
        exact hlookup
      have hrightSelectorFlowRaw :=
        analyzed_raw_closure_callee_receives_selector_influence hjudgment hanalysis hrightLookup hclosure
          hrightCallee
      have hleftSelectorFlow : Label.internal.flowsTo
          (labelAt analysis.labels leftCallee.id) = true := by
        simpa [hinternal] using hleftSelectorFlow
      have hrightSelectorFlow : Label.internal.flowsTo
          (labelAt analysis.labels rightCallee.id) = true := by
        rw [hrightSelector] at hrightSelectorFlowRaw
        exact hrightSelectorFlowRaw
      constructor <;> intro hpublicCallee
      · have : Label.internal = .pub := eq_public_of_flowsTo_public (by
          simpa [hpublicCallee] using hleftSelectorFlow)
        contradiction
      · have : Label.internal = .pub := eq_public_of_flowsTo_public (by
          simpa [hpublicCallee] using hrightSelectorFlow)
        contradiction
    · have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
      have hwell := instruction_well_formed_of_raw_static_safe hstatic hlookup
      have hvalues := operandValues_publicEquivalent hlow.2.2.2.2 hwell
      have hrightSelector : (operandValue machine right instruction).label = .secret := by
        have hlabels := ValueListPublicEquivalent.head_label_eq hvalues
        have heq : (operandValue machine right instruction).label =
            (operandValue machine left instruction).label := by
          simpa [operandValue] using hlabels.symm
        exact heq.trans hsecret
      have hleftSelectorFlow :=
        analyzed_raw_closure_callee_receives_selector_influence hjudgment hanalysis hlookup hclosure
          hleftCallee
      have hrightLookup : machine.instructions[right.pc]? = some instruction := by
        rw [← hlow.1]
        exact hlookup
      have hrightSelectorFlowRaw :=
        analyzed_raw_closure_callee_receives_selector_influence hjudgment hanalysis hrightLookup hclosure
          hrightCallee
      have hleftSelectorFlow : Label.secret.flowsTo
          (labelAt analysis.labels leftCallee.id) = true := by
        simpa [hsecret] using hleftSelectorFlow
      have hrightSelectorFlow : Label.secret.flowsTo
          (labelAt analysis.labels rightCallee.id) = true := by
        rw [hrightSelector] at hrightSelectorFlowRaw
        exact hrightSelectorFlowRaw
      constructor <;> intro hpublicCallee
      · have : Label.secret = .pub := eq_public_of_flowsTo_public (by
          simpa [hpublicCallee] using hleftSelectorFlow)
        contradiction
      · have : Label.secret = .pub := eq_public_of_flowsTo_public (by
          simpa [hpublicCallee] using hrightSelectorFlow)
        contradiction

/-- Invocation influence is load-bearing at the real return.  The accepted internal-return check
    makes the current callee's invocation label flow to its declared return label; genuine frame
    provenance identifies that declaration with the top raw frame, and well-formedness prevents
    the non-Public return label from flowing into a Public destination. -/
theorem verified_private_invocation_output_top_frame_isolated
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine : List CallFrame} {state : State}
    {instruction : Instruction} {frame : CallFrame} {tail : List CallFrame}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlive : ActivationLive spine state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (houtput : instruction.op = .output)
    (hnonpublic : labelAt analysis.labels (activeFunctionId root spine) ≠ .pub)
    (hstack : state.callStack = frame :: tail) :
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
  obtain ⟨privateFrames, hliveStack⟩ := hlive
  have hchain := hactive.frameChain
  rw [hliveStack] at hchain
  have hprefixChain := frameChain_prefix_above_suffix hchain
  have hinvocationToActive :=
    frameChain_root_occurrence_flows_to_active hanalysis hprefixChain
  obtain ⟨current, hcurrentLookup, hcurrentFunction⟩ := hactive.currentInstruction
  have hcurrentEq : current = instruction := by
    rw [hlookup] at hcurrentLookup
    exact Option.some.inj hcurrentLookup.symm
  subst current
  have hactiveEq : activeFunctionId root state.callStack =
      activeFunctionId (activeFunctionId root spine) privateFrames := by
    rw [hliveStack]
    exact activeFunctionId_append_suffix root privateFrames spine
  have hfunctionEq : activeFunctionId (activeFunctionId root spine) privateFrames =
      source.functionId := by
    rw [← hactiveEq, ← hcurrentFunction, ← hsourceFunction]
  have hinvocationToSource :
      (labelAt analysis.labels (activeFunctionId root spine)).flowsTo
        (labelAt analysis.labels source.functionId) = true := by
    simpa [hfunctionEq] using hinvocationToActive
  have hsourceToEffective :
      (labelAt analysis.labels source.functionId).flowsTo
        (effectiveOccurrence analysis source state.pc) = true := by
    exact labelFlows_lub_left _ _
  have heffectiveToSink :
      (effectiveOccurrence analysis source state.pc).flowsTo sink = true :=
    lub_right_component_of_flow hreturnFlow
  have hinvocationToSink :
      (labelAt analysis.labels (activeFunctionId root spine)).flowsTo sink = true :=
    labelFlows_trans hinvocationToSource
      (labelFlows_trans hsourceToEffective heffectiveToSink)
  have hsinkNonpublic : sink ≠ .pub := by
    intro hsinkPublic
    exact hnonpublic (eq_public_of_flowsTo_public (by
      simpa [hsinkPublic] using hinvocationToSink))

  have htopChain := hactive.frameChain
  rw [hstack] at htopChain
  obtain ⟨callerDeclaration, callee, call, continuation, hcaller, hcallee, hpositive,
    hcall, hcallFunction, hcallOperation, hcallDestination, hdirect, hcontinuation,
    hcontinuationFunction, hframeReturn, hsaved⟩ := htopChain.1
  have hinstructionFrame : instruction.functionId = frame.calleeId := by
    rw [hstack] at hcurrentFunction
    simpa [activeFunctionId] using hcurrentFunction
  have hsourceFrame : source.functionId = frame.calleeId :=
    hsourceFunction.trans hinstructionFrame
  have hcalleeIndexed := analyzed_functionById_indexed hanalysis hcallee
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
  have hframeReturnSink : frame.returnLabel = sink :=
    hframeReturn.trans hcalleeReturn
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
    intro hpublic
    apply hframeReturnNonpublic
    rw [hpublic] at hreturnToDestination
    exact eq_public_of_flowsTo_public hreturnToDestination

/-- Constructor-complete local rule for an invocation-private activation.  The proof-only
    prefix includes the invocation's own entry frame, so a successful final output pops the last
    prefix frame and reaches the genuine caller stack. -/
theorem verified_private_invocation_step_preserves_prefix
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine callerSpine privatePrefix : List CallFrame}
    {entryFrame : CallFrame} {state : State} {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlive : ActivationLive spine state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : labelAt analysis.labels (activeFunctionId root spine) ≠ .pub)
    (hspine : spine = entryFrame :: callerSpine)
    (hstack : state.callStack = privatePrefix ++ callerSpine) :
    let next := step (rawSemanticProgram program analysis) state
    ∃ nextPrefix,
      next.state.callStack = nextPrefix ++ callerSpine ∧
        publicProjection (rawSemanticProgram program analysis)
            (restoreFrameStack next.state nextPrefix) =
          publicProjection (rawSemanticProgram program analysis)
            (restoreFrameStack state privatePrefix) ∧
        publicBoundaryTrace next.events = [] := by
  let machine := rawSemanticProgram program analysis
  by_cases houtput : instruction.op = .output
  · have hprefixNonempty : privatePrefix ≠ [] := by
      intro hempty
      subst privatePrefix
      obtain ⟨nested, hliveStack⟩ := hlive
      rw [hspine] at hliveStack
      have hlength := congrArg List.length (hstack.symm.trans hliveStack)
      simp only [List.nil_append, List.length_append, List.length_cons] at hlength
      omega
    obtain ⟨frame, rest, rfl⟩ := List.exists_cons_of_ne_nil hprefixNonempty
    have hstateStack : state.callStack = frame :: (rest ++ callerSpine) := by
      simpa using hstack
    have hisolated := verified_private_invocation_output_top_frame_isolated
      hjudgment hanalysis hactive hlive hlookup houtput hnonpublic hstateStack
    obtain ⟨nextPrefix, _, hnextStack, hprojection, hboundary⟩ :=
      private_output_step_preserves_prefix (machine := machine) (root := root)
        hactive hlookup houtput hstateStack hisolated
    exact ⟨nextPrefix, hnextStack, hprojection, hboundary⟩
  · have hrawNonpublic := private_invocation_nonoutput_raw_block_nonpublic hanalysis
      hactive hlive hlookup hnonpublic houtput
    by_cases hcall : instruction.op = .call
    · obtain ⟨nextPrefix, hnextStack, hprojection, hboundary⟩ :=
        verified_nonpublic_call_step_preserves_prefix hjudgment hanalysis hactive hlookup
          hrawNonpublic (Or.inl hcall) privatePrefix callerSpine hstack
      exact ⟨nextPrefix, hnextStack, hprojection, hboundary⟩
    · by_cases hclosure : instruction.op = .closure
      · obtain ⟨nextPrefix, hnextStack, hprojection, hboundary⟩ :=
          verified_nonpublic_call_step_preserves_prefix hjudgment hanalysis hactive hlookup
            hrawNonpublic (Or.inr hclosure) privatePrefix callerSpine hstack
        exact ⟨nextPrefix, hnextStack, hprojection, hboundary⟩
      · have hstate : instruction.op = .stateWrite →
            let offset := (immediateOperands machine instruction).head?.getD 0
            0 ≤ offset → stateLabelAt machine (UInt32.ofNat offset.toNat) ≠ .pub := by
          intro hwrite
          exact verified_private_stateWrite_runtime_sink hjudgment hanalysis hlookup
            hwrite hrawNonpublic
        have hlocal := verified_nonoutput_noncall_nonpublic_step_preserves_prefix
          hjudgment hanalysis hactive hlookup hrawNonpublic hcall hclosure houtput
          privatePrefix callerSpine hstack hstate
        exact ⟨privatePrefix, hlocal.1, hlocal.2.1, hlocal.2.2⟩

/-- Fold the local invocation rule over one actual finite prefix.  The initial proof-only prefix
    is exactly the genuine entry frame; the returned prefix records nested calls still live at
    the selected endpoint.  Public-release silence is derived from the same strict-prefix facts,
    so no independently chosen existential length is involved. -/
theorem verified_private_invocation_prefix_preservation
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine callerSpine : List CallFrame} {entryFrame : CallFrame}
    {length : Nat} {start : State}
    (hstartStack : start.callStack = spine)
    (hspine : spine = entryFrame :: callerSpine)
    (hnonpublic : labelAt analysis.labels (activeFunctionId root spine) ≠ .pub)
    (hprivate : ∀ elapsed, elapsed < length →
      ActiveState (rawSemanticProgram program analysis) root
          (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
        ActivationLive spine
          (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
        ∃ instruction,
          (rawSemanticProgram program analysis).instructions[
              (runPrefix (rawSemanticProgram program analysis) elapsed start).state.pc]? =
            some instruction) :
    ∃ endPrefix,
      (runPrefix (rawSemanticProgram program analysis) length start).state.callStack =
          endPrefix ++ callerSpine ∧
        publicProjection (rawSemanticProgram program analysis)
            (restoreFrameStack
              (runPrefix (rawSemanticProgram program analysis) length start).state endPrefix) =
          publicProjection (rawSemanticProgram program analysis)
            (restoreFrameStack start [entryFrame]) ∧
        (∀ elapsed, elapsed < length →
          publicBoundaryTrace
              (step (rawSemanticProgram program analysis)
                (runPrefix (rawSemanticProgram program analysis) elapsed start).state).events =
            []) ∧
        PublicReleaseSilentSegment (rawSemanticProgram program analysis) length start := by
  let machine := rawSemanticProgram program analysis
  have hprefix : ∀ elapsed, elapsed ≤ length →
      ∃ privatePrefix,
        (runPrefix machine elapsed start).state.callStack =
            privatePrefix ++ callerSpine ∧
          publicProjection machine
              (restoreFrameStack (runPrefix machine elapsed start).state privatePrefix) =
            publicProjection machine (restoreFrameStack start [entryFrame]) := by
    intro elapsed helapsed
    induction elapsed with
    | zero =>
        refine ⟨[entryFrame], ?_, rfl⟩
        change start.callStack = [entryFrame] ++ callerSpine
        simpa [hspine] using hstartStack
    | succ previous ih =>
        have hpreviousLe : previous ≤ length := by omega
        have hpreviousStrict : previous < length := by omega
        obtain ⟨privatePrefix, hstack, hprojection⟩ := ih hpreviousLe
        obtain ⟨hactive, hlive, instruction, hlookup⟩ :=
          hprivate previous hpreviousStrict
        obtain ⟨nextPrefix, hnextStack, hnextProjection, _⟩ :=
          verified_private_invocation_step_preserves_prefix hjudgment hanalysis
            hactive hlive hlookup hnonpublic hspine (by simpa [machine] using hstack)
        have hnextState :
            (runPrefix machine (previous + 1) start).state =
              (step machine (runPrefix machine previous start).state).state := by
          have hadd := congrArg StepResult.state
            (ReleaseSynchronization.runPrefix_add machine previous 1 start)
          simpa [runPrefix] using hadd
        refine ⟨nextPrefix, ?_, ?_⟩
        · rw [hnextState]
          exact hnextStack
        · rw [hnextState]
          exact hnextProjection.trans hprojection
  obtain ⟨endPrefix, hendStack, hendProjection⟩ := hprefix length le_rfl
  refine ⟨endPrefix, hendStack, hendProjection, ?_, ?_⟩
  · intro elapsed helapsed
    obtain ⟨privatePrefix, hstack, _⟩ := hprefix elapsed (Nat.le_of_lt helapsed)
    obtain ⟨hactive, hlive, instruction, hlookup⟩ := hprivate elapsed helapsed
    obtain ⟨_, _, _, hboundary⟩ :=
      verified_private_invocation_step_preserves_prefix hjudgment hanalysis
        hactive hlive hlookup hnonpublic hspine (by simpa [machine] using hstack)
    exact hboundary
  · exact verified_private_invocation_publicReleaseSilentSegment hanalysis hnonpublic
      hprivate

/-- Production bridge from the verifier's independently sized invocation segment to frame-
    restored Public preservation at its genuine return.  The existential `exitStep` is shared by
    projection preservation, boundary silence, and Public-release silence. -/
theorem v9_verified_successful_private_invocation_prefix_restoration
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {steps : Nat} {start : State} {result : StepResult}
    {spine : List CallFrame}
    (hreachable : ReachableFromRoot (rawSemanticProgram program analysis) root start)
    (hexecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root steps start result)
    (hstartStack : start.callStack = spine) (hspine : spine ≠ [])
    (hnonpublic : labelAt analysis.labels (activeFunctionId root spine) ≠ .pub) :
    ∃ exitStep frame rest output,
      0 < exitStep ∧ exitStep < steps ∧ spine = frame :: rest ∧
        (runPrefix (rawSemanticProgram program analysis) (exitStep - 1) start).state.callStack =
          spine ∧
        (rawSemanticProgram program analysis).instructions[
          (runPrefix (rawSemanticProgram program analysis) (exitStep - 1) start).state.pc]? =
            some output ∧
        output.functionId = activeFunctionId root spine ∧ output.op = .output ∧
        (runPrefix (rawSemanticProgram program analysis) exitStep start).state.callStack = rest ∧
        (runPrefix (rawSemanticProgram program analysis) exitStep start).state.pc =
          frame.returnPc ∧
        ReachableFromRoot (rawSemanticProgram program analysis) root
          (runPrefix (rawSemanticProgram program analysis) exitStep start).state ∧
        publicProjection (rawSemanticProgram program analysis)
            (runPrefix (rawSemanticProgram program analysis) exitStep start).state =
          publicProjection (rawSemanticProgram program analysis)
            (restoreFrameStack start [frame]) ∧
        (∀ earlier, earlier < exitStep →
          publicBoundaryTrace
              (step (rawSemanticProgram program analysis)
                (runPrefix (rawSemanticProgram program analysis) earlier start).state).events =
            []) ∧
        PublicReleaseSilentSegment (rawSemanticProgram program analysis) exitStep start := by
  let machine := rawSemanticProgram program analysis
  have hjudgment := v9_occurrence_verifier_sound hverified
  obtain ⟨exitStep, frame, rest, output, hexitPositive, hexitBound, hspineEq,
    hbeforeStack, houtputLookup, houtputFunction, houtput, hendStack, hendPc,
    hendReachable, hstrict⟩ :=
    v9_verified_successful_private_invocation_segment hverified hanalysis hreachable
      hexecution hstartStack hspine hnonpublic
  have hprivate : ∀ earlier, earlier < exitStep →
      ActiveState machine root (runPrefix machine earlier start).state ∧
        ActivationLive spine (runPrefix machine earlier start).state ∧
        ∃ instruction,
          machine.instructions[(runPrefix machine earlier start).state.pc]? = some instruction := by
    intro earlier hearlier
    obtain ⟨_, hactive, hlive, instruction, hlookup, _, _⟩ := hstrict earlier hearlier
    exact ⟨hactive, hlive, instruction, hlookup⟩
  obtain ⟨endPrefix, hfoldStack, hprojection, hboundary, hreleaseSilent⟩ :=
    verified_private_invocation_prefix_preservation hjudgment hanalysis hstartStack
      hspineEq hnonpublic hprivate
  have hendPrefix : endPrefix = [] := by
    have hlength := congrArg List.length (hfoldStack.symm.trans hendStack)
    simp only [List.length_append] at hlength
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst endPrefix
  refine ⟨exitStep, frame, rest, output, hexitPositive, hexitBound, hspineEq,
    hbeforeStack, houtputLookup, houtputFunction, houtput, hendStack, hendPc,
    hendReachable, ?_, hboundary, hreleaseSilent⟩
  simpa only [restoreFrameStack] using hprojection

private theorem call_or_closure_step_public_traces_nil
    {machine : SemanticProgram} {root : UInt32} {state : State}
    {instruction : Instruction}
    (hactive : ActiveState machine root state)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hoperation : instruction.op = .call ∨ instruction.op = .closure)
    {callee : Function}
    (hcallee : instructionCallee? machine state instruction = some callee)
    (hguard : ¬((callArguments machine state instruction).length !=
        callee.parameterCells.size ||
      !callLabelsOK machine instruction callee (callArguments machine state instruction))) :
    publicBoundaryTrace (step machine state).events = [] ∧
      publicReleaseTrace machine (step machine state).events = [] := by
  rcases hoperation with hcall | hclosure
  · simp [step, hactive.notHalted, hactive.notTrapped, hlookup, hcall, callStep,
      hcallee, hguard,
      publicBoundaryTrace, publicReleaseTrace, ReleaseSynchronization.releaseTrace,
      Semantic.releaseEvents]
  · simp [step, hactive.notHalted, hactive.notTrapped, hlookup, hclosure, callStep,
      hcallee, hguard,
      publicBoundaryTrace, publicReleaseTrace, ReleaseSynchronization.releaseTrace,
      Semantic.releaseEvents]

/-- A progress-ready unary package beginning at the actual caller state and ending immediately
    after the private invocation's genuine return.  `exitStep` is measured from the post-call
    state; the raw caller segment therefore has exact length `exitStep + 1`. -/
structure VerifiedPrivateInvocationCallSegment
    (program : V9.Program) (analysis : Analysis) (root : UInt32) (remaining : Nat)
    (start finish : State) (instruction : Instruction) (callee : Function)
    (exitStep : Nat) : Prop where
  lookup : (rawSemanticProgram program analysis).instructions[start.pc]? = some instruction
  operation : instruction.op = .call ∨ instruction.op = .closure
  resolved : instructionCallee? (rawSemanticProgram program analysis) start instruction =
    some callee
  invocationPrivate : labelAt analysis.labels callee.id ≠ .pub
  exitPositive : 0 < exitStep
  exitBound : exitStep < remaining
  finish_eq : finish =
    (runPrefix (rawSemanticProgram program analysis) (exitStep + 1) start).state
  silent : PublicSilentSegment (rawSemanticProgram program analysis) (exitStep + 1)
    start finish
  releaseSilent : PublicReleaseSilentSegment (rawSemanticProgram program analysis)
    (exitStep + 1) start
  finishStack : finish.callStack = start.callStack
  finishPc : finish.pc = start.pc + 1
  reachable : ReachableFromRoot (rawSemanticProgram program analysis) root finish
  active : ActiveState (rawSemanticProgram program analysis) root finish

/-- Package one actual nontrapping caller step plus its independently sized private invocation.
    The caller supplies only the verifier-derived classification that the resolved callee is
    private; the callee, frame, arguments, and return are all extracted from raw execution. -/
theorem v9_verified_successful_private_invocation_call_segment
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {remaining : Nat} {start : State} {result : StepResult}
    {instruction : Instruction}
    (hreachable : ReachableFromRoot (rawSemanticProgram program analysis) root start)
    (hexecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root (remaining + 1) start result)
    (hremaining : 0 < remaining)
    (hlookup : (rawSemanticProgram program analysis).instructions[start.pc]? =
      some instruction)
    (hoperation : instruction.op = .call ∨ instruction.op = .closure)
    (hprivate : ∀ callee,
      instructionCallee? (rawSemanticProgram program analysis) start instruction = some callee →
        labelAt analysis.labels callee.id ≠ .pub) :
    ∃ finish callee exitStep,
      VerifiedPrivateInvocationCallSegment program analysis root remaining start finish
        instruction callee exitStep := by
  let machine := rawSemanticProgram program analysis
  change machine.instructions[start.pc]? = some instruction at hlookup
  have hstartActive := hexecution.start_active
  have hpostActiveRaw := hexecution.reached_active (elapsed := 1) (by omega)
  have hpostActive : ActiveState machine root (step machine start).state := by
    simpa only [runPrefix] using hpostActiveRaw
  obtain ⟨callee, hcallee, hguard⟩ := nontrapping_call_step_shape
    (by simpa [machine] using hlookup) hoperation
    ⟨hstartActive.notHalted, hstartActive.notTrapped⟩ hpostActive.notTrapped
  let frame := privateCallFrame start instruction callee
  let post := privateCallEntry machine start instruction callee
    (callArguments machine start instruction)
  have hpostEq : (step machine start).state = post := by
    rcases hoperation with hcall | hclosure
    · simp [step, hstartActive.notHalted, hstartActive.notTrapped, hlookup, hcall,
        callStep, hcallee, hguard, post, privateCallEntry, privateCallFrame]
    · simp [step, hstartActive.notHalted, hstartActive.notTrapped, hlookup, hclosure,
        callStep, hcallee, hguard, post, privateCallEntry, privateCallFrame]
  have hpostExecutionRaw := hexecution.drop (elapsed := 1) (by omega)
  have hpostExecution : SuccessfulExecution machine root remaining post
      (runPrefix machine remaining post) := by
    change SuccessfulExecution machine root remaining (step machine start).state
      (runPrefix machine remaining (step machine start).state) at hpostExecutionRaw
    rw [hpostEq] at hpostExecutionRaw
    exact hpostExecutionRaw
  have hpostReachable : ReachableFromRoot machine root post := by
    have hreach := reachableFromRoot_runPrefix_state hreachable 1
    change ReachableFromRoot machine root (runPrefix machine 1 start).state at hreach
    simpa only [runPrefix, hpostEq] using hreach
  have hpostStack : post.callStack = frame :: start.callStack := by
    simp [post, frame]
  have hpostNonempty : post.callStack ≠ [] := by simp [hpostStack]
  have hcalleePrivate : labelAt analysis.labels callee.id ≠ .pub :=
    hprivate callee (by simpa [machine] using hcallee)
  have hpostInvocationPrivate :
      labelAt analysis.labels (activeFunctionId root post.callStack) ≠ .pub := by
    simpa [hpostStack, frame, privateCallFrame, activeFunctionId] using hcalleePrivate
  obtain ⟨exitStep, returnedFrame, callerStack, output, hexitPositive, hexitBound,
    hspineEq, hbeforeStack, houtputLookup, houtputFunction, houtput,
    hendStack, hendPc, hendReachable, hendProjection, hboundary, hreleaseSilent⟩ :=
    v9_verified_successful_private_invocation_prefix_restoration hverified hanalysis
      hpostReachable hpostExecution rfl hpostNonempty hpostInvocationPrivate
  have hframeEq : returnedFrame = frame := by
    have hcons : returnedFrame :: callerStack = frame :: start.callStack :=
      hspineEq.symm.trans hpostStack
    exact List.cons.inj hcons |>.1
  have hcallerStackEq : callerStack = start.callStack := by
    have hcons : returnedFrame :: callerStack = frame :: start.callStack :=
      hspineEq.symm.trans hpostStack
    exact List.cons.inj hcons |>.2
  subst returnedFrame
  subst callerStack
  let finish := (runPrefix machine (exitStep + 1) start).state
  have hshiftState : finish = (runPrefix machine exitStep post).state := by
    have hadd := congrArg StepResult.state
      (ReleaseSynchronization.runPrefix_add machine 1 exitStep start)
    have hsum : 1 + exitStep = exitStep + 1 := by omega
    rw [hsum] at hadd
    simpa only [runPrefix, hpostEq, finish] using hadd
  have hentryProjection :
      publicProjection machine (restoreFrameStack post [frame]) =
        publicProjection machine start := by
    simpa [post, frame] using
      (publicProjection_privateCallEntry_restore_prefix machine start instruction callee
        (callArguments machine start instruction) [])
  have hendProjectionFull : publicProjection machine finish =
      publicProjection machine start := by
    rw [hshiftState]
    exact hendProjection.trans hentryProjection
  have hcallTraces := call_or_closure_step_public_traces_nil hstartActive hlookup hoperation
    hcallee hguard
  have hprefixShift : ∀ offset,
      (runPrefix machine (offset + 1) start).state = (runPrefix machine offset post).state := by
    intro offset
    have hadd := congrArg StepResult.state
      (ReleaseSynchronization.runPrefix_add machine 1 offset start)
    have hsum : 1 + offset = offset + 1 := by omega
    rw [hsum] at hadd
    simpa only [runPrefix, hpostEq] using hadd
  have hsilent : ∀ elapsed, elapsed < exitStep + 1 →
      publicBoundaryTrace
          (step machine (runPrefix machine elapsed start).state).events = [] := by
    intro elapsed helapsed
    cases elapsed with
    | zero => simpa only [runPrefix] using hcallTraces.1
    | succ offset =>
        rw [hprefixShift offset]
        exact hboundary offset (by omega)
  have hreleaseFull : PublicReleaseSilentSegment machine (exitStep + 1) start := by
    intro elapsed helapsed
    cases elapsed with
    | zero => simpa only [runPrefix] using hcallTraces.2
    | succ offset =>
        rw [hprefixShift offset]
        exact hreleaseSilent offset (by omega)
  have hfinishReachable : ReachableFromRoot machine root finish := by
    rw [hshiftState]
    exact hendReachable
  have hfinishActive : ActiveState machine root finish := by
    rw [hshiftState]
    exact hpostExecution.reached_active hexitBound
  refine ⟨finish, callee, exitStep, hlookup, hoperation,
    (by simpa [machine] using hcallee), hcalleePrivate, hexitPositive, hexitBound, rfl,
    ?_, hreleaseFull, ?_, ?_, hfinishReachable, hfinishActive⟩
  · exact ⟨rfl, hsilent, hendProjectionFull⟩
  · rw [hshiftState]
    exact hcallerStackEq
  · rw [hshiftState, hendPc]
    simp [frame, privateCallFrame]

/-- Two independently sized private invocations return to the same genuine caller
    continuation.  Unary segment restoration plus the original complete Public-low relation
    reconstructs the full endpoint relation, including frame payloads and immutable input
    streams.  Successful invocation segments cannot end at a synthetic return: each package
    stops strictly before the enclosing successful execution finishes and is therefore active. -/
theorem paired_private_invocation_call_continuation
    {program : V9.Program} {analysis : Analysis} {root : UInt32}
    {leftRemaining rightRemaining : Nat} {left right leftFinish rightFinish : State}
    {instruction : Instruction} {leftCallee rightCallee : Function}
    {leftExitStep rightExitStep : Nat}
    (hstartLow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hleft : VerifiedPrivateInvocationCallSegment program analysis root leftRemaining
      left leftFinish instruction leftCallee leftExitStep)
    (hright : VerifiedPrivateInvocationCallSegment program analysis root rightRemaining
      right rightFinish instruction rightCallee rightExitStep) :
    MatchingCurrentContinuation (rawSemanticProgram program analysis) root (left.pc + 1)
      leftFinish rightFinish := by
  let machine := rawSemanticProgram program analysis
  have hleftStreams : leftFinish.externalInputs = left.externalInputs := by
    rw [hleft.finish_eq]
    exact PublicRegionSecurity.runPrefix_preserves_external_inputs machine
      (leftExitStep + 1) left
  have hrightStreams : rightFinish.externalInputs = right.externalInputs := by
    rw [hright.finish_eq]
    exact PublicRegionSecurity.runPrefix_preserves_external_inputs machine
      (rightExitStep + 1) right
  have hstreams : leftFinish.externalInputs = rightFinish.externalInputs :=
    hleftStreams.trans
      ((publicLow_storage_facts hstartLow).2.2.trans hrightStreams.symm)
  have hprojection : publicProjection machine leftFinish =
      publicProjection machine rightFinish :=
    hleft.silent.endProjection.trans
      ((publicProjection_eq_of_low hstartLow).trans hright.silent.endProjection.symm)
  have hpc : leftFinish.pc = rightFinish.pc := by
    rw [hleft.finishPc, hright.finishPc, hstartLow.1]
  have hstack : CallStackPublicEquivalent machine leftFinish.callStack
      rightFinish.callStack := by
    rw [hleft.finishStack, hright.finishStack]
    exact hstartLow.2.2.2.1
  have hnextLow : PublicLowEquivalent machine leftFinish rightFinish :=
    publicLowEquivalent_of_projection_and_control hleft.active.wellFormed.1
      hright.active.wellFormed.1 hstreams hprojection hpc
      (hleft.active.notHalted.trans hright.active.notHalted.symm)
      (hleft.active.notTrapped.trans hright.active.notTrapped.symm) hstack
  have hparentLeft : left.pc + 1 = leftFinish.pc := hleft.finishPc.symm
  have hparentRight : left.pc + 1 = rightFinish.pc := by
    rw [hright.finishPc, hstartLow.1]
  obtain ⟨current, hcurrentLookup, _⟩ := hleft.active.currentInstruction
  have hrightLookup : machine.instructions[rightFinish.pc]? = some current := by
    rw [← hpc]
    exact hcurrentLookup
  exact ⟨hnextLow, hleft.reachable, hright.reachable, hleft.active, hright.active,
    hparentLeft, hparentRight, current, hcurrentLookup, hrightLookup⟩

private theorem successful_call_has_positive_tail
    {machine : SemanticProgram} {root : UInt32} {tail : Nat}
    {start : State} {result : StepResult} {instruction : Instruction} {callee : Function}
    (hexecution : SuccessfulExecution machine root (tail + 1) start result)
    (hlookup : machine.instructions[start.pc]? = some instruction)
    (hoperation : instruction.op = .call ∨ instruction.op = .closure)
    (hcallee : instructionCallee? machine start instruction = some callee)
    (hguard : ¬((callArguments machine start instruction).length !=
        callee.parameterCells.size ||
      !callLabelsOK machine instruction callee (callArguments machine start instruction))) :
    0 < tail := by
  have hactive := hexecution.start_active
  have hnotHalted : (step machine start).state.halted = false := by
    rcases hoperation with hcall | hclosure
    · simp [step, hactive.notHalted, hactive.notTrapped, hlookup, hcall, callStep,
        hcallee, hguard]
    · simp [step, hactive.notHalted, hactive.notTrapped, hlookup, hclosure, callStep,
        hcallee, hguard]
  by_contra htail
  have hzero : tail = 0 := Nat.eq_zero_of_not_pos htail
  subst tail
  have hstep : step machine start = result := by
    simpa [runPrefix] using hexecution.run
  rw [hstep] at hnotHalted
  rw [hexecution.halted] at hnotHalted
  contradiction

/-- Progress-ready paired call/closure classification for the production dispatcher.

    If both raw states select the same callee, the existing constructor-local matcher consumes
    exactly one step.  If they select different callees, V9's checked selector influence proves
    that both invocations are private; each real call entry is then composed with its independently
    sized successful invocation and genuine return.  The two endpoints are active at the same
    actual caller continuation and satisfy the complete `PublicLowEquivalent` relation.  Public
    release suffix equality is cancelled only across the two proved release-silent prefixes; raw
    release events remain untouched in the complete machine traces. -/
theorem publicExecutionProgress_of_verified_call_or_closure
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {leftTail rightTail : Nat} {left right : State}
    {leftResult rightResult : StepResult} {instruction : Instruction}
    (hleftSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root left)
    (hrightSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hoperation : instruction.op = .call ∨ instruction.op = .closure)
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
  change machine.instructions[left.pc]? = some instruction at hlookup
  change PublicLowEquivalent machine left right at hlow
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  have hleftNext := successfulExecution_first_successor_not_trapped hleftExecution
  have hrightNext := successfulExecution_first_successor_not_trapped hrightExecution
  obtain ⟨leftCallee, hleftCallee, hleftGuard⟩ := nontrapping_call_step_shape
    hlookup hoperation ⟨hleftSync.active.notHalted, hleftSync.active.notTrapped⟩ hleftNext
  obtain ⟨rightCallee, hrightCallee, hrightGuard⟩ := nontrapping_call_step_shape
    hrightLookup hoperation ⟨hrightSync.active.notHalted, hrightSync.active.notTrapped⟩ hrightNext
  have hnotRelease : instruction.op ≠ .release := by
    exact hoperation.elim (fun hcall => by simp [hcall]) (fun hclosure => by simp [hclosure])
  have hnotReleaseCT : instruction.op ≠ .releaseCT := by
    exact hoperation.elim (fun hcall => by simp [hcall]) (fun hclosure => by simp [hclosure])
  by_cases hsame : leftCallee = rightCallee
  · subst rightCallee
    have hjudgment := v9_occurrence_verifier_sound hverified
    have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
    have hmatching := matching_call_step_same_callee hstatic hleftSync.active.wellFormed
      hrightSync.active.wellFormed hlow hlookup hoperation
      ⟨hleftSync.active.notHalted, hleftSync.active.notTrapped⟩
      ⟨hrightSync.active.notHalted, hrightSync.active.notTrapped⟩
      hleftCallee hrightCallee hleftGuard hrightGuard
    have hreleaseTail := public_release_tail_of_shared_nonrelease hlow hlookup
      hnotRelease hnotReleaseCT hrelease
    exact publicExecutionProgress_of_reachable_matching_step hleftSync.reachable
      hrightSync.reachable hleftExecution hrightExecution hmatching.1 hmatching.2 hreleaseTail
  · have hjudgment := v9_occurrence_verifier_sound hverified
    obtain ⟨hleftPrivate, hrightPrivate⟩ :=
      different_resolved_call_callees_are_private hjudgment hanalysis hlow hlookup hoperation
        hleftCallee hrightCallee hsame
    have hleftPositive : 0 < leftTail :=
      successful_call_has_positive_tail hleftExecution hlookup hoperation hleftCallee hleftGuard
    have hrightPositive : 0 < rightTail :=
      successful_call_has_positive_tail hrightExecution hrightLookup hoperation hrightCallee
        hrightGuard
    obtain ⟨leftFinish, packagedLeftCallee, leftExitStep, hleftSegment⟩ :=
      v9_verified_successful_private_invocation_call_segment hverified hanalysis
        hleftSync.reachable hleftExecution hleftPositive hlookup hoperation (by
          intro candidate hcandidate
          have heq : candidate = leftCallee :=
            Option.some.inj (hcandidate.symm.trans hleftCallee)
          simpa [heq] using hleftPrivate)
    obtain ⟨rightFinish, packagedRightCallee, rightExitStep, hrightSegment⟩ :=
      v9_verified_successful_private_invocation_call_segment hverified hanalysis
        hrightSync.reachable hrightExecution hrightPositive hrightLookup hoperation (by
          intro candidate hcandidate
          have heq : candidate = rightCallee :=
            Option.some.inj (hcandidate.symm.trans hrightCallee)
          simpa [heq] using hrightPrivate)
    have hcontinuation := paired_private_invocation_call_continuation hlow hleftSegment
      hrightSegment
    have hleftLengthBound : leftExitStep + 1 < leftTail + 1 := by
      have hexit := hleftSegment.exitBound
      omega
    have hrightLengthBound : rightExitStep + 1 < rightTail + 1 := by
      have hexit := hrightSegment.exitBound
      omega
    have hleftSum :
        leftExitStep + 1 + (leftTail + 1 - (leftExitStep + 1)) = leftTail + 1 :=
      Nat.add_sub_of_le (Nat.le_of_lt hleftLengthBound)
    have hrightSum :
        rightExitStep + 1 + (rightTail + 1 - (rightExitStep + 1)) = rightTail + 1 :=
      Nat.add_sub_of_le (Nat.le_of_lt hrightLengthBound)
    have hreleaseDecomposed : publicReleaseTrace machine
          (runPrefix machine
            (leftExitStep + 1 + (leftTail + 1 - (leftExitStep + 1))) left).events =
        publicReleaseTrace machine
          (runPrefix machine
            (rightExitStep + 1 + (rightTail + 1 - (rightExitStep + 1))) right).events := by
      simpa only [hleftSum, hrightSum] using hrelease
    have hreleaseTail := public_release_suffix_eq_after_private_regions
      hleftSegment.silent hrightSegment.silent hleftSegment.releaseSilent
        hrightSegment.releaseSilent hreleaseDecomposed
    exact publicExecutionProgress_of_private_segments (by omega) (by omega)
      hleftLengthBound hrightLengthBound hleftSegment.silent hrightSegment.silent
      ⟨hleftSegment.reachable, hleftSegment.active⟩
      ⟨hrightSegment.reachable, hrightSegment.active⟩ hcontinuation.low
      hleftExecution hrightExecution hreleaseTail

end LambdaSigil.Combined.V9.PublicPrivateInvocationSecurity
