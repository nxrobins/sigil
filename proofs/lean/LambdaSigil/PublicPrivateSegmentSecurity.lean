import LambdaSigil.PublicLocalSecurity
import LambdaSigil.PublicRegionConvergence

/-!
# Private-segment preservation

This module connects the verifier-owned activation anchors and finite raw prefixes from
`PublicRegionConvergence` to the unary, constructor-local preservation facts in
`PublicLocalSecurity`.

V9's mandatory `LocalDestinationSafe` rule makes this fold apply to private `release` and
`releaseCT` instructions as well: a non-Public occurrence cannot write a Public destination.
Their actual release events remain in the complete trace.  This module proves Public projection
preservation and Public output/boundary silence only; it never claims release-trace silence.
-/

namespace LambdaSigil.Combined.V9.PublicPrivateSegmentSecurity

open Semantic OccurrenceDataflowInvocation OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity Semantic.PublicFrameSecurity
open Semantic.PublicRegionConvergence
open Semantic.PublicReleaseSynchronization
open PublicLocalSecurity
open OccurrenceRegions OccurrenceTransfer DecodedOccurrence

private theorem eq_public_of_flowsTo_public {label : Label}
    (hflow : label.flowsTo .pub = true) : label = .pub := by
  cases label <;> simp_all [Label.flowsTo, Label.rank]

private theorem labelFlows_trans {first middle last : Label}
    (hfirst : first.flowsTo middle = true) (hlast : middle.flowsTo last = true) :
    first.flowsTo last = true := by
  cases first <;> cases middle <;> cases last <;>
    simp_all [Label.flowsTo, Label.rank]

private theorem activeFunctionId_append_outer (root : UInt32)
    (inner : List CallFrame) (outer : CallFrame) (spine : List CallFrame) :
    activeFunctionId root (inner ++ outer :: spine) = activeFunctionId outer.calleeId inner := by
  cases inner <;> simp [activeFunctionId]

/-- A private activation anchor is a lower bound for the raw occurrence of every non-return
    instruction.  Internal returns are intentionally excluded: their root-return contract may
    raise the raw block label to Public even though the step is an internal, boundary-silent pop.
-/
theorem private_anchor_nonoutput_raw_block_nonpublic
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine : List CallFrame} {anchor : Nat} {state : State}
    {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hanchor : ActivationAnchor spine anchor state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub)
    (hnonoutput : instruction.op ≠ .output) :
    instruction.blockLabel ≠ .pub := by
  cases hanchor with
  | current hstack =>
      have hflow := local_occurrence_flows_to_raw_block_of_lookup hlookup hnonoutput
      intro hpublic
      have hlocalPublic :
          localOccurrenceAt analysis.localAnalysis.frontiers state.pc = .pub :=
        eq_public_of_flowsTo_public (by simpa [hpublic] using hflow)
      exact hnonpublic hlocalPublic
  | descendant inner outer hstack =>
      have hchain := hactive.frameChain
      rw [hstack] at hchain
      obtain ⟨houter, hinner⟩ := frameChain_split_activation hchain
      have hanchorToOuter :=
        coherent_frame_local_occurrence_flows_to_callee hanalysis houter
      have houterToActive := frameChain_root_occurrence_flows_to_active hanalysis hinner
      have hanchorToActive := labelFlows_trans hanchorToOuter houterToActive
      obtain ⟨current, hcurrentLookup, hcurrentFunction⟩ := hactive.currentInstruction
      have hcurrentEq : current = instruction := by
        rw [hlookup] at hcurrentLookup
        exact Option.some.inj hcurrentLookup.symm
      subst current
      have hactiveEq : activeFunctionId root state.callStack =
          activeFunctionId outer.calleeId inner := by
        rw [hstack]
        exact activeFunctionId_append_outer root inner outer spine
      have hactiveToBlock :=
        invocation_occurrence_flows_to_raw_block_of_lookup hlookup hnonoutput
      have hanchorToBlock :
          (localOccurrenceAt analysis.localAnalysis.frontiers
            (outer.returnPc - 1)).flowsTo instruction.blockLabel = true := by
        apply labelFlows_trans hanchorToActive
        rw [← hactiveEq, ← hcurrentFunction]
        exact hactiveToBlock
      intro hpublic
      have hanchorPublic :
          localOccurrenceAt analysis.localAnalysis.frontiers (outer.returnPc - 1) = .pub :=
        eq_public_of_flowsTo_public (by simpa [hpublic] using hanchorToBlock)
      exact hnonpublic hanchorPublic

/-- Instruction identifiers are unique in every accepted raw V9 machine, so the immutable
    release-site lookup resolves the exact looked-up instruction rather than an earlier alias.
-/
theorem releaseSiteOccurrence_eq_blockLabel_of_lookup
    {machine : SemanticProgram} {pc : Nat} {instruction : Instruction}
    (hnodup : (machine.instructions.toList.map Instruction.id).Nodup)
    (hlookup : machine.instructions[pc]? = some instruction) :
    releaseSiteOccurrence machine instruction.id = instruction.blockLabel := by
  have hcurrentMem : instruction ∈ machine.instructions :=
    Array.mem_iff_getElem?.mpr ⟨pc, hlookup⟩
  unfold releaseSiteOccurrence
  cases hfind : machine.instructions.find?
      (fun candidate => candidate.id == instruction.id) with
  | none =>
      exact False.elim ((Array.find?_eq_none.mp hfind) instruction hcurrentMem (by simp))
  | some found =>
      have hfoundMem : found ∈ machine.instructions := Array.mem_of_find?_eq_some hfind
      have hfoundId : found.id = instruction.id := by
        simpa using (Array.find?_some hfind)
      obtain ⟨foundPc, hfoundBound, hfoundGet⟩ := Array.mem_iff_getElem.mp hfoundMem
      obtain ⟨hcurrentBound, hcurrentGet⟩ := Array.getElem?_eq_some_iff.mp hlookup
      have hfoundListBound : foundPc < machine.instructions.toList.length := by
        simpa using hfoundBound
      have hcurrentListBound : pc < machine.instructions.toList.length := by
        simpa using hcurrentBound
      have hposition : foundPc = pc := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have hpair := (List.pairwise_iff_getElem.mp
              (List.nodup_iff_pairwise_ne.mp hnodup)) foundPc pc
              (by simpa using hfoundListBound) (by simpa using hcurrentListBound) hlt
          apply hpair
          simp only [List.getElem_map]
          simpa [hfoundGet, hcurrentGet] using hfoundId
        · have hpair := (List.pairwise_iff_getElem.mp
              (List.nodup_iff_pairwise_ne.mp hnodup)) pc foundPc
              (by simpa using hcurrentListBound) (by simpa using hfoundListBound) hgt
          apply hpair
          simp only [List.getElem_map]
          simpa [hfoundGet, hcurrentGet] using hfoundId.symm
      subst foundPc
      have heq : found = instruction := by simpa [hcurrentGet] using hfoundGet.symm
      subst found
      simp [hcurrentGet]

/-- Production-specialized release-site identity. -/
theorem raw_releaseSiteOccurrence_eq_blockLabel
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction) :
    releaseSiteOccurrence (rawSemanticProgram program analysis) instruction.id =
      instruction.blockLabel :=
  releaseSiteOccurrence_eq_blockLabel_of_lookup
    (rawSemanticProgram_instruction_ids_nodup hanalysis) hlookup

/-- A real downgrade at a private raw occurrence remains present in the complete release trace,
    but is absent from the statically filtered Public release subsequence. -/
theorem private_release_step_publicReleaseTrace_nil
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {state : State} {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hoperation : instruction.op = .release ∨ instruction.op = .releaseCT)
    (hnonpublic : instruction.blockLabel ≠ .pub) :
    publicReleaseTrace (rawSemanticProgram program analysis)
      (step (rawSemanticProgram program analysis) state).events = [] := by
  let machine := rawSemanticProgram program analysis
  have hsite := raw_releaseSiteOccurrence_eq_blockLabel hanalysis hlookup
  rcases hoperation with hrelease | hreleaseCT
  · simp [step, hactive.notHalted, hactive.notTrapped, hlookup, hrelease, ordinaryStep,
      instructionEvents, publicReleaseTrace, ReleaseSynchronization.releaseTrace,
      Semantic.releaseEvents, EventKind.eqb, hsite, hnonpublic, Label.eqb]
  · simp [step, hactive.notHalted, hactive.notTrapped, hlookup, hreleaseCT, ordinaryStep,
      instructionEvents, publicReleaseTrace, ReleaseSynchronization.releaseTrace,
      Semantic.releaseEvents, EventKind.eqb, hsite, hnonpublic, Label.eqb]

private theorem verified_private_call_frame_destination_isolated
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {callPc : Nat} {call : Instruction} {frame : CallFrame}
    (hcallLookup : (rawSemanticProgram program analysis).instructions[callPc]? = some call)
    (hcallPrivate : call.blockLabel ≠ .pub)
    (hdestination : call.destination = frame.destination) :
    frame.destination = 0 ∨
      labelAt (rawSemanticProgram program analysis).valueLabels frame.destination ≠ .pub := by
  have hisolated := verified_nonpublic_has_no_public_destination hjudgment hanalysis
    hcallLookup hcallPrivate
  rcases hisolated with hzero | hresult
  · exact Or.inl (hdestination ▸ hzero)
  · right
    have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
    have hwell := instruction_well_formed_of_raw_static_safe hstatic hcallLookup
    intro hpublic
    apply hresult
    exact hwell.2.2.1.trans (by simpa [hdestination] using hpublic)

/-- A nested output's actual top frame came from a verifier-accepted call/closure inside the
    private activation.  The activation anchor flows through the genuine coherent frame chain to
    that originating call, so its destination is zero or statically non-Public. -/
theorem private_anchor_output_top_frame_isolated
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine rest : List CallFrame} {frame : CallFrame}
    {anchor : Nat} {state : State} {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hanchor : ActivationAnchor spine anchor state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? = some instruction)
    (houtput : instruction.op = .output)
    (hnonpublic : localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub)
    (hstack : state.callStack = frame :: (rest ++ spine)) :
    frame.destination = 0 ∨
      labelAt (rawSemanticProgram program analysis).valueLabels frame.destination ≠ .pub := by
  cases hanchor with
  | current hcurrentStack =>
      have hlength := congrArg List.length (hstack.symm.trans hcurrentStack)
      simp at hlength
      omega
  | descendant inner outer hdescStack =>
      have hchain := hactive.frameChain
      rw [hdescStack] at hchain
      obtain ⟨houter, hinner⟩ := frameChain_split_activation hchain
      have hpadded : inner ++ [outer] = frame :: rest := by
        have : (inner ++ [outer]) ++ spine = (frame :: rest) ++ spine := by
          simpa [List.append_assoc] using hdescStack.symm.trans hstack
        exact List.append_cancel_right this
      cases inner with
      | nil =>
          have hparts : outer = frame ∧ rest = [] := by
            simpa using List.cons.inj hpadded
          rcases hparts with ⟨rfl, rfl⟩
          obtain ⟨_, _, call, _, _, _, _, hcallLookup, _, hcallOperation,
            hcallDestination, _, _, _, _, _⟩ := houter
          have hcallNonoutput : call.op ≠ .output := by
            rcases hcallOperation with hcall | hclosure
            · simp [hcall]
            · simp [hclosure]
          have hflow := local_occurrence_flows_to_raw_block_of_lookup hcallLookup
            hcallNonoutput
          have hcallPrivate : call.blockLabel ≠ .pub := by
            intro hpublic
            exact hnonpublic (eq_public_of_flowsTo_public (by simpa [hpublic] using hflow))
          exact verified_private_call_frame_destination_isolated hjudgment hanalysis
            hcallLookup hcallPrivate hcallDestination

      | cons top tail =>
          have hparts : top = frame ∧ tail ++ [outer] = rest := List.cons.inj hpadded
          rcases hparts with ⟨rfl, rfl⟩
          have htop := hinner.1
          have htail := hinner.2
          obtain ⟨_, _, call, _, _, _, _, hcallLookup, hcallFunction, hcallOperation,
            hcallDestination, _, _, _, _, _⟩ := htop
          have hanchorToOuter :=
            coherent_frame_local_occurrence_flows_to_callee hanalysis houter
          have houterToCaller := frameChain_root_occurrence_flows_to_active hanalysis htail
          have hanchorToCaller := labelFlows_trans hanchorToOuter houterToCaller
          have hcallerToCall := invocation_occurrence_flows_to_raw_block_of_lookup
            hcallLookup (by rcases hcallOperation with hcall | hclosure <;> simp_all)
          have hanchorToCall :
              (localOccurrenceAt analysis.localAnalysis.frontiers
                (outer.returnPc - 1)).flowsTo call.blockLabel = true := by
            apply labelFlows_trans hanchorToCaller
            rw [← hcallFunction]
            exact hcallerToCall
          have hcallPrivate : call.blockLabel ≠ .pub := by
            intro hpublic
            exact hnonpublic
              (eq_public_of_flowsTo_public (by simpa [hpublic] using hanchorToCall))
          exact verified_private_call_frame_destination_isolated hjudgment hanalysis
            hcallLookup hcallPrivate hcallDestination

private theorem activationAnchor_activationLive
    {spine : List CallFrame} {anchor : Nat} {state : State}
    (hanchor : ActivationAnchor spine anchor state) : ActivationLive spine state := by
  cases hanchor with
  | current hstack => exact activationLive_current spine state hstack
  | descendant inner outer hstack =>
      exact ⟨inner ++ [outer], by simpa [List.append_assoc] using hstack⟩

private theorem activationContinuationAt_activationLive
    {machine : SemanticProgram} {root : UInt32} {spine : List CallFrame}
    {node : Nat} {state : State}
    (hcontinuation : ActivationContinuationAt machine root spine node state) :
    ActivationLive spine state := by
  rcases hcontinuation with hanchor | ⟨_, hstack, _⟩
  · exact activationAnchor_activationLive hanchor
  · exact activationLive_current spine state hstack

/-- Executing an actual internal output with no private frame above the activation suffix exits
    that activation.  Therefore its live successor cannot still have the same suffix. -/
private theorem active_output_at_spine_next_not_live
    {machine : SemanticProgram} {root : UInt32} {spine : List CallFrame}
    {state : State} {instruction : Instruction}
    (hactive : ActiveState machine root state)
    (hnextActive : ActiveState machine root (step machine state).state)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (houtput : instruction.op = .output)
    (hstack : state.callStack = spine) :
    ¬ ActivationLive spine (step machine state).state := by
  intro hlive
  have htransition := live_step_stack_transition hlookup hactive.notHalted
    hactive.notTrapped hnextActive.notHalted hnextActive.notTrapped
  cases htransition with
  | same _ _ _ hnotReturn => exact hnotReturn houtput
  | push _ _ _ hoperation =>
      rcases hoperation with hcall | hclosure
      · cases houtput.symm.trans hcall
      · cases houtput.symm.trans hclosure
  | pop frame rest hbefore hafter _ _ =>
      obtain ⟨privatePrefix, hliveStack⟩ := hlive
      have hspine : spine = frame :: rest := hstack.symm.trans hbefore
      have hrest : rest = privatePrefix ++ spine := hafter.symm.trans hliveStack
      have hspineLength := congrArg List.length hspine
      have hrestLength := congrArg List.length hrest
      simp only [List.length_cons, List.length_append] at hspineLength hrestLength
      omega

/-- If a verified private output has a live successor in the same activation, then it necessarily
    returns through an actual private frame above the activation suffix.  Coherent frame
    provenance and `LocalDestinationSafe` make that frame's destination invisible to the Public
    projection. -/
theorem private_anchor_output_prefix_isolated
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine privatePrefix : List CallFrame}
    {anchor : Nat} {state : State} {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hnextActive : ActiveState (rawSemanticProgram program analysis) root
      (step (rawSemanticProgram program analysis) state).state)
    (hnextLive : ActivationLive spine
      (step (rawSemanticProgram program analysis) state).state)
    (hanchor : ActivationAnchor spine anchor state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (houtput : instruction.op = .output)
    (hnonpublic : localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub)
    (hstack : state.callStack = privatePrefix ++ spine) :
    ∃ frame rest, privatePrefix = frame :: rest ∧
      (frame.destination = 0 ∨
        labelAt (rawSemanticProgram program analysis).valueLabels frame.destination ≠ .pub) := by
  have hprefixNonempty : privatePrefix ≠ [] := by
    intro hnil
    subst privatePrefix
    exact active_output_at_spine_next_not_live hactive hnextActive hlookup houtput
      (by simpa using hstack) hnextLive
  rcases List.exists_cons_of_ne_nil hprefixNonempty with ⟨frame, rest, rfl⟩
  refine ⟨frame, rest, rfl, ?_⟩
  exact private_anchor_output_top_frame_isolated hjudgment hanalysis hactive hanchor
    hlookup houtput hnonpublic (by simpa using hstack)

/-- Exact raw internal-return algebra for a proof-only private stack prefix.  The explicit
    isolation premise is load-bearing: a return into a Public destination may change the Public
    projection and therefore cannot be folded as unary stuttering.
-/
theorem private_output_step_preserves_prefix
    {machine : SemanticProgram} {state : State} {instruction : Instruction}
    {root : UInt32} {frame : CallFrame} {rest spine : List CallFrame}
    (hactive : ActiveState machine root state)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (houtput : instruction.op = .output)
    (hstack : state.callStack = frame :: (rest ++ spine))
    (hisolated : frame.destination = 0 ∨
      labelAt machine.valueLabels frame.destination ≠ .pub) :
    let next := step machine state
    ∃ nextPrefix,
      (nextPrefix = rest ∨ nextPrefix = frame :: rest) ∧
        next.state.callStack = nextPrefix ++ spine ∧
        publicProjection machine (restoreFrameStack next.state nextPrefix) =
          publicProjection machine (restoreFrameStack state (frame :: rest)) ∧
        publicBoundaryTrace next.events = [] := by
  let operand := operandValue machine state instruction
  by_cases hflow : operand.label.flowsTo frame.returnLabel
  · have hprojection := privateReturn_preserves_prefix_restored_publicProjection
      machine state frame (rest ++ spine) rest operand.payload hisolated
    dsimp only
    refine ⟨rest, Or.inl rfl, ?_, ?_, ?_⟩
    · simp [step, hactive.notHalted, hactive.notTrapped, hlookup, houtput, hstack,
        operand, hflow]
    · simpa [step, hactive.notHalted, hactive.notTrapped, hlookup, houtput, hstack,
        operand, hflow] using hprojection
    · simp [step, hactive.notHalted, hactive.notTrapped, hlookup, houtput, hstack,
        operand, hflow, publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]
  · dsimp only
    have hbase : publicProjection machine { state with trapped := true } =
        publicProjection machine state := rfl
    have htrapProjection := restoreFrameStack_preserves_publicProjection_eq machine
      hbase (frame :: rest)
    refine ⟨frame :: rest, Or.inr rfl, ?_, ?_, ?_⟩
    · simp [step, hactive.notHalted, hactive.notTrapped, hlookup, houtput, hstack,
        operand, hflow]
    · simpa [step, hactive.notHalted, hactive.notTrapped, hlookup, houtput, hstack,
        operand, hflow] using htrapProjection
    · simp [step, hactive.notHalted, hactive.notTrapped, hlookup, houtput, hstack,
        operand, hflow, publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]

/-- The exact state-write offset used by the raw step resolves to a non-Public global actor-state
    cell whenever the accepted raw occurrence is non-Public.  This discharges the last runtime
    sink premise of the local preservation lemma from production verifier acceptance.
-/
theorem verified_private_stateWrite_runtime_sink
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {state : State} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hwrite : instruction.op = .stateWrite)
    (hnonpublic : instruction.blockLabel ≠ .pub) :
    let offset := (immediateOperands (rawSemanticProgram program analysis)
      instruction).head?.getD 0
    0 ≤ offset → stateLabelAt (rawSemanticProgram program analysis)
      (UInt32.ofNat offset.toNat) ≠ .pub := by
  obtain ⟨source, offset, sink, _, hsourceId, _, _, himmediate, hcontract, hoccurrence⟩ :=
    returned_stateWrite_occurrence_safe hjudgment hanalysis hlookup hwrite
  have himmediate' :
      semanticImmediateAt? program.base instruction.id 2 = some offset := by
    simpa [hsourceId] using himmediate
  have hruntimeHead := verified_state_runtime_immediate_head hjudgment hanalysis hlookup
    (Or.inr hwrite) (by simpa [hwrite] using himmediate')
  have hsinkNonpublic : sink ≠ .pub := by
    intro hsinkPublic
    have hblockPublic : instruction.blockLabel = .pub :=
      eq_public_of_flowsTo_public (by
        simpa [OccurrenceKernel.externalSiteLabel, hsinkPublic] using hoccurrence)
    exact hnonpublic hblockPublic
  have hruntimeFlow := analyzed_state_sink_flows_to_runtime_label hanalysis hcontract
  have hruntimePrivate :
      stateLabelAt (rawSemanticProgram program analysis) offset ≠ .pub := by
    intro hpublic
    exact hsinkNonpublic (eq_public_of_flowsTo_public (by simpa [hpublic] using hruntimeFlow))
  dsimp only
  intro _
  rw [hruntimeHead]
  simpa using hruntimePrivate

/-- Constructor-complete private local bridge.  Calls and closures extend the proof-only
    private prefix; ordinary instructions retain it; internal returns pop it (or trap without
    changing it).  Every case is boundary-silent and preserves the prefix-restored Public
    projection.  `release` and `releaseCT` use the ordinary verifier-derived destination rule;
    their real release events are deliberately not erased or classified as absent here.

    `hreturn` names the actual top private frame and proves its result destination invisible.
    Region/frame provenance discharges this premise in the segment-level theorem; keeping it
    explicit here prevents a Public-returning private call from being treated as unary silence.
-/
theorem verified_private_anchor_step_preserves_prefix
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine privatePrefix : List CallFrame}
    {anchor : Nat} {state : State} {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hanchor : ActivationAnchor spine anchor state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub)
    (hstack : state.callStack = privatePrefix ++ spine)
    (hreturn : instruction.op = .output →
      ∃ frame rest, privatePrefix = frame :: rest ∧
        (frame.destination = 0 ∨
          labelAt (rawSemanticProgram program analysis).valueLabels frame.destination ≠ .pub)) :
    let next := step (rawSemanticProgram program analysis) state
    ∃ nextPrefix,
      next.state.callStack = nextPrefix ++ spine ∧
        publicProjection (rawSemanticProgram program analysis)
            (restoreFrameStack next.state nextPrefix) =
          publicProjection (rawSemanticProgram program analysis)
            (restoreFrameStack state privatePrefix) ∧
        publicBoundaryTrace next.events = [] := by
  let machine := rawSemanticProgram program analysis
  by_cases houtput : instruction.op = .output
  · obtain ⟨frame, rest, hprefix, hisolated⟩ := hreturn houtput
    subst privatePrefix
    have hstack' : state.callStack = frame :: (rest ++ spine) := by simpa using hstack
    have houtputStep := private_output_step_preserves_prefix
      (machine := machine) (root := root) hactive hlookup houtput hstack' hisolated
    obtain ⟨nextPrefix, _, hstackNext, hprojection, hboundary⟩ := houtputStep
    exact ⟨nextPrefix, hstackNext, hprojection, hboundary⟩
  · have hrawNonpublic := private_anchor_nonoutput_raw_block_nonpublic hanalysis
      hactive hanchor hlookup hnonpublic houtput
    by_cases hcall : instruction.op = .call
    · have hlocal := verified_nonpublic_call_step_preserves_prefix
        hjudgment hanalysis hactive hlookup hrawNonpublic (Or.inl hcall)
        privatePrefix spine hstack
      obtain ⟨nextPrefix, hnextStack, hprojection, hboundary⟩ := hlocal
      exact ⟨nextPrefix, hnextStack, hprojection, hboundary⟩
    · by_cases hclosure : instruction.op = .closure
      · have hlocal := verified_nonpublic_call_step_preserves_prefix
          hjudgment hanalysis hactive hlookup hrawNonpublic (Or.inr hclosure)
          privatePrefix spine hstack
        obtain ⟨nextPrefix, hnextStack, hprojection, hboundary⟩ := hlocal
        exact ⟨nextPrefix, hnextStack, hprojection, hboundary⟩
      · have hstate : instruction.op = .stateWrite →
            let offset := (immediateOperands machine instruction).head?.getD 0
            0 ≤ offset → stateLabelAt machine (UInt32.ofNat offset.toNat) ≠ .pub := by
          intro hwrite
          exact verified_private_stateWrite_runtime_sink hjudgment hanalysis hlookup
            hwrite hrawNonpublic
        have hlocal := verified_nonoutput_noncall_nonpublic_step_preserves_prefix
          hjudgment hanalysis hactive hlookup hrawNonpublic hcall hclosure houtput
          privatePrefix spine hstack hstate
        exact ⟨privatePrefix, hlocal.1, hlocal.2.1, hlocal.2.2⟩

/-! ## Finite private fold -/

/-- Fold the constructor-complete local rule over one actual finite `runPrefix`.  The hypothesis
    is exactly the shape returned by the region layer at each strict prefix, plus the
    frame-provenance fact needed for an internal return.  It contains no projection equality and
    no replacement transition.

    Downgrade events remain part of the actual `runPrefix` trace.  The conclusion deliberately
    says nothing about either the complete or filtered release sequence.
-/
theorem verified_private_prefix_preservation
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine startPrefix : List CallFrame}
    {length : Nat} {start : State}
    (hstartStack : start.callStack = startPrefix ++ spine)
    (hprivate : ∀ elapsed, elapsed < length →
      ∀ privatePrefix,
        (runPrefix (rawSemanticProgram program analysis) elapsed start).state.callStack =
            privatePrefix ++ spine →
        ∃ anchor instruction,
          ActiveState (rawSemanticProgram program analysis) root
              (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
            ActivationAnchor spine anchor
              (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
            (rawSemanticProgram program analysis).instructions[
                (runPrefix (rawSemanticProgram program analysis) elapsed start).state.pc]? =
              some instruction ∧
            localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub ∧
            (instruction.op = .output →
              ∃ frame rest, privatePrefix = frame :: rest ∧
                (frame.destination = 0 ∨
                  labelAt (rawSemanticProgram program analysis).valueLabels
                    frame.destination ≠ .pub))) :
    ∃ endPrefix,
      (runPrefix (rawSemanticProgram program analysis) length start).state.callStack =
          endPrefix ++ spine ∧
        publicProjection (rawSemanticProgram program analysis)
            (restoreFrameStack
              (runPrefix (rawSemanticProgram program analysis) length start).state endPrefix) =
          publicProjection (rawSemanticProgram program analysis)
            (restoreFrameStack start startPrefix) ∧
        ∀ elapsed, elapsed < length →
          publicBoundaryTrace
              (step (rawSemanticProgram program analysis)
                (runPrefix (rawSemanticProgram program analysis) elapsed start).state).events =
            [] := by
  let machine := rawSemanticProgram program analysis
  have hprefix : ∀ elapsed, elapsed ≤ length →
      ∃ privatePrefix,
        (runPrefix machine elapsed start).state.callStack = privatePrefix ++ spine ∧
          publicProjection machine
              (restoreFrameStack (runPrefix machine elapsed start).state privatePrefix) =
            publicProjection machine (restoreFrameStack start startPrefix) := by
    intro elapsed helapsed
    induction elapsed with
    | zero =>
        exact ⟨startPrefix, by simpa only [runPrefix] using hstartStack, rfl⟩
    | succ previous ih =>
        have hpreviousBound : previous ≤ length := by omega
        have hpreviousStrict : previous < length := by omega
        obtain ⟨privatePrefix, hstack, hprojection⟩ := ih hpreviousBound
        obtain ⟨anchor, instruction, hactive, hanchor, hlookup, hnonpublic, hreturn⟩ :=
          hprivate previous hpreviousStrict privatePrefix (by simpa [machine] using hstack)
        obtain ⟨nextPrefix, hnextStack, hnextProjection, _⟩ :=
          verified_private_anchor_step_preserves_prefix hjudgment hanalysis
            hactive hanchor hlookup hnonpublic (by simpa [machine] using hstack) hreturn
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
  refine ⟨endPrefix, hendStack, hendProjection, ?_⟩
  intro elapsed helapsed
  obtain ⟨privatePrefix, hstack, _⟩ := hprefix elapsed (Nat.le_of_lt helapsed)
  obtain ⟨anchor, instruction, hactive, hanchor, hlookup, hnonpublic, hreturn⟩ :=
    hprivate elapsed helapsed privatePrefix hstack
  obtain ⟨_, _, _, hboundary⟩ :=
    verified_private_anchor_step_preserves_prefix hjudgment hanalysis
      hactive hanchor hlookup hnonpublic hstack hreturn
  exact hboundary

/-- Empty proof-only prefixes at both real endpoints turn the fold into the exact unary segment
    fact consumed by weak-bisimulation composition: full Public projection preservation and
    ordered Public output/boundary silence.  The two executions may use different `length`s when
    this theorem is applied independently.
-/
theorem verified_private_segment_preserves_publicProjection
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine : List CallFrame} {length : Nat} {start : State}
    (hstartStack : start.callStack = spine)
    (hendStack :
      (runPrefix (rawSemanticProgram program analysis) length start).state.callStack = spine)
    (hprivate : ∀ elapsed, elapsed < length →
      ∀ privatePrefix,
        (runPrefix (rawSemanticProgram program analysis) elapsed start).state.callStack =
            privatePrefix ++ spine →
        ∃ anchor instruction,
          ActiveState (rawSemanticProgram program analysis) root
              (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
            ActivationAnchor spine anchor
              (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
            (rawSemanticProgram program analysis).instructions[
                (runPrefix (rawSemanticProgram program analysis) elapsed start).state.pc]? =
              some instruction ∧
            localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub ∧
            (instruction.op = .output →
              ∃ frame rest, privatePrefix = frame :: rest ∧
                (frame.destination = 0 ∨
                  labelAt (rawSemanticProgram program analysis).valueLabels
                    frame.destination ≠ .pub))) :
    publicProjection (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) length start).state =
      publicProjection (rawSemanticProgram program analysis) start ∧
      ∀ elapsed, elapsed < length →
        publicBoundaryTrace
            (step (rawSemanticProgram program analysis)
              (runPrefix (rawSemanticProgram program analysis) elapsed start).state).events = [] := by
  have hfold := verified_private_prefix_preservation hjudgment hanalysis
    (startPrefix := []) (by simpa using hstartStack) hprivate
  obtain ⟨endPrefix, hfoldStack, hprojection, hboundary⟩ := hfold
  have hprefixEmpty : endPrefix = [] := by
    have hlength := congrArg List.length (hfoldStack.symm.trans hendStack)
    simp only [List.length_append] at hlength
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst endPrefix
  simpa only [restoreFrameStack] using And.intro hprojection hboundary

/-! ## Production region-to-segment bridge -/

/-- First-hit minimality rules out a descendant call-site anchor at the selected continuation.
    A descendant endpoint would imply that the immediately preceding active state already had
    the same anchor: ordinary and nested steps retain the outer frame, a new call stutters at its
    own call site, and a deeper return retains that outer frame.  Thus a verified first hit is a
    genuine reusable activation cut point with exactly the original suspended caller stack. -/
private theorem first_activation_continuation_stack_eq
    {machine : SemanticProgram} {root : UInt32} {steps elapsed parent : Nat}
    {start : State} {result : StepResult} {spine : List CallFrame}
    (hexecution : SuccessfulExecution machine root steps start result)
    (hstartStack : start.callStack = spine) (helapsed : elapsed < steps)
    (hcontinuation : ActivationContinuationAt machine root spine parent
      (runPrefix machine elapsed start).state)
    (hstrict : ∀ earlier, earlier < elapsed →
      ¬ ActivationContinuationAt machine root spine parent
          (runPrefix machine earlier start).state ∧
        ActiveState machine root (runPrefix machine earlier start).state ∧
        ∃ anchor instruction,
          ActivationAnchor spine anchor (runPrefix machine earlier start).state ∧
            machine.instructions[(runPrefix machine earlier start).state.pc]? =
              some instruction) :
    (runPrefix machine elapsed start).state.callStack = spine := by
  rcases hcontinuation with hendAnchor | ⟨_, hstack, _⟩
  · cases hendAnchor with
    | current hstack => exact hstack
    | descendant inner outer hendStack =>
        have helapsedPositive : 0 < elapsed := by
          by_contra hzero
          have helapsedZero : elapsed = 0 := Nat.eq_zero_of_not_pos hzero
          subst elapsed
          have hlength := congrArg List.length (hstartStack.symm.trans hendStack)
          simp at hlength
          omega
        let previous := elapsed - 1
        have hprevious : previous < elapsed := by dsimp [previous]; omega
        obtain ⟨hnotContinuation, hbeforeActive, anchor, instruction, hbeforeAnchor,
          hlookup⟩ := hstrict previous hprevious
        have hafterActiveRaw := hexecution.reached_active helapsed
        have hnextState :
            (runPrefix machine elapsed start).state =
              (step machine (runPrefix machine previous start).state).state := by
          have hadd := congrArg StepResult.state
            (ReleaseSynchronization.runPrefix_add machine previous 1 start)
          have hsum : previous + 1 = elapsed := by dsimp [previous]; omega
          rw [hsum] at hadd
          simpa only [runPrefix] using hadd
        have hafterActive : ActiveState machine root
            (step machine (runPrefix machine previous start).state).state := by
          rw [← hnextState]
          exact hafterActiveRaw
        have htransition := live_step_stack_transition hlookup hbeforeActive.notHalted
          hbeforeActive.notTrapped hafterActive.notHalted hafterActive.notTrapped
        have hendStackStep :
            (step machine (runPrefix machine previous start).state).state.callStack =
              inner ++ outer :: spine := by
          rw [← hnextState]
          exact hendStack
        apply False.elim
        apply hnotContinuation
        left
        cases htransition with
        | same hsame _ _ _ =>
            exact .descendant inner outer (hsame.symm.trans hendStackStep)
        | push frame hpush hreturnPc _ =>
            cases inner with
            | nil =>
                have hcons : frame ::
                    (runPrefix machine previous start).state.callStack = outer :: spine := by
                  simpa using hpush.symm.trans hendStackStep
                have hframe : frame = outer := List.cons.inj hcons |>.1
                have hbeforeStack :
                    (runPrefix machine previous start).state.callStack = spine :=
                  List.cons.inj hcons |>.2
                have hpc : outer.returnPc - 1 =
                    (runPrefix machine previous start).state.pc := by
                  rw [hframe] at hreturnPc
                  omega
                rw [hpc]
                exact .current hbeforeStack
            | cons top tail =>
                have hcons : frame ::
                    (runPrefix machine previous start).state.callStack =
                      top :: (tail ++ outer :: spine) := by
                  simpa using hpush.symm.trans hendStackStep
                have hbeforeStack :
                    (runPrefix machine previous start).state.callStack =
                      tail ++ outer :: spine := List.cons.inj hcons |>.2
                exact .descendant tail outer hbeforeStack
        | pop frame rest hbefore hafter _ _ =>
            have hrest : rest = inner ++ outer :: spine :=
              hafter.symm.trans hendStackStep
            have hbeforeStack :
                (runPrefix machine previous start).state.callStack =
                  (frame :: inner) ++ outer :: spine := by
              rw [hbefore, hrest]
              rfl
            exact .descendant (frame :: inner) outer hbeforeStack
  · exact hstack

/-- The production V9 first-hit region theorem supplies every local premise needed by the unary
    private fold.  In particular, a strict-prefix output cannot pop the activation itself: its
    successor is still live either at the next strict prefix or at the verified continuation.
    Hence the output returns through a genuine coherent private frame and
    `LocalDestinationSafe` isolates its destination.

    First-hit minimality additionally rules out a descendant call-site anchor at the selected
    endpoint, while the synthetic-return case explicitly carries the original stack.  Thus the
    endpoint is a genuine reusable cut point with stack exactly `spine`, and the frame-restored
    fold reduces to equality of the raw Public projections.  Actual release and releaseCT events
    remain in the complete trace.
-/
theorem v9_verified_successful_private_activation_prefix_preservation
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {steps controller arm : Nat} {start : State} {result : StepResult}
    {spine : List CallFrame}
    (hreachable : ReachableFromRoot (rawSemanticProgram program analysis) root start)
    (hexecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root steps start result)
    (hstartStack : start.callStack = spine) (hstartPc : start.pc = arm)
    (hcontroller : controller <
      (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow).instructions.size)
    (hedge : arm ∈
      (decodedControlGraph
        (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow)).successors.getD
          controller [])
    {lane : Label}
    (hlane : PrivateControllerLane
      (decodedControlGraph
        (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow))
      analysis.localAnalysis controller lane) :
    ∃ elapsed,
      elapsed < steps ∧
        ActivationContinuationAt (rawSemanticProgram program analysis) root spine
          (analysis.localAnalysis.regions.index.parentAt controller)
          (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
        ReachableFromRoot (rawSemanticProgram program analysis) root
          (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
        (analysis.localAnalysis.regions.index.parentAt controller =
            functionReturn (rawSemanticProgram program analysis)
              (activeFunctionId root spine) →
          ∃ instruction,
            (rawSemanticProgram program analysis).instructions[
                (runPrefix (rawSemanticProgram program analysis) elapsed start).state.pc]? =
              some instruction ∧
            localOccurrenceAt analysis.localAnalysis.frontiers
                (runPrefix (rawSemanticProgram program analysis) elapsed start).state.pc ≠ .pub) ∧
        (runPrefix (rawSemanticProgram program analysis) elapsed start).state.callStack = spine ∧
        publicProjection (rawSemanticProgram program analysis)
            (runPrefix (rawSemanticProgram program analysis) elapsed start).state =
          publicProjection (rawSemanticProgram program analysis) start ∧
        (∀ earlier, earlier < elapsed →
          ∃ anchor instruction,
            ActiveState (rawSemanticProgram program analysis) root
                (runPrefix (rawSemanticProgram program analysis) earlier start).state ∧
              ActivationAnchor spine anchor
                (runPrefix (rawSemanticProgram program analysis) earlier start).state ∧
              (rawSemanticProgram program analysis).instructions[
                  (runPrefix (rawSemanticProgram program analysis) earlier start).state.pc]? =
                some instruction ∧
              localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub) ∧
        ∀ earlier, earlier < elapsed →
          publicBoundaryTrace
              (step (rawSemanticProgram program analysis)
                (runPrefix (rawSemanticProgram program analysis) earlier start).state).events =
            [] := by
  let machine := rawSemanticProgram program analysis
  have hjudgment := v9_occurrence_verifier_sound hverified
  obtain ⟨elapsed, helapsed, hcontinuation, hreachEnd, hendpointPrivate, hstrict⟩ :=
    v9_verified_successful_private_activation_segment hverified hanalysis hreachable
      hexecution hstartStack hstartPc hcontroller hedge hlane
  have hendStackExact :
      (runPrefix machine elapsed start).state.callStack = spine := by
    apply first_activation_continuation_stack_eq hexecution
      (by simpa [machine] using hstartStack) helapsed hcontinuation
    intro earlier hearlier
    obtain ⟨hnotContinuation, _, hactive, hevidence⟩ := hstrict earlier hearlier
    obtain ⟨anchor, instruction, hanchor, hlookup, _, _, _, _⟩ := hevidence
    exact ⟨hnotContinuation, hactive, anchor, instruction, hanchor, hlookup⟩
  have hprivate : ∀ earlier, earlier < elapsed →
      ∀ privatePrefix,
        (runPrefix machine earlier start).state.callStack = privatePrefix ++ spine →
        ∃ anchor instruction,
          ActiveState machine root (runPrefix machine earlier start).state ∧
            ActivationAnchor spine anchor (runPrefix machine earlier start).state ∧
            machine.instructions[(runPrefix machine earlier start).state.pc]? =
              some instruction ∧
            localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub ∧
            (instruction.op = .output →
              ∃ frame rest, privatePrefix = frame :: rest ∧
                (frame.destination = 0 ∨
                  labelAt machine.valueLabels frame.destination ≠ .pub)) := by
    intro earlier hearlier privatePrefix hstack
    obtain ⟨_, _, hactive, hevidence⟩ := hstrict earlier hearlier
    obtain ⟨anchor, instruction, hanchor, hlookup, _, hnonpublic, _, _⟩ := hevidence
    refine ⟨anchor, instruction, hactive, hanchor, hlookup, hnonpublic, ?_⟩
    intro houtput
    have hnextBound : earlier + 1 < steps := by omega
    have hnextActiveRaw := hexecution.reached_active hnextBound
    have hnextState :
        (runPrefix machine (earlier + 1) start).state =
          (step machine (runPrefix machine earlier start).state).state := by
      have hadd := congrArg StepResult.state
        (ReleaseSynchronization.runPrefix_add machine earlier 1 start)
      simpa only [runPrefix] using hadd
    have hnextActive : ActiveState machine root
        (step machine (runPrefix machine earlier start).state).state := by
      rw [← hnextState]
      exact hnextActiveRaw
    have hnextLiveRaw :
        ActivationLive spine (runPrefix machine (earlier + 1) start).state := by
      by_cases hnextStrict : earlier + 1 < elapsed
      · obtain ⟨_, _, _, hnextEvidence⟩ := hstrict (earlier + 1) hnextStrict
        obtain ⟨_, _, hnextAnchor, _, _, _, _, _⟩ := hnextEvidence
        exact activationAnchor_activationLive hnextAnchor
      · have hnextEq : earlier + 1 = elapsed := by omega
        rw [hnextEq]
        exact activationContinuationAt_activationLive hcontinuation
    have hnextLive : ActivationLive spine
        (step machine (runPrefix machine earlier start).state).state := by
      rw [← hnextState]
      exact hnextLiveRaw
    exact private_anchor_output_prefix_isolated hjudgment hanalysis hactive hnextActive
      hnextLive hanchor hlookup houtput hnonpublic hstack
  obtain ⟨endPrefix, hendStack, hendProjection, hboundary⟩ :=
    verified_private_prefix_preservation hjudgment hanalysis
      (startPrefix := []) (length := elapsed) (by simpa [machine] using hstartStack)
      (by simpa [machine] using hprivate)
  have hendPrefixEmpty : endPrefix = [] := by
    have hlength := congrArg List.length (hendStack.symm.trans hendStackExact)
    simp only [List.length_append] at hlength
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst endPrefix
  refine ⟨elapsed, helapsed, hcontinuation, hreachEnd, hendpointPrivate,
    hendStackExact, ?_, ?_, ?_⟩
  · simpa [machine] using hendProjection
  · intro earlier hearlier
    obtain ⟨_, _, hactive, hevidence⟩ := hstrict earlier hearlier
    obtain ⟨anchor, instruction, hanchor, hlookup, _, hnonpublic, _, _⟩ := hevidence
    exact ⟨anchor, instruction, hactive, hanchor, hlookup, hnonpublic⟩
  · simpa [machine] using hboundary

end LambdaSigil.Combined.V9.PublicPrivateSegmentSecurity
