import LambdaSigil.PublicMatchingSecurity
import LambdaSigil.PublicRegionConvergence

/-!
# Verifier-derived classification of Public raw successors

This module contains only static/executable bridges needed by the independent-length Public
composition.  In particular, it recovers controller labels from the analyzer-owned selector
array and turns an Internal or Secret selector into the exact `PrivateControllerLane` evidence
consumed by region convergence.  No relational verdict, merge certificate, or future trace is an
input.
-/

namespace LambdaSigil.Combined.V9.PublicStepClassification

open Semantic OccurrenceRegions OccurrenceTransfer DecodedOccurrence
open DecodedOccurrenceSecurity
open OccurrenceDataflowInvocation OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity Semantic.PublicRegionConvergence
open PublicLocalSecurity PublicMatchingSecurity

private theorem list_mapM_some_length {α β : Type _} {f : α → Option β}
    {items : List α} {images : List β} (run : items.mapM f = some images) :
    images.length = items.length := by
  induction items generalizing images with
  | nil => simp_all [List.mapM_nil]
  | cons head tail ih =>
      simp [List.mapM_cons, Option.bind_eq_some_iff] at run
      obtain ⟨image, -, rest, restRun, shape⟩ := run
      subst shape
      simp [ih restRun]

private theorem list_mapM_some_getElem {α β : Type _} {f : α → Option β}
    {items : List α} {images : List β} (run : items.mapM f = some images)
    (position : Nat) (hitems : position < items.length) (himages : position < images.length) :
    f items[position] = some images[position] := by
  induction items generalizing images position with
  | nil => simp at hitems
  | cons head tail ih =>
      simp [List.mapM_cons, Option.bind_eq_some_iff] at run
      obtain ⟨image, himage, rest, restRun, shape⟩ := run
      subst shape
      cases position with
      | zero => simpa using himage
      | succ offset =>
          simp only [List.getElem_cons_succ]
          exact ih restRun offset (by simpa using hitems) (by simpa using himages)

/-- Successful selector extraction is pointwise exact on every decoded instruction.  Synthetic
    function-return vertices occupy only the appended suffix and are irrelevant here. -/
theorem selectorLabels_pointwise {machine : SemanticProgram} {selectors : Array Label}
    (hselectors : selectorLabels? machine = some selectors)
    {pc : Nat} {instruction : Instruction}
    (hlookup : machine.instructions[pc]? = some instruction) :
    selectorLabel? machine instruction = some (selectors.getD pc .pub) := by
  unfold selectorLabels? at hselectors
  simp only [bind] at hselectors
  cases hmapped : machine.instructions.mapM (selectorLabel? machine) with
  | none => simp [hmapped] at hselectors
  | some mapped =>
      have hselectorsEq : selectors = mapped ++ Array.replicate machine.functions.size .pub := by
        rw [hmapped] at hselectors
        simpa using hselectors.symm
      have hpc : pc < machine.instructions.size := (Array.getElem?_eq_some_iff.mp hlookup).1
      have hmapList : machine.instructions.toList.mapM (selectorLabel? machine) =
          some mapped.toList := by
        have htoList := congrArg (fun result => Array.toList <$> result) hmapped
        simpa using htoList
      have hlength := list_mapM_some_length hmapList
      have hsize : mapped.size = machine.instructions.size := by simpa using hlength
      have hpoint := list_mapM_some_getElem hmapList pc (by simpa using hpc) (by
        rw [hlength]
        simpa using hpc)
      have hinstruction : machine.instructions[pc] = instruction :=
        (Array.getElem?_eq_some_iff.mp hlookup).2
      rw [hselectorsEq]
      have hmappedBound : pc < mapped.size := by omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left hmappedBound]
      simpa [hinstruction, hmappedBound] using hpoint

/-- The ranked analyzer's selector at a raw instruction is the selector extracted from the exact
    unraised decoded instruction.  Raising occurrences changes only `blockLabel`. -/
theorem analyzed_raw_selector_exact
    {program : V9.Program} {analysis : OccurrenceDataflowInvocation.Analysis}
    (hjudgment : V9OccurrenceJudgment program)
    (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction) :
    selectorLabel? (rawSemanticProgram program analysis) instruction =
      some (analysis.localAnalysis.selectors.getD pc .pub) := by
  exact returned_selector_coherent hjudgment hanalysis hlookup

/-- The first runtime program value carries exactly the statically extracted controlling label.
    Runtime `Value.label` fields are not consulted. -/
theorem controllingValueLabel_eq_operandValue_label
    {machine : SemanticProgram} {state : State} {instruction : Instruction} {label : Label}
    (hlabel : controllingValueLabel? machine instruction = some label) :
    (operandValue machine state instruction).label = label := by
  obtain ⟨operand, hoperand, hkind, hcell⟩ := controlling_label_has_exact_operand hlabel
  cases hcount : instruction.operandCount.toNat with
  | zero =>
      unfold instructionOperandAt? at hoperand
      simp [hcount] at hoperand
  | succ count =>
      unfold operandValue operandValues valueOperandCells instructionOperands
      rw [hcount, List.range_succ_eq_map]
      simp [hoperand, hkind]
      simp [labelAt, hcell]

/-- For every real conditional controller, the analyzer-owned selector equals the exact label of
    the raw controlling value used by `nextPc`. -/
theorem analyzed_controller_selector_eq_operand_label
    {program : V9.Program} {analysis : OccurrenceDataflowInvocation.Analysis}
    (hjudgment : V9OccurrenceJudgment program)
    (hanalysis : analyze? program = some analysis)
    {state : State} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2)) :
    analysis.localAnalysis.selectors.getD state.pc .pub =
      (operandValue (rawSemanticProgram program analysis) state instruction).label := by
  have hselector := analyzed_raw_selector_exact hjudgment hanalysis hlookup
  have hcontrolling : controllingValueLabel? (rawSemanticProgram program analysis) instruction =
      some (analysis.localAnalysis.selectors.getD state.pc .pub) := by
    rcases hcontrol with hbranch | hloop | hrange | hdispatch
    · simp only [selectorLabel?, hbranch] at hselector
      split at hselector <;> simp_all
    · simp only [selectorLabel?, hloop] at hselector
      split at hselector <;> simp_all
    · simp only [selectorLabel?, hrange] at hselector
      split at hselector <;> simp_all
    · simp only [selectorLabel?, hdispatch.1] at hselector
      have hcount : (instruction.operandCount == 2) = false := by simp [hdispatch.2]
      simp only [hcount, Bool.false_eq_true, ↓reduceIte] at hselector
      split at hselector <;> simp_all
  exact (controllingValueLabel_eq_operandValue_label hcontrolling).symm

/-- At an accepted raw Public occurrence, the analyzer-owned local occurrence is exactly Public.
    This is a consequence of the lattice lower-bound theorem, not a runtime label check. -/
theorem local_occurrence_public_of_raw_public
    {program : V9.Program} {analysis : OccurrenceDataflowInvocation.Analysis}
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hnonoutput : instruction.op ≠ .output)
    (hpublic : instruction.blockLabel = .pub) :
    localOccurrenceAt analysis.localAnalysis.frontiers pc = .pub := by
  have hflow := local_occurrence_flows_to_raw_block_of_lookup hlookup hnonoutput
  rw [hpublic] at hflow
  cases hlabel : localOccurrenceAt analysis.localAnalysis.frontiers pc <;>
    simp_all [Label.flowsTo, Label.rank]

/-- A decoded two-way controller is structurally a controller in the verifier-owned CFG. -/
theorem isControllerB_of_control_lookup
    {machine : SemanticProgram} {pc : Nat} {instruction : Instruction}
    (hlookup : machine.instructions[pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2)) :
    isControllerB (decodedControlGraph machine) pc = true := by
  have hpc : pc < machine.instructions.size := (Array.getElem?_eq_some_iff.mp hlookup).1
  have hinstruction : machine.instructions[pc] = instruction :=
    (Array.getElem?_eq_some_iff.mp hlookup).2
  let mapped := machine.instructions.mapIdx (instructionSuccessors machine)
  have hmappedBound : pc < mapped.size := by simpa [mapped] using hpc
  have hrow : (decodedControlGraph machine).successors.getD pc [] =
      instructionSuccessors machine pc instruction := by
    rw [Array.getD_eq_getD_getElem?]
    change (mapped ++ Array.replicate machine.functions.size [])[pc]?.getD [] = _
    rw [Array.getElem?_append_left hmappedBound]
    simp [mapped, hlookup]
  obtain hbranch | hloop | hrange | hdispatch := hcontrol
  · simp [isControllerB, hrow, instructionSuccessors, hbranch]
  · simp [isControllerB, hrow, instructionSuccessors, hloop]
  · simp [isControllerB, hrow, instructionSuccessors, hrange]
  · simp [isControllerB, hrow, instructionSuccessors, hdispatch.1, hdispatch.2]

/-- Internal and ordinary-Secret selector labels give the exact private lane consumed by the
    checked region theorem.  SecretCT has no constructor and remains rejected by static safety. -/
theorem privateControllerLane_of_selector
    {program : V9.Program} {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction} {lane : Label}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2))
    (hselector : analysis.localAnalysis.selectors.getD pc .pub = lane)
    (hlane : lane = .internal ∨ lane = .secret) :
    PrivateControllerLane
      (decodedControlGraph
        (OccurrenceDataflow.semanticProgram program analysis.dataflow))
      analysis.localAnalysis pc lane := by
  let base := OccurrenceDataflow.semanticProgram program analysis.dataflow
  obtain ⟨source, hsource, hraised⟩ := rawInstructionSource_of_lookup hlookup
  have hsourceOp : source.op = instruction.op := by
    rw [hraised]
    simp [raiseInstructionResultLabel, raiseInstructionOccurrence]
  have hsourceCount : source.operandCount = instruction.operandCount := by
    rw [hraised]
    simp [raiseInstructionResultLabel, raiseInstructionOccurrence]
  have hcontrolSource : source.op = .branch ∨ source.op = .loop ∨ source.op = .range ∨
      (source.op = .dispatch ∧ source.operandCount ≠ 2) := by
    rcases hcontrol with hbranch | hloop | hrange | hdispatch
    · exact Or.inl (hsourceOp.trans hbranch)
    · exact Or.inr (Or.inl (hsourceOp.trans hloop))
    · exact Or.inr (Or.inr (Or.inl (hsourceOp.trans hrange)))
    · exact Or.inr (Or.inr (Or.inr
        ⟨hsourceOp.trans hdispatch.1, fun htwo => hdispatch.2 (hsourceCount.symm.trans htwo)⟩))
  have hcontroller := isControllerB_of_control_lookup hsource hcontrolSource
  rcases hlane with rfl | rfl
  · apply PrivateControllerLane.internal
    simp [controllerActiveB, hcontroller, hselector, Label.rank]
  · apply PrivateControllerLane.secret
    simp [controllerActiveB, hcontroller, hselector, Label.rank]

/-- Production classification of a conditional controller at a raw Public cut point.  The
    selector is either Public, or the verifier itself supplies an Internal/Secret private lane.
    SecretCT is eliminated by the retained raw static check over the same decoded operand. -/
theorem verified_controller_selector_classification
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {state : State} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2)) :
    analysis.localAnalysis.selectors.getD state.pc .pub = .pub ∨
      ∃ lane,
        (lane = .internal ∨ lane = .secret) ∧
          analysis.localAnalysis.selectors.getD state.pc .pub = lane ∧
          PrivateControllerLane
            (decodedControlGraph
              (OccurrenceDataflow.semanticProgram program analysis.dataflow))
            analysis.localAnalysis state.pc lane := by
  let machine := rawSemanticProgram program analysis
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hmem : instruction ∈ machine.instructions.toList := by
    obtain ⟨hbound, heq⟩ := Array.getElem?_eq_some_iff.mp (by simpa [machine] using hlookup)
    simpa using (heq ▸ Array.getElem_mem hbound)
  have hcontrolFull : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2) ∨
      instruction.op = .closure ∨
      (instruction.op = .trap ∧ instruction.operandCount ≠ 0) := by
    rcases hcontrol with hbranch | hloop | hrange | hdispatch
    · exact Or.inl hbranch
    · exact Or.inr (Or.inl hloop)
    · exact Or.inr (Or.inr (Or.inl hrange))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hdispatch)))
  have hcontrolSafe := (hstatic.1.2 instruction hmem).2.2.2 hcontrolFull
  change (match (valueOperandCells machine instruction).head? with
    | some cell => labelAt machine.valueLabels cell ≠ .secretCT
    | none => False) at hcontrolSafe
  have hoperandNotCT : (operandValue machine state instruction).label ≠ .secretCT := by
    cases hhead : (valueOperandCells machine instruction).head? with
    | none => exact False.elim (by simpa [hhead] using hcontrolSafe)
    | some cell =>
        have hcell : labelAt machine.valueLabels cell ≠ .secretCT := by
          simpa [hhead] using hcontrolSafe
        simpa [operandValue, operandValues, hhead] using hcell
  have hselectorOperand :=
    analyzed_controller_selector_eq_operand_label hjudgment hanalysis hlookup hcontrol
  generalize hselectorEq : analysis.localAnalysis.selectors.getD state.pc .pub = selector
  cases selector with
  | pub => exact Or.inl rfl
  | internal =>
      exact Or.inr ⟨.internal, Or.inl rfl, rfl,
        privateControllerLane_of_selector hanalysis hlookup hcontrol hselectorEq (Or.inl rfl)⟩
  | secret =>
      exact Or.inr ⟨.secret, Or.inr rfl, rfl,
        privateControllerLane_of_selector hanalysis hlookup hcontrol hselectorEq (Or.inr rfl)⟩
  | secretCT =>
      exfalso
      apply hoperandNotCT
      rw [← hselectorOperand, hselectorEq]

/-- When the verifier-derived controller selector is Public, the exact raw payload consulted by
    `nextPc` is equal in Public-low-equivalent states.  This uses the decoded operand slice and
    the complete Public data relation; runtime `Value.label` fields remain non-authoritative. -/
theorem controller_operand_payload_eq_of_public_selector
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {left right : State} {instruction : Instruction}
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2))
    (hselector : analysis.localAnalysis.selectors.getD left.pc .pub = .pub) :
    (operandValue (rawSemanticProgram program analysis) left instruction).payload =
      (operandValue (rawSemanticProgram program analysis) right instruction).payload := by
  let machine := rawSemanticProgram program analysis
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hwell : instructionWellFormed machine instruction :=
    instruction_well_formed_of_raw_static_safe hstatic (by simpa [machine] using hlookup)
  have hoperands := operandValues_publicEquivalent hlow.2.2.2.2 hwell
  apply hoperands.head_payload_of_public
  have hlabel := analyzed_controller_selector_eq_operand_label hjudgment hanalysis hlookup hcontrol
  simpa [machine, operandValue, hselector] using hlabel.symm

/-- A Public controller therefore selects the same actual decoded successor on both runs. -/
theorem controller_nextPc_eq_of_public_selector
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {left right : State} {instruction : Instruction}
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2))
    (hselector : analysis.localAnalysis.selectors.getD left.pc .pub = .pub) :
    nextPc (rawSemanticProgram program analysis) left instruction
        (operandValue (rawSemanticProgram program analysis) left instruction) =
      nextPc (rawSemanticProgram program analysis) right instruction
        (operandValue (rawSemanticProgram program analysis) right instruction) := by
  have hpayload := controller_operand_payload_eq_of_public_selector hjudgment hanalysis
    hlow hlookup hcontrol hselector
  rcases hcontrol with hbranch | hloop | hrange | hdispatch
  · simp [nextPc, hbranch, hpayload]
  · simp [nextPc, hloop, hpayload]
  · simp [nextPc, hrange, hpayload]
  · simp [nextPc, hdispatch.1, hdispatch.2, hpayload]

/-- The raw branch chosen by `nextPc` is one of the exact verifier-owned CFG successors. -/
theorem controller_nextPc_mem_decoded_successors
    {machine : SemanticProgram} {state : State} {instruction : Instruction}
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hcontrol : instruction.op = .branch ∨ instruction.op = .loop ∨
      instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2)) :
    nextPc machine state instruction (operandValue machine state instruction) ∈
      (decodedControlGraph machine).successors.getD state.pc [] := by
  have hpc : state.pc < machine.instructions.size :=
    (Array.getElem?_eq_some_iff.mp hlookup).1
  have hinstruction : machine.instructions[state.pc] = instruction :=
    (Array.getElem?_eq_some_iff.mp hlookup).2
  let mapped := machine.instructions.mapIdx (instructionSuccessors machine)
  have hmappedBound : state.pc < mapped.size := by simpa [mapped] using hpc
  have hrow : (decodedControlGraph machine).successors.getD state.pc [] =
      instructionSuccessors machine state.pc instruction := by
    rw [Array.getD_eq_getD_getElem?]
    change (mapped ++ Array.replicate machine.functions.size [])[state.pc]?.getD [] = _
    rw [Array.getElem?_append_left hmappedBound]
    simp [mapped, hlookup]
  rw [hrow]
  by_cases hzero : (operandValue machine state instruction).payload = 0
  all_goals
    generalize hop : instruction.op = operation at hcontrol
    cases operation <;> simp_all [instructionSuccessors, nextPc]

/-- The raw closure selector is statically one of the three Public-theorem labels.  SecretCT is
    excluded by the production variable-time control check over the exact decoded first operand. -/
theorem verified_closure_selector_classification
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {state : State} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? = some instruction)
    (hclosure : instruction.op = .closure) :
    (operandValue (rawSemanticProgram program analysis) state instruction).label = .pub ∨
      (operandValue (rawSemanticProgram program analysis) state instruction).label = .internal ∨
      (operandValue (rawSemanticProgram program analysis) state instruction).label = .secret := by
  let machine := rawSemanticProgram program analysis
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hmem : instruction ∈ machine.instructions.toList := by
    obtain ⟨hbound, heq⟩ := Array.getElem?_eq_some_iff.mp (by simpa [machine] using hlookup)
    simpa using (heq ▸ Array.getElem_mem hbound)
  have hcontrolSafe := (hstatic.1.2 instruction hmem).2.2.2
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hclosure)))))
  change (match (valueOperandCells machine instruction).head? with
    | some cell => labelAt machine.valueLabels cell ≠ .secretCT
    | none => False) at hcontrolSafe
  have hnotCT : (operandValue machine state instruction).label ≠ .secretCT := by
    cases hhead : (valueOperandCells machine instruction).head? with
    | none => exact False.elim (by simpa [hhead] using hcontrolSafe)
    | some cell =>
        have hcell : labelAt machine.valueLabels cell ≠ .secretCT := by
          simpa [hhead] using hcontrolSafe
        simpa [operandValue, operandValues, hhead] using hcell
  cases hlabel : (operandValue machine state instruction).label with
  | pub => exact Or.inl rfl
  | internal => exact Or.inr (Or.inl rfl)
  | secret => exact Or.inr (Or.inr rfl)
  | secretCT => exact False.elim (hnotCT hlabel)

/-- A Public dynamic closure selector resolves to the same actual callee in Public-low states. -/
theorem instructionCallee_eq_of_public_closure_selector
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : analyze? program = some analysis)
    {left right : State} {instruction : Instruction}
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hclosure : instruction.op = .closure)
    (hpublic : (operandValue (rawSemanticProgram program analysis) left instruction).label =
      .pub) :
    instructionCallee? (rawSemanticProgram program analysis) left instruction =
      instructionCallee? (rawSemanticProgram program analysis) right instruction := by
  let machine := rawSemanticProgram program analysis
  change PublicLowEquivalent machine left right at hlow
  change machine.instructions[left.pc]? = some instruction at hlookup
  change (operandValue machine left instruction).label = .pub at hpublic
  change instructionCallee? machine left instruction =
    instructionCallee? machine right instruction
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hwell : instructionWellFormed machine instruction :=
    instruction_well_formed_of_raw_static_safe hstatic hlookup
  have hoperands := operandValues_publicEquivalent hlow.2.2.2.2 hwell
  have hpayload : (operandValue machine left instruction).payload =
      (operandValue machine right instruction).payload := by
    exact hoperands.head_payload_of_public (by simpa [operandValue] using hpublic)
  cases hleft : operandValues machine left instruction with
  | nil =>
      cases hright : operandValues machine right instruction with
      | nil => simp [instructionCallee?, hclosure, hleft, hright]
      | cons rightHead rightRest =>
          simp [ValueListPublicEquivalent, hleft, hright] at hoperands
  | cons leftHead leftRest =>
      cases hright : operandValues machine right instruction with
      | nil => simp [ValueListPublicEquivalent, hleft, hright] at hoperands
      | cons rightHead rightRest =>
          have hpayloadHead : leftHead.payload = rightHead.payload := by
            simpa [machine, operandValue, hleft, hright] using hpayload
          simp [instructionCallee?, hclosure, hleft, hright, hpayloadHead]

end LambdaSigil.Combined.V9.PublicStepClassification
