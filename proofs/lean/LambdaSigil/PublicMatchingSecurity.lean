import LambdaSigil.PublicTraceSecurity

/-!
# Matching Public instruction algebra

This module contains the binary, constructor-local algebra used at verified Public cut points.
Visibility is always read from the decoded machine.  The lemmas compare the complete Public data
projection and immutable per-site input streams; they do not assume a relational policy, a common
execution length, or a future trace.
-/

namespace LambdaSigil.Combined.V9.PublicMatchingSecurity

open Semantic OccurrenceKernel OccurrenceKernelSecurity PublicLocalSecurity PublicTraceSecurity
open Semantic.PublicRegionSecurity

/-- Reassemble the cut-point relation from the complete Public projection and the pieces of
    control that the raw machine keeps outside that projection.  This is deliberately a pure
    relational algebra lemma: constructor proofs must establish every premise from real steps. -/
theorem publicLowEquivalent_of_projection_and_control {machine : SemanticProgram}
    {nextLeft nextRight : State}
    (hleftSize : nextLeft.values.size = machine.valueLabels.size)
    (hrightSize : nextRight.values.size = machine.valueLabels.size)
    (hstreams : nextLeft.externalInputs = nextRight.externalInputs)
    (hprojection : publicProjection machine nextLeft = publicProjection machine nextRight)
    (hpc : nextLeft.pc = nextRight.pc)
    (hhalted : nextLeft.halted = nextRight.halted)
    (htrapped : nextLeft.trapped = nextRight.trapped)
    (hstack : CallStackPublicEquivalent machine nextLeft.callStack nextRight.callStack) :
    PublicLowEquivalent machine nextLeft nextRight := by
  apply (publicLowEquivalent_iff_projection machine nextLeft nextRight).2
  exact ⟨hpc, hhalted, htrapped, hstack, hleftSize, hrightSize, hstreams, hprojection⟩

/-- Public-low equivalence exposes equality of the entire declared Public projection. -/
theorem publicProjection_eq_of_low {machine : SemanticProgram} {left right : State}
    (hlow : PublicLowEquivalent machine left right) :
    publicProjection machine left = publicProjection machine right :=
  (publicLowEquivalent_iff_projection machine left right).1 hlow |>.2.2.2.2.2.2.2

/-- The scalar-size and immutable-stream facts carried by Public-low equivalence. -/
theorem publicLow_storage_facts {machine : SemanticProgram} {left right : State}
    (hlow : PublicLowEquivalent machine left right) :
    left.values.size = machine.valueLabels.size ∧
      right.values.size = machine.valueLabels.size ∧
      left.externalInputs = right.externalInputs := by
  have h := (publicLowEquivalent_iff_projection machine left right).1 hlow
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- Static acceptance and active-state well-formedness provide the shape facts needed after one
    real raw step. -/
theorem accepted_step_shape_facts {machine : SemanticProgram} {left right : State}
    (hstatic : OperationalStaticSafe machine)
    (hleft : StateWellFormed machine left) (hright : StateWellFormed machine right)
    (hstreams : left.externalInputs = right.externalInputs) :
    (step machine left).state.values.size = machine.valueLabels.size ∧
      (step machine right).state.values.size = machine.valueLabels.size ∧
      (step machine left).state.externalInputs =
        (step machine right).state.externalInputs := by
  have hleftNext := state_well_formed_preserved hstatic.1.1 hleft
  have hrightNext := state_well_formed_preserved hstatic.1.1 hright
  refine ⟨hleftNext.1, hrightNext.1, ?_⟩
  rw [PublicRegionSecurity.step_preserves_external_inputs,
    PublicRegionSecurity.step_preserves_external_inputs, hstreams]

/-- Constructor proofs can close a matching raw step by supplying only its load-bearing facts:
    control/stack agreement, full projection agreement, and the exact Public boundary trace. -/
theorem matching_step_of_projection {machine : SemanticProgram} {left right : State}
    (hstatic : OperationalStaticSafe machine)
    (hleft : StateWellFormed machine left) (hright : StateWellFormed machine right)
    (hlow : PublicLowEquivalent machine left right)
    (hprojection : publicProjection machine (step machine left).state =
      publicProjection machine (step machine right).state)
    (hpc : (step machine left).state.pc = (step machine right).state.pc)
    (hhalted : (step machine left).state.halted = (step machine right).state.halted)
    (htrapped : (step machine left).state.trapped = (step machine right).state.trapped)
    (hstack : CallStackPublicEquivalent machine
      (step machine left).state.callStack (step machine right).state.callStack)
    (hevents : publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hstorage := publicLow_storage_facts hlow
  have hshape := accepted_step_shape_facts hstatic hleft hright hstorage.2.2
  exact ⟨publicLowEquivalent_of_projection_and_control hshape.1 hshape.2.1 hshape.2.2
    hprojection hpc hhalted htrapped hstack, hevents⟩

/-- A list of verifier-owned Public cells has equal decoded values in Public-equivalent states. -/
theorem readProgramValues_eq_of_cellsPublic {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) {cells : List UInt32}
    (hbounds : ∀ cell ∈ cells, cell.toNat < machine.valueLabels.size)
    (hpublic : CellsPublic machine cells) :
    cells.map (readProgramValue machine left) =
      cells.map (readProgramValue machine right) :=
  readProgramValues_eq_of_public_data hdata cells hbounds hpublic

/-- Every selected policy operand is also an ordinary decoded value operand. -/
theorem policyOperandCells_subset_valueOperandCells (machine : SemanticProgram)
    (instruction : Instruction) (classCode : UInt32) :
    ∀ cell ∈ policyOperandCells machine instruction classCode,
      cell ∈ valueOperandCells machine instruction := by
  intro cell hcell
  unfold policyOperandCells at hcell
  simp only [List.mem_filterMap] at hcell
  obtain ⟨position, hposition, hselected⟩ := hcell
  by_cases hpolicy : policySelectsPosition machine instruction.id classCode position = true
  · simp only [hpolicy, Bool.not_true, Bool.false_eq_true, if_false] at hselected
    cases hoperand : instructionOperandAt? machine instruction position with
    | none => simp [hoperand] at hselected
    | some operand =>
        simp only [hoperand] at hselected
        by_cases hkind : operand.kind = 0
        · have hvalue : operand.value = cell := by simpa [hkind] using hselected
          rw [← hvalue]
          unfold valueOperandCells instructionOperands
          simp only [List.mem_filterMap]
          exact ⟨operand, ⟨position, hposition, hoperand⟩, by simp [hkind]⟩
        · simp [hkind] at hselected
  · have hpolicyFalse : policySelectsPosition machine instruction.id classCode position = false := by
      cases hvalue : policySelectsPosition machine instruction.id classCode position
      · rfl
      · exact False.elim (hpolicy hvalue)
    simp [hpolicyFalse] at hselected

/-- Policy slices inherit the operand bounds checked by the semantic decoder. -/
theorem policyOperandCells_bounded {machine : SemanticProgram} {instruction : Instruction}
    (hwell : instructionWellFormed machine instruction) (classCode : UInt32) {cell : UInt32}
    (hcell : cell ∈ policyOperandCells machine instruction classCode) :
    cell.toNat < machine.valueLabels.size :=
  valueOperandCells_bounded hwell
    (policyOperandCells_subset_valueOperandCells machine instruction classCode cell hcell)

/-- A Public policy slice is read identically, including its decoded labels and list shape. -/
theorem policyOperandValues_eq_of_cellsPublic {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) {instruction : Instruction}
    (hwell : instructionWellFormed machine instruction) (classCode : UInt32)
    (hpublic : CellsPublic machine (policyOperandCells machine instruction classCode)) :
    policyOperandValues machine left instruction classCode =
      policyOperandValues machine right instruction classCode := by
  unfold policyOperandValues
  exact readProgramValues_eq_of_cellsPublic hdata
    (fun cell hcell => policyOperandCells_bounded hwell classCode hcell) hpublic

/-- The complete ordinary value operand list is identical when the verifier proves it Public. -/
theorem operandValues_eq_of_cellsPublic {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) {instruction : Instruction}
    (hwell : instructionWellFormed machine instruction)
    (hpublic : CellsPublic machine (valueOperandCells machine instruction)) :
    operandValues machine left instruction = operandValues machine right instruction := by
  unfold operandValues
  exact readProgramValues_eq_of_cellsPublic hdata
    (fun cell hcell => valueOperandCells_bounded hwell hcell) hpublic

/-- Pointwise updates preserve a masked-array equality when their payloads agree whenever the
    updated position is visible.  Hidden cells may receive unrelated raw values. -/
theorem maskedCells_setIfInBounds_pair_congr {alpha beta : Type}
    (visible : Nat → Bool) (payload : alpha → beta) {left right : Array alpha}
    (position : Nat) (leftValue rightValue : alpha)
    (heq : maskedCells visible payload left = maskedCells visible payload right)
    (hvalue : visible position = true → payload leftValue = payload rightValue) :
    maskedCells visible payload (left.setIfInBounds position leftValue) =
      maskedCells visible payload (right.setIfInBounds position rightValue) := by
  have hsize : left.size = right.size := by
    simpa [maskedCells] using congrArg Array.size heq
  apply Array.ext
  · simp [maskedCells, hsize]
  · intro index hleft hright
    have hleftBound : index < left.size := by simpa [maskedCells] using hleft
    have hrightBound : index < right.size := by simpa [maskedCells] using hright
    by_cases hindex : index = position
    · subst index
      by_cases hvisible : visible position = true
      · simp [maskedCells, hvisible, hvalue hvisible]
      · have hvisibleFalse : visible position = false := by
          cases h : visible position
          · rfl
          · exact False.elim (hvisible h)
        simp [maskedCells, hvisibleFalse]
    · have hcell := congrArg (fun cells => cells[index]?) heq
      have hne : position ≠ index := Ne.symm hindex
      simpa [maskedCells, hleftBound, hrightBound, hindex, hne] using hcell

/-- Restoring corresponding verifier-related frame saves preserves the complete Public
    projection.  Public saved payloads agree; private saved payloads remain masked. -/
theorem restoreValues_preserves_publicProjection_eq_of_savedPublic
    (machine : SemanticProgram) {left right : State}
    {leftSaved rightSaved : List (UInt32 × Value)}
    (heq : publicProjection machine left = publicProjection machine right)
    (hsaved : SavedPublicEquivalent machine leftSaved rightSaved) :
    publicProjection machine (restoreValues left leftSaved) =
      publicProjection machine (restoreValues right rightSaved) := by
  induction leftSaved generalizing rightSaved left right with
  | nil => cases rightSaved <;> simp_all [SavedPublicEquivalent, restoreValues]
  | cons leftHead leftRest ih =>
      cases rightSaved with
      | nil => simp [SavedPublicEquivalent] at hsaved
      | cons rightHead rightRest =>
          rcases leftHead with ⟨leftCell, leftValue⟩
          rcases rightHead with ⟨rightCell, rightValue⟩
          simp only [SavedPublicEquivalent] at hsaved
          rcases hsaved with ⟨hcell, hpayload, hrest⟩
          subst rightCell
          simp only [restoreValues]
          apply ih
          · simp only [publicProjection, PublicProjection.mk.injEq] at heq ⊢
            refine ⟨?_, heq.2.1, heq.2.2.1, heq.2.2.2⟩
            apply maskedCells_setIfInBounds_pair_congr
              (fun position =>
                (labelAt machine.valueLabels (UInt32.ofNat position)).eqb .pub)
              Value.payload leftCell.toNat leftValue rightValue heq.1
            intro hvisible
            have hroundtrip : UInt32.ofNat leftCell.toNat = leftCell := by simp
            rw [hroundtrip, label_eqb_true_iff] at hvisible
            exact hpayload hvisible
          · exact hrest

/-- Writing equal payloads to the same decoded destination preserves equality of the full Public
    projection, whether that destination is Public, private, absent, or out of bounds. -/
theorem writeDestination_preserves_publicProjection_eq {machine : SemanticProgram}
    {left right : State} (instruction : Instruction) {leftPayload rightPayload : Int}
    (hprojection : publicProjection machine left = publicProjection machine right)
    (hpayload : leftPayload = rightPayload) :
    publicProjection machine (writeDestination left instruction leftPayload) =
      publicProjection machine (writeDestination right instruction rightPayload) := by
  subst rightPayload
  by_cases hdestination : instruction.destination = 0
  · simpa [writeDestination, hdestination] using hprojection
  · simp only [publicProjection, PublicProjection.mk.injEq] at hprojection ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [writeDestination, beq_iff_eq, hdestination, ↓reduceIte]
      exact maskedCells_setIfInBounds_congr
        (fun cell => (labelAt machine.valueLabels (UInt32.ofNat cell)).eqb .pub)
        Value.payload instruction.destination.toNat
        ⟨instruction.resultLabel, leftPayload⟩ hprojection.1
    · simpa only [writeDestination_aggregates] using hprojection.2.1
    · simpa only [writeDestination_actorState] using hprojection.2.2.1
    · simpa only [writeDestination_externalCursors] using hprojection.2.2.2

@[simp] theorem writeDestination_values_size (state : State) (instruction : Instruction)
    (payload : Int) :
    (writeDestination state instruction payload).values.size = state.values.size := by
  by_cases hdestination : instruction.destination = 0 <;>
    simp [writeDestination, hdestination]

/-- A decoded destination only requires payload equality when that destination is statically
    Public.  Private result cells may differ and remain absent from the complete projection. -/
theorem writeDestination_preserves_publicProjection_eq_if_public
    {machine : SemanticProgram} {left right : State} (instruction : Instruction)
    {leftPayload rightPayload : Int}
    (hprojection : publicProjection machine left = publicProjection machine right)
    (hpayload : instruction.destination ≠ 0 →
      labelAt machine.valueLabels instruction.destination = .pub →
      leftPayload = rightPayload) :
    publicProjection machine (writeDestination left instruction leftPayload) =
      publicProjection machine (writeDestination right instruction rightPayload) := by
  by_cases hdestination : instruction.destination = 0
  · simpa [writeDestination, hdestination] using hprojection
  · simp only [publicProjection, PublicProjection.mk.injEq] at hprojection ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [writeDestination, beq_iff_eq, hdestination, ↓reduceIte]
      apply maskedCells_setIfInBounds_pair_congr
        (fun cell => (labelAt machine.valueLabels (UInt32.ofNat cell)).eqb .pub)
        Value.payload instruction.destination.toNat
        ⟨instruction.resultLabel, leftPayload⟩ ⟨instruction.resultLabel, rightPayload⟩
        hprojection.1
      intro hvisible
      have hroundtrip : UInt32.ofNat instruction.destination.toNat =
          instruction.destination := by simp
      rw [hroundtrip, label_eqb_true_iff] at hvisible
      exact hpayload hdestination hvisible
    · simpa only [writeDestination_aggregates] using hprojection.2.1
    · simpa only [writeDestination_actorState] using hprojection.2.2.1
    · simpa only [writeDestination_externalCursors] using hprojection.2.2.2

/-- Corresponding internal-return frames restore their related saved cells and then write the
    returned payload.  Equality is needed only when the shared destination is Public. -/
theorem internalReturnStorage_preserves_publicProjection_eq
    {machine : SemanticProgram} {left right : State}
    {leftFrame rightFrame : CallFrame} {leftPayload rightPayload : Int}
    (hprojection : publicProjection machine left = publicProjection machine right)
    (hframe : CallFramePublicEquivalent machine leftFrame rightFrame)
    (hpayload : leftFrame.destination ≠ 0 →
      labelAt machine.valueLabels leftFrame.destination = .pub →
      leftPayload = rightPayload) :
    let leftRestored := restoreValues left leftFrame.savedParameters
    let rightRestored := restoreValues right rightFrame.savedParameters
    let leftValues := leftRestored.values.setIfInBounds leftFrame.destination.toNat
      ⟨labelAt machine.valueLabels leftFrame.destination, leftPayload⟩
    let rightValues := rightRestored.values.setIfInBounds rightFrame.destination.toNat
      ⟨labelAt machine.valueLabels rightFrame.destination, rightPayload⟩
    let leftReturned := if leftFrame.destination == 0 then leftRestored else
      { leftRestored with values := leftValues }
    let rightReturned := if rightFrame.destination == 0 then rightRestored else
      { rightRestored with values := rightValues }
    publicProjection machine leftReturned = publicProjection machine rightReturned := by
  rcases hframe with ⟨hreturnPc, hdestination, hcallee, hreturnLabel, hsaved⟩
  rw [← hdestination]
  dsimp only
  have hrestored := restoreValues_preserves_publicProjection_eq_of_savedPublic
    machine hprojection hsaved
  by_cases hzero : leftFrame.destination = 0
  · simpa [hzero] using hrestored
  · simp only [beq_iff_eq, hzero, ↓reduceIte]
    let destinationInstruction : Instruction :=
      { op := .scalar, id := 0, functionId := 0, blockId := 0,
        destination := leftFrame.destination, firstOperand := 0, operandCount := 0,
        target := 0, resultLabel := labelAt machine.valueLabels leftFrame.destination,
        aux := 0 }
    have hwrite := writeDestination_preserves_publicProjection_eq_if_public
      destinationInstruction hrestored (fun _ => hpayload hzero)
    simpa [destinationInstruction, writeDestination, hzero] using hwrite

/-- A pair of genuine internal returns is a matching Public step.  The only payload premise is
    conditional on the shared return destination being Public; verifier-derived return facts
    discharge it in the production composition layer. -/
theorem matching_internal_return {machine : SemanticProgram} {left right : State}
    {instruction : Instruction} {leftFrame rightFrame : CallFrame}
    {leftRest rightRest : List CallFrame}
    (hstatic : OperationalStaticSafe machine)
    (hleftWellFormed : StateWellFormed machine left)
    (hrightWellFormed : StateWellFormed machine right)
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (houtput : instruction.op = .output)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hleftStack : left.callStack = leftFrame :: leftRest)
    (hrightStack : right.callStack = rightFrame :: rightRest)
    (hleftFlow : (operandValue machine left instruction).label.flowsTo
      leftFrame.returnLabel = true)
    (hrightFlow : (operandValue machine right instruction).label.flowsTo
      rightFrame.returnLabel = true)
    (hpayload : leftFrame.destination ≠ 0 →
      labelAt machine.valueLabels leftFrame.destination = .pub →
      (operandValue machine left instruction).payload =
        (operandValue machine right instruction).payload) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  have hstackEquivalent := hlow.2.2.2.1
  rw [hleftStack, hrightStack] at hstackEquivalent
  simp only [CallStackPublicEquivalent] at hstackEquivalent
  rcases hstackEquivalent with ⟨hframe, hrest⟩
  have hdestination : leftFrame.destination = rightFrame.destination := hframe.2.1
  have hprojection := internalReturnStorage_preserves_publicProjection_eq
    (publicProjection_eq_of_low hlow) hframe hpayload
  have hstepProjection :
      publicProjection machine (step machine left).state =
        publicProjection machine (step machine right).state := by
    simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, houtput, hleftStack, hrightStack,
      hleftFlow, hrightFlow, publicProjection] using hprojection
  apply matching_step_of_projection hstatic hleftWellFormed hrightWellFormed hlow
    hstepProjection
  · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, houtput, hleftStack, hrightStack,
      hleftFlow, hrightFlow] using hframe.1
  · by_cases hzero : leftFrame.destination = 0
    · have hrightZero : rightFrame.destination = 0 := hdestination.symm.trans hzero
      simp [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, houtput, hleftStack, hrightStack,
        hleftFlow, hrightFlow, hzero, hrightZero]
    · have hrightZero : rightFrame.destination ≠ 0 := by
        intro heq
        exact hzero (hdestination.trans heq)
      simp [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, houtput, hleftStack, hrightStack,
        hleftFlow, hrightFlow, hzero, hrightZero]
  · by_cases hzero : leftFrame.destination = 0
    · have hrightZero : rightFrame.destination = 0 := hdestination.symm.trans hzero
      simp [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, houtput, hleftStack, hrightStack,
        hleftFlow, hrightFlow, hzero, hrightZero]
    · have hrightZero : rightFrame.destination ≠ 0 := by
        intro heq
        exact hzero (hdestination.trans heq)
      simp [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, houtput, hleftStack, hrightStack,
        hleftFlow, hrightFlow, hzero, hrightZero]
  · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, houtput, hleftStack, hrightStack,
      hleftFlow, hrightFlow] using hrest
  · simp [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, houtput, hleftStack, hrightStack,
      hleftFlow, hrightFlow, publicBoundaryTrace]

/-- Equal aggregate payloads written to the same cell preserve the complete projection. -/
theorem aggregateWrite_preserves_publicProjection_eq {machine : SemanticProgram}
    {left right : State} (cell : UInt32) {leftPayload rightPayload : List Int}
    (hprojection : publicProjection machine left = publicProjection machine right)
    (hpayload : leftPayload = rightPayload) :
    publicProjection machine
        { left with aggregates := left.aggregates.setIfInBounds cell.toNat leftPayload } =
      publicProjection machine
        { right with aggregates := right.aggregates.setIfInBounds cell.toNat rightPayload } := by
  subst rightPayload
  simp only [publicProjection, PublicProjection.mk.injEq] at hprojection ⊢
  refine ⟨hprojection.1, ?_, hprojection.2.2.1, hprojection.2.2.2⟩
  exact maskedCells_setIfInBounds_congr
    (fun position => (labelAt machine.valueLabels (UInt32.ofNat position)).eqb .pub)
    id cell.toNat leftPayload hprojection.2.1

/-- Aggregate result payloads need agree only for a statically Public aggregate cell. -/
theorem aggregateWrite_preserves_publicProjection_eq_if_public
    {machine : SemanticProgram} {left right : State} (cell : UInt32)
    {leftPayload rightPayload : List Int}
    (hprojection : publicProjection machine left = publicProjection machine right)
    (hpayload : labelAt machine.valueLabels cell = .pub → leftPayload = rightPayload) :
    publicProjection machine
        { left with aggregates := left.aggregates.setIfInBounds cell.toNat leftPayload } =
      publicProjection machine
        { right with aggregates := right.aggregates.setIfInBounds cell.toNat rightPayload } := by
  simp only [publicProjection, PublicProjection.mk.injEq] at hprojection ⊢
  refine ⟨hprojection.1, ?_, hprojection.2.2.1, hprojection.2.2.2⟩
  apply maskedCells_setIfInBounds_pair_congr
    (fun position => (labelAt machine.valueLabels (UInt32.ofNat position)).eqb .pub)
    id cell.toNat leftPayload rightPayload hprojection.2.1
  intro hvisible
  have hroundtrip : UInt32.ofNat cell.toNat = cell := by simp
  rw [hroundtrip, label_eqb_true_iff] at hvisible
  exact hpayload hvisible

/-- Binary algebra for an ordinary raw constructor.  Static verifier facts are used by callers
    to discharge the three dependency premises; this lemma performs no policy assumption. -/
theorem ordinaryStep_preserves_publicLowEquivalent
    {machine : SemanticProgram} {left right : State}
    (hlow : PublicLowEquivalent machine left right) (instruction : Instruction)
    (hpayload : instruction.destination ≠ 0 →
      labelAt machine.valueLabels instruction.destination = .pub →
      instructionPayload machine left instruction =
        instructionPayload machine right instruction)
    (haggregate : instruction.op = .aggregate →
      instruction.destination ≠ 0 →
      labelAt machine.valueLabels instruction.destination = .pub →
      operandPayloads machine left instruction = operandPayloads machine right instruction)
    (hnext : nextPc machine left instruction (operandValue machine left instruction) =
      nextPc machine right instruction (operandValue machine right instruction))
    (htraps : (if instruction.op == .trap then
        (operandValues machine left instruction).isEmpty ||
          (operandValue machine left instruction).payload != 0 else false) =
      (if instruction.op == .trap then
        (operandValues machine right instruction).isEmpty ||
          (operandValue machine right instruction).payload != 0 else false)) :
    PublicLowEquivalent machine (ordinaryStep machine left instruction).state
      (ordinaryStep machine right instruction).state := by
  have hbase := writeDestination_preserves_publicProjection_eq_if_public instruction
    (publicProjection_eq_of_low hlow) hpayload
  have hprojection :
      publicProjection machine (ordinaryStep machine left instruction).state =
        publicProjection machine (ordinaryStep machine right instruction).state := by
    by_cases hcondition : instruction.op == .aggregate && instruction.destination != 0
    · have hparts : (instruction.op == .aggregate) = true ∧
          (instruction.destination != 0) = true := by
        simpa only [Bool.and_eq_true] using hcondition
      have hkind : instruction.op = .aggregate := by
        exact (Semantic.semanticInstrOp_beq_true_iff instruction.op .aggregate).mp hparts.1
      have hdestination : instruction.destination ≠ 0 := (bne_iff_ne).mp hparts.2
      have haggregateProjection := aggregateWrite_preserves_publicProjection_eq_if_public
        instruction.destination hbase (haggregate hkind hdestination)
      simpa [ordinaryStep, hcondition, publicProjection] using haggregateProjection
    · simpa [ordinaryStep, hcondition, publicProjection] using hbase
  have hprojectionFacts :=
    (publicLowEquivalent_iff_projection machine left right).1 hlow
  apply (publicLowEquivalent_iff_projection machine
    (ordinaryStep machine left instruction).state
    (ordinaryStep machine right instruction).state).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hprojection⟩
  · simpa [ordinaryStep] using hnext
  · simp [ordinaryStep]
  · simpa [ordinaryStep] using htraps
  · simpa [ordinaryStep] using hlow.2.2.2.1
  · simpa [ordinaryStep] using hprojectionFacts.2.2.2.2.1
  · simpa [ordinaryStep] using hprojectionFacts.2.2.2.2.2.1
  · simpa [ordinaryStep] using hprojectionFacts.2.2.2.2.2.2.1

/-- Equal actor-state payloads written to the same offset preserve the complete projection. -/
theorem actorStateWrite_preserves_publicProjection_eq {machine : SemanticProgram}
    {left right : State} (offset : Nat) {leftValue rightValue : Value}
    (hprojection : publicProjection machine left = publicProjection machine right)
    (hvalue : leftValue = rightValue) :
    publicProjection machine
        { left with actorState := left.actorState.setIfInBounds offset leftValue } =
      publicProjection machine
        { right with actorState := right.actorState.setIfInBounds offset rightValue } := by
  subst rightValue
  simp only [publicProjection, PublicProjection.mk.injEq] at hprojection ⊢
  refine ⟨hprojection.1, hprojection.2.1, ?_, hprojection.2.2.2⟩
  exact maskedCells_setIfInBounds_congr
    (fun position => (stateLabelAt machine (UInt32.ofNat position)).eqb .pub)
    Value.payload offset leftValue hprojection.2.2.1

/-- Advancing the same Public site in states with equal streams and Public projections preserves
    the complete projection.  Missing and exhausted streams take the same deterministic branch. -/
theorem advanceExternal_preserves_publicProjection_eq {machine : SemanticProgram}
    {left right : State} {site : UInt32}
    (hleftSize : left.values.size = machine.valueLabels.size)
    (hrightSize : right.values.size = machine.valueLabels.size)
    (hstreams : left.externalInputs = right.externalInputs)
    (hprojection : publicProjection machine left = publicProjection machine right)
    (hpublic : externalSiteLabel machine site.toNat = .pub) :
    publicProjection machine (advanceExternal left site) =
      publicProjection machine (advanceExternal right site) := by
  have hdata : PublicDataEquivalent machine left right :=
    (publicDataEquivalent_iff_projection machine left right).2
      ⟨hleftSize, hrightSize, hstreams, hprojection⟩
  rcases hdata.1 with ⟨hinputs, hcursorSize, hcursors⟩
  have hcursor : left.externalCursors.getD site.toNat 0 =
      right.externalCursors.getD site.toNat 0 := by
    by_cases hleftBound : site.toNat < left.externalCursors.size
    · have hrightBound : site.toNat < right.externalCursors.size := by
        simpa [hcursorSize] using hleftBound
      have hindexed := hcursors site.toNat hleftBound hrightBound hpublic
      simpa [Array.getD, hleftBound, hrightBound] using hindexed
    · have hrightBound : ¬ site.toNat < right.externalCursors.size := by
        simpa [hcursorSize] using hleftBound
      simp [Array.getD, hleftBound, hrightBound]
  have hstream : left.externalInputs.getD site.toNat [] =
      right.externalInputs.getD site.toNat [] := by simp [hinputs]
  unfold advanceExternal
  dsimp only
  rw [hcursor, hstream]
  split
  · simp only [publicProjection, PublicProjection.mk.injEq] at hprojection ⊢
    refine ⟨hprojection.1, hprojection.2.1, hprojection.2.2.1, ?_⟩
    exact maskedCells_setIfInBounds_congr
      (fun position => (externalSiteLabel machine position).eqb .pub)
      id site.toNat (right.externalCursors.getD site.toNat 0 + 1) hprojection.2.2.2
  · exact hprojection

/-- The optional payload of a Public boundary observation agrees for any shared decoded cell.
    Non-Public payloads remain `none`; they are not required to be equal. -/
theorem observationPayload_readProgramValue_eq {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) {cell : UInt32}
    (hbound : cell.toNat < machine.valueLabels.size) :
    observationPayload (readProgramValue machine left cell) =
      observationPayload (readProgramValue machine right cell) := by
  by_cases hpublic : labelAt machine.valueLabels cell = .pub
  · rw [readProgramValue_eq_of_public_data hdata hbound hpublic]
  · cases hlabel : labelAt machine.valueLabels cell <;>
      simp_all [observationPayload, readProgramValue, Label.eqb]

/-- A Public actor occurrence has the same complete observation list under Public data
    equivalence, even when some payload contracts are non-Public. -/
theorem boundaryObservations_policyOperands_eq {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) {instruction : Instruction}
    (hwell : instructionWellFormed machine instruction) (classCode : UInt32) :
    boundaryObservations instruction.id
        (policyOperandValues machine left instruction classCode) =
      boundaryObservations instruction.id
        (policyOperandValues machine right instruction classCode) := by
  unfold boundaryObservations policyOperandValues
  simp only [List.map_map]
  apply List.map_congr_left
  intro cell hcell
  exact congrArg
    (fun payload : Option Int =>
      ({ kind := .boundary, site := instruction.id, payload } : PublicBoundaryObservation))
    (observationPayload_readProgramValue_eq hdata
      (policyOperandCells_bounded hwell classCode hcell))

/-! ## Verifier-derived Public result dependencies -/

/-- The executable dependency bit is reflected back into the declarative cell predicate used by
    the binary raw-step algebra. -/
theorem cellsPublic_of_cellsPublicB {machine : SemanticProgram} {cells : List UInt32}
    (h : OccurrenceKernel.cellsPublicB machine cells = true) : CellsPublic machine cells :=
  (cellsPublicB_iff machine cells).1 h

/-- For every ordinary result-producing constructor, v9 acceptance makes the exact payload read
    identically whenever the destination is part of the Public projection. Calls, external reads,
    state reads, and explicit releases have dedicated transition lemmas because their payload is
    not computed solely from this instruction's ordinary operand slice. -/
theorem instructionPayload_eq_of_public_dependencies
    {program : V9.Program} {analysis : OccurrenceDataflowInvocation.Analysis}
    {machine : SemanticProgram} {left right : State} {instruction : Instruction}
    (hdata : PublicDataEquivalent machine left right)
    (hwell : instructionWellFormed machine instruction)
    (hsafe : PublicResultDependenciesSafe program analysis machine instruction)
    (hdestination : instruction.destination ≠ 0)
    (hpublic : labelAt machine.valueLabels instruction.destination = .pub)
    (hordinary : instruction.op ≠ .ffi ∧ instruction.op ≠ .actorBoundary ∧
      instruction.op ≠ .call ∧ instruction.op ≠ .closure ∧
      instruction.op ≠ .stateRead ∧ instruction.op ≠ .release ∧
      instruction.op ≠ .releaseCT) :
    instructionPayload machine left instruction =
      instructionPayload machine right instruction := by
  have hresult : instruction.resultLabel = .pub := hwell.2.2.1.trans hpublic
  have hbody := hsafe hdestination hresult
  rcases hordinary with ⟨hffi, hactor, hcall, hclosure, hstateRead, hrelease, hreleaseCT⟩
  generalize hop : instruction.op = operation at *
  cases operation <;> simp_all [publicResultDependencyBodyOK]
  case allocation =>
    have hcells : CellsPublic machine (policyOperandCells machine instruction 9) :=
      cellsPublic_of_cellsPublicB hbody
    have heq := policyOperandValues_eq_of_cellsPublic hdata hwell 9 hcells
    simp [instructionPayload, hop, heq]
  all_goals
    have hcells : CellsPublic machine (valueOperandCells machine instruction) :=
      cellsPublic_of_cellsPublicB hbody
    have heq := operandValues_eq_of_cellsPublic hdata hwell hcells
    simp [instructionPayload, hop, heq]

/-- Aggregate storage carries the complete operand payload list, so a Public aggregate result
    uses the same verifier-owned dependency slice as its scalar hash result. -/
theorem aggregateOperandPayloads_eq_of_public_dependencies
    {program : V9.Program} {analysis : OccurrenceDataflowInvocation.Analysis}
    {machine : SemanticProgram} {left right : State} {instruction : Instruction}
    (hdata : PublicDataEquivalent machine left right)
    (hwell : instructionWellFormed machine instruction)
    (hsafe : PublicResultDependenciesSafe program analysis machine instruction)
    (haggregate : instruction.op = .aggregate)
    (hdestination : instruction.destination ≠ 0)
    (hpublic : labelAt machine.valueLabels instruction.destination = .pub) :
    operandPayloads machine left instruction =
      operandPayloads machine right instruction := by
  have hresult : instruction.resultLabel = .pub := hwell.2.2.1.trans hpublic
  have hbody := hsafe hdestination hresult
  have hcellsB : cellsPublicB machine (valueOperandCells machine instruction) = true := by
    simpa [publicResultDependencyBodyOK, haggregate] using hbody
  have heq := operandValues_eq_of_cellsPublic hdata hwell
    (cellsPublic_of_cellsPublicB hcellsB)
  exact congrArg (List.map Value.payload) heq

/-! ## Matching call entry -/

/-- Pointwise relation on actual call arguments. Labels are program-derived and therefore agree;
    payloads agree exactly when the argument cell is Public. -/
def ValueListPublicEquivalent : List Value → List Value → Prop
  | [], [] => True
  | left :: leftRest, right :: rightRest =>
      left.label = right.label ∧
        (left.label = .pub → left.payload = right.payload) ∧
        ValueListPublicEquivalent leftRest rightRest
  | _, _ => False

theorem readValue_payload_eq_of_public_data {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) {cell : UInt32}
    (hbound : cell.toNat < machine.valueLabels.size)
    (hpublic : labelAt machine.valueLabels cell = .pub) :
    (readValue left cell).payload = (readValue right cell).payload := by
  have h := congrArg Value.payload
    (readProgramValue_eq_of_public_data hdata hbound hpublic)
  simpa [readProgramValue] using h

/-- Saving the same decoded parameter list in Public-equivalent states creates genuinely related
    frames. This fact is what makes returning restore the caller's complete Public view. -/
theorem saveValues_publicEquivalent {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) {cells : List UInt32}
    (hbounds : ∀ cell ∈ cells, cell.toNat < machine.valueLabels.size) :
    SavedPublicEquivalent machine (saveValues left cells) (saveValues right cells) := by
  induction cells with
  | nil => trivial
  | cons cell rest ih =>
      refine ⟨rfl, ?_, ih (fun candidate hmember =>
        hbounds candidate (List.mem_cons_of_mem cell hmember))⟩
      intro hpublic
      exact readValue_payload_eq_of_public_data hdata (hbounds cell (by simp)) hpublic

/-- Mapping any bounded decoded cell list through the raw accessor preserves Public argument
    equivalence. -/
theorem readProgramValues_publicEquivalent {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) (cells : List UInt32)
    (hbounds : ∀ cell ∈ cells, cell.toNat < machine.valueLabels.size) :
    ValueListPublicEquivalent (cells.map (readProgramValue machine left))
      (cells.map (readProgramValue machine right)) := by
  induction cells with
  | nil => trivial
  | cons cell rest ih =>
      refine ⟨rfl, ?_, ih (fun candidate hmember =>
        hbounds candidate (List.mem_cons_of_mem cell hmember))⟩
      intro hpublic
      exact congrArg Value.payload (readProgramValue_eq_of_public_data hdata
        (hbounds cell (by simp)) hpublic)

/-- Reading a well-formed operand slice in two Public-equivalent states yields argument lists with
    identical labels and identical Public payloads. -/
theorem operandValues_publicEquivalent {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) {instruction : Instruction}
    (hwell : instructionWellFormed machine instruction) :
    ValueListPublicEquivalent (operandValues machine left instruction)
      (operandValues machine right instruction) := by
  exact readProgramValues_publicEquivalent hdata (valueOperandCells machine instruction)
    (fun cell hcell => valueOperandCells_bounded hwell hcell)

/-- Public argument equivalence determines exactly the optional payload exposed by the head
    operand.  This is deliberately weaker than raw `Value` equality: a non-Public output still
    has an observable occurrence and site, but its payload remains absent from the Public trace. -/
theorem ValueListPublicEquivalent.head_observation {left right : List Value}
    (h : ValueListPublicEquivalent left right) :
    observationPayload (left.head?.getD defaultValue) =
      observationPayload (right.head?.getD defaultValue) := by
  cases left with
  | nil =>
      cases right <;> simp_all [ValueListPublicEquivalent]
  | cons leftHead leftRest =>
      cases right with
      | nil => simp [ValueListPublicEquivalent] at h
      | cons rightHead rightRest =>
          rcases h with ⟨hlabel, hpayload, _⟩
          simp only [List.head?_cons, Option.getD_some]
          unfold observationPayload
          rw [← hlabel]
          by_cases hpublic : leftHead.label = .pub
          · simp [hpublic, hpayload hpublic]
          · cases hlabelValue : leftHead.label <;>
              simp_all [Label.eqb]

/-- When the statically derived head label is Public, argument equivalence gives the exact raw
    payload equality needed by a Public return destination. -/
theorem ValueListPublicEquivalent.head_payload_of_public {left right : List Value}
    (h : ValueListPublicEquivalent left right)
    (hpublic : (left.head?.getD defaultValue).label = .pub) :
    (left.head?.getD defaultValue).payload = (right.head?.getD defaultValue).payload := by
  cases left with
  | nil =>
      cases right <;> simp_all [ValueListPublicEquivalent]
  | cons leftHead leftRest =>
      cases right with
      | nil => simp [ValueListPublicEquivalent] at h
      | cons rightHead rightRest =>
          exact h.2.1 (by simpa using hpublic)

/-- The actual head operand of a well-formed instruction has the same Public observation in two
    Public-equivalent states.  No blanket equality of private payloads is introduced. -/
theorem observationPayload_operandValue_eq {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) {instruction : Instruction}
    (hwell : instructionWellFormed machine instruction) :
    observationPayload (operandValue machine left instruction) =
      observationPayload (operandValue machine right instruction) := by
  exact (operandValues_publicEquivalent hdata hwell).head_observation

/-- Production-friendly internal-return rule.  State well-formedness supplies the frame's checked
    return flow; when the shared destination is Public, that forces the actual returned operand
    to be Public, so its payload equality follows from the decoded operand relation. -/
theorem matching_internal_return_of_wellFormed {machine : SemanticProgram}
    {left right : State} {instruction : Instruction} {leftFrame rightFrame : CallFrame}
    {leftRest rightRest : List CallFrame}
    (hstatic : OperationalStaticSafe machine)
    (hleftWellFormed : StateWellFormed machine left)
    (hrightWellFormed : StateWellFormed machine right)
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (houtput : instruction.op = .output)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hleftStack : left.callStack = leftFrame :: leftRest)
    (hrightStack : right.callStack = rightFrame :: rightRest)
    (hleftFlow : (operandValue machine left instruction).label.flowsTo
      leftFrame.returnLabel = true)
    (hrightFlow : (operandValue machine right instruction).label.flowsTo
      rightFrame.returnLabel = true) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hwell := instruction_well_formed_of_raw_static_safe hstatic hlookup
  have hoperands := operandValues_publicEquivalent hlow.2.2.2.2 hwell
  have hframeWellFormed := hleftWellFormed.2.2.2.2 leftFrame (by simp [hleftStack])
  apply matching_internal_return hstatic hleftWellFormed hrightWellFormed hlow hlookup
    houtput hleftLive hrightLive hleftStack hrightStack hleftFlow hrightFlow
  intro hdestination hpublic
  have hreturnFlow : leftFrame.returnLabel.flowsTo
      (labelAt machine.valueLabels leftFrame.destination) = true := by
    have hchecked := hframeWellFormed.2.2.2.1
    simpa [hdestination] using hchecked
  have hreturnPublic : leftFrame.returnLabel = .pub := by
    cases hreturn : leftFrame.returnLabel <;>
      simp_all [Label.flowsTo, Label.rank]
  have hoperandPublic : (operandValue machine left instruction).label = .pub := by
    cases hoperand : (operandValue machine left instruction).label <;>
      simp_all [Label.flowsTo, Label.rank]
  exact hoperands.head_payload_of_public (by simpa [operandValue] using hoperandPublic)

theorem ValueListPublicEquivalent.drop {left right : List Value}
    (h : ValueListPublicEquivalent left right) (count : Nat) :
    ValueListPublicEquivalent (left.drop count) (right.drop count) := by
  induction count generalizing left right with
  | zero => simpa
  | succ count ih =>
      cases left <;> cases right <;> simp_all [ValueListPublicEquivalent]

theorem ValueListPublicEquivalent.length_eq {left right : List Value}
    (h : ValueListPublicEquivalent left right) : left.length = right.length := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [ValueListPublicEquivalent]
  | cons leftHead leftRest ih =>
      cases right with
      | nil => simp [ValueListPublicEquivalent] at h
      | cons rightHead rightRest =>
          simp only [List.length_cons]
          exact congrArg Nat.succ (ih h.2.2)

theorem ValueListPublicEquivalent.argumentLabelsFlow_eq {machine : SemanticProgram}
    {left right : List Value} (h : ValueListPublicEquivalent left right)
    (parameters : List UInt32) :
    argumentLabelsFlow machine left parameters = argumentLabelsFlow machine right parameters := by
  induction left generalizing right parameters with
  | nil => cases right <;> cases parameters <;>
      simp_all [ValueListPublicEquivalent, argumentLabelsFlow]
  | cons leftHead leftRest ih =>
      cases right with
      | nil => cases parameters <;>
          simp_all [ValueListPublicEquivalent, argumentLabelsFlow]
      | cons rightHead rightRest =>
          rcases h with ⟨hlabel, _, hrest⟩
          cases parameters with
          | nil => rfl
          | cons parameter parameters =>
              simp [argumentLabelsFlow, ← hlabel, ih hrest parameters]

theorem callLabelsOK_eq_of_publicEquivalent {machine : SemanticProgram}
    {left right : List Value} (h : ValueListPublicEquivalent left right)
    (instruction : Instruction) (callee : Function) :
    callLabelsOK machine instruction callee left =
      callLabelsOK machine instruction callee right := by
  simp only [callLabelsOK, h.argumentLabelsFlow_eq callee.parameterCells.toList]

/-- A flow-checked argument assigned to a Public parameter has an equal payload. -/
theorem flowing_public_argument_payload_eq {left right : Value} {parameter : Label}
    (hequivalent : left.label = right.label ∧
      (left.label = .pub → left.payload = right.payload))
    (hflow : left.label.flowsTo parameter = true)
    (hpublic : parameter = .pub) : left.payload = right.payload := by
  rcases hequivalent with ⟨hlabel, hpayload⟩
  subst parameter
  cases hleft : left.label with
  | pub => exact hpayload hleft
  | internal => simp [hleft, Label.flowsTo, Label.rank] at hflow
  | secret => simp [hleft, Label.flowsTo, Label.rank] at hflow
  | secretCT => simp [hleft, Label.flowsTo, Label.rank] at hflow

/-- Pairwise parameter assignment preserves the full projection. Private parameters may receive
    different values, while flow checking forces every Public parameter's source to be Public. -/
theorem assignArguments_preserves_publicProjection_eq
    {machine : SemanticProgram} {left right : State}
    {parameters : List UInt32} {leftArguments rightArguments : List Value}
    (hprojection : publicProjection machine left = publicProjection machine right)
    (harguments : ValueListPublicEquivalent leftArguments rightArguments)
    (hflow : argumentLabelsFlow machine leftArguments parameters = true) :
    publicProjection machine (assignArguments machine left parameters leftArguments) =
      publicProjection machine (assignArguments machine right parameters rightArguments) := by
  induction parameters generalizing left right leftArguments rightArguments with
  | nil =>
      cases leftArguments <;> cases rightArguments <;>
        simp_all [assignArguments, argumentLabelsFlow, ValueListPublicEquivalent]
  | cons parameter parameters ih =>
      cases leftArguments with
      | nil => simp [argumentLabelsFlow] at hflow
      | cons leftArgument leftRest =>
          cases rightArguments with
          | nil => simp [ValueListPublicEquivalent] at harguments
          | cons rightArgument rightRest =>
              rcases harguments with ⟨hlabel, hpayload, hrest⟩
              simp only [argumentLabelsFlow, Bool.and_eq_true] at hflow
              simp only [assignArguments]
              apply ih
              · simp only [publicProjection, PublicProjection.mk.injEq] at hprojection ⊢
                refine ⟨?_, hprojection.2.1, hprojection.2.2.1, hprojection.2.2.2⟩
                apply maskedCells_setIfInBounds_pair_congr
                  (fun position =>
                    (labelAt machine.valueLabels (UInt32.ofNat position)).eqb .pub)
                  Value.payload parameter.toNat
                  ⟨labelAt machine.valueLabels parameter, leftArgument.payload⟩
                  ⟨labelAt machine.valueLabels parameter, rightArgument.payload⟩
                  hprojection.1
                intro hvisible
                have hroundtrip : UInt32.ofNat parameter.toNat = parameter := by simp
                rw [hroundtrip, label_eqb_true_iff] at hvisible
                exact flowing_public_argument_payload_eq
                  (left := leftArgument) (right := rightArgument)
                  ⟨hlabel, hpayload⟩ hflow.1 hvisible
              · exact hrest
              · exact hflow.2

/-- A successful call entry to the same decoded callee is a matching Public transition. Dynamic
    closure calls whose private selector chooses different callees are handled as independently
    sized private activation regions instead of using this lemma. -/
theorem enterCall_preserves_publicLowEquivalent {machine : SemanticProgram}
    {left right : State} (hlow : PublicLowEquivalent machine left right)
    (instruction : Instruction) (callee : Function)
    (hcalleeWellFormed : functionWellFormed machine callee)
    (leftArguments rightArguments : List Value)
    (harguments : ValueListPublicEquivalent leftArguments rightArguments)
    (hflow : argumentLabelsFlow machine leftArguments callee.parameterCells.toList = true) :
    PublicLowEquivalent machine
      { assignArguments machine left callee.parameterCells.toList leftArguments with
        pc := callee.firstInstruction.toNat
        callStack :=
          { returnPc := left.pc + 1, destination := instruction.destination,
            calleeId := callee.id, returnLabel := callee.returnLabel,
            savedParameters := saveValues left callee.parameterCells.toList } :: left.callStack }
      { assignArguments machine right callee.parameterCells.toList rightArguments with
        pc := callee.firstInstruction.toNat
        callStack :=
          { returnPc := right.pc + 1, destination := instruction.destination,
            calleeId := callee.id, returnLabel := callee.returnLabel,
            savedParameters := saveValues right callee.parameterCells.toList } :: right.callStack } := by
  have hdata := hlow.2.2.2.2
  have hprojection := assignArguments_preserves_publicProjection_eq
    (publicProjection_eq_of_low hlow) harguments hflow
  have hsaved := saveValues_publicEquivalent hdata hcalleeWellFormed.2.2
  have hstorage := publicLow_storage_facts hlow
  apply publicLowEquivalent_of_projection_and_control
  · simpa using hstorage.1
  · simpa using hstorage.2.1
  · simpa using hstorage.2.2
  · simpa [publicProjection] using hprojection
  · rfl
  · simpa using hlow.2.1
  · simpa using hlow.2.2.1
  · exact ⟨⟨congrArg (fun pc => pc + 1) hlow.1, rfl, rfl, rfl, hsaved⟩,
      hlow.2.2.2.1⟩

/-- Any callee returned by the raw accessor is an actual member of the decoded function table. -/
theorem instructionCallee_mem_functions {machine : SemanticProgram} {state : State}
    {instruction : Instruction} {callee : Function}
    (hcallee : instructionCallee? machine state instruction = some callee) :
    callee ∈ machine.functions := by
  cases hop : instruction.op <;> simp only [instructionCallee?, hop] at hcallee
  case call =>
    rw [Option.bind_eq_some_iff] at hcallee
    obtain ⟨_, _, hfunction⟩ := hcallee
    exact Array.mem_of_find?_eq_some hfunction
  case closure =>
    rw [Option.bind_eq_some_iff] at hcallee
    obtain ⟨_, _, hfunction⟩ := hcallee
    unfold closureFunction? at hfunction
    simp only [bind] at hfunction
    split at hfunction
    · cases hfunction
    · split at hfunction
      · cases hfunction
      · exact Array.mem_of_find?_eq_some hfunction
  all_goals contradiction

/-- A nontrapping raw call/closure step must have resolved a real callee and passed the actual
    arity/label guard.  This is extracted from the raw reducer, not supplied as a static claim. -/
theorem nontrapping_call_step_shape {machine : SemanticProgram} {state : State}
    {instruction : Instruction}
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hoperation : instruction.op = .call ∨ instruction.op = .closure)
    (hlive : state.halted = false ∧ state.trapped = false)
    (hnext : (step machine state).state.trapped = false) :
    ∃ callee,
      instructionCallee? machine state instruction = some callee ∧
        ¬((callArguments machine state instruction).length !=
            callee.parameterCells.size ||
          !callLabelsOK machine instruction callee
            (callArguments machine state instruction)) := by
  rcases hoperation with hcall | hclosure
  · cases hcallee : instructionCallee? machine state instruction with
    | none => simp [step, hlive.1, hlive.2, hlookup, hcall, callStep, hcallee] at hnext
    | some callee =>
        by_cases hguard : (callArguments machine state instruction).length !=
              callee.parameterCells.size ||
            !callLabelsOK machine instruction callee
              (callArguments machine state instruction)
        · simp [step, hlive.1, hlive.2, hlookup, hcall, callStep, hcallee, hguard] at hnext
        · exact ⟨callee, rfl, hguard⟩
  · cases hcallee : instructionCallee? machine state instruction with
    | none => simp [step, hlive.1, hlive.2, hlookup, hclosure, callStep, hcallee] at hnext
    | some callee =>
        by_cases hguard : (callArguments machine state instruction).length !=
              callee.parameterCells.size ||
            !callLabelsOK machine instruction callee
              (callArguments machine state instruction)
        · simp [step, hlive.1, hlive.2, hlookup, hclosure, callStep, hcallee, hguard] at hnext
        · exact ⟨callee, rfl, hguard⟩

/-- A nontrapping internal output has passed the reducer's real return-label guard. -/
theorem nontrapping_internal_output_flow {machine : SemanticProgram} {state : State}
    {instruction : Instruction} {frame : CallFrame} {rest : List CallFrame}
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (houtput : instruction.op = .output)
    (hlive : state.halted = false ∧ state.trapped = false)
    (hstack : state.callStack = frame :: rest)
    (hnext : (step machine state).state.trapped = false) :
    (operandValue machine state instruction).label.flowsTo frame.returnLabel = true := by
  cases hflow : (operandValue machine state instruction).label.flowsTo frame.returnLabel
  · simp [step, hlive.1, hlive.2, hlookup, houtput, hstack, hflow] at hnext
  · rfl

/-- On a nontrapping raw step, the ordinary trap predicate is false.  Away from `.trap` it is
    definitionally false; at `.trap` this follows from the actual successor state. -/
theorem trap_test_eq_of_nontrapping_steps {machine : SemanticProgram} {left right : State}
    {instruction : Instruction}
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hleftNext : (step machine left).state.trapped = false)
    (hrightNext : (step machine right).state.trapped = false) :
    (if instruction.op == .trap then
        (operandValues machine left instruction).isEmpty ||
          (operandValue machine left instruction).payload != 0 else false) =
      (if instruction.op == .trap then
        (operandValues machine right instruction).isEmpty ||
          (operandValue machine right instruction).payload != 0 else false) := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  by_cases htrap : instruction.op = .trap
  · have hleftFalse :
        ((operandValues machine left instruction).isEmpty ||
          (operandValue machine left instruction).payload != 0) = false := by
      simpa [step, hleftLive.1, hleftLive.2, hlookup, htrap, ordinaryStep] using hleftNext
    have hrightFalse :
        ((operandValues machine right instruction).isEmpty ||
          (operandValue machine right instruction).payload != 0) = false := by
      simpa [step, hrightLive.1, hrightLive.2, hrightLookup, htrap, ordinaryStep] using hrightNext
    simp [htrap, hleftFalse, hrightFalse]
  · generalize hop : instruction.op = operation at htrap ⊢
    cases operation <;> simp_all

/-- Same-callee call entry is a complete matching raw step. Failed or private-selector calls are
    classified separately by successful-execution/region composition; this lemma never assumes a
    fabricated target or hides a trap. -/
theorem matching_call_step_same_callee {machine : SemanticProgram} {left right : State}
    {instruction : Instruction} {callee : Function}
    (hstatic : OperationalStaticSafe machine)
    (hleftWellFormed : StateWellFormed machine left)
    (hrightWellFormed : StateWellFormed machine right)
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hoperation : instruction.op = .call ∨ instruction.op = .closure)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hleftCallee : instructionCallee? machine left instruction = some callee)
    (hrightCallee : instructionCallee? machine right instruction = some callee)
    (hleftGuard : ¬((callArguments machine left instruction).length !=
        callee.parameterCells.size ||
      !callLabelsOK machine instruction callee (callArguments machine left instruction)))
    (hrightGuard : ¬((callArguments machine right instruction).length !=
        callee.parameterCells.size ||
      !callLabelsOK machine instruction callee (callArguments machine right instruction))) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  have hwell := instruction_well_formed_of_raw_static_safe hstatic hlookup
  have hoperandArguments := operandValues_publicEquivalent hlow.2.2.2.2 hwell
  have harguments : ValueListPublicEquivalent
      (callArguments machine left instruction) (callArguments machine right instruction) := by
    rcases hoperation with hcall | hclosure
    · simpa [callArguments, hcall] using hoperandArguments
    · simpa [callArguments, hclosure] using hoperandArguments.drop 1
  have hcallOK : callLabelsOK machine instruction callee
      (callArguments machine left instruction) = true := by
    cases hcall : callLabelsOK machine instruction callee
        (callArguments machine left instruction) <;> simp_all
  have hflow : argumentLabelsFlow machine (callArguments machine left instruction)
      callee.parameterCells.toList = true := by
    have hparts : argumentLabelsFlow machine (callArguments machine left instruction)
          callee.parameterCells.toList = true ∧
        (instruction.destination == 0 ||
          callee.returnLabel.flowsTo instruction.resultLabel) = true := by
      simpa [callLabelsOK, Bool.and_eq_true] using hcallOK
    exact hparts.1
  have hcalleeWellFormed : functionWellFormed machine callee :=
    hstatic.1.1.2.1 callee
      (Array.mem_toList_iff.mpr (instructionCallee_mem_functions hleftCallee))
  have hentered := enterCall_preserves_publicLowEquivalent hlow instruction callee
    hcalleeWellFormed (callArguments machine left instruction)
      (callArguments machine right instruction) harguments hflow
  constructor
  · rcases hoperation with hcall | hclosure
    · simpa [step, callStep, hleftLive.1, hleftLive.2, hrightLive.1,
        hrightLive.2, hlookup, hrightLookup, hcall, hleftCallee,
        hrightCallee, hleftGuard, hrightGuard] using hentered
    · simpa [step, callStep, hleftLive.1, hleftLive.2, hrightLive.1,
        hrightLive.2, hlookup, hrightLookup, hclosure, hleftCallee,
        hrightCallee, hleftGuard, hrightGuard] using hentered
  · rcases hoperation with hcall | hclosure
    · simp [step, callStep, hleftLive.1, hleftLive.2, hrightLive.1,
        hrightLive.2, hlookup, hrightLookup, hcall, hleftCallee,
        hrightCallee, hleftGuard, hrightGuard, publicBoundaryTrace]
    · simp [step, callStep, hleftLive.1, hleftLive.2, hrightLive.1,
        hrightLive.2, hlookup, hrightLookup, hclosure, hleftCallee,
        hrightCallee, hleftGuard, hrightGuard, publicBoundaryTrace]

/-! ## External, state, and terminal constructor algebra -/

/-- Updating only raw control fields preserves Public-low equivalence when the new control fields
    agree. This is used by constructors whose data transition is handled separately. -/
theorem controlUpdate_preserves_publicLowEquivalent {machine : SemanticProgram}
    {left right : State} (hlow : PublicLowEquivalent machine left right)
    (leftPc rightPc : Nat) (leftHalted rightHalted leftTrapped rightTrapped : Bool)
    (hpc : leftPc = rightPc) (hhalted : leftHalted = rightHalted)
    (htrapped : leftTrapped = rightTrapped) :
    PublicLowEquivalent machine
      { left with pc := leftPc, halted := leftHalted, trapped := leftTrapped }
      { right with pc := rightPc, halted := rightHalted, trapped := rightTrapped } := by
  have h := (publicLowEquivalent_iff_projection machine left right).1 hlow
  apply (publicLowEquivalent_iff_projection machine _ _).2
  exact ⟨hpc, hhalted, htrapped, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- Pairwise writes preserve the whole Public-low relation when equality is supplied exactly for
    a nonzero Public destination. -/
theorem writeDestination_preserves_publicLowEquivalent {machine : SemanticProgram}
    {left right : State} (hlow : PublicLowEquivalent machine left right)
    (instruction : Instruction) (leftPayload rightPayload : Int)
    (hpayload : instruction.destination ≠ 0 →
      labelAt machine.valueLabels instruction.destination = .pub →
      leftPayload = rightPayload) :
    PublicLowEquivalent machine (writeDestination left instruction leftPayload)
      (writeDestination right instruction rightPayload) := by
  have h := (publicLowEquivalent_iff_projection machine left right).1 hlow
  apply (publicLowEquivalent_iff_projection machine _ _).2
  refine ⟨by simpa only [writeDestination_pc] using h.1,
    by simpa only [writeDestination_halted] using h.2.1,
    by simpa only [writeDestination_trapped] using h.2.2.1,
    by simpa only [writeDestination_callStack] using h.2.2.2.1,
    by simpa using h.2.2.2.2.1, by simpa using h.2.2.2.2.2.1,
    by simpa using h.2.2.2.2.2.2.1, ?_⟩
  exact writeDestination_preserves_publicProjection_eq_if_public instruction
    h.2.2.2.2.2.2.2 hpayload

/-- Advancing one shared Public external-input site preserves the complete cut-point relation,
    including deterministic missing/exhausted-stream behavior. -/
theorem advanceExternal_preserves_publicLowEquivalent {machine : SemanticProgram}
    {left right : State} (hlow : PublicLowEquivalent machine left right) {site : UInt32}
    (hpublic : externalSiteLabel machine site.toNat = .pub) :
    PublicLowEquivalent machine (advanceExternal left site) (advanceExternal right site) := by
  have h := (publicLowEquivalent_iff_projection machine left right).1 hlow
  apply publicLowEquivalent_of_projection_and_control
  · simpa using h.2.2.2.2.1
  · simpa using h.2.2.2.2.2.1
  · simpa using h.2.2.2.2.2.2.1
  · exact advanceExternal_preserves_publicProjection_eq h.2.2.2.2.1
      h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2 hpublic
  · simpa using h.1
  · simpa using h.2.1
  · simpa using h.2.2.1
  · simpa using h.2.2.2.1

/-- A Public actor-state slot requires equal payloads only when the verifier-derived global state
    label includes that slot in `PublicProjection`. -/
theorem actorStateWrite_preserves_publicProjection_eq_if_public
    {machine : SemanticProgram} {left right : State} (offset : Nat)
    {leftValue rightValue : Value}
    (hprojection : publicProjection machine left = publicProjection machine right)
    (hpayload : stateLabelAt machine (UInt32.ofNat offset) = .pub →
      leftValue.payload = rightValue.payload) :
    publicProjection machine
        { left with actorState := left.actorState.setIfInBounds offset leftValue } =
      publicProjection machine
        { right with actorState := right.actorState.setIfInBounds offset rightValue } := by
  simp only [publicProjection, PublicProjection.mk.injEq] at hprojection ⊢
  refine ⟨hprojection.1, hprojection.2.1, ?_, hprojection.2.2.2⟩
  apply maskedCells_setIfInBounds_pair_congr
    (fun position => (stateLabelAt machine (UInt32.ofNat position)).eqb .pub)
    Value.payload offset leftValue rightValue hprojection.2.2.1
  intro hvisible
  rw [label_eqb_true_iff] at hvisible
  exact hpayload hvisible

/-- Equal complete Public data determines the raw payload read from any statically Public actor
    slot.  Missing/out-of-bounds slots deterministically read zero on both sides. -/
theorem readActorValue_payload_eq_of_public_data {machine : SemanticProgram}
    {left right : State} (hdata : PublicDataEquivalent machine left right)
    (offset : UInt32) (hpublic : stateLabelAt machine offset = .pub) :
    (readActorValue machine left offset).payload =
      (readActorValue machine right offset).payload := by
  have hactor := hdata.2.1
  have hsize : left.actorState.size = right.actorState.size := hactor.1
  by_cases hleft : offset.toNat < left.actorState.size
  · have hright : offset.toNat < right.actorState.size := by simpa [hsize] using hleft
    have hpayload := hactor.2 offset.toNat hleft hright (by
      simpa using hpublic)
    simpa [readActorValue, hleft, hright] using hpayload
  · have hright : ¬ offset.toNat < right.actorState.size := by simpa [hsize] using hleft
    simp [readActorValue, hleft, hright]

/-- If a concrete decoded value operand position names a Public cell, the actual operand payload
    used by the raw machine is equal in Public-equivalent states. -/
theorem operandValueAt_payload_eq_of_public_cell {machine : SemanticProgram}
    {left right : State} (hdata : PublicDataEquivalent machine left right)
    {instruction : Instruction} {position : Nat} {cell : UInt32}
    (hwell : instructionWellFormed machine instruction)
    (hcell : (valueOperandCells machine instruction)[position]? = some cell)
    (hpublic : labelAt machine.valueLabels cell = .pub) :
    ((operandValues machine left instruction)[position]?.getD defaultValue).payload =
      ((operandValues machine right instruction)[position]?.getD defaultValue).payload := by
  have hmember : cell ∈ valueOperandCells machine instruction :=
    List.getElem?_eq_some_iff.mp hcell |>.2 ▸ List.getElem_mem
      (List.getElem?_eq_some_iff.mp hcell).1
  have hvalue := readProgramValue_eq_of_public_data hdata
    (valueOperandCells_bounded hwell hmember) hpublic
  simp [operandValues, hcell, hvalue]

/-- Flow/effect/authority and other non-boundary value events never enter the Public theorem's
    output/boundary trace, independently of their payload labels. -/
theorem publicBoundaryTrace_eventsForValues_nonobserved (kind : EventKind)
    (site : UInt32) (values : List Value) (houtput : kind ≠ .output)
    (hboundary : kind ≠ .boundary) :
    publicBoundaryTrace (eventsForValues kind site values) = [] := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [eventsForValues, publicBoundaryTrace, publicBoundaryObservation?,
        EventKind.eqb, houtput, hboundary, ih]

/-- The nonempty/defaulting event constructor is equally invisible for every non-output,
    non-boundary event kind. -/
theorem publicBoundaryTrace_eventsForObserved_nonobserved (kind : EventKind)
    (site : UInt32) (values : List Value) (houtput : kind ≠ .output)
    (hboundary : kind ≠ .boundary) :
    publicBoundaryTrace (eventsForObserved kind site values) = [] := by
  by_cases hempty : values.isEmpty
  · simp [eventsForObserved, hempty, publicBoundaryTrace, publicBoundaryObservation?,
      EventKind.eqb, houtput, hboundary]
  · simpa [eventsForObserved, hempty] using
      publicBoundaryTrace_eventsForValues_nonobserved kind site values houtput hboundary

/-- Pairwise state reads preserve the complete Public relation once the production decoder proves
    that any actor slot feeding a Public destination is itself Public.  Negative signed offsets
    take the raw machine's deterministic zero branch. -/
theorem matching_stateRead_step {machine : SemanticProgram} {left right : State}
    {instruction : Instruction}
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hread : instruction.op = .stateRead)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hsource : instruction.destination ≠ 0 →
      labelAt machine.valueLabels instruction.destination = .pub →
      let offset := (immediateOperands machine instruction).head?.getD 0
      0 ≤ offset → stateLabelAt machine (UInt32.ofNat offset.toNat) = .pub) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  let offset := (immediateOperands machine instruction).head?.getD 0
  let leftPayload := if offset < 0 then 0 else
    (readActorValue machine left (UInt32.ofNat offset.toNat)).payload
  let rightPayload := if offset < 0 then 0 else
    (readActorValue machine right (UInt32.ofNat offset.toNat)).payload
  have hpayload : instruction.destination ≠ 0 →
      labelAt machine.valueLabels instruction.destination = .pub →
      leftPayload = rightPayload := by
    intro hdestination hpublic
    by_cases hnegative : offset < 0
    · simp [leftPayload, rightPayload, hnegative]
    · have hnonnegative : 0 ≤ offset := by omega
      have hslot := hsource hdestination hpublic hnonnegative
      simpa [leftPayload, rightPayload, hnegative] using
        readActorValue_payload_eq_of_public_data hlow.2.2.2.2
          (UInt32.ofNat offset.toNat) hslot
  have hwrite := writeDestination_preserves_publicLowEquivalent hlow instruction
    leftPayload rightPayload hpayload
  have hcontrol := controlUpdate_preserves_publicLowEquivalent hwrite
    (left.pc + 1) (right.pc + 1) left.halted right.halted left.trapped right.trapped
    (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 hlow.2.2.1
  constructor
  · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, hread, offset, leftPayload, rightPayload] using hcontrol
  · simp [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, hread, publicBoundaryTrace]

/-- Pairwise state writes update the same decoded signed offset.  Equality is required only when
    that slot is part of the full Public actor-state projection; private writes may differ. -/
theorem matching_stateWrite_step {machine : SemanticProgram} {left right : State}
    {instruction : Instruction}
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hwriteOp : instruction.op = .stateWrite)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hsource :
      let offset := (immediateOperands machine instruction).head?.getD 0
      let leftValue := (operandValues machine left instruction)[1]?.getD defaultValue
      let rightValue := (operandValues machine right instruction)[1]?.getD defaultValue
      0 ≤ offset → stateLabelAt machine (UInt32.ofNat offset.toNat) = .pub →
        leftValue.payload = rightValue.payload) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  let offset := (immediateOperands machine instruction).head?.getD 0
  let leftValue := (operandValues machine left instruction)[1]?.getD defaultValue
  let rightValue := (operandValues machine right instruction)[1]?.getD defaultValue
  let leftStored : Value := if offset < 0 then leftValue else
    ⟨stateLabelAt machine (UInt32.ofNat offset.toNat), leftValue.payload⟩
  let rightStored : Value := if offset < 0 then rightValue else
    ⟨stateLabelAt machine (UInt32.ofNat offset.toNat), rightValue.payload⟩
  let leftActorState := if offset < 0 then left.actorState else
    left.actorState.setIfInBounds offset.toNat leftStored
  let rightActorState := if offset < 0 then right.actorState else
    right.actorState.setIfInBounds offset.toNat rightStored
  let leftUpdated : State := { left with actorState := leftActorState }
  let rightUpdated : State := { right with actorState := rightActorState }
  let leftNext : State := { leftUpdated with pc := left.pc + 1 }
  let rightNext : State := { rightUpdated with pc := right.pc + 1 }
  have hprojection :
      publicProjection machine leftUpdated = publicProjection machine rightUpdated := by
    by_cases hnegative : offset < 0
    · simpa [leftUpdated, rightUpdated, leftActorState, rightActorState, hnegative] using
        publicProjection_eq_of_low hlow
    · have hnonnegative : 0 ≤ offset := by omega
      simp only [leftUpdated, rightUpdated, leftActorState, rightActorState, hnegative,
        ↓reduceIte]
      apply actorStateWrite_preserves_publicProjection_eq_if_public offset.toNat
        (publicProjection_eq_of_low hlow)
      intro hpublic
      have hpayload := hsource hnonnegative hpublic
      simpa [leftStored, rightStored, hnegative] using hpayload
  have hstorage := publicLow_storage_facts hlow
  have hnext : PublicLowEquivalent machine leftNext rightNext := by
    apply (publicLowEquivalent_iff_projection machine leftNext rightNext).2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change left.pc + 1 = right.pc + 1
      exact congrArg (fun pc => pc + 1) hlow.1
    · simpa [leftNext, rightNext, leftUpdated, rightUpdated] using hlow.2.1
    · simpa [leftNext, rightNext, leftUpdated, rightUpdated] using hlow.2.2.1
    · simpa [leftNext, rightNext, leftUpdated, rightUpdated] using hlow.2.2.2.1
    · simpa [leftNext, leftUpdated] using hstorage.1
    · simpa [rightNext, rightUpdated] using hstorage.2.1
    · simpa [leftNext, rightNext, leftUpdated, rightUpdated] using hstorage.2.2
    · simpa [leftNext, rightNext, publicProjection] using hprojection
  constructor
  · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, hwriteOp, offset, leftValue, rightValue,
      leftStored, rightStored, leftActorState, rightActorState, leftUpdated,
      rightUpdated, leftNext, rightNext] using hnext
  · have hleftEvents := publicBoundaryTrace_eventsForValues_nonobserved .flow instruction.id
      ((operandValues machine left instruction).drop 1 |>.take 1) (by decide) (by decide)
    have hrightEvents := publicBoundaryTrace_eventsForValues_nonobserved .flow instruction.id
      ((operandValues machine right instruction).drop 1 |>.take 1) (by decide) (by decide)
    simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, hwriteOp, instructionEvents] using
        hleftEvents.trans hrightEvents.symm

/-- Production state-read matching.  The occurrence verifier identifies the exact function-owned
    state contract, the decoder correspondence theorem identifies that same offset as the first
    raw immediate, and the semantic seed proof rules out a hidden global-label collision whenever
    the destination is Public.  No runtime `Value.label` is trusted. -/
theorem matching_verified_stateRead_step
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : OccurrenceDataflowInvocation.analyze? program = some analysis)
    {left right : State} {instruction : Instruction}
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hread : instruction.op = .stateRead)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false) :
    PublicLowEquivalent (rawSemanticProgram program analysis)
        (step (rawSemanticProgram program analysis) left).state
        (step (rawSemanticProgram program analysis) right).state ∧
      publicBoundaryTrace (step (rawSemanticProgram program analysis) left).events =
        publicBoundaryTrace (step (rawSemanticProgram program analysis) right).events := by
  let machine := rawSemanticProgram program analysis
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hwell : instructionWellFormed machine instruction :=
    instruction_well_formed_of_raw_static_safe hstatic hlookup
  apply matching_stateRead_step hlow hlookup hread hleftLive hrightLive
  intro hdestination hpublic
  have hresult : instruction.resultLabel = .pub := hwell.2.2.1.trans hpublic
  obtain ⟨offset, _, himmediate, hglobal⟩ :=
    verified_public_stateRead_declared_global_label_public hjudgment hanalysis hlookup
      hread hdestination hresult
  have hhead := verified_state_runtime_immediate_head hjudgment hanalysis hlookup
    (Or.inl hread) (by simpa [hread] using himmediate)
  have hrawOffset :
      (immediateOperands machine instruction).head?.getD 0 =
        Int.ofNat offset.toNat := by
    simpa [machine, hhead]
  dsimp only
  rw [hrawOffset]
  intro _
  simpa [machine, stateLabelAt, rawSemanticProgram, OccurrenceDataflow.semanticProgram,
    semanticProgramOfWith] using hglobal

/-- Production state-write matching.  Acceptance resolves an exact sink and exact raw offset.
    If the globally joined runtime slot is Public, monotonicity forces the function-owned sink to
    be Public too; the verifier then proves the actual second value operand Public, which supplies
    precisely the payload equality required by the raw actor-state update. -/
theorem matching_verified_stateWrite_step
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : OccurrenceDataflowInvocation.analyze? program = some analysis)
    {left right : State} {instruction : Instruction}
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hwrite : instruction.op = .stateWrite)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false) :
    PublicLowEquivalent (rawSemanticProgram program analysis)
        (step (rawSemanticProgram program analysis) left).state
        (step (rawSemanticProgram program analysis) right).state ∧
      publicBoundaryTrace (step (rawSemanticProgram program analysis) left).events =
        publicBoundaryTrace (step (rawSemanticProgram program analysis) right).events := by
  let machine := rawSemanticProgram program analysis
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hwell : instructionWellFormed machine instruction :=
    instruction_well_formed_of_raw_static_safe hstatic hlookup
  have hsafe : PublicStateWriteSourceSafe program analysis machine instruction :=
    returned_public_state_write_source_safe hjudgment hanalysis hlookup
  have hbody := hsafe hwrite
  unfold publicStateWriteSourceBodyOK at hbody
  cases hsink : stateSinkAt? program analysis instruction .stateWrite 2 with
  | none => simp [hsink] at hbody
  | some sink =>
      obtain ⟨offset, hcontract, hrawOffset⟩ :=
        verified_stateWrite_runtime_offset hjudgment hanalysis hlookup hwrite hsink
      have hflow := analyzed_state_sink_flows_to_runtime_label hanalysis hcontract
      apply matching_stateWrite_step hlow hlookup hwrite hleftLive hrightLive
      dsimp only
      intro _ hglobalPublic
      have hrawOffsetNat :
          UInt32.ofNat
              ((immediateOperands machine instruction).head?.getD 0).toNat = offset := by
        rw [hrawOffset]
        simp
      have hsinkPublic : sink = .pub := by
        have hglobalAtOffset : stateLabelAt machine offset = .pub := by
          rw [← hrawOffsetNat]
          exact hglobalPublic
        have hflowPublic : sink.flowsTo .pub = true := by
          simpa [machine, hglobalAtOffset] using hflow
        cases sink <;> simp_all [Label.flowsTo, Label.rank]
      have hsinkPublicExact :
          stateSinkAt? program analysis instruction .stateWrite 2 = some .pub := by
        simpa [hsinkPublic] using hsink
      obtain ⟨cell, hcell, hcellPublic⟩ :=
        public_state_write_has_public_source hsafe hwrite hsinkPublicExact
      exact operandValueAt_payload_eq_of_public_cell hlow.2.2.2.2 hwell hcell hcellPublic

/-- A pair of reads from the same Public FFI site advances only that site's cursor, writes the
    same Public result when present, and emits no Public output/boundary observation. -/
theorem matching_ffi_step {machine : SemanticProgram} {left right : State}
    {instruction : Instruction}
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hop : instruction.op = .ffi)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hsite : externalSiteLabel machine instruction.id.toNat = .pub) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  have hread := public_readExternal_eq_total hlow.2.2.2.2.1 hsite
  have hadvance := advanceExternal_preserves_publicLowEquivalent hlow hsite
  have hwrite := writeDestination_preserves_publicLowEquivalent hadvance instruction
    (readExternal left instruction.id) (readExternal right instruction.id)
    (fun _ _ => hread)
  have hcontrol := controlUpdate_preserves_publicLowEquivalent hwrite
    (left.pc + 1) (right.pc + 1) left.halted right.halted left.trapped right.trapped
    (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 hlow.2.2.1
  constructor
  · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, hop] using hcontrol
  · have hleftEvents : publicBoundaryTrace (instructionEvents machine left instruction) = [] := by
      simpa [instructionEvents, hop] using
        publicBoundaryTrace_eventsForValues_nonobserved .effect instruction.id
          (policyOperandValues machine left instruction 7) (by decide) (by decide)
    have hrightEvents : publicBoundaryTrace (instructionEvents machine right instruction) = [] := by
      simpa [instructionEvents, hop] using
        publicBoundaryTrace_eventsForValues_nonobserved .effect instruction.id
          (policyOperandValues machine right instruction 7) (by decide) (by decide)
    simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, hop] using hleftEvents.trans hrightEvents.symm

/-- Actor boundaries preserve the same Public data transition as an FFI result and retain every
    ordered boundary occurrence. Payloads are compared only where their decoded labels are Public. -/
theorem matching_actorBoundary_step {machine : SemanticProgram} {left right : State}
    {instruction : Instruction}
    (hstatic : OperationalStaticSafe machine)
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hop : instruction.op = .actorBoundary)
    (hpublic : instruction.blockLabel = .pub)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hsite : externalSiteLabel machine instruction.id.toNat = .pub) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  have hwell := instruction_well_formed_of_raw_static_safe hstatic hlookup
  have hinstructionEvents :
      publicBoundaryTrace (instructionEvents machine left instruction) =
        publicBoundaryTrace (instructionEvents machine right instruction) := by
    rw [public_actor_instruction_observations machine left instruction hop hpublic,
      public_actor_instruction_observations machine right instruction hop hpublic]
    exact boundaryObservations_policyOperands_eq hlow.2.2.2.2 hwell 8
  have hevents : publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events := by
    simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, hop] using hinstructionEvents
  by_cases hdestination : instruction.destination = 0
  · have hcontrol := controlUpdate_preserves_publicLowEquivalent hlow
      (left.pc + 1) (right.pc + 1) left.halted right.halted left.trapped right.trapped
      (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 hlow.2.2.1
    refine ⟨?_, hevents⟩
    simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, hop, hdestination, writeDestination] using hcontrol
  · have hread := public_readExternal_eq_total hlow.2.2.2.2.1 hsite
    have hadvance := advanceExternal_preserves_publicLowEquivalent hlow hsite
    have hwrite := writeDestination_preserves_publicLowEquivalent hadvance instruction
      (readExternal left instruction.id) (readExternal right instruction.id)
      (fun _ _ => hread)
    have hcontrol := controlUpdate_preserves_publicLowEquivalent hwrite
      (left.pc + 1) (right.pc + 1) left.halted right.halted left.trapped right.trapped
      (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 hlow.2.2.1
    refine ⟨?_, hevents⟩
    simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, hop, hdestination] using hcontrol

/-- Effect events are outside the Public output/boundary trace. Ordinary effects advance in
    lockstep; abortive effects trap both sides and therefore cannot occur on a successful suffix. -/
theorem matching_effect_step {machine : SemanticProgram} {left right : State}
    {instruction : Instruction}
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hoperation : instruction.op = .effect ∨ instruction.op = .abortiveEffect)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  have hcontrol := controlUpdate_preserves_publicLowEquivalent hlow
    (left.pc + 1) (right.pc + 1) left.halted right.halted
      (instruction.op == .abortiveEffect) (instruction.op == .abortiveEffect)
    (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 rfl
  constructor
  · rcases hoperation with heffect | habort
    · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, heffect] using hcontrol
    · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, habort] using hcontrol
  · have hleftEvents : publicBoundaryTrace (instructionEvents machine left instruction) = [] := by
      rcases hoperation with heffect | habort
      · simpa [instructionEvents, heffect] using
          publicBoundaryTrace_eventsForValues_nonobserved .effect instruction.id
            (operandValues machine left instruction) (by decide) (by decide)
      · simpa [instructionEvents, habort] using
          publicBoundaryTrace_eventsForValues_nonobserved .effect instruction.id
            (operandValues machine left instruction) (by decide) (by decide)
    have hrightEvents : publicBoundaryTrace (instructionEvents machine right instruction) = [] := by
      rcases hoperation with heffect | habort
      · simpa [instructionEvents, heffect] using
          publicBoundaryTrace_eventsForValues_nonobserved .effect instruction.id
            (operandValues machine right instruction) (by decide) (by decide)
      · simpa [instructionEvents, habort] using
          publicBoundaryTrace_eventsForValues_nonobserved .effect instruction.id
            (operandValues machine right instruction) (by decide) (by decide)
    rcases hoperation with heffect | habort
    · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, heffect] using hleftEvents.trans hrightEvents.symm
    · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, habort] using hleftEvents.trans hrightEvents.symm

/-- Exact syntactic class handled by `ordinaryStep` in the raw machine.  Keeping this executable
    classification next to the semantic reduction prevents constructor additions from silently
    falling into a generic proof case. -/
def UsesOrdinaryStep (operation : SemanticInstrOp) : Prop :=
  operation ≠ .call ∧ operation ≠ .closure ∧ operation ≠ .output ∧
    operation ≠ .ffi ∧ operation ≠ .actorBoundary ∧ operation ≠ .effect ∧
    operation ≠ .abortiveEffect ∧ operation ≠ .stateRead ∧ operation ≠ .stateWrite

theorem step_eq_ordinaryStep {machine : SemanticProgram} {state : State}
    {instruction : Instruction}
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hlive : state.halted = false ∧ state.trapped = false)
    (hordinary : UsesOrdinaryStep instruction.op) :
    step machine state = ordinaryStep machine state instruction := by
  unfold step
  rw [if_neg (by simp [hlive.1, hlive.2]), hlookup]
  generalize hop : instruction.op = operation at hordinary
  cases operation <;> simp_all [UsesOrdinaryStep]

/-- No constructor delegated to `ordinaryStep` emits an output or actor-boundary observation.
    Release, control, address, allocation, cost, authority, flow, and trap events remain in their
    own traces but are intentionally outside the Public output/boundary projection. -/
theorem ordinary_instruction_publicBoundaryTrace_nil (machine : SemanticProgram)
    (state : State) (instruction : Instruction)
    (hordinary : UsesOrdinaryStep instruction.op) :
    publicBoundaryTrace (instructionEvents machine state instruction) = [] := by
  generalize hop : instruction.op = operation at hordinary
  cases operation <;>
    simp_all [UsesOrdinaryStep, instructionEvents,
      publicBoundaryTrace_eventsForValues_nonobserved,
      publicBoundaryTrace_eventsForObserved_nonobserved,
      EventKind.eqb, Label.eqb]
  all_goals simp [publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]

/-- Constructor-neutral matching rule for the exact ordinary-step family.  Production callers
    derive the payload, aggregate, control, and trap premises from v9 acceptance and the current
    instruction class; this lemma only performs the raw semantic reduction. -/
theorem matching_ordinary_step {machine : SemanticProgram} {left right : State}
    {instruction : Instruction}
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hordinary : UsesOrdinaryStep instruction.op)
    (hpayload : instruction.destination ≠ 0 →
      labelAt machine.valueLabels instruction.destination = .pub →
      instructionPayload machine left instruction =
        instructionPayload machine right instruction)
    (haggregate : instruction.op = .aggregate →
      instruction.destination ≠ 0 →
      labelAt machine.valueLabels instruction.destination = .pub →
      operandPayloads machine left instruction = operandPayloads machine right instruction)
    (hnext : nextPc machine left instruction (operandValue machine left instruction) =
      nextPc machine right instruction (operandValue machine right instruction))
    (htraps : (if instruction.op == .trap then
        (operandValues machine left instruction).isEmpty ||
          (operandValue machine left instruction).payload != 0 else false) =
      (if instruction.op == .trap then
        (operandValues machine right instruction).isEmpty ||
          (operandValue machine right instruction).payload != 0 else false)) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  have hleftStep := step_eq_ordinaryStep hlookup hleftLive hordinary
  have hrightStep := step_eq_ordinaryStep hrightLookup hrightLive hordinary
  constructor
  · rw [hleftStep, hrightStep]
    exact ordinaryStep_preserves_publicLowEquivalent hlow instruction hpayload haggregate
      hnext htraps
  · rw [hleftStep, hrightStep]
    simp only [ordinaryStep]
    rw [ordinary_instruction_publicBoundaryTrace_nil machine left instruction hordinary,
      ordinary_instruction_publicBoundaryTrace_nil machine right instruction hordinary]

/-- Production specialization for an accepted v9 ordinary instruction other than the two
    releases.  Taint-derived payload and aggregate dependencies come directly from the returned
    verifier judgment.  Only raw control and trap agreement remain explicit: secret control is
    handled by the structured-region rule, while successful suffixes discharge trap agreement. -/
theorem matching_verified_ordinary_step
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : OccurrenceDataflowInvocation.analyze? program = some analysis)
    {left right : State} {instruction : Instruction}
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hordinary : UsesOrdinaryStep instruction.op)
    (hnotRelease : instruction.op ≠ .release)
    (hnotReleaseCT : instruction.op ≠ .releaseCT)
    (hnext : nextPc (rawSemanticProgram program analysis) left instruction
        (operandValue (rawSemanticProgram program analysis) left instruction) =
      nextPc (rawSemanticProgram program analysis) right instruction
        (operandValue (rawSemanticProgram program analysis) right instruction))
    (htraps : (if instruction.op == .trap then
        (operandValues (rawSemanticProgram program analysis) left instruction).isEmpty ||
          (operandValue (rawSemanticProgram program analysis) left instruction).payload != 0
        else false) =
      (if instruction.op == .trap then
        (operandValues (rawSemanticProgram program analysis) right instruction).isEmpty ||
          (operandValue (rawSemanticProgram program analysis) right instruction).payload != 0
        else false)) :
    PublicLowEquivalent (rawSemanticProgram program analysis)
        (step (rawSemanticProgram program analysis) left).state
        (step (rawSemanticProgram program analysis) right).state ∧
      publicBoundaryTrace (step (rawSemanticProgram program analysis) left).events =
        publicBoundaryTrace (step (rawSemanticProgram program analysis) right).events := by
  let machine := rawSemanticProgram program analysis
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hwell : instructionWellFormed machine instruction :=
    instruction_well_formed_of_raw_static_safe hstatic hlookup
  have hsafe : PublicResultDependenciesSafe program analysis machine instruction :=
    returned_public_result_dependencies_safe hjudgment hanalysis hlookup
  have hordinaryParts := hordinary
  rcases hordinaryParts with
    ⟨hcall, hclosure, houtput, hffi, hactor, heffect, habortive,
      hstateRead, hstateWrite⟩
  apply matching_ordinary_step hlow hlookup hleftLive hrightLive hordinary
  · intro hdestination hpublic
    exact instructionPayload_eq_of_public_dependencies hlow.2.2.2.2 hwell hsafe
      hdestination hpublic
      ⟨hffi, hactor, hcall, hclosure, hstateRead, hnotRelease, hnotReleaseCT⟩
  · intro haggregate hdestination hpublic
    exact aggregateOperandPayloads_eq_of_public_dependencies hlow.2.2.2.2 hwell hsafe
      haggregate hdestination hpublic
  · exact hnext
  · exact htraps

/-- Every non-branching raw constructor computes its successor solely from the shared decoded
    instruction and equal current pc.  Secret-dependent branch/loop/range/dispatch selection is
    intentionally left to structured-region convergence. -/
theorem nextPc_eq_of_nonbranching {machine : SemanticProgram} {left right : State}
    (hlow : PublicLowEquivalent machine left right) (instruction : Instruction)
    (hbranch : instruction.op ≠ .branch) (hloop : instruction.op ≠ .loop)
    (hrange : instruction.op ≠ .range) (hdispatch : instruction.op ≠ .dispatch) :
    nextPc machine left instruction (operandValue machine left instruction) =
      nextPc machine right instruction (operandValue machine right instruction) := by
  generalize hop : instruction.op = operation at hbranch hloop hrange hdispatch
  cases operation <;> simp_all [nextPc, hlow.1]

/-- Away from the explicit trap constructor, the raw trap bit is definitionally identical. -/
theorem trap_test_eq_of_nontrap (machine : SemanticProgram) (left right : State)
    (instruction : Instruction) (htrap : instruction.op ≠ .trap) :
    (if instruction.op == .trap then
        (operandValues machine left instruction).isEmpty ||
          (operandValue machine left instruction).payload != 0 else false) =
      (if instruction.op == .trap then
        (operandValues machine right instruction).isEmpty ||
          (operandValue machine right instruction).payload != 0 else false) := by
  have : (instruction.op == .trap) = false := by
    cases hbeq : instruction.op == .trap with
    | false => rfl
    | true => exact False.elim (htrap ((Semantic.semanticInstrOp_beq_true_iff _ _).mp hbeq))
  simp [this]

/-- Once release synchronization supplies equality of the real raw payload at this occurrence,
    either downgrade stage is an ordinary matching transition.  The premise is local to the
    current release; later occurrences remain in the release-trace suffix used by composition. -/
theorem matching_release_step {machine : SemanticProgram} {left right : State}
    {instruction : Instruction}
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hoperation : instruction.op = .release ∨ instruction.op = .releaseCT)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hpayload : instructionPayload machine left instruction =
      instructionPayload machine right instruction) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  have hordinary : PublicLowEquivalent machine
      (ordinaryStep machine left instruction).state
      (ordinaryStep machine right instruction).state := by
    apply ordinaryStep_preserves_publicLowEquivalent hlow instruction
    · intro _ _
      exact hpayload
    · intro haggregate _
      rcases hoperation with hrelease | hreleaseCT <;> simp_all
    · rcases hoperation with hrelease | hreleaseCT
      · simp [nextPc, hrelease, hlow.1]
      · simp [nextPc, hreleaseCT, hlow.1]
    · rcases hoperation with hrelease | hreleaseCT
      · simp [hrelease]
      · simp [hreleaseCT]
  constructor
  · rcases hoperation with hrelease | hreleaseCT
    · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, hrelease] using hordinary
    · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, hreleaseCT] using hordinary
  · rcases hoperation with hrelease | hreleaseCT
    · simp [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, hrelease, ordinaryStep, instructionEvents,
        publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]
    · simp [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
        hlookup, hrightLookup, hreleaseCT, ordinaryStep, instructionEvents,
        publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]

/-- A real top-level Public output is a matching terminal transition.  The observable occurrence
    and site always agree.  Its optional payload is derived from the decoded operand label and the
    complete Public data relation, so private payload equality is neither assumed nor exposed. -/
theorem matching_topLevel_output_step {machine : SemanticProgram} {left right : State}
    {instruction : Instruction}
    (hstatic : OperationalStaticSafe machine)
    (hleftWellFormed : StateWellFormed machine left)
    (hrightWellFormed : StateWellFormed machine right)
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (houtput : instruction.op = .output)
    (hpublic : instruction.blockLabel = .pub)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hleftStack : left.callStack = []) :
    PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  have hrightStack : right.callStack = [] := by
    have hstack := hlow.2.2.2.1
    rw [hleftStack] at hstack
    cases hright : right.callStack with
    | nil => rfl
    | cons frame rest => simp [CallStackPublicEquivalent, hright] at hstack
  have hwell := instruction_well_formed_of_raw_static_safe hstatic hlookup
  have hobservation := observationPayload_operandValue_eq hlow.2.2.2.2 hwell
  have hlabelEq : (operandValue machine left instruction).label =
      (operandValue machine right instruction).label :=
    operandValue_label_state_independent machine left right instruction
  have houtputObservation :
      outputObservationPayload instruction (operandValue machine left instruction) =
        outputObservationPayload instruction (operandValue machine right instruction) := by
    cases hoccurrence : instruction.outputPayloadOccurrence <;>
      cases hleftLabel : (operandValue machine left instruction).label <;>
      cases hrightLabel : (operandValue machine right instruction).label <;>
      simp_all [outputObservationPayload, observationPayload, Label.eqb, Label.lub, Label.rank]
  have hevents : publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events := by
    rw [step, if_neg (by simp [hleftLive.1, hleftLive.2]), hlookup,
      step, if_neg (by simp [hrightLive.1, hrightLive.2]), hrightLookup]
    simp only [houtput, hleftStack, hrightStack]
    rw [public_output_instruction_observation machine left instruction houtput hpublic,
      public_output_instruction_observation machine right instruction houtput hpublic,
      houtputObservation]
  apply matching_step_of_projection hstatic hleftWellFormed hrightWellFormed hlow
  · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, houtput, hleftStack, hrightStack, publicProjection] using
        publicProjection_eq_of_low hlow
  · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, houtput, hleftStack, hrightStack] using hlow.1
  · simp [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, houtput, hleftStack, hrightStack]
  · simp [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, houtput, hleftStack, hrightStack]
  · simpa [step, hleftLive.1, hleftLive.2, hrightLive.1, hrightLive.2,
      hlookup, hrightLookup, houtput, hleftStack, hrightStack,
      CallStackPublicEquivalent]
  · exact hevents

/-- Constructor-complete matching at one verified Public cut point when the two raw successors
    choose the same control position.  The theorem extracts call guards and return-flow guards
    from the actual nontrapping successors, derives external/state facts from v9 acceptance, and
    dispatches every semantic constructor.  Releases are excluded because complete-trace
    synchronization must consume their exact site/stage/payload before invoking the release rule.

    A private branch/loop or dynamic closure whose successors differ is intentionally outside
    this lemma and is handled by structured-region convergence. -/
theorem matching_verified_same_control_step
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : OccurrenceDataflowInvocation.Analysis}
    (hanalysis : OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {left right : State} {instruction : Instruction}
    (hleftActive : ActiveState (rawSemanticProgram program analysis) root left)
    (hrightActive : ActiveState (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hpublic : instruction.blockLabel = .pub)
    (hnextPc : nextPc (rawSemanticProgram program analysis) left instruction
        (operandValue (rawSemanticProgram program analysis) left instruction) =
      nextPc (rawSemanticProgram program analysis) right instruction
        (operandValue (rawSemanticProgram program analysis) right instruction))
    (hclosureCallee : instruction.op = .closure →
      instructionCallee? (rawSemanticProgram program analysis) left instruction =
        instructionCallee? (rawSemanticProgram program analysis) right instruction)
    (hnotRelease : instruction.op ≠ .release)
    (hnotReleaseCT : instruction.op ≠ .releaseCT)
    (hleftNext : (step (rawSemanticProgram program analysis) left).state.trapped = false)
    (hrightNext : (step (rawSemanticProgram program analysis) right).state.trapped = false) :
    PublicLowEquivalent (rawSemanticProgram program analysis)
        (step (rawSemanticProgram program analysis) left).state
        (step (rawSemanticProgram program analysis) right).state ∧
      publicBoundaryTrace (step (rawSemanticProgram program analysis) left).events =
        publicBoundaryTrace (step (rawSemanticProgram program analysis) right).events := by
  let machine := rawSemanticProgram program analysis
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hleftLive : left.halted = false ∧ left.trapped = false :=
    ⟨hleftActive.notHalted, hleftActive.notTrapped⟩
  have hrightLive : right.halted = false ∧ right.trapped = false :=
    ⟨hrightActive.notHalted, hrightActive.notTrapped⟩
  have htraps := trap_test_eq_of_nontrapping_steps hlow hlookup hleftLive hrightLive
    hleftNext hrightNext
  generalize hop : instruction.op = operation at *
  cases operation
  case call =>
    obtain ⟨leftCallee, hleftCallee, hleftGuard⟩ :=
      nontrapping_call_step_shape hlookup (Or.inl hop) hleftLive hleftNext
    obtain ⟨rightCallee, hrightCallee, hrightGuard⟩ :=
      nontrapping_call_step_shape (by simpa [hlow.1] using hlookup)
        (Or.inl hop) hrightLive hrightNext
    have hcalleeOptions :
        instructionCallee? machine left instruction =
          instructionCallee? machine right instruction := by
      simp [instructionCallee?, hop]
    rw [hleftCallee, hrightCallee] at hcalleeOptions
    have hcalleeEq : leftCallee = rightCallee := Option.some.inj hcalleeOptions
    subst rightCallee
    exact matching_call_step_same_callee hstatic hleftActive.wellFormed
      hrightActive.wellFormed hlow hlookup (Or.inl hop) hleftLive hrightLive
      hleftCallee hrightCallee hleftGuard hrightGuard
  case closure =>
    obtain ⟨leftCallee, hleftCallee, hleftGuard⟩ :=
      nontrapping_call_step_shape hlookup (Or.inr hop) hleftLive hleftNext
    obtain ⟨rightCallee, hrightCallee, hrightGuard⟩ :=
      nontrapping_call_step_shape (by simpa [hlow.1] using hlookup)
        (Or.inr hop) hrightLive hrightNext
    have hcalleeOptions := hclosureCallee rfl
    rw [hleftCallee, hrightCallee] at hcalleeOptions
    have hcalleeEq : leftCallee = rightCallee := Option.some.inj hcalleeOptions
    subst rightCallee
    exact matching_call_step_same_callee hstatic hleftActive.wellFormed
      hrightActive.wellFormed hlow hlookup (Or.inr hop) hleftLive hrightLive
      hleftCallee hrightCallee hleftGuard hrightGuard
  case output =>
    cases hleftStack : left.callStack with
    | nil =>
        exact matching_topLevel_output_step hstatic hleftActive.wellFormed
          hrightActive.wellFormed hlow hlookup hop hpublic hleftLive hrightLive hleftStack
    | cons leftFrame leftRest =>
        cases hrightStack : right.callStack with
        | nil =>
            have hstack := hlow.2.2.2.1
            simp [CallStackPublicEquivalent, hleftStack, hrightStack] at hstack
        | cons rightFrame rightRest =>
            have hleftFlow := nontrapping_internal_output_flow hlookup hop hleftLive
              hleftStack hleftNext
            have hrightLookup : machine.instructions[right.pc]? = some instruction := by
              rw [← hlow.1]
              exact hlookup
            have hrightFlow := nontrapping_internal_output_flow hrightLookup hop hrightLive
              hrightStack hrightNext
            exact matching_internal_return_of_wellFormed hstatic hleftActive.wellFormed
              hrightActive.wellFormed hlow hlookup hop hleftLive hrightLive hleftStack
              hrightStack hleftFlow hrightFlow
  case ffi =>
    exact matching_ffi_step hlow hlookup hop hleftLive hrightLive
      ((raw_externalSiteLabel_eq_blockLabel hanalysis hlookup).trans hpublic)
  case actorBoundary =>
    exact matching_actorBoundary_step hstatic hlow hlookup hop hpublic hleftLive hrightLive
      ((raw_externalSiteLabel_eq_blockLabel hanalysis hlookup).trans hpublic)
  case effect =>
    exact matching_effect_step hlow hlookup (Or.inl hop) hleftLive hrightLive
  case abortiveEffect =>
    exact matching_effect_step hlow hlookup (Or.inr hop) hleftLive hrightLive
  case stateRead =>
    exact matching_verified_stateRead_step hjudgment hanalysis hlow hlookup hop
      hleftLive hrightLive
  case stateWrite =>
    exact matching_verified_stateWrite_step hjudgment hanalysis hlow hlookup hop
      hleftLive hrightLive
  case release => exact False.elim (hnotRelease rfl)
  case releaseCT => exact False.elim (hnotReleaseCT rfl)
  all_goals
    apply matching_verified_ordinary_step hjudgment hanalysis hlow hlookup hleftLive
      hrightLive
    · simp [UsesOrdinaryStep, hop]
    · simpa [hop] using hnotRelease
    · simpa [hop] using hnotReleaseCT
    · exact hnextPc
    · simpa [hop] using htraps

end LambdaSigil.Combined.V9.PublicMatchingSecurity
