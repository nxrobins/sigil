import LambdaSigil.CombinedSecurity

/-!
# Local guarantees of the narrowly classified private-return leaf

The instruction predicate resolves nonzero destinations and returned operands through the
semantic index, requires their labels to be non-Public, and excludes calls and shared effects.
These facts describe actual source operand records, not a caller-supplied relational policy.
They do not establish active-frame provenance, a Public relational theorem, or structural index
ownership in isolation; the ordinary decoded-program checks remain independently required.
-/

namespace LambdaSigil.Combined.PrivateLeafReturnSecurity

open Semantic

private theorem nonpublic_label_has_cell {labels : Array Label} {cell : UInt32}
    (h : labelAt labels cell ≠ .pub) : cell.toNat < labels.size := by
  by_cases hbound : cell.toNat < labels.size
  · exact hbound
  · have hlabel : labelAt labels cell = .pub := by simp [labelAt, Array.getD, hbound]
    exact False.elim (h hlabel)

theorem private_leaf_nonzero_destination_is_private {p : Program} {index : SemanticIndex}
    {labels : Array Label} {n : Node}
    (h : semanticPrivateLeafInstructionB p index labels n = true) (hresult : n.required ≠ 0) :
    ∃ cell, semanticValueCell? index n.origin n.required = some cell ∧
      cell.toNat < labels.size ∧ labelAt labels cell ≠ .pub := by
  simp only [semanticPrivateLeafInstructionB, Bool.and_eq_true] at h
  have hdest := h.1
  simp only [Bool.or_eq_true, beq_iff_eq, hresult, false_or] at hdest
  cases hcell : semanticValueCell? index n.origin n.required with
  | none => simp [hcell] at hdest
  | some cell =>
      have hprivate : labelAt labels cell ≠ .pub := by
        simpa [hcell] using hdest
      exact ⟨cell, rfl, nonpublic_label_has_cell hprivate, hprivate⟩

theorem private_leaf_output_has_private_value {p : Program} {index : SemanticIndex}
    {labels : Array Label} {n : Node}
    (h : semanticPrivateLeafInstructionB p index labels n = true)
    (hop : decodeSemanticInstrOp? n.aux = some .output) :
    n.ceiling = 1 ∧ ∃ valueId cell,
      semanticOperandValueIdAt? p n.nodeId 0 = some valueId ∧
      semanticValueCell? index n.origin valueId = some cell ∧
      cell.toNat < labels.size ∧ labelAt labels cell ≠ .pub := by
  simp only [semanticPrivateLeafInstructionB, hop, Bool.and_eq_true] at h
  have houtput := h.2
  simp only [beq_iff_eq] at houtput
  refine ⟨houtput.1, ?_⟩
  cases hvalue : semanticOperandValueIdAt? p n.nodeId 0 with
  | none => simp [hvalue] at houtput
  | some valueId =>
      cases hcell : semanticValueCell? index n.origin valueId with
      | none => simp [hvalue, hcell] at houtput
      | some cell =>
          have hprivate : labelAt labels cell ≠ .pub := by
            simpa [hvalue, hcell] using houtput.2
          exact ⟨valueId, cell, rfl, hcell, nonpublic_label_has_cell hprivate, hprivate⟩

theorem private_leaf_output_uses_actual_operand_record {p : Program} {index : SemanticIndex}
    {labels : Array Label} {n : Node}
    (h : semanticPrivateLeafInstructionB p index labels n = true)
    (hop : decodeSemanticInstrOp? n.aux = some .output) :
    ∃ operand cell, p.nodes[n.nodeId.toNat]? = some operand ∧
      operand.op = .semOperand ∧ operand.origin = n.nodeId ∧ operand.actual.toNat = 0 ∧
      operand.flags = 0 ∧ semanticValueCell? index n.origin operand.required = some cell ∧
      cell.toNat < labels.size ∧ labelAt labels cell ≠ .pub := by
  obtain ⟨_, valueId, cell, hvalue, hcell, hbound, hprivate⟩ :=
    private_leaf_output_has_private_value h hop
  unfold semanticOperandValueIdAt? at hvalue
  cases hoperand : semanticOperandAt? p n.nodeId 0 with
  | none => simp [hoperand] at hvalue
  | some operand =>
      simp only [hoperand] at hvalue
      split at hvalue
      · rename_i hflags
        cases hvalue
        unfold semanticOperandAt? at hoperand
        simp only [Nat.add_zero] at hoperand
        cases hrecord : p.nodes[n.nodeId.toNat]? with
        | none => simp [hrecord] at hoperand
        | some actual =>
            simp only [hrecord] at hoperand
            split at hoperand
            · rename_i hidentity
              cases hoperand
              simp only [Bool.and_eq_true] at hidentity
              have hparts := hidentity
              have hparts' := hparts.1
              have hop' : operand.op = .semOperand := by
                have generic : ∀ op : Op, (op == .semOperand) = true → op = .semOperand := by
                  intro op
                  cases op <;> decide
                exact generic operand.op hparts'.1
              exact ⟨operand, cell, rfl, hop', by simpa using hparts'.2,
                by simpa using hparts.2, by simpa using hflags, hcell, hbound, hprivate⟩
            · cases hoperand
      · cases hvalue

theorem private_leaf_operation_is_in_pure_whitelist {p : Program} {index : SemanticIndex}
    {labels : Array Label} {n : Node}
    (h : semanticPrivateLeafInstructionB p index labels n = true) :
    ∃ operation, decodeSemanticInstrOp? n.aux = some operation ∧
      operation ∈ [.scalar, .aggregate, .project, .branch, .jump, .loop, .range, .dispatch,
        .index, .divRem, .stringCompare, .ctEq, .ctSelect, .ctLt, .address, .trap, .output] := by
  cases hop : decodeSemanticInstrOp? n.aux with
  | none => simp [semanticPrivateLeafInstructionB, hop] at h
  | some operation =>
      refine ⟨operation, rfl, ?_⟩
      cases operation <;> simp_all [semanticPrivateLeafInstructionB]

theorem private_leaf_excludes_calls_and_shared_operations {p : Program} {index : SemanticIndex}
    {labels : Array Label} {n : Node} {operation : SemanticInstrOp}
    (hop : decodeSemanticInstrOp? n.aux = some operation)
    (hforbidden : operation ∈ [.call, .closure, .actorBoundary, .stateRead, .stateWrite,
      .slotNew, .slotPut, .slotTake, .effect, .abortiveEffect, .ffi, .allocation, .capMint,
      .capRestrict, .capSplit, .capDraw, .capExercise, .release, .releaseCT, .halt]) :
    semanticPrivateLeafInstructionB p index labels n = false := by
  cases operation <;> simp_all [semanticPrivateLeafInstructionB]

theorem private_leaf_trap_is_unconditional {p : Program} {index : SemanticIndex}
    {labels : Array Label} {n : Node}
    (h : semanticPrivateLeafInstructionB p index labels n = true)
    (hop : decodeSemanticInstrOp? n.aux = some .trap) : n.ceiling = 0 := by
  simp only [semanticPrivateLeafInstructionB, hop, Bool.and_eq_true] at h
  simpa using h.2

theorem private_leaf_address_is_read_form {p : Program} {index : SemanticIndex}
    {labels : Array Label} {n : Node}
    (h : semanticPrivateLeafInstructionB p index labels n = true)
    (hop : decodeSemanticInstrOp? n.aux = some .address) : n.required ≠ 0 := by
  simp only [semanticPrivateLeafInstructionB, hop, Bool.and_eq_true] at h
  simpa using h.2

theorem private_leaf_index_is_read_form {p : Program} {index : SemanticIndex}
    {labels : Array Label} {n : Node}
    (h : semanticPrivateLeafInstructionB p index labels n = true)
    (hop : decodeSemanticInstrOp? n.aux = some .index) : n.required ≠ 0 := by
  simp only [semanticPrivateLeafInstructionB, hop, Bool.and_eq_true] at h
  simpa using h.2

private def leafScanStep (p : Program) (index : SemanticIndex) (labels : Array Label)
    (state : Array Bool × Array Bool) (n : Node) : Array Bool × Array Bool :=
  if n.op == .semInstruction then
    (state.1.setIfInBounds n.origin.toNat
      (state.1.getD n.origin.toNat false && semanticPrivateLeafInstructionB p index labels n),
      if n.aux == 28 then state.2.setIfInBounds n.origin.toNat true else state.2)
  else state

private def leafInitial (index : SemanticIndex) : Array Bool × Array Bool :=
  (index.functions.foldl (fun eligible function => eligible.setIfInBounds function.origin.toNat
    (function.flags == 1 || function.flags == 4)) (Array.replicate (index.functions.size + 1) false),
    Array.replicate (index.functions.size + 1) false)

private theorem leaf_cache_as_fold (p : Program) (index : SemanticIndex) (labels : Array Label) :
    semanticPrivateLeafReturnFunctions p index labels =
      let result := p.nodes.foldl (leafScanStep p index labels) (leafInitial index)
      result.1.mapIdx (fun function allowed => allowed && result.2.getD function false) := by
  unfold semanticPrivateLeafReturnFunctions leafInitial
  have hid {α β : Type} (nodes : Array α) (initial : β) (f : β → α → β) :
      (forIn nodes initial (fun a b => ForInStep.yield (f b a)) : Id β) = nodes.foldl f initial :=
    Array.forIn_pure_yield_eq_foldl (m := Id) (fun a b => f b a) initial
  simp only [Id.run, pure, bind, hid, ← apply_ite]
  rfl

private theorem getD_and_set {flags : Array Bool} {owner function : Nat} {allowed : Bool}
    (h : (flags.setIfInBounds owner (flags.getD owner false && allowed)).getD function false = true) :
    flags.getD function false = true ∧ (owner = function → allowed = true) := by
  by_cases heq : owner = function
  · subst owner
    by_cases hbound : function < flags.size
    · simpa [Array.getD, Array.setIfInBounds, hbound, Bool.and_eq_true] using h
    · simp [Array.getD, Array.setIfInBounds, hbound] at h
  · have hsame : (flags.setIfInBounds owner (flags.getD owner false && allowed)).getD
        function false = flags.getD function false := by
      by_cases howner : owner < flags.size <;> by_cases hfunction : function < flags.size <;>
        simp [Array.getD, Array.setIfInBounds, howner, hfunction, heq]
    exact ⟨hsame ▸ h, fun hequal => False.elim (heq hequal)⟩

private theorem scan_step_allowed {p : Program} {index : SemanticIndex} {labels : Array Label}
    {state : Array Bool × Array Bool} {n : Node} {function : Nat}
    (h : (leafScanStep p index labels state n).1.getD function false = true) :
    state.1.getD function false = true ∧
      ((n.op == .semInstruction) = true → n.origin.toNat = function →
        semanticPrivateLeafInstructionB p index labels n = true) := by
  unfold leafScanStep at h
  split at h
  · rename_i hop
    exact ⟨(getD_and_set h).1, fun _ howner => (getD_and_set h).2 howner⟩
  · rename_i hop
    exact ⟨h, fun hyes => False.elim (hop hyes)⟩

private theorem scan_allowed {p : Program} {index : SemanticIndex} {labels : Array Label}
    {nodes : List Node} {state : Array Bool × Array Bool} {function : Nat}
    (h : (nodes.foldl (leafScanStep p index labels) state).1.getD function false = true) :
    state.1.getD function false = true ∧
      ∀ n ∈ nodes, (n.op == .semInstruction) = true → n.origin.toNat = function →
        semanticPrivateLeafInstructionB p index labels n = true := by
  induction nodes generalizing state with
  | nil => exact ⟨h, by simp⟩
  | cons head tail ih =>
      have htail := ih h
      have hhead := scan_step_allowed htail.1
      refine ⟨hhead.1, ?_⟩
      intro n hn hop howner
      rcases List.mem_cons.mp hn with rfl | hn
      · exact hhead.2 hop howner
      · exact htail.2 n hn hop howner

private theorem cache_both_flags {p : Program} {index : SemanticIndex} {labels : Array Label}
    {function : Nat}
    (h : (semanticPrivateLeafReturnFunctions p index labels).getD function false = true) :
    let result := p.nodes.foldl (leafScanStep p index labels) (leafInitial index)
    result.1.getD function false = true ∧ result.2.getD function false = true := by
  rw [leaf_cache_as_fold] at h
  dsimp only at h ⊢
  by_cases hbound : function <
      (p.nodes.foldl (leafScanStep p index labels) (leafInitial index)).1.size
  · simpa [Array.getD, hbound, Bool.and_eq_true] using h
  · simp [Array.getD, hbound] at h

/-- A positive cached function classification entails the local check for every source
    instruction owned by that function, including instructions after an earlier private return. -/
theorem classified_leaf_checks_every_owned_instruction {p : Program} {index : SemanticIndex}
    {labels : Array Label} {function : Nat}
    (h : (semanticPrivateLeafReturnFunctions p index labels).getD function false = true)
    {n : Node} (hn : n ∈ p.nodes.toList) (hop : (n.op == .semInstruction) = true)
    (howner : n.origin.toNat = function) :
    semanticPrivateLeafInstructionB p index labels n = true := by
  have hallowed := (cache_both_flags h).1
  rw [← Array.foldl_toList] at hallowed
  exact (scan_allowed hallowed).2 n hn hop howner

private theorem scan_step_output_source {p : Program} {index : SemanticIndex}
    {labels : Array Label} {state : Array Bool × Array Bool} {n : Node} {function : Nat}
    (h : (leafScanStep p index labels state n).2.getD function false = true) :
    state.2.getD function false = true ∨
      (n.op == .semInstruction) = true ∧ n.origin.toNat = function ∧ n.aux = 28 := by
  unfold leafScanStep at h
  split at h
  · rename_i hop
    dsimp only at h
    split at h
    · rename_i houtput
      by_cases heq : n.origin.toNat = function
      · exact Or.inr ⟨hop, heq, by simpa using houtput⟩
      · left
        have hsame : (state.2.setIfInBounds n.origin.toNat true).getD function false =
            state.2.getD function false := by
          by_cases howner : n.origin.toNat < state.2.size <;>
            by_cases hfunction : function < state.2.size <;>
              simp [Array.getD, Array.setIfInBounds, howner, hfunction, heq]
        exact hsame ▸ h
    · exact Or.inl h
  · exact Or.inl h

private theorem scan_output_source {p : Program} {index : SemanticIndex} {labels : Array Label}
    {nodes : List Node} {state : Array Bool × Array Bool} {function : Nat}
    (h : (nodes.foldl (leafScanStep p index labels) state).2.getD function false = true) :
    state.2.getD function false = true ∨ ∃ n ∈ nodes,
      (n.op == .semInstruction) = true ∧ n.origin.toNat = function ∧ n.aux = 28 := by
  induction nodes generalizing state with
  | nil => exact Or.inl h
  | cons head tail ih =>
      rcases ih h with hstep | ⟨n, hn, hop, howner, houtput⟩
      · rcases scan_step_output_source hstep with hbefore | hhead
        · exact Or.inl hbefore
        · exact Or.inr ⟨head, List.mem_cons_self, hhead⟩
      · exact Or.inr ⟨n, List.mem_cons_of_mem _ hn, hop, howner, houtput⟩

/-- A cached leaf cannot be justified vacuously by an empty body or by a function that only
    loops: it has an actual source output, and that output returns a non-Public value cell. -/
theorem classified_leaf_has_private_output_witness {p : Program} {index : SemanticIndex}
    {labels : Array Label} {function : Nat}
    (h : (semanticPrivateLeafReturnFunctions p index labels).getD function false = true) :
    ∃ n ∈ p.nodes.toList, (n.op == .semInstruction) = true ∧ n.origin.toNat = function ∧
      n.aux = 28 ∧ n.ceiling = 1 ∧ ∃ valueId cell,
      semanticOperandValueIdAt? p n.nodeId 0 = some valueId ∧
      semanticValueCell? index n.origin valueId = some cell ∧
      cell.toNat < labels.size ∧ labelAt labels cell ≠ .pub := by
  have houtput := (cache_both_flags h).2
  rw [← Array.foldl_toList] at houtput
  rcases scan_output_source houtput with hfalse | ⟨n, hn, hop, howner, haux⟩
  · simp [leafInitial, Array.getD] at hfalse
  · have hlocal := classified_leaf_checks_every_owned_instruction h hn hop howner
    have hexact := private_leaf_output_has_private_value hlocal (by simp [haux, decodeSemanticInstrOp?])
    exact ⟨n, hn, hop, howner, haux, hexact⟩

private theorem seed_step_source {flags : Array Bool} {declaration : Node} {function : Nat}
    (h : (flags.setIfInBounds declaration.origin.toNat
      (declaration.flags == 1 || declaration.flags == 4)).getD function false = true) :
    flags.getD function false = true ∨ declaration.origin.toNat = function ∧
      (declaration.flags = 1 ∨ declaration.flags = 4) := by
  by_cases heq : declaration.origin.toNat = function
  · right
    refine ⟨heq, ?_⟩
    by_cases hbound : function < flags.size
    · simpa [Array.getD, Array.setIfInBounds, heq, hbound] using h
    · simp [Array.getD, Array.setIfInBounds, heq, hbound] at h
  · left
    have hsame : (flags.setIfInBounds declaration.origin.toNat
        (declaration.flags == 1 || declaration.flags == 4)).getD function false =
          flags.getD function false := by
      by_cases howner : declaration.origin.toNat < flags.size <;>
        by_cases hfunction : function < flags.size <;>
          simp [Array.getD, Array.setIfInBounds, howner, hfunction, heq]
    exact hsame ▸ h

private theorem seed_source {declarations : List Node} {flags : Array Bool} {function : Nat}
    (h : (declarations.foldl (fun eligible declaration => eligible.setIfInBounds
      declaration.origin.toNat (declaration.flags == 1 || declaration.flags == 4))
        flags).getD function false = true) :
    flags.getD function false = true ∨ ∃ declaration ∈ declarations,
      declaration.origin.toNat = function ∧ (declaration.flags = 1 ∨ declaration.flags = 4) := by
  induction declarations generalizing flags with
  | nil => exact Or.inl h
  | cons head tail ih =>
      rcases ih h with hstep | ⟨declaration, hmember, howner, hkind⟩
      · rcases seed_step_source hstep with hbefore | hhead
        · exact Or.inl hbefore
        · exact Or.inr ⟨head, List.mem_cons_self, hhead⟩
      · exact Or.inr ⟨declaration, List.mem_cons_of_mem _ hmember, howner, hkind⟩

/-- The positive bit originates in an indexed module/closure declaration. Structural decoding
    separately proves that these indexed declarations are the actual canonical source functions. -/
theorem classified_leaf_has_module_or_closure_declaration {p : Program} {index : SemanticIndex}
    {labels : Array Label} {function : Nat}
    (h : (semanticPrivateLeafReturnFunctions p index labels).getD function false = true) :
    ∃ declaration ∈ index.functions.toList, declaration.origin.toNat = function ∧
      (declaration.flags = 1 ∨ declaration.flags = 4) := by
  have hallowed := (cache_both_flags h).1
  rw [← Array.foldl_toList] at hallowed
  have hinitial := (scan_allowed hallowed).1
  simp only [leafInitial] at hinitial
  rw [← Array.foldl_toList] at hinitial
  rcases seed_source hinitial with hfalse | hsource
  · simp [Array.getD] at hfalse
  · exact hsource

namespace PrivateLeafReturnWitnesses

/- The full verifier is evaluated on actual source Programs. These small witnesses exercise only
   the bounded compatibility correction; they do not establish full JSON or v9 acceptance. -/

private def node (op : Op) (id origin actual required ceiling aux : UInt32)
    (flags : UInt8 := 1) (label : Label := .pub) : Node :=
  { op, nodeId := id, origin, actual, required, ceiling, aux, flags,
    labelA := label, labelB := label }

private def privateLeaf : Program := ⟨#[
  node .semProgram 1 1 3 3 6 1,
  node .semFunction 2 1 1 3 1 0,
  node .semValue 3 1 1 1 0 0,
  node .semBlock 4 1 1 1 0 0,
  node .semInstruction 5 1 1 0 4 3,
  node .semOperand 6 5 0 1 0 0 0,
  node .semOperand 7 5 1 2 0 0,
  node .semOperand 8 5 2 3 0 0,
  node .semOperand 9 5 3 3 0 0,
  node .semBlock 10 1 2 1 0 0,
  node .semInstruction 11 1 2 0 1 28,
  node .semOperand 12 11 0 1 0 0 0,
  node .semBlock 13 1 3 1 0 0,
  node .semInstruction 14 1 3 0 1 28,
  node .semOperand 15 14 0 1 0 0 0,
  node .semLabelContract 16 1 0 2 0 2 1 .secret,
  node .semLabelContract 17 1 1 0 0 0 1 .secret,
  node .semPolicyClass 18 5 1 20 0 0]⟩

private def leafCache (p : Program) : Array Bool :=
  let index := buildSemanticIndex p
  semanticPrivateLeafReturnFunctions p index (semanticLabelsWithIndex p index)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem private_early_return_exercises_accepted_leaf_exception :
    leafCache privateLeaf = #[false, true] ∧ verifyProgram privateLeaf = none ∧
      verifyProgramWithRawSemantics privateLeaf = none ∧
      ((privateLeaf.nodes[4]?).map (semanticPublicControlContinuationOK privateLeaf
        (buildSemanticIndex privateLeaf) (semanticLabels privateLeaf))) = some false := by
  decide +kernel

private def laterWrite (writtenLabel : Label) : Program := ⟨#[
  node .semProgram 1 1 4 5 8 2,
  node .semFunction 2 1 1 4 2 0,
  node .semValue 3 1 1 1 0 0,
  node .semValue 4 1 2 0 0 0,
  node .semBlock 5 1 1 1 0 0,
  node .semInstruction 6 1 1 0 4 3,
  node .semOperand 7 6 0 1 0 0 0,
  node .semOperand 8 6 1 2 0 0,
  node .semOperand 9 6 2 3 0 0,
  node .semOperand 10 6 3 4 0 0,
  node .semBlock 11 1 2 1 0 0,
  node .semInstruction 12 1 2 0 1 28,
  node .semOperand 13 12 0 1 0 0 0,
  node .semBlock 14 1 3 1 0 0,
  node .semInstruction 15 1 3 0 1 4,
  node .semOperand 16 15 0 4 0 0,
  node .semBlock 17 1 4 2 0 0,
  node .semInstruction 18 1 4 2 1 0,
  node .semOperand 19 18 0 7 0 0 3,
  node .semInstruction 20 1 4 0 1 28,
  node .semOperand 21 20 0 1 0 0 0,
  node .semLabelContract 22 1 0 2 0 2 1 .secret,
  node .semLabelContract 23 1 1 0 0 0 1 .secret,
  node .semLabelContract 24 1 2 1 0 1 1 writtenLabel,
  node .semPolicyClass 25 6 1 20 0 0]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem later_private_write_retains_leaf_acceptance :
    leafCache (laterWrite .secret) = #[false, true] ∧
      verifyProgram (laterWrite .secret) = none ∧
      verifyProgramWithRawSemantics (laterWrite .secret) = none := by decide +kernel

/- Changing only the written value's contract produces the dangerous skipped-Public-write
    variant. The declared merge no longer postdominates the early-returning arm, so the later
    write executes under the branch's private pc and its Secret result violates the written
    value's Public contract: the program is rejected as a flow violation at that contract node
    before the private-return exception is ever consulted. The leaf classification itself still
    holds, because every result the function computes is private; what fails is the contract. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem later_public_write_cannot_hide_behind_private_returns :
    leafCache (laterWrite .pub) = #[false, true] ∧
      verifyProgram (laterWrite .pub) = some ⟨.flow, 24, 1⟩ ∧
      verifyProgramWithRawSemantics (laterWrite .pub) = some ⟨.flow, 24, 1⟩ ∧
      (((semanticProgramOf (laterWrite .pub)).instructions[3]?).map
        (fun instruction => (instruction.id, instruction.destination, instruction.resultLabel))) =
          some (18, 4, .secret) := by decide +kernel

private def withCall : Program := ⟨#[
  node .semProgram 1 1 3 4 8 1,
  node .semFunction 2 1 1 3 1 0,
  node .semValue 3 1 1 1 0 0,
  node .semBlock 4 1 1 2 0 0,
  node .semInstruction 5 1 1 0 2 6,
  node .semOperand 6 5 0 1 0 0 2,
  node .semOperand 7 5 1 1 0 0 0,
  node .semInstruction 8 1 1 0 4 3,
  node .semOperand 9 8 0 1 0 0 0,
  node .semOperand 10 8 1 2 0 0,
  node .semOperand 11 8 2 3 0 0,
  node .semOperand 12 8 3 3 0 0,
  node .semBlock 13 1 2 1 0 0,
  node .semInstruction 14 1 2 0 1 28,
  node .semOperand 15 14 0 1 0 0 0,
  node .semBlock 16 1 3 1 0 0,
  node .semInstruction 17 1 3 0 1 28,
  node .semOperand 18 17 0 1 0 0 0,
  node .semLabelContract 19 1 0 2 0 2 1 .secret,
  node .semLabelContract 20 1 1 0 0 0 1 .secret,
  node .semPolicyClass 21 8 1 20 0 0]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem recursive_call_does_not_qualify_as_private_leaf :
    leafCache withCall = #[false, false] ∧ verifyProgram withCall = none ∧
      verifyProgramWithRawSemantics withCall = some ⟨.malformed, 8, 9⟩ := by decide +kernel

private def withHalt : Program := ⟨#[
  node .semProgram 1 1 3 3 5 1,
  node .semFunction 2 1 1 3 1 0,
  node .semValue 3 1 1 1 0 0,
  node .semBlock 4 1 1 1 0 0,
  node .semInstruction 5 1 1 0 4 3,
  node .semOperand 6 5 0 1 0 0 0,
  node .semOperand 7 5 1 2 0 0,
  node .semOperand 8 5 2 3 0 0,
  node .semOperand 9 5 3 3 0 0,
  node .semBlock 10 1 2 1 0 0,
  node .semInstruction 11 1 2 0 0 30,
  node .semBlock 12 1 3 1 0 0,
  node .semInstruction 13 1 3 0 1 28,
  node .semOperand 14 13 0 1 0 0 0,
  node .semLabelContract 15 1 0 2 0 2 1 .secret,
  node .semLabelContract 16 1 1 0 0 0 1 .secret,
  node .semPolicyClass 17 5 1 20 0 0]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem whole_machine_halt_does_not_qualify_as_private_leaf :
    leafCache withHalt = #[false, false] ∧ verifyProgram withHalt = none ∧
      verifyProgramWithRawSemantics withHalt = some ⟨.malformed, 11, 9⟩ := by decide +kernel

private def rebase (records : Array Node) : Program :=
  ⟨records.mapIdx fun position n =>
    { n with nodeId := UInt32.ofNat (position + 1), origin :=
      if n.op == .semOperand || n.op == .semPolicyClass then
        UInt32.ofNat ((records.findIdx? fun owner => owner.nodeId == n.origin).getD 0 + 1)
      else n.origin }⟩

/- These are the compiler's actual dynamic-read/dynamic-store operand layouts: two/three value
   operands followed by element size, value type, and offset. Both address and index policy
   records are present, so a store's refusal is not incidental malformed-metadata rejection. -/
private def dynamicIndexLeaf (store : Bool) : Program :=
  let records := (laterWrite .secret).nodes
  let count : Nat := if store then 3 else 2
  let manifest := { records.getD 0 (node .semProgram 1 1 4 5 8 2) with
    ceiling := UInt32.ofNat (7 + count + 3) }
  let value := { records.getD 3 (node .semValue 4 1 2 0 0 0) with required := 4 }
  let beforeIndex := (records.extract 0 17).setIfInBounds 0 manifest |>.setIfInBounds 3 value
  let operation := node .semInstruction 18 1 4 (if store then 0 else 2)
    (UInt32.ofNat (count + 3)) 33
  let operands := (List.range (count + 3)).toArray.map fun position =>
    node .semOperand (UInt32.ofNat (100 + position)) 18 (UInt32.ofNat position)
      (if position < count then 2 else #[8, 4, 0].getD (position - count) 0) 0 0
      (if position < count then 0 else 3)
  let policies := #[node .semPolicyClass 201 18 3 24 0 4,
    node .semPolicyClass 202 18 3 25 0 5]
  rebase (beforeIndex ++ #[operation] ++ operands ++ records.extract 19 records.size ++ policies)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem private_dynamic_index_read_retains_leaf_acceptance :
    leafCache (dynamicIndexLeaf false) = #[false, true] ∧
      verifyProgram (dynamicIndexLeaf false) = none ∧
      verifyProgramWithRawSemantics (dynamicIndexLeaf false) = none ∧
      (((semanticProgramOf (dynamicIndexLeaf false)).instructions[3]?).map
        (fun instruction => (instruction.op, instruction.destination, instruction.resultLabel))) =
          some (.index, 4, .secret) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem destination_free_dynamic_store_is_not_a_private_leaf_read :
    leafCache (dynamicIndexLeaf true) = #[false, false] ∧
      verifyProgram (dynamicIndexLeaf true) = none ∧
      verifyProgramWithRawSemantics (dynamicIndexLeaf true) = some ⟨.malformed, 6, 9⟩ ∧
      (((semanticProgramOf (dynamicIndexLeaf true)).instructions[3]?).map
        (fun instruction => (instruction.op, instruction.destination))) =
          some (.index, 0) := by decide +kernel

end PrivateLeafReturnWitnesses

end LambdaSigil.Combined.PrivateLeafReturnSecurity
