import LambdaSigil.SemanticDataflow
import LambdaSigil.CombinedSecurity

/-!
# Source-derived semantic-index bounds

The semantic graph's endpoint premise is unary: indexed values, blocks, and parameters must refer
to allocated source cells. This module tracks those fields through the actual index-building fold.
It changes neither decoding nor acceptance and does not remove malformed edges to obtain bounds.
-/

namespace LambdaSigil.Combined.SemanticIndexBounds

open SemanticDataflow

/-- The three index fields that can become semantic graph targets. Other fields only select
    existing records or supply edge sources, so no bound on them is assumed here. -/
structure IndexContentsBound (count : Nat) (index : SemanticIndex) : Prop where
  values : ∀ node ∈ index.values, node.nodeId.toNat < count
  blocks : ∀ node ∈ index.blocks, node.nodeId.toNat < count
  parameters : ∀ site : Nat, ∀ cell ∈ index.parameterCells.getD site [], cell.toNat < count

private theorem cellLists_set_preserves_bound {count : Nat} {lists : Array (List UInt32)}
    (hbound : ∀ site : Nat, ∀ cell ∈ lists.getD site [], cell.toNat < count)
    (site : Nat) (cells : List UInt32) (hcells : ∀ cell ∈ cells, cell.toNat < count) :
    ∀ observed : Nat, ∀ cell ∈ (lists.setIfInBounds site cells).getD observed [],
      cell.toNat < count := by
  intro observed cell hcell
  by_cases hobserved : observed < lists.size
  · have hget := Array.getElem_setIfInBounds (xs := lists) (i := site)
      (a := cells) (j := observed) hobserved
    by_cases heq : site = observed
    · subst site
      apply hcells cell
      simpa [Array.getD, hobserved] using hcell
    · apply hbound observed cell
      simpa [Array.getD, hobserved, hget, heq] using hcell
  · simp [Array.getD, hobserved] at hcell

private theorem contract_target_bound {count : Nat} {index : SemanticIndex}
    (hindex : IndexContentsBound count index) (node : Node) {cell : Nat}
    (hcell :
      ((index.valueStarts[node.origin.toNat - 1]?).bind fun start =>
        (index.functions[node.origin.toNat - 1]?).bind fun function =>
          if node.actual.toNat ≤ function.ceiling.toNat then
            (index.values[start + node.actual.toNat - 1]?).map (fun value => value.nodeId.toNat)
          else none) = some cell) : cell < count := by
  rw [Option.bind_eq_some_iff] at hcell
  obtain ⟨start, _, hcell⟩ := hcell
  rw [Option.bind_eq_some_iff] at hcell
  obtain ⟨function, _, hcell⟩ := hcell
  split at hcell
  · rw [Option.map_eq_some_iff] at hcell
    obtain ⟨value, hvalue, rfl⟩ := hcell
    exact hindex.values value (Array.mem_of_getElem? hvalue)
  · cases hcell

/-- Every index target stays within the original source-ID bound throughout the actual fold.
    The input list need not already satisfy semantic typing or control-region rules. -/
theorem buildSemanticIndex_contents_bound {p : Program} {count : Nat}
    (hsource : ∀ node ∈ p.nodes.toList, node.nodeId.toNat < count) :
    IndexContentsBound count (buildSemanticIndex p) := by
  unfold buildSemanticIndex
  rw [← Array.foldl_toList]
  apply List.foldlRecOn
  · refine ⟨?_, ?_, ?_⟩
    · simp [emptySemanticIndex]
    · simp [emptySemanticIndex]
    · intro site cell hcell
      simp [emptySemanticIndex, Array.getD] at hcell
  · intro index hindex node hmember
    have hnode := hsource node hmember
    cases node.op <;> dsimp only
    all_goals try exact ⟨hindex.values, hindex.blocks, hindex.parameters⟩
    case semValue =>
      refine ⟨?_, hindex.blocks, hindex.parameters⟩
      intro value hvalue
      simp only [Array.mem_push] at hvalue
      exact hvalue.elim (hindex.values value) (fun heq => heq ▸ hnode)
    case semBlock =>
      refine ⟨hindex.values, ?_, hindex.parameters⟩
      intro block hblock
      simp only [Array.mem_push] at hblock
      exact hblock.elim (hindex.blocks block) (fun heq => heq ▸ hnode)
    case semInstruction =>
      repeat' first | exact ⟨hindex.values, hindex.blocks, hindex.parameters⟩ | split
    case semLabelContract =>
      split
      · split
        · rename_i cell hcell
          have hcellBound := contract_target_bound hindex node hcell
          split
          · refine ⟨hindex.values, hindex.blocks, ?_⟩
            apply cellLists_set_preserves_bound hindex.parameters
            intro candidate hcandidate
            simp only [List.mem_append, List.mem_singleton] at hcandidate
            rcases hcandidate with hcandidate | rfl
            · exact hindex.parameters _ candidate hcandidate
            · have hmod : (UInt32.ofNat cell).toNat ≤ cell := Nat.mod_le _ _
              exact Nat.lt_of_le_of_lt hmod hcellBound
          · exact ⟨hindex.values, hindex.blocks, hindex.parameters⟩
        · exact ⟨hindex.values, hindex.blocks, hindex.parameters⟩
      · split <;> exact ⟨hindex.values, hindex.blocks, hindex.parameters⟩

private theorem indexedSemanticValueNode_mem {index : SemanticIndex}
    {functionId valueId : UInt32} {node : Node}
    (hnode : indexedSemanticValueNode? index functionId valueId = some node) :
    node ∈ index.values := by
  unfold indexedSemanticValueNode? at hnode
  rw [Option.bind_eq_some_iff] at hnode
  obtain ⟨start, _, hnode⟩ := hnode
  rw [Option.bind_eq_some_iff] at hnode
  obtain ⟨function, _, hnode⟩ := hnode
  split at hnode
  · exact Array.mem_of_getElem? hnode
  · cases hnode

private theorem indexedSemanticBlockNode_mem {index : SemanticIndex}
    {functionId blockId : UInt32} {node : Node}
    (hnode : indexedSemanticBlockNode? index functionId blockId = some node) :
    node ∈ index.blocks := by
  unfold indexedSemanticBlockNode? at hnode
  rw [Option.bind_eq_some_iff] at hnode
  obtain ⟨start, _, hnode⟩ := hnode
  rw [Option.bind_eq_some_iff] at hnode
  obtain ⟨function, _, hnode⟩ := hnode
  split at hnode
  · exact Array.mem_of_getElem? hnode
  · cases hnode

theorem indexCellBounds_of_contents {count : Nat} {index : SemanticIndex}
    (hindex : IndexContentsBound count index) : IndexCellBounds count index := by
  refine ⟨?_, ?_, ?_⟩
  · intro functionId blockId cell hcell
    rw [semanticBlockCell?, Option.map_eq_some_iff] at hcell
    obtain ⟨node, hnode, rfl⟩ := hcell
    exact hindex.blocks node (indexedSemanticBlockNode_mem hnode)
  · intro functionId valueId cell hcell
    rw [semanticValueCell?, Option.map_eq_some_iff] at hcell
    obtain ⟨node, hnode, rfl⟩ := hcell
    exact hindex.values node (indexedSemanticValueNode_mem hnode)
  · intro functionId cell hcell
    exact hindex.parameters functionId.toNat cell hcell

theorem buildSemanticIndex_cell_bounds_of_source_ids {p : Program}
    (hsource : ∀ node ∈ p.nodes.toList, node.nodeId.toNat ≤ p.nodes.size) :
    IndexCellBounds (semanticTaintCellCount p) (buildSemanticIndex p) := by
  apply indexCellBounds_of_contents
  apply buildSemanticIndex_contents_bound
  intro node hnode
  have hbound := hsource node hnode
  unfold semanticTaintCellCount
  omega

theorem buildSemanticIndex_cell_bounds_of_canonical {p : Program}
    (hcanonical : CanonicalNodeIds p) :
    IndexCellBounds (semanticTaintCellCount p) (buildSemanticIndex p) := by
  apply buildSemanticIndex_cell_bounds_of_source_ids
  intro node hnode
  obtain ⟨position, hposition, rfl⟩ := List.mem_iff_getElem.mp hnode
  rw [hcanonical position hposition]
  simpa using Nat.succ_le_of_lt hposition

theorem semanticLabels_is_least_solution_of_canonical {p : Program}
    (hcanonical : CanonicalNodeIds p) :
    SemanticSolution p (semanticLabels p) ∧
      ∀ candidate, SemanticSolution p candidate → ArrayFlows (semanticLabels p) candidate :=
  semanticLabels_is_least_solution_of_index_bounds
    (buildSemanticIndex_cell_bounds_of_canonical hcanonical)

private def noncanonicalBlockProgram : Program :=
  ⟨minimalSemanticProgram.nodes.setIfInBounds 2
    { minimalSemanticBlock with nodeId := 1000 }⟩

/-- `ProgramSafe` is a predicate on already constructed programs, not a substitute for the wire
    decoder's canonical numbering check. An unused block-cell ID can otherwise exceed the label
    allocation even when the retained program checker accepts its halt-only machine. -/
theorem program_safe_without_canonical_ids_does_not_bound_index :
    ProgramSafe noncanonicalBlockProgram ∧
      ¬ IndexCellBounds (semanticTaintCellCount noncanonicalBlockProgram)
        (buildSemanticIndex noncanonicalBlockProgram) := by
  constructor
  · unfold ProgramSafe
    decide +kernel
  · intro hbounds
    have hlookup : semanticBlockCell? (buildSemanticIndex noncanonicalBlockProgram) 1 1 =
        some 1000 := by decide +kernel
    have hbound := hbounds.block 1 1 1000 hlookup
    have hcount : semanticTaintCellCount noncanonicalBlockProgram = 8 := by decide +kernel
    rw [hcount] at hbound
    contradiction

end LambdaSigil.Combined.SemanticIndexBounds
