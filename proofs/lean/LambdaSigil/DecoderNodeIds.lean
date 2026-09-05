import LambdaSigil.SemanticIndexBounds
import Init.Data.Range.Lemmas

/-!
# Decoder-derived canonical node IDs

This module derives the structural source-cell premise from successful byte decoding. The proof
tracks the actual decoder loop's array growth and numbering check; it changes neither the wire
decoder nor any verifier guard.
-/

namespace LambdaSigil.Combined.DecoderNodeIds

open SemanticDataflow SemanticIndexBounds

private theorem canonical_push {nodes : Array Node} {node : Node}
    (hcanonical : CanonicalNodeIds ⟨nodes⟩)
    (hnode : node.nodeId.toNat = nodes.size + 1) :
    CanonicalNodeIds ⟨nodes.push node⟩ := by
  intro index hindex
  simp only [Array.toList_push, List.length_append, List.length_singleton,
    Array.length_toList] at hindex
  by_cases hbefore : index < nodes.size
  · simpa [List.getElem_append_left, hbefore] using hcanonical index hbefore
  · have heq : index = nodes.size := by omega
    subst index
    simpa using hnode

private theorem checked_loop_canonical
    (read : Nat → Option Node) (remaining : Nat) :
    ∀ (start : Nat) (nodes result : Array Node),
      nodes.size = start → CanonicalNodeIds ⟨nodes⟩ →
      start + remaining < UInt32.size →
      (forIn (List.range' start remaining) nodes fun i current => do
        let node ← read i
        if node.nodeId != UInt32.ofNat (i + 1) then none
        pure (ForInStep.yield (current.push node))) = some result →
      result.size = start + remaining ∧ CanonicalNodeIds ⟨result⟩ := by
  induction remaining with
  | zero =>
    intro start nodes result hsize hcanonical _ hrun
    simp only [List.range'_zero, List.forIn_nil, pure] at hrun
    cases hrun
    exact ⟨by omega, hcanonical⟩
  | succ remaining ih =>
    intro start nodes result hsize hcanonical hbound hrun
    simp only [List.range'_succ, List.forIn_cons] at hrun
    cases hread : read start with
    | none => simp [hread] at hrun
    | some node =>
      by_cases hcheck : node.nodeId = UInt32.ofNat (start + 1)
      · simp [hread, hcheck] at hrun
        have hnat : node.nodeId.toNat = nodes.size + 1 := by
          rw [hcheck, UInt32.toNat_ofNat_of_lt' (by omega), hsize]
        have hnext := ih (start + 1) (nodes.push node) result
          (by simp [hsize]) (canonical_push hcanonical hnat) (by omega)
          (by simpa using hrun)
        exact ⟨by omega, hnext.2⟩
      · simp_all

/-- Successful decoding establishes the canonical numbering premise directly from the wire
    checks. No program-checker acceptance or relational semantic premise is required. -/
theorem decode_canonical_node_ids {bytes : ByteArray} {p : Program}
    (hdecode : decode bytes = some p) : CanonicalNodeIds p := by
  unfold decode at hdecode
  simp only [bind, pure] at hdecode
  split at hdecode
  · cases hdecode
  · rw [Option.bind_eq_some_iff] at hdecode
    obtain ⟨version, _, hdecode⟩ := hdecode
    split at hdecode
    · cases hdecode
    · rw [Option.bind_eq_some_iff] at hdecode
      obtain ⟨count, _, hdecode⟩ := hdecode
      split at hdecode
      · cases hdecode
      · rename_i hcount
        split at hdecode
        · cases hdecode
        · rw [Option.bind_eq_some_iff] at hdecode
          obtain ⟨nodes, hloop, hprogram⟩ := hdecode
          cases hprogram
          rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop
          simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
            Nat.div_one] at hloop
          exact (checked_loop_canonical _ count.toNat 0 #[] nodes rfl
            (by intro index hindex; simp at hindex)
            (by simp only [UInt32.size]; unfold maxNodes at hcount; omega) hloop).2

/-- Every semantic-index target is allocated for any successfully decoded byte program. -/
theorem buildSemanticIndex_cell_bounds_of_decode {bytes : ByteArray} {p : Program}
    (hdecode : decode bytes = some p) :
    IndexCellBounds (semanticTaintCellCount p) (buildSemanticIndex p) :=
  buildSemanticIndex_cell_bounds_of_canonical (decode_canonical_node_ids hdecode)

/-- The existing bounded semantic worklist computes the least solution for decoded programs,
    including the actual control, call, parameter, and closure-summary edges. -/
theorem semanticLabels_is_least_solution_of_decode {bytes : ByteArray} {p : Program}
    (hdecode : decode bytes = some p) :
    SemanticSolution p (semanticLabels p) ∧
      ∀ candidate, SemanticSolution p candidate → ArrayFlows (semanticLabels p) candidate :=
  semanticLabels_is_least_solution_of_canonical (decode_canonical_node_ids hdecode)

end LambdaSigil.Combined.DecoderNodeIds
