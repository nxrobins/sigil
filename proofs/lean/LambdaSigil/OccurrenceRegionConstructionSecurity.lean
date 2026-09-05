import LambdaSigil.OccurrenceRegionConstruction
import LambdaSigil.OccurrenceRegionSecurity
import LambdaSigil.OccurrenceReference

/-!
# Checked internal region construction and bounded success queues

The queue's arrays have exactly one slot per graph vertex; counters remain within that fixed
allocation. Returned constructions pass the existing path-soundness checker, so their success
table covers every finite successful graph path and every reported live node has such a path.
The current result is conditional on successful construction: solver totality and final native
region-transfer performance are not asserted. The small generated corpus compares the internal
BFS with the independent slow reachability oracle and includes a planted incomplete-rank mutant.
-/

namespace LambdaSigil.Combined.OccurrenceRegionConstructionSecurity

open OccurrenceRegions OccurrenceRegionConstruction OccurrenceRegionSecurity

def QueueShape (count : Nat) (state : SuccessQueue) : Prop :=
  state.ranks.size = count ∧ state.queue.size = count ∧
    state.head ≤ state.tail ∧ state.tail ≤ count

theorem enqueue_preserves_shape {count : Nat} {state : SuccessQueue}
    (hshape : QueueShape count state) (node rank : Nat) :
    QueueShape count (enqueue state node rank) := by
  unfold enqueue
  split
  · exact hshape
  · split
    · exact hshape
    · split
      · exact hshape
      · simp only [QueueShape, Array.size_setIfInBounds]
        rcases hshape with ⟨hranks, hqueue, hhead, htail⟩
        refine ⟨hranks, hqueue, ?_, ?_⟩ <;> omega

theorem successBfs_preserves_shape {count : Nat} {state : SuccessQueue}
    (hshape : QueueShape count state) (reverse : Array (List Nat)) (fuel : Nat) :
    QueueShape count (successBfs reverse fuel state) := by
  induction fuel generalizing state with
  | zero => exact hshape
  | succ fuel ih =>
    unfold successBfs
    split
    · exact hshape
    · rename_i hactive
      dsimp only
      split
      · exact hshape
      · apply ih
        apply List.foldlRecOn
        · rcases hshape with ⟨hranks, hqueue, hhead, htail⟩
          simp only [Bool.or_eq_true, Bool.not_eq_true, decide_eq_true_eq,
            not_or] at hactive
          exact ⟨hranks, hqueue, by dsimp; omega, htail⟩
        · intro next hnext predecessor _
          exact enqueue_preserves_shape hnext predecessor _

theorem computeSuccessQueue_bounded (graph : ControlGraph) :
    QueueShape graph.size (computeSuccessQueue graph) := by
  apply successBfs_preserves_shape
  apply List.foldlRecOn
  · simp [QueueShape]
  · intro state hstate exit _
    exact enqueue_preserves_shape hstate exit 0

theorem reverseEdges_size (graph : ControlGraph) : (reverseEdges graph).size = graph.size := by
  unfold reverseEdges
  apply List.foldlRecOn (motive := fun reverse : Array (List Nat) => reverse.size = graph.size)
  · simp
  · intro reverse hsize source _
    apply List.foldlRecOn (motive := fun reverse : Array (List Nat) => reverse.size = graph.size)
    · exact hsize
    · intro next hnext target _
      simpa using hnext

theorem successRanks_checked {graph : ControlGraph} {ranks : Array (Option Nat)}
    (h : successRanks? graph = some ranks) : successRankChecks graph ranks = true := by
  unfold successRanks? at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
        assumption
      · cases h

private theorem marked_mask_lookup (exits : List Nat) (mask : Array Bool) (node : Nat)
    (hnode : node < mask.size) :
    (exits.foldl (fun next exit => next.setIfInBounds exit true) mask).getD node false =
      (mask.getD node false || exits.contains node) := by
  induction exits generalizing mask with
  | nil => simp
  | cons exit exits ih =>
    rw [List.foldl_cons, ih _ (by simpa using hnode)]
    by_cases heq : exit = node
    · subst exit
      simp [Array.getD, hnode]
    · simp [Array.getD, hnode, heq, Ne.symm heq]

private theorem exitMask_true_iff (graph : ControlGraph) {node : Nat}
    (hnode : node < graph.size) :
    (exitMask graph).getD node false = true ↔ node ∈ graph.successfulExits := by
  unfold exitMask
  rw [marked_mask_lookup graph.successfulExits _ node (by simpa using hnode)]
  simp [Array.getD, hnode]

private structure RankFacts (graph : ControlGraph) (ranks : Array (Option Nat)) : Prop where
  size : ranks.size = graph.size
  exitRank : ∀ exit ∈ graph.successfulExits, rankAt ranks exit = some 0
  edgeBound : ∀ source < graph.size, ∀ target ∈ graph.successors.getD source [],
    target < graph.size
  justified : ∀ source < graph.size, ∀ rank, rankAt ranks source = some rank →
    source ∈ graph.successfulExits ∨
      ∃ target ∈ graph.successors.getD source [], ∃ nextRank,
        rankAt ranks target = some nextRank ∧ rank = nextRank + 1
  backward : ∀ source < graph.size, ∀ target ∈ graph.successors.getD source [],
    ∀ nextRank, rankAt ranks target = some nextRank →
      ∃ rank, rankAt ranks source = some rank ∧ rank ≤ nextRank + 1

private theorem rankFacts_of_checks {graph : ControlGraph} {ranks : Array (Option Nat)}
    (hchecks : successRankChecks graph ranks = true) : RankFacts graph ranks := by
  simp only [successRankChecks, Bool.and_eq_true, beq_iff_eq] at hchecks
  obtain ⟨⟨⟨hgraph, hsize⟩, hexits⟩, hnodes⟩ := hchecks
  simp only [ControlGraph.wellFormedB, Bool.and_eq_true, List.all_eq_true,
    Array.all_eq_true, decide_eq_true_eq] at hgraph
  simp only [List.all_eq_true, beq_iff_eq] at hexits
  simp only [List.all_eq_true, Bool.and_eq_true] at hnodes
  refine ⟨hsize, hexits, ?_, ?_, ?_⟩
  · intro source hsource target htarget
    have hsource' : source < graph.successors.size := hsource
    exact hgraph.2 source hsource' target (by simpa [Array.getD, hsource'] using htarget)
  · intro source hsource rank hrank
    have hnode := (hnodes source (List.mem_range.mpr hsource)).1
    simp only [hrank, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at hnode
    rcases hnode.2 with hexit | ⟨target, htarget, hnext⟩
    · exact Or.inl ((exitMask_true_iff graph hsource).mp hexit)
    · right
      split at hnext
      · cases hnext
      · rename_i nextRank hnextRank
        exact ⟨target, htarget, nextRank, hnextRank, by simpa using hnext⟩
  · intro source hsource target htarget nextRank hnextRank
    have hedge := (hnodes source (List.mem_range.mpr hsource)).2 target htarget
    simp only [hnextRank] at hedge
    split at hedge
    · cases hedge
    · rename_i rank hrank
      exact ⟨rank, hrank, of_decide_eq_true hedge⟩

private theorem rank_has_exact_successful_path {graph : ControlGraph}
    {ranks : Array (Option Nat)} (hfacts : RankFacts graph ranks) {source rank : Nat}
    (hsource : source < graph.size) (hrank : rankAt ranks source = some rank) :
    ∃ trace, SuccessfulPath graph source trace ∧ trace.length = rank + 1 := by
  induction rank using Nat.strongRecOn generalizing source with
  | ind rank ih =>
    rcases hfacts.justified source hsource rank hrank with hexit | hnext
    · have hzero : rank = 0 := Option.some.inj (hrank.symm.trans (hfacts.exitRank source hexit))
      exact ⟨[source], ⟨source, hexit, .single source⟩, by simp [hzero]⟩
    · obtain ⟨target, hedge, nextRank, hnextRank, hrankEq⟩ := hnext
      obtain ⟨tail, ⟨exit, hexit, hpath⟩, hlength⟩ :=
        ih nextRank (by omega) (hfacts.edgeBound source hsource target hedge) hnextRank
      exact ⟨source :: tail, ⟨exit, hexit, .next hsource hedge hpath⟩, by simp [hlength, hrankEq]⟩

private theorem successful_path_bounds_rank {graph : ControlGraph}
    {ranks : Array (Option Nat)} (hfacts : RankFacts graph ranks)
    {source exit : Nat} {trace : List Nat} (hpath : ControlPath graph source exit trace)
    (hexit : exit ∈ graph.successfulExits) :
    ∃ rank, rankAt ranks source = some rank ∧ rank + 1 ≤ trace.length := by
  induction hpath with
  | single node => exact ⟨0, hfacts.exitRank node hexit, by simp⟩
  | @next source target exit tail hbound hedge _ ih =>
    obtain ⟨nextRank, hnextRank, hlength⟩ := ih hexit
    obtain ⟨rank, hrank, hrankBound⟩ := hfacts.backward source hbound target hedge nextRank hnextRank
    exact ⟨rank, hrank, by simp only [List.length_cons]; omega⟩

/-- Every returned BFS live bit is witnessed, and every finite successful path is covered,
    independently of whether continuation-parent construction subsequently succeeds. -/
theorem successRanks_live_iff_successful_path {graph : ControlGraph}
    {ranks : Array (Option Nat)} (h : successRanks? graph = some ranks)
    {source : Nat} (hsource : source < graph.size) :
    (rankAt ranks source).isSome = true ↔ ∃ trace, SuccessfulPath graph source trace := by
  have hfacts := rankFacts_of_checks (successRanks_checked h)
  constructor
  · intro hlive
    cases hrank : rankAt ranks source with
    | none => simp [hrank] at hlive
    | some rank =>
      obtain ⟨trace, hpath, _⟩ := rank_has_exact_successful_path hfacts hsource hrank
      exact ⟨trace, hpath⟩
  · rintro ⟨trace, exit, hexit, hpath⟩
    obtain ⟨rank, hrank, _⟩ := successful_path_bounds_rank hfacts hpath hexit
    simp [hrank]

/-- Returned ranks are exact shortest successful path lengths, counted in graph edges. Neither
    a rank heuristic nor a possibly incomplete continuation tree is assumed in this statement. -/
theorem successRanks_exact_shortest_distance {graph : ControlGraph}
    {ranks : Array (Option Nat)} (h : successRanks? graph = some ranks)
    {source rank : Nat} (hsource : source < graph.size) (hrank : rankAt ranks source = some rank) :
    (∃ trace, SuccessfulPath graph source trace ∧ trace.length = rank + 1) ∧
      ∀ trace, SuccessfulPath graph source trace → rank + 1 ≤ trace.length := by
  have hfacts := rankFacts_of_checks (successRanks_checked h)
  refine ⟨rank_has_exact_successful_path hfacts hsource hrank, ?_⟩
  rintro trace ⟨exit, hexit, hpath⟩
  obtain ⟨other, hother, hbound⟩ := successful_path_bounds_rank hfacts hpath hexit
  have heq : other = rank := Option.some.inj (hother.symm.trans hrank)
  simpa [heq] using hbound

theorem constructed_index_checked {p : Semantic.SemanticProgram} {result : ConstructedRegions}
    (h : constructRegions? p = some result) :
    escapeIndexChecks (decodedControlGraph p) result.index = true := by
  unfold constructRegions? at h
  simp only [bind] at h
  split at h
  · cases h
  · rw [Option.bind_eq_some_iff] at h
    obtain ⟨ranks, _, h⟩ := h
    split at h
    · cases h
      assumption
    · split at h
      · cases h
        assumption
      · cases h

theorem constructed_live_iff_successful_path {p : Semantic.SemanticProgram}
    {result : ConstructedRegions} (h : constructRegions? p = some result)
    {source : Nat} (hsource : source < (decodedControlGraph p).size) :
    result.index.liveB source = true ↔
      ∃ trace, SuccessfulPath (decodedControlGraph p) source trace :=
  checked_live_iff_successful_path (constructed_index_checked h) hsource

theorem constructed_continuation_cannot_be_escaped {p : Semantic.SemanticProgram}
    {result : ConstructedRegions} (h : constructRegions? p = some result)
    {candidate source : Nat} (hancestor : ancestorB result.index candidate source = true)
    {trace : List Nat} (havoid : candidate ∉ trace) :
    ¬ SuccessfulPath (decodedControlGraph p) source trace :=
  checked_continuation_cannot_be_escaped (constructed_index_checked h) hancestor havoid

private def generatedGraph (bits : Nat) : ControlGraph :=
  ⟨#[(List.range 3).filter (fun target => bits.testBit target),
      (List.range 3).filter (fun target => bits.testBit (3 + target)), []], [2]⟩

private def ranksMatchReference (graph : ControlGraph) (ranks : Array (Option Nat)) : Bool :=
  let reference : OccurrenceReference.Graph :=
    ⟨graph.successors, graph.successfulExits, Array.replicate graph.size .pub⟩
  ranks.size == graph.size && (List.range graph.size).all (fun source =>
    (rankAt ranks source).isSome == OccurrenceReference.canSucceed reference none source)

/-- All 64 three-vertex graphs with the designated exit having no outgoing edge. The two other
    vertices independently choose every subset of three targets, including self/mutual cycles.
    Construction failure is a test failure, so an always-refusing solver cannot pass this oracle.
-/
theorem generated_three_vertex_success_parity :
    (List.range 64).all (fun bits =>
      match successRanks? (generatedGraph bits) with
      | none => false
      | some ranks => ranksMatchReference (generatedGraph bits) ranks) = true := by
  decide +kernel

theorem generated_chain_has_exact_bfs_distances :
    successRanks? (generatedGraph 34) = some #[some 2, some 1, some 0] := by decide +kernel

/-- The comparator detects a dropped live node; the executable rank postcheck independently
    refuses the same planted fault instead of converting that node into a dead branch. -/
theorem missing_live_rank_mutant_detected :
    ranksMatchReference (generatedGraph 34) #[none, some 1, some 0] = false ∧
    successRankChecks (generatedGraph 34) #[none, some 1, some 0] = false := by decide +kernel

theorem duplicated_edges_enqueue_each_vertex_once :
    let graph : ControlGraph := ⟨#[[1, 1, 1, 1], [2, 2], []], [2, 2]⟩
    successRanks? graph = some #[some 2, some 1, some 0] ∧
      (computeSuccessQueue graph).tail = 3 ∧ (computeSuccessQueue graph).queue.size = 3 := by
  decide +kernel

private def returnInstruction (op : SemanticInstrOp) (id target alternate merge : UInt32) :
    Semantic.Instruction :=
  { op, id, functionId := 1, blockId := 1, destination := 0, firstOperand := 0,
    operandCount := 0, target, alternate, merge, resultLabel := .pub, aux := 0 }

private def invalidMergeProgram : Semantic.SemanticProgram :=
  { functions := #[{ id := 1, entry := 1, firstInstruction := 0, instructionCount := 3 }]
    instructions := #[returnInstruction .branch 1 1 2 1,
      returnInstruction .output 2 0 0 0, returnInstruction .output 3 0 0 0]
    operands := #[], valueLabels := #[] }

/-- An invented branch merge is not trusted: construction reports its conservative fallback,
    whose only shared continuation is the synthetic function return. This is CFG evidence only.
-/
theorem invalid_merge_uses_checked_function_return_fallback :
    (constructRegions? invalidMergeProgram).map
      (fun result => (result.index.parent, result.index.successRank, result.conservativeFallback)) =
      some (#[3, 3, 3, 3], #[some 2, some 1, some 1, some 0], true) := by decide +kernel

private def loopProgram : Semantic.SemanticProgram :=
  { functions := #[{ id := 1, entry := 1, firstInstruction := 0, instructionCount := 3 }]
    instructions := #[returnInstruction .loop 1 1 2 2,
      returnInstruction .jump 2 0 0 0, returnInstruction .output 3 0 0 0]
    operands := #[], valueLabels := #[] }

/-- The normal loop retains its checked exit continuation without taking the coarse fallback. -/
theorem loop_candidate_preserves_its_real_continuation :
    (constructRegions? loopProgram).map
      (fun result => (result.index.parent, result.index.successRank, result.conservativeFallback)) =
      some (#[2, 0, 3, 3], #[some 2, some 3, some 1, some 0], false) := by decide +kernel

end LambdaSigil.Combined.OccurrenceRegionConstructionSecurity
