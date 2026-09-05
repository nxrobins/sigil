import LambdaSigil.IntervalEscapeChecks
import LambdaSigil.AncestorIntervalSecurity

/-!
# Historical escape obligations from shared interval checks

The cached exit mask has exact bounded membership meaning, and checked interval edges have the
historical parent-walk verdict. Their composition discharges the old checker without executing
it in the new kernel entry point. This is conditional soundness, not a constructor-totality,
production-performance, or Public noninterference theorem.
-/

namespace LambdaSigil.Combined.IntervalEscapeSecurity

open OccurrenceRegions AncestorIntervals AncestorIntervalSecurity IntervalEscapeChecks

private theorem mask_fold_lookup (roots : List Nat) (mask : Array Bool) (node : Nat)
    (hnode : node < mask.size) :
    (roots.foldl (fun result root => result.setIfInBounds root true) mask).getD node false =
      (mask.getD node false || roots.contains node) := by
  induction roots generalizing mask with
  | nil => simp
  | cons root roots ih =>
    rw [List.foldl_cons, ih (mask.setIfInBounds root true) (by simpa using hnode)]
    have hget := Array.getElem_setIfInBounds (xs := mask) (i := root) (a := true)
      (j := node) hnode
    by_cases heq : root = node
    · simp [Array.getD, hnode, heq]
    · simp [Array.getD, hnode, hget, heq, Ne.symm heq]

theorem cached_exit_mask_eq_contains (size : Nat) (roots : List Nat) (node : Nat)
    (hnode : node < size) :
    (rootMask size roots).getD node false = roots.contains node := by
  simpa [rootMask, Array.getD, hnode] using
    mask_fold_lookup roots (Array.replicate size false) node (by simpa using hnode)

private theorem masked_node_checks_eq_old (graph : ControlGraph) (forest : EscapeIndex)
    (node : Nat) (hnode : node < graph.size) :
    successJustifiedWithMaskB graph forest (rootMask graph.size graph.successfulExits) node =
      successJustifiedB graph forest node ∧
    parentRankedWithMaskB graph forest (rootMask graph.size graph.successfulExits) node =
      parentRankedB graph forest node := by
  simp only [successJustifiedWithMaskB, successJustifiedB, parentRankedWithMaskB,
    parentRankedB, cached_exit_mask_eq_contains graph.size graph.successfulExits node hnode]
  cases forest.rankAt node <;> simp

private theorem all_congr_mem {α : Type} {nodes : List α} {left right : α → Bool}
    (h : ∀ node ∈ nodes, left node = right node) : nodes.all left = nodes.all right := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
    simp only [List.all_cons, h node (by simp)]
    rw [ih (fun next hnext => h next (by simp [hnext]))]

private theorem live_interval_node {forest : EscapeIndex} {roots : List Nat}
    {children : Array (List Nat)} {intervals : IntervalIndex}
    (hchecks : intervalChecks forest roots children intervals = true) {node : Nat}
    (hnode : node < forest.parent.size) (hlive : forest.liveB node = true) :
    forest.parentAt node < forest.parent.size ∧
      intervals.start node < intervals.stop node ∧ intervals.stop node ≤ intervals.count ∧
      (forest.parentAt node = node ∨
        (forest.liveB (forest.parentAt node) = true ∧
          intervals.start (forest.parentAt node) < intervals.start node)) := by
  simp only [intervalChecks, Bool.and_eq_true, List.all_eq_true] at hchecks
  have h := hchecks.2 node (List.mem_range.mpr hnode)
  simp only [liveNodeChecks, hlive, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  refine ⟨h.1, h.2.1.1.1.1.1, h.2.1.1.1.1.2, ?_⟩
  have hp := h.2.1.1.2
  split at hp
  · exact Or.inl ‹forest.parentAt node = node›
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact Or.inr ⟨hp.1.1.2, hp.1.2⟩

/-- Explicit Nat equality avoids importing generic order-law equality instances into this
    bounded-walk bridge. The executable checker itself still performs only interval queries. -/
private theorem ancestor_within_entry {forest : EscapeIndex} {roots : List Nat}
    {children : Array (List Nat)} {intervals : IntervalIndex}
    (hchecks : intervalChecks forest roots children intervals = true)
    {candidate : Nat} (fuel : Nat) {node : Nat} (hnode : node < forest.parent.size)
    (hlive : forest.liveB node = true) (hentry : intervals.start node ≤ fuel)
    (hancestor : OccurrenceRegionSecurity.Ancestor forest candidate node) :
    ancestorWithin forest candidate fuel node = true := by
  induction fuel generalizing node with
  | zero =>
    have heq : candidate = node := by
      rcases (live_interval_node hchecks hnode hlive).2.2.2 with hfixed | hparent
      · exact hancestor.fixed hfixed
      · have hdecrease := hparent.2
        omega
    subst candidate
    change decide (node = node) = true
    exact decide_eq_true rfl
  | succ fuel ih =>
    by_cases heq : candidate = node
    · subst candidate
      change (node == node || ancestorWithin forest node fuel (forest.parentAt node)) = true
      have hself : (node == node) = true := by
        change decide (node = node) = true
        exact decide_eq_true rfl
      rw [hself, Bool.true_or]
    · have hfacts := live_interval_node hchecks hnode hlive
      rcases hfacts.2.2.2 with hfixed | ⟨hparentLive, hdecrease⟩
      · exact False.elim (heq (hancestor.fixed hfixed))
      · have hnext := ih hfacts.1 hparentLive (by omega) (hancestor.of_ne heq)
        change (candidate == node || ancestorWithin forest candidate fuel
          (forest.parentAt node)) = true
        rw [hnext, Bool.or_true]

private theorem interval_query_eq_walk {forest : EscapeIndex} {roots : List Nat}
    {children : Array (List Nat)} {intervals : IntervalIndex}
    (hchecks : intervalChecks forest roots children intervals = true)
    {candidate node : Nat} (hc : candidate < forest.parent.size)
    (hn : node < forest.parent.size) (hlc : forest.liveB candidate = true)
    (hln : forest.liveB node = true) :
    AncestorIntervals.ancestorB forest intervals candidate node =
      OccurrenceRegions.ancestorB forest candidate node := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hquery
    have hancestor := (checked_query_iff_ancestor hchecks hc hn hlc hln).mp hquery
    have hfacts := live_interval_node hchecks hn hln
    have hcapacity : intervals.count ≤ forest.parent.size := by
      simp only [intervalChecks, Bool.and_eq_true, decide_eq_true_eq] at hchecks
      exact hchecks.1.1.1.2
    exact ancestor_within_entry hchecks forest.parent.size hn hln (by omega) hancestor
  · intro hquery
    exact (checked_query_iff_ancestor hchecks hc hn hlc hln).mpr
      (OccurrenceRegionSecurity.ancestorB_sound hquery)

private theorem interval_edge_eq_walk {forest : EscapeIndex} {roots : List Nat}
    {children : Array (List Nat)} {intervals : IntervalIndex}
    (hchecks : intervalChecks forest roots children intervals = true) {source target : Nat}
    (hsource : source < forest.parent.size) (htarget : target < forest.parent.size) :
    AncestorIntervals.edgeParentB forest intervals source target =
      OccurrenceRegions.edgeParentB forest source target := by
  by_cases hliveTarget : forest.liveB target = true
  · by_cases hliveSource : forest.liveB source = true
    · have hfacts := live_interval_node hchecks hsource hliveSource
      have hparentLive : forest.liveB (forest.parentAt source) = true := by
        rcases hfacts.2.2.2 with hfixed | hparent
        · simpa only [hfixed] using hliveSource
        · exact hparent.1
      have heq := interval_query_eq_walk hchecks hfacts.1 htarget hparentLive hliveTarget
      simpa only [AncestorIntervals.edgeParentB, OccurrenceRegions.edgeParentB,
        hliveTarget, hliveSource, Bool.not_true, Bool.true_and, Bool.false_or] using heq
    · simp only [AncestorIntervals.edgeParentB, OccurrenceRegions.edgeParentB,
        Bool.not_eq_true] at hliveSource ⊢
      simp [hliveSource]
  · simp [AncestorIntervals.edgeParentB, OccurrenceRegions.edgeParentB, hliveTarget]

/-- Once intervals are independently checked, the local scan has exactly the historical
    verdict. The graph bounds are needed to apply the bounded interval-edge equivalence. -/
theorem interval_escape_checks_eq_old {graph : ControlGraph} {forest : EscapeIndex}
    {intervals : IntervalIndex}
    (hintervals : intervalChecks forest graph.successfulExits (childLists forest) intervals = true)
    (hgraph : graph.wellFormedB = true) (hsize : forest.parent.size = graph.size) :
    intervalEscapeChecks graph forest intervals = escapeIndexChecks graph forest := by
  have htargets : ∀ node < graph.size, ∀ target ∈ graph.successors.getD node [],
      target < graph.size := by
    simp only [ControlGraph.wellFormedB, Bool.and_eq_true] at hgraph
    intro node hnode target htarget
    have hrow := Array.all_eq_true.mp hgraph.2 node hnode
    have hnode' : node < graph.successors.size := hnode
    have hmem : target ∈ graph.successors[node] := by
      simpa [Array.getD, hnode'] using htarget
    exact of_decide_eq_true (List.all_eq_true.mp hrow target hmem)
  unfold intervalEscapeChecks escapeIndexChecks
  dsimp only
  congr 1
  apply all_congr_mem
  intro node hnode
  have hbound := List.mem_range.mp hnode
  obtain ⟨hmaskSuccess, hmaskParent⟩ := masked_node_checks_eq_old graph forest node hbound
  rw [hmaskSuccess, hmaskParent]
  congr 1
  apply all_congr_mem
  intro target htarget
  exact interval_edge_eq_walk hintervals (by simpa [hsize] using hbound)
    (by simpa [hsize] using htargets node hbound target htarget)

theorem returned_interval_checks {graph : ControlGraph} {forest : EscapeIndex}
    {intervals : IntervalIndex} (h : checkedIntervals? graph forest = some intervals) :
    intervalChecks forest graph.successfulExits (childLists forest) intervals = true ∧
      intervalEscapeChecks graph forest intervals = true := by
  unfold checkedIntervals? at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨constructed, hconstructed, h⟩ := h
  split at h
  · cases h
    exact ⟨constructed_intervals_checked hconstructed, by assumption⟩
  · cases h

theorem returned_implies_escape_index_checks {graph : ControlGraph} {forest : EscapeIndex}
    {intervals : IntervalIndex} (h : checkedIntervals? graph forest = some intervals) :
    escapeIndexChecks graph forest = true := by
  obtain ⟨hintervals, hlocal⟩ := returned_interval_checks h
  have hparts := hlocal
  simp only [intervalEscapeChecks, Bool.and_eq_true, beq_iff_eq] at hparts
  rw [interval_escape_checks_eq_old hintervals hparts.1.1.1.1 hparts.1.1.1.2] at hlocal
  exact hlocal

namespace IntervalEscapeWitnesses

private def diamond : ControlGraph := ⟨#[[1, 2], [3], [3], []], [3]⟩
private def diamondForest : EscapeIndex := ⟨#[3, 3, 3, 3], #[some 2, some 1, some 1, some 0]⟩

theorem interval_escape_accepts_checked_diamond :
    (checkedIntervals? diamond diamondForest).isSome = true ∧
      escapeIndexChecks diamond diamondForest = true := by decide +kernel

theorem interval_escape_rejects_unjustified_parent_and_missing_exit :
    (AncestorIntervals.construct? { diamondForest with parent := #[1, 3, 3, 3] }
      diamond.successfulExits).isSome = true ∧
    (checkedIntervals? diamond { diamondForest with parent := #[1, 3, 3, 3] }).isNone = true ∧
    (checkedIntervals? diamond { diamondForest with successRank :=
      #[some 2, some 1, some 1, none] }).isNone = true := by decide +kernel

end IntervalEscapeWitnesses

end LambdaSigil.Combined.IntervalEscapeSecurity
