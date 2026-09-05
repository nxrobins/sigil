import LambdaSigil.AncestorIntervals
import LambdaSigil.OccurrenceRegionSecurity

/-!
# Parent-chain meaning of checked Euler intervals

Returned interval queries agree with the existing live-node parent-chain relation. The proof
uses checked contiguous child partitions and inverse preorder slots, not a trusted DFS theorem,
an assumed region certificate, or a supplied all-pairs ancestry table. Existing successful-path
postdominance can therefore consume this index without repeating parent walks.
-/

namespace LambdaSigil.Combined.AncestorIntervalSecurity

open OccurrenceRegions OccurrenceRegionSecurity AncestorIntervals

private theorem partition_lower {index : IntervalIndex} {nodes : List Nat} {start stop : Nat}
    (h : partition? index nodes start = some stop) : start ≤ stop := by
  induction nodes generalizing start with
  | nil => simp only [partition?, Option.some.injEq] at h; omega
  | cons node nodes ih =>
    simp only [partition?] at h
    split at h
    · rename_i hnode
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hnode
      have := ih h
      omega
    · cases h

private theorem partition_member_bounds {index : IntervalIndex} {nodes : List Nat}
    {start stop node : Nat} (h : partition? index nodes start = some stop) (hmem : node ∈ nodes) :
    start ≤ index.start node ∧ index.stop node ≤ stop := by
  induction nodes generalizing start with
  | nil => simp at hmem
  | cons head nodes ih =>
    simp only [partition?] at h
    split at h
    · rename_i hhead
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hhead
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨by omega, partition_lower h⟩
      · obtain ⟨hlower, hupper⟩ := ih h hmem
        exact ⟨by omega, hupper⟩
    · cases h

private theorem partition_covers {index : IntervalIndex} {nodes : List Nat}
    {start stop point : Nat} (h : partition? index nodes start = some stop)
    (hlower : start ≤ point) (hupper : point < stop) :
    ∃ child ∈ nodes, index.start child ≤ point ∧ point < index.stop child := by
  induction nodes generalizing start with
  | nil => simp only [partition?, Option.some.injEq] at h; omega
  | cons head nodes ih =>
    simp only [partition?] at h
    split at h
    · rename_i hhead
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hhead
      by_cases hins : point < index.stop head
      · exact ⟨head, by simp, by omega, hins⟩
      · obtain ⟨child, hmem, hchild⟩ := ih h (by omega)
        exact ⟨child, List.mem_cons_of_mem _ hmem, hchild⟩
    · cases h

private structure IntervalFacts (forest : EscapeIndex) (index : IntervalIndex)
    (children : Array (List Nat)) : Prop where
  capacity : index.count ≤ forest.parent.size
  parentBound : ∀ node < forest.parent.size, forest.parentAt node < forest.parent.size
  positive : ∀ node < forest.parent.size, forest.liveB node = true →
    index.start node < index.stop node
  stopBound : ∀ node < forest.parent.size, forest.liveB node = true →
    index.stop node ≤ index.count
  inverse : ∀ node < forest.parent.size, forest.liveB node = true →
    index.order.getD (index.start node) forest.parent.size = node
  parent : ∀ node < forest.parent.size, forest.liveB node = true →
    forest.parentAt node = node ∨
      (forest.liveB (forest.parentAt node) = true ∧
        index.start (forest.parentAt node) < index.start node ∧
        index.stop node ≤ index.stop (forest.parentAt node))
  childParent : ∀ node < forest.parent.size, forest.liveB node = true →
    ∀ child ∈ children.getD node [], child < forest.parent.size ∧
      forest.liveB child = true ∧ forest.parentAt child = node
  partition : ∀ node < forest.parent.size, forest.liveB node = true →
    partition? index (children.getD node []) (index.start node + 1) = some (index.stop node)

private theorem facts_of_checks {forest : EscapeIndex} {roots : List Nat}
    {children : Array (List Nat)} {index : IntervalIndex}
    (hchecks : intervalChecks forest roots children index = true) :
    IntervalFacts forest index children := by
  simp only [intervalChecks, Bool.and_eq_true, List.all_eq_true] at hchecks
  have hnodes := hchecks.2
  have hnode : ∀ node < forest.parent.size,
      liveNodeChecks forest index children (rootMask forest.parent.size roots) node = true := by
    intro node hbound
    exact hnodes node (List.mem_range.mpr hbound)
  have hlive : ∀ node < forest.parent.size, forest.liveB node = true →
      index.start node < index.stop node ∧ index.stop node ≤ index.count ∧
      index.order.getD (index.start node) forest.parent.size = node ∧
      (if forest.parentAt node = node then (rootMask forest.parent.size roots).getD node false
       else !(rootMask forest.parent.size roots).getD node false &&
         forest.liveB (forest.parentAt node) &&
         index.start (forest.parentAt node) < index.start node &&
         index.stop node ≤ index.stop (forest.parentAt node)) = true ∧
      (∀ child ∈ children.getD node [], child < forest.parent.size ∧
        forest.liveB child = true ∧ forest.parentAt child = node) ∧
      partition? index (children.getD node []) (index.start node + 1) = some (index.stop node) := by
    intro node hbound hlive
    have h := hnode node hbound
    simp only [liveNodeChecks, hlive, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨h.2.1.1.1.1.1, h.2.1.1.1.1.2, h.2.1.1.1.2, h.2.1.1.2,
      fun child hmem => ⟨(h.2.1.2 child hmem).1.1,
        (h.2.1.2 child hmem).1.2, (h.2.1.2 child hmem).2⟩, h.2.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact of_decide_eq_true hchecks.1.1.1.2
  · intro node hbound
    have h := hnode node hbound
    simp only [liveNodeChecks, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  · intro node hbound h
    exact (hlive node hbound h).1
  · intro node hbound h
    exact (hlive node hbound h).2.1
  · intro node hbound h
    exact (hlive node hbound h).2.2.1
  · intro node hbound h
    have hp := (hlive node hbound h).2.2.2.1
    split at hp
    · exact Or.inl ‹forest.parentAt node = node›
    · right
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      exact ⟨hp.1.1.2, hp.1.2, hp.2⟩
  · intro node hbound h
    exact (hlive node hbound h).2.2.2.2.1
  · intro node hbound h
    exact (hlive node hbound h).2.2.2.2.2

private theorem contains_implies_ancestor {forest : EscapeIndex} {index : IntervalIndex}
    {children : Array (List Nat)} (facts : IntervalFacts forest index children)
    {candidate node : Nat} (hc : candidate < forest.parent.size)
    (hn : node < forest.parent.size) (hlc : forest.liveB candidate = true)
    (hln : forest.liveB node = true) (hlower : index.start candidate ≤ index.start node)
    (hupper : index.start node < index.stop candidate) : Ancestor forest candidate node := by
  generalize hwidth : index.stop candidate - index.start candidate = width
  induction width using Nat.strongRecOn generalizing candidate with
  | ind width ih =>
    by_cases heq : index.start candidate = index.start node
    · have hsame : candidate = node :=
        (facts.inverse candidate hc hlc).symm.trans (heq ▸ facts.inverse node hn hln)
      subst candidate
      exact ⟨0, rfl⟩
    · obtain ⟨child, hmem, hchildLower, hchildUpper⟩ :=
        partition_covers (facts.partition candidate hc hlc) (by omega) hupper
      obtain ⟨hchildBound, hchildLive, hparent⟩ := facts.childParent candidate hc hlc child hmem
      obtain ⟨hentry, hexit⟩ :=
        partition_member_bounds (facts.partition candidate hc hlc) hmem
      have hchildAncestor := ih (index.stop child - index.start child) (by omega)
        hchildBound hchildLive hchildLower hchildUpper rfl
      exact (show Ancestor forest candidate child from ⟨1, by simpa [parentIter] using hparent⟩).trans
        hchildAncestor

private theorem iterate_preserves_interval {forest : EscapeIndex} {index : IntervalIndex}
    {children : Array (List Nat)} (facts : IntervalFacts forest index children)
    (steps : Nat) {node : Nat} (hn : node < forest.parent.size)
    (hln : forest.liveB node = true) :
    let ancestor := parentIter forest steps node
    ancestor < forest.parent.size ∧ forest.liveB ancestor = true ∧
      index.start ancestor ≤ index.start node ∧ index.stop node ≤ index.stop ancestor := by
  induction steps generalizing node with
  | zero => exact ⟨hn, hln, Nat.le_refl _, Nat.le_refl _⟩
  | succ steps ih =>
    dsimp only [parentIter]
    rcases facts.parent node hn hln with hfixed | ⟨hparentLive, hentry, hexit⟩
    · simpa [parentIter, hfixed] using ih hn hln
    · obtain ⟨hbound, hlive, hlower, hupper⟩ := ih (facts.parentBound node hn) hparentLive
      exact ⟨hbound, hlive, by omega, by omega⟩

/-- Constant-time interval containment has exactly the existing live parent-chain meaning.
    No trusted constructor or graph postdominance fact is a premise. -/
theorem checked_query_iff_ancestor {forest : EscapeIndex} {roots : List Nat}
    {children : Array (List Nat)} {index : IntervalIndex}
    (hchecks : intervalChecks forest roots children index = true)
    {candidate node : Nat} (hc : candidate < forest.parent.size)
    (hn : node < forest.parent.size) (hlc : forest.liveB candidate = true)
    (hln : forest.liveB node = true) :
    AncestorIntervals.ancestorB forest index candidate node = true ↔
      Ancestor forest candidate node := by
  have facts := facts_of_checks hchecks
  simp only [AncestorIntervals.ancestorB, hc, hn, hlc, hln, decide_true, Bool.true_and,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hlower, hupper⟩
    exact contains_implies_ancestor facts hc hn hlc hln hlower hupper
  · rintro ⟨steps, hsteps⟩
    have h := iterate_preserves_interval facts steps hn hln
    rw [hsteps] at h
    exact ⟨h.2.2.1, by have := facts.positive node hn hln; omega⟩

theorem constructed_intervals_checked {forest : EscapeIndex} {roots : List Nat}
    {index : IntervalIndex} (h : construct? forest roots = some index) :
    intervalChecks forest roots (childLists forest) index = true := by
  unfold construct? at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
        assumption
      · cases h

theorem constructed_query_iff_ancestor {forest : EscapeIndex} {roots : List Nat}
    {index : IntervalIndex} (h : construct? forest roots = some index)
    {candidate node : Nat} (hc : candidate < forest.parent.size)
    (hn : node < forest.parent.size) (hlc : forest.liveB candidate = true)
    (hln : forest.liveB node = true) :
    AncestorIntervals.ancestorB forest index candidate node = true ↔
      Ancestor forest candidate node :=
  checked_query_iff_ancestor (constructed_intervals_checked h) hc hn hlc hln

private theorem ancestor_within_entry_bound {forest : EscapeIndex} {index : IntervalIndex}
    {children : Array (List Nat)} (facts : IntervalFacts forest index children)
    {candidate : Nat} (fuel : Nat) {node : Nat} (hn : node < forest.parent.size)
    (hln : forest.liveB node = true) (hentry : index.start node ≤ fuel)
    (hancestor : Ancestor forest candidate node) :
    ancestorWithin forest candidate fuel node = true := by
  induction fuel generalizing node with
  | zero =>
    have heq : candidate = node := by
      rcases facts.parent node hn hln with hfixed | ⟨_, hdecrease, _⟩
      · exact hancestor.fixed hfixed
      · omega
    simp [ancestorWithin, heq]
  | succ fuel ih =>
    by_cases heq : candidate = node
    · simp [ancestorWithin, heq]
    · rcases facts.parent node hn hln with hfixed | ⟨hparentLive, hdecrease, _⟩
      · exact False.elim (heq (hancestor.fixed hfixed))
      · have hnext := ih (facts.parentBound node hn) hparentLive (by omega) (hancestor.of_ne heq)
        simp [ancestorWithin, hnext]

/-- The bounded historical parent walk and the new constant-time query have the same verdict
    on live in-bounds nodes. The entry bound supplies finite walk fuel; no unbounded search is
    added to the executable interval checker. -/
theorem checked_query_eq_parent_walk {forest : EscapeIndex} {roots : List Nat}
    {children : Array (List Nat)} {index : IntervalIndex}
    (hchecks : intervalChecks forest roots children index = true)
    {candidate node : Nat} (hc : candidate < forest.parent.size)
    (hn : node < forest.parent.size) (hlc : forest.liveB candidate = true)
    (hln : forest.liveB node = true) :
    AncestorIntervals.ancestorB forest index candidate node =
      OccurrenceRegions.ancestorB forest candidate node := by
  apply Bool.eq_iff_iff.mpr
  rw [checked_query_iff_ancestor hchecks hc hn hlc hln]
  constructor
  · intro hancestor
    have facts := facts_of_checks hchecks
    apply ancestor_within_entry_bound facts forest.parent.size hn hln
    · have := facts.positive node hn hln
      have := facts.stopBound node hn hln
      have := facts.capacity
      omega
    · exact hancestor
  · exact OccurrenceRegionSecurity.ancestorB_sound

theorem checked_edge_query_eq_parent_walk {forest : EscapeIndex} {roots : List Nat}
    {children : Array (List Nat)} {index : IntervalIndex}
    (hchecks : intervalChecks forest roots children index = true) {source target : Nat}
    (hsource : source < forest.parent.size) (htarget : target < forest.parent.size) :
    AncestorIntervals.edgeParentB forest index source target =
      OccurrenceRegions.edgeParentB forest source target := by
  by_cases hliveTarget : forest.liveB target = true
  · by_cases hliveSource : forest.liveB source = true
    · have facts := facts_of_checks hchecks
      have hparentLive : forest.liveB (forest.parentAt source) = true := by
        rcases facts.parent source hsource hliveSource with hfixed | hparent
        · simpa [hfixed] using hliveSource
        · exact hparent.1
      have heq := checked_query_eq_parent_walk hchecks (facts.parentBound source hsource)
        htarget hparentLive hliveTarget
      simpa only [AncestorIntervals.edgeParentB, OccurrenceRegions.edgeParentB,
        hliveTarget, hliveSource, Bool.not_true, Bool.true_and, Bool.false_or] using heq
    · simp [AncestorIntervals.edgeParentB, OccurrenceRegions.edgeParentB, hliveSource]
  · simp [AncestorIntervals.edgeParentB, OccurrenceRegions.edgeParentB, hliveTarget]

/-- Existing successful-path postdominance consumes a checked interval query directly. This
    says nothing about complete occurrence classification or balanced interprocedural runs. -/
theorem constructed_query_forces_successful_hit {graph : ControlGraph} {forest : EscapeIndex}
    {roots : List Nat} {index : IntervalIndex} (h : construct? forest roots = some index)
    (hforest : escapeIndexChecks graph forest = true) {candidate node : Nat}
    (hc : candidate < forest.parent.size) (hn : node < forest.parent.size)
    (hlc : forest.liveB candidate = true) (hln : forest.liveB node = true)
    (hquery : AncestorIntervals.ancestorB forest index candidate node = true)
    {trace : List Nat} (hpath : SuccessfulPath graph node trace) : candidate ∈ trace := by
  have heq := checked_query_eq_parent_walk (constructed_intervals_checked h) hc hn hlc hln
  exact checked_ancestor_forces_successful_hit hforest (heq ▸ hquery) hpath

theorem constructed_table_capacity {forest : EscapeIndex} {roots : List Nat}
    {index : IntervalIndex} (h : construct? forest roots = some index) :
    index.enter.size = forest.parent.size ∧ index.leave.size = forest.parent.size ∧
      index.order.size = forest.parent.size ∧ index.count ≤ forest.parent.size := by
  have hchecks := constructed_intervals_checked h
  simp only [intervalChecks, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchecks
  exact ⟨hchecks.1.1.1.1.1.1.2, hchecks.1.1.1.1.1.2, hchecks.1.1.1.1.2,
    hchecks.1.1.1.2⟩

theorem constructed_roots_are_live_fixed_points {forest : EscapeIndex} {roots : List Nat}
    {index : IntervalIndex} (h : construct? forest roots = some index) :
    ∀ root ∈ roots, root < forest.parent.size ∧ forest.liveB root = true ∧
      forest.parentAt root = root := by
  have hchecks := constructed_intervals_checked h
  simp only [intervalChecks, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hchecks
  intro root hroot
  have hr := hchecks.1.1.2 root hroot
  exact ⟨hr.1.1, hr.1.2, hr.2⟩

/-- A returned live forest cannot contain a nontrivial parent cycle. This follows from strict
    checked preorder descent, independently of whether the traversal noticed a repeated visit. -/
theorem checked_parent_cycle_is_fixed {forest : EscapeIndex} {roots : List Nat}
    {children : Array (List Nat)} {index : IntervalIndex}
    (hchecks : intervalChecks forest roots children index = true) {node : Nat}
    (hn : node < forest.parent.size) (hln : forest.liveB node = true) (steps : Nat)
    (hcycle : parentIter forest (steps + 1) node = node) : forest.parentAt node = node := by
  have facts := facts_of_checks hchecks
  rcases facts.parent node hn hln with hfixed | ⟨hparentLive, hdecrease, _⟩
  · exact hfixed
  · have h := iterate_preserves_interval facts steps (facts.parentBound node hn) hparentLive
    change parentIter forest steps (forest.parentAt node) = node at hcycle
    rw [hcycle] at h
    have := h.2.2.1
    omega

def TraversalShape (size : Nat) (state : Traversal) : Prop :=
  state.intervals.enter.size = size ∧ state.intervals.leave.size = size ∧
    state.intervals.order.size = size ∧ state.seen.size = size ∧ state.intervals.count ≤ size

theorem traverse_preserves_table_shape {forest : EscapeIndex} {children : Array (List Nat)}
    {state : Traversal} (hshape : TraversalShape forest.parent.size state) (fuel : Nat) :
    TraversalShape forest.parent.size (traverse forest children fuel state) := by
  induction fuel generalizing state with
  | zero => exact hshape
  | succ fuel ih =>
    unfold traverse
    split
    · exact hshape
    · split
      · exact hshape
      · split
        · exact hshape
        · apply ih
          rcases hshape with ⟨henter, hleave, horder, hseen, hcount⟩
          simp only [TraversalShape, Array.size_setIfInBounds]
          refine ⟨henter, hleave, horder, hseen, ?_⟩
          rename_i hactive
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hactive
          omega
      · split
        · exact hshape
        · apply ih
          simpa only [TraversalShape, Array.size_setIfInBounds] using hshape

theorem constructed_traversal_uses_fixed_tables (forest : EscapeIndex) (roots : List Nat) :
    TraversalShape forest.parent.size
      (traverse forest (childLists forest) (2 * forest.parent.size)
        (initialTraversal forest.parent.size roots)) := by
  apply traverse_preserves_table_shape
  simp [TraversalShape, initialTraversal]

theorem child_adjacency_has_one_slot_per_vertex (forest : EscapeIndex) :
    (childLists forest).size = forest.parent.size := by
  unfold childLists
  apply List.foldlRecOn (motive := fun children : Array (List Nat) =>
    children.size = forest.parent.size)
  · simp
  · intro children hsize node _
    split <;> simpa using hsize

end LambdaSigil.Combined.AncestorIntervalSecurity
