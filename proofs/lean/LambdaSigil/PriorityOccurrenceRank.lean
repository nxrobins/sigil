import LambdaSigil.OccurrenceTransferSecurity

/-!
# Exact-stop invariants for rank-priority occurrence propagation

An exact seed stop remains a proper checked ancestor along every live prefix that avoids it.
Such an active stop already has rank no greater than the current controller's parent, so carrying
it subsumes the controller-parent seed without introducing a smaller priority. These local facts
use the checked forest and actual CFG edges; neither immediate-postdominator completeness nor
an assumed path-postdominance property is required.

The argument applies to exact received stops. Arbitrary rank-only replacements allowed by the
older frontier checker need not preserve ancestry. No priority-queue totality, minimality,
runtime bound, balanced invocation, or Public preservation is asserted here.
-/

namespace LambdaSigil.Combined.PriorityOccurrenceRank

open OccurrenceRegions OccurrenceRegionSecurity OccurrenceTransfer OccurrenceTransferSecurity

private theorem checked_parent_rank_or_fixed {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {source rank : Nat}
    (hsource : source < graph.size) (hrank : index.rankAt source = some rank) :
    index.parentAt source = source ∨
      ∃ parentRank, index.parentAt source < graph.size ∧
        index.rankAt (index.parentAt source) = some parentRank ∧ parentRank < rank := by
  simp only [escapeIndexChecks, Bool.and_eq_true] at hchecks
  have hparent := ((List.all_eq_true.mp hchecks.2) source (List.mem_range.mpr hsource))
  simp only [Bool.and_eq_true] at hparent
  have hranked := hparent.1.2
  simp only [parentRankedB, hrank, Bool.or_eq_true, List.contains_iff_mem,
    Bool.and_eq_true, decide_eq_true_eq] at hranked
  rcases hranked with hexit | ⟨hbound, hdecrease⟩
  · have hexitChecked := List.all_eq_true.mp hchecks.1.2 source hexit
    simp only [Bool.and_eq_true, beq_iff_eq] at hexitChecked
    exact Or.inl hexitChecked.1
  · right
    unfold rankDecreasesB at hdecrease
    split at hdecrease
    · cases hdecrease
    · rename_i parentRank hparentRank
      exact ⟨parentRank, hbound, hparentRank, of_decide_eq_true hdecrease⟩

/-- A proper exact stop already covers the controller-parent priority. A fixed root cannot
    carry a distinct ancestor; the nonroot case uses the same rank field as the queue ordering.
    No exact-tree or complete control-dependence premise is needed. -/
theorem exact_stop_subsumes_parent_seed {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {source stop : Nat}
    (hsource : source < graph.size) (hlive : index.liveB source = true)
    (hancestor : Ancestor index stop source) (hne : stop ≠ source) :
    stopRankLeB index stop (index.parentAt source) = true := by
  cases hrank : index.rankAt source with
  | none => simp [EscapeIndex.liveB, hrank] at hlive
  | some rank =>
    rcases checked_parent_rank_or_fixed hchecks hsource hrank with hfixed | hparent
    · exact False.elim (hne (hancestor.fixed hfixed))
    · obtain ⟨parentRank, hparentBound, hparentRank, _⟩ := hparent
      by_cases heq : stop = index.parentAt source
      · simp [stopRankLeB, heq, hparentRank]
      · obtain ⟨stopRank, hstopRank, hless⟩ := checked_ancestor_strict_rank hchecks
          hparentBound hparentRank (hancestor.of_ne hne) heq
        simp only [stopRankLeB, hstopRank, hparentRank, decide_eq_true_eq]
        omega

private theorem checked_live_edge {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {source target : Nat}
    (hsource : source < graph.size) (hedge : target ∈ graph.successors.getD source [])
    (hlive : index.liveB target = true) :
    index.liveB source = true ∧ Ancestor index (index.parentAt source) target := by
  simp only [escapeIndexChecks, Bool.and_eq_true] at hchecks
  have hnode := List.all_eq_true.mp hchecks.2 source (List.mem_range.mpr hsource)
  simp only [Bool.and_eq_true] at hnode
  have htarget := List.all_eq_true.mp hnode.2 target hedge
  simp only [edgeParentB, hlive, Bool.not_true, Bool.false_or, Bool.and_eq_true] at htarget
  exact ⟨htarget.1, ancestorB_sound htarget.2⟩

private theorem prefix_start_live {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {source target : Nat} {trace : List Nat}
    (hpath : ControlPath graph source target trace) (hlive : index.liveB target = true) :
    index.liveB source = true := by
  induction hpath with
  | single node => exact hlive
  | @next source middle target tail hsource hedge _ ih =>
    exact (checked_live_edge hchecks hsource hedge (ih hlive)).1

private theorem ancestor_through_avoiding_prefix {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {source target stop : Nat}
    {trace : List Nat} (hpath : ControlPath graph source target trace)
    (hlive : index.liveB target = true) (havoid : stop ∉ trace)
    (hancestor : Ancestor index stop source) :
    Ancestor index stop target ∧ stop ≠ target := by
  induction hpath with
  | single node => exact ⟨hancestor, by simpa using havoid⟩
  | @next source middle target tail hsource hedge hrest ih =>
    have hsourceNe : stop ≠ source := by
      intro heq
      exact havoid (by simp [heq])
    have htailAvoid : stop ∉ tail := by
      intro hmem
      exact havoid (List.mem_cons_of_mem source hmem)
    have hmiddleLive := prefix_start_live hchecks hrest hlive
    have hmiddleAncestor := (hancestor.of_ne hsourceNe).trans
      (checked_live_edge hchecks hsource hedge hmiddleLive).2
    exact ih hlive htailAvoid hmiddleAncestor

/-- Exact controller seeds have ancestry provenance at every live avoiding-prefix endpoint.
    The seed comes from a real outgoing edge; no synthetic per-region reachability relation or
    assumed successful-path theorem is used. Repeated vertices are retained by ControlPath. -/
theorem exact_seed_stays_proper_ancestor_on_live_prefix {graph : ControlGraph}
    {index : EscapeIndex} (hchecks : escapeIndexChecks graph index = true)
    {controller arm target : Nat} {trace : List Nat}
    (hcontroller : controller < graph.size)
    (hedge : arm ∈ graph.successors.getD controller [])
    (hpath : ControlPath graph arm target trace) (hlive : index.liveB target = true)
    (havoid : index.parentAt controller ∉ trace) :
    Ancestor index (index.parentAt controller) target ∧ index.parentAt controller ≠ target := by
  have harmLive := prefix_start_live hchecks hpath hlive
  exact ancestor_through_avoiding_prefix hchecks hpath hlive havoid
    (checked_live_edge hchecks hcontroller hedge harmLive).2

end LambdaSigil.Combined.PriorityOccurrenceRank
