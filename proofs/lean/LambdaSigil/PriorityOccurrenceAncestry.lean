import LambdaSigil.PriorityOccurrenceProvenance

/-!
# Checked ancestry of actually computed priority stops

The worklist's concrete seed/carry lineage, rather than an externally supplied path certificate,
establishes that each computed active stop is a proper checked ancestor. Its carry therefore
subsumes an occurrence-activated controller's parent seed even with an incomplete parent forest.
This is a provenance composition; minimality and successful-return completeness remain separate.
-/

namespace LambdaSigil.Combined.PriorityOccurrenceAncestry

open OccurrenceRegions OccurrenceRegionSecurity OccurrenceTransfer PriorityOccurrence
open PriorityOccurrenceProvenance PriorityOccurrenceRank

private theorem checked_edge_ancestor {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {source target : Nat}
    (hsource : source < graph.size) (hedge : target ∈ graph.successors.getD source [])
    (hlive : index.liveB target = true) : Ancestor index (index.parentAt source) target := by
  simp only [escapeIndexChecks, Bool.and_eq_true] at hchecks
  have hnode := List.all_eq_true.mp hchecks.2 source (List.mem_range.mpr hsource)
  simp only [Bool.and_eq_true] at hnode
  have htarget := List.all_eq_true.mp hnode.2 target hedge
  simp only [edgeParentB, hlive, Bool.not_true, Bool.false_or, Bool.and_eq_true] at htarget
  exact ancestorB_sound htarget.2

private theorem actual_origin_has_ancestor {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {threshold controller node : Nat}
    (hchecks : escapeIndexChecks graph index = true)
    (horigin : OfferReach graph index selectors threshold controller node)
    (hlive : index.liveB node = true) : Ancestor index (index.parentAt controller) node := by
  induction horigin with
  | seed hcontroller _ _ _ hedge => exact checked_edge_ancestor hchecks hcontroller hedge hlive
  | carry _ hsource hsourceLive hnotStop hedge ih =>
      exact ((ih hsourceLive).of_ne hnotStop.symm).trans
        (checked_edge_ancestor hchecks hsource hedge hlive)

theorem computed_stop_is_proper_checked_ancestor {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {threshold node stop : Nat}
    (hchecks : escapeIndexChecks graph index = true)
    (hstop : stopAt (compute graph index selectors threshold).frontier node = some stop) :
    Ancestor index stop node ∧ stop ≠ node ∧ index.liveB node = true := by
  obtain ⟨controller, horigin, hparent, hne, hlive⟩ :=
    compute_stored_stops_have_actual_origin graph index selectors threshold hstop
  exact ⟨hparent ▸ actual_origin_has_ancestor hchecks horigin hlive, hne.symm, hlive⟩

theorem computed_carry_subsumes_controller_parent_seed {graph : ControlGraph}
    {index : EscapeIndex} {selectors : Array Label} {threshold node stop : Nat}
    (hchecks : escapeIndexChecks graph index = true) (hnode : node < graph.size)
    (hstop : stopAt (compute graph index selectors threshold).frontier node = some stop) :
    stopRankLeB index stop (index.parentAt node) = true := by
  obtain ⟨hancestor, hne, hlive⟩ := computed_stop_is_proper_checked_ancestor hchecks hstop
  exact exact_stop_subsumes_parent_seed hchecks hnode hlive hancestor hne

end LambdaSigil.Combined.PriorityOccurrenceAncestry
