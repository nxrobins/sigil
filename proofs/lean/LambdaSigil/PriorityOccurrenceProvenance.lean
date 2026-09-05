import LambdaSigil.PriorityOccurrence
import LambdaSigil.PriorityOccurrenceRank

/-!
# Original-controller provenance through the actual priority worklist

Every offer starts at an actual private-selector edge or carries the same controller across an
actual CFG edge. A settled frontier entry retains that controller's exact parent and never
settles at its own stop. The invariant covers the real seed fold, bucket transfers, consumed
adjacency, and work transitions, including early failure and arbitrary fuel.

These are origin-preservation facts, not minimality, scheduling optimality, or production Public
noninterference. No alternative traversal supplies the returned frontier.
-/

namespace LambdaSigil.Combined.PriorityOccurrenceProvenance

open OccurrenceRegions OccurrenceRegionSecurity OccurrenceTransfer PriorityOccurrence

inductive OfferReach (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (threshold controller : Nat) : Nat → Prop
  | seed {node : Nat}
      (controllerBound : controller < graph.size)
      (controllerKind : isControllerB graph controller = true)
      (privateSelector : threshold ≤ (selectors.getD controller .pub).rank)
      (controllerLive : index.liveB controller = true)
      (edge : node ∈ graph.successors.getD controller []) :
      OfferReach graph index selectors threshold controller node
  | carry {source target : Nat}
      (previous : OfferReach graph index selectors threshold controller source)
      (sourceBound : source < graph.size)
      (sourceLive : index.liveB source = true)
      (notStopped : source ≠ index.parentAt controller)
      (edge : target ∈ graph.successors.getD source []) :
      OfferReach graph index selectors threshold controller target

private def RowsHold {α : Type} (rows : Array (List α)) (predicate : Nat → α → Prop) : Prop :=
  ∀ row, ∀ item ∈ rows.getD row [], predicate row item

private theorem rowsHold_set {α : Type} {rows : Array (List α)} {predicate : Nat → α → Prop}
    (hrows : RowsHold rows predicate) (position : Nat) (replacement : List α)
    (hreplacement : ∀ item ∈ replacement, predicate position item) :
    RowsHold (rows.setIfInBounds position replacement) predicate := by
  intro row item hitem
  by_cases hbound : row < rows.size
  · have hget := Array.getElem_setIfInBounds (xs := rows) (i := position)
      (a := replacement) (j := row) hbound
    by_cases heq : position = row
    · subst row
      exact hreplacement item (by simpa [Array.getD, hbound, hget] using hitem)
    · exact hrows row item (by simpa [Array.getD, hbound, hget, heq] using hitem)
  · simp [Array.getD, hbound] at hitem

private def SeedProvenance (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold : Nat) (state : Seeds) : Prop :=
  RowsHold state.buckets (fun _ offer =>
    OfferReach graph index selectors threshold offer.controller offer.node)

private theorem seedSource_preserves_provenance (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold source : Nat) (state : Seeds)
    (hsource : source < graph.size) (hstate : SeedProvenance graph index selectors threshold state) :
    SeedProvenance graph index selectors threshold
      (seedSource graph index selectors threshold source state) := by
  unfold seedSource
  split
  · exact hstate
  · rename_i hactive
    have hcontroller : isControllerB graph source = true := by
      cases h : isControllerB graph source <;> simp_all
    have hlive : index.liveB source = true := by
      cases h : index.liveB source <;> simp_all
    have hprivate : threshold ≤ (selectors.getD source .pub).rank := by
      simp only [hcontroller, hlive, Bool.not_true, Bool.false_or, Bool.or_false,
        decide_eq_true_eq] at hactive
      omega
    split
    · exact hstate
    · rename_i rank _
      split
      · exact hstate
      · apply rowsHold_set hstate
        intro offer hoffer
        rcases List.mem_append.mp hoffer with hnew | hold
        · obtain ⟨node, hedge, rfl⟩ := List.mem_map.mp hnew
          exact OfferReach.seed hsource hcontroller hprivate hlive hedge
        · exact hstate rank offer hold

private theorem seedBuckets_provenance (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold : Nat) :
    SeedProvenance graph index selectors threshold (seedBuckets graph index selectors threshold) := by
  unfold seedBuckets
  apply List.foldlRecOn (List.range graph.size)
    (fun state source => seedSource graph index selectors threshold source state)
  · intro row item hitem
    simp [Array.getD] at hitem
  · intro state hstate source hmem
    exact seedSource_preserves_provenance graph index selectors threshold source state
      (List.mem_range.mp hmem) hstate

def StateProvenance (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (threshold : Nat) (state : WorkState) : Prop :=
  state.frontier.size = graph.size ∧ state.unscanned.size = graph.size ∧
    RowsHold state.unscanned (fun source target => target ∈ graph.successors.getD source []) ∧
    (∀ offer ∈ state.pending, OfferReach graph index selectors threshold offer.controller offer.node) ∧
    (∀ bucket ∈ state.buckets, ∀ offer ∈ bucket,
      OfferReach graph index selectors threshold offer.controller offer.node) ∧
    (∀ node stop, stopAt state.frontier node = some stop →
      ∃ controller, OfferReach graph index selectors threshold controller node ∧
        index.parentAt controller = stop ∧ node ≠ stop ∧ index.liveB node = true)

private theorem initial_provenance (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold : Nat) :
    StateProvenance graph index selectors threshold
      (initialState graph (seedBuckets graph index selectors threshold)) := by
  refine ⟨by simp [initialState], rfl, ?_, ?_, ?_, ?_⟩
  · intro source target hedge
    exact hedge
  · intro offer hmem
    simp [initialState] at hmem
  · intro bucket hbucket offer hoffer
    obtain ⟨position, hposition, hrow⟩ := List.mem_iff_getElem.mp hbucket
    have hbound : position < (seedBuckets graph index selectors threshold).buckets.size := by
      simpa [initialState] using hposition
    have hget : (seedBuckets graph index selectors threshold).buckets.getD position [] = bucket := by
      simpa [initialState, Array.getD, hbound] using hrow
    exact seedBuckets_provenance graph index selectors threshold position offer (hget ▸ hoffer)
  · intro node stop hstop
    simp [initialState, stopAt, Array.getD] at hstop

theorem advance_preserves_origin {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {threshold : Nat} {state : WorkState}
    (hstate : StateProvenance graph index selectors threshold state) :
    StateProvenance graph index selectors threshold (advance index state) := by
  obtain ⟨hfrontSize, hscanSize, hrows, hpending, hbuckets, hstored⟩ := hstate
  unfold advance
  split
  · exact ⟨hfrontSize, hscanSize, hrows, hpending, hbuckets, hstored⟩
  · cases hp : state.pending with
    | nil =>
        dsimp only
        cases hb : state.buckets with
        | nil => exact ⟨hfrontSize, hscanSize, hrows, hpending, hbuckets, hstored⟩
        | cons bucket buckets =>
            refine ⟨hfrontSize, hscanSize, hrows, ?_, ?_, hstored⟩
            · exact hbuckets bucket (by simp [hb])
            · intro next hnext
              exact hbuckets next (by simp [hb, hnext])
    | cons offer pending =>
        dsimp only
        have horigin := hpending offer (by simp [hp])
        have hwhole : ∀ next ∈ offer :: pending,
            OfferReach graph index selectors threshold next.controller next.node := by
          simpa only [hp] using hpending
        have htail : ∀ next ∈ pending,
            OfferReach graph index selectors threshold next.controller next.node := by
          intro next hnext
          exact hpending next (by simp [hp, hnext])
        split
        · exact ⟨hfrontSize, hscanSize, hrows, hwhole, hbuckets, hstored⟩
        · rename_i hbound
          split
          · exact ⟨hfrontSize, hscanSize, hrows, htail, hbuckets, hstored⟩
          · rename_i hactive
            have hnode : offer.node < state.frontier.size := by
              simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hbound
              omega
            have hlive : index.liveB offer.node = true := by
              cases h : index.liveB offer.node <;> simp_all
            have hnotStop : offer.node ≠ index.parentAt offer.controller := by
              simp only [hlive, Bool.not_true, Bool.false_or, beq_iff_eq] at hactive
              exact hactive
            split
            · exact ⟨hfrontSize, hscanSize, hrows, hwhole, hbuckets, hstored⟩
            · split
              · exact ⟨hfrontSize, hscanSize, hrows, htail, hbuckets, hstored⟩
              · refine ⟨by simpa using hfrontSize, by simpa using hscanSize,
                  rowsHold_set hrows offer.node [] (by simp), ?_, hbuckets, ?_⟩
                · intro next hnext
                  rcases List.mem_append.mp hnext with hnew | hold
                  · obtain ⟨target, hedge, rfl⟩ := List.mem_map.mp hnew
                    exact OfferReach.carry horigin (by omega) hlive hnotStop
                      (hrows offer.node target hedge)
                  · exact htail next hold
                · intro node stop hstop
                  by_cases hnodeBound : node < state.frontier.size
                  · have hget := Array.getElem_setIfInBounds (xs := state.frontier)
                      (i := offer.node) (a := some (index.parentAt offer.controller))
                      (j := node) hnodeBound
                    by_cases heq : offer.node = node
                    · subst node
                      have hstopEq : index.parentAt offer.controller = stop := by
                        simpa [stopAt, Array.getD, hnodeBound, hget] using hstop
                      exact ⟨offer.controller, horigin, hstopEq, hstopEq ▸ hnotStop, hlive⟩
                    · apply hstored node stop
                      simpa [stopAt, Array.getD, hnodeBound, hget, heq] using hstop
                  · simp [stopAt, Array.getD, hnodeBound] at hstop

theorem run_preserves_origin {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {threshold : Nat} {state : WorkState}
    (hstate : StateProvenance graph index selectors threshold state) (fuel : Nat) :
    StateProvenance graph index selectors threshold (run index fuel state) := by
  induction fuel generalizing state with
  | zero => exact hstate
  | succ fuel ih =>
      unfold run
      split
      · exact hstate
      · exact ih (advance_preserves_origin hstate)

theorem compute_stored_stops_have_actual_origin (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold : Nat) {node stop : Nat}
    (hstop : stopAt (compute graph index selectors threshold).frontier node = some stop) :
    ∃ controller, OfferReach graph index selectors threshold controller node ∧
      index.parentAt controller = stop ∧ node ≠ stop ∧ index.liveB node = true := by
  have h := run_preserves_origin (initial_provenance graph index selectors threshold)
    (graph.size + 2 * edgeCount graph.successors)
  exact h.2.2.2.2.2 node stop hstop

end LambdaSigil.Combined.PriorityOccurrenceProvenance
