import LambdaSigil.PriorityOccurrence
import LambdaSigil.OccurrenceTransferSecurity
import LambdaSigil.IntervalEscapeSecurity

/-!
# Exact-stop work accounting and checked frontier results

The work measure accounts for unconsumed buckets, pending offers, and unscanned adjacency.
Consuming a vertex transfers its edge mass into pending offers and pays one unit for the pop;
duplicate, stopped and dead offers also pay one. This establishes the stated fixed work budget
without an assumed convergence result or an enlarged quadratic retry bound.
-/

namespace LambdaSigil.Combined.PriorityOccurrenceSecurity

open OccurrenceRegions OccurrenceRegionSecurity OccurrenceTransfer OccurrenceTransferSecurity
open PriorityOccurrence

/-- The stack-safe array fold computes exactly the historical adjacency-list edge mass. -/
theorem edgeCount_eq_list_mass (adjacency : Array (List Nat)) :
    edgeCount adjacency = (adjacency.toList.map List.length).sum := by
  rw [edgeCount, ← Array.foldl_toList, List.sum_eq_foldl]
  simp only [List.foldl_map]

private theorem list_mass_set {α : Type} (xs : List (List α)) (position : Nat)
    (replacement : List α) (hposition : position < xs.length) :
    ((xs.set position replacement).map List.length).sum + (xs[position]).length =
      (xs.map List.length).sum + replacement.length := by
  induction xs generalizing position with
  | nil => simp at hposition
  | cons head tail ih =>
      cases position with
      | zero => simp; omega
      | succ position =>
          have htail : position < tail.length := by simpa using hposition
          have h := ih position htail
          simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
          omega

private theorem array_mass_set {α : Type} (xs : Array (List α)) (position : Nat)
    (replacement : List α) (hposition : position < xs.size) :
    (((xs.setIfInBounds position replacement).toList).map List.length).sum +
        (xs.getD position []).length =
      (xs.toList.map List.length).sum + replacement.length := by
  have h := list_mass_set xs.toList position replacement (by simpa using hposition)
  simpa [Array.getD, hposition] using h

def workMass (state : WorkState) : Nat :=
  state.buckets.length + (state.buckets.map List.length).sum + state.pending.length +
    edgeCount state.unscanned

theorem advance_consumes_work {index : EscapeIndex} {state : WorkState}
    (hactive : finishedB state = false) :
    finishedB (advance index state) = true ∨ workMass (advance index state) < workMass state := by
  have hfailed : state.failed = false := by
    simp only [finishedB, Bool.or_eq_false_iff] at hactive
    exact hactive.1
  unfold advance
  rw [hfailed]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hpending : state.pending with
  | nil =>
      dsimp only
      cases hbuckets : state.buckets with
      | nil => simp [finishedB, hfailed, hpending, hbuckets] at hactive
      | cons bucket buckets =>
          dsimp only
          right
          simp [workMass, hpending, hbuckets]
          omega
  | cons offer pending =>
      dsimp only
      split
      · left; simp [finishedB]
      · rename_i hbound
        split
        · right; simp [workMass, hpending]
        · split
          · left; simp [finishedB]
          · split
            · right; simp [workMass, hpending]
            · right
              have hnode : offer.node < state.unscanned.size := by
                simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hbound
                omega
              have hmass := array_mass_set state.unscanned offer.node [] hnode
              simp only [List.length_nil, Nat.add_zero] at hmass
              simp only [workMass, edgeCount_eq_list_mass, hpending, List.length_cons,
                List.length_append, List.length_map]
              omega

theorem advance_mass_nonincreasing (index : EscapeIndex) (state : WorkState) :
    workMass (advance index state) ≤ workMass state := by
  unfold advance
  split
  · exact Nat.le_refl _
  · cases hpending : state.pending with
    | nil =>
        dsimp only
        cases hbuckets : state.buckets with
        | nil => simp
        | cons bucket buckets => simp [workMass, hpending, hbuckets]; omega
    | cons offer pending =>
        dsimp only
        split
        · simp [workMass, hpending]
        · rename_i hbound
          split
          · simp [workMass, hpending]
          · split
            · simp [workMass, hpending]
            · split
              · simp [workMass, hpending]
              · have hnode : offer.node < state.unscanned.size := by
                  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hbound
                  omega
                have hmass := array_mass_set state.unscanned offer.node [] hnode
                simp only [List.length_nil, Nat.add_zero] at hmass
                simp only [workMass, edgeCount_eq_list_mass, hpending, List.length_cons,
                  List.length_append, List.length_map]
                omega

theorem run_mass_nonincreasing (index : EscapeIndex) (fuel : Nat) (state : WorkState) :
    workMass (run index fuel state) ≤ workMass state := by
  induction fuel generalizing state with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      unfold run
      split
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih _) (advance_mass_nonincreasing index state)

theorem run_finishes_with_mass_fuel (index : EscapeIndex) (fuel : Nat) (state : WorkState)
    (hbudget : workMass state ≤ fuel) : finishedB (run index fuel state) = true := by
  induction fuel generalizing state with
  | zero =>
      by_cases hdone : finishedB state = true
      · simpa [run] using hdone
      · have hmass : workMass state = 0 := by omega
        simp only [workMass, Nat.add_eq_zero_iff] at hmass
        have hpending : state.pending = [] := by simpa using hmass.1.2
        have hbuckets : state.buckets = [] := by simpa using hmass.1.1.1
        simp [run, finishedB, hpending, hbuckets]
  | succ fuel ih =>
      unfold run
      by_cases hdone : finishedB state = true
      · simp [hdone]
      · simp only [hdone, Bool.false_eq_true, ↓reduceIte]
        have hactive : finishedB state = false := by simpa using hdone
        rcases advance_consumes_work (index := index) hactive with hfinished | hdecrease
        · cases fuel <;> simp [run, hfinished]
        · exact ih (advance index state) (by omega)

private theorem seedSource_size (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold source : Nat) (state : Seeds) :
    (seedSource graph index selectors threshold source state).buckets.size = state.buckets.size := by
  unfold seedSource
  split
  · rfl
  · split
    · rfl
    · split <;> simp

private theorem seedSource_mass (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold source : Nat) (state : Seeds) :
    ((seedSource graph index selectors threshold source state).buckets.toList.map List.length).sum ≤
      (state.buckets.toList.map List.length).sum + (graph.successors.getD source []).length := by
  unfold seedSource
  split
  · simp
  · split
    · simp
    · rename_i rank _
      split
      · simp
      · rename_i hbound
        have hmass := array_mass_set state.buckets rank
          ((graph.successors.getD source []).map (fun node => (⟨source, node⟩ : Offer)) ++
            state.buckets.getD rank []) (by simpa using hbound)
        simp only [List.length_append, List.length_map] at hmass
        dsimp only
        omega

private theorem seedFold_mass (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold : Nat) (positions : List Nat) (initial : Seeds) :
    let result := positions.foldl (fun state source =>
      seedSource graph index selectors threshold source state) initial
    result.buckets.size = initial.buckets.size ∧
      (result.buckets.toList.map List.length).sum ≤
        (initial.buckets.toList.map List.length).sum +
          (positions.map (fun source => (graph.successors.getD source []).length)).sum := by
  induction positions generalizing initial with
  | nil => simp
  | cons source rest ih =>
      have hsize := seedSource_size graph index selectors threshold source initial
      have hstep := seedSource_mass graph index selectors threshold source initial
      have hrest := ih (seedSource graph index selectors threshold source initial)
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      exact ⟨hrest.1.trans hsize, by omega⟩

private theorem range_edge_mass (graph : ControlGraph) :
    ((List.range graph.size).map (fun source => (graph.successors.getD source []).length)).sum =
      edgeCount graph.successors := by
  have hlist : (List.range graph.size).map (fun source => graph.successors.getD source []) =
      graph.successors.toList := by
    apply List.ext_getElem
    · simp [ControlGraph.size]
    · intro position hleft hright
      have hposition : position < graph.successors.size := by simpa using hright
      simp [Array.getD, hposition]
  have h := congrArg (fun rows : List (List Nat) => (rows.map List.length).sum) hlist
  simpa [List.map_map, Function.comp_def, edgeCount_eq_list_mass] using h

theorem seed_storage_is_linear (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold : Nat) :
    (seedBuckets graph index selectors threshold).buckets.size = graph.size ∧
      ((seedBuckets graph index selectors threshold).buckets.toList.map List.length).sum ≤
        edgeCount graph.successors := by
  have h := seedFold_mass graph index selectors threshold (List.range graph.size)
    { buckets := Array.replicate graph.size [] }
  dsimp only at h
  rw [range_edge_mass] at h
  simpa [seedBuckets] using h

theorem initial_work_mass_is_linear (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold : Nat) :
    workMass (initialState graph (seedBuckets graph index selectors threshold)) ≤
      graph.size + 2 * edgeCount graph.successors := by
  have h := seed_storage_is_linear graph index selectors threshold
  simp only [workMass, initialState, Array.length_toList, List.length_nil, Nat.add_zero]
  omega

theorem compute_finishes_with_linear_fuel (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold : Nat) :
    finishedB (compute graph index selectors threshold) = true :=
  run_finishes_with_mass_fuel index _ _ (initial_work_mass_is_linear graph index selectors threshold)

theorem compute_cannot_exhaust_unfinished_work {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {threshold : Nat}
    (h : (compute graph index selectors threshold).failed = false) :
    (compute graph index selectors threshold).pending = [] ∧
      (compute graph index selectors threshold).buckets = [] := by
  have hfinished := compute_finishes_with_linear_fuel graph index selectors threshold
  simpa [finishedB, h] using hfinished

theorem compute_pending_storage_is_linear (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold : Nat) :
    workMass (compute graph index selectors threshold) ≤
      graph.size + 2 * edgeCount graph.successors :=
  Nat.le_trans (run_mass_nonincreasing index _ _)
    (initial_work_mass_is_linear graph index selectors threshold)

theorem advance_preserves_settled_stop {index : EscapeIndex} {state : WorkState}
    {node stop : Nat} (hstop : stopAt state.frontier node = some stop) :
    stopAt (advance index state).frontier node = some stop := by
  unfold advance
  split
  · exact hstop
  · cases hpending : state.pending with
    | nil => cases state.buckets <;> exact hstop
    | cons offer pending =>
        dsimp only
        split
        · exact hstop
        · split
          · exact hstop
          · split
            · exact hstop
            · split
              · exact hstop
              · rename_i hnew
                have hne : offer.node ≠ node := by
                  intro heq
                  simp [heq, hstop] at hnew
                have hnode : node < state.frontier.size := by
                  by_cases hbound : node < state.frontier.size
                  · exact hbound
                  · simp [stopAt, Array.getD, hbound] at hstop
                have hget := Array.getElem_setIfInBounds (xs := state.frontier)
                  (i := offer.node) (a := some (index.parentAt offer.controller))
                  (j := node) hnode
                simpa [stopAt, Array.getD, hnode, hget, hne] using hstop

theorem run_preserves_settled_stop {index : EscapeIndex} {state : WorkState}
    {node stop : Nat} (hstop : stopAt state.frontier node = some stop) (fuel : Nat) :
    stopAt (run index fuel state).frontier node = some stop := by
  induction fuel generalizing state with
  | zero => exact hstop
  | succ fuel ih =>
      unfold run
      split
      · exact hstop
      · exact ih (advance_preserves_settled_stop hstop)

theorem returned_frontier_is_checked {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {threshold : Nat} {frontier : Frontier}
    (h : buildFrontier? graph index selectors threshold = some frontier) :
    frontierChecks graph index selectors threshold frontier = true := by
  unfold buildFrontier? at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
      assumption
    · cases h

theorem constructed_frontiers_are_checked {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {frontiers : ThresholdFrontiers}
    (h : constructFrontiers? graph index selectors = some frontiers) :
    transferChecks graph index selectors frontiers = true := by
  unfold constructFrontiers? at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨intervals, hintervals, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨internalLane, hinternal, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨secretLane, hsecret, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨secretCTLane, hct, h⟩ := h
  cases h
  simp only [transferChecks, Bool.and_eq_true]
  exact ⟨⟨⟨IntervalEscapeSecurity.returned_implies_escape_index_checks hintervals,
    returned_frontier_is_checked hinternal⟩, returned_frontier_is_checked hsecret⟩,
    returned_frontier_is_checked hct⟩

theorem constructed_secret_branch_prefix_is_private {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {frontiers : ThresholdFrontiers}
    (h : constructFrontiers? graph index selectors = some frontiers)
    {controller arm target : Nat} {trace : List Nat} (hcontroller : controller < graph.size)
    (hactive : controllerActiveB graph selectors frontiers.secretLane 2 controller = true)
    (hedge : arm ∈ graph.successors.getD controller [])
    (hpath : ControlPath graph arm target trace) (htarget : target < graph.size)
    (hcompletion : ∃ suffix, SuccessfulPath graph target suffix)
    (havoid : index.parentAt controller ∉ trace) :
    Label.secret.flowsTo (localOccurrenceAt frontiers target) = true := by
  have hchecks := constructed_frontiers_are_checked h
  simp only [transferChecks, Bool.and_eq_true] at hchecks
  exact secret_lane_flows_to_local_occurrence
    (checked_branch_prefix_lane_is_present hchecks.1.1.1 hchecks.1.2 hcontroller hactive
      hedge hpath htarget hcompletion havoid)

namespace PriorityOccurrenceWitnesses

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

/- The production self-host graph is large enough that converting the whole adjacency array to a
   recursively consumed list overflowed the native verifier stack. This executable witness stays
   above that observed size and must complete on the ordinary Lean build stack. -/
private def stackBoundedEdgeCountCanary : Bool :=
  edgeCount (Array.replicate 400_000 ([0] : List Nat)) == 400_000

#eval require stackBoundedEdgeCountCanary
  "400,000-row priority edge counting must remain an iterative array fold"

private def nestedDiamond : ControlGraph :=
  ⟨#[[1, 4], [2, 3], [3], [5], [5], [6], [7], []], [7]⟩
private def nestedDiamondIndex : EscapeIndex :=
  ⟨#[5, 3, 3, 5, 5, 6, 7, 7],
    #[some 4, some 4, some 4, some 3, some 3, some 2, some 1, some 0]⟩
private def nestedSelectors : Array Label :=
  #[.secret, .secret, .pub, .pub, .pub, .pub, .pub, .pub]

/-- Unlike the retained two-change counterexample, the wider outer stop settles the inner arm
    first. The actual checked outer continuation remains Public; no rank-zero widening occurs. -/
theorem nested_diamond_restores_checked_public_continuation :
    (constructFrontiers? nestedDiamond nestedDiamondIndex nestedSelectors).map
      (fun result => result.secretLane) =
      some #[none, some 5, some 5, some 5, some 5, none, none, none] := by decide +kernel

private def setupLoop : ControlGraph := ⟨#[[1], [2, 3], [1], []], [3]⟩
private def setupLoopIndex : EscapeIndex :=
  ⟨#[1, 3, 1, 3], #[some 2, some 1, some 2, some 0]⟩

theorem repeated_header_preserves_one_time_setup_and_public_exit :
    (constructFrontiers? setupLoop setupLoopIndex #[.pub, .secret, .pub, .pub]).map
      (fun result => (result.internalLane, result.secretLane, result.secretCTLane)) =
      some (#[none, some 3, some 3, none], #[none, some 3, some 3, none],
        #[none, none, none, none]) := by decide +kernel

/-- These finite successful CFG paths have different lengths and different header counts.
    This witness does not identify them with balanced raw executions or a Public theorem. -/
theorem unequal_successful_loop_paths_keep_the_header_private :
    (constructFrontiers? setupLoop setupLoopIndex #[.pub, .secret, .pub, .pub]).map
      (fun result => localOccurrenceAt result 1) = some .secret ∧
    SuccessfulPath setupLoop 0 [0, 1, 3] ∧
    SuccessfulPath setupLoop 0 [0, 1, 2, 1, 3] := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · exact ⟨3, by decide, .next (by decide) (by decide)
      (.next (by decide) (by decide) (.single 3))⟩
  · exact ⟨3, by decide, .next (by decide) (by decide)
      (.next (by decide) (by decide) (.next (by decide) (by decide)
        (.next (by decide) (by decide) (.single 3))))⟩

private def balancedBranch : ControlGraph := ⟨#[[1, 5], [2, 3], [4], [4], [0], []], [5]⟩
private def balancedBranchIndex : EscapeIndex :=
  ⟨#[5, 4, 4, 4, 0, 5], #[some 1, some 4, some 3, some 3, some 2, some 0]⟩

theorem balanced_private_branch_preserves_enclosing_public_loop :
    (constructFrontiers? balancedBranch balancedBranchIndex
      #[.pub, .secret, .pub, .pub, .pub, .pub]).map (fun result => result.secretLane) =
      some #[none, none, some 4, some 4, none, none] := by decide +kernel

theorem missing_seed_and_early_clear_mutants_rejected :
    frontierChecks nestedDiamond nestedDiamondIndex nestedSelectors 2
      #[none, none, none, none, none, none, none, none] = false ∧
    frontierChecks nestedDiamond nestedDiamondIndex nestedSelectors 2
      #[none, some 5, some 5, none, some 5, none, none, none] = false ∧
    frontierChecks setupLoop setupLoopIndex #[.pub, .secret, .pub, .pub] 2
      #[none, none, some 3, none] = false := by decide +kernel

private def twoExits : ControlGraph := ⟨#[[1, 2], [3], [3], [], []], [3, 4]⟩
private def twoExitsIndex : EscapeIndex :=
  ⟨#[3, 3, 3, 3, 4], #[some 2, some 1, some 1, some 0, some 0]⟩

theorem unrelated_equal_rank_stop_is_not_silently_cleared :
    (constructFrontiers? twoExits twoExitsIndex #[.secret, .pub, .pub, .pub, .pub]).map
      (fun result => result.secretLane) = some #[none, some 3, some 3, none, none] ∧
    frontierChecks twoExits twoExitsIndex #[.secret, .pub, .pub, .pub, .pub] 2
      #[none, some 4, some 4, none, none] = false := by decide +kernel

private def deadArm : ControlGraph := ⟨#[[1, 2], [1], []], [2]⟩
private def deadArmIndex : EscapeIndex := ⟨#[2, 1, 2], #[some 1, none, some 0]⟩

theorem dead_cycle_does_not_supply_a_synchronization_stop :
    (constructFrontiers? deadArm deadArmIndex #[.secret, .secret, .pub]).map
      (fun result => result.secretLane) = some #[none, none, none] ∧
    frontierChecks deadArm deadArmIndex #[.secret, .secret, .pub] 2
      #[some 1, none, none] = false := by decide +kernel

end PriorityOccurrenceWitnesses

end LambdaSigil.Combined.PriorityOccurrenceSecurity
