import LambdaSigil.OccurrenceTransferConstruction
import LambdaSigil.OccurrenceTransferSecurity
import LambdaSigil.OccurrenceReference
import LambdaSigil.OccurrenceRegionConstruction

/-!
# Bounded frontier candidates and checked prefix coverage

The pure slot update permits at most two strict changes under a live rank-zero fallback. Queue
arrays and counters remain bounded for all inputs. Returned tables satisfy the independently
proved local transfer equations, so their finite successful prefixes are covered. Solver totality,
global operation-count accounting, native timing, and production selector derivation are not
claims of this conditional-construction layer.
-/

namespace LambdaSigil.Combined.OccurrenceTransferConstructionSecurity

open OccurrenceRegions OccurrenceRegionSecurity OccurrenceTransfer OccurrenceTransferSecurity
open OccurrenceTransferConstruction

theorem chooseStop_present_change_is_fallback {index : EscapeIndex}
    {fallback incoming current : Nat}
    (hchange : chooseStop index fallback incoming (some current) ≠ some current) :
    chooseStop index fallback incoming (some current) = some fallback := by
  by_cases hkeep : stopRankLeB index current incoming = true
  · exact False.elim (hchange (by simp [chooseStop, hkeep]))
  · simp [chooseStop, hkeep]

theorem chooseStop_zero_rank_stable {index : EscapeIndex} {fallback incoming rank : Nat}
    (hfallback : index.rankAt fallback = some 0) (hincoming : index.rankAt incoming = some rank) :
    chooseStop index fallback incoming (some fallback) = some fallback := by
  simp [chooseStop, stopRankLeB, hfallback, hincoming]

/-- After the first stored stop changes once, it is the rank-zero fallback and every further
    live offer leaves it fixed. No descending chain of per-node ancestry refinements occurs. -/
theorem chooseStop_third_strict_change_impossible {index : EscapeIndex}
    {fallback first second third rank : Nat}
    (hfallback : index.rankAt fallback = some 0) (hthird : index.rankAt third = some rank)
    (hchange : chooseStop index fallback second (chooseStop index fallback first none) ≠
      chooseStop index fallback first none) :
    chooseStop index fallback third (chooseStop index fallback second
      (chooseStop index fallback first none)) =
      chooseStop index fallback second (chooseStop index fallback first none) := by
  have hreturn := chooseStop_present_change_is_fallback hchange
  change chooseStop index fallback third (chooseStop index fallback second (some first)) =
    chooseStop index fallback second (some first)
  rw [hreturn]
  exact chooseStop_zero_rank_stable hfallback hthird

def FrontierQueueShape (count : Nat) (state : FrontierQueue) : Prop :=
  state.frontier.size = count ∧ state.queue.size = 2 * count ∧
    state.head ≤ state.tail ∧ state.tail ≤ 2 * count

theorem offer_preserves_shape {count : Nat} {state : FrontierQueue}
    (hshape : FrontierQueueShape count state) (index : EscapeIndex) (roots : Array Nat)
    (node incoming : Nat) : FrontierQueueShape count (offer index roots state node incoming) := by
  simp only [offer]
  split
  · exact hshape
  · split
    · exact hshape
    · split
      · exact hshape
      · split
        · exact hshape
        · split
          · exact hshape
          · split
            · exact hshape
            · simp only [FrontierQueueShape, Array.size_setIfInBounds]
              rcases hshape with ⟨hfrontier, hqueue, hhead, htail⟩
              exact ⟨hfrontier, hqueue, by omega, by omega⟩

theorem propagateVertex_preserves_shape {count : Nat} {state : FrontierQueue}
    (hshape : FrontierQueueShape count state) (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (roots : Array Nat) (threshold source : Nat) :
    FrontierQueueShape count (propagateVertex graph index selectors roots threshold source state) := by
  unfold propagateVertex
  apply List.foldlRecOn
  · exact hshape
  · intro next hnext target _
    dsimp only
    have hcarried : FrontierQueueShape count
        (match stopAt state.frontier source with
         | none => next
         | some outstanding => offer index roots next target outstanding) := by
      split
      · exact hnext
      · exact offer_preserves_shape hnext index roots target _
    split
    · exact offer_preserves_shape hcarried index roots target _
    · exact hcarried

theorem frontierWork_preserves_shape {count : Nat} {state : FrontierQueue}
    (hshape : FrontierQueueShape count state) (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (roots : Array Nat) (threshold fuel : Nat) :
    FrontierQueueShape count (frontierWork graph index selectors roots threshold fuel state) := by
  induction fuel generalizing state with
  | zero => exact hshape
  | succ fuel ih =>
    unfold frontierWork
    split
    · exact hshape
    · rename_i hactive
      dsimp only
      split
      · exact hshape
      · apply ih
        apply propagateVertex_preserves_shape
        rcases hshape with ⟨hfrontier, hqueue, hhead, htail⟩
        simp only [Bool.or_eq_true, Bool.not_eq_true, decide_eq_true_eq, not_or] at hactive
        exact ⟨hfrontier, hqueue, by dsimp; omega, htail⟩

theorem computeFrontier_bounded (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (roots : Array Nat) (threshold : Nat) :
    FrontierQueueShape graph.size (computeFrontier graph index selectors roots threshold) := by
  apply frontierWork_preserves_shape
  apply List.foldlRecOn
  · simp [FrontierQueueShape]
  · intro state hstate source _
    split
    · apply List.foldlRecOn
      · exact hstate
      · intro next hnext target _
        exact offer_preserves_shape hnext index roots target _
    · exact hstate

theorem buildFrontier_checked {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {roots : Array Nat} {threshold : Nat} {frontier : Frontier}
    (h : buildFrontier? graph index selectors roots threshold = some frontier) :
    frontierChecks graph index selectors threshold frontier = true := by
  unfold buildFrontier? at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
      assumption
    · cases h

theorem constructed_frontiers_checked {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {roots : Array Nat} {frontiers : ThresholdFrontiers}
    (h : constructFrontiers? graph index selectors roots = some frontiers) :
    transferChecks graph index selectors frontiers = true := by
  unfold constructFrontiers? at h
  simp only [bind] at h
  split at h
  · cases h
  · rename_i hguard
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨internalLane, hinternal, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨secretLane, hsecret, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨secretCTLane, hct, h⟩ := h
    cases h
    have hindex : escapeIndexChecks graph index = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true, not_or] at hguard
      cases hvalue : escapeIndexChecks graph index <;> simp_all
    simp only [transferChecks, Bool.and_eq_true]
    exact ⟨⟨⟨hindex, buildFrontier_checked hinternal⟩,
      buildFrontier_checked hsecret⟩, buildFrontier_checked hct⟩

theorem constructed_secret_branch_prefix_is_private {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {roots : Array Nat} {frontiers : ThresholdFrontiers}
    (hconstructed : constructFrontiers? graph index selectors roots = some frontiers)
    {controller arm target : Nat} {trace : List Nat}
    (hcontroller : controller < graph.size)
    (hactive : controllerActiveB graph selectors frontiers.secretLane 2 controller = true)
    (hedge : arm ∈ graph.successors.getD controller [])
    (hpath : ControlPath graph arm target trace) (htarget : target < graph.size)
    (hcompletion : ∃ suffix, SuccessfulPath graph target suffix)
    (havoid : index.parentAt controller ∉ trace) :
    Label.secret.flowsTo (localOccurrenceAt frontiers target) = true := by
  have hchecks := constructed_frontiers_checked hconstructed
  simp only [transferChecks, Bool.and_eq_true] at hchecks
  exact secret_lane_flows_to_local_occurrence
    (checked_branch_prefix_lane_is_present hchecks.1.1.1 hchecks.1.2 hcontroller hactive
      hedge hpath htarget hcompletion havoid)

private def setupLoop : ControlGraph := ⟨#[[1], [2, 3], [1], []], [3]⟩
private def setupLoopIndex : EscapeIndex :=
  ⟨#[1, 3, 1, 3], #[some 2, some 1, some 2, some 0]⟩

theorem constructed_loop_preserves_setup_and_continuation :
    (constructFrontiers? setupLoop setupLoopIndex #[.pub, .secret, .pub, .pub] #[3, 3, 3, 3]).map
      (fun result => (result.internalLane, result.secretLane, result.secretCTLane)) =
      some (#[none, some 3, some 3, none], #[none, some 3, some 3, none],
        #[none, none, none, none]) := by decide +kernel

private def balancedBranch : ControlGraph := ⟨#[[1, 5], [2, 3], [4], [4], [0], []], [5]⟩
private def balancedBranchIndex : EscapeIndex :=
  ⟨#[5, 4, 4, 4, 0, 5], #[some 1, some 4, some 3, some 3, some 2, some 0]⟩

theorem constructed_balanced_branch_preserves_public_loop :
    (constructFrontiers? balancedBranch balancedBranchIndex
      #[.pub, .secret, .pub, .pub, .pub, .pub] #[5, 5, 5, 5, 5, 5]).map
      (fun result => (result.internalLane, result.secretLane, result.secretCTLane)) =
      some (#[none, none, some 4, some 4, none, none],
        #[none, none, some 4, some 4, none, none], #[none, none, none, none, none, none]) := by
  decide +kernel

private def chainIndex : EscapeIndex :=
  ⟨#[1, 2, 3, 4, 4], #[some 4, some 3, some 2, some 1, some 0]⟩
private def offerProbe : FrontierQueue :=
  let initial : FrontierQueue :=
    { frontier := Array.replicate 5 none, queue := Array.replicate 10 0 }
  let first := offer chainIndex #[4, 4, 4, 4, 4] initial 0 1
  let second := offer chainIndex #[4, 4, 4, 4, 4] first 0 2
  let third := offer chainIndex #[4, 4, 4, 4, 4] second 0 3
  offer chainIndex #[4, 4, 4, 4, 4] third 0 0

/-- The second incompatible scope widens once. Further offers and a stopped incoming edge
    neither allocate a third queue entry nor erase that active contribution. -/
theorem conflicting_scope_widens_once_and_never_erases :
    stopAt offerProbe.frontier 0 = some 4 ∧ offerProbe.tail = 2 ∧
      offerProbe.queue.size = 10 ∧ offerProbe.failed = false := by decide +kernel

private def generatedGraph (bits : Nat) : ControlGraph :=
  ⟨#[(List.range 3).filter (fun target => bits.testBit target),
      (List.range 3).filter (fun target => bits.testBit (3 + target)), []], [2]⟩

private def dominatesReference (graph : ControlGraph) (selectors : Array Label)
    (frontiers : ThresholdFrontiers) : Bool :=
  let reference : OccurrenceReference.Graph := ⟨graph.successors, graph.successfulExits, selectors⟩
  let labels := OccurrenceReference.localLabels reference
  (List.range graph.size).all (fun node =>
    (labels.getD node .pub).flowsTo (localOccurrenceAt frontiers node))

private def constructedDominatesReference (bits : Nat) : Bool :=
  let graph := generatedGraph bits
  let selectors : Array Label := #[.secret, .pub, .pub]
  match OccurrenceRegionConstruction.successRanks? graph with
  | none => false
  | some ranks =>
      let index : EscapeIndex := ⟨#[2, 2, 2], ranks⟩
      match constructFrontiers? graph index selectors #[2, 2, 2] with
      | none => false
      | some frontiers => dominatesReference graph selectors frontiers

/-- Every generated graph must construct successfully and dominate the independent slow
    oracle, including self edges, mutual cycles, dead arms and three-way controllers. Exact
    equality is intentionally not required of the conservative all-return parent candidate. -/
theorem generated_frontiers_cover_reference_occurrences :
    (List.range 64).all constructedDominatesReference = true := by decide +kernel

theorem reference_comparator_detects_missing_private_arm :
    dominatesReference (generatedGraph 38) #[.secret, .pub, .pub]
      ⟨#[none, none, none], #[none, none, none], #[none, none, none]⟩ = false := by decide +kernel

end LambdaSigil.Combined.OccurrenceTransferConstructionSecurity
