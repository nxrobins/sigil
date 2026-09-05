import LambdaSigil.OccurrenceTransfer
import LambdaSigil.OccurrenceRegionSecurity

/-!
# Rank-bounded private influence on finite successful CFG prefixes

These proofs derive prefix coverage from the executable per-edge frontier checks. A coarse
parent tree may enlarge the region, but cannot omit its live prefix by clearing at an unrelated
equal-rank stop. Successful continuation is explicit; dead vertices do not justify clearing.
The layer proves neither a verifier-derived selector table nor balanced invocation semantics,
and makes no Public noninterference claim.
-/

namespace LambdaSigil.Combined.OccurrenceTransferSecurity

open OccurrenceRegions OccurrenceRegionSecurity OccurrenceTransfer

private structure ParentFacts (graph : ControlGraph) (index : EscapeIndex) : Prop where
  edgeBound : ∀ source < graph.size, ∀ target ∈ graph.successors.getD source [],
    target < graph.size
  backwardLive : ∀ source < graph.size, ∀ target ∈ graph.successors.getD source [],
    index.liveB target = true → index.liveB source = true
  edgeParent : ∀ source < graph.size, ∀ target ∈ graph.successors.getD source [],
    index.liveB target = true → Ancestor index (index.parentAt source) target
  parentStep : ∀ source < graph.size, ∀ rank, index.rankAt source = some rank →
    index.parentAt source = source ∨
      ∃ nextRank, index.parentAt source < graph.size ∧
        index.rankAt (index.parentAt source) = some nextRank ∧ nextRank < rank

private theorem parentFacts_of_checks {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) : ParentFacts graph index := by
  simp only [escapeIndexChecks, Bool.and_eq_true] at hchecks
  obtain ⟨⟨⟨⟨hgraph, _⟩, _⟩, hexits⟩, hnodes⟩ := hchecks
  simp only [ControlGraph.wellFormedB, Bool.and_eq_true, List.all_eq_true,
    Array.all_eq_true, decide_eq_true_eq] at hgraph
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hexits
  simp only [List.all_eq_true, Bool.and_eq_true] at hnodes
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro source hsource target htarget
    have hsource' : source < graph.successors.size := hsource
    exact hgraph.2 source hsource' target (by simpa [Array.getD, hsource'] using htarget)
  · intro source hsource target htarget hlive
    have hedge := (hnodes source (List.mem_range.mpr hsource)).2 target htarget
    simp only [edgeParentB, hlive, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hedge
    exact hedge.1
  · intro source hsource target htarget hlive
    have hedge := (hnodes source (List.mem_range.mpr hsource)).2 target htarget
    simp only [edgeParentB, hlive, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hedge
    exact ancestorB_sound hedge.2
  · intro source hsource rank hrank
    have hparent := (hnodes source (List.mem_range.mpr hsource)).1.2
    simp only [parentRankedB, hrank, Bool.or_eq_true, List.contains_iff_mem,
      Bool.and_eq_true, decide_eq_true_eq] at hparent
    rcases hparent with hexit | ⟨hbound, hdecrease⟩
    · exact Or.inl (hexits source hexit).1
    · unfold rankDecreasesB at hdecrease
      split at hdecrease
      · cases hdecrease
      · rename_i nextRank hnextRank
        exact Or.inr ⟨nextRank, hbound, hnextRank, of_decide_eq_true hdecrease⟩

private theorem parentIter_rank_bound {graph : ControlGraph} {index : EscapeIndex}
    (hfacts : ParentFacts graph index) (steps : Nat) {source rank : Nat}
    (hsource : source < graph.size) (hrank : index.rankAt source = some rank) :
    ∃ nextRank, index.rankAt (parentIter index steps source) = some nextRank ∧
      nextRank ≤ rank ∧ (parentIter index steps source = source ∨ nextRank < rank) := by
  induction steps generalizing source rank with
  | zero => exact ⟨rank, hrank, Nat.le_refl _, Or.inl rfl⟩
  | succ steps ih =>
    rcases hfacts.parentStep source hsource rank hrank with hfixed | hnext
    · simpa only [parentIter, hfixed] using ih hsource hrank
    · obtain ⟨parentRank, hparentBound, hparentRank, hdecrease⟩ := hnext
      obtain ⟨nextRank, hnextRank, hle, _⟩ := ih hparentBound hparentRank
      exact ⟨nextRank, hnextRank, by omega, Or.inr (by omega)⟩

/-- This uses the same rank field as the local frontier check. A different progress measure
    cannot silently replace it: strict descent along live parent links is load-bearing. -/
theorem checked_ancestor_strict_rank {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {candidate source rank : Nat}
    (hsource : source < graph.size) (hrank : index.rankAt source = some rank)
    (hancestor : Ancestor index candidate source) (hne : candidate ≠ source) :
    ∃ candidateRank, index.rankAt candidate = some candidateRank ∧ candidateRank < rank := by
  obtain ⟨steps, hsteps⟩ := hancestor
  obtain ⟨candidateRank, hrank', _, hstrict⟩ :=
    parentIter_rank_bound (parentFacts_of_checks hchecks) steps hsource hrank
  rw [hsteps] at hrank' hstrict
  exact ⟨candidateRank, hrank', hstrict.resolve_left hne⟩

private structure FrontierFacts (graph : ControlGraph) (index : EscapeIndex)
    (selectors : Array Label) (threshold : Nat) (frontier : Frontier) : Prop where
  stopLive : ∀ source < graph.size, ∀ stop, stopAt frontier source = some stop →
    stop < graph.size ∧ index.liveB stop = true
  carry : ∀ source < graph.size, ∀ target ∈ graph.successors.getD source [],
    index.liveB target = true → ∀ stop, stopAt frontier source = some stop →
      target ≠ stop → carriesB index frontier target stop = true
  seed : ∀ source < graph.size, ∀ target ∈ graph.successors.getD source [],
    index.liveB target = true →
      controllerActiveB graph selectors frontier threshold source = true →
      target ≠ index.parentAt source → carriesB index frontier target (index.parentAt source) = true

private theorem frontierFacts_of_checks {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {threshold : Nat} {frontier : Frontier}
    (hchecks : frontierChecks graph index selectors threshold frontier = true) :
    FrontierFacts graph index selectors threshold frontier := by
  simp only [frontierChecks, Bool.and_eq_true] at hchecks
  obtain ⟨_, hnodes⟩ := hchecks
  simp only [List.all_eq_true, Bool.and_eq_true] at hnodes
  refine ⟨?_, ?_, ?_⟩
  · intro source hsource stop hstop
    have hnode := (hnodes source (List.mem_range.mpr hsource)).1
    simpa [hstop] using hnode
  · intro source hsource target hedge hlive stop hstop hne
    have hnode := (hnodes source (List.mem_range.mpr hsource)).2 target hedge
    simp only [frontierEdgeB, hlive, Bool.not_true, Bool.false_or,
      Bool.and_eq_true, hstop, Bool.or_eq_true, beq_iff_eq] at hnode
    exact hnode.1.resolve_left hne
  · intro source hsource target hedge hlive hactive hne
    have hnode := (hnodes source (List.mem_range.mpr hsource)).2 target hedge
    simp only [frontierEdgeB, hlive, Bool.not_true, Bool.false_or,
      Bool.and_eq_true, hactive, Bool.or_eq_true, beq_iff_eq] at hnode
    exact hnode.2.resolve_left hne

private theorem carries_rank {index : EscapeIndex} {frontier : Frontier}
    {target originalStop : Nat} (h : carriesB index frontier target originalStop = true) :
    ∃ replacement replacementRank originalRank, stopAt frontier target = some replacement ∧
      index.rankAt replacement = some replacementRank ∧
      index.rankAt originalStop = some originalRank ∧ replacementRank ≤ originalRank := by
  unfold carriesB at h
  split at h
  · cases h
  · rename_i replacement hreplacement
    unfold stopRankLeB at h
    split at h
    · rename_i replacementRank originalRank hreplacementRank horiginalRank
      exact ⟨replacement, replacementRank, originalRank, hreplacement,
        hreplacementRank, horiginalRank, of_decide_eq_true h⟩
    · cases h

private theorem prefix_start_mem {graph : ControlGraph} {source target : Nat} {trace : List Nat}
    (hpath : ControlPath graph source target trace) : source ∈ trace := by
  cases hpath <;> simp

private theorem live_before_prefix {graph : ControlGraph} {index : EscapeIndex}
    (hfacts : ParentFacts graph index) {source target : Nat} {trace : List Nat}
    (hpath : ControlPath graph source target trace) (hlive : index.liveB target = true) :
    index.liveB source = true := by
  induction hpath with
  | single node => exact hlive
  | @next source middle target tail hsource hedge _ ih =>
    exact hfacts.backwardLive source hsource middle hedge (ih hlive)

private theorem carries_through_prefix {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {threshold : Nat} {frontier : Frontier}
    (hindex : escapeIndexChecks graph index = true)
    (hfrontier : FrontierFacts graph index selectors threshold frontier)
    {source target originalStop : Nat} {trace : List Nat}
    (hpath : ControlPath graph source target trace)
    (hlive : index.liveB target = true) (havoid : originalStop ∉ trace)
    (hancestor : Ancestor index originalStop source)
    (hcarry : carriesB index frontier source originalStop = true) :
    carriesB index frontier target originalStop = true := by
  have hparents := parentFacts_of_checks hindex
  induction hpath with
  | single node => exact hcarry
  | @next source middle target tail hsource hedge hrest ih =>
    have hmiddleLive := live_before_prefix hparents hrest hlive
    have hmiddleBound := hparents.edgeBound source hsource middle hedge
    have hsourceNe : originalStop ≠ source := by
      intro heq
      exact havoid (by simp [heq])
    have htailAvoid : originalStop ∉ tail := by
      intro hmem
      exact havoid (List.mem_cons_of_mem source hmem)
    have hmiddleNe : originalStop ≠ middle := by
      intro heq
      exact htailAvoid (heq ▸ prefix_start_mem hrest)
    have hmiddleAncestor := (hancestor.of_ne hsourceNe).trans
      (hparents.edgeParent source hsource middle hedge hmiddleLive)
    obtain ⟨stop, stopRank, originalRank, hstop, hstopRank, horiginalRank, hstopLe⟩ :=
      carries_rank hcarry
    have hnotClear : middle ≠ stop := by
      intro heq
      have hmiddleRank : index.rankAt middle = some stopRank := heq.symm ▸ hstopRank
      obtain ⟨otherRank, hotherRank, hstrict⟩ := checked_ancestor_strict_rank hindex
        hmiddleBound hmiddleRank hmiddleAncestor hmiddleNe
      have heqRank : otherRank = originalRank :=
        Option.some.inj (hotherRank.symm.trans horiginalRank)
      omega
    have hnextCarry := hfrontier.carry source hsource middle hedge hmiddleLive stop hstop hnotClear
    obtain ⟨nextStop, nextRank, oldRank, hnextStop, hnextRank, holdRank, hnextLe⟩ :=
      carries_rank hnextCarry
    have heqRank : oldRank = stopRank := Option.some.inj (holdRank.symm.trans hstopRank)
    have hnext : carriesB index frontier middle originalStop = true := by
      simp only [carriesB, hnextStop, stopRankLeB, hnextRank, horiginalRank, decide_eq_true_eq]
      omega
    exact ih hlive htailAvoid hmiddleAncestor hnext

/-- Every live prefix avoiding an original checked continuation retains the threshold lane.
    The endpoint must have an actual finite successful suffix; rank-zero dead vertices do not
    satisfy this contract. Replacement stops may be unrelated in the checked parent tree. -/
theorem checked_frontier_covers_successful_prefix {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {threshold : Nat} {frontier : Frontier}
    (hindex : escapeIndexChecks graph index = true)
    (hfrontier : frontierChecks graph index selectors threshold frontier = true)
    {source target originalStop : Nat} {trace : List Nat}
    (hpath : ControlPath graph source target trace) (htarget : target < graph.size)
    (hcompletion : ∃ suffix, SuccessfulPath graph target suffix)
    (havoid : originalStop ∉ trace) (hancestor : Ancestor index originalStop source)
    (hcarry : carriesB index frontier source originalStop = true) :
    carriesB index frontier target originalStop = true :=
  carries_through_prefix hindex (frontierFacts_of_checks hfrontier) hpath
    ((checked_live_iff_successful_path hindex htarget).mpr hcompletion) havoid hancestor hcarry

/-- The seed is derived from an actual controller edge and the executable local check. Neither
    repeated-header detection nor completeness of the checked parent tree is assumed. -/
theorem checked_branch_covers_successful_prefix {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {threshold : Nat} {frontier : Frontier}
    (hindex : escapeIndexChecks graph index = true)
    (hfrontier : frontierChecks graph index selectors threshold frontier = true)
    {controller arm target : Nat} {trace : List Nat}
    (hcontroller : controller < graph.size)
    (hactive : controllerActiveB graph selectors frontier threshold controller = true)
    (hedge : arm ∈ graph.successors.getD controller [])
    (hpath : ControlPath graph arm target trace) (htarget : target < graph.size)
    (hcompletion : ∃ suffix, SuccessfulPath graph target suffix)
    (havoid : index.parentAt controller ∉ trace) :
    carriesB index frontier target (index.parentAt controller) = true := by
  have hparents := parentFacts_of_checks hindex
  have hfrontiers := frontierFacts_of_checks hfrontier
  have htargetLive := (checked_live_iff_successful_path hindex htarget).mpr hcompletion
  have harmLive := live_before_prefix hparents hpath htargetLive
  have harmNe : arm ≠ index.parentAt controller := by
    intro heq
    exact havoid (heq ▸ prefix_start_mem hpath)
  have hseed := hfrontiers.seed controller hcontroller arm hedge harmLive hactive harmNe
  exact carries_through_prefix hindex hfrontiers hpath htargetLive havoid
    (hparents.edgeParent controller hcontroller arm hedge harmLive) hseed

theorem checked_branch_prefix_lane_is_present {graph : ControlGraph} {index : EscapeIndex}
    {selectors : Array Label} {threshold : Nat} {frontier : Frontier}
    (hindex : escapeIndexChecks graph index = true)
    (hfrontier : frontierChecks graph index selectors threshold frontier = true)
    {controller arm target : Nat} {trace : List Nat}
    (hcontroller : controller < graph.size)
    (hactive : controllerActiveB graph selectors frontier threshold controller = true)
    (hedge : arm ∈ graph.successors.getD controller [])
    (hpath : ControlPath graph arm target trace) (htarget : target < graph.size)
    (hcompletion : ∃ suffix, SuccessfulPath graph target suffix)
    (havoid : index.parentAt controller ∉ trace) :
    (stopAt frontier target).isSome = true := by
  obtain ⟨stop, _, _, hstop, _⟩ := carries_rank
    (checked_branch_covers_successful_prefix hindex hfrontier hcontroller hactive hedge
      hpath htarget hcompletion havoid)
  simp [hstop]

theorem internal_lane_flows_to_local_occurrence {frontiers : ThresholdFrontiers} {node : Nat}
    (h : (stopAt frontiers.internalLane node).isSome = true) :
    Label.internal.flowsTo (localOccurrenceAt frontiers node) = true := by
  unfold localOccurrenceAt
  split
  · rfl
  · split
    · rfl
    · simp [Label.flowsTo, Label.rank]

theorem secret_lane_flows_to_local_occurrence {frontiers : ThresholdFrontiers} {node : Nat}
    (h : (stopAt frontiers.secretLane node).isSome = true) :
    Label.secret.flowsTo (localOccurrenceAt frontiers node) = true := by
  unfold localOccurrenceAt
  split <;> simp_all [Label.flowsTo, Label.rank]

theorem secretCT_lane_flows_to_local_occurrence {frontiers : ThresholdFrontiers} {node : Nat}
    (h : (stopAt frontiers.secretCTLane node).isSome = true) :
    Label.secretCT.flowsTo (localOccurrenceAt frontiers node) = true := by
  simp [localOccurrenceAt, h, Label.flowsTo, Label.rank]

private def setupLoop : ControlGraph := ⟨#[[1], [2, 3], [1], []], [3]⟩
private def setupLoopIndex : EscapeIndex :=
  ⟨#[1, 3, 1, 3], #[some 2, some 1, some 2, some 0]⟩
private def setupLoopSelectors : Array Label := #[.pub, .secret, .pub, .pub]
private def setupLoopFrontier : Frontier := #[none, some 3, some 3, none]

/-- Backedges carry the private lane into the repeated header, but the one-time setup and
    checked continuation remain clear. This does not classify an entire SCC as private. -/
theorem repeated_header_kept_setup_and_continuation_clear :
    escapeIndexChecks setupLoop setupLoopIndex = true ∧
      frontierChecks setupLoop setupLoopIndex setupLoopSelectors 2 setupLoopFrontier = true ∧
      stopAt setupLoopFrontier 0 = none ∧ stopAt setupLoopFrontier 1 = some 3 ∧
      stopAt setupLoopFrontier 3 = none := by decide +kernel

theorem missing_repeated_header_lane_detected :
    frontierChecks setupLoop setupLoopIndex setupLoopSelectors 2
      #[none, none, some 3, none] = false := by decide +kernel

private def balancedBranch : ControlGraph := ⟨#[[1, 5], [2, 3], [4], [4], [0], []], [5]⟩
private def balancedBranchIndex : EscapeIndex :=
  ⟨#[5, 4, 4, 4, 0, 5], #[some 1, some 4, some 3, some 3, some 2, some 0]⟩

theorem balanced_private_branch_does_not_taint_public_loop :
    escapeIndexChecks balancedBranch balancedBranchIndex = true ∧
      frontierChecks balancedBranch balancedBranchIndex
        #[.pub, .secret, .pub, .pub, .pub, .pub] 2
        #[none, none, some 4, some 4, none, none] = true := by decide +kernel

private def twoExits : ControlGraph := ⟨#[[1, 2], [3], [3], [], []], [3, 4]⟩
private def twoExitsIndex : EscapeIndex :=
  ⟨#[3, 3, 3, 3, 4], #[some 2, some 1, some 1, some 0, some 0]⟩
private def twoExitsSelectors : Array Label := #[.secret, .pub, .pub, .pub, .pub]

/-- Stop four is unrelated to the real continuation three, with the same live rank. Choosing
    it is safe but conservative: influence persists at three rather than clearing too early. -/
theorem unrelated_equal_rank_stop_only_enlarges_region :
    escapeIndexChecks twoExits twoExitsIndex = true ∧
      ancestorB twoExitsIndex 4 3 = false ∧
      frontierChecks twoExits twoExitsIndex twoExitsSelectors 2
        #[none, some 4, some 4, some 4, none] = true := by decide +kernel

/-- The old real continuation cannot erase a different outstanding stop. This planted dropped
    contribution is refused even though the two stop ranks are equal. -/
theorem unrelated_equal_rank_stop_cannot_silently_clear :
    frontierChecks twoExits twoExitsIndex twoExitsSelectors 2
      #[none, some 4, some 4, none, none] = false := by decide +kernel

private def deadStopGraph : ControlGraph := ⟨#[[1, 2], [3], [3], [], [4]], [3]⟩
private def deadStopIndex : EscapeIndex :=
  ⟨#[3, 3, 3, 3, 4], #[some 2, some 1, some 1, some 0, none]⟩

theorem dead_stop_cannot_justify_clearing :
    escapeIndexChecks deadStopGraph deadStopIndex = true ∧
      frontierChecks deadStopGraph deadStopIndex twoExitsSelectors 2
        #[none, some 4, some 4, some 4, none] = false ∧
      stopRankLeB deadStopIndex 4 3 = false := by decide +kernel

end LambdaSigil.Combined.OccurrenceTransferSecurity
