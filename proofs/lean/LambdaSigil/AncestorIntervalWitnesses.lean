import LambdaSigil.AncestorIntervalSecurity

/-!
# Non-vacuous interval construction and fail-closed mutants

All witness propositions reduce in the Lean kernel (`decide`, not `native_decide`). The tiny
generated corpus uses the old bounded parent walk only as an independent test oracle. Large
depth behavior is exercised by the separate executable benchmark, not by raising proof budgets.
-/

namespace LambdaSigil.Combined.AncestorIntervalWitnesses

open OccurrenceRegions AncestorIntervals

private def allLive (parents : Array Nat) : EscapeIndex :=
  ⟨parents, Array.replicate parents.size (some 0)⟩

private def nested : EscapeIndex := allLive #[3, 3, 4, 4, 4]
private def nestedIndex : IntervalIndex := (construct? nested [4]).getD default

theorem nested_forest_constructs : (construct? nested [4]).isSome = true := by decide

theorem nested_ancestor_and_sibling_queries :
    AncestorIntervals.ancestorB nested nestedIndex 4 0 = true ∧
    AncestorIntervals.ancestorB nested nestedIndex 3 0 = true ∧
    AncestorIntervals.ancestorB nested nestedIndex 3 1 = true ∧
    AncestorIntervals.ancestorB nested nestedIndex 3 2 = false ∧
    AncestorIntervals.ancestorB nested nestedIndex 0 1 = false := by decide

private def multiple : EscapeIndex := allLive #[2, 2, 2, 4, 4]

theorem separate_roots_do_not_alias :
    (construct? multiple [2, 4]).isSome = true ∧
    AncestorIntervals.ancestorB multiple ((construct? multiple [2, 4]).getD default) 2 3 = false ∧
    AncestorIntervals.ancestorB multiple ((construct? multiple [2, 4]).getD default) 4 0 = false := by
  decide

theorem cycles_and_bad_roots_reject :
    (construct? (allLive #[1, 0]) []).isNone = true ∧
    (construct? (allLive #[1, 2, 1, 3]) [3]).isNone = true ∧
    (construct? nested []).isNone = true ∧
    (construct? nested [4, 4]).isNone = true ∧
    (construct? nested [3]).isNone = true ∧
    (construct? nested [5]).isNone = true := by decide

theorem malformed_parent_and_rank_shapes_reject :
    (construct? (allLive #[8, 1]) [1]).isNone = true ∧
    (construct? ⟨#[0], #[]⟩ [0]).isNone = true ∧
    (construct? ⟨#[0, 2], #[some 0, none]⟩ [0]).isNone = true := by decide

private def dead : EscapeIndex := ⟨#[0, 0, 0], #[some 0, none, none]⟩

theorem dead_nodes_never_become_ancestors :
    (construct? dead [0]).isSome = true ∧
    AncestorIntervals.ancestorB dead ((construct? dead [0]).getD default) 1 1 = false ∧
    AncestorIntervals.ancestorB dead ((construct? dead [0]).getD default) 0 1 = false ∧
    (construct? dead [0, 1]).isNone = true := by decide

theorem forged_intervals_and_child_partitions_reject :
    intervalChecks nested [4] (childLists nested)
      { nestedIndex with leave := nestedIndex.leave.setIfInBounds 3 5 } = false ∧
    intervalChecks nested [4] (childLists nested)
      { nestedIndex with enter := nestedIndex.enter.setIfInBounds 0 (nestedIndex.start 1) } = false ∧
    intervalChecks nested [4] (childLists nested)
      { nestedIndex with order := nestedIndex.order.setIfInBounds 0 3 } = false ∧
    intervalChecks nested [4] ((childLists nested).setIfInBounds 3 [1]) nestedIndex = false ∧
    intervalChecks nested [4] ((childLists nested).setIfInBounds 3 [2, 0]) nestedIndex = false := by
  decide

/-- Deliberately unsound mutant: retain size, liveness, inverse-slot, and parent containment
    checks but drop the gap-free child partitions. The enlarged sibling interval below then
    manufactures an ancestor that the actual parent relation does not contain. -/
private def noChildPartitionsMutant (forest : EscapeIndex) (index : IntervalIndex) : Bool :=
  index.enter.size == forest.parent.size && index.leave.size == forest.parent.size &&
    index.order.size == forest.parent.size && index.count ≤ forest.parent.size &&
    (List.range forest.parent.size).all (fun node =>
      forest.parentAt node < forest.parent.size && forest.liveB node &&
      index.start node < index.stop node && index.stop node ≤ index.count &&
      index.order.getD (index.start node) forest.parent.size == node &&
      (forest.parentAt node == node ||
        (forest.liveB (forest.parentAt node) &&
          index.start (forest.parentAt node) < index.start node &&
          index.stop node ≤ index.stop (forest.parentAt node))))

theorem omitted_partition_mutant_readmits_false_ancestor :
    let forged := { nestedIndex with leave := nestedIndex.leave.setIfInBounds 3 5 }
    noChildPartitionsMutant nested forged = true ∧
      intervalChecks nested [4] (childLists nested) forged = false ∧
      AncestorIntervals.ancestorB nested forged 3 2 = true ∧
      OccurrenceRegions.ancestorB nested 3 2 = false := by decide

private def generatedForest (code : Nat) : EscapeIndex :=
  allLive #[code % 3, code / 3 % 3, code / 9 % 3]

private def roots (forest : EscapeIndex) : List Nat :=
  (List.range forest.parent.size).filter (fun node => forest.parentAt node == node)

private def oracleAccepts (forest : EscapeIndex) : Bool :=
  (List.range forest.parent.size).all (fun node =>
    (roots forest).any (fun root => OccurrenceRegions.ancestorB forest root node))

private def exactQueries (forest : EscapeIndex) (index : IntervalIndex) : Bool :=
  (List.range forest.parent.size).all (fun candidate =>
    (List.range forest.parent.size).all (fun node =>
      AncestorIntervals.ancestorB forest index candidate node ==
        OccurrenceRegions.ancestorB forest candidate node))

private def generatedCase (code : Nat) : Bool :=
  let forest := generatedForest code
  match construct? forest (roots forest) with
  | none => !oracleAccepts forest
  | some index => oracleAccepts forest && exactQueries forest index

theorem all_three_vertex_forests_match_independent_oracle :
    (List.range 27).all generatedCase = true := by decide

private def chain (size : Nat) : EscapeIndex :=
  allLive ((List.range size).map (fun node => if node + 1 < size then node + 1 else node)).toArray

theorem deep_chain_has_exact_ancestors :
    (construct? (chain 16) [15]).isSome = true ∧
    AncestorIntervals.ancestorB (chain 16) ((construct? (chain 16) [15]).getD default) 15 0 = true ∧
    AncestorIntervals.ancestorB (chain 16) ((construct? (chain 16) [15]).getD default) 0 15 = false := by
  decide

theorem bounded_traversal_does_not_return_unfinished_work :
    let unfinished := traverse nested (childLists nested) 1 (initialTraversal 5 [4])
    unfinished.pending.isEmpty = false ∧
      intervalChecks nested [4] (childLists nested) unfinished.intervals = false := by decide

end LambdaSigil.Combined.AncestorIntervalWitnesses
