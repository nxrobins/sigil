import LambdaSigil.OccurrenceRegions

/-!
# Checked Euler intervals for live parent forests

This Init-only module constructs shared child adjacency once and traverses it with at most two
events per vertex. The independent postcheck scans each vertex and child edge once. In particular,
it does not call the old `ancestorB`, chase a parent chain, or store per-node ancestry lists.
Queries use a fixed number of bounded array lookups and interval comparisons. This is a new
internal foundation, not a change to the production v8 decoder, checker, or raw machine.

The postcheck does not trust a DFS implementation or supplied intervals: unique preorder slots,
strict parent containment, gap-free child partitions, and exact declared-root partitions are
checked separately. Cycles, missing roots, duplicate roots, malformed parents, unfinished work,
and forged intervals fail closed. Soundness is conditional on returned construction; no compiler
or native timing claim follows from this module.
-/

namespace LambdaSigil.Combined.AncestorIntervals

open OccurrenceRegions

structure IntervalIndex where
  enter : Array Nat
  leave : Array Nat
  order : Array Nat
  count : Nat
  deriving Repr, Inhabited

def IntervalIndex.start (index : IntervalIndex) (node : Nat) : Nat := index.enter.getD node 0
def IntervalIndex.stop (index : IntervalIndex) (node : Nat) : Nat := index.leave.getD node 0

def childLists (forest : EscapeIndex) : Array (List Nat) :=
  (List.range forest.parent.size).foldl (fun children node =>
    if forest.liveB node && forest.parentAt node != node then
      let parent := forest.parentAt node
      children.setIfInBounds parent (node :: children.getD parent [])
    else children) (Array.replicate forest.parent.size [])

def rootMask (size : Nat) (roots : List Nat) : Array Bool :=
  roots.foldl (fun mask root => mask.setIfInBounds root true) (Array.replicate size false)

/-- Consume one contiguous partition. Every segment is nonempty; omission, overlap, reordered
    children, duplicate roots, or a forged endpoint therefore refuses the entire partition. -/
def partition? (index : IntervalIndex) : List Nat → Nat → Option Nat
  | [], cursor => some cursor
  | child :: children, cursor =>
      if index.start child == cursor && index.start child < index.stop child then
        partition? index children (index.stop child)
      else none

def liveNodeChecks (forest : EscapeIndex) (index : IntervalIndex)
    (children : Array (List Nat)) (roots : Array Bool) (node : Nat) : Bool :=
  forest.parentAt node < forest.parent.size &&
  (if !forest.liveB node then !roots.getD node false else
    index.start node < index.stop node && index.stop node ≤ index.count &&
    index.order.getD (index.start node) forest.parent.size == node &&
    (if forest.parentAt node == node then roots.getD node false else
      !roots.getD node false && forest.liveB (forest.parentAt node) &&
      index.start (forest.parentAt node) < index.start node &&
      index.stop node ≤ index.stop (forest.parentAt node)) &&
    (children.getD node []).all (fun child =>
      child < forest.parent.size && forest.liveB child && forest.parentAt child == node) &&
    partition? index (children.getD node []) (index.start node + 1) == some (index.stop node))

def intervalChecks (forest : EscapeIndex) (roots : List Nat)
    (children : Array (List Nat)) (index : IntervalIndex) : Bool :=
  let size := forest.parent.size
  forest.successRank.size == size && children.size == size &&
    index.enter.size == size && index.leave.size == size && index.order.size == size &&
    index.count ≤ size &&
    roots.all (fun root => root < size && forest.liveB root && forest.parentAt root == root) &&
    partition? index roots 0 == some index.count &&
    (List.range size).all (liveNodeChecks forest index children (rootMask size roots))

inductive Visit where
  | enter (node : Nat)
  | leave (node : Nat)
  deriving Repr

structure Traversal where
  intervals : IntervalIndex
  seen : Array Bool
  pending : List Visit
  failed : Bool := false
  deriving Repr

def enterVisits (nodes : List Nat) (tail : List Visit) : List Visit :=
  nodes.reverse.foldl (fun pending node => .enter node :: pending) tail

def traverse (forest : EscapeIndex) (children : Array (List Nat)) :
    Nat → Traversal → Traversal
  | 0, state => state
  | fuel + 1, state =>
      if state.failed then state else
      match state.pending with
      | [] => state
      | .enter node :: pending =>
          if node ≥ forest.parent.size || !forest.liveB node ||
              state.seen.getD node false || state.intervals.count ≥ forest.parent.size then
            { state with failed := true }
          else
            let clock := state.intervals.count
            traverse forest children fuel
              { intervals :=
                  { state.intervals with
                    enter := state.intervals.enter.setIfInBounds node clock
                    order := state.intervals.order.setIfInBounds clock node
                    count := clock + 1 }
                seen := state.seen.setIfInBounds node true
                pending := enterVisits (children.getD node []) (.leave node :: pending) }
      | .leave node :: pending =>
          if node ≥ forest.parent.size || !state.seen.getD node false then
            { state with failed := true }
          else
            traverse forest children fuel
              { state with
                intervals := { state.intervals with
                  leave := state.intervals.leave.setIfInBounds node state.intervals.count }
                pending }

def initialTraversal (size : Nat) (roots : List Nat) : Traversal :=
  { intervals :=
      { enter := Array.replicate size 0
        leave := Array.replicate size 0
        order := Array.replicate size size
        count := 0 }
    seen := Array.replicate size false
    pending := enterVisits roots [] }

/-- Fixed two-events-per-vertex fuel, fixed-width tables, and no partial result on failure.
    Child adjacency is internal and the shared postcheck is independent of traversal state. -/
def construct? (forest : EscapeIndex) (roots : List Nat) : Option IntervalIndex :=
  let size := forest.parent.size
  if forest.successRank.size != size || roots.length > size then none else
  let children := childLists forest
  let result := traverse forest children (2 * size) (initialTraversal size roots)
  if result.failed || !result.pending.isEmpty then none else
  if intervalChecks forest roots children result.intervals then some result.intervals else none

def ancestorB (forest : EscapeIndex) (index : IntervalIndex) (candidate node : Nat) : Bool :=
  candidate < forest.parent.size && node < forest.parent.size &&
    forest.liveB candidate && forest.liveB node &&
    index.start candidate ≤ index.start node && index.start node < index.stop candidate

/-- Drop-in edge obligation once the shared forest index has been constructed and checked.
    Callers still owe CFG bounds and the other success-rank/parent obligations. -/
def edgeParentB (forest : EscapeIndex) (index : IntervalIndex) (source target : Nat) : Bool :=
  !forest.liveB target ||
    (forest.liveB source && ancestorB forest index (forest.parentAt source) target)

end LambdaSigil.Combined.AncestorIntervals
