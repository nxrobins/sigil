import LambdaSigil.OccurrenceRegions

/-!
# Internal success-rank and continuation construction

Reverse adjacency, an exit mask, and a fixed-capacity array queue are built once. Nodes are marked
on enqueue, so the intended BFS visits each node once and scans each reverse edge once. Queue
overflow, unfinished work, malformed graphs, or failed postchecks refuse the entire construction;
no dropped edge or partial rank table is returned as evidence.

Continuation candidates are internal: actual single successors, loop alternates, and branch
merge hints are tried, then independently checked. A failed candidate takes an explicit
function-return fallback and is checked again. This is not production acceptance. The retained
parent-walk checker is not yet performance qualified, and conservative traversal to checked
continuations, balanced invocation effects, and Public preservation remain separate work.
-/

namespace LambdaSigil.Combined.OccurrenceRegionConstruction

open Semantic OccurrenceRegions

def reverseEdges (graph : ControlGraph) : Array (List Nat) :=
  (List.range graph.size).foldl (fun reverse source =>
    (graph.successors.getD source []).foldl (fun reverse target =>
      reverse.setIfInBounds target (source :: reverse.getD target [])) reverse)
    (Array.replicate graph.size [])

def exitMask (graph : ControlGraph) : Array Bool :=
  graph.successfulExits.foldl (fun mask exit => mask.setIfInBounds exit true)
    (Array.replicate graph.size false)

structure SuccessQueue where
  ranks : Array (Option Nat)
  queue : Array Nat
  head : Nat := 0
  tail : Nat := 0
  failed : Bool := false
  deriving Repr

def enqueue (state : SuccessQueue) (node rank : Nat) : SuccessQueue :=
  if node ≥ state.ranks.size then { state with failed := true }
  else if (state.ranks.getD node none).isSome then state
  else if state.tail ≥ state.queue.size then { state with failed := true }
  else
    { state with
      ranks := state.ranks.setIfInBounds node (some rank)
      queue := state.queue.setIfInBounds state.tail node
      tail := state.tail + 1 }

def successBfs (reverse : Array (List Nat)) : Nat → SuccessQueue → SuccessQueue
  | 0, state => state
  | fuel + 1, state =>
      if state.failed || state.head ≥ state.tail then state else
      let node := state.queue.getD state.head 0
      match state.ranks.getD node none with
      | none => { state with failed := true }
      | some rank =>
          let next := (reverse.getD node []).foldl (fun next predecessor =>
            enqueue next predecessor (rank + 1)) { state with head := state.head + 1 }
          successBfs reverse fuel next

def computeSuccessQueue (graph : ControlGraph) : SuccessQueue :=
  let initial : SuccessQueue :=
    { ranks := Array.replicate graph.size none, queue := Array.replicate graph.size 0 }
  let seeded := graph.successfulExits.foldl (fun state exit => enqueue state exit 0) initial
  successBfs (reverseEdges graph) graph.size seeded

def rankAt (ranks : Array (Option Nat)) (node : Nat) : Option Nat := ranks.getD node none

/-- Linear local shortest-distance equations: every live non-exit has a successor one rank
    closer to success, and every live-target edge bounds its source by that successor plus one.
    The mask is built from actual exits once, rather than rescanning exits at every node. -/
def successRankChecks (graph : ControlGraph) (ranks : Array (Option Nat)) : Bool :=
  let exits := exitMask graph
  graph.wellFormedB && ranks.size == graph.size &&
    graph.successfulExits.all (fun exit => rankAt ranks exit == some 0) &&
    (List.range graph.size).all (fun source =>
      (match rankAt ranks source with
       | none => true
       | some rank => rank < graph.size &&
           (exits.getD source false || (graph.successors.getD source []).any (fun target =>
             match rankAt ranks target with
             | none => false
             | some nextRank => rank == nextRank + 1))) &&
      (graph.successors.getD source []).all (fun target =>
        match rankAt ranks target with
        | none => true
        | some nextRank =>
            match rankAt ranks source with
            | none => false
            | some rank => rank ≤ nextRank + 1))

def successRanks? (graph : ControlGraph) : Option (Array (Option Nat)) :=
  if !graph.wellFormedB then none else
  let result := computeSuccessQueue graph
  if result.failed || result.head != result.tail then none else
  if successRankChecks graph result.ranks then some result.ranks else none

def candidateParent (p : SemanticProgram) (pc : Nat) (instruction : Instruction) : Nat :=
  match instructionSuccessors p pc instruction with
  | [successor] => successor
  | _ =>
      match instruction.op with
      | .loop | .range => instruction.alternate.toNat
      | .branch | .dispatch => instruction.merge.toNat
      | _ => functionReturn p instruction.functionId

def candidateParents (p : SemanticProgram) : Array Nat :=
  (p.instructions.mapIdx (candidateParent p)) ++
    (List.range' p.instructions.size p.functions.size).toArray

def functionReturnParents (p : SemanticProgram) : Array Nat :=
  (p.instructions.map (fun instruction => functionReturn p instruction.functionId)) ++
    (List.range' p.instructions.size p.functions.size).toArray

/-- Rank-keyed chain intersection for the postdominator candidate: walk both parent chains
    toward the exit, always stepping from the node whose (rank, id) key is larger, until they
    meet. Every stored candidate parent has a strictly smaller key than its node, so the walk
    descends; the fuel bounds it on malformed input, where `none` (no meeting point) is the
    answer rather than a guess. -/
def intersectChains (parents : Array (Option Nat)) (ranks : Array (Option Nat)) :
    Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, a, b =>
      if a == b then some a else
      let keyA := (rankAt ranks a).getD 0
      let keyB := (rankAt ranks b).getD 0
      let stepA := keyA > keyB || (keyA == keyB && a > b)
      let source := if stepA then a else b
      match parents.getD source none with
      | none => none
      | some next =>
          if next == source then none
          else if stepA then intersectChains parents ranks fuel next b
          else intersectChains parents ranks fuel a next

/-- One refinement pass in rank order (nearest to success first): a live non-exit node's
    parent becomes the intersection of the chains of its live successors that already carry a
    parent. In the first pass every such node has a successor one rank nearer to success that
    was processed before it, so every live node receives a parent immediately and later passes
    only tighten it toward the immediate postdominator. A pair of chains that never meet marks
    the node unresolved for this pass instead of guessing. -/
def refineParentsOnce (graph : ControlGraph) (ranks : Array (Option Nat)) (exits : Array Bool)
    (order : Array Nat) (parents : Array (Option Nat)) : Array (Option Nat) × Bool :=
  order.foldl (fun state node =>
    let (parents, changed) := state
    if exits.getD node false then (parents, changed) else
    let (candidate, failed) := (graph.successors.getD node []).foldl (fun acc successor =>
      let (current, failed) := acc
      if failed then acc else
      match rankAt ranks successor, parents.getD successor none with
      | some _, some _ =>
          match current with
          | none => (some successor, false)
          | some current =>
              match intersectChains parents ranks graph.size current successor with
              | none => (none, true)
              | some met => (some met, false)
      | _, _ => acc) ((none : Option Nat), false)
    if failed then (parents, changed) else
    match candidate with
    | none => (parents, changed)
    | some next =>
        if parents.getD node none == some next then (parents, changed)
        else (parents.setIfInBounds node (some next), true)) (parents, false)

def refineParents (graph : ControlGraph) (ranks : Array (Option Nat)) (exits : Array Bool)
    (order : Array Nat) : Nat → Array (Option Nat) → Array (Option Nat)
  | 0, parents => parents
  | fuel + 1, parents =>
      let (next, changed) := refineParentsOnce graph ranks exits order parents
      if changed then refineParents graph ranks exits order fuel next else next

/-- Postdominator candidate: the immediate postdominators of the live nodes with respect to the
    successful exits, computed by rank-ordered iterative refinement over the actual control
    graph (Cooper–Harvey–Kennedy with (rank, id) keys, which strictly decrease toward the
    exit). This is the exact continuation of every controller: a branch whose arms both leave
    their loop converges at the loop exit, and a branch with a returning arm converges only at
    its function return, so neither shape forces any other controller to its function return.
    Dead nodes keep the structural hint, which the checks treat as unconstrained, and a live
    node the refinement leaves unresolved keeps it as well. This chooses candidates only: the
    interval and escape checks validate every parent, and the whole-program fallback remains
    behind them. -/
def postdominatorParents (p : SemanticProgram) (graph : ControlGraph)
    (ranks : Array (Option Nat)) : Array Nat :=
  let exits := exitMask graph
  let seeded : Array (Option Nat) := graph.successfulExits.foldl
    (fun parents exit => parents.setIfInBounds exit (some exit))
    (Array.replicate graph.size none)
  -- Live nodes in (rank, id) order, bucketed by rank rather than sorted: every rank is below
  -- `graph.size` by the success-rank checks, and the folds stay kernel-reducible for the
  -- executable witnesses.
  let buckets := (List.range graph.size).foldr (fun node buckets =>
    match rankAt ranks node with
    | none => buckets
    | some rank => buckets.setIfInBounds rank (node :: buckets.getD rank []))
    (Array.replicate graph.size ([] : List Nat))
  let order := buckets.foldl (fun order bucket => order ++ bucket.toArray) (#[] : Array Nat)
  let refined := refineParents graph ranks exits order (graph.size + 1) seeded
  let hints := candidateParents p
  (List.range graph.size).toArray.map (fun node =>
    match refined.getD node none with
    | some parent => parent
    | none => hints.getD node node)

structure ConstructedRegions where
  index : EscapeIndex
  conservativeFallback : Bool
  deriving Repr

/-- No parent array enters from outside this function. Merge operands supply candidates only;
    they cannot bypass the graph-derived success and edge checks. The fallback is explicit so
    later occurrence analysis cannot mistake coarse ancestry for complete control dependence. -/
def constructRegions? (p : SemanticProgram) : Option ConstructedRegions := do
  if !decodedControlGraphWellFormedB p then none else pure ()
  let graph := decodedControlGraph p
  let ranks ← successRanks? graph
  let candidate : EscapeIndex := ⟨candidateParents p, ranks⟩
  if escapeIndexChecks graph candidate then some ⟨candidate, false⟩ else
    let fallback : EscapeIndex := ⟨functionReturnParents p, ranks⟩
    if escapeIndexChecks graph fallback then some ⟨fallback, true⟩ else none

end LambdaSigil.Combined.OccurrenceRegionConstruction
