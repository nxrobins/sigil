import LambdaSigil.OccurrenceTransfer

/-!
# Two-change conservative frontier construction

An empty lane accepts its first outstanding stop. A later offer already covered by that stop's
rank is ignored; a conflicting lower-rank offer widens directly to the node's live rank-zero
function return. No lane is reset by an inactive incoming edge. Each slot therefore has only
two possible strict changes, rather than walking all ancestors at successive joins.

The work queue has exactly twice the vertex count in slots. Every strict change enqueues once;
unfinished work, overflow, invalid roots, or failed local postchecks reject the construction.
This is an internal candidate constructor, not production acceptance. The existing checked-parent
precondition still has its separately documented performance boundary. Selector derivation and
interprocedural invocation influence are not supplied by this module.
-/

namespace LambdaSigil.Combined.OccurrenceTransferConstruction

open OccurrenceRegions OccurrenceTransfer

def chooseStop (index : EscapeIndex) (fallback incoming : Nat) : Option Nat → Option Nat
  | none => some incoming
  | some current =>
      if stopRankLeB index current incoming then some current else some fallback

structure FrontierQueue where
  frontier : Frontier
  queue : Array Nat
  head : Nat := 0
  tail : Nat := 0
  failed : Bool := false
  deriving Repr

/-- A stopped contribution is a no-op, never a command to clear another active contribution.
    Bad endpoints and invalid live stops fail closed before any partial result can be returned. -/
def offer (index : EscapeIndex) (roots : Array Nat) (state : FrontierQueue)
    (node incoming : Nat) : FrontierQueue :=
  if node ≥ state.frontier.size || node ≥ roots.size then { state with failed := true }
  else if !index.liveB node || node == incoming then state
  else if !index.liveB incoming then { state with failed := true }
  else
    let fallback := roots.getD node node
    if index.rankAt fallback != some 0 then { state with failed := true } else
    let old := stopAt state.frontier node
    let next := chooseStop index fallback incoming old
    if next == old then state else
    if state.tail ≥ state.queue.size then { state with failed := true } else
    { state with
      frontier := state.frontier.setIfInBounds node next
      queue := state.queue.setIfInBounds state.tail node
      tail := state.tail + 1 }

def propagateVertex (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (roots : Array Nat) (threshold source : Nat) (state : FrontierQueue) : FrontierQueue :=
  let active := controllerActiveB graph selectors state.frontier threshold source
  let stop := stopAt state.frontier source
  (graph.successors.getD source []).foldl (fun next target =>
    let carried := match stop with
      | none => next
      | some outstanding => offer index roots next target outstanding
    if active then offer index roots carried target (index.parentAt source) else carried) state

def frontierWork (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (roots : Array Nat) (threshold : Nat) : Nat → FrontierQueue → FrontierQueue
  | 0, state => state
  | fuel + 1, state =>
      if state.failed || state.head ≥ state.tail then state else
      let source := state.queue.getD state.head 0
      if source ≥ graph.size then { state with failed := true } else
      let next := propagateVertex graph index selectors roots threshold source
        { state with head := state.head + 1 }
      frontierWork graph index selectors roots threshold fuel next

def computeFrontier (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (roots : Array Nat) (threshold : Nat) : FrontierQueue :=
  let initial : FrontierQueue :=
    { frontier := Array.replicate graph.size none, queue := Array.replicate (2 * graph.size) 0 }
  let seeded := (List.range graph.size).foldl (fun state source =>
    if isControllerB graph source &&
        threshold ≤ (selectors.getD source .pub).rank then
      (graph.successors.getD source []).foldl (fun next target =>
        offer index roots next target (index.parentAt source)) state
    else state) initial
  frontierWork graph index selectors roots threshold (2 * graph.size) seeded

def buildFrontier? (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (roots : Array Nat) (threshold : Nat) : Option Frontier :=
  let result := computeFrontier graph index selectors roots threshold
  if result.failed || result.head != result.tail then none else
  if frontierChecks graph index selectors threshold result.frontier then some result.frontier else none

/-- Roots are internal per-function return lookups in the intended decoded-graph caller. The
    local soundness proof only needs live rank zero, and therefore permits conservative roots
    unrelated to a controller's exact continuation. Wrong roots can overtaint, never erase a
    checked prefix. There is no accepted external frontier or root certificate. -/
def constructFrontiers? (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (roots : Array Nat) : Option ThresholdFrontiers := do
  if !escapeIndexChecks graph index || selectors.size != graph.size || roots.size != graph.size ||
      !(roots.all (fun root => root < graph.size && index.rankAt root == some 0)) then none
    else pure ()
  let internalLane ← buildFrontier? graph index selectors roots 1
  let secretLane ← buildFrontier? graph index selectors roots 2
  let secretCTLane ← buildFrontier? graph index selectors roots 3
  some ⟨internalLane, secretLane, secretCTLane⟩

end LambdaSigil.Combined.OccurrenceTransferConstruction
