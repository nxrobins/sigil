import LambdaSigil.OccurrenceTransfer
import LambdaSigil.IntervalEscapeChecks

/-!
# Rank-ordered exact-stop occurrence construction

All private-selector arm offers are bucketed by their checked continuation's success rank before
work starts. A vertex is settled on its first pop, not its first enqueue. Its outgoing adjacency
is consumed once, carrying the same original controller; no stop is invented or widened to a
function return. A carried proper ancestor already covers an occurrence-activated controller's
own parent, so carrying is sufficient without adding a lower-priority dynamic seed.

One bucket advance costs one step. Initial seed offers are bounded by the edge count, and each
outgoing edge is consumed at most once. The work budget is therefore vertices plus twice edges,
with shared linear-space tables/lists rather than independent walks for every controller.
The independent final frontier check remains mandatory. This module is not production acceptance
or an end-to-end performance claim about the older region-candidate constructor.
-/

namespace LambdaSigil.Combined.PriorityOccurrence

open OccurrenceRegions OccurrenceTransfer

structure Offer where
  controller : Nat
  node : Nat
  deriving Repr, BEq, DecidableEq

def edgeCount (adjacency : Array (List Nat)) : Nat :=
  adjacency.foldl (fun total successors => total + successors.length) 0

structure Seeds where
  buckets : Array (List Offer)
  failed : Bool := false
  deriving Repr

def seedSource (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (threshold source : Nat) (state : Seeds) : Seeds :=
  if !isControllerB graph source || threshold > (selectors.getD source .pub).rank ||
      !index.liveB source then state else
  match index.rankAt (index.parentAt source) with
  | none => { state with failed := true }
  | some rank =>
      if rank ≥ state.buckets.size then { state with failed := true } else
      let offers := (graph.successors.getD source []).map (fun node => ⟨source, node⟩)
      { state with
        buckets := state.buckets.setIfInBounds rank (offers ++ state.buckets.getD rank []) }

def seedBuckets (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (threshold : Nat) : Seeds :=
  (List.range graph.size).foldl (fun state source =>
    seedSource graph index selectors threshold source state)
    { buckets := Array.replicate graph.size [] }

structure WorkState where
  frontier : Frontier
  unscanned : Array (List Nat)
  buckets : List (List Offer)
  pending : List Offer := []
  failed : Bool := false
  deriving Repr

def finishedB (state : WorkState) : Bool :=
  state.failed || (state.pending.isEmpty && state.buckets.isEmpty)

/-- Consuming adjacency is a resource accounting device as well as an implementation guard:
    even malformed duplicate offers cannot cause the same edge list to be expanded twice. -/
def advance (index : EscapeIndex) (state : WorkState) : WorkState :=
  if state.failed then state else
  match state.pending with
  | [] =>
      match state.buckets with
      | [] => state
      | bucket :: buckets => { state with buckets, pending := bucket }
  | offer :: pending =>
      let stop := index.parentAt offer.controller
      if offer.node ≥ state.frontier.size || offer.node ≥ state.unscanned.size ||
          stop ≥ state.frontier.size then { state with failed := true } else
      if !index.liveB offer.node || offer.node == stop then { state with pending } else
      if !index.liveB stop then { state with failed := true } else
      if (stopAt state.frontier offer.node).isSome then { state with pending } else
      let next := (state.unscanned.getD offer.node []).map
        (fun node => { offer with node })
      { state with
        frontier := state.frontier.setIfInBounds offer.node (some stop)
        unscanned := state.unscanned.setIfInBounds offer.node []
        pending := next ++ pending }

def run (index : EscapeIndex) : Nat → WorkState → WorkState
  | 0, state => state
  | fuel + 1, state =>
      if finishedB state then state else run index fuel (advance index state)

def initialState (graph : ControlGraph) (seeds : Seeds) : WorkState :=
  { frontier := Array.replicate graph.size none
    unscanned := graph.successors
    buckets := seeds.buckets.toList
    failed := seeds.failed }

def compute (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (threshold : Nat) : WorkState :=
  run index (graph.size + 2 * edgeCount graph.successors)
    (initialState graph (seedBuckets graph index selectors threshold))

/-- This component checks its actual output. The independent region-index obligation is
    supplied by the checked-interval wrapper, not assumed from a merge operand. -/
def buildFrontier? (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (threshold : Nat) : Option Frontier :=
  let result := compute graph index selectors threshold
  if result.failed || !result.pending.isEmpty || !result.buckets.isEmpty then none else
  if frontierChecks graph index selectors threshold result.frontier then some result.frontier else none

/-- Parent soundness is checked through internally constructed constant-time interval queries.
    No old ancestry-walk checker or old region-candidate constructor is executed here. -/
def constructFrontiers? (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label) :
    Option ThresholdFrontiers := do
  let _ ← IntervalEscapeChecks.checkedIntervals? graph index
  let internalLane ← buildFrontier? graph index selectors 1
  let secretLane ← buildFrontier? graph index selectors 2
  let secretCTLane ← buildFrontier? graph index selectors 3
  some ⟨internalLane, secretLane, secretCTLane⟩

end LambdaSigil.Combined.PriorityOccurrence
