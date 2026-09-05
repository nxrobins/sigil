import LambdaSigil.OccurrenceRegions

/-!
# Shared conservative occurrence frontiers

Each confidentiality threshold has one optional outstanding stop per CFG vertex. Local edge
checks preserve that frontier until its exact stop; joins may replace it by any live stop of
no greater success rank. The checked parent index makes this rank-only coarsening safe: before
an original continuation is reached, that continuation remains a checked ancestor of the current
vertex and therefore has strictly smaller rank. No per-controller CFG walk or ancestry list per
vertex participates in these local transfer checks.

These are internal analysis equations, not an externally accepted certificate or a production
security verdict. Selector derivation, construction precision, invocation transfer, and Public
preservation remain separate obligations. In particular, a function's synthetic return is not
automatically an observable root output. Proofs live in OccurrenceTransferSecurity.
-/

namespace LambdaSigil.Combined.OccurrenceTransfer

open OccurrenceRegions

abbrev Frontier := Array (Option Nat)

def stopAt (frontier : Frontier) (node : Nat) : Option Nat := frontier.getD node none

def stopRankLeB (index : EscapeIndex) (left right : Nat) : Bool :=
  match index.rankAt left, index.rankAt right with
  | some leftRank, some rightRank => leftRank ≤ rightRank
  | _, _ => false

def carriesB (index : EscapeIndex) (frontier : Frontier) (target originalStop : Nat) : Bool :=
  match stopAt frontier target with
  | none => false
  | some replacement => stopRankLeB index replacement originalStop

def isControllerB (graph : ControlGraph) (source : Nat) : Bool :=
  match graph.successors.getD source [] with
  | _ :: _ :: _ => true
  | _ => false

/-- An occurrence-controlled Public selector still introduces a controlled decision. This is
    separate from operand/data labels; it cannot be erased by a Public return-value contract. -/
def controllerActiveB (graph : ControlGraph) (selectors : Array Label)
    (frontier : Frontier) (threshold source : Nat) : Bool :=
  isControllerB graph source &&
    (threshold ≤ (selectors.getD source .pub).rank || (stopAt frontier source).isSome)

def frontierEdgeB (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (frontier : Frontier) (threshold source target : Nat) : Bool :=
  !index.liveB target ||
    ((match stopAt frontier source with
      | none => true
      | some stop => target == stop || carriesB index frontier target stop) &&
      (!controllerActiveB graph selectors frontier threshold source ||
        target == index.parentAt source || carriesB index frontier target (index.parentAt source)))

/-- This scan is linear in vertices and edges. A dead or out-of-bounds stop rejects; it cannot
    serve as a synchronization point. The separate escape check supplies sound parent ranks. -/
def frontierChecks (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (threshold : Nat) (frontier : Frontier) : Bool :=
  1 ≤ threshold && threshold ≤ 3 && selectors.size == graph.size &&
    frontier.size == graph.size &&
    (List.range graph.size).all (fun source =>
      (match stopAt frontier source with
       | none => true
       | some stop => stop < graph.size && index.liveB stop) &&
      (graph.successors.getD source []).all
        (frontierEdgeB graph index selectors frontier threshold source))

structure ThresholdFrontiers where
  internalLane : Frontier
  secretLane : Frontier
  secretCTLane : Frontier
  deriving Repr, Inhabited

def localOccurrenceAt (frontiers : ThresholdFrontiers) (node : Nat) : Label :=
  if (stopAt frontiers.secretCTLane node).isSome then .secretCT
  else if (stopAt frontiers.secretLane node).isSome then .secret
  else if (stopAt frontiers.internalLane node).isSome then .internal
  else .pub

/-- No policy or observation equality is an input. This checks graph-derived local obligations
    only; supplying an arbitrary table does not bypass the independently checked parent index.
    There is no production caller of this internal foundation. -/
def transferChecks (graph : ControlGraph) (index : EscapeIndex) (selectors : Array Label)
    (frontiers : ThresholdFrontiers) : Bool :=
  escapeIndexChecks graph index &&
    frontierChecks graph index selectors 1 frontiers.internalLane &&
    frontierChecks graph index selectors 2 frontiers.secretLane &&
    frontierChecks graph index selectors 3 frontiers.secretCTLane

end LambdaSigil.Combined.OccurrenceTransfer
