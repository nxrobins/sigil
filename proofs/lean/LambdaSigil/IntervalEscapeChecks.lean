import LambdaSigil.AncestorIntervals

/-!
# Shared interval and exit-mask escape checks

The parent intervals and successful-exit mask are constructed once. The remaining checks scan
vertices, CFG edges, and exits without parent walks or per-vertex exit-list membership scans.
Malformed construction or any failed local obligation rejects the whole result. This internal
entry point does not change the historical checker, wire format, or production acceptance.

The interval constructor additionally rejects malformed dead parent links and duplicate roots;
no totality or identical rejection-domain claim is made. Returned results imply every historical
escape obligation. Proofs and executable mutation witnesses live in IntervalEscapeSecurity.
-/

namespace LambdaSigil.Combined.IntervalEscapeChecks

open OccurrenceRegions AncestorIntervals

def successJustifiedWithMaskB (graph : ControlGraph) (forest : EscapeIndex)
    (exits : Array Bool) (node : Nat) : Bool :=
  match forest.rankAt node with
  | none => true
  | some rank => exits.getD node false ||
      (graph.successors.getD node []).any (rankDecreasesB forest rank)

def parentRankedWithMaskB (graph : ControlGraph) (forest : EscapeIndex)
    (exits : Array Bool) (node : Nat) : Bool :=
  match forest.rankAt node with
  | none => true
  | some rank => exits.getD node false ||
      (forest.parentAt node < graph.size && rankDecreasesB forest rank (forest.parentAt node))

def intervalEscapeChecks (graph : ControlGraph) (forest : EscapeIndex)
    (intervals : IntervalIndex) : Bool :=
  let exits := rootMask graph.size graph.successfulExits
  graph.wellFormedB && forest.parent.size == graph.size &&
    forest.successRank.size == graph.size &&
    graph.successfulExits.all (fun exit => forest.parentAt exit == exit &&
      forest.rankAt exit == some 0) &&
    (List.range graph.size).all (fun node =>
      successJustifiedWithMaskB graph forest exits node &&
      parentRankedWithMaskB graph forest exits node &&
      (graph.successors.getD node []).all (AncestorIntervals.edgeParentB forest intervals node))

/-- Intervals are internal, not an accepted certificate. All edge queries use the same checked
    index, and no partially checked result is returned on construction or obligation failure. -/
def checkedIntervals? (graph : ControlGraph) (forest : EscapeIndex) : Option IntervalIndex := do
  let intervals ← AncestorIntervals.construct? forest graph.successfulExits
  if intervalEscapeChecks graph forest intervals then some intervals else none

end LambdaSigil.Combined.IntervalEscapeChecks
