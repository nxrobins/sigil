import LambdaSigil.DecodedOccurrenceSecurity
import LambdaSigil.OccurrenceTransferSecurity

/-!
# Successful-prefix coverage from decoded local analysis

The analysis result supplies the selector extraction and checked frontier construction; no
separate table certificate or checker premise is accepted here. This remains intraprocedural:
the CFG's call-to-continuation edge does not establish balanced invocation semantics, and this
prefix theorem neither authorizes execution nor proves Public noninterference. The source/wire
boundary separately establishes where the semantic program's value labels came from.
-/

namespace LambdaSigil.Combined.DecodedOccurrencePrefix

open Semantic OccurrenceRegions OccurrenceRegionSecurity OccurrenceTransfer
open OccurrenceTransferSecurity DecodedOccurrence DecodedOccurrenceSecurity

theorem analyzed_secret_controller_covers_successful_prefix
    {p : SemanticProgram} {analysis : Analysis} (hanalysis : analyze? p = some analysis)
    {controller arm target : Nat} {trace : List Nat}
    (hcontroller : controller < p.instructions.size)
    (hbranch : isControllerB (decodedControlGraph p) controller = true)
    (hselector : 2 ≤ (analysis.selectors.getD controller .pub).rank)
    (hedge : arm ∈ (decodedControlGraph p).successors.getD controller [])
    (hpath : ControlPath (decodedControlGraph p) arm target trace)
    (htarget : target < (decodedControlGraph p).size)
    (hcompletion : ∃ suffix, SuccessfulPath (decodedControlGraph p) target suffix)
    (havoid : analysis.regions.index.parentAt controller ∉ trace) :
    carriesB analysis.regions.index analysis.frontiers.secretLane target
      (analysis.regions.index.parentAt controller) = true ∧
      (stopAt analysis.frontiers.secretLane target).isSome = true := by
  have hchecks := analyzed_frontiers_satisfy_transfer hanalysis
  simp only [transferChecks, Bool.and_eq_true] at hchecks
  have hcontrollerGraph : controller < (decodedControlGraph p).size := by
    simp only [ControlGraph.size, decodedControlGraph, Array.size_append, Array.size_mapIdx,
      Array.size_replicate]
    omega
  have hactive : controllerActiveB (decodedControlGraph p) analysis.selectors
      analysis.frontiers.secretLane 2 controller = true := by
    simp only [controllerActiveB, hbranch, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl hselector
  exact ⟨checked_branch_covers_successful_prefix hchecks.1.1.1 hchecks.1.2
      hcontrollerGraph hactive hedge hpath htarget hcompletion havoid,
    checked_branch_prefix_lane_is_present hchecks.1.1.1 hchecks.1.2
      hcontrollerGraph hactive hedge hpath htarget hcompletion havoid⟩

end LambdaSigil.Combined.DecodedOccurrencePrefix
