import LambdaSigil.DecodedOccurrence
import LambdaSigil.OccurrenceTransferConstructionSecurity

/-!
# Checked components of decoded local occurrence analysis

These theorems connect actual operand-derived selector labels with the internally constructed
region/frontier checks. They do not claim a call simulation or a Public relational result, and
are not production acceptance corollaries. In-memory semantic inputs may still have arbitrary
label tables; the existing source-decoder theorem supplies derived labels at the wire boundary.
-/

namespace LambdaSigil.Combined.DecodedOccurrenceSecurity

open Semantic OccurrenceRegions OccurrenceRegionConstruction OccurrenceTransfer
open OccurrenceTransferConstruction OccurrenceTransferConstructionSecurity DecodedOccurrence

theorem controlling_label_has_exact_operand {p : SemanticProgram} {instruction : Instruction}
    {label : Label} (h : controllingValueLabel? p instruction = some label) :
    ∃ operand, instructionOperandAt? p instruction 0 = some operand ∧ operand.kind = 0 ∧
      p.valueLabels[operand.value.toNat]? = some label := by
  unfold controllingValueLabel? at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨operand, hoperand, h⟩ := h
  split at h
  · cases h
  · rename_i hkind
    exact ⟨operand, hoperand, by simpa using hkind, h⟩

theorem analysis_has_constructed_components {p : SemanticProgram} {analysis : Analysis}
    (h : analyze? p = some analysis) :
    semanticProgramWellFormedB p = true ∧
      selectorLabels? p = some analysis.selectors ∧
      constructRegions? p = some analysis.regions ∧
      constructFrontiers? (decodedControlGraph p) analysis.regions.index analysis.selectors
        (functionReturnParents p) = some analysis.frontiers := by
  unfold analyze? at h
  simp only [bind] at h
  split at h
  · cases h
  · rename_i hwell
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨selectors, hselectors, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨regions, hregions, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨frontiers, hfrontiers, h⟩ := h
    cases h
    exact ⟨by simpa using hwell, hselectors, hregions, hfrontiers⟩

theorem analyzed_frontiers_satisfy_transfer {p : SemanticProgram} {analysis : Analysis}
    (h : analyze? p = some analysis) :
    transferChecks (decodedControlGraph p) analysis.regions.index analysis.selectors
      analysis.frontiers = true :=
  constructed_frontiers_checked (analysis_has_constructed_components h).2.2.2

end LambdaSigil.Combined.DecodedOccurrenceSecurity
