import LambdaSigil.RankedDecodedOccurrence
import LambdaSigil.PriorityOccurrenceSecurity

/-!
# Returned obligations for the ranked decoded occurrence candidate

These are unary extraction/transfer facts. In particular, no assumed relational policy or
future-output equality appears in them. The actual source-to-semantic label derivation and the
balanced call/return proof remain separate obligations before any production Public claim.
-/

namespace LambdaSigil.Combined.RankedDecodedOccurrenceSecurity

open Semantic OccurrenceRegions OccurrenceRegionConstruction OccurrenceTransfer
open RankedDecodedOccurrence

theorem constructed_regions_are_checked {p : SemanticProgram} {regions : ConstructedRegions}
    (h : RankedDecodedOccurrence.constructRegions? p = some regions) :
    decodedControlGraphWellFormedB p = true ∧
      escapeIndexChecks (decodedControlGraph p) regions.index = true := by
  unfold RankedDecodedOccurrence.constructRegions? at h
  simp only [bind] at h
  split at h
  · cases h
  · rename_i hwell
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨ranks, _, h⟩ := h
    split at h
    · rename_i intervals hintervals
      cases h
      exact ⟨by simpa using hwell,
        IntervalEscapeSecurity.returned_implies_escape_index_checks hintervals⟩
    · split at h
      · rename_i intervals hintervals
        cases h
        exact ⟨by simpa using hwell,
          IntervalEscapeSecurity.returned_implies_escape_index_checks hintervals⟩
      · rw [Option.bind_eq_some_iff] at h
        obtain ⟨intervals, hintervals, h⟩ := h
        cases h
        exact ⟨by simpa using hwell,
          IntervalEscapeSecurity.returned_implies_escape_index_checks hintervals⟩

theorem analysis_has_constructed_components {p : SemanticProgram}
    {analysis : DecodedOccurrence.Analysis} (h : analyze? p = some analysis) :
    semanticProgramWellFormedB p = true ∧
      DecodedOccurrence.selectorLabels? p = some analysis.selectors ∧
      RankedDecodedOccurrence.constructRegions? p = some analysis.regions ∧
      PriorityOccurrence.constructFrontiers? (decodedControlGraph p) analysis.regions.index
        analysis.selectors = some analysis.frontiers := by
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

theorem analyzed_frontiers_satisfy_transfer {p : SemanticProgram}
    {analysis : DecodedOccurrence.Analysis} (h : analyze? p = some analysis) :
    transferChecks (decodedControlGraph p) analysis.regions.index analysis.selectors
      analysis.frontiers = true :=
  PriorityOccurrenceSecurity.constructed_frontiers_are_checked
    (analysis_has_constructed_components h).2.2.2

theorem analyzed_invocation_components {p : SemanticProgram}
    {result : OccurrenceInvocation.InvocationAnalysis}
    (h : analyzeInvocations? p = some result) :
    analyze? p = some result.localAnalysis ∧
      (∃ plan, OccurrenceInvocation.invocationPlan? p result.localAnalysis.frontiers = some plan ∧
        result.labels = OccurrenceInvocation.computeInvocationLabels p plan) ∧
      OccurrenceInvocation.invocationChecks p result.localAnalysis.frontiers result.labels = true := by
  unfold analyzeInvocations? at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨localAnalysis, hlocal, h⟩ := h
  split at h
  · cases h
  · rw [Option.bind_eq_some_iff] at h
    obtain ⟨plan, hplan, h⟩ := h
    split at h
    · cases h
      exact ⟨hlocal, ⟨plan, hplan, rfl⟩, by assumption⟩
    · cases h

end LambdaSigil.Combined.RankedDecodedOccurrenceSecurity
