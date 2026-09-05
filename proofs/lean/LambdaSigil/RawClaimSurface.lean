import LambdaSigil.CombinedSecurity
import LambdaSigil.PublicBisimulationSecurity

/-!
# Production raw-relational claim surface

Only the corollaries in this module are cited by the product claims ledger. Keeping their complete
signatures here prevents a downstream document or audit from silently retaining one of the former
sanitized-machine statements.
-/

namespace LambdaSigil.Combined.RawClaimSurface

open V9.OccurrenceDataflowInvocation V9.OccurrenceKernel
open V9.PublicExecutionSecurity V9.PublicBisimulationSecurity
open Semantic.PublicRegionSecurity

theorem secretCT_delimited_release_trace_equality {p : Program}
    (hverified : ProgramSafe p) {fuel : Nat} {left right : Semantic.State}
    (hwleft : Semantic.StateWellFormed (Semantic.semanticProgramOf p) left)
    (hwright : Semantic.StateWellFormed (Semantic.semanticProgramOf p) right)
    (hlow : Semantic.SecretCTLowEquivalent (Semantic.semanticProgramOf p) left right)
    (hrelease : Semantic.ReleaseAlignedRaw (Semantic.semanticProgramOf p) fuel left right) :
    Semantic.publicEvents
        (Semantic.runPrefix (Semantic.semanticProgramOf p) fuel left).events =
      Semantic.publicEvents
        (Semantic.runPrefix (Semantic.semanticProgramOf p) fuel right).events :=
  raw_secretCT_delimited_release_trace_equality_of_verified
    hverified hwleft hwright hlow hrelease

/-- Production Public noninterference over the occurrence-derived raw V9 machine.  The two fuel
    budgets are syntactically independent, both runs must complete successfully, every release
    occurrence must agree in the complete raw trace, and the conclusion retains the full Public
    projection plus the ordered Public output/boundary trace. -/
theorem public_delimited_release_noninterference
    (program : V9.Program) (analysis : Analysis) (root : UInt32)
    (leftFuel rightFuel : Nat) (left right : Semantic.State)
    (leftResult rightResult : Semantic.StepResult)
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    (hanalysis : analyze? program = some analysis)
    (hleftCut : VerifiedPublicCutPoint (rawSemanticProgram program analysis) root left)
    (hrightCut : VerifiedPublicCutPoint (rawSemanticProgram program analysis) root right)
    (hleftWellFormed : Semantic.StateWellFormed
      (rawSemanticProgram program analysis) left)
    (hrightWellFormed : Semantic.StateWellFormed
      (rawSemanticProgram program analysis) right)
    (hlow : Semantic.PublicLowEquivalent
      (rawSemanticProgram program analysis) left right)
    (hstreams : left.externalInputs = right.externalInputs)
    (hleftRun : SuccessfulRun (rawSemanticProgram program analysis)
      root leftFuel left leftResult)
    (hrightRun : SuccessfulRun (rawSemanticProgram program analysis)
      root rightFuel right rightResult)
    (hrelease : ReleaseSynchronization.releaseTrace leftResult.events =
      ReleaseSynchronization.releaseTrace rightResult.events) :
    PublicExecutionConclusion (rawSemanticProgram program analysis) leftResult rightResult :=
  raw_public_delimited_release_noninterference_of_v9_verified
    program analysis root leftFuel rightFuel left right leftResult rightResult
    hverified hanalysis hleftCut hrightCut hleftWellFormed hrightWellFormed hlow
    hstreams hleftRun hrightRun hrelease

end LambdaSigil.Combined.RawClaimSurface
