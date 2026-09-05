import LambdaSigil.DecodedOccurrence
import LambdaSigil.PriorityOccurrence
import LambdaSigil.OccurrenceInvocation

/-!
# Decoded occurrence with checked intervals and rank-ordered frontiers

This replaces neither the historical verifier nor its raw semantics. It is the internal local
analysis candidate for v9: selectors come from actual operands, success ranks from actual CFG
edges, continuation candidates from decoded control, and every candidate is checked through the
shared interval index. No parent table or derived label enters from Rust. The older two-change
frontier constructor and parent-walk checker are not executed on this path.

An invalid candidate uses the explicit function-return fallback. That conservative choice is
visible in the result and still needs corpus precision qualification. This layer does not claim
complete postdominators, interprocedural occurrence safety, or Public noninterference.
-/

namespace LambdaSigil.Combined.RankedDecodedOccurrence

open Semantic OccurrenceRegions OccurrenceRegionConstruction OccurrenceTransfer

/-- Use the exact graph-derived success ranks with internally selected parent candidates. A
    successful interval construction checks the parent obligations rather than trusting merges.
    No historical ancestry walk is used by this candidate construction. The structural
    candidate is tried first, unchanged, so every program it already satisfies keeps its exact
    regions; only when it fails does the postdominator candidate computed from the actual
    control graph take over, so one early-returning branch, or a `match` whose arms all leave
    their loop, no longer forces the whole-program function-return fallback on every other
    controller. Every returned index is re-validated here; nothing is trusted from the
    construction. -/
def constructRegions? (p : SemanticProgram) : Option ConstructedRegions := do
  if !decodedControlGraphWellFormedB p then none else pure ()
  let graph := decodedControlGraph p
  let ranks ← successRanks? graph
  let structural : EscapeIndex := ⟨candidateParents p, ranks⟩
  match IntervalEscapeChecks.checkedIntervals? graph structural with
  | some _ => some ⟨structural, false⟩
  | none =>
      let postdominators : EscapeIndex := ⟨postdominatorParents p graph ranks, ranks⟩
      match IntervalEscapeChecks.checkedIntervals? graph postdominators with
      | some _ => some ⟨postdominators, false⟩
      | none =>
          let fallback : EscapeIndex := ⟨functionReturnParents p, ranks⟩
          let _ ← IntervalEscapeChecks.checkedIntervals? graph fallback
          some ⟨fallback, true⟩

/-- The same result layout permits independent comparison with the retained old constructor.
    This does not make its acceptance theorem or precision assumptions interchangeable. -/
def analyze? (p : SemanticProgram) : Option DecodedOccurrence.Analysis := do
  if !semanticProgramWellFormedB p then none else pure ()
  let selectors ← DecodedOccurrence.selectorLabels? p
  let regions ← constructRegions? p
  let frontiers ← PriorityOccurrence.constructFrontiers? (decodedControlGraph p)
    regions.index selectors
  some ⟨regions, selectors, frontiers⟩

/-- Compose local occurrence with the existing actual-call extraction and bounded invocation
    worklist. The independent call-site and dynamic-target checks are retained. As before, the
    all-functions dynamic-target superset is conservative and needs precision qualification. -/
def analyzeInvocations? (p : SemanticProgram) : Option OccurrenceInvocation.InvocationAnalysis := do
  let localAnalysis ← analyze? p
  if !OccurrenceInvocation.functionLayoutB p then none else pure ()
  let plan ← OccurrenceInvocation.invocationPlan? p localAnalysis.frontiers
  let labels := OccurrenceInvocation.computeInvocationLabels p plan
  if OccurrenceInvocation.invocationChecks p localAnalysis.frontiers labels then
    some ⟨localAnalysis, labels⟩ else none

end LambdaSigil.Combined.RankedDecodedOccurrence
