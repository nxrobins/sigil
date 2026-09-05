import LambdaSigil.OccurrenceRegionConstruction
import LambdaSigil.OccurrenceTransferConstruction

/-!
# Intraprocedural occurrence analysis from decoded operands

The selector table is derived here, not supplied by Rust or a caller. Missing, wrongly typed,
or out-of-bounds controlling operands reject rather than becoming Public. Region candidates,
success ranks and threshold frontiers are then constructed internally from actual CFG edges.

This is a local analysis component, not CSIR v9 acceptance. It uses the historical decoded
instruction vocabulary and does not approve actor subtypes, host contracts or call invocation
effects. The call edges still summarize a successful return; a Public theorem needs a separate
balanced call/return argument and invocation propagation. No production verifier calls this yet.
-/

namespace LambdaSigil.Combined.DecodedOccurrence

open Semantic OccurrenceRegions OccurrenceRegionConstruction
open OccurrenceTransfer OccurrenceTransferConstruction

def controllingValueLabel? (p : SemanticProgram) (instruction : Instruction) : Option Label := do
  let operand ← instructionOperandAt? p instruction 0
  if operand.kind != 0 then none else p.valueLabels[operand.value.toNat]?

/-- A flat dispatch wrapper has no selector; its child tests carry the actual decisions.
    All instruction cases are explicit so a new semantic constructor requires classification. -/
def selectorLabel? (p : SemanticProgram) (instruction : Instruction) : Option Label :=
  match instruction.op with
  | .branch =>
      if instruction.operandCount == 3 || instruction.operandCount == 4 then
        controllingValueLabel? p instruction else none
  | .loop | .range =>
      if instruction.operandCount == 3 then controllingValueLabel? p instruction else none
  | .dispatch =>
      if instruction.operandCount == 2 then some .pub
      else if instruction.operandCount == 3 || instruction.operandCount == 4 then
        controllingValueLabel? p instruction else none
  | .scalar | .aggregate | .project | .jump | .call | .closure | .actorBoundary
  | .stateRead | .stateWrite | .slotNew | .slotPut | .slotTake | .effect
  | .abortiveEffect | .ffi | .allocation | .address | .index | .capMint | .capRestrict
  | .capSplit | .capDraw | .capExercise | .release | .releaseCT | .ctEq | .ctSelect
  | .ctLt | .divRem | .stringCompare | .output | .trap | .halt => some .pub

def selectorLabels? (p : SemanticProgram) : Option (Array Label) := do
  let instructions ← p.instructions.mapM (selectorLabel? p)
  some (instructions ++ Array.replicate p.functions.size .pub)

structure Analysis where
  regions : ConstructedRegions
  selectors : Array Label
  frontiers : ThresholdFrontiers
  deriving Repr

/-- No derived-label, frontier, root or continuation certificate is an input. The stored labels
    are exactly those extracted from `p`; the source-decoder/least-solution layer separately
    determines how `p.valueLabels` was produced. This result alone authorizes no execution. -/
def analyze? (p : SemanticProgram) : Option Analysis := do
  if !semanticProgramWellFormedB p then none else pure ()
  let selectors ← selectorLabels? p
  let regions ← constructRegions? p
  let frontiers ← constructFrontiers? (decodedControlGraph p) regions.index selectors
    (functionReturnParents p)
  some ⟨regions, selectors, frontiers⟩

end LambdaSigil.Combined.DecodedOccurrence
