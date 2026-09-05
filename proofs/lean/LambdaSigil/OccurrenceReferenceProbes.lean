import LambdaSigil.OccurrenceReference
import LambdaSigil.PublicRegionProbes
import LambdaSigil.V8OccurrenceProbes

/-!
# Decoded counterexamples against the occurrence reference classifier

The adapter below extracts actual instruction targets from a decoded single-function raw program.
It never reads merge markers or infers a backedge from numeric ordering. Calls are deliberately
unsupported in this adapter: dropping their effects would not be an honest normalization. The
separate normalized call witnesses in `OccurrenceReference` cover the invocation-summary problem.

This remains test-only evidence. V8's labels are used to reproduce its concrete counterexamples,
not asserted to solve the new v9 semantic-dataflow judgment. No production v9 acceptance theorem
or source-to-CFG correspondence is established here.
-/

namespace LambdaSigil.Combined.OccurrenceReferenceProbes

open Semantic OccurrenceReference

def instructionSuccessors? (p : SemanticProgram) (pc : Nat) (i : Instruction) :
    Option (List Nat) :=
  match i.op with
  | .call | .closure => none
  | .output | .halt | .abortiveEffect => some []
  | .trap => if i.operandCount == 0 then some [] else some [pc + 1]
  | .branch | .loop | .range => some [i.target.toNat, i.alternate.toNat]
  | .dispatch => if i.operandCount == 2 then some [i.target.toNat]
      else some [i.target.toNat, i.alternate.toNat]
  | .jump => some [i.target.toNat]
  | .scalar | .aggregate | .project | .actorBoundary | .stateRead | .stateWrite
  | .slotNew | .slotPut | .slotTake | .effect | .ffi | .allocation
  | .address | .index | .capMint | .capRestrict | .capSplit | .capDraw | .capExercise
  | .release | .releaseCT | .ctEq | .ctSelect | .ctLt | .divRem | .stringCompare =>
      if pc + 1 < p.instructions.size then some [pc + 1] else none

def selectorLabel (p : SemanticProgram) (i : Instruction) : Label :=
  match i.op with
  | .branch | .loop | .range | .dispatch =>
      match (valueOperandCells p i).head? with
      | some cell => labelAt p.valueLabels cell
      | none => .pub
  | .scalar | .aggregate | .project | .jump | .call | .closure | .actorBoundary
  | .stateRead | .stateWrite | .slotNew | .slotPut | .slotTake | .effect
  | .abortiveEffect | .ffi | .allocation | .address | .index | .capMint | .capRestrict
  | .capSplit | .capDraw | .capExercise | .release | .releaseCT | .ctEq | .ctSelect
  | .ctLt | .divRem | .stringCompare | .output | .trap | .halt => .pub

def singleFunctionGraph? (p : SemanticProgram) : Option Graph := do
  if p.functions.size != 1 then none else pure ()
  let sites := p.instructions.toList.map (·.id)
  if sites.eraseDups.length != sites.length then none else pure ()
  let function ← p.functions[0]?
  if function.firstInstruction != 0 then none else pure ()
  let mut successors := #[]
  let mut exits := []
  let mut selectors := #[]
  for pc in List.range p.instructions.size do
    let i ← p.instructions[pc]?
    if i.functionId != function.id then none else pure ()
    let targets ← instructionSuccessors? p pc i
    successors := successors.push targets
    if i.op == .output || i.op == .halt then exits := pc :: exits
    selectors := selectors.push (selectorLabel p i)
  let graph : Graph := ⟨successors, exits, selectors⟩
  if graph.wellFormed then some graph else none

def classifySites (p : SemanticProgram) (sites : List UInt32) : Bool :=
  if sites.isEmpty || sites.eraseDups.length != sites.length then false else
  match singleFunctionGraph? p with
  | none => false
  | some graph =>
      let actions := (List.range p.instructions.size).filterMap fun pc => do
        let i ← p.instructions[pc]?
        if sites.contains i.id then some (⟨pc, .pub, []⟩ : Action) else none
      /- Missing/duplicate declarations must not turn a requested check into an empty pass. -/
      actions.length == sites.length && sites.length > 0 &&
        classify #[⟨graph, actions, []⟩]

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem decoded_loop_header_reference_rejects :
    classifySites PublicRegionProbes.loopHeaderProgram [8] = false := by decide +kernel

theorem decoded_loop_continuation_reference_accepts :
    classifySites PublicRegionProbes.loopHeaderProgram [31] = true := by decide +kernel

theorem decoded_acyclic_backward_escape_reference_rejects :
    classifySites V8OccurrenceProbes.acyclicBackwardEscapeProgram [12, 21] = false := by
  decide +kernel

theorem omitted_occurrence_site_reference_rejects :
    classifySites PublicRegionProbes.loopHeaderProgram [9000] = false := by decide +kernel

theorem empty_occurrence_manifest_reference_rejects :
    classifySites PublicRegionProbes.loopHeaderProgram [] = false := by decide +kernel

theorem duplicate_occurrence_manifest_reference_rejects :
    classifySites PublicRegionProbes.loopHeaderProgram [31, 31] = false := by decide +kernel

private def duplicatedInstructionSites : SemanticProgram :=
  let scalar : Instruction :=
    { op := .scalar, id := 31, functionId := 1, blockId := 1, destination := 0,
      firstOperand := 0, operandCount := 0, target := 1, resultLabel := .pub, aux := 0 }
  { functions := #[{ id := 1, entry := 1, firstInstruction := 0, instructionCount := 2 }],
    instructions := #[scalar, { scalar with op := .output, target := 2 }],
    operands := #[], valueLabels := #[] }

theorem duplicate_instruction_cannot_mask_missing_site :
    classifySites duplicatedInstructionSites [31, 9000] = false := by decide +kernel

theorem duplicate_instruction_cannot_mask_duplicate_manifest :
    classifySites duplicatedInstructionSites [31, 31] = false := by decide +kernel

end LambdaSigil.Combined.OccurrenceReferenceProbes
