import LambdaSigil.RankedDecodedOccurrenceSecurity
import LambdaSigil.DecodedOccurrenceWitnesses

/-!
# Raw operand/CFG probes for rank-ordered decoded occurrence

The historical loop-header bytes remain accepted by the old verifier, while the acyclic escape
is now rejected by it (see `V8OccurrenceProbes`). These witnesses establish the fixtures' derived
local occurrence influence, not acceptance by an unfinished v9 policy checker.
-/

namespace LambdaSigil.Combined.RankedDecodedOccurrenceWitnesses

open Semantic OccurrenceTransfer RankedDecodedOccurrence

private def occurrences? (p : SemanticProgram) : Option (Array Label) := do
  let result ← analyze? p
  some ((List.range p.instructions.size).toArray.map (localOccurrenceAt result.frontiers))

theorem historical_header_is_private_and_exit_public :
    occurrences? PublicRegionProbes.loopHeaderProgram =
      some #[.secret, .secret, .secret, .secret, .secret, .pub] := by decide +kernel

theorem historical_backward_escape_is_private :
    occurrences? V8OccurrenceProbes.acyclicBackwardEscapeProgram =
      some #[.pub, .secret, .secret, .secret, .secret] := by decide +kernel

private def instruction (op : InstrOp) (id first count target alternate merge : UInt32) :
    Instruction :=
  { op, id, functionId := 1, blockId := id, destination := 0,
    firstOperand := first, operandCount := count, target, alternate, merge,
    resultLabel := .pub, aux := 0 }

private def operand (owner position value : UInt32) (kind : UInt8 := 0) : OperandRecord :=
  ⟨owner, position, value, 0, kind⟩

private def nestedDiamond : SemanticProgram :=
  { functions := #[{ id := 1, entry := 1, firstInstruction := 0, instructionCount := 7 }]
    instructions := #[instruction .branch 1 0 3 1 4 5,
      instruction .branch 2 3 3 2 3 3, instruction .scalar 3 6 0 3 0 0,
      instruction .jump 4 6 0 5 0 0, instruction .scalar 5 6 0 5 0 0,
      instruction .effect 6 6 0 6 0 0, instruction .output 7 6 0 7 0 0]
    operands := #[operand 1 0 1, operand 1 1 1 1, operand 1 2 4 1,
      operand 2 0 1, operand 2 1 2 1, operand 2 2 3 1]
    valueLabels := #[.pub, .secret] }

/-- This is the old two-change constructor's exact precision counterexample. The new path
    derives the same checked parent candidates but does not widen the outer merge to return. -/
theorem nested_branches_restore_actual_checked_continuation :
    (analyze? nestedDiamond).map (fun result =>
      (result.regions.conservativeFallback, result.regions.index.parentAt 0,
        result.regions.index.parentAt 1, localOccurrenceAt result.frontiers 5)) =
      some (false, 5, 3, .pub) ∧
    (DecodedOccurrence.analyze? nestedDiamond).map (fun result =>
      localOccurrenceAt result.frontiers 5) = some .secret := by decide +kernel

theorem malformed_selector_cannot_become_public :
    (analyze? { nestedDiamond with operands :=
      nestedDiamond.operands.setIfInBounds 0 (operand 1 0 1 3) }).isNone = true ∧
    (analyze? { nestedDiamond with operands :=
      nestedDiamond.operands.setIfInBounds 0 (operand 0 0 1) }).isNone = true := by
  decide +kernel

theorem malformed_target_and_cross_function_fallthrough_refuse :
    (analyze? { nestedDiamond with instructions :=
      nestedDiamond.instructions.setIfInBounds 0 (instruction .branch 1 0 3 99 4 5) }).isNone = true ∧
    (analyze? { nestedDiamond with instructions :=
      nestedDiamond.instructions.setIfInBounds 2 { (instruction .scalar 3 6 0 3 0 0) with functionId := 2 } }).isNone = true := by
  decide +kernel

/-- Function one returns from one arm of its branch, so that branch's only in-function
    postdominator is the return and its structural merge hint (the continuing arm) can never
    satisfy the parent obligations. Function two is an ordinary diamond whose merge does. -/
private def earlyReturnSibling : SemanticProgram :=
  { functions := #[{ id := 1, entry := 1, firstInstruction := 0, instructionCount := 4 },
      { id := 2, entry := 5, firstInstruction := 4, instructionCount := 7 }]
    instructions := #[instruction .branch 1 0 3 1 2 2,
      instruction .output 2 3 0 2 0 0, instruction .scalar 3 3 0 3 0 0,
      instruction .output 4 3 0 4 0 0,
      { instruction .branch 5 3 3 5 7 9 with functionId := 2 },
      { instruction .scalar 6 6 0 6 0 0 with functionId := 2 },
      { instruction .jump 7 6 0 9 0 0 with functionId := 2 },
      { instruction .scalar 8 6 0 8 0 0 with functionId := 2 },
      { instruction .jump 9 6 0 9 0 0 with functionId := 2 },
      { instruction .scalar 10 6 0 10 0 0 with functionId := 2 },
      { instruction .output 11 6 0 11 0 0 with functionId := 2 }]
    operands := #[operand 1 0 1, operand 1 1 1 1, operand 1 2 2 1,
      operand 5 0 2, operand 5 1 5 1, operand 5 2 7 1]
    valueLabels := #[.pub, .secret, .secret] }

/-- The structural candidate fails its interval obligations because of function one alone, and
    the older all-or-nothing construction therefore fell back to function-return parents for the
    whole program, leaving function two's continuation after its diamond under Secret occurrence.
    The postdominator candidate keeps that continuation Public while function one's continuing
    arm correctly stays under its early-returning branch. -/
theorem early_return_elsewhere_keeps_sibling_diamond_continuation_public :
    (analyze? earlyReturnSibling).map (fun result =>
      (result.regions.conservativeFallback, localOccurrenceAt result.frontiers 9,
        localOccurrenceAt result.frontiers 2)) = some (false, .pub, .secret) ∧
    (DecodedOccurrence.analyze? earlyReturnSibling).map (fun result =>
      (result.regions.conservativeFallback, localOccurrenceAt result.frontiers 9)) =
        some (true, .secret) ∧
    ((OccurrenceRegionConstruction.successRanks?
        (OccurrenceRegions.decodedControlGraph earlyReturnSibling)).map fun ranks =>
      (IntervalEscapeChecks.checkedIntervals?
        (OccurrenceRegions.decodedControlGraph earlyReturnSibling)
        ⟨OccurrenceRegionConstruction.candidateParents earlyReturnSibling, ranks⟩).isNone) =
      some true := by
  decide +kernel

end LambdaSigil.Combined.RankedDecodedOccurrenceWitnesses
