import LambdaSigil.DecodedOccurrenceSecurity
import LambdaSigil.PublicRegionProbes
import LambdaSigil.V8OccurrenceProbes

/-!
# Decoded occurrence witnesses and fail-closed operand mutants

These use the very same historical wire programs as the native/raw counterexamples. A successful
local analysis is not security acceptance: their Public actions are assigned private occurrence
influence and must subsequently be refused by the future v9 policy gate.
-/

namespace LambdaSigil.Combined.DecodedOccurrenceWitnesses

open Semantic OccurrenceTransfer DecodedOccurrence

private def occurrences? (p : SemanticProgram) : Option (Array Label) := do
  let result ← analyze? p
  some ((List.range p.instructions.size).toArray.map (localOccurrenceAt result.frontiers))

theorem historical_header_is_private_but_continuation_stays_public :
    occurrences? PublicRegionProbes.loopHeaderProgram =
      some #[.secret, .secret, .secret, .secret, .secret, .pub] := by decide +kernel

theorem historical_acyclic_escape_is_not_a_public_continuation :
    occurrences? V8OccurrenceProbes.acyclicBackwardEscapeProgram =
      some #[.pub, .secret, .secret, .secret, .secret] := by decide +kernel

private def selectorInstruction : Instruction :=
  PublicRegionProbes.loopHeaderProgram.instructions[3]'(by decide +kernel)

theorem loop_selector_comes_from_actual_decoded_value :
    selectorLabel? PublicRegionProbes.loopHeaderProgram selectorInstruction = some .secret := by
  decide +kernel

theorem missing_loop_selector_is_not_defaulted_to_public :
    selectorLabel? PublicRegionProbes.loopHeaderProgram
      { selectorInstruction with operandCount := 0 } = none := by decide +kernel

private def changedSelector (kind : UInt8) (cell : UInt32) : SemanticProgram :=
  let p := PublicRegionProbes.loopHeaderProgram
  let position := selectorInstruction.firstOperand.toNat
  let operand := p.operands[position]!
  { p with operands := p.operands.setIfInBounds position { operand with kind, value := cell } }

theorem nonvalue_or_unbounded_selector_is_rejected :
    selectorLabel? (changedSelector 3 0) selectorInstruction = none ∧
      selectorLabel? (changedSelector 0 0xffffffff) selectorInstruction = none := by decide +kernel

theorem changed_selector_owner_is_rejected :
    let p := PublicRegionProbes.loopHeaderProgram
    let position := selectorInstruction.firstOperand.toNat
    let operand := p.operands[position]!
    selectorLabel? { p with
        operands := p.operands.setIfInBounds position { operand with owner := 0 } }
      selectorInstruction = none := by decide +kernel

end LambdaSigil.Combined.DecodedOccurrenceWitnesses
