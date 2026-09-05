import LambdaSigil.OccurrenceActivation
import LambdaSigil.OccurrenceWire

/-!
# Activation storage against a compiler-produced v9 envelope

The fixture is emitted from the committed pure loop-header source by the Rust fixture generator.
This executable regression uses the actual v9 decoder and `semanticProgramOf`, including its
closure-summary allocation. It exercises a real decoded call and return declaration while making
explicit synthetic local-store mutations between them. It is not a complete execution, a security
acceptance witness, or a proof of source/machine correspondence.
-/

namespace LambdaSigil.Combined.OccurrenceActivationSourceChecks

open Semantic OccurrenceActivation

private def fixtureHex : String :=
  include_str ".." / "fixtures" / "csir-v9" / "accept-loop-header-pure.hex"

private def parseHex (text : String) : Option ByteArray := do
  let digits := text.toList.filter (fun c => !c.isWhitespace)
  if digits.length % 2 != 0 then none
  let mut bytes := ByteArray.empty
  let mut high : Option Nat := none
  for c in digits do
    let value ← if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
    match high with
    | none => high := some value
    | some first =>
        bytes := bytes.push (UInt8.ofNat (first * 16 + value))
        high := none
  if high.isSome then none else some bytes

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError s!"source activation fixture: {message}")

private def checkSourceActivation : IO Unit := do
  let some bytes := parseHex fixtureHex | throw (IO.userError "invalid source activation hex")
  let some wire := V9.decode bytes | throw (IO.userError "source activation envelope refused")
  let p := semanticProgramOf wire.base
  let some prepared := prepare? p | throw (IO.userError "source activation ownership refused")
  require (p.instructions.size == 12 && p.functions.size == 2) "source constructor inventory"
  require (p.valueLabels.size == semanticTaintCellCount wire.base &&
      p.valueLabels.size > wire.base.nodes.size + 1) "actual semantic summary allocation"
  let some call := p.instructions[4]? | throw (IO.userError "source activation call missing")
  require (call.id == 67 && call.op == .call && functionOperand? p call == some 1)
    "actual call identity and target"
  let before : State :=
    { pc := 4
      activeFunction := call.functionId
      store :=
        { scalars := ((List.range p.valueLabels.size).map (fun cell => Int.ofNat (cell * 17))).toArray
          aggregates := ((List.range p.valueLabels.size).map
            (fun cell => [Int.ofNat cell, Int.ofNat (cell + 101)])).toArray }
      shared := { actorState := #[11], externalInputs := #[[21, 22]], externalCursors := #[0] } }
  let some entered := enterPrepared? p prepared before
    | throw (IO.userError "source activation entry refused")
  let some frame := entered.frames.head? | throw (IO.userError "source activation frame missing")
  let owned := prepared.index.byFunction.getD frame.callee.toNat []
  require (!owned.isEmpty && frame.saved.map Prod.fst == owned &&
      owned == (declaredCells wire.base frame.callee).reverse) "complete source-owned snapshot"
  require (entered.shared == before.shared) "entry altered shared state"
  let some returnPc := p.instructions.toList.findIdx? (fun instruction =>
      instruction.functionId == frame.callee && instruction.op == .output)
    | throw (IO.userError "source activation return declaration missing")
  let some output := p.instructions[returnPc]?
    | throw (IO.userError "source activation return index invalid")
  let mutated := owned.foldl (fun store cell =>
    store.write cell ⟨Int.ofNat (cell + 1000), [Int.ofNat (cell + 2000)]⟩) entered.store
  let changed : State :=
    { entered with
      pc := returnPc
      store := mutated
      shared := { entered.shared with actorState := #[31], externalCursors := #[1] } }
  let some resultCell := (valueOperandCells p output).head?
    | throw (IO.userError "source activation fixture needs a non-unit result")
  let expected := changed.store.read resultCell.toNat
  let some returned := returnPrepared? p prepared changed
    | throw (IO.userError "source activation return refused")
  require (returned.pc == before.pc + 1 && returned.activeFunction == before.activeFunction &&
      returned.frames == before.frames) "caller continuation and frame restoration"
  require (frame.destination != 0 && returned.store.read frame.destination.toNat == expected)
    "captured result must survive activation restoration"
  require ((List.range p.valueLabels.size).all (fun cell =>
      cell == frame.destination.toNat || returned.store.read cell == before.store.read cell))
    "every other scalar and aggregate cell must be restored or unchanged"
  require ((List.range p.valueLabels.size).filter (fun cell => cell > wire.base.nodes.size) |>.all
      (fun cell => returned.store.read cell == before.store.read cell))
    "non-owned summary slots must remain unchanged"
  require (returned.shared == changed.shared && returned.shared != before.shared)
    "callee actor and external-cursor effects must survive return"
  require (returned.store.scalars.size == p.valueLabels.size &&
      returned.store.aggregates.size == p.valueLabels.size) "storage bounds must not change"

#eval checkSourceActivation

end LambdaSigil.Combined.OccurrenceActivationSourceChecks
