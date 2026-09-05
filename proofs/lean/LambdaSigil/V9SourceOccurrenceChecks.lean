import LambdaSigil.RankedDecodedOccurrenceWitnesses
import LambdaSigil.OccurrenceWire

/-!
# Executable source-to-wire occurrence regression pairs

The compiler fixture generator produces these two complete v9 envelopes from committed SIGIL
sources. Declaration/native parity separately checks their exact bytes. These checks then run
the actual Lean operand, CFG and invocation analysis; they are executable regression evidence,
not kernel proofs of decoder acceptance or a production Public theorem. Both envelopes are valid
declarations, but the repeated Public delivery must fail the forthcoming occurrence policy.
-/

namespace LambdaSigil.Combined.V9SourceOccurrenceChecks

private def sendHex : String :=
  include_str ".." / "fixtures" / "csir-v9" / "accept-loop-header-send.hex"
private def pureHex : String :=
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

private def checked (hex : String) : IO (V9.Program × Semantic.SemanticProgram ×
    OccurrenceInvocation.InvocationAnalysis) := do
  let some bytes := parseHex hex | throw (IO.userError "source occurrence fixture: invalid hex")
  let some wire := V9.decode bytes | throw (IO.userError "source occurrence fixture: bad declarations")
  let p := Semantic.semanticProgramOf wire.base
  let some result := RankedDecodedOccurrence.analyzeInvocations? p
    | throw (IO.userError "source occurrence fixture: analysis refused")
  if result.localAnalysis.regions.conservativeFallback then
    throw (IO.userError "source occurrence fixture: unexpected whole-function fallback")
  return (wire, p, result)

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError s!"source occurrence fixture: {message}")

private def checkSend : IO Unit := do
  let (wire, p, result) ← checked sendHex
  require (p.instructions.size == 18 && p.functions.size == 4) "send constructor inventory"
  require (wire.actorBindings == #[V9.ActorBinding.mk 88 4, V9.ActorBinding.mk 93 1])
    "serialization/delivery identity"
  require ((labelAt result.labels 3).eqb .secret && (labelAt result.labels 4).eqb .pub)
    "repeated helper invocation must be private; caller root remains Public"
  let some call := p.instructions[10]? | throw (IO.userError "missing actual call")
  require (call.id == 124 && call.op == .call && call.functionId == 4 &&
    (Semantic.functionOperand? p call == some 3)) "actual source call target"
  require ((OccurrenceTransfer.localOccurrenceAt result.localAnalysis.frontiers 10).eqb .secret)
    "call occurrence cannot be inferred from its Public arguments"
  let some delivery := p.instructions[5]? | throw (IO.userError "missing actual send")
  require (delivery.id == 93 && delivery.op == .actorBoundary && delivery.functionId == 3)
    "actual source delivery owner"
  require ((OccurrenceTransfer.localOccurrenceAt result.localAnalysis.frontiers 5).eqb .pub)
    "intraprocedural analysis alone intentionally misses caller invocation"
  require (((labelAt result.labels delivery.functionId).lub
    (OccurrenceTransfer.localOccurrenceAt result.localAnalysis.frontiers 5)).eqb .secret)
    "Public delivery cannot survive omission of caller invocation"
  require ((OccurrenceTransfer.localOccurrenceAt result.localAnalysis.frontiers 17).eqb .pub)
    "justified caller continuation must remain Public"

private def checkPure : IO Unit := do
  let (wire, p, result) ← checked pureHex
  require (p.instructions.size == 12 && p.functions.size == 2) "pure constructor inventory"
  require (wire.actorBindings.isEmpty && wire.ffiBindings.isEmpty) "pure guard has no crossings"
  require ((labelAt result.labels 1).eqb .secret && (labelAt result.labels 2).eqb .pub)
    "pure helper is still privately invoked"
  let some call := p.instructions[4]? | throw (IO.userError "missing pure call")
  require (call.id == 67 && call.op == .call && Semantic.functionOperand? p call == some 1)
    "pure actual call target"
  require ((OccurrenceTransfer.localOccurrenceAt result.localAnalysis.frontiers 4).eqb .secret &&
    (OccurrenceTransfer.localOccurrenceAt result.localAnalysis.frontiers 11).eqb .pub)
    "private loop must not contaminate successful root continuation"
  let some root := wire.roots[0]? | throw (IO.userError "missing pure helper root contract")
  require (root.functionId == 1 && root.returnOccurrence.eqb .pub)
    "an internal return is not an invocation of the helper's Public root boundary"

#eval checkSend
#eval checkPure

end LambdaSigil.Combined.V9SourceOccurrenceChecks
