import LambdaSigil.DecodedOccurrence

/-!
# Decoded invocation influence with a shared dynamic-target summary

Direct targets use the raw machine's function-operand accessor. Dynamic targets use its first
decoded value operand, not an assumed operand-zero shape. Every decoded function is a possible
dynamic target, represented by one summary vertex and one shared fan-out rather than a closure
times function edge expansion. Captures remain data arguments; only target selection, local
occurrence and caller invocation contribute to invocation influence.

This is an internal conservative foundation, not production acceptance or a balanced-stack
theorem. The all-functions superset can overtaint unrelated functions and is not source-corpus
precision qualified. Pure-helper and justified-continuation compatibility remain requirements
for eventual production integration. No historical verifier or wire meaning is changed here.
-/

namespace LambdaSigil.Combined.OccurrenceInvocation

open Semantic OccurrenceRegions OccurrenceTransfer DecodedOccurrence

def invocationCellCount (p : SemanticProgram) : Nat := p.functions.size + 2

def dynamicCell (p : SemanticProgram) : UInt32 := UInt32.ofNat (p.functions.size + 1)

def functionLayoutB (p : SemanticProgram) : Bool :=
  p.functions.size ≤ maxNodes && (List.range p.functions.size).all (fun position =>
    match p.functions[position]? with
    | none => false
    | some function => function.id.toNat == position + 1)

def validFunctionIdB (p : SemanticProgram) (id : UInt32) : Bool :=
  id != 0 && (p.functions[id.toNat - 1]?).any (fun function => function.id == id)

structure InvocationSite where
  caller : UInt32
  destination : UInt32
  occurrence : Label
  selection : Label
  dynamic : Bool
  deriving Repr, BEq, DecidableEq

/-- `none` rejects malformed call extraction; `some none` means a genuine non-call instruction.
    An empty closure selector never becomes a fabricated Public target. The value accessor also
    handles the raw semantics of generic in-memory records with non-value operands before it. -/
def invocationSite? (p : SemanticProgram) (frontiers : ThresholdFrontiers) (pc : Nat) :
    Option (Option InvocationSite) := do
  let instruction ← p.instructions[pc]?
  match instruction.op with
  | .call =>
      if !validFunctionIdB p instruction.functionId then none else do
      let callee ← functionOperand? p instruction
      if !validFunctionIdB p callee then none else
      some (some ⟨instruction.functionId, callee, localOccurrenceAt frontiers pc, .pub, false⟩)
  | .closure =>
      if !validFunctionIdB p instruction.functionId then none else do
      let selector ← (valueOperandCells p instruction).head?
      some (some ⟨instruction.functionId, dynamicCell p, localOccurrenceAt frontiers pc,
        labelAt p.valueLabels selector, true⟩)
  | _ => some none

def siteInfluence (labels : Array Label) (site : InvocationSite) : Label :=
  ((labelAt labels site.caller).lub site.occurrence).lub site.selection

structure InvocationPlan where
  adjacency : Array (List UInt32)
  seeds : Array Label
  deriving Repr

def addInvocationSite (plan : InvocationPlan) (site : InvocationSite) : InvocationPlan :=
  { adjacency := plan.adjacency.setIfInBounds site.caller.toNat
      (site.destination :: plan.adjacency.getD site.caller.toNat [])
    seeds := raiseCell plan.seeds site.destination (site.occurrence.lub site.selection) }

def invocationPlan? (p : SemanticProgram) (frontiers : ThresholdFrontiers) : Option InvocationPlan :=
  let count := invocationCellCount p
  let initial : InvocationPlan :=
    { adjacency := (Array.replicate count []).setIfInBounds (dynamicCell p).toNat
        (p.functions.toList.map Function.id)
      seeds := Array.replicate count .pub }
  (List.range p.instructions.size).foldlM (fun plan pc => do
    let site ← invocationSite? p frontiers pc
    match site with
    | none => some plan
    | some call => some (addInvocationSite plan call)) initial

/-- The same bounded finite-label worklist as semantic dataflow: one initial visit plus at most
    three strict raises per cell. The local postcheck is independent of the constructed graph. -/
def computeInvocationLabels (p : SemanticProgram) (plan : InvocationPlan) : Array Label :=
  let count := invocationCellCount p
  saturateGraphWorklist plan.adjacency (4 * count)
    ((List.range count).map UInt32.ofNat) plan.seeds

/-- Re-extraction from every actual instruction catches omitted call edges or seeds. The shared
    summary fan-out separately catches missing possible dynamic targets. Neither return-value
    contracts nor payload confidentiality replace these occurrence obligations. -/
def invocationChecks (p : SemanticProgram) (frontiers : ThresholdFrontiers)
    (labels : Array Label) : Bool :=
  functionLayoutB p && labels.size == invocationCellCount p &&
    (List.range p.instructions.size).all (fun pc =>
      match invocationSite? p frontiers pc with
      | none => false
      | some none => true
      | some (some site) => (siteInfluence labels site).flowsTo (labelAt labels site.destination)) &&
    p.functions.all (fun function =>
      (labelAt labels (dynamicCell p)).flowsTo (labelAt labels function.id))

structure InvocationAnalysis where
  localAnalysis : Analysis
  labels : Array Label
  deriving Repr

/-- No local frontier, target set, seed table or fixed-point certificate is an argument. Failure
    of extraction or any returned-label obligation rejects the whole internal analysis. -/
def analyzeInvocations? (p : SemanticProgram) : Option InvocationAnalysis := do
  let localAnalysis ← analyze? p
  if !functionLayoutB p then none else pure ()
  let plan ← invocationPlan? p localAnalysis.frontiers
  let labels := computeInvocationLabels p plan
  if invocationChecks p localAnalysis.frontiers labels then some ⟨localAnalysis, labels⟩ else none

end LambdaSigil.Combined.OccurrenceInvocation
