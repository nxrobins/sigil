import LambdaSigil.V9OccurrenceDataflowInvocation
import LambdaSigil.OccurrenceActivation

/-!
# Production CSIR v9 occurrence verifier

This Init-only kernel composes the retained v8 verifier with occurrence facts derived from the
exact decoded v9 envelope. Declaration decoding alone remains non-authorizing. Rust supplies no
labels, region certificates, activation ownership lists, or policy verdicts.

The check is deliberately unary. It enforces the boundary ceilings needed by the future Public
relational proof, but does not itself claim weak bisimulation or source/runtime correspondence.
-/

namespace LambdaSigil.Combined.V9.OccurrenceKernel

open Semantic BoundaryContracts OccurrenceTransfer OccurrenceDataflowInvocation

def effectiveOccurrence (analysis : Analysis) (instruction : Instruction) (pc : Nat) : Label :=
  (labelAt analysis.labels instruction.functionId).lub
    (localOccurrenceAt analysis.localAnalysis.frontiers pc)

/-- Recover the exact decoded function return-value contract. -/
def functionReturnLabel? (machine : SemanticProgram) (instruction : Instruction) : Option Label := do
  let function ← machine.functions[instruction.functionId.toNat - 1]?
  if function.id == instruction.functionId then some function.returnLabel else none

/-- Recover the exact declaration-owned root contract. -/
def rootContract? (analysis : Analysis) (instruction : Instruction) :
    Option FunctionRootContract := do
  let root ← analysis.dataflow.contracts.roots[instruction.functionId.toNat - 1]?
  if root.functionId == instruction.functionId then some root else none

/-- Select the raw top-level output occurrence. Externally invokable roots use their declared
    return occurrence. Canonical role-zero functions have no external boundary, so a forged
    top-level start remains classified by the exact function return contract. -/
def rootReturnOccurrence? (machine : SemanticProgram) (analysis : Analysis)
    (instruction : Instruction) : Option Label := do
  let root ← rootContract? analysis instruction
  if root.role == 0 then functionReturnLabel? machine instruction else some root.returnOccurrence

/-- Raise the raw instruction's pc visibility with occurrence facts. An output is additionally
    classified by its declared root-return occurrence; a missing declaration receives the
    fail-closed `SecretCT` visibility and is independently rejected by `rootReturnOK`. -/
def raiseInstructionOccurrence (instruction : Instruction) (occurrence : Label)
    (rootReturn : Option Label) : Instruction :=
  let raisedBlock : Instruction := { instruction with blockLabel :=
    (if instruction.op == SemanticInstrOp.output then rootReturn.getD .secretCT
    else instruction.blockLabel.lub occurrence) }
  { raisedBlock with outputPayloadOccurrence :=
    (if instruction.op == SemanticInstrOp.output then occurrence
    else instruction.outputPayloadOccurrence) }

/-- One occurrence-seeding step. Keeping the program counter in the accumulator makes the
    executable pass linear while exposing a small step that the proof layer can reflect. -/
def occurrenceSeedStep (analysis : Analysis) (state : Nat × Array Label)
    (instruction : Instruction) : Nat × Array Label :=
    let pc := state.1
    let labels := if instruction.destination == 0 then state.2 else
      let occurrence := effectiveOccurrence analysis instruction pc
      let current := labelAt state.2 instruction.destination
      state.2.setIfInBounds instruction.destination.toNat (current.lub occurrence)
    (pc + 1, labels)

/-- Occurrence control is a real dependency for activation-local destinations. Seed every
    destination with the verified local-plus-invocation occurrence, then close the existing
    semantic dependency graph. This is what keeps the full modeled Public projection honest:
    values materialized only on a private invocation/iteration are no longer left Public. -/
def occurrenceSeedLabels (analysis : Analysis) (candidate : SemanticProgram) : Array Label :=
  (candidate.instructions.foldl (occurrenceSeedStep analysis)
    (0, analysis.dataflow.labels)).2

def occurrenceValueLabels (analysis : Analysis) (candidate : SemanticProgram) : Array Label :=
  let count := semanticTaintCellCount candidate.source
  saturateGraphWorklist
    (semanticTaintAdjacencyWithIndex candidate.source analysis.dataflow.semanticIndex)
    (4 * count) ((List.range count).map UInt32.ofNat)
    (occurrenceSeedLabels analysis candidate)

/-- Install the occurrence-closed label on a decoded destination without changing any semantic
    operand, opcode, target, identity, or ownership field. -/
def raiseInstructionResultLabel (labels : Array Label)
    (instruction : Instruction) : Instruction :=
  { instruction with resultLabel :=
      (if instruction.destination == 0 then instruction.resultLabel
      else labelAt labels instruction.destination) }

/-- Raise one already decoded machine with the accepted v9 occurrence analysis. Keeping the
    decoded machine explicit is load-bearing on large programs: output checks must not reconstruct
    the complete semantic program once per return instruction. -/
abbrev rawSemanticProgramFromDecoded (analysis : Analysis)
    (candidate : SemanticProgram) : SemanticProgram :=
  let valueLabels := occurrenceValueLabels analysis candidate
  let rootOutputSites := analysis.dataflow.contracts.roots.map (fun root => root.nodeId)
  let candidateWithLabels := { candidate with valueLabels := valueLabels }
  let candidateWithSites := { candidateWithLabels with rootOutputSites := rootOutputSites }
  { candidateWithSites with
    instructions := candidate.instructions.mapIdx (fun pc instruction =>
      let occurrence := if instruction.op == .output then
        localOccurrenceAt analysis.localAnalysis.frontiers pc
      else effectiveOccurrence analysis instruction pc
      let raised := raiseInstructionOccurrence instruction occurrence
        (rootReturnOccurrence? candidate analysis instruction)
      raiseInstructionResultLabel valueLabels raised) }

/-- The production raw machine derived solely from the decoded program and the accepted v9
    analysis. Value labels already include exact host-result seeds; instruction pc labels are
    raised by local and invocation occurrence, and outputs also carry the declared root-return
    occurrence. Rust supplies none of these labels. -/
def rawSemanticProgram (program : Program) (analysis : Analysis) : SemanticProgram :=
  rawSemanticProgramFromDecoded analysis
    (OccurrenceDataflow.semanticProgram program analysis.dataflow)

/-- Until the production raw machine executes activation-local save/restore, invocation influence
    must reach every destination in the complete Public scalar/aggregate projection. Merely
    constructing an `OccurrenceActivation.Prepared` index does not make the historical raw call
    step restore nonparameter callee locals. This conservative check is therefore load-bearing. -/
def localDestinationOK (instruction : Instruction) : Bool :=
  instruction.destination == 0 ||
    instruction.blockLabel.flowsTo instruction.resultLabel

/-- Boundary visibility is read from the occurrence-raised raw instruction, so local pc,
    transitive invocation influence, and the original semantic block label cannot be forgotten by
    a parallel side check. -/
def externalSiteLabel (instruction : Instruction) : Label := instruction.blockLabel

def cellsPublicB (machine : SemanticProgram) (cells : List UInt32) : Bool :=
  cells.all fun cell => (labelAt machine.valueLabels cell).eqb .pub

/-- Recover a function-owned actor-state declaration through the exact v9 state index. The
    source instruction identity and opcode are checked before its embedded offset is trusted. -/
def stateSinkAt? (program : Program) (analysis : Analysis) (instruction : Instruction)
    (operation : SemanticInstrOp) (offsetPosition : Nat) : Option Label := do
  let source ← program.base.nodes[instruction.id.toNat - 1]?
  if source.nodeId != instruction.id || source.op != .semInstruction ||
      decodeSemanticInstrOp? source.aux != some operation then none
  let offset ← semanticImmediateAt? program.base source.nodeId offsetPosition
  stateLabelForFunctionAt? analysis.stateContracts instruction.functionId offset

/-- Instruction-specific body of the Public result dependency check. -/
def publicResultDependencyBodyOK (program : Program) (analysis : Analysis)
    (machine : SemanticProgram) (instruction : Instruction) : Bool :=
  match instruction.op with
    | .stateRead =>
        match stateSinkAt? program analysis instruction .stateRead 1 with
        | some sink => sink.flowsTo instruction.resultLabel
        | none => false
    | .ffi | .actorBoundary => (externalSiteLabel instruction).eqb .pub
    | .call | .closure | .release | .releaseCT => true
    | .allocation => cellsPublicB machine (policyOperandCells machine instruction 9)
    | _ => cellsPublicB machine (valueOperandCells machine instruction)

/-- Direct payload-dependency check used by Public local preservation. Literals have an empty
    cell list. Calls and closures defer their result proof to the checked return transition;
    explicit releases defer payload equality to release synchronization. External results use
    their per-site stream and therefore require the occurrence-raised site to be Public. -/
def publicResultDependenciesOK (program : Program) (analysis : Analysis)
    (machine : SemanticProgram) (instruction : Instruction) : Bool :=
  if instruction.destination == 0 || instruction.resultLabel.neqb .pub then true
  else publicResultDependencyBodyOK program analysis machine instruction

def publicStateWriteSourceBodyOK (program : Program) (analysis : Analysis)
    (machine : SemanticProgram) (instruction : Instruction) : Bool :=
  match stateSinkAt? program analysis instruction .stateWrite 2 with
  | none => false
  | some sink =>
      sink.neqb .pub || match (valueOperandCells machine instruction)[1]? with
        | some cell => (labelAt machine.valueLabels cell).eqb .pub
        | none => false

/-- A write into Public actor state must take its raw payload from a Public value cell. Non-Public
    state remains outside the final Public projection, but the exact sink must still resolve. -/
def publicStateWriteSourceOK (program : Program) (analysis : Analysis)
    (machine : SemanticProgram) (instruction : Instruction) : Bool :=
  if instruction.op != .stateWrite then true
  else publicStateWriteSourceBodyOK program analysis machine instruction

/-- A dynamic closure target is itself an occurrence-sensitive choice. The current invocation
    analysis conservatively considers every decoded function, so the occurrence-closed target
    label must flow to every possible callee's invocation label. -/
def closureTargetOccurrenceOK (analysis : Analysis) (machine : SemanticProgram)
    (instruction : Instruction) : Bool :=
  if instruction.op != .closure then true
  else match (valueOperandCells machine instruction).head? with
    | none => false
    | some cell => machine.functions.toList.all fun function =>
        (labelAt machine.valueLabels cell).flowsTo (labelAt analysis.labels function.id)

/-- Every actual value operand in the exact FFI argument slice must flow to the corresponding
    declared parameter label. The boundary extractor already proves the slice length, identity,
    ABI types, and ownership; this check supplies the missing payload-flow judgment. -/
def ffiArgumentsOK (machine : SemanticProgram) (analysis : Analysis)
    (instruction : Instruction) (contract : FfiContract) : Bool :=
  let first := contract.binding.firstArgument.toNat
  (List.range contract.parameters.size).all fun offset =>
    match instructionOperandAt? machine instruction (first + offset), contract.parameters[offset]? with
    | some operand, some parameter =>
        operand.kind == 0 &&
          (labelAt analysis.dataflow.labels operand.value).flowsTo parameter.label
    | _, _ => false

/-- A nonempty-stack return must respect the exact function return-value contract under the full
    local plus transitive invocation occurrence. -/
def internalReturnOK (analysis : Analysis) (machine : SemanticProgram)
    (instruction : Instruction) (pc : Nat) : Bool :=
  match functionReturnLabel? machine instruction with
  | none => false
  | some sink =>
      (instruction.blockLabel.lub (effectiveOccurrence analysis instruction pc)).flowsTo sink

/-- An empty-stack output is an external root occurrence. Aggregate internal invocation influence
    is excluded because internal returns emit no boundary event. Local pc occurrence is retained
    separately in `outputPayloadOccurrence`, while all returns share the declaration-owned root
    site and entry/return occurrence. Role-zero roots are not externally invokable; their exact
    internal return check remains mandatory. -/
def externalRootReturnOK (analysis : Analysis) (instruction : Instruction) (pc : Nat) : Bool :=
  match rootContract? analysis instruction with
  | none => false
  | some root => root.role == 0 ||
      root.entryOccurrence.flowsTo root.returnOccurrence

/-- Check a return against the already decoded source machine. This is the executable core used
    by the production instruction loop, where the decoded machine is shared across all outputs. -/
def rootReturnOKWithDecoded (analysis : Analysis) (machine decoded : SemanticProgram)
    (instruction : Instruction) (pc : Nat) : Bool :=
  match decoded.instructions[pc]? with
  | none => false
  | some source => instruction.id == source.id &&
      internalReturnOK analysis machine source pc && externalRootReturnOK analysis source pc

/-- Every output satisfies both runtime contexts: internal call-return and, where declared,
    external empty-stack root return. Role zero receives no unconditional internal bypass. -/
def rootReturnOK (program : Program) (analysis : Analysis) (machine : SemanticProgram)
    (instruction : Instruction) (pc : Nat) : Bool :=
  rootReturnOKWithDecoded analysis machine
    (OccurrenceDataflow.semanticProgram program analysis.dataflow) instruction pc

def stateWriteOccurrenceOK (program : Program) (analysis : Analysis)
    (instruction : Instruction) (_pc : Nat) : Bool :=
  match program.base.nodes[instruction.id.toNat - 1]? with
  | none => false
  | some source =>
      source.nodeId == instruction.id && source.op == .semInstruction && source.aux == 10 &&
        match semanticImmediateAt? program.base source.nodeId 2 with
        | none => false
        | some offset =>
            match stateLabelForFunctionAt? analysis.stateContracts instruction.functionId offset with
            | none => false
            | some sink => (externalSiteLabel instruction).flowsTo sink

/-- Instruction policy check over shared decoded and occurrence-raised machines. -/
def instructionOccurrenceOKWithDecoded (program : Program) (analysis : Analysis)
    (machine decoded : SemanticProgram)
    (instruction : Instruction) (pc : Nat) : Bool :=
  localDestinationOK instruction &&
    publicResultDependenciesOK program analysis machine instruction &&
    publicStateWriteSourceOK program analysis machine instruction &&
    closureTargetOccurrenceOK analysis machine instruction &&
    match site? analysis.dataflow.contracts instruction.id with
    | none => false
    | some site =>
        site.owner == instruction.id && site.functionId == instruction.functionId &&
          match site.kind with
          | .ffi _ contract =>
              ffiArgumentsOK machine analysis instruction contract &&
                (externalSiteLabel instruction).flowsTo contract.occurrence
          | .actor _ _ =>
              -- The current raw machine emits a boundary event for every actor opcode, including
              -- codecs. A future semantic distinction may justify a narrower ceiling.
              (externalSiteLabel instruction).flowsTo .pub
          | .ordinary operation =>
              operation == instruction.op &&
                match operation with
                | .stateWrite => stateWriteOccurrenceOK program analysis instruction pc
                | .output => rootReturnOKWithDecoded analysis machine decoded instruction pc
                | _ => true

/-- The checked site is recovered from the declaration index tied to the same decoded program.
    Codec-only actor operations have no delivery-occurrence sink; send/ask/spawn remain Public. -/
def instructionOccurrenceOK (program : Program) (analysis : Analysis) (machine : SemanticProgram)
    (instruction : Instruction) (pc : Nat) : Bool :=
  instructionOccurrenceOKWithDecoded program analysis machine
    (OccurrenceDataflow.semanticProgram program analysis.dataflow) instruction pc

/-- One exact selector-coherence row. -/
def selectorCoherentAt (analysis : Analysis) (machine : SemanticProgram) (pc : Nat) : Bool :=
  match machine.instructions[pc]? with
  | none => false
  | some instruction =>
      match DecodedOccurrence.selectorLabel? machine instruction with
      | none => false
      | some selector => selector == analysis.localAnalysis.selectors.getD pc .pub

/-- The region/frontier analysis and the raw machine must classify every exact decoded selector
    identically. Occurrence-raised values are permitted, but if that raise changes a controller's
    selector then the current one-pass analysis rejects instead of authorizing a stale region
    proof. A future joint monotone fixed point may replace this conservative coherence gate. -/
def selectorCoherenceChecks (analysis : Analysis) (machine : SemanticProgram) : Bool :=
  (List.range machine.instructions.size).all (selectorCoherentAt analysis machine)

def occurrencePolicyChecksWithMachines (program : Program) (analysis : Analysis)
    (decoded machine : SemanticProgram) : Bool :=
  selectorCoherenceChecks analysis machine &&
  (List.range machine.instructions.size).all (fun pc =>
    match machine.instructions[pc]? with
    | none => false
    | some instruction =>
        instructionOccurrenceOKWithDecoded program analysis machine decoded instruction pc)

def occurrencePolicyChecks (program : Program) (analysis : Analysis) : Bool :=
  let decoded := OccurrenceDataflow.semanticProgram program analysis.dataflow
  occurrencePolicyChecksWithMachines program analysis decoded
    (rawSemanticProgramFromDecoded analysis decoded)

def firstOccurrenceViolationWithMachines (program : Program) (analysis : Analysis)
    (decoded machine : SemanticProgram) : Option Violation :=
  let selectorViolation := (List.range machine.instructions.size).findSome? fun pc =>
    match machine.instructions[pc]? with
    | none => some ⟨.malformed, 0, 40⟩
    | some instruction =>
        match DecodedOccurrence.selectorLabel? machine instruction with
        | some selector =>
            if selector == analysis.localAnalysis.selectors.getD pc .pub then none
            else some ⟨.malformed, instruction.id, 40⟩
        | none => some ⟨.malformed, instruction.id, 40⟩
  selectorViolation.orElse fun _ => (List.range machine.instructions.size).findSome? fun pc =>
    match machine.instructions[pc]? with
    | none => some ⟨.malformed, 0, 40⟩
    | some instruction =>
        if instructionOccurrenceOKWithDecoded program analysis machine decoded instruction pc then none
        else some ⟨.malformed, instruction.id, 40⟩

def firstOccurrenceViolation (program : Program) (analysis : Analysis) : Option Violation :=
  let decoded := OccurrenceDataflow.semanticProgram program analysis.dataflow
  firstOccurrenceViolationWithMachines program analysis decoded
    (rawSemanticProgramFromDecoded analysis decoded)

/-- Success means the exact v8 prefix passed every retained check, the decoded v9 declarations
    produced the complete root/host/invocation analyses, the ordinary semantic checks were rerun
    over those host-seeded labels, the occurrence-aware raw machine passed relational static
    safety, activation ownership was derivable, and every occurrence-sensitive boundary respected
    its declaration-derived ceiling. -/
def verifyProgram (program : Program) : Option Violation :=
  match Combined.verifyProgram program.base with
  | some violation => some violation
  | none =>
      match analyze? program with
      | none => some ⟨.malformed, 0, 40⟩
      | some analysis =>
          match verifyProgramWithContext program.base analysis.dataflow.semanticIndex
              analysis.dataflow.labels with
          | some violation => some violation
          | none =>
              let decoded := OccurrenceDataflow.semanticProgram program analysis.dataflow
              let machine := rawSemanticProgramFromDecoded analysis decoded
              if !(OccurrenceActivation.prepare? machine).isSome then some ⟨.malformed, 0, 40⟩
              else if !Semantic.operationalStaticSafeB machine then
                some ((Semantic.firstDecodedStaticViolation machine).getD ⟨.malformed, 0, 9⟩)
              else if occurrencePolicyChecksWithMachines program analysis decoded machine then none
              else some ((firstOccurrenceViolationWithMachines program analysis decoded machine).getD
                ⟨.malformed, 0, 40⟩)

def verifyBytes (bytes : ByteArray) : UInt64 :=
  match V9.decode bytes with
  | none => packViolation ⟨.malformed, 0, 40⟩
  | some program => (verifyProgram program).map packViolation |>.getD 0

@[export sigil_csir_v9_verify]
def exportedVerify (bytes : ByteArray) : UInt64 := verifyBytes bytes

end LambdaSigil.Combined.V9.OccurrenceKernel
