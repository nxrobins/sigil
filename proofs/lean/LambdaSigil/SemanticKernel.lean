import LambdaSigil.CombinedKernel

/-!
# Init-only raw semantic verifier kernel

This module contains the decoded v8 machine representation and the finite decision whose truth is
the premise of the raw relational proofs.  It remains `Init`-only so compiling the production
verifier does not link theorem automation or Mathlib into the trusted native runtime.
-/

namespace LambdaSigil.Combined.Semantic

abbrev InstrOp := SemanticInstrOp

structure OperandRecord where
  owner : UInt32
  position : UInt32
  value : UInt32
  high : UInt32 := 0
  kind : UInt8 := 0
  deriving Repr, BEq, DecidableEq, Inhabited

structure Instruction where
  op : InstrOp
  id : UInt32
  functionId : UInt32
  blockId : UInt32
  destination : UInt32
  firstOperand : UInt32
  operandCount : UInt32
  target : UInt32
  alternate : UInt32 := 0
  merge : UInt32 := 0
  blockLabel : Label := .pub
  resultLabel : Label
  /-- Verifier-derived pc occurrence applied to a top-level output payload.  This is separate
      from `blockLabel`: the latter classifies the stable external root occurrence, while this
      field prevents a value returned under private control from becoming a Public payload. -/
  outputPayloadOccurrence : Label := .pub
  aux : Int
  deriving Repr, BEq, DecidableEq

structure Function where
  id : UInt32
  entry : UInt32
  firstInstruction : UInt32
  instructionCount : UInt32
  parameterCells : Array UInt32 := #[]
  returnLabel : Label := .pub
  deriving Repr, BEq, DecidableEq

structure PolicySelection where
  classCode : UInt32
  start : UInt32
  mask : UInt32
  deriving Repr, BEq, DecidableEq, Inhabited

structure SemanticProgram where
  source : Program := ⟨#[]⟩
  sourceIndex : SemanticIndex := emptySemanticIndex 0
  functions : Array Function
  instructions : Array Instruction
  operands : Array OperandRecord
  valueLabels : Array Label
  stateLabels : List (UInt32 × Label) := []
  policySelections : Array (List PolicySelection) := #[]
  /-- Canonical external boundary site per one-based function ID. V8 programs leave this empty
      and retain instruction-ID sites; the V9 raw machine derives it from exact root records. -/
  rootOutputSites : Array UInt32 := #[]
  deriving Repr, BEq, DecidableEq

structure SemanticDecodeState where
  functions : Array Function := #[]
  instructions : Array Instruction := #[]
  operands : Array OperandRecord := #[]
  stateLabels : List (UInt32 × Label) := []
  policySelections : Array (List PolicySelection) := #[]

/-- Instruction ordinals are computed once and stored by canonical block-node ID.  The original
    decoder rescanned the complete CSIR stream for every branch target and rebuilt the semantic
    index for every instruction/operand, which made the raw-verifier suffix quadratic on the
    self-host corpus. -/
def semanticBlockEntries (p : Program) (index : SemanticIndex) : Array (Option Nat) :=
  let initial : Nat × Array (Option Nat) :=
    (0, Array.replicate (p.nodes.size + 1) none)
  (p.nodes.foldl (fun state node =>
    let (count, entries) := state
    if node.op == .semInstruction then
      let entries := match indexedSemanticBlockNode? index node.origin node.actual with
        | some block =>
            if (entries.getD block.nodeId.toNat none).isSome then entries
            else entries.setIfInBounds block.nodeId.toNat (some count)
        | none => entries
      (count + 1, entries)
    else state) initial).2

def semanticBlockEntryFrom? (index : SemanticIndex) (entries : Array (Option Nat))
    (functionId blockId : UInt32) : Option Nat := do
  let block ← indexedSemanticBlockNode? index functionId blockId
  entries[block.nodeId.toNat]?.join

def semanticBlockTargetAtFrom? (p : Program) (index : SemanticIndex)
    (entries : Array (Option Nat)) (instruction : Node) (position : Nat) : Option Nat := do
  let operand ← semanticOperandAt? p instruction.nodeId position
  if operand.flags == 1 then
    semanticBlockEntryFrom? index entries instruction.origin operand.required
  else none

def semanticFunctionEntryFrom? (index : SemanticIndex) (entries : Array (Option Nat))
    (functionId : UInt32) : Option Nat := do
  let function ← index.functions[functionId.toNat - 1]?
  semanticBlockEntryFrom? index entries functionId function.actual

def semanticResultCellFrom (index : SemanticIndex) (instruction : Node) : UInt32 :=
  if instruction.required == 0 then 0 else
    (semanticValueCell? index instruction.origin instruction.required).getD 0

def semanticImmediateInt (operand : Node) : Int :=
  let magnitude := operand.required.toNat + operand.ceiling.toNat * (2 ^ 32)
  if (operand.ceiling &&& 0x80000000) != 0 then
    Int.ofNat magnitude - Int.ofNat (2 ^ 64)
  else Int.ofNat magnitude

def semanticFirstImmediate (p : Program) (instruction : Node) : Int :=
  (List.range instruction.ceiling.toNat).foldl (fun found position =>
    match found with
    | some value => some value
    | none =>
        match semanticOperandAt? p instruction.nodeId position with
        | some operand => if operand.flags == 3 then some (semanticImmediateInt operand) else none
        | none => none) none |>.getD 0

def decodeSemanticNode (p : Program) (index : SemanticIndex) (labels : Array Label)
    (blockEntries : Array (Option Nat)) (state : SemanticDecodeState) (node : Node) :
    SemanticDecodeState :=
  match node.op with
  | .semFunction =>
      let first := (semanticBlockEntryFrom? index blockEntries node.origin node.actual).getD 0
      let parameters := (index.parameterCells.getD node.origin.toNat []).toArray
      let returnLabel := match index.returnContractNodes[node.origin.toNat]?.join with
        | some contract => contract.labelA
        | none => .pub
      let function : Function :=
        { id := node.origin, entry := node.actual, firstInstruction := UInt32.ofNat first,
          instructionCount := node.required, parameterCells := parameters, returnLabel }
      { state with functions := state.functions.push function }
  | .semInstruction =>
      match decodeSemanticInstrOp? node.aux with
      | none => state
      | some op =>
          let destination := semanticResultCellFrom index node
          let primaryPosition := match op with
            | .branch | .loop | .range => 1
            | .dispatch => if node.ceiling == 2 then 0 else 1
            | _ => 0
          let alternatePosition := match op with
            | .branch | .loop | .range => 2
            | .dispatch => if node.ceiling == 2 then 1 else 2
            | _ => 0
          let target := match op with
            | .call =>
                match semanticOperandAt? p node.nodeId 0 with
                | some operand => if operand.flags == 2 then
                    (semanticFunctionEntryFrom? index blockEntries operand.required).getD
                      (state.instructions.size + 1)
                  else state.instructions.size + 1
                | none => state.instructions.size + 1
            | .branch | .loop | .range | .dispatch | .jump =>
                (semanticBlockTargetAtFrom? p index blockEntries node primaryPosition).getD
                  (state.instructions.size + 1)
            | _ => state.instructions.size + 1
          let alternate := match op with
            | .branch | .loop | .range | .dispatch =>
                (semanticBlockTargetAtFrom? p index blockEntries node alternatePosition).getD
                  (state.instructions.size + 1)
            | _ => state.instructions.size + 1
          let merge := match op with
            | .branch | .dispatch =>
                if node.ceiling == 4 then
                  (semanticBlockTargetAtFrom? p index blockEntries node 3).getD alternate
                else alternate
            | .loop | .range => alternate
            | _ => state.instructions.size + 1
          let resultLabel := labelAt labels destination
          let blockLabel := match semanticBlockCell? index node.origin node.actual with
            | some cell => labelAt labels cell
            | none => .pub
          let instruction : Instruction :=
            { op, id := node.nodeId, functionId := node.origin, blockId := node.actual,
              destination, firstOperand := UInt32.ofNat state.operands.size,
              operandCount := node.ceiling, target := UInt32.ofNat target,
              alternate := UInt32.ofNat alternate, merge := UInt32.ofNat merge,
              blockLabel, resultLabel, aux := semanticFirstImmediate p node }
          { state with instructions := state.instructions.push instruction }
  | .semOperand =>
      match p.nodes[node.origin.toNat - 1]? with
      | none => state
      | some owner =>
          let value := if node.flags == 0 then
            (semanticValueCell? index owner.origin node.required).getD 0
          else node.required
          let operand : OperandRecord :=
            { owner := node.origin, position := node.actual, value, high := node.ceiling,
              kind := node.flags }
          { state with operands := state.operands.push operand }
  | .semLabelContract =>
      if node.aux == 3 then
        { state with stateLabels := (node.actual, node.labelA) :: state.stateLabels }
      else state
  | .semPolicyClass =>
      let existing := state.policySelections.getD node.origin.toNat []
      let selection : PolicySelection :=
        { classCode := node.aux, start := node.ceiling, mask := node.actual }
      { state with policySelections := (state.policySelections.setIfInBounds
          node.origin.toNat (selection :: existing)) }
  | _ => state

def semanticProgramOfWith (p : Program) (index : SemanticIndex) (labels : Array Label) :
    SemanticProgram :=
  let blockEntries := semanticBlockEntries p index
  let initial : SemanticDecodeState :=
    { policySelections := Array.replicate (p.nodes.size + 1) [] }
  let decoded := p.nodes.foldl (decodeSemanticNode p index labels blockEntries) initial
  { source := p, sourceIndex := index, functions := decoded.functions,
    instructions := decoded.instructions,
    operands := decoded.operands, valueLabels := labels,
    stateLabels := decoded.stateLabels, policySelections := decoded.policySelections }

def semanticProgramOf (p : Program) : SemanticProgram :=
  let index := buildSemanticIndex p
  semanticProgramOfWith p index (semanticLabelsWithIndex p index)

def stateLabelAt (p : SemanticProgram) (offset : UInt32) : Label :=
  semanticDeclaredStateLabelAt p.source offset

def operandSliceWellFormed (p : SemanticProgram) (i : Instruction) : Prop :=
  i.firstOperand.toNat + i.operandCount.toNat ≤ p.operands.size ∧
    ∀ offset < i.operandCount.toNat,
      let operand := p.operands.getD (i.firstOperand.toNat + offset) default
      operand.owner = i.id ∧ operand.position.toNat = offset ∧
        (operand.kind = 0 → operand.value.toNat < p.valueLabels.size)

def instructionWellFormed (p : SemanticProgram) (i : Instruction) : Prop :=
  i.id != 0 ∧
    (i.destination == 0 ∨ i.destination.toNat < p.valueLabels.size) ∧
    i.resultLabel = labelAt p.valueLabels i.destination ∧ operandSliceWellFormed p i ∧
    (i.op = .jump → i.target.toNat < p.instructions.size) ∧
    (i.op = .branch ∨ i.op = .loop ∨ i.op = .range ∨ i.op = .dispatch →
      i.target.toNat < p.instructions.size ∧ i.alternate.toNat < p.instructions.size ∧
        i.merge.toNat < p.instructions.size)

def functionWellFormed (p : SemanticProgram) (function : Function) : Prop :=
  function.id != 0 ∧ function.firstInstruction.toNat < p.instructions.size ∧
    ∀ cell ∈ function.parameterCells.toList, cell.toNat < p.valueLabels.size

def SemanticProgram.WellFormed (p : SemanticProgram) : Prop :=
  p.instructions.size ≤ maxNodes ∧
    (∀ function ∈ p.functions.toList, functionWellFormed p function) ∧
    ∀ i ∈ p.instructions.toList, instructionWellFormed p i

def operandSliceWellFormedB (p : SemanticProgram) (i : Instruction) : Bool :=
  decide (i.firstOperand.toNat + i.operandCount.toNat ≤ p.operands.size) &&
    (List.range i.operandCount.toNat).all fun offset =>
      let operand := p.operands.getD (i.firstOperand.toNat + offset) default
      operand.owner == i.id && operand.position.toNat == offset &&
        decide (operand.kind = 0 → operand.value.toNat < p.valueLabels.size)

def instructionWellFormedB (p : SemanticProgram) (i : Instruction) : Bool :=
  i.id != 0 && decide (i.destination = 0 ∨ i.destination.toNat < p.valueLabels.size) &&
    i.resultLabel == labelAt p.valueLabels i.destination && operandSliceWellFormedB p i &&
    decide (i.op = .jump → i.target.toNat < p.instructions.size) &&
    decide ((i.op = .branch ∨ i.op = .loop ∨ i.op = .range ∨ i.op = .dispatch) →
      i.target.toNat < p.instructions.size ∧ i.alternate.toNat < p.instructions.size ∧
        i.merge.toNat < p.instructions.size)

def functionWellFormedB (p : SemanticProgram) (function : Function) : Bool :=
  function.id != 0 && decide (function.firstInstruction.toNat < p.instructions.size) &&
    function.parameterCells.toList.all fun cell => decide (cell.toNat < p.valueLabels.size)

def semanticProgramWellFormedB (p : SemanticProgram) : Bool :=
  decide (p.instructions.size ≤ maxNodes) &&
    p.functions.toList.all (functionWellFormedB p) &&
    p.instructions.toList.all (instructionWellFormedB p)

def instructionOperandAt? (p : SemanticProgram) (i : Instruction) (position : Nat) :
    Option OperandRecord := do
  if position < i.operandCount.toNat then pure () else none
  let operand ← p.operands[i.firstOperand.toNat + position]?
  if operand.owner == i.id && operand.position.toNat == position then some operand else none

def instructionOperands (p : SemanticProgram) (i : Instruction) : List OperandRecord :=
  (List.range i.operandCount.toNat).filterMap (instructionOperandAt? p i)

def valueOperandCells (p : SemanticProgram) (i : Instruction) : List UInt32 :=
  (instructionOperands p i).filterMap fun operand =>
    if operand.kind == 0 then some operand.value else none

def operandImmediate (operand : OperandRecord) : Int :=
  let magnitude := operand.value.toNat + operand.high.toNat * (2 ^ 32)
  if (operand.high &&& 0x80000000) != 0 then
    Int.ofNat magnitude - Int.ofNat (2 ^ 64)
  else Int.ofNat magnitude

def immediateOperands (p : SemanticProgram) (i : Instruction) : List Int :=
  (instructionOperands p i).filterMap fun operand =>
    if operand.kind == 3 then some (operandImmediate operand) else none

def functionOperand? (p : SemanticProgram) (i : Instruction) : Option UInt32 :=
  (instructionOperands p i).find? (fun operand => operand.kind == 2) |>.map (fun op => op.value)

def policySelectsPosition (p : SemanticProgram) (owner classCode : UInt32)
    (position : Nat) : Bool :=
  (p.policySelections.getD owner.toNat []).any fun policy =>
    policy.classCode == classCode && policy.start.toNat ≤ position &&
      position < policy.start.toNat + 32 &&
      (policy.mask &&& ((1 : UInt32) <<< UInt32.ofNat (position - policy.start.toNat))) != 0

def policyOperandCells (p : SemanticProgram) (instruction : Instruction) (classCode : UInt32) :
    List UInt32 :=
  (List.range instruction.operandCount.toNat).filterMap fun position =>
    if !policySelectsPosition p instruction.id classCode position then none else
      match instructionOperandAt? p instruction position with
      | some operand => if operand.kind == 0 then some operand.value else none
      | none => none

def cellsAvoidSecretCT (p : SemanticProgram) (cells : List UInt32) : Prop :=
  ∀ cell ∈ cells, labelAt p.valueLabels cell ≠ .secretCT

def policyCells (p : SemanticProgram) (instruction : Instruction) (classCode : UInt32) :
    List UInt32 := policyOperandCells p instruction classCode

def observedCellsAvoidSecretCT (p : SemanticProgram) (instruction : Instruction) : Prop :=
  ∀ classCode ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 15] : List UInt32),
    cellsAvoidSecretCT p (policyCells p instruction classCode)

def resultDependenciesAvoidSecretCT (p : SemanticProgram) (instruction : Instruction) : Prop :=
  instruction.destination == 0 ∨ instruction.resultLabel = .secretCT ∨
    match instruction.op with
    | .ffi | .actorBoundary | .call | .closure | .release | .releaseCT => True
    | .stateRead =>
        let offset := (immediateOperands p instruction).head?.getD 0
        offset < 0 ∨ stateLabelAt p (UInt32.ofNat offset.toNat) ≠ .secretCT
    | .allocation => cellsAvoidSecretCT p (policyCells p instruction 9)
    | _ => cellsAvoidSecretCT p (valueOperandCells p instruction)

def stateWriteAvoidsSecretCT (p : SemanticProgram) (instruction : Instruction) : Prop :=
  instruction.op = .stateWrite →
    let offset := (immediateOperands p instruction).head?.getD 0
    offset < 0 ∨ stateLabelAt p (UInt32.ofNat offset.toNat) = .secretCT ∨
      match (valueOperandCells p instruction)[1]? with
      | some cell => labelAt p.valueLabels cell ≠ .secretCT
      | none => False

def SecretCTInstructionSafe (p : SemanticProgram) (instruction : Instruction) : Prop :=
  observedCellsAvoidSecretCT p instruction ∧ resultDependenciesAvoidSecretCT p instruction ∧
    stateWriteAvoidsSecretCT p instruction ∧
    (instruction.op = .branch ∨ instruction.op = .loop ∨ instruction.op = .range ∨
      (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2) ∨
      instruction.op = .closure ∨
      (instruction.op = .trap ∧ instruction.operandCount ≠ 0) →
        match (valueOperandCells p instruction).head? with
        | some cell => labelAt p.valueLabels cell ≠ .secretCT
        | none => False)

def SecretCTStaticSafe (p : SemanticProgram) : Prop :=
  p.WellFormed ∧ ∀ instruction ∈ p.instructions.toList,
    SecretCTInstructionSafe p instruction

def cellsAvoidSecretCTB (p : SemanticProgram) (cells : List UInt32) : Bool :=
  cells.all fun cell => labelAt p.valueLabels cell != .secretCT

def observedCellsAvoidSecretCTB (p : SemanticProgram) (instruction : Instruction) : Bool :=
  ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 15] : List UInt32).all fun classCode =>
    cellsAvoidSecretCTB p (policyCells p instruction classCode)

def resultDependenciesAvoidSecretCTB (p : SemanticProgram) (instruction : Instruction) : Bool :=
  if instruction.destination == 0 || instruction.resultLabel.eqb .secretCT then true else
    match instruction.op with
    | .ffi | .actorBoundary | .call | .closure | .release | .releaseCT => true
    | .stateRead =>
        let offset := (immediateOperands p instruction).head?.getD 0
        decide (offset < 0 ∨ stateLabelAt p (UInt32.ofNat offset.toNat) ≠ .secretCT)
    | .allocation => cellsAvoidSecretCTB p (policyCells p instruction 9)
    | _ => cellsAvoidSecretCTB p (valueOperandCells p instruction)

def stateWriteAvoidsSecretCTB (p : SemanticProgram) (instruction : Instruction) : Bool :=
  match instruction.op with
  | .stateWrite =>
      let offset := (immediateOperands p instruction).head?.getD 0
      if offset < 0 then true
      else if (stateLabelAt p (UInt32.ofNat offset.toNat)).eqb .secretCT then true
      else match (valueOperandCells p instruction)[1]? with
        | some cell => (labelAt p.valueLabels cell).neqb .secretCT
        | none => false
  | _ => true

def controlAvoidsSecretCTB (p : SemanticProgram) (instruction : Instruction) : Bool :=
  let controls := match instruction.op with
    | .branch | .loop | .range | .closure => true
    | .trap => instruction.operandCount != 0
    | .dispatch => instruction.operandCount != 2
    | _ => false
  !controls || match (valueOperandCells p instruction).head? with
    | some cell => (labelAt p.valueLabels cell).neqb .secretCT
    | none => false

def secretCTInstructionSafeB (p : SemanticProgram) (instruction : Instruction) : Bool :=
  observedCellsAvoidSecretCTB p instruction &&
    resultDependenciesAvoidSecretCTB p instruction &&
    stateWriteAvoidsSecretCTB p instruction && controlAvoidsSecretCTB p instruction

def secretCTStaticSafeB (p : SemanticProgram) : Bool :=
  semanticProgramWellFormedB p &&
    p.instructions.toList.all (secretCTInstructionSafeB p)

/-- The Public static check retains the structured continuation rule. A separately derived private
    leaf class may return early: every destination and returned operand is non-Public, with no
    shared effects or calls. This does not establish the unfinished Public relational theorem. -/
def PublicControlStaticSafe (p : SemanticProgram) : Prop :=
  ∀ instruction ∈ p.source.nodes.toList, (instruction.op == .semInstruction) = true →
    ((semanticPrivateLeafReturnFunctions p.source p.sourceIndex p.valueLabels).getD
        instruction.origin.toNat false ||
      semanticPublicControlContinuationOK p.source p.sourceIndex p.valueLabels instruction) = true

def publicControlStaticSafeB (p : SemanticProgram) : Bool :=
  let privateLeaves := semanticPrivateLeafReturnFunctions p.source p.sourceIndex p.valueLabels
  p.source.nodes.toList.all fun instruction =>
    if instruction.op == .semInstruction then
      privateLeaves.getD instruction.origin.toNat false ||
        semanticPublicControlContinuationOK p.source p.sourceIndex p.valueLabels instruction
    else true

/-- A successful halt is a Public cut point.  In particular, a callee reached only below a
    non-Public caller pc may not terminate the whole machine instead of returning to the verified
    continuation.  Caller-pc and CFG edges make `blockLabel` a verifier-derived fact. -/
def PublicHaltStaticSafe (p : SemanticProgram) : Prop :=
  ∀ instruction ∈ p.instructions.toList, instruction.op = .halt →
    instruction.blockLabel = .pub

def publicHaltStaticSafeB (p : SemanticProgram) : Bool :=
  p.instructions.toList.all fun instruction =>
    instruction.op != .halt || instruction.blockLabel.eqb .pub

def RawRelationalStaticSafe (p : SemanticProgram) : Prop :=
  SecretCTStaticSafe p ∧ PublicControlStaticSafe p ∧ PublicHaltStaticSafe p

def rawRelationalStaticSafeB (p : SemanticProgram) : Bool :=
  secretCTStaticSafeB p && publicControlStaticSafeB p && publicHaltStaticSafeB p

/-- Static machine obligations consumed by the v9 region-derived Public proof.  The retained v8
    continuation heuristic remains available through `RawRelationalStaticSafe`, but v9 obtains
    convergence from its decoded ranked-region analysis instead of that function-local rule. -/
def OperationalStaticSafe (p : SemanticProgram) : Prop :=
  SecretCTStaticSafe p ∧ PublicHaltStaticSafe p

def operationalStaticSafeB (p : SemanticProgram) : Bool :=
  secretCTStaticSafeB p && publicHaltStaticSafeB p

def firstDecodedStaticViolation (p : SemanticProgram) : Option Violation :=
  if !semanticProgramWellFormedB p then some ⟨.malformed, 0, 9⟩
  else match p.instructions.find? (fun instruction => !secretCTInstructionSafeB p instruction) with
  | some instruction => some ⟨.malformed, instruction.id, 9⟩
  | none =>
      match p.instructions.find? (fun instruction =>
          instruction.op == .halt && instruction.blockLabel.neqb .pub) with
      | some instruction => some ⟨.malformed, instruction.id, 9⟩
      | none =>
          let privateLeaves := semanticPrivateLeafReturnFunctions p.source p.sourceIndex p.valueLabels
          match p.source.nodes.find? (fun instruction =>
              instruction.op == .semInstruction &&
                !privateLeaves.getD instruction.origin.toNat false &&
                !semanticPublicControlContinuationOK p.source p.sourceIndex p.valueLabels
                  instruction) with
          | some instruction => some ⟨.malformed, instruction.nodeId, 9⟩
          | none => none

def verifyProgramWithRawSemantics (p : Program) : Option Violation :=
  let index := buildSemanticIndex p
  let labels := semanticLabelsWithIndex p index
  match verifyProgramWithContext p index labels with
  | some violation => some violation
  | none =>
      let decoded := semanticProgramOfWith p index labels
      if rawRelationalStaticSafeB decoded then none
      else some ((firstDecodedStaticViolation decoded).getD ⟨.malformed, 0, 9⟩)

def verifyBytesWithRawSemantics (bytes : ByteArray) : UInt64 :=
  match decode bytes with
  | none => packViolation ⟨.malformed, 0, 0⟩
  | some p =>
      match semanticProgramNode? p with
      | none => packViolation ⟨.malformed, 0, 7⟩
      | some _ => (verifyProgramWithRawSemantics p).map packViolation |>.getD 0

@[export sigil_csir_verify_semantic]
def exportedVerifyWithRawSemantics (bytes : ByteArray) : UInt64 :=
  verifyBytesWithRawSemantics bytes

end LambdaSigil.Combined.Semantic
