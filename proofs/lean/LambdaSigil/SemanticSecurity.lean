import LambdaSigil.SemanticKernel
import Mathlib.Data.List.Basic

/-!
# CSIR semantic machine and delimited-release relational layer

This is a deterministic resolved-instruction semantics.  Aggregate storage and capability tables
are abstract, while scheduling, queues, Wasmtime, and microarchitectural timing remain outside the
model.  The relational policy below is deliberately stated over the actual one-step function; its
two closure theorems therefore compare executions rather than recombining pre-assumed traces.
-/

namespace LambdaSigil.Combined.Semantic

@[simp] theorem semanticInstrOp_beq_true_iff (left right : SemanticInstrOp) :
    (left == right) = true ↔ left = right := by
  cases left <;> cases right <;> decide

@[simp] theorem semanticInstrOp_bne_true_iff (left right : SemanticInstrOp) :
    (left != right) = true ↔ left ≠ right := by
  cases left <;> cases right <;> decide

@[simp] theorem label_beq_true_iff (left right : Label) :
    (left == right) = true ↔ left = right := by
  cases left <;> cases right <;> decide

@[simp] theorem label_bne_true_iff (left right : Label) :
    (left != right) = true ↔ left ≠ right := by
  cases left <;> cases right <;> decide

@[simp] theorem label_eqb_true_iff (left right : Label) :
    left.eqb right = true ↔ left = right := by
  cases left <;> cases right <;> decide

@[simp] theorem label_neqb_true_iff (left right : Label) :
    left.neqb right = true ↔ left ≠ right := by
  cases left <;> cases right <;> decide

theorem operandSliceWellFormedB_iff (p : SemanticProgram) (i : Instruction) :
    operandSliceWellFormedB p i = true ↔ operandSliceWellFormed p i := by
  simp only [operandSliceWellFormedB, operandSliceWellFormed, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨hsize, hall⟩
    refine ⟨hsize, ?_⟩
    intro offset hoffset
    have hitem := hall offset (List.mem_range.mpr hoffset)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hitem
    exact ⟨hitem.1.1, hitem.1.2, hitem.2⟩
  · rintro ⟨hsize, hall⟩
    refine ⟨hsize, ?_⟩
    intro offset hmember
    have hitem := hall offset (List.mem_range.mp hmember)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨hitem.1, hitem.2.1⟩, hitem.2.2⟩

theorem instructionWellFormedB_iff (p : SemanticProgram) (i : Instruction) :
    instructionWellFormedB p i = true ↔ instructionWellFormed p i := by
  simp only [instructionWellFormedB, instructionWellFormed, Bool.and_eq_true,
    bne_iff_ne, beq_iff_eq, label_beq_true_iff, decide_eq_true_eq,
    operandSliceWellFormedB_iff]
  tauto

theorem functionWellFormedB_iff (p : SemanticProgram) (function : Function) :
    functionWellFormedB p function = true ↔ functionWellFormed p function := by
  simp only [functionWellFormedB, functionWellFormed, Bool.and_eq_true, bne_iff_ne,
    decide_eq_true_eq, List.all_eq_true]
  tauto

theorem semanticProgramWellFormedB_iff (p : SemanticProgram) :
    semanticProgramWellFormedB p = true ↔ p.WellFormed := by
  simp only [semanticProgramWellFormedB, SemanticProgram.WellFormed, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, functionWellFormedB_iff,
    instructionWellFormedB_iff]
  constructor
  · rintro ⟨⟨hsize, hfunctions⟩, hinstructions⟩
    exact ⟨hsize, hfunctions, hinstructions⟩
  · rintro ⟨hsize, hfunctions, hinstructions⟩
    exact ⟨⟨hsize, hfunctions⟩, hinstructions⟩

structure Value where
  label : Label
  payload : Int
  deriving Repr, BEq, DecidableEq

inductive EventKind where
  | authority | flow | release | effect | boundary | control | address
  | allocation | cost | trap | output
  deriving Repr, BEq, DecidableEq

def EventKind.eqb : EventKind → EventKind → Bool
  | .authority, .authority | .flow, .flow | .release, .release | .effect, .effect
  | .boundary, .boundary | .control, .control | .address, .address
  | .allocation, .allocation | .cost, .cost | .trap, .trap | .output, .output => true
  | _, _ => false

structure Event where
  kind : EventKind
  payload : Int
  site : UInt32 := 0
  stage : UInt8 := 0
  /-- Static visibility of the event occurrence itself.  For output and actor-boundary events this
      is the verifier-derived instruction pc/occurrence label, independent of payload secrecy. -/
  occurrence : Label := .pub
  /-- Static visibility of a payload-bearing event. Control/address/cost observations remain
      observable regardless of this field; output and boundary filtering consult it together with
      `occurrence`. -/
  label : Label := .pub
  deriving Repr, BEq, DecidableEq

structure CallFrame where
  returnPc : Nat
  destination : UInt32
  calleeId : UInt32
  returnLabel : Label
  /-- Recursive calls reuse global SSA cells, so entry saves and return restores parameter cells. -/
  savedParameters : List (UInt32 × Value) := []
  deriving Repr, BEq, DecidableEq

structure State where
  pc : Nat
  values : Array Value
  aggregates : Array (List Int)
  capabilityBalances : Array Nat
  callStack : List CallFrame := []
  actorState : Array Value := #[]
  externalInputs : Array (List Int) := #[]
  externalCursors : Array Nat := #[]
  halted : Bool := false
  trapped : Bool := false
  deriving Repr, BEq, DecidableEq

structure StepResult where
  state : State
  events : List Event
  deriving Repr, BEq, DecidableEq

def defaultValue : Value := ⟨.pub, 0⟩

def readValue (state : State) (cell : UInt32) : Value :=
  state.values.getD cell.toNat defaultValue

/-- Runtime labels are never trusted.  The decoded, verifier-derived label table is authoritative;
    the state contributes only the raw payload. -/
def readProgramValue (p : SemanticProgram) (state : State) (cell : UInt32) : Value :=
  ⟨labelAt p.valueLabels cell, (readValue state cell).payload⟩

def readActorValue (p : SemanticProgram) (state : State) (offset : UInt32) : Value :=
  ⟨stateLabelAt p offset, (state.actorState[offset.toNat]?).map Value.payload |>.getD 0⟩

@[simp] theorem readProgramValue_label (p : SemanticProgram) (state : State) (cell : UInt32) :
    (readProgramValue p state cell).label = labelAt p.valueLabels cell := rfl

@[simp] theorem readActorValue_label (p : SemanticProgram) (state : State) (offset : UInt32) :
    (readActorValue p state offset).label = stateLabelAt p offset := rfl

def firstOperand? (p : SemanticProgram) (i : Instruction) : Option UInt32 := do
  let operand ← p.operands[i.firstOperand.toNat]?
  if operand.owner == i.id && operand.kind == 0 then some operand.value else none

def operandValues (p : SemanticProgram) (state : State) (i : Instruction) : List Value :=
  (valueOperandCells p i).map (readProgramValue p state)

def operandPayloads (p : SemanticProgram) (state : State) (i : Instruction) : List Int :=
  (operandValues p state i).map Value.payload

def policyOperandValues (p : SemanticProgram) (state : State) (i : Instruction)
    (classCode : UInt32) : List Value :=
  (policyOperandCells p i classCode).map (readProgramValue p state)

def operandValue (p : SemanticProgram) (state : State) (i : Instruction) : Value :=
  (operandValues p state i).head?.getD defaultValue

def functionById? (p : SemanticProgram) (functionId : UInt32) : Option Function :=
  p.functions.find? fun function => function.id == functionId

/-- AIR table entries are emitted in zero-based function order; CSIR function IDs are the same
    order plus one. An out-of-range or negative dynamic table index traps rather than inventing a
    target. -/
def closureFunction? (p : SemanticProgram) (tableIndex : Int) : Option Function := do
  if tableIndex < 0 then none else pure ()
  let functionId := tableIndex.toNat + 1
  if functionId > UInt32.size then none else functionById? p (UInt32.ofNat functionId)

def instructionCallee? (p : SemanticProgram) (state : State) (i : Instruction) :
    Option Function :=
  match i.op with
  | .call => (functionOperand? p i).bind (functionById? p)
  | .closure => (operandValues p state i).head?.bind fun value => closureFunction? p value.payload
  | _ => none

def saveValues (state : State) (cells : List UInt32) : List (UInt32 × Value) :=
  cells.map fun cell => (cell, readValue state cell)

def restoreValues (state : State) : List (UInt32 × Value) → State
  | [] => state
  | (cell, value) :: rest =>
      restoreValues { state with values := state.values.setIfInBounds cell.toNat value } rest

def assignArguments (p : SemanticProgram) (state : State) : List UInt32 → List Value → State
  | parameter :: parameters, argument :: arguments =>
      let assigned : Value := ⟨labelAt p.valueLabels parameter, argument.payload⟩
      assignArguments p
        { state with values := state.values.setIfInBounds parameter.toNat assigned }
        parameters arguments
  | _, _ => state

def argumentLabelsFlow (p : SemanticProgram) : List Value → List UInt32 → Bool
  | [], [] => true
  | argument :: arguments, parameter :: parameters =>
      argument.label.flowsTo (labelAt p.valueLabels parameter) &&
        argumentLabelsFlow p arguments parameters
  | _, _ => false

def callLabelsOK (p : SemanticProgram) (instruction : Instruction) (callee : Function)
    (arguments : List Value) : Bool :=
  argumentLabelsFlow p arguments callee.parameterCells.toList &&
    (instruction.destination == 0 || callee.returnLabel.flowsTo instruction.resultLabel)

def writeDestination (state : State) (i : Instruction) (payload : Int) : State :=
  if i.destination == 0 then state else
    { state with values := state.values.setIfInBounds i.destination.toNat ⟨i.resultLabel, payload⟩ }

@[simp] theorem writeDestination_pc (state : State) (i : Instruction) (payload : Int) :
    (writeDestination state i payload).pc = state.pc := by
  by_cases h : i.destination = 0 <;> simp [writeDestination, h]

@[simp] theorem writeDestination_aggregates (state : State) (i : Instruction) (payload : Int) :
    (writeDestination state i payload).aggregates = state.aggregates := by
  by_cases h : i.destination = 0 <;> simp [writeDestination, h]

@[simp] theorem writeDestination_capabilityBalances (state : State) (i : Instruction)
    (payload : Int) :
    (writeDestination state i payload).capabilityBalances = state.capabilityBalances := by
  by_cases h : i.destination = 0 <;> simp [writeDestination, h]

@[simp] theorem writeDestination_callStack (state : State) (i : Instruction) (payload : Int) :
    (writeDestination state i payload).callStack = state.callStack := by
  by_cases h : i.destination = 0 <;> simp [writeDestination, h]

@[simp] theorem writeDestination_actorState (state : State) (i : Instruction) (payload : Int) :
    (writeDestination state i payload).actorState = state.actorState := by
  by_cases h : i.destination = 0 <;> simp [writeDestination, h]

@[simp] theorem writeDestination_externalInputs (state : State) (i : Instruction) (payload : Int) :
    (writeDestination state i payload).externalInputs = state.externalInputs := by
  by_cases h : i.destination = 0 <;> simp [writeDestination, h]

@[simp] theorem writeDestination_externalCursors (state : State) (i : Instruction)
    (payload : Int) :
    (writeDestination state i payload).externalCursors = state.externalCursors := by
  by_cases h : i.destination = 0 <;> simp [writeDestination, h]

@[simp] theorem writeDestination_halted (state : State) (i : Instruction) (payload : Int) :
    (writeDestination state i payload).halted = state.halted := by
  by_cases h : i.destination = 0 <;> simp [writeDestination, h]

@[simp] theorem writeDestination_trapped (state : State) (i : Instruction) (payload : Int) :
    (writeDestination state i payload).trapped = state.trapped := by
  by_cases h : i.destination = 0 <;> simp [writeDestination, h]

def readExternal (state : State) (site : UInt32) : Int :=
  let stream := state.externalInputs.getD site.toNat []
  let cursor := state.externalCursors.getD site.toNat 0
  stream.getD cursor 0

def advanceExternal (state : State) (site : UInt32) : State :=
  let cursor := state.externalCursors.getD site.toNat 0
  let stream := state.externalInputs.getD site.toNat []
  let externalCursors := if cursor < stream.length then
    state.externalCursors.setIfInBounds site.toNat (cursor + 1)
  else state.externalCursors
  { state with externalCursors }

def nextPc (_p : SemanticProgram) (state : State) (i : Instruction) (operand : Value) : Nat :=
  match i.op with
  | .branch | .loop | .range =>
      if operand.payload = 0 then i.alternate.toNat else i.target.toNat
  | .dispatch =>
      if i.operandCount == 2 then i.target.toNat
      else if operand.payload = 0 then i.alternate.toNat else i.target.toNat
  | .jump | .call => i.target.toNat
  | .scalar | .aggregate | .project | .closure | .actorBoundary | .stateRead | .stateWrite
  | .slotNew | .slotPut | .slotTake | .effect | .abortiveEffect | .ffi | .allocation
  | .address | .index | .capMint | .capRestrict | .capSplit | .capDraw | .capExercise
  | .release | .releaseCT | .ctEq | .ctSelect | .ctLt | .divRem | .stringCompare
  | .output | .trap | .halt => state.pc + 1

def payloadAt (values : List Value) (position : Nat) : Int :=
  (values[position]?).map Value.payload |>.getD 0

@[simp] theorem payloadAt_zero (values : List Value) :
    payloadAt values 0 = (values.head?.map Value.payload).getD 0 := by
  cases values <;> rfl

@[simp] theorem headValue_payload (values : List Value) :
    (values.head?.getD defaultValue).payload = (values.head?.map Value.payload).getD 0 := by
  cases values <;> rfl

def binaryPayload (code : Int) (left right : Int) : Int :=
  match code with
  | 0 => left + right
  | 1 => left - right
  | 2 => left * right
  | 3 => if right = 0 then 0 else left / right
  | 4 => if right = 0 then 0 else left % right
  | 9 => if left = 0 then 0 else if right = 0 then 0 else 1
  | 10 => if left = 0 ∧ right = 0 then 0 else 1
  | 11 => if left < right then 1 else 0
  | 12 => if left ≤ right then 1 else 0
  | 13 => if left > right then 1 else 0
  | 14 => if left ≥ right then 1 else 0
  | 15 => if left = right then 1 else 0
  | 16 => if left = right then 0 else 1
  /- Shifts and bit operations remain deterministic abstract scalar operations here. Their
     security dependence is complete because both operands flow to the result. -/
  | other => left + right * 257 + other

def instructionPayload (p : SemanticProgram) (state : State) (i : Instruction) : Int :=
  let values := operandValues p state i
  let immediates := immediateOperands p i
  match i.op with
  | .scalar =>
      if values.isEmpty then payloadAt (immediates.map fun value => ⟨.pub, value⟩) 1
      else binaryPayload (immediates.getD 1 0) (payloadAt values 0) (payloadAt values 1)
  | .ctEq => if payloadAt values 0 = payloadAt values 1 then 1 else 0
  | .ctLt => if payloadAt values 0 < payloadAt values 1 then 1 else 0
  | .ctSelect => if payloadAt values 0 = 0 then payloadAt values 2 else payloadAt values 1
  | .divRem => binaryPayload (immediates.getD 1 3) (payloadAt values 0) (payloadAt values 1)
  | .stringCompare => if List.Pairwise (fun left right => left = right) (values.map Value.payload)
      then 1 else 0
  | .aggregate => (values.map Value.payload).foldl (fun hash value => hash * 257 + value) 1
  | .allocation =>
      ((policyOperandValues p state i 9).map Value.payload ++ immediates).foldl
        (fun size value => size + value) 0
  | .project | .branch | .jump | .loop | .call | .closure | .actorBoundary | .stateRead
  | .stateWrite | .slotNew | .slotPut | .slotTake | .effect | .abortiveEffect | .ffi
  | .address | .capMint | .capRestrict | .capSplit | .capDraw | .capExercise | .release
  | .releaseCT | .output | .trap | .halt | .range | .dispatch | .index => payloadAt values 0

def eventsForValues (kind : EventKind) (site : UInt32) (values : List Value) : List Event :=
  values.map fun value => { kind, payload := value.payload, site, label := value.label }

/-- Payloads remain raw; only visibility is classified with the verifier-derived pc label. This
    prevents a Public constant emitted on a secret arm from being mistaken for a Public event. -/
def eventsForValuesUnderPc (kind : EventKind) (site : UInt32) (pc : Label)
    (values : List Value) : List Event :=
  values.map fun value =>
    { kind, payload := value.payload, site, occurrence := pc, label := value.label }

def eventsForObserved (kind : EventKind) (site : UInt32) (values : List Value) : List Event :=
  if values.isEmpty then [{ kind, payload := 0, site }] else eventsForValues kind site values

/-- Top-level outputs expose one declaration-owned site per function, not the particular source
    `return` instruction chosen inside that function. Missing V9 metadata falls back to the
    historical instruction site and is rejected by the V9 root checks before authorization. -/
def outputBoundarySite (p : SemanticProgram) (i : Instruction) : UInt32 :=
  p.rootOutputSites[i.functionId.toNat - 1]?.getD i.id

def instructionEvents (p : SemanticProgram) (state : State) (i : Instruction) : List Event :=
  let values := operandValues p state i
  let operand := values.head?.getD defaultValue
  let payload := operand.payload
  match i.op with
  | .branch => eventsForObserved .control i.id (policyOperandValues p state i 0)
  | .loop => eventsForObserved .control i.id (policyOperandValues p state i 1)
  | .range => eventsForObserved .control i.id (policyOperandValues p state i 2)
  | .dispatch => eventsForObserved .control i.id (policyOperandValues p state i 3)
  | .jump => [{ kind := .control, payload := 0, site := i.id }]
  | .actorBoundary =>
      eventsForValuesUnderPc .boundary i.id i.blockLabel (policyOperandValues p state i 8)
  | .stateWrite => eventsForValues .flow i.id (values.drop 1 |>.take 1)
  | .effect | .abortiveEffect => eventsForValues .effect i.id values
  | .ffi => eventsForValues .effect i.id (policyOperandValues p state i 7)
  | .allocation =>
      eventsForObserved .allocation i.id (policyOperandValues p state i 9)
  | .address => eventsForValues .address i.id (policyOperandValues p state i 5)
  | .index => eventsForValues .address i.id
      (policyOperandValues p state i 5 ++ policyOperandValues p state i 4)
  | .stringCompare => eventsForValues .address i.id (policyOperandValues p state i 13)
  | .capMint | .capRestrict | .capSplit | .capDraw | .capExercise =>
      eventsForValues .authority i.id values
  | .release =>
      [{ kind := .release, payload, site := i.id, stage := 1, label := .pub }]
  | .releaseCT =>
      [{ kind := .release, payload, site := i.id, stage := 2, label := .secret }]
  | .ctEq | .ctSelect | .ctLt => [{ kind := .cost, payload := 1, site := i.id }]
  | .divRem =>
      eventsForValues .cost i.id (policyOperandValues p state i 6)
  | .output =>
      [{ kind := .output, payload, site := outputBoundarySite p i,
          occurrence := i.blockLabel,
          label := operand.label.lub i.outputPayloadOccurrence }]
  | .trap => [{ kind := .trap, payload := 0, site := i.id }]
  | .scalar | .aggregate | .project | .call | .closure | .stateRead | .slotNew | .slotPut
  | .slotTake | .halt => []

def ordinaryStep (p : SemanticProgram) (state : State) (i : Instruction) : StepResult :=
  let operand := operandValue p state i
  let written := writeDestination state i (instructionPayload p state i)
  let aggregates := if i.op == SemanticInstrOp.aggregate && i.destination != 0 then
    written.aggregates.setIfInBounds i.destination.toNat (operandPayloads p state i)
  else written.aggregates
  let written := { written with aggregates }
  let written := { written with pc := nextPc p state i operand }
  let written := { written with halted := i.op == SemanticInstrOp.halt }
  let traps := if i.op == SemanticInstrOp.trap then
    (operandValues p state i).isEmpty || operand.payload != 0 else false
  let next := { written with trapped := traps }
  ⟨next, instructionEvents p state i⟩

def callArguments (p : SemanticProgram) (state : State) (i : Instruction) : List Value :=
  if i.op == .closure then (operandValues p state i).drop 1 else operandValues p state i

def callStep (p : SemanticProgram) (state : State) (i : Instruction) : StepResult :=
  match instructionCallee? p state i with
  | none =>
      ⟨{ state with trapped := true }, [{ kind := .trap, payload := 0, site := i.id }]⟩
  | some callee =>
      let arguments := callArguments p state i
      if arguments.length != callee.parameterCells.size || !callLabelsOK p i callee arguments then
        ⟨{ state with trapped := true }, [{ kind := .trap, payload := 0, site := i.id }]⟩
      else
        let parameters := callee.parameterCells.toList
        let saved := saveValues state parameters
        let entered := assignArguments p state parameters arguments
        let frame : CallFrame :=
          { returnPc := state.pc + 1, destination := i.destination, calleeId := callee.id,
            returnLabel := callee.returnLabel, savedParameters := saved }
        let entryPc := callee.firstInstruction.toNat
        let stack := frame :: state.callStack
        let next := { entered with pc := entryPc, callStack := stack }
        ⟨next, []⟩

/-- Deterministic one-step semantics.  Capability balance mutation is abstracted by the v6
    guarded transition; this machine records its authority event and control outcome. -/
def step (p : SemanticProgram) (state : State) : StepResult :=
  if state.halted || state.trapped then ⟨state, []⟩ else
  match p.instructions[state.pc]? with
  | none => ⟨{ state with halted := true }, []⟩
  | some i =>
      let operand := operandValue p state i
      match i.op with
      | .call | .closure =>
          callStep p state i
      | .output =>
          match state.callStack with
          | frame :: rest =>
              if !operand.label.flowsTo frame.returnLabel then
                ⟨{ state with trapped := true },
                  [{ kind := .trap, payload := 0, site := i.id }]⟩
              else
                let restored := restoreValues state frame.savedParameters
                let values := restored.values.setIfInBounds frame.destination.toNat
                  ⟨labelAt p.valueLabels frame.destination, operand.payload⟩
                let returned := if frame.destination == 0 then restored else
                  { restored with values := values }
                ⟨{ returned with pc := frame.returnPc, callStack := rest }, []⟩
          | [] =>
              ⟨{ state with halted := true }, instructionEvents p state i⟩
      | .ffi =>
          let payload := readExternal state i.id
          let advanced := advanceExternal state i.id
          let written := writeDestination advanced i payload
          ⟨{ written with pc := state.pc + 1 }, instructionEvents p state i⟩
      | .actorBoundary =>
          let advanced := if i.destination == 0 then state else advanceExternal state i.id
          let payload := if i.destination == 0 then instructionPayload p state i
            else readExternal state i.id
          let written := writeDestination advanced i payload
          ⟨{ written with pc := state.pc + 1 }, instructionEvents p state i⟩
      | .effect | .abortiveEffect =>
          let advanced := { state with pc := state.pc + 1 }
          let next := { advanced with trapped := i.op == .abortiveEffect }
          ⟨next, instructionEvents p state i⟩
      | .stateRead =>
          let offset := (immediateOperands p i).head?.getD 0
          let payload := if offset < 0 then 0 else
            (readActorValue p state (UInt32.ofNat offset.toNat)).payload
          let written := writeDestination state i payload
          ⟨{ written with pc := state.pc + 1 }, []⟩
      | .stateWrite =>
          let offset := (immediateOperands p i).head?.getD 0
          let value := (operandValues p state i)[1]?.getD defaultValue
          let stored : Value := if offset < 0 then value else
            ⟨stateLabelAt p (UInt32.ofNat offset.toNat), value.payload⟩
          let actorState := if offset < 0 then state.actorState else
            state.actorState.setIfInBounds offset.toNat stored
          ⟨{ state with pc := state.pc + 1, actorState }, instructionEvents p state i⟩
      | .scalar | .aggregate | .project | .branch | .jump | .loop
      | .slotNew | .slotPut | .slotTake
      | .allocation | .address | .capMint | .capRestrict | .capSplit | .capDraw
      | .capExercise | .release | .releaseCT | .ctEq | .ctSelect | .ctLt | .trap | .halt
      | .range | .dispatch | .index | .divRem | .stringCompare =>
          ordinaryStep p state i

def runPrefix (p : SemanticProgram) : Nat → State → StepResult
  | 0, state => ⟨state, []⟩
  | fuel + 1, state =>
      let head := step p state
      let tail := runPrefix p fuel head.state
      ⟨tail.state, head.events ++ tail.events⟩

def releaseEvents (events : List Event) : List Event :=
  events.filter fun event => event.kind.eqb .release

def publicEvents (events : List Event) : List Event :=
  events.filter fun event =>
    let base := !(event.kind.eqb .release) && !(event.kind.eqb .flow) &&
      !(event.kind.eqb .authority) && !(event.kind.eqb .effect)
    let visiblePayload :=
      if event.kind.eqb .output || event.kind.eqb .boundary then
        event.occurrence.eqb .pub && event.label.eqb .pub
      else true
    base && visiblePayload

def outputBoundaryEvents (events : List Event) : List Event :=
  events.filter fun event =>
    (event.kind.eqb .output || event.kind.eqb .boundary) &&
      event.occurrence.eqb .pub && event.label.eqb .pub

/-- Public boundary observations retain occurrence, site, and order independently from payload
    confidentiality. A Public occurrence with a non-Public payload remains in the trace, but the
    payload is hidden rather than replaced by a fabricated value. -/
structure PublicBoundaryObservation where
  kind : EventKind
  site : UInt32
  payload : Option Int
  deriving Repr, BEq, DecidableEq

def publicBoundaryObservation? (event : Event) : Option PublicBoundaryObservation :=
  if (event.kind.eqb .output || event.kind.eqb .boundary) && event.occurrence.eqb .pub then
    some ⟨event.kind, event.site,
      if event.label.eqb .pub then some event.payload else none⟩
  else none

def publicBoundaryTrace (events : List Event) : List PublicBoundaryObservation :=
  events.filterMap publicBoundaryObservation?

@[simp] theorem publicBoundaryTrace_append (left right : List Event) :
    publicBoundaryTrace (left ++ right) =
      publicBoundaryTrace left ++ publicBoundaryTrace right := by
  simp [publicBoundaryTrace]

@[simp] theorem publicEvents_effect_values (site : UInt32) (values : List Value) :
    publicEvents (eventsForValues .effect site values) = [] := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [eventsForValues, publicEvents, EventKind.eqb, ih]

@[simp] theorem publicEvents_authority_values (site : UInt32) (values : List Value) :
    publicEvents (eventsForValues .authority site values) = [] := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [eventsForValues, publicEvents, EventKind.eqb, ih]

@[simp] theorem publicEvents_flow_values (site : UInt32) (values : List Value) :
    publicEvents (eventsForValues .flow site values) = [] := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [eventsForValues, publicEvents, EventKind.eqb, ih]

def ExternalStateWellFormed (state : State) : Prop :=
  state.externalCursors.size = state.externalInputs.size ∧
    ∀ site (h : site < state.externalCursors.size),
      state.externalCursors[site] ≤ (state.externalInputs.getD site []).length

theorem advanceExternal_preserves_well_formed {state : State}
    (h : ExternalStateWellFormed state) (site : UInt32) :
    ExternalStateWellFormed (advanceExternal state site) := by
  rcases h with ⟨hsize, hbound⟩
  simp only [advanceExternal]
  split
  · rename_i hadvance
    constructor
    · simpa only [Array.size_setIfInBounds] using hsize
    · intro other hother
      have hother' : other < state.externalCursors.size := by
        simpa only [Array.size_setIfInBounds] using hother
      rw [Array.getElem_setIfInBounds hother']
      split
      · rename_i heq
        subst other
        simpa using Nat.succ_le_of_lt hadvance
      · exact hbound other hother'
  · exact ⟨hsize, hbound⟩

@[simp] theorem advanceExternal_values (state : State) (site : UInt32) :
    (advanceExternal state site).values = state.values := by
  rfl

@[simp] theorem advanceExternal_aggregates (state : State) (site : UInt32) :
    (advanceExternal state site).aggregates = state.aggregates := by
  rfl

@[simp] theorem advanceExternal_callStack (state : State) (site : UInt32) :
    (advanceExternal state site).callStack = state.callStack := by
  rfl

@[simp] theorem advanceExternal_actorState (state : State) (site : UInt32) :
    (advanceExternal state site).actorState = state.actorState := by
  rfl

@[simp] theorem advanceExternal_externalInputs (state : State) (site : UInt32) :
    (advanceExternal state site).externalInputs = state.externalInputs := by
  rfl

/-- A runtime state is admissible only when every stored label agrees with the program-derived
    label for that cell.  This prevents a theorem caller from forging a more-public runtime label. -/
def StateWellFormed (p : SemanticProgram) (state : State) : Prop :=
  state.values.size = p.valueLabels.size ∧
    state.aggregates.size = p.valueLabels.size ∧
    (state.pc ≤ p.instructions.size ∨ state.halted = true ∨ state.trapped = true) ∧
    ExternalStateWellFormed state ∧
    (∀ frame ∈ state.callStack,
      frame.returnPc ≤ p.instructions.size ∧
        (frame.destination == 0 ∨ frame.destination.toNat < p.valueLabels.size) ∧
        frame.calleeId != 0 ∧
        (frame.destination == 0 ||
          frame.returnLabel.flowsTo (labelAt p.valueLabels frame.destination)) = true ∧
        ∀ saved ∈ frame.savedParameters, saved.1.toNat < p.valueLabels.size)

@[simp] theorem restoreValues_size (state : State) (saved : List (UInt32 × Value)) :
    (restoreValues state saved).values.size = state.values.size := by
  induction saved generalizing state with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨cell, value⟩
      simp [restoreValues, ih]

@[simp] theorem assignArguments_size (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    (assignArguments p state parameters arguments).values.size = state.values.size := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons parameter parameters ih =>
      cases arguments with
      | nil => rfl
      | cons argument arguments => simp [assignArguments, ih]

@[simp] theorem assignArguments_pc (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    (assignArguments p state parameters arguments).pc = state.pc := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons _ _ ih => cases arguments <;> simp [assignArguments, ih]

@[simp] theorem assignArguments_capabilityBalances (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    (assignArguments p state parameters arguments).capabilityBalances =
      state.capabilityBalances := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons _ _ ih => cases arguments <;> simp [assignArguments, ih]

@[simp] theorem assignArguments_aggregates (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    (assignArguments p state parameters arguments).aggregates = state.aggregates := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons _ _ ih => cases arguments <;> simp [assignArguments, ih]

@[simp] theorem assignArguments_externalInputs (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    (assignArguments p state parameters arguments).externalInputs = state.externalInputs := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons _ _ ih => cases arguments <;> simp [assignArguments, ih]

@[simp] theorem assignArguments_externalCursors (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    (assignArguments p state parameters arguments).externalCursors = state.externalCursors := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons _ _ ih => cases arguments <;> simp [assignArguments, ih]

@[simp] theorem assignArguments_callStack (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    (assignArguments p state parameters arguments).callStack = state.callStack := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons _ _ ih => cases arguments <;> simp [assignArguments, ih]

@[simp] theorem assignArguments_actorState (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    (assignArguments p state parameters arguments).actorState = state.actorState := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons _ _ ih => cases arguments <;> simp [assignArguments, ih]

@[simp] theorem assignArguments_halted (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    (assignArguments p state parameters arguments).halted = state.halted := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons _ _ ih => cases arguments <;> simp [assignArguments, ih]

@[simp] theorem assignArguments_trapped (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    (assignArguments p state parameters arguments).trapped = state.trapped := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons _ _ ih => cases arguments <;> simp [assignArguments, ih]

@[simp] theorem restoreValues_aggregates (state : State) (saved : List (UInt32 × Value)) :
    (restoreValues state saved).aggregates = state.aggregates := by
  induction saved generalizing state with
  | nil => rfl
  | cons head tail ih => rcases head with ⟨cell, value⟩; simp [restoreValues, ih]

@[simp] theorem restoreValues_pc (state : State) (saved : List (UInt32 × Value)) :
    (restoreValues state saved).pc = state.pc := by
  induction saved generalizing state with
  | nil => rfl
  | cons head tail ih => rcases head with ⟨cell, value⟩; simp [restoreValues, ih]

@[simp] theorem restoreValues_capabilityBalances (state : State)
    (saved : List (UInt32 × Value)) :
    (restoreValues state saved).capabilityBalances = state.capabilityBalances := by
  induction saved generalizing state with
  | nil => rfl
  | cons head tail ih => rcases head with ⟨cell, value⟩; simp [restoreValues, ih]

@[simp] theorem restoreValues_callStack (state : State) (saved : List (UInt32 × Value)) :
    (restoreValues state saved).callStack = state.callStack := by
  induction saved generalizing state with
  | nil => rfl
  | cons head tail ih => rcases head with ⟨cell, value⟩; simp [restoreValues, ih]

@[simp] theorem restoreValues_externalInputs (state : State) (saved : List (UInt32 × Value)) :
    (restoreValues state saved).externalInputs = state.externalInputs := by
  induction saved generalizing state with
  | nil => rfl
  | cons head tail ih => rcases head with ⟨cell, value⟩; simp [restoreValues, ih]

@[simp] theorem restoreValues_externalCursors (state : State) (saved : List (UInt32 × Value)) :
    (restoreValues state saved).externalCursors = state.externalCursors := by
  induction saved generalizing state with
  | nil => rfl
  | cons head tail ih => rcases head with ⟨cell, value⟩; simp [restoreValues, ih]

@[simp] theorem restoreValues_actorState (state : State) (saved : List (UInt32 × Value)) :
    (restoreValues state saved).actorState = state.actorState := by
  induction saved generalizing state with
  | nil => rfl
  | cons head tail ih => rcases head with ⟨cell, value⟩; simp [restoreValues, ih]

@[simp] theorem restoreValues_halted (state : State) (saved : List (UInt32 × Value)) :
    (restoreValues state saved).halted = state.halted := by
  induction saved generalizing state with
  | nil => rfl
  | cons head tail ih => rcases head with ⟨cell, value⟩; simp [restoreValues, ih]

@[simp] theorem restoreValues_trapped (state : State) (saved : List (UInt32 × Value)) :
    (restoreValues state saved).trapped = state.trapped := by
  induction saved generalizing state with
  | nil => rfl
  | cons head tail ih => rcases head with ⟨cell, value⟩; simp [restoreValues, ih]

theorem functionById_well_formed {p : SemanticProgram} (hp : p.WellFormed)
    {functionId : UInt32} {function : Function}
    (hfind : functionById? p functionId = some function) : functionWellFormed p function := by
  exact hp.2.1 function (by
    simpa using Array.mem_of_find?_eq_some hfind)

theorem instructionCallee_well_formed {p : SemanticProgram} (hp : p.WellFormed)
    {state : State} {instruction : Instruction} {function : Function}
    (hfind : instructionCallee? p state instruction = some function) :
    functionWellFormed p function := by
  cases hop : instruction.op <;>
    simp only [instructionCallee?, hop] at hfind
  case call =>
    rw [Option.bind_eq_some_iff] at hfind
    rcases hfind with ⟨functionId, _, hfunction⟩
    exact functionById_well_formed hp hfunction
  case closure =>
    rw [Option.bind_eq_some_iff] at hfind
    rcases hfind with ⟨tableValue, _, hclosure⟩
    unfold closureFunction? at hclosure
    split at hclosure <;> simp_all
    rcases hclosure with ⟨_, hclosure⟩
    exact functionById_well_formed hp hclosure
  all_goals contradiction

theorem saveValues_cell_mem {state : State} {cells : List UInt32}
    {saved : UInt32 × Value} (h : saved ∈ saveValues state cells) : saved.1 ∈ cells := by
  rcases List.mem_map.mp h with ⟨cell, hcell, rfl⟩
  exact hcell

theorem trap_preserves_well_formed {p : SemanticProgram} {state : State}
    (hs : StateWellFormed p state) : StateWellFormed p { state with trapped := true } := by
  rcases hs with ⟨hvalues, haggregates, _, hexternal, hframes⟩
  exact ⟨hvalues, haggregates, Or.inr (Or.inr rfl), hexternal, hframes⟩

/-- Entering a decoded callee only rewrites declared parameter cells and pushes a frame whose
    shape is justified by the instruction and callee contracts. Keeping this lemma separate makes
    call-frame preservation insensitive to simplifier heuristics in the constructor census. -/
theorem enterCall_preserves_well_formed {p : SemanticProgram} {state : State}
    {instruction : Instruction} {callee : Function} {arguments : List Value}
    (hs : StateWellFormed p state) (hpc : state.pc < p.instructions.size)
    (hi : instructionWellFormed p instruction)
    (hf : functionWellFormed p callee) (hlabels : callLabelsOK p instruction callee arguments = true) :
    StateWellFormed p
      { assignArguments p state callee.parameterCells.toList arguments with
        pc := callee.firstInstruction.toNat
        callStack :=
          { returnPc := state.pc + 1
            destination := instruction.destination
            calleeId := callee.id
            returnLabel := callee.returnLabel
            savedParameters := saveValues state callee.parameterCells.toList } :: state.callStack } := by
  rcases hs with ⟨hvalues, haggregates, _, hexternal, hframes⟩
  rcases hi with ⟨_, hdestination, hresult, _, _, _⟩
  rcases hf with ⟨hcallee, hentry, hparameters⟩
  have hlabels' := hlabels
  simp only [callLabelsOK, Bool.and_eq_true] at hlabels'
  have hreturn := hlabels'.2
  constructor
  · simpa using hvalues
  constructor
  · simpa using haggregates
  constructor
  · exact Or.inl (Nat.le_of_lt hentry)
  constructor
  · simpa only [ExternalStateWellFormed, assignArguments_externalInputs,
      assignArguments_externalCursors] using hexternal
  · intro frame hframe
    simp only [List.mem_cons] at hframe
    rcases hframe with rfl | hframe
    · constructor
      · exact Nat.succ_le_of_lt hpc
      constructor
      · exact hdestination
      constructor
      · exact hcallee
      constructor
      · simpa [hresult] using hreturn
      · intro saved hsaved
        exact hparameters saved.1 (saveValues_cell_mem hsaved)
    · exact hframes frame hframe

set_option maxHeartbeats 800000

/-- Every constructor of the raw machine preserves the decoded state shape. Runtime payloads are
    unconstrained; labels are always reattached by `readProgramValue` and `readActorValue`. -/
theorem state_well_formed_preserved {p : SemanticProgram} (hp : p.WellFormed)
    {state : State} (hs : StateWellFormed p state) :
    StateWellFormed p (step p state).state := by
  simp only [step]
  split
  · exact hs
  · rename_i hactive
    split
    · rcases hs with ⟨hvalues, haggregates, _, hexternal, hframes⟩
      exact ⟨hvalues, haggregates, Or.inr (Or.inl rfl), hexternal, hframes⟩
    · rename_i instruction hlookup
      have hpc : state.pc < p.instructions.size :=
        (Array.getElem?_eq_some_iff.mp hlookup).1
      have hinstruction : instructionWellFormed p instruction := hp.2.2 instruction (by
        simpa using Array.mem_of_getElem? hlookup)
      rcases hs with ⟨hvalues, haggregates, hcontrol, hexternal, hframes⟩
      generalize hop : instruction.op = op at *
      cases op
      case call =>
        cases hcallee : instructionCallee? p state instruction with
        | none =>
            simp_all [callStep, StateWellFormed, ExternalStateWellFormed,
              instructionWellFormed]
            grind
        | some callee =>
            have hcalleeWF := instructionCallee_well_formed hp hcallee
            simp only [callStep, hcallee]
            split <;> rename_i hguard
            · exact trap_preserves_well_formed
                ⟨hvalues, haggregates, hcontrol, hexternal, hframes⟩
            · have hlabels : callLabelsOK p instruction callee
                  (operandValues p state instruction) = true := by
                simp_all [callArguments, hop]
              have hentered := enterCall_preserves_well_formed
                ⟨hvalues, haggregates, hcontrol, hexternal, hframes⟩ hpc hinstruction
                hcalleeWF hlabels
              simpa [callArguments, hop] using hentered
      case closure =>
        cases hcallee : instructionCallee? p state instruction with
        | none =>
            simp_all [callStep, StateWellFormed, ExternalStateWellFormed,
              instructionWellFormed]
            grind
        | some callee =>
            have hcalleeWF := instructionCallee_well_formed hp hcallee
            simp only [callStep, hcallee]
            split <;> rename_i hguard
            · exact trap_preserves_well_formed
                ⟨hvalues, haggregates, hcontrol, hexternal, hframes⟩
            · have hlabels : callLabelsOK p instruction callee
                  ((operandValues p state instruction).drop 1) = true := by
                simp_all [callArguments, hop]
              have hentered := enterCall_preserves_well_formed
                ⟨hvalues, haggregates, hcontrol, hexternal, hframes⟩ hpc hinstruction
                hcalleeWF hlabels
              simpa [callArguments, hop] using hentered
      case actorBoundary =>
        have hadvance := advanceExternal_preserves_well_formed hexternal instruction.id
        by_cases hdestination : instruction.destination = 0 <;>
          simp_all [StateWellFormed, ExternalStateWellFormed, instructionWellFormed,
            writeDestination, Array.size_setIfInBounds] <;> grind
      case ffi =>
        have hadvance := advanceExternal_preserves_well_formed hexternal instruction.id
        by_cases hdestination : instruction.destination = 0 <;>
          simp_all [StateWellFormed, ExternalStateWellFormed, instructionWellFormed,
            writeDestination, Array.size_setIfInBounds] <;> grind
      case output =>
        cases hstack : state.callStack with
        | nil =>
            simp_all [StateWellFormed, ExternalStateWellFormed]
            grind
        | cons frame rest =>
            have hframe := hframes frame (by simp [hstack])
            by_cases hflow : (operandValue p state instruction).label.flowsTo
                frame.returnLabel = false
            · simp_all [StateWellFormed, ExternalStateWellFormed]
              grind
            · by_cases hreturn : frame.destination = 0 <;>
                simp_all [StateWellFormed, ExternalStateWellFormed,
                  Array.size_setIfInBounds] <;> grind
      all_goals
        by_cases hdestination : instruction.destination = 0 <;>
          simp_all [StateWellFormed, ExternalStateWellFormed, instructionWellFormed,
            Array.size_setIfInBounds, writeDestination, nextPc, ordinaryStep] <;> try grind

set_option maxHeartbeats 200000

theorem cellsAvoidSecretCTB_iff (p : SemanticProgram) (cells : List UInt32) :
    cellsAvoidSecretCTB p cells = true ↔ cellsAvoidSecretCT p cells := by
  simp only [cellsAvoidSecretCTB, cellsAvoidSecretCT, List.all_eq_true]
  constructor
  · intro hall cell hcell
    exact (label_bne_true_iff _ _).mp (hall cell hcell)
  · intro hall cell hcell
    exact (label_bne_true_iff _ _).mpr (hall cell hcell)

theorem observedCellsAvoidSecretCTB_iff (p : SemanticProgram) (instruction : Instruction) :
    observedCellsAvoidSecretCTB p instruction = true ↔
      observedCellsAvoidSecretCT p instruction := by
  simp [observedCellsAvoidSecretCTB, observedCellsAvoidSecretCT, cellsAvoidSecretCTB_iff]

theorem resultDependenciesAvoidSecretCTB_iff (p : SemanticProgram)
    (instruction : Instruction) :
    resultDependenciesAvoidSecretCTB p instruction = true ↔
      resultDependenciesAvoidSecretCT p instruction := by
  by_cases hdestination : instruction.destination = 0
  · simp [resultDependenciesAvoidSecretCTB, resultDependenciesAvoidSecretCT, hdestination]
  by_cases hresult : instruction.resultLabel = .secretCT
  · have hdestinationB : (instruction.destination == 0) = false := by
      simp [hdestination]
    have hresultB : instruction.resultLabel.eqb Label.secretCT = true :=
      (label_eqb_true_iff _ _).mpr hresult
    simp [resultDependenciesAvoidSecretCTB, resultDependenciesAvoidSecretCT, hdestination,
      hdestinationB, hresult, hresultB]
  have hdestinationB : (instruction.destination == 0) = false := by simp [hdestination]
  have hresultB : instruction.resultLabel.eqb Label.secretCT = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hresult ((label_eqb_true_iff _ _).mp htrue)
  generalize hop : instruction.op = op at *
  cases op <;> simp_all [resultDependenciesAvoidSecretCTB, resultDependenciesAvoidSecretCT,
    cellsAvoidSecretCTB_iff, decide_eq_true_eq, hdestinationB, hresultB]

theorem stateWriteAvoidsSecretCTB_iff (p : SemanticProgram) (instruction : Instruction) :
    stateWriteAvoidsSecretCTB p instruction = true ↔
      stateWriteAvoidsSecretCT p instruction := by
  generalize hop : instruction.op = op at *
  cases op <;> simp_all [stateWriteAvoidsSecretCTB, stateWriteAvoidsSecretCT]
  case stateWrite =>
    let offset := (immediateOperands p instruction).head?.getD 0
    by_cases hnegative : offset < 0
    · simp [offset, hnegative]
    by_cases hstate : stateLabelAt p (UInt32.ofNat offset.toNat) = .secretCT
    · simp [offset, hnegative, hstate, Label.eqb]
    cases hcell : (valueOperandCells p instruction)[1]? with
    | none => simp [offset, hnegative, hstate, hcell, Label.eqb]
    | some cell =>
        simp [offset, hnegative, hstate, hcell, label_neqb_true_iff]

theorem controlAvoidsSecretCTB_iff (p : SemanticProgram) (instruction : Instruction) :
    controlAvoidsSecretCTB p instruction = true ↔
      (instruction.op = .branch ∨ instruction.op = .loop ∨ instruction.op = .range ∨
        (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2) ∨
        instruction.op = .closure ∨
        (instruction.op = .trap ∧ instruction.operandCount ≠ 0) →
          match (valueOperandCells p instruction).head? with
          | some cell => labelAt p.valueLabels cell ≠ .secretCT
          | none => False) := by
  generalize hop : instruction.op = op at *
  cases op <;>
    simp_all [controlAvoidsSecretCTB] <;>
    try { by_cases hcount : instruction.operandCount = 2 <;> simp_all } <;>
    try { by_cases hcount : instruction.operandCount = 0 <;> simp_all } <;>
    cases hhead : (valueOperandCells p instruction).head? <;>
    simp_all [controlAvoidsSecretCTB, hhead, label_neqb_true_iff] <;> tauto

theorem secretCTInstructionSafeB_iff (p : SemanticProgram) (instruction : Instruction) :
    secretCTInstructionSafeB p instruction = true ↔
      SecretCTInstructionSafe p instruction := by
  simp only [secretCTInstructionSafeB, SecretCTInstructionSafe, Bool.and_eq_true,
    observedCellsAvoidSecretCTB_iff, resultDependenciesAvoidSecretCTB_iff,
    stateWriteAvoidsSecretCTB_iff, controlAvoidsSecretCTB_iff]
  tauto

theorem secretCTStaticSafeB_iff (p : SemanticProgram) :
    secretCTStaticSafeB p = true ↔ SecretCTStaticSafe p := by
  simp only [secretCTStaticSafeB, SecretCTStaticSafe, Bool.and_eq_true,
    semanticProgramWellFormedB_iff, List.all_eq_true, secretCTInstructionSafeB_iff]

theorem publicControlStaticSafeB_iff (p : SemanticProgram) :
    publicControlStaticSafeB p = true ↔ PublicControlStaticSafe p := by
  simp only [publicControlStaticSafeB, PublicControlStaticSafe, List.all_eq_true]
  constructor
  · intro hall instruction hmem hop
    have hitem := hall instruction hmem
    simpa only [if_pos hop] using hitem
  · intro hall instruction hmem
    by_cases hop : (instruction.op == .semInstruction) = true
    · simpa only [if_pos hop] using hall instruction hmem hop
    · simp only [if_neg hop]

theorem publicHaltStaticSafeB_iff (p : SemanticProgram) :
    publicHaltStaticSafeB p = true ↔ PublicHaltStaticSafe p := by
  simp only [publicHaltStaticSafeB, PublicHaltStaticSafe, List.all_eq_true,
    Bool.or_eq_true, semanticInstrOp_bne_true_iff, label_eqb_true_iff]
  constructor
  · intro hall instruction hmem hop
    exact (hall instruction hmem).resolve_left (fun hne => hne hop)
  · intro hall instruction hmem
    by_cases hop : instruction.op = .halt
    · exact Or.inr (hall instruction hmem hop)
    · exact Or.inl hop

theorem rawRelationalStaticSafeB_iff (p : SemanticProgram) :
    rawRelationalStaticSafeB p = true ↔ RawRelationalStaticSafe p := by
  simp [rawRelationalStaticSafeB, RawRelationalStaticSafe, secretCTStaticSafeB_iff,
    publicControlStaticSafeB_iff, publicHaltStaticSafeB_iff, and_assoc]

theorem operationalStaticSafeB_iff (p : SemanticProgram) :
    operationalStaticSafeB p = true ↔ OperationalStaticSafe p := by
  simp [operationalStaticSafeB, OperationalStaticSafe, secretCTStaticSafeB_iff,
    publicHaltStaticSafeB_iff]

/-! ## Raw relational surface -/

def PublicActorEquivalent (p : SemanticProgram) (left right : Array Value) : Prop :=
  left.size = right.size ∧ ∀ offset (hl : offset < left.size) (hr : offset < right.size),
    stateLabelAt p (UInt32.ofNat offset) = .pub → left[offset].payload = right[offset].payload

def PublicAggregateEquivalent (p : SemanticProgram) (left right : Array (List Int)) : Prop :=
  left.size = right.size ∧ ∀ cell (hl : cell < left.size) (hr : cell < right.size),
    labelAt p.valueLabels (UInt32.ofNat cell) = .pub → left[cell] = right[cell]

def SecretCTActorEquivalent (p : SemanticProgram) (left right : Array Value) : Prop :=
  left.size = right.size ∧ ∀ offset (hl : offset < left.size) (hr : offset < right.size),
    stateLabelAt p (UInt32.ofNat offset) ≠ .secretCT →
      left[offset].payload = right[offset].payload

def SecretCTAggregateEquivalent (p : SemanticProgram) (left right : Array (List Int)) : Prop :=
  left.size = right.size ∧ ∀ cell (hl : cell < left.size) (hr : cell < right.size),
    labelAt p.valueLabels (UInt32.ofNat cell) ≠ .secretCT → left[cell] = right[cell]

def SavedSecretCTEquivalent (p : SemanticProgram) :
    List (UInt32 × Value) → List (UInt32 × Value) → Prop
  | [], [] => True
  | (leftCell, leftValue) :: leftRest, (rightCell, rightValue) :: rightRest =>
      leftCell = rightCell ∧
        (labelAt p.valueLabels leftCell ≠ .secretCT → leftValue.payload = rightValue.payload) ∧
        SavedSecretCTEquivalent p leftRest rightRest
  | _, _ => False

def CallFrameSecretCTEquivalent (p : SemanticProgram) (left right : CallFrame) : Prop :=
  left.returnPc = right.returnPc ∧ left.destination = right.destination ∧
    left.calleeId = right.calleeId ∧ left.returnLabel = right.returnLabel ∧
    SavedSecretCTEquivalent p left.savedParameters right.savedParameters

def CallStackSecretCTEquivalent (p : SemanticProgram) : List CallFrame → List CallFrame → Prop
  | [], [] => True
  | left :: leftRest, right :: rightRest =>
      CallFrameSecretCTEquivalent p left right ∧
        CallStackSecretCTEquivalent p leftRest rightRest
  | _, _ => False

def externalSiteLabel (p : SemanticProgram) (site : Nat) : Label :=
  match p.instructions.find? (fun instruction => instruction.id.toNat == site) with
  | some instruction => instruction.blockLabel
  | none => .pub

/-- Streams are immutable and shared. Cursor equality is required exactly at sites whose next
    input can affect Public state; activity at a non-Public site cannot shift another site. -/
def PublicExternalEquivalent (p : SemanticProgram) (left right : State) : Prop :=
  left.externalInputs = right.externalInputs ∧
    left.externalCursors.size = right.externalCursors.size ∧
    ∀ site (hl : site < left.externalCursors.size) (hr : site < right.externalCursors.size),
      externalSiteLabel p site = .pub →
        left.externalCursors[site] = right.externalCursors[site]

def SavedPublicEquivalent (p : SemanticProgram) :
    List (UInt32 × Value) → List (UInt32 × Value) → Prop
  | [], [] => True
  | (leftCell, leftValue) :: leftRest, (rightCell, rightValue) :: rightRest =>
      leftCell = rightCell ∧
        (labelAt p.valueLabels leftCell = .pub → leftValue.payload = rightValue.payload) ∧
        SavedPublicEquivalent p leftRest rightRest
  | _, _ => False

def CallFramePublicEquivalent (p : SemanticProgram) (left right : CallFrame) : Prop :=
  left.returnPc = right.returnPc ∧ left.destination = right.destination ∧
    left.calleeId = right.calleeId ∧ left.returnLabel = right.returnLabel ∧
    SavedPublicEquivalent p left.savedParameters right.savedParameters

def CallStackPublicEquivalent (p : SemanticProgram) : List CallFrame → List CallFrame → Prop
  | [], [] => True
  | left :: leftRest, right :: rightRest =>
      CallFramePublicEquivalent p left right ∧ CallStackPublicEquivalent p leftRest rightRest
  | _, _ => False

/-- The public data projection deliberately excludes control. It is the relation restored at a
    structured continuation and compared after two independently long successful executions. -/
def PublicDataEquivalent (p : SemanticProgram) (left right : State) : Prop :=
  PublicExternalEquivalent p left right ∧
    PublicActorEquivalent p left.actorState right.actorState ∧
    PublicAggregateEquivalent p left.aggregates right.aggregates ∧
    left.values.size = p.valueLabels.size ∧ right.values.size = p.valueLabels.size ∧
    ∀ cell (hl : cell < left.values.size) (hr : cell < right.values.size),
      labelAt p.valueLabels (UInt32.ofNat cell) = .pub →
        left.values[cell].payload = right.values[cell].payload

/-- Entry/cut-point equivalence adds real control and frame alignment. Secret-region stuttering is
    expressed separately, so theorem callers cannot choose unrelated starting instructions. -/
def PublicLowEquivalent (p : SemanticProgram) (left right : State) : Prop :=
  left.pc = right.pc ∧ left.halted = right.halted ∧ left.trapped = right.trapped ∧
    CallStackPublicEquivalent p left.callStack right.callStack ∧
    PublicDataEquivalent p left right

/-- SecretCT comparison is lockstep: control and all non-SecretCT payloads agree. -/
def SecretCTLowEquivalent (p : SemanticProgram) (left right : State) : Prop :=
  left.pc = right.pc ∧ left.halted = right.halted ∧ left.trapped = right.trapped ∧
    CallStackSecretCTEquivalent p left.callStack right.callStack ∧
    SecretCTAggregateEquivalent p left.aggregates right.aggregates ∧
    SecretCTActorEquivalent p left.actorState right.actorState ∧
    left.capabilityBalances = right.capabilityBalances ∧
    left.externalInputs = right.externalInputs ∧ left.externalCursors = right.externalCursors ∧
    left.values.size = p.valueLabels.size ∧ right.values.size = p.valueLabels.size ∧
    ∀ cell (hl : cell < left.values.size) (hr : cell < right.values.size),
      labelAt p.valueLabels (UInt32.ofNat cell) ≠ .secretCT →
        left.values[cell].payload = right.values[cell].payload

def SecretCTValuesEquivalent (p : SemanticProgram) (left right : Array Value) : Prop :=
  left.size = p.valueLabels.size ∧ right.size = p.valueLabels.size ∧
    ∀ cell (hl : cell < left.size) (hr : cell < right.size),
      labelAt p.valueLabels (UInt32.ofNat cell) ≠ .secretCT →
        left[cell].payload = right[cell].payload

theorem secretCT_values_of_low {p : SemanticProgram} {left right : State}
    (h : SecretCTLowEquivalent p left right) :
    SecretCTValuesEquivalent p left.values right.values :=
  ⟨h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2⟩

theorem SecretCTValuesEquivalent.setIfInBounds {p : SemanticProgram}
    {left right : Array Value} (h : SecretCTValuesEquivalent p left right)
    (cell : UInt32) (leftValue rightValue : Value)
    (hpayload : labelAt p.valueLabels cell ≠ .secretCT →
      leftValue.payload = rightValue.payload) :
    SecretCTValuesEquivalent p
      (left.setIfInBounds cell.toNat leftValue) (right.setIfInBounds cell.toNat rightValue) := by
  refine ⟨by simp [h.1], by simp [h.2.1], ?_⟩
  intro observed hl hr hlabel
  have hl' : observed < left.size := by simpa using hl
  have hr' : observed < right.size := by simpa using hr
  rw [Array.getElem_setIfInBounds hl', Array.getElem_setIfInBounds hr']
  by_cases heq : cell.toNat = observed
  · subst observed
    simp only [if_pos rfl]
    exact hpayload (by simpa using hlabel)
  · simp only [heq, ↓reduceIte]
    exact h.2.2 _ hl' hr' hlabel

theorem writeDestination_preserves_secretCT_values {p : SemanticProgram}
    {left right : State} (h : SecretCTValuesEquivalent p left.values right.values)
    (instruction : Instruction) (leftPayload rightPayload : Int)
    (hpayload : instruction.destination ≠ 0 → instruction.resultLabel ≠ .secretCT →
      leftPayload = rightPayload)
    (hresult : instruction.resultLabel = labelAt p.valueLabels instruction.destination) :
    SecretCTValuesEquivalent p
      (writeDestination left instruction leftPayload).values
      (writeDestination right instruction rightPayload).values := by
  simp only [writeDestination]
  split <;> rename_i hdestination
  · exact h
  · apply h.setIfInBounds
    intro hlabel
    apply hpayload
    · simpa using hdestination
    · intro heq
      apply hlabel
      rw [← hresult]
      exact heq

theorem readProgramValue_eq_of_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (cell : UInt32)
    (hnonct : labelAt p.valueLabels cell ≠ .secretCT) :
    readProgramValue p left cell = readProgramValue p right cell := by
  rcases hlow with ⟨_, _, _, _, _, _, _, _, _, hleftSize, hrightSize, hvalues⟩
  unfold readProgramValue
  congr 1
  ·
    by_cases hcell : cell.toNat < p.valueLabels.size
    · have hleft : cell.toNat < left.values.size := by simpa [hleftSize]
      have hright : cell.toNat < right.values.size := by simpa [hrightSize]
      simpa [readValue, Array.getD, hleft, hright] using
        hvalues cell.toNat hleft hright (by simpa using hnonct)
    · have hleft : ¬cell.toNat < left.values.size := fun h =>
        hcell (by simpa [hleftSize] using h)
      have hright : ¬cell.toNat < right.values.size := fun h =>
        hcell (by simpa [hrightSize] using h)
      simp [readValue, Array.getD, hleft, hright]

theorem readValue_payload_eq_of_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (cell : UInt32)
    (hnonct : labelAt p.valueLabels cell ≠ .secretCT) :
    (readValue left cell).payload = (readValue right cell).payload := by
  have h := congrArg Value.payload (readProgramValue_eq_of_secretCT_low hlow cell hnonct)
  simpa [readProgramValue] using h

theorem saveValues_secretCT_equivalent {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (cells : List UInt32) :
    SavedSecretCTEquivalent p (saveValues left cells) (saveValues right cells) := by
  induction cells with
  | nil => trivial
  | cons cell rest ih =>
      refine ⟨rfl, ?_, ih⟩
      intro hnonct
      exact readValue_payload_eq_of_secretCT_low hlow cell hnonct

def ValueListSecretCTEquivalent : List Value → List Value → Prop
  | [], [] => True
  | left :: leftRest, right :: rightRest =>
      left.label = right.label ∧
        (left.label ≠ .secretCT → left.payload = right.payload) ∧
        ValueListSecretCTEquivalent leftRest rightRest
  | _, _ => False

theorem operandValues_secretCT_equivalent {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (instruction : Instruction) :
    ValueListSecretCTEquivalent (operandValues p left instruction)
      (operandValues p right instruction) := by
  unfold operandValues
  induction valueOperandCells p instruction with
  | nil => trivial
  | cons cell rest ih =>
      refine ⟨rfl, ?_, ih⟩
      intro hnonct
      exact congrArg Value.payload (readProgramValue_eq_of_secretCT_low hlow cell hnonct)

theorem ValueListSecretCTEquivalent.drop {left right : List Value}
    (h : ValueListSecretCTEquivalent left right) (count : Nat) :
    ValueListSecretCTEquivalent (left.drop count) (right.drop count) := by
  induction count generalizing left right with
  | zero => simpa
  | succ count ih =>
      cases left <;> cases right <;> simp_all [ValueListSecretCTEquivalent]

theorem ValueListSecretCTEquivalent.length_eq {left right : List Value}
    (h : ValueListSecretCTEquivalent left right) : left.length = right.length := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [ValueListSecretCTEquivalent]
  | cons head tail ih =>
      cases right with
      | nil => simp [ValueListSecretCTEquivalent] at h
      | cons rightHead rightTail =>
          have hlength := ih h.2.2
          simp only [List.length_cons]
          omega

theorem flowing_argument_payload_eq {argumentLeft argumentRight : Value} {parameter : Label}
    (hequivalent : argumentLeft.label = argumentRight.label ∧
      (argumentLeft.label ≠ .secretCT → argumentLeft.payload = argumentRight.payload))
    (hflow : argumentLeft.label.flowsTo parameter = true)
    (hnonct : parameter ≠ .secretCT) :
    argumentLeft.payload = argumentRight.payload := by
  rcases hequivalent with ⟨hlabel, hpayload⟩
  apply hpayload
  intro hct
  rw [hct] at hflow
  cases parameter <;> simp_all [Label.flowsTo, Label.rank]

theorem assignArguments_preserves_secretCT_values {p : SemanticProgram}
    {left right : State} {leftArguments rightArguments : List Value}
    {parameters : List UInt32}
    (hvalues : SecretCTValuesEquivalent p left.values right.values)
    (harguments : ValueListSecretCTEquivalent leftArguments rightArguments)
    (hflow : argumentLabelsFlow p leftArguments parameters = true) :
    SecretCTValuesEquivalent p
      (assignArguments p left parameters leftArguments).values
      (assignArguments p right parameters rightArguments).values := by
  induction parameters generalizing left right leftArguments rightArguments with
  | nil =>
      cases leftArguments <;> cases rightArguments <;>
        simp_all [assignArguments, argumentLabelsFlow, ValueListSecretCTEquivalent]
  | cons parameter parameters ih =>
      cases leftArguments with
      | nil => simp [argumentLabelsFlow] at hflow
      | cons leftArgument leftRest =>
          cases rightArguments with
          | nil => simp [ValueListSecretCTEquivalent] at harguments
          | cons rightArgument rightRest =>
              rcases harguments with ⟨hlabel, hpayload, hrest⟩
              simp only [argumentLabelsFlow, Bool.and_eq_true] at hflow
              apply ih
              · apply hvalues.setIfInBounds
                intro hparameter
                exact flowing_argument_payload_eq
                  (argumentLeft := leftArgument) (argumentRight := rightArgument)
                  ⟨hlabel, hpayload⟩ hflow.1 hparameter
              · exact hrest
              · exact hflow.2

theorem restoreValues_preserves_secretCT_values {p : SemanticProgram}
    {left right : State} {leftSaved rightSaved : List (UInt32 × Value)}
    (hvalues : SecretCTValuesEquivalent p left.values right.values)
    (hsaved : SavedSecretCTEquivalent p leftSaved rightSaved) :
    SecretCTValuesEquivalent p
      (restoreValues left leftSaved).values (restoreValues right rightSaved).values := by
  induction leftSaved generalizing rightSaved left right with
  | nil => cases rightSaved <;> simp_all [SavedSecretCTEquivalent, restoreValues]
  | cons leftHead leftRest ih =>
      cases rightSaved with
      | nil => simp [SavedSecretCTEquivalent] at hsaved
      | cons rightHead rightRest =>
          rcases leftHead with ⟨leftCell, leftValue⟩
          rcases rightHead with ⟨rightCell, rightValue⟩
          rcases hsaved with ⟨rfl, hpayload, hrest⟩
          simp only [restoreValues]
          apply ih
          · apply hvalues.setIfInBounds
            exact hpayload
          · exact hrest

theorem ValueListSecretCTEquivalent.argumentLabelsFlow_eq {p : SemanticProgram}
    {left right : List Value} (h : ValueListSecretCTEquivalent left right)
    (parameters : List UInt32) :
    argumentLabelsFlow p left parameters = argumentLabelsFlow p right parameters := by
  induction left generalizing right parameters with
  | nil => cases right <;> cases parameters <;> simp_all [ValueListSecretCTEquivalent,
      argumentLabelsFlow]
  | cons leftHead leftRest ih =>
      cases right with
      | nil => cases parameters <;> simp_all [ValueListSecretCTEquivalent, argumentLabelsFlow]
      | cons rightHead rightRest =>
          rcases h with ⟨hlabel, _, hrest⟩
          cases parameters with
          | nil => rfl
          | cons parameter parameters =>
              simp [argumentLabelsFlow, ← hlabel, ih hrest parameters]

theorem callLabelsOK_eq_of_secretCT_equivalent {p : SemanticProgram}
    {left right : List Value} (h : ValueListSecretCTEquivalent left right)
    (instruction : Instruction) (callee : Function) :
    callLabelsOK p instruction callee left = callLabelsOK p instruction callee right := by
  simp only [callLabelsOK, h.argumentLabelsFlow_eq callee.parameterCells.toList]

theorem readExternal_eq_of_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (site : UInt32) :
    readExternal left site = readExternal right site := by
  rcases hlow with ⟨_, _, _, _, _, _, _, hinputs, hcursors, _⟩
  simp [readExternal, hinputs, hcursors]

theorem readActorValue_payload_eq_of_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (offset : UInt32)
    (hnonct : stateLabelAt p offset ≠ .secretCT) :
    (readActorValue p left offset).payload = (readActorValue p right offset).payload := by
  have hactor := hlow.2.2.2.2.2.1
  unfold readActorValue
  by_cases hleft : offset.toNat < left.actorState.size
  · have hright : offset.toNat < right.actorState.size := by
      simpa [← hactor.1] using hleft
    simpa [hleft, hright] using hactor.2 offset.toNat hleft hright (by simpa using hnonct)
  · have hright : ¬offset.toNat < right.actorState.size := by
      intro hright
      apply hleft
      simpa [hactor.1] using hright
    have hleftNone := Array.getElem?_eq_none (Nat.le_of_not_gt hleft)
    have hrightNone := Array.getElem?_eq_none (Nat.le_of_not_gt hright)
    simp [hleftNone, hrightNone]

theorem instructionCallee_eq_of_secretCT_safe {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (instruction : Instruction)
    (hsafe : SecretCTInstructionSafe p instruction) :
    instructionCallee? p left instruction = instructionCallee? p right instruction := by
  rcases hsafe with ⟨_, _, _, hcontrol⟩
  generalize hop : instruction.op = op at *
  cases op <;> simp_all [instructionCallee?]
  case closure =>
    cases hcells : valueOperandCells p instruction with
    | nil => simp [operandValues, hcells]
    | cons cell rest =>
        have hnonct : labelAt p.valueLabels cell ≠ .secretCT := by
          simpa [hcells] using hcontrol
        have heq := readProgramValue_eq_of_secretCT_low hlow cell hnonct
        simp [operandValues, hcells, heq]

theorem SecretCTAggregateEquivalent.setIfInBounds {p : SemanticProgram}
    {left right : Array (List Int)} (h : SecretCTAggregateEquivalent p left right)
    (cell : UInt32) (leftValue rightValue : List Int)
    (hvalue : labelAt p.valueLabels cell ≠ .secretCT → leftValue = rightValue) :
    SecretCTAggregateEquivalent p
      (left.setIfInBounds cell.toNat leftValue) (right.setIfInBounds cell.toNat rightValue) := by
  refine ⟨by simp [h.1], ?_⟩
  intro observed hl hr hlabel
  have hl' : observed < left.size := by simpa using hl
  have hr' : observed < right.size := by simpa [h.1] using hr
  rw [Array.getElem_setIfInBounds hl', Array.getElem_setIfInBounds hr']
  by_cases heq : cell.toNat = observed
  · subst observed
    simp only [if_pos]
    exact hvalue (by simpa using hlabel)
  · simp only [heq, ↓reduceIte]
    exact h.2 observed hl' hr' hlabel

theorem SecretCTActorEquivalent.setIfInBounds {p : SemanticProgram}
    {left right : Array Value} (h : SecretCTActorEquivalent p left right)
    (offset : UInt32) (leftValue rightValue : Value)
    (hvalue : stateLabelAt p offset ≠ .secretCT →
      leftValue.payload = rightValue.payload) :
    SecretCTActorEquivalent p
      (left.setIfInBounds offset.toNat leftValue) (right.setIfInBounds offset.toNat rightValue) := by
  refine ⟨by simp [h.1], ?_⟩
  intro observed hl hr hlabel
  have hl' : observed < left.size := by simpa using hl
  have hr' : observed < right.size := by simpa [h.1] using hr
  rw [Array.getElem_setIfInBounds hl', Array.getElem_setIfInBounds hr']
  by_cases heq : offset.toNat = observed
  · subst observed
    simp only [if_pos]
    exact hvalue (by simpa using hlabel)
  · simp only [heq, ↓reduceIte]
    exact h.2 observed hl' hr' hlabel

theorem SecretCTActorEquivalent.setIfInBoundsNat {p : SemanticProgram}
    {left right : Array Value} (h : SecretCTActorEquivalent p left right)
    (offset : Nat) (leftValue rightValue : Value)
    (hvalue : stateLabelAt p (UInt32.ofNat offset) ≠ .secretCT →
      leftValue.payload = rightValue.payload) :
    SecretCTActorEquivalent p
      (left.setIfInBounds offset leftValue) (right.setIfInBounds offset rightValue) := by
  refine ⟨by simp [h.1], ?_⟩
  intro observed hl hr hlabel
  have hl' : observed < left.size := by simpa using hl
  have hr' : observed < right.size := by simpa [h.1] using hr
  rw [Array.getElem_setIfInBounds hl', Array.getElem_setIfInBounds hr']
  by_cases heq : offset = observed
  · subst observed
    simp only [if_pos]
    exact hvalue hlabel
  · simp only [heq, ↓reduceIte]
    exact h.2 observed hl' hr' hlabel

theorem operandValues_eq_of_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (instruction : Instruction)
    (hsafe : cellsAvoidSecretCT p (valueOperandCells p instruction)) :
    operandValues p left instruction = operandValues p right instruction := by
  unfold operandValues
  apply List.map_congr_left
  intro cell hcell
  exact readProgramValue_eq_of_secretCT_low hlow cell (hsafe cell hcell)

theorem policyOperandValues_eq_of_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (instruction : Instruction) (classCode : UInt32)
    (hsafe : cellsAvoidSecretCT p (policyCells p instruction classCode)) :
    policyOperandValues p left instruction classCode =
      policyOperandValues p right instruction classCode := by
  unfold policyOperandValues
  apply List.map_congr_left
  intro cell hcell
  exact readProgramValue_eq_of_secretCT_low hlow cell
    (hsafe cell (by simpa [policyCells] using hcell))

theorem operandValue_eq_of_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (instruction : Instruction)
    (hnonct : (operandValue p left instruction).label ≠ .secretCT) :
    operandValue p left instruction = operandValue p right instruction := by
  cases hcells : valueOperandCells p instruction with
  | nil => simp [operandValue, operandValues, hcells]
  | cons cell rest =>
      have hlabel : labelAt p.valueLabels cell ≠ .secretCT := by
        simpa [operandValue, operandValues, hcells] using hnonct
      simp [operandValue, operandValues, hcells,
        readProgramValue_eq_of_secretCT_low hlow cell hlabel]

theorem operandValue_label_state_independent (p : SemanticProgram) (left right : State)
    (instruction : Instruction) :
    (operandValue p left instruction).label = (operandValue p right instruction).label := by
  cases hcells : valueOperandCells p instruction <;>
    simp [operandValue, operandValues, hcells]

theorem public_instruction_events_eq_of_secretCT_safe {p : SemanticProgram}
    {left right : State} (hlow : SecretCTLowEquivalent p left right)
    (instruction : Instruction) (hsafe : SecretCTInstructionSafe p instruction) :
    publicEvents (instructionEvents p left instruction) =
      publicEvents (instructionEvents p right instruction) := by
  rcases hsafe with ⟨hobserved, _, _, _⟩
  generalize hop : instruction.op = op
  cases op <;> simp only [instructionEvents, hop]
  case branch =>
    have heq := policyOperandValues_eq_of_secretCT_low hlow instruction 0
      (hobserved 0 (by simp))
    simp [heq]
  case loop =>
    have heq := policyOperandValues_eq_of_secretCT_low hlow instruction 1
      (hobserved 1 (by simp))
    simp [heq]
  case range =>
    have heq := policyOperandValues_eq_of_secretCT_low hlow instruction 2
      (hobserved 2 (by simp))
    simp [heq]
  case dispatch =>
    have heq := policyOperandValues_eq_of_secretCT_low hlow instruction 3
      (hobserved 3 (by simp))
    simp [heq]
  case actorBoundary =>
    have heq := policyOperandValues_eq_of_secretCT_low hlow instruction 8
      (hobserved 8 (by simp))
    simp [heq]
  case ffi => simp
  case allocation =>
    have heq := policyOperandValues_eq_of_secretCT_low hlow instruction 9
      (hobserved 9 (by simp))
    simp [heq]
  case address =>
    have heq := policyOperandValues_eq_of_secretCT_low hlow instruction 5
      (hobserved 5 (by simp))
    simp [heq]
  case index =>
    have haddress := policyOperandValues_eq_of_secretCT_low hlow instruction 5
      (hobserved 5 (by simp))
    have hindex := policyOperandValues_eq_of_secretCT_low hlow instruction 4
      (hobserved 4 (by simp))
    simp [haddress, hindex]
  case stringCompare =>
    have heq := policyOperandValues_eq_of_secretCT_low hlow instruction 13
      (hobserved 13 (by simp))
    simp [heq]
  case divRem =>
    have heq := policyOperandValues_eq_of_secretCT_low hlow instruction 6
      (hobserved 6 (by simp))
    simp [heq]
  case stateWrite => rw [publicEvents_flow_values, publicEvents_flow_values]
  case effect => rw [publicEvents_effect_values, publicEvents_effect_values]
  case abortiveEffect => rw [publicEvents_effect_values, publicEvents_effect_values]
  case capMint => rw [publicEvents_authority_values, publicEvents_authority_values]
  case capRestrict => rw [publicEvents_authority_values, publicEvents_authority_values]
  case capSplit => rw [publicEvents_authority_values, publicEvents_authority_values]
  case capDraw => rw [publicEvents_authority_values, publicEvents_authority_values]
  case capExercise => rw [publicEvents_authority_values, publicEvents_authority_values]
  case release => simp [publicEvents, EventKind.eqb]
  case releaseCT => simp [publicEvents, EventKind.eqb]
  case output =>
    have hlabelEq : (operandValue p left instruction).label =
        (operandValue p right instruction).label :=
      operandValue_label_state_independent p left right instruction
    by_cases hct : (operandValue p left instruction).label = .secretCT
    · have hctRight : (operandValue p right instruction).label = .secretCT := by
        rw [← hlabelEq]
        exact hct
      have hct' : ((operandValues p left instruction).head?.getD defaultValue).label =
          .secretCT := by simpa only [operandValue] using hct
      have hctRight' : ((operandValues p right instruction).head?.getD defaultValue).label =
          .secretCT := by simpa only [operandValue] using hctRight
      cases instruction.blockLabel <;> cases instruction.outputPayloadOccurrence <;>
        simp [publicEvents, EventKind.eqb, Label.eqb, Label.lub, Label.rank, hct', hctRight']
    · have heq := operandValue_eq_of_secretCT_low hlow instruction hct
      have heq' : (operandValues p left instruction).head?.getD defaultValue =
          (operandValues p right instruction).head?.getD defaultValue := by
        simpa only [operandValue] using heq
      rw [heq']

theorem instructionPayload_eq_of_secretCT_safe {p : SemanticProgram}
    {left right : State} (hlow : SecretCTLowEquivalent p left right)
    (instruction : Instruction) (hsafe : resultDependenciesAvoidSecretCT p instruction)
    (hdestination : instruction.destination ≠ 0)
    (hresult : instruction.resultLabel ≠ .secretCT)
    (hop : instruction.op ≠ .ffi ∧ instruction.op ≠ .actorBoundary ∧
      instruction.op ≠ .call ∧ instruction.op ≠ .closure ∧
      instruction.op ≠ .stateRead ∧ instruction.op ≠ .release ∧
      instruction.op ≠ .releaseCT) :
    instructionPayload p left instruction = instructionPayload p right instruction := by
  rcases hop with ⟨hffi, hboundary, hcall, hclosure, hstate, hrelease, hreleaseCT⟩
  generalize hop : instruction.op = op at *
  cases op <;> simp_all [resultDependenciesAvoidSecretCT]
  case allocation =>
    have heq := policyOperandValues_eq_of_secretCT_low hlow instruction 9 hsafe
    simp [instructionPayload, hop, heq]
  all_goals
    have heq := operandValues_eq_of_secretCT_low hlow instruction hsafe
    simp [instructionPayload, hop, heq]

theorem nextPc_eq_of_secretCT_safe {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (instruction : Instruction)
    (hsafe : SecretCTInstructionSafe p instruction) :
    nextPc p left instruction (operandValue p left instruction) =
      nextPc p right instruction (operandValue p right instruction) := by
  have hpc := hlow.1
  rcases hsafe with ⟨_, _, _, hcontrol⟩
  generalize hop : instruction.op = op at *
  cases op <;> simp_all [nextPc]
  case branch =>
    have hnonct : (operandValue p left instruction).label ≠ .secretCT := by
      cases hcells : valueOperandCells p instruction with
      | nil => simp [hcells] at hcontrol
      | cons cell rest => simpa [operandValue, operandValues, hcells] using hcontrol
    rw [operandValue_eq_of_secretCT_low hlow instruction hnonct]
  case loop =>
    have hnonct : (operandValue p left instruction).label ≠ .secretCT := by
      cases hcells : valueOperandCells p instruction with
      | nil => simp [hcells] at hcontrol
      | cons cell rest => simpa [operandValue, operandValues, hcells] using hcontrol
    rw [operandValue_eq_of_secretCT_low hlow instruction hnonct]
  case range =>
    have hnonct : (operandValue p left instruction).label ≠ .secretCT := by
      cases hcells : valueOperandCells p instruction with
      | nil => simp [hcells] at hcontrol
      | cons cell rest => simpa [operandValue, operandValues, hcells] using hcontrol
    rw [operandValue_eq_of_secretCT_low hlow instruction hnonct]
  case dispatch =>
    by_cases harity : instruction.operandCount = 2
    · simp [nextPc, hop, harity]
    · have hcontrol' := hcontrol harity
      have hnonct : (operandValue p left instruction).label ≠ .secretCT := by
        cases hcells : valueOperandCells p instruction with
        | nil => simp [hcells] at hcontrol'
        | cons cell rest => simpa [operandValue, operandValues, hcells] using hcontrol'
      rw [operandValue_eq_of_secretCT_low hlow instruction hnonct]

theorem ordinaryStep_secretCT_equivalent {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (instruction : Instruction)
    (hinstruction : instructionWellFormed p instruction)
    (hpayload : instruction.destination ≠ 0 → instruction.resultLabel ≠ .secretCT →
      instructionPayload p left instruction = instructionPayload p right instruction)
    (haggregate : instruction.op = .aggregate → instruction.destination ≠ 0 →
      labelAt p.valueLabels instruction.destination ≠ .secretCT →
      operandPayloads p left instruction = operandPayloads p right instruction)
    (hnext : nextPc p left instruction (operandValue p left instruction) =
      nextPc p right instruction (operandValue p right instruction))
    (htraps : ((if instruction.op == .trap then
        (operandValues p left instruction).isEmpty ||
          (operandValue p left instruction).payload != 0 else false) =
      (if instruction.op == .trap then
        (operandValues p right instruction).isEmpty ||
          (operandValue p right instruction).payload != 0 else false))) :
    SecretCTLowEquivalent p (ordinaryStep p left instruction).state
      (ordinaryStep p right instruction).state := by
  rcases hlow with ⟨hpc, hhalted, htrapped, hstack, haggregates, hactor, hbalances,
    hinputs, hcursors, hleftSize, hrightSize, hvalues⟩
  have hvalueRelation := writeDestination_preserves_secretCT_values
    (p := p) (left := left) (right := right)
    ⟨hleftSize, hrightSize, hvalues⟩ instruction
    (instructionPayload p left instruction) (instructionPayload p right instruction)
    hpayload hinstruction.2.2.1
  have haggregateRelation : SecretCTAggregateEquivalent p
      (if instruction.op == .aggregate && instruction.destination != 0 then
        left.aggregates.setIfInBounds instruction.destination.toNat
          (operandPayloads p left instruction)
      else left.aggregates)
      (if instruction.op == .aggregate && instruction.destination != 0 then
        right.aggregates.setIfInBounds instruction.destination.toNat
          (operandPayloads p right instruction)
      else right.aggregates) := by
    by_cases hcondition : instruction.op == .aggregate && instruction.destination != 0
    · have hcondition' : (instruction.op == .aggregate) = true ∧
          (instruction.destination != 0) = true := by
        simpa only [Bool.and_eq_true] using hcondition
      have hkind : instruction.op = .aggregate := by
        simpa only [semanticInstrOp_beq_true_iff] using hcondition'.1
      have hdestination : instruction.destination ≠ 0 := by
        simpa using hcondition'.2
      simp only [hcondition, if_pos]
      apply haggregates.setIfInBounds
      exact haggregate hkind hdestination
    · simp only [hcondition, if_neg]
      exact haggregates
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ordinaryStep] using hnext
  · simp [ordinaryStep]
  · simpa [ordinaryStep] using htraps
  · simpa [ordinaryStep] using hstack
  · simpa [ordinaryStep] using haggregateRelation
  · simpa [ordinaryStep] using hactor
  · simpa [ordinaryStep] using hbalances
  · simpa [ordinaryStep] using hinputs
  · simpa [ordinaryStep] using hcursors
  · simpa [ordinaryStep] using hvalueRelation.1
  · simpa [ordinaryStep] using hvalueRelation.2.1
  · simpa [ordinaryStep] using hvalueRelation.2.2

theorem ordinaryStep_secretCT_equivalent_of_safe {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (instruction : Instruction)
    (hinstruction : instructionWellFormed p instruction)
    (hsafe : SecretCTInstructionSafe p instruction)
    (hrelease : releaseEvents (instructionEvents p left instruction) =
      releaseEvents (instructionEvents p right instruction))
    (hordinary : instruction.op ≠ .call ∧ instruction.op ≠ .closure ∧
      instruction.op ≠ .ffi ∧ instruction.op ≠ .actorBoundary ∧
      instruction.op ≠ .effect ∧ instruction.op ≠ .abortiveEffect ∧
      instruction.op ≠ .stateRead ∧ instruction.op ≠ .stateWrite ∧
      instruction.op ≠ .output) :
    SecretCTLowEquivalent p (ordinaryStep p left instruction).state
      (ordinaryStep p right instruction).state := by
  have hpayload : instruction.destination ≠ 0 → instruction.resultLabel ≠ .secretCT →
      instructionPayload p left instruction = instructionPayload p right instruction := by
    intro hdestination hresult
    by_cases hreleaseOp : instruction.op = .release
    · have h := hrelease
      simp [instructionEvents, hreleaseOp, releaseEvents, EventKind.eqb] at h
      simpa [instructionPayload, hreleaseOp] using h
    · by_cases hreleaseCTOp : instruction.op = .releaseCT
      · have h := hrelease
        simp [instructionEvents, hreleaseCTOp, releaseEvents, EventKind.eqb] at h
        simpa [instructionPayload, hreleaseCTOp] using h
      · exact instructionPayload_eq_of_secretCT_safe hlow instruction hsafe.2.1
          hdestination hresult
          ⟨hordinary.2.2.1, hordinary.2.2.2.1, hordinary.1, hordinary.2.1,
            hordinary.2.2.2.2.2.2.1, hreleaseOp, hreleaseCTOp⟩
  have haggregate : instruction.op = .aggregate → instruction.destination ≠ 0 →
      labelAt p.valueLabels instruction.destination ≠ .secretCT →
      operandPayloads p left instruction = operandPayloads p right instruction := by
    intro hkind hdestination hlabel
    have hdependencies := hsafe.2.1
    simp [resultDependenciesAvoidSecretCT, hkind, hdestination,
      hinstruction.2.2.1, hlabel] at hdependencies
    exact congrArg (List.map Value.payload)
      (operandValues_eq_of_secretCT_low hlow instruction hdependencies)
  have hnext := nextPc_eq_of_secretCT_safe hlow instruction hsafe
  have htraps : ((if instruction.op == .trap then
        (operandValues p left instruction).isEmpty ||
          (operandValue p left instruction).payload != 0 else false) =
      (if instruction.op == .trap then
        (operandValues p right instruction).isEmpty ||
          (operandValue p right instruction).payload != 0 else false)) := by
    by_cases htrap : instruction.op = .trap
    · by_cases hcount : instruction.operandCount = 0
      · simp [htrap, operandValues, valueOperandCells, instructionOperands, hcount]
      · have hcontrol := hsafe.2.2.2
        have hcontrol' := hcontrol (by simp [htrap, hcount])
        have hnonct : (operandValue p left instruction).label ≠ .secretCT := by
          cases hcells : valueOperandCells p instruction with
          | nil => simp [hcells] at hcontrol'
          | cons cell rest => simpa [operandValue, operandValues, hcells] using hcontrol'
        rw [operandValue_eq_of_secretCT_low hlow instruction hnonct]
        simp [htrap, operandValues]
    · simp [htrap]
  exact ordinaryStep_secretCT_equivalent hlow instruction hinstruction hpayload haggregate
    hnext htraps

theorem writeDestination_preserves_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (instruction : Instruction)
    (leftPayload rightPayload : Int)
    (hpayload : instruction.destination ≠ 0 → instruction.resultLabel ≠ .secretCT →
      leftPayload = rightPayload)
    (hresult : instruction.resultLabel = labelAt p.valueLabels instruction.destination) :
    SecretCTLowEquivalent p (writeDestination left instruction leftPayload)
      (writeDestination right instruction rightPayload) := by
  rcases hlow with ⟨hpc, hhalted, htrapped, hstack, haggregates, hactor, hbalances,
    hinputs, hcursors, hleftSize, hrightSize, hvalues⟩
  have hvalueRelation := writeDestination_preserves_secretCT_values
    (p := p) (left := left) (right := right) ⟨hleftSize, hrightSize, hvalues⟩
    instruction leftPayload rightPayload hpayload hresult
  exact ⟨by simpa using hpc, by simpa using hhalted, by simpa using htrapped,
    by simpa using hstack, by simpa using haggregates, by simpa using hactor,
    by simpa using hbalances, by simpa using hinputs, by simpa using hcursors,
    hvalueRelation.1, hvalueRelation.2.1, hvalueRelation.2.2⟩

theorem controlUpdate_preserves_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (leftPc rightPc : Nat)
    (leftHalted rightHalted leftTrapped rightTrapped : Bool)
    (hpc : leftPc = rightPc) (hhalted : leftHalted = rightHalted)
    (htrapped : leftTrapped = rightTrapped) :
    SecretCTLowEquivalent p
      { left with pc := leftPc, halted := leftHalted, trapped := leftTrapped }
      { right with pc := rightPc, halted := rightHalted, trapped := rightTrapped } := by
  rcases hlow with ⟨_, _, _, hstack, haggregates, hactor, hbalances, hinputs, hcursors,
    hleftSize, hrightSize, hvalues⟩
  exact ⟨hpc, hhalted, htrapped, hstack, haggregates, hactor, hbalances, hinputs, hcursors,
    hleftSize, hrightSize, hvalues⟩

@[simp] theorem advanceExternal_pc (state : State) (site : UInt32) :
    (advanceExternal state site).pc = state.pc := by
  simp [advanceExternal]

@[simp] theorem advanceExternal_capabilityBalances (state : State) (site : UInt32) :
    (advanceExternal state site).capabilityBalances = state.capabilityBalances := by
  simp [advanceExternal]

@[simp] theorem advanceExternal_halted (state : State) (site : UInt32) :
    (advanceExternal state site).halted = state.halted := by
  simp [advanceExternal]

@[simp] theorem advanceExternal_trapped (state : State) (site : UInt32) :
    (advanceExternal state site).trapped = state.trapped := by
  simp [advanceExternal]

theorem advanceExternal_preserves_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (site : UInt32) :
    SecretCTLowEquivalent p (advanceExternal left site) (advanceExternal right site) := by
  rcases hlow with ⟨hpc, hhalted, htrapped, hstack, haggregates, hactor, hbalances,
    hinputs, hcursors, hleftSize, hrightSize, hvalues⟩
  have hcursors' : (advanceExternal left site).externalCursors =
      (advanceExternal right site).externalCursors := by
    simp [advanceExternal, hinputs, hcursors]
  exact ⟨by simpa using hpc, by simpa using hhalted, by simpa using htrapped,
    by simpa using hstack, by simpa using haggregates, by simpa using hactor,
    by simpa using hbalances, by simpa using hinputs, hcursors', by simpa using hleftSize,
    by simpa using hrightSize, by simpa using hvalues⟩

theorem actorStateUpdate_preserves_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (leftActor rightActor : Array Value)
    (hactor : SecretCTActorEquivalent p leftActor rightActor) :
    SecretCTLowEquivalent p { left with actorState := leftActor }
      { right with actorState := rightActor } := by
  rcases hlow with ⟨hpc, hhalted, htrapped, hstack, haggregates, _, hbalances,
    hinputs, hcursors, hleftSize, hrightSize, hvalues⟩
  exact ⟨hpc, hhalted, htrapped, hstack, haggregates, hactor, hbalances, hinputs,
    hcursors, hleftSize, hrightSize, hvalues⟩

theorem enterCall_preserves_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (instruction : Instruction)
    (callee : Function) (leftArguments rightArguments : List Value)
    (harguments : ValueListSecretCTEquivalent leftArguments rightArguments)
    (hflow : argumentLabelsFlow p leftArguments callee.parameterCells.toList = true) :
    SecretCTLowEquivalent p
      { assignArguments p left callee.parameterCells.toList leftArguments with
        pc := callee.firstInstruction.toNat
        callStack :=
          { returnPc := left.pc + 1, destination := instruction.destination,
            calleeId := callee.id, returnLabel := callee.returnLabel,
            savedParameters := saveValues left callee.parameterCells.toList } :: left.callStack }
      { assignArguments p right callee.parameterCells.toList rightArguments with
        pc := callee.firstInstruction.toNat
        callStack :=
          { returnPc := right.pc + 1, destination := instruction.destination,
            calleeId := callee.id, returnLabel := callee.returnLabel,
            savedParameters := saveValues right callee.parameterCells.toList } :: right.callStack } := by
  rcases hlow with ⟨hpc, hhalted, htrapped, hstack, haggregates, hactor, hbalances,
    hinputs, hcursors, hleftSize, hrightSize, hvalues⟩
  have hassigned := assignArguments_preserves_secretCT_values
    (p := p) (left := left) (right := right) ⟨hleftSize, hrightSize, hvalues⟩
    harguments hflow
  have hsaved := saveValues_secretCT_equivalent
    (p := p) (left := left) (right := right)
    ⟨hpc, hhalted, htrapped, hstack, haggregates, hactor, hbalances, hinputs, hcursors,
      hleftSize, hrightSize, hvalues⟩ callee.parameterCells.toList
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hhalted
  · simpa using htrapped
  · exact ⟨⟨congrArg (fun pc => pc + 1) hpc, rfl, rfl, rfl, hsaved⟩, hstack⟩
  · simpa using haggregates
  · simpa using hactor
  · simpa using hbalances
  · simpa using hinputs
  · simpa using hcursors
  · simpa using hassigned.1
  · simpa using hassigned.2.1
  · simpa using hassigned.2.2

theorem restoreValues_preserves_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right)
    (leftSaved rightSaved : List (UInt32 × Value))
    (hsaved : SavedSecretCTEquivalent p leftSaved rightSaved) :
    SecretCTLowEquivalent p (restoreValues left leftSaved) (restoreValues right rightSaved) := by
  rcases hlow with ⟨hpc, hhalted, htrapped, hstack, haggregates, hactor, hbalances,
    hinputs, hcursors, hleftSize, hrightSize, hvalues⟩
  have hrestored := restoreValues_preserves_secretCT_values
    (p := p) (left := left) (right := right) ⟨hleftSize, hrightSize, hvalues⟩ hsaved
  exact ⟨by simpa using hpc, by simpa using hhalted, by simpa using htrapped,
    by simpa using hstack, by simpa using haggregates, by simpa using hactor,
    by simpa using hbalances, by simpa using hinputs, by simpa using hcursors,
    hrestored.1, hrestored.2.1, hrestored.2.2⟩

theorem callStackUpdate_preserves_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (leftPc rightPc : Nat)
    (leftStack rightStack : List CallFrame) (hpc : leftPc = rightPc)
    (hstack : CallStackSecretCTEquivalent p leftStack rightStack) :
    SecretCTLowEquivalent p { left with pc := leftPc, callStack := leftStack }
      { right with pc := rightPc, callStack := rightStack } := by
  rcases hlow with ⟨_, hhalted, htrapped, _, haggregates, hactor, hbalances, hinputs,
    hcursors, hleftSize, hrightSize, hvalues⟩
  exact ⟨hpc, hhalted, htrapped, hstack, haggregates, hactor, hbalances, hinputs,
    hcursors, hleftSize, hrightSize, hvalues⟩

theorem return_operand_payload_eq {operandLeft operandRight : Value}
    {returnLabel destinationLabel : Label}
    (hlabel : operandLeft.label = operandRight.label)
    (hoperandFlow : operandLeft.label.flowsTo returnLabel = true)
    (hreturnFlow : returnLabel.flowsTo destinationLabel = true)
    (hdestination : destinationLabel ≠ .secretCT)
    (hpayload : operandLeft.label ≠ .secretCT →
      operandLeft.payload = operandRight.payload) :
    operandLeft.payload = operandRight.payload := by
  apply hpayload
  intro hct
  rw [hct] at hoperandFlow
  cases returnLabel <;> cases destinationLabel <;>
    simp_all [Label.flowsTo, Label.rank]

theorem secondOperandValue_eq_of_secretCT_low {p : SemanticProgram} {left right : State}
    (hlow : SecretCTLowEquivalent p left right) (instruction : Instruction)
    (hsafe : match (valueOperandCells p instruction)[1]? with
      | some cell => labelAt p.valueLabels cell ≠ .secretCT
      | none => False) :
    (operandValues p left instruction)[1]?.getD defaultValue =
      (operandValues p right instruction)[1]?.getD defaultValue := by
  cases hcells : valueOperandCells p instruction with
  | nil => simp [hcells] at hsafe
  | cons first rest =>
      cases rest with
      | nil => simp [hcells] at hsafe
      | cons second tail =>
          have heq := readProgramValue_eq_of_secretCT_low hlow second (by
            simpa [hcells] using hsafe)
          simp [operandValues, hcells, heq]

/-- Constructor-level raw lockstep obligation.  Production corollaries derive it from verifier
    acceptance; callers never supply it to a production-facing theorem. -/
def RawSecretCTStepPolicy (p : SemanticProgram) : Prop :=
  ∀ left right, StateWellFormed p left → StateWellFormed p right →
    SecretCTLowEquivalent p left right →
    releaseEvents (step p left).events = releaseEvents (step p right).events →
      StateWellFormed p (step p left).state ∧ StateWellFormed p (step p right).state ∧
      SecretCTLowEquivalent p (step p left).state (step p right).state ∧
      publicEvents (step p left).events = publicEvents (step p right).events

set_option maxHeartbeats 1000000

/-- The raw deterministic machine is lockstep for SecretCT once every decoded constructor has the
    verifier-derived static obligation. Explicit releases are the only case where payload equality
    is supplied by the delimited-release premise. -/
theorem raw_secretCT_step_lockstep_of_static_safe {p : SemanticProgram}
    (hsafeProgram : SecretCTStaticSafe p) : RawSecretCTStepPolicy p := by
  intro left right hwleft hwright hlow hrelease
  have hwleft' := state_well_formed_preserved hsafeProgram.1 hwleft
  have hwright' := state_well_formed_preserved hsafeProgram.1 hwright
  refine ⟨hwleft', hwright', ?_⟩
  have hactive : (left.halted || left.trapped) = (right.halted || right.trapped) := by
    rw [hlow.2.1, hlow.2.2.1]
  by_cases hstopped : left.halted || left.trapped
  · have hstoppedRight : right.halted || right.trapped := by simpa [← hactive] using hstopped
    exact ⟨by simpa [step, hstopped, hstoppedRight] using hlow,
      by simp [step, hstopped, hstoppedRight]⟩
  · have hstoppedRight : ¬(right.halted || right.trapped) := by
      simpa [← hactive] using hstopped
    cases hlookup : p.instructions[left.pc]? with
    | none =>
        have hlookupRight : p.instructions[right.pc]? = none := by simpa [hlow.1] using hlookup
        exact ⟨by
          rcases hlow with ⟨hpc, _, htrap, hstack, haggregates, hactor, hbalances,
            hinputs, hcursors, hleftSize, hrightSize, hvalues⟩
          simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight,
            SecretCTLowEquivalent] using
              And.intro hpc (And.intro htrap (And.intro hstack (And.intro haggregates
                (And.intro hactor (And.intro hbalances (And.intro hinputs
                  (And.intro hcursors (And.intro hleftSize (And.intro hrightSize hvalues))))))))),
          by simp [step, hstopped, hstoppedRight, hlookup, hlookupRight]⟩
    | some instruction =>
        have hlookupRight : p.instructions[right.pc]? = some instruction := by
          simpa [hlow.1] using hlookup
        have hinstruction : instruction ∈ p.instructions.toList := by
          simpa using Array.mem_of_getElem? hlookup
        have hsafe := hsafeProgram.2 instruction hinstruction
        have hinstructionWF := hsafeProgram.1.2.2 instruction hinstruction
        have hevents := public_instruction_events_eq_of_secretCT_safe hlow instruction hsafe
        generalize hop : instruction.op = op at *
        cases op
        case scalar | aggregate | project | branch | jump | loop | slotNew | slotPut | slotTake |
            allocation | address | capMint | capRestrict | capSplit | capDraw | capExercise |
            release | releaseCT | ctEq | ctSelect | ctLt | trap | halt | range | dispatch | index |
            divRem | stringCompare =>
          have hreleaseInstruction : releaseEvents (instructionEvents p left instruction) =
              releaseEvents (instructionEvents p right instruction) := by
            simpa [step, ordinaryStep, hstopped, hstoppedRight, hlookup, hlookupRight, hop]
              using hrelease
          refine ⟨?_, ?_⟩
          · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop] using
              ordinaryStep_secretCT_equivalent_of_safe hlow instruction hinstructionWF hsafe
                hreleaseInstruction (by simp_all)
          · simpa [step, ordinaryStep, hstopped, hstoppedRight, hlookup, hlookupRight, hop]
              using hevents
        case effect | abortiveEffect =>
          have hrel := controlUpdate_preserves_secretCT_low hlow
            (left.pc + 1) (right.pc + 1) left.halted right.halted
            (instruction.op == .abortiveEffect) (instruction.op == .abortiveEffect)
            (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 rfl
          refine ⟨?_, ?_⟩
          · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop] using hrel
          · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop] using hevents
        case ffi =>
          have hread := readExternal_eq_of_secretCT_low hlow instruction.id
          have hadvance := advanceExternal_preserves_secretCT_low hlow instruction.id
          have hwrite := writeDestination_preserves_secretCT_low hadvance instruction
            (readExternal left instruction.id) (readExternal right instruction.id)
            (fun _ _ => hread) hinstructionWF.2.2.1
          have hrel := controlUpdate_preserves_secretCT_low hwrite
            (left.pc + 1) (right.pc + 1) left.halted right.halted left.trapped right.trapped
            (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 hlow.2.2.1
          refine ⟨?_, ?_⟩
          · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop] using hrel
          · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop] using hevents
        case actorBoundary =>
          by_cases hdestination : instruction.destination = 0
          · have hrel := controlUpdate_preserves_secretCT_low hlow
              (left.pc + 1) (right.pc + 1) left.halted right.halted left.trapped right.trapped
              (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 hlow.2.2.1
            refine ⟨?_, ?_⟩
            · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
                hdestination, writeDestination] using hrel
            · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop] using hevents
          · have hread := readExternal_eq_of_secretCT_low hlow instruction.id
            have hadvance := advanceExternal_preserves_secretCT_low hlow instruction.id
            have hwrite := writeDestination_preserves_secretCT_low hadvance instruction
              (readExternal left instruction.id) (readExternal right instruction.id)
              (fun _ _ => hread) hinstructionWF.2.2.1
            have hrel := controlUpdate_preserves_secretCT_low hwrite
              (left.pc + 1) (right.pc + 1) left.halted right.halted left.trapped right.trapped
              (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 hlow.2.2.1
            refine ⟨?_, ?_⟩
            · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
                hdestination] using hrel
            · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop] using hevents
        case stateRead =>
          let offset := (immediateOperands p instruction).head?.getD 0
          let leftPayload := if offset < 0 then 0 else
            (readActorValue p left (UInt32.ofNat offset.toNat)).payload
          let rightPayload := if offset < 0 then 0 else
            (readActorValue p right (UInt32.ofNat offset.toNat)).payload
          have hpayload : instruction.destination ≠ 0 →
              instruction.resultLabel ≠ .secretCT → leftPayload = rightPayload := by
            intro hdestination hresult
            have hdependencies := hsafe.2.1
            simp [resultDependenciesAvoidSecretCT, hop, hdestination, hresult] at hdependencies
            by_cases hnegative : offset < 0
            · simp [leftPayload, rightPayload, hnegative]
            · have hsource : stateLabelAt p (UInt32.ofNat offset.toNat) ≠ .secretCT :=
                hdependencies.resolve_left hnegative
              simpa [leftPayload, rightPayload, hnegative] using
                readActorValue_payload_eq_of_secretCT_low hlow
                  (UInt32.ofNat offset.toNat) hsource
          have hwrite := writeDestination_preserves_secretCT_low hlow instruction
            leftPayload rightPayload hpayload hinstructionWF.2.2.1
          have hrel := controlUpdate_preserves_secretCT_low hwrite
            (left.pc + 1) (right.pc + 1) left.halted right.halted left.trapped right.trapped
            (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 hlow.2.2.1
          refine ⟨?_, ?_⟩
          · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
              offset, leftPayload, rightPayload] using hrel
          · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop] using hevents
        case stateWrite =>
          let offset := (immediateOperands p instruction).head?.getD 0
          let leftValue := (operandValues p left instruction)[1]?.getD defaultValue
          let rightValue := (operandValues p right instruction)[1]?.getD defaultValue
          by_cases hnegative : offset < 0
          · have hrel := controlUpdate_preserves_secretCT_low hlow
              (left.pc + 1) (right.pc + 1) left.halted right.halted left.trapped right.trapped
              (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 hlow.2.2.1
            refine ⟨?_, ?_⟩
            · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
                offset, hnegative, leftValue, rightValue] using hrel
            · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop] using hevents
          · have hactor := hlow.2.2.2.2.2.1
            have hnewActor : SecretCTActorEquivalent p
                (left.actorState.setIfInBounds offset.toNat
                  ⟨stateLabelAt p (UInt32.ofNat offset.toNat), leftValue.payload⟩)
                (right.actorState.setIfInBounds offset.toNat
                  ⟨stateLabelAt p (UInt32.ofNat offset.toNat), rightValue.payload⟩) := by
              have hset := hactor.setIfInBoundsNat offset.toNat
                ⟨stateLabelAt p (UInt32.ofNat offset.toNat), leftValue.payload⟩
                ⟨stateLabelAt p (UInt32.ofNat offset.toNat), rightValue.payload⟩ (by
                  intro hsink
                  have hstateSafe := hsafe.2.2.1
                  simp [stateWriteAvoidsSecretCT, hop, offset, hnegative, hsink] at hstateSafe
                  have heq := secondOperandValue_eq_of_secretCT_low hlow instruction hstateSafe
                  have hpayload : leftValue.payload = rightValue.payload := by
                    simpa [leftValue, rightValue] using congrArg Value.payload heq
                  exact hpayload)
              exact hset
            have hactorRel := actorStateUpdate_preserves_secretCT_low hlow _ _ hnewActor
            have hrel := controlUpdate_preserves_secretCT_low hactorRel
              (left.pc + 1) (right.pc + 1) left.halted right.halted left.trapped right.trapped
              (congrArg (fun pc => pc + 1) hlow.1) hlow.2.1 hlow.2.2.1
            refine ⟨?_, ?_⟩
            · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
                offset, hnegative, leftValue, rightValue] using hrel
            · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop] using hevents
        case call | closure =>
          let leftArguments := callArguments p left instruction
          let rightArguments := callArguments p right instruction
          have harguments : ValueListSecretCTEquivalent leftArguments rightArguments := by
            by_cases hclosure : instruction.op = .closure
            · simpa [leftArguments, rightArguments, callArguments, hclosure] using
                (operandValues_secretCT_equivalent hlow instruction).drop 1
            · simpa [leftArguments, rightArguments, callArguments, hclosure] using
                operandValues_secretCT_equivalent hlow instruction
          have hcalleeEq := instructionCallee_eq_of_secretCT_safe hlow instruction hsafe
          cases hcallee : instructionCallee? p left instruction with
          | none =>
              have hcalleeRight : instructionCallee? p right instruction = none := by
                simpa [hcallee] using hcalleeEq.symm
              have hrel := controlUpdate_preserves_secretCT_low hlow
                left.pc right.pc left.halted right.halted true true
                hlow.1 hlow.2.1 rfl
              exact ⟨by simpa [step, callStep, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
                  hcallee, hcalleeRight] using hrel,
                by simp [step, callStep, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
                  hcallee, hcalleeRight, publicEvents, EventKind.eqb]⟩
          | some callee =>
              have hcalleeRight : instructionCallee? p right instruction = some callee := by
                simpa [hcallee] using hcalleeEq.symm
              have hlength := harguments.length_eq
              have hlabels := harguments.argumentLabelsFlow_eq
                (p := p) callee.parameterCells.toList
              have hguardEq :
                  (leftArguments.length != callee.parameterCells.size ||
                    !callLabelsOK p instruction callee leftArguments) =
                  (rightArguments.length != callee.parameterCells.size ||
                    !callLabelsOK p instruction callee rightArguments) := by
                rw [hlength, callLabelsOK_eq_of_secretCT_equivalent harguments]
              by_cases hguard : leftArguments.length != callee.parameterCells.size ||
                  !callLabelsOK p instruction callee leftArguments
              · have hguardRight : rightArguments.length != callee.parameterCells.size ||
                    !callLabelsOK p instruction callee rightArguments := by
                  simpa [← hguardEq] using hguard
                have hrel := controlUpdate_preserves_secretCT_low hlow
                  left.pc right.pc left.halted right.halted true true hlow.1 hlow.2.1 rfl
                exact ⟨by simpa [step, callStep, hstopped, hstoppedRight, hlookup, hlookupRight,
                    hop, hcallee, hcalleeRight, leftArguments, rightArguments, hguard, hguardRight]
                    using hrel,
                  by simp [step, callStep, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
                    hcallee, hcalleeRight, leftArguments, rightArguments, hguard, hguardRight,
                    publicEvents, EventKind.eqb]⟩
              · have hguardRight : ¬(rightArguments.length != callee.parameterCells.size ||
                    !callLabelsOK p instruction callee rightArguments) := by
                  simpa [← hguardEq] using hguard
                have hcall : callLabelsOK p instruction callee leftArguments = true := by
                  cases hcall : callLabelsOK p instruction callee leftArguments with
                  | false => simp [hcall] at hguard
                  | true => rfl
                have hflow : argumentLabelsFlow p leftArguments
                    callee.parameterCells.toList = true := by
                  have hparts : argumentLabelsFlow p leftArguments
                        callee.parameterCells.toList = true ∧
                      (instruction.destination == 0 ||
                        callee.returnLabel.flowsTo instruction.resultLabel) = true := by
                    simpa [callLabelsOK, Bool.and_eq_true] using hcall
                  exact hparts.1
                have hrel := enterCall_preserves_secretCT_low hlow instruction callee
                  leftArguments rightArguments harguments hflow
                refine ⟨?_, ?_⟩
                · simpa [step, callStep, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
                    hcallee, hcalleeRight, leftArguments, rightArguments, hguard, hguardRight]
                    using hrel
                · simp [step, callStep, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
                    hcallee, hcalleeRight, leftArguments, rightArguments, hguard, hguardRight]
        case output =>
          have hstack := hlow.2.2.2.1
          cases hleftStack : left.callStack with
          | nil =>
              cases hrightStack : right.callStack with
              | nil =>
                  have hrel := controlUpdate_preserves_secretCT_low hlow
                    left.pc right.pc true true left.trapped right.trapped
                    hlow.1 rfl hlow.2.2.1
                  exact ⟨by simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight,
                      hop, hleftStack, hrightStack] using hrel,
                    by simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight,
                      hop, hleftStack, hrightStack] using hevents⟩
              | cons rightFrame rightRest =>
                  simp [CallStackSecretCTEquivalent, hleftStack, hrightStack] at hstack
          | cons leftFrame leftRest =>
              cases hrightStack : right.callStack with
              | nil => simp [CallStackSecretCTEquivalent, hleftStack, hrightStack] at hstack
              | cons rightFrame rightRest =>
                  have hstack' : CallFrameSecretCTEquivalent p leftFrame rightFrame ∧
                      CallStackSecretCTEquivalent p leftRest rightRest := by
                    simpa [CallStackSecretCTEquivalent, hleftStack, hrightStack] using hstack
                  rcases hstack' with ⟨hframe, hrest⟩
                  rcases hframe with ⟨hreturnPc, hdestination, hcalleeId, hreturnLabel, hsaved⟩
                  have hoperandLabel := operandValue_label_state_independent p left right instruction
                  have hguardEq :
                      (!(operandValue p left instruction).label.flowsTo leftFrame.returnLabel) =
                      (!(operandValue p right instruction).label.flowsTo rightFrame.returnLabel) := by
                    rw [hoperandLabel, hreturnLabel]
                  by_cases hguard : !(operandValue p left instruction).label.flowsTo
                      leftFrame.returnLabel
                  · have hguardRight : !(operandValue p right instruction).label.flowsTo
                        rightFrame.returnLabel := by simpa [← hguardEq] using hguard
                    have hrel := controlUpdate_preserves_secretCT_low hlow
                      left.pc right.pc left.halted right.halted true true
                      hlow.1 hlow.2.1 rfl
                    exact ⟨by simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight,
                        hop, hleftStack, hrightStack, hguard, hguardRight] using hrel,
                      by simp [step, hstopped, hstoppedRight, hlookup, hlookupRight,
                        hop, hleftStack, hrightStack, hguard, hguardRight,
                        publicEvents, EventKind.eqb]⟩
                  · have hguardRight : ¬(!(operandValue p right instruction).label.flowsTo
                        rightFrame.returnLabel) := by simpa [← hguardEq] using hguard
                    have hoperandFlow : (operandValue p left instruction).label.flowsTo
                        leftFrame.returnLabel = true := by
                      cases hflow : (operandValue p left instruction).label.flowsTo
                          leftFrame.returnLabel <;> simp_all
                    have hrestored := restoreValues_preserves_secretCT_low hlow
                      leftFrame.savedParameters rightFrame.savedParameters hsaved
                    let returnDestination := leftFrame.destination
                    let returnResultLabel := labelAt p.valueLabels returnDestination
                    let returnInstruction : Instruction :=
                      { { instruction with destination := returnDestination } with
                        resultLabel := returnResultLabel }
                    have hpayload : returnInstruction.destination ≠ 0 →
                        returnInstruction.resultLabel ≠ .secretCT →
                        (operandValue p left instruction).payload =
                          (operandValue p right instruction).payload := by
                      intro hdestinationNonzero hdestinationLabel
                      have hframeWF := hwleft.2.2.2.2 leftFrame (by simp [hleftStack])
                      have hreturnFlow : leftFrame.returnLabel.flowsTo
                          (labelAt p.valueLabels leftFrame.destination) = true := by
                        have hflow := hframeWF.2.2.2.1
                        simp only [Bool.or_eq_true] at hflow
                        have hdestinationNonzero' : leftFrame.destination ≠ 0 := by
                          simpa [returnInstruction, returnDestination] using hdestinationNonzero
                        have hdestinationFalse : (leftFrame.destination == 0) = false := by
                          simpa using hdestinationNonzero'
                        exact hflow.resolve_left (by simpa [hdestinationFalse])
                      apply return_operand_payload_eq hoperandLabel hoperandFlow hreturnFlow
                        hdestinationLabel
                      intro hnonct
                      exact congrArg Value.payload
                        (operandValue_eq_of_secretCT_low hlow instruction hnonct)
                    have hwritten := writeDestination_preserves_secretCT_low hrestored
                      returnInstruction (operandValue p left instruction).payload
                      (operandValue p right instruction).payload hpayload rfl
                    have hreturned := callStackUpdate_preserves_secretCT_low hwritten
                      leftFrame.returnPc rightFrame.returnPc leftRest rightRest hreturnPc hrest
                    refine ⟨?_, ?_⟩
                    · simpa [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
                        hleftStack, hrightStack, hguard, hguardRight, returnInstruction,
                        returnDestination, returnResultLabel, writeDestination, hdestination]
                        using hreturned
                    · simp [step, hstopped, hstoppedRight, hlookup, hlookupRight, hop,
                        hleftStack, hrightStack, hguard, hguardRight]
set_option maxHeartbeats 200000

/-- Public cut points are aligned control positions (or terminal states). The forthcoming Public
    proof stutters only *between* such points; it must not demand that arbitrary mid-arm states in
    two differently long Secret regions have the same pc. -/
def PublicCutPoint (p : SemanticProgram) (state : State) : Prop :=
  state.halted = true ∨ state.trapped = true ∨
    ∃ instruction, p.instructions[state.pc]? = some instruction ∧ instruction.blockLabel = .pub

def ReleaseAlignedRaw (p : SemanticProgram) : Nat → State → State → Prop
  | 0, _, _ => True
  | fuel + 1, left, right =>
      releaseEvents (step p left).events = releaseEvents (step p right).events ∧
        ReleaseAlignedRaw p fuel (step p left).state (step p right).state

private theorem raw_secretCT_prefix_preservation {p : SemanticProgram}
    (policy : RawSecretCTStepPolicy p) :
    ∀ fuel left right, StateWellFormed p left → StateWellFormed p right →
      SecretCTLowEquivalent p left right → ReleaseAlignedRaw p fuel left right →
        StateWellFormed p (runPrefix p fuel left).state ∧
        StateWellFormed p (runPrefix p fuel right).state ∧
        SecretCTLowEquivalent p (runPrefix p fuel left).state
          (runPrefix p fuel right).state ∧
        publicEvents (runPrefix p fuel left).events =
          publicEvents (runPrefix p fuel right).events := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right hwleft hwright hrel _
      exact ⟨hwleft, hwright, hrel, rfl⟩
  | succ fuel ih =>
      intro left right hwleft hwright hrel haligned
      have hone := policy left right hwleft hwright hrel haligned.1
      have htail := ih (step p left).state (step p right).state
        hone.1 hone.2.1 hone.2.2.1 haligned.2
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [runPrefix] using htail.1
      · simpa [runPrefix] using htail.2.1
      · simpa [runPrefix] using htail.2.2.1
      · simp only [runPrefix, publicEvents, List.filter_append]
        exact congrArg₂ (fun left right => left ++ right) hone.2.2.2 htail.2.2.2

theorem raw_secretCT_delimited_release_trace_equality {p : SemanticProgram}
    (policy : RawSecretCTStepPolicy p) {fuel : Nat} {left right : State}
    (hwleft : StateWellFormed p left) (hwright : StateWellFormed p right)
    (hlow : SecretCTLowEquivalent p left right)
    (hrelease : ReleaseAlignedRaw p fuel left right) :
    publicEvents (runPrefix p fuel left).events = publicEvents (runPrefix p fuel right).events := by
  exact (raw_secretCT_prefix_preservation policy fuel left right hwleft hwright hlow hrelease).2.2.2

theorem raw_secretCT_delimited_release_trace_equality_of_static_safe {p : SemanticProgram}
    (hsafe : SecretCTStaticSafe p) {fuel : Nat} {left right : State}
    (hwleft : StateWellFormed p left) (hwright : StateWellFormed p right)
    (hlow : SecretCTLowEquivalent p left right)
    (hrelease : ReleaseAlignedRaw p fuel left right) :
    publicEvents (runPrefix p fuel left).events = publicEvents (runPrefix p fuel right).events :=
  raw_secretCT_delimited_release_trace_equality
    (raw_secretCT_step_lockstep_of_static_safe hsafe) hwleft hwright hlow hrelease

/-! Non-vacuous machine witnesses. -/

def haltedState : State :=
  { pc := 0, values := #[], aggregates := #[], capabilityBalances := #[], halted := true }

def emptySemanticProgram : SemanticProgram :=
  { functions := #[], instructions := #[], operands := #[], valueLabels := #[] }

def fixedCTInstruction : Instruction :=
  { op := .ctEq, id := 0, functionId := 0, blockId := 0, destination := 0,
    firstOperand := 0, operandCount := 1, target := 0, resultLabel := .secretCT, aux := 7 }

theorem fixed_ct_cost_event_is_payload_independent (left right : Value) :
    instructionEvents emptySemanticProgram
        { haltedState with values := #[left] } fixedCTInstruction =
      instructionEvents emptySemanticProgram
        { haltedState with values := #[right] } fixedCTInstruction := by
  rfl

def variableCostMutant (secret : Int) : List Event :=
  List.replicate secret.natAbs { kind := .cost, payload := 1 }

theorem variable_cost_secretCT_mutant_breaks_trace_equality :
    variableCostMutant 1 ≠ variableCostMutant 2 := by decide

def rawSecretBranchInstruction : Instruction :=
  { op := .branch, id := 7, functionId := 1, blockId := 1, destination := 0,
    firstOperand := 0, operandCount := 1, target := 2, alternate := 1, merge := 3,
    blockLabel := .pub, resultLabel := .pub, aux := 0 }

def rawSecretBranchProgram : SemanticProgram :=
  { functions := #[], instructions := #[rawSecretBranchInstruction],
    operands := #[{ owner := 7, position := 0, value := 0, kind := 0 }],
    valueLabels := #[.secret] }

def rawSecretBranchState (payload : Int) : State :=
  { pc := 0, values := #[⟨.secret, payload⟩], aggregates := #[], capabilityBalances := #[] }

/-- Load-bearing witness: verification may reject a SecretCT branch, but ordinary Secret control is
    legal and the semantic machine must preserve its real branch decision rather than forcing one
    successor. -/
theorem raw_secret_branch_uses_the_unsanitized_payload :
    nextPc rawSecretBranchProgram (rawSecretBranchState 0) rawSecretBranchInstruction
        ⟨.secret, 0⟩ = 1 ∧
      nextPc rawSecretBranchProgram (rawSecretBranchState 1) rawSecretBranchInstruction
        ⟨.secret, 1⟩ = 2 := by decide

def forcedBranchMutant (instruction : Instruction) (operand : Value) : Nat :=
  if operand.label != .pub then instruction.target.toNat
  else if operand.payload = 0 then instruction.alternate.toNat else instruction.target.toNat

theorem forced_branch_mutant_changes_the_accepted_secret_execution :
    forcedBranchMutant rawSecretBranchInstruction ⟨.secret, 0⟩ ≠
      nextPc rawSecretBranchProgram (rawSecretBranchState 0) rawSecretBranchInstruction
        ⟨.secret, 0⟩ := by decide

/-- A raw Public payload emitted under ordinary-Secret control stays present in the machine trace,
    but its independently recorded occurrence label keeps it out of the legacy Public payload
    projection. -/
theorem secret_pc_boundary_keeps_raw_payload_without_public_leak (payload : Int) :
    eventsForValuesUnderPc .boundary 9 .secret [⟨.pub, payload⟩] =
        [{ kind := .boundary, payload, site := 9, occurrence := .secret, label := .pub }] ∧
      publicEvents (eventsForValuesUnderPc .boundary 9 .secret [⟨.pub, payload⟩]) = [] := by
  simp [eventsForValuesUnderPc, publicEvents, EventKind.eqb, Label.eqb]

/-- Load-bearing occurrence/payload separation. Public occurrence remains observable at the exact
    site and position even when its payload is Secret; changing only the occurrence to Secret
    removes the observation instead of revealing or fabricating a payload. -/
theorem public_boundary_trace_retains_occurrence_and_hides_secret_payload (payload : Int) :
    publicBoundaryTrace
        [{ kind := .output, payload, site := 17, occurrence := .pub, label := .secret }] =
      [{ kind := .output, site := 17, payload := none }] ∧
    publicBoundaryTrace
        [{ kind := .output, payload, site := 17, occurrence := .secret, label := .secret }] = [] := by
  simp [publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb, Label.eqb]

/-! ## Load-bearing native verifier surface

The source-record verifier runs first.  The second decision is over the decoded machine itself and
is reflection-equivalent to the SecretCT constructor obligations plus the Public structured-control
continuation check. A disagreement is an internal malformed verdict rather than a new source-policy
diagnostic; the legacy/source checker therefore retains diagnostic precedence during dual-gate
rollout. -/

theorem verifyProgramWithRawSemantics_none_iff (p : Program) :
    verifyProgramWithRawSemantics p = none ↔
      verifyProgram p = none ∧ rawRelationalStaticSafeB (semanticProgramOf p) = true := by
  have hverify : verifyProgramWithContext p (buildSemanticIndex p)
      (semanticLabelsWithIndex p (buildSemanticIndex p)) = verifyProgram p := by rfl
  have hdecoded : semanticProgramOfWith p (buildSemanticIndex p)
      (semanticLabelsWithIndex p (buildSemanticIndex p)) = semanticProgramOf p := by rfl
  unfold verifyProgramWithRawSemantics
  simp only [hverify, hdecoded]
  cases hsource : verifyProgram p with
  | some violation => simp
  | none =>
      cases hraw : rawRelationalStaticSafeB (semanticProgramOf p) <;> simp [hsource, hraw]

end LambdaSigil.Combined.Semantic
