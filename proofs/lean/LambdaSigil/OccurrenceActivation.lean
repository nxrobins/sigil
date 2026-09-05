import LambdaSigil.SemanticKernel

/-!
# Separate activation storage for the future occurrence machine

The existing wire already identifies every semantic value's owning function and global machine
cell. This Init-only foundation derives a shared ownership index from those declarations, saves
all callee-owned scalar AND aggregate cells, and restores them before writing a call result. It
does not change the historical v8 machine, approve security policy, or prove Public equivalence.

Actor state, external streams/cursors, and capability balances are intentionally shared effects,
not activation-local storage. Snapshots never roll them back. Payloads have no runtime-controlled
labels; labels remain in decoded program declarations. Calls and returns are partial only through
explicit `Option` rejection; all underlying storage operations are total and bounds preserving.
-/

namespace LambdaSigil.Combined.OccurrenceActivation

open Semantic

structure CellValue where
  scalar : Int
  aggregate : List Int
  deriving Repr, BEq, DecidableEq, Inhabited

structure Store where
  scalars : Array Int
  aggregates : Array (List Int)
  deriving Repr, BEq, DecidableEq

def Store.read (store : Store) (cell : Nat) : CellValue :=
  ⟨store.scalars.getD cell 0, store.aggregates.getD cell []⟩

def Store.write (store : Store) (cell : Nat) (value : CellValue) : Store :=
  ⟨store.scalars.setIfInBounds cell value.scalar,
    store.aggregates.setIfInBounds cell value.aggregate⟩

abbrev Snapshot := List (Nat × CellValue)

def snapshot (store : Store) (cells : List Nat) : Snapshot :=
  cells.map (fun cell => (cell, store.read cell))

def restore (store : Store) : Snapshot → Store
  | [] => store
  | (cell, value) :: rest => restore (store.write cell value) rest

def assign (store : Store) : List Nat → List CellValue → Store
  | parameter :: parameters, argument :: arguments =>
      assign (store.write parameter argument) parameters arguments
  | _, _ => store

structure Shared where
  actorState : Array Int := #[]
  externalInputs : Array (List Int) := #[]
  externalCursors : Array Nat := #[]
  capabilityBalances : Array Nat := #[]
  deriving Repr, BEq, DecidableEq

structure Frame where
  callPc : Nat
  callSite : UInt32
  caller : UInt32
  callee : UInt32
  entryPc : Nat
  returnPc : Nat
  destination : UInt32
  returnLabel : Label
  saved : Snapshot
  deriving Repr, BEq, DecidableEq

structure State where
  pc : Nat
  activeFunction : UInt32
  store : Store
  shared : Shared := {}
  frames : List Frame := []
  halted : Bool := false
  trapped : Bool := false
  deriving Repr, BEq, DecidableEq

/-- Exact declarative ownership, independent of any parameter/capture list or runtime frame. -/
def declaredCells (source : Combined.Program) (function : UInt32) : List Nat :=
  source.nodes.toList.filterMap (fun node =>
    if node.op = .semValue ∧ node.origin = function then some node.nodeId.toNat else none)

def addOwned (table : Array (List Nat)) (node : Node) : Array (List Nat) :=
  if node.op = .semValue then
    table.setIfInBounds node.origin.toNat (node.nodeId.toNat :: table.getD node.origin.toNat [])
  else table

def buildOwned (source : Combined.Program) (functionCount : Nat) : Array (List Nat) :=
  source.nodes.toList.foldl addOwned (Array.replicate (functionCount + 1) [])

def declaredOwnerB (p : SemanticProgram) (function : UInt32) (cell : Nat) : Bool :=
  cell != 0 && match p.source.nodes[cell - 1]? with
    | none => false
    | some node => node.op == .semValue && node.nodeId.toNat == cell && node.origin == function

def functionAt? (p : SemanticProgram) (id : UInt32) : Option Function := do
  if id == 0 then none
  let function ← p.functions[id.toNat - 1]?
  if function.id != id then none else some function

/-- Check the ownership representation once. Function parameters may be only a subset of owned
    cells, but each must belong to the same declared function. No Rust-owned list is accepted. -/
def ownershipLayoutB (p : SemanticProgram) : Bool :=
  let declarations := p.source.nodes.filter (fun node => node.op == .semFunction)
  p.source.nodes.size ≤ maxNodes && p.valueLabels.size == semanticTaintCellCount p.source &&
    declarations.size == p.functions.size &&
    (List.range p.functions.size).all (fun position =>
      match p.functions[position]?, declarations[position]? with
      | some function, some declaration =>
          function.id.toNat == position + 1 && declaration.origin == function.id &&
          function.parameterCells.all (fun cell => declaredOwnerB p function.id cell.toNat)
      | _, _ => false) &&
    (List.range p.source.nodes.size).all (fun position =>
      match p.source.nodes[position]? with
      | none => false
      | some node => node.nodeId.toNat == position + 1 &&
          (if node.op == .semValue then
            node.actual != 0 && (functionAt? p node.origin).isSome
           else true))

structure OwnershipIndex where
  byFunction : Array (List Nat)
  deriving Repr, BEq, DecidableEq

def ownershipIndex? (p : SemanticProgram) : Option OwnershipIndex :=
  if ownershipLayoutB p then some ⟨buildOwned p.source p.functions.size⟩ else none

/-- The reusable cache cannot carry a separately supplied ownership table. Its proof is erased
    in native code; construction occurs inside Lean and is tied to this immutable program. -/
structure Prepared (p : SemanticProgram) where
  index : OwnershipIndex
  checked : ownershipIndex? p = some index

def prepare? (p : SemanticProgram) : Option (Prepared p) :=
  match h : ownershipIndex? p with
  | none => none
  | some index => some ⟨index, h⟩

def storeShapeB (p : SemanticProgram) (store : Store) : Bool :=
  store.scalars.size == p.valueLabels.size && store.aggregates.size == p.valueLabels.size

def resolvedCallee? (p : SemanticProgram) (state : State) (call : Instruction) : Option Function :=
  match call.op with
  | .call => (functionOperand? p call).bind (functionAt? p)
  | .closure => do
      let selector ← (valueOperandCells p call).head?
      if !declaredOwnerB p call.functionId selector.toNat then none
      let target := (state.store.read selector.toNat).scalar
      if target < 0 || target.toNat ≥ p.functions.size then none
      functionAt? p (UInt32.ofNat (target.toNat + 1))
  | _ => none

def argumentCells (p : SemanticProgram) (call : Instruction) : List Nat :=
  let values := (valueOperandCells p call).map UInt32.toNat
  if call.op == .closure then values.drop 1 else values

/-- Historical call selection and continuation must refer to real decoded declarations. A
    dynamic frame records its selected callee; reachability/history is established by entry,
    not invented by this static return-time coherence check. -/
def frameCoherentB (p : SemanticProgram) (frame : Frame) : Bool :=
  match p.instructions[frame.callPc]?, p.instructions[frame.returnPc]?,
      functionAt? p frame.caller, functionAt? p frame.callee with
  | some call, some continuation, some _, some callee =>
      (call.op == .call || call.op == .closure) && call.id == frame.callSite &&
      call.functionId == frame.caller && frame.returnPc == frame.callPc + 1 &&
      continuation.functionId == frame.caller && call.destination == frame.destination &&
      callee.firstInstruction.toNat == frame.entryPc && callee.returnLabel == frame.returnLabel &&
      (if call.op == .call then functionOperand? p call == some frame.callee else true) &&
      (frame.destination == 0 || declaredOwnerB p frame.caller frame.destination.toNat)
  | _, _, _, _ => false

def makeFrame (state : State) (call : Instruction) (callee : Function)
    (cells : List Nat) : Frame :=
  { callPc := state.pc
    callSite := call.id
    caller := state.activeFunction
    callee := callee.id
    entryPc := callee.firstInstruction.toNat
    returnPc := state.pc + 1
    destination := call.destination
    returnLabel := callee.returnLabel
    saved := snapshot state.store cells }

def enterResolved (state : State) (frame : Frame) (parameters : List Nat)
    (arguments : List CellValue) : State :=
  { state with
    pc := frame.entryPc
    activeFunction := frame.callee
    store := assign state.store parameters arguments
    frames := frame :: state.frames }

/-- Prepared ownership is shared across calls; each entry touches only operands and callee-local
    cells, rather than rescanning the complete declaration stream. -/
def enterPrepared? (p : SemanticProgram) (prepared : Prepared p) (state : State) : Option State := do
  let index := prepared.index
  if state.halted || state.trapped || !storeShapeB p state.store then none
  let call ← p.instructions[state.pc]?
  if call.functionId != state.activeFunction || !operandSliceWellFormedB p call then none
  let callee ← resolvedCallee? p state call
  let entry ← p.instructions[callee.firstInstruction.toNat]?
  if entry.functionId != callee.id then none
  let cells := index.byFunction.getD callee.id.toNat []
  let arguments := argumentCells p call
  if arguments.length != callee.parameterCells.size ||
      !arguments.all (declaredOwnerB p state.activeFunction) then none
  let frame := makeFrame state call callee cells
  if !frameCoherentB p frame then none
  some (enterResolved state frame (callee.parameterCells.toList.map UInt32.toNat)
    (arguments.map state.store.read))

def enter? (p : SemanticProgram) (state : State) : Option State := do
  let prepared ← prepare? p
  enterPrepared? p prepared state

def restoreFrame (state : State) (frame : Frame) : State :=
  { state with store := restore state.store frame.saved }

/-- Return values are captured before restoring the callee. Restoration happens before writing
    the result, including recursive calls whose destination is in the callee's saved cell set. -/
def finish (state : State) (frame : Frame) (rest : List Frame) (result : CellValue) : State :=
  let restored := restoreFrame state frame
  let store := if frame.destination == 0 then restored.store
    else restored.store.write frame.destination.toNat result
  { restored with store, pc := frame.returnPc, activeFunction := frame.caller, frames := rest }

def returnPrepared? (p : SemanticProgram) (prepared : Prepared p) (state : State) : Option State := do
  let index := prepared.index
  if state.halted || state.trapped || !storeShapeB p state.store then none
  let frame :: rest := state.frames | none
  if state.activeFunction != frame.callee || !frameCoherentB p frame ||
      frame.saved.map Prod.fst != index.byFunction.getD frame.callee.toNat [] then none
  let output ← p.instructions[state.pc]?
  if output.op != .output || output.functionId != frame.callee ||
      !operandSliceWellFormedB p output then none
  let result ← match (valueOperandCells p output).head? with
    | none => if frame.destination == 0 then some (0, []) else none
    | some cell =>
        if declaredOwnerB p frame.callee cell.toNat then
          let value := state.store.read cell.toNat
          some (value.scalar, value.aggregate)
        else none
  some (finish state frame rest ⟨result.1, result.2⟩)

def return? (p : SemanticProgram) (state : State) : Option State := do
  let prepared ← prepare? p
  returnPrepared? p prepared state

end LambdaSigil.Combined.OccurrenceActivation
