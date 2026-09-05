import LambdaSigil.OccurrenceWire

/-!
# Indexed boundary contracts, without a policy verdict

This layer rederives FFI identities and signatures from actual instruction operands using the
wire decoder's shared index. It does not assume that an arbitrary in-memory `V9.Program` came
from decoding. Missing, duplicate and mismatched declarations fail extraction.

Legacy host occurrence is Public and its parameter/result policy remains Internal. Its state
footprint is explicitly unknown, not an empty/private footprint. Actor delivery defaults are
Public; serialize/deserialize are retained as codecs, not external deliveries. No private actor
endpoint or receiver-isolation contract exists in this wire format. Function-root occurrences
come only from the exact root declarations, independently of payload labels.

The invocation context below is explicit input, not a proof that a runtime frame is genuine.
Extraction is neither occurrence enforcement, host conformance nor a Public security theorem.
-/

namespace LambdaSigil.Combined.V9.BoundaryContracts

inductive FfiPolicy where
  | legacyUnknown
  | declared (operation : HostProfile.Operation)
  deriving Repr, BEq, DecidableEq

structure FfiContract where
  binding : FfiBinding
  policy : FfiPolicy
  deriving Repr, BEq, DecidableEq

def FfiContract.occurrence (contract : FfiContract) : Label :=
  match contract.policy with
  | .legacyUnknown => .pub
  | .declared operation => operation.occurrence

def FfiContract.parameters (contract : FfiContract) : Array HostProfile.ValueContract :=
  match contract.policy with
  | .legacyUnknown => contract.binding.params.map fun type => ⟨type, .internal⟩
  | .declared operation => operation.params

def FfiContract.results (contract : FfiContract) : Array HostProfile.ValueContract :=
  match contract.policy with
  | .legacyUnknown => contract.binding.results.map fun type => ⟨type, .internal⟩
  | .declared operation => operation.results

/-- None is unknown legacy host state, not a claim that the callback has no footprint. -/
def FfiContract.accesses (contract : FfiContract) : Option (Array HostProfile.Access) :=
  match contract.policy with
  | .legacyUnknown => none
  | .declared operation => some operation.accesses

inductive ActorSubtype where
  | send | ask | spawn | serialize | deserialize
  deriving Repr, BEq, DecidableEq

def actorSubtype? : UInt32 → Option ActorSubtype
  | 1 => some .send
  | 2 => some .ask
  | 3 => some .spawn
  | 4 => some .serialize
  | 5 => some .deserialize
  | _ => none

/-- No delivery is attributed to serialization, even when its payload is private. -/
def ActorSubtype.deliveryOccurrence : ActorSubtype → Option Label
  | .send | .ask | .spawn => some .pub
  | .serialize | .deserialize => none

structure ActorContract where
  binding : ActorBinding
  subtype : ActorSubtype
  deriving Repr, BEq, DecidableEq

inductive SiteKind where
  | ordinary (operation : SemanticInstrOp)
  | ffi (bindingPosition : Nat) (contract : FfiContract)
  | actor (bindingPosition : Nat) (contract : ActorContract)
  deriving Repr, BEq, DecidableEq

structure SiteContract where
  owner : UInt32
  functionId : UInt32
  kind : SiteKind
  deriving Repr, BEq, DecidableEq

structure Index where
  /-- One slot per original record; non-instruction records have no site entry. -/
  sites : Array (Option SiteContract)
  roots : Array FunctionRootContract
  hostProfile : Option HostProfile.Profile
  deriving Repr, BEq, DecidableEq

/-- Reuse the one shared value/function index; do not rebuild it for each extern call. -/
def ffiContract? (program : Program) (source : BindingIndex) (owner : Node)
    (position : Nat) : Option FfiContract := do
  if owner.op != .semInstruction || owner.aux != 15 || owner.origin == 0 ||
      owner.origin.toNat > source.functions.size then none
  let binding ← program.ffiBindings[position]?
  if binding.owner != owner.nodeId then none
  let (name, first) ← externName? program.base owner
  if binding.name != name || binding.firstArgument.toNat != first ||
      first + binding.paramCount.toNat != owner.ceiling.toNat ||
      binding.resultCount.toNat != (if owner.required == 0 then 0 else 1) then none
  let mut params := #[]
  for operandPosition in [first:owner.ceiling.toNat] do
    let operand ← operand? program.base owner operandPosition 0
    params := params.push (← valueType? source owner operand.required)
  let results ← if owner.required == 0 then pure #[]
    else do pure #[← valueType? source owner owner.required]
  if !decide (binding.params = params ∧ binding.results = results) then none
  if !hostBindingOK program.hostProfile binding then none
  let policy ← match program.hostProfile with
    | none => some FfiPolicy.legacyUnknown
    | some profile => do
        let operation ← profile.operations[binding.profileOperation.toNat - 1]?
        some (.declared operation)
  some ⟨binding, policy⟩

def actorContract? (program : Program) (owner : Node) (position : Nat) :
    Option ActorContract := do
  if owner.op != .semInstruction || owner.aux != 8 then none
  let binding ← program.actorBindings[position]?
  if binding.owner != owner.nodeId then none
  let subtype ← actorSubtype? binding.subtype
  some ⟨binding, subtype⟩

/-- A source-derived correspondence check, separate from the table-construction traversal. -/
def siteMatches (program : Program) (source : BindingIndex) (owner : Node)
    (site : SiteContract) : Bool :=
  owner.op == .semInstruction && owner.origin != 0 &&
    owner.origin.toNat ≤ source.functions.size &&
    site.owner == owner.nodeId && site.functionId == owner.origin &&
    match site.kind with
    | .ordinary operation =>
        operation != .ffi && operation != .actorBoundary &&
          decide (decodeSemanticInstrOp? owner.aux = some operation)
    | .ffi position contract => decide (ffiContract? program source owner position = some contract)
    | .actor position contract => decide (actorContract? program owner position = some contract)

def recordMatches (program : Program) (source : BindingIndex) (index : Index)
    (position : Nat) : Bool :=
  match program.base.nodes[position]?, index.sites[position]? with
  | some owner, some site =>
      owner.nodeId.toNat == position + 1 &&
        match site with
        | none => owner.op != .semInstruction
        | some site => siteMatches program source owner site
  | _, _ => false

def site? (index : Index) (owner : UInt32) : Option SiteContract := do
  if owner == 0 then none
  let entry ← index.sites[owner.toNat - 1]?
  entry

def ffiCovered (program : Program) (index : Index) (position : Nat) : Bool :=
  match program.ffiBindings[position]? with
  | none => false
  | some binding =>
      match site? index binding.owner with
      | some { kind := .ffi found _, .. } => found == position
      | _ => false

def actorCovered (program : Program) (index : Index) (position : Nat) : Bool :=
  match program.actorBindings[position]? with
  | none => false
  | some binding =>
      match site? index binding.owner with
      | some { kind := .actor found _, .. } => found == position
      | _ => false

/-- Checked once after construction. There is no caller-supplied accepted bit in an Index. -/
def indexChecks (program : Program) (source : BindingIndex) (index : Index) : Bool :=
  index.sites.size == program.base.nodes.size &&
    decide (index.roots = program.roots ∧ index.hostProfile = program.hostProfile) &&
    (List.range program.base.nodes.size).all (recordMatches program source index) &&
    (List.range program.ffiBindings.size).all (ffiCovered program index) &&
    (List.range program.actorBindings.size).all (actorCovered program index)

private def ownerTable? {α : Type} (count : Nat) (bindings : Array α)
    (ownerOf : α → UInt32) : Option (Array (Option Nat)) := do
  let mut table := Array.replicate count none
  for position in [0:bindings.size] do
    let binding ← bindings[position]?
    let owner := (ownerOf binding).toNat
    if owner == 0 || owner > count then none
    let previous ← table[owner - 1]?
    if previous.isSome then none
    table := table.set! (owner - 1) (some position)
  some table

private def buildSite? (program : Program) (source : BindingIndex)
    (ffi actor : Array (Option Nat)) (position : Nat) : Option (Option SiteContract) := do
  let owner ← program.base.nodes[position]?
  let ffiPosition ← ffi[position]?
  let actorPosition ← actor[position]?
  if owner.nodeId.toNat != position + 1 then none
  if owner.op != .semInstruction then
    if ffiPosition.isSome || actorPosition.isSome then none else some none
  else do
    if owner.origin == 0 || owner.origin.toNat > source.functions.size then none
    let operation ← decodeSemanticInstrOp? owner.aux
    let kind ← match operation with
      | .ffi => do
          if actorPosition.isSome then none
          let position ← ffiPosition
          some (.ffi position (← ffiContract? program source owner position))
      | .actorBoundary => do
          if ffiPosition.isSome then none
          let position ← actorPosition
          some (.actor position (← actorContract? program owner position))
      | operation =>
          if ffiPosition.isSome || actorPosition.isSome then none
          else some (.ordinary operation)
    some (some ⟨owner.nodeId, owner.origin, kind⟩)

private def rootsOK (program : Program) (source : BindingIndex) : Bool := Id.run do
  if program.roots.size != source.functions.size then return false
  let mut record := program.base.nodes.size + 2 + (program.hostProfileBytes.size + 19) / 20 +
    program.ffiBindings.size + program.actorBindings.size
  for position in [0:program.roots.size] do
    let some root := program.roots[position]? | return false
    let some function := source.functions[position]? | return false
    if root.functionId.toNat != position + 1 || root.functionId != function.origin ||
        root.nodeId.toNat != record || root.exportName.isEmpty ||
        root.entryOccurrence == .secretCT || root.returnOccurrence == .secretCT then return false
    let internal := root.role == 0
    if internal then
      if !(function.flags == 1 || function.flags == 4 || root.exportName.startsWith "$") ||
          root.entryOccurrence != .pub || root.returnOccurrence != .pub ||
          root.actorType != 0 || root.handlerId != 0 || root.isEntry then return false
    else
      if root.role != function.flags + 1 then return false
      if function.flags ≤ 1 && (root.actorType != 0 || root.handlerId != 0 || root.isEntry) then
        return false
      if function.flags == 2 && root.handlerId != 0 then return false
    record := record + 1 + (root.exportName.utf8ByteSize + 19) / 20
  let names := ((program.roots.filter (fun root => root.role != 0)).map (·.exportName)).qsort (· < ·)
  return record - 1 ≤ maxNodes && headerBytes + (record - 1) * nodeBytes ≤ maxWireBytes &&
    HostProfile.ordered (· < ·) names.toList

/-- Bounded structural extraction only. The actual verifier and host-approval gates are separate. -/
def extract? (program : Program) : Option Index := do
  if program.wireVersion != version || program.hostProfileBytes.size > maxWireBytes ||
      program.base.nodes.size + program.ffiBindings.size + program.actorBindings.size +
        program.roots.size + 1 > maxNodes then none
  let decodedProfile := if program.hostProfileBytes.isEmpty then some none
    else (HostProfile.decode program.hostProfileBytes).map some
  if !decide (decodedProfile = some program.hostProfile) then none
  let source ← bindingIndex? program.base
  if !rootsOK program source then none
  if !HostProfile.ordered (fun a b : FfiBinding => a.owner < b.owner) program.ffiBindings.toList ||
      !HostProfile.ordered (fun a b : ActorBinding => a.owner < b.owner)
        program.actorBindings.toList then none
  let ffi ← ownerTable? program.base.nodes.size program.ffiBindings (·.owner)
  let actor ← ownerTable? program.base.nodes.size program.actorBindings (·.owner)
  let sites ← (List.range program.base.nodes.size).toArray.mapM (buildSite? program source ffi actor)
  let index := Index.mk sites program.roots program.hostProfile
  if !indexChecks program source index then none
  some index

inductive InvocationContext where
  | root | internalCall
  deriving Repr, BEq, DecidableEq

inductive RootPhase where
  | entry | returned
  deriving Repr, BEq, DecidableEq

structure RootBoundary where
  declaration : FunctionRootContract
  phase : RootPhase
  occurrence : Label
  deriving Repr, BEq, DecidableEq

/-- Invalid/missing function IDs refuse. A present internal-call context emits no root boundary.
    This API classifies a supplied context; it does not prove an operational call-stack fact. -/
def rootBoundary? (index : Index) (functionId : UInt32) (context : InvocationContext)
    (phase : RootPhase) : Option (Option RootBoundary) := do
  if functionId == 0 then none
  let root ← index.roots[functionId.toNat - 1]?
  if root.functionId != functionId then none
  if context == .internalCall then some none
  else if root.role == 0 then none
  else some (some ⟨root, phase,
    match phase with | .entry => root.entryOccurrence | .returned => root.returnOccurrence⟩)

end LambdaSigil.Combined.V9.BoundaryContracts
