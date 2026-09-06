import LambdaSigil.HostProfileKernel
import Init.Data.Array.QSort

/-!
# Separate, declaration-only occurrence wire envelope

Version nine retains a complete version-eight record prefix and appends tags 44--48. The
unchanged version-eight decoder still rejects version nine. This decoder retains the version,
complete provider declarations, exact FFI identities/signatures, actor constructors and root
contracts. Decoding is not a policy verdict, a compilation report, or host approval.

An absent profile is explicitly unknown legacy host semantics, never an implicit private host.
Root occurrence declarations are independent of return-payload labels. The separate native
declaration entry reports only successful decoding; it does not call the production verifier,
authorize compilation or approve profiles. Declaration witnesses and local decoder facts live
in OccurrenceWireSecurity.
-/

namespace LambdaSigil.Combined.V9

def version : UInt32 := 9
def chunkBytes : Nat := 20

structure FfiBinding where
  owner : UInt32
  profileOperation : UInt32
  firstArgument : UInt32
  paramCount : UInt32
  resultCount : UInt32
  name : String
  params : Array HostProfile.ValueType
  results : Array HostProfile.ValueType
  deriving Repr, BEq, DecidableEq

structure ActorBinding where
  owner : UInt32
  subtype : UInt32
  deriving Repr, BEq, DecidableEq

structure FunctionRootContract where
  nodeId : UInt32
  functionId : UInt32
  actorType : UInt32
  handlerId : UInt32
  exportName : String
  isEntry : Bool
  role : UInt8
  entryOccurrence : Label
  returnOccurrence : Label
  deriving Repr, BEq, DecidableEq

structure Program where
  wireVersion : UInt32
  base : Combined.Program
  hostProfileBytes : ByteArray
  hostProfile : Option HostProfile.Profile
  ffiBindings : Array FfiBinding
  actorBindings : Array ActorBinding
  roots : Array FunctionRootContract
  deriving BEq, DecidableEq

private structure Record where
  tag : UInt8
  labelA : UInt8
  labelB : UInt8
  flags : UInt8
  w0 : UInt32
  w1 : UInt32
  w2 : UInt32
  w3 : UInt32
  w4 : UInt32
  nodeId : UInt32

private def byte? (bytes : ByteArray) (offset : Nat) : Option UInt8 :=
  if h : offset < bytes.size then some (bytes.get offset h) else none

private def word? (bytes : ByteArray) (offset : Nat) : Option UInt32 := do
  let a ← byte? bytes offset
  let b ← byte? bytes (offset + 1)
  let c ← byte? bytes (offset + 2)
  let d ← byte? bytes (offset + 3)
  some (a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) |||
    (d.toUInt32 <<< 24))

private def record? (bytes : ByteArray) (index : Nat) : Option Record := do
  let offset := headerBytes + index * nodeBytes
  let tag ← byte? bytes offset
  let labelA ← byte? bytes (offset + 1)
  let labelB ← byte? bytes (offset + 2)
  let flags ← byte? bytes (offset + 3)
  let w0 ← word? bytes (offset + 4)
  let w1 ← word? bytes (offset + 8)
  let w2 ← word? bytes (offset + 12)
  let w3 ← word? bytes (offset + 16)
  let w4 ← word? bytes (offset + 20)
  let nodeId ← word? bytes (offset + 24)
  let reserved ← word? bytes (offset + 28)
  if reserved != 0 || nodeId.toNat != index + 1 then none else
    some ⟨tag, labelA, labelB, flags, w0, w1, w2, w3, w4, nodeId⟩

private def zeroHeader (record : Record) : Bool :=
  record.labelA == 0 && record.labelB == 0 && record.flags == 0

private structure Reader where
  bytes : ByteArray
  position : Nat
  count : Nat

private abbrev Parser (α : Type) := StateT Reader Option α

private def nextRecord : Parser Record := do
  let reader ← get
  if reader.position ≥ reader.count then failure
  let record ← record? reader.bytes reader.position
  set { reader with position := reader.position + 1 }
  pure record

private def readBytes (length : Nat) : Parser ByteArray := do
  let reader ← get
  let chunks := (length + chunkBytes - 1) / chunkBytes
  if length > maxWireBytes || chunks > reader.count - reader.position then failure
  let mut result := ByteArray.empty
  for _ in [0:chunks] do
    let record ← nextRecord
    if record.tag != 45 || !zeroHeader record then failure
    for word in #[record.w0, record.w1, record.w2, record.w3, record.w4] do
      for shift in [0:4] do
        let byte := UInt8.ofNat ((word.toNat / 2 ^ (8 * shift)) % 256)
        if result.size < length then result := result.push byte
        else if byte != 0 then failure
  pure result

private def occurrence? : UInt8 → Option Label
  | 0 => some .pub
  | 1 => some .internal
  | 2 => some .secret
  | _ => none

private def valueBefore (left right : Node) : Bool :=
  left.origin < right.origin || (left.origin == right.origin && left.actual < right.actual)

structure BindingIndex where
  functions : Array Node
  values : Array Node
  ffiOwners : Array Node
  actorOwners : Array Node

/-- This is an unambiguous declaration index, not a CFG or security-policy check. -/
def bindingIndex? (base : Combined.Program) : Option BindingIndex := do
  let functions := base.nodes.filter (fun node => node.op == .semFunction)
  for i in [0:functions.size] do
    let function ← functions[i]?
    if function.origin.toNat != i + 1 || function.flags > 4 then none
  let values := (base.nodes.filter (fun node => node.op == .semValue)).qsort valueBefore
  if !HostProfile.ordered valueBefore values.toList then none
  for value in values do
    if value.origin == 0 || value.origin.toNat > functions.size || value.actual == 0 ||
        value.required > 7 then none
  for owner in base.nodes do
    if owner.op == .semInstruction && (owner.aux == 15 || owner.aux == 8) &&
        (owner.origin == 0 || owner.origin.toNat > functions.size) then none
  some ⟨functions, values,
    base.nodes.filter (fun node => node.op == .semInstruction && node.aux == 15),
    base.nodes.filter (fun node => node.op == .semInstruction && node.aux == 8)⟩

private def abiType? : UInt32 → Option HostProfile.ValueType
  | 0 | 1 | 2 | 3 | 7 => some .i32
  | 4 | 5 => some .i64
  | 6 => some .f64
  | _ => none

def valueType? (index : BindingIndex) (owner : Node) (valueId : UInt32) :
    Option HostProfile.ValueType := do
  if owner.origin == 0 || owner.origin.toNat > index.functions.size || valueId == 0 then none
  let value ← index.values.binSearch { owner with actual := valueId } valueBefore
  if value.origin != owner.origin || value.actual != valueId then none
  abiType? value.required

def operand? (base : Combined.Program) (owner : Node) (position : Nat)
    (kind : UInt8) : Option Node := do
  if position ≥ owner.ceiling.toNat then none
  let operand ← base.nodes[owner.nodeId.toNat + position]?
  if operand.op != .semOperand || operand.origin != owner.nodeId ||
      operand.actual.toNat != position || operand.flags != kind then none
  some operand

private def immediate? (base : Combined.Program) (owner : Node) (position : Nat) :
    Option UInt64 := do
  let operand ← operand? base owner position 3
  some (operand.required.toUInt64 ||| (operand.ceiling.toUInt64 <<< 32))

private def identifierByte (byte : UInt8) : Bool :=
  (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122) || byte == 95

def externName? (base : Combined.Program) (owner : Node) : Option (String × Nat) := do
  if (← immediate? base owner 0) != 3 then none
  let length := (← immediate? base owner 1).toNat
  if length == 0 || length > HostProfile.maxNameBytes then none
  let words := (length + 7) / 8
  if 2 + words > owner.ceiling.toNat then none
  let mut name := ByteArray.empty
  for i in [0:words] do
    let word ← immediate? base owner (2 + i)
    for shift in [0:8] do
      let byte := UInt8.ofNat ((word.toNat / 2 ^ (8 * shift)) % 256)
      if name.size < length then name := name.push byte
      else if byte != 0 then none
  let first ← name.data[0]?
  if !identifierByte first ||
      !name.data.all (fun byte => identifierByte byte || (48 ≤ byte && byte ≤ 57)) then none
  let text ← String.fromUTF8? name
  some (text, 2 + words)

/-- Exact declaration binding. Zero is the explicit unknown legacy mode, not a policy label. -/
def hostBindingOK (profile : Option HostProfile.Profile) (binding : FfiBinding) : Bool :=
  match profile with
  | none => binding.profileOperation == 0
  | some profile =>
      if binding.profileOperation == 0 then false else
        match profile.operations[binding.profileOperation.toNat - 1]? with
        | none => false
        | some operation =>
            operation.moduleName == "ffi" && operation.name == binding.name &&
              operation.params.map (·.type) == binding.params &&
              operation.results.map (·.type) == binding.results

private def readFfi (base : Combined.Program) (index : BindingIndex)
    (profile : Option HostProfile.Profile) (owner : Node) : Parser FfiBinding := do
  let record ← nextRecord
  if record.tag != 46 || !zeroHeader record || record.w0 != owner.nodeId then failure
  let (name, first) ← externName? base owner
  if record.w2.toNat != first || first + record.w3.toNat != owner.ceiling.toNat ||
      record.w4.toNat != (if owner.required == 0 then 0 else 1) then failure
  let mut params := #[]
  for position in [first:owner.ceiling.toNat] do
    let operand ← operand? base owner position 0
    params := params.push (← valueType? index owner operand.required)
  let results ← if owner.required == 0 then pure #[]
    else do pure #[← valueType? index owner owner.required]
  let binding := FfiBinding.mk owner.nodeId record.w1 record.w2 record.w3 record.w4 name params results
  if !hostBindingOK profile binding then failure
  pure binding

private def readActor (owner : Node) : Parser ActorBinding := do
  let record ← nextRecord
  if record.tag != 47 || !zeroHeader record || record.w0 != owner.nodeId ||
      record.w1 < 1 || record.w1 > 5 || record.w2 != 0 || record.w3 != 0 || record.w4 != 0 then
    failure
  pure ⟨owner.nodeId, record.w1⟩

private def readRoot (function : Node) : Parser FunctionRootContract := do
  let record ← nextRecord
  if record.tag != 48 || record.w0 != function.origin || record.w4 > 1 then failure
  let entryOccurrence ← occurrence? record.labelA
  let returnOccurrence ← occurrence? record.labelB
  let nameBytes ← readBytes record.w3.toNat
  let exportName ← String.fromUTF8? nameBytes
  if exportName.isEmpty then failure
  let internal := record.flags == 0
  if internal then
    if !(function.flags == 1 || function.flags == 4 || exportName.startsWith "$") ||
        record.labelA != 0 || record.labelB != 0 || record.w1 != 0 ||
        record.w2 != 0 || record.w4 != 0 then failure
  else
    if record.flags != function.flags + 1 then failure
    if function.flags ≤ 1 && (record.w1 != 0 || record.w2 != 0 || record.w4 != 0) then failure
    if function.flags == 2 && record.w2 != 0 then failure
  pure ⟨record.nodeId, record.w0, record.w1, record.w2, exportName, record.w4 == 1,
    record.flags, entryOccurrence, returnOccurrence⟩

/-- The old prefix, decoded in place. This is exactly what `Combined.decode` computes on the
    reconstructed old header followed by the first `count` records: every header check of that
    decoder holds by construction (the magic and old version would be written here, `count` is
    at most the envelope's, and the envelope's size check guarantees the records are present),
    so only its node loop remains, and it runs at the same offsets on the same bytes. The
    prefix is not copied: a copy is a `copySlice`, which the kernel evaluates as an indexed
    walk (1.6 GB for 400 bytes under `decide +kernel`, measured 2026-09-05). -/
private def oldPrefix? (bytes : ByteArray) (count : Nat) : Option Combined.Program :=
  (Combined.decodeNodes bytes count).map (⟨·⟩)

private structure Declarations where
  hostProfileBytes : ByteArray
  hostProfile : Option HostProfile.Profile
  ffiBindings : Array FfiBinding
  actorBindings : Array ActorBinding
  roots : Array FunctionRootContract

private def readBody (base : Combined.Program) (manifest : Record) : Parser Declarations := do
  let index ← bindingIndex? base
  if manifest.w2.toNat != index.ffiOwners.size || manifest.w3.toNat != index.actorOwners.size ||
      manifest.w4.toNat != index.functions.size then failure
  let hostProfileBytes ← readBytes manifest.w1.toNat
  let hostProfile ← if hostProfileBytes.isEmpty then pure none
    else do pure (some (← HostProfile.decode hostProfileBytes))
  let ffiBindings ← index.ffiOwners.mapM (readFfi base index hostProfile)
  let actorBindings ← index.actorOwners.mapM readActor
  let roots ← index.functions.mapM readRoot
  let names := ((roots.filter (fun root => root.role != 0)).map (·.exportName)).qsort (· < ·)
  if !HostProfile.ordered (· < ·) names.toList then failure
  let reader ← get
  if reader.position != reader.count then failure
  pure ⟨hostProfileBytes, hostProfile, ffiBindings, actorBindings, roots⟩

/-- Bounded canonical framing and declaration binding only. No accepted-policy bit is returned. -/
def decode (bytes : ByteArray) : Option Program := do
  if bytes.size > maxWireBytes || bytes.size < headerBytes then none
  -- `CSIR`, read byte by byte: an `extract` is a copy, and the kernel evaluates a copy as an
  -- indexed walk over the whole array (see `oldPrefix?`); four reads are four short walks.
  if (← byte? bytes 0) != 0x43 || (← byte? bytes 1) != 0x53 ||
      (← byte? bytes 2) != 0x49 || (← byte? bytes 3) != 0x52 then none
  if (← word? bytes 4) != version then none
  let count := (← word? bytes 8).toNat
  if count > maxNodes || bytes.size != headerBytes + count * nodeBytes then none
  let mut baseCount := 0
  for i in [0:count] do
    if baseCount == i then
      if (← byte? bytes (headerBytes + i * nodeBytes)) ≤ 43 then baseCount := baseCount + 1
  if baseCount == count then none
  let manifest ← record? bytes baseCount
  if manifest.tag != 44 || !zeroHeader manifest || manifest.w0.toNat != baseCount then none
  let base ← oldPrefix? bytes baseCount
  let (declarations, _) ← (readBody base manifest).run ⟨bytes, baseCount + 1, count⟩
  -- Keep the final binding obligation explicit at the decoded-program boundary. Each FFI
  -- parser already checks this, so the linear postcheck does not broaden acceptance.
  if !declarations.ffiBindings.all (hostBindingOK declarations.hostProfile) then none
  some ⟨version, base, declarations.hostProfileBytes, declarations.hostProfile,
    declarations.ffiBindings, declarations.actorBindings, declarations.roots⟩

/-- Zero means well-formed declarations only, never policy acceptance or host approval. -/
def validateBytes (bytes : ByteArray) : UInt64 :=
  match decode bytes with
  | none => 1
  | some _ => 0

@[export sigil_csir_v9_validate_declarations]
def exportedValidateDeclarations (bytes : ByteArray) : UInt64 := validateBytes bytes

end LambdaSigil.Combined.V9
