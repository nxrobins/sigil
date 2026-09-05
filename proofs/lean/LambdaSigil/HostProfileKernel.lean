import LambdaSigil.CombinedKernel
import Init.Data.Array.BinSearch

/-!
# Canonical provider declarations for the v9 host boundary

This Init-only decoder consumes the complete version-1 `sigil-abi` host profile, not a digest
or caller-computed flow verdict. Occurrence visibility and payload labels are independent.
Consumed streams must declare a write as well as a read. Domain scope is retained verbatim;
checking a declaration does not prove that an installed callback respects that scope.

This module is an input-validation component, not the v9 occurrence verifier or a relational
theorem. In particular, it must not authorize a profile-bearing compilation by itself.
-/

namespace LambdaSigil.Combined.HostProfile

def encodingVersion : Nat := 1
def maxBytes : Nat := 64 * 1024 * 1024
def maxItems : Nat := 1_000_000
def maxNameBytes : Nat := 1024
def magic : ByteArray := "SIGIL-HOST-PROFILE\x00".toUTF8

inductive ValueType where
  | i32 | i64 | f32 | f64
  deriving Repr, BEq, DecidableEq

inductive DomainKind where
  | state | inputStream | output | guestMemory
  deriving Repr, BEq, DecidableEq

inductive DomainScope where
  | shared | perSite | perActor
  deriving Repr, BEq, DecidableEq

inductive AccessMode where
  | read | write | readWrite
  deriving Repr, BEq, DecidableEq

def AccessMode.reads : AccessMode → Bool
  | .read | .readWrite => true
  | .write => false

def AccessMode.writes : AccessMode → Bool
  | .write | .readWrite => true
  | .read => false

structure ValueContract where
  type : ValueType
  label : Label
  deriving Repr, BEq, DecidableEq

structure Domain where
  name : String
  kind : DomainKind := .state
  scope : DomainScope := .shared
  label : Label := .pub
  deriving Repr, BEq, DecidableEq

structure Access where
  domain : String
  mode : AccessMode
  deriving Repr, BEq, DecidableEq

structure Operation where
  moduleName : String
  name : String
  occurrence : Label
  params : Array ValueContract
  results : Array ValueContract
  accesses : Array Access
  deriving Repr, BEq, DecidableEq

structure Profile where
  identity : String
  revision : UInt64
  domains : Array Domain
  operations : Array Operation
  deriving Repr, BEq, DecidableEq

def Profile.itemCount (profile : Profile) : Nat :=
  profile.domains.size + profile.operations.size +
    profile.operations.foldl (fun count operation =>
      count + operation.params.size + operation.results.size + operation.accesses.size) 0

/-- Exact size of the canonical encoding, with all length fields counted. This structural
    bound also covers in-memory declarations; the reader checks before allocating collections. -/
def Profile.encodedSize (profile : Profile) : Nat :=
  magic.size + 4 + 4 + profile.identity.utf8ByteSize + 8 + 4 + 4 +
    profile.domains.foldl (fun size domain => size + 4 + domain.name.utf8ByteSize + 3) 0 +
    profile.operations.foldl (fun size operation =>
      size + 4 + operation.moduleName.utf8ByteSize + 4 + operation.name.utf8ByteSize + 1 +
        12 + 2 * (operation.params.size + operation.results.size) +
        operation.accesses.foldl (fun size access => size + 4 + access.domain.utf8ByteSize + 1) 0) 0

def nameByte (b : UInt8) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) || (48 ≤ b && b ≤ 57) ||
    b == 95 || b == 46 || b == 47 || b == 58 || b == 45

def validName (name : String) : Bool :=
  !name.isEmpty && name.utf8ByteSize ≤ maxNameBytes && name.toUTF8.data.all nameByte

/-- Linear adjacent-order validation. Strict ordering excludes duplicates without sorting or
    normalizing an adversarial encoding into another certificate identity. -/
def ordered {α : Type} (lt : α → α → Bool) : List α → Bool
  | [] | [_] => true
  | a :: b :: rest => lt a b && ordered lt (b :: rest)

def operationBefore (a b : Operation) : Bool :=
  a.moduleName < b.moduleName || (a.moduleName == b.moduleName && a.name < b.name)

/-- A logarithmic lookup into the strictly name-sorted declaration table. No source-side
    resolved domain index is trusted by this decoder. -/
def findDomain (domains : Array Domain) (name : String) : Option Domain :=
  domains.binSearch { name } (fun a b => a.name < b.name)

def accessKindOK (domain : Domain) (mode : AccessMode) : Bool :=
  match domain.kind with
  | .inputStream => mode == .readWrite
  | .output => mode == .write
  | .state | .guestMemory => true

def resolveAccesses (domains : Array Domain) (accesses : Array Access) :
    Option (Array (Domain × AccessMode)) :=
  accesses.mapM fun access => do
    let domain ← findDomain domains access.domain
    if !accessKindOK domain access.mode then none
    else some (domain, access.mode)

/-- All results and written domains depend on the occurrence, every parameter, and every read
    domain. This deliberately does not infer a finer dependency contract from the host name. -/
def influence (operation : Operation) (accesses : Array (Domain × AccessMode)) : Label :=
  accesses.foldl (fun label access =>
    if access.2.reads then label.lub access.1.label else label)
    (operation.params.foldl (fun label value => label.lub value.label) operation.occurrence)

def resolvedFlowsOK (operation : Operation) (accesses : Array (Domain × AccessMode)) : Bool :=
  let source := influence operation accesses
  source != .secretCT &&
    accesses.all (fun access => !access.2.writes || source.flowsTo access.1.label) &&
    operation.results.all (fun value => source.flowsTo value.label)

def operationOK (domains : Array Domain) (operation : Operation) : Bool :=
  validName operation.moduleName && validName operation.name &&
    operation.occurrence != .secretCT &&
    operation.accesses.all (fun access => validName access.domain) &&
    ordered (fun a b : Access => a.domain < b.domain) operation.accesses.toList &&
    match resolveAccesses domains operation.accesses with
    | none => false
    | some accesses => resolvedFlowsOK operation accesses

def declarationsOK (profile : Profile) : Bool :=
  validName profile.identity && profile.revision != 0 &&
    profile.domains.all (fun domain => validName domain.name) &&
    ordered (fun a b : Domain => a.name < b.name) profile.domains.toList &&
    ordered operationBefore profile.operations.toList &&
    profile.operations.all (operationOK profile.domains) &&
    profile.itemCount ≤ maxItems && profile.encodedSize ≤ maxBytes

structure Reader where
  bytes : ByteArray
  offset : Nat := 0
  items : Nat := 0

abbrev Parser (α : Type) := StateT Reader Option α

def take (count : Nat) : Parser ByteArray := do
  let reader ← get
  if reader.offset + count > reader.bytes.size then failure
  else
    set { reader with offset := reader.offset + count }
    pure (reader.bytes.extract reader.offset (reader.offset + count))

def byte : Parser Nat := do
  let reader ← get
  if h : reader.offset < reader.bytes.size then
    set { reader with offset := reader.offset + 1 }
    pure reader.bytes[reader.offset].toNat
  else failure

def word (width : Nat) : Parser Nat := do
  let reader ← get
  if reader.offset + width > reader.bytes.size then failure
  else
    let mut value := 0
    for i in [0:width] do
      value := value + reader.bytes[reader.offset + i]!.toNat * 2 ^ (8 * i)
    set { reader with offset := reader.offset + width }
    pure value

def name : Parser String := do
  let length ← word 4
  if length == 0 || length > maxNameBytes then failure
  let bytes ← take length
  if !bytes.data.all nameByte then failure
  match String.fromUTF8? bytes with
  | none => failure
  | some value => pure value

/-- Check both the aggregate item ceiling and a remaining-byte lower bound before allocating
    or iterating a declared collection. A huge count in a short input takes bounded work. -/
def count (minimumBytes : Nat) : Parser Nat := do
  let count ← word 4
  let reader ← get
  if reader.items + count > maxItems ||
      count * minimumBytes > reader.bytes.size - reader.offset then failure
  set { reader with items := reader.items + count }
  pure count

def label : Parser Label := do
  match ← byte with
  | 0 => pure .pub
  | 1 => pure .internal
  | 2 => pure .secret
  | 3 => pure .secretCT
  | _ => failure

def occurrence : Parser Label := do
  match ← byte with
  | 0 => pure .pub
  | 1 => pure .internal
  | 2 => pure .secret
  | _ => failure

def valueType : Parser ValueType := do
  match ← byte with
  | 0 => pure .i32
  | 1 => pure .i64
  | 2 => pure .f32
  | 3 => pure .f64
  | _ => failure

def domainKind : Parser DomainKind := do
  match ← byte with
  | 0 => pure .state
  | 1 => pure .inputStream
  | 2 => pure .output
  | 3 => pure .guestMemory
  | _ => failure

def domainScope : Parser DomainScope := do
  match ← byte with
  | 0 => pure .shared
  | 1 => pure .perSite
  | 2 => pure .perActor
  | _ => failure

def accessMode : Parser AccessMode := do
  match ← byte with
  | 0 => pure .read
  | 1 => pure .write
  | 2 => pure .readWrite
  | _ => failure

def values : Parser (Array ValueContract) := do
  let size ← count 2
  let mut result := #[]
  for _ in [0:size] do
    result := result.push ⟨← valueType, ← label⟩
  pure result

def readDomains : Parser (Array Domain) := do
  let size ← count 8
  let mut result := #[]
  for _ in [0:size] do
    result := result.push ⟨← name, ← domainKind, ← domainScope, ← label⟩
  pure result

def readAccesses : Parser (Array Access) := do
  let size ← count 6
  let mut result := #[]
  for _ in [0:size] do
    result := result.push ⟨← name, ← accessMode⟩
  pure result

def readOperations : Parser (Array Operation) := do
  let size ← count 23
  let mut result := #[]
  for _ in [0:size] do
    result := result.push ⟨← name, ← name, ← occurrence, ← values, ← values, ← readAccesses⟩
  pure result

def readProfile : Parser Profile := do
  if (← take magic.size) != magic then failure
  if (← word 4) != encodingVersion then failure
  let identity ← name
  let revision := UInt64.ofNat (← word 8)
  let domains ← readDomains
  let operations ← readOperations
  let reader ← get
  if reader.offset != reader.bytes.size then failure
  pure ⟨identity, revision, domains, operations⟩

/-- Fail-closed full-profile decoder. Names, order, duplicate declarations, exact enum tags,
    lengths, footprints, downgrade attempts, and trailing bytes are checked in Lean. -/
def decode (bytes : ByteArray) : Option Profile := do
  if bytes.size > maxBytes then none
  let (profile, _) ← readProfile.run { bytes }
  if declarationsOK profile then some profile else none

/-- Native declaration-validation entry point. Zero means this profile decoded and its declared
    flows passed; it does not mean any CSIR program or host implementation was verified. -/
@[export sigil_host_profile_validate]
def validateBytes (bytes : ByteArray) : UInt64 :=
  if (decode bytes).isSome then 0 else 1

end LambdaSigil.Combined.HostProfile
