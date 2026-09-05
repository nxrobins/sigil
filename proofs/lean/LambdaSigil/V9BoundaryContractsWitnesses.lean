import LambdaSigil.V9BoundaryContractsSecurity

/-!
# Nonvacuous boundary-extraction witnesses

These executable checks are not kernel theorems. Small declaration programs need not satisfy
a CFG/security judgment. Their positive extraction checks plant the entries subsequently
removed or corrupted by the mutants. No private callback, private actor endpoint, or
occurrence-safe execution is approved here. Source-built positives are embedded below so the
normal module build checks them; an extraction failure cannot count as a mutant rejection.
-/

namespace LambdaSigil.Combined.V9.BoundaryContracts.BoundaryWitnesses

private def node (op : Op) (id : UInt32) (origin : UInt32 := 0) (actual : UInt32 := 0)
    (required : UInt32 := 0) (ceiling : UInt32 := 0) (aux : UInt32 := 0)
    (flags : UInt8 := 0) (label : Label := .pub) : Node :=
  ⟨op, label, .pub, flags, origin, actual, required, ceiling, aux, id⟩

private def function : Node := node .semFunction 1 1 1 0 0 0 1

private def root (id : UInt32) : FunctionRootContract :=
  ⟨id, 1, 0, 0, "run", false, 2, .pub, .pub⟩

private def legacyBinding : FfiBinding := ⟨2, 0, 3, 0, 0, "tick", #[], #[]⟩

private def zeroPayload : Program :=
  ⟨9, ⟨#[function, node .semInstruction 2 1 1 0 3 15 1,
    node .semOperand 3 2 0 3 0 0 3, node .semOperand 4 2 1 4 0 0 3,
    node .semOperand 5 2 2 0x6b636974 0 0 3]⟩,
    ByteArray.empty, none, #[legacyBinding], #[], #[root 8]⟩

private def ffiAt? (program : Program) (owner : UInt32) : Option FfiContract := do
  let index ← extract? program
  let site ← site? index owner
  match site.kind with
  | .ffi _ contract => some contract
  | _ => none

private def zeroPayloadHasPublicUnknownContract : Bool :=
    (ffiAt? zeroPayload 2).map (fun contract =>
      (contract.occurrence, contract.parameters.size, contract.results.size,
        contract.accesses.isNone)) == some (.pub, 0, 0, true)

private def missingDuplicateWrongOwnerAndChangedNameRefused : Bool :=
    (extract? { zeroPayload with ffiBindings := #[] }).isNone &&
      (extract? { { zeroPayload with ffiBindings := #[legacyBinding, legacyBinding] }
        with roots := #[root 9] }).isNone &&
      (extract? { zeroPayload with ffiBindings := #[{ legacyBinding with owner := 1 }] }).isNone &&
      (extract? { zeroPayload with ffiBindings := #[{ legacyBinding with name := "tock" }] }).isNone

private def privatePayload : Program :=
  ⟨9, ⟨#[function,
    node .semValue 2 1 1 4 0 0 0 .secret,
    node .semValue 3 1 2 4 0 0 0 .internal,
    node .semInstruction 4 1 1 2 4 15 1 .secret,
    node .semOperand 5 4 0 3 0 0 3,
    node .semOperand 6 4 1 4 0 0 3,
    node .semOperand 7 4 2 0x6b636974 0 0 3,
    node .semOperand 8 4 3 1]⟩,
    ByteArray.empty, none, #[⟨4, 0, 3, 1, 1, "tick", #[.i64], #[.i64]⟩], #[], #[root 11]⟩

private def privatePayloadCannotSupplyPrivatePolicy : Bool :=
    (ffiAt? privatePayload 4).map (fun contract =>
      (contract.occurrence, contract.parameters.map (·.label), contract.results.map (·.label))) ==
      some (.pub, #[.internal], #[.internal])

private def privateHostMutantRefused : Bool := Id.run do
  let some source := bindingIndex? privatePayload.base | return false
  let some index := extract? privatePayload | return false
  let some site := site? index 4 | return false
  let .ffi position contract := site.kind | return false
  let fabricated : HostProfile.Operation :=
    ⟨"ffi", "tick", .secret, #[⟨.i64, .secret⟩], #[⟨.i64, .secret⟩], #[]⟩
  let mutant := { site with kind := .ffi position { contract with policy := .declared fabricated } }
  return !indexChecks privatePayload source { index with sites := index.sites.set! 3 (some mutant) }

private def privatePolicyLaunderingAndWrongAbiRefused : Bool :=
    privateHostMutantRefused &&
      (extract? { privatePayload with ffiBindings :=
        #[⟨4, 0, 3, 1, 1, "tick", #[.i32], #[.i64]⟩] }).isNone

private def actorProgram : Program :=
  ⟨9, ⟨#[function] ++ (List.range 5).toArray.map (fun i =>
    node .semInstruction (UInt32.ofNat (i + 2)) 1 1 0 0 8 1 .secret)⟩,
    ByteArray.empty, none, #[], (List.range 5).toArray.map (fun i =>
      ⟨UInt32.ofNat (i + 2), UInt32.ofNat (i + 1)⟩), #[root 13]⟩

private def actorSummary : Option (Array (ActorSubtype × Option Label)) := do
  let index ← extract? actorProgram
  (List.range 5).toArray.mapM fun i => do
    let site ← site? index (UInt32.ofNat (i + 2))
    let .actor _ contract := site.kind | none
    some (contract.subtype, contract.subtype.deliveryOccurrence)

private def actorSubtypesKeepDeliverySeparate : Bool :=
    actorSummary == some #[(.send, some .pub), (.ask, some .pub), (.spawn, some .pub),
      (.serialize, none), (.deserialize, none)]

private def subtypeConflationRefused : Bool := Id.run do
  let some source := bindingIndex? actorProgram.base | return false
  let some index := extract? actorProgram | return false
  let some site := site? index 2 | return false
  let .actor position contract := site.kind | return false
  let mutant := { site with kind := .actor position { contract with subtype := .serialize } }
  return !indexChecks actorProgram source { index with sites := index.sites.set! 1 (some mutant) }

private def subtypeConflationAndMissingActorRefused : Bool :=
    subtypeConflationRefused && (extract? { actorProgram with actorBindings := #[] }).isNone

private def twoReturns : Program :=
  ⟨9, ⟨#[function, node .semValue 2 1 1 4 0 0 0 .secret,
    node .semInstruction 3 1 1 0 1 28, node .semOperand 4 3 0 1,
    node .semInstruction 5 1 2 0 1 28, node .semOperand 6 5 0 1]⟩,
    ByteArray.empty, none, #[], #[], #[root 8]⟩

private def rootSummary : Option (UInt32 × Label × Bool × Bool) := do
  let index ← extract? twoReturns
  let some boundary ← rootBoundary? index 1 .root .returned | none
  let internal ← rootBoundary? index 1 .internalCall .returned
  let left ← site? index 3
  let right ← site? index 5
  some (boundary.declaration.nodeId, boundary.occurrence, internal.isNone,
    left.owner != boundary.declaration.nodeId && right.owner != boundary.declaration.nodeId)

private def rootReturnUsesStableDeclarationSite : Bool :=
    rootSummary == some (8, .pub, true, true)

private def missingAndWrongRootIdentityRefused : Bool :=
    (extract? { twoReturns with roots := #[] }).isNone &&
      (extract? { twoReturns with roots := #[{ root 8 with functionId := 2 }] }).isNone

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError s!"boundary contract fixture: {message}")

#eval show IO Unit from do
  let checks : Array (String × Bool) := #[
    ("zero-payload positive", zeroPayloadHasPublicUnknownContract),
    ("missing/duplicate/owner/name mutants", missingDuplicateWrongOwnerAndChangedNameRefused),
    ("private payload positive", privatePayloadCannotSupplyPrivatePolicy),
    ("private-policy/ABI mutants", privatePolicyLaunderingAndWrongAbiRefused),
    ("all actor subtype positives", actorSubtypesKeepDeliverySeparate),
    ("subtype/missing actor mutants", subtypeConflationAndMissingActorRefused),
    ("stable root/internal return positive", rootReturnUsesStableDeclarationSite),
    ("missing/wrong root mutants", missingAndWrongRootIdentityRefused)]
  for (name, passes) in checks do require passes name

private def parseHex (text : String) : Option ByteArray := do
  let digits := text.toList.filter (fun char => !char.isWhitespace)
  if digits.length % 2 != 0 then none
  let mut bytes := ByteArray.empty
  let mut high : Option Nat := none
  for char in digits do
    let value ← if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
      else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10) else none
    match high with
    | none => high := some value
    | some first =>
        bytes := bytes.push (UInt8.ofNat (first * 16 + value))
        high := none
  if high.isSome then none else some bytes

private def sourceCases : Array (String × String × Nat × Nat) := #[
  ("send", include_str ".." / "fixtures" / "csir-v9" / "accept-loop-header-send.hex", 18, 4),
  ("pure", include_str ".." / "fixtures" / "csir-v9" / "accept-loop-header-pure.hex", 12, 2),
  ("declared", include_str ".." / "fixtures" / "csir-v9" / "accept-declared-ffi.hex", 2, 1),
  ("legacy", include_str ".." / "fixtures" / "csir-v9" / "accept-legacy-unknown-ffi.hex", 2, 1),
  ("actors", include_str ".." / "fixtures" / "csir-v9" / "accept-actor-identities.hex", 14, 4),
  ("empty", include_str ".." / "fixtures" / "csir-v9" / "accept-empty-framing.hex", 0, 0),
  ("empty-profile", include_str ".." / "fixtures" / "csir-v9" / "accept-empty-explicit-profile.hex", 0, 0)]

#eval show IO Unit from do
  for (name, hex, sites, roots) in sourceCases do
    let some bytes := parseHex hex | throw (IO.userError s!"bad source fixture hex: {name}")
    let some program := decode bytes | throw (IO.userError s!"source fixture did not decode: {name}")
    let some index := extract? program | throw (IO.userError s!"source fixture did not extract: {name}")
    require ((index.sites.filterMap id).size == sites && index.roots.size == roots)
      s!"{name}: exact instruction/root census"
    require (index.roots == program.roots && index.hostProfile == program.hostProfile)
      s!"{name}: exact declarations"
    for binding in program.ffiBindings do
      let some site := site? index binding.owner | throw (IO.userError s!"missing source FFI: {name}")
      let .ffi _ contract := site.kind | throw (IO.userError s!"source FFI was reclassified: {name}")
      require (contract.binding == binding) s!"{name}: exact source FFI binding and ABI"
      match contract.policy, program.hostProfile with
      | .legacyUnknown, none =>
          require (contract.occurrence == .pub && contract.accesses.isNone &&
            contract.parameters.all (fun value => value.label == .internal) &&
            contract.results.all (fun value => value.label == .internal))
            s!"{name}: legacy Public occurrence/Internal value policy/unknown footprint"
      | .declared operation, some profile =>
          require (profile.operations[binding.profileOperation.toNat - 1]? == some operation &&
            contract.occurrence == operation.occurrence && contract.parameters == operation.params &&
            contract.results == operation.results && contract.accesses == some operation.accesses)
            s!"{name}: exact declared operation, occurrence, labels and footprint"
      | _, _ => throw (IO.userError s!"source FFI profile mode changed: {name}")
    for declaration in index.roots do
      require (rootBoundary? index declaration.functionId .internalCall .returned == some none)
        s!"{name}: internal return must not become root output"
      let actual := rootBoundary? index declaration.functionId .root .returned
      if declaration.role == 0 then
        require actual.isNone s!"{name}: internal function cannot be exposed as a root"
      else
        let some (some boundary) := actual | throw (IO.userError s!"missing root contract: {name}")
        require (boundary.declaration == declaration &&
          boundary.occurrence == declaration.returnOccurrence) s!"{name}: stable root identity/occurrence"
    if name == "send" then
      let some serializer := site? index 88 | throw (IO.userError "missing actual serializer")
      let some delivery := site? index 93 | throw (IO.userError "missing actual send")
      let .actor _ serialization := serializer.kind | throw (IO.userError "serializer lost subtype")
      let .actor _ sending := delivery.kind | throw (IO.userError "send lost subtype")
      require (serialization.subtype == .serialize && serialization.subtype.deliveryOccurrence.isNone &&
        sending.subtype == .send && sending.subtype.deliveryOccurrence == some .pub)
        "actual source serialization/delivery distinction"

end LambdaSigil.Combined.V9.BoundaryContracts.BoundaryWitnesses
