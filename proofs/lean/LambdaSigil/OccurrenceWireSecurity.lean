import LambdaSigil.OccurrenceWire
import Mathlib.Data.List.Basic

/-!
# Declaration binding facts and decoder witnesses

The fixtures deliberately need not satisfy the v8 CFG/policy judgment: this is a separate wire
decoder, not security acceptance. Kernel-proved refusal witnesses are paired with executable
positive declaration checks. Those executable checks are not theorems. No theorem here proves
host conformance, source approval of private roots, occurrence safety, full decoder soundness,
or successful compilation. The byte builder is test-only and assigns actual global record IDs.
-/

namespace LambdaSigil.Combined.V9

-- Explicit theorem declarations keep the source inventory and elaborated theorem census aligned.
theorem instReflBEqValueType : ReflBEq HostProfile.ValueType := by
  constructor
  intro value
  cases value <;> rfl

attribute [instance] instReflBEqValueType

theorem instLawfulBEqValueType : LawfulBEq HostProfile.ValueType := by
  constructor
  intro left right h
  cases left <;> cases right <;> first | rfl | cases h

attribute [instance] instLawfulBEqValueType

set_option maxRecDepth 10000 in
theorem decoded_program_retains_version {bytes : ByteArray} {program : Program}
    (h : decode bytes = some program) : program.wireVersion = version := by
  unfold decode at h
  simp only [bind, Option.bind_none] at h
  repeat' first
    | cases h
    | (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
    | split at h
  rfl

theorem valid_declarations_have_decoded_witness (bytes : ByteArray) :
    validateBytes bytes = 0 ↔ ∃ program, decode bytes = some program := by
  unfold validateBytes
  cases decode bytes <;> simp

set_option maxRecDepth 10000 in
theorem decoded_ffi_bindings_checked {bytes : ByteArray} {program : Program}
    (h : decode bytes = some program) :
    program.ffiBindings.all (hostBindingOK program.hostProfile) = true := by
  unfold decode at h
  simp only [bind, Option.bind_none] at h
  repeat' first
    | cases h
    | (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
    | split at h
  simpa only [Bool.not_eq_true, Bool.not_eq_false'] using ‹¬ (!_)= true›

theorem legacy_binding_is_explicitly_unknown (binding : FfiBinding) :
    hostBindingOK none binding = true ↔ binding.profileOperation = 0 := by
  simp [hostBindingOK]

theorem declared_binding_cannot_use_legacy_zero (profile : HostProfile.Profile)
    (binding : FfiBinding) (h : hostBindingOK (some profile) binding = true) :
    binding.profileOperation ≠ 0 := by
  intro hz
  simp [hostBindingOK, hz] at h

theorem declared_binding_retains_exact_identity_and_abi (profile : HostProfile.Profile)
    (binding : FfiBinding) (h : hostBindingOK (some profile) binding = true) :
    ∃ operation, profile.operations[binding.profileOperation.toNat - 1]? = some operation ∧
      operation.moduleName = "ffi" ∧ operation.name = binding.name ∧
      operation.params.map (·.type) = binding.params ∧
      operation.results.map (·.type) = binding.results := by
  have hn := declared_binding_cannot_use_legacy_zero profile binding h
  cases ho : profile.operations[binding.profileOperation.toNat - 1]? with
  | none => simp [hostBindingOK, hn, ho] at h
  | some operation =>
      refine ⟨operation, rfl, ?_⟩
      simpa [hostBindingOK, hn, ho, Bool.and_eq_true, and_assoc] using h

theorem decoded_legacy_binding_is_explicitly_unknown {bytes : ByteArray} {program : Program}
    (hdecode : decode bytes = some program) (hprofile : program.hostProfile = none)
    (binding : FfiBinding) (hbinding : binding ∈ program.ffiBindings) :
    binding.profileOperation = 0 := by
  have hchecked := decoded_ffi_bindings_checked hdecode
  rw [Array.all_eq_true_iff_forall_mem] at hchecked
  apply (legacy_binding_is_explicitly_unknown binding).mp
  simpa only [hprofile] using hchecked binding hbinding

theorem decoded_declared_binding_retains_exact_identity_and_abi
    {bytes : ByteArray} {program : Program} (hdecode : decode bytes = some program)
    (profile : HostProfile.Profile) (hprofile : program.hostProfile = some profile)
    (binding : FfiBinding) (hbinding : binding ∈ program.ffiBindings) :
    binding.profileOperation ≠ 0 ∧
      ∃ operation, profile.operations[binding.profileOperation.toNat - 1]? = some operation ∧
        operation.moduleName = "ffi" ∧ operation.name = binding.name ∧
        operation.params.map (·.type) = binding.params ∧
        operation.results.map (·.type) = binding.results := by
  have hchecked := decoded_ffi_bindings_checked hdecode
  rw [Array.all_eq_true_iff_forall_mem] at hchecked
  have hexact : hostBindingOK (some profile) binding = true := by
    simpa only [hprofile] using hchecked binding hbinding
  exact ⟨declared_binding_cannot_use_legacy_zero profile binding hexact,
    declared_binding_retains_exact_identity_and_abi profile binding hexact⟩

namespace WireWitnesses

private structure FixtureRecord where
  tag : UInt8
  fields : Array UInt32
  flags : UInt8 := 0
  labelA : UInt8 := 0
  labelB : UInt8 := 0
  deriving Inhabited

private def fixtureWord (bytes : List UInt8) (word : UInt32) : List UInt8 :=
  bytes ++ (List.range 4).map fun shift => UInt8.ofNat ((word.toNat / 2 ^ (8 * shift)) % 256)

private def fixtureName (bytes : List UInt8) (name : String) : List UInt8 :=
  fixtureWord bytes (UInt32.ofNat name.utf8ByteSize) ++ name.toUTF8.data.toList

/-- Fixture bytes are assembled as a list and wrapped once. `ByteArray.append` and `push` are
    `copySlice` copies, which the kernel evaluates as indexed walks over the growing array: one
    400-byte fixture cost 0.6 GB under `decide +kernel` (measured 2026-09-05). -/
private def fixtureWire (wireVersion : UInt32) (records : Array FixtureRecord) : ByteArray :=
  Id.run do
    -- `CSIR`, the bytes of `"CSIR".toUTF8`.
    let mut bytes := fixtureWord (fixtureWord [0x43, 0x53, 0x49, 0x52] wireVersion)
      (UInt32.ofNat records.size)
    for i in [0:records.size] do
      let record := records[i]!
      bytes := bytes ++ [record.tag, record.labelA, record.labelB, record.flags]
      for word in record.fields do bytes := fixtureWord bytes word
      bytes := fixtureWord (fixtureWord bytes (UInt32.ofNat (i + 1))) 0
    return ⟨⟨bytes⟩⟩

private def fixtureChunks (bytes : ByteArray) : Array FixtureRecord := Id.run do
  let mut records := #[]
  for chunk in [0:(bytes.size + 19) / 20] do
    let fields := (List.range 5).toArray.map fun word =>
      UInt32.ofNat ((List.range 4).foldl (fun value byte =>
        value + (bytes.data.getD (20 * chunk + 4 * word + byte) 0).toNat * 2 ^ (8 * byte)) 0)
    records := records.push ⟨45, fields, 0, 0, 0⟩
  return records

private def functionRecord : FixtureRecord := ⟨34, #[1, 1, 0, 0, 0], 1, 0, 0⟩
private def rootRecord : FixtureRecord := ⟨48, #[1, 0, 0, 3, 0], 2, 0, 0⟩
private def manifestRecord (base profile ffi actors roots : Nat) : FixtureRecord :=
  ⟨44, #[base, profile, ffi, actors, roots].map UInt32.ofNat, 0, 0, 0⟩

private def tinyRecords : Array FixtureRecord :=
  #[functionRecord, manifestRecord 1 0 0 0 1, rootRecord] ++ fixtureChunks "run".toUTF8

private def tinyWire : ByteArray := fixtureWire 9 tinyRecords

private def decodedEnvelopeRetainsVersionAndRootIdentity : Bool :=
    (decode tinyWire).map (fun program =>
      (program.wireVersion, program.base.nodes.size,
        program.roots.map (fun root => (root.nodeId, root.functionId, root.exportName)))) ==
      some (9, 1, #[(3, 1, "run")])

set_option maxRecDepth 100000 in
theorem versions_do_not_silently_cross_decode :
    Combined.decode tinyWire = none ∧
      decode (fixtureWire 8 tinyRecords) = none := by decide +kernel

private def ffiBase (functionId : UInt32 := 1) : Array FixtureRecord :=
  #[functionRecord,
    ⟨37, #[functionId, 1, 0, 3, 15], 1, 0, 0⟩,
    ⟨38, #[2, 0, 3, 0, 0], 3, 0, 0⟩,
    ⟨38, #[2, 1, 4, 0, 0], 3, 0, 0⟩,
    ⟨38, #[2, 2, 0x6b636974, 0, 0], 3, 0, 0⟩]

private def ffiRecords (profile : ByteArray := ByteArray.empty) (operation : UInt32 := 0)
    (functionId : UInt32 := 1) : Array FixtureRecord :=
  ffiBase functionId ++ #[manifestRecord 5 profile.size 1 0 1] ++ fixtureChunks profile ++
    #[⟨46, #[2, operation, 3, 0, 0], 0, 0, 0⟩, rootRecord] ++ fixtureChunks "run".toUTF8

private def profileBytes (name : String := "tick") (result : Bool := false) : ByteArray :=
  Id.run do
    let mut bytes := fixtureWord HostProfile.magic.data.toList 1
    bytes := fixtureName bytes "provider"
    bytes := fixtureWord (fixtureWord bytes 1) 0
    bytes := fixtureWord (fixtureWord bytes 0) 1
    bytes := fixtureName (fixtureName bytes "ffi") name
    bytes := bytes ++ [0]
    bytes := fixtureWord bytes 0
    bytes := fixtureWord bytes (if result then 1 else 0)
    if result then bytes := bytes ++ [0, 0]
    return ⟨⟨fixtureWord bytes 0⟩⟩

private def zeroArgumentLegacyBindingPreservesExactIdentity : Bool :=
    (decode (fixtureWire 9 (ffiRecords))).map (fun program =>
      (program.hostProfile.isNone,
        program.ffiBindings.map (fun binding =>
          (binding.profileOperation, binding.name, binding.params.size, binding.results.size)))) ==
      some (true, #[(0, "tick", 0, 0)])

private def canonicalProfileBytesAndOperationBindingSurvive : Bool :=
    (decode (fixtureWire 9 (ffiRecords profileBytes 1))).map (fun program =>
      (program.hostProfileBytes, program.ffiBindings.map (·.profileOperation))) ==
      some (profileBytes, #[1])

set_option maxRecDepth 100000 in
private theorem profile_mode_identity_and_signature_mutants_are_refused_operation_without_profile :
    decode (fixtureWire 9 (ffiRecords ByteArray.empty 1)) = none := by decide +kernel

set_option maxRecDepth 100000 in
private theorem profile_mode_identity_and_signature_mutants_are_refused_profile_without_operation :
    decode (fixtureWire 9 (ffiRecords profileBytes 0)) = none := by decide +kernel

set_option maxRecDepth 100000 in
private theorem profile_mode_identity_and_signature_mutants_are_refused_wrong_identity :
    decode (fixtureWire 9 (ffiRecords (profileBytes "tock") 1)) = none := by decide +kernel

set_option maxRecDepth 100000 in
private theorem profile_mode_identity_and_signature_mutants_are_refused_wrong_signature :
    decode (fixtureWire 9 (ffiRecords (profileBytes "tick" true) 1)) = none := by decide +kernel

/-- One kernel decision per conjunct: the kernel's caches accumulate across a conjunction,
    so deciding the parts as separate declarations divides the peak (measured 2026-09-05). -/
theorem profile_mode_identity_and_signature_mutants_are_refused :
    decode (fixtureWire 9 (ffiRecords ByteArray.empty 1)) = none ∧
      decode (fixtureWire 9 (ffiRecords profileBytes 0)) = none ∧
      decode (fixtureWire 9 (ffiRecords (profileBytes "tock") 1)) = none ∧
      decode (fixtureWire 9 (ffiRecords (profileBytes "tick" true) 1)) = none :=
  ⟨profile_mode_identity_and_signature_mutants_are_refused_operation_without_profile, profile_mode_identity_and_signature_mutants_are_refused_profile_without_operation, profile_mode_identity_and_signature_mutants_are_refused_wrong_identity, profile_mode_identity_and_signature_mutants_are_refused_wrong_signature⟩

set_option maxRecDepth 100000 in
theorem zero_argument_orphan_cannot_hide_missing_function_ownership :
    decode (fixtureWire 9 (ffiRecords ByteArray.empty 0 0)) = none := by decide +kernel

set_option maxRecDepth 100000 in
private theorem missing_binding_and_changed_operand_owner_are_refused_missing_binding :
    decode (fixtureWire 9 ((ffiRecords).set! 5 (manifestRecord 5 0 0 0 1))) = none := by decide +kernel

set_option maxRecDepth 100000 in
private theorem missing_binding_and_changed_operand_owner_are_refused_changed_operand_owner :
    decode (fixtureWire 9 ((ffiRecords).set! 4
        ⟨38, #[3, 2, 0x6b636974, 0, 0], 3, 0, 0⟩)) = none := by decide +kernel

/-- One kernel decision per conjunct: the kernel's caches accumulate across a conjunction,
    so deciding the parts as separate declarations divides the peak (measured 2026-09-05). -/
theorem missing_binding_and_changed_operand_owner_are_refused :
    decode (fixtureWire 9 ((ffiRecords).set! 5 (manifestRecord 5 0 0 0 1))) = none ∧
      decode (fixtureWire 9 ((ffiRecords).set! 4
        ⟨38, #[3, 2, 0x6b636974, 0, 0], 3, 0, 0⟩)) = none :=
  ⟨missing_binding_and_changed_operand_owner_are_refused_missing_binding, missing_binding_and_changed_operand_owner_are_refused_changed_operand_owner⟩

private def actorRecords : Array FixtureRecord :=
  #[functionRecord] ++
    ((List.range 5).toArray.map fun _ => ⟨37, #[1, 1, 0, 0, 8], 1, 0, 0⟩) ++
    #[manifestRecord 6 0 0 5 1] ++
    ((List.range 5).toArray.map fun index =>
      ⟨47, #[UInt32.ofNat (index + 2), UInt32.ofNat (index + 1), 0, 0, 0], 0, 0, 0⟩) ++
    #[rootRecord] ++ fixtureChunks "run".toUTF8

private def allActorSubtypesAreRetainedWithoutShapeInference : Bool :=
    (decode (fixtureWire 9 actorRecords)).map (fun program =>
      program.actorBindings.map (·.subtype)) == some #[1, 2, 3, 4, 5]

set_option maxRecDepth 100000 in
private theorem unknown_actor_subtype_and_nonzero_root_padding_are_refused_unknown_actor_subtype :
    decode (fixtureWire 9 (actorRecords.set! 7 ⟨47, #[2, 0, 0, 0, 0], 0, 0, 0⟩)) = none := by decide +kernel

set_option maxRecDepth 100000 in
private theorem unknown_actor_subtype_and_nonzero_root_padding_are_refused_nonzero_root_padding :
    decode (fixtureWire 9 (tinyRecords.set! 3 ⟨45, #[0x6e7572, 0, 0, 0, 1], 0, 0, 0⟩)) =
        none := by decide +kernel

/-- One kernel decision per conjunct: the kernel's caches accumulate across a conjunction,
    so deciding the parts as separate declarations divides the peak (measured 2026-09-05). -/
theorem unknown_actor_subtype_and_nonzero_root_padding_are_refused :
    decode (fixtureWire 9 (actorRecords.set! 7 ⟨47, #[2, 0, 0, 0, 0], 0, 0, 0⟩)) = none ∧
      decode (fixtureWire 9 (tinyRecords.set! 3 ⟨45, #[0x6e7572, 0, 0, 0, 1], 0, 0, 0⟩)) =
        none :=
  ⟨unknown_actor_subtype_and_nonzero_root_padding_are_refused_unknown_actor_subtype, unknown_actor_subtype_and_nonzero_root_padding_are_refused_nonzero_root_padding⟩

private def rootOccurrenceIsSeparateFromPayloadAndRejectsCt : Bool :=
    ((decode (fixtureWire 9 (tinyRecords.set! 2
      { rootRecord with labelA := 1, labelB := 2 }))).map fun program =>
        program.roots.map (fun root => (root.entryOccurrence, root.returnOccurrence))) ==
      some #[(.internal, .secret)] &&
      (decode (fixtureWire 9 (tinyRecords.set! 2 { rootRecord with labelA := 3 }))).isNone

-- These execute the actual decoder and fail module elaboration on any disagreement. They
-- complement, but do not masquerade as, the generic theorems and kernel refusal witnesses.
#eval show IO Unit from do
  let checks : Array (String × Bool) := #[
    ("version and root identity", decodedEnvelopeRetainsVersionAndRootIdentity),
    ("zero-argument legacy identity", zeroArgumentLegacyBindingPreservesExactIdentity),
    ("canonical profile and operation", canonicalProfileBytesAndOperationBindingSurvive),
    ("all actor subtypes", allActorSubtypesAreRetainedWithoutShapeInference),
    ("independent root occurrence", rootOccurrenceIsSeparateFromPayloadAndRejectsCt)]
  for (name, accepted) in checks do
    if !accepted then throw (IO.userError s!"v9 declaration witness failed: {name}")

end WireWitnesses

end LambdaSigil.Combined.V9
