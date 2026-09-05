import LambdaSigil.V9BoundaryContracts
import Mathlib.Data.List.Basic

/-!
# Correspondence of extracted boundary contracts

Theorems here connect the returned indexed entries to the actual program declarations and
operands checked by extraction. They do not prove occurrence safety, host implementation
conformance, genuine invocation contexts, or a Public relational property.
-/

namespace LambdaSigil.Combined.V9.BoundaryContracts

theorem extracted_components {program : Program} {index : Index}
    (h : extract? program = some index) :
    ∃ source, bindingIndex? program.base = some source ∧ indexChecks program source index = true := by
  unfold extract? at h
  simp only [bind, Option.bind_none] at h
  repeat' first
    | cases h
    | (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
    | split at h
  all_goals
    refine ⟨_, by assumption, ?_⟩
    simpa only [Bool.not_eq_true, Bool.not_eq_false'] using ‹¬ (!_)= true›

theorem checked_record {program : Program} {source : BindingIndex} {index : Index}
    (h : indexChecks program source index = true) {position : Nat}
    (hposition : position < program.base.nodes.size) :
    recordMatches program source index position = true := by
  simp only [indexChecks, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.1.2 position (List.mem_range.mpr hposition)

theorem checked_roots_and_profile {program : Program} {source : BindingIndex} {index : Index}
    (h : indexChecks program source index = true) :
    index.roots = program.roots ∧ index.hostProfile = program.hostProfile := by
  simp only [indexChecks, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem extracted_roots_and_profile {program : Program} {index : Index}
    (h : extract? program = some index) :
    index.roots = program.roots ∧ index.hostProfile = program.hostProfile := by
  obtain ⟨_, _, hchecked⟩ := extracted_components h
  exact checked_roots_and_profile hchecked

theorem returned_record_corresponds {program : Program} {index : Index}
    (h : extract? program = some index) {position : Nat} {owner : Node} {site : SiteContract}
    (howner : program.base.nodes[position]? = some owner)
    (hsite : index.sites[position]? = some (some site)) :
    ∃ source, bindingIndex? program.base = some source ∧
      owner.nodeId.toNat = position + 1 ∧ siteMatches program source owner site = true := by
  obtain ⟨source, hsource, hchecked⟩ := extracted_components h
  have hrecord := checked_record hchecked (Array.getElem?_eq_some_iff.mp howner).1
  refine ⟨source, hsource, ?_⟩
  simpa only [recordMatches, howner, hsite, Bool.and_eq_true, beq_iff_eq] using hrecord

theorem site_lookup_has_indexed_entry {index : Index} {owner : UInt32} {site : SiteContract}
    (h : site? index owner = some site) :
    index.sites[owner.toNat - 1]? = some (some site) := by
  unfold site? at h
  simp only [bind, Option.bind_none] at h
  split at h
  · cases h
  · rw [Option.bind_eq_some_iff] at h
    obtain ⟨entry, hentry, h⟩ := h
    simpa only [h] using hentry

theorem returned_site_has_actual_record {program : Program} {index : Index}
    (h : extract? program = some index) {ownerId : UInt32} {site : SiteContract}
    (hsite : site? index ownerId = some site) :
    ∃ source owner, bindingIndex? program.base = some source ∧
      program.base.nodes[ownerId.toNat - 1]? = some owner ∧
      owner.nodeId.toNat = ownerId.toNat - 1 + 1 ∧
      siteMatches program source owner site = true := by
  obtain ⟨source, hsource, hchecked⟩ := extracted_components h
  have hentry := site_lookup_has_indexed_entry hsite
  have hsize : index.sites.size = program.base.nodes.size := by
    simp only [indexChecks, Bool.and_eq_true, beq_iff_eq] at hchecked
    exact hchecked.1.1.1.1
  have hbound : ownerId.toNat - 1 < program.base.nodes.size := by
    rw [← hsize]
    exact (Array.getElem?_eq_some_iff.mp hentry).1
  let owner := program.base.nodes[ownerId.toNat - 1]
  have howner : program.base.nodes[ownerId.toNat - 1]? = some owner :=
    Array.getElem?_eq_some_iff.mpr ⟨hbound, rfl⟩
  obtain ⟨checkedSource, hcheckedSource, hrecord, hmatch⟩ := returned_record_corresponds h howner hentry
  exact ⟨checkedSource, owner, hcheckedSource, howner, hrecord, hmatch⟩

theorem ffi_contract_retains_source_binding {program : Program} {source : BindingIndex}
    {owner : Node} {position : Nat} {contract : FfiContract}
    (h : ffiContract? program source owner position = some contract) :
    program.ffiBindings[position]? = some contract.binding ∧
      contract.binding.owner = owner.nodeId ∧ hostBindingOK program.hostProfile contract.binding = true := by
  unfold ffiContract? at h
  simp only [bind, Option.bind_none] at h
  repeat' first
    | cases h
    | (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
    | split at h
  all_goals
    refine ⟨by assumption, ?_, ?_⟩
    · apply bne_eq_false_iff_eq.mp
      simpa only [Bool.not_eq_true] using ‹¬ (_ != _) = true›
    · simpa only [Bool.not_eq_true, Bool.not_eq_false'] using ‹¬ (!_)= true›

theorem actor_contract_retains_source_subtype {program : Program} {owner : Node}
    {position : Nat} {contract : ActorContract}
    (h : actorContract? program owner position = some contract) :
    program.actorBindings[position]? = some contract.binding ∧
      contract.binding.owner = owner.nodeId ∧
      actorSubtype? contract.binding.subtype = some contract.subtype := by
  unfold actorContract? at h
  simp only [bind, Option.bind_none] at h
  repeat' first
    | cases h
    | (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
    | split at h
  refine ⟨by assumption, ?_, by assumption⟩
  apply bne_eq_false_iff_eq.mp
  simpa only [Bool.not_eq_true] using ‹¬ (_ != _) = true›

theorem legacy_occurrence_and_footprint_are_not_payload_derived (binding : FfiBinding) :
    (FfiContract.mk binding .legacyUnknown).occurrence = .pub ∧
      (FfiContract.mk binding .legacyUnknown).accesses = none := by
  exact ⟨rfl, rfl⟩

theorem legacy_value_policy_is_internal (binding : FfiBinding) :
    (FfiContract.mk binding .legacyUnknown).parameters =
        binding.params.map (fun type => ⟨type, .internal⟩) ∧
      (FfiContract.mk binding .legacyUnknown).results =
        binding.results.map (fun type => ⟨type, .internal⟩) := by
  exact ⟨rfl, rfl⟩

theorem declared_occurrence_and_payload_policy_are_separate (binding : FfiBinding)
    (operation : HostProfile.Operation) :
    (FfiContract.mk binding (.declared operation)).occurrence = operation.occurrence ∧
      (FfiContract.mk binding (.declared operation)).parameters = operation.params ∧
      (FfiContract.mk binding (.declared operation)).results = operation.results := by
  exact ⟨rfl, rfl, rfl⟩

theorem actor_deliveries_are_public_and_codecs_are_not_deliveries :
    ActorSubtype.send.deliveryOccurrence = some .pub ∧
      ActorSubtype.ask.deliveryOccurrence = some .pub ∧
      ActorSubtype.spawn.deliveryOccurrence = some .pub ∧
      ActorSubtype.serialize.deliveryOccurrence = none ∧
      ActorSubtype.deserialize.deliveryOccurrence = none := by decide +kernel

theorem internal_call_has_no_root_boundary {index : Index} {functionId : UInt32}
    {root : FunctionRootContract} (hzero : functionId ≠ 0)
    (hroot : index.roots[functionId.toNat - 1]? = some root)
    (hidentity : root.functionId = functionId) (phase : RootPhase) :
    rootBoundary? index functionId .internalCall phase = some none := by
  simp [rootBoundary?, hzero, hroot, hidentity]
  rfl

theorem root_boundary_retains_exact_declaration {index : Index} {functionId : UInt32}
    {context : InvocationContext} {phase : RootPhase} {boundary : RootBoundary}
    (h : rootBoundary? index functionId context phase = some (some boundary)) :
    index.roots[functionId.toNat - 1]? = some boundary.declaration ∧
      boundary.phase = phase ∧ boundary.occurrence =
        (match phase with | .entry => boundary.declaration.entryOccurrence
                          | .returned => boundary.declaration.returnOccurrence) := by
  cases context <;> cases phase
  all_goals
    unfold rootBoundary? at h
    simp only [bind, Option.bind_none] at h
    repeat' first
      | cases h
      | (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
      | split at h
  all_goals exact ⟨by assumption, rfl, rfl⟩

end LambdaSigil.Combined.V9.BoundaryContracts
