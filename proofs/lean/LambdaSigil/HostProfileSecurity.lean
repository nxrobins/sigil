import LambdaSigil.HostProfileKernel
import Mathlib.Data.List.Basic

/-!
# Local security obligations of decoded provider declarations

These are declaration-validation results. They neither assume nor establish conformance of a
native host implementation, occurrence safety of a CSIR program, or the Public relational claim.
The finite checker is characterized against inequalities over the resolved domain footprint.
-/

namespace LambdaSigil.Combined.HostProfile

/-- An algorithm-independent local flow judgment after names have been resolved to domains.
    The result and write obligations are universal, not verdict bits supplied in the profile. -/
def ResolvedOperationJudgment (operation : Operation)
    (accesses : Array (Domain × AccessMode)) : Prop :=
  (influence operation accesses).rank < 3 ∧
    (∀ access ∈ accesses, access.2.writes = true →
      (influence operation accesses).rank ≤ access.1.label.rank) ∧
    ∀ result ∈ operation.results, (influence operation accesses).rank ≤ result.label.rank

private theorem not_ct_iff_rank (label : Label) :
    (label != .secretCT) = true ↔ label.rank < 3 := by
  cases label <;> decide

theorem resolved_flows_sound_and_complete (operation : Operation)
    (accesses : Array (Domain × AccessMode)) :
    resolvedFlowsOK operation accesses = true ↔ ResolvedOperationJudgment operation accesses := by
  simp only [resolvedFlowsOK, ResolvedOperationJudgment, Bool.and_eq_true,
    not_ct_iff_rank, Array.all_eq_true_iff_forall_mem, Bool.or_eq_true,
    Bool.not_eq_true', Label.flowsTo, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hct, hwrites⟩, hresults⟩
    exact ⟨hct, fun access ha hw => (hwrites access ha).resolve_left (by simp [hw]), hresults⟩
  · rintro ⟨hct, hwrites, hresults⟩
    refine ⟨⟨hct, ?_⟩, hresults⟩
    intro access ha
    cases hw : access.2.writes
    · exact Or.inl rfl
    · exact Or.inr (hwrites access ha hw)

private theorem rank_lub (left right : Label) :
    (left.lub right).rank = max left.rank right.rank := by
  cases left <;> cases right <;> decide

private theorem fold_rank_ge_initial {α : Type} (getLabel : α → Label)
    (items : List α) (initial : Label) :
    initial.rank ≤ (items.foldl (fun current item => current.lub (getLabel item)) initial).rank := by
  induction items generalizing initial with
  | nil => exact Nat.le_refl _
  | cons item rest ih =>
      exact Nat.le_trans (by rw [rank_lub]; exact Nat.le_max_left _ _) (ih _)

private theorem member_rank_le_fold {α : Type} (getLabel : α → Label)
    (items : List α) (initial : Label) (item : α) (hitem : item ∈ items) :
    (getLabel item).rank ≤
      (items.foldl (fun current item => current.lub (getLabel item)) initial).rank := by
  induction items generalizing initial with
  | nil => simp at hitem
  | cons head rest ih =>
      simp only [List.mem_cons] at hitem
      rcases hitem with rfl | hitem
      · exact Nat.le_trans (by rw [rank_lub]; exact Nat.le_max_right _ _)
          (fold_rank_ge_initial getLabel rest _)
      · exact ih _ hitem

private def readLabel (access : Domain × AccessMode) : Label :=
  if access.2.reads then access.1.label else .pub

private theorem influence_eq_fold (operation : Operation)
    (accesses : Array (Domain × AccessMode)) :
    influence operation accesses =
      accesses.toList.foldl (fun label access => label.lub (readLabel access))
        (operation.params.toList.foldl (fun label value => label.lub value.label)
          operation.occurrence) := by
  unfold influence
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  congr 1
  funext label access
  unfold readLabel
  cases access.2 <;> cases label <;> rfl

theorem occurrence_rank_le_influence (operation : Operation)
    (accesses : Array (Domain × AccessMode)) :
    operation.occurrence.rank ≤ (influence operation accesses).rank := by
  rw [influence_eq_fold]
  exact Nat.le_trans (fold_rank_ge_initial (·.label) operation.params.toList _)
    (fold_rank_ge_initial readLabel accesses.toList _)

theorem parameter_rank_le_influence (operation : Operation)
    (accesses : Array (Domain × AccessMode)) (parameter : ValueContract)
    (hparameter : parameter ∈ operation.params) :
    parameter.label.rank ≤ (influence operation accesses).rank := by
  rw [influence_eq_fold]
  exact Nat.le_trans (member_rank_le_fold (·.label) operation.params.toList _ parameter
    (by simpa using hparameter)) (fold_rank_ge_initial readLabel accesses.toList _)

theorem read_domain_rank_le_influence (operation : Operation)
    (accesses : Array (Domain × AccessMode)) (access : Domain × AccessMode)
    (haccess : access ∈ accesses) (hread : access.2.reads = true) :
    access.1.label.rank ≤ (influence operation accesses).rank := by
  rw [influence_eq_fold]
  have h := member_rank_le_fold readLabel accesses.toList
    (operation.params.toList.foldl (fun label value => label.lub value.label)
      operation.occurrence) access (by simpa using haccess)
  simpa [readLabel, hread] using h

/-- Even an operation with no result cannot consume a lower-visible shared stream under a
    private occurrence contract: cursor advancement is a domain write. -/
theorem occurrence_cannot_write_lower_domain (operation : Operation)
    (accesses : Array (Domain × AccessMode))
    (hverified : resolvedFlowsOK operation accesses = true)
    (access : Domain × AccessMode) (haccess : access ∈ accesses)
    (hwrite : access.2.writes = true) :
    operation.occurrence.rank ≤ access.1.label.rank :=
  Nat.le_trans (occurrence_rank_le_influence operation accesses)
    (((resolved_flows_sound_and_complete operation accesses).mp hverified).2.1 access haccess hwrite)

theorem verified_parameters_are_not_secretCT (operation : Operation)
    (accesses : Array (Domain × AccessMode))
    (hverified : resolvedFlowsOK operation accesses = true)
    (parameter : ValueContract) (hparameter : parameter ∈ operation.params) :
    parameter.label.rank < 3 :=
  Nat.lt_of_le_of_lt (parameter_rank_le_influence operation accesses parameter hparameter)
    ((resolved_flows_sound_and_complete operation accesses).mp hverified).1

theorem decoded_profile_declarations_checked {bytes : ByteArray} {profile : Profile}
    (hdecode : decode bytes = some profile) : declarationsOK profile = true := by
  unfold decode at hdecode
  simp only [bind] at hdecode
  split at hdecode
  · cases hdecode
  · rw [Option.bind_eq_some_iff] at hdecode
    obtain ⟨⟨parsed, reader⟩, _, hdecode⟩ := hdecode
    split at hdecode
    · cases hdecode
      assumption
    · cases hdecode

theorem decoded_profile_byte_bound {bytes : ByteArray} {profile : Profile}
    (hdecode : decode bytes = some profile) : bytes.size ≤ maxBytes := by
  by_contra hbound
  simp [decode, Nat.lt_of_not_ge hbound] at hdecode

theorem decoded_profile_structural_bounds {bytes : ByteArray} {profile : Profile}
    (hdecode : decode bytes = some profile) :
    profile.itemCount ≤ maxItems ∧ profile.encodedSize ≤ maxBytes := by
  have hchecked := decoded_profile_declarations_checked hdecode
  simp only [declarationsOK, Bool.and_eq_true, decide_eq_true_eq] at hchecked
  exact ⟨hchecked.1.2, hchecked.2⟩

theorem accepted_profile_has_decoded_witness (bytes : ByteArray) :
    validateBytes bytes = 0 ↔ ∃ profile, decode bytes = some profile := by
  unfold validateBytes
  cases decode bytes <;> simp

end LambdaSigil.Combined.HostProfile
