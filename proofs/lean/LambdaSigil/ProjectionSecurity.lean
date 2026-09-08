import LambdaSigil.ProjectionKernel
import Mathlib.Data.List.Basic

/-!
Machine-checked transfer preservation for the production APC-1 validator.

The relation below is over actual decoded phi records, not an assumed security judgment.
The arbitrary-length path result includes cyclic graphs. It establishes preservation of the
extracted transfers; it does not prove that Rust enumerates every source-language dependency,
that AIR marks unreachable paths correctly, or that the native/Wasm backends preserve semantics.
-/

namespace LambdaSigil.Combined.Projection

/-- An independently stated dependency in the decoded CSIR operand stream. -/
def PhiEdge (program : Combined.Program) (functionId source target : UInt32) : Prop :=
  ∃ instruction ∈ program.nodes, ∃ operand ∈ program.nodes,
    instruction.op = .semInstruction ∧ instruction.aux = 2 ∧
    instruction.origin = functionId ∧ instruction.required = target ∧
    operand.op = .semOperand ∧ operand.flags = 0 ∧
    operand.origin = instruction.nodeId ∧ operand.required = source ∧
    operand.actual.toNat < instruction.ceiling.toNat ∧
    operand.nodeId.toNat = instruction.nodeId.toNat + 1 + operand.actual.toNat

def RequiredEdge (transfers : Array Transfer) (functionId source target : UInt32) : Prop :=
  ∃ transfer ∈ transfers, transfer.functionId = functionId ∧
    transfer.source = source ∧ transfer.target = target

inductive Path (edge : UInt32 → UInt32 → Prop) : UInt32 → UInt32 → Prop where
  | refl (value) : Path edge value value
  | step {source middle target} : edge source middle → Path edge middle target →
      Path edge source target

theorem transfer_sound {program : Combined.Program} {transfer : Transfer}
    (h : transferOK program transfer = true) :
    PhiEdge program transfer.functionId transfer.source transfer.target := by
  unfold transferOK at h
  cases hi : program.nodes[transfer.instruction.toNat - 1]? with
  | none => simp [hi] at h
  | some instruction =>
    cases ho : program.nodes[transfer.operand.toNat - 1]? with
    | none => simp [hi, ho] at h
    | some operand =>
      simp only [hi, ho, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
        decide_eq_true_eq, and_assoc] at h
      rcases h with ⟨_, _, _, _, _, hop, haux, hfunction, htarget, hid,
        hoOp, hflags, horigin, hsource, hoid, hbound, hposition⟩
      have hop' : instruction.op = .semInstruction := by
        revert hop
        generalize instruction.op = op
        intro h
        cases op <;> first | rfl | cases h
      have hoOp' : operand.op = .semOperand := by
        revert hoOp
        generalize operand.op = op
        intro h
        cases op <;> first | rfl | cases h
      refine ⟨instruction, Array.mem_of_getElem? hi, operand, Array.mem_of_getElem? ho,
        hop', haux, hfunction, htarget, hoOp', hflags, ?_, hsource, hbound, ?_⟩
      · simpa [hid] using horigin
      · simpa [hid, hoid] using hposition

theorem checked_edges_preserved {program : Combined.Program} {transfers : Array Transfer}
    (h : check program transfers = true) {functionId source target : UInt32}
    (edge : RequiredEdge transfers functionId source target) :
    PhiEdge program functionId source target := by
  obtain ⟨transfer, hm, rfl, rfl, rfl⟩ := edge
  exact transfer_sound ((Array.all_eq_true_iff_forall_mem.mp h) transfer hm)

theorem checked_paths_preserved {program : Combined.Program} {transfers : Array Transfer}
    (h : check program transfers = true) {functionId source target : UInt32}
    (path : Path (RequiredEdge transfers functionId) source target) :
    Path (PhiEdge program functionId) source target := by
  induction path with
  | refl value => exact .refl value
  | step edge _ ih => exact .step (checked_edges_preserved h edge) ih

/-- Any label assignment closed under actual phi dependencies also preserves every extracted
    transfer path. This is a conditional composition result, not an assumed Public/CT theorem. -/
theorem checked_path_rank_monotone {program : Combined.Program} {transfers : Array Transfer}
    (h : check program transfers = true) (functionId : UInt32) (rank : UInt32 → Nat)
    (closed : ∀ a b, PhiEdge program functionId a b → rank a ≤ rank b)
    {source target : UInt32} (path : Path (RequiredEdge transfers functionId) source target) :
    rank source ≤ rank target := by
  have preserved := checked_paths_preserved h path
  clear path
  induction preserved with
  | refl value => exact Nat.le_refl _
  | step edge _ ih => exact Nat.le_trans (closed _ _ edge) ih

theorem accepted_bytes_have_checked_transfers {bytes obligations : ByteArray}
    (h : validateBytes bytes obligations = 0) :
    ∃ program transfers, V9.decode bytes = some program ∧
      decodeTransfers obligations = some transfers ∧ check program.base transfers = true := by
  unfold validateBytes at h
  cases hp : V9.decode bytes with
  | none => simp [hp] at h
  | some program =>
    cases ht : decodeTransfers obligations with
    | none => simp [hp, ht] at h
    | some transfers =>
      refine ⟨program, transfers, rfl, rfl, ?_⟩
      by_cases hc : check program.base transfers = true
      · exact hc
      · simp [hp, ht, hc] at h

theorem accepted_bytes_preserve_paths {bytes obligations : ByteArray}
    (h : validateBytes bytes obligations = 0) :
    ∃ program transfers, V9.decode bytes = some program ∧
      decodeTransfers obligations = some transfers ∧
      ∀ functionId source target,
        Path (RequiredEdge transfers functionId) source target →
        Path (PhiEdge program.base functionId) source target := by
  obtain ⟨program, transfers, hp, ht, hc⟩ := accepted_bytes_have_checked_transfers h
  exact ⟨program, transfers, hp, ht, fun _ _ _ path => checked_paths_preserved hc path⟩

end LambdaSigil.Combined.Projection
