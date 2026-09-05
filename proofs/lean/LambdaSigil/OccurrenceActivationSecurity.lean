import LambdaSigil.OccurrenceActivation
import Mathlib.Data.List.Basic

/-!
# Exact sparse activation restoration

These theorems concern decoded ownership, snapshots, and call-frame construction only. They do
not prove the v9 instruction machine preserves an activation invariant or any relational output
theorem. In particular, arbitrary initial frame payloads still need a genuine execution-history
invariant before a whole-machine proof may treat them as prior caller state.
-/

namespace LambdaSigil.Combined.OccurrenceActivationSecurity

open Semantic OccurrenceActivation

@[simp] theorem write_scalar_size (store : Store) (cell : Nat) (value : CellValue) :
    (store.write cell value).scalars.size = store.scalars.size := by simp [Store.write]

@[simp] theorem write_aggregate_size (store : Store) (cell : Nat) (value : CellValue) :
    (store.write cell value).aggregates.size = store.aggregates.size := by simp [Store.write]

@[simp] theorem restore_scalar_size (store : Store) (saved : Snapshot) :
    (restore store saved).scalars.size = store.scalars.size := by
  induction saved generalizing store with
  | nil => rfl
  | cons pair rest ih => simpa only [restore, write_scalar_size] using ih (store.write pair.1 pair.2)

@[simp] theorem restore_aggregate_size (store : Store) (saved : Snapshot) :
    (restore store saved).aggregates.size = store.aggregates.size := by
  induction saved generalizing store with
  | nil => rfl
  | cons pair rest ih =>
    simpa only [restore, write_aggregate_size] using ih (store.write pair.1 pair.2)

theorem read_write_same {store : Store} {cell : Nat} (hs : cell < store.scalars.size)
    (ha : cell < store.aggregates.size) (value : CellValue) :
    (store.write cell value).read cell = value := by
  cases value
  simp [Store.read, Store.write, Array.getD, hs, ha]

theorem read_write_other (store : Store) {cell written : Nat} (hne : cell ≠ written)
    (value : CellValue) : (store.write written value).read cell = store.read cell := by
  by_cases hs : cell < store.scalars.size <;>
    by_cases ha : cell < store.aggregates.size <;>
      simp [Store.read, Store.write, Array.getD, hs, ha, Ne.symm hne]

/-- Every key is saved exactly once per occurrence in the supplied list, with both its scalar
    payload and aggregate slot. No parameter-only approximation occurs here. -/
theorem snapshot_keys (store : Store) (cells : List Nat) :
    (snapshot store cells).map Prod.fst = cells := by
  simp [snapshot, List.map_map, Function.comp_def]

/-- Exact lookup characterization also handles duplicate keys: every copy contains the same
    prior cell value. Cells outside the activation keep the callee's current store unchanged. -/
theorem restore_snapshot_lookup (before current : Store) (cells : List Nat) {cell : Nat}
    (hs : cell < current.scalars.size) (ha : cell < current.aggregates.size) :
    (restore current (snapshot before cells)).read cell =
      if cell ∈ cells then before.read cell else current.read cell := by
  induction cells generalizing current with
  | nil => simp [snapshot, restore]
  | cons head rest ih =>
    simp only [snapshot, List.map_cons, restore]
    change (restore (current.write head (before.read head)) (snapshot before rest)).read cell = _
    rw [ih (current.write head (before.read head)) (by simpa using hs) (by simpa using ha)]
    by_cases hrest : cell ∈ rest
    · simp [hrest]
    · by_cases heq : cell = head
      · subst head
        simp [hrest, read_write_same hs ha]
      · simp [hrest, heq, read_write_other current heq]

theorem restores_every_owned_cell (before current : Store) {cells : List Nat} {cell : Nat}
    (hs : cell < current.scalars.size) (ha : cell < current.aggregates.size)
    (howned : cell ∈ cells) :
    (restore current (snapshot before cells)).read cell = before.read cell := by
  simp [restore_snapshot_lookup before current cells hs ha, howned]

theorem preserves_every_disjoint_cell (before current : Store) {cells : List Nat} {cell : Nat}
    (hs : cell < current.scalars.size) (ha : cell < current.aggregates.size)
    (hdisjoint : cell ∉ cells) :
    (restore current (snapshot before cells)).read cell = current.read cell := by
  simp [restore_snapshot_lookup before current cells hs ha, hdisjoint]

theorem recursive_snapshots_restore_outer_activation (outer middle current : Store)
    {cells : List Nat} {cell : Nat} (hs : cell < current.scalars.size)
    (ha : cell < current.aggregates.size) (howned : cell ∈ cells) :
    (restore (restore current (snapshot middle cells)) (snapshot outer cells)).read cell =
      outer.read cell := by
  apply restores_every_owned_cell
  · simpa using hs
  · simpa using ha
  · exact howned

private theorem addOwned_size (table : Array (List Nat)) (node : Node) :
    (addOwned table node).size = table.size := by
  unfold addOwned
  split <;> simp

private theorem owned_fold_lookup (nodes : List Node) (table : Array (List Nat))
    (function : UInt32) (hbound : function.toNat < table.size) :
    (nodes.foldl addOwned table).getD function.toNat [] =
      ((nodes.filterMap (fun node =>
        if node.op = .semValue ∧ node.origin = function then some node.nodeId.toNat else none)).reverse
        ++ table.getD function.toNat []) := by
  induction nodes generalizing table with
  | nil => simp
  | cons node nodes ih =>
    rw [List.foldl_cons, ih _ (by simpa [addOwned_size] using hbound)]
    by_cases hop : node.op = .semValue
    · by_cases howner : node.origin = function
      · simp [addOwned, hop, howner, Array.getD, hbound, List.append_assoc]
      · have hne : node.origin.toNat ≠ function.toNat := by
          intro heq
          exact howner (UInt32.toNat_inj.mp heq)
        simp [addOwned, hop, howner, Array.getD, hbound, hne]
    · simp [addOwned, hop]

/-- The shared executable index contains exactly every decoded semValue declaration belonging
    to the function, including parameters, captures, and nonparameter temporaries. -/
theorem built_index_has_exact_declared_cells (source : Combined.Program) (functionCount : Nat)
    (function : UInt32) (hbound : function.toNat < functionCount + 1) :
    (buildOwned source functionCount).getD function.toNat [] =
      (declaredCells source function).reverse := by
  unfold buildOwned
  rw [owned_fold_lookup _ _ _ (by simpa using hbound)]
  simp [declaredCells, Array.getD, hbound]

theorem prepared_index_has_exact_declared_cells {p : SemanticProgram} (prepared : Prepared p)
    (function : UInt32) (hbound : function.toNat < p.functions.size + 1) :
    prepared.index.byFunction.getD function.toNat [] = (declaredCells p.source function).reverse := by
  have h := prepared.checked
  unfold ownershipIndex? at h
  split at h
  · have hi := Option.some.inj h
    rw [← hi]
    exact built_index_has_exact_declared_cells _ _ _ hbound
  · cases h

theorem built_index_has_one_slot_per_function (source : Combined.Program) (functionCount : Nat) :
    (buildOwned source functionCount).size = functionCount + 1 := by
  unfold buildOwned
  apply List.foldlRecOn (motive := fun table : Array (List Nat) => table.size = functionCount + 1)
  · simp
  · intro table htable node _
    simpa only [addOwned_size] using htable

theorem frame_snapshot_has_all_declared_cells {p : SemanticProgram} (prepared : Prepared p)
    (state : State) (call : Instruction) (callee : Function)
    (hbound : callee.id.toNat < p.functions.size + 1) :
    (makeFrame state call callee (prepared.index.byFunction.getD callee.id.toNat [])).saved.map Prod.fst =
      (declaredCells p.source callee.id).reverse := by
  simp only [makeFrame, snapshot_keys]
  exact prepared_index_has_exact_declared_cells prepared callee.id hbound

theorem restoreFrame_preserves_shared_state (state : State) (frame : Frame) :
    (restoreFrame state frame).shared = state.shared := rfl

theorem entry_preserves_shared_state (state : State) (frame : Frame)
    (parameters : List Nat) (arguments : List CellValue) :
    (enterResolved state frame parameters arguments).shared = state.shared := rfl

theorem return_preserves_shared_state (state : State) (frame : Frame) (rest : List Frame)
    (result : CellValue) : (finish state frame rest result).shared = state.shared := rfl

/-- In particular, a callee's actor writes and consumed external inputs are retained on return;
    only activation-local memory is restored. -/
theorem return_preserves_actor_and_external_effects (state : State) (frame : Frame)
    (rest : List Frame) (result : CellValue) :
    (finish state frame rest result).shared.actorState = state.shared.actorState ∧
      (finish state frame rest result).shared.externalInputs = state.shared.externalInputs ∧
      (finish state frame rest result).shared.externalCursors = state.shared.externalCursors ∧
      (finish state frame rest result).shared.capabilityBalances = state.shared.capabilityBalances :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Correct even when the caller destination aliases a callee-local saved cell in recursion.
    Both the scalar result and its abstract aggregate are written after restoration. -/
theorem return_destination_wins_over_saved_cell (state : State) (frame : Frame)
    (rest : List Frame) (result : CellValue) (hne : frame.destination ≠ 0)
    (hs : frame.destination.toNat < state.store.scalars.size)
    (ha : frame.destination.toNat < state.store.aggregates.size) :
    (finish state frame rest result).store.read frame.destination.toNat = result := by
  simp only [finish, restoreFrame, beq_iff_eq, hne, ↓reduceIte]
  apply read_write_same
  · simpa using hs
  · simpa using ha

theorem return_restores_owned_nondestination (before : Store) (state : State) (frame : Frame)
    (rest : List Frame) (result : CellValue) (cells : List Nat)
    (hsaved : frame.saved = snapshot before cells) {cell : Nat}
    (hs : cell < state.store.scalars.size) (ha : cell < state.store.aggregates.size)
    (howned : cell ∈ cells) (hne : cell ≠ frame.destination.toNat) :
    (finish state frame rest result).store.read cell = before.read cell := by
  unfold finish restoreFrame
  dsimp only
  split
  · simpa [hsaved] using restores_every_owned_cell before state.store hs ha howned
  · rw [read_write_other _ hne]
    simpa [hsaved] using restores_every_owned_cell before state.store hs ha howned

/-- A successful entry constructs its frame from the actual decoded call, its dynamically
    resolved callee, the immutable declaration index, and the pre-call store. This is a unary
    creation fact, not an assumption that an arbitrary supplied frame has a valid history. -/
theorem entered_frame_has_exact_provenance {p : SemanticProgram} (prepared : Prepared p)
    {before after : State} (h : enterPrepared? p prepared before = some after) :
    ∃ call callee,
      p.instructions[before.pc]? = some call ∧
      call.functionId = before.activeFunction ∧
      resolvedCallee? p before call = some callee ∧
      let cells := prepared.index.byFunction.getD callee.id.toNat []
      let frame := makeFrame before call callee cells
      frameCoherentB p frame = true ∧
      after = enterResolved before frame (callee.parameterCells.toList.map UInt32.toNat)
        ((argumentCells p call).map before.store.read) ∧
      frame.saved = snapshot before.store cells := by
  unfold enterPrepared? at h
  simp only [bind, Option.bind_none] at h
  split at h
  · cases h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨call, hcall, h⟩ := h
    split at h
    · cases h
    · rename_i hcaller
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨callee, hcallee, entry, hentry, h⟩ := h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i hcoherent
            simp only [Option.some.injEq] at h
            refine ⟨call, callee, hcall, ?_, hcallee, ?_, h.symm, rfl⟩
            · simp only [Bool.or_eq_true, Bool.not_eq_true, bne_iff_ne, not_or,
                not_not] at hcaller
              exact hcaller.1
            · simpa only [Bool.not_eq_true, Bool.not_eq_false'] using hcoherent

theorem successful_entry_keeps_actor_and_external_state {p : SemanticProgram}
    (prepared : Prepared p) {before after : State}
    (h : enterPrepared? p prepared before = some after) : after.shared = before.shared := by
  obtain ⟨call, callee, _, _, _, _, hafter, _⟩ := entered_frame_has_exact_provenance prepared h
  rw [hafter]
  rfl

theorem returned_frame_checks_complete_snapshot_keys {p : SemanticProgram} (prepared : Prepared p)
    {before after : State} (h : returnPrepared? p prepared before = some after) :
    ∃ frame rest result,
      before.frames = frame :: rest ∧ before.activeFunction = frame.callee ∧
      frameCoherentB p frame = true ∧
      frame.saved.map Prod.fst = prepared.index.byFunction.getD frame.callee.toNat [] ∧
      after = finish before frame rest result := by
  unfold returnPrepared? at h
  simp only [bind, Option.bind_none] at h
  split at h
  · cases h
  · split at h
    · rename_i frame rest hframes
      split at h
      · cases h
      · rename_i hframe
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨output, _, h⟩ := h
        split at h
        · cases h
        ·
          simp only [Bool.or_eq_true, bne_iff_ne, Bool.not_eq_true, not_or, not_not,
            Bool.not_eq_false'] at hframe
          have complete : ∀ result, some (finish before frame rest result) = some after →
              ∃ frame rest result,
                before.frames = frame :: rest ∧ before.activeFunction = frame.callee ∧
                frameCoherentB p frame = true ∧
                frame.saved.map Prod.fst = prepared.index.byFunction.getD frame.callee.toNat [] ∧
                after = finish before frame rest result := by
            intro result hfinish
            exact ⟨frame, rest, result, hframes, hframe.1.1, hframe.1.2,
              hframe.2, (Option.some.inj hfinish).symm⟩
          split at h
          · split at h
            · exact complete _ h
            · cases h
          · split at h
            · exact complete _ h
            · cases h
    · cases h

theorem successful_return_keeps_actor_and_external_state {p : SemanticProgram}
    (prepared : Prepared p) {before after : State}
    (h : returnPrepared? p prepared before = some after) : after.shared = before.shared := by
  obtain ⟨frame, rest, result, _, _, _, _, hafter⟩ :=
    returned_frame_checks_complete_snapshot_keys prepared h
  rw [hafter]
  rfl

end LambdaSigil.Combined.OccurrenceActivationSecurity
