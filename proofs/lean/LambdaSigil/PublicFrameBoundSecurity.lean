import LambdaSigil.PublicRegionSecurity

/-!
# Bound-free call-frame restoration

Call-frame parameter cells are `UInt32`, so assigning arguments can touch only positions below
`2^32`.  The older projection proof reconstructed every natural array position through
`UInt32.ofNat` and therefore required the whole scalar array to fit below that limit.  This file
proves directly that positions outside the `UInt32` range are untouched, removing that proof-only
restriction without changing the executable verifier or its acceptance language.
-/

namespace LambdaSigil.Combined.Semantic.PublicFrameBoundSecurity

open PublicRegionSecurity

private theorem uint32_toNat_lt_size (cell : UInt32) : cell.toNat < 2 ^ 32 := by
  exact cell.toFin.isLt

theorem assignArguments_getElem?_above_uint32 (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) (position : Nat)
    (hposition : 2 ^ 32 ≤ position) :
    (assignArguments p state parameters arguments).values[position]? =
      state.values[position]? := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons parameter parameters ih =>
      cases arguments with
      | nil => rfl
      | cons argument arguments =>
          rw [assignArguments, ih]
          have hne : parameter.toNat ≠ position := by
            intro heq
            have := uint32_toNat_lt_size parameter
            omega
          simp [hne]

theorem restoreValues_getElem?_above_uint32 (state : State)
    (saved : List (UInt32 × Value)) (position : Nat) (hposition : 2 ^ 32 ≤ position) :
    (restoreValues state saved).values[position]? = state.values[position]? := by
  induction saved generalizing state with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨cell, value⟩
      rw [restoreValues, ih]
      have hne : cell.toNat ≠ position := by
        intro heq
        have := uint32_toNat_lt_size cell
        omega
      simp [hne]

/-- Saving caller parameters, assigning callee arguments, and restoring the saved parameters is
    an exact scalar-array identity.  No global bound on the array is needed: positions representable
    by `UInt32` use `readValue_restore_assigned`; all larger positions are structurally untouched. -/
theorem restore_assigned_values_unbounded (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    (restoreValues (assignArguments p state parameters arguments)
      (saveValues state parameters)).values = state.values := by
  let restored := restoreValues (assignArguments p state parameters arguments)
    (saveValues state parameters)
  apply Array.ext
  · simp
  · intro position hl hr
    by_cases hposition : position < 2 ^ 32
    · have hnat : (UInt32.ofNat position).toNat = position := by
        simp [Nat.mod_eq_of_lt hposition]
      have hread := readValue_restore_assigned p state parameters arguments
        (UInt32.ofNat position)
      simpa [restored, readValue, Array.getD, hl, hr, hnat] using hread
    · have habove : 2 ^ 32 ≤ position := by omega
      have hrestore := restoreValues_getElem?_above_uint32
        (assignArguments p state parameters arguments) (saveValues state parameters)
        position habove
      have hassign := assignArguments_getElem?_above_uint32 p state parameters arguments
        position habove
      have hoption := hrestore.trans hassign
      simpa [restored, hl, hr] using hoption

/-- Bound-free replacement for `publicProjection_restore_assigned`. -/
theorem publicProjection_restore_assigned_unbounded (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) :
    publicProjection p
        (restoreValues (assignArguments p state parameters arguments)
          (saveValues state parameters)) =
      publicProjection p state := by
  have hvalues := restore_assigned_values_unbounded p state parameters arguments
  unfold publicProjection
  rw [hvalues]
  simp

/-- Bound-free call-entry counterpart of `callerPublicProjection_entered`. -/
theorem callerPublicProjection_entered_unbounded (p : SemanticProgram) (state : State)
    (instruction : Instruction) (callee : Function) (arguments : List Value) :
    let parameters := callee.parameterCells.toList
    let saved := saveValues state parameters
    let frame : CallFrame :=
      { returnPc := state.pc + 1, destination := instruction.destination,
        calleeId := callee.id, returnLabel := callee.returnLabel,
        savedParameters := saved }
    let entered := assignArguments p state parameters arguments
    let next : State :=
      { entered with
        pc := callee.firstInstruction.toNat
        callStack := frame :: state.callStack }
    callerPublicProjection p next = callerPublicProjection p state := by
  dsimp only
  unfold callerPublicProjection
  simp only [restoreFrameStack]
  let enteredState : State :=
    { assignArguments p state callee.parameterCells.toList arguments with
      pc := callee.firstInstruction.toNat
      callStack :=
        { returnPc := state.pc + 1, destination := instruction.destination,
          calleeId := callee.id, returnLabel := callee.returnLabel,
          savedParameters := saveValues state callee.parameterCells.toList } :: state.callStack }
  let restoredEntered := restoreValues enteredState
    (saveValues state callee.parameterCells.toList)
  have hstorage : ProjectionStorageEqual restoredEntered state := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have henteredValues : enteredState.values =
          (assignArguments p state callee.parameterCells.toList arguments).values := rfl
      exact (restoreValues_values_congr henteredValues
        (saveValues state callee.parameterCells.toList)).trans
          (restore_assigned_values_unbounded p state callee.parameterCells.toList arguments)
    · simp [restoredEntered, enteredState]
    · simp [restoredEntered, enteredState]
    · simp [restoredEntered, enteredState]
    · simp [restoredEntered, enteredState]
  change publicProjection p (restoreFrameStack restoredEntered state.callStack) = _
  exact (hstorage.restoreFrameStack restoredEntered state state.callStack).publicProjection p

end LambdaSigil.Combined.Semantic.PublicFrameBoundSecurity
