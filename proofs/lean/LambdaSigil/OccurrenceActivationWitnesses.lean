import LambdaSigil.OccurrenceActivationSecurity

/-!
# Concrete activation witnesses and restoration mutants

The programs below are decoded from semantic declaration records using the existing decoder.
The witnesses execute the new entry/return storage operations, not a full instruction run or a
production security acceptance test. Intermediate store writes explicitly model local mutations;
no termination, effect policy, or whole-machine relational result is asserted.
-/

namespace LambdaSigil.Combined.OccurrenceActivationWitnesses

open Semantic OccurrenceActivation

private def node (op : Op) (origin actual required ceiling aux : UInt32)
    (flags : UInt8 := 0) : Node :=
  ⟨op, .pub, .pub, flags, origin, actual, required, ceiling, aux, 0⟩

private def records : Array Node := #[
  node .semProgram 0 0 0 0 0,
  node .semFunction 1 1 1 2 0,
  node .semValue 1 1 0 0 0,
  node .semValue 1 2 0 0 0,
  node .semBlock 1 1 0 0 0,
  node .semInstruction 1 1 2 2 6,
  node .semOperand 6 0 2 0 0 2,
  node .semOperand 6 1 1 0 0,
  node .semInstruction 1 1 0 1 28,
  node .semOperand 9 0 2 0 0,
  node .semFunction 2 1 1 3 0,
  node .semValue 2 1 0 0 0,
  node .semValue 2 2 0 0 0,
  node .semValue 2 3 0 0 0,
  node .semLabelContract 2 1 0 0 0,
  node .semBlock 2 1 0 0 0,
  node .semInstruction 2 1 3 2 6,
  node .semOperand 17 0 2 0 0 2,
  node .semOperand 17 1 1 0 0,
  node .semInstruction 2 1 0 1 28,
  node .semOperand 20 0 3 0 0]

private def sourceFrom (records : Array Node) : Combined.Program :=
  ⟨records.mapIdx (fun position record => { record with nodeId := UInt32.ofNat (position + 1) })⟩

private def programFrom (records : Array Node) : SemanticProgram :=
  let source := sourceFrom records
  semanticProgramOf source

private def program : SemanticProgram := programFrom records

private def initialFor (p : SemanticProgram) : State :=
  { pc := 0
    activeFunction := 1
    store :=
      { scalars := ((List.range p.valueLabels.size).map (fun cell => Int.ofNat (cell * 10))).toArray
        aggregates := ((List.range p.valueLabels.size).map
          (fun cell => [Int.ofNat cell, Int.ofNat (cell + 100)])).toArray }
    shared := { actorState := #[0], externalInputs := #[[7, 8]], externalCursors := #[0] } }

private def initial : State := initialFor program

private def entered : State := (enter? program initial).getD initial

private def locallyChanged : State :=
  { entered with
    pc := 3
    store := ((entered.store.write 12 ⟨999, [99]⟩).write 13 ⟨888, [88]⟩).write 14 ⟨777, [77]⟩
    shared := { entered.shared with actorState := #[6], externalCursors := #[1] } }

private def returned : State := (return? program locallyChanged).getD initial

theorem decoded_ownership_covers_parameters_and_temporaries :
    ownershipLayoutB program = true ∧
      (ownershipIndex? program).map (fun index => index.byFunction.getD 2 []) = some [14, 13, 12] ∧
      (program.functions[1]?).map (fun function => function.parameterCells.toList) = some [12] := by
  decide +kernel

theorem direct_entry_copies_scalar_and_aggregate_arguments :
    (enter? program initial).isSome = true ∧ entered.activeFunction = 2 ∧ entered.pc = 2 ∧
      entered.store.read 12 = ⟨30, [3, 103]⟩ ∧
      entered.frames.map (fun frame => frame.saved.map Prod.fst) = [[14, 13, 12]] := by decide +kernel

theorem direct_return_restores_locals_and_retains_shared_effects :
    (return? program locallyChanged).isSome = true ∧
      returned.store.read 12 = initial.store.read 12 ∧
      returned.store.read 13 = initial.store.read 13 ∧
      returned.store.read 14 = initial.store.read 14 ∧
      returned.store.read 4 = ⟨777, [77]⟩ ∧
      returned.shared.actorState = #[6] ∧ returned.shared.externalCursors = #[1] ∧
      returned.pc = 1 ∧ returned.activeFunction = 1 ∧ returned.frames = [] := by decide +kernel

private def recursiveEntry : State := (enter? program entered).getD initial
private def recursiveChanged : State :=
  { recursiveEntry with pc := 3, store := recursiveEntry.store.write 14 ⟨222, [222]⟩ }
private def innerReturn : State := (return? program recursiveChanged).getD initial
private def outerReturn : State := (return? program innerReturn).getD initial

theorem recursive_alias_returns_survive_both_restorations :
    (enter? program entered).isSome = true ∧ recursiveEntry.frames.length = 2 ∧
      (return? program recursiveChanged).isSome = true ∧ innerReturn.frames.length = 1 ∧
      innerReturn.store.read 12 = entered.store.read 12 ∧ innerReturn.store.read 14 = ⟨222, [222]⟩ ∧
      (return? program innerReturn).isSome = true ∧ outerReturn.frames = [] ∧
      outerReturn.store.read 4 = ⟨222, [222]⟩ ∧
      outerReturn.store.read 12 = initial.store.read 12 ∧
      outerReturn.store.read 14 = initial.store.read 14 := by decide +kernel

private def topFrame (state : State) : Frame :=
  state.frames.head?.getD
    ⟨0, 0, 0, 0, 0, 0, 0, .pub, []⟩

private def parameterOnly : Frame :=
  { topFrame locallyChanged with saved := snapshot initial.store [12] }

theorem omitted_nonparameter_snapshot_is_load_bearing :
    (return? program { locallyChanged with frames := [parameterOnly] }).isNone = true ∧
      (finish locallyChanged parameterOnly [] ⟨777, [77]⟩).store.read 13 = ⟨888, [88]⟩ ∧
      returned.store.read 13 = ⟨130, [13, 113]⟩ := by decide +kernel

private def scalarOnlyRestore (store : Store) : Snapshot → Store
  | [] => store
  | (cell, value) :: rest => scalarOnlyRestore
      { store with scalars := store.scalars.setIfInBounds cell value.scalar } rest

theorem omitted_aggregate_restore_is_load_bearing :
    (scalarOnlyRestore locallyChanged.store (topFrame locallyChanged).saved).read 13 = ⟨130, [88]⟩ ∧
      (restore locallyChanged.store (topFrame locallyChanged).saved).read 13 = ⟨130, [13, 113]⟩ := by
  decide +kernel

private def writeBeforeRestore (state : State) (frame : Frame) (result : CellValue) : Store :=
  restore (state.store.write frame.destination.toNat result) frame.saved

theorem wrong_restore_write_order_loses_recursive_result :
    (writeBeforeRestore recursiveChanged (topFrame recursiveChanged) ⟨222, [222]⟩).read 14 =
      ⟨140, [14, 114]⟩ ∧ innerReturn.store.read 14 = ⟨222, [222]⟩ := by decide +kernel

private def wrongParameterOwner : SemanticProgram :=
  { program with functions := (program.functions.modify 1
      (fun function => { function with parameterCells := #[3] })) }

theorem wrong_parameter_owner_and_forged_return_provenance_reject :
    (enter? wrongParameterOwner initial).isNone = true ∧
      (return? program { locallyChanged with frames :=
        [{ topFrame locallyChanged with returnPc := 2 }] }).isNone = true ∧
      (return? program { locallyChanged with frames :=
        [{ topFrame locallyChanged with destination := 13 }] }).isNone = true ∧
      (return? program { locallyChanged with frames :=
        [{ topFrame locallyChanged with callee := 1 }] }).isNone = true := by decide +kernel

private def closureProgram : SemanticProgram :=
  programFrom ((records.modify 5 (fun call => { call with aux := 7 })).modify 6
    (fun selector => { selector with flags := 0, required := 1 }))
private def closureStart : State :=
  let start := initialFor closureProgram
  { start with store := start.store.write 3 ⟨1, [3, 103]⟩ }

theorem actual_semantic_allocation_includes_unchanged_summary_cells :
    program.valueLabels.size = semanticTaintCellCount program.source ∧
      program.valueLabels.size = program.source.nodes.size + 3 ∧
      entered.store.read 22 = initial.store.read 22 ∧ entered.store.read 23 = initial.store.read 23 ∧
      returned.store.read 22 = initial.store.read 22 ∧ returned.store.read 23 = initial.store.read 23 ∧
      closureProgram.valueLabels.size = closureProgram.source.nodes.size + 4 := by decide +kernel

theorem decoded_closure_target_has_same_complete_activation :
    (enter? closureProgram closureStart).isSome = true ∧
      ((enter? closureProgram closureStart).getD initial).activeFunction = 2 ∧
      ((enter? closureProgram closureStart).getD initial).frames.map
        (fun frame => frame.saved.map Prod.fst) = [[14, 13, 12]] := by decide +kernel

end LambdaSigil.Combined.OccurrenceActivationWitnesses
