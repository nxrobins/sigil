import LambdaSigil.CombinedSecurity

/-!
Executable feasibility probes for the Public structured-region theorem. These are not a
production Public security claim. The wire program is decoded by the production semantic decoder;
the executions below do not use a parallel hand-constructed SemanticProgram.
-/

namespace LambdaSigil.Combined.PublicRegionProbes

open Semantic

private def node (op : Op) (id origin actual required ceiling aux : UInt32)
    (flags : UInt8 := 1) (label : Label := .pub) : Node :=
  { op, nodeId := id, origin, actual, required, ceiling, aux, flags,
    labelA := label, labelB := label }

/-- The loop header emits a Public actor-boundary payload, reads an Internal stream, and tests
    whether that input is below the Secret limit. No mutable/duplicate SSA definition or malformed
    control target is needed: the body is just the ordinary backedge to the header. -/
def loopHeaderWire : Program := ⟨#[
  node .semProgram 1 1 3 6 17 4,
  node .semFunction 2 1 1 3 4 0 0,
  node .semValue 3 1 1 4 0 0,
  node .semValue 4 1 2 4 0 0,
  node .semValue 5 1 3 1 0 0,
  node .semValue 6 1 4 4 0 0,
  node .semBlock 7 1 1 4 0 0,
  node .semInstruction 8 1 1 0 6 8,
  node .semOperand 9 8 0 4 0 0 0,
  node .semOperand 10 8 1 4 0 0 0,
  node .semOperand 11 8 2 4 0 0 0,
  node .semOperand 12 8 3 4 0 0 0,
  node .semOperand 13 8 4 0 0 0 3,
  node .semOperand 14 8 5 0 0 0 3,
  node .semInstruction 15 1 1 2 2 15,
  node .semOperand 16 15 0 0 0 0 3,
  node .semOperand 17 15 1 0 0 0 3,
  node .semInstruction 18 1 1 3 4 0,
  node .semOperand 19 18 0 1 0 0 0,
  node .semOperand 20 18 1 2 0 0 0,
  node .semOperand 21 18 2 1 0 0 3,
  node .semOperand 22 18 3 13 0 0 3,
  node .semInstruction 23 1 1 0 3 5,
  node .semOperand 24 23 0 3 0 0 0,
  node .semOperand 25 23 1 2 0 0 1,
  node .semOperand 26 23 2 3 0 0 1,
  node .semBlock 27 1 2 1 0 0,
  node .semInstruction 28 1 2 0 1 4,
  node .semOperand 29 28 0 1 0 0 1,
  node .semBlock 30 1 3 1 0 0,
  node .semInstruction 31 1 3 0 1 28,
  node .semOperand 32 31 0 4 0 0 0,
  node .semLabelContract 33 1 0 2 0 2,
  node .semLabelContract 34 1 1 0 0 0 1 .secret,
  node .semLabelContract 35 1 2 1 0 1 1 .internal,
  node .semLabelContract 36 1 3 1 0 1 1 .secret,
  node .semLabelContract 37 1 4 0 0 0,
  node .semPolicyClass 38 8 15 28 0 8,
  node .semPolicyClass 39 15 0 27 0 7,
  node .semPolicyClass 40 23 1 21 0 1
]⟩

def loopHeaderProgram : SemanticProgram := semanticProgramOf loopHeaderWire

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def hexPairs? : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
      let h ← hexDigit? high
      let l ← hexDigit? low
      let tail ← hexPairs? rest
      pure (UInt8.ofNat (16 * h + l) :: tail)
  | [_] => none

private def fixtureHex : String :=
  include_str ".." / "fixtures" / "public-loop-header-boundary.hex"

/-- Quote fixture bytes as literals rather than making the kernel normalize a text parser.
    This does not decide any proposition: the decoder and verifier theorems below are still
    kernel-checked over the literal bytes also read by the Rust linked-native test. -/
elab "public_loop_header_bytes%" : term => do
  let digits := fixtureHex.toList.filter fun c => !c.isWhitespace
  let some bytes := hexPairs? digits | throwError "invalid Public loop-header fixture hex"
  return Lean.mkApp (Lean.mkConst ``ByteArray.mk) (Lean.toExpr bytes.toArray)

def loopHeaderBytes : ByteArray := public_loop_header_bytes%

def loopHeaderState (limit : Int) : State :=
  let labels := loopHeaderProgram.valueLabels
  let values := labels.map fun label => (⟨label, 0⟩ : Value)
  { pc := 0,
    values := (values.setIfInBounds 3 ⟨.secret, limit⟩).setIfInBounds 6 ⟨.pub, 7⟩,
    aggregates := Array.replicate labels.size [], capabilityBalances := #[],
    externalInputs := (Array.replicate 43 []).setIfInBounds 15 [0, 1],
    externalCursors := Array.replicate 43 0 }

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem loop_header_wire_accepted : ProgramSafe loopHeaderWire := by
  unfold ProgramSafe
  decide +kernel

theorem loop_header_shared_bytes_decode : decode loopHeaderBytes = some loopHeaderWire := by
  decide +kernel

theorem loop_header_shared_bytes_accepted : verifyBytesWithRawSemantics loopHeaderBytes = 0 := by
  have hcheck := (linked_raw_semantic_verifier_acceptance_iff loopHeaderWire).mp
    loop_header_wire_accepted |>.2
  have hmanifest : semanticProgramNode? loopHeaderWire =
      some (node .semProgram 1 1 3 6 17 4) := by
    decide +kernel
  simp only [verifyBytesWithRawSemantics, loop_header_shared_bytes_decode, hmanifest,
    hcheck, Option.map_none, Option.getD_none]

theorem loop_header_start_well_formed (limit : Int) :
    StateWellFormed loopHeaderProgram (loopHeaderState limit) := by
  simp [StateWellFormed, loopHeaderState, ExternalStateWellFormed]

theorem loop_header_starts_public_equivalent :
    PublicLowEquivalent loopHeaderProgram (loopHeaderState 0) (loopHeaderState 1) := by
  refine ⟨rfl, rfl, rfl, trivial, ?_⟩
  refine ⟨⟨rfl, rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ?_, ?_, ?_⟩
  · intro site hl hr hpublic
    rfl
  · intro offset hl hr hpublic
    rfl
  · intro cell hl hr hpublic
    rfl
  · simp [loopHeaderState]
  · simp [loopHeaderState]
  · intro cell hl hr hpublic
    have hsecret : labelAt loopHeaderProgram.valueLabels (UInt32.ofNat 3) = .secret := by
      decide +kernel
    have hne : cell ≠ 3 := by
      intro heq
      subst cell
      rw [hsecret] at hpublic
      cases hpublic
    dsimp only [loopHeaderState] at hl hr ⊢
    have hbase : cell < (loopHeaderProgram.valueLabels.map
        fun label => (⟨label, 0⟩ : Value)).size := by simpa using hl
    have hl3 : cell < ((loopHeaderProgram.valueLabels.map
        fun label => (⟨label, 0⟩ : Value)).setIfInBounds 3 ⟨.secret, 0⟩).size := by
      simpa using hl
    have hr3 : cell < ((loopHeaderProgram.valueLabels.map
        fun label => (⟨label, 0⟩ : Value)).setIfInBounds 3 ⟨.secret, 1⟩).size := by
      simpa using hr
    rw [Array.getElem_setIfInBounds hl3, Array.getElem_setIfInBounds hr3]
    by_cases hsix : 6 = cell
    · simp [hsix]
    · simp only [if_neg hsix]
      rw [Array.getElem_setIfInBounds hbase, Array.getElem_setIfInBounds hbase]
      simp [Ne.symm hne]

theorem loop_header_starts_at_public_function_entry :
    (loopHeaderProgram.functions[0]?).map Function.firstInstruction = some 0 ∧
      (loopHeaderProgram.instructions[0]?).map Instruction.blockLabel = some .pub := by
  decide +kernel

theorem loop_header_independent_runs_halt :
    (runPrefix loopHeaderProgram 5 (loopHeaderState 0)).state.halted = true ∧
    (runPrefix loopHeaderProgram 10 (loopHeaderState 1)).state.halted = true ∧
    (runPrefix loopHeaderProgram 5 (loopHeaderState 0)).state.trapped = false ∧
    (runPrefix loopHeaderProgram 10 (loopHeaderState 1)).state.trapped = false := by decide +kernel

theorem loop_header_release_traces_agree :
    releaseEvents (runPrefix loopHeaderProgram 5 (loopHeaderState 0)).events =
      releaseEvents (runPrefix loopHeaderProgram 10 (loopHeaderState 1)).events := by decide +kernel

theorem loop_header_public_boundary_traces_differ :
    outputBoundaryEvents (runPrefix loopHeaderProgram 5 (loopHeaderState 0)).events ≠
      outputBoundaryEvents (runPrefix loopHeaderProgram 10 (loopHeaderState 1)).events := by decide +kernel

theorem loop_header_starts_at_public_cut_points :
    PublicCutPoint loopHeaderProgram (loopHeaderState 0) ∧
      PublicCutPoint loopHeaderProgram (loopHeaderState 1) := by
  have hbound : 0 < loopHeaderProgram.instructions.size := by decide +kernel
  let first := loopHeaderProgram.instructions[0]'hbound
  have hlookup : loopHeaderProgram.instructions[0]? = some first :=
    Array.getElem?_eq_getElem hbound
  have h : first.blockLabel = .pub := by
    simpa only [hlookup, Option.map_some, Option.some.injEq] using
      loop_header_starts_at_public_function_entry.2
  exact ⟨Or.inr (Or.inr ⟨first, hlookup, h⟩),
    Or.inr (Or.inr ⟨first, hlookup, h⟩)⟩

theorem loop_header_uses_equal_external_streams :
    (loopHeaderState 0).externalInputs = (loopHeaderState 1).externalInputs ∧
      (loopHeaderState 0).externalCursors = (loopHeaderState 1).externalCursors := by
  exact ⟨rfl, rfl⟩

/-- Both runs execute the same real top-level output instruction as their last step. Neither
    a fabricated call frame, falling off the instruction array, nor exhausted fuel explains the
    result. The left and right executions actually need different numbers of steps. -/
theorem loop_header_success_is_explicit_not_fuel_exhaustion :
    (runPrefix loopHeaderProgram 4 (loopHeaderState 0)).state.pc = 5 ∧
    (runPrefix loopHeaderProgram 9 (loopHeaderState 1)).state.pc = 5 ∧
    (runPrefix loopHeaderProgram 4 (loopHeaderState 0)).state.halted = false ∧
    (runPrefix loopHeaderProgram 9 (loopHeaderState 1)).state.halted = false ∧
    (runPrefix loopHeaderProgram 4 (loopHeaderState 0)).state.callStack = [] ∧
    (runPrefix loopHeaderProgram 9 (loopHeaderState 1)).state.callStack = [] ∧
    (loopHeaderProgram.instructions[5]?).map Instruction.op = some .output := by decide +kernel

/-- A kernel-checked obstruction to the proposed production Public corollary under the current
    acceptance policy. No weakening of the final Public-state projection repairs this unequal
    Public boundary trace. Policy changes require the separate product approval in the roadmap. -/
theorem accepted_loop_header_public_counterexample :
    ProgramSafe loopHeaderWire ∧
    StateWellFormed loopHeaderProgram (loopHeaderState 0) ∧
    StateWellFormed loopHeaderProgram (loopHeaderState 1) ∧
    PublicLowEquivalent loopHeaderProgram (loopHeaderState 0) (loopHeaderState 1) ∧
    (runPrefix loopHeaderProgram 5 (loopHeaderState 0)).state.halted = true ∧
    (runPrefix loopHeaderProgram 10 (loopHeaderState 1)).state.halted = true ∧
    (runPrefix loopHeaderProgram 5 (loopHeaderState 0)).state.trapped = false ∧
    (runPrefix loopHeaderProgram 10 (loopHeaderState 1)).state.trapped = false ∧
    releaseEvents (runPrefix loopHeaderProgram 5 (loopHeaderState 0)).events =
      releaseEvents (runPrefix loopHeaderProgram 10 (loopHeaderState 1)).events ∧
    outputBoundaryEvents (runPrefix loopHeaderProgram 5 (loopHeaderState 0)).events ≠
      outputBoundaryEvents (runPrefix loopHeaderProgram 10 (loopHeaderState 1)).events := by
  have hhalt := loop_header_independent_runs_halt
  exact ⟨loop_header_wire_accepted, loop_header_start_well_formed 0,
    loop_header_start_well_formed 1, loop_header_starts_public_equivalent,
    hhalt.1, hhalt.2.1, hhalt.2.2.1, hhalt.2.2.2,
    loop_header_release_traces_agree, loop_header_public_boundary_traces_differ⟩

end LambdaSigil.Combined.PublicRegionProbes
