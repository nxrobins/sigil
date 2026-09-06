import LambdaSigil.CombinedSecurity
import LambdaSigil.DecoderStream

/-!
# Retained v8 occurrence-policy counterexamples

These executable raw-machine witnesses record the historical acyclic backward escape. It depends
on numeric block ordering, not on loop repetition: a Secret dispatch arm jumps back to a block
whose numeric ID is smaller than the arm's, so that block's output inherits no pc edge, while the
declared merge block was restored to the Public pc even though the escaping arm never reaches it.
Since the merge-restore rule became postdominance-aware (`semanticSuccessfulPathsReach`), the
retained verifier rejects the program at the merge block's output, and the raw-machine theorems
below show why that verdict is the right one: two Public-equivalent starts produce different
Public output traces. The lower block's output is still decoded as a Public occurrence, so the
witnesses remain regression evidence for the stronger v9 occurrence checker, never a production
security claim.
-/

namespace LambdaSigil.Combined.V8OccurrenceProbes

open Semantic

private def node (op : Op) (id actual required ceiling aux : UInt32)
    (flags : UInt8 := 1) (label : Label := .pub) : Node :=
  { op, nodeId := id, origin := 1, actual, required, ceiling, aux, flags,
    labelA := label, labelB := label }

/-- Block one selects blocks three/four using a Secret parameter. Block three jumps to block two,
    whose output inherits no pc edge because its numeric block ID is smaller. The other arm reaches
    the declared merge, block five. There is no cycle: both executions take exactly three steps. -/
def acyclicBackwardEscapeWire : Program := ⟨#[
  semanticManifest 1 2 5 5 8,
  { minimalSemanticFunction with required := 5, ceiling := 2 },
  node .semValue 3 1 1 0 0,
  node .semValue 4 2 4 0 0,
  node .semBlock 5 1 1 0 0,
  node .semInstruction 6 1 0 4 3,
  { node .semOperand 7 0 1 0 0 0 with origin := 6 },
  { node .semOperand 8 1 3 0 0 with origin := 6 },
  { node .semOperand 9 2 4 0 0 with origin := 6 },
  { node .semOperand 10 3 5 0 0 with origin := 6 },
  node .semBlock 11 2 1 0 0,
  node .semInstruction 12 2 0 1 28,
  { node .semOperand 13 0 2 0 0 0 with origin := 12 },
  node .semBlock 14 3 1 0 0,
  node .semInstruction 15 3 0 1 4,
  { node .semOperand 16 0 2 0 0 with origin := 15 },
  node .semBlock 17 4 1 0 0,
  node .semInstruction 18 4 0 1 4,
  { node .semOperand 19 0 5 0 0 with origin := 18 },
  node .semBlock 20 5 1 0 0,
  node .semInstruction 21 5 0 1 28,
  { node .semOperand 22 0 2 0 0 0 with origin := 21 },
  node .semLabelContract 23 0 2 0 2,
  node .semLabelContract 24 1 0 0 0 1 .secret,
  node .semLabelContract 25 2 1 0 1,
  { node .semPolicyClass 26 1 20 0 0 with origin := 6 }
]⟩

def acyclicBackwardEscapeProgram : SemanticProgram :=
  semanticProgramOf acyclicBackwardEscapeWire

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
  include_str ".." / "fixtures" / "public-acyclic-backward-escape.hex"

/-- Literal quotation shares exactly the fixture bytes with the linked Rust regression test.
    The decoder/verdict proofs below are still checked by the Lean kernel. -/
elab "public_acyclic_escape_bytes%" : term => do
  let digits := fixtureHex.toList.filter fun c => !c.isWhitespace
  let some bytes := hexPairs? digits | throwError "invalid acyclic Public escape fixture hex"
  return Lean.mkApp (Lean.mkConst ``ByteArray.mk) (Lean.toExpr bytes.toArray)

def acyclicBackwardEscapeBytes : ByteArray := public_acyclic_escape_bytes%

def acyclicBackwardEscapeState (selector : Int) : State :=
  let labels := acyclicBackwardEscapeProgram.valueLabels
  { pc := 0,
    values := (labels.map fun label => (⟨label, 0⟩ : Value)).setIfInBounds
      3 ⟨.secret, selector⟩,
    aggregates := Array.replicate labels.size [], capabilityBalances := #[] }

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The retained verifier now rejects the escape: block five no longer restores the Public pc,
    so its output of a Public-contract value under Secret control is a flow violation. The
    relational static check on its own still accepts the program, which is the residual gap the
    v9 occurrence policy closes. -/
theorem acyclic_backward_escape_retained_verifier_rejects :
    (semanticProgramNode? acyclicBackwardEscapeWire).isSome = true ∧
      verifyProgram acyclicBackwardEscapeWire = some ⟨.flow, 21, 1⟩ ∧
      verifyProgramWithRawSemantics acyclicBackwardEscapeWire = some ⟨.flow, 21, 1⟩ ∧
      rawRelationalStaticSafeB (semanticProgramOf acyclicBackwardEscapeWire) = true := by
  decide +kernel

theorem acyclic_backward_escape_shared_bytes_decode :
    decode acyclicBackwardEscapeBytes = some acyclicBackwardEscapeWire := by
  -- Through the sequential twin (DecoderStream): 6.9 GB before, under 2 GB after.
  exact (DecoderStream.decode_eq_decodeList _).trans (by decide +kernel)

/-- The linked native verdict for the shared fixture bytes is the packed flow violation at node
    21 with detail 1: node-id in the high word, detail in bits 16..31, kind code 2 in the low
    half-word. The Rust regression test pins the same number against the compiled verifier. -/
theorem acyclic_backward_escape_shared_bytes_rejected :
    verifyBytesWithRawSemantics acyclicBackwardEscapeBytes = 90194378754 := by
  have hverdict := acyclic_backward_escape_retained_verifier_rejects.2.2.1
  have hmanifest : semanticProgramNode? acyclicBackwardEscapeWire =
      some (semanticManifest 1 2 5 5 8) := by decide +kernel
  -- `rw`, not `unfold` or `simp`: those reduce the match on the fixture's `decode` by
  -- evaluating the indexed decoder in the elaborator (see PublicRegionProbes).
  rw [verifyBytesWithRawSemantics, acyclic_backward_escape_shared_bytes_decode]
  simp only [hmanifest, hverdict, Option.map_some, Option.getD_some]
  decide +kernel

theorem acyclic_backward_escape_decoded_labels :
    acyclicBackwardEscapeProgram.instructions.map (fun instruction =>
      (instruction.id, instruction.blockLabel)) =
      #[(6, .pub), (12, .pub), (15, .secret), (18, .secret), (21, .secret)] := by
  decide +kernel

theorem acyclic_backward_escape_start_well_formed (selector : Int) :
    StateWellFormed acyclicBackwardEscapeProgram (acyclicBackwardEscapeState selector) := by
  simp [StateWellFormed, acyclicBackwardEscapeState, ExternalStateWellFormed]

theorem acyclic_backward_escape_starts_public_equivalent :
    PublicLowEquivalent acyclicBackwardEscapeProgram
      (acyclicBackwardEscapeState 0) (acyclicBackwardEscapeState 1) := by
  refine ⟨rfl, rfl, rfl, trivial, ?_⟩
  refine ⟨⟨rfl, rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ?_, ?_, ?_⟩
  · intro site hl
    simp [acyclicBackwardEscapeState] at hl
  · intro offset hl
    simp [acyclicBackwardEscapeState] at hl
  · intro cell hl hr hpublic
    rfl
  · simp [acyclicBackwardEscapeState]
  · simp [acyclicBackwardEscapeState]
  · intro cell hl hr hpublic
    have hsecret : labelAt acyclicBackwardEscapeProgram.valueLabels (UInt32.ofNat 3) =
        .secret := by decide +kernel
    have hne : 3 ≠ cell := by
      intro heq
      rw [← heq, hsecret] at hpublic
      cases hpublic
    have hbound : cell < (acyclicBackwardEscapeProgram.valueLabels.map
        fun label => (⟨label, 0⟩ : Value)).size := by
      simpa [acyclicBackwardEscapeState] using hl
    dsimp only [acyclicBackwardEscapeState] at hl hr ⊢
    rw [Array.getElem_setIfInBounds hbound, Array.getElem_setIfInBounds hbound]
    simp [hne]

theorem acyclic_backward_escape_starts_at_matching_public_cut :
    PublicCutPoint acyclicBackwardEscapeProgram (acyclicBackwardEscapeState 0) ∧
      PublicCutPoint acyclicBackwardEscapeProgram (acyclicBackwardEscapeState 1) := by
  have hfirst : ∃ instruction, acyclicBackwardEscapeProgram.instructions[0]? = some instruction ∧
      instruction.blockLabel = .pub := by decide +kernel
  exact ⟨Or.inr (Or.inr hfirst), Or.inr (Or.inr hfirst)⟩

theorem acyclic_backward_escape_successful_runs :
    (runPrefix acyclicBackwardEscapeProgram 3 (acyclicBackwardEscapeState 0)).state.halted = true ∧
    (runPrefix acyclicBackwardEscapeProgram 3 (acyclicBackwardEscapeState 1)).state.halted = true ∧
    (runPrefix acyclicBackwardEscapeProgram 3 (acyclicBackwardEscapeState 0)).state.trapped = false ∧
    (runPrefix acyclicBackwardEscapeProgram 3 (acyclicBackwardEscapeState 1)).state.trapped = false := by
  decide +kernel

theorem acyclic_backward_escape_complete_release_traces_equal :
    releaseEvents (runPrefix acyclicBackwardEscapeProgram 3 (acyclicBackwardEscapeState 0)).events =
      releaseEvents (runPrefix acyclicBackwardEscapeProgram 3 (acyclicBackwardEscapeState 1)).events := by
  decide +kernel

/-- With the merge block under Secret control, the selector-zero run emits no Public output at
    all, while the selector-one run escapes to the lower block's Public output at site 12. -/
theorem acyclic_backward_escape_public_output_sites_differ :
    (outputBoundaryEvents
      (runPrefix acyclicBackwardEscapeProgram 3 (acyclicBackwardEscapeState 0)).events).map Event.site =
        [] ∧
    (outputBoundaryEvents
      (runPrefix acyclicBackwardEscapeProgram 3 (acyclicBackwardEscapeState 1)).events).map Event.site =
        [12] := by
  decide +kernel

theorem acyclic_backward_escape_public_traces_differ :
    outputBoundaryEvents
      (runPrefix acyclicBackwardEscapeProgram 3 (acyclicBackwardEscapeState 0)).events ≠
    outputBoundaryEvents
      (runPrefix acyclicBackwardEscapeProgram 3 (acyclicBackwardEscapeState 1)).events := by
  decide +kernel

end LambdaSigil.Combined.V8OccurrenceProbes
