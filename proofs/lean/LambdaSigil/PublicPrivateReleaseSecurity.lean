import LambdaSigil.PublicExecutionSecurity
import LambdaSigil.PublicPrivateSegmentSecurity

/-!
# Public-release silence of verified private segments

The complete release trace deliberately retains every downgrade. The Public induction carries
the immutable subsequence whose decoded occurrence is Public. This module packages the
production lookup theorem from `PublicExecutionSecurity` with verifier-derived private-region
facts, proving that an independently sized private segment contributes no occurrence to that
Public subsequence.

No event is removed from the raw machine and no replacement payload is introduced.
-/

namespace LambdaSigil.Combined.V9.PublicPrivateReleaseSecurity

open Semantic OccurrenceDataflowInvocation OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity Semantic.PublicRegionConvergence
open Semantic.PublicReleaseSynchronization
open PublicExecutionSecurity PublicLocalSecurity PublicPrivateSegmentSecurity
open OccurrenceTransfer

private theorem eq_public_of_flowsTo_public {label : Label}
    (hflow : label.flowsTo .pub = true) : label = .pub := by
  cases label <;> simp_all [Label.flowsTo, Label.rank]

private theorem labelFlows_trans {first middle last : Label}
    (hfirst : first.flowsTo middle = true) (hlast : middle.flowsTo last = true) :
    first.flowsTo last = true := by
  cases first <;> cases middle <;> cases last <;>
    simp_all [Label.flowsTo, Label.rank]

private theorem activeFunctionId_append_suffix (root : UInt32)
    (privateFrames suffix : List CallFrame) :
    activeFunctionId root (privateFrames ++ suffix) =
      activeFunctionId (activeFunctionId root suffix) privateFrames := by
  cases privateFrames <;> simp [activeFunctionId]

/-! ## One-step classification -/

/-- A real release or releaseCT step at a non-Public occurrence contributes no Public release
    observation. The exact event remains in `ReleaseSynchronization.releaseTrace`. -/
theorem raw_publicReleaseTrace_step_private_release
    {program : V9.Program} {analysis : Analysis}
    (hanalysis : analyze? program = some analysis) {state : State}
    {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hoperation : instruction.op = .release ∨ instruction.op = .releaseCT)
    (hnonpublic : instruction.blockLabel ≠ .pub) :
    publicReleaseTrace (rawSemanticProgram program analysis)
      (step (rawSemanticProgram program analysis) state).events = [] := by
  have hsite := releaseSiteOccurrence_eq_blockLabel_of_raw_lookup hanalysis hlookup
  have hsitePrivate :
      (releaseSiteOccurrence (rawSemanticProgram program analysis) instruction.id).eqb
        .pub = false := by
    rw [hsite]
    cases hlabel : instruction.blockLabel <;> simp_all [Label.eqb]
  unfold step
  by_cases hdone : state.halted || state.trapped
  · simp [hdone, publicReleaseTrace, ReleaseSynchronization.releaseTrace,
      Semantic.releaseEvents]
  · rw [if_neg hdone, hlookup]
    rcases hoperation with hrelease | hreleaseCT
    · simp [hrelease, ordinaryStep, instructionEvents, publicReleaseTrace,
        ReleaseSynchronization.releaseTrace, Semantic.releaseEvents, EventKind.eqb,
        hsitePrivate]
    · simp [hreleaseCT, ordinaryStep, instructionEvents, publicReleaseTrace,
        ReleaseSynchronization.releaseTrace, Semantic.releaseEvents, EventKind.eqb,
        hsitePrivate]

/-- Every actual step classified by a private activation anchor contributes no Public release
    occurrence, including both downgrade stages. -/
theorem verified_private_anchor_step_publicReleaseTrace_nil
    {program : V9.Program} {analysis : Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine : List CallFrame} {anchor : Nat} {state : State}
    {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hanchor : ActivationAnchor spine anchor state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub) :
    publicReleaseTrace (rawSemanticProgram program analysis)
      (step (rawSemanticProgram program analysis) state).events = [] := by
  by_cases hrelease : instruction.op = .release
  · have hrawNonpublic := private_anchor_nonoutput_raw_block_nonpublic hanalysis
      hactive hanchor hlookup hnonpublic (by simp [hrelease])
    exact raw_publicReleaseTrace_step_private_release hanalysis hlookup
      (Or.inl hrelease) hrawNonpublic
  · by_cases hreleaseCT : instruction.op = .releaseCT
    · have hrawNonpublic := private_anchor_nonoutput_raw_block_nonpublic hanalysis
        hactive hanchor hlookup hnonpublic (by simp [hreleaseCT])
      exact raw_publicReleaseTrace_step_private_release hanalysis hlookup
        (Or.inr hreleaseCT) hrawNonpublic
    · exact publicReleaseTrace_step_nonrelease
        (rawSemanticProgram program analysis) state instruction hlookup hrelease hreleaseCT

/-- Away from an internal return, a private invocation summary remains a lower bound of the raw
    block label through every coherent descendant frame. -/
theorem private_invocation_nonoutput_raw_block_nonpublic
    {program : V9.Program} {analysis : Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine : List CallFrame} {state : State}
    {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlive : ActivationLive spine state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : labelAt analysis.labels (activeFunctionId root spine) ≠ .pub)
    (hnonoutput : instruction.op ≠ .output) :
    instruction.blockLabel ≠ .pub := by
  obtain ⟨privateFrames, hstack⟩ := hlive
  have hchain := hactive.frameChain
  rw [hstack] at hchain
  have hprefixChain := frameChain_prefix_above_suffix hchain
  have hinvocationToActive :=
    frameChain_root_occurrence_flows_to_active hanalysis hprefixChain
  obtain ⟨current, hcurrentLookup, hcurrentFunction⟩ := hactive.currentInstruction
  have hcurrentEq : current = instruction := by
    rw [hlookup] at hcurrentLookup
    exact Option.some.inj hcurrentLookup.symm
  subst current
  have hactiveEq : activeFunctionId root state.callStack =
      activeFunctionId (activeFunctionId root spine) privateFrames := by
    rw [hstack]
    exact activeFunctionId_append_suffix root privateFrames spine
  have hactiveToBlock :=
    invocation_occurrence_flows_to_raw_block_of_lookup hlookup hnonoutput
  have hrootToBlock :
      (labelAt analysis.labels (activeFunctionId root spine)).flowsTo
        instruction.blockLabel = true := by
    apply labelFlows_trans hinvocationToActive
    rw [← hactiveEq, ← hcurrentFunction]
    exact hactiveToBlock
  intro hpublic
  have hrootPublic : labelAt analysis.labels (activeFunctionId root spine) = .pub :=
    eq_public_of_flowsTo_public (by simpa [hpublic] using hrootToBlock)
  exact hnonpublic hrootPublic

/-- Every step inside an invocation-private activation contributes no Public release occurrence.
    Internal returns are non-release steps, so their root-return occurrence raise is irrelevant. -/
theorem verified_private_invocation_step_publicReleaseTrace_nil
    {program : V9.Program} {analysis : Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine : List CallFrame} {state : State}
    {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlive : ActivationLive spine state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : labelAt analysis.labels (activeFunctionId root spine) ≠ .pub) :
    publicReleaseTrace (rawSemanticProgram program analysis)
      (step (rawSemanticProgram program analysis) state).events = [] := by
  by_cases hrelease : instruction.op = .release
  · have hrawNonpublic := private_invocation_nonoutput_raw_block_nonpublic hanalysis
      hactive hlive hlookup hnonpublic (by simp [hrelease])
    exact raw_publicReleaseTrace_step_private_release hanalysis hlookup
      (Or.inl hrelease) hrawNonpublic
  · by_cases hreleaseCT : instruction.op = .releaseCT
    · have hrawNonpublic := private_invocation_nonoutput_raw_block_nonpublic hanalysis
        hactive hlive hlookup hnonpublic (by simp [hreleaseCT])
      exact raw_publicReleaseTrace_step_private_release hanalysis hlookup
        (Or.inr hreleaseCT) hrawNonpublic
    · exact publicReleaseTrace_step_nonrelease
        (rawSemanticProgram program analysis) state instruction hlookup hrelease hreleaseCT

/-! ## Reusable segment facts -/

/-- The exact anchor facts returned by `v9_verified_successful_private_activation_segment`
    construct the release-silence component consumed by independent-length composition. -/
theorem verified_private_activation_publicReleaseSilentSegment
    {program : V9.Program} {analysis : Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine : List CallFrame} {length : Nat} {start : State}
    (hprivate : ∀ elapsed, elapsed < length →
      ∃ anchor instruction,
        ActiveState (rawSemanticProgram program analysis) root
            (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
          ActivationAnchor spine anchor
            (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
          (rawSemanticProgram program analysis).instructions[
              (runPrefix (rawSemanticProgram program analysis) elapsed start).state.pc]? =
            some instruction ∧
          localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub) :
    PublicReleaseSilentSegment (rawSemanticProgram program analysis) length start := by
  intro elapsed helapsed
  obtain ⟨anchor, instruction, hactive, hanchor, hlookup, hnonpublic⟩ :=
    hprivate elapsed helapsed
  exact verified_private_anchor_step_publicReleaseTrace_nil hanalysis hactive hanchor
    hlookup hnonpublic

/-- The active/live facts returned by `v9_verified_successful_private_invocation_segment`
    construct the same release-silence component for an invocation-private callee. -/
theorem verified_private_invocation_publicReleaseSilentSegment
    {program : V9.Program} {analysis : Analysis}
    (hanalysis : analyze? program = some analysis)
    {root : UInt32} {spine : List CallFrame} {length : Nat} {start : State}
    (hnonpublic : labelAt analysis.labels (activeFunctionId root spine) ≠ .pub)
    (hprivate : ∀ elapsed, elapsed < length →
      ActiveState (rawSemanticProgram program analysis) root
          (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
        ActivationLive spine
          (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
        ∃ instruction,
          (rawSemanticProgram program analysis).instructions[
              (runPrefix (rawSemanticProgram program analysis) elapsed start).state.pc]? =
            some instruction) :
    PublicReleaseSilentSegment (rawSemanticProgram program analysis) length start := by
  intro elapsed helapsed
  obtain ⟨hactive, hlive, instruction, hlookup⟩ := hprivate elapsed helapsed
  exact verified_private_invocation_step_publicReleaseTrace_nil hanalysis hactive hlive
    hlookup hnonpublic

end LambdaSigil.Combined.V9.PublicPrivateReleaseSecurity
