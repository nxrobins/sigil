import LambdaSigil.PublicPrivateSegmentSecurity

/-!
# Paired verified-continuation closure

Two independently long private activation segments restore the complete Public projection at
their actual endpoints.  This module closes the remaining control/state bridge.  An exact
activation stack makes an ordinary `ActivationContinuationAt` a real current instruction at the
shared verifier parent.  A synthetic function-return vertex is kept separate: it is a live state
poised at a genuine output (or a top-level halt), not a fabricated Public instruction.

`ActivationContinuationAt` alone does not say that an ordinary parent instruction is Public: a
parent may still be nested under an enclosing private frontier.  The core theorem therefore
derives matching current-continuation evidence without reclassifying it.  A separate corollary
constructs `VerifiedPublicCutPoint`s from the explicit verifier-derived fact that every decoded
instruction at the parent is Public.  No runtime transition or observation is replaced.
-/

namespace LambdaSigil.Combined.V9.PublicContinuationSecurity

open Semantic OccurrenceRegions
open Semantic.PublicRegionSecurity Semantic.PublicRegionConvergence

/-- Two restored endpoints at the same ordinary verifier continuation.  The relation contains
    the complete existing `PublicLowEquivalent`, including control, frames, immutable external
    streams, and all Public data. -/
structure MatchingCurrentContinuation (machine : SemanticProgram) (root : UInt32)
    (parent : Nat) (left right : State) : Prop where
  low : PublicLowEquivalent machine left right
  leftReachable : ReachableFromRoot machine root left
  rightReachable : ReachableFromRoot machine root right
  leftActive : ActiveState machine root left
  rightActive : ActiveState machine root right
  parent_eq_leftPc : parent = left.pc
  parent_eq_rightPc : parent = right.pc
  occurrence : ∃ instruction,
    machine.instructions[left.pc]? = some instruction ∧
      machine.instructions[right.pc]? = some instruction

/-- Exact pre-completion classification at a synthetic function-return vertex.  Each endpoint is
    still active and executes a genuine decoded output, or (only with an empty activation spine)
    a genuine halt. -/
structure PairedSyntheticReturnContinuation (machine : SemanticProgram) (root : UInt32)
    (parent : Nat) (leftSpine rightSpine : List CallFrame) (left right : State) : Prop where
  leftReachable : ReachableFromRoot machine root left
  rightReachable : ReachableFromRoot machine root right
  leftActive : ActiveState machine root left
  rightActive : ActiveState machine root right
  leftParent : parent = functionReturn machine (activeFunctionId root leftSpine)
  rightParent : parent = functionReturn machine (activeFunctionId root rightSpine)
  leftStack : left.callStack = leftSpine
  rightStack : right.callStack = rightSpine
  leftReturn : ∃ instruction,
    machine.instructions[left.pc]? = some instruction ∧
      instruction.functionId = activeFunctionId root leftSpine ∧
      (instruction.op = .output ∨ (leftSpine = [] ∧ instruction.op = .halt))
  rightReturn : ∃ instruction,
    machine.instructions[right.pc]? = some instruction ∧
      instruction.functionId = activeFunctionId root rightSpine ∧
      (instruction.op = .output ∨ (rightSpine = [] ∧ instruction.op = .halt))

/-- Honest endpoint dichotomy.  The current case is not called a Public cut point until the
    verifier-derived parent-occurrence fact is supplied. -/
inductive PairedContinuationOutcome (machine : SemanticProgram) (root : UInt32)
    (parent : Nat) (leftSpine rightSpine : List CallFrame) (left right : State) : Prop
  | current (evidence : MatchingCurrentContinuation machine root parent left right) :
      PairedContinuationOutcome machine root parent leftSpine rightSpine left right
  | synthetic
      (evidence : PairedSyntheticReturnContinuation machine root parent
        leftSpine rightSpine left right) :
      PairedContinuationOutcome machine root parent leftSpine rightSpine left right

private theorem functionReturn_not_instruction_pc (machine : SemanticProgram)
    (functionId : UInt32) {pc : Nat}
    (hpc : pc < machine.instructions.size) :
    functionReturn machine functionId ≠ pc := by
  unfold functionReturn
  omega

private theorem callStackPublicEquivalent_of_restored_spines
    {machine : SemanticProgram} {leftStart rightStart left right : State}
    {leftSpine rightSpine : List CallFrame}
    (hlow : PublicLowEquivalent machine leftStart rightStart)
    (hleftStart : leftStart.callStack = leftSpine)
    (hrightStart : rightStart.callStack = rightSpine)
    (hleft : left.callStack = leftSpine) (hright : right.callStack = rightSpine) :
    CallStackPublicEquivalent machine left.callStack right.callStack := by
  have hstacks := hlow.2.2.2.1
  simpa [hleftStart, hrightStart, hleft, hright] using hstacks

private theorem publicLowEquivalent_of_restored_current
    {machine : SemanticProgram} {leftStart rightStart left right : State}
    {root : UInt32} {leftSpine rightSpine : List CallFrame} {parent : Nat}
    (hstartLow : PublicLowEquivalent machine leftStart rightStart)
    (hleftStartStack : leftStart.callStack = leftSpine)
    (hrightStartStack : rightStart.callStack = rightSpine)
    (hleftActive : ActiveState machine root left)
    (hrightActive : ActiveState machine root right)
    (hleftStack : left.callStack = leftSpine)
    (hrightStack : right.callStack = rightSpine)
    (hleftPc : parent = left.pc) (hrightPc : parent = right.pc)
    (hleftStreams : left.externalInputs = leftStart.externalInputs)
    (hrightStreams : right.externalInputs = rightStart.externalInputs)
    (hleftProjection : publicProjection machine left = publicProjection machine leftStart)
    (hrightProjection : publicProjection machine right = publicProjection machine rightStart) :
    PublicLowEquivalent machine left right := by
  obtain ⟨_, _, _, _, _, _, hstartStreams, hstartProjection⟩ :=
    (publicLowEquivalent_iff_projection machine leftStart rightStart).mp hstartLow
  apply (publicLowEquivalent_iff_projection machine left right).2
  refine ⟨hleftPc.symm.trans hrightPc, ?_, ?_, ?_, hleftActive.wellFormed.1,
    hrightActive.wellFormed.1, ?_, ?_⟩
  · exact hleftActive.notHalted.trans hrightActive.notHalted.symm
  · exact hleftActive.notTrapped.trans hrightActive.notTrapped.symm
  · exact callStackPublicEquivalent_of_restored_spines hstartLow hleftStartStack
      hrightStartStack hleftStack hrightStack
  · exact hleftStreams.trans (hstartStreams.trans hrightStreams.symm)
  · exact hleftProjection.trans (hstartProjection.trans hrightProjection.symm)

/-- Paired endpoint bridge for two actual private segments.  Projection restoration is not enough
    by itself because `PublicProjection` intentionally excludes immutable external streams; the
    two stream-preservation premises are the exact unary facts provided by raw `runPrefix`.

    The root parameter of each `ActiveState` is shared, but otherwise the two activation spines
    may contain different Secret saved payloads.  Their Public frame equivalence is inherited
    from the starting `PublicLowEquivalent` relation. -/
theorem paired_activation_continuation_outcome
    {machine : SemanticProgram} {root : UInt32} {parent : Nat}
    {leftStart rightStart left right : State} {leftSpine rightSpine : List CallFrame}
    (hstartLow : PublicLowEquivalent machine leftStart rightStart)
    (hleftStartStack : leftStart.callStack = leftSpine)
    (hrightStartStack : rightStart.callStack = rightSpine)
    (hleftStack : left.callStack = leftSpine)
    (hrightStack : right.callStack = rightSpine)
    (hleftProjection : publicProjection machine left = publicProjection machine leftStart)
    (hrightProjection : publicProjection machine right = publicProjection machine rightStart)
    (hleftStreams : left.externalInputs = leftStart.externalInputs)
    (hrightStreams : right.externalInputs = rightStart.externalInputs)
    (hleftReachable : ReachableFromRoot machine root left)
    (hrightReachable : ReachableFromRoot machine root right)
    (hleftActive : ActiveState machine root left)
    (hrightActive : ActiveState machine root right)
    (hleftContinuation : ActivationContinuationAt machine root leftSpine parent left)
    (hrightContinuation : ActivationContinuationAt machine root rightSpine parent right) :
    PairedContinuationOutcome machine root parent leftSpine rightSpine left right := by
  rcases hleftContinuation with hleftAnchor |
      ⟨hleftParent, _, leftInstruction, hleftLookup, hleftFunction, hleftOperation⟩
  · have hleftPc : parent = left.pc := hleftAnchor.current_injective hleftStack
    rcases hrightContinuation with hrightAnchor |
        ⟨hrightParent, _, rightInstruction, hrightLookup, hrightFunction, hrightOperation⟩
    · have hrightPc : parent = right.pc := hrightAnchor.current_injective hrightStack
      have hlow : PublicLowEquivalent machine left right := by
        apply publicLowEquivalent_of_restored_current hstartLow hleftStartStack
          hrightStartStack hleftActive hrightActive hleftStack hrightStack
          hleftPc hrightPc hleftStreams hrightStreams hleftProjection hrightProjection
      obtain ⟨instruction, hlookup, _⟩ := hleftActive.currentInstruction
      have hrightLookup' : machine.instructions[right.pc]? = some instruction := by
        rw [← hrightPc, hleftPc]
        exact hlookup
      exact .current ⟨hlow, hleftReachable, hrightReachable, hleftActive, hrightActive,
        hleftPc, hrightPc, instruction, hlookup, hrightLookup'⟩
    · obtain ⟨instruction, hlookup, _⟩ := hleftActive.currentInstruction
      have hbound := (Array.getElem?_eq_some_iff.mp hlookup).1
      exact False.elim ((functionReturn_not_instruction_pc machine
        (activeFunctionId root rightSpine) hbound) (hrightParent.symm.trans hleftPc))
  · rcases hrightContinuation with hrightAnchor |
        ⟨hrightParent, _, rightInstruction, hrightLookup, hrightFunction, hrightOperation⟩
    · have hrightPc : parent = right.pc := hrightAnchor.current_injective hrightStack
      obtain ⟨instruction, hlookup, _⟩ := hrightActive.currentInstruction
      have hbound := (Array.getElem?_eq_some_iff.mp hlookup).1
      exact False.elim ((functionReturn_not_instruction_pc machine
        (activeFunctionId root leftSpine) hbound) (hleftParent.symm.trans hrightPc))
    · exact .synthetic
        ⟨hleftReachable, hrightReachable, hleftActive, hrightActive,
          hleftParent, hrightParent, hleftStack, hrightStack,
          ⟨leftInstruction, hleftLookup, hleftFunction, hleftOperation⟩,
          ⟨rightInstruction, hrightLookup, hrightFunction, hrightOperation⟩⟩

/-- Direct `SuccessfulExecution` wrapper for the production private-segment outputs.  Active-state
    and immutable-stream preservation are derived from the two actual raw prefixes rather than
    repeated as caller premises. -/
theorem paired_runPrefix_activation_continuation_outcome
    {machine : SemanticProgram} {root : UInt32} {parent : Nat}
    {leftSteps rightSteps leftElapsed rightElapsed : Nat}
    {leftStart rightStart : State} {leftResult rightResult : StepResult}
    {leftSpine rightSpine : List CallFrame}
    (hstartLow : PublicLowEquivalent machine leftStart rightStart)
    (hleftStartStack : leftStart.callStack = leftSpine)
    (hrightStartStack : rightStart.callStack = rightSpine)
    (hleftExecution : SuccessfulExecution machine root leftSteps leftStart leftResult)
    (hrightExecution : SuccessfulExecution machine root rightSteps rightStart rightResult)
    (hleftElapsed : leftElapsed < leftSteps) (hrightElapsed : rightElapsed < rightSteps)
    (hleftReachable : ReachableFromRoot machine root
      (runPrefix machine leftElapsed leftStart).state)
    (hrightReachable : ReachableFromRoot machine root
      (runPrefix machine rightElapsed rightStart).state)
    (hleftStack : (runPrefix machine leftElapsed leftStart).state.callStack = leftSpine)
    (hrightStack : (runPrefix machine rightElapsed rightStart).state.callStack = rightSpine)
    (hleftProjection : publicProjection machine
        (runPrefix machine leftElapsed leftStart).state = publicProjection machine leftStart)
    (hrightProjection : publicProjection machine
        (runPrefix machine rightElapsed rightStart).state = publicProjection machine rightStart)
    (hleftContinuation : ActivationContinuationAt machine root leftSpine parent
      (runPrefix machine leftElapsed leftStart).state)
    (hrightContinuation : ActivationContinuationAt machine root rightSpine parent
      (runPrefix machine rightElapsed rightStart).state) :
    PairedContinuationOutcome machine root parent leftSpine rightSpine
      (runPrefix machine leftElapsed leftStart).state
      (runPrefix machine rightElapsed rightStart).state := by
  apply paired_activation_continuation_outcome hstartLow hleftStartStack hrightStartStack
    hleftStack hrightStack hleftProjection hrightProjection
  · exact runPrefix_preserves_external_inputs machine leftElapsed leftStart
  · exact runPrefix_preserves_external_inputs machine rightElapsed rightStart
  · exact hleftReachable
  · exact hrightReachable
  · exact hleftExecution.reached_active hleftElapsed
  · exact hrightExecution.reached_active hrightElapsed
  · exact hleftContinuation
  · exact hrightContinuation

/-- An ordinary matching continuation becomes a pair of reusable Public cut points exactly when
    its decoded occurrence is Public.  This premise is intentionally local and static; it is not
    inferred from projection equality or from the runtime payloads. -/
theorem MatchingCurrentContinuation.toVerifiedPublicCutPoints
    {machine : SemanticProgram} {root : UInt32} {parent : Nat} {left right : State}
    (hcurrent : MatchingCurrentContinuation machine root parent left right)
    (hparentPublic : ∀ instruction,
      machine.instructions[parent]? = some instruction → instruction.blockLabel = .pub) :
    PublicLowEquivalent machine left right ∧
      VerifiedPublicCutPoint machine root left ∧
      VerifiedPublicCutPoint machine root right := by
  obtain ⟨instruction, hleftLookup, hrightLookup⟩ := hcurrent.occurrence
  have hleftAtParent : machine.instructions[parent]? = some instruction := by
    rw [hcurrent.parent_eq_leftPc]
    exact hleftLookup
  have hpublic := hparentPublic instruction hleftAtParent
  refine ⟨hcurrent.low, ?_, ?_⟩
  · exact ⟨hcurrent.leftReachable, hcurrent.leftActive,
      ⟨instruction, hleftLookup, hpublic⟩⟩
  · exact ⟨hcurrent.rightReachable, hcurrent.rightActive,
      ⟨instruction, hrightLookup, hpublic⟩⟩

/-- Production-shaped disjunction: an actual Public parent yields matching reusable cut points;
    a synthetic parent yields the precise pre-completion evidence and is never reified as an
    instruction.  The `hparentPublic` premise is vacuous for synthetic vertices and is the exact
    verifier fact required in the ordinary case. -/
theorem paired_public_cutpoints_or_synthetic_return
    {machine : SemanticProgram} {root : UInt32} {parent : Nat}
    {leftStart rightStart left right : State} {leftSpine rightSpine : List CallFrame}
    (hstartLow : PublicLowEquivalent machine leftStart rightStart)
    (hleftStartStack : leftStart.callStack = leftSpine)
    (hrightStartStack : rightStart.callStack = rightSpine)
    (hleftStack : left.callStack = leftSpine)
    (hrightStack : right.callStack = rightSpine)
    (hleftProjection : publicProjection machine left = publicProjection machine leftStart)
    (hrightProjection : publicProjection machine right = publicProjection machine rightStart)
    (hleftStreams : left.externalInputs = leftStart.externalInputs)
    (hrightStreams : right.externalInputs = rightStart.externalInputs)
    (hleftReachable : ReachableFromRoot machine root left)
    (hrightReachable : ReachableFromRoot machine root right)
    (hleftActive : ActiveState machine root left)
    (hrightActive : ActiveState machine root right)
    (hleftContinuation : ActivationContinuationAt machine root leftSpine parent left)
    (hrightContinuation : ActivationContinuationAt machine root rightSpine parent right)
    (hparentPublic : ∀ instruction,
      machine.instructions[parent]? = some instruction → instruction.blockLabel = .pub) :
    (PublicLowEquivalent machine left right ∧
      VerifiedPublicCutPoint machine root left ∧
      VerifiedPublicCutPoint machine root right) ∨
      PairedSyntheticReturnContinuation machine root parent
        leftSpine rightSpine left right := by
  have houtcome := paired_activation_continuation_outcome hstartLow hleftStartStack
    hrightStartStack hleftStack hrightStack hleftProjection hrightProjection
    hleftStreams hrightStreams hleftReachable hrightReachable hleftActive hrightActive
    hleftContinuation hrightContinuation
  cases houtcome with
  | current hcurrent => exact Or.inl (hcurrent.toVerifiedPublicCutPoints hparentPublic)
  | synthetic hsynthetic => exact Or.inr hsynthetic

/-- Production wrapper combining two independently sized successful private prefixes. -/
theorem paired_runPrefix_public_cutpoints_or_synthetic_return
    {machine : SemanticProgram} {root : UInt32} {parent : Nat}
    {leftSteps rightSteps leftElapsed rightElapsed : Nat}
    {leftStart rightStart : State} {leftResult rightResult : StepResult}
    {leftSpine rightSpine : List CallFrame}
    (hstartLow : PublicLowEquivalent machine leftStart rightStart)
    (hleftStartStack : leftStart.callStack = leftSpine)
    (hrightStartStack : rightStart.callStack = rightSpine)
    (hleftExecution : SuccessfulExecution machine root leftSteps leftStart leftResult)
    (hrightExecution : SuccessfulExecution machine root rightSteps rightStart rightResult)
    (hleftElapsed : leftElapsed < leftSteps) (hrightElapsed : rightElapsed < rightSteps)
    (hleftReachable : ReachableFromRoot machine root
      (runPrefix machine leftElapsed leftStart).state)
    (hrightReachable : ReachableFromRoot machine root
      (runPrefix machine rightElapsed rightStart).state)
    (hleftStack : (runPrefix machine leftElapsed leftStart).state.callStack = leftSpine)
    (hrightStack : (runPrefix machine rightElapsed rightStart).state.callStack = rightSpine)
    (hleftProjection : publicProjection machine
        (runPrefix machine leftElapsed leftStart).state = publicProjection machine leftStart)
    (hrightProjection : publicProjection machine
        (runPrefix machine rightElapsed rightStart).state = publicProjection machine rightStart)
    (hleftContinuation : ActivationContinuationAt machine root leftSpine parent
      (runPrefix machine leftElapsed leftStart).state)
    (hrightContinuation : ActivationContinuationAt machine root rightSpine parent
      (runPrefix machine rightElapsed rightStart).state)
    (hparentPublic : ∀ instruction,
      machine.instructions[parent]? = some instruction → instruction.blockLabel = .pub) :
    (PublicLowEquivalent machine
        (runPrefix machine leftElapsed leftStart).state
        (runPrefix machine rightElapsed rightStart).state ∧
      VerifiedPublicCutPoint machine root
        (runPrefix machine leftElapsed leftStart).state ∧
      VerifiedPublicCutPoint machine root
        (runPrefix machine rightElapsed rightStart).state) ∨
      PairedSyntheticReturnContinuation machine root parent leftSpine rightSpine
        (runPrefix machine leftElapsed leftStart).state
        (runPrefix machine rightElapsed rightStart).state := by
  have houtcome := paired_runPrefix_activation_continuation_outcome hstartLow
    hleftStartStack hrightStartStack hleftExecution hrightExecution hleftElapsed
    hrightElapsed hleftReachable hrightReachable hleftStack hrightStack hleftProjection
    hrightProjection hleftContinuation hrightContinuation
  cases houtcome with
  | current hcurrent => exact Or.inl (hcurrent.toVerifiedPublicCutPoints hparentPublic)
  | synthetic hsynthetic => exact Or.inr hsynthetic

end LambdaSigil.Combined.V9.PublicContinuationSecurity
