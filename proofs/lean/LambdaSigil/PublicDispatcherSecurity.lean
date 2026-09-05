import LambdaSigil.PublicSameControlProgressSecurity
import LambdaSigil.PublicReleaseProgressSecurity

/-!
# Constructor-complete Public dispatcher shell

This module isolates the finite case split over the raw semantic instruction vocabulary.  Only
two cases require structured multi-step reasoning and remain callbacks: conditional controllers
and call/closure entry.  Every other constructor is discharged here by the verified same-control
or release packages.  The callbacks return actual `PublicExecutionProgress`; they are not policy
assumptions and never appear in the production theorem signature.
-/

namespace LambdaSigil.Combined.V9.PublicDispatcherSecurity

open Semantic OccurrenceDataflowInvocation OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity Semantic.PublicReleaseSynchronization
open PublicExecutionSecurity PublicSameControlProgressSecurity
open PublicReleaseProgressSecurity

/-- Once the verifier-derived controller and invocation layers provide their two structured
    cases, the decoded semantic operation split is exhaustive.  Flat dispatch has one fixed
    target and therefore stays in the ordinary same-control lane. -/
theorem publicExecutionProgress_of_structured_callbacks
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {leftTail rightTail : Nat} {left right : State}
    {leftResult rightResult : StepResult} {instruction : Instruction}
    (hleftSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root left)
    (hrightSync : VerifiedSynchronizationPoint (rawSemanticProgram program analysis) root right)
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hleftExecution : SuccessfulExecution (rawSemanticProgram program analysis) root
      (leftTail + 1) left leftResult)
    (hrightExecution : SuccessfulExecution (rawSemanticProgram program analysis) root
      (rightTail + 1) right rightResult)
    (hrelease : publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (leftTail + 1) left).events =
      publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (rightTail + 1) right).events)
    (hcontroller :
      (instruction.op = .branch ∨ instruction.op = .loop ∨
        instruction.op = .range ∨
        (instruction.op = .dispatch ∧ instruction.operandCount ≠ 2)) →
      PublicExecutionProgress (rawSemanticProgram program analysis) root
        (leftTail + 1) left (rightTail + 1) right)
    (hinvocation : (instruction.op = .call ∨ instruction.op = .closure) →
      PublicExecutionProgress (rawSemanticProgram program analysis) root
        (leftTail + 1) left (rightTail + 1) right) :
    PublicExecutionProgress (rawSemanticProgram program analysis) root
      (leftTail + 1) left (rightTail + 1) right := by
  let machine := rawSemanticProgram program analysis
  have ordinary
      (hnotCall : instruction.op ≠ .call)
      (hnotClosure : instruction.op ≠ .closure)
      (hnotRelease : instruction.op ≠ .release)
      (hnotReleaseCT : instruction.op ≠ .releaseCT)
      (hnextPc : nextPc machine left instruction (operandValue machine left instruction) =
        nextPc machine right instruction (operandValue machine right instruction)) :
      PublicExecutionProgress machine root
        (leftTail + 1) left (rightTail + 1) right := by
    apply publicExecutionProgress_of_verified_same_control_noncall_step
      hverified hanalysis hleftSync hrightSync hlow hlookup hnotCall hnotClosure
      hnotRelease hnotReleaseCT
    · simpa [machine] using hnextPc
    · intro hclosure
      exact False.elim (hnotClosure hclosure)
    · exact hleftExecution
    · exact hrightExecution
    · exact hrelease
  generalize hop : instruction.op = operation
  cases operation
  case branch => exact hcontroller (Or.inl hop)
  case loop => exact hcontroller (Or.inr (Or.inl hop))
  case range => exact hcontroller (Or.inr (Or.inr (Or.inl hop)))
  case dispatch =>
    by_cases hflat : instruction.operandCount = 2
    · apply ordinary (by simp [hop]) (by simp [hop]) (by simp [hop]) (by simp [hop])
      simp [machine, nextPc, hop, hflat, hlow.1]
    · exact hcontroller (Or.inr (Or.inr (Or.inr ⟨hop, hflat⟩)))
  case call => exact hinvocation (Or.inl hop)
  case closure => exact hinvocation (Or.inr hop)
  case release =>
    exact publicExecutionProgress_of_verified_release_step hverified hanalysis
      hleftSync hrightSync hlow hlookup (Or.inl hop) hleftExecution hrightExecution hrelease
  case releaseCT =>
    exact publicExecutionProgress_of_verified_release_step hverified hanalysis
      hleftSync hrightSync hlow hlookup (Or.inr hop) hleftExecution hrightExecution hrelease
  all_goals
    apply ordinary (by simp [hop]) (by simp [hop]) (by simp [hop]) (by simp [hop])
    simp [machine, nextPc, hop, hlow.1]

end LambdaSigil.Combined.V9.PublicDispatcherSecurity
