import LambdaSigil.PublicLocalSecurity
import LambdaSigil.PublicTraceSecurity
import LambdaSigil.PublicMatchingSecurity
import LambdaSigil.PublicRegionConvergence
import LambdaSigil.PublicReleaseSynchronization
import LambdaSigil.PublicPrivateSegmentSecurity
import LambdaSigil.PublicStepClassification

/-!
# Production Public execution composition

This file is the final composition boundary for the CSIR v9 Public result.  It deliberately
separates two obligations:

* `FinitePublicAlignment` is an internal derivation over actual raw steps; it is never accepted
  from a theorem caller by a production claim.
* once that derivation exists, the complete final Public projection and ordered Public
  output/boundary trace follow without an equal-fuel premise or an alternate execution model.

The verifier-derived construction of the alignment is kept below the reduction lemmas.  Keeping
the reduction explicit prevents a future proof from weakening the conclusion to exported return
values or from replacing either execution by a sanitized trace.
-/

namespace LambdaSigil.Combined.V9.PublicExecutionSecurity

open Semantic OccurrenceDataflowInvocation OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity Semantic.PublicWeakAlignment
open Semantic.PublicReleaseSynchronization Semantic.PublicRegionConvergence
open PublicLocalSecurity PublicTraceSecurity PublicMatchingSecurity
open PublicPrivateSegmentSecurity
open PublicStepClassification

/-- The complete Public observation promised by the production theorem.  It contains every
    statically Public scalar and aggregate cell, Public actor state, Public-site input cursors,
    and the ordered output/boundary trace with stable sites and optional payloads. -/
structure PublicExecutionConclusion (machine : SemanticProgram)
    (left right : StepResult) : Prop where
  projection : publicProjection machine left.state = publicProjection machine right.state
  boundaryTrace : publicBoundaryTrace left.events = publicBoundaryTrace right.events

/-- Generic raw alignment closes the complete result contract.  This lemma has no verifier or
    release premise because those are used to *construct* the alignment, not to read its result.
    It is intentionally not a production-facing claim. -/
theorem publicExecutionConclusion_of_alignment {machine : SemanticProgram}
    {leftFuel rightFuel : Nat} {left right : State}
    (halignment : FinitePublicAlignment machine leftFuel left rightFuel right) :
    PublicExecutionConclusion machine (runPrefix machine leftFuel left)
      (runPrefix machine rightFuel right) := by
  exact ⟨halignment.result.1, halignment.result.2⟩

/-- Padding a genuine completion to its independently chosen budget does not alter the state or
    trace consumed by the composition layer. -/
theorem publicExecutionConclusion_of_successful_alignment {machine : SemanticProgram}
    {root : UInt32} {leftFuel rightFuel : Nat} {left right : State}
    {leftResult rightResult : StepResult}
    (hleft : SuccessfulRun machine root leftFuel left leftResult)
    (hright : SuccessfulRun machine root rightFuel right rightResult)
    (halignment : FinitePublicAlignment machine leftFuel left rightFuel right) :
    PublicExecutionConclusion machine leftResult rightResult := by
  rw [← hleft.runPrefix_eq, ← hright.runPrefix_eq]
  exact publicExecutionConclusion_of_alignment halignment

/-- Complete release equality supplies the exact Public-release subsequence used while deriving
    a finite alignment.  In particular, occurrence count, site, stage, order, and payload are all
    retained; no per-step release equality or first-release cutoff is introduced. -/
theorem public_release_alignment_of_complete_runs {machine : SemanticProgram}
    {leftFuel rightFuel : Nat} {left right : State}
    (hrelease : ReleaseSynchronization.releaseTrace
        (runPrefix machine leftFuel left).events =
      ReleaseSynchronization.releaseTrace (runPrefix machine rightFuel right).events) :
    publicReleaseTrace machine (runPrefix machine leftFuel left).events =
      publicReleaseTrace machine (runPrefix machine rightFuel right).events :=
  run_complete_release_equality_implies_public_release_equality machine hrelease

/-- Extract the unique production judgment and the static facts for the exact occurrence-aware
    machine named by the caller's successful analysis equation. -/
theorem accepted_machine_facts {program : V9.Program} {analysis : Analysis}
    (hverified : OccurrenceKernel.verifyProgram program = none)
    (hanalysis : analyze? program = some analysis) :
    V9OccurrenceJudgment program ∧
      Semantic.OperationalStaticSafe (rawSemanticProgram program analysis) ∧
      OccurrencePolicyJudgment program analysis := by
  have hjudgment := v9_occurrence_verifier_sound hverified
  exact ⟨hjudgment, raw_semantic_program_static_safe_of_judgment hjudgment hanalysis,
    (analyzed_policy_of_judgment hjudgment hanalysis).2⟩

/-- Stable instruction identifiers make the occurrence classifier used by the filtered release
    trace agree with the exact instruction currently executing.  This is a production decoder
    fact, not a caller-provided site annotation. -/
theorem releaseSiteOccurrence_eq_blockLabel_of_raw_lookup
    {program : V9.Program} {analysis : Analysis}
    (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction) :
    releaseSiteOccurrence (rawSemanticProgram program analysis) instruction.id =
      instruction.blockLabel := by
  let machine := rawSemanticProgram program analysis
  have hnodup := rawSemanticProgram_instruction_ids_nodup hanalysis
  change machine.instructions[pc]? = some instruction at hlookup
  change (machine.instructions.toList.map Instruction.id).Nodup at hnodup
  have hcurrentMem : instruction ∈ machine.instructions :=
    Array.mem_iff_getElem?.mpr ⟨pc, hlookup⟩
  unfold releaseSiteOccurrence
  cases hfind : machine.instructions.find?
      (fun candidate => candidate.id == instruction.id) with
  | none =>
      exact False.elim ((Array.find?_eq_none.mp hfind) instruction hcurrentMem (by simp))
  | some found =>
      have hfoundMem : found ∈ machine.instructions := Array.mem_of_find?_eq_some hfind
      have hfoundIdB := @Array.find?_some Instruction
        (fun candidate => candidate.id == instruction.id) found machine.instructions hfind
      have hfoundId : found.id = instruction.id := beq_iff_eq.mp hfoundIdB
      obtain ⟨foundPc, hfoundBound, hfoundGet⟩ := Array.mem_iff_getElem.mp hfoundMem
      obtain ⟨hcurrentBound, hcurrentGet⟩ := Array.getElem?_eq_some_iff.mp hlookup
      have hfoundListBound : foundPc < machine.instructions.toList.length := by
        simpa using hfoundBound
      have hcurrentListBound : pc < machine.instructions.toList.length := by
        simpa using hcurrentBound
      have hfoundMapBound : foundPc <
          (machine.instructions.toList.map Instruction.id).length := by
        simpa using hfoundListBound
      have hcurrentMapBound : pc <
          (machine.instructions.toList.map Instruction.id).length := by
        simpa using hcurrentListBound
      have hposition : foundPc = pc := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have hpair := (List.pairwise_iff_getElem.mp
              (List.nodup_iff_pairwise_ne.mp hnodup)) foundPc pc
              hfoundMapBound hcurrentMapBound hlt
          apply hpair
          simp only [List.getElem_map]
          simpa [hfoundGet, hcurrentGet] using hfoundId
        · have hpair := (List.pairwise_iff_getElem.mp
              (List.nodup_iff_pairwise_ne.mp hnodup)) pc foundPc
              hcurrentMapBound hfoundMapBound hgt
          apply hpair
          simp only [List.getElem_map]
          simpa [hfoundGet, hcurrentGet] using hfoundId.symm
      subst foundPc
      have heq : found = instruction := by simpa [hcurrentGet] using hfoundGet.symm
      exact congrArg Instruction.blockLabel heq

/-- An active verified cut point rules out the `alreadyCompleted` constructor.  Hence every
    successful theorem input contains an exact positive execution length below its independently
    selected budget.  This is the well-founded measure used by the alignment construction. -/
theorem successfulRun_at_active_cut_is_exact {machine : SemanticProgram} {root : UInt32}
    {budget : Nat} {start : State} {result : StepResult}
    (hcut : VerifiedPublicCutPoint machine root start)
    (hrun : SuccessfulRun machine root budget start result) :
    ∃ steps, steps ≤ budget ∧ SuccessfulExecution machine root steps start result := by
  cases hrun with
  | completes hwithin hexecution => exact ⟨_, hwithin, hexecution⟩
  | alreadyCompleted hprovenance =>
      obtain ⟨_, _, _, hexecution⟩ := hprovenance
      have hhalted := hexecution.halted
      rw [hcut.active.notHalted] at hhalted
      cases hhalted

/-- Exact executions identify the result at every padded budget without changing either trace.
    This small normalization lemma avoids accidentally inducting on unused fuel. -/
theorem successfulRun_exact_result {machine : SemanticProgram} {root : UInt32}
    {budget steps : Nat} {start : State} {result : StepResult}
    (hrun : SuccessfulRun machine root budget start result)
    (hexecution : SuccessfulExecution machine root steps start result) :
    runPrefix machine steps start = runPrefix machine budget start := by
  rw [hexecution.run, hrun.runPrefix_eq]

/-! ## Exact private-segment composition

These records do not certify that a segment is private.  They record the concrete local
consequences that the verifier/region lemmas must establish at every actual raw step.  In
particular they contain neither a replacement trace nor any equality about the other run.
-/

/-- A concrete independently sized segment that is Public-boundary-silent and restores the
    complete Public projection at its real endpoint. -/
structure PublicSilentSegment (machine : SemanticProgram) (length : Nat)
    (start finish : State) : Prop where
  finish_eq : (runPrefix machine length start).state = finish
  silent : ∀ elapsed, elapsed < length →
    publicBoundaryTrace
        (step machine (runPrefix machine elapsed start).state).events = []
  /-- Private call entry may temporarily overwrite globally reused Public parameter cells.  The
      verifier-derived frame proof restores those cells when the private activation returns, so
      only the two real segment endpoints are equal in the raw Public projection. -/
  endProjection : publicProjection machine finish = publicProjection machine start

/-- During a private activation, raw parameter cells may temporarily occupy globally reused
    Public slots.  `prefixAt` is proof-only stack bookkeeping recovered from actual call frames;
    restoring it exposes the invariant caller view.  Empty prefixes at both endpoints turn this
    frame-aware invariant into a `PublicSilentSegment`. -/
structure PrefixRestoredSilentSegment (machine : SemanticProgram) (length : Nat)
    (start finish : State) : Type where
  prefixAt : Nat → List CallFrame
  prefixStart : prefixAt 0 = []
  prefixFinish : prefixAt length = []
  finish_eq : (runPrefix machine length start).state = finish
  restoredProjection : ∀ elapsed, elapsed ≤ length →
    publicProjection machine
        (restoreFrameStack (runPrefix machine elapsed start).state (prefixAt elapsed)) =
      publicProjection machine start
  silent : ∀ elapsed, elapsed < length →
    publicBoundaryTrace
        (step machine (runPrefix machine elapsed start).state).events = []

theorem PrefixRestoredSilentSegment.toPublicSilent {machine : SemanticProgram} {length : Nat}
    {start finish : State}
    (segment : PrefixRestoredSilentSegment machine length start finish) :
    PublicSilentSegment machine length start finish := by
  refine ⟨segment.finish_eq, segment.silent, ?_⟩
  have hend := segment.restoredProjection length le_rfl
  rw [segment.prefixFinish] at hend
  simp only [restoreFrameStack] at hend
  simpa only [segment.finish_eq] using hend

/-- Public-release silence is kept separate from boundary silence.  Private regions may execute
    real releases in the complete trace; composition proves, occurrence by occurrence, which of
    those releases are outside the Public subsequence. -/
def PublicReleaseSilentSegment (machine : SemanticProgram) (length : Nat)
    (start : State) : Prop :=
  ∀ elapsed, elapsed < length →
    publicReleaseTrace machine
      (step machine (runPrefix machine elapsed start).state).events = []

theorem publicReleaseTrace_eq_nil_of_silentSegment {machine : SemanticProgram} {length : Nat}
    {start : State} (hsilent : PublicReleaseSilentSegment machine length start) :
    publicReleaseTrace machine (runPrefix machine length start).events = [] := by
  have aux : ∀ (n : Nat) (state : State),
      (∀ elapsed, elapsed < n →
        publicReleaseTrace machine
            (step machine (runPrefix machine elapsed state).state).events = []) →
      publicReleaseTrace machine (runPrefix machine n state).events = [] := by
    intro n
    induction n with
    | zero => intro state _; rfl
    | succ n ih =>
        intro state hsilent
        have hhead := hsilent 0 (by omega)
        have htail : ∀ elapsed, elapsed < n →
            publicReleaseTrace machine
                (step machine
                  (runPrefix machine elapsed (step machine state).state).state).events = [] := by
          intro elapsed helapsed
          simpa only [runPrefix] using hsilent (elapsed + 1) (by omega)
        simp only [runPrefix] at hhead ⊢
        rw [publicReleaseTrace_append, hhead, List.nil_append,
          ih (step machine state).state htail]
  exact aux length start hsilent

/-- The flattened ordered Public boundary trace of a silent segment is empty. -/
theorem PublicSilentSegment.boundaryTrace_eq_nil {machine : SemanticProgram} {length : Nat}
    {start finish : State} (segment : PublicSilentSegment machine length start finish) :
    publicBoundaryTrace (runPrefix machine length start).events = [] := by
  have aux : ∀ (n : Nat) (state : State),
      (∀ elapsed, elapsed < n →
        publicBoundaryTrace
            (step machine (runPrefix machine elapsed state).state).events = []) →
      publicBoundaryTrace (runPrefix machine n state).events = [] := by
    intro n
    induction n with
    | zero => intro state _; rfl
    | succ n ih =>
        intro state hsilent
        have hhead := hsilent 0 (by omega)
        have htail : ∀ elapsed, elapsed < n →
            publicBoundaryTrace
                (step machine
                  (runPrefix machine elapsed (step machine state).state).state).events = [] := by
          intro elapsed helapsed
          simpa only [runPrefix] using hsilent (elapsed + 1) (by omega)
        simp only [runPrefix] at hhead ⊢
        rw [publicBoundaryTrace_append, hhead, List.nil_append,
          ih (step machine state).state htail]
  exact aux length start segment.silent

theorem PublicSilentSegment.end_projection {machine : SemanticProgram} {length : Nat}
    {start finish : State} (segment : PublicSilentSegment machine length start finish) :
    publicProjection machine finish = publicProjection machine start :=
  segment.endProjection

@[simp] theorem publicSilentSegment_zero (machine : SemanticProgram) (state : State) :
    PublicSilentSegment machine 0 state state := by
  exact ⟨rfl, by omega, rfl⟩

/-- A genuine raw step with no Public boundary observation is the smallest silent
    segment.  Endpoint projection preservation remains explicit because call entry need not have
    it until the matching return is included in a larger segment. -/
theorem publicSilentSegment_one {machine : SemanticProgram} {start : State}
    (hboundary : publicBoundaryTrace (step machine start).events = [])
    (hprojection : publicProjection machine (step machine start).state =
      publicProjection machine start) :
    PublicSilentSegment machine 1 start (step machine start).state := by
  refine ⟨by simp [runPrefix], ?_, hprojection⟩
  · intro elapsed helapsed
    have : elapsed = 0 := by omega
    subst elapsed
    simpa only [runPrefix] using hboundary

/-- Concatenation is over the real `runPrefix` state, not a summarized transition. -/
theorem PublicSilentSegment.append {machine : SemanticProgram}
    {firstLength secondLength : Nat} {start middle finish : State}
    (first : PublicSilentSegment machine firstLength start middle)
    (second : PublicSilentSegment machine secondLength middle finish) :
    PublicSilentSegment machine (firstLength + secondLength) start finish := by
  refine ⟨?_, ?_, second.endProjection.trans first.endProjection⟩
  · rw [ReleaseSynchronization.runPrefix_add]
    simpa only [first.finish_eq] using second.finish_eq
  · intro elapsed helapsed
    by_cases hfirst : elapsed < firstLength
    · exact first.silent elapsed hfirst
    · have hsecond : elapsed - firstLength < secondLength := by omega
      have hstate := congrArg StepResult.state
        (ReleaseSynchronization.runPrefix_add machine firstLength
          (elapsed - firstLength) start)
      have hsum : firstLength + (elapsed - firstLength) = elapsed := by omega
      rw [hsum] at hstate
      dsimp only at hstate
      rw [first.finish_eq] at hstate
      rw [hstate]
      exact second.silent (elapsed - firstLength) hsecond

/-- A verified private segment is exactly a finite chain of `silentLeft` constructors. -/
theorem PublicSilentSegment.prependLeft {machine : SemanticProgram} {length leftTail rightFuel : Nat}
    {start finish right : State} (segment : PublicSilentSegment machine length start finish)
    (tail : FinitePublicAlignment machine leftTail finish rightFuel right) :
    FinitePublicAlignment machine (length + leftTail) start rightFuel right := by
  apply FinitePublicAlignment.prependSilentLeft segment.silent
  simpa only [segment.finish_eq] using tail

/-- Symmetric conversion for the independently sized right segment. -/
theorem PublicSilentSegment.prependRight {machine : SemanticProgram}
    {length leftFuel rightTail : Nat} {left start finish : State}
    (segment : PublicSilentSegment machine length start finish)
    (tail : FinitePublicAlignment machine leftFuel left rightTail finish) :
    FinitePublicAlignment machine leftFuel left (length + rightTail) start := by
  apply FinitePublicAlignment.prependSilentRight segment.silent
  simpa only [segment.finish_eq] using tail

/-- Two independently long private regions may be composed in either order.  The final alignment
    begins at their real starting states; no common region fuel appears in the type. -/
theorem prepend_private_regions {machine : SemanticProgram}
    {leftLength rightLength leftTail rightTail : Nat}
    {leftStart leftFinish rightStart rightFinish : State}
    (leftSegment : PublicSilentSegment machine leftLength leftStart leftFinish)
    (rightSegment : PublicSilentSegment machine rightLength rightStart rightFinish)
    (tail : FinitePublicAlignment machine leftTail leftFinish rightTail rightFinish) :
    FinitePublicAlignment machine (leftLength + leftTail) leftStart
      (rightLength + rightTail) rightStart := by
  exact leftSegment.prependLeft (rightSegment.prependRight tail)

/-- Paired form used when a private structured region contains explicit downgrades.  Neither
    endpoint is required to equal its own start: an actual release may update Public storage.
    Instead, equality is established between the two real endpoints from the synchronized raw
    release occurrences.  The record contains no future observation and cannot inject a payload
    into either execution. -/
structure PairedPublicSilentSegments (machine : SemanticProgram)
    (leftLength rightLength : Nat) (leftStart rightStart leftFinish rightFinish : State) : Prop
    where
  leftFinish_eq : (runPrefix machine leftLength leftStart).state = leftFinish
  rightFinish_eq : (runPrefix machine rightLength rightStart).state = rightFinish
  leftSilent : ∀ elapsed, elapsed < leftLength →
    publicBoundaryTrace
        (step machine (runPrefix machine elapsed leftStart).state).events = []
  rightSilent : ∀ elapsed, elapsed < rightLength →
    publicBoundaryTrace
        (step machine (runPrefix machine elapsed rightStart).state).events = []
  endpointProjection : publicProjection machine leftFinish =
    publicProjection machine rightFinish

/-- Paired private segments prepend directly to a tail alignment.  This is strictly more general
    than two unary `PublicSilentSegment`s and is the correct algebra for regions containing legal
    releases: only the paired endpoint projection is claimed. -/
theorem PairedPublicSilentSegments.prepend {machine : SemanticProgram}
    {leftLength rightLength leftTail rightTail : Nat}
    {leftStart rightStart leftFinish rightFinish : State}
    (segments : PairedPublicSilentSegments machine leftLength rightLength
      leftStart rightStart leftFinish rightFinish)
    (tail : FinitePublicAlignment machine leftTail leftFinish rightTail rightFinish) :
    FinitePublicAlignment machine (leftLength + leftTail) leftStart
      (rightLength + rightTail) rightStart := by
  apply FinitePublicAlignment.prependSilentLeft segments.leftSilent
  rw [segments.leftFinish_eq]
  apply FinitePublicAlignment.prependSilentRight segments.rightSilent
  simpa only [segments.rightFinish_eq] using tail

/-- If paired private segments consume both successful executions completely, their synchronized
    endpoint projection closes the weak alignment without manufacturing a reusable intermediate
    cut point.  This handles the honest case where release occurrences on one path do not align
    with a particular region boundary on the other path. -/
theorem PairedPublicSilentSegments.complete {machine : SemanticProgram} {root : UInt32}
    {leftLength rightLength : Nat} {leftStart rightStart : State}
    {leftResult rightResult : StepResult}
    (segments : PairedPublicSilentSegments machine leftLength rightLength
      leftStart rightStart leftResult.state rightResult.state)
    (hleft : SuccessfulExecution machine root leftLength leftStart leftResult)
    (hright : SuccessfulExecution machine root rightLength rightStart rightResult) :
    FinitePublicAlignment machine leftLength leftStart rightLength rightStart := by
  have hterminal : FinitePublicAlignment machine 0 leftResult.state 0 rightResult.state :=
    .terminal (Or.inl hleft.halted) (Or.inl hright.halted) segments.endpointProjection
  simpa only [Nat.add_zero] using segments.prepend hterminal

/-- Removing two independently long Public-silent prefixes preserves equality of the remaining
    Public-release suffixes once their separately proved occurrence filters are empty.  The proof
    uses events produced by `runPrefix`; a boundary-silent segment cannot claim release silence. -/
theorem public_release_suffix_eq_after_private_regions {machine : SemanticProgram}
    {leftLength rightLength leftTail rightTail : Nat}
    {leftStart leftFinish rightStart rightFinish : State}
    (leftSegment : PublicSilentSegment machine leftLength leftStart leftFinish)
    (rightSegment : PublicSilentSegment machine rightLength rightStart rightFinish)
    (leftReleaseSilent : PublicReleaseSilentSegment machine leftLength leftStart)
    (rightReleaseSilent : PublicReleaseSilentSegment machine rightLength rightStart)
    (hrelease : publicReleaseTrace machine
        (runPrefix machine (leftLength + leftTail) leftStart).events =
      publicReleaseTrace machine
        (runPrefix machine (rightLength + rightTail) rightStart).events) :
    publicReleaseTrace machine (runPrefix machine leftTail leftFinish).events =
      publicReleaseTrace machine (runPrefix machine rightTail rightFinish).events := by
  rw [ReleaseSynchronization.runPrefix_add, ReleaseSynchronization.runPrefix_add,
    publicReleaseTrace_append, publicReleaseTrace_append,
    publicReleaseTrace_eq_nil_of_silentSegment leftReleaseSilent,
    publicReleaseTrace_eq_nil_of_silentSegment rightReleaseSilent,
    List.nil_append, List.nil_append] at hrelease
  simpa only [leftSegment.finish_eq, rightSegment.finish_eq] using hrelease

/-! ## Exact-execution alignment algebra -/

/-- Two genuine successful endpoints close an alignment once the complete projection has been
    related.  Successful executions end halted and nontrapped, so this cannot turn fuel exhaustion
    or a malformed fallthrough into the terminal case. -/
theorem terminal_alignment_of_successful_executions {machine : SemanticProgram} {root : UInt32}
    {leftSteps rightSteps : Nat} {left right : State} {leftResult rightResult : StepResult}
    (hleft : SuccessfulExecution machine root leftSteps left leftResult)
    (hright : SuccessfulExecution machine root rightSteps right rightResult)
    (hprojection : publicProjection machine leftResult.state =
      publicProjection machine rightResult.state) :
    FinitePublicAlignment machine 0 leftResult.state 0 rightResult.state := by
  exact .terminal (Or.inl hleft.halted) (Or.inl hright.halted) hprojection

/-- Prepending one real matched transition consumes one step on each independently sized exact
    execution.  The fuels need not be equal before or after this constructor. -/
theorem prepend_matching_step {machine : SemanticProgram}
    {leftTail rightTail : Nat} {left right : State}
    (hobservation : publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events)
    (tail : FinitePublicAlignment machine leftTail (step machine left).state
      rightTail (step machine right).state) :
    FinitePublicAlignment machine (leftTail + 1) left (rightTail + 1) right :=
  .matched hobservation tail

/-- Equal remaining Public-release traces can be advanced across a pair of matched raw steps.
    This is ordinary left cancellation on the actual event-derived trace, not a supplied release
    cursor. -/
theorem public_release_tail_eq_of_matching_heads {machine : SemanticProgram}
    {leftSteps rightSteps : Nat} {left right : State}
    (hcomplete : publicReleaseTrace machine
        (runPrefix machine (leftSteps + 1) left).events =
      publicReleaseTrace machine
        (runPrefix machine (rightSteps + 1) right).events)
    (hhead : publicReleaseTrace machine (step machine left).events =
      publicReleaseTrace machine (step machine right).events) :
    publicReleaseTrace machine
        (runPrefix machine leftSteps (step machine left).state).events =
      publicReleaseTrace machine
        (runPrefix machine rightSteps (step machine right).state).events := by
  simp only [runPrefix, publicReleaseTrace_append] at hcomplete
  rw [hhead] at hcomplete
  exact List.append_cancel_left hcomplete

/-- The production induction keeps the complete release trace, not merely its Public-site
    subsequence.  Advancing two raw steps with the same actual release head therefore preserves
    equality of every remaining occurrence, including releases executed under a private
    occurrence. -/
theorem complete_release_tail_eq_of_matching_heads {machine : SemanticProgram}
    {leftSteps rightSteps : Nat} {left right : State}
    (hcomplete : ReleaseSynchronization.releaseTrace
        (runPrefix machine (leftSteps + 1) left).events =
      ReleaseSynchronization.releaseTrace
        (runPrefix machine (rightSteps + 1) right).events)
    (hhead : ReleaseSynchronization.releaseTrace (step machine left).events =
      ReleaseSynchronization.releaseTrace (step machine right).events) :
    ReleaseSynchronization.releaseTrace
        (runPrefix machine leftSteps (step machine left).state).events =
      ReleaseSynchronization.releaseTrace
        (runPrefix machine rightSteps (step machine right).state).events := by
  simp only [runPrefix, ReleaseSynchronization.releaseTrace_append] at hcomplete
  rw [hhead] at hcomplete
  exact List.append_cancel_left hcomplete

/-- A Public release at the same decoded site and stage exposes equality of its real payload from
    equality of the complete remaining Public-release sequences.  Later occurrences remain in
    the list and therefore cannot be discarded after the first release. -/
theorem public_release_payload_and_tail_of_equal_runs {machine : SemanticProgram}
    {leftSteps rightSteps : Nat} {left right : State} {site : UInt32} {stage : UInt8}
    {leftPayload rightPayload : Int}
    (hleftHead : publicReleaseTrace machine (step machine left).events =
      [⟨site, stage, leftPayload⟩])
    (hrightHead : publicReleaseTrace machine (step machine right).events =
      [⟨site, stage, rightPayload⟩])
    (hcomplete : publicReleaseTrace machine
        (runPrefix machine (leftSteps + 1) left).events =
      publicReleaseTrace machine
        (runPrefix machine (rightSteps + 1) right).events) :
    leftPayload = rightPayload ∧
      publicReleaseTrace machine
          (runPrefix machine leftSteps (step machine left).state).events =
        publicReleaseTrace machine
          (runPrefix machine rightSteps (step machine right).state).events := by
  simp only [runPrefix, publicReleaseTrace_append, hleftHead, hrightHead,
    List.singleton_append] at hcomplete
  exact ⟨congrArg (fun observation => observation.payload) (List.cons.inj hcomplete).1,
    (List.cons.inj hcomplete).2⟩

/-- Complete release synchronization exposes the current raw downgrade payload and retains the
    entire later suffix.  This is the form needed inside private structured regions: those
    releases may be absent from `publicReleaseTrace`, but never from the theorem's complete
    release premise. -/
theorem complete_release_payload_and_tail_of_equal_runs {machine : SemanticProgram}
    {leftSteps rightSteps : Nat} {left right : State} {site : UInt32} {stage : UInt8}
    {leftPayload rightPayload : Int}
    (hleftHead : ReleaseSynchronization.releaseTrace (step machine left).events =
      [⟨site, stage, leftPayload⟩])
    (hrightHead : ReleaseSynchronization.releaseTrace (step machine right).events =
      [⟨site, stage, rightPayload⟩])
    (hcomplete : ReleaseSynchronization.releaseTrace
        (runPrefix machine (leftSteps + 1) left).events =
      ReleaseSynchronization.releaseTrace
        (runPrefix machine (rightSteps + 1) right).events) :
    leftPayload = rightPayload ∧
      ReleaseSynchronization.releaseTrace
          (runPrefix machine leftSteps (step machine left).state).events =
        ReleaseSynchronization.releaseTrace
          (runPrefix machine rightSteps (step machine right).state).events := by
  simp only [runPrefix, ReleaseSynchronization.releaseTrace_append, hleftHead, hrightHead,
    List.singleton_append] at hcomplete
  exact ⟨congrArg (fun observation => observation.payload) (List.cons.inj hcomplete).1,
    (List.cons.inj hcomplete).2⟩

/-- The complete release head of an actual live downgrade step is a singleton carrying the
    decoded site, the exact stage, and the unsanitized operand payload. -/
theorem complete_releaseTrace_step_release {machine : SemanticProgram} {state : State}
    {instruction : Instruction}
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hlive : state.halted = false ∧ state.trapped = false)
    (hop : instruction.op = .release) :
    ReleaseSynchronization.releaseTrace (step machine state).events =
      [⟨instruction.id, 1, (operandValue machine state instruction).payload⟩] := by
  simp [step, hlive.1, hlive.2, hlookup, hop, ordinaryStep, instructionEvents,
    ReleaseSynchronization.releaseTrace, Semantic.releaseEvents, EventKind.eqb,
    operandValue, headValue_payload]

theorem complete_releaseTrace_step_releaseCT {machine : SemanticProgram} {state : State}
    {instruction : Instruction}
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hlive : state.halted = false ∧ state.trapped = false)
    (hop : instruction.op = .releaseCT) :
    ReleaseSynchronization.releaseTrace (step machine state).events =
      [⟨instruction.id, 2, (operandValue machine state instruction).payload⟩] := by
  simp [step, hlive.1, hlive.2, hlookup, hop, ordinaryStep, instructionEvents,
    ReleaseSynchronization.releaseTrace, Semantic.releaseEvents, EventKind.eqb,
    operandValue, headValue_payload]

@[simp] private theorem completeReleaseTrace_eventsForValues_nonrelease
    (kind : EventKind) (site : UInt32) (values : List Value) (hkind : kind ≠ .release) :
    ReleaseSynchronization.releaseTrace (eventsForValues kind site values) = [] := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [eventsForValues, ReleaseSynchronization.releaseTrace, Semantic.releaseEvents,
        EventKind.eqb, hkind]

@[simp] private theorem completeReleaseTrace_eventsForValuesUnderPc_nonrelease
    (kind : EventKind) (site : UInt32) (pc : Label) (values : List Value)
    (hkind : kind ≠ .release) :
    ReleaseSynchronization.releaseTrace (eventsForValuesUnderPc kind site pc values) = [] := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [eventsForValuesUnderPc, ReleaseSynchronization.releaseTrace,
        Semantic.releaseEvents, EventKind.eqb, hkind]

@[simp] private theorem completeReleaseTrace_eventsForObserved_nonrelease
    (kind : EventKind) (site : UInt32) (values : List Value) (hkind : kind ≠ .release) :
    ReleaseSynchronization.releaseTrace (eventsForObserved kind site values) = [] := by
  by_cases hempty : values.isEmpty
  · simp [eventsForObserved, hempty, ReleaseSynchronization.releaseTrace,
      Semantic.releaseEvents, EventKind.eqb, hkind]
  · simpa [eventsForObserved, hempty] using
      completeReleaseTrace_eventsForValues_nonrelease kind site values hkind

@[simp] private theorem completeReleaseTrace_singleton_nonrelease (event : Event)
    (hkind : event.kind ≠ .release) :
    ReleaseSynchronization.releaseTrace [event] = [] := by
  simp [ReleaseSynchronization.releaseTrace, Semantic.releaseEvents, EventKind.eqb, hkind]

private theorem completeReleaseTrace_instruction_nonrelease (machine : SemanticProgram)
    (state : State) (instruction : Instruction)
    (hrelease : instruction.op ≠ .release) (hreleaseCT : instruction.op ≠ .releaseCT) :
    ReleaseSynchronization.releaseTrace (instructionEvents machine state instruction) = [] := by
  generalize hop : instruction.op = operation
  cases operation
  all_goals simp only [instructionEvents, hop]
  case release => exact (hrelease hop).elim
  case releaseCT => exact (hreleaseCT hop).elim
  all_goals first
    | rfl
    | apply completeReleaseTrace_eventsForValues_nonrelease; decide
    | apply completeReleaseTrace_eventsForValuesUnderPc_nonrelease; decide
    | apply completeReleaseTrace_eventsForObserved_nonrelease; decide

/-- Every non-downgrade raw step contributes no entry to the complete release trace, regardless
    of its other authority, flow, effect, control, trap, or boundary events. -/
theorem complete_releaseTrace_step_nonrelease {machine : SemanticProgram} {state : State}
    {instruction : Instruction}
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hrelease : instruction.op ≠ .release)
    (hreleaseCT : instruction.op ≠ .releaseCT) :
    ReleaseSynchronization.releaseTrace (step machine state).events = [] := by
  unfold step
  by_cases hdone : state.halted || state.trapped
  · simp [hdone, ReleaseSynchronization.releaseTrace, Semantic.releaseEvents]
  · rw [if_neg hdone, hlookup]
    generalize hop : instruction.op = operation
    cases operation
    all_goals simp only [hop]
    case call =>
      unfold callStep
      split
      · simp [ReleaseSynchronization.releaseTrace, Semantic.releaseEvents, EventKind.eqb]
      · dsimp only
        split
        · simp [ReleaseSynchronization.releaseTrace, Semantic.releaseEvents, EventKind.eqb]
        · rfl
    case closure =>
      unfold callStep
      split
      · simp [ReleaseSynchronization.releaseTrace, Semantic.releaseEvents, EventKind.eqb]
      · dsimp only
        split
        · simp [ReleaseSynchronization.releaseTrace, Semantic.releaseEvents, EventKind.eqb]
        · rfl
    case output =>
      cases state.callStack with
      | nil =>
          simpa using completeReleaseTrace_instruction_nonrelease machine state instruction
            hrelease hreleaseCT
      | cons frame rest =>
          simp only
          split <;>
            simp [ReleaseSynchronization.releaseTrace, Semantic.releaseEvents, EventKind.eqb]
    case release => exact (hrelease hop).elim
    case releaseCT => exact (hreleaseCT hop).elim
    case ffi =>
      exact completeReleaseTrace_instruction_nonrelease machine state instruction
        hrelease hreleaseCT
    case actorBoundary =>
      simpa using completeReleaseTrace_instruction_nonrelease machine state instruction
        hrelease hreleaseCT
    case effect =>
      exact completeReleaseTrace_instruction_nonrelease machine state instruction
        hrelease hreleaseCT
    case abortiveEffect =>
      simpa using completeReleaseTrace_instruction_nonrelease machine state instruction
        hrelease hreleaseCT
    case stateRead => rfl
    case stateWrite =>
      simpa using completeReleaseTrace_instruction_nonrelease machine state instruction
        hrelease hreleaseCT
    all_goals
      simpa [ordinaryStep] using completeReleaseTrace_instruction_nonrelease
        machine state instruction hrelease hreleaseCT

theorem complete_release_tail_of_shared_nonrelease {machine : SemanticProgram}
    {leftSteps rightSteps : Nat} {left right : State} {instruction : Instruction}
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hrelease : instruction.op ≠ .release)
    (hreleaseCT : instruction.op ≠ .releaseCT)
    (hcomplete : ReleaseSynchronization.releaseTrace
        (runPrefix machine (leftSteps + 1) left).events =
      ReleaseSynchronization.releaseTrace
        (runPrefix machine (rightSteps + 1) right).events) :
    ReleaseSynchronization.releaseTrace
        (runPrefix machine leftSteps (step machine left).state).events =
      ReleaseSynchronization.releaseTrace
        (runPrefix machine rightSteps (step machine right).state).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  apply complete_release_tail_eq_of_matching_heads hcomplete
  rw [complete_releaseTrace_step_nonrelease hlookup hrelease hreleaseCT,
    complete_releaseTrace_step_nonrelease hrightLookup hrelease hreleaseCT]

/-- Filtered Public-release synchronization advances over any shared non-downgrade step.  This
    is the invariant used by the independent-length induction after the theorem's complete raw
    release equality has been filtered once. -/
theorem public_release_tail_of_shared_nonrelease {machine : SemanticProgram}
    {leftSteps rightSteps : Nat} {left right : State} {instruction : Instruction}
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hrelease : instruction.op ≠ .release)
    (hreleaseCT : instruction.op ≠ .releaseCT)
    (hcomplete : publicReleaseTrace machine
        (runPrefix machine (leftSteps + 1) left).events =
      publicReleaseTrace machine
        (runPrefix machine (rightSteps + 1) right).events) :
    publicReleaseTrace machine
        (runPrefix machine leftSteps (step machine left).state).events =
      publicReleaseTrace machine
        (runPrefix machine rightSteps (step machine right).state).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  apply public_release_tail_eq_of_matching_heads hcomplete
  rw [publicReleaseTrace_step_nonrelease machine left instruction hlookup hrelease hreleaseCT,
    publicReleaseTrace_step_nonrelease machine right instruction hrightLookup hrelease hreleaseCT]

/-- At a shared decoded downgrade site, equality of the complete remaining release traces is
    sufficient to derive the current payload equality and the complete suffix invariant used by
    the recursive execution proof.  Later releases are not discarded. -/
theorem matching_release_of_complete_remaining_traces {machine : SemanticProgram}
    {leftSteps rightSteps : Nat} {left right : State} {instruction : Instruction}
    (hlow : PublicLowEquivalent machine left right)
    (hlookup : machine.instructions[left.pc]? = some instruction)
    (hoperation : instruction.op = .release ∨ instruction.op = .releaseCT)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hcomplete : ReleaseSynchronization.releaseTrace
        (runPrefix machine (leftSteps + 1) left).events =
      ReleaseSynchronization.releaseTrace
        (runPrefix machine (rightSteps + 1) right).events) :
    (PublicLowEquivalent machine (step machine left).state (step machine right).state ∧
      publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events) ∧
      ReleaseSynchronization.releaseTrace
          (runPrefix machine leftSteps (step machine left).state).events =
        ReleaseSynchronization.releaseTrace
          (runPrefix machine rightSteps (step machine right).state).events := by
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  rcases hoperation with hrelease | hreleaseCT
  · have hleftHead := complete_releaseTrace_step_release hlookup hleftLive hrelease
    have hrightHead := complete_releaseTrace_step_release hrightLookup hrightLive hrelease
    obtain ⟨hpayload, htail⟩ := complete_release_payload_and_tail_of_equal_runs
      hleftHead hrightHead hcomplete
    have hmatching := matching_release_step hlow hlookup (Or.inl hrelease)
      hleftLive hrightLive (by
        simpa [instructionPayload, hrelease, operandValue, headValue_payload] using hpayload)
    exact ⟨hmatching, htail⟩
  · have hleftHead := complete_releaseTrace_step_releaseCT hlookup hleftLive hreleaseCT
    have hrightHead := complete_releaseTrace_step_releaseCT hrightLookup hrightLive hreleaseCT
    obtain ⟨hpayload, htail⟩ := complete_release_payload_and_tail_of_equal_runs
      hleftHead hrightHead hcomplete
    have hmatching := matching_release_step hlow hlookup (Or.inr hreleaseCT)
      hleftLive hrightLive (by
        simpa [instructionPayload, hreleaseCT, operandValue, headValue_payload] using hpayload)
    exact ⟨hmatching, htail⟩

/-- The filtered Public-release head of a live downgrade at a verifier-Public site is the exact
    singleton emitted by the raw step. -/
theorem publicReleaseTrace_step_release_of_public
    {program : V9.Program} {analysis : Analysis}
    (hanalysis : analyze? program = some analysis)
    {state : State} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? = some instruction)
    (hlive : state.halted = false ∧ state.trapped = false)
    (hop : instruction.op = .release)
    (hpublic : instruction.blockLabel = .pub) :
    publicReleaseTrace (rawSemanticProgram program analysis)
        (step (rawSemanticProgram program analysis) state).events =
      [⟨instruction.id, 1,
        (operandValue (rawSemanticProgram program analysis) state instruction).payload⟩] := by
  have hsite : releaseSiteOccurrence (rawSemanticProgram program analysis) instruction.id =
      .pub := (releaseSiteOccurrence_eq_blockLabel_of_raw_lookup hanalysis hlookup).trans hpublic
  have hhead := publicReleaseTrace_instruction_release
    (rawSemanticProgram program analysis) state instruction hop hsite
  simpa [step, hlive.1, hlive.2, hlookup, hop, ordinaryStep] using hhead

theorem publicReleaseTrace_step_releaseCT_of_public
    {program : V9.Program} {analysis : Analysis}
    (hanalysis : analyze? program = some analysis)
    {state : State} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? = some instruction)
    (hlive : state.halted = false ∧ state.trapped = false)
    (hop : instruction.op = .releaseCT)
    (hpublic : instruction.blockLabel = .pub) :
    publicReleaseTrace (rawSemanticProgram program analysis)
        (step (rawSemanticProgram program analysis) state).events =
      [⟨instruction.id, 2,
        (operandValue (rawSemanticProgram program analysis) state instruction).payload⟩] := by
  have hsite : releaseSiteOccurrence (rawSemanticProgram program analysis) instruction.id =
      .pub := (releaseSiteOccurrence_eq_blockLabel_of_raw_lookup hanalysis hlookup).trans hpublic
  have hhead := publicReleaseTrace_instruction_releaseCT
    (rawSemanticProgram program analysis) state instruction hop hsite
  simpa [step, hlive.1, hlive.2, hlookup, hop, ordinaryStep] using hhead

/-- Public release synchronization is carried as a filtered suffix through the independent-length
    induction. Private downgrades are stuttering projection-preserving steps; only a downgrade at
    the current Public site consumes the next release occurrence here. -/
theorem matching_public_release_of_remaining_traces
    {program : V9.Program} {analysis : Analysis}
    (hanalysis : analyze? program = some analysis)
    {leftSteps rightSteps : Nat} {left right : State} {instruction : Instruction}
    (hlow : PublicLowEquivalent (rawSemanticProgram program analysis) left right)
    (hlookup : (rawSemanticProgram program analysis).instructions[left.pc]? = some instruction)
    (hoperation : instruction.op = .release ∨ instruction.op = .releaseCT)
    (hpublic : instruction.blockLabel = .pub)
    (hleftLive : left.halted = false ∧ left.trapped = false)
    (hrightLive : right.halted = false ∧ right.trapped = false)
    (hremaining : publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (leftSteps + 1) left).events =
      publicReleaseTrace (rawSemanticProgram program analysis)
        (runPrefix (rawSemanticProgram program analysis) (rightSteps + 1) right).events) :
    (PublicLowEquivalent (rawSemanticProgram program analysis)
        (step (rawSemanticProgram program analysis) left).state
        (step (rawSemanticProgram program analysis) right).state ∧
      publicBoundaryTrace (step (rawSemanticProgram program analysis) left).events =
        publicBoundaryTrace (step (rawSemanticProgram program analysis) right).events) ∧
      publicReleaseTrace (rawSemanticProgram program analysis)
          (runPrefix (rawSemanticProgram program analysis) leftSteps
            (step (rawSemanticProgram program analysis) left).state).events =
        publicReleaseTrace (rawSemanticProgram program analysis)
          (runPrefix (rawSemanticProgram program analysis) rightSteps
            (step (rawSemanticProgram program analysis) right).state).events := by
  let machine := rawSemanticProgram program analysis
  have hrightLookup : machine.instructions[right.pc]? = some instruction := by
    rw [← hlow.1]
    exact hlookup
  rcases hoperation with hrelease | hreleaseCT
  · have hleftHead := publicReleaseTrace_step_release_of_public hanalysis
      hlookup hleftLive hrelease hpublic
    have hrightHead := publicReleaseTrace_step_release_of_public hanalysis
      hrightLookup hrightLive hrelease hpublic
    obtain ⟨hpayload, htail⟩ := public_release_payload_and_tail_of_equal_runs
      hleftHead hrightHead hremaining
    have hmatching := matching_release_step hlow hlookup (Or.inl hrelease)
      hleftLive hrightLive (by
        simpa [instructionPayload, hrelease, operandValue, headValue_payload] using hpayload)
    exact ⟨hmatching, htail⟩
  · have hleftHead := publicReleaseTrace_step_releaseCT_of_public hanalysis
      hlookup hleftLive hreleaseCT hpublic
    have hrightHead := publicReleaseTrace_step_releaseCT_of_public hanalysis
      hrightLookup hrightLive hreleaseCT hpublic
    obtain ⟨hpayload, htail⟩ := public_release_payload_and_tail_of_equal_runs
      hleftHead hrightHead hremaining
    have hmatching := matching_release_step hlow hlookup (Or.inr hreleaseCT)
      hleftLive hrightLive (by
        simpa [instructionPayload, hreleaseCT, operandValue, headValue_payload] using hpayload)
    exact ⟨hmatching, htail⟩

/-- A lockstep stretch is only a local composition device.  Its final projection premise is about
    the reached states, and each observation premise names an actual raw step; no future trace is
    embedded in `PublicLowEquivalent`. -/
theorem finitePublicAlignment_of_matching_prefix {machine : SemanticProgram} {length : Nat}
    {left right : State}
    (hobservation : ∀ elapsed, elapsed < length →
      publicBoundaryTrace
          (step machine (runPrefix machine elapsed left).state).events =
        publicBoundaryTrace
          (step machine (runPrefix machine elapsed right).state).events)
    (hprojection : publicProjection machine (runPrefix machine length left).state =
      publicProjection machine (runPrefix machine length right).state)
    (hstoppedLeft : (runPrefix machine length left).state.halted = true ∨
      (runPrefix machine length left).state.trapped = true)
    (hstoppedRight : (runPrefix machine length right).state.halted = true ∨
      (runPrefix machine length right).state.trapped = true) :
    FinitePublicAlignment machine length left length right := by
  induction length generalizing left right with
  | zero => exact .terminal hstoppedLeft hstoppedRight hprojection
  | succ length ih =>
      have hhead := hobservation 0 (by omega)
      have htailObservation : ∀ elapsed, elapsed < length →
          publicBoundaryTrace
              (step machine
                (runPrefix machine elapsed (step machine left).state).state).events =
            publicBoundaryTrace
              (step machine
                (runPrefix machine elapsed (step machine right).state).state).events := by
        intro elapsed helapsed
        simpa only [runPrefix] using hobservation (elapsed + 1) (by omega)
      have htail : FinitePublicAlignment machine length (step machine left).state
          length (step machine right).state := by
        apply ih htailObservation
        · simpa only [runPrefix] using hprojection
        · simpa only [runPrefix] using hstoppedLeft
        · simpa only [runPrefix] using hstoppedRight
      simpa only [Nat.succ_eq_add_one, runPrefix] using
        FinitePublicAlignment.matched hhead htail

/-- A successful execution decomposes at every positive first step into the raw successor and an
    exact successful suffix.  This is the recursion rule used by the production construction. -/
theorem successfulExecution_tail {machine : SemanticProgram} {root : UInt32}
    {steps : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution machine root (steps + 2) start result) :
    SuccessfulExecution machine root (steps + 1) (step machine start).state
      (runPrefix machine (steps + 1) (step machine start).state) := by
  have hdropped := hexecution.drop (elapsed := 1) (by omega)
  have hsteps : steps + 2 - 1 = steps + 1 := by omega
  have hrunPrefixOne : (runPrefix machine 1 start).state = (step machine start).state := by
    simp [runPrefix]
  rw [hsteps, hrunPrefixOne] at hdropped
  exact hdropped

/-- After a relationally matching first step, two genuine successful executions either both end
    on that step or both retain a positive genuine suffix.  One side cannot halt while the other
    remains active because `PublicLowEquivalent` includes the raw halted/trapped control bits.
    This is the exact independent-length recursion split; it introduces no common fuel. -/
theorem matched_successful_tail_dichotomy {machine : SemanticProgram} {root : UInt32}
    {leftTail rightTail : Nat} {left right : State}
    {leftResult rightResult : StepResult}
    (hleft : SuccessfulExecution machine root (leftTail + 1) left leftResult)
    (hright : SuccessfulExecution machine root (rightTail + 1) right rightResult)
    (hnextLow : PublicLowEquivalent machine (step machine left).state
      (step machine right).state) :
    (leftTail = 0 ∧ rightTail = 0) ∨
      (0 < leftTail ∧ 0 < rightTail ∧
        SuccessfulExecution machine root leftTail (step machine left).state
          (runPrefix machine leftTail (step machine left).state) ∧
        SuccessfulExecution machine root rightTail (step machine right).state
          (runPrefix machine rightTail (step machine right).state)) := by
  by_cases hleftZero : leftTail = 0
  · subst leftTail
    have hleftRun : step machine left = leftResult := by
      simpa [runPrefix] using hleft.run
    have hleftHalted : (step machine left).state.halted = true := by
      rw [hleftRun]
      exact hleft.halted
    have hrightHalted : (step machine right).state.halted = true := by
      rw [← hnextLow.2.1]
      exact hleftHalted
    have hrightZero : rightTail = 0 := by
      by_contra hpositive
      have hactive := hright.reached_active (elapsed := 1) (by omega)
      have hstate : (runPrefix machine 1 right).state = (step machine right).state := by
        simp [runPrefix]
      rw [hstate] at hactive
      have hnotHalted := hactive.notHalted
      rw [hrightHalted] at hnotHalted
      contradiction
    exact Or.inl ⟨rfl, hrightZero⟩
  · have hleftPositive : 0 < leftTail := Nat.pos_of_ne_zero hleftZero
    by_cases hrightZero : rightTail = 0
    · subst rightTail
      have hrightRun : step machine right = rightResult := by
        simpa [runPrefix] using hright.run
      have hrightHalted : (step machine right).state.halted = true := by
        rw [hrightRun]
        exact hright.halted
      have hleftHalted : (step machine left).state.halted = true := by
        rw [hnextLow.2.1]
        exact hrightHalted
      have hactive := hleft.reached_active (elapsed := 1) (by omega)
      have hstate : (runPrefix machine 1 left).state = (step machine left).state := by
        simp [runPrefix]
      rw [hstate] at hactive
      have hnotHalted := hactive.notHalted
      rw [hleftHalted] at hnotHalted
      contradiction
    · have hrightPositive : 0 < rightTail := Nat.pos_of_ne_zero hrightZero
      have hleftDrop := hleft.drop (elapsed := 1) (by omega)
      have hrightDrop := hright.drop (elapsed := 1) (by omega)
      have hleftLength : leftTail + 1 - 1 = leftTail := by omega
      have hrightLength : rightTail + 1 - 1 = rightTail := by omega
      have hleftState : (runPrefix machine 1 left).state = (step machine left).state := by
        simp [runPrefix]
      have hrightState : (runPrefix machine 1 right).state = (step machine right).state := by
        simp [runPrefix]
      rw [hleftLength, hleftState] at hleftDrop
      rw [hrightLength, hrightState] at hrightDrop
      exact Or.inr ⟨hleftPositive, hrightPositive, hleftDrop, hrightDrop⟩

/-- The terminal branch of `matched_successful_tail_dichotomy` closes the one-step suffix using
    the complete Public projection carried by the local matching theorem. -/
theorem terminal_alignment_after_matching_final_step {machine : SemanticProgram}
    {left right : State}
    (hnextLow : PublicLowEquivalent machine (step machine left).state
      (step machine right).state)
    (hleftHalted : (step machine left).state.halted = true)
    (hrightHalted : (step machine right).state.halted = true)
    (hobservation : publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events) :
    FinitePublicAlignment machine 1 left 1 right := by
  apply FinitePublicAlignment.matched hobservation
  exact .terminal (Or.inl hleftHalted) (Or.inl hrightHalted)
    (publicProjection_eq_of_low hnextLow)

/-! ## Well-founded production composition algebra

The executable verifier layer classifies a pair of live Public cut points into one of the
following concrete progress cases.  This datatype is intentionally only a description of raw
execution progress: it contains actual successful suffixes, actual raw silent segments, and the
filtered release suffix produced by those executions.  It contains neither a future-output
equality nor a relational-policy premise.

Keeping the well-founded recursion here lets the downstream V9 dispatcher focus solely on the
constructor-complete semantic case split.  Internal recursive points retain genuine reachability
and active-state provenance, but need not pretend that every intermediate fallthrough or callee
entry has a Public occurrence.  The exported production theorem still starts at the stronger
`VerifiedPublicCutPoint` boundary and must construct every progress case from verifier acceptance;
no theorem caller supplies it.
-/

/-- Internal synchronization provenance.  Public occurrence is deliberately absent: a matching
    Public step may enter a verifier-private callee or a target with another private predecessor.
    Reachability and `ActiveState` are the exact facts needed to continue the semantic dispatcher. -/
structure VerifiedSynchronizationPoint (machine : SemanticProgram) (root : UInt32)
    (state : State) : Prop where
  reachable : ReachableFromRoot machine root state
  active : ActiveState machine root state

theorem verifiedSynchronizationPoint_of_public_cut
    {machine : SemanticProgram} {root : UInt32}
    {state : State} (hcut : VerifiedPublicCutPoint machine root state) :
    VerifiedSynchronizationPoint machine root state :=
  ⟨hcut.reachable, hcut.active⟩

/-- Every strict prefix of a genuine successful execution is a verifier-owned internal
    synchronization point.  This is the standard provenance constructor for matched successors
    and independently sized private-segment endpoints. -/
theorem verifiedSynchronizationPoint_of_successful_prefix
    {machine : SemanticProgram} {root : UInt32} {steps elapsed : Nat}
    {start : State} {result : StepResult}
    (hreachable : ReachableFromRoot machine root start)
    (hexecution : SuccessfulExecution machine root steps start result)
    (helapsed : elapsed < steps) :
    VerifiedSynchronizationPoint machine root (runPrefix machine elapsed start).state :=
  ⟨reachableFromRoot_runPrefix_state hreachable elapsed,
    hexecution.reached_active helapsed⟩

theorem verifiedSynchronizationPoint_after_successful_step
    {machine : SemanticProgram} {root : UInt32} {tail : Nat}
    {start : State} {result : StepResult}
    (hreachable : ReachableFromRoot machine root start)
    (hexecution : SuccessfulExecution machine root (tail + 1) start result)
    (htail : 0 < tail) :
    VerifiedSynchronizationPoint machine root (step machine start).state := by
  have hsync := verifiedSynchronizationPoint_of_successful_prefix hreachable hexecution
    (elapsed := 1) (by omega)
  simpa only [runPrefix] using hsync

/-- One strictly decreasing progress case for two independently sized successful executions. -/
inductive PublicExecutionProgress (machine : SemanticProgram) (root : UInt32) :
    Nat → State → Nat → State → Prop
  /-- Two independently long private stretches consume both successful executions.  Their
      actual endpoints are related directly; no common pc or fabricated continuation is needed.
      This is the honest synthetic-function-return case. -/
  | privateTerminal {leftLength rightLength : Nat} {leftStart rightStart : State}
      {leftResult rightResult : StepResult}
      (segments : PairedPublicSilentSegments machine leftLength rightLength
        leftStart rightStart leftResult.state rightResult.state)
      (leftExecution : SuccessfulExecution machine root leftLength leftStart leftResult)
      (rightExecution : SuccessfulExecution machine root rightLength rightStart rightResult) :
      PublicExecutionProgress machine root leftLength leftStart rightLength rightStart
  /-- Independently long private prefixes may end in distinct raw top-level output
      instructions.  The prefixes are silent, while the two real terminal output steps match at
      the declaration-owned boundary site.  Keeping the final step explicit prevents a private
      return occurrence from being mislabeled as boundary-silent merely to close the proof. -/
  | privateMatchedTerminal {leftLength rightLength : Nat}
      {leftStart rightStart leftFinish rightFinish : State}
      (leftSegment : PublicSilentSegment machine leftLength leftStart leftFinish)
      (rightSegment : PublicSilentSegment machine rightLength rightStart rightFinish)
      (observation : publicBoundaryTrace (step machine leftFinish).events =
        publicBoundaryTrace (step machine rightFinish).events)
      (endpointProjection : publicProjection machine (step machine leftFinish).state =
        publicProjection machine (step machine rightFinish).state)
      (leftHalted : (step machine leftFinish).state.halted = true)
      (rightHalted : (step machine rightFinish).state.halted = true) :
      PublicExecutionProgress machine root (leftLength + 1) leftStart
        (rightLength + 1) rightStart
  /-- Both executions finish in their current, observationally matching raw step. -/
  | matchedTerminal {left right : State}
      (observation : publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events)
      (nextLow : PublicLowEquivalent machine (step machine left).state
        (step machine right).state)
      (leftHalted : (step machine left).state.halted = true)
      (rightHalted : (step machine right).state.halted = true) :
      PublicExecutionProgress machine root 1 left 1 right
  /-- One raw matching step on each side leaves two genuine reachable, active suffixes. -/
  | matchedContinue {leftTail rightTail : Nat} {left right : State}
      (observation : publicBoundaryTrace (step machine left).events =
        publicBoundaryTrace (step machine right).events)
      (leftSync : VerifiedSynchronizationPoint machine root (step machine left).state)
      (rightSync : VerifiedSynchronizationPoint machine root (step machine right).state)
      (nextLow : PublicLowEquivalent machine (step machine left).state
        (step machine right).state)
      (leftExecution : SuccessfulExecution machine root leftTail
        (step machine left).state (runPrefix machine leftTail (step machine left).state))
      (rightExecution : SuccessfulExecution machine root rightTail
        (step machine right).state (runPrefix machine rightTail (step machine right).state))
      (releaseTail : publicReleaseTrace machine
          (runPrefix machine leftTail (step machine left).state).events =
        publicReleaseTrace machine
          (runPrefix machine rightTail (step machine right).state).events) :
      PublicExecutionProgress machine root (leftTail + 1) left (rightTail + 1) right
  /-- Independently long structured private regions are silent in the Public boundary trace,
      restore the full raw Public projection, and meet again at verifier-owned synchronization
      points.  A downstream case may separately prove that the endpoint is a reusable Public cut. -/
  | privateContinue {leftLength rightLength leftTail rightTail : Nat}
      {leftStart rightStart leftFinish rightFinish : State}
      (leftPositive : 0 < leftLength)
      (rightPositive : 0 < rightLength)
      (leftSegment : PublicSilentSegment machine leftLength leftStart leftFinish)
      (rightSegment : PublicSilentSegment machine rightLength rightStart rightFinish)
      (leftSync : VerifiedSynchronizationPoint machine root leftFinish)
      (rightSync : VerifiedSynchronizationPoint machine root rightFinish)
      (nextLow : PublicLowEquivalent machine leftFinish rightFinish)
      (leftExecution : SuccessfulExecution machine root leftTail leftFinish
        (runPrefix machine leftTail leftFinish))
      (rightExecution : SuccessfulExecution machine root rightTail rightFinish
        (runPrefix machine rightTail rightFinish))
      (releaseTail : publicReleaseTrace machine
          (runPrefix machine leftTail leftFinish).events =
        publicReleaseTrace machine (runPrefix machine rightTail rightFinish).events) :
      PublicExecutionProgress machine root (leftLength + leftTail) leftStart
        (rightLength + rightTail) rightStart
  /-- Paired private regions may restore only the relational endpoint projection.  This is
      required when the last real transition is an internal return into a Public destination:
      neither side preserves its own projection, while the verifier-derived matched return
      establishes equality between the two actual endpoints. -/
  | pairedPrivateContinue {leftLength rightLength leftTail rightTail : Nat}
      {leftStart rightStart leftFinish rightFinish : State}
      (leftPositive : 0 < leftLength)
      (rightPositive : 0 < rightLength)
      (segments : PairedPublicSilentSegments machine leftLength rightLength
        leftStart rightStart leftFinish rightFinish)
      (leftSync : VerifiedSynchronizationPoint machine root leftFinish)
      (rightSync : VerifiedSynchronizationPoint machine root rightFinish)
      (nextLow : PublicLowEquivalent machine leftFinish rightFinish)
      (leftExecution : SuccessfulExecution machine root leftTail leftFinish
        (runPrefix machine leftTail leftFinish))
      (rightExecution : SuccessfulExecution machine root rightTail rightFinish
        (runPrefix machine rightTail rightFinish))
      (releaseTail : publicReleaseTrace machine
          (runPrefix machine leftTail leftFinish).events =
        publicReleaseTrace machine (runPrefix machine rightTail rightFinish).events) :
      PublicExecutionProgress machine root (leftLength + leftTail) leftStart
        (rightLength + rightTail) rightStart

/-- A constructor-complete dispatcher for the current verifier-owned synchronization points. This is a
    parameter of the generic algebra only.  Production claims instantiate it with a proved V9
    semantic dispatcher in the downstream composition module; it is never exposed in their
    theorem signatures. -/
def PublicExecutionProgressDispatcher (machine : SemanticProgram) (root : UInt32) : Prop :=
  ∀ (leftSteps rightSteps : Nat) (left right : State)
    (leftResult rightResult : StepResult),
    VerifiedSynchronizationPoint machine root left →
    VerifiedSynchronizationPoint machine root right →
    PublicLowEquivalent machine left right →
    SuccessfulExecution machine root leftSteps left leftResult →
    SuccessfulExecution machine root rightSteps right rightResult →
    publicReleaseTrace machine leftResult.events =
      publicReleaseTrace machine rightResult.events →
    PublicExecutionProgress machine root leftSteps left rightSteps right

/-- Package one verifier-matching raw step into the exact progress constructor.  The successful
    executions themselves decide whether this was the final step; cut-point evidence is demanded
    only for a genuinely nonempty suffix. -/
theorem publicExecutionProgress_of_matching_step {machine : SemanticProgram} {root : UInt32}
    {leftTail rightTail : Nat} {left right : State}
    {leftResult rightResult : StepResult}
    (hleftExecution : SuccessfulExecution machine root (leftTail + 1) left leftResult)
    (hrightExecution : SuccessfulExecution machine root (rightTail + 1) right rightResult)
    (hnextLow : PublicLowEquivalent machine (step machine left).state
      (step machine right).state)
    (hobservation : publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events)
    (hleftSync : 0 < leftTail →
      VerifiedSynchronizationPoint machine root (step machine left).state)
    (hrightSync : 0 < rightTail →
      VerifiedSynchronizationPoint machine root (step machine right).state)
    (hreleaseTail : publicReleaseTrace machine
        (runPrefix machine leftTail (step machine left).state).events =
      publicReleaseTrace machine
        (runPrefix machine rightTail (step machine right).state).events) :
    PublicExecutionProgress machine root (leftTail + 1) left (rightTail + 1) right := by
  rcases matched_successful_tail_dichotomy hleftExecution hrightExecution hnextLow with
    hterminal | hcontinue
  · obtain ⟨rfl, rfl⟩ := hterminal
    have hleftRun : step machine left = leftResult := by
      simpa [runPrefix] using hleftExecution.run
    have hrightRun : step machine right = rightResult := by
      simpa [runPrefix] using hrightExecution.run
    exact .matchedTerminal hobservation hnextLow
      (by rw [hleftRun]; exact hleftExecution.halted)
      (by rw [hrightRun]; exact hrightExecution.halted)
  · obtain ⟨hleftPositive, hrightPositive, hleftTailExecution,
      hrightTailExecution⟩ := hcontinue
    exact .matchedContinue hobservation (hleftSync hleftPositive)
      (hrightSync hrightPositive) hnextLow hleftTailExecution hrightTailExecution hreleaseTail

/-- Package two actual independently sized silent prefixes.  The suffix lengths and successful
    executions are derived by dropping those exact raw prefixes, so a dispatcher cannot smuggle
    in unrelated endpoint runs. -/
theorem publicExecutionProgress_of_private_segments {machine : SemanticProgram} {root : UInt32}
    {leftSteps rightSteps leftLength rightLength : Nat}
    {leftStart rightStart leftFinish rightFinish : State}
    {leftResult rightResult : StepResult}
    (hleftPositive : 0 < leftLength) (hrightPositive : 0 < rightLength)
    (hleftBound : leftLength < leftSteps) (hrightBound : rightLength < rightSteps)
    (hleftSegment : PublicSilentSegment machine leftLength leftStart leftFinish)
    (hrightSegment : PublicSilentSegment machine rightLength rightStart rightFinish)
    (hleftSync : VerifiedSynchronizationPoint machine root leftFinish)
    (hrightSync : VerifiedSynchronizationPoint machine root rightFinish)
    (hnextLow : PublicLowEquivalent machine leftFinish rightFinish)
    (hleftExecution : SuccessfulExecution machine root leftSteps leftStart leftResult)
    (hrightExecution : SuccessfulExecution machine root rightSteps rightStart rightResult)
    (hreleaseTail : publicReleaseTrace machine
        (runPrefix machine (leftSteps - leftLength) leftFinish).events =
      publicReleaseTrace machine
        (runPrefix machine (rightSteps - rightLength) rightFinish).events) :
    PublicExecutionProgress machine root leftSteps leftStart rightSteps rightStart := by
  have hleftDrop := hleftExecution.drop hleftBound
  have hrightDrop := hrightExecution.drop hrightBound
  rw [hleftSegment.finish_eq] at hleftDrop
  rw [hrightSegment.finish_eq] at hrightDrop
  have hprogress : PublicExecutionProgress machine root
      (leftLength + (leftSteps - leftLength)) leftStart
      (rightLength + (rightSteps - rightLength)) rightStart :=
    .privateContinue hleftPositive hrightPositive hleftSegment hrightSegment hleftSync hrightSync
      hnextLow hleftDrop hrightDrop hreleaseTail
  have hleftSum : leftLength + (leftSteps - leftLength) = leftSteps :=
    Nat.add_sub_of_le (Nat.le_of_lt hleftBound)
  have hrightSum : rightLength + (rightSteps - rightLength) = rightSteps :=
    Nat.add_sub_of_le (Nat.le_of_lt hrightBound)
  simpa only [hleftSum, hrightSum] using hprogress

/-- Paired analogue of `publicExecutionProgress_of_private_segments`.  Exact suffix executions
    are still obtained by dropping the two actual raw prefixes; the only generalization is that
    endpoint projection equality is relational rather than two unary restoration claims. -/
theorem publicExecutionProgress_of_paired_private_segments
    {machine : SemanticProgram} {root : UInt32}
    {leftSteps rightSteps leftLength rightLength : Nat}
    {leftStart rightStart leftFinish rightFinish : State}
    {leftResult rightResult : StepResult}
    (hleftPositive : 0 < leftLength) (hrightPositive : 0 < rightLength)
    (hleftBound : leftLength < leftSteps) (hrightBound : rightLength < rightSteps)
    (hsegments : PairedPublicSilentSegments machine leftLength rightLength
      leftStart rightStart leftFinish rightFinish)
    (hleftSync : VerifiedSynchronizationPoint machine root leftFinish)
    (hrightSync : VerifiedSynchronizationPoint machine root rightFinish)
    (hnextLow : PublicLowEquivalent machine leftFinish rightFinish)
    (hleftExecution : SuccessfulExecution machine root leftSteps leftStart leftResult)
    (hrightExecution : SuccessfulExecution machine root rightSteps rightStart rightResult)
    (hreleaseTail : publicReleaseTrace machine
        (runPrefix machine (leftSteps - leftLength) leftFinish).events =
      publicReleaseTrace machine
        (runPrefix machine (rightSteps - rightLength) rightFinish).events) :
    PublicExecutionProgress machine root leftSteps leftStart rightSteps rightStart := by
  have hleftDrop := hleftExecution.drop hleftBound
  have hrightDrop := hrightExecution.drop hrightBound
  rw [hsegments.leftFinish_eq] at hleftDrop
  rw [hsegments.rightFinish_eq] at hrightDrop
  have hprogress : PublicExecutionProgress machine root
      (leftLength + (leftSteps - leftLength)) leftStart
      (rightLength + (rightSteps - rightLength)) rightStart :=
    .pairedPrivateContinue hleftPositive hrightPositive hsegments hleftSync hrightSync
      hnextLow hleftDrop hrightDrop hreleaseTail
  have hleftSum : leftLength + (leftSteps - leftLength) = leftSteps :=
    Nat.add_sub_of_le (Nat.le_of_lt hleftBound)
  have hrightSum : rightLength + (rightSteps - rightLength) = rightSteps :=
    Nat.add_sub_of_le (Nat.le_of_lt hrightBound)
  simpa only [hleftSum, hrightSum] using hprogress

/-- If two unary private segments consume both successful executions, their starting Public-low
    relation supplies the paired endpoint projection required by `privateTerminal`.  No terminal
    observation equality is assumed: it follows because every actual step in each segment is
    boundary-silent. -/
theorem publicExecutionProgress_of_complete_private_segments
    {machine : SemanticProgram} {root : UInt32}
    {leftLength rightLength : Nat} {leftStart rightStart : State}
    {leftResult rightResult : StepResult}
    (hstartLow : PublicLowEquivalent machine leftStart rightStart)
    (hleftSegment : PublicSilentSegment machine leftLength leftStart leftResult.state)
    (hrightSegment : PublicSilentSegment machine rightLength rightStart rightResult.state)
    (hleftExecution : SuccessfulExecution machine root leftLength leftStart leftResult)
    (hrightExecution : SuccessfulExecution machine root rightLength rightStart rightResult) :
    PublicExecutionProgress machine root leftLength leftStart rightLength rightStart := by
  have hpaired : PairedPublicSilentSegments machine leftLength rightLength
      leftStart rightStart leftResult.state rightResult.state := by
    refine ⟨hleftSegment.finish_eq, hrightSegment.finish_eq, hleftSegment.silent,
      hrightSegment.silent, ?_⟩
    exact hleftSegment.endProjection.trans
      ((publicProjection_eq_of_low hstartLow).trans hrightSegment.endProjection.symm)
  exact .privateTerminal hpaired hleftExecution hrightExecution

/-- Strong induction over the sum of the two real execution lengths turns locally verified
    progress into a complete finite weak alignment.  The matched case decreases both lengths;
    the private case decreases them by independently positive region lengths. -/
theorem finitePublicAlignment_of_progress_dispatcher {machine : SemanticProgram} {root : UInt32}
    (hdispatch : PublicExecutionProgressDispatcher machine root)
    {leftSteps rightSteps : Nat} {left right : State}
    {leftResult rightResult : StepResult}
    (hleftSync : VerifiedSynchronizationPoint machine root left)
    (hrightSync : VerifiedSynchronizationPoint machine root right)
    (hlow : PublicLowEquivalent machine left right)
    (hleftExecution : SuccessfulExecution machine root leftSteps left leftResult)
    (hrightExecution : SuccessfulExecution machine root rightSteps right rightResult)
    (hrelease : publicReleaseTrace machine leftResult.events =
      publicReleaseTrace machine rightResult.events) :
    FinitePublicAlignment machine leftSteps left rightSteps right := by
  have hmain : ∀ total leftSteps rightSteps left right leftResult rightResult,
      leftSteps + rightSteps = total →
      VerifiedSynchronizationPoint machine root left →
      VerifiedSynchronizationPoint machine root right →
      PublicLowEquivalent machine left right →
      SuccessfulExecution machine root leftSteps left leftResult →
      SuccessfulExecution machine root rightSteps right rightResult →
      publicReleaseTrace machine leftResult.events =
        publicReleaseTrace machine rightResult.events →
      FinitePublicAlignment machine leftSteps left rightSteps right := by
    intro total
    induction total using Nat.strong_induction_on with
    | h total ih =>
      intro leftSteps rightSteps left right leftResult rightResult htotal
        hleftSync hrightSync hlow hleftExecution hrightExecution hrelease
      have hprogress := hdispatch leftSteps rightSteps left right leftResult rightResult
        hleftSync hrightSync hlow hleftExecution hrightExecution hrelease
      cases hprogress with
      | privateTerminal segments leftTerminalExecution rightTerminalExecution =>
          exact segments.complete leftTerminalExecution rightTerminalExecution
      | privateMatchedTerminal leftSegment rightSegment observation endpointProjection
          leftHalted rightHalted =>
          have hterminal : FinitePublicAlignment machine 0
              (step machine _).state 0 (step machine _).state :=
            .terminal (Or.inl leftHalted) (Or.inl rightHalted) endpointProjection
          have hmatched : FinitePublicAlignment machine 1 _ 1 _ :=
            .matched observation hterminal
          exact prepend_private_regions leftSegment rightSegment hmatched
      | matchedTerminal observation nextLow leftHalted rightHalted =>
          exact terminal_alignment_after_matching_final_step nextLow leftHalted rightHalted
            observation
      | @matchedContinue leftTail rightTail left right observation leftSync rightSync nextLow
          leftTailExecution rightTailExecution releaseTail =>
          have hsmaller : leftTail + rightTail < total := by omega
          have htail := ih (leftTail + rightTail) hsmaller leftTail rightTail
            (step machine left).state (step machine right).state
            (runPrefix machine leftTail (step machine left).state)
            (runPrefix machine rightTail (step machine right).state)
            rfl leftSync rightSync nextLow leftTailExecution rightTailExecution releaseTail
          exact prepend_matching_step observation htail
      | @privateContinue leftLength rightLength leftTail rightTail leftStart rightStart
          leftFinish rightFinish leftPositive rightPositive leftSegment rightSegment
          leftSync rightSync nextLow leftTailExecution rightTailExecution releaseTail =>
          have hsmaller : leftTail + rightTail < total := by omega
          have htail := ih (leftTail + rightTail) hsmaller leftTail rightTail leftFinish
            rightFinish (runPrefix machine leftTail leftFinish)
            (runPrefix machine rightTail rightFinish) rfl leftSync rightSync nextLow
            leftTailExecution rightTailExecution releaseTail
          exact prepend_private_regions leftSegment rightSegment htail
      | @pairedPrivateContinue leftLength rightLength leftTail rightTail leftStart rightStart
          leftFinish rightFinish leftPositive rightPositive segments leftSync rightSync nextLow
          leftTailExecution rightTailExecution releaseTail =>
          have hsmaller : leftTail + rightTail < total := by omega
          have htail := ih (leftTail + rightTail) hsmaller leftTail rightTail leftFinish
            rightFinish (runPrefix machine leftTail leftFinish)
            (runPrefix machine rightTail rightFinish) rfl leftSync rightSync nextLow
            leftTailExecution rightTailExecution releaseTail
          exact segments.prepend htail
  exact hmain (leftSteps + rightSteps) leftSteps rightSteps left right leftResult rightResult
    rfl hleftSync hrightSync hlow hleftExecution hrightExecution hrelease

/-- Production entry points remain the strong reusable Public cut points.  Only the internal
    recursive invariant is generalized to reachable active synchronization points. -/
theorem finitePublicAlignment_of_progress_dispatcher_at_public_cuts
    {machine : SemanticProgram} {root : UInt32}
    (hdispatch : PublicExecutionProgressDispatcher machine root)
    {leftSteps rightSteps : Nat} {left right : State}
    {leftResult rightResult : StepResult}
    (hleftCut : VerifiedPublicCutPoint machine root left)
    (hrightCut : VerifiedPublicCutPoint machine root right)
    (hlow : PublicLowEquivalent machine left right)
    (hleftExecution : SuccessfulExecution machine root leftSteps left leftResult)
    (hrightExecution : SuccessfulExecution machine root rightSteps right rightResult)
    (hrelease : publicReleaseTrace machine leftResult.events =
      publicReleaseTrace machine rightResult.events) :
    FinitePublicAlignment machine leftSteps left rightSteps right :=
  finitePublicAlignment_of_progress_dispatcher hdispatch
    (verifiedSynchronizationPoint_of_public_cut hleftCut)
    (verifiedSynchronizationPoint_of_public_cut hrightCut) hlow hleftExecution
    hrightExecution hrelease

/-! ## Pinned production contracts

These propositions pin the complete claim surface while the construction below is assembled.
They are definitions of the theorem statements, not assumptions and not authorization predicates;
only a theorem inhabiting them may be exported by `RawClaimSurface`.
-/

/-- Exact independently-sized weak-alignment contract.  `analysis` is fixed by the successful
    production analyzer equation, and every trace is generated by `rawSemanticProgram`. -/
def RawPublicWeakBisimulationV9Contract : Prop :=
  ∀ (program : V9.Program) (analysis : Analysis) (root : UInt32)
    (leftSteps rightSteps : Nat) (left right : State)
    (leftResult rightResult : StepResult),
    OccurrenceKernel.verifyProgram program = none →
    analyze? program = some analysis →
    VerifiedPublicCutPoint (rawSemanticProgram program analysis) root left →
    VerifiedPublicCutPoint (rawSemanticProgram program analysis) root right →
    StateWellFormed (rawSemanticProgram program analysis) left →
    StateWellFormed (rawSemanticProgram program analysis) right →
    PublicLowEquivalent (rawSemanticProgram program analysis) left right →
    left.externalInputs = right.externalInputs →
    SuccessfulExecution (rawSemanticProgram program analysis) root leftSteps left leftResult →
    SuccessfulExecution (rawSemanticProgram program analysis) root rightSteps right rightResult →
    ReleaseSynchronization.releaseTrace leftResult.events =
      ReleaseSynchronization.releaseTrace rightResult.events →
    FinitePublicAlignment (rawSemanticProgram program analysis)
      leftSteps left rightSteps right

/-- Budgeted Public noninterference contract.  The two fuels remain syntactically independent,
    and `SuccessfulRun` rules out both trapping and mere exhaustion. -/
def RawPublicDelimitedReleaseNoninterferenceV9Contract : Prop :=
  ∀ (program : V9.Program) (analysis : Analysis) (root : UInt32)
    (leftFuel rightFuel : Nat) (left right : State)
    (leftResult rightResult : StepResult),
    OccurrenceKernel.verifyProgram program = none →
    analyze? program = some analysis →
    VerifiedPublicCutPoint (rawSemanticProgram program analysis) root left →
    VerifiedPublicCutPoint (rawSemanticProgram program analysis) root right →
    StateWellFormed (rawSemanticProgram program analysis) left →
    StateWellFormed (rawSemanticProgram program analysis) right →
    PublicLowEquivalent (rawSemanticProgram program analysis) left right →
    left.externalInputs = right.externalInputs →
    SuccessfulRun (rawSemanticProgram program analysis) root leftFuel left leftResult →
    SuccessfulRun (rawSemanticProgram program analysis) root rightFuel right rightResult →
    ReleaseSynchronization.releaseTrace leftResult.events =
    ReleaseSynchronization.releaseTrace rightResult.events →
    PublicExecutionConclusion (rawSemanticProgram program analysis) leftResult rightResult

/-- The budgeted production result is a strict consequence of the exact weak-bisimulation
    contract.  This proof performs the only fuel normalization: each active successful run yields
    its own exact completion length, so no equality or common upper bound is introduced. -/
theorem rawPublicDelimitedReleaseContract_of_weakBisimulation
    (hweak : RawPublicWeakBisimulationV9Contract) :
    RawPublicDelimitedReleaseNoninterferenceV9Contract := by
  intro program analysis root leftFuel rightFuel left right leftResult rightResult
    hverified hanalysis hleftCut hrightCut hleftWellFormed hrightWellFormed hlow hstreams
    hleftRun hrightRun hrelease
  obtain ⟨leftSteps, _, hleftExecution⟩ :=
    successfulRun_at_active_cut_is_exact hleftCut hleftRun
  obtain ⟨rightSteps, _, hrightExecution⟩ :=
    successfulRun_at_active_cut_is_exact hrightCut hrightRun
  have halignment := hweak program analysis root leftSteps rightSteps left right
    leftResult rightResult hverified hanalysis hleftCut hrightCut hleftWellFormed
    hrightWellFormed hlow hstreams hleftExecution hrightExecution hrelease
  have hconclusion := publicExecutionConclusion_of_alignment halignment
  rw [hleftExecution.run, hrightExecution.run] at hconclusion
  exact hconclusion

end LambdaSigil.Combined.V9.PublicExecutionSecurity
