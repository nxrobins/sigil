import LambdaSigil.PublicWeakAlignment
import LambdaSigil.ReleaseSynchronization

/-!
# Public release synchronization

Complete release equality includes private-region releases.  Public preservation needs the stable
subsequence whose decoded sites have Public occurrence.  This file derives that subsequence from
actual raw events and the immutable program; it does not annotate or replace an event payload.
-/

namespace LambdaSigil.Combined.Semantic.PublicReleaseSynchronization

open ReleaseSynchronization

def releaseSiteOccurrence (p : SemanticProgram) (site : UInt32) : Label :=
  match p.instructions.find? (fun instruction => instruction.id == site) with
  | some instruction => instruction.blockLabel
  | none => .secretCT

def publicReleaseTrace (p : SemanticProgram) (events : List Event) :
    List ReleaseObservation :=
  (ReleaseSynchronization.releaseTrace events).filter fun observation =>
    (releaseSiteOccurrence p observation.site).eqb .pub

@[simp] theorem publicReleaseTrace_append (p : SemanticProgram) (left right : List Event) :
    publicReleaseTrace p (left ++ right) =
      publicReleaseTrace p left ++ publicReleaseTrace p right := by
  simp [publicReleaseTrace]

theorem complete_release_equality_implies_public_release_equality
    (p : SemanticProgram) {left right : List Event}
    (hcomplete : ReleaseSynchronization.releaseTrace left =
      ReleaseSynchronization.releaseTrace right) :
    publicReleaseTrace p left = publicReleaseTrace p right := by
  unfold publicReleaseTrace
  rw [hcomplete]

theorem run_complete_release_equality_implies_public_release_equality
    (p : SemanticProgram) {leftFuel rightFuel : Nat} {left right : State}
    (hcomplete : ReleaseSynchronization.releaseTrace
        (runPrefix p leftFuel left).events =
      ReleaseSynchronization.releaseTrace (runPrefix p rightFuel right).events) :
    publicReleaseTrace p (runPrefix p leftFuel left).events =
      publicReleaseTrace p (runPrefix p rightFuel right).events :=
  complete_release_equality_implies_public_release_equality p hcomplete

/-! ## Independently advanced Public-release cursors -/

/-- Proof-only progress through one concrete raw execution.  The cursor stores only a step count;
    the Public release observations are recomputed from `runPrefix`, so it cannot invent a site,
    stage, payload, or occurrence. -/
structure PublicReleaseProgress (total : Nat) where
  steps : Nat
  within : steps ≤ total

def PublicReleaseProgress.consumed {total : Nat} (cursor : PublicReleaseProgress total)
    (p : SemanticProgram) (start : State) : List ReleaseObservation :=
  publicReleaseTrace p (runPrefix p cursor.steps start).events

def PublicReleaseProgress.remaining {total : Nat} (cursor : PublicReleaseProgress total)
    (p : SemanticProgram) (start : State) : List ReleaseObservation :=
  publicReleaseTrace p (runPrefix p (total - cursor.steps)
    (runPrefix p cursor.steps start).state).events

theorem publicReleaseProgress_partition (p : SemanticProgram) (start : State) {total : Nat}
    (cursor : PublicReleaseProgress total) :
    publicReleaseTrace p (runPrefix p total start).events =
      cursor.consumed p start ++ cursor.remaining p start := by
  have htotal : total = cursor.steps + (total - cursor.steps) :=
    (Nat.add_sub_of_le cursor.within).symm
  conv_lhs => rw [htotal, ReleaseSynchronization.runPrefix_add]
  exact publicReleaseTrace_append _ _ _

theorem publicReleaseConsumed_is_actual_prefix (p : SemanticProgram) (start : State)
    {total : Nat} (cursor : PublicReleaseProgress total) :
    cursor.consumed p start =
      (publicReleaseTrace p (runPrefix p total start).events).take
        (cursor.consumed p start).length := by
  rw [publicReleaseProgress_partition p start cursor]
  simp

theorem publicReleaseRemaining_is_actual_suffix (p : SemanticProgram) (start : State)
    {total : Nat} (cursor : PublicReleaseProgress total) :
    cursor.remaining p start =
      (publicReleaseTrace p (runPrefix p total start).events).drop
        (cursor.consumed p start).length := by
  rw [publicReleaseProgress_partition p start cursor]
  simp

/-- Equal complete release traces synchronize independently advanced proof cursors as soon as
    they have consumed the same number of *Public* release occurrences.  Private releases may be
    reached at unrelated step counts and are intentionally absent from this count. -/
theorem equal_public_occurrence_counts_synchronize_prefix_and_suffix
    (p : SemanticProgram) (left right : State) {leftFuel rightFuel : Nat}
    (leftCursor : PublicReleaseProgress leftFuel)
    (rightCursor : PublicReleaseProgress rightFuel)
    (hcomplete : ReleaseSynchronization.releaseTrace
        (runPrefix p leftFuel left).events =
      ReleaseSynchronization.releaseTrace (runPrefix p rightFuel right).events)
    (hcount : (leftCursor.consumed p left).length =
      (rightCursor.consumed p right).length) :
    leftCursor.consumed p left = rightCursor.consumed p right ∧
      leftCursor.remaining p left = rightCursor.remaining p right := by
  have hpublic := run_complete_release_equality_implies_public_release_equality p hcomplete
  constructor
  · calc
      leftCursor.consumed p left = _ :=
        publicReleaseConsumed_is_actual_prefix p left leftCursor
      _ = (publicReleaseTrace p (runPrefix p rightFuel right).events).take
          (rightCursor.consumed p right).length := by rw [hpublic, hcount]
      _ = rightCursor.consumed p right :=
        (publicReleaseConsumed_is_actual_prefix p right rightCursor).symm
  · calc
      leftCursor.remaining p left = _ :=
        publicReleaseRemaining_is_actual_suffix p left leftCursor
      _ = (publicReleaseTrace p (runPrefix p rightFuel right).events).drop
          (rightCursor.consumed p right).length := by rw [hpublic, hcount]
      _ = rightCursor.remaining p right :=
        (publicReleaseRemaining_is_actual_suffix p right rightCursor).symm

/-! ## One-step release classification -/

@[simp] private theorem releaseEvents_nil : releaseEvents [] = [] := rfl

@[simp] private theorem releaseEvents_eventsForValues_nonrelease (kind : EventKind)
    (site : UInt32) (values : List Value) (hkind : kind ≠ .release) :
    releaseEvents (eventsForValues kind site values) = [] := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [eventsForValues, releaseEvents, EventKind.eqb, hkind]

@[simp] private theorem releaseEvents_eventsForValuesUnderPc_nonrelease (kind : EventKind)
    (site : UInt32) (pc : Label) (values : List Value) (hkind : kind ≠ .release) :
    releaseEvents (eventsForValuesUnderPc kind site pc values) = [] := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [eventsForValuesUnderPc, releaseEvents, EventKind.eqb, hkind]

@[simp] private theorem releaseEvents_eventsForObserved_nonrelease (kind : EventKind)
    (site : UInt32) (values : List Value) (hkind : kind ≠ .release) :
    releaseEvents (eventsForObserved kind site values) = [] := by
  by_cases hempty : values.isEmpty
  · simp [eventsForObserved, hempty, releaseEvents, EventKind.eqb, hkind]
  · simp [eventsForObserved, hempty, hkind]

@[simp] private theorem releaseEvents_singleton_nonrelease (event : Event)
    (hkind : event.kind ≠ .release) :
    releaseEvents [event] = [] := by
  simp [releaseEvents, EventKind.eqb, hkind]

theorem publicReleaseTrace_instruction_release (p : SemanticProgram) (state : State)
    (instruction : Instruction) (hop : instruction.op = .release)
    (hpublic : releaseSiteOccurrence p instruction.id = .pub) :
    publicReleaseTrace p (instructionEvents p state instruction) =
      [⟨instruction.id, 1, (operandValue p state instruction).payload⟩] := by
  simp [instructionEvents, hop, publicReleaseTrace, ReleaseSynchronization.releaseTrace,
    Semantic.releaseEvents, EventKind.eqb, hpublic, Label.eqb, operandValue]

theorem publicReleaseTrace_instruction_releaseCT (p : SemanticProgram) (state : State)
    (instruction : Instruction) (hop : instruction.op = .releaseCT)
    (hpublic : releaseSiteOccurrence p instruction.id = .pub) :
    publicReleaseTrace p (instructionEvents p state instruction) =
      [⟨instruction.id, 2, (operandValue p state instruction).payload⟩] := by
  simp [instructionEvents, hop, publicReleaseTrace, ReleaseSynchronization.releaseTrace,
    Semantic.releaseEvents, EventKind.eqb, hpublic, Label.eqb, operandValue]

theorem publicReleaseTrace_instruction_nonrelease (p : SemanticProgram) (state : State)
    (instruction : Instruction) (hrelease : instruction.op ≠ .release)
    (hreleaseCT : instruction.op ≠ .releaseCT) :
    publicReleaseTrace p (instructionEvents p state instruction) = [] := by
  have hnone : releaseEvents (instructionEvents p state instruction) = [] := by
    generalize hop : instruction.op = operation at *
    cases operation <;> simp_all [instructionEvents]
  simp [publicReleaseTrace, ReleaseSynchronization.releaseTrace, hnone]

/-- Public-release occurrence is positional. Repeated execution of one release site is retained,
    so equality aligns site, stage, payload, and occurrence number. -/
theorem equal_public_release_traces_align_occurrence (p : SemanticProgram)
    {left right : List Event} (occurrence : Nat)
    (h : publicReleaseTrace p left = publicReleaseTrace p right) :
    (publicReleaseTrace p left)[occurrence]? =
      (publicReleaseTrace p right)[occurrence]? := by
  rw [h]

private def publicReleaseInstruction : Instruction :=
  { op := .release, id := 7, functionId := 1, blockId := 1, destination := 0,
    firstOperand := 0, operandCount := 0, target := 0, blockLabel := .pub,
    resultLabel := .pub, aux := 0 }

private def privateReleaseInstruction : Instruction :=
  { publicReleaseInstruction with id := 8, blockLabel := .secret }

private def releaseClassifierProgram : SemanticProgram :=
  { functions := #[], instructions := #[publicReleaseInstruction, privateReleaseInstruction],
    operands := #[], valueLabels := #[] }

/-- Load-bearing classifier: a private release remains in the complete trace but not the Public
    subsequence; repeated Public releases are not deduplicated. -/
theorem public_release_filter_preserves_occurrences :
    let events : List Event := [
      { kind := .release, payload := 10, site := 7, stage := 1 },
      { kind := .release, payload := 20, site := 8, stage := 1 },
      { kind := .release, payload := 30, site := 7, stage := 1 }]
    ReleaseSynchronization.releaseTrace events =
        [(⟨7, 1, 10⟩ : ReleaseObservation), ⟨8, 1, 20⟩, ⟨7, 1, 30⟩] ∧
      publicReleaseTrace releaseClassifierProgram events =
        [(⟨7, 1, 10⟩ : ReleaseObservation), ⟨7, 1, 30⟩] := by
  decide +kernel

end LambdaSigil.Combined.Semantic.PublicReleaseSynchronization
