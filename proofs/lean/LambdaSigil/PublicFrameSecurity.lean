import LambdaSigil.PublicFrameBoundSecurity
import LambdaSigil.V9OccurrenceKernelSecurity

/-!
# Frame-restored Public equivalence

The raw semantic machine reuses global SSA parameter cells across calls.  While one execution is
inside a private call (or several recursive private calls), its raw value array and stack depth
therefore need not match another execution that has already returned to the same Public caller.

This module records the proof-only relation needed for that stuttering case.  Stacks are stored
innermost-first, so the private active segment is a list prefix and the suspended Public spine is
the remaining list suffix.  The relation never changes execution and does not turn a frame split
into a verifier certificate: a later theorem must obtain the split from verified regions and real
call provenance.
-/

namespace LambdaSigil.Combined.Semantic.PublicFrameSecurity

open PublicRegionSecurity
open PublicFrameBoundSecurity

/-- Restoring an innermost prefix and then its caller suffix is exactly whole-stack restoration. -/
theorem restoreFrameStack_append (state : State) (privateFrames publicSpine : List CallFrame) :
    restoreFrameStack state (privateFrames ++ publicSpine) =
      restoreFrameStack (restoreFrameStack state privateFrames) publicSpine := by
  induction privateFrames generalizing state with
  | nil => rfl
  | cons frame rest ih =>
      simpa only [List.cons_append, restoreFrameStack_cons] using
        ih (restoreValues state frame.savedParameters)

/-- An explicit decomposition of two active stacks into independently long private prefixes and
    aligned suspended Public spines.  `restoredPublic` removes only the private prefixes.  It does
    not restore the shared Public spine: those current Public cells are part of the relation and
    must not be replaced by the spine's saved caller images.  Immutable external streams are kept
    separately because `PublicProjection` intentionally contains only their cursors. -/
structure SplitFramePublicEquivalent (p : SemanticProgram)
    (leftPrivate rightPrivate leftSpine rightSpine : List CallFrame)
    (left right : State) : Prop where
  leftStack : left.callStack = leftPrivate ++ leftSpine
  rightStack : right.callStack = rightPrivate ++ rightSpine
  spineEquivalent : CallStackPublicEquivalent p leftSpine rightSpine
  externalStreams : left.externalInputs = right.externalInputs
  restoredPublic :
    publicProjection p (restoreFrameStack left leftPrivate) =
      publicProjection p (restoreFrameStack right rightPrivate)

/-- Existential surface used while stuttering.  Region proofs must retain the witnessing split;
    merely inhabiting this proposition does not classify any frame as private. -/
def PrivatePrefixPublicEquivalent (p : SemanticProgram) (left right : State) : Prop :=
  ∃ leftPrivate rightPrivate leftSpine rightSpine,
    SplitFramePublicEquivalent p leftPrivate rightPrivate leftSpine rightSpine left right

theorem SplitFramePublicEquivalent.toPrivatePrefix {p : SemanticProgram}
    {leftPrivate rightPrivate leftSpine rightSpine : List CallFrame} {left right : State}
    (h : SplitFramePublicEquivalent p leftPrivate rightPrivate leftSpine rightSpine left right) :
    PrivatePrefixPublicEquivalent p left right :=
  ⟨leftPrivate, rightPrivate, leftSpine, rightSpine, h⟩

/-- Direct elimination form: only the independently long private prefixes are restored. -/
theorem SplitFramePublicEquivalent.restored_private_prefix {p : SemanticProgram}
    {leftPrivate rightPrivate leftSpine rightSpine : List CallFrame} {left right : State}
    (h : SplitFramePublicEquivalent p leftPrivate rightPrivate leftSpine rightSpine left right) :
    publicProjection p (restoreFrameStack left leftPrivate) =
      publicProjection p (restoreFrameStack right rightPrivate) :=
  h.restoredPublic

/-- At a frame-free cut point the new relation reduces to equality of the full Public projection
    plus equality of the immutable input streams. -/
theorem splitFramePublicEquivalent_empty_iff (p : SemanticProgram) (left right : State)
    (hleft : left.callStack = []) (hright : right.callStack = []) :
    SplitFramePublicEquivalent p [] [] [] [] left right ↔
      left.externalInputs = right.externalInputs ∧
        publicProjection p left = publicProjection p right := by
  constructor
  · intro h
    exact ⟨h.externalStreams, by simpa using h.restoredPublic⟩
  · rintro ⟨hstreams, hprojection⟩
    exact ⟨by simpa using hleft, by simpa using hright, trivial, hstreams,
      by simpa using hprojection⟩

theorem privatePrefixPublicEquivalent_of_empty_stacks (p : SemanticProgram)
    (left right : State) (hleft : left.callStack = []) (hright : right.callStack = [])
    (hstreams : left.externalInputs = right.externalInputs)
    (hprojection : publicProjection p left = publicProjection p right) :
    PrivatePrefixPublicEquivalent p left right := by
  refine ⟨[], [], [], [], ?_⟩
  exact (splitFramePublicEquivalent_empty_iff p left right hleft hright).2
    ⟨hstreams, hprojection⟩

/-- At an aligned Public cut point the complete related stacks form the shared spine; neither side
    has entered an unmatched private activation yet.  This is the canonical bridge from the
    theorem's entry relation into frame-aware stuttering. -/
theorem splitFramePublicEquivalent_of_publicLowEquivalent {p : SemanticProgram}
    {left right : State} (hlow : PublicLowEquivalent p left right) :
    SplitFramePublicEquivalent p [] [] left.callStack right.callStack left right := by
  have hprojection := (publicLowEquivalent_iff_projection p left right).mp hlow
  refine ⟨rfl, rfl, hlow.2.2.2.1, hlow.2.2.2.2.1.1, ?_⟩
  simpa using hprojection.2.2.2.2.2.2.2

/-- Proof-only frame constructed by a successful raw call entry. -/
def privateCallFrame (state : State) (instruction : Instruction) (callee : Function) :
    CallFrame :=
  { returnPc := state.pc + 1
    destination := instruction.destination
    calleeId := callee.id
    returnLabel := callee.returnLabel
    savedParameters := saveValues state callee.parameterCells.toList }

/-- The successful (nontrapping) call-entry state, factored out from `callStep` for proofs. -/
def privateCallEntry (p : SemanticProgram) (state : State) (instruction : Instruction)
    (callee : Function) (arguments : List Value) : State :=
  let entered := assignArguments p state callee.parameterCells.toList arguments
  { entered with
    pc := callee.firstInstruction.toNat
    callStack := privateCallFrame state instruction callee :: state.callStack }

@[simp] theorem privateCallEntry_stack (p : SemanticProgram) (state : State)
    (instruction : Instruction) (callee : Function) (arguments : List Value) :
    (privateCallEntry p state instruction callee arguments).callStack =
      privateCallFrame state instruction callee :: state.callStack := by
  simp [privateCallEntry]

@[simp] theorem privateCallEntry_externalInputs (p : SemanticProgram) (state : State)
    (instruction : Instruction) (callee : Function) (arguments : List Value) :
    (privateCallEntry p state instruction callee arguments).externalInputs =
      state.externalInputs := by
  simp [privateCallEntry]

/-- Whole-stack restoration is unchanged by call entry.  This algebraic fact is intentionally not
    the split relation: restoring a suspended Public spine can mask its current Public cells. -/
theorem callerPublicProjection_privateCallEntry (p : SemanticProgram) (state : State)
    (instruction : Instruction) (callee : Function) (arguments : List Value) :
    callerPublicProjection p (privateCallEntry p state instruction callee arguments) =
      callerPublicProjection p state := by
  simpa [privateCallEntry, privateCallFrame] using
    callerPublicProjection_entered_unbounded p state instruction callee arguments

/-- Restoring the newly pushed frame recovers the complete projection-bearing storage of the
    pre-call state.  Control and stack fields are deliberately absent from `ProjectionStorageEqual`.
-/
theorem privateCallEntry_restores_storage (p : SemanticProgram) (state : State)
    (instruction : Instruction) (callee : Function) (arguments : List Value) :
    ProjectionStorageEqual
      (restoreValues (privateCallEntry p state instruction callee arguments)
        (privateCallFrame state instruction callee).savedParameters) state := by
  have hentry : ProjectionStorageEqual
      (privateCallEntry p state instruction callee arguments)
      (assignArguments p state callee.parameterCells.toList arguments) := by
    simp [ProjectionStorageEqual, privateCallEntry]
  have hrestored := ProjectionStorageEqual.restoreValues _ _
    (privateCallFrame state instruction callee).savedParameters hentry
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hrestored.1.trans (by
      simpa [privateCallFrame] using
        restore_assigned_values_unbounded p state callee.parameterCells.toList arguments)
  · simp [privateCallEntry, privateCallFrame]
  · simp [privateCallEntry, privateCallFrame]
  · simp [privateCallEntry, privateCallFrame]
  · simp [privateCallEntry, privateCallFrame]

/-- Restoring a new private call frame and then an older private prefix leaves exactly the
    pre-entry prefix-restored Public projection. -/
theorem publicProjection_privateCallEntry_restore_prefix (p : SemanticProgram) (state : State)
    (instruction : Instruction) (callee : Function) (arguments : List Value)
    (privatePrefix : List CallFrame) :
    publicProjection p
        (restoreFrameStack (privateCallEntry p state instruction callee arguments)
          (privateCallFrame state instruction callee :: privatePrefix)) =
      publicProjection p (restoreFrameStack state privatePrefix) := by
  simp only [restoreFrameStack_cons]
  exact ProjectionStorageEqual.publicProjection p
    (ProjectionStorageEqual.restoreFrameStack _ _ privatePrefix
      (privateCallEntry_restores_storage p state instruction callee arguments))

/-- One-sided private entry is the essential independent-length stuttering case. -/
theorem SplitFramePublicEquivalent.enter_private_left {p : SemanticProgram}
    {leftPrivate rightPrivate leftSpine rightSpine : List CallFrame} {left right : State}
    (h : SplitFramePublicEquivalent p leftPrivate rightPrivate leftSpine rightSpine left right)
    (instruction : Instruction) (callee : Function) (arguments : List Value) :
    SplitFramePublicEquivalent p
      (privateCallFrame left instruction callee :: leftPrivate) rightPrivate
      leftSpine rightSpine (privateCallEntry p left instruction callee arguments) right := by
  refine ⟨?_, h.rightStack, h.spineEquivalent, ?_, ?_⟩
  · simp [h.leftStack]
  · simpa using h.externalStreams
  · rw [publicProjection_privateCallEntry_restore_prefix _ _ _ _ _ _]
    exact h.restoredPublic

/-- Symmetric one-sided private entry. -/
theorem SplitFramePublicEquivalent.enter_private_right {p : SemanticProgram}
    {leftPrivate rightPrivate leftSpine rightSpine : List CallFrame} {left right : State}
    (h : SplitFramePublicEquivalent p leftPrivate rightPrivate leftSpine rightSpine left right)
    (instruction : Instruction) (callee : Function) (arguments : List Value) :
    SplitFramePublicEquivalent p leftPrivate
      (privateCallFrame right instruction callee :: rightPrivate)
      leftSpine rightSpine left (privateCallEntry p right instruction callee arguments) := by
  refine ⟨h.leftStack, ?_, h.spineEquivalent, ?_, ?_⟩
  · simp [h.rightStack]
  · simpa using h.externalStreams
  · rw [publicProjection_privateCallEntry_restore_prefix _ _ _ _ _ _]
    exact h.restoredPublic

/-- The two executions may independently enter different private callees and pass different
    private arguments.  Their private-prefix lengths grow together here, while the suspended
    Public spine and restored Public relation are preserved.  One-sided entry is the same lemma
    with the unchanged side retained by the region-stuttering layer. -/
theorem SplitFramePublicEquivalent.enter_private_calls {p : SemanticProgram}
    {leftPrivate rightPrivate leftSpine rightSpine : List CallFrame} {left right : State}
    (h : SplitFramePublicEquivalent p leftPrivate rightPrivate leftSpine rightSpine left right)
    (leftInstruction rightInstruction : Instruction) (leftCallee rightCallee : Function)
    (leftArguments rightArguments : List Value) :
    SplitFramePublicEquivalent p
      (privateCallFrame left leftInstruction leftCallee :: leftPrivate)
      (privateCallFrame right rightInstruction rightCallee :: rightPrivate)
      leftSpine rightSpine
      (privateCallEntry p left leftInstruction leftCallee leftArguments)
      (privateCallEntry p right rightInstruction rightCallee rightArguments) := by
  refine ⟨?_, ?_, h.spineEquivalent, ?_, ?_⟩
  · simp [h.leftStack]
  · simp [h.rightStack]
  · simpa using h.externalStreams
  · rw [publicProjection_privateCallEntry_restore_prefix _ _ _ _ _ _,
      publicProjection_privateCallEntry_restore_prefix _ _ _ _ _ _]
    exact h.restoredPublic

/-- Return from a private frame whose call has no destination.  This is the exact raw return
    state before any subsequent caller instruction executes. -/
def privateReturnNoResult (state : State) (frame : CallFrame) (rest : List CallFrame) : State :=
  { restoreValues state frame.savedParameters with
    pc := frame.returnPc
    callStack := rest }

@[simp] theorem privateReturnNoResult_stack (state : State) (frame : CallFrame)
    (rest : List CallFrame) :
    (privateReturnNoResult state frame rest).callStack = rest := rfl

@[simp] theorem privateReturnNoResult_externalInputs (state : State) (frame : CallFrame)
    (rest : List CallFrame) :
    (privateReturnNoResult state frame rest).externalInputs = state.externalInputs := by
  simp [privateReturnNoResult]

/-- Popping a destination-free private frame preserves the whole-stack caller view.  As above,
    this fact alone is too weak to define the Public relation. -/
theorem callerPublicProjection_privateReturnNoResult (p : SemanticProgram) (state : State)
    (frame : CallFrame) (rest : List CallFrame)
    (hstack : state.callStack = frame :: rest) :
    callerPublicProjection p (privateReturnNoResult state frame rest) =
      callerPublicProjection p state := by
  unfold callerPublicProjection
  rw [hstack]
  simp only [restoreFrameStack_cons]
  apply ProjectionStorageEqual.publicProjection
  apply ProjectionStorageEqual.restoreFrameStack
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The executable pop state, restored through the remaining private prefix, has the same Public
    projection as restoring the original frame and that prefix in place. -/
theorem publicProjection_privateReturnNoResult_restore_prefix (p : SemanticProgram)
    (state : State) (frame : CallFrame) (rest privatePrefix : List CallFrame) :
    publicProjection p
        (restoreFrameStack (privateReturnNoResult state frame rest) privatePrefix) =
      publicProjection p (restoreFrameStack state (frame :: privatePrefix)) := by
  simp only [restoreFrameStack_cons]
  apply ProjectionStorageEqual.publicProjection
  apply ProjectionStorageEqual.restoreFrameStack
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem SplitFramePublicEquivalent.exit_private_left_no_result {p : SemanticProgram}
    {frame : CallFrame} {leftPrivate rightPrivate leftSpine rightSpine : List CallFrame}
    {left right : State}
    (h : SplitFramePublicEquivalent p (frame :: leftPrivate) rightPrivate
      leftSpine rightSpine left right) :
    SplitFramePublicEquivalent p leftPrivate rightPrivate leftSpine rightSpine
      (privateReturnNoResult left frame (leftPrivate ++ leftSpine)) right := by
  refine ⟨rfl, h.rightStack, h.spineEquivalent, ?_, ?_⟩
  · simpa using h.externalStreams
  · rw [publicProjection_privateReturnNoResult_restore_prefix]
    exact h.restoredPublic

theorem SplitFramePublicEquivalent.exit_private_right_no_result {p : SemanticProgram}
    {frame : CallFrame} {leftPrivate rightPrivate leftSpine rightSpine : List CallFrame}
    {left right : State}
    (h : SplitFramePublicEquivalent p leftPrivate (frame :: rightPrivate)
      leftSpine rightSpine left right) :
    SplitFramePublicEquivalent p leftPrivate rightPrivate leftSpine rightSpine left
      (privateReturnNoResult right frame (rightPrivate ++ rightSpine)) := by
  refine ⟨h.leftStack, rfl, h.spineEquivalent, ?_, ?_⟩
  · simpa using h.externalStreams
  · rw [publicProjection_privateReturnNoResult_restore_prefix]
    exact h.restoredPublic

/-! ## Load-bearing recursive-frame counterexample -/

private def witnessValue (payload : Int) : Value := ⟨.pub, payload⟩

private def witnessReturn : Instruction :=
  { op := .output, id := 1, functionId := 2, blockId := 1, destination := 0
    firstOperand := 0, operandCount := 1, target := 0, blockLabel := .pub
    resultLabel := .pub, aux := 0 }

private def witnessRootOutput : Instruction :=
  { op := .output, id := 2, functionId := 1, blockId := 1, destination := 0
    firstOperand := 1, operandCount := 1, target := 0, blockLabel := .pub
    resultLabel := .pub, aux := 0 }

private def witnessProgram : SemanticProgram :=
  { functions := #[]
    instructions := #[witnessReturn, witnessRootOutput]
    operands := #[{ owner := 1, position := 0, value := 0 },
      { owner := 2, position := 0, value := 1 }]
    valueLabels := #[.pub, .pub] }

/-- The suspended Public frame saved the same older caller parameter on both sides.  Its current
    return payload is stored in cell zero and its Public result is written to cell one. -/
private def outerFrame : CallFrame :=
  { returnPc := 1, destination := 1, calleeId := 2, returnLabel := .pub
    savedParameters := [(0, witnessValue 10)] }

/-- The left run is one recursive private activation deeper. -/
private def innerFrame : CallFrame :=
  { returnPc := 0, destination := 0, calleeId := 3, returnLabel := .pub
    savedParameters := [(0, witnessValue 20)] }

private def singlePrivateState : State :=
  { pc := 0, values := #[witnessValue 21, witnessValue 0], aggregates := #[[], []]
    capabilityBalances := #[], callStack := [outerFrame] }

private def nestedPrivateState : State :=
  { singlePrivateState with values := #[witnessValue 30, witnessValue 0], callStack := [innerFrame, outerFrame] }

private def leftAtPublicSpine : State :=
  privateReturnNoResult nestedPrivateState innerFrame [outerFrame]

private def rightAtPublicSpine : State := singlePrivateState

/-- Whole-stack equality is too weak for Public stuttering.  Both sides restore the shared
    spine's saved value `10`, so `callerPublicProjection` declares them equal.  Restoring only the
    genuinely private prefix exposes the different current Public parameters `20` and `21`.
    Those values are returned into a Public result cell and the next root output observably emits
    different payloads.  Consequently the corrected split relation rejects the pair. -/
theorem whole_stack_projection_is_too_weak :
    callerPublicProjection witnessProgram nestedPrivateState =
        callerPublicProjection witnessProgram singlePrivateState ∧
      publicProjection witnessProgram
          (restoreFrameStack nestedPrivateState [innerFrame]) ≠
        publicProjection witnessProgram
          (restoreFrameStack singlePrivateState []) ∧
      ¬ SplitFramePublicEquivalent witnessProgram [innerFrame] [] [outerFrame] [outerFrame]
        nestedPrivateState singlePrivateState ∧
      publicBoundaryTrace (runPrefix witnessProgram 2 leftAtPublicSpine).events ≠
        publicBoundaryTrace (runPrefix witnessProgram 2 rightAtPublicSpine).events := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  intro hsplit
  exact (by decide +kernel :
    publicProjection witnessProgram (restoreFrameStack nestedPrivateState [innerFrame]) ≠
      publicProjection witnessProgram (restoreFrameStack singlePrivateState []))
    hsplit.restoredPublic

end LambdaSigil.Combined.Semantic.PublicFrameSecurity
