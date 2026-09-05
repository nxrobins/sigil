import LambdaSigil.ReleaseSynchronization

/-!
# Public projection and successful raw-run contracts

This module exposes the complete data projection of the existing raw Public relation and records
strict successful completion of the actual machine. It proves no Public noninterference result:
the historical v8 occurrence counterexamples remain valid. Control-region verification, frame
history, and preservation of the stronger active-control obligations remain separate work.
-/

namespace LambdaSigil.Combined.Semantic.PublicRegionSecurity

/-- Keep array shape and statically visible payloads, without consulting runtime value labels. -/
def maskedCells {α β : Type} (visible : Nat → Bool) (payload : α → β)
    (cells : Array α) : Array (Option β) :=
  cells.mapIdx fun position value => if visible position then some (payload value) else none

private theorem maskedCells_eq_iff {α β : Type} (visible : Nat → Bool) (payload : α → β)
    (left right : Array α) :
    maskedCells visible payload left = maskedCells visible payload right ↔
      left.size = right.size ∧
        ∀ position (hl : position < left.size) (hr : position < right.size),
          visible position = true → payload left[position] = payload right[position] := by
  constructor
  · intro heq
    have hsize := congrArg Array.size heq
    simp only [maskedCells, Array.size_mapIdx] at hsize
    refine ⟨hsize, ?_⟩
    intro position hl hr hvisible
    have hcell := congrArg (fun cells => cells[position]?) heq
    simpa [maskedCells, hl, hr, hvisible] using hcell
  · rintro ⟨hsize, hvalues⟩
    apply Array.ext
    · simpa [maskedCells] using hsize
    · intro position hl hr
      have hl' : position < left.size := by simpa [maskedCells] using hl
      have hr' : position < right.size := by simpa [maskedCells] using hr
      by_cases hvisible : visible position = true
      · simpa [maskedCells, hvisible] using hvalues position hl' hr' hvisible
      · simp [maskedCells, hvisible]

/-- Full data snapshot of `PublicDataEquivalent`: Public scalar/aggregate cells, actor state,
    and per-site input positions, including each array's shape. Streams are immutable environment
    data and their equality is stated separately. Control, frames, and capability balances are
    not components of that existing data relation; capability mutation is abstracted by this
    machine. No observations of future execution occur in this snapshot. -/
structure PublicProjection where
  scalars : Array (Option Int)
  aggregates : Array (Option (List Int))
  actorState : Array (Option Int)
  inputPositions : Array (Option Nat)
  deriving Repr, DecidableEq

def publicProjection (p : SemanticProgram) (state : State) : PublicProjection :=
  { scalars := maskedCells (fun cell => (labelAt p.valueLabels (UInt32.ofNat cell)).eqb .pub)
      Value.payload state.values
    aggregates := maskedCells (fun cell => (labelAt p.valueLabels (UInt32.ofNat cell)).eqb .pub)
      id state.aggregates
    actorState := maskedCells (fun offset => (stateLabelAt p (UInt32.ofNat offset)).eqb .pub)
      Value.payload state.actorState
    inputPositions := maskedCells (fun site => (externalSiteLabel p site).eqb .pub)
      id state.externalCursors }

/-- The size conditions are essential: the existing relation is not reflexive on malformed
    scalar arrays. Equality of a projection alone cannot enforce a unary validity condition. -/
theorem publicDataEquivalent_iff_projection (p : SemanticProgram) (left right : State) :
    PublicDataEquivalent p left right ↔
      left.values.size = p.valueLabels.size ∧ right.values.size = p.valueLabels.size ∧
      left.externalInputs = right.externalInputs ∧
      publicProjection p left = publicProjection p right := by
  simp only [PublicDataEquivalent, PublicExternalEquivalent, PublicActorEquivalent,
    PublicAggregateEquivalent, publicProjection, PublicProjection.mk.injEq,
    maskedCells_eq_iff, label_eqb_true_iff, id_eq]
  constructor
  · rintro ⟨⟨hstreams, hcursors⟩, hactor, haggregates, hleft, hright, hscalars⟩
    exact ⟨hleft, hright, hstreams, ⟨hleft.trans hright.symm, hscalars⟩,
      haggregates, hactor, hcursors⟩
  · rintro ⟨hleft, hright, hstreams, ⟨_, hscalars⟩, haggregates, hactor, hcursors⟩
    exact ⟨⟨hstreams, hcursors⟩, hactor, haggregates, hleft, hright, hscalars⟩

/-- Aligned control and saved-frame payloads stay outside the data projection, as in the existing
    cut-point relation. This equivalence does not assert that the control position is verified. -/
theorem publicLowEquivalent_iff_projection (p : SemanticProgram) (left right : State) :
    PublicLowEquivalent p left right ↔
      left.pc = right.pc ∧ left.halted = right.halted ∧ left.trapped = right.trapped ∧
      CallStackPublicEquivalent p left.callStack right.callStack ∧
      left.values.size = p.valueLabels.size ∧ right.values.size = p.valueLabels.size ∧
      left.externalInputs = right.externalInputs ∧
      publicProjection p left = publicProjection p right := by
  rw [PublicLowEquivalent, publicDataEquivalent_iff_projection]

/-- The raw machine may advance per-site cursors, but never replaces the immutable streams. -/
theorem step_preserves_external_inputs (p : SemanticProgram) (state : State) :
    (step p state).state.externalInputs = state.externalInputs := by
  have hordinary (instruction : Instruction) :
      (ordinaryStep p state instruction).state.externalInputs = state.externalInputs := by
    simp [ordinaryStep]
  have hcall (instruction : Instruction) :
      (callStep p state instruction).state.externalInputs = state.externalInputs := by
    unfold callStep
    split
    · rfl
    · dsimp only
      split
      · rfl
      · simp
  unfold step
  split
  · rfl
  · split
    · rfl
    · rename_i instruction _
      cases instruction.op <;> simp only [hordinary, hcall, writeDestination_externalInputs,
        advanceExternal_externalInputs]
      case actorBoundary => split <;> simp
      case output =>
        cases state.callStack with
        | nil => rfl
        | cons frame rest =>
          dsimp only
          split
          · rfl
          · dsimp only
            split <;> simp

theorem runPrefix_preserves_external_inputs (p : SemanticProgram) (budget : Nat)
    (start : State) : (runPrefix p budget start).state.externalInputs = start.externalInputs := by
  induction budget generalizing start with
  | zero => rfl
  | succ budget ih =>
    simpa only [runPrefix, ih] using step_preserves_external_inputs p start

/-- The root invocation is explicit because the raw state has no active-function field. A pushed
    frame identifies the current callee; its tail identifies the suspended caller. -/
def activeFunctionId (root : UInt32) : List CallFrame → UInt32
  | [] => root
  | frame :: _ => frame.calleeId

/-- Static frame coherence checks the actual declarations and instructions, not just numeric
    bounds. For closures, the historical selector and saved payloads still require a separate
    reachability argument; this predicate deliberately does not assert that the call occurred. -/
def FrameDeclarationCoherent (p : SemanticProgram) (caller : UInt32)
    (frame : CallFrame) : Prop :=
  ∃ callerDeclaration callee call continuation,
    functionById? p caller = some callerDeclaration ∧
    functionById? p frame.calleeId = some callee ∧
    0 < frame.returnPc ∧
    p.instructions[frame.returnPc - 1]? = some call ∧
    call.functionId = caller ∧ (call.op = .call ∨ call.op = .closure) ∧
    call.destination = frame.destination ∧
    (call.op = .call → functionOperand? p call = some frame.calleeId) ∧
    p.instructions[frame.returnPc]? = some continuation ∧
    continuation.functionId = caller ∧
    frame.returnLabel = callee.returnLabel ∧
    frame.savedParameters.map Prod.fst = callee.parameterCells.toList

def FrameChainCoherent (p : SemanticProgram) (root : UInt32) : List CallFrame → Prop
  | [] => True
  | frame :: rest =>
      FrameDeclarationCoherent p (activeFunctionId root rest) frame ∧
        FrameChainCoherent p root rest

/-- Stronger active-state obligations required by this foundation. The old `StateWellFormed`
    predicate alone permits an out-of-range instruction cursor and does not identify the active
    function. Neither these extra obligations nor their preservation are claimed verifier-derived.
    Matching verifier-owned region cut points remain outside this unary predicate. -/
structure ActiveState (p : SemanticProgram) (root : UInt32) (state : State) : Prop where
  wellFormed : StateWellFormed p state
  notHalted : state.halted = false
  notTrapped : state.trapped = false
  rootDeclared : ∃ declaration, functionById? p root = some declaration
  activeDeclared : ∃ declaration,
    functionById? p (activeFunctionId root state.callStack) = some declaration
  currentInstruction : ∃ instruction, p.instructions[state.pc]? = some instruction ∧
    instruction.functionId = activeFunctionId root state.callStack
  frameChain : FrameChainCoherent p root state.callStack

/-- A root entry has real decoded provenance and starts outside every suspended invocation.  The
    payload store is intentionally unconstrained beyond `StateWellFormed`: relational clients may
    choose different Secret data while sharing the Public projection. -/
def RootEntryState (p : SemanticProgram) (root : UInt32) (state : State) : Prop :=
  state.callStack = [] ∧ state.halted = false ∧ state.trapped = false ∧
    ∃ declaration,
      functionById? p root = some declaration ∧
        state.pc = declaration.firstInstruction.toNat

/-- Genuine reachability supplies call/closure-frame history without trusting a caller-built
    frame.  The witness is an actual prefix of the raw machine from a decoded root entry. -/
def ReachableFromRoot (p : SemanticProgram) (root : UInt32) (state : State) : Prop :=
  ∃ initial steps events,
    RootEntryState p root initial ∧ StateWellFormed p initial ∧
      runPrefix p steps initial = ⟨state, events⟩

/-- Reusable Public synchronization points are running, reachable states at an instruction whose
    occurrence label is Public in the verifier-derived raw machine. -/
structure VerifiedPublicCutPoint (p : SemanticProgram) (root : UInt32)
    (state : State) : Prop where
  reachable : ReachableFromRoot p root state
  active : ActiveState p root state
  occurrencePublic : ∃ instruction,
    p.instructions[state.pc]? = some instruction ∧ instruction.blockLabel = .pub

theorem ReachableFromRoot.step {p : SemanticProgram} {root : UInt32} {state : State}
    (hreachable : ReachableFromRoot p root state) :
    ReachableFromRoot p root (Semantic.step p state).state := by
  obtain ⟨initial, steps, events, hentry, hwellFormed, hrun⟩ := hreachable
  refine ⟨initial, steps + 1, events ++ (Semantic.step p state).events,
    hentry, hwellFormed, ?_⟩
  rw [ReleaseSynchronization.runPrefix_add p steps 1 initial, hrun]
  simp [runPrefix, Semantic.step]

/-- Exact first completion from an active state. Every strict prefix must be active, the last
    instruction must be a real top-level output or halt, and the endpoint must be well formed,
    halted, nontrapped, and frame-free. Thus invalid-PC fallback halts and callee-local halts are
    not successful. These explicit unary premises are stronger than the existing checker theorem
    and are not a completed Public theorem contract. Arbitrary larger budgets use `SuccessfulRun`.
-/
structure SuccessfulExecution (p : SemanticProgram) (root : UInt32) (steps : Nat)
    (start : State) (result : StepResult) : Prop where
  run : runPrefix p steps start = result
  positive : 0 < steps
  activePrefixes : ∀ elapsed < steps, ActiveState p root (runPrefix p elapsed start).state
  finalWellFormed : StateWellFormed p result.state
  halted : result.state.halted = true
  notTrapped : result.state.trapped = false
  emptyStack : result.state.callStack = []
  lastTopLevel :
    let before := (runPrefix p (steps - 1) start).state
    before.callStack = [] ∧
      ∃ instruction, p.instructions[before.pc]? = some instruction ∧
        (instruction.op = .output ∨ instruction.op = .halt)

/-- A terminal start is admitted only with genuine raw completion provenance, not just a caller-
    supplied halted bit. The prior execution's events are not events of the new execution. -/
def SuccessfulStateProvenance (p : SemanticProgram) (root : UInt32) (state : State) : Prop :=
  ∃ steps start events, SuccessfulExecution p root steps start ⟨state, events⟩

/-- Budgeted successful execution, allowing independent arbitrary fuel budgets and already-
    completed cut-point starts with provenance. The actual `runPrefix` equation is proved below;
    no trace is substituted for machine execution, and termination is never promised. -/
inductive SuccessfulRun (p : SemanticProgram) (root : UInt32) :
    Nat → State → StepResult → Prop
  | completes {budget steps : Nat} {start : State} {result : StepResult}
      (within : steps ≤ budget) (execution : SuccessfulExecution p root steps start result) :
      SuccessfulRun p root budget start result
  | alreadyCompleted {budget : Nat} {start : State}
      (provenance : SuccessfulStateProvenance p root start) :
      SuccessfulRun p root budget start ⟨start, []⟩

/-- This is only a fuel-exhaustion observer: the supplied budget ends in a still-live state. -/
def FuelExhausted (p : SemanticProgram) (budget : Nat) (start : State) : Prop :=
  (runPrefix p budget start).state.halted = false ∧
    (runPrefix p budget start).state.trapped = false

theorem runPrefix_of_stopped (p : SemanticProgram) (budget : Nat) (state : State)
    (hstopped : state.halted = true ∨ state.trapped = true) :
    runPrefix p budget state = ⟨state, []⟩ := by
  induction budget with
  | zero => rfl
  | succ budget ih =>
    have hstep : step p state = ⟨state, []⟩ := by
      rcases hstopped with hhalted | htrapped
      · simp [step, hhalted]
      · simp [step, htrapped]
    simp [runPrefix, hstep, ih]

theorem SuccessfulExecution.at_larger_budget {p : SemanticProgram} {root : UInt32}
    {steps budget : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution p root steps start result) (hwithin : steps ≤ budget) :
    runPrefix p budget start = result := by
  have hbudget : budget = steps + (budget - steps) := (Nat.add_sub_of_le hwithin).symm
  rw [hbudget, ReleaseSynchronization.runPrefix_add, hexecution.run]
  simp [runPrefix_of_stopped p (budget - steps) result.state (Or.inl hexecution.halted)]

/-- Dropping a strict prefix of a genuine successful execution yields another genuine successful
    execution from the actual reached state.  Its length is the exact remaining length, not a
    common relational bound. -/
theorem SuccessfulExecution.drop {p : SemanticProgram} {root : UInt32}
    {steps elapsed : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution p root steps start result)
    (helapsed : elapsed < steps) :
    SuccessfulExecution p root (steps - elapsed)
      (runPrefix p elapsed start).state
      (runPrefix p (steps - elapsed) (runPrefix p elapsed start).state) := by
  let middle := (runPrefix p elapsed start).state
  let remaining := steps - elapsed
  let tail := runPrefix p remaining middle
  have helapsedLe : elapsed ≤ steps := Nat.le_of_lt helapsed
  have htotal : elapsed + remaining = steps := by
    exact Nat.add_sub_of_le helapsedLe
  have hdecompose := ReleaseSynchronization.runPrefix_add p elapsed remaining start
  have htailState : tail.state = result.state := by
    have hstate := congrArg StepResult.state hdecompose
    rw [htotal, hexecution.run] at hstate
    simpa [middle, tail] using hstate.symm
  refine ⟨rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro offset hoffset
    have horiginal := hexecution.activePrefixes (elapsed + offset) (by omega)
    have hadd := ReleaseSynchronization.runPrefix_add p elapsed offset start
    have hstate := congrArg StepResult.state hadd
    change ActiveState p root (runPrefix p offset middle).state
    rw [← hstate]
    exact horiginal
  · rw [htailState]
    exact hexecution.finalWellFormed
  · rw [htailState]
    exact hexecution.halted
  · rw [htailState]
    exact hexecution.notTrapped
  · rw [htailState]
    exact hexecution.emptyStack
  · dsimp only
    have hremainingPositive : 0 < remaining := by omega
    have hbeforeIndex : elapsed + (remaining - 1) = steps - 1 := by omega
    have hadd := ReleaseSynchronization.runPrefix_add p elapsed (remaining - 1) start
    have hstate := congrArg StepResult.state hadd
    rw [hbeforeIndex] at hstate
    change
      let before := (runPrefix p (remaining - 1) middle).state
      before.callStack = [] ∧
        ∃ instruction, p.instructions[before.pc]? = some instruction ∧
          (instruction.op = .output ∨ instruction.op = .halt)
    dsimp only
    rw [← hstate]
    exact hexecution.lastTopLevel

theorem SuccessfulExecution.reached_active {p : SemanticProgram} {root : UInt32}
    {steps elapsed : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution p root steps start result)
    (helapsed : elapsed < steps) :
    ActiveState p root (runPrefix p elapsed start).state :=
  hexecution.activePrefixes elapsed helapsed

theorem SuccessfulExecution.start_active {p : SemanticProgram} {root : UInt32}
    {steps : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution p root steps start result) :
    ActiveState p root start := by
  simpa only [runPrefix] using hexecution.activePrefixes 0 hexecution.positive

theorem SuccessfulExecution.start_not_halted {p : SemanticProgram} {root : UInt32}
    {steps : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution p root steps start result) :
    start.halted = false :=
  hexecution.start_active.notHalted

theorem SuccessfulExecution.start_not_trapped {p : SemanticProgram} {root : UInt32}
    {steps : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution p root steps start result) :
    start.trapped = false :=
  hexecution.start_active.notTrapped

/-- The contract observes the unchanged raw machine, including all original events. -/
theorem SuccessfulRun.runPrefix_eq {p : SemanticProgram} {root : UInt32} {budget : Nat}
    {start : State} {result : StepResult} (hrun : SuccessfulRun p root budget start result) :
    runPrefix p budget start = result := by
  cases hrun with
  | completes hwithin hexecution => exact hexecution.at_larger_budget hwithin
  | alreadyCompleted hprovenance =>
    obtain ⟨_, _, _, hexecution⟩ := hprovenance
    exact runPrefix_of_stopped p budget start (Or.inl hexecution.halted)

/-- A successful budget is either backed by one exact positive execution inside the budget, or
    starts in a genuinely completed state with prior raw provenance.  This eliminates the tempting
    but invalid third case where fuel merely expires at a live state. -/
theorem SuccessfulRun.execution_or_completed {p : SemanticProgram} {root : UInt32}
    {budget : Nat} {start : State} {result : StepResult}
    (hrun : SuccessfulRun p root budget start result) :
    (∃ steps, steps ≤ budget ∧ SuccessfulExecution p root steps start result) ∨
      (start.halted = true ∧ result = ⟨start, []⟩ ∧
        SuccessfulStateProvenance p root start) := by
  cases hrun with
  | completes hwithin hexecution => exact Or.inl ⟨_, hwithin, hexecution⟩
  | alreadyCompleted hprovenance =>
      obtain ⟨_, _, _, hexecution⟩ := hprovenance
      exact Or.inr ⟨hexecution.halted, rfl, ⟨_, _, _, hexecution⟩⟩

theorem SuccessfulRun.completed {p : SemanticProgram} {root : UInt32} {budget : Nat}
    {start : State} {result : StepResult} (hrun : SuccessfulRun p root budget start result) :
    StateWellFormed p result.state ∧ result.state.halted = true ∧
      result.state.trapped = false ∧ result.state.callStack = [] := by
  cases hrun with
  | completes _ hexecution =>
    exact ⟨hexecution.finalWellFormed, hexecution.halted, hexecution.notTrapped,
      hexecution.emptyStack⟩
  | alreadyCompleted hprovenance =>
    obtain ⟨_, _, _, hexecution⟩ := hprovenance
    exact ⟨hexecution.finalWellFormed, hexecution.halted, hexecution.notTrapped,
      hexecution.emptyStack⟩

theorem SuccessfulRun.not_fuel_exhausted {p : SemanticProgram} {root : UInt32}
    {budget : Nat} {start : State} {result : StepResult}
    (hrun : SuccessfulRun p root budget start result) : ¬ FuelExhausted p budget start := by
  intro hexhausted
  rw [FuelExhausted, hrun.runPrefix_eq] at hexhausted
  rw [hrun.completed.2.1] at hexhausted
  cases hexhausted.1

theorem SuccessfulRun.not_trapped {p : SemanticProgram} {root : UInt32}
    {budget : Nat} {start : State} {result : StepResult}
    (hrun : SuccessfulRun p root budget start result) :
    (runPrefix p budget start).state.trapped = false := by
  rw [hrun.runPrefix_eq]
  exact hrun.completed.2.2.1

theorem SuccessfulRun.at_larger_budget {p : SemanticProgram} {root : UInt32}
    {budget larger : Nat} {start : State} {result : StepResult}
    (hrun : SuccessfulRun p root budget start result) (hbudget : budget ≤ larger) :
    SuccessfulRun p root larger start result := by
  cases hrun with
  | completes hwithin hexecution =>
    exact .completes (Nat.le_trans hwithin hbudget) hexecution
  | alreadyCompleted hprovenance => exact .alreadyCompleted hprovenance

/-- A live invalid cursor cannot acquire a success witness merely because the raw fallback sets
    its halted bit. This is stricter than the old endpoint flag and numeric-state checks. -/
theorem no_success_from_live_missing_instruction {p : SemanticProgram} {root : UInt32}
    {budget : Nat} {start : State} {result : StepResult}
    (hlive : start.halted = false) (hmissing : p.instructions[start.pc]? = none) :
    ¬ SuccessfulRun p root budget start result := by
  intro hrun
  cases hrun with
  | completes _ hexecution =>
    have hactive := hexecution.activePrefixes 0 hexecution.positive
    obtain ⟨instruction, hlookup, _⟩ := hactive.currentInstruction
    simp only [runPrefix] at hlookup
    rw [hmissing] at hlookup
    cases hlookup
  | alreadyCompleted hprovenance =>
    obtain ⟨_, _, _, hexecution⟩ := hprovenance
    have hhalted := hexecution.halted
    simp only at hhalted
    rw [hlive] at hhalted
    cases hhalted

private def haltInstruction : Instruction :=
  { op := .halt, id := 1, functionId := 1, blockId := 1, destination := 0,
    firstOperand := 0, operandCount := 0, target := 0, resultLabel := .pub, aux := 0 }

private def haltFunction : Function :=
  { id := 1, entry := 1, firstInstruction := 0, instructionCount := 1 }

private def haltProgram : SemanticProgram :=
  { functions := #[haltFunction], instructions := #[haltInstruction], operands := #[],
    valueLabels := #[] }

private def haltStart : State :=
  { pc := 0, values := #[], aggregates := #[], capabilityBalances := #[] }

private theorem haltExecution :
    SuccessfulExecution haltProgram 1 1 haltStart (runPrefix haltProgram 1 haltStart) := by
  refine ⟨rfl, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro elapsed helapsed
    have helapsed' : elapsed = 0 := by omega
    subst elapsed
    change ActiveState haltProgram 1 haltStart
    refine ⟨?_, rfl, rfl, ?_, ?_, ?_, trivial⟩
    · simp [StateWellFormed, haltProgram, haltStart, ExternalStateWellFormed]
    · exact ⟨haltFunction, by decide +kernel⟩
    · exact ⟨haltFunction, by decide +kernel⟩
    · exact ⟨haltInstruction, by decide +kernel, rfl⟩
  · simp [runPrefix, step, haltProgram, haltStart, haltInstruction, ordinaryStep,
      writeDestination, StateWellFormed, ExternalStateWellFormed]
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ⟨rfl, haltInstruction, by decide +kernel, Or.inr rfl⟩

/-- A genuine execution inhabits the contract at its first halt, at a larger fuel budget, and
    when resuming from the proven terminal state with zero budget. The latter emits no history. -/
theorem successfulRun_accepts_padding_and_completed_starts :
    SuccessfulRun haltProgram 1 1 haltStart (runPrefix haltProgram 1 haltStart) ∧
    SuccessfulRun haltProgram 1 7 haltStart (runPrefix haltProgram 1 haltStart) ∧
    SuccessfulRun haltProgram 1 0 (runPrefix haltProgram 1 haltStart).state
      ⟨(runPrefix haltProgram 1 haltStart).state, []⟩ := by
  refine ⟨.completes (by decide) haltExecution,
    .completes (by decide) haltExecution, .alreadyCompleted ?_⟩
  exact ⟨1, haltStart, (runPrefix haltProgram 1 haltStart).events, haltExecution⟩

/-- The raw invalid-PC fallback really halts, but that observable flag is not a successful run. -/
theorem implicit_halt_is_not_successful :
    (runPrefix haltProgram 1 { haltStart with pc := 1 }).state.halted = true ∧
    ¬ SuccessfulRun haltProgram 1 1 { haltStart with pc := 1 }
      (runPrefix haltProgram 1 { haltStart with pc := 1 }) := by
  constructor
  · decide +kernel
  · exact no_success_from_live_missing_instruction rfl (by decide +kernel)

/-! ## Whole-stack restoration algebra

The historical raw machine stores SSA cells globally and saves only parameter cells at a call.
Consequently two executions stuttering through different private callees need not have equal raw
arrays or equal stack depth.  The view below is proof-only: it restores the saved parameter images
from every active frame, from the innermost frame outwards, and then takes the complete Public data
projection.  It never feeds a value back to `step`.  It is an algebraic helper, not the Public
stuttering relation: restoring a shared active Public frame could mask its current Public
parameter values.  `PublicFrameSecurity` restores only each unmatched private prefix.

Restoring the whole stack in this order is important for recursion.  If nested activations save the
same parameter cell, the outermost saved value is written last and therefore reconstructs the
actual caller-visible cell.
-/

def restoreFrameStack (state : State) : List CallFrame → State
  | [] => state
  | frame :: rest => restoreFrameStack (restoreValues state frame.savedParameters) rest

def callerPublicProjection (p : SemanticProgram) (state : State) : PublicProjection :=
  publicProjection p (restoreFrameStack state state.callStack)

@[simp] theorem restoreFrameStack_nil (state : State) :
    restoreFrameStack state [] = state := rfl

@[simp] theorem restoreFrameStack_cons (state : State) (frame : CallFrame)
    (rest : List CallFrame) :
    restoreFrameStack state (frame :: rest) =
      restoreFrameStack (restoreValues state frame.savedParameters) rest := rfl

@[simp] theorem callerPublicProjection_empty_stack (p : SemanticProgram) (state : State)
    (hstack : state.callStack = []) :
    callerPublicProjection p state = publicProjection p state := by
  simp [callerPublicProjection, hstack]

@[simp] theorem restoreFrameStack_aggregates (state : State) (frames : List CallFrame) :
    (restoreFrameStack state frames).aggregates = state.aggregates := by
  induction frames generalizing state with
  | nil => rfl
  | cons frame rest ih =>
      simpa only [restoreFrameStack, restoreValues_aggregates] using
        ih (restoreValues state frame.savedParameters)

@[simp] theorem restoreFrameStack_actorState (state : State) (frames : List CallFrame) :
    (restoreFrameStack state frames).actorState = state.actorState := by
  induction frames generalizing state with
  | nil => rfl
  | cons frame rest ih =>
      simpa only [restoreFrameStack, restoreValues_actorState] using
        ih (restoreValues state frame.savedParameters)

@[simp] theorem restoreFrameStack_externalInputs (state : State) (frames : List CallFrame) :
    (restoreFrameStack state frames).externalInputs = state.externalInputs := by
  induction frames generalizing state with
  | nil => rfl
  | cons frame rest ih =>
      simpa only [restoreFrameStack, restoreValues_externalInputs] using
        ih (restoreValues state frame.savedParameters)

@[simp] theorem restoreFrameStack_externalCursors (state : State) (frames : List CallFrame) :
    (restoreFrameStack state frames).externalCursors = state.externalCursors := by
  induction frames generalizing state with
  | nil => rfl
  | cons frame rest ih =>
      simpa only [restoreFrameStack, restoreValues_externalCursors] using
        ih (restoreValues state frame.savedParameters)

/-- The frame-restored view has exactly the same non-scalar Public components as the raw state.
    Only the scalar array can differ, and only at saved parameter keys. -/
theorem callerPublicProjection_components (p : SemanticProgram) (state : State) :
    (callerPublicProjection p state).aggregates = (publicProjection p state).aggregates ∧
      (callerPublicProjection p state).actorState = (publicProjection p state).actorState ∧
      (callerPublicProjection p state).inputPositions =
        (publicProjection p state).inputPositions := by
  simp [callerPublicProjection, publicProjection]

theorem readValue_restore_saved (before current : State) (cells : List UInt32)
    (cell : UInt32) (hsize : before.values.size = current.values.size) :
    readValue (restoreValues current (saveValues before cells)) cell =
      if cell ∈ cells then readValue before cell else readValue current cell := by
  induction cells generalizing current with
  | nil => simp [saveValues, restoreValues]
  | cons saved rest ih =>
      simp only [saveValues, List.map_cons, restoreValues]
      let updated : State :=
        { current with
          values := current.values.setIfInBounds saved.toNat (readValue before saved) }
      change readValue (restoreValues updated (saveValues before rest)) cell = _
      have hupdatedSize : before.values.size = updated.values.size := by
        simpa [updated] using hsize
      rw [ih updated hupdatedSize]
      by_cases hrest : cell ∈ rest
      · simp [hrest]
      · by_cases heq : cell = saved
        · subst saved
          by_cases hbound : cell.toNat < current.values.size
          · simp [hrest, updated, readValue, Array.getD, hbound, hsize]
          · simp [hrest, updated, readValue, Array.getD, hbound, hsize]
        · by_cases hbound : cell.toNat < current.values.size
          · have hnat : saved.toNat ≠ cell.toNat := by
              intro heqNat
              exact heq (UInt32.toNat_inj.mp heqNat.symm)
            simp [hrest, heq, updated, readValue, Array.getD, hbound, hnat]
          · simp [hrest, heq, updated, readValue, Array.getD, hbound]

theorem readValue_assignArguments_outside (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) (cell : UInt32)
    (houtside : cell ∉ parameters) :
    readValue (assignArguments p state parameters arguments) cell = readValue state cell := by
  induction parameters generalizing state arguments with
  | nil => cases arguments <;> rfl
  | cons parameter parameters ih =>
      cases arguments with
      | nil => rfl
      | cons argument arguments =>
          have hne : cell ≠ parameter := by
            intro heq
            exact houtside (by simp [heq])
          have htail : cell ∉ parameters := by
            intro hmem
            exact houtside (List.mem_cons_of_mem parameter hmem)
          rw [assignArguments, ih _ _ htail]
          by_cases hbound : cell.toNat < state.values.size
          · have hnat : parameter.toNat ≠ cell.toNat := by
              intro heq
              exact hne (UInt32.toNat_inj.mp heq.symm)
            simp [readValue, Array.getD, hbound, hnat]
          · simp [readValue, Array.getD, hbound]

/-- Saving before entry and restoring on the caller view hides every temporary parameter
    assignment, even when a malformed in-memory parameter list repeats a cell.  Call acceptance
    separately checks arity and bounds; this identity itself needs neither uniqueness nor a
    payload-label assumption. -/
theorem readValue_restore_assigned (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value) (cell : UInt32) :
    readValue
        (restoreValues (assignArguments p state parameters arguments)
          (saveValues state parameters)) cell =
      readValue state cell := by
  rw [readValue_restore_saved _ _ _ _ (by simp)]
  split
  · rfl
  · rename_i houtside
    exact readValue_assignArguments_outside p state parameters arguments cell houtside

theorem publicProjection_restore_assigned (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value)
    (hbound : state.values.size ≤ 2 ^ 32) :
    publicProjection p
        (restoreValues (assignArguments p state parameters arguments)
          (saveValues state parameters)) =
      publicProjection p state := by
  let restored := restoreValues (assignArguments p state parameters arguments)
    (saveValues state parameters)
  have hsize : restored.values.size = state.values.size := by
    simp [restored]
  simp only [publicProjection, PublicProjection.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (maskedCells_eq_iff _ _ _ _).mpr
    refine ⟨hsize, ?_⟩
    intro position hl hr _
    have hposition : position < 2 ^ 32 := by omega
    have hnat : (UInt32.ofNat position).toNat = position := by
      simp [Nat.mod_eq_of_lt hposition]
    have hread := readValue_restore_assigned p state parameters arguments
      (UInt32.ofNat position)
    simpa [restored, readValue, Array.getD, hl, hr, hnat] using
      congrArg Value.payload hread
  · simp
  · simp
  · simp

theorem restore_assigned_values (p : SemanticProgram) (state : State)
    (parameters : List UInt32) (arguments : List Value)
    (hbound : state.values.size ≤ 2 ^ 32) :
    (restoreValues (assignArguments p state parameters arguments)
      (saveValues state parameters)).values = state.values := by
  apply Array.ext
  · simp
  · intro position hl hr
    have hposition : position < 2 ^ 32 := by omega
    have hnat : (UInt32.ofNat position).toNat = position := by
      simp [Nat.mod_eq_of_lt hposition]
    have hread := readValue_restore_assigned p state parameters arguments
      (UInt32.ofNat position)
    simpa [readValue, Array.getD, hl, hr, hnat] using hread

def ProjectionStorageEqual (left right : State) : Prop :=
  left.values = right.values ∧ left.aggregates = right.aggregates ∧
    left.actorState = right.actorState ∧ left.externalInputs = right.externalInputs ∧
    left.externalCursors = right.externalCursors

theorem restoreValues_values_congr {left right : State}
    (hvalues : left.values = right.values) (saved : List (UInt32 × Value)) :
    (restoreValues left saved).values = (restoreValues right saved).values := by
  induction saved generalizing left right with
  | nil => exact hvalues
  | cons pair rest ih =>
      rcases pair with ⟨cell, value⟩
      apply ih
      exact congrArg (fun values => values.setIfInBounds cell.toNat value) hvalues

theorem ProjectionStorageEqual.restoreValues (left right : State)
    (saved : List (UInt32 × Value)) (h : ProjectionStorageEqual left right) :
    ProjectionStorageEqual (restoreValues left saved) (restoreValues right saved) := by
  induction saved generalizing left right with
  | nil => exact h
  | cons pair rest ih =>
      rcases pair with ⟨cell, value⟩
      apply ih
      simp only [ProjectionStorageEqual]
      exact ⟨congrArg (fun values => values.setIfInBounds cell.toNat value) h.1,
        h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem ProjectionStorageEqual.restoreFrameStack (left right : State)
    (frames : List CallFrame) (h : ProjectionStorageEqual left right) :
    ProjectionStorageEqual (restoreFrameStack left frames) (restoreFrameStack right frames) := by
  induction frames generalizing left right with
  | nil => exact h
  | cons frame rest ih =>
      exact ih _ _ (h.restoreValues left right frame.savedParameters)

theorem ProjectionStorageEqual.publicProjection (p : SemanticProgram) {left right : State}
    (h : ProjectionStorageEqual left right) :
    publicProjection p left = publicProjection p right := by
  rcases h with ⟨hvalues, haggregates, hactor, _, hcursors⟩
  unfold LambdaSigil.Combined.Semantic.PublicRegionSecurity.publicProjection
  rw [hvalues, haggregates, hactor, hcursors]

/-- A successful raw call entry may change stack depth and parameter cells, but whole-stack
    restoration is algebraically unchanged. `PublicFrameSecurity` uses this only to derive its
    stronger private-prefix fact; equality of the whole-stack view is deliberately insufficient. -/
theorem callerPublicProjection_entered (p : SemanticProgram) (state : State)
    (instruction : Instruction) (callee : Function) (arguments : List Value)
    (hbound : state.values.size ≤ 2 ^ 32) :
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
  let restored := restoreValues
    (assignArguments p state callee.parameterCells.toList arguments)
    (saveValues state callee.parameterCells.toList)
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
          (restore_assigned_values p state callee.parameterCells.toList arguments hbound)
    · simp [restoredEntered, enteredState]
    · simp [restoredEntered, enteredState]
    · simp [restoredEntered, enteredState]
    · simp [restoredEntered, enteredState]
  change publicProjection p (restoreFrameStack restoredEntered state.callStack) = _
  exact (hstorage.restoreFrameStack restoredEntered state state.callStack).publicProjection p

/-! ## Public external-site occurrence is independent of result secrecy -/

private def publicOccurrenceSecretResult : Instruction :=
  { op := .ffi, id := 0, functionId := 1, blockId := 1, destination := 1,
    firstOperand := 0, operandCount := 0, target := 0,
    blockLabel := .pub, resultLabel := .secret, aux := 0 }

private def publicOccurrenceSecretResultProgram : SemanticProgram :=
  { functions := #[], instructions := #[publicOccurrenceSecretResult], operands := #[],
    valueLabels := #[.pub, .secret] }

private def publicCursorState (cursor : Nat) : State :=
  { pc := 0, values := #[⟨.pub, 0⟩, ⟨.secret, 0⟩], aggregates := #[[], []],
    capabilityBalances := #[], externalInputs := #[[10, 20]], externalCursors := #[cursor] }

private def payloadJoinedExternalSiteLabel (p : SemanticProgram) (site : Nat) : Label :=
  match p.instructions.find? (fun instruction => instruction.id.toNat == site) with
  | some instruction => instruction.blockLabel.lub instruction.resultLabel
  | none => .pub

private def payloadJoinedInputProjection (p : SemanticProgram) (state : State) :
    Array (Option Nat) :=
  maskedCells (fun site => (payloadJoinedExternalSiteLabel p site).eqb .pub)
    id state.externalCursors

/-- Load-bearing classifier witness: a Public FFI occurrence remains a Public site even when its
    result is Secret. Joining payload secrecy into the occurrence label would erase unequal
    Public-site cursor positions from the promised final projection. -/
theorem public_site_cursor_is_not_hidden_by_secret_result :
    (publicProjection publicOccurrenceSecretResultProgram (publicCursorState 0)).inputPositions ≠
      (publicProjection publicOccurrenceSecretResultProgram (publicCursorState 1)).inputPositions ∧
    payloadJoinedInputProjection publicOccurrenceSecretResultProgram (publicCursorState 0) =
      payloadJoinedInputProjection publicOccurrenceSecretResultProgram (publicCursorState 1) := by
  decide +kernel

end LambdaSigil.Combined.Semantic.PublicRegionSecurity
