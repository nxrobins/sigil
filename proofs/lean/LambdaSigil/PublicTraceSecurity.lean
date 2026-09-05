import LambdaSigil.PublicLocalSecurity
import LambdaSigil.PublicFrameSecurity
import LambdaSigil.V9OccurrenceKernelSecurity

/-!
# Public boundary traces and per-site external-input isolation

This module packages the event- and tape-local facts used by the independent-length Public proof.
Public boundary observations retain occurrence, site, and order even when their payload is hidden.
External input is modeled by immutable per-site streams, so activity at one site cannot shift any
other site.  None of these lemmas assumes equal execution lengths.
-/

namespace LambdaSigil.Combined.V9.PublicTraceSecurity

open Semantic BoundaryContracts OccurrenceDataflowInvocation OccurrenceKernel
open OccurrenceKernelSecurity PublicLocalSecurity

/-! ## Exact Public boundary observations -/

def observationPayload (value : Value) : Option Int :=
  if value.label.eqb .pub then some value.payload else none

/-- Output payload visibility includes the verifier-derived occurrence of the return expression;
    the external occurrence site itself remains the stable declaration-owned root site. -/
def outputObservationPayload (instruction : Instruction) (value : Value) : Option Int :=
  if (value.label.lub instruction.outputPayloadOccurrence).eqb .pub then some value.payload
  else none

def boundaryObservations (site : UInt32) (values : List Value) :
    List PublicBoundaryObservation :=
  values.map fun value => ⟨.boundary, site, observationPayload value⟩

@[simp] theorem publicBoundaryTrace_public_boundary_values (site : UInt32)
    (values : List Value) :
    publicBoundaryTrace (eventsForValuesUnderPc .boundary site .pub values) =
      boundaryObservations site values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp [eventsForValuesUnderPc, publicBoundaryTrace, publicBoundaryObservation?,
        boundaryObservations, observationPayload, EventKind.eqb, Label.eqb]

/-- A Public actor occurrence preserves one observation per policy payload, in the original order.
    Every observation retains the exact site.  A non-Public payload becomes `none`; it is never
    replaced with a fabricated integer. -/
theorem public_actor_instruction_observations (machine : SemanticProgram) (state : State)
    (instruction : Instruction) (hop : instruction.op = .actorBoundary)
    (hpublic : instruction.blockLabel = .pub) :
    publicBoundaryTrace (instructionEvents machine state instruction) =
      boundaryObservations instruction.id (policyOperandValues machine state instruction 8) := by
  simp [instructionEvents, hop, hpublic]

/-- A Public output always contributes exactly one ordered occurrence at its canonical root site.
    Only the payload field is conditional on the operand label joined with its local occurrence. -/
theorem public_output_instruction_observation (machine : SemanticProgram) (state : State)
    (instruction : Instruction) (hop : instruction.op = .output)
    (hpublic : instruction.blockLabel = .pub) :
    publicBoundaryTrace (instructionEvents machine state instruction) =
      [⟨.output, outputBoundarySite machine instruction,
        outputObservationPayload instruction (operandValue machine state instruction)⟩] := by
  simp [instructionEvents, hop, hpublic, publicBoundaryTrace, publicBoundaryObservation?,
    outputObservationPayload, operandValue, EventKind.eqb, Label.eqb]

/-- Matching Public actor occurrences emit the same ordered sites and optional payloads.  The
    operand-list equality is the exact local dependency obligation supplied at a Public cut. -/
theorem matching_public_actor_instruction_observations (machine : SemanticProgram)
    (left right : State) (instruction : Instruction) (hop : instruction.op = .actorBoundary)
    (hpublic : instruction.blockLabel = .pub)
    (hvalues : policyOperandValues machine left instruction 8 =
      policyOperandValues machine right instruction 8) :
    publicBoundaryTrace (instructionEvents machine left instruction) =
      publicBoundaryTrace (instructionEvents machine right instruction) := by
  rw [public_actor_instruction_observations machine left instruction hop hpublic,
    public_actor_instruction_observations machine right instruction hop hpublic, hvalues]

/-- Matching Public output occurrences emit the same exact site and optional payload. -/
theorem matching_public_output_instruction_observation (machine : SemanticProgram)
    (left right : State) (instruction : Instruction) (hop : instruction.op = .output)
    (hpublic : instruction.blockLabel = .pub)
    (hvalue : operandValue machine left instruction = operandValue machine right instruction) :
    publicBoundaryTrace (instructionEvents machine left instruction) =
      publicBoundaryTrace (instructionEvents machine right instruction) := by
  rw [public_output_instruction_observation machine left instruction hop hpublic,
    public_output_instruction_observation machine right instruction hop hpublic, hvalue]

/-- Step-level actor form used by execution composition.  It retains the actual stable site and
    ordered optional payloads, rather than comparing a site-erased projection. -/
theorem matching_public_actor_step_observations (machine : SemanticProgram) (left right : State)
    (instruction : Instruction) (hleftReady : ¬(left.halted || left.trapped))
    (hrightReady : ¬(right.halted || right.trapped))
    (hleftLookup : machine.instructions[left.pc]? = some instruction)
    (hrightLookup : machine.instructions[right.pc]? = some instruction)
    (hop : instruction.op = .actorBoundary) (hpublic : instruction.blockLabel = .pub)
    (hvalues : policyOperandValues machine left instruction 8 =
      policyOperandValues machine right instruction 8) :
    publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events := by
  rw [step, if_neg hleftReady, hleftLookup, step, if_neg hrightReady, hrightLookup]
  simpa [hop] using
    matching_public_actor_instruction_observations machine left right instruction hop hpublic
      hvalues

/-- A matching top-level Public output step has the same exact observation.  Empty call stacks
    make explicit that these are boundary outputs, not internal returns. -/
theorem matching_public_output_step_observation (machine : SemanticProgram) (left right : State)
    (instruction : Instruction) (hleftReady : ¬(left.halted || left.trapped))
    (hrightReady : ¬(right.halted || right.trapped))
    (hleftLookup : machine.instructions[left.pc]? = some instruction)
    (hrightLookup : machine.instructions[right.pc]? = some instruction)
    (hleftStack : left.callStack = []) (hrightStack : right.callStack = [])
    (hop : instruction.op = .output) (hpublic : instruction.blockLabel = .pub)
    (hvalue : operandValue machine left instruction = operandValue machine right instruction) :
    publicBoundaryTrace (step machine left).events =
      publicBoundaryTrace (step machine right).events := by
  rw [step, if_neg hleftReady, hleftLookup, step, if_neg hrightReady, hrightLookup]
  simpa [hop, hleftStack, hrightStack] using
    matching_public_output_instruction_observation machine left right instruction hop hpublic
      hvalue

/-- The v9 actor-site decision supplies the Public occurrence premise used by the exact trace
    equation; Rust supplies neither the observation nor a trusted visibility bit. -/
theorem verified_actor_instruction_observations {program : V9.Program} {analysis : Analysis}
    {machine : SemanticProgram} {state : State} {instruction : Instruction} {pc position : Nat}
    {contract : ActorContract}
    (hmachine : machine = rawSemanticProgram program analysis)
    (hsafe : SiteKindOccurrenceSafe program analysis instruction pc (.actor position contract))
    (hop : instruction.op = .actorBoundary) :
    publicBoundaryTrace (instructionEvents machine state instruction) =
      boundaryObservations instruction.id (policyOperandValues machine state instruction 8) := by
  subst machine
  exact public_actor_instruction_observations _ _ _ hop
    (actor_site_has_public_occurrence hsafe)

/-! ## Per-site cursor isolation -/

private theorem getD_setIfInBounds_of_ne {α : Type} (cells : Array α) (updated : Nat)
    (value fallback : α) (observed : Nat) (hne : updated ≠ observed) :
    (cells.setIfInBounds updated value).getD observed fallback =
      cells.getD observed fallback := by
  by_cases hbound : observed < cells.size
  · simp [Array.getD, hbound, hne]
  · simp [Array.getD, hbound]

/-- `advanceExternal` can change only the cursor indexed by its own stable site ID. -/
theorem advanceExternal_cursor_other (state : State) (site : UInt32) (observed : Nat)
    (hne : site.toNat ≠ observed) :
    (advanceExternal state site).externalCursors.getD observed 0 =
      state.externalCursors.getD observed 0 := by
  unfold advanceExternal
  dsimp only
  split
  · exact getD_setIfInBounds_of_ne _ _ _ _ _ hne
  · rfl

/-- At an in-bounds site the cursor increments exactly once when input remains, and remains fixed
    when the stream is exhausted. -/
theorem advanceExternal_cursor_same (state : State) (site : UInt32)
    (hbound : site.toNat < state.externalCursors.size) :
    (advanceExternal state site).externalCursors.getD site.toNat 0 =
      if state.externalCursors.getD site.toNat 0 <
          (state.externalInputs.getD site.toNat []).length then
        state.externalCursors.getD site.toNat 0 + 1
      else state.externalCursors.getD site.toNat 0 := by
  let cursor := state.externalCursors.getD site.toNat 0
  let stream := state.externalInputs.getD site.toNat []
  change (if cursor < stream.length then
      state.externalCursors.setIfInBounds site.toNat (cursor + 1)
    else state.externalCursors).getD site.toNat 0 =
      if cursor < stream.length then cursor + 1 else cursor
  by_cases hremaining : cursor < stream.length
  · simp only [hremaining, if_pos]
    simp [Array.getD, hbound]
  · have hcursor : cursor = state.externalCursors[site.toNat] := by
      simp [cursor, hbound]
    rw [hcursor] at hremaining
    simp [hremaining, hcursor, Array.getD, hbound]

/-- An FFI step changes no cursor other than its own stable site. -/
theorem ffi_step_cursor_other (machine : SemanticProgram) (state : State)
    (instruction : Instruction) (observed : Nat)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hop : instruction.op = .ffi)
    (hne : instruction.id.toNat ≠ observed) :
    (step machine state).state.externalCursors.getD observed 0 =
      state.externalCursors.getD observed 0 := by
  by_cases hdone : state.halted || state.trapped
  · simp [step, hdone]
  rw [step, if_neg hdone, hlookup]
  simp [hop, advanceExternal_cursor_other _ _ _ hne]

/-- An actor input step changes no cursor other than its own stable site.  Actor sends with no
    destination do not advance even that site. -/
theorem actor_step_cursor_other (machine : SemanticProgram) (state : State)
    (instruction : Instruction) (observed : Nat)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hop : instruction.op = .actorBoundary)
    (hne : instruction.id.toNat ≠ observed) :
    (step machine state).state.externalCursors.getD observed 0 =
      state.externalCursors.getD observed 0 := by
  by_cases hdone : state.halted || state.trapped
  · simp [step, hdone]
  rw [step, if_neg hdone, hlookup]
  by_cases hdestination : instruction.destination = 0
  · simp [hop, hdestination]
  · simp [hop, hdestination, advanceExternal_cursor_other _ _ _ hne]

/-- A private external site cannot share its numeric site with a statically Public site. -/
theorem private_site_ne_public_site (machine : SemanticProgram) (privateSite : UInt32)
    (publicSite : Nat)
    (hprivate : externalSiteLabel machine privateSite.toNat ≠ .pub)
    (hpublic : externalSiteLabel machine publicSite = .pub) :
    privateSite.toNat ≠ publicSite := by
  intro heq
  exact hprivate (heq ▸ hpublic)

/-- Therefore a step at a private FFI/actor site cannot advance any Public site's cursor. -/
theorem private_external_step_preserves_public_cursor (machine : SemanticProgram) (state : State)
    (instruction : Instruction) (publicSite : Nat)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hexternal : instruction.op = .ffi ∨ instruction.op = .actorBoundary)
    (hprivate : externalSiteLabel machine instruction.id.toNat ≠ .pub)
    (hpublic : externalSiteLabel machine publicSite = .pub) :
    (step machine state).state.externalCursors.getD publicSite 0 =
      state.externalCursors.getD publicSite 0 := by
  have hne := private_site_ne_public_site machine instruction.id publicSite hprivate hpublic
  rcases hexternal with hop | hop
  · exact ffi_step_cursor_other machine state instruction publicSite hlookup hop hne
  · exact actor_step_cursor_other machine state instruction publicSite hlookup hop hne

/-! ## Equal reads, including exhaustion -/

/-- Immutable equality of one site's stream and equality of its cursor are the complete inputs to
    `readExternal`.  This statement has no in-bounds or non-exhaustion premise: missing and
    exhausted reads deterministically return zero on both sides. -/
theorem readExternal_eq_of_stream_and_cursor {left right : State} {site : UInt32}
    (hstream : left.externalInputs.getD site.toNat [] =
      right.externalInputs.getD site.toNat [])
    (hcursor : left.externalCursors.getD site.toNat 0 =
      right.externalCursors.getD site.toNat 0) :
    readExternal left site = readExternal right site := by
  unfold readExternal
  rw [hstream, hcursor]

/-- Total form of the Public-site read theorem.  It covers an absent cursor slot and an exhausted
    stream as well as the ordinary in-bounds case. -/
theorem public_readExternal_eq_total {machine : SemanticProgram} {left right : State}
    (hexternal : PublicExternalEquivalent machine left right) {site : UInt32}
    (hpublic : externalSiteLabel machine site.toNat = .pub) :
    readExternal left site = readExternal right site := by
  rcases hexternal with ⟨hinputs, hsize, hcursors⟩
  by_cases hleft : site.toNat < left.externalCursors.size
  · have hright : site.toNat < right.externalCursors.size := by simpa [hsize] using hleft
    exact public_readExternal_eq ⟨hinputs, hsize, hcursors⟩ hleft hright hpublic
  · have hright : ¬ site.toNat < right.externalCursors.size := by simpa [hsize] using hleft
    apply readExternal_eq_of_stream_and_cursor
    · simp [hinputs]
    · simp [Array.getD, hleft, hright]

/-- Equal complete Public projections and immutable streams determine every Public-site read.
    The scalar-size premises are precisely those required to recover `PublicDataEquivalent`; no
    execution-length or stream-remaining premise is introduced. -/
theorem public_readExternal_eq_of_projection {machine : SemanticProgram} {left right : State}
    (hleftSize : left.values.size = machine.valueLabels.size)
    (hrightSize : right.values.size = machine.valueLabels.size)
    (hstreams : left.externalInputs = right.externalInputs)
    (hprojection : Semantic.PublicRegionSecurity.publicProjection machine left =
      Semantic.PublicRegionSecurity.publicProjection machine right)
    {site : UInt32} (hpublic : externalSiteLabel machine site.toNat = .pub) :
    readExternal left site = readExternal right site := by
  have hdata : PublicDataEquivalent machine left right :=
    (Semantic.PublicRegionSecurity.publicDataEquivalent_iff_projection machine left right).2
      ⟨hleftSize, hrightSize, hstreams, hprojection⟩
  exact public_readExternal_eq_total hdata.1 hpublic

end LambdaSigil.Combined.V9.PublicTraceSecurity
