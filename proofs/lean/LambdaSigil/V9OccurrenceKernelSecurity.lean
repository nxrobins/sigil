import LambdaSigil.V9OccurrenceKernel
import LambdaSigil.V9OccurrenceDataflowInvocationSecurity
import LambdaSigil.V9OccurrenceDataflowSecurity
import LambdaSigil.RankedDecodedOccurrenceSecurity

/-!
# Unary correctness of the production CSIR v9 occurrence verifier

This module reflects the executable policy checks into instruction-indexed propositions.  The
result is deliberately narrower than a Public relational theorem: it says that the retained raw
v8 verifier accepted, the v9 analyses and activation ownership layout were derivable, and every
decoded instruction satisfies the occurrence ceilings checked by the production kernel.

`ActivationLayoutJudgment` records only successful construction of the immutable ownership
index.  It is not a statement that the historical raw machine uses activation-local storage, and
none of the results below claim source projection, native-code, Wasm, or runtime correspondence.
-/

namespace LambdaSigil.Combined.V9.OccurrenceKernelSecurity

open Semantic BoundaryContracts OccurrenceTransfer OccurrenceDataflowInvocation
open OccurrenceDataflowInvocationSecurity
open OccurrenceKernel
open SemanticDataflow

def LocalDestinationSafe (instruction : Instruction) : Prop :=
  instruction.destination = 0 ∨
    instruction.blockLabel.flowsTo instruction.resultLabel = true

def CellsPublic (machine : SemanticProgram) (cells : List UInt32) : Prop :=
  ∀ cell ∈ cells, labelAt machine.valueLabels cell = .pub

def PublicResultDependenciesSafe (program : Program) (analysis : Analysis)
    (machine : SemanticProgram) (instruction : Instruction) : Prop :=
  instruction.destination ≠ 0 → instruction.resultLabel = .pub →
    publicResultDependencyBodyOK program analysis machine instruction = true

def PublicStateWriteSourceSafe (program : Program) (analysis : Analysis)
    (machine : SemanticProgram) (instruction : Instruction) : Prop :=
  instruction.op = .stateWrite →
    publicStateWriteSourceBodyOK program analysis machine instruction = true

def ClosureTargetOccurrenceSafe (analysis : Analysis) (machine : SemanticProgram)
    (instruction : Instruction) : Prop :=
  closureTargetOccurrenceOK analysis machine instruction = true

def FfiArgumentsSafe (machine : SemanticProgram) (analysis : Analysis)
    (instruction : Instruction) (contract : FfiContract) : Prop :=
  ∀ (offset : Nat) (_hoffset : offset < contract.parameters.size),
    ∃ operand parameter,
      instructionOperandAt? machine instruction
          (contract.binding.firstArgument.toNat + offset) = some operand ∧
        contract.parameters[offset]? = some parameter ∧ operand.kind = 0 ∧
        (labelAt analysis.dataflow.labels operand.value).flowsTo parameter.label = true

def InternalReturnSafe (machine : SemanticProgram) (analysis : Analysis)
    (instruction : Instruction) (pc : Nat) : Prop :=
  ∃ sink, functionReturnLabel? machine instruction = some sink ∧
    (instruction.blockLabel.lub (effectiveOccurrence analysis instruction pc)).flowsTo sink = true

def ExternalRootReturnSafe (analysis : Analysis) (instruction : Instruction) (_pc : Nat) : Prop :=
  ∃ root, rootContract? analysis instruction = some root ∧
    (root.role = 0 ∨
      root.entryOccurrence.flowsTo root.returnOccurrence = true)

def RootReturnSafe (program : Program) (machine : SemanticProgram) (analysis : Analysis)
    (instruction : Instruction) (pc : Nat) : Prop :=
  ∃ source,
    (OccurrenceDataflow.semanticProgram program analysis.dataflow).instructions[pc]? = some source ∧
      instruction.id = source.id ∧ InternalReturnSafe machine analysis source pc ∧
      ExternalRootReturnSafe analysis source pc

def StateWriteOccurrenceSafe (program : Program) (analysis : Analysis)
    (instruction : Instruction) (_pc : Nat) : Prop :=
  ∃ source offset sink,
    program.base.nodes[instruction.id.toNat - 1]? = some source ∧
      source.nodeId = instruction.id ∧ source.op = .semInstruction ∧ source.aux = 10 ∧
      semanticImmediateAt? program.base source.nodeId 2 = some offset ∧
      stateLabelForFunctionAt? analysis.stateContracts instruction.functionId offset = some sink ∧
      (externalSiteLabel instruction).flowsTo sink = true

def SiteKindOccurrenceSafe (program : Program) (analysis : Analysis)
    (instruction : Instruction) (pc : Nat) : SiteKind → Prop
  | .ffi _ contract =>
      FfiArgumentsSafe (rawSemanticProgram program analysis) analysis instruction contract ∧
      (externalSiteLabel instruction).flowsTo contract.occurrence = true
  | .actor _ _ =>
      /- The current raw machine exposes all five actor opcodes as boundary events. -/
      (externalSiteLabel instruction).flowsTo .pub = true
  | .ordinary operation =>
      operation = instruction.op ∧
        match operation with
        | .stateWrite => StateWriteOccurrenceSafe program analysis instruction pc
        | .output =>
            RootReturnSafe program (rawSemanticProgram program analysis) analysis instruction pc
        | _ => True

def SiteOccurrenceSafe (program : Program) (analysis : Analysis)
    (instruction : Instruction) (pc : Nat) : Prop :=
  match site? analysis.dataflow.contracts instruction.id with
  | none => False
  | some site =>
      site.owner = instruction.id ∧ site.functionId = instruction.functionId ∧
        SiteKindOccurrenceSafe program analysis instruction pc site.kind

def InstructionOccurrenceSafe (program : Program) (analysis : Analysis)
    (instruction : Instruction) (pc : Nat) : Prop :=
  LocalDestinationSafe instruction ∧
    PublicResultDependenciesSafe program analysis (rawSemanticProgram program analysis)
      instruction ∧
    PublicStateWriteSourceSafe program analysis (rawSemanticProgram program analysis)
      instruction ∧
    ClosureTargetOccurrenceSafe analysis (rawSemanticProgram program analysis) instruction ∧
    SiteOccurrenceSafe program analysis instruction pc

def SelectorCoherenceSafe (program : Program) (analysis : Analysis) : Prop :=
  let machine := rawSemanticProgram program analysis
  ∀ (pc : Nat) (hpc : pc < machine.instructions.size),
    DecodedOccurrence.selectorLabel? machine machine.instructions[pc] =
      some (analysis.localAnalysis.selectors.getD pc .pub)

def InstructionOccurrencePolicyJudgment (program : Program) (analysis : Analysis) : Prop :=
  let machine := rawSemanticProgram program analysis
  ∀ (pc : Nat) (hpc : pc < machine.instructions.size),
    InstructionOccurrenceSafe program analysis machine.instructions[pc] pc

def OccurrencePolicyJudgment (program : Program) (analysis : Analysis) : Prop :=
  SelectorCoherenceSafe program analysis ∧
    InstructionOccurrencePolicyJudgment program analysis

def ActivationLayoutJudgment (program : Program) (analysis : Analysis) : Prop :=
  let machine := rawSemanticProgram program analysis
  ∃ prepared : OccurrenceActivation.Prepared machine,
    OccurrenceActivation.prepare? machine = some prepared

/-- Algorithm-independent facts already proved for the analyses returned by the executable
    constructors: the semantic labels are the least extended solution, the ranked local
    occurrence transfer satisfies its declarative postcheck, and the invocation graph is closed.
    These remain unary graph facts; they do not assert balanced call/return execution. -/
def AnalysisJudgment (program : Program) (analysis : Analysis) : Prop :=
  let machine := OccurrenceDataflow.semanticProgram program analysis.dataflow
  OccurrenceDataflowSecurity.ExtendedSolution program analysis.dataflow.semanticIndex
      analysis.dataflow.hostSeeds analysis.dataflow.labels ∧
    (∀ candidate,
      OccurrenceDataflowSecurity.ExtendedSolution program analysis.dataflow.semanticIndex
          analysis.dataflow.hostSeeds candidate →
        ArrayFlows analysis.dataflow.labels candidate) ∧
    OccurrenceTransfer.transferChecks (OccurrenceRegions.decodedControlGraph machine)
        analysis.localAnalysis.regions.index analysis.localAnalysis.selectors
        analysis.localAnalysis.frontiers = true ∧
    ∃ plan,
      OccurrenceInvocation.invocationPlan? machine analysis.localAnalysis.frontiers = some plan ∧
        ArrayFlows plan.seeds analysis.labels ∧
        EdgesClosed plan.adjacency analysis.labels ∧
    analysis.stateContracts = buildStateContractIndex program machine.functions.size ∧
    StateContractIndexExact program machine.functions.size analysis.stateContracts

/-- Declarative unary acceptance surface for the current production v9 verifier. The complete
    combined v8 policy decision remains explicit, and `verifyProgramWithContext` is independently
    rerun over the v9 host-seeded labels before the occurrence-aware raw machine is authorized.
    Structured Public convergence is verifier-derived in v9, not supplied by the retired
    function-local v8 continuation heuristic. -/
def V9OccurrenceJudgment (program : Program) : Prop :=
  ∃ analysis,
    Combined.verifyProgram program.base = none ∧
      analyze? program = some analysis ∧
      verifyProgramWithContext program.base analysis.dataflow.semanticIndex
        analysis.dataflow.labels = none ∧
      AnalysisJudgment program analysis ∧
      ActivationLayoutJudgment program analysis ∧
      Semantic.OperationalStaticSafe (rawSemanticProgram program analysis) ∧
      OccurrencePolicyJudgment program analysis

theorem analysis_judgment_of_analyze {program : Program} {analysis : Analysis}
    (h : analyze? program = some analysis) : AnalysisJudgment program analysis := by
  have hcomponents := OccurrenceDataflowInvocationSecurity.analyzed_components h
  have hleast := V9.OccurrenceDataflowSecurity.analyzed_labels_are_least hcomponents.1
  have htransfer := RankedDecodedOccurrenceSecurity.analyzed_frontiers_satisfy_transfer
    hcomponents.2.1
  have hinvocation := OccurrenceDataflowInvocationSecurity.returned_invocation_graph_is_closed h
  have hstate := OccurrenceDataflowInvocationSecurity.analyzed_state_contract_index h
  have hexact := OccurrenceDataflowInvocationSecurity.analyzed_state_contract_exact h
  obtain ⟨plan, hplan, hseeds, hclosed⟩ := hinvocation
  exact ⟨hleast.1, hleast.2, htransfer, plan, hplan, hseeds, hclosed, hstate, hexact⟩

theorem localDestinationOK_iff (instruction : Instruction) :
    localDestinationOK instruction = true ↔ LocalDestinationSafe instruction := by
  simp [localDestinationOK, LocalDestinationSafe]

theorem cellsPublicB_iff (machine : SemanticProgram) (cells : List UInt32) :
    cellsPublicB machine cells = true ↔ CellsPublic machine cells := by
  simp [cellsPublicB, CellsPublic, label_eqb_true_iff]

theorem publicResultDependenciesOK_iff (program : Program) (analysis : Analysis)
    (machine : SemanticProgram) (instruction : Instruction) :
    publicResultDependenciesOK program analysis machine instruction = true ↔
      PublicResultDependenciesSafe program analysis machine instruction := by
  unfold publicResultDependenciesOK PublicResultDependenciesSafe
  by_cases hdestination : instruction.destination = 0
  · simp [hdestination]
  by_cases hresult : instruction.resultLabel = .pub
  · simp [hdestination, hresult, Label.neqb, Label.eqb]
  · have hneq : instruction.resultLabel.neqb .pub = true :=
      (label_neqb_true_iff _ _).mpr hresult
    simp [hdestination, hresult, hneq]

theorem publicStateWriteSourceOK_iff (program : Program) (analysis : Analysis)
    (machine : SemanticProgram) (instruction : Instruction) :
    publicStateWriteSourceOK program analysis machine instruction = true ↔
      PublicStateWriteSourceSafe program analysis machine instruction := by
  unfold publicStateWriteSourceOK PublicStateWriteSourceSafe
  by_cases hop : instruction.op = .stateWrite
  · simp [hop]
  · have hbne : instruction.op != .stateWrite := by simpa using hop
    simp [hop, hbne]

theorem ffiArgumentsOK_iff (machine : SemanticProgram) (analysis : Analysis)
    (instruction : Instruction) (contract : FfiContract) :
    ffiArgumentsOK machine analysis instruction contract = true ↔
      FfiArgumentsSafe machine analysis instruction contract := by
  unfold ffiArgumentsOK FfiArgumentsSafe
  constructor
  · intro h offset hoffset
    have hrow := List.all_eq_true.mp h offset (List.mem_range.mpr hoffset)
    cases hoperand : instructionOperandAt? machine instruction
        (contract.binding.firstArgument.toNat + offset) with
    | none => simp [hoperand] at hrow
    | some operand =>
        cases hparameter : contract.parameters[offset]? with
        | none => simp [hoperand, hparameter] at hrow
        | some parameter =>
            simp only [hoperand, hparameter, Bool.and_eq_true, beq_iff_eq] at hrow
            exact ⟨operand, parameter, rfl, rfl, hrow.1, hrow.2⟩
  · intro h
    apply List.all_eq_true.mpr
    intro offset hoffset
    have hbound := List.mem_range.mp hoffset
    obtain ⟨operand, parameter, hoperand, hparameter, hkind, hflow⟩ := h offset hbound
    simp [hoperand, hparameter, hkind, hflow]

theorem rootReturnOK_iff (program : Program) (analysis : Analysis) (machine : SemanticProgram)
    (instruction : Instruction) (pc : Nat) :
    rootReturnOK program analysis machine instruction pc = true ↔
      RootReturnSafe program machine analysis instruction pc := by
  unfold rootReturnOK rootReturnOKWithDecoded RootReturnSafe
  cases hsource :
      (OccurrenceDataflow.semanticProgram program analysis.dataflow).instructions[pc]? with
  | none => simp [hsource]
  | some source =>
      simp only [hsource, Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨⟨hid, hinternal⟩, hexternal⟩
        refine ⟨source, rfl, hid, ?_, ?_⟩
        · unfold internalReturnOK at hinternal
          cases hsink : functionReturnLabel? machine source with
          | none => simp [hsink] at hinternal
          | some sink => exact ⟨sink, hsink, by simpa [hsink] using hinternal⟩
        · unfold externalRootReturnOK at hexternal
          cases hroot : rootContract? analysis source with
          | none => simp [hroot] at hexternal
          | some root =>
              refine ⟨root, hroot, ?_⟩
              simpa [hroot, Bool.or_eq_true] using hexternal
      · rintro ⟨source', hsource', hid, ⟨sink, hsink, hinternal⟩,
            ⟨root, hroot, hexternal⟩⟩
        have hsourceEq : source' = source := Option.some.inj hsource'.symm
        subst source'
        refine ⟨⟨hid, ?_⟩, ?_⟩
        · simpa [internalReturnOK, hsink] using hinternal
        · simpa [externalRootReturnOK, hroot, Bool.or_eq_true] using hexternal

private theorem rootReturnOKWithDecoded_canonical_iff (program : Program) (analysis : Analysis)
    (machine : SemanticProgram) (instruction : Instruction) (pc : Nat) :
    rootReturnOKWithDecoded analysis machine
        (OccurrenceDataflow.semanticProgram program analysis.dataflow) instruction pc = true ↔
      RootReturnSafe program machine analysis instruction pc := by
  exact rootReturnOK_iff program analysis machine instruction pc

private theorem op_beq_semInstruction_iff (operation : Op) :
    (operation == .semInstruction) = true ↔ operation = .semInstruction := by
  cases operation <;> decide

theorem stateWriteOccurrenceOK_iff (program : Program) (analysis : Analysis)
    (instruction : Instruction) (pc : Nat) :
    stateWriteOccurrenceOK program analysis instruction pc = true ↔
      StateWriteOccurrenceSafe program analysis instruction pc := by
  unfold stateWriteOccurrenceOK StateWriteOccurrenceSafe
  cases hsource : program.base.nodes[instruction.id.toNat - 1]? with
  | none => simp
  | some source =>
      cases hoffset : semanticImmediateAt? program.base source.nodeId 2 with
      | none => simp [hoffset]
      | some offset =>
          cases hsink : stateLabelForFunctionAt? analysis.stateContracts instruction.functionId offset with
          | none => simp [hoffset, hsink]
          | some sink =>
              simp [hoffset, hsink, Bool.and_eq_true, op_beq_semInstruction_iff, and_assoc]

theorem instructionOccurrenceOK_iff (program : Program) (analysis : Analysis)
    (instruction : Instruction) (pc : Nat) :
    instructionOccurrenceOK program analysis
        (rawSemanticProgram program analysis) instruction pc = true ↔
      InstructionOccurrenceSafe program analysis instruction pc := by
  unfold instructionOccurrenceOK instructionOccurrenceOKWithDecoded InstructionOccurrenceSafe
    SiteOccurrenceSafe
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    localDestinationOK_iff,
    publicResultDependenciesOK_iff, publicStateWriteSourceOK_iff]
  cases hsite : site? analysis.dataflow.contracts instruction.id with
  | none => simp
  | some site =>
      cases hkind : site.kind with
      | ffi position contract =>
          simp [hkind, SiteKindOccurrenceSafe, Bool.and_eq_true, beq_iff_eq,
            ffiArgumentsOK_iff, ClosureTargetOccurrenceSafe, and_assoc]
      | actor position contract =>
          simp [hkind, SiteKindOccurrenceSafe, Bool.and_eq_true, beq_iff_eq,
            ClosureTargetOccurrenceSafe, and_assoc]
      | ordinary operation =>
          cases operation <;>
            simp [hkind, SiteKindOccurrenceSafe, Bool.and_eq_true, beq_iff_eq,
              stateWriteOccurrenceOK_iff, rootReturnOKWithDecoded_canonical_iff,
              ClosureTargetOccurrenceSafe, and_assoc]

theorem selectorCoherenceChecks_iff (program : Program) (analysis : Analysis) :
    selectorCoherenceChecks analysis (rawSemanticProgram program analysis) = true ↔
      SelectorCoherenceSafe program analysis := by
  let machine := rawSemanticProgram program analysis
  change (List.range machine.instructions.size).all
      (selectorCoherentAt analysis machine) = true ↔ _
  change _ ↔ ∀ (pc : Nat) (hpc : pc < machine.instructions.size),
    DecodedOccurrence.selectorLabel? machine machine.instructions[pc] =
      some (analysis.localAnalysis.selectors.getD pc .pub)
  constructor
  · intro h pc hpc
    have hrow := List.all_eq_true.mp h pc (List.mem_range.mpr hpc)
    unfold selectorCoherentAt at hrow
    simp only [Array.getElem?_eq_getElem hpc] at hrow
    cases hselector : DecodedOccurrence.selectorLabel? machine machine.instructions[pc] with
    | none => simp [hselector] at hrow
    | some selector =>
        have heq : selector = analysis.localAnalysis.selectors.getD pc .pub := by
          simpa [hselector] using hrow
        simpa [hselector, heq]
  · intro h
    apply List.all_eq_true.mpr
    intro pc hpc
    have hbound := List.mem_range.mp hpc
    have hselector : DecodedOccurrence.selectorLabel? machine machine.instructions[pc] =
        some (analysis.localAnalysis.selectors.getD pc .pub) := h pc hbound
    unfold selectorCoherentAt
    rw [Array.getElem?_eq_getElem hbound]
    simp [hselector]

theorem occurrenceInstructionChecks_iff (program : Program) (analysis : Analysis) :
    let machine := rawSemanticProgram program analysis
    (List.range machine.instructions.size).all (fun pc =>
      match machine.instructions[pc]? with
      | none => false
      | some instruction => instructionOccurrenceOK program analysis machine instruction pc) = true ↔
      InstructionOccurrencePolicyJudgment program analysis := by
  let machine := rawSemanticProgram program analysis
  unfold InstructionOccurrencePolicyJudgment
  change _ ↔ ∀ (pc : Nat) (hpc : pc < machine.instructions.size),
    InstructionOccurrenceSafe program analysis machine.instructions[pc] pc
  constructor
  · intro h pc hpc
    have hrow := List.all_eq_true.mp h pc (List.mem_range.mpr hpc)
    have hrow' : instructionOccurrenceOK program analysis
        (rawSemanticProgram program analysis) machine.instructions[pc] pc = true := by
      simpa only [Array.getElem?_eq_getElem hpc, machine] using hrow
    exact (instructionOccurrenceOK_iff program analysis machine.instructions[pc] pc).mp hrow'
  · intro h
    apply List.all_eq_true.mpr
    intro pc hpc
    have hbound := List.mem_range.mp hpc
    have hrow := (instructionOccurrenceOK_iff program analysis machine.instructions[pc] pc).mpr
      (h pc hbound)
    simpa only [Array.getElem?_eq_getElem hbound, machine] using hrow

theorem occurrencePolicyChecks_iff (program : Program) (analysis : Analysis) :
    occurrencePolicyChecks program analysis = true ↔
      OccurrencePolicyJudgment program analysis := by
  simp only [occurrencePolicyChecks, occurrencePolicyChecksWithMachines,
    Bool.and_eq_true, OccurrencePolicyJudgment]
  exact and_congr (selectorCoherenceChecks_iff program analysis)
    (occurrenceInstructionChecks_iff program analysis)

theorem activation_layout_iff (program : Program) (analysis : Analysis) :
    (OccurrenceActivation.prepare?
      (rawSemanticProgram program analysis)).isSome = true ↔
      ActivationLayoutJudgment program analysis := by
  unfold ActivationLayoutJudgment
  exact Option.isSome_iff_exists

theorem v9_occurrence_verifier_sound {program : Program}
    (h : OccurrenceKernel.verifyProgram program = none) : V9OccurrenceJudgment program := by
  unfold OccurrenceKernel.verifyProgram at h
  cases hraw : Combined.verifyProgram program.base with
  | some violation => simp [hraw] at h
  | none =>
      cases hanalysis : analyze? program with
      | none => simp [hraw, hanalysis] at h
      | some analysis =>
          cases hcontext : verifyProgramWithContext program.base analysis.dataflow.semanticIndex
              analysis.dataflow.labels with
          | some violation => simp [hraw, hanalysis, hcontext] at h
          | none =>
              let decoded := OccurrenceDataflow.semanticProgram program analysis.dataflow
              let machine := rawSemanticProgramFromDecoded analysis decoded
              cases hactivation : (OccurrenceActivation.prepare? machine).isSome with
              | false =>
                  simp [hraw, hanalysis, hcontext, decoded, machine, hactivation] at h
              | true =>
                  cases hsemantic : Semantic.operationalStaticSafeB machine with
                  | false =>
                      simp [hraw, hanalysis, hcontext, decoded, machine, hactivation, hsemantic] at h
                  | true =>
                      cases hpolicy :
                          occurrencePolicyChecksWithMachines program analysis decoded machine with
                      | false =>
                          simp [hraw, hanalysis, hcontext, decoded, machine, hactivation,
                            hsemantic, hpolicy] at h
                      | true =>
                          refine ⟨analysis, hraw, hanalysis, hcontext,
                            analysis_judgment_of_analyze hanalysis, ?_, ?_, ?_⟩
                          · exact (activation_layout_iff program analysis).mp
                              (by simpa [rawSemanticProgram, decoded, machine] using hactivation)
                          · exact (Semantic.operationalStaticSafeB_iff _).mp
                              (by simpa [rawSemanticProgram, decoded, machine] using hsemantic)
                          · apply (occurrencePolicyChecks_iff program analysis).mp
                            simpa [occurrencePolicyChecks, decoded, machine] using hpolicy

theorem v9_occurrence_verifier_complete {program : Program}
    (h : V9OccurrenceJudgment program) : OccurrenceKernel.verifyProgram program = none := by
  obtain ⟨analysis, hraw, hanalysis, hcontext, _, hactivation, hsemantic, hpolicy⟩ := h
  have hactivation' := (activation_layout_iff program analysis).mpr hactivation
  have hsemantic' := (Semantic.operationalStaticSafeB_iff _).mpr hsemantic
  have hpolicy' := (occurrencePolicyChecks_iff program analysis).mpr hpolicy
  let decoded := OccurrenceDataflow.semanticProgram program analysis.dataflow
  let machine := rawSemanticProgramFromDecoded analysis decoded
  have hactivationCached : (OccurrenceActivation.prepare? machine).isSome = true := by
    simpa [rawSemanticProgram, decoded, machine] using hactivation'
  have hsemanticCached : Semantic.operationalStaticSafeB machine = true := by
    simpa [rawSemanticProgram, decoded, machine] using hsemantic'
  have hpolicyCached :
      occurrencePolicyChecksWithMachines program analysis decoded machine = true := by
    simpa [occurrencePolicyChecks, decoded, machine] using hpolicy'
  simp [OccurrenceKernel.verifyProgram, hraw, hanalysis, hcontext, decoded, machine,
    hactivationCached, hsemanticCached, hpolicyCached]

/-- Executable soundness and completeness, relative to the named retained-v8 premise and the
    instruction-indexed v9 occurrence judgment above. -/
theorem v9_occurrence_verifier_sound_and_complete (program : Program) :
    OccurrenceKernel.verifyProgram program = none ↔ V9OccurrenceJudgment program :=
  ⟨v9_occurrence_verifier_sound, v9_occurrence_verifier_complete⟩

@[simp] theorem rawSemanticProgram_valueLabels (program : Program) (analysis : Analysis) :
    (rawSemanticProgram program analysis).valueLabels =
      occurrenceValueLabels analysis
        (OccurrenceDataflow.semanticProgram program analysis.dataflow) := by
  rfl

private theorem occurrence_seed_step_inflationary (analysis : Analysis)
    (pc : Nat) (labels : Array Label) (instruction : Instruction) :
    ArrayFlows labels (occurrenceSeedStep analysis (pc, labels) instruction).2 := by
  unfold occurrenceSeedStep
  by_cases hdestination : instruction.destination = 0
  · simp [hdestination, ArrayFlows.refl]
  · have hdestinationB : (instruction.destination == 0) = false := by
      simpa using hdestination
    simpa [hdestinationB, raiseCell] using
      (ArrayFlows.raise labels instruction.destination
        (effectiveOccurrence analysis instruction pc))

private theorem occurrence_seed_fold_inflationary (analysis : Analysis)
    (instructions : List Instruction) (pc : Nat) (labels : Array Label) :
    ArrayFlows labels
      ((instructions.foldl (occurrenceSeedStep analysis) (pc, labels)).2) := by
  induction instructions generalizing pc labels with
  | nil => exact ArrayFlows.refl labels
  | cons instruction rest ih =>
      simp only [List.foldl_cons]
      exact (occurrence_seed_step_inflationary analysis pc labels instruction).trans
        (ih (pc + 1) (occurrenceSeedStep analysis (pc, labels) instruction).2)

theorem occurrence_seed_labels_inflationary (analysis : Analysis)
    (candidate : SemanticProgram) :
    ArrayFlows analysis.dataflow.labels (occurrenceSeedLabels analysis candidate) := by
  simpa [occurrenceSeedLabels, Array.foldl_toList] using
    occurrence_seed_fold_inflationary analysis candidate.instructions.toList 0
      analysis.dataflow.labels

theorem occurrence_value_labels_inflationary (analysis : Analysis)
    (candidate : SemanticProgram) :
    ArrayFlows analysis.dataflow.labels (occurrenceValueLabels analysis candidate) := by
  exact (occurrence_seed_labels_inflationary analysis candidate).trans
    (saturateGraphWorklist_inflationary
      (semanticTaintAdjacencyWithIndex candidate.source analysis.dataflow.semanticIndex)
      (4 * semanticTaintCellCount candidate.source)
      ((List.range (semanticTaintCellCount candidate.source)).map UInt32.ofNat)
      (occurrenceSeedLabels analysis candidate))

theorem analyzed_labels_flow_to_raw_value_labels (program : Program) (analysis : Analysis) :
    ArrayFlows analysis.dataflow.labels
      (rawSemanticProgram program analysis).valueLabels := by
  simpa using occurrence_value_labels_inflationary analysis
    (OccurrenceDataflow.semanticProgram program analysis.dataflow)

@[simp] theorem rawSemanticProgram_instructions_size (program : Program) (analysis : Analysis) :
    (rawSemanticProgram program analysis).instructions.size =
      (OccurrenceDataflow.semanticProgram program analysis.dataflow).instructions.size := by
  simp [rawSemanticProgram, rawSemanticProgramFromDecoded]

theorem raw_semantic_program_static_safe_of_judgment {program : Program}
    (h : V9OccurrenceJudgment program) {analysis : Analysis}
    (hanalysis : analyze? program = some analysis) :
    Semantic.OperationalStaticSafe (rawSemanticProgram program analysis) := by
  obtain ⟨accepted, _, haccepted, _, _, _, hsafe, _⟩ := h
  have heq : accepted = analysis := by
    rw [hanalysis] at haccepted
    exact Option.some.inj haccepted.symm
  subst accepted
  exact hsafe

/-- Production acceptance directly yields the occurrence-aware raw machine and its rerun raw
    relational static-safety judgment. The witness is the unique analysis returned from the
    decoded v9 program, not a caller-supplied label table. -/
theorem raw_relational_static_safe_of_v9_verified {program : Program}
    (h : OccurrenceKernel.verifyProgram program = none) :
    ∃ analysis, analyze? program = some analysis ∧
      Semantic.OperationalStaticSafe (rawSemanticProgram program analysis) := by
  obtain ⟨analysis, _, hanalysis, _, _, _, hsafe, _⟩ :=
    v9_occurrence_verifier_sound h
  exact ⟨analysis, hanalysis, hsafe⟩

/-- The ordinary semantic/context gate is rerun over the host-seeded v9 least labels; the retained
    v8 result over its older label table is not used as a substitute. -/
theorem host_seeded_context_safe_of_v9_verified {program : Program}
    (h : OccurrenceKernel.verifyProgram program = none) :
    ∃ analysis, analyze? program = some analysis ∧
      verifyProgramWithContext program.base analysis.dataflow.semanticIndex
        analysis.dataflow.labels = none := by
  obtain ⟨analysis, _, hanalysis, hcontext, _, _, _, _⟩ :=
    v9_occurrence_verifier_sound h
  exact ⟨analysis, hanalysis, hcontext⟩

theorem analyzed_policy_of_judgment {program : Program} (h : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis) :
    ActivationLayoutJudgment program analysis ∧ OccurrencePolicyJudgment program analysis := by
  obtain ⟨accepted, _, haccepted, _, _, hactivation, _, hpolicy⟩ := h
  have : accepted = analysis := by
    rw [hanalysis] at haccepted
    exact Option.some.inj haccepted.symm
  subst accepted
  exact ⟨hactivation, hpolicy⟩

theorem returned_instruction_occurrence_safe {program : Program}
    (h : V9OccurrenceJudgment program) {analysis : Analysis}
    (hanalysis : analyze? program = some analysis) {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction) :
    InstructionOccurrenceSafe program analysis instruction pc := by
  let machine := rawSemanticProgram program analysis
  have hbound : pc < machine.instructions.size := (Array.getElem?_eq_some_iff.mp hlookup).1
  have hsafe := (analyzed_policy_of_judgment h hanalysis).2.2 pc hbound
  have hinstruction : machine.instructions[pc] = instruction :=
    (Array.getElem?_eq_some_iff.mp hlookup).2
  simpa [machine, hinstruction] using hsafe

theorem returned_selector_coherent {program : Program}
    (h : V9OccurrenceJudgment program) {analysis : Analysis}
    (hanalysis : analyze? program = some analysis) {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction) :
    DecodedOccurrence.selectorLabel? (rawSemanticProgram program analysis) instruction =
      some (analysis.localAnalysis.selectors.getD pc .pub) := by
  let machine := rawSemanticProgram program analysis
  have hbound : pc < machine.instructions.size := (Array.getElem?_eq_some_iff.mp hlookup).1
  have hcoherent := (analyzed_policy_of_judgment h hanalysis).2.1 pc hbound
  have hinstruction : machine.instructions[pc] = instruction :=
    (Array.getElem?_eq_some_iff.mp hlookup).2
  simpa [machine, hinstruction] using hcoherent

theorem returned_public_result_dependencies_safe {program : Program}
    (h : V9OccurrenceJudgment program) {analysis : Analysis}
    (hanalysis : analyze? program = some analysis) {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction) :
    PublicResultDependenciesSafe program analysis (rawSemanticProgram program analysis)
      instruction :=
  (returned_instruction_occurrence_safe h hanalysis hlookup).2.1

theorem returned_public_state_write_source_safe {program : Program}
    (h : V9OccurrenceJudgment program) {analysis : Analysis}
    (hanalysis : analyze? program = some analysis) {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction) :
    PublicStateWriteSourceSafe program analysis (rawSemanticProgram program analysis)
      instruction :=
  (returned_instruction_occurrence_safe h hanalysis hlookup).2.2.1

theorem returned_closure_target_occurrence_safe {program : Program}
    (h : V9OccurrenceJudgment program) {analysis : Analysis}
    (hanalysis : analyze? program = some analysis) {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction) :
    ClosureTargetOccurrenceSafe analysis (rawSemanticProgram program analysis) instruction :=
  (returned_instruction_occurrence_safe h hanalysis hlookup).2.2.2.1

/-- Canonical role-zero declarations still have a checked return sink: the decoded function return
    contract. They no longer receive an unconditional output-policy bypass. -/
theorem role_zero_return_uses_function_contract {machine : SemanticProgram}
    {analysis : Analysis} {instruction : Instruction} {root : FunctionRootContract}
    {function : Function}
    (hroot : analysis.dataflow.contracts.roots[instruction.functionId.toNat - 1]? = some root)
    (hfunction : machine.functions[instruction.functionId.toNat - 1]? = some function)
    (hrootId : root.functionId = instruction.functionId)
    (hfunctionId : function.id = instruction.functionId) (hrole : root.role = 0) :
    rootReturnOccurrence? machine analysis instruction = some function.returnLabel := by
  simp [rootReturnOccurrence?, rootContract?, functionReturnLabel?, hroot, hfunction, hrootId,
    hfunctionId, hrole]

/-- Load-bearing bypass mutant: a private internal return cannot flow to a Public function return
    contract merely because its root declaration has canonical role zero. -/
theorem role_zero_private_public_return_is_rejected
    {machine : SemanticProgram} {analysis : Analysis} {instruction : Instruction}
    {root : FunctionRootContract} {function : Function}
    (hfunction : machine.functions[instruction.functionId.toNat - 1]? = some function)
    (hfunctionId : function.id = instruction.functionId) (_hrole : root.role = 0)
    (hreturn : function.returnLabel = .pub)
    (heffective : effectiveOccurrence analysis instruction 0 = .secret) :
    internalReturnOK analysis machine instruction 0 = false := by
  cases hblock : instruction.blockLabel <;>
    simp [internalReturnOK, functionReturnLabel?, hfunction, hfunctionId, heffective, hreturn,
      hblock, Label.flowsTo, Label.lub, Label.rank]

/-- A convenient site-level consequence.  It recovers the exact contract indexed by the same
    analysis and exposes the checked ceiling without introducing a supplied verdict. -/
theorem returned_site_occurrence_safe {program : Program} (h : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? =
      some instruction) {site : SiteContract}
    (hsite : site? analysis.dataflow.contracts instruction.id = some site) :
    site.owner = instruction.id ∧ site.functionId = instruction.functionId ∧
      SiteKindOccurrenceSafe program analysis instruction pc site.kind := by
  let machine := rawSemanticProgram program analysis
  have hbound : pc < machine.instructions.size := by
    exact (Array.getElem?_eq_some_iff.mp hlookup).1
  have hsafe := (analyzed_policy_of_judgment h hanalysis).2.2 pc hbound
  have hinstruction : machine.instructions[pc] = instruction := by
    exact (Array.getElem?_eq_some_iff.mp hlookup).2
  rw [hinstruction] at hsafe
  simpa [InstructionOccurrenceSafe, SiteOccurrenceSafe, hsite] using hsafe.2.2.2.2

/-- The state sink recovered by an accepted analysis is not merely a computed label: it is carried
    by a declaration with the exact requested owning function and offset. -/
theorem analyzed_state_lookup_has_exact_declaration {program : Program} {analysis : Analysis}
    (hanalysis : analyze? program = some analysis) {functionId offset : UInt32} {sink : Label}
    (hlookup : stateLabelForFunctionAt? analysis.stateContracts functionId offset = some sink) :
    ∃ contract,
      program.base.nodes[contract.nodeId.toNat - 1]? = some contract ∧
        stateContractDeclarationB contract = true ∧ contract.origin = functionId ∧
        contract.actual = offset ∧ contract.labelA = sink :=
  state_contract_lookup_has_exact_declaration
    (OccurrenceDataflowInvocationSecurity.analyzed_state_contract_witnessed hanalysis) hlookup

private def actorOffsetCollisionProgram : Program :=
  { wireVersion := 9
    base := { nodes := #[
      { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
        origin := 1, actual := 0, required := 3, ceiling := 0, aux := 3, nodeId := 1 },
      { op := .semLabelContract, labelA := .secret, labelB := .secret, flags := 1,
        origin := 2, actual := 0, required := 3, ceiling := 0, aux := 3, nodeId := 2 }
    ] }
    hostProfileBytes := ByteArray.empty
    hostProfile := none
    ffiBindings := #[]
    actorBindings := #[]
    roots := #[] }

private def actorOffsetCollisionIndex : Array StateContractEntry := #[
  ⟨1, 0, .pub, 1⟩,
  ⟨2, 0, .secret, 2⟩
]

/-- Load-bearing actor-identity witness: the historical global-offset join is Secret, which would
    accept a Secret occurrence at actor 1's Public field. The production v9 lookup keeps the two
    owning functions separate and therefore refuses that laundering step. -/
theorem per_function_state_contract_prevents_offset_laundering :
    stateContractIndexChecks actorOffsetCollisionProgram 2 actorOffsetCollisionIndex = true ∧
      stateLabelForFunctionAt? actorOffsetCollisionIndex 1 0 = some .pub ∧
      stateLabelForFunctionAt? actorOffsetCollisionIndex 2 0 = some .secret ∧
      semanticDeclaredStateLabelAt actorOffsetCollisionProgram.base 0 = .secret ∧
      (Label.secret).flowsTo (semanticDeclaredStateLabelAt actorOffsetCollisionProgram.base 0) = true ∧
      (Label.secret).flowsTo
          ((stateLabelForFunctionAt? actorOffsetCollisionIndex 1 0).getD .pub) = false := by
  have hop : ((Op.semLabelContract == Op.semLabelContract) = true) := by decide
  simp [stateContractIndexChecks, stateContractRecordCoveredB, stateContractEntryWitnessedB,
    stateContractDeclarationB,
    actorOffsetCollisionProgram, actorOffsetCollisionIndex, stateLabelForFunctionAt?,
    binarySearchStateContract, semanticDeclaredStateLabelAt, semanticDeclaredStateLabelAtList,
    Label.flowsTo, Label.rank, Label.lub, hop]

private def duplicateStateContract : Node :=
  { op := .semLabelContract, labelA := .secret, labelB := .secret, flags := 1,
    origin := 1, actual := 0, required := 3, ceiling := 0, aux := 3, nodeId := 3 }

private def duplicateStateContractProgram : Program :=
  { actorOffsetCollisionProgram with
    base := ⟨actorOffsetCollisionProgram.base.nodes.push duplicateStateContract⟩ }

private def droppedDuplicateStateContractIndex : Array StateContractEntry := #[
  ⟨1, 0, .pub, 1⟩,
  ⟨2, 0, .secret, 2⟩
]

private def completeDuplicateStateContractIndex : Array StateContractEntry := #[
  ⟨1, 0, .secret, 3⟩,
  ⟨2, 0, .secret, 2⟩
]

/-- Load-bearing optimized-index mutant: losing one duplicate would lower actor 1's joined sink
    from Secret to Public.  The one-pass coverage postcheck rejects that under-approximation even
    though the mutant table remains sorted and exact-key lookup still succeeds. -/
theorem dropped_duplicate_state_contract_is_rejected :
    stateContractIndexChecks duplicateStateContractProgram 2
        completeDuplicateStateContractIndex = true ∧
      stateLabelForFunctionAt? completeDuplicateStateContractIndex 1 0 = some .secret ∧
      stateContractIndexChecks duplicateStateContractProgram 2
        droppedDuplicateStateContractIndex = false := by
  have hop : ((Op.semLabelContract == Op.semLabelContract) = true) := by decide
  simp [stateContractIndexChecks, stateContractRecordCoveredB, stateContractEntryWitnessedB,
    stateContractDeclarationB,
    duplicateStateContractProgram, duplicateStateContract, completeDuplicateStateContractIndex,
    droppedDuplicateStateContractIndex, actorOffsetCollisionProgram, stateLabelForFunctionAt?,
    binarySearchStateContract, Label.flowsTo, Label.rank, hop]

private def wrongKeyOverCoalescedStateContractIndex : Array StateContractEntry := #[
  /- Mutant: actor 1's Public key borrows actor 2's Secret label and witness. -/
  ⟨1, 0, .secret, 2⟩,
  ⟨2, 0, .secret, 2⟩
]

/-- Load-bearing unsafe-direction mutant. Declaration-to-lookup coverage alone accepts the
    over-coalesced Secret sink and would allow a Secret write to actor 1's Public field again. The
    reverse exact-key witness check rejects the borrowed actor-2 declaration. -/
theorem wrong_key_overcoalesced_state_contract_is_rejected :
    actorOffsetCollisionProgram.base.nodes.all
        (stateContractRecordCoveredB 2 wrongKeyOverCoalescedStateContractIndex) = true ∧
      (Label.secret).flowsTo
          ((stateLabelForFunctionAt? wrongKeyOverCoalescedStateContractIndex 1 0).getD .pub) = true ∧
      wrongKeyOverCoalescedStateContractIndex.all
          (stateContractEntryWitnessedB actorOffsetCollisionProgram) = false ∧
      stateContractIndexChecks actorOffsetCollisionProgram 2
          wrongKeyOverCoalescedStateContractIndex = false := by
  have hop : ((Op.semLabelContract == Op.semLabelContract) = true) := by decide
  simp [stateContractIndexChecks, stateContractRecordCoveredB, stateContractEntryWitnessedB,
    stateContractDeclarationB, actorOffsetCollisionProgram,
    wrongKeyOverCoalescedStateContractIndex, stateLabelForFunctionAt?,
    binarySearchStateContract, Label.flowsTo, Label.rank, hop]

private def secretCTBranchInstruction : Instruction :=
  { op := .branch, id := 1, functionId := 1, blockId := 1, destination := 0,
    firstOperand := 0, operandCount := 1, target := 0, alternate := 0, merge := 0,
    blockLabel := .pub, resultLabel := .pub, aux := 0 }

private def branchMachine (selector : Label) : SemanticProgram :=
  { functions := #[],
    instructions := #[secretCTBranchInstruction],
    operands := #[{ owner := 1, position := 0, value := 1, kind := 0 }],
    valueLabels := #[.pub, selector] }

/-- Load-bearing host-seed mutant: the same decoded branch passes the old-label raw decision but
    fails once an exact host result raises its selector to SecretCT. This is why production reruns
    raw relational static safety after v9 analysis instead of trusting the retained-v8 result. -/
theorem host_seeded_secretCT_requires_raw_rerun :
    Semantic.rawRelationalStaticSafeB (branchMachine .pub) = true ∧
      Semantic.rawRelationalStaticSafeB (branchMachine .secretCT) = false := by
  decide

private def publicActorInstruction : Instruction :=
  { op := .actorBoundary, id := 1, functionId := 1, blockId := 1, destination := 0,
    firstOperand := 0, operandCount := 0, target := 0, alternate := 0, merge := 0,
    blockLabel := .pub, resultLabel := .pub, aux := 0 }

/-- Load-bearing occurrence-label mutant: omitting the local/invocation raise would classify a
    boundary reached under Secret occurrence as Public in the raw event projection. -/
theorem occurrence_raise_changes_boundary_visibility :
    externalSiteLabel publicActorInstruction = .pub ∧
      externalSiteLabel
        (raiseInstructionOccurrence publicActorInstruction .secret none) = .secret := by
  decide

private def publicOutputInstruction : Instruction :=
  { op := .output, id := 2, functionId := 1, blockId := 1, destination := 0,
    firstOperand := 0, operandCount := 1, target := 0, alternate := 0, merge := 0,
    blockLabel := .pub, resultLabel := .pub, aux := 0 }

/-- One function may be a Public external root and also be called under private control. The raw
    external event remains Public because internal returns emit no event, while the private
    call-return occurrence is separately admitted only by the exact Secret function-return
    contract. A single aggregate output label would incorrectly hide the external event. -/
theorem external_public_and_private_internal_return_are_context_split :
    externalSiteLabel
        (raiseInstructionOccurrence publicOutputInstruction .pub (some .pub)) = .pub ∧
      ((publicOutputInstruction.blockLabel.lub .secret).flowsTo .secret = true) ∧
      ((((publicOutputInstruction.blockLabel.lub .pub).lub .pub).flowsTo .pub) = true) := by
  decide

private def publicResultInstruction : Instruction :=
  { op := .scalar, id := 1, functionId := 1, blockId := 1, destination := 1,
    firstOperand := 0, operandCount := 1, target := 0, alternate := 0, merge := 0,
    blockLabel := .pub, resultLabel := .pub, aux := 0 }

private def secretOperandPublicResultMachine : SemanticProgram :=
  { functions := #[],
    instructions := #[publicResultInstruction],
    operands := #[{ owner := 1, position := 0, value := 2, kind := 0 }],
    valueLabels := #[.pub, .pub, .secret] }

/-- Load-bearing dependency mutant: pc-to-result safety alone accepts this instruction shape, but
    the direct Public payload dependency check exposes its Secret source. -/
theorem public_result_requires_public_payload_dependencies :
    localDestinationOK publicResultInstruction = true ∧
      cellsPublicB secretOperandPublicResultMachine
        (valueOperandCells secretOperandPublicResultMachine publicResultInstruction) = false := by
  decide

end LambdaSigil.Combined.V9.OccurrenceKernelSecurity
