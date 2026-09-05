import LambdaSigil.V9OccurrenceKernelSecurity
import LambdaSigil.PublicRegionSecurity
import LambdaSigil.PublicFrameSecurity

/-!
# Verifier-derived local Public preservation facts

This module is the local bridge between the production CSIR v9 occurrence verifier and the raw
semantic machine used by the Public proof.  It deliberately proves only unary, instruction-local
facts.  In particular, it does not assume activation-local execution, region convergence, release
alignment, or a relational policy supplied by a theorem caller.

Every machine below is `OccurrenceKernel.rawSemanticProgram program analysis`, where `analysis` is
the unique result returned by the production verifier's own `analyze?` pass.
-/

namespace LambdaSigil.Combined.V9.PublicLocalSecurity

open Semantic BoundaryContracts OccurrenceTransfer OccurrenceDataflowInvocation
open OccurrenceKernel OccurrenceKernelSecurity
open Semantic.PublicRegionSecurity
open Semantic.PublicFrameSecurity

private theorem flowsTo_public_iff (label : Label) :
    label.flowsTo .pub = true ↔ label = .pub := by
  cases label <;> decide

private theorem flowsTo_lub_left (left right : Label) :
    left.flowsTo (left.lub right) = true := by
  cases left <;> cases right <;> decide

private theorem flowsTo_lub_right (left right : Label) :
    right.flowsTo (left.lub right) = true := by
  cases left <;> cases right <;> decide

private theorem flowsTo_trans {first second third : Label}
    (hfirst : first.flowsTo second = true) (hsecond : second.flowsTo third = true) :
    first.flowsTo third = true := by
  cases first <;> cases second <;> cases third <;>
    simp_all [Label.flowsTo, Label.rank]

/-- Production acceptance exposes one verifier-owned analysis and the exact occurrence-raised raw
    machine, together with all unary facts needed by subsequent local proofs. -/
theorem accepted_raw_machine {program : V9.Program}
    (hverified : OccurrenceKernel.verifyProgram program = none) :
    ∃ analysis,
      analyze? program = some analysis ∧
      AnalysisJudgment program analysis ∧
      ActivationLayoutJudgment program analysis ∧
      Semantic.OperationalStaticSafe (rawSemanticProgram program analysis) ∧
      OccurrencePolicyJudgment program analysis := by
  obtain ⟨analysis, _, hanalysis, _, hdataflow, hactivation, hstatic, hpolicy⟩ :=
    v9_occurrence_verifier_sound hverified
  exact ⟨analysis, hanalysis, hdataflow, hactivation, hstatic, hpolicy⟩

/-- A non-output occurrence raise preserves the decoded block-pc lower bound. Outputs are
    classified by their stable root-return contract and use the accepted return-policy fact
    instead of this purely syntactic lemma. -/
theorem decoded_block_flows_to_raised_block (instruction : Instruction)
    (occurrence : Label) (rootReturn : Option Label)
    (hnonoutput : instruction.op ≠ .output) :
    instruction.blockLabel.flowsTo
      (raiseInstructionOccurrence instruction occurrence rootReturn).blockLabel = true := by
  simpa [raiseInstructionOccurrence, hnonoutput] using
    (flowsTo_lub_left instruction.blockLabel occurrence)

/-- Local and invocation occurrence are genuine lower bounds on the raw instruction's pc label. -/
theorem derived_occurrence_flows_to_raised_block (instruction : Instruction)
    (occurrence : Label) (rootReturn : Option Label)
    (hnonoutput : instruction.op ≠ .output) :
    occurrence.flowsTo
      (raiseInstructionOccurrence instruction occurrence rootReturn).blockLabel = true := by
  simpa [raiseInstructionOccurrence, hnonoutput] using
    (flowsTo_lub_right instruction.blockLabel occurrence)

/-- When an output return sink resolves, that sink is also a lower bound of the emitted raw
    occurrence.  Missing sinks are raised to SecretCT and rejected independently. -/
theorem output_sink_flows_to_raised_block (instruction : Instruction)
    (occurrence sink : Label) (houtput : instruction.op = .output) :
    sink.flowsTo
      (raiseInstructionOccurrence instruction occurrence (some sink)).blockLabel = true := by
  unfold raiseInstructionOccurrence
  simp [houtput]
  cases sink <;> decide

/-- The verifier's exact local occurrence at a decoded instruction remains a lower bound on that
    instruction's block label in the production raw machine.  Non-output instructions first join
    the invocation summary; outputs use the local occurrence directly. -/
theorem local_occurrence_flows_to_raw_block_of_lookup
    {program : V9.Program} {analysis : Analysis} {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hnonoutput : instruction.op ≠ .output) :
    (localOccurrenceAt analysis.localAnalysis.frontiers pc).flowsTo instruction.blockLabel =
      true := by
  let candidate := OccurrenceDataflow.semanticProgram program analysis.dataflow
  have hrawBound := (Array.getElem?_eq_some_iff.mp hlookup).1
  have hbound : pc < candidate.instructions.size := by
    simpa [rawSemanticProgram, candidate] using hrawBound
  let decoded := candidate.instructions[pc]
  let occurrence := if decoded.op == .output then
    localOccurrenceAt analysis.localAnalysis.frontiers pc
  else effectiveOccurrence analysis decoded pc
  let rootReturn := rootReturnOccurrence? candidate analysis decoded
  have hrawGet := (Array.getElem?_eq_some_iff.mp hlookup).2
  have hraised : raiseInstructionResultLabel
      (occurrenceValueLabels analysis candidate)
      (raiseInstructionOccurrence decoded occurrence rootReturn) = instruction := by
    simpa [rawSemanticProgram, candidate, decoded, occurrence, rootReturn, hbound] using hrawGet
  have hlocalToOccurrence :
      (localOccurrenceAt analysis.localAnalysis.frontiers pc).flowsTo occurrence = true := by
    unfold occurrence
    split
    · cases localOccurrenceAt analysis.localAnalysis.frontiers pc <;> decide
    · unfold effectiveOccurrence
      exact flowsTo_lub_right (labelAt analysis.labels decoded.functionId)
        (localOccurrenceAt analysis.localAnalysis.frontiers pc)
  rw [← hraised] at hnonoutput ⊢
  have hdecodedNonoutput : decoded.op ≠ .output := by
    simpa [raiseInstructionResultLabel, raiseInstructionOccurrence] using hnonoutput
  simpa [raiseInstructionResultLabel] using
    flowsTo_trans hlocalToOccurrence
      (derived_occurrence_flows_to_raised_block decoded occurrence rootReturn hdecodedNonoutput)

set_option linter.unusedSimpArgs false in
private theorem decodeSemanticNode_instruction_ids
    (program : Combined.Program) (index : SemanticIndex) (labels : Array Label)
    (entries : Array (Option Nat)) (state : SemanticDecodeState) (node : Node) :
    ((decodeSemanticNode program index labels entries state node).instructions.toList.map
        Instruction.id = state.instructions.toList.map Instruction.id) ∨
      ((decodeSemanticNode program index labels entries state node).instructions.toList.map
        Instruction.id = state.instructions.toList.map Instruction.id ++ [node.nodeId]) := by
  cases hop : node.op <;> simp [decodeSemanticNode, hop]
  case semInstruction =>
    cases hdecode : decodeSemanticInstrOp? node.aux <;>
      simp [decodeSemanticNode, hop, hdecode]
  case semOperand =>
    cases howner : program.nodes[node.origin.toNat - 1]? <;>
      simp [decodeSemanticNode, hop, howner]
  case semLabelContract =>
    by_cases haux : node.aux = 3 <;> simp [decodeSemanticNode, hop, haux]

private theorem canonical_node_ids_nodup {program : Combined.Program}
    (hcanonical : CanonicalNodeIds program) :
    (program.nodes.toList.map Node.nodeId).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro left right hleft hright horder heq
  simp only [List.length_map, Array.length_toList] at hleft hright
  have hleftId := hcanonical left hleft
  have hrightId := hcanonical right hright
  have hid := congrArg UInt32.toNat heq
  simp only [List.getElem_map] at hid
  rw [hleftId, hrightId] at hid
  omega

private theorem decodeSemanticFold_instruction_id_sublist
    (program : Combined.Program) (index : SemanticIndex) (labels : Array Label)
    (entries : Array (Option Nat)) (nodes : List Node) (state : SemanticDecodeState) :
    ∃ selected,
      selected.Sublist (nodes.map Node.nodeId) ∧
        (nodes.foldl (decodeSemanticNode program index labels entries) state).instructions.toList.map
          Instruction.id = state.instructions.toList.map Instruction.id ++ selected := by
  induction nodes generalizing state with
  | nil => exact ⟨[], .slnil, by simp⟩
  | cons node rest ih =>
      let next := decodeSemanticNode program index labels entries state node
      obtain ⟨selected, hsublist, hresult⟩ := ih next
      rcases decodeSemanticNode_instruction_ids program index labels entries state node with
        hsame | hpushed
      · refine ⟨selected, hsublist.cons node.nodeId, ?_⟩
        simp only [List.foldl_cons, hresult, next]
        rw [hsame]
      · refine ⟨node.nodeId :: selected, hsublist.cons_cons node.nodeId, ?_⟩
        simp only [List.foldl_cons, hresult, next]
        rw [hpushed]
        simp [List.append_assoc]

private theorem semanticProgramOfWith_instruction_ids_nodup
    {program : Combined.Program} (hcanonical : CanonicalNodeIds program)
    (index : SemanticIndex) (labels : Array Label) :
    ((semanticProgramOfWith program index labels).instructions.toList.map Instruction.id).Nodup := by
  let entries := semanticBlockEntries program index
  let initial : SemanticDecodeState :=
    { policySelections := Array.replicate (program.nodes.size + 1) [] }
  let decoded := program.nodes.foldl
    (decodeSemanticNode program index labels entries) initial
  change (decoded.instructions.toList.map Instruction.id).Nodup
  obtain ⟨selected, hsublist, hresult⟩ :=
    decodeSemanticFold_instruction_id_sublist program index labels entries
      program.nodes.toList initial
  have hsource := canonical_node_ids_nodup hcanonical
  have hselected := hsublist.nodup hsource
  have hfold : decoded = program.nodes.toList.foldl
      (decodeSemanticNode program index labels entries) initial := by
    simp [decoded]
  rw [hfold, hresult]
  exact hselected

private theorem map_instruction_id_mapIdx_raise
    (instructions : List Instruction)
    (labels : Array Label)
    (occurrence : Nat → Instruction → Label)
    (rootReturn : Nat → Instruction → Option Label) :
    (List.mapIdx (fun pc instruction =>
        raiseInstructionResultLabel labels
          (raiseInstructionOccurrence instruction (occurrence pc instruction)
            (rootReturn pc instruction))) instructions).map Instruction.id =
      instructions.map Instruction.id := by
  induction instructions generalizing occurrence rootReturn with
  | nil => rfl
  | cons instruction rest ih =>
      rw [List.mapIdx_cons]
      simp only [List.map_cons]
      congr 1
      exact ih (fun pc next => occurrence (pc + 1) next)
        (fun pc next => rootReturn (pc + 1) next)

/-- The production raw machine retains the canonical source node identifiers, so instruction
    identifiers are unique.  This makes every site lookup authoritative rather than order
    dependent. -/
theorem rawSemanticProgram_instruction_ids_nodup {program : V9.Program}
    {analysis : Analysis} (hanalysis : analyze? program = some analysis) :
    ((rawSemanticProgram program analysis).instructions.toList.map Instruction.id).Nodup := by
  have hdataflow := (OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).1
  have hextract := (V9.OccurrenceDataflowSecurity.analyzed_components hdataflow).1
  have hcanonical := V9.OccurrenceDataflowSecurity.extracted_base_has_canonical_node_ids hextract
  have hcandidate := semanticProgramOfWith_instruction_ids_nodup hcanonical
    analysis.dataflow.semanticIndex analysis.dataflow.labels
  rw [rawSemanticProgram, Array.toList_mapIdx, map_instruction_id_mapIdx_raise]
  exact hcandidate

/-- A lookup in an instruction-ID-unique machine agrees with the semantic external-site lookup.
    This closes the gap between the verifier's instruction-local boundary classification and the
    raw machine's per-site cursor projection. -/
theorem externalSiteLabel_eq_blockLabel_of_lookup {machine : SemanticProgram}
    {pc : Nat} {instruction : Instruction}
    (hnodup : (machine.instructions.toList.map Instruction.id).Nodup)
    (hlookup : machine.instructions[pc]? = some instruction) :
    Semantic.externalSiteLabel machine instruction.id.toNat = instruction.blockLabel := by
  have hcurrentMem : instruction ∈ machine.instructions :=
    Array.mem_iff_getElem?.mpr ⟨pc, hlookup⟩
  unfold Semantic.externalSiteLabel
  cases hfind : machine.instructions.find?
      (fun candidate => candidate.id.toNat == instruction.id.toNat) with
  | none =>
      exact False.elim ((Array.find?_eq_none.mp hfind) instruction hcurrentMem (by simp))
  | some found =>
      have hfoundMem : found ∈ machine.instructions :=
        Array.mem_of_find?_eq_some hfind
      have hfoundIdNat : found.id.toNat = instruction.id.toNat := by
        simpa using (Array.find?_some hfind)
      have hfoundId : found.id = instruction.id := UInt32.ext hfoundIdNat
      obtain ⟨foundPc, hfoundBound, hfoundGet⟩ := Array.mem_iff_getElem.mp hfoundMem
      obtain ⟨hcurrentBound, hcurrentGet⟩ := Array.getElem?_eq_some_iff.mp hlookup
      have hfoundListBound : foundPc < machine.instructions.toList.length := by
        simpa using hfoundBound
      have hcurrentListBound : pc < machine.instructions.toList.length := by
        simpa using hcurrentBound
      have hposition : foundPc = pc := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have hpair := (List.pairwise_iff_getElem.mp
              (List.nodup_iff_pairwise_ne.mp hnodup)) foundPc pc
              (by simpa using hfoundListBound) (by simpa using hcurrentListBound) hlt
          apply hpair
          simp only [List.getElem_map]
          simpa [hfoundGet, hcurrentGet] using hfoundId
        · have hpair := (List.pairwise_iff_getElem.mp
              (List.nodup_iff_pairwise_ne.mp hnodup)) pc foundPc
              (by simpa using hcurrentListBound) (by simpa using hfoundListBound) hgt
          apply hpair
          simp only [List.getElem_map]
          simpa [hfoundGet, hcurrentGet] using hfoundId.symm
      subst foundPc
      have heq : found = instruction := by simpa [hcurrentGet] using hfoundGet.symm
      subst found
      simp [hcurrentGet]

/-- Production-specialized site agreement. -/
theorem raw_externalSiteLabel_eq_blockLabel {program : V9.Program}
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction) :
    Semantic.externalSiteLabel (rawSemanticProgram program analysis) instruction.id.toNat =
      instruction.blockLabel :=
  externalSiteLabel_eq_blockLabel_of_lookup
    (rawSemanticProgram_instruction_ids_nodup hanalysis) hlookup

/-- Every raw instruction still has the exact source semantic-instruction record from which the
    decoder constructed it.  Occurrence raising changes only the block label, so identity,
    function ownership, operation, and destination remain source-derived. -/
def DecodedInstructionSourceShape (program : Combined.Program)
    (index : SemanticIndex) (instruction : Instruction) : Prop :=
  ∃ source,
    source ∈ program.nodes.toList ∧ source.op = .semInstruction ∧
      decodeSemanticInstrOp? source.aux = some instruction.op ∧
      source.nodeId = instruction.id ∧
      source.origin = instruction.functionId ∧
      semanticResultCellFrom index source = instruction.destination ∧
      source.ceiling = instruction.operandCount ∧
      semanticFirstImmediate program source = instruction.aux

set_option linter.unusedSimpArgs false in
private theorem decodeSemanticNode_instruction_shape
    (program : Combined.Program) (index : SemanticIndex) (labels : Array Label)
    (entries : Array (Option Nat)) (state : SemanticDecodeState) (node : Node)
    (hnodeMem : node ∈ program.nodes)
    (hprior : ∀ instruction ∈ state.instructions,
      DecodedInstructionSourceShape program index instruction) :
    ∀ instruction ∈
        (decodeSemanticNode program index labels entries state node).instructions,
      DecodedInstructionSourceShape program index instruction := by
  intro instruction hmem
  cases hop : node.op
  case semInstruction =>
    cases hdecode : decodeSemanticInstrOp? node.aux with
    | none =>
        apply hprior instruction
        simpa [decodeSemanticNode, hop, hdecode] using hmem
    | some operation =>
        simp only [decodeSemanticNode, hop, hdecode, Array.mem_push] at hmem
        rcases hmem with hprevious | hnew
        · exact hprior instruction hprevious
        · subst instruction
          exact ⟨node, Array.mem_toList_iff.mpr hnodeMem, hop, hdecode, rfl, rfl, rfl, rfl, rfl⟩
  case semOperand =>
    cases howner : program.nodes[node.origin.toNat - 1]? <;>
      apply hprior instruction <;>
      simpa [decodeSemanticNode, hop, howner] using hmem
  case semLabelContract =>
    by_cases haux : node.aux = 3 <;>
      apply hprior instruction <;>
      simpa [decodeSemanticNode, hop, haux] using hmem
  all_goals
    apply hprior instruction
    simpa [decodeSemanticNode, hop] using hmem

private theorem decodeSemanticFold_instruction_shape
    (program : Combined.Program) (index : SemanticIndex) (labels : Array Label)
    (entries : Array (Option Nat)) (nodes : List Node) (state : SemanticDecodeState)
    (hnodes : ∀ node ∈ nodes, node ∈ program.nodes)
    (hprior : ∀ instruction ∈ state.instructions,
      DecodedInstructionSourceShape program index instruction) :
    ∀ instruction ∈
        (nodes.foldl (decodeSemanticNode program index labels entries) state).instructions,
      DecodedInstructionSourceShape program index instruction := by
  induction nodes generalizing state with
  | nil => simpa using hprior
  | cons node rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro candidate hcandidate
        exact hnodes candidate (List.mem_cons_of_mem node hcandidate)
      · exact decodeSemanticNode_instruction_shape program index labels entries state node
          (hnodes node (by simp)) hprior

theorem semanticProgramOfWith_instruction_source_shape
    (program : Combined.Program) (index : SemanticIndex) (labels : Array Label)
    {instruction : Instruction}
    (hmem : instruction ∈ (semanticProgramOfWith program index labels).instructions) :
    DecodedInstructionSourceShape program index instruction := by
  let entries := semanticBlockEntries program index
  let initial : SemanticDecodeState :=
    { policySelections := Array.replicate (program.nodes.size + 1) [] }
  let decoded := program.nodes.foldl
    (decodeSemanticNode program index labels entries) initial
  have hshape := decodeSemanticFold_instruction_shape program index labels entries
    program.nodes.toList initial (by simp) (by simp [initial])
  apply hshape instruction
  simpa [semanticProgramOfWith, entries, initial, decoded] using hmem

/-- Production-specialized source-shape extraction for any looked-up raw instruction. -/
theorem raw_instruction_source_shape
    {program : V9.Program} {analysis : Analysis} {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction) :
    DecodedInstructionSourceShape program.base analysis.dataflow.semanticIndex instruction := by
  let candidate := OccurrenceDataflow.semanticProgram program analysis.dataflow
  have hrawBound := (Array.getElem?_eq_some_iff.mp hlookup).1
  have hbound : pc < candidate.instructions.size := by
    simpa [rawSemanticProgram, candidate] using hrawBound
  let decoded := candidate.instructions[pc]
  have hdecodedMem : decoded ∈ candidate.instructions := Array.getElem_mem hbound
  have hdecodedShape := semanticProgramOfWith_instruction_source_shape program.base
    analysis.dataflow.semanticIndex analysis.dataflow.labels (by
      simpa [candidate, OccurrenceDataflow.semanticProgram] using hdecodedMem)
  have hrawGet := (Array.getElem?_eq_some_iff.mp hlookup).2
  have hraised : raiseInstructionResultLabel
      (occurrenceValueLabels analysis candidate) (raiseInstructionOccurrence decoded
      (if decoded.op == .output then localOccurrenceAt analysis.localAnalysis.frontiers pc
        else effectiveOccurrence analysis decoded pc)
      (rootReturnOccurrence? candidate analysis decoded)) = instruction := by
    simpa [rawSemanticProgram, candidate, decoded, hbound] using hrawGet
  rcases hdecodedShape with
    ⟨source, hmem, hop, hdecode, hid, hfunction, hdestination, hcount, haux⟩
  subst instruction
  exact ⟨source, hmem, hop,
    by simpa [raiseInstructionResultLabel, raiseInstructionOccurrence] using hdecode,
    by simpa [raiseInstructionResultLabel, raiseInstructionOccurrence] using hid,
    by simpa [raiseInstructionResultLabel, raiseInstructionOccurrence] using hfunction,
    by simpa [raiseInstructionResultLabel, raiseInstructionOccurrence] using hdestination,
    by simpa [raiseInstructionResultLabel, raiseInstructionOccurrence] using hcount,
    by simpa [raiseInstructionResultLabel, raiseInstructionOccurrence] using haux⟩

private theorem seedSemanticNode_inflationary
    (program : Combined.Program) (index : SemanticIndex)
    (labels : Array Label) (node : Node) :
    SemanticDataflow.ArrayFlows labels (seedSemanticNode program index labels node) := by
  unfold seedSemanticNode
  split <;> try exact SemanticDataflow.ArrayFlows.refl labels
  · split <;> try exact SemanticDataflow.ArrayFlows.refl labels
    split <;> try exact SemanticDataflow.ArrayFlows.refl labels
    split <;> try exact SemanticDataflow.ArrayFlows.refl labels
    · exact SemanticDataflow.ArrayFlows.raise labels _ _
    · split <;> try exact SemanticDataflow.ArrayFlows.refl labels
      exact SemanticDataflow.ArrayFlows.raise labels _ _
  · split <;> try exact SemanticDataflow.ArrayFlows.refl labels
    all_goals split <;> try exact SemanticDataflow.ArrayFlows.refl labels
    all_goals exact SemanticDataflow.ArrayFlows.raise labels _ _

private theorem seedSemanticFold_inflationary
    (program : Combined.Program) (index : SemanticIndex)
    (labels : Array Label) (nodes : List Node) :
    SemanticDataflow.ArrayFlows labels
      (nodes.foldl (seedSemanticNode program index) labels) := by
  induction nodes generalizing labels with
  | nil => exact SemanticDataflow.ArrayFlows.refl labels
  | cons node rest ih =>
      exact (seedSemanticNode_inflationary program index labels node).trans (ih _)

private theorem stateRead_seed_flows_through_list
    (program : Combined.Program) (index : SemanticIndex) (nodes : List Node)
    (labels : Array Label) {source : Node} {offset destination : UInt32}
    (hmem : source ∈ nodes)
    (hop : source.op = .semInstruction)
    (hdecode : decodeSemanticInstrOp? source.aux = some .stateRead)
    (himmediate : semanticImmediateAt? program source.nodeId 1 = some offset)
    (hdestination : semanticValueCell? index source.origin source.required = some destination)
    (hbound : destination.toNat < labels.size) :
    (semanticDeclaredStateLabelAt program offset).flowsTo
      (labelAt (nodes.foldl (seedSemanticNode program index) labels) destination) = true := by
  induction nodes generalizing labels with
  | nil => contradiction
  | cons head rest ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with heq | hrest
      · subst head
        have hraised : (semanticDeclaredStateLabelAt program offset).flowsTo
            (labelAt (seedSemanticNode program index labels source) destination) = true := by
          have hget := Array.getElem_setIfInBounds (xs := labels)
            (i := destination.toNat)
            (a := (labelAt labels destination).lub
              (semanticDeclaredStateLabelAt program offset))
            (j := destination.toNat) hbound
          simpa [seedSemanticNode, hop, hdecode, himmediate, hdestination, raiseCell, labelAt,
            Array.getD, hbound, hget] using
              flowsTo_lub_right (labelAt labels destination)
                (semanticDeclaredStateLabelAt program offset)
        have htail := seedSemanticFold_inflationary program index
          (seedSemanticNode program index labels source) rest
        exact flowsTo_trans hraised
          (htail.2 destination (by
            simpa [SemanticDataflow.seedSemanticNode_size] using hbound))
      · apply ih (seedSemanticNode program index labels head) hrest
        simpa [SemanticDataflow.seedSemanticNode_size] using hbound

/-- The declared global state label at a state-read offset is a lower bound on the semantic seed
    of that instruction's destination. -/
theorem stateRead_seed_flows_to_semantic_seed_labels
    (program : Combined.Program) (index : SemanticIndex)
    {source : Node} {offset destination : UInt32}
    (hmem : source ∈ program.nodes.toList)
    (hop : source.op = .semInstruction)
    (hdecode : decodeSemanticInstrOp? source.aux = some .stateRead)
    (himmediate : semanticImmediateAt? program source.nodeId 1 = some offset)
    (hdestination : semanticValueCell? index source.origin source.required = some destination)
    (hbound : destination.toNat < semanticTaintCellCount program) :
    (semanticDeclaredStateLabelAt program offset).flowsTo
      (labelAt (semanticSeedLabelsWithIndex program index) destination) = true := by
  unfold semanticSeedLabelsWithIndex
  rw [← Array.foldl_toList]
  exact stateRead_seed_flows_through_list program index program.nodes.toList
    (Array.replicate (semanticTaintCellCount program) .pub) hmem hop hdecode himmediate
      hdestination (by simpa using hbound)

private theorem stateSinkAt_source {program : V9.Program} {analysis : Analysis}
    {instruction : Instruction} {operation : SemanticInstrOp} {position : Nat}
    {sink : Label}
    (h : stateSinkAt? program analysis instruction operation position = some sink) :
    ∃ source offset,
      program.base.nodes[instruction.id.toNat - 1]? = some source ∧
        semanticImmediateAt? program.base source.nodeId position = some offset ∧
        stateLabelForFunctionAt? analysis.stateContracts instruction.functionId offset =
          some sink := by
  unfold stateSinkAt? at h
  simp only [bind, Option.bind_none] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨source, hsource, h⟩ := h
  split at h
  · cases h
  · rw [Option.bind_eq_some_iff] at h
    obtain ⟨offset, hoffset, hlookup⟩ := h
    exact ⟨source, offset, hsource, hoffset, hlookup⟩

theorem canonical_node_lookup_of_mem_id {program : V9.Program}
    {node : Node} {id : UInt32}
    (hcanonical : CanonicalNodeIds program.base)
    (hmem : node ∈ program.base.nodes.toList) (hid : node.nodeId = id) :
    program.base.nodes[id.toNat - 1]? = some node := by
  obtain ⟨position, hposition, hget⟩ :=
    Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hmem)
  have hcanonicalAt := hcanonical position hposition
  have hgetList : program.base.nodes.toList[position] = node := by simpa using hget
  have hpositionEq : id.toNat - 1 = position := by
    have hidNat := congrArg UInt32.toNat hid
    rw [hgetList] at hcanonicalAt
    omega
  subst position
  exact Array.getElem?_eq_some_iff.mpr ⟨hposition, hget⟩

private theorem stateSinkAt_stateWrite_source
    {program : V9.Program} {analysis : Analysis} {instruction : Instruction} {sink : Label}
    (h : stateSinkAt? program analysis instruction .stateWrite 2 = some sink) :
    ∃ source offset,
      program.base.nodes[instruction.id.toNat - 1]? = some source ∧
        decodeSemanticInstrOp? source.aux = some .stateWrite ∧
        semanticImmediateAt? program.base source.nodeId 2 = some offset ∧
        stateLabelForFunctionAt? analysis.stateContracts instruction.functionId offset =
          some sink := by
  unfold stateSinkAt? at h
  simp only [bind, Option.bind_none] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨source, hsource, h⟩ := h
  by_cases hbad : (source.nodeId != instruction.id || source.op != .semInstruction ||
      decodeSemanticInstrOp? source.aux != some .stateWrite) = true
  · simp [hbad] at h
  · have hgood : (source.nodeId != instruction.id || source.op != .semInstruction ||
        decodeSemanticInstrOp? source.aux != some .stateWrite) = false :=
      by simpa only [Bool.not_eq_true] using hbad
    simp only [Bool.or_eq_false_iff] at hgood
    have hdecode : decodeSemanticInstrOp? source.aux = some .stateWrite := by
      have hdecoded := hgood.2
      cases hresult : decodeSemanticInstrOp? source.aux with
      | none =>
          rw [hresult] at hdecoded
          cases hdecoded
      | some operation =>
          rw [hresult] at hdecoded
          cases operation <;> first | rfl | cases hdecoded
    simp [hgood] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨offset, hoffset, hlookup⟩ := h
    exact ⟨source, offset, hsource, hdecode, hoffset, hlookup⟩

private theorem label_flows_to_state_contract_fold
    (initial : Label) (offset : UInt32) (contracts : List Node) :
    initial.flowsTo
      (contracts.foldl (fun label contract =>
        if contract.op == .semLabelContract && contract.aux == 3 && contract.flags == 1 &&
            contract.actual == offset then label.lub contract.labelA
        else label) initial) = true := by
  induction contracts generalizing initial with
  | nil => simp [Label.flowsTo, Label.rank]
  | cons contract rest ih =>
      simp only [List.foldl_cons]
      apply flowsTo_trans (second := if contract.op == .semLabelContract &&
        contract.aux == 3 && contract.flags == 1 && contract.actual == offset then
          initial.lub contract.labelA else initial)
      · split
        · exact flowsTo_lub_left initial contract.labelA
        · cases initial <;> decide
      · exact ih _

private theorem matching_state_contract_flows_to_fold
    (initial : Label) (offset : UInt32) (contracts : List Node) {contract : Node}
    (hmem : contract ∈ contracts)
    (hmatch : (contract.op == .semLabelContract && contract.aux == 3 &&
      contract.flags == 1 && contract.actual == offset) = true) :
    contract.labelA.flowsTo
      (contracts.foldl (fun label current =>
        if current.op == .semLabelContract && current.aux == 3 && current.flags == 1 &&
            current.actual == offset then label.lub current.labelA
        else label) initial) = true := by
  induction contracts generalizing initial with
  | nil => contradiction
  | cons head rest ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with heq | hrest
      · subst head
        have hfirst : contract.labelA.flowsTo (initial.lub contract.labelA) = true :=
          flowsTo_lub_right initial contract.labelA
        have htail := label_flows_to_state_contract_fold
          (initial.lub contract.labelA) offset rest
        simpa [hmatch] using flowsTo_trans hfirst htail
      · exact ih (if head.op == .semLabelContract && head.aux == 3 && head.flags == 1 &&
          head.actual == offset then initial.lub head.labelA else initial) hrest

/-- Every exact function-owned actor-state sink flows to the label used by the current raw
    machine. The implication is intentionally one-way: the raw label joins declarations at the
    same numeric offset across functions. -/
theorem analyzed_state_sink_flows_to_runtime_label {program : V9.Program}
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {functionId offset : UInt32} {sink : Label}
    (hlookup : stateLabelForFunctionAt? analysis.stateContracts functionId offset = some sink) :
    sink.flowsTo (stateLabelAt (rawSemanticProgram program analysis) offset) = true := by
  obtain ⟨contract, hcontract, hdeclaration, _, hactual, hlabel⟩ :=
    analyzed_state_lookup_has_exact_declaration hanalysis hlookup
  have hmem : contract ∈ program.base.nodes.toList := by
    apply Array.mem_toList_iff.mpr
    exact Array.mem_iff_getElem?.mpr ⟨contract.nodeId.toNat - 1, hcontract⟩
  have hmatch : (contract.op == .semLabelContract && contract.aux == 3 &&
      contract.flags == 1 && contract.actual == offset) = true := by
    simpa [stateContractDeclarationB, hactual] using hdeclaration
  have hflow := matching_state_contract_flows_to_fold .pub offset
    program.base.nodes.toList hmem hmatch
  simpa [rawSemanticProgram, OccurrenceDataflow.semanticProgram, semanticProgramOfWith,
    stateLabelAt, semanticDeclaredStateLabelAt, semanticDeclaredStateLabelAtList, hlabel]
    using hflow

private theorem ffiContract_impossible_of_stateWrite_decode
    {program : V9.Program} {sourceIndex : BindingIndex} {owner : Node}
    {position : Nat} {contract : FfiContract}
    (hdecode : decodeSemanticInstrOp? owner.aux = some .stateWrite)
    (hffi : ffiContract? program sourceIndex owner position = some contract) : False := by
  have haux : owner.aux ≠ 15 := by
    intro heq
    simp [heq, decodeSemanticInstrOp?] at hdecode
  have hbne : (owner.aux != 15) = true := bne_iff_ne.mpr haux
  simp [ffiContract?, hbne] at hffi

private theorem actorContract_impossible_of_stateWrite_decode
    {program : V9.Program} {owner : Node} {position : Nat} {contract : ActorContract}
    (hdecode : decodeSemanticInstrOp? owner.aux = some .stateWrite)
    (hactor : actorContract? program owner position = some contract) : False := by
  have haux : owner.aux ≠ 8 := by
    intro heq
    simp [heq, decodeSemanticInstrOp?] at hdecode
  have hbne : (owner.aux != 8) = true := bne_iff_ne.mpr haux
  simp [actorContract?, hbne] at hactor

/-- Production site extraction cannot hide a state write behind an FFI or actor site kind. -/
theorem returned_stateWrite_occurrence_safe
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hop : instruction.op = .stateWrite) :
    StateWriteOccurrenceSafe program analysis instruction pc := by
  have hsiteSafe :=
    (returned_instruction_occurrence_safe hjudgment hanalysis hlookup).2.2.2.2
  unfold SiteOccurrenceSafe at hsiteSafe
  cases hsite : site? analysis.dataflow.contracts instruction.id with
  | none => simp [hsite] at hsiteSafe
  | some site =>
      simp only [hsite] at hsiteSafe
      have hbody := returned_public_state_write_source_safe hjudgment hanalysis hlookup hop
      unfold publicStateWriteSourceBodyOK at hbody
      cases hsink : stateSinkAt? program analysis instruction .stateWrite 2 with
      | none => simp [hsink] at hbody
      | some sink =>
          obtain ⟨source, _, hsource, hdecode, _, _⟩ :=
            stateSinkAt_stateWrite_source hsink
          have hdataflow :=
            (OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).1
          have hextract := (V9.OccurrenceDataflowSecurity.analyzed_components hdataflow).1
          obtain ⟨sourceIndex, owner, _, howner, _, hmatches⟩ :=
            BoundaryContracts.returned_site_has_actual_record hextract hsite
          have hownerEq : owner = source := Option.some.inj (howner.symm.trans hsource)
          subst owner
          have hkindSafe := hsiteSafe.2.2
          cases hkind : site.kind with
          | ordinary operation =>
              simp only [hkind] at hkindSafe
              rcases hkindSafe with ⟨hoperation, hoperationSafe⟩
              rw [hop] at hoperation
              subst operation
              exact hoperationSafe
          | ffi position contract =>
              have hffi : ffiContract? program sourceIndex source position = some contract := by
                have hm := hmatches
                simp [siteMatches, hkind] at hm
                exact hm.2
              exact False.elim
                (ffiContract_impossible_of_stateWrite_decode hdecode hffi)
          | actor position contract =>
              have hactor : actorContract? program source position = some contract := by
                have hm := hmatches
                simp [siteMatches, hkind] at hm
                exact hm.2
              exact False.elim
                (actorContract_impossible_of_stateWrite_decode hdecode hactor)

/-- A verified state write reached at a non-Public occurrence resolves to an exact non-Public
    function-owned sink, and therefore also to a non-Public raw global-offset label. -/
theorem verified_stateWrite_sink_nonpublic
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hop : instruction.op = .stateWrite)
    (hnonpublic : instruction.blockLabel ≠ .pub) :
    ∃ offset sink,
      stateSinkAt? program analysis instruction .stateWrite 2 = some sink ∧
        stateLabelForFunctionAt? analysis.stateContracts instruction.functionId offset = some sink ∧
        stateLabelAt (rawSemanticProgram program analysis) offset ≠ .pub := by
  have hsafe := returned_public_state_write_source_safe hjudgment hanalysis hlookup hop
  unfold publicStateWriteSourceBodyOK at hsafe
  cases hsink : stateSinkAt? program analysis instruction .stateWrite 2 with
  | none => simp [hsink] at hsafe
  | some sink =>
      obtain ⟨source, offset, hsource, _, hoffset, hlookupSink⟩ :=
        stateSinkAt_stateWrite_source hsink
      have hglobal := analyzed_state_sink_flows_to_runtime_label hanalysis hlookupSink
      have hsinkPrivate : sink ≠ .pub := by
        obtain ⟨occSource, occOffset, occSink, hoccSource, _, _, _, hoccOffset,
            hoccLookup, hoccFlow⟩ :=
          returned_stateWrite_occurrence_safe hjudgment hanalysis hlookup hop
        have hsourceEq : occSource = source :=
          Option.some.inj (hoccSource.symm.trans hsource)
        subst occSource
        have hoffsetEq : occOffset = offset :=
          Option.some.inj (hoccOffset.symm.trans hoffset)
        subst occOffset
        have hsinkEq : occSink = sink :=
          Option.some.inj (hoccLookup.symm.trans hlookupSink)
        subst occSink
        intro hpublic
        exact hnonpublic ((flowsTo_public_iff instruction.blockLabel).mp
          (hpublic ▸ hoccFlow))
      have hglobalPrivate : stateLabelAt (rawSemanticProgram program analysis) offset ≠ .pub := by
        intro hpublic
        exact hsinkPrivate ((flowsTo_public_iff sink).mp (hpublic ▸ hglobal))
      exact ⟨offset, sink, by simpa using hsink, hlookupSink, hglobalPrivate⟩

/-- A non-Public raw instruction cannot write a nonzero Public destination.  This is the
    load-bearing conservative rule while the raw machine still uses globally shared SSA storage. -/
theorem nonpublic_has_no_public_destination {instruction : Instruction}
    (hsafe : LocalDestinationSafe instruction) (hnonpublic : instruction.blockLabel ≠ .pub) :
    instruction.destination = 0 ∨ instruction.resultLabel ≠ .pub := by
  rcases hsafe with hdestination | hflow
  · exact Or.inl hdestination
  · exact Or.inr fun hresult => hnonpublic
      ((flowsTo_public_iff instruction.blockLabel).mp (hresult ▸ hflow))

/-- Lookup-specialized form used directly by raw-step proofs. -/
theorem verified_nonpublic_has_no_public_destination {program : V9.Program}
    (hjudgment : V9OccurrenceJudgment program) {analysis : Analysis}
    (hanalysis : analyze? program = some analysis) {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub) :
    instruction.destination = 0 ∨ instruction.resultLabel ≠ .pub :=
  nonpublic_has_no_public_destination
    (returned_instruction_occurrence_safe hjudgment hanalysis hlookup).1 hnonpublic

/-- Conversely, any nonzero Public result forces the raw instruction occurrence to be Public. -/
theorem public_destination_has_public_occurrence {instruction : Instruction}
    (hsafe : LocalDestinationSafe instruction) (hdestination : instruction.destination ≠ 0)
    (hresult : instruction.resultLabel = .pub) :
    instruction.blockLabel = .pub := by
  rcases hsafe with hzero | hflow
  · exact False.elim (hdestination hzero)
  · exact (flowsTo_public_iff instruction.blockLabel).mp (hresult ▸ hflow)

/-- Raw static safety supplies actual decoder well-formedness for the looked-up instruction. -/
theorem instruction_well_formed_of_raw_static_safe {machine : SemanticProgram}
    (hstatic : OperationalStaticSafe machine) {pc : Nat} {instruction : Instruction}
    (hlookup : machine.instructions[pc]? = some instruction) :
    instructionWellFormed machine instruction := by
  obtain ⟨hpc, hinstruction⟩ := Array.getElem?_eq_some_iff.mp hlookup
  have hmem : instruction ∈ machine.instructions.toList :=
    Array.mem_toList_iff.mpr (hinstruction ▸ Array.getElem_mem hpc)
  exact hstatic.1.1.2.2 instruction hmem

/-- Every decoded value operand names an in-bounds verifier label cell. -/
theorem valueOperandCells_bounded {machine : SemanticProgram} {instruction : Instruction}
    (hwell : instructionWellFormed machine instruction) {cell : UInt32}
    (hcell : cell ∈ valueOperandCells machine instruction) :
    cell.toNat < machine.valueLabels.size := by
  unfold valueOperandCells at hcell
  simp only [List.mem_filterMap] at hcell
  obtain ⟨operand, hoperand, hselected⟩ := hcell
  unfold instructionOperands at hoperand
  simp only [List.mem_filterMap] at hoperand
  obtain ⟨offset, hoffset, hlookup⟩ := hoperand
  have hoffsetBound : offset < instruction.operandCount.toNat := List.mem_range.mp hoffset
  have hslice := hwell.2.2.2.1.2 offset hoffsetBound
  simp only at hslice
  unfold instructionOperandAt? at hlookup
  simp [hoffsetBound] at hlookup
  split at hselected
  · rename_i hkind
    have hvalue : operand.value = cell := Option.some.inj hselected
    subst cell
    cases harr : machine.operands[instruction.firstOperand.toNat + offset]? with
    | none => simp [harr] at hlookup
    | some actual =>
        simp only [harr, Option.bind_some] at hlookup
        split at hlookup
        · have heq : actual = operand := Option.some.inj hlookup
          subst operand
          obtain ⟨hindex, hget⟩ := Array.getElem?_eq_some_iff.mp harr
          have hgetD : machine.operands.getD
              (instruction.firstOperand.toNat + offset) default = actual := by
            simp [Array.getD, hindex, hget]
          rw [hgetD] at hslice
          exact hslice.2.2 ((beq_iff_eq).mp hkind)
        · simp at hlookup
  · simp at hselected

/-- Public data equivalence determines every in-bounds statically Public scalar read. -/
theorem readProgramValue_eq_of_public_data {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) {cell : UInt32}
    (hbound : cell.toNat < machine.valueLabels.size)
    (hpublic : labelAt machine.valueLabels cell = .pub) :
    readProgramValue machine left cell = readProgramValue machine right cell := by
  rcases hdata with ⟨_, _, _, hleftSize, hrightSize, hvalues⟩
  have hleftBound : cell.toNat < left.values.size := by simpa [hleftSize] using hbound
  have hrightBound : cell.toNat < right.values.size := by simpa [hrightSize] using hbound
  have hpayload := hvalues cell.toNat hleftBound hrightBound (by simpa using hpublic)
  simp [readProgramValue, readValue, Array.getD, hleftBound, hrightBound, hpayload]

/-- Pointwise Public dependency facts lift to the complete operand-value list. -/
theorem readProgramValues_eq_of_public_data {machine : SemanticProgram} {left right : State}
    (hdata : PublicDataEquivalent machine left right) (cells : List UInt32)
    (hbounds : ∀ cell ∈ cells, cell.toNat < machine.valueLabels.size)
    (hpublic : ∀ cell ∈ cells, labelAt machine.valueLabels cell = .pub) :
    cells.map (readProgramValue machine left) = cells.map (readProgramValue machine right) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨readProgramValue_eq_of_public_data hdata (hbounds cell (by simp))
        (hpublic cell (by simp)), ?_⟩
      exact ih (fun item hitem => hbounds item (by simp [hitem]))
        (fun item hitem => hpublic item (by simp [hitem]))

/-- Immutable per-site streams plus equality of a Public site's own cursor determine its next
    external input. Activity at any other site is irrelevant to this equation. -/
theorem public_readExternal_eq {machine : SemanticProgram} {left right : State}
    (hexternal : PublicExternalEquivalent machine left right) {site : UInt32}
    (hleft : site.toNat < left.externalCursors.size)
    (hright : site.toNat < right.externalCursors.size)
    (hpublic : Semantic.externalSiteLabel machine site.toNat = .pub) :
    readExternal left site = readExternal right site := by
  rcases hexternal with ⟨hinputs, _, hcursors⟩
  have hcursor := hcursors site.toNat hleft hright hpublic
  have hleftCursor : left.externalCursors.getD site.toNat 0 =
      left.externalCursors[site.toNat] := by simp [Array.getD, hleft]
  have hrightCursor : right.externalCursors.getD site.toNat 0 =
      right.externalCursors[site.toNat] := by simp [Array.getD, hright]
  unfold readExternal
  rw [hinputs, hleftCursor, hrightCursor, hcursor]

/-! ## Unary Public-projection preservation -/

/-- Updating an array cell hidden by a static visibility mask leaves the complete masked array,
    including its shape, unchanged. -/
theorem maskedCells_setIfInBounds_invisible {α β : Type} (visible : Nat → Bool)
    (payload : α → β) (cells : Array α) (position : Nat) (value : α)
    (hinvisible : visible position = false) :
    maskedCells visible payload (cells.setIfInBounds position value) =
      maskedCells visible payload cells := by
  apply Array.ext
  · simp [maskedCells]
  · intro index hleft hright
    have hbound : index < cells.size := by simpa [maskedCells] using hright
    by_cases heq : index = position
    · subst index
      simp [maskedCells, hinvisible]
    · have hne : position ≠ index := Ne.symm heq
      simp [maskedCells, hbound, hne]

/-- A verifier-isolated non-Public destination write cannot change any component of the full
    Public projection. Runtime value labels are irrelevant: visibility comes from `machine`. -/
theorem writeDestination_preserves_publicProjection {machine : SemanticProgram}
    (state : State) (instruction : Instruction) (payload : Int)
    (hwell : instructionWellFormed machine instruction)
    (hisolated : instruction.destination = 0 ∨ instruction.resultLabel ≠ .pub) :
    publicProjection machine (writeDestination state instruction payload) =
      publicProjection machine state := by
  by_cases hdestination : instruction.destination = 0
  · simp [writeDestination, hdestination]
  · have hresult : instruction.resultLabel ≠ .pub := by
      exact hisolated.resolve_left hdestination
    have hlabelNonpublic : labelAt machine.valueLabels instruction.destination ≠ .pub := by
      intro hpublic
      exact hresult (hwell.2.2.1.trans hpublic)
    have hinvisible :
        (labelAt machine.valueLabels (UInt32.ofNat instruction.destination.toNat)).eqb .pub =
          false := by
      have hroundtrip : UInt32.ofNat instruction.destination.toNat = instruction.destination := by
        simp
      rw [hroundtrip]
      cases hlabel : labelAt machine.valueLabels instruction.destination <;>
        simp_all [Label.eqb]
    have hdestinationB : (instruction.destination == 0) = false := by
      cases hbeq : instruction.destination == 0 with
      | false => rfl
      | true => exact False.elim (hdestination ((beq_iff_eq).mp hbeq))
    simp only [publicProjection, writeDestination_aggregates, writeDestination_actorState,
      writeDestination_externalCursors, PublicProjection.mk.injEq]
    refine ⟨?_, trivial, trivial, trivial⟩
    simp only [writeDestination, hdestinationB]
    exact maskedCells_setIfInBounds_invisible
      (fun cell => (labelAt machine.valueLabels (UInt32.ofNat cell)).eqb .pub)
      Value.payload state.values instruction.destination.toNat
      ⟨instruction.resultLabel, payload⟩ hinvisible

/-- Advancing one statically non-Public external site cannot change the per-site Public cursor
    projection; every other site is untouched by construction. -/
theorem advanceExternal_preserves_publicProjection_of_nonpublic_site
    (machine : SemanticProgram) (state : State) (site : UInt32)
    (hnonpublic : Semantic.externalSiteLabel machine site.toNat ≠ .pub) :
    publicProjection machine (advanceExternal state site) = publicProjection machine state := by
  have hinvisible :
      (Semantic.externalSiteLabel machine site.toNat).eqb .pub = false := by
    cases hlabel : Semantic.externalSiteLabel machine site.toNat <;>
      simp_all [Label.eqb]
  unfold advanceExternal
  dsimp only
  split
  · rename_i hadvance
    simp only [publicProjection, PublicProjection.mk.injEq]
    refine ⟨trivial, trivial, trivial, ?_⟩
    exact maskedCells_setIfInBounds_invisible
      (fun position => (Semantic.externalSiteLabel machine position).eqb .pub)
      id state.externalCursors site.toNat
      (state.externalCursors.getD site.toNat 0 + 1) hinvisible
  · rfl

/-- A concrete write to a statically non-Public actor-state cell leaves the full Public
    projection unchanged, even if its runtime `Value.label` is adversarial. -/
theorem actorStateWrite_preserves_publicProjection_of_nonpublic_sink
    (machine : SemanticProgram) (state : State) (offset : UInt32) (stored : Value)
    (hnonpublic : stateLabelAt machine offset ≠ .pub) :
    publicProjection machine
        { state with actorState := state.actorState.setIfInBounds offset.toNat stored } =
      publicProjection machine state := by
  have hinvisible :
      (stateLabelAt machine (UInt32.ofNat offset.toNat)).eqb .pub = false := by
    have hroundtrip : UInt32.ofNat offset.toNat = offset := by simp
    rw [hroundtrip]
    cases hlabel : stateLabelAt machine offset <;> simp_all [Label.eqb]
  simp only [publicProjection, PublicProjection.mk.injEq]
  refine ⟨trivial, trivial, ?_, trivial⟩
  exact maskedCells_setIfInBounds_invisible
    (fun position => (stateLabelAt machine (UInt32.ofNat position)).eqb .pub)
    Value.payload state.actorState offset.toNat stored hinvisible

/-- Raw state offsets are signed 64-bit immediates, so the update index is a `Nat` before the
    program-label lookup truncates it to `UInt32`. This exact helper mirrors that machine shape. -/
theorem actorStateWriteAtNat_preserves_publicProjection_of_nonpublic_sink
    (machine : SemanticProgram) (state : State) (position : Nat) (stored : Value)
    (hnonpublic : stateLabelAt machine (UInt32.ofNat position) ≠ .pub) :
    publicProjection machine
        { state with actorState := state.actorState.setIfInBounds position stored } =
      publicProjection machine state := by
  have hinvisible : (stateLabelAt machine (UInt32.ofNat position)).eqb .pub = false := by
    cases hlabel : stateLabelAt machine (UInt32.ofNat position) <;>
      simp_all [Label.eqb]
  simp only [publicProjection, PublicProjection.mk.injEq]
  refine ⟨trivial, trivial, ?_, trivial⟩
  exact maskedCells_setIfInBounds_invisible
    (fun offset => (stateLabelAt machine (UInt32.ofNat offset)).eqb .pub)
    Value.payload state.actorState position stored hinvisible

/-- Updating the aggregate attached to a non-Public SSA cell is invisible to the same static
    projection mask used for scalar storage. -/
theorem aggregateWrite_preserves_publicProjection_of_nonpublic_cell
    (machine : SemanticProgram) (state : State) (cell : UInt32) (payload : List Int)
    (hnonpublic : labelAt machine.valueLabels cell ≠ .pub) :
    publicProjection machine
        { state with aggregates := state.aggregates.setIfInBounds cell.toNat payload } =
      publicProjection machine state := by
  have hinvisible :
      (labelAt machine.valueLabels (UInt32.ofNat cell.toNat)).eqb .pub = false := by
    have hroundtrip : UInt32.ofNat cell.toNat = cell := by simp
    rw [hroundtrip]
    cases hlabel : labelAt machine.valueLabels cell <;> simp_all [Label.eqb]
  simp only [publicProjection, PublicProjection.mk.injEq]
  refine ⟨trivial, ?_, trivial, trivial⟩
  exact maskedCells_setIfInBounds_invisible
    (fun position => (labelAt machine.valueLabels (UInt32.ofNat position)).eqb .pub)
    id state.aggregates cell.toNat payload hinvisible

/-- Every ordinary constructor under a non-Public verified occurrence preserves the entire
    Public projection. This includes scalar and aggregate writes; control, halt, and trap fields
    are deliberately absent from the data projection. -/
theorem ordinaryStep_preserves_publicProjection
    (machine : SemanticProgram) (state : State) (instruction : Instruction)
    (hwell : instructionWellFormed machine instruction)
    (hsafe : LocalDestinationSafe instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub) :
    publicProjection machine (ordinaryStep machine state instruction).state =
      publicProjection machine state := by
  have hisolated := nonpublic_has_no_public_destination hsafe hnonpublic
  have hwrite := writeDestination_preserves_publicProjection state instruction
    (instructionPayload machine state instruction) hwell hisolated
  unfold ordinaryStep
  dsimp only
  split
  · rename_i haggregate
    have hdestination : instruction.destination ≠ 0 := by
      simp only [Bool.and_eq_true, bne_iff_ne] at haggregate
      exact haggregate.2
    have hresult : instruction.resultLabel ≠ .pub :=
      hisolated.resolve_left hdestination
    have hlabel : labelAt machine.valueLabels instruction.destination ≠ .pub := by
      intro hpublic
      exact hresult (hwell.2.2.1.trans hpublic)
    have haggregateProjection :=
      aggregateWrite_preserves_publicProjection_of_nonpublic_cell machine
        (writeDestination state instruction (instructionPayload machine state instruction))
        instruction.destination (operandPayloads machine state instruction) hlabel
    exact (by simpa [publicProjection] using haggregateProjection.trans hwrite)
  · exact (by simpa [publicProjection] using hwrite)

/-- Applying the same concrete update to two arrays preserves equality of their complete masked
    views. This is the algebra needed to restore identical saved-frame cells after stuttering. -/
theorem maskedCells_setIfInBounds_congr {α β : Type} (visible : Nat → Bool)
    (payload : α → β) {left right : Array α} (position : Nat) (value : α)
    (heq : maskedCells visible payload left = maskedCells visible payload right) :
    maskedCells visible payload (left.setIfInBounds position value) =
      maskedCells visible payload (right.setIfInBounds position value) := by
  have hsize : left.size = right.size := by
    simpa [maskedCells] using congrArg Array.size heq
  apply Array.ext
  · simp [maskedCells, hsize]
  · intro index hleft hright
    have hleftBound : index < left.size := by simpa [maskedCells] using hleft
    have hrightBound : index < right.size := by simpa [maskedCells] using hright
    by_cases hindex : index = position
    · subst index
      simp [maskedCells]
    · have hcell := congrArg (fun cells => cells[index]?) heq
      have hne : position ≠ index := Ne.symm hindex
      simpa [maskedCells, hleftBound, hrightBound, hindex, hne] using hcell

/-- Identical saved-cell restoration preserves equality of complete Public projections. -/
theorem restoreValues_preserves_publicProjection_eq
    (machine : SemanticProgram) {left right : State}
    (heq : publicProjection machine left = publicProjection machine right)
    (saved : List (UInt32 × Value)) :
    publicProjection machine (restoreValues left saved) =
      publicProjection machine (restoreValues right saved) := by
  induction saved generalizing left right with
  | nil => exact heq
  | cons head rest ih =>
      rcases head with ⟨cell, value⟩
      apply ih
      simp only [publicProjection, PublicProjection.mk.injEq] at heq ⊢
      exact ⟨maskedCells_setIfInBounds_congr _ _ cell.toNat value heq.1,
        heq.2.1, heq.2.2.1, heq.2.2.2⟩

/-- Applying the same proof-only frame prefix preserves equality of Public projections. -/
theorem restoreFrameStack_preserves_publicProjection_eq
    (machine : SemanticProgram) {left right : State}
    (heq : publicProjection machine left = publicProjection machine right)
    (frames : List CallFrame) :
    publicProjection machine (restoreFrameStack left frames) =
      publicProjection machine (restoreFrameStack right frames) := by
  induction frames generalizing left right with
  | nil => exact heq
  | cons frame rest ih =>
      exact ih (restoreValues_preserves_publicProjection_eq machine heq
        frame.savedParameters)

/-- A private return may restore its saved parameters and write a non-Public result. After popping
    that frame, restoring the remaining private prefix yields exactly the same Public projection
    as restoring the original prefix in place. -/
theorem privateReturn_preserves_prefix_restored_publicProjection
    (machine : SemanticProgram) (state : State) (frame : CallFrame)
    (rest privatePrefix : List CallFrame) (payload : Int)
    (hisolated : frame.destination = 0 ∨
      labelAt machine.valueLabels frame.destination ≠ .pub) :
    let restored := restoreValues state frame.savedParameters
    let values := restored.values.setIfInBounds frame.destination.toNat
      ⟨labelAt machine.valueLabels frame.destination, payload⟩
    let returned := if frame.destination == 0 then restored else
      { restored with values := values }
    publicProjection machine
        (restoreFrameStack { returned with pc := frame.returnPc, callStack := rest }
          privatePrefix) =
      publicProjection machine (restoreFrameStack state (frame :: privatePrefix)) := by
  dsimp only
  simp only [restoreFrameStack_cons]
  apply restoreFrameStack_preserves_publicProjection_eq
  by_cases hdestination : frame.destination = 0
  · simp [hdestination, publicProjection]
  · have hnonpublic := hisolated.resolve_left hdestination
    have hinvisible :
        (labelAt machine.valueLabels (UInt32.ofNat frame.destination.toNat)).eqb .pub = false := by
      have hroundtrip : UInt32.ofNat frame.destination.toNat = frame.destination := by simp
      rw [hroundtrip]
      cases hlabel : labelAt machine.valueLabels frame.destination <;>
        simp_all [Label.eqb]
    have hmasked := maskedCells_setIfInBounds_invisible
      (fun position => (labelAt machine.valueLabels (UInt32.ofNat position)).eqb .pub)
      Value.payload (restoreValues state frame.savedParameters).values
      frame.destination.toNat
      ⟨labelAt machine.valueLabels frame.destination, payload⟩ hinvisible
    simpa [publicProjection, hdestination] using hmasked

/-- Raw call entry either traps without changing projection-bearing storage or pushes the genuine
    machine frame. Restoring that new frame and the older private prefix recovers the exact
    pre-call Public projection. -/
theorem callStep_preserves_prefix_restored_publicProjection
    (machine : SemanticProgram) (state : State) (instruction : Instruction)
    (privatePrefix spine : List CallFrame)
    (hstack : state.callStack = privatePrefix ++ spine) :
    ∃ nextPrefix,
      (callStep machine state instruction).state.callStack = nextPrefix ++ spine ∧
        publicProjection machine
            (restoreFrameStack (callStep machine state instruction).state nextPrefix) =
          publicProjection machine (restoreFrameStack state privatePrefix) := by
  unfold callStep
  split
  · refine ⟨privatePrefix, by simpa using hstack, ?_⟩
    have hbase : publicProjection machine { state with trapped := true } =
        publicProjection machine state := rfl
    exact restoreFrameStack_preserves_publicProjection_eq machine hbase privatePrefix
  · rename_i callee hcallee
    dsimp only
    split
    · refine ⟨privatePrefix, by simpa using hstack, ?_⟩
      have hbase : publicProjection machine { state with trapped := true } =
          publicProjection machine state := rfl
      exact restoreFrameStack_preserves_publicProjection_eq machine hbase privatePrefix
    · refine ⟨privateCallFrame state instruction callee :: privatePrefix, ?_, ?_⟩
      · simp [privateCallFrame, hstack]
      · simpa [privateCallEntry, privateCallFrame] using
          publicProjection_privateCallEntry_restore_prefix machine state instruction callee
            (callArguments machine state instruction) privatePrefix

/-- Exact raw `stateWrite` preservation once the verifier-derived sink for its signed immediate is
    known non-Public. Negative offsets are failure-atomic no-ops, matching `step`. -/
theorem stateWriteStep_preserves_publicProjection
    (machine : SemanticProgram) (state : State) (instruction : Instruction)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hlive : state.halted = false) (hnotTrapped : state.trapped = false)
    (hop : instruction.op = .stateWrite)
    (hsink : let offset := (immediateOperands machine instruction).head?.getD 0
      0 ≤ offset → stateLabelAt machine (UInt32.ofNat offset.toNat) ≠ .pub) :
    publicProjection machine (step machine state).state = publicProjection machine state := by
  let offset := (immediateOperands machine instruction).head?.getD 0
  let value := (operandValues machine state instruction)[1]?.getD defaultValue
  let stored : Value := if offset < 0 then value else
    ⟨stateLabelAt machine (UInt32.ofNat offset.toNat), value.payload⟩
  by_cases hnegative : offset < 0
  · simp [step, hlive, hnotTrapped, hlookup, hop, offset, hnegative, publicProjection]
  · have hnonnegative : 0 ≤ offset := by omega
    have hprivate := hsink hnonnegative
    have hpreserved := actorStateWriteAtNat_preserves_publicProjection_of_nonpublic_sink
      machine state offset.toNat stored hprivate
    simpa [step, hlive, hnotTrapped, hlookup, hop, offset, value, stored, hnegative,
      publicProjection] using hpreserved

/-- Every non-call, non-return constructor at a non-Public occurrence preserves the raw Public
    projection. The two explicit coherence premises are exact decoder obligations: the per-site
    cursor label and the state-write immediate's global joined sink. -/
theorem nonoutput_noncall_nonpublic_step_preserves_publicProjection
    (machine : SemanticProgram) (state : State) (instruction : Instruction)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hlive : state.halted = false) (hnotTrapped : state.trapped = false)
    (hwell : instructionWellFormed machine instruction)
    (hsafe : LocalDestinationSafe instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (hnotCall : instruction.op ≠ .call) (hnotClosure : instruction.op ≠ .closure)
    (hnotOutput : instruction.op ≠ .output)
    (hsite : instruction.op = .ffi ∨ instruction.op = .actorBoundary →
      Semantic.externalSiteLabel machine instruction.id.toNat ≠ .pub)
    (hstate : instruction.op = .stateWrite →
      let offset := (immediateOperands machine instruction).head?.getD 0
      0 ≤ offset → stateLabelAt machine (UInt32.ofNat offset.toNat) ≠ .pub) :
    publicProjection machine (step machine state).state = publicProjection machine state := by
  have hisolated := nonpublic_has_no_public_destination hsafe hnonpublic
  generalize hop : instruction.op = operation at *
  cases operation
  case call => exact False.elim (hnotCall rfl)
  case closure => exact False.elim (hnotClosure rfl)
  case output => exact False.elim (hnotOutput rfl)
  case ffi =>
    have hadvance := advanceExternal_preserves_publicProjection_of_nonpublic_site
      machine state instruction.id (hsite (Or.inl rfl))
    have hwrite := writeDestination_preserves_publicProjection
      (advanceExternal state instruction.id) instruction (readExternal state instruction.id)
      hwell hisolated
    simpa [step, hlive, hnotTrapped, hlookup, hop, publicProjection] using
      hwrite.trans hadvance
  case actorBoundary =>
    let advanced := if instruction.destination == 0 then state
      else advanceExternal state instruction.id
    have hadvance : publicProjection machine advanced = publicProjection machine state := by
      by_cases hdestination : instruction.destination = 0
      · simp [advanced, hdestination]
      · simpa [advanced, hdestination] using
          advanceExternal_preserves_publicProjection_of_nonpublic_site
            machine state instruction.id (hsite (Or.inr rfl))
    have hwrite := writeDestination_preserves_publicProjection advanced instruction
      (if instruction.destination == 0 then instructionPayload machine state instruction
        else readExternal state instruction.id) hwell hisolated
    simpa [step, hlive, hnotTrapped, hlookup, hop, advanced, publicProjection] using
      hwrite.trans hadvance
  case stateRead =>
    have hwrite := writeDestination_preserves_publicProjection state instruction
      (if (immediateOperands machine instruction).head?.getD 0 < 0 then 0 else
        (readActorValue machine state (UInt32.ofNat
          ((immediateOperands machine instruction).head?.getD 0).toNat)).payload)
      hwell hisolated
    simpa [step, hlive, hnotTrapped, hlookup, hop, publicProjection] using hwrite
  case stateWrite =>
    exact stateWriteStep_preserves_publicProjection machine state instruction hlookup
      hlive hnotTrapped hop (hstate rfl)
  case effect => simp [step, hlive, hnotTrapped, hlookup, hop, publicProjection]
  case abortiveEffect => simp [step, hlive, hnotTrapped, hlookup, hop, publicProjection]
  all_goals
    have hordinary := ordinaryStep_preserves_publicProjection machine state instruction
      hwell hsafe hnonpublic
    simpa [step, hlive, hnotTrapped, hlookup, hop] using hordinary

/-- The same non-call/non-return constructor keeps the raw call stack byte-for-byte unchanged. -/
theorem nonoutput_noncall_step_preserves_stack
    (machine : SemanticProgram) (state : State) (instruction : Instruction)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hlive : state.halted = false) (hnotTrapped : state.trapped = false)
    (hnotCall : instruction.op ≠ .call) (hnotClosure : instruction.op ≠ .closure)
    (hnotOutput : instruction.op ≠ .output) :
    (step machine state).state.callStack = state.callStack := by
  generalize hop : instruction.op = operation at *
  cases operation
  case call => exact False.elim (hnotCall rfl)
  case closure => exact False.elim (hnotClosure rfl)
  case output => exact False.elim (hnotOutput rfl)
  case actorBoundary =>
    by_cases hdestination : instruction.destination = 0 <;>
      simp [step, hlive, hnotTrapped, hlookup, hop, hdestination]
  all_goals simp [step, hlive, hnotTrapped, hlookup, hop, ordinaryStep]

/-! ## Public result and state-source consequences -/

/-- A Public external result can only be read at a Public occurrence.  Per-site cursors therefore
    align exactly at every FFI/actor read capable of changing the Public projection. -/
theorem public_external_result_has_public_occurrence {program : V9.Program}
    {analysis : Analysis} {machine : SemanticProgram} {instruction : Instruction}
    (hsafe : PublicResultDependenciesSafe program analysis machine instruction)
    (hdestination : instruction.destination ≠ 0) (hresult : instruction.resultLabel = .pub)
    (hexternal : instruction.op = .ffi ∨ instruction.op = .actorBoundary) :
    instruction.blockLabel = .pub := by
  have hbody := hsafe hdestination hresult
  rcases hexternal with hop | hop
  · simpa [publicResultDependencyBodyOK, hop, OccurrenceKernel.externalSiteLabel,
      label_eqb_true_iff] using hbody
  · simpa [publicResultDependencyBodyOK, hop, OccurrenceKernel.externalSiteLabel,
      label_eqb_true_iff] using hbody

/-- A Public state read must resolve the exact function-owned state contract to Public. -/
theorem public_state_read_has_public_sink {program : V9.Program}
    {analysis : Analysis} {machine : SemanticProgram} {instruction : Instruction}
    (hsafe : PublicResultDependenciesSafe program analysis machine instruction)
    (hdestination : instruction.destination ≠ 0) (hresult : instruction.resultLabel = .pub)
    (hread : instruction.op = .stateRead) :
    stateSinkAt? program analysis instruction .stateRead 1 = some .pub := by
  have hbody := hsafe hdestination hresult
  simp only [publicResultDependencyBodyOK, hread] at hbody
  cases hsink : stateSinkAt? program analysis instruction .stateRead 1 with
  | none => simp [hsink] at hbody
  | some sink =>
      have hflow : sink.flowsTo .pub = true := by simpa [hsink, hresult] using hbody
      have hsinkPublic := (flowsTo_public_iff sink).mp hflow
      simp [hsinkPublic]

/-- Production acceptance rules out the apparent same-offset actor-state collision for a Public
    state-read result: the decoded semantic offset itself must have a globally Public declared
    label.  This is derived from the verifier seed graph, not from a runtime `Value.label`.

    The raw machine uses its decoded immediate slice to choose the runtime actor-state index.  A
    separate decoder-slice correspondence lemma is still needed to rewrite that runtime index to
    this semantic `offset`; this theorem intentionally does not assume or assert that bridge. -/
theorem verified_public_stateRead_declared_global_label_public
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hread : instruction.op = .stateRead)
    (hdestination : instruction.destination ≠ 0)
    (hresult : instruction.resultLabel = .pub) :
    ∃ offset,
      stateSinkAt? program analysis instruction .stateRead 1 = some .pub ∧
        semanticImmediateAt? program.base instruction.id 1 = some offset ∧
        semanticDeclaredStateLabelAt program.base offset = .pub := by
  have hresultSafe := returned_public_result_dependencies_safe hjudgment hanalysis hlookup
  have hsink := public_state_read_has_public_sink hresultSafe hdestination hresult hread
  obtain ⟨sinkSource, offset, hsinkSource, himmediate, _⟩ :=
    stateSinkAt_source hsink
  obtain ⟨source, hsourceMem, hsourceOp, hdecode, hid, _, hsourceDestination, _, _⟩ :=
    raw_instruction_source_shape hlookup
  have hdataflow := (OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).1
  have hcomponents := V9.OccurrenceDataflowSecurity.analyzed_components hdataflow
  have hcanonical := V9.OccurrenceDataflowSecurity.extracted_base_has_canonical_node_ids
    hcomponents.1
  have hsourceLookup := canonical_node_lookup_of_mem_id hcanonical hsourceMem hid
  have hsourcesEq : sinkSource = source :=
    Option.some.inj (hsinkSource.symm.trans hsourceLookup)
  subst sinkSource
  have himmediateInstruction :
      semanticImmediateAt? program.base instruction.id 1 = some offset := by
    simpa [hid] using himmediate
  have hcell : semanticValueCell? analysis.dataflow.semanticIndex source.origin source.required =
      some instruction.destination := by
    unfold semanticResultCellFrom at hsourceDestination
    by_cases hzero : source.required = 0
    · simp [hzero] at hsourceDestination
      exact False.elim (hdestination hsourceDestination.symm)
    · cases hvalue : semanticValueCell? analysis.dataflow.semanticIndex source.origin
          source.required with
      | none =>
          simp [hzero, hvalue] at hsourceDestination
          exact False.elim (hdestination hsourceDestination.symm)
      | some cell =>
          have hcellEq : cell = instruction.destination := by
            simpa [hzero, hvalue] using hsourceDestination
          simpa [hcellEq] using hvalue
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hwell := instruction_well_formed_of_raw_static_safe hstatic hlookup
  have hrawBound : instruction.destination.toNat <
      (rawSemanticProgram program analysis).valueLabels.size :=
    hwell.2.1.resolve_left (by simpa using hdestination)
  have hbaseToRaw := analyzed_labels_flow_to_raw_value_labels program analysis
  have hseedSize : (semanticSeedLabels program.base).size =
      semanticTaintCellCount program.base := by
    simp [semanticSeedLabels, SemanticDataflow.semanticSeedLabelsWithIndex_size]
  have hsourceFlows := V9.OccurrenceDataflowSecurity.analyzed_labels_preserve_source_seeds
    hdataflow
  have hlabelSize : analysis.dataflow.labels.size = semanticTaintCellCount program.base :=
    hsourceFlows.1.symm.trans hseedSize
  have hbound : instruction.destination.toNat < semanticTaintCellCount program.base := by
    have : instruction.destination.toNat < analysis.dataflow.labels.size := by
      simpa [hbaseToRaw.1] using hrawBound
    simpa [hlabelSize] using this
  have hindex : analysis.dataflow.semanticIndex = buildSemanticIndex program.base :=
    hcomponents.2.1
  rw [hindex] at hcell
  have hdecodeRead : decodeSemanticInstrOp? source.aux = some .stateRead := by
    simpa [hread] using hdecode
  have hseed := stateRead_seed_flows_to_semantic_seed_labels program.base
    (buildSemanticIndex program.base) hsourceMem hsourceOp hdecodeRead himmediate hcell hbound
  have hseedToLabels := hsourceFlows.2 instruction.destination
    (by simpa [hseedSize] using hbound)
  have hglobalToResult := flowsTo_trans hseed (by
    simpa [semanticSeedLabels] using hseedToLabels)
  have hlabelPublic : labelAt analysis.dataflow.labels instruction.destination = .pub := by
    have hrawPublic := hwell.2.2.1.symm.trans hresult
    exact (flowsTo_public_iff _).mp (by
      have hflow := hbaseToRaw.2 instruction.destination
        (by simpa [hlabelSize] using hbound)
      have hupperPublic : labelAt
          (occurrenceValueLabels analysis
            (OccurrenceDataflow.semanticProgram program analysis.dataflow))
          instruction.destination = .pub := by
        simpa [rawSemanticProgram] using hrawPublic
      simpa [hupperPublic] using hflow)
  have hglobalPublic : semanticDeclaredStateLabelAt program.base offset = .pub :=
    (flowsTo_public_iff _).mp (hlabelPublic ▸ hglobalToResult)
  exact ⟨offset, hsink, himmediateInstruction, hglobalPublic⟩

/-- If an exact function-owned state sink is Public, the accepted state-write payload is read from
    a concrete Public SSA cell.  This is stronger than merely checking the instruction pc. -/
theorem public_state_write_has_public_source {program : V9.Program}
    {analysis : Analysis} {machine : SemanticProgram} {instruction : Instruction}
    (hsafe : PublicStateWriteSourceSafe program analysis machine instruction)
    (hwrite : instruction.op = .stateWrite)
    (hsink : stateSinkAt? program analysis instruction .stateWrite 2 = some .pub) :
    ∃ cell,
      (valueOperandCells machine instruction)[1]? = some cell ∧
        labelAt machine.valueLabels cell = .pub := by
  have hbody := hsafe hwrite
  unfold publicStateWriteSourceBodyOK at hbody
  rw [hsink] at hbody
  cases hcell : (valueOperandCells machine instruction)[1]? with
  | none => simp [hcell] at hbody
  | some cell =>
      refine ⟨cell, rfl, ?_⟩
      simpa [hcell, label_eqb_true_iff] using hbody

/-- Public actor boundaries are necessarily reached under a Public raw occurrence.  Unlike a
    payload test, this preserves the observable fact, site, and ordering of the boundary. -/
theorem actor_site_has_public_occurrence {program : V9.Program} {analysis : Analysis}
    {instruction : Instruction} {pc position : Nat} {contract : ActorContract}
    (hsafe : SiteKindOccurrenceSafe program analysis instruction pc
      (.actor position contract)) :
    instruction.blockLabel = .pub :=
  (flowsTo_public_iff instruction.blockLabel).mp hsafe

/-- A declared-Public FFI occurrence is reached under a Public raw pc. -/
theorem public_ffi_site_has_public_occurrence {program : V9.Program} {analysis : Analysis}
    {instruction : Instruction} {pc position : Nat} {contract : FfiContract}
    (hsafe : SiteKindOccurrenceSafe program analysis instruction pc (.ffi position contract))
    (hcontract : contract.occurrence = .pub) :
    instruction.blockLabel = .pub := by
  exact (flowsTo_public_iff instruction.blockLabel).mp (hcontract ▸ hsafe.2)

/-! ## Constructor-local Public boundary observations -/

@[simp] private theorem publicBoundaryTrace_eventsForValues_of_unobserved_kind
    (kind : EventKind) (site : UInt32) (values : List Value)
    (houtput : kind ≠ .output) (hboundary : kind ≠ .boundary) :
    publicBoundaryTrace (eventsForValues kind site values) = [] := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [eventsForValues, publicBoundaryTrace, publicBoundaryObservation?, houtput,
        hboundary, EventKind.eqb]

@[simp] private theorem publicBoundaryTrace_eventsForObserved_of_unobserved_kind
    (kind : EventKind) (site : UInt32) (values : List Value)
    (houtput : kind ≠ .output) (hboundary : kind ≠ .boundary) :
    publicBoundaryTrace (eventsForObserved kind site values) = [] := by
  by_cases hempty : values.isEmpty
  · simp [eventsForObserved, hempty, publicBoundaryTrace, publicBoundaryObservation?, houtput,
      hboundary, EventKind.eqb]
  · simp [eventsForObserved, hempty, houtput, hboundary]

@[simp] private theorem publicBoundaryTrace_eventsForValuesUnderPc_of_nonpublic
    (kind : EventKind) (site : UInt32) (pc : Label) (values : List Value)
    (hpc : pc ≠ .pub) :
    publicBoundaryTrace (eventsForValuesUnderPc kind site pc values) = [] := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [eventsForValuesUnderPc, publicBoundaryTrace, publicBoundaryObservation?, hpc,
        EventKind.eqb, Label.eqb]

/-- Constructor-complete event classification for a private raw instruction.  Only actor and
    top-level output constructors emit boundary observations, and both use the raised block label. -/
theorem nonpublic_instruction_has_no_public_boundary_observation
    (machine : SemanticProgram) (state : State) (instruction : Instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub) :
    publicBoundaryTrace (instructionEvents machine state instruction) = [] := by
  generalize hop : instruction.op = operation at *
  cases operation <;>
    simp [instructionEvents, hop, hnonpublic] <;>
    simp [publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb, Label.eqb, hnonpublic]

/-- The actual raw step inherits the constructor-local boundary silence result.  Calls/closures
    can only emit a trap here; internal returns emit no boundary; a top-level output delegates to
    `instructionEvents`. -/
theorem nonpublic_step_has_no_public_boundary_observation
    (machine : SemanticProgram) (state : State) (instruction : Instruction)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub) :
    publicBoundaryTrace (step machine state).events = [] := by
  have hinstruction := nonpublic_instruction_has_no_public_boundary_observation
    machine state instruction hnonpublic
  unfold step
  by_cases hdone : state.halted || state.trapped
  · simp [hdone, publicBoundaryTrace]
  · rw [if_neg hdone, hlookup]
    generalize hop : instruction.op = operation at *
    cases operation
    all_goals simp only [hop]
    case call =>
      unfold callStep
      split
      · simp [publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]
      · dsimp only
        split
        · simp [publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]
        · rfl
    case closure =>
      unfold callStep
      split
      · simp [publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]
      · dsimp only
        split
        · simp [publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]
        · rfl
    case output =>
      cases hstack : state.callStack with
      | nil => simpa [hstack, hop] using hinstruction
      | cons frame rest =>
          simp only
          split <;> simp [publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]
    case ffi => simpa [hop] using hinstruction
    case actorBoundary => simpa [hop] using hinstruction
    case effect => simpa [hop] using hinstruction
    case abortiveEffect => simpa [hop] using hinstruction
    case stateRead => rfl
    case stateWrite => simpa [hop] using hinstruction
    all_goals simpa [ordinaryStep, hop] using hinstruction

/-- Production-facing silent-step API. For every non-call/non-return instruction accepted by the
    v9 occurrence verifier, the actual raw step keeps the private-prefix stack decomposition,
    preserves its complete prefix-restored Public projection, and emits no Public output/boundary
    observation. The external-site fact is derived from canonical raw instruction identifiers;
    the explicit state coherence argument isolates the remaining state-immediate/index bridge and
    is not a supplied taint label or policy verdict. -/
theorem verified_nonoutput_noncall_nonpublic_step_preserves_prefix
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {root : UInt32} {state : State} {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (hnotCall : instruction.op ≠ .call) (hnotClosure : instruction.op ≠ .closure)
    (hnotOutput : instruction.op ≠ .output)
    (privatePrefix spine : List CallFrame)
    (hstack : state.callStack = privatePrefix ++ spine)
    (hstate : instruction.op = .stateWrite →
      let offset := (immediateOperands (rawSemanticProgram program analysis)
        instruction).head?.getD 0
      0 ≤ offset → stateLabelAt (rawSemanticProgram program analysis)
        (UInt32.ofNat offset.toNat) ≠ .pub) :
    let next := step (rawSemanticProgram program analysis) state
    next.state.callStack = privatePrefix ++ spine ∧
      publicProjection (rawSemanticProgram program analysis)
          (restoreFrameStack next.state privatePrefix) =
        publicProjection (rawSemanticProgram program analysis)
          (restoreFrameStack state privatePrefix) ∧
      publicBoundaryTrace next.events = [] := by
  let machine := rawSemanticProgram program analysis
  have hpolicy := returned_instruction_occurrence_safe hjudgment hanalysis hlookup
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hwell := instruction_well_formed_of_raw_static_safe hstatic hlookup
  have hsite : instruction.op = .ffi ∨ instruction.op = .actorBoundary →
      Semantic.externalSiteLabel machine instruction.id.toNat ≠ .pub := by
    intro _ hpublic
    exact hnonpublic ((raw_externalSiteLabel_eq_blockLabel hanalysis hlookup).symm.trans hpublic)
  have hprojection :=
    nonoutput_noncall_nonpublic_step_preserves_publicProjection machine state instruction
      hlookup hactive.notHalted hactive.notTrapped hwell hpolicy.1 hnonpublic hnotCall
      hnotClosure hnotOutput hsite hstate
  have hnextStack := nonoutput_noncall_step_preserves_stack machine state instruction
    hlookup hactive.notHalted hactive.notTrapped hnotCall hnotClosure hnotOutput
  dsimp only
  refine ⟨hnextStack.trans hstack, ?_,
    nonpublic_step_has_no_public_boundary_observation machine state instruction hlookup
      hnonpublic⟩
  exact restoreFrameStack_preserves_publicProjection_eq machine hprojection privatePrefix

/-- Accepted non-Public call and closure steps preserve the prefix-restored projection whether
    they trap or enter the callee. Successful entry grows the proof-only private prefix by the
    exact frame constructed by `callStep`; no supplied activation certificate is substituted. -/
theorem verified_nonpublic_call_step_preserves_prefix
    {program : V9.Program} (_hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (_hanalysis : analyze? program = some analysis)
    {root : UInt32} {state : State} {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : instruction.blockLabel ≠ .pub)
    (hoperation : instruction.op = .call ∨ instruction.op = .closure)
    (privatePrefix spine : List CallFrame)
    (hstack : state.callStack = privatePrefix ++ spine) :
    let next := step (rawSemanticProgram program analysis) state
    ∃ nextPrefix,
      next.state.callStack = nextPrefix ++ spine ∧
        publicProjection (rawSemanticProgram program analysis)
            (restoreFrameStack next.state nextPrefix) =
          publicProjection (rawSemanticProgram program analysis)
            (restoreFrameStack state privatePrefix) ∧
        publicBoundaryTrace next.events = [] := by
  let machine := rawSemanticProgram program analysis
  have hcall := callStep_preserves_prefix_restored_publicProjection machine state
    instruction privatePrefix spine hstack
  obtain ⟨nextPrefix, hnextStack, hprojection⟩ := hcall
  have hsilence := nonpublic_step_has_no_public_boundary_observation machine state instruction
    hlookup hnonpublic
  dsimp only
  refine ⟨nextPrefix, ?_, ?_, hsilence⟩
  · rcases hoperation with hop | hop <;>
      simpa [step, hactive.notHalted, hactive.notTrapped, hlookup, hop] using hnextStack
  · rcases hoperation with hop | hop <;>
      simpa [step, hactive.notHalted, hactive.notTrapped, hlookup, hop] using hprojection

open OccurrenceKernel OccurrenceKernelSecurity

private theorem op_eq_semOperand_of_beq {operation : Op}
    (h : (operation == .semOperand) = true) : operation = .semOperand := by
  cases operation <;> first | rfl | cases h

def DecodedOperandSourceShape (program : Combined.Program) (index : SemanticIndex)
    (operand : OperandRecord) : Prop :=
  ∃ source owner,
    source ∈ program.nodes.toList ∧ source.op = .semOperand ∧
      program.nodes[source.origin.toNat - 1]? = some owner ∧
      operand.owner = source.origin ∧ operand.position = source.actual ∧
      operand.value = (if source.flags == 0 then
        (semanticValueCell? index owner.origin source.required).getD 0 else source.required) ∧
      operand.high = source.ceiling ∧ operand.kind = source.flags

set_option linter.unusedSimpArgs false in
private theorem decodeSemanticNode_operand_shape
    (program : Combined.Program) (index : SemanticIndex) (labels : Array Label)
    (entries : Array (Option Nat)) (state : SemanticDecodeState) (node : Node)
    (hnodeMem : node ∈ program.nodes)
    (hprior : ∀ operand ∈ state.operands, DecodedOperandSourceShape program index operand) :
    ∀ operand ∈ (decodeSemanticNode program index labels entries state node).operands,
      DecodedOperandSourceShape program index operand := by
  intro operand hmem
  cases hop : node.op
  case semOperand =>
    cases howner : program.nodes[node.origin.toNat - 1]? with
    | none =>
        apply hprior operand
        simpa [decodeSemanticNode, hop, howner] using hmem
    | some owner =>
        simp only [decodeSemanticNode, hop, howner, Array.mem_push] at hmem
        rcases hmem with hprevious | hnew
        · exact hprior operand hprevious
        · subst operand
          exact ⟨node, owner, Array.mem_toList_iff.mpr hnodeMem, hop, howner,
            rfl, rfl, rfl, rfl, rfl⟩
  case semInstruction =>
    cases hdecode : decodeSemanticInstrOp? node.aux <;>
      apply hprior operand <;>
      simpa [decodeSemanticNode, hop, hdecode] using hmem
  case semLabelContract =>
    by_cases haux : node.aux = 3 <;>
      apply hprior operand <;>
      simpa [decodeSemanticNode, hop, haux] using hmem
  all_goals
    apply hprior operand
    simpa [decodeSemanticNode, hop] using hmem

private theorem decodeSemanticFold_operand_shape
    (program : Combined.Program) (index : SemanticIndex) (labels : Array Label)
    (entries : Array (Option Nat)) (nodes : List Node) (state : SemanticDecodeState)
    (hnodes : ∀ node ∈ nodes, node ∈ program.nodes)
    (hprior : ∀ operand ∈ state.operands, DecodedOperandSourceShape program index operand) :
    ∀ operand ∈ (nodes.foldl (decodeSemanticNode program index labels entries) state).operands,
      DecodedOperandSourceShape program index operand := by
  induction nodes generalizing state with
  | nil => simpa using hprior
  | cons node rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro candidate hcandidate
        exact hnodes candidate (List.mem_cons_of_mem node hcandidate)
      · exact decodeSemanticNode_operand_shape program index labels entries state node
          (hnodes node (by simp)) hprior

theorem semanticProgramOfWith_operand_source_shape
    (program : Combined.Program) (index : SemanticIndex) (labels : Array Label)
    {operand : OperandRecord}
    (hmem : operand ∈ (semanticProgramOfWith program index labels).operands) :
    DecodedOperandSourceShape program index operand := by
  let entries := semanticBlockEntries program index
  let initial : SemanticDecodeState :=
    { policySelections := Array.replicate (program.nodes.size + 1) [] }
  let decoded := program.nodes.foldl
    (decodeSemanticNode program index labels entries) initial
  have hshape := decodeSemanticFold_operand_shape program index labels entries
    program.nodes.toList initial (by simp) (by simp [initial])
  apply hshape operand
  simpa [semanticProgramOfWith, entries, initial, decoded] using hmem

theorem raw_operand_source_shape
    {program : V9.Program} {analysis : Analysis} {operand : OperandRecord}
    (hmem : operand ∈ (rawSemanticProgram program analysis).operands) :
    DecodedOperandSourceShape program.base analysis.dataflow.semanticIndex operand := by
  apply semanticProgramOfWith_operand_source_shape program.base
    analysis.dataflow.semanticIndex analysis.dataflow.labels
  simpa [rawSemanticProgram, OccurrenceDataflow.semanticProgram] using hmem

private theorem firstSemanticViolationList_none_sound
    (program : Combined.Program) (index : SemanticIndex) {nodes : List Node}
    (h : firstSemanticViolationList program index nodes = none) :
    ∀ node ∈ nodes, semanticRecordOK program index node = true := by
  induction nodes with
  | nil => simp
  | cons head tail ih =>
      by_cases hok : semanticRecordOK program index head = true
      · have htail : firstSemanticViolationList program index tail = none := by
          simpa [firstSemanticViolationList, hok] using h
        intro node hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hok
        · exact ih htail node hmem
      · simp [firstSemanticViolationList, hok] at h

private theorem semantic_record_ok_of_verified
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {node : Node} (hmem : node ∈ program.base.nodes.toList)
    (hsemanticNode : node.op.isSemantic = true) :
    semanticRecordOK program.base (buildSemanticIndex program.base) node = true := by
  obtain ⟨_, hraw, _, _, _, _, _, _⟩ := hjudgment
  have hverify := hraw
  have hsemantic : firstSemanticViolation program.base = none := by
    unfold verifyProgram at hverify
    cases hs : firstSemanticViolation program.base with
    | some violation => simp [hs] at hverify
    | none => rfl
  unfold firstSemanticViolation firstSemanticViolationWithIndex at hsemantic
  split at hsemantic
  · rename_i hlegacy
    simp only [Bool.and_eq_true] at hlegacy
    have hrow := List.all_eq_true.mp hlegacy.2 node hmem
    simp [hsemanticNode] at hrow
  · split at hsemantic
    · cases hsemantic
    · split at hsemantic
      · cases hsemantic
      · cases hmanifest : semanticProgramNode? program.base with
        | none => simp [hmanifest] at hsemantic
        | some manifest =>
            have hlist : firstSemanticViolationList program.base
                (buildSemanticIndex program.base) program.base.nodes.toList = none := by
              simpa [hmanifest] using hsemantic
            exact firstSemanticViolationList_none_sound program.base
              (buildSemanticIndex program.base) hlist node hmem

private theorem semantic_operand_record_ok_of_verified
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {node : Node} (hmem : node ∈ program.base.nodes.toList)
    (hop : node.op = .semOperand) :
    semanticOperandRecordOK program.base (buildSemanticIndex program.base) node = true := by
  have hsemantic : node.op.isSemantic = true := by rw [hop]; decide
  have hrecord := semantic_record_ok_of_verified hjudgment hmem hsemantic
  simpa [semanticRecordOK, hop] using hrecord

theorem instructionOperandAt_exists_of_wellFormed
    {machine : SemanticProgram} {instruction : Instruction} {position : Nat}
    (hwell : instructionWellFormed machine instruction)
    (hposition : position < instruction.operandCount.toNat) :
    ∃ operand, instructionOperandAt? machine instruction position = some operand := by
  let index := instruction.firstOperand.toNat + position
  have hbound : index < machine.operands.size := by
    have hslice := hwell.2.2.2.1
    unfold operandSliceWellFormed at hslice
    omega
  let operand := machine.operands[index]
  have hidentity := hwell.2.2.2.1.2 position hposition
  have howner : operand.owner = instruction.id := by
    simpa [operand, index, Array.getD, hbound] using hidentity.1
  have hposition' : operand.position.toNat = position := by
    simpa [operand, index, Array.getD, hbound] using hidentity.2.1
  refine ⟨operand, ?_⟩
  simp [instructionOperandAt?, hposition, index, operand, hbound, howner, hposition']

private theorem instructionOperandAt_identity
    {machine : SemanticProgram} {instruction : Instruction} {position : Nat}
    {operand : OperandRecord}
    (h : instructionOperandAt? machine instruction position = some operand) :
    operand.owner = instruction.id ∧ operand.position.toNat = position := by
  unfold instructionOperandAt? at h
  by_cases hposition : position < instruction.operandCount.toNat
  · simp only [hposition, bind] at h
    cases hget : machine.operands[instruction.firstOperand.toNat + position]? with
    | none => simp [hget] at h
    | some found =>
        have hparts : (found.owner = instruction.id ∧ found.position.toNat = position) ∧
            found = operand := by
          simpa [hget] using h
        rw [← hparts.2]
        exact hparts.1
  · simp [hposition] at h

private theorem semanticOperandRecordOK_contiguous
    {program : Combined.Program} {index : SemanticIndex} {source owner : Node}
    (howner : program.nodes[source.origin.toNat - 1]? = some owner)
    (hrecord : semanticOperandRecordOK program index source = true) :
    source.nodeId.toNat - 1 = source.origin.toNat + source.actual.toNat := by
  unfold semanticOperandRecordOK at hrecord
  rw [howner] at hrecord
  simp only [Bool.and_eq_true, beq_iff_eq] at hrecord
  omega

private theorem semanticImmediateAt_source
    {program : Combined.Program} {owner offset : UInt32} {position : Nat}
    (h : semanticImmediateAt? program owner position = some offset) :
    ∃ operand,
      program.nodes[owner.toNat + position]? = some operand ∧
        operand.op = .semOperand ∧ operand.origin = owner ∧
        operand.actual.toNat = position ∧ operand.flags = 3 ∧
        operand.ceiling = 0 ∧ operand.required = offset := by
  unfold semanticImmediateAt? at h
  cases hoperand : semanticOperandAt? program owner position with
  | none => simp [hoperand] at h
  | some operand =>
      simp only [hoperand] at h
      by_cases hshape : operand.flags == 3 && operand.ceiling == 0
      · simp only [hshape, ↓reduceIte, Option.some.injEq] at h
        unfold semanticOperandAt? at hoperand
        cases hget : program.nodes[owner.toNat + position]? with
        | none => simp [hget] at hoperand
        | some found =>
            simp only [hget] at hoperand
            by_cases hidentity :
                found.op == .semOperand && found.origin == owner &&
                  found.actual.toNat == position
            · simp only [hidentity, ↓reduceIte, Option.some.injEq] at hoperand
              subst found
              simp only [Bool.and_eq_true, beq_iff_eq] at hshape
              have hop : operand.op = .semOperand := by
                have hopB : (operand.op == .semOperand) = true := by
                  have := hidentity
                  simp only [Bool.and_eq_true] at this
                  exact this.1.1
                exact op_eq_semOperand_of_beq hopB
              have hparts := hidentity
              simp only [Bool.and_eq_true] at hparts
              exact ⟨operand, by simpa using hget, hop, beq_iff_eq.mp hparts.1.2,
                beq_iff_eq.mp hparts.2, hshape.1, hshape.2, h⟩
            · simp [hidentity] at hoperand
      · simp [hshape] at h

theorem verified_semanticImmediate_position_bounded
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} {pc position : Nat} {instruction : Instruction} {offset : UInt32}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (himmediate : semanticImmediateAt? program.base instruction.id position = some offset) :
    position < instruction.operandCount.toNat := by
  obtain ⟨semanticOperand, hoperandLookup, hoperandOp, hoperandOwner, hoperandPosition,
      _, _, _⟩ := semanticImmediateAt_source himmediate
  have hoperandMem : semanticOperand ∈ program.base.nodes.toList := by
    exact Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr
      ⟨instruction.id.toNat + position, hoperandLookup⟩)
  have hrecord := semantic_operand_record_ok_of_verified hjudgment hoperandMem hoperandOp
  obtain ⟨source, hsourceMem, _, _, hsourceId, _, _, hsourceCount, _⟩ :=
    raw_instruction_source_shape hlookup
  have hdataflow : ∃ accepted, analyze? program = some accepted := by
    obtain ⟨accepted, _, haccepted, _, _, _, _, _⟩ := hjudgment
    exact ⟨accepted, haccepted⟩
  have hcanonical : CanonicalNodeIds program.base := by
    obtain ⟨accepted, haccepted⟩ := hdataflow
    have hflow := (OccurrenceDataflowInvocationSecurity.analyzed_components haccepted).1
    have hextract := (V9.OccurrenceDataflowSecurity.analyzed_components hflow).1
    exact V9.OccurrenceDataflowSecurity.extracted_base_has_canonical_node_ids hextract
  have hsourceLookup := canonical_node_lookup_of_mem_id hcanonical hsourceMem hsourceId
  have hoperandBound : instruction.id.toNat + position < program.base.nodes.size :=
    (Array.getElem?_eq_some_iff.mp hoperandLookup).1
  have hoperandGet : program.base.nodes[instruction.id.toNat + position] = semanticOperand :=
    (Array.getElem?_eq_some_iff.mp hoperandLookup).2
  have hoperandGetList :
      program.base.nodes.toList[instruction.id.toNat + position] = semanticOperand := by
    simpa using hoperandGet
  have hcanonicalOperand := hcanonical (instruction.id.toNat + position) hoperandBound
  rw [hoperandGetList] at hcanonicalOperand
  unfold semanticOperandRecordOK at hrecord
  rw [hoperandOwner, hsourceLookup] at hrecord
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrecord
  rw [← hsourceCount]
  omega

theorem verified_semanticImmediate_runtime_operand
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc position : Nat} {instruction : Instruction} {offset : UInt32}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (himmediate : semanticImmediateAt? program.base instruction.id position = some offset) :
    ∃ operand,
      instructionOperandAt? (rawSemanticProgram program analysis) instruction position =
          some operand ∧
        operand.kind = 3 ∧ operand.value = offset ∧ operand.high = 0 := by
  let machine := rawSemanticProgram program analysis
  have hposition := verified_semanticImmediate_position_bounded hjudgment hlookup himmediate
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hwell := instruction_well_formed_of_raw_static_safe hstatic hlookup
  obtain ⟨operand, hoperand⟩ := instructionOperandAt_exists_of_wellFormed hwell hposition
  have hidentity := instructionOperandAt_identity hoperand
  have hoperandMem : operand ∈ machine.operands := by
    change instructionOperandAt? machine instruction position = some operand at hoperand
    cases hget : machine.operands[instruction.firstOperand.toNat + position]? with
    | none => simp [instructionOperandAt?, hposition, hget] at hoperand
    | some found =>
        have hfoundMem := Array.mem_iff_getElem?.mpr
          ⟨instruction.firstOperand.toNat + position, hget⟩
        have hparts : (found.owner = instruction.id ∧ found.position.toNat = position) ∧
            found = operand := by
          simpa [instructionOperandAt?, hposition, hget] using hoperand
        rw [← hparts.2]
        exact hfoundMem
  obtain ⟨source, owner, hsourceMem, hsourceOp, howner, hoperandOwner,
      hoperandPosition, hoperandValue, hoperandHigh, hoperandKind⟩ :=
    raw_operand_source_shape hoperandMem
  have hrecord := semantic_operand_record_ok_of_verified hjudgment hsourceMem hsourceOp
  have hcontiguous := semanticOperandRecordOK_contiguous howner hrecord
  have hsourceOwner : source.origin = instruction.id := by
    exact hoperandOwner.symm.trans hidentity.1
  have hsourcePosition : source.actual.toNat = position := by
    exact (congrArg UInt32.toNat hoperandPosition).symm.trans hidentity.2
  have hdataflow := (OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).1
  have hextract := (V9.OccurrenceDataflowSecurity.analyzed_components hdataflow).1
  have hcanonical := V9.OccurrenceDataflowSecurity.extracted_base_has_canonical_node_ids hextract
  have hsourceLookup : program.base.nodes[source.nodeId.toNat - 1]? = some source := by
    obtain ⟨sourceIndex, hsourceBound, hsourceGet⟩ :=
      Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hsourceMem)
    have hcanonicalAt := hcanonical sourceIndex hsourceBound
    have hsourceGetList : program.base.nodes.toList[sourceIndex] = source := by
      simpa using hsourceGet
    have hsourceIndexEq : source.nodeId.toNat - 1 = sourceIndex := by
      rw [hsourceGetList] at hcanonicalAt
      omega
    subst sourceIndex
    exact Array.getElem?_eq_some_iff.mpr ⟨hsourceBound, hsourceGet⟩
  have hsemanticOperand : semanticOperandAt? program.base instruction.id position = some source := by
    unfold semanticOperandAt?
    have hindex : instruction.id.toNat + position = source.nodeId.toNat - 1 := by
      rw [hcontiguous, hsourceOwner, hsourcePosition]
    rw [hindex, hsourceLookup]
    have hopB : (source.op == .semOperand) = true := by
      rw [hsourceOp]
      decide
    have hownerB : (source.origin == instruction.id) = true := beq_iff_eq.mpr hsourceOwner
    have hpositionB : (source.actual.toNat == position) = true :=
      beq_iff_eq.mpr hsourcePosition
    simp [hopB, hownerB, hpositionB]
  unfold semanticImmediateAt? at himmediate
  rw [hsemanticOperand] at himmediate
  by_cases himmediateShape : source.flags == 3 && source.ceiling == 0
  · simp only [himmediateShape, ↓reduceIte, Option.some.injEq] at himmediate
    simp only [Bool.and_eq_true] at himmediateShape
    have hflags : source.flags = 3 := by
      exact beq_iff_eq.mp himmediateShape.1
    have hhigh : source.ceiling = 0 := by
      exact beq_iff_eq.mp himmediateShape.2
    have hvalue : operand.value = offset := by
      rw [hoperandValue, hflags]
      simp [himmediate]
    exact ⟨operand, hoperand, hoperandKind.trans hflags, hvalue,
      hoperandHigh.trans hhigh⟩
  · simp [himmediateShape] at himmediate

private theorem runtime_immediate_prefix_nil
    (machine : SemanticProgram) (instruction : Instruction) (firstImmediate : Nat)
    (hbefore : ∀ position, position < firstImmediate →
      ∃ operand, instructionOperandAt? machine instruction position = some operand ∧
        operand.kind ≠ 3) :
    ((List.range firstImmediate).filterMap
        (instructionOperandAt? machine instruction)).filterMap
          (fun operand => if operand.kind == 3 then some (operandImmediate operand) else none) =
      [] := by
  have go : ∀ positions : List Nat,
      (∀ position ∈ positions, position < firstImmediate) →
      (positions.filterMap (instructionOperandAt? machine instruction)).filterMap
          (fun operand => if operand.kind == 3 then some (operandImmediate operand) else none) =
        [] := by
    intro positions hpositions
    induction positions with
    | nil => rfl
    | cons position rest ih =>
        obtain ⟨operand, hoperand, hkind⟩ :=
          hbefore position (hpositions position (by simp))
        have hkindB : (operand.kind == 3) = false := by
          exact beq_eq_false_iff_ne.mpr hkind
        simp only [List.filterMap_cons, hoperand, hkindB, ↓reduceIte]
        apply ih
        intro next hnext
        exact hpositions next (List.mem_cons_of_mem position hnext)
  apply go (List.range firstImmediate)
  intro position hposition
  exact List.mem_range.mp hposition

theorem immediateOperands_head_of_first_runtime_immediate
    (machine : SemanticProgram) (instruction : Instruction) {firstImmediate : Nat}
    {operand : OperandRecord}
    (hbound : firstImmediate < instruction.operandCount.toNat)
    (hoperand : instructionOperandAt? machine instruction firstImmediate = some operand)
    (hkind : operand.kind = 3)
    (hbefore : ∀ position, position < firstImmediate →
      ∃ prior, instructionOperandAt? machine instruction position = some prior ∧
        prior.kind ≠ 3) :
    (immediateOperands machine instruction).head? = some (operandImmediate operand) := by
  let count := instruction.operandCount.toNat
  have hle : firstImmediate ≤ count := Nat.le_of_lt hbound
  have hdecomposition : List.range count =
      List.range firstImmediate ++ List.range' firstImmediate (count - firstImmediate) := by
    rw [List.range_eq_range', List.range_eq_range']
    have happend := List.range'_append
      (s := 0) (m := firstImmediate) (n := count - firstImmediate) (step := 1)
    simpa [Nat.add_sub_of_le hle] using happend.symm
  have hprefix := runtime_immediate_prefix_nil machine instruction firstImmediate hbefore
  unfold immediateOperands instructionOperands
  rw [hdecomposition, List.filterMap_append, List.filterMap_append, hprefix]
  simp only [List.nil_append]
  cases hremaining : count - firstImmediate with
  | zero => omega
  | succ remaining =>
      simp [List.range', hoperand, hkind]

theorem verified_state_instruction_semantic_value_prefix
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hstate : instruction.op = .stateRead ∨ instruction.op = .stateWrite) :
    ∀ position, position < (if instruction.op = .stateRead then 1 else 2) →
      semanticOperandKindAt? program.base instruction.id position = some 0 := by
  obtain ⟨source, hsourceMem, hsourceOp, hdecode, hsourceId, _, _, _, _⟩ :=
    raw_instruction_source_shape hlookup
  have hsemantic : source.op.isSemantic = true := by rw [hsourceOp]; decide
  have hrecord := semantic_record_ok_of_verified hjudgment hsourceMem hsemantic
  unfold semanticRecordOK at hrecord
  rw [hsourceOp] at hrecord
  unfold semanticInstructionRecordOK at hrecord
  cases hfunction : indexedSemanticFunctionNode? (buildSemanticIndex program.base) source.origin with
  | none => simp [hdecode, hfunction] at hrecord
  | some function =>
      simp only [hdecode, hfunction, Bool.and_eq_true] at hrecord
      have hshape : semanticInstructionShapeOK program.base source instruction.op = true := by
        aesop
      have horder : semanticOperandOrderOK program.base source instruction.op = true := by
        aesop
      rcases hstate with hread | hwrite
      · rw [hread] at hshape horder
        have hvalues : semanticOperandKindCount program.base source.nodeId 0 = 1 := by
          simp [semanticInstructionShapeOK] at hshape
          omega
        unfold semanticOperandOrderOK at horder
        simp only at horder
        rw [hvalues] at horder
        unfold semanticOperandKindRun at horder
        simp only [Bool.and_eq_true, beq_iff_eq] at horder
        intro position hposition
        have hposition' : position < 1 := by
          simpa [hread] using hposition
        have hzero : position = 0 := by omega
        subst position
        simpa [hsourceId] using horder.1.1
      · rw [hwrite] at hshape horder
        have hvalues : semanticOperandKindCount program.base source.nodeId 0 = 2 := by
          simp [semanticInstructionShapeOK] at hshape
          omega
        unfold semanticOperandOrderOK at horder
        simp only at horder
        rw [hvalues] at horder
        unfold semanticOperandKindRun at horder
        simp only [Bool.and_eq_true, beq_iff_eq] at horder
        intro position hposition
        have hposition' : position < 2 := by
          simpa [hwrite] using hposition
        have hcases : position = 0 ∨ position = 1 := by omega
        rcases hcases with rfl | rfl
        · simpa [hsourceId] using horder.1.1
        · have htail := horder.1.2
          unfold semanticOperandKindRun at htail
          simp only [Bool.and_eq_true, beq_iff_eq] at htail
          simpa [hsourceId] using htail.1

theorem verified_semanticOperand_runtime_kind
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc position : Nat} {instruction : Instruction} {kind : UInt8}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hposition : position < instruction.operandCount.toNat)
    (hkind : semanticOperandKindAt? program.base instruction.id position = some kind) :
    ∃ operand,
      instructionOperandAt? (rawSemanticProgram program analysis) instruction position =
          some operand ∧
        operand.kind = kind := by
  let machine := rawSemanticProgram program analysis
  have hstatic := raw_semantic_program_static_safe_of_judgment hjudgment hanalysis
  have hwell := instruction_well_formed_of_raw_static_safe hstatic hlookup
  obtain ⟨operand, hoperand⟩ := instructionOperandAt_exists_of_wellFormed hwell hposition
  have hidentity := instructionOperandAt_identity hoperand
  have hoperandMem : operand ∈ machine.operands := by
    change instructionOperandAt? machine instruction position = some operand at hoperand
    cases hget : machine.operands[instruction.firstOperand.toNat + position]? with
    | none => simp [instructionOperandAt?, hposition, hget] at hoperand
    | some found =>
        have hfoundMem := Array.mem_iff_getElem?.mpr
          ⟨instruction.firstOperand.toNat + position, hget⟩
        have hparts : (found.owner = instruction.id ∧ found.position.toNat = position) ∧
            found = operand := by
          simpa [instructionOperandAt?, hposition, hget] using hoperand
        rw [← hparts.2]
        exact hfoundMem
  obtain ⟨source, owner, hsourceMem, hsourceOp, howner, hoperandOwner,
      hoperandPosition, _, _, hoperandKind⟩ :=
    raw_operand_source_shape hoperandMem
  have hrecord := semantic_operand_record_ok_of_verified hjudgment hsourceMem hsourceOp
  have hcontiguous := semanticOperandRecordOK_contiguous howner hrecord
  have hsourceOwner : source.origin = instruction.id := by
    exact hoperandOwner.symm.trans hidentity.1
  have hsourcePosition : source.actual.toNat = position := by
    exact (congrArg UInt32.toNat hoperandPosition).symm.trans hidentity.2
  have hdataflow := (OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).1
  have hextract := (V9.OccurrenceDataflowSecurity.analyzed_components hdataflow).1
  have hcanonical := V9.OccurrenceDataflowSecurity.extracted_base_has_canonical_node_ids hextract
  have hsourceLookup : program.base.nodes[source.nodeId.toNat - 1]? = some source := by
    obtain ⟨sourceIndex, hsourceBound, hsourceGet⟩ :=
      Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hsourceMem)
    have hcanonicalAt := hcanonical sourceIndex hsourceBound
    have hsourceGetList : program.base.nodes.toList[sourceIndex] = source := by
      simpa using hsourceGet
    have hsourceIndexEq : source.nodeId.toNat - 1 = sourceIndex := by
      rw [hsourceGetList] at hcanonicalAt
      omega
    subst sourceIndex
    exact Array.getElem?_eq_some_iff.mpr ⟨hsourceBound, hsourceGet⟩
  have hsemanticOperand :
      semanticOperandAt? program.base instruction.id position = some source := by
    unfold semanticOperandAt?
    have hindex : instruction.id.toNat + position = source.nodeId.toNat - 1 := by
      rw [hcontiguous, hsourceOwner, hsourcePosition]
    rw [hindex, hsourceLookup]
    have hopB : (source.op == .semOperand) = true := by
      rw [hsourceOp]
      decide
    have hownerB : (source.origin == instruction.id) = true := beq_iff_eq.mpr hsourceOwner
    have hpositionB : (source.actual.toNat == position) = true :=
      beq_iff_eq.mpr hsourcePosition
    simp [hopB, hownerB, hpositionB]
  unfold semanticOperandKindAt? at hkind
  rw [hsemanticOperand] at hkind
  simp only [Option.map_some, Option.some.injEq] at hkind
  exact ⟨operand, hoperand, hoperandKind.trans hkind⟩

theorem verified_state_runtime_immediate_head
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction} {offset : UInt32}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hstate : instruction.op = .stateRead ∨ instruction.op = .stateWrite)
    (himmediate : semanticImmediateAt? program.base instruction.id
      (if instruction.op = .stateRead then 1 else 2) = some offset) :
    (immediateOperands (rawSemanticProgram program analysis) instruction).head? =
      some (Int.ofNat offset.toNat) := by
  let firstImmediate := if instruction.op = .stateRead then 1 else 2
  have himmediate' :
      semanticImmediateAt? program.base instruction.id firstImmediate = some offset := by
    simpa [firstImmediate] using himmediate
  have hbound := verified_semanticImmediate_position_bounded
    hjudgment hlookup himmediate'
  obtain ⟨operand, hoperand, hoperandKind, hoperandValue, hoperandHigh⟩ :=
    verified_semanticImmediate_runtime_operand
      hjudgment hanalysis hlookup himmediate'
  have hsemanticPrefix :=
    verified_state_instruction_semantic_value_prefix hjudgment hlookup hstate
  have hbefore : ∀ position, position < firstImmediate →
      ∃ prior,
        instructionOperandAt? (rawSemanticProgram program analysis) instruction position =
            some prior ∧
          prior.kind ≠ 3 := by
    intro position hposition
    have hposition' :
        position < (if instruction.op = .stateRead then 1 else 2) := by
      simpa [firstImmediate] using hposition
    have hsemanticKind := hsemanticPrefix position hposition'
    have hruntimeBound : position < instruction.operandCount.toNat :=
      Nat.lt_trans hposition hbound
    obtain ⟨prior, hprior, hpriorKind⟩ :=
      verified_semanticOperand_runtime_kind
        hjudgment hanalysis hlookup hruntimeBound hsemanticKind
    refine ⟨prior, hprior, ?_⟩
    rw [hpriorKind]
    decide
  have hhead := immediateOperands_head_of_first_runtime_immediate
    (rawSemanticProgram program analysis) instruction hbound hoperand hoperandKind hbefore
  have himmediateValue : operandImmediate operand = Int.ofNat offset.toNat := by
    unfold operandImmediate
    rw [hoperandValue, hoperandHigh]
    simp
  rw [hhead, himmediateValue]

theorem stateSinkAt_semantic_immediate_exact
    {program : V9.Program} {analysis : Analysis} {instruction : Instruction}
    {operation : SemanticInstrOp} {position : Nat} {sink : Label}
    (h : stateSinkAt? program analysis instruction operation position = some sink) :
    ∃ offset,
      semanticImmediateAt? program.base instruction.id position = some offset ∧
        stateLabelForFunctionAt? analysis.stateContracts instruction.functionId offset =
          some sink := by
  unfold stateSinkAt? at h
  simp only [bind, Option.bind_none] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨source, hsource, h⟩ := h
  split at h
  · cases h
  · rename_i hguard
    have hsourceId : source.nodeId = instruction.id := by
      by_contra hne
      have hneB : (source.nodeId != instruction.id) = true := bne_iff_ne.mpr hne
      simp [hneB] at hguard
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨offset, hoffset, hlookup⟩ := h
    exact ⟨offset, by simpa [hsourceId] using hoffset, hlookup⟩

theorem verified_stateSink_runtime_offset
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction} {sink : Label}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hstate : instruction.op = .stateRead ∨ instruction.op = .stateWrite)
    (hsink : stateSinkAt? program analysis instruction instruction.op
      (if instruction.op = .stateRead then 1 else 2) = some sink) :
    ∃ offset,
      stateLabelForFunctionAt? analysis.stateContracts instruction.functionId offset =
          some sink ∧
        (immediateOperands (rawSemanticProgram program analysis) instruction).head?.getD 0 =
          Int.ofNat offset.toNat := by
  obtain ⟨offset, himmediate, hcontract⟩ :=
    stateSinkAt_semantic_immediate_exact hsink
  have hhead := verified_state_runtime_immediate_head
    hjudgment hanalysis hlookup hstate himmediate
  exact ⟨offset, hcontract, by simp [hhead]⟩

/-- Exact decoder-slice bridge for a verified state read.  The offset used by the raw step is the
    same function-owned offset inspected by the production occurrence judgment. -/
theorem verified_stateRead_runtime_offset
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction} {sink : Label}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hread : instruction.op = .stateRead)
    (hsink : stateSinkAt? program analysis instruction .stateRead 1 = some sink) :
    ∃ offset,
      stateLabelForFunctionAt? analysis.stateContracts instruction.functionId offset =
          some sink ∧
        (immediateOperands (rawSemanticProgram program analysis) instruction).head?.getD 0 =
          Int.ofNat offset.toNat := by
  have hsink' : stateSinkAt? program analysis instruction instruction.op
      (if instruction.op = .stateRead then 1 else 2) = some sink := by
    simpa [hread] using hsink
  exact verified_stateSink_runtime_offset hjudgment hanalysis hlookup
    (Or.inl hread) hsink'

/-- Exact decoder-slice bridge for a verified state write. -/
theorem verified_stateWrite_runtime_offset
    {program : V9.Program} (hjudgment : V9OccurrenceJudgment program)
    {analysis : Analysis} (hanalysis : analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction} {sink : Label}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hwrite : instruction.op = .stateWrite)
    (hsink : stateSinkAt? program analysis instruction .stateWrite 2 = some sink) :
    ∃ offset,
      stateLabelForFunctionAt? analysis.stateContracts instruction.functionId offset =
          some sink ∧
        (immediateOperands (rawSemanticProgram program analysis) instruction).head?.getD 0 =
          Int.ofNat offset.toNat := by
  have hsink' : stateSinkAt? program analysis instruction instruction.op
      (if instruction.op = .stateRead then 1 else 2) = some sink := by
    simpa [hwrite] using hsink
  exact verified_stateSink_runtime_offset hjudgment hanalysis hlookup
    (Or.inr hwrite) hsink'

end LambdaSigil.Combined.V9.PublicLocalSecurity
