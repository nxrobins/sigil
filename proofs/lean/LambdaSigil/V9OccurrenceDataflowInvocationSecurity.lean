import LambdaSigil.V9OccurrenceDataflowInvocation
import LambdaSigil.OccurrenceInvocationSecurity

/-!
# Root-seeded, actual-callee invocation obligations

Returned results use the new host-derived machine and ranked local analysis. Existing local
seeds survive root seeding, the unchanged bounded worklist closes the extracted call graph,
and independently re-extracted checks cover actual raw callees. Root entry contracts are
lower bounds, including along conservative invocation paths; they are not internal-call caps.
These unary facts do not assert balanced execution, host approval, or Public noninterference.
-/

namespace LambdaSigil.Combined.V9.OccurrenceDataflowInvocationSecurity

open Semantic OccurrenceTransfer OccurrenceInvocation OccurrenceDataflowInvocation
open SemanticDataflow

private theorem flows_trans {a b c : Label} (hab : a.flowsTo b = true)
    (hbc : b.flowsTo c = true) : a.flowsTo c = true := by
  simp only [Label.flowsTo, decide_eq_true_eq] at *
  omega

private theorem influence_components {a b c d : Label}
    (h : ((a.lub b).lub c).flowsTo d = true) :
    a.flowsTo d = true ∧ b.flowsTo d = true ∧ c.flowsTo d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Label.flowsTo, Label.lub, Label.rank]

theorem analyzed_components {program : Program} {result : Analysis}
    (h : analyze? program = some result) :
    OccurrenceDataflow.analyze? program = some result.dataflow ∧
      RankedDecodedOccurrence.analyze? (OccurrenceDataflow.semanticProgram program result.dataflow) =
        some result.localAnalysis ∧
      (∃ plan rootedPlan,
        invocationPlan? (OccurrenceDataflow.semanticProgram program result.dataflow)
          result.localAnalysis.frontiers = some plan ∧
        seedRootEntries? program result.dataflow.contracts
          (OccurrenceDataflow.semanticProgram program result.dataflow) plan = some rootedPlan ∧
        result.labels = computeInvocationLabels
          (OccurrenceDataflow.semanticProgram program result.dataflow) rootedPlan) ∧
      rootEntryChecks program result.dataflow.contracts
        (OccurrenceDataflow.semanticProgram program result.dataflow) result.labels = true ∧
      invocationChecks (OccurrenceDataflow.semanticProgram program result.dataflow)
        result.localAnalysis.frontiers result.labels = true := by
  unfold analyze? at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨dataflow, hdataflow, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨localAnalysis, hlocal, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨plan, hplan, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨rootedPlan, hrooted, h⟩ := h
  split at h
  · rename_i hchecks
    cases h
    simp only [Bool.and_eq_true] at hchecks
    exact ⟨hdataflow, hlocal, ⟨plan, rootedPlan, hplan, hrooted, rfl⟩,
      hchecks.1.2, hchecks.2⟩
  · cases h

/-- The state-contract table returned by analysis is the exact one-pass index built from the
    accepted program and decoded function count; it is not caller-supplied evidence. -/
theorem analyzed_state_contract_index {program : Program} {result : Analysis}
    (h : analyze? program = some result) :
    result.stateContracts = buildStateContractIndex program
      (OccurrenceDataflow.semanticProgram program result.dataflow).functions.size := by
  unfold analyze? at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨dataflow, hdataflow, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨localAnalysis, hlocal, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨plan, hplan, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨rootedPlan, hrooted, h⟩ := h
  split at h
  · cases h
    rfl
  · cases h

def StateContractRecordCovered (functionCount : Nat) (index : Array StateContractEntry)
    (contract : Node) : Prop :=
  stateContractDeclarationB contract = true →
    contract.origin ≠ 0 ∧ contract.origin.toNat ≤ functionCount ∧
      ∃ sink, stateLabelForFunctionAt? index contract.origin contract.actual = some sink ∧
        contract.labelA.flowsTo sink = true

def StateContractCoverage (program : Program) (functionCount : Nat)
    (index : Array StateContractEntry) : Prop :=
  ∀ (position : Nat) (hposition : position < program.base.nodes.size),
    StateContractRecordCovered functionCount index program.base.nodes[position]

def StateContractEntryWitnessed (program : Program) (entry : StateContractEntry) : Prop :=
  entry.witnessNodeId ≠ 0 ∧
    ∃ contract,
      program.base.nodes[entry.witnessNodeId.toNat - 1]? = some contract ∧
        contract.nodeId = entry.witnessNodeId ∧
        stateContractDeclarationB contract = true ∧
        contract.origin = entry.functionId ∧ contract.actual = entry.offset ∧
        contract.labelA = entry.label

def StateContractIndexWitnessed (program : Program) (index : Array StateContractEntry) : Prop :=
  ∀ (position : Nat) (hposition : position < index.size),
    StateContractEntryWitnessed program index[position]

/-- Exact index evidence has both directions: every declaration contributes a lower bound to its
    exact-key lookup, and every returned index label is witnessed by a declaration with that same
    function, offset, and label.  Since labels form a chain, these facts identify the result with
    the declared lub rather than merely with an arbitrary upper bound. -/
def StateContractIndexExact (program : Program) (functionCount : Nat)
    (index : Array StateContractEntry) : Prop :=
  StateContractCoverage program functionCount index ∧
    StateContractIndexWitnessed program index

theorem stateContractRecordCoveredB_iff (functionCount : Nat)
    (index : Array StateContractEntry) (contract : Node) :
    stateContractRecordCoveredB functionCount index contract = true ↔
      StateContractRecordCovered functionCount index contract := by
  unfold stateContractRecordCoveredB StateContractRecordCovered
  by_cases hdeclaration : stateContractDeclarationB contract = true
  · simp only [hdeclaration, if_true]
    cases hlookup : stateLabelForFunctionAt? index contract.origin contract.actual with
    | none => simp
    | some sink => simp [and_assoc]
  · have hfalse : stateContractDeclarationB contract = false := by
      cases hvalue : stateContractDeclarationB contract <;> simp_all
    simp [hfalse]

theorem stateContractEntryWitnessedB_iff (program : Program) (entry : StateContractEntry) :
    stateContractEntryWitnessedB program entry = true ↔
      StateContractEntryWitnessed program entry := by
  unfold stateContractEntryWitnessedB StateContractEntryWitnessed
  by_cases hzero : entry.witnessNodeId = 0
  · simp [hzero]
  · cases hcontract : program.base.nodes[entry.witnessNodeId.toNat - 1]? with
    | none => simp [hzero]
    | some contract => simp [hzero, and_assoc]

theorem stateContractIndexChecks_iff (program : Program) (functionCount : Nat)
    (index : Array StateContractEntry) :
    stateContractIndexChecks program functionCount index = true ↔
      StateContractIndexExact program functionCount index := by
  unfold stateContractIndexChecks StateContractIndexExact
  rw [Bool.and_eq_true]
  apply and_congr
  · unfold StateContractCoverage
    constructor
    · intro h position hposition
      have hrow := Array.all_eq_true.mp h position hposition
      exact (stateContractRecordCoveredB_iff functionCount index
        program.base.nodes[position]).mp hrow
    · intro h
      apply Array.all_eq_true.mpr
      intro position hposition
      exact (stateContractRecordCoveredB_iff functionCount index
        program.base.nodes[position]).mpr (h position hposition)
  · unfold StateContractIndexWitnessed
    constructor
    · intro h position hposition
      have hrow := Array.all_eq_true.mp h position hposition
      exact (stateContractEntryWitnessedB_iff program index[position]).mp hrow
    · intro h
      apply Array.all_eq_true.mpr
      intro position hposition
      exact (stateContractEntryWitnessedB_iff program index[position]).mpr
        (h position hposition)

theorem binarySearchStateContract_sound (index : Array StateContractEntry)
    (functionId offset : UInt32) (fuel lower upper : Nat) (sink : Label)
    (h : binarySearchStateContract index functionId offset fuel lower upper = some sink) :
    ∃ (position : Nat) (entry : StateContractEntry),
      index[position]? = some entry ∧ entry.functionId = functionId ∧
        entry.offset = offset ∧ entry.label = sink := by
  induction fuel generalizing lower upper with
  | zero => simp [binarySearchStateContract] at h
  | succ fuel ih =>
      unfold binarySearchStateContract at h
      split at h
      · contradiction
      · let middle := lower + (upper - lower) / 2
        cases hentry : index[middle]? with
        | none => simp [middle, hentry] at h
        | some entry =>
            simp only [middle, hentry] at h
            split at h
            · rename_i hexact
              cases h
              simp only [Bool.and_eq_true, beq_iff_eq] at hexact
              exact ⟨middle, entry, hentry, hexact.1, hexact.2, rfl⟩
            · split at h
              · exact ih _ _ h
              · exact ih _ _ h

theorem stateLabelForFunctionAt_sound (index : Array StateContractEntry)
    (functionId offset : UInt32) (sink : Label)
    (h : stateLabelForFunctionAt? index functionId offset = some sink) :
    ∃ (position : Nat) (entry : StateContractEntry),
      index[position]? = some entry ∧ entry.functionId = functionId ∧
        entry.offset = offset ∧ entry.label = sink := by
  exact binarySearchStateContract_sound index functionId offset (index.size + 1) 0 index.size sink h

/-- Lookup soundness is independent of sorting correctness: the executable search can return only
    an exact-key array entry, and the reverse index check ties that entry to an exact declaration. -/
theorem state_contract_lookup_has_exact_declaration {program : Program}
    {index : Array StateContractEntry}
    (hwitnessed : StateContractIndexWitnessed program index)
    {functionId offset : UInt32} {sink : Label}
    (hlookup : stateLabelForFunctionAt? index functionId offset = some sink) :
    ∃ contract,
      program.base.nodes[contract.nodeId.toNat - 1]? = some contract ∧
        stateContractDeclarationB contract = true ∧ contract.origin = functionId ∧
        contract.actual = offset ∧ contract.labelA = sink := by
  obtain ⟨position, entry, hentry, hfunction, hoffset, hlabel⟩ :=
    stateLabelForFunctionAt_sound index functionId offset sink hlookup
  have hposition := (Array.getElem?_eq_some_iff.mp hentry).1
  have hvalue := (Array.getElem?_eq_some_iff.mp hentry).2
  have hwitness := hwitnessed position hposition
  rw [hvalue] at hwitness
  obtain ⟨_, contract, hcontract, hnode, hdeclaration, horigin, hactual, hcontractLabel⟩ :=
    hwitness
  have horigin' := horigin.trans hfunction
  have hactual' := hactual.trans hoffset
  have hcontractLabel' := hcontractLabel.trans hlabel
  rw [← hnode] at hcontract
  exact ⟨contract, hcontract, hdeclaration, horigin', hactual', hcontractLabel'⟩

/-- Two-sided characterization of an accepted lookup. Its result is the label of an exact-key
    declaration and is an upper bound for every declaration at that same key; on the four-label
    chain this is precisely the declared lub. -/
theorem state_contract_lookup_is_exact_declared_lub {program : Program} {functionCount : Nat}
    {index : Array StateContractEntry}
    (hexact : StateContractIndexExact program functionCount index)
    {functionId offset : UInt32} {sink : Label}
    (hlookup : stateLabelForFunctionAt? index functionId offset = some sink) :
    (∃ contract,
      program.base.nodes[contract.nodeId.toNat - 1]? = some contract ∧
        stateContractDeclarationB contract = true ∧ contract.origin = functionId ∧
        contract.actual = offset ∧ contract.labelA = sink) ∧
      ∀ (position : Nat) (hposition : position < program.base.nodes.size),
        stateContractDeclarationB program.base.nodes[position] = true →
          program.base.nodes[position].origin = functionId →
          program.base.nodes[position].actual = offset →
          program.base.nodes[position].labelA.flowsTo sink = true := by
  refine ⟨state_contract_lookup_has_exact_declaration hexact.2 hlookup, ?_⟩
  intro position hposition hdeclaration horigin hactual
  obtain ⟨_, _, found, hfound, hflow⟩ := hexact.1 position hposition hdeclaration
  rw [horigin, hactual, hlookup] at hfound
  cases hfound
  exact hflow

/-- Both directions of the exact-key index check are carried by every accepted analysis. -/
theorem analyzed_state_contract_exact {program : Program} {result : Analysis}
    (h : analyze? program = some result) :
    StateContractIndexExact program
      (OccurrenceDataflow.semanticProgram program result.dataflow).functions.size
      result.stateContracts := by
  unfold analyze? at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨dataflow, hdataflow, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨localAnalysis, hlocal, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨plan, hplan, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨rootedPlan, hrooted, h⟩ := h
  split at h
  · rename_i hchecks
    cases h
    simp only [Bool.and_eq_true] at hchecks
    exact (stateContractIndexChecks_iff _ _ _).mp hchecks.1.1
  · cases h

/-- Every analyzed state declaration is covered by the exact-pair lookup, so its declared label
    flows to the coalesced sink. -/
theorem analyzed_state_contract_coverage {program : Program} {result : Analysis}
    (h : analyze? program = some result) :
    StateContractCoverage program
      (OccurrenceDataflow.semanticProgram program result.dataflow).functions.size
      result.stateContracts :=
  (analyzed_state_contract_exact h).1

/-- Conversely, every index label has an exact-key source declaration carrying that same label. -/
theorem analyzed_state_contract_witnessed {program : Program} {result : Analysis}
    (h : analyze? program = some result) :
    StateContractIndexWitnessed program result.stateContracts :=
  (analyzed_state_contract_exact h).2

private theorem seedRootList_preserves_source (roots : List FunctionRootContract)
    (labels : Array Label) : ArrayFlows labels (roots.foldl seedRootEntry labels) := by
  induction roots generalizing labels with
  | nil => exact ArrayFlows.refl labels
  | cons root roots ih =>
      have hstep : ArrayFlows labels (seedRootEntry labels root) := by
        unfold seedRootEntry
        split
        · exact ArrayFlows.refl labels
        · exact ArrayFlows.raise _ _ _
      exact hstep.trans (ih _)

theorem seedRootLabels_preserves_source (roots : Array FunctionRootContract)
    (labels : Array Label) : ArrayFlows labels (seedRootLabels roots labels) := by
  simpa only [seedRootLabels, ← Array.foldl_toList] using
    seedRootList_preserves_source roots.toList labels

private theorem rooted_plan_components {program : Program} {contracts : BoundaryContracts.Index}
    {machine : SemanticProgram} {plan rootedPlan : InvocationPlan}
    (h : seedRootEntries? program contracts machine plan = some rootedPlan) :
    rootLayoutChecks program contracts machine = true ∧
      plan.seeds.size = invocationCellCount machine ∧
      rootedPlan.adjacency = plan.adjacency ∧
      rootedPlan.seeds = seedRootLabels contracts.roots plan.seeds := by
  unfold seedRootEntries? at h
  split at h
  · rename_i hchecks
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hchecks
    exact ⟨hchecks.1.1, hchecks.1.2, rfl, rfl⟩
  · cases h

/-- Root seeding preserves the graph and every local seed. Closure here is derived from the
    real construction and the worklist bound, rather than assumed from its final postcheck. -/
theorem returned_invocation_graph_is_closed {program : Program} {result : Analysis}
    (h : analyze? program = some result) :
    ∃ plan, invocationPlan? (OccurrenceDataflow.semanticProgram program result.dataflow)
        result.localAnalysis.frontiers = some plan ∧
      ArrayFlows plan.seeds result.labels ∧ EdgesClosed plan.adjacency result.labels := by
  obtain ⟨_, _, ⟨plan, rootedPlan, hplan, hrooted, hlabels⟩, _, _⟩ := analyzed_components h
  obtain ⟨hlayout, hsize, hadjacency, hseeds⟩ := rooted_plan_components hrooted
  have hfunctionLayout : functionLayoutB
      (OccurrenceDataflow.semanticProgram program result.dataflow) = true := by
    simp only [rootLayoutChecks, Bool.and_eq_true] at hlayout
    exact hlayout.1.1.1
  have hbound := OccurrenceInvocationSecurity.constructed_invocation_plan_is_bounded
    hfunctionLayout hplan
  have hrootSeed := seedRootLabels_preserves_source result.dataflow.contracts.roots plan.seeds
  have hrootSize : rootedPlan.seeds.size = invocationCellCount
      (OccurrenceDataflow.semanticProgram program result.dataflow) := by
    rw [hseeds, ← hrootSeed.1, hsize]
  have hgraph : AdjacencyWellFormed rootedPlan.seeds.size rootedPlan.adjacency := by
    rw [hrootSize, hadjacency]
    exact hbound.2.2
  have hclosed := initial_work_edges_closed hgraph
  have hinflation : ArrayFlows rootedPlan.seeds result.labels := by
    rw [hlabels]
    exact saturateGraphWorklist_inflationary _ _ _ _
  refine ⟨plan, hplan, ?_, ?_⟩
  · have hsource : ArrayFlows plan.seeds rootedPlan.seeds := by
      simpa only [hseeds] using hrootSeed
    exact hsource.trans hinflation
  · simpa only [hlabels, computeInvocationLabels, hrootSize, hadjacency] using hclosed

/-- This reads the actual program declaration, not a substituted caller-provided root table. -/
theorem returned_root_entry_flows {program : Program} {result : Analysis}
    (h : analyze? program = some result) {root : FunctionRootContract}
    (hroot : root ∈ program.roots) (hexternal : root.role ≠ 0) :
    root.entryOccurrence.flowsTo (labelAt result.labels root.functionId) = true := by
  have hchecks := (analyzed_components h).2.2.2.1
  simp only [rootEntryChecks, Bool.and_eq_true] at hchecks
  have hsame : result.dataflow.contracts.roots = program.roots := by
    have hlayout := hchecks.1.1
    simp only [rootLayoutChecks, Bool.and_eq_true, decide_eq_true_eq] at hlayout
    exact hlayout.1.1.2
  have hroot' : root ∈ result.dataflow.contracts.roots := by simpa only [hsame] using hroot
  obtain ⟨position, hposition, heq⟩ := Array.mem_iff_getElem.mp hroot'
  have hrow := Array.all_eq_true.mp hchecks.2 position hposition
  simpa [heq, hexternal] using hrow

private theorem checked_sites {machine : SemanticProgram} {frontiers : ThresholdFrontiers}
    {labels : Array Label} (h : invocationChecks machine frontiers labels = true)
    {pc : Nat} (hpc : pc < machine.instructions.size) :
    (match invocationSite? machine frontiers pc with
     | none => false
     | some none => true
     | some (some site) => (siteInfluence labels site).flowsTo (labelAt labels site.destination)) = true := by
  simp only [invocationChecks, Bool.and_eq_true] at h
  exact (List.all_eq_true.mp h.1.2) pc (List.mem_range.mpr hpc)

private theorem checked_dynamic_targets {machine : SemanticProgram} {frontiers : ThresholdFrontiers}
    {labels : Array Label} (h : invocationChecks machine frontiers labels = true)
    {callee : Function} (hcallee : callee ∈ machine.functions) :
    (labelAt labels (dynamicCell machine)).flowsTo (labelAt labels callee.id) = true := by
  simp only [invocationChecks, Bool.and_eq_true] at h
  obtain ⟨position, hposition, heq⟩ := Array.mem_iff_getElem.mp hcallee
  simpa [heq] using Array.all_eq_true.mp h.2 position hposition

theorem returned_call_site_constraint {program : Program} {result : Analysis}
    (h : analyze? program = some result) {pc : Nat}
    (hpc : pc < (OccurrenceDataflow.semanticProgram program result.dataflow).instructions.size)
    {site : InvocationSite}
    (hsite : invocationSite? (OccurrenceDataflow.semanticProgram program result.dataflow)
      result.localAnalysis.frontiers pc = some (some site)) :
    (siteInfluence result.labels site).flowsTo (labelAt result.labels site.destination) = true := by
  have hchecked := checked_sites (analyzed_components h).2.2.2.2 hpc
  simpa only [hsite] using hchecked

private theorem functionById_has_id {machine : SemanticProgram} {id : UInt32} {callee : Function}
    (h : functionById? machine id = some callee) : callee.id = id := by
  have hid := Array.find?_some (p := fun function : Function => function.id == id)
    (xs := machine.functions) (a := callee) h
  exact beq_iff_eq.mp hid

private theorem closure_callee_mem {machine : SemanticProgram} {payload : Int} {callee : Function}
    (h : closureFunction? machine payload = some callee) : callee ∈ machine.functions := by
  unfold closureFunction? at h
  simp only [bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact Array.mem_of_find?_eq_some h

private theorem first_operand_value_cell {machine : SemanticProgram} {state : State}
    {instruction : Instruction} {value : Value}
    (h : (operandValues machine state instruction).head? = some value) :
    ∃ cell, (valueOperandCells machine instruction).head? = some cell ∧
      labelAt machine.valueLabels cell = value.label := by
  simp only [operandValues, List.head?_map] at h
  cases hhead : (valueOperandCells machine instruction).head? with
  | none => simp [hhead] at h
  | some cell =>
    simp only [hhead, Option.map_some, Option.some.injEq] at h
    exact ⟨cell, rfl, congrArg Value.label h⟩

/-- Direct targets and dynamic selectors follow the actual raw accessors, including the
    first decoded value operand and fallible closure table lookup. No supplied target set. -/
theorem returned_actual_callee_receives_influence {program : Program} {result : Analysis}
    (h : analyze? program = some result) {state : State} {instruction : Instruction} {callee : Function}
    (hlookup : (OccurrenceDataflow.semanticProgram program result.dataflow).instructions[state.pc]? =
      some instruction)
    (hcallee : instructionCallee? (OccurrenceDataflow.semanticProgram program result.dataflow)
      state instruction = some callee) :
    (((labelAt result.labels instruction.functionId).lub
      (localOccurrenceAt result.localAnalysis.frontiers state.pc)).lub
      (if instruction.op == .closure then
        (operandValue (OccurrenceDataflow.semanticProgram program result.dataflow) state instruction).label
       else .pub)).flowsTo (labelAt result.labels callee.id) = true := by
  have hpc : state.pc < (OccurrenceDataflow.semanticProgram program result.dataflow).instructions.size :=
    (Array.getElem?_eq_some_iff.mp hlookup).1
  have hchecks := (analyzed_components h).2.2.2.2
  have hsite := checked_sites hchecks hpc
  cases hop : instruction.op <;> simp only [instructionCallee?, hop] at hcallee
  case call =>
    rw [Option.bind_eq_some_iff] at hcallee
    obtain ⟨id, hid, hfunction⟩ := hcallee
    have hcalleeId := functionById_has_id hfunction
    by_cases hcaller : validFunctionIdB (OccurrenceDataflow.semanticProgram program result.dataflow)
        instruction.functionId = true
    · by_cases hvalid : validFunctionIdB (OccurrenceDataflow.semanticProgram program result.dataflow) id = true
      · simp [invocationSite?, hlookup, bind, hop, hcaller, hid, hvalid, siteInfluence] at hsite
        simpa [hop, hcalleeId] using hsite
      · simp [invocationSite?, hlookup, bind, hop, hcaller, hid, hvalid] at hsite
    · simp [invocationSite?, hlookup, bind, hop, hcaller] at hsite
  case closure =>
    rw [Option.bind_eq_some_iff] at hcallee
    obtain ⟨value, hvalue, hfunction⟩ := hcallee
    obtain ⟨cell, hcell, hlabel⟩ := first_operand_value_cell hvalue
    have htarget := checked_dynamic_targets hchecks (closure_callee_mem hfunction)
    by_cases hcaller : validFunctionIdB (OccurrenceDataflow.semanticProgram program result.dataflow)
        instruction.functionId = true
    · simp [invocationSite?, hlookup, bind, hop, hcaller, hcell, siteInfluence] at hsite
      have hflow := flows_trans hsite htarget
      simpa [hop, operandValue, hvalue, hlabel] using hflow
    · simp [invocationSite?, hlookup, bind, hop, hcaller] at hsite
  all_goals contradiction

/-- Invocation edges may use different raw value stores. This composes conservative call
    influence, not a claim that a single balanced execution takes all path edges. -/
theorem returned_root_entry_reaches_transitive_callee {program : Program} {result : Analysis}
    (h : analyze? program = some result) {root : FunctionRootContract} {target : UInt32}
    (hroot : root ∈ program.roots) (hexternal : root.role ≠ 0)
    (hpath : OccurrenceInvocationSecurity.InvocationPath
      (OccurrenceDataflow.semanticProgram program result.dataflow) root.functionId target) :
    root.entryOccurrence.flowsTo (labelAt result.labels target) = true := by
  have hpaths : ∀ {caller target}, OccurrenceInvocationSecurity.InvocationPath
      (OccurrenceDataflow.semanticProgram program result.dataflow) caller target →
      (labelAt result.labels caller).flowsTo (labelAt result.labels target) = true := by
    intro caller target path
    induction path with
    | same functionId => simp [Label.flowsTo]
    | @next caller middle target hedge _ ih =>
        obtain ⟨state, instruction, callee, hlookup, hcallee, hcaller, htarget⟩ := hedge
        have hstep := (influence_components
          (returned_actual_callee_receives_influence h hlookup hcallee)).1
        rw [hcaller, htarget] at hstep
        exact flows_trans hstep ih
  exact flows_trans (returned_root_entry_flows h hroot hexternal) (hpaths hpath)

namespace InvocationWitnesses

/- These fail-closed executable regressions exercise the whole pipeline. They are deliberately
   not kernel theorems: the shared declaration extractor does not fully kernel-reduce here. -/

private def node (op : Op) (nodeId origin actual required ceiling aux : UInt32)
    (flags : UInt8 := 0) : Node :=
  ⟨op, .pub, .pub, flags, origin, actual, required, ceiling, aux, nodeId⟩

private def root (nodeId functionId : UInt32) (exportName : String)
    (role : UInt8) (entryOccurrence returnOccurrence : Label) : FunctionRootContract :=
  ⟨nodeId, functionId, 0, 0, exportName, false, role, entryOccurrence, returnOccurrence⟩

/-- Three decoded functions, two zero-argument direct calls, and no private local selector.
    The middle function has a Public external entry declaration; the last is role-zero internal. -/
private def privateRootProgram : Program :=
  { wireVersion := 9
    base := ⟨#[node .semFunction 1 1 1 2 1 0,
      node .semBlock 2 1 1 2 0 0, node .semInstruction 3 1 1 0 1 6,
      node .semOperand 4 3 0 2 0 0 2, node .semInstruction 5 1 1 0 0 28,
      node .semFunction 6 2 1 2 1 0, node .semBlock 7 2 1 2 0 0,
      node .semInstruction 8 2 1 0 1 6, node .semOperand 9 8 0 3 0 0 2,
      node .semInstruction 10 2 1 0 0 28,
      node .semFunction 11 3 1 1 1 0 4, node .semBlock 12 3 1 1 0 0,
      node .semInstruction 13 3 1 0 0 28]⟩
    hostProfileBytes := ByteArray.empty
    hostProfile := none
    ffiBindings := #[]
    actorBindings := #[]
    roots := #[root 15 1 "entry" 1 .secret .pub, root 17 2 "middle" 1 .pub .secret,
      root 19 3 "$helper" 0 .pub .pub] }

private def summary? (program : Program) : Option (Array Label × Array Label × Array (Option UInt32)) := do
  let result ← analyze? program
  let machine := OccurrenceDataflow.semanticProgram program result.dataflow
  let state : State := { pc := 0, values := #[], aggregates := #[], capabilityBalances := #[] }
  some (result.labels,
    (List.range machine.instructions.size).toArray.map (localOccurrenceAt result.localAnalysis.frontiers),
    #[0, 2].map (fun pc => (machine.instructions[pc]?).bind fun instruction =>
      (instructionCallee? machine state instruction).map Function.id))

def private_root_reaches_public_calls_and_public_declared_helper : Bool :=
    summary? privateRootProgram ==
      some (#[.pub, .secret, .secret, .secret, .pub],
        #[.pub, .pub, .pub, .pub, .pub], #[some 2, some 3])

private def omitRootSeeds? (program : Program) : Option (Bool × Bool × Array Label) := do
  let dataflow ← OccurrenceDataflow.analyze? program
  let machine := OccurrenceDataflow.semanticProgram program dataflow
  let localAnalysis ← RankedDecodedOccurrence.analyze? machine
  let plan ← invocationPlan? machine localAnalysis.frontiers
  let labels := computeInvocationLabels machine plan
  some (rootEntryChecks program dataflow.contracts machine labels,
    invocationChecks machine localAnalysis.frontiers labels, labels)

/-- Local call constraints alone really pass on the mutant, but the independent root check
    catches its lost seed. The positive full pipeline above is not vacuous. -/
def missing_root_seed_is_detected_independently : Bool :=
    omitRootSeeds? privateRootProgram ==
      some (false, true, #[.pub, .pub, .pub, .pub, .pub])

private def publicEntriesPrivateReturn : Program :=
  { privateRootProgram with roots :=
    #[root 15 1 "entry" 1 .pub .secret, root 17 2 "middle" 1 .pub .secret,
      root 19 3 "$helper" 0 .pub .pub] }

def private_return_does_not_seed_invocation : Bool :=
    (analyze? publicEntriesPrivateReturn).map Analysis.labels ==
      some #[.pub, .pub, .pub, .pub, .pub]

private def checkRegression (name : String) (passed : Bool) : IO Unit :=
  if passed then pure () else throw (IO.userError ("v9 root-invocation regression failed: " ++ name))

#eval do
  checkRegression "private root reaches Public local calls and Public-declared helper"
    private_root_reaches_public_calls_and_public_declared_helper
  checkRegression "missing root seed is independently rejected"
    missing_root_seed_is_detected_independently
  checkRegression "private return is not an invocation seed"
    private_return_does_not_seed_invocation

end InvocationWitnesses

end LambdaSigil.Combined.V9.OccurrenceDataflowInvocationSecurity
