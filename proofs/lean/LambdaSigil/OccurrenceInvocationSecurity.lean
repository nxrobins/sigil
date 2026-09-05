import LambdaSigil.OccurrenceInvocation
import LambdaSigil.DecodedOccurrenceSecurity
import LambdaSigil.SemanticDataflow

/-!
# Actual-callee coverage and recursive invocation constraints

Returned labels come from decoded call sites and the bounded worklist, then pass local checks
re-extracted from those same instructions. Dynamic coverage includes every function returned by
the raw lookup, without a supplied possible-target table. The path relation below composes
invocation edges, not balanced executions; return restoration and Public preservation are not
claimed. All-functions dynamic coverage remains deliberately conservative and precision-unqualified.
-/

namespace LambdaSigil.Combined.OccurrenceInvocationSecurity

open Semantic OccurrenceTransfer DecodedOccurrence OccurrenceInvocation

private theorem flows_trans {a b c : Label} (hab : a.flowsTo b = true)
    (hbc : b.flowsTo c = true) : a.flowsTo c = true := by
  simp only [Label.flowsTo, decide_eq_true_eq] at *
  omega

private theorem influence_components {a b c d : Label}
    (h : ((a.lub b).lub c).flowsTo d = true) :
    a.flowsTo d = true ∧ b.flowsTo d = true ∧ c.flowsTo d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Label.flowsTo, Label.lub, Label.rank]

theorem analyzed_invocation_components {p : SemanticProgram} {result : InvocationAnalysis}
    (h : analyzeInvocations? p = some result) :
    analyze? p = some result.localAnalysis ∧
      (∃ plan, invocationPlan? p result.localAnalysis.frontiers = some plan ∧
        result.labels = computeInvocationLabels p plan) ∧
      invocationChecks p result.localAnalysis.frontiers result.labels = true := by
  unfold analyzeInvocations? at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨localAnalysis, hlocal, h⟩ := h
  split at h
  · cases h
  · rw [Option.bind_eq_some_iff] at h
    obtain ⟨plan, hplan, h⟩ := h
    split at h
    · cases h
      exact ⟨hlocal, ⟨plan, hplan, rfl⟩, by assumption⟩
    · cases h

private theorem checked_sites {p : SemanticProgram} {frontiers : ThresholdFrontiers}
    {labels : Array Label} (h : invocationChecks p frontiers labels = true)
    {pc : Nat} (hpc : pc < p.instructions.size) :
    (match invocationSite? p frontiers pc with
     | none => false
     | some none => true
     | some (some site) => (siteInfluence labels site).flowsTo (labelAt labels site.destination)) = true := by
  simp only [invocationChecks, Bool.and_eq_true] at h
  exact (List.all_eq_true.mp h.1.2) pc (List.mem_range.mpr hpc)

private theorem checked_dynamic_targets {p : SemanticProgram} {frontiers : ThresholdFrontiers}
    {labels : Array Label} (h : invocationChecks p frontiers labels = true)
    {callee : Function} (hcallee : callee ∈ p.functions) :
    (labelAt labels (dynamicCell p)).flowsTo (labelAt labels callee.id) = true := by
  simp only [invocationChecks, Bool.and_eq_true] at h
  obtain ⟨position, hposition, heq⟩ := Array.mem_iff_getElem.mp hcallee
  simpa [heq] using Array.all_eq_true.mp h.2 position hposition

theorem returned_call_site_constraint {p : SemanticProgram} {result : InvocationAnalysis}
    (h : analyzeInvocations? p = some result) {pc : Nat} (hpc : pc < p.instructions.size)
    {site : InvocationSite}
    (hsite : invocationSite? p result.localAnalysis.frontiers pc = some (some site)) :
    (siteInfluence result.labels site).flowsTo (labelAt result.labels site.destination) = true := by
  have hchecked := checked_sites (analyzed_invocation_components h).2.2 hpc
  simpa only [hsite] using hchecked

theorem returned_dynamic_summary_covers_every_function {p : SemanticProgram}
    {result : InvocationAnalysis} (h : analyzeInvocations? p = some result)
    {callee : Function} (hcallee : callee ∈ p.functions) :
    (labelAt result.labels (dynamicCell p)).flowsTo (labelAt result.labels callee.id) = true :=
  checked_dynamic_targets (analyzed_invocation_components h).2.2 hcallee

private theorem functionById_has_id {p : SemanticProgram} {id : UInt32} {callee : Function}
    (h : functionById? p id = some callee) : callee.id = id := by
  have hid := Array.find?_some (p := fun function : Function => function.id == id)
    (xs := p.functions) (a := callee) h
  exact beq_iff_eq.mp hid

private theorem closure_callee_mem {p : SemanticProgram} {payload : Int} {callee : Function}
    (h : closureFunction? p payload = some callee) : callee ∈ p.functions := by
  unfold closureFunction? at h
  simp only [bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact Array.mem_of_find?_eq_some h

private theorem first_operand_value_cell {p : SemanticProgram} {state : State}
    {instruction : Instruction} {value : Value}
    (h : (operandValues p state instruction).head? = some value) :
    ∃ cell, (valueOperandCells p instruction).head? = some cell ∧
      labelAt p.valueLabels cell = value.label := by
  simp only [operandValues, List.head?_map] at h
  cases hhead : (valueOperandCells p instruction).head? with
  | none => simp [hhead] at h
  | some cell =>
    simp only [hhead, Option.map_some, Option.some.injEq] at h
    exact ⟨cell, rfl, congrArg Value.label h⟩

/-- The selected callee is the raw machine's actual result, including dynamic table lookup.
    Target-selection labels use decoded program labels, not labels supplied in runtime values.
    Argument arity/label checks may later trap; they cannot create another unrepresented callee. -/
theorem returned_actual_callee_receives_influence {p : SemanticProgram}
    {result : InvocationAnalysis} (h : analyzeInvocations? p = some result)
    {state : State} {instruction : Instruction} {callee : Function}
    (hlookup : p.instructions[state.pc]? = some instruction)
    (hcallee : instructionCallee? p state instruction = some callee) :
    (((labelAt result.labels instruction.functionId).lub
      (localOccurrenceAt result.localAnalysis.frontiers state.pc)).lub
      (if instruction.op == .closure then (operandValue p state instruction).label else .pub)).flowsTo
      (labelAt result.labels callee.id) = true := by
  have hpc : state.pc < p.instructions.size := (Array.getElem?_eq_some_iff.mp hlookup).1
  have hsite := checked_sites (analyzed_invocation_components h).2.2 hpc
  cases hop : instruction.op <;> simp only [instructionCallee?, hop] at hcallee
  case call =>
    rw [Option.bind_eq_some_iff] at hcallee
    obtain ⟨id, hid, hfunction⟩ := hcallee
    have hcalleeId := functionById_has_id hfunction
    by_cases hcaller : validFunctionIdB p instruction.functionId = true
    · by_cases hvalid : validFunctionIdB p id = true
      · simp [invocationSite?, hlookup, bind, hop, hcaller, hid, hvalid, siteInfluence] at hsite
        simpa [hop, hcalleeId] using hsite
      · simp [invocationSite?, hlookup, bind, hop, hcaller, hid, hvalid] at hsite
    · simp [invocationSite?, hlookup, bind, hop, hcaller] at hsite
  case closure =>
    rw [Option.bind_eq_some_iff] at hcallee
    obtain ⟨value, hvalue, hfunction⟩ := hcallee
    obtain ⟨cell, hcell, hlabel⟩ := first_operand_value_cell hvalue
    have htarget := returned_dynamic_summary_covers_every_function h (closure_callee_mem hfunction)
    by_cases hcaller : validFunctionIdB p instruction.functionId = true
    · simp [invocationSite?, hlookup, bind, hop, hcaller, hcell, siteInfluence] at hsite
      have hflow := flows_trans hsite htarget
      simpa [hop, operandValue, hvalue, hlabel] using hflow
    · simp [invocationSite?, hlookup, bind, hop, hcaller] at hsite
  all_goals contradiction

/-- Edges may be witnessed by different raw value stores. This is the conservative invocation
    relation, not a claim that the witnesses form one balanced or terminating execution. -/
def RawInvocationEdge (p : SemanticProgram) (caller target : UInt32) : Prop :=
  ∃ state instruction callee,
    p.instructions[state.pc]? = some instruction ∧
    instructionCallee? p state instruction = some callee ∧
    instruction.functionId = caller ∧ callee.id = target

inductive InvocationPath (p : SemanticProgram) : UInt32 → UInt32 → Prop
  | same (functionId : UInt32) : InvocationPath p functionId functionId
  | next {caller middle target : UInt32}
      (edge : RawInvocationEdge p caller middle) (rest : InvocationPath p middle target) :
      InvocationPath p caller target

theorem returned_recursive_invocation_path_flows {p : SemanticProgram}
    {result : InvocationAnalysis} (h : analyzeInvocations? p = some result)
    {caller target : UInt32} (hpath : InvocationPath p caller target) :
    (labelAt result.labels caller).flowsTo (labelAt result.labels target) = true := by
  induction hpath with
  | same functionId => simp [Label.flowsTo]
  | @next caller middle target hedge _ ih =>
    obtain ⟨state, instruction, callee, hlookup, hcallee, hcaller, htarget⟩ := hedge
    have hstep := (influence_components (returned_actual_callee_receives_influence h hlookup hcallee)).1
    rw [hcaller, htarget] at hstep
    exact flows_trans hstep ih

theorem returned_local_occurrence_reaches_transitive_callee {p : SemanticProgram}
    {result : InvocationAnalysis} (h : analyzeInvocations? p = some result)
    {state : State} {instruction : Instruction} {callee : Function} {target : UInt32}
    (hlookup : p.instructions[state.pc]? = some instruction)
    (hcallee : instructionCallee? p state instruction = some callee)
    (hpath : InvocationPath p callee.id target) :
    (localOccurrenceAt result.localAnalysis.frontiers state.pc).flowsTo
      (labelAt result.labels target) = true := by
  have hlocal := (influence_components (returned_actual_callee_receives_influence h hlookup hcallee)).2.1
  exact flows_trans hlocal (returned_recursive_invocation_path_flows h hpath)

private theorem valid_function_id_bound {p : SemanticProgram} {id : UInt32}
    (h : validFunctionIdB p id = true) : id.toNat < invocationCellCount p := by
  simp only [validFunctionIdB, Bool.and_eq_true, bne_iff_ne] at h
  cases hget : p.functions[id.toNat - 1]? with
  | none => simp [hget] at h
  | some function =>
    have hbound := (Array.getElem?_eq_some_iff.mp hget).1
    unfold invocationCellCount
    omega

private theorem extracted_site_bounds {p : SemanticProgram} {frontiers : ThresholdFrontiers}
    {pc : Nat} {site : InvocationSite}
    (h : invocationSite? p frontiers pc = some (some site)) :
    site.caller.toNat < invocationCellCount p ∧ site.destination.toNat < invocationCellCount p := by
  unfold invocationSite? at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨instruction, _, h⟩ := h
  cases hop : instruction.op <;> simp only [hop] at h
  case call =>
    split at h
    · cases h
    · rename_i hcaller
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨callee, _, h⟩ := h
      split at h
      · cases h
      · rename_i htarget
        cases h
        exact ⟨valid_function_id_bound (by simpa using hcaller),
          valid_function_id_bound (by simpa using htarget)⟩
  case closure =>
    split at h
    · cases h
    · rename_i hcaller
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨selector, _, h⟩ := h
      cases h
      refine ⟨valid_function_id_bound (by simpa using hcaller), ?_⟩
      have hmod : (dynamicCell p).toNat ≤ p.functions.size + 1 := Nat.mod_le _ _
      change (dynamicCell p).toNat < p.functions.size + 2
      omega
  all_goals cases h

private theorem function_layout_bounds_ids {p : SemanticProgram}
    (h : functionLayoutB p = true) {function : Function} (hfunction : function ∈ p.functions) :
    function.id.toNat < invocationCellCount p := by
  simp only [functionLayoutB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨position, hposition, heq⟩ := Array.mem_iff_getElem.mp hfunction
  have hrow := h.2 position (List.mem_range.mpr hposition)
  simp only [Array.getElem?_eq_getElem hposition, heq, beq_iff_eq] at hrow
  unfold invocationCellCount
  omega

private theorem set_outgoing_preserves_bounds {count : Nat} {adjacency : Array (List UInt32)}
    (hgraph : SemanticDataflow.AdjacencyWellFormed count adjacency) (source : UInt32)
    (targets : List UInt32) (htargets : ∀ target ∈ targets, target.toNat < count) :
    SemanticDataflow.AdjacencyWellFormed count
      (adjacency.setIfInBounds source.toNat targets) := by
  intro observed hobserved candidate hcandidate
  by_cases hbound : observed.toNat < adjacency.size
  · have hget := Array.getElem_setIfInBounds (xs := adjacency) (i := source.toNat)
      (a := targets) (j := observed.toNat) hbound
    by_cases heq : source.toNat = observed.toNat
    · exact htargets candidate (by simpa [Array.getD, hbound, hget, heq] using hcandidate)
    · exact hgraph observed hobserved candidate
        (by simpa [Array.getD, hbound, hget, heq] using hcandidate)
  · simp [Array.getD, hbound] at hcandidate

private def PlanBound (p : SemanticProgram) (plan : InvocationPlan) : Prop :=
  plan.adjacency.size = invocationCellCount p ∧ plan.seeds.size = invocationCellCount p ∧
    SemanticDataflow.AdjacencyWellFormed (invocationCellCount p) plan.adjacency

private theorem add_site_preserves_plan_bound {p : SemanticProgram} {plan : InvocationPlan}
    (hplan : PlanBound p plan) {site : InvocationSite}
    (hsite : site.caller.toNat < invocationCellCount p ∧
      site.destination.toNat < invocationCellCount p) : PlanBound p (addInvocationSite plan site) := by
  refine ⟨by simpa [addInvocationSite] using hplan.1,
    by simpa [addInvocationSite, raiseCell] using hplan.2.1, ?_⟩
  apply set_outgoing_preserves_bounds hplan.2.2
  intro target htarget
  rcases List.mem_cons.mp htarget with rfl | htarget
  · exact hsite.2
  · exact hplan.2.2 site.caller hsite.1 target htarget

private theorem fold_sites_preserves_plan_bound (p : SemanticProgram) (frontiers : ThresholdFrontiers)
    (positions : List Nat) {initial result : InvocationPlan} (hbound : PlanBound p initial)
    (hfold : positions.foldlM (fun plan pc => do
      let site ← invocationSite? p frontiers pc
      match site with
      | none => some plan
      | some call => some (addInvocationSite plan call)) initial = some result) :
    PlanBound p result := by
  induction positions generalizing initial with
  | nil => cases hfold; exact hbound
  | cons pc rest ih =>
    simp only [List.foldlM_cons, bind] at hfold
    rw [Option.bind_eq_some_iff] at hfold
    obtain ⟨next, hnext, hrest⟩ := hfold
    rw [Option.bind_eq_some_iff] at hnext
    obtain ⟨site, hsite, hnext⟩ := hnext
    cases site with
    | none => cases hnext; exact ih hbound hrest
    | some call =>
      cases hnext
      exact ih (add_site_preserves_plan_bound hbound (extracted_site_bounds hsite)) hrest

theorem constructed_invocation_plan_is_bounded {p : SemanticProgram} {frontiers : ThresholdFrontiers}
    {plan : InvocationPlan} (hlayout : functionLayoutB p = true)
    (hplan : invocationPlan? p frontiers = some plan) :
    plan.adjacency.size = invocationCellCount p ∧ plan.seeds.size = invocationCellCount p ∧
      SemanticDataflow.AdjacencyWellFormed (invocationCellCount p) plan.adjacency := by
  apply fold_sites_preserves_plan_bound p frontiers (List.range p.instructions.size) _ hplan
  refine ⟨by simp, by simp, ?_⟩
  apply set_outgoing_preserves_bounds
  · intro source _ target htarget
    simp [Array.getD] at htarget
  · intro target htarget
    obtain ⟨function, hfunction, rfl⟩ := List.mem_map.mp htarget
    exact function_layout_bounds_ids hlayout (by simpa using hfunction)

theorem constructed_invocation_worklist_closes_edges {p : SemanticProgram}
    {frontiers : ThresholdFrontiers} {plan : InvocationPlan} (hlayout : functionLayoutB p = true)
    (hplan : invocationPlan? p frontiers = some plan) :
    SemanticDataflow.ArrayFlows plan.seeds (computeInvocationLabels p plan) ∧
      SemanticDataflow.EdgesClosed plan.adjacency (computeInvocationLabels p plan) := by
  have hbound := constructed_invocation_plan_is_bounded hlayout hplan
  refine ⟨SemanticDataflow.saturateGraphWorklist_inflationary _ _ _ _, ?_⟩
  unfold computeInvocationLabels
  rw [← hbound.2.1]
  exact SemanticDataflow.initial_work_edges_closed (by simpa [hbound.2.1] using hbound.2.2)

theorem returned_invocation_graph_is_closed {p : SemanticProgram} {result : InvocationAnalysis}
    (h : analyzeInvocations? p = some result) :
    ∃ plan, invocationPlan? p result.localAnalysis.frontiers = some plan ∧
      SemanticDataflow.ArrayFlows plan.seeds result.labels ∧
      SemanticDataflow.EdgesClosed plan.adjacency result.labels := by
  obtain ⟨_, ⟨plan, hplan, hlabels⟩, hchecks⟩ := analyzed_invocation_components h
  have hlayout : functionLayoutB p = true := by
    simp only [invocationChecks, Bool.and_eq_true] at hchecks
    exact hchecks.1.1.1
  obtain ⟨hseeds, hedges⟩ := constructed_invocation_worklist_closes_edges hlayout hplan
  exact ⟨plan, hplan, by simpa [hlabels] using hseeds, by simpa [hlabels] using hedges⟩

namespace InvocationWitnesses

private def instruction (op : SemanticInstrOp) (id functionId firstOperand operandCount : UInt32)
    (target : UInt32 := 0) (alternate : UInt32 := 0) (merge : UInt32 := 0) : Instruction :=
  { op, id, functionId, blockId := 1, destination := 0, firstOperand, operandCount,
    target, alternate, merge, resultLabel := .pub, aux := 0 }

private def operand (owner position value : UInt32) (kind : UInt8 := 0) : OperandRecord :=
  { owner, position, value, kind }

private def recursiveProgram : SemanticProgram :=
  { functions := #[
      { id := 1, entry := 1, firstInstruction := 0, instructionCount := 4 },
      { id := 2, entry := 1, firstInstruction := 4, instructionCount := 2 },
      { id := 3, entry := 1, firstInstruction := 6, instructionCount := 3 }]
    instructions := #[instruction .loop 1 1 0 3 1 3 3,
      instruction .call 2 1 3 1 4, instruction .jump 3 1 4 0 0,
      instruction .output 4 1 4 0, instruction .call 5 2 4 1 6,
      instruction .output 6 2 5 0, instruction .branch 7 3 5 3 7 8 8,
      instruction .call 8 3 8 1 4, instruction .output 9 3 9 0]
    operands := #[operand 1 0 1, operand 1 1 1 1, operand 1 2 3 1,
      operand 2 0 2 2, operand 5 0 3 2, operand 7 0 0,
      operand 7 1 7 1, operand 7 2 8 1, operand 8 0 2 2]
    valueLabels := #[.pub, .secret] }

/-- The locally Public second call and recursive return edge retain the invocation influence
    introduced by the first private loop. No payload label is used as an occurrence verdict. -/
theorem direct_transitive_and_recursive_calls_receive_private_invocation :
    (analyzeInvocations? recursiveProgram).map InvocationAnalysis.labels =
      some #[.pub, .pub, .secret, .secret, .pub] := by decide +kernel

private def fixtureChecks (p : SemanticProgram) (labels : Array Label) : Bool :=
  match analyze? p with
  | none => true
  | some localAnalysis => invocationChecks p localAnalysis.frontiers labels

private def fixtureMutatedEdgesRejected (p : SemanticProgram) (source : UInt32)
    (targets : List UInt32) : Bool :=
  match analyze? p with
  | none => false
  | some localAnalysis =>
      match invocationPlan? p localAnalysis.frontiers with
      | none => false
      | some plan =>
          let mutant := { plan with adjacency := plan.adjacency.setIfInBounds source.toNat targets }
          !invocationChecks p localAnalysis.frontiers (computeInvocationLabels p mutant)

theorem missing_caller_invocation_propagation_detected :
    fixtureChecks recursiveProgram #[.pub, .pub, .secret, .pub, .pub] = false ∧
      fixtureMutatedEdgesRejected recursiveProgram 2 [] = true := by decide +kernel

theorem missing_private_call_site_seed_detected :
    fixtureChecks recursiveProgram #[.pub, .pub, .pub, .pub, .pub] = false := by decide +kernel

private def recursiveState : State :=
  { pc := 7, values := #[⟨.pub, 0⟩, ⟨.pub, 1⟩], aggregates := #[], capabilityBalances := #[] }

theorem recursive_raw_call_enters_actual_decoded_function :
    (instructionCallee? recursiveProgram recursiveState recursiveProgram.instructions[7]).map
      Function.id = some 2 ∧
      (callStep recursiveProgram recursiveState recursiveProgram.instructions[7]).state.pc = 4 ∧
      (callStep recursiveProgram recursiveState recursiveProgram.instructions[7]).state.trapped = false := by
  decide +kernel

private def closureProgram : SemanticProgram :=
  { functions := #[
      { id := 1, entry := 1, firstInstruction := 0, instructionCount := 2 },
      { id := 2, entry := 1, firstInstruction := 2, instructionCount := 1 },
      { id := 3, entry := 1, firstInstruction := 3, instructionCount := 1 }]
    instructions := #[instruction .closure 1 1 0 2, instruction .output 2 1 2 0,
      instruction .output 3 2 2 0, instruction .output 4 3 2 0]
    operands := #[operand 1 0 777 3, operand 1 1 1]
    valueLabels := #[.pub, .secret] }

private def closureState : State :=
  { pc := 0, values := #[⟨.pub, 0⟩, ⟨.pub, 1⟩], aggregates := #[], capabilityBalances := #[] }

/-- Generic in-memory semantics permits a non-value operand before the selector. The wire shape
    is stricter; the analysis still follows the actual raw accessor and ignores forged runtime
    labels. All-function coverage is explicit overtaint, not a precision/compatibility claim. -/
theorem closure_uses_first_value_selector_and_covers_all_functions :
    (analyzeInvocations? closureProgram).map InvocationAnalysis.labels =
      some #[.pub, .secret, .secret, .secret, .secret] ∧
      (instructionCallee? closureProgram closureState closureProgram.instructions[0]).map
        Function.id = some 2 ∧
      (callStep closureProgram closureState closureProgram.instructions[0]).state.pc = 2 ∧
      (callStep closureProgram closureState closureProgram.instructions[0]).state.trapped = false := by
  decide +kernel

theorem missing_dynamic_target_detected :
    fixtureChecks closureProgram #[.pub, .secret, .secret, .pub, .secret] = false ∧
      fixtureMutatedEdgesRejected closureProgram 4 [1, 2] = true := by decide +kernel

theorem missing_dynamic_selector_influence_detected :
    fixtureChecks closureProgram #[.pub, .pub, .pub, .pub, .pub] = false := by decide +kernel

private def capturedProgram : SemanticProgram :=
  { closureProgram with
    functions := #[
      { id := 1, entry := 1, firstInstruction := 0, instructionCount := 2 },
      { id := 2, entry := 1, firstInstruction := 2, instructionCount := 1, parameterCells := #[1] },
      { id := 3, entry := 1, firstInstruction := 3, instructionCount := 1 }]
    operands := #[operand 1 0 0, operand 1 1 1] }

private def capturedState : State :=
  { pc := 0, values := #[⟨.pub, 1⟩, ⟨.pub, 99⟩], aggregates := #[], capabilityBalances := #[] }

theorem private_capture_is_data_not_blanket_invocation_control :
    (analyzeInvocations? capturedProgram).map InvocationAnalysis.labels =
      some #[.pub, .pub, .pub, .pub, .pub] ∧
      (callStep capturedProgram capturedState capturedProgram.instructions[0]).state.pc = 2 ∧
      (callStep capturedProgram capturedState capturedProgram.instructions[0]).state.trapped = false := by
  decide +kernel

private def emptySelectorProgram : SemanticProgram :=
  { closureProgram with operands := #[operand 1 0 777 3, operand 1 1 888 3] }

theorem empty_dynamic_selector_rejects_without_fabricated_target :
    (analyzeInvocations? emptySelectorProgram).isNone = true ∧
      instructionCallee? emptySelectorProgram closureState emptySelectorProgram.instructions[0] = none := by
  decide +kernel

/-- An exhausted runtime value array supplies payload zero, which can select function one;
    a missing operand is different. Negative and overflowing table indices return no callee.
    The exact wrap boundary also finds no target in this canonical nonzero-ID program. -/
theorem exhausted_and_invalid_closure_values_follow_raw_lookup :
    (instructionCallee? closureProgram { closureState with values := #[] }
      closureProgram.instructions[0]).map Function.id = some 1 ∧
    instructionCallee? closureProgram { closureState with values := #[⟨.pub, 0⟩, ⟨.pub, -1⟩] }
      closureProgram.instructions[0] = none ∧
    closureFunction? closureProgram (Int.ofNat UInt32.size - 1) = none ∧
    closureFunction? closureProgram (Int.ofNat UInt32.size) = none := by
  decide +kernel

private def nestedDiamondProgram : SemanticProgram :=
  { functions := #[{ id := 1, entry := 1, firstInstruction := 0, instructionCount := 7 }]
    instructions := #[instruction .branch 1 1 0 3 1 4 5,
      instruction .branch 2 1 3 3 2 3 3, instruction .scalar 3 1 6 0,
      instruction .jump 4 1 6 0 5, instruction .scalar 5 1 6 0,
      instruction .effect 6 1 6 0, instruction .output 7 1 6 0]
    operands := #[operand 1 0 1, operand 1 1 1 1, operand 1 2 4 1,
      operand 2 0 1, operand 2 1 2 1, operand 2 2 3 1]
    valueLabels := #[.pub, .secret] }

/-- Both branches rejoin before instruction five. Nevertheless the inner-arm lane, seeded
    with stop three, widens to the function return when the outer stop five arrives. This is
    a conservative precision counterexample, not an accepted Public leak: no policy is run.
    Production compatibility must address it before enabling this constructor on the corpus. -/
theorem nested_diamond_widening_overtaints_checked_outer_continuation :
    (analyze? nestedDiamondProgram).map (fun analysis =>
      (analysis.regions.index.parentAt 0, analysis.regions.index.parentAt 1,
        localOccurrenceAt analysis.frontiers 5)) = some (5, 3, .secret) := by
  decide +kernel

end InvocationWitnesses

end LambdaSigil.Combined.OccurrenceInvocationSecurity
