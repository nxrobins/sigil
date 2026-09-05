import LambdaSigil.OccurrenceRegions
import LambdaSigil.SemanticSecurity

/-!
# Finite successful-path escape from checked parent edges

Theorems here derive path properties from the executable local checks, not from a supplied merge
claim or an assumed postdominance theorem. Reported ancestors are sound continuations, and live
vertices have finite graph-success witnesses. Completeness of the parent tree and correspondence
between balanced raw calls and the intraprocedural graph remain separate obligations; no theorem
here approves Public actions or claims Public noninterference.
-/

namespace LambdaSigil.Combined.OccurrenceRegionSecurity

open OccurrenceRegions

def parentIter (index : EscapeIndex) : Nat → Nat → Nat
  | 0, node => node
  | steps + 1, node => parentIter index steps (index.parentAt node)

def Ancestor (index : EscapeIndex) (candidate node : Nat) : Prop :=
  ∃ steps, parentIter index steps node = candidate

theorem ancestorB_sound {index : EscapeIndex} {candidate node : Nat}
    (h : ancestorB index candidate node = true) : Ancestor index candidate node := by
  unfold ancestorB at h
  generalize index.parent.size = fuel at h
  induction fuel generalizing node with
  | zero =>
    simp only [ancestorWithin, beq_iff_eq] at h
    exact ⟨0, h.symm⟩
  | succ fuel ih =>
    simp only [ancestorWithin, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, h.symm⟩
    · obtain ⟨steps, hsteps⟩ := ih h
      exact ⟨steps + 1, hsteps⟩

private theorem parentIter_add (index : EscapeIndex) (first second node : Nat) :
    parentIter index (first + second) node =
      parentIter index second (parentIter index first node) := by
  induction first generalizing node with
  | zero => simp [parentIter]
  | succ first ih => simpa [parentIter, Nat.succ_add] using ih (index.parentAt node)

theorem Ancestor.trans {index : EscapeIndex} {ancestor middle node : Nat}
    (hleft : Ancestor index ancestor middle) (hright : Ancestor index middle node) :
    Ancestor index ancestor node := by
  obtain ⟨left, hleft⟩ := hleft
  obtain ⟨right, hright⟩ := hright
  exact ⟨right + left, by rw [parentIter_add, hright, hleft]⟩

theorem Ancestor.of_ne {index : EscapeIndex} {candidate node : Nat}
    (h : Ancestor index candidate node) (hne : candidate ≠ node) :
    Ancestor index candidate (index.parentAt node) := by
  obtain ⟨steps, hsteps⟩ := h
  cases steps with
  | zero => exact False.elim (hne hsteps.symm)
  | succ steps => exact ⟨steps, hsteps⟩

theorem Ancestor.fixed {index : EscapeIndex} {candidate root : Nat}
    (hfixed : index.parentAt root = root) (h : Ancestor index candidate root) :
    candidate = root := by
  obtain ⟨steps, hsteps⟩ := h
  have hroot : parentIter index steps root = root := by
    clear hsteps
    induction steps with
    | zero => rfl
    | succ steps ih => simpa [parentIter, hfixed] using ih
  exact hsteps.symm.trans hroot

/-- Finite control paths retain every occurrence, including repeated vertices. The explicit
    source bound matches the whole-graph check; terminal success is selected separately. -/
inductive ControlPath (graph : ControlGraph) : Nat → Nat → List Nat → Prop
  | single (node : Nat) : ControlPath graph node node [node]
  | next {source target exit : Nat} {tail : List Nat}
      (bound : source < graph.size)
      (edge : target ∈ graph.successors.getD source [])
      (rest : ControlPath graph target exit tail) :
      ControlPath graph source exit (source :: tail)

def SuccessfulPath (graph : ControlGraph) (start : Nat) (trace : List Nat) : Prop :=
  ∃ exit ∈ graph.successfulExits, ControlPath graph start exit trace

/-- The facts used by the path proof are all local and are derived below from Boolean checks. -/
private structure CheckedFacts (graph : ControlGraph) (index : EscapeIndex) : Prop where
  exitBound : ∀ exit ∈ graph.successfulExits, exit < graph.size
  edgeBound : ∀ source < graph.size, ∀ target ∈ graph.successors.getD source [],
    target < graph.size
  exitFixed : ∀ exit ∈ graph.successfulExits, index.parentAt exit = exit
  exitLive : ∀ exit ∈ graph.successfulExits, index.liveB exit = true
  rankJustified : ∀ source < graph.size, ∀ rank, index.rankAt source = some rank →
    source ∈ graph.successfulExits ∨
      ∃ target ∈ graph.successors.getD source [], ∃ nextRank,
        index.rankAt target = some nextRank ∧ nextRank < rank
  backwardLive : ∀ source < graph.size, ∀ target ∈ graph.successors.getD source [],
    index.liveB target = true → index.liveB source = true
  edgeParent : ∀ source < graph.size, ∀ target ∈ graph.successors.getD source [],
    index.liveB target = true → Ancestor index (index.parentAt source) target

private theorem checkedFacts_of_checks {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) : CheckedFacts graph index := by
  simp only [escapeIndexChecks, Bool.and_eq_true] at hchecks
  obtain ⟨⟨⟨⟨hgraph, _⟩, _⟩, hexits⟩, hnodes⟩ := hchecks
  simp only [ControlGraph.wellFormedB, Bool.and_eq_true, List.all_eq_true,
    Array.all_eq_true, decide_eq_true_eq] at hgraph
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hexits
  simp only [List.all_eq_true, Bool.and_eq_true] at hnodes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro exit hexit
    exact (hgraph.1 exit hexit).1
  · intro source hsource target htarget
    have hsource' : source < graph.successors.size := hsource
    exact hgraph.2 source hsource' target (by simpa [Array.getD, hsource'] using htarget)
  · intro exit hexit
    exact (hexits exit hexit).1
  · intro exit hexit
    simp [EscapeIndex.liveB, (hexits exit hexit).2]
  · intro source hsource rank hrank
    have hnode := (hnodes source (List.mem_range.mpr hsource)).1.1
    simp only [successJustifiedB, hrank, Bool.or_eq_true,
      List.any_eq_true] at hnode
    rcases hnode with hexit | ⟨target, htarget, hdecrease⟩
    · exact Or.inl (by simpa using hexit)
    · right
      unfold rankDecreasesB at hdecrease
      split at hdecrease
      · cases hdecrease
      · rename_i nextRank hnext
        exact ⟨target, htarget, nextRank, hnext, of_decide_eq_true hdecrease⟩
  · intro source hsource target htarget hlive
    have hedge := (hnodes source (List.mem_range.mpr hsource)).2 target htarget
    simp only [edgeParentB, hlive, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hedge
    exact hedge.1
  · intro source hsource target htarget hlive
    have hedge := (hnodes source (List.mem_range.mpr hsource)).2 target htarget
    simp only [edgeParentB, hlive, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hedge
    exact ancestorB_sound hedge.2

private theorem successful_path_live {graph : ControlGraph} {index : EscapeIndex}
    (hfacts : CheckedFacts graph index) {start exit : Nat} {trace : List Nat}
    (hpath : ControlPath graph start exit trace) (hexit : exit ∈ graph.successfulExits) :
    index.liveB start = true := by
  induction hpath with
  | single node => exact hfacts.exitLive node hexit
  | @next source target exit tail hbound hedge _ ih =>
    exact hfacts.backwardLive source hbound target hedge (ih hexit)

private theorem rank_has_successful_path {graph : ControlGraph} {index : EscapeIndex}
    (hfacts : CheckedFacts graph index) {source rank : Nat} (hsource : source < graph.size)
    (hrank : index.rankAt source = some rank) :
    ∃ trace, SuccessfulPath graph source trace := by
  induction rank using Nat.strongRecOn generalizing source with
  | ind rank ih =>
    rcases hfacts.rankJustified source hsource rank hrank with hexit | hnext
    · exact ⟨[source], source, hexit, .single source⟩
    · obtain ⟨target, hedge, nextRank, hnextRank, hdecrease⟩ := hnext
      obtain ⟨tail, exit, hexit, hpath⟩ :=
        ih nextRank hdecrease (hfacts.edgeBound source hsource target hedge) hnextRank
      exact ⟨source :: tail, exit, hexit, .next hsource hedge hpath⟩

/-- Success membership is both witnessed and backwards complete. The checker cannot omit a
    successful arm to manufacture a continuation, nor invent reachability for a dead cycle. -/
theorem checked_live_iff_successful_path {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {source : Nat}
    (hsource : source < graph.size) :
    index.liveB source = true ↔ ∃ trace, SuccessfulPath graph source trace := by
  have hfacts := checkedFacts_of_checks hchecks
  constructor
  · intro hlive
    unfold EscapeIndex.liveB at hlive
    cases hrank : index.rankAt source with
    | none => simp [hrank] at hlive
    | some rank => exact rank_has_successful_path hfacts hsource hrank
  · rintro ⟨trace, exit, hexit, hpath⟩
    exact successful_path_live hfacts hpath hexit

private theorem ancestor_on_successful_path {graph : ControlGraph} {index : EscapeIndex}
    (hfacts : CheckedFacts graph index) {candidate start exit : Nat} {trace : List Nat}
    (hpath : ControlPath graph start exit trace) (hexit : exit ∈ graph.successfulExits)
    (hancestor : Ancestor index candidate start) : candidate ∈ trace := by
  induction hpath with
  | single node =>
    have heq := hancestor.fixed (hfacts.exitFixed node hexit)
    simp [heq]
  | @next source target exit tail hbound hedge hrest ih =>
    by_cases heq : candidate = source
    · simp [heq]
    · have hlive := successful_path_live hfacts hrest hexit
      have hnext := (hancestor.of_ne heq).trans
        (hfacts.edgeParent source hbound target hedge hlive)
      exact List.mem_cons_of_mem source (ih hexit hnext)

/-- Every finite successful path hits a reported ancestor. No supplied merge marker, numerical
    block ordering, successful-run length equality, or relational policy occurs in this theorem. -/
theorem checked_ancestor_forces_successful_hit {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {candidate start : Nat}
    (hancestor : ancestorB index candidate start = true) {trace : List Nat}
    (hpath : SuccessfulPath graph start trace) : candidate ∈ trace := by
  obtain ⟨exit, hexit, hpath⟩ := hpath
  exact ancestor_on_successful_path (checkedFacts_of_checks hchecks) hpath hexit
    (ancestorB_sound hancestor)

theorem checked_continuation_cannot_be_escaped {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {candidate start : Nat}
    (hancestor : ancestorB index candidate start = true) {trace : List Nat}
    (havoid : candidate ∉ trace) : ¬ SuccessfulPath graph start trace := by
  intro hpath
  exact havoid (checked_ancestor_forces_successful_hit hchecks hancestor hpath)

/-- Non-vacuous postdominance over finite successful graph paths: some successful path exists,
    and all such paths contain the candidate. This is soundness, not exact-tree completeness. -/
theorem checked_ancestor_postdominates {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {candidate start : Nat}
    (hstart : start < graph.size) (hlive : index.liveB start = true)
    (hancestor : ancestorB index candidate start = true) :
    (∃ trace, SuccessfulPath graph start trace) ∧
      ∀ trace, SuccessfulPath graph start trace → candidate ∈ trace := by
  exact ⟨(checked_live_iff_successful_path hchecks hstart).mp hlive,
    fun _ hpath => checked_ancestor_forces_successful_hit hchecks hancestor hpath⟩

/-- A positive self-control witness entails an actual repeated vertex on a finite successful
    graph path. Its negation cannot prove absence of repetition or approve an action. -/
theorem checked_repetition_has_repeated_path {graph : ControlGraph} {index : EscapeIndex}
    (hchecks : escapeIndexChecks graph index = true) {controller : Nat}
    (hrepeats : repeatsB graph index controller = true) :
    ∃ tail, controller ∈ tail ∧ SuccessfulPath graph controller (controller :: tail) := by
  simp only [repeatsB, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hrepeats
  obtain ⟨hcontroller, successor, hedge, hlive, hancestor⟩ := hrepeats
  have hsuccessor := (checkedFacts_of_checks hchecks).edgeBound controller hcontroller
    successor hedge
  obtain ⟨tail, hpath⟩ := (checked_live_iff_successful_path hchecks hsuccessor).mp hlive
  refine ⟨tail, checked_ancestor_forces_successful_hit hchecks hancestor hpath, ?_⟩
  obtain ⟨exit, hexit, hpath⟩ := hpath
  exact ⟨exit, hexit, .next hcontroller hedge hpath⟩

theorem instructionSuccessors_ignore_merge (p : Semantic.SemanticProgram) (pc : Nat)
    (instruction : Semantic.Instruction) (merge : UInt32) :
    instructionSuccessors p pc { instruction with merge } =
      instructionSuccessors p pc instruction := by
  cases hop : instruction.op <;> simp [instructionSuccessors, hop]

theorem instructionSuccessors_ignore_numeric_block_order (p : Semantic.SemanticProgram)
    (pc : Nat) (instruction : Semantic.Instruction) (blockId : UInt32) :
    instructionSuccessors p pc { instruction with blockId } =
      instructionSuccessors p pc instruction := by
  cases hop : instruction.op <;> simp [instructionSuccessors, hop]

theorem decodedControlGraph_instruction_edges (p : Semantic.SemanticProgram)
    (pc : Nat) (hpc : pc < p.instructions.size) :
    (decodedControlGraph p).successors.getD pc [] =
      instructionSuccessors p pc p.instructions[pc] := by
  have hcombined : pc < p.instructions.size + p.functions.size := by omega
  simp [decodedControlGraph, Array.getD, hpc, hcombined]

/-- Every live-to-live raw step other than a call or return follows the extracted edge relation.
    Calls and returns are deliberately not flattened by this lemma: their balanced-frame path
    correspondence must establish the invocation/continuation distinction separately. -/
theorem raw_noncall_step_follows_cfg {p : Semantic.SemanticProgram} {state : Semantic.State}
    {instruction : Semantic.Instruction}
    (hlookup : p.instructions[state.pc]? = some instruction)
    (hhalted : state.halted = false) (htrapped : state.trapped = false)
    (hnextHalted : (Semantic.step p state).state.halted = false)
    (hnextTrapped : (Semantic.step p state).state.trapped = false)
    (hcall : instruction.op ≠ .call) (hclosure : instruction.op ≠ .closure)
    (hreturn : instruction.op ≠ .output) :
    (Semantic.step p state).state.pc ∈ instructionSuccessors p state.pc instruction := by
  simp only [Semantic.step, hhalted, htrapped, Bool.false_or, Bool.false_eq_true,
    if_false, hlookup] at *
  cases hop : instruction.op <;>
    simp_all [Semantic.ordinaryStep, Semantic.nextPc, instructionSuccessors]
  case branch | loop | range =>
    by_cases hzero : (Semantic.operandValue p state instruction).payload = 0 <;> simp [hzero]
  case dispatch =>
    by_cases hcount : instruction.operandCount = 2 <;> simp [hcount]
    by_cases hzero : (Semantic.operandValue p state instruction).payload = 0 <;> simp [hzero]
  case trap =>
    by_cases hcount : instruction.operandCount = 0
    · simp [Semantic.operandValues, Semantic.valueOperandCells, Semantic.instructionOperands,
        hcount] at hnextTrapped
    · simp [hcount]
  case halt =>
    change true = false at hnextHalted
    cases hnextHalted
  case abortiveEffect =>
    change true = false at hnextTrapped
    cases hnextTrapped

private def headerGraph : ControlGraph := ⟨#[[1, 2], [0], []], [2]⟩
private def headerIndex : EscapeIndex := ⟨#[2, 0, 2], #[some 1, some 2, some 0]⟩

theorem repeated_header_and_continuation_witness :
    escapeIndexChecks headerGraph headerIndex = true ∧
    repeatsB headerGraph headerIndex 0 = true ∧
    ancestorB headerIndex 2 0 = true := by decide +kernel

theorem repeated_header_has_successful_repetition :
    ∃ tail, 0 ∈ tail ∧ SuccessfulPath headerGraph 0 (0 :: tail) :=
  checked_repetition_has_repeated_path repeated_header_and_continuation_witness.1
    repeated_header_and_continuation_witness.2.1

private def backwardGraph : ControlGraph := ⟨#[[2, 3], [5], [1], [4], [5], []], [5]⟩
private def backwardIndex : EscapeIndex :=
  ⟨#[5, 5, 1, 4, 5, 5], #[some 3, some 1, some 2, some 2, some 1, some 0]⟩

/-- The acyclic backwards jump confers no restoration authority: changing the branch's parent
    to the backwards arm's return fails a concrete edge condition on the other successful arm. -/
theorem acyclic_backwards_escape_rejects_invented_continuation :
    escapeIndexChecks backwardGraph backwardIndex = true ∧
    escapeIndexChecks backwardGraph
      { backwardIndex with parent := backwardIndex.parent.setIfInBounds 0 1 } = false ∧
    ancestorB backwardIndex 1 0 = false := by decide +kernel

theorem omitted_successful_arm_cannot_justify_continuation :
    escapeIndexChecks backwardGraph
      { backwardIndex with successRank := #[some 3, some 1, some 2, none, none, some 0] } =
      false := by decide +kernel

theorem dead_cycle_cannot_invent_success :
    escapeIndexChecks ⟨#[[0], []], [1]⟩
      ⟨#[1, 1], #[some 1, some 0]⟩ = false := by decide +kernel

private def chainGraph : ControlGraph := ⟨#[[1], [2], []], [2]⟩
private def preciseChain : EscapeIndex := ⟨#[1, 2, 2], #[some 2, some 1, some 0]⟩
private def coarseChain : EscapeIndex := ⟨#[2, 2, 2], #[some 2, some 1, some 0]⟩

/-- Anti-overclaim: local parent checks allow a sound but incomplete tree. Such a tree must not
    feed an occurrence-approval test that treats absent ancestry as absent control dependence. -/
theorem checked_tree_can_omit_a_real_postdominator :
    escapeIndexChecks chainGraph coarseChain = true ∧ ancestorB coarseChain 1 0 = false ∧
    ∀ trace, SuccessfulPath chainGraph 0 trace → 1 ∈ trace := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro trace hpath
  exact checked_ancestor_forces_successful_hit
    (index := preciseChain) (by decide +kernel) (by decide +kernel) hpath

private def mutualGraph : ControlGraph := ⟨#[[1, 2], [0, 2], []], [2]⟩
private def mutualIndex : EscapeIndex := ⟨#[2, 2, 2], #[some 1, some 1, some 0]⟩

/-- Even exact postdominators need transitive control-dependence closure: two controllers may
    enable a revisit without either immediately forcing it on every successful successor path. -/
theorem direct_repetition_test_does_not_detect_every_repeat :
    escapeIndexChecks mutualGraph mutualIndex = true ∧
    repeatsB mutualGraph mutualIndex 0 = false ∧
    SuccessfulPath mutualGraph 0 [0, 1, 0, 2] := by
  refine ⟨by decide +kernel, by decide +kernel, 2, by decide, ?_⟩
  exact .next (by decide) (by decide) (.next (by decide) (by decide)
    (.next (by decide) (by decide) (.single 2)))

private def fixtureInstruction (op : SemanticInstrOp) (id functionId target alternate : UInt32) :
    Semantic.Instruction :=
  { op, id, functionId, blockId := 1, destination := 0, firstOperand := 0,
    operandCount := 0, target, alternate, resultLabel := .pub, aux := 0 }

/-- A caller plus a skip-whitespace-shaped helper: the helper has a loop exit and a private
    early return. This is a CFG-shape fixture, not a capability/data-verifier acceptance claim. -/
private def privateReturnProgram : Semantic.SemanticProgram :=
  { functions := #[{ id := 1, entry := 1, firstInstruction := 0, instructionCount := 2 },
      { id := 2, entry := 1, firstInstruction := 2, instructionCount := 5 }]
    instructions := #[fixtureInstruction .call 1 1 2 0,
      fixtureInstruction .output 2 1 0 0,
      fixtureInstruction .loop 3 2 3 5,
      fixtureInstruction .branch 4 2 4 6,
      fixtureInstruction .jump 5 2 2 0,
      fixtureInstruction .output 6 2 0 0,
      fixtureInstruction .output 7 2 0 0]
    operands := #[], valueLabels := #[] }

private def privateReturnIndex : EscapeIndex :=
  ⟨#[1, 7, 8, 8, 2, 8, 8, 7, 8],
    #[some 2, some 1, some 2, some 2, some 3, some 1, some 1, some 0, some 0]⟩

/-- Private early return sites share a callee return, while the caller's continuation retains
    its own return context. The call site remains available for later invocation-effect analysis.
    No root/export observation identity or label verdict is inferred from these CFG facts. -/
theorem private_returns_preserve_distinct_caller_continuation :
    decodedControlGraphWellFormedB privateReturnProgram = true ∧
    callSites privateReturnProgram = #[0] ∧
    escapeIndexChecks (decodedControlGraph privateReturnProgram) privateReturnIndex = true ∧
    ancestorB privateReturnIndex 1 0 = true ∧
    ancestorB privateReturnIndex 8 2 = true ∧
    ancestorB privateReturnIndex 1 2 = false := by decide +kernel

end LambdaSigil.Combined.OccurrenceRegionSecurity
