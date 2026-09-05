import LambdaSigil.SemanticSecurity
import Mathlib.Data.List.Nodup

/-!
# Joint capability, information-flow, and SecretCT safety

The production checker calls `Combined.verifyBytes`; the theorems below are over the same
`verifyProgram` definition.  Version-8 CSIR adds a mandatory resolved semantic envelope to the
version-6 verifier-owned finite-lattice taint and pc-taint
cells: Rust supplies seeds and monotone edges, while Lean computes the cyclic fixed point and checks
sinks, SecretCT uses, and both downgrade stages against that derived labeling.  Capability origins,
BV32 restriction/split/draw propagation, sinks, release gates, control-flow authority meet, and slot
authority meet are likewise derived by the Lean kernel rather than accepted as Rust legitimacy
flags.  Capability consumption is checked separately along explicit `if`/`match` alternatives,
joined over fallthrough arms, and composed through loop condition/body/`continue` back-edges and
`break` exits.  Signed amount cells, normalized difference constraints, and mandatory guest/host
guards connect quantitative split/draw behavior to the same judgment.  The resolved raw
deterministic instruction machine, constructor-complete preservation proof, and conditional
SecretCT delimited-release theorem live in `SemanticSecurity`; the verifier-to-semantic-premise
connection is load-bearing through the Init-only decoded checker and the claim-surface SecretCT
corollary.  The occurrence-derived structured-region Public theorem and its pinned production
corollary live in `PublicBisimulationSecurity` and `RawClaimSurface`; they use this raw machine but
are deliberately separated from the older version-8 compatibility theorem layer.
Rust source-to-CSIR projection and native-code correspondence also remain named TCB assumptions in
`docs/SECURITY_MODEL.md`.
-/

namespace LambdaSigil.Combined

/-- Acceptance condition for a decoded production-v8 program.  `verifyProgram` alone deliberately
    remains usable by legacy theorem witnesses without a semantic suffix; the exported byte
    verifier and this predicate additionally require the manifest. -/
def ProgramSafe (p : Program) : Prop :=
  (semanticProgramNode? p).isSome = true ∧ verifyProgram p = none ∧
    Semantic.rawRelationalStaticSafeB (Semantic.semanticProgramOf p) = true

theorem linked_raw_semantic_verifier_acceptance_iff (p : Program) :
    ProgramSafe p ↔
      (semanticProgramNode? p).isSome = true ∧
        Semantic.verifyProgramWithRawSemantics p = none := by
  unfold ProgramSafe
  rw [Semantic.verifyProgramWithRawSemantics_none_iff]

def AuthorityConfined (p : Program) : Prop :=
  ∀ n, n ∈ p.nodes → n.op = .authority →
    hasFlag n.flags 0x01 = true ∧ maskSubset n.actual n.ceiling = true ∧
      maskContains n.actual n.required = true

def FlowsClean (p : Program) : Prop :=
  ∀ n, n ∈ p.nodes → (n.op = .flow ∨ n.op = .boundary) →
    n.labelA.flowsTo n.labelB = true

def ReleasesAuthorized (p : Program) : Prop :=
  ∀ n, n ∈ p.nodes → n.op = .declassify →
    hasFlag n.flags 0x01 = true ∧ maskSubset n.actual n.ceiling = true ∧
      ((capKindOf n = some .declassify ∧ n.labelA ≠ .secretCT ∧ n.labelB = .pub) ∨
       (capKindOf n = some .declassifyCT ∧ n.labelA = .secretCT ∧ n.labelB = .secret))

def CTPolicySafe (p : Program) : Prop :=
  ∀ n, n ∈ p.nodes → (n.op = .ctUse ∨ n.op = .boundary) → n.labelA ≠ .secretCT

def consumedOriginsList : List Node → List UInt32
  | [] => []
  | n :: rest =>
      if consumesOrigin n then n.origin :: consumedOriginsList rest
      else consumedOriginsList rest

def consumedOrigins (p : Program) : List UInt32 := consumedOriginsList p.nodes.toList

def AffineSafe (p : Program) : Prop := (consumedOrigins p).Nodup

def GraphSafe (p : Program) : Prop := firstGraphViolation p = none

/-- Algorithm-independent taint solution: it contains all seeds and is monotone across every
    normalized graph edge.  No reference to the worklist or its iteration order appears here. -/
def LabelsBelowCells (cellCount : Nat) (lower upper : Array Label) : Prop :=
  lower.size = cellCount ∧ upper.size = cellCount ∧
    ∀ cell < cellCount,
      (labelAt lower (UInt32.ofNat cell)).flowsTo
        (labelAt upper (UInt32.ofNat cell)) = true

def TaintSolution (p : Program) (labels : Array Label) : Prop :=
  let cellCount := p.nodes.size + 1
  p.nodes.size ≤ maxNodes ∧
    LabelsBelowCells cellCount (graphSeedLabels p) labels ∧
    ∀ source < cellCount, ∀ target,
      target ∈ (graphAdjacency p).getD source [] →
        target.toNat < cellCount ∧
          (labelAt labels (UInt32.ofNat source)).flowsTo
            (labelAt labels target) = true

/-- Per-node graph judgment: all references are bounded and every seed, edge, sink, CT use,
    and release constraint holds under the labeling computed by the kernel.  In particular, the
    edge clause makes acceptance fail closed even if the executable saturation bound were ever
    changed incorrectly. -/
def TaintGraphJudgment (p : Program) : Prop :=
  (∀ n ∈ p.nodes.toList,
    graphNodeWellFormed p n = true ∧ graphNodeSafe (graphLabels p) n = true) ∧
    TaintSolution p (graphLabels p)

/-- The capability derivation judgment follows the program in canonical node order, threading only
    verifier-produced capability/slot states.  Unlike the legacy local obligation records, there is
    no Rust-provided legitimacy bit or Rust-provided final authority mask in this judgment. -/
def CapabilityJudgmentFrom (p : Program) : Array CapState → List Node → Prop
  | _, [] => True
  | states, n :: rest =>
      capNodeWellFormed p n = true ∧ capNodeSafe states n = true ∧
        CapabilityJudgmentFrom p (applyCapabilityNode states n) rest

def CapabilityJudgment (p : Program) : Prop :=
  CapabilityJudgmentFrom p (emptyCapStates p) p.nodes.toList

/-- Ordered path-sensitive affine judgment.  Alternatives are joined by may-consumption over only
    fallthrough arms; repeatable loop edges preserve loop-head origins and `break` exits join into
    the post-loop state. -/
def PathAffineJudgmentFrom : PathAffineState → List Node → Prop
  | state, [] => state.frames.isEmpty = true ∧ state.loops.isEmpty = true
  | state, n :: rest =>
      pathAffineViolation state n = none ∧
        PathAffineJudgmentFrom (applyPathAffineNode state n) rest

def PathAffineJudgment (p : Program) : Prop :=
  PathAffineJudgmentFrom (emptyPathAffineState p) p.nodes.toList

def QuantitativeJudgment (p : Program) : Prop :=
  (∀ n ∈ p.nodes.toList, quantitativeNodeWellFormed p n = true) ∧
    differenceConsistent p = true

/-- Declarative satisfaction of the finite normalized difference constraints by an arbitrary
    integer potential. -/
def DifferencePotentialSatisfies (p : Program) (potential : Array Int) : Prop :=
  ∀ edge ∈ quantitativeEdges p,
    diffDistance potential edge.target ≤ diffDistance potential edge.source + edge.weight

/-- The v6 integer domain is i64 relative to the distinguished arithmetic-zero cell. -/
def DifferencePotentialWithinI64 (p : Program) (potential : Array Int) : Prop :=
  ∀ cell : UInt32,
    (cell = 0 ∨ ∃ edge ∈ quantitativeEdges p, edge.source = cell ∨ edge.target = cell) →
      i64Min ≤ diffDistance potential cell - diffDistance potential 0 ∧
        diffDistance potential cell - diffDistance potential 0 ≤ i64Max

/-- Version 6 deliberately accepts only the literal-RHS fragment emitted by Rust: every normalized
    edge is in bounds and anchored at arithmetic zero. Unsupported cell-to-cell forms fail closed
    during quantitative well-formedness checking. -/
def DifferenceEdgeShape (p : Program) : Prop :=
  ∀ edge ∈ quantitativeEdges p,
    edge.source.toNat < p.nodes.size + 1 ∧ edge.target.toNat < p.nodes.size + 1 ∧
      (edge.source = 0 ∨ edge.target = 0)

/-- Every referenced nonzero cell carries the two implicit i64-domain edges. -/
def DifferenceI64EdgesComplete (p : Program) : Prop :=
  ∀ cell : UInt32, cell ≠ 0 →
    (∃ edge ∈ quantitativeEdges p, edge.source = cell ∨ edge.target = cell) →
      ({ source := cell, target := 0, weight := -i64Min } : DiffEdge) ∈ quantitativeEdges p ∧
        ({ source := 0, target := cell, weight := i64Max } : DiffEdge) ∈ quantitativeEdges p

def V6DifferenceWellFormed (p : Program) : Prop :=
  DifferenceEdgeShape p ∧ DifferenceI64EdgesComplete p

/-- Canonical CSIR record numbering.  The decoder enforces this while reading every record; the
    explicit proposition lets the metatheory use that wire invariant without trusting array
    lookup coincidences. -/
def CanonicalNodeIds (p : Program) : Prop :=
  ∀ index (hindex : index < p.nodes.toList.length),
    p.nodes.toList[index].nodeId.toNat = index + 1

private theorem canonical_node_id_bound {p : Program} (hcanonical : CanonicalNodeIds p)
    {n : Node} (hn : n ∈ p.nodes.toList) : n.nodeId.toNat < p.nodes.size + 1 := by
  obtain ⟨index, hindex, hnode⟩ := List.mem_iff_getElem.mp hn
  subst n
  rw [hcanonical index hindex]
  have hindex' : index < p.nodes.size := by simpa using hindex
  omega

/-- Canonical, quantitatively well-formed v6 records generate only in-bounds zero-anchored
    difference edges.  This discharges `DifferenceEdgeShape` from the executable node grammar. -/
theorem difference_edge_shape_of_nodes {p : Program} (hcanonical : CanonicalNodeIds p)
    (hwell : ∀ n ∈ p.nodes.toList, quantitativeNodeWellFormed p n = true) :
    DifferenceEdgeShape p := by
  intro edge hedge
  obtain ⟨node, hnode, hedgeNode⟩ := List.mem_flatMap.mp hedge
  have hnodeId := canonical_node_id_bound hcanonical hnode
  have hnodeWell := hwell node hnode
  cases hop : node.op <;>
    simp only [quantitativeEdgesForNode, hop] at hedgeNode
  all_goals try contradiction
  case intCell =>
    rw [quantitativeNodeWellFormed, hop] at hnodeWell
    unfold intCellWellFormed at hnodeWell
    simp only [Bool.and_eq_true] at hnodeWell
    have hactual : node.actual = node.nodeId := by
      simpa using hnodeWell.1.1.1.1.2
    rw [← hactual] at hnodeId
    split at hedgeNode
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hedgeNode
      rcases hedgeNode with rfl | rfl | rfl | rfl <;> simp_all
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hedgeNode
      rcases hedgeNode with rfl | rfl <;> simp_all
  case diffLe =>
    rw [quantitativeNodeWellFormed, hop] at hnodeWell
    unfold diffNodeWellFormed at hnodeWell
    simp only [Bool.and_eq_true] at hnodeWell
    have horigin : (node.origin == 0 || priorIntCell p node.nodeId node.origin) = true :=
      hnodeWell.1.1.2
    have hactual : (node.actual == 0 || priorIntCell p node.nodeId node.actual) = true :=
      hnodeWell.1.2
    have hanchor : (node.origin == 0 || node.actual == 0) = true := hnodeWell.2
    simp only [List.mem_singleton] at hedgeNode
    subst edge
    have originBound : node.origin.toNat < p.nodes.size + 1 := by
      by_cases hzero : node.origin = 0
      · simp [hzero]
      · have hprior : priorIntCell p node.nodeId node.origin = true := by
          simpa [hzero] using horigin
        unfold priorIntCell at hprior
        simp only [Bool.and_eq_true] at hprior
        have hlt : node.origin < node.nodeId := by simpa using hprior.1.2
        have hltNat : node.origin.toNat < node.nodeId.toNat := by
          simpa [UInt32.lt_iff_toNat_lt] using hlt
        omega
    have actualBound : node.actual.toNat < p.nodes.size + 1 := by
      by_cases hzero : node.actual = 0
      · simp [hzero]
      · have hprior : priorIntCell p node.nodeId node.actual = true := by
          simpa [hzero] using hactual
        unfold priorIntCell at hprior
        simp only [Bool.and_eq_true] at hprior
        have hlt : node.actual < node.nodeId := by simpa using hprior.1.2
        have hltNat : node.actual.toNat < node.nodeId.toNat := by
          simpa [UInt32.lt_iff_toNat_lt] using hlt
        omega
    have hanchor' : node.origin = 0 ∨ node.actual = 0 := by simpa using hanchor
    exact ⟨actualBound, originBound, hanchor'.symm⟩

private theorem int_cell_of_prior {p : Program} {position cell : UInt32}
    (hprior : priorIntCell p position cell = true) :
    ∃ node ∈ p.nodes.toList, node.op = .intCell ∧ node.actual = cell := by
  have hnonzero : cell ≠ 0 := by
    unfold priorIntCell at hprior
    simp only [Bool.and_eq_true] at hprior
    simpa using hprior.1.1
  cases hlookup : nodeAt? p cell with
  | none =>
      unfold priorIntCell at hprior
      simp [hlookup] at hprior
  | some node =>
      have hlookupArray : p.nodes[cell.toNat - 1]? = some node := by
        unfold nodeAt? at hlookup
        simpa [hnonzero] using hlookup
      have hmemberArray : node ∈ p.nodes := Array.mem_of_getElem? hlookupArray
      have hkind : node.op = .intCell ∧ node.actual = cell := by
        unfold priorIntCell at hprior
        simp [hlookup] at hprior
        have hop : node.op = .intCell := by
          cases hOp : node.op <;> simp [hOp, Op.isIntCell] at hprior ⊢
        exact ⟨hop, hprior.2.2⟩
      exact ⟨node, by simpa using hmemberArray, hkind⟩

private theorem referenced_cell_is_int_cell {p : Program}
    (hwell : ∀ n ∈ p.nodes.toList, quantitativeNodeWellFormed p n = true)
    {cell : UInt32} (hne : cell ≠ 0)
    (href : ∃ edge ∈ quantitativeEdges p, edge.source = cell ∨ edge.target = cell) :
    ∃ node ∈ p.nodes.toList, node.op = .intCell ∧ node.actual = cell := by
  obtain ⟨edge, hedge, hreferences⟩ := href
  obtain ⟨node, hnode, hedgeNode⟩ := List.mem_flatMap.mp hedge
  have hnodeWell := hwell node hnode
  cases hop : node.op <;>
    simp only [quantitativeEdgesForNode, hop] at hedgeNode
  all_goals try contradiction
  case intCell =>
    rw [quantitativeNodeWellFormed, hop] at hnodeWell
    unfold intCellWellFormed at hnodeWell
    simp only [Bool.and_eq_true] at hnodeWell
    have hzeroNe : 0 ≠ cell := fun h => hne h.symm
    split at hedgeNode
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hedgeNode
      rcases hedgeNode with rfl | rfl | rfl | rfl
      all_goals
        rcases hreferences with hreference | hreference
        all_goals first
          | exact ⟨node, hnode, hop, hreference⟩
          | exact (hzeroNe hreference).elim
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hedgeNode
      rcases hedgeNode with rfl | rfl
      all_goals
        rcases hreferences with hreference | hreference
        all_goals first
          | exact ⟨node, hnode, hop, hreference⟩
          | exact (hzeroNe hreference).elim
  case diffLe =>
    rw [quantitativeNodeWellFormed, hop] at hnodeWell
    unfold diffNodeWellFormed at hnodeWell
    simp only [Bool.and_eq_true] at hnodeWell
    have horigin : (node.origin == 0 || priorIntCell p node.nodeId node.origin) = true :=
      hnodeWell.1.1.2
    have hactual : (node.actual == 0 || priorIntCell p node.nodeId node.actual) = true :=
      hnodeWell.1.2
    simp only [List.mem_singleton] at hedgeNode
    subst edge
    rcases hreferences with hcell | hcell
    · have hcell' : node.actual = cell := hcell
      have hprior : priorIntCell p node.nodeId node.actual = true := by
        simpa [hcell', hne] using hactual
      obtain ⟨intNode, hintNode, hkind⟩ := int_cell_of_prior hprior
      exact ⟨intNode, hintNode, hkind.1, hkind.2.trans hcell'⟩
    · have hcell' : node.origin = cell := hcell
      have hprior : priorIntCell p node.nodeId node.origin = true := by
        simpa [hcell', hne] using horigin
      obtain ⟨intNode, hintNode, hkind⟩ := int_cell_of_prior hprior
      exact ⟨intNode, hintNode, hkind.1, hkind.2.trans hcell'⟩

/-- Every nonzero cell mentioned by well-formed v6 difference records comes from an integer-cell
    record, hence its implicit i64 lower and upper edges are present. -/
theorem difference_i64_edges_complete_of_nodes {p : Program}
    (hwell : ∀ n ∈ p.nodes.toList, quantitativeNodeWellFormed p n = true) :
    DifferenceI64EdgesComplete p := by
  intro cell hne href
  obtain ⟨node, hnode, hkind, hactual⟩ := referenced_cell_is_int_cell hwell hne href
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨node, hnode, ?_⟩
    by_cases hflag : hasFlag node.flags 4 = true <;>
      simp [quantitativeEdgesForNode, hkind, hactual, hflag]
  · apply List.mem_flatMap.mpr
    refine ⟨node, hnode, ?_⟩
    by_cases hflag : hasFlag node.flags 4 = true <;>
      simp [quantitativeEdgesForNode, hkind, hactual, hflag]

/-- The v6 difference-logic side conditions used by classifier completeness follow from canonical
    record numbering and the same quantitative well-formedness predicate run by the verifier. -/
theorem v6_difference_well_formed_of_nodes {p : Program}
    (hcanonical : CanonicalNodeIds p)
    (hwell : ∀ n ∈ p.nodes.toList, quantitativeNodeWellFormed p n = true) :
    V6DifferenceWellFormed p :=
  ⟨difference_edge_shape_of_nodes hcanonical hwell,
    difference_i64_edges_complete_of_nodes hwell⟩

theorem difference_bounds_complete_of_edges {p : Program}
    (hedges : DifferenceI64EdgesComplete p) :
    ∀ potential, DifferencePotentialSatisfies p potential →
      DifferencePotentialWithinI64 p potential := by
  intro potential hpotential cell href
  by_cases hzero : cell = 0
  · subst hzero
    simp [i64Min, i64Max]
  · have href' : ∃ edge ∈ quantitativeEdges p,
        edge.source = cell ∨ edge.target = cell := by
      rcases href with href | href
      · exact (hzero href).elim
      · exact href
    obtain ⟨hlower, hupper⟩ := hedges cell hzero href'
    have hlowerSatisfied := hpotential
      { source := cell, target := 0, weight := -i64Min } hlower
    have hupperSatisfied := hpotential
      { source := 0, target := cell, weight := i64Max } hupper
    simp only at hlowerSatisfied hupperSatisfied
    constructor <;> omega

private theorem fold_diff_lower_le (edges : List DiffEdge) (cell : UInt32)
    (normalized : Int) (initial : Int) (hinitial : initial ≤ normalized)
    (hedges : ∀ edge ∈ edges,
      edge.source = cell → edge.target = 0 → -edge.weight ≤ normalized) :
    edges.foldl (fun lower edge =>
      if edge.source = cell ∧ edge.target = 0 then max lower (-edge.weight) else lower) initial ≤
        normalized := by
  induction edges generalizing initial with
  | nil => simpa using hinitial
  | cons edge rest ih =>
      simp only [List.foldl_cons]
      by_cases hs : edge.source = cell
      · by_cases ht : edge.target = 0
        · simp [hs, ht]
          apply ih (max initial (-edge.weight))
          · have hweight := hedges edge (by simp) hs ht
            exact Int.max_le.mpr ⟨hinitial, hweight⟩
          · intro candidate hcandidate
            exact hedges candidate (by simp [hcandidate])
        · simp [hs, ht]
          apply ih initial hinitial
          · intro candidate hcandidate
            exact hedges candidate (by simp [hcandidate])
      · simp [hs]
        apply ih initial hinitial
        · intro candidate hcandidate
          exact hedges candidate (by simp [hcandidate])

theorem diffLowerBoundFor_le_of_potential (edges : List DiffEdge) (cell : UInt32)
    (normalized : Int) (hmin : i64Min ≤ normalized)
    (hedges : ∀ edge ∈ edges,
      edge.source = cell → edge.target = 0 → -edge.weight ≤ normalized) :
    diffLowerBoundFor edges cell ≤ normalized := by
  exact fold_diff_lower_le edges cell normalized i64Min hmin hedges

private theorem initial_le_fold_diff_lower (edges : List DiffEdge) (cell : UInt32)
    (initial : Int) :
    initial ≤ edges.foldl (fun lower edge =>
      if edge.source = cell ∧ edge.target = 0 then max lower (-edge.weight) else lower) initial := by
  induction edges generalizing initial with
  | nil => exact Int.le_refl _
  | cons edge rest ih =>
      simp only [List.foldl_cons]
      by_cases hmatch : edge.source = cell ∧ edge.target = 0
      · rw [if_pos hmatch]
        exact Int.le_trans (Int.le_max_left _ _) (ih (max initial (-edge.weight)))
      · rw [if_neg hmatch]
        exact ih initial

private theorem fold_diff_lower_ge_edge (edges : List DiffEdge) (cell : UInt32)
    (initial : Int) (edge : DiffEdge) (hmember : edge ∈ edges)
    (hsource : edge.source = cell) (htarget : edge.target = 0) :
    -edge.weight ≤ edges.foldl (fun lower edge =>
      if edge.source = cell ∧ edge.target = 0 then max lower (-edge.weight) else lower) initial := by
  induction edges generalizing cell initial with
  | nil => simp at hmember
  | cons head rest ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmember with rfl | hrest
      · rw [if_pos ⟨hsource, htarget⟩]
        exact Int.le_trans (Int.le_max_right _ _)
          (initial_le_fold_diff_lower rest cell (max initial (-edge.weight)))
      · by_cases hmatch : head.source = cell ∧ head.target = 0
        · rw [if_pos hmatch]
          exact ih (cell := cell) (initial := max initial (-head.weight)) hrest hsource
        · rw [if_neg hmatch]
          exact ih (cell := cell) (initial := initial) hrest hsource

theorem diffLowerBoundFor_ge_edge (edges : List DiffEdge) (cell : UInt32)
    (edge : DiffEdge) (hmember : edge ∈ edges)
    (hsource : edge.source = cell) (htarget : edge.target = 0) :
    -edge.weight ≤ diffLowerBoundFor edges cell := by
  exact fold_diff_lower_ge_edge edges cell i64Min edge hmember hsource htarget

theorem intervalDiffDistances_size (p : Program) :
    (intervalDiffDistances p).size = p.nodes.size + 1 := by
  simp [intervalDiffDistances]

theorem intervalDiffDistances_zero (p : Program) :
    diffDistance (intervalDiffDistances p) 0 = 0 := by
  simp [diffDistance, intervalDiffDistances]

theorem intervalDiffDistances_cell (p : Program) (cell : UInt32)
    (hcell : cell.toNat < p.nodes.size + 1) (hne : cell ≠ 0) :
    diffDistance (intervalDiffDistances p) cell =
      diffLowerBoundFor (quantitativeEdges p) cell := by
  have hneNat : cell.toNat ≠ 0 := by
    intro hzero
    apply hne
    apply UInt32.toNat_inj.mp
    simpa using hzero
  simp [diffDistance, intervalDiffDistances, hcell, hneNat]

/-- The canonical lower-bound potential satisfies every constraint whenever any i64 potential
    satisfies the accepted zero-anchored fragment. -/
theorem interval_difference_potential {p : Program} {potential : Array Int}
    (hshape : DifferenceEdgeShape p)
    (hpotential : DifferencePotentialSatisfies p potential)
    (hi64 : DifferencePotentialWithinI64 p potential) :
    DifferencePotentialSatisfies p (intervalDiffDistances p) := by
  intro edge hedge
  obtain ⟨hsourceBound, htargetBound, hzero⟩ := hshape edge hedge
  rcases hzero with hsourceZero | htargetZero
  · by_cases htargetIsZero : edge.target = 0
    · have hold := hpotential edge hedge
      rw [hsourceZero, htargetIsZero] at hold
      rw [hsourceZero, htargetIsZero, intervalDiffDistances_zero]
      omega
    · rw [hsourceZero, intervalDiffDistances_zero,
        intervalDiffDistances_cell p edge.target htargetBound htargetIsZero]
      let normalized := diffDistance potential edge.target - diffDistance potential 0
      have hnormalizedMin : i64Min ≤ normalized := by
        exact (hi64 edge.target (Or.inr ⟨edge, hedge, Or.inr rfl⟩)).1
      have hlower : diffLowerBoundFor (quantitativeEdges p) edge.target ≤ normalized := by
        apply diffLowerBoundFor_le_of_potential _ _ normalized hnormalizedMin
        intro lowerEdge hlowerEdge hlowerSource hlowerTarget
        have hsatisfied := hpotential lowerEdge hlowerEdge
        rw [hlowerSource, hlowerTarget] at hsatisfied
        dsimp [normalized]
        omega
      have hupper := hpotential edge hedge
      rw [hsourceZero] at hupper
      dsimp [normalized] at hlower
      omega
  · by_cases hsourceIsZero : edge.source = 0
    · have hold := hpotential edge hedge
      rw [hsourceIsZero, htargetZero] at hold
      rw [hsourceIsZero, htargetZero, intervalDiffDistances_zero]
      omega
    · rw [htargetZero, intervalDiffDistances_zero,
        intervalDiffDistances_cell p edge.source hsourceBound hsourceIsZero]
      have hlower := diffLowerBoundFor_ge_edge
        (quantitativeEdges p) edge.source edge hedge rfl htargetZero
      omega

theorem difference_classifier_sound_at_computed_potential {p : Program}
    (h : differenceConsistent p = true) :
    DifferencePotentialSatisfies p (settledDiffDistances p) := by
  intro edge hedge
  unfold differenceConsistent at h
  by_cases hempty : (quantitativeEdges p).isEmpty = true
  · have : quantitativeEdges p = [] := List.isEmpty_iff.mp hempty
    simp [this] at hedge
  · have hall : (quantitativeEdges p).all
        (diffEdgeSatisfied (settledDiffDistances p)) = true := by
      simpa [hempty] using h
    have hsatisfied := (List.all_eq_true.mp hall) edge hedge
    simpa [diffEdgeSatisfied] using hsatisfied

theorem difference_classifier_sound {p : Program} (h : differenceConsistent p = true) :
    ∃ potential, DifferencePotentialSatisfies p potential :=
  ⟨settledDiffDistances p, difference_classifier_sound_at_computed_potential h⟩

/-- Completeness against arbitrary satisfying potentials for the exact v6 wire fragment. The
    well-formedness premise names both the implicit i64 edges and the canonical, zero-anchored
    edge shape; `v6_difference_well_formed_of_nodes` derives it from verifier predicates. -/
theorem difference_classifier_complete {p : Program} (hwell : V6DifferenceWellFormed p)
    (h : ∃ potential, DifferencePotentialSatisfies p potential) :
    differenceConsistent p = true := by
  obtain ⟨potential, hpotential⟩ := h
  have hinterval := interval_difference_potential hwell.1 hpotential
    (difference_bounds_complete_of_edges hwell.2 potential hpotential)
  unfold differenceConsistent settledDiffDistances
  by_cases hempty : (quantitativeEdges p).isEmpty = true
  · simp [hempty]
  · simp only [hempty, Bool.false_eq_true, ↓reduceIte]
    by_cases hbellman : (quantitativeEdges p).all
        (diffEdgeSatisfied (bellmanFordDiffDistances p)) = true
    · simp [hbellman]
    · simp only [hbellman, Bool.false_eq_true, ↓reduceIte]
      apply List.all_eq_true.mpr
      intro edge hedge
      simpa [diffEdgeSatisfied] using hinterval edge hedge

theorem difference_classifier_sound_and_complete {p : Program}
    (hwell : V6DifferenceWellFormed p) :
    differenceConsistent p = true ↔
      ∃ potential, DifferencePotentialSatisfies p potential :=
  ⟨difference_classifier_sound, difference_classifier_complete hwell⟩

/-- Load-bearing form of classifier correctness: canonical decoded record numbering plus the
    executable quantitative node checks are sufficient to obtain full soundness and completeness
    for the supported v6 literal-RHS fragment. -/
theorem difference_classifier_sound_and_complete_of_nodes {p : Program}
    (hcanonical : CanonicalNodeIds p)
    (hwell : ∀ n ∈ p.nodes.toList, quantitativeNodeWellFormed p n = true) :
    differenceConsistent p = true ↔
      ∃ potential, DifferencePotentialSatisfies p potential :=
  difference_classifier_sound_and_complete
    (v6_difference_well_formed_of_nodes hcanonical hwell)

theorem difference_classifier_complete_at_computed_potential {p : Program}
    (h : DifferencePotentialSatisfies p (settledDiffDistances p)) :
    differenceConsistent p = true := by
  unfold differenceConsistent
  by_cases hempty : (quantitativeEdges p).isEmpty = true
  · simp [hempty]
  · simp only [hempty, Bool.false_eq_true, ↓reduceIte]
    apply List.all_eq_true.mpr
    intro edge hedge
    simpa [diffEdgeSatisfied] using h edge hedge

theorem difference_classifier_sound_and_complete_at_computed_potential {p : Program} :
    differenceConsistent p = true ↔
      DifferencePotentialSatisfies p (settledDiffDistances p) :=
  ⟨difference_classifier_sound_at_computed_potential,
    difference_classifier_complete_at_computed_potential⟩

/-- Abstract result of the two runtime checks attached to a quantitative capability operation.
    A trap carries no child and therefore cannot change either balance. -/
inductive QuantityTransition where
  | trap
  | success (parent child : Nat)
  deriving Repr, BEq, DecidableEq

/-- Guarded split/draw semantics.  Signed negativity is checked before conversion; balance is
    checked before subtraction or child construction. -/
def guardedQuantityTransition (parent : Nat) (amount : Int) : QuantityTransition :=
  if amount < 0 then .trap
  else if amount.toNat ≤ parent then .success (parent - amount.toNat) amount.toNat else .trap

theorem guarded_quantity_negative_traps {parent : Nat} {amount : Int} (h : amount < 0) :
    guardedQuantityTransition parent amount = .trap := by
  simp [guardedQuantityTransition, h]

theorem guarded_quantity_insufficient_traps {parent : Nat} {amount : Int}
    (hn : 0 ≤ amount) (hi : parent < amount.toNat) :
    guardedQuantityTransition parent amount = .trap := by
  simp [guardedQuantityTransition, Int.not_lt.mpr hn, Nat.not_le.mpr hi]

theorem guarded_quantity_success_conserves {parent parent' child : Nat} {amount : Int}
    (h : guardedQuantityTransition parent amount = .success parent' child) :
    parent' + child = parent := by
  unfold guardedQuantityTransition at h
  split at h
  · contradiction
  · split at h
    · simp_all
      omega
    · contradiction

theorem guarded_quantity_success_exact {parent parent' child : Nat} {amount : Int}
    (h : guardedQuantityTransition parent amount = .success parent' child) :
    child = amount.toNat ∧ parent' = parent - amount.toNat := by
  unfold guardedQuantityTransition at h
  split at h
  · contradiction
  · split at h
    · injection h with hp hc
      exact ⟨hc.symm, hp.symm⟩
    · contradiction

theorem quantitative_judgment_requires_both_guards {p : Program} (h : QuantitativeJudgment p)
    {n : Node} (hn : n ∈ p.nodes.toList) (hop : n.op = .quantityUse) :
    hasFlag n.flags 0x01 = true ∧ hasFlag n.flags 0x02 = true := by
  have hw := h.1 n hn
  rw [quantitativeNodeWellFormed, hop] at hw
  unfold quantityNodeWellFormed at hw
  by_cases hf : n.flags = 0x03
  · simpa [hf] using (show hasFlag (0x03 : UInt8) 0x01 = true ∧
        hasFlag (0x03 : UInt8) 0x02 = true by decide)
  · simp [hf] at hw

/-- Declarative structural and policy judgment for the production v8 semantic envelope. -/
def SemanticEnvelopeJudgment (p : Program) : Prop :=
  (semanticProgramNode? p).isSome = true ∧ firstSemanticViolation p = none ∧
    firstSemanticMetadataViolation p = none ∧ firstV8SecurityViolation p = none ∧
      Semantic.RawRelationalStaticSafe (Semantic.semanticProgramOf p)

def CoreCSIRJudgment (p : Program) : Prop :=
  (∀ n ∈ p.nodes.toList, nodeSafe n = true) ∧ AffineSafe p ∧
    CapabilityJudgment p ∧ QuantitativeJudgment p ∧ PathAffineJudgment p ∧ TaintGraphJudgment p

/-- Declarative judgment used to state decision-procedure correctness. -/
def CSIRJudgment (p : Program) : Prop := SemanticEnvelopeJudgment p ∧ CoreCSIRJudgment p

def SemanticNodeSecure (p : Program) (index : SemanticIndex) (labels : Array Label)
    (n : Node) : Prop :=
  (match n.op with
    | .semPolicyClass => semanticPolicyViolation p index labels n
    | .semLabelContract => semanticContractViolation index labels n
    | .semInstruction =>
        match semanticInstructionFlowViolation p index labels n with
        | some violation => some violation
        | none =>
            match semanticInstructionCapabilityViolation p index n with
            | some violation => some violation
            | none => semanticRawSecretCTViolation p index labels n
    | _ => none) = none

/-- Algorithm-independent statement of the v8 static policy. Structural decoding remains a
    separate premise; metadata completeness and every semantic security condition are quantified
    over the decoded records rather than phrased as an aggregate verifier result. -/
def V8SecurityJudgment (p : Program) : Prop :=
  (semanticProgramNode? p).isSome = true ∧ firstSemanticViolation p = none ∧
    (∀ n ∈ p.nodes.toList,
      semanticMetadataCompleteNode p (buildSemanticIndex p) n = true) ∧
    (∀ n ∈ p.nodes.toList,
      SemanticNodeSecure p (buildSemanticIndex p) (semanticLabels p) n) ∧
    Semantic.RawRelationalStaticSafe (Semantic.semanticProgramOf p)

private theorem firstSemanticMetadata_none_iff (p : Program) (index : SemanticIndex)
    (nodes : List Node) :
    firstSemanticMetadataViolationList p index nodes = none ↔
      ∀ n ∈ nodes, semanticMetadataCompleteNode p index n = true := by
  induction nodes with
  | nil => simp [firstSemanticMetadataViolationList]
  | cons head tail ih =>
      cases hs : semanticMetadataCompleteNode p index head <;>
        simp [firstSemanticMetadataViolationList, hs, ih]

private theorem firstV8Security_none_iff (p : Program) (index : SemanticIndex)
    (labels : Array Label) (nodes : List Node) :
    firstV8SecurityViolationList p index labels nodes = none ↔
      ∀ n ∈ nodes, SemanticNodeSecure p index labels n := by
  induction nodes with
  | nil => simp [firstV8SecurityViolationList]
  | cons head tail ih =>
      cases hop : head.op <;>
        simp [firstV8SecurityViolationList, SemanticNodeSecure, hop, ih]
      case semInstruction =>
        cases hv : semanticInstructionFlowViolation p index labels head with
        | some violation => simp
        | none =>
          cases hc : semanticInstructionCapabilityViolation p index head with
          | some violation => simp
          | none =>
            cases hr : semanticRawSecretCTViolation p index labels head <;>
              simp [ih, SemanticNodeSecure]
      case semLabelContract =>
        cases hv : semanticContractViolation index labels head <;>
          simp [ih, SemanticNodeSecure]
      case semPolicyClass =>
        cases hv : semanticPolicyViolation p index labels head <;>
          simp [ih, SemanticNodeSecure]

/-- The production v8 semantic decision procedure is sound and complete for the declarative
    `V8SecurityJudgment`. Completeness is intentionally relative to this static judgment. -/
theorem v8_semantic_verifier_sound_and_complete {p : Program} :
    ((semanticProgramNode? p).isSome = true ∧ firstSemanticViolation p = none ∧
      firstSemanticMetadataViolation p = none ∧ firstV8SecurityViolation p = none ∧
        Semantic.rawRelationalStaticSafeB (Semantic.semanticProgramOf p) = true) ↔
      V8SecurityJudgment p := by
  unfold V8SecurityJudgment firstSemanticMetadataViolation firstV8SecurityViolation
  rw [firstSemanticMetadata_none_iff]
  rw [firstV8Security_none_iff]
  rw [Semantic.rawRelationalStaticSafeB_iff]

private theorem graphViolation_none_iff (p : Program) (labels : Array Label) (n : Node) :
    graphViolation p labels n = none ↔
      graphNodeWellFormed p n = true ∧ graphNodeSafe labels n = true := by
  unfold graphViolation
  cases hw : graphNodeWellFormed p n with
  | false => simp
  | true =>
      cases hs : graphNodeSafe labels n with
      | true => simp
      | false => cases n.op <;> simp

private theorem firstGraph_none_sound (p : Program) (labels : Array Label) {nodes : List Node}
    (h : firstGraphViolationList p labels nodes = none) :
    ∀ n ∈ nodes, graphNodeWellFormed p n = true ∧ graphNodeSafe labels n = true := by
  induction nodes with
  | nil => simp
  | cons head tail ih =>
      cases hv : graphViolation p labels head with
      | some violation => simp [firstGraphViolationList, hv] at h
      | none =>
          have hhead := (graphViolation_none_iff p labels head).mp hv
          have htail : firstGraphViolationList p labels tail = none := by
            simpa [firstGraphViolationList, hv] using h
          intro n hn
          simp only [List.mem_cons] at hn
          rcases hn with heq | hn
          · simpa [heq] using hhead
          · exact ih htail n hn

private theorem firstGraph_none_complete (p : Program) (labels : Array Label)
    {nodes : List Node}
    (h : ∀ n ∈ nodes,
      graphNodeWellFormed p n = true ∧ graphNodeSafe labels n = true) :
    firstGraphViolationList p labels nodes = none := by
  induction nodes with
  | nil => rfl
  | cons head tail ih =>
      have hhead := h head (by simp)
      have hnone : graphViolation p labels head = none :=
        (graphViolation_none_iff p labels head).mpr hhead
      have htail : ∀ n ∈ tail,
          graphNodeWellFormed p n = true ∧ graphNodeSafe labels n = true := by
        intro n hn
        exact h n (by simp [hn])
      simp [firstGraphViolationList, hnone, ih htail]

private theorem labelsBelowCellsBool_iff (n : Nat) (a b : Array Label) :
    labelsBelowCellsBool n a b = true ↔ LabelsBelowCells n a b := by
  simp [labelsBelowCellsBool, LabelsBelowCells, List.all_eq_true]
  tauto

private theorem graphComputedSolutionSafe_iff (p : Program) (labels : Array Label) :
    graphComputedSolutionSafe p labels = true ↔ TaintSolution p labels := by
  simp [graphComputedSolutionSafe, TaintSolution, labelsBelowCellsBool_iff,
    adjacencyCellSafeWith, List.all_eq_true]
  tauto

theorem graph_verifier_sound {p : Program} (h : firstGraphViolation p = none) :
    TaintGraphJudgment p := by
  unfold firstGraphViolation at h
  cases hv : firstGraphViolationList p (graphLabels p) p.nodes.toList with
  | some violation => simp [hv] at h
  | none =>
      have hs : graphComputedSolutionSafe p (graphLabels p) = true := by
        cases hc : graphComputedSolutionSafe p (graphLabels p) <;> simp [hv, hc] at h ⊢
      exact ⟨firstGraph_none_sound p (graphLabels p) hv,
        (graphComputedSolutionSafe_iff p (graphLabels p)).mp hs⟩

theorem graph_verifier_complete {p : Program} (h : TaintGraphJudgment p) :
    firstGraphViolation p = none := by
  have hn := firstGraph_none_complete p (graphLabels p) h.1
  have hs := (graphComputedSolutionSafe_iff p (graphLabels p)).mpr h.2
  simp [firstGraphViolation, hn, hs]

theorem graph_verifier_sound_and_complete {p : Program} :
    firstGraphViolation p = none ↔ TaintGraphJudgment p :=
  ⟨graph_verifier_sound, graph_verifier_complete⟩

private theorem label_lub_below {a b c : Label} (ha : a.flowsTo c = true)
    (hb : b.flowsTo c = true) : (a.lub b).flowsTo c = true := by
  cases a <;> cases b <;> cases c <;>
    simp_all [Label.flowsTo, Label.lub, Label.rank]

private theorem label_below_trans {a b c : Label} (ha : a.flowsTo b = true)
    (hb : b.flowsTo c = true) : a.flowsTo c = true := by
  cases a <;> cases b <;> cases c <;>
    simp_all [Label.flowsTo, Label.rank]

theorem label_rank_at_most_three (label : Label) : label.rank ≤ 3 := by
  cases label <;> decide

theorem strict_label_rise_decreases_remaining_budget {old raised : Label}
    (h : old.rank < raised.rank) : 3 - raised.rank < 3 - old.rank := by
  have hold := label_rank_at_most_three old
  have hraised := label_rank_at_most_three raised
  omega

theorem initial_work_plus_all_possible_reenqueues (cellCount : Nat) :
    cellCount + 3 * cellCount = 4 * cellCount := by omega

private theorem labelsBelowCells_at {count : Nat} {lower upper : Array Label}
    (h : LabelsBelowCells count lower upper) (cell : UInt32) (hc : cell.toNat < count) :
    (labelAt lower cell).flowsTo (labelAt upper cell) = true := by
  simpa using h.2.2 cell.toNat hc

private theorem labelsBelowCells_set {count : Nat} {lower upper : Array Label}
    (h : LabelsBelowCells count lower upper) (cell : UInt32) (raised : Label)
    (hcount : count ≤ maxNodes + 1) (_hc : cell.toNat < count)
    (hr : raised.flowsTo (labelAt upper cell) = true) :
    LabelsBelowCells count (lower.setIfInBounds cell.toNat raised) upper := by
  refine ⟨by simpa using h.1, h.2.1, ?_⟩
  intro observed hobserved
  have hsmall : observed < 2 ^ 32 := by
    have : maxNodes + 1 < 2 ^ 32 := by decide
    omega
  have hpow : 2 ^ 32 = 4294967296 := by decide
  have hsmall' : observed < 4294967296 := by simpa [hpow] using hsmall
  have hmod : observed % 4294967296 = observed := Nat.mod_eq_of_lt hsmall'
  have hbound : observed < lower.size := by simpa [h.1] using hobserved
  have hget := Array.getElem_setIfInBounds (xs := lower) (i := cell.toNat)
    (a := raised) (j := observed) hbound
  by_cases he : cell.toNat = observed
  · have hcell : UInt32.ofNat observed = cell := by
      apply UInt32.ext
      simp [hmod, he]
    simpa [labelAt, Array.getD, Array.size_setIfInBounds, hbound, hget, he, hcell,
      hmod] using hr
  · simpa [labelAt, Array.getD, Array.size_setIfInBounds, hbound, hget, he, hmod]
      using h.2.2 observed hobserved

private theorem relaxTargets_below_solution {count : Nat} {sourceCell : UInt32}
    {sourceLabel : Label} {targets : List UInt32} {labels solution : Array Label}
    {work : List UInt32} (hcount : count ≤ maxNodes + 1)
    (hbelow : LabelsBelowCells count labels solution)
    (hsource : sourceLabel.flowsTo (labelAt solution sourceCell) = true)
    (hedges : ∀ target ∈ targets, target.toNat < count ∧
      (labelAt solution sourceCell).flowsTo (labelAt solution target) = true) :
    LabelsBelowCells count (relaxTargets sourceLabel targets labels work).1 solution := by
  induction targets generalizing labels work with
  | nil => simpa [relaxTargets] using hbelow
  | cons target rest ih =>
      have hedge := hedges target (by simp)
      have hold := labelsBelowCells_at hbelow target hedge.1
      have hsTarget := label_below_trans hsource hedge.2
      have hraised : ((labelAt labels target).lub sourceLabel).flowsTo
          (labelAt solution target) = true := label_lub_below hold hsTarget
      have hrest : ∀ candidate ∈ rest, candidate.toNat < count ∧
          (labelAt solution sourceCell).flowsTo (labelAt solution candidate) = true := by
        intro candidate hc
        exact hedges candidate (by simp [hc])
      simp only [relaxTargets]
      by_cases heq : ((labelAt labels target).lub sourceLabel).eqb
          (labelAt labels target) = true
      · simp [heq]
        exact ih hbelow hrest
      · simp [heq]
        exact ih (labelsBelowCells_set hbelow target _ hcount hedge.1 hraised) hrest

def WorkCellsValid (count : Nat) (work : List UInt32) : Prop :=
  ∀ cell ∈ work, cell.toNat < count

private theorem relaxTargets_preserves_work_valid {count : Nat} {source : Label}
    {targets work : List UInt32} {labels : Array Label} (hw : WorkCellsValid count work)
    (ht : ∀ target ∈ targets, target.toNat < count) :
    WorkCellsValid count (relaxTargets source targets labels work).2 := by
  induction targets generalizing labels work with
  | nil => simpa [relaxTargets] using hw
  | cons target rest ih =>
      have htarget := ht target (by simp)
      have hrest : ∀ candidate ∈ rest, candidate.toNat < count := by
        intro candidate hc
        exact ht candidate (by simp [hc])
      simp only [relaxTargets]
      by_cases heq : ((labelAt labels target).lub source).eqb (labelAt labels target) = true
      · simp [heq]
        exact ih hw hrest
      · simp [heq]
        apply ih _ hrest
        intro cell hc
        simp only [List.mem_cons] at hc
        exact hc.elim (fun he => he ▸ htarget) (hw cell)

private theorem saturateGraphWorklist_below_solution {p : Program}
    {solution labels : Array Label} {fuel : Nat} {work : List UInt32}
    (hsize : p.nodes.size + 1 ≤ maxNodes + 1)
    (hbelow : LabelsBelowCells (p.nodes.size + 1) labels solution)
    (hw : WorkCellsValid (p.nodes.size + 1) work)
    (hedges : ∀ source < p.nodes.size + 1, ∀ target,
      target ∈ (graphAdjacency p).getD source [] →
        target.toNat < p.nodes.size + 1 ∧
          (labelAt solution (UInt32.ofNat source)).flowsTo
            (labelAt solution target) = true) :
    LabelsBelowCells (p.nodes.size + 1)
      (saturateGraphWorklist (graphAdjacency p) fuel work labels) solution := by
  induction fuel generalizing work labels with
  | zero => simpa [saturateGraphWorklist] using hbelow
  | succ fuel ih =>
      cases work with
      | nil => simpa [saturateGraphWorklist] using hbelow
      | cons cell rest =>
          have hcell : cell.toNat < p.nodes.size + 1 := hw cell (by simp)
          have hsource := labelsBelowCells_at hbelow cell hcell
          have htargets := hedges cell.toNat hcell
          have hcellEq : UInt32.ofNat cell.toNat = cell := by simp
          have htargets' : ∀ target ∈ (graphAdjacency p).getD cell.toNat [],
              target.toNat < p.nodes.size + 1 ∧
                (labelAt solution cell).flowsTo (labelAt solution target) = true := by
            simpa [hcellEq] using htargets
          have hbelow' := relaxTargets_below_solution (work := rest) hsize hbelow
            hsource htargets'
          have hwrest : WorkCellsValid (p.nodes.size + 1) rest := by
            intro candidate hc
            exact hw candidate (by simp [hc])
          have hw' := relaxTargets_preserves_work_valid (source := labelAt labels cell)
            (labels := labels) hwrest (fun target ht => (htargets target ht).1)
          simpa [saturateGraphWorklist] using ih hbelow' hw'

/-- The linked worklist result is pointwise below every algorithm-independent solution.  Combined
    with the executable post-fixpoint check in `TaintGraphJudgment`, this is the least-solution
    characterization used by the joint theorem. -/
theorem graphLabels_least {p : Program} {solution : Array Label}
    (hsolution : TaintSolution p solution) :
    LabelsBelowCells (p.nodes.size + 1) (graphLabels p) solution := by
  unfold graphLabels
  apply saturateGraphWorklist_below_solution (by
    have hp := hsolution.1
    omega) hsolution.2.1
  · intro cell hc
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨source, hs, rfl⟩ := hc
    have hsmall : source < 4294967296 := by
      have : maxNodes + 1 < 4294967296 := by decide
      have hp := hsolution.1
      omega
    simpa [Nat.mod_eq_of_lt hsmall] using hs
  · exact hsolution.2.2

theorem graphLabels_is_least_solution {p : Program} (h : TaintGraphJudgment p) :
    TaintSolution p (graphLabels p) ∧
      ∀ candidate, TaintSolution p candidate →
        LabelsBelowCells (p.nodes.size + 1) (graphLabels p) candidate := by
  exact ⟨h.2, fun candidate hcandidate => graphLabels_least hcandidate⟩

private theorem capabilityViolation_none_iff (p : Program) (states : Array CapState) (n : Node) :
    capabilityViolation p states n = none ↔
      capNodeWellFormed p n = true ∧ capNodeSafe states n = true := by
  unfold capabilityViolation
  cases hw : capNodeWellFormed p n with
  | false => simp
  | true =>
      cases hs : capNodeSafe states n with
      | true => simp
      | false => cases n.op <;> simp

private theorem firstCapability_none_sound (p : Program) (states : Array CapState)
    {nodes : List Node} (h : firstCapabilityViolationList p states nodes = none) :
    CapabilityJudgmentFrom p states nodes := by
  induction nodes generalizing states with
  | nil => trivial
  | cons head tail ih =>
      cases hv : capabilityViolation p states head with
      | some violation => simp [firstCapabilityViolationList, hv] at h
      | none =>
          have hhead := (capabilityViolation_none_iff p states head).mp hv
          have htail : firstCapabilityViolationList p (applyCapabilityNode states head) tail =
              none := by
            simpa [firstCapabilityViolationList, hv] using h
          exact ⟨hhead.1, hhead.2, ih _ htail⟩

private theorem firstCapability_none_complete (p : Program) (states : Array CapState)
    {nodes : List Node} (h : CapabilityJudgmentFrom p states nodes) :
    firstCapabilityViolationList p states nodes = none := by
  induction nodes generalizing states with
  | nil => rfl
  | cons head tail ih =>
      have hnone : capabilityViolation p states head = none :=
        (capabilityViolation_none_iff p states head).mpr ⟨h.1, h.2.1⟩
      simp [firstCapabilityViolationList, hnone]
      exact ih _ h.2.2

theorem capability_verifier_sound {p : Program} (h : firstCapabilityViolation p = none) :
    CapabilityJudgment p := by
  exact firstCapability_none_sound p (emptyCapStates p)
    (by simpa [firstCapabilityViolation] using h)

theorem capability_verifier_complete {p : Program} (h : CapabilityJudgment p) :
    firstCapabilityViolation p = none := by
  exact firstCapability_none_complete p (emptyCapStates p) h

theorem capability_verifier_sound_and_complete {p : Program} :
    firstCapabilityViolation p = none ↔ CapabilityJudgment p :=
  ⟨capability_verifier_sound, capability_verifier_complete⟩

private theorem firstQuantitativeMalformed_none_iff (p : Program) (nodes : List Node) :
    firstQuantitativeMalformed p nodes = none ↔
      ∀ n ∈ nodes, quantitativeNodeWellFormed p n = true := by
  induction nodes with
  | nil => simp [firstQuantitativeMalformed]
  | cons head tail ih =>
      cases hw : quantitativeNodeWellFormed p head <;>
        simp [firstQuantitativeMalformed, hw, ih]

theorem quantitative_verifier_sound {p : Program} (h : firstQuantitativeViolation p = none) :
    QuantitativeJudgment p := by
  unfold firstQuantitativeViolation at h
  cases hm : firstQuantitativeMalformed p p.nodes.toList with
  | some violation => simp [hm] at h
  | none =>
      have hnodes := (firstQuantitativeMalformed_none_iff p p.nodes.toList).mp hm
      cases hc : differenceConsistent p with
      | false => simp [hm, hc] at h
      | true => exact ⟨hnodes, hc⟩

theorem quantitative_verifier_complete {p : Program} (h : QuantitativeJudgment p) :
    firstQuantitativeViolation p = none := by
  have hm : firstQuantitativeMalformed p p.nodes.toList = none :=
    (firstQuantitativeMalformed_none_iff p p.nodes.toList).mpr h.1
  simp [firstQuantitativeViolation, hm, h.2]

theorem quantitative_verifier_sound_and_complete {p : Program} :
    firstQuantitativeViolation p = none ↔ QuantitativeJudgment p :=
  ⟨quantitative_verifier_sound, quantitative_verifier_complete⟩

private theorem firstPathAffine_none_iff (state : PathAffineState) (nodes : List Node) :
    firstPathAffineViolationList state nodes = none ↔ PathAffineJudgmentFrom state nodes := by
  induction nodes generalizing state with
  | nil => simp [firstPathAffineViolationList, PathAffineJudgmentFrom]
  | cons head tail ih =>
      cases hv : pathAffineViolation state head with
      | some violation => simp [firstPathAffineViolationList, PathAffineJudgmentFrom, hv]
      | none => simp [firstPathAffineViolationList, PathAffineJudgmentFrom, hv, ih]

theorem path_affine_verifier_sound {p : Program} (h : firstPathAffineViolation p = none) :
    PathAffineJudgment p := by
  exact (firstPathAffine_none_iff (emptyPathAffineState p) p.nodes.toList).mp
    (by simpa [firstPathAffineViolation] using h)

theorem path_affine_verifier_complete {p : Program} (h : PathAffineJudgment p) :
    firstPathAffineViolation p = none := by
  exact (firstPathAffine_none_iff (emptyPathAffineState p) p.nodes.toList).mpr h

theorem path_affine_verifier_sound_and_complete {p : Program} :
    firstPathAffineViolation p = none ↔ PathAffineJudgment p :=
  ⟨path_affine_verifier_sound, path_affine_verifier_complete⟩

private theorem localViolation_none_iff (n : Node) :
    localViolation n = none ↔ nodeSafe n = true := by
  cases hs : nodeSafe n with
  | true => simp [localViolation, hs]
  | false =>
      cases hop : n.op <;> simp [localViolation, hs, hop]
      case authority =>
        by_cases hf : hasFlag n.flags 1 = true <;> simp [hf]
      case fixedCT => simp [nodeSafe, hop] at hs
      case taintSeed => simp [nodeSafe, hop] at hs
      case taintEdge => simp [nodeSafe, hop] at hs
      case taintSink => simp [nodeSafe, hop] at hs
      case taintCtUse => simp [nodeSafe, hop] at hs
      case taintRelease => simp [nodeSafe, hop] at hs
      case capOrigin => simp [nodeSafe, hop] at hs
      case capRestrict => simp [nodeSafe, hop] at hs
      case capSplit => simp [nodeSafe, hop] at hs
      case capDraw => simp [nodeSafe, hop] at hs
      case capSink => simp [nodeSafe, hop] at hs
      case capRelease => simp [nodeSafe, hop] at hs
      case capSlot => simp [nodeSafe, hop] at hs
      case capSlotPut => simp [nodeSafe, hop] at hs
      case capSlotTake => simp [nodeSafe, hop] at hs
      case capMeet => simp [nodeSafe, hop] at hs
      case semLabelContract => simp [nodeSafe, hop] at hs
      case semCapabilityType => simp [nodeSafe, hop] at hs
      case semPolicyClass => simp [nodeSafe, hop] at hs
      case semRefinementFact => simp [nodeSafe, hop] at hs
      case semRuntimeGuard => simp [nodeSafe, hop] at hs
      case intCell => simp [nodeSafe, hop] at hs
      case diffLe => simp [nodeSafe, hop] at hs
      case quantityUse => simp [nodeSafe, hop] at hs
      case semProgram => simp [nodeSafe, hop] at hs
      case semFunction => simp [nodeSafe, hop] at hs
      case semValue => simp [nodeSafe, hop] at hs
      case semBlock => simp [nodeSafe, hop] at hs
      case semInstruction => simp [nodeSafe, hop] at hs
      case semOperand => simp [nodeSafe, hop] at hs

private theorem firstLocal_none_sound {nodes : List Node}
    (h : firstLocalViolationList nodes = none) :
    ∀ n ∈ nodes, nodeSafe n = true := by
  induction nodes with
  | nil => simp
  | cons head tail ih =>
      cases hv : localViolation head with
      | some v => simp [firstLocalViolationList, hv] at h
      | none =>
          have htail : firstLocalViolationList tail = none := by
            simpa [firstLocalViolationList, hv] using h
          intro n hn
          simp only [List.mem_cons] at hn
          rcases hn with heq | hn
          · rw [heq]
            exact (localViolation_none_iff head).mp hv
          · exact ih htail n hn

private theorem firstAffine_none_sound (seen : List UInt32) (nodes : List Node)
    (h : firstAffineViolationList seen nodes = none) :
    (consumedOriginsList nodes).Nodup ∧
      ∀ origin ∈ consumedOriginsList nodes, origin ∉ seen := by
  induction nodes generalizing seen with
  | nil => simp [consumedOriginsList]
  | cons head tail ih =>
      cases hc : consumesOrigin head with
      | true =>
        have hnot : head.origin ∉ seen := by
          intro hm
          simp [firstAffineViolationList, hc, hm] at h
        have htail : firstAffineViolationList (head.origin :: seen) tail = none := by
          simpa [firstAffineViolationList, hc, hnot] using h
        obtain ⟨hnd, hfresh⟩ := ih (head.origin :: seen) htail
        have hhead : head.origin ∉ consumedOriginsList tail := by
          intro hmem
          exact (hfresh head.origin hmem) (by simp)
        constructor
        · simpa [consumedOriginsList, hc] using List.nodup_cons.mpr ⟨hhead, hnd⟩
        · intro origin horigin
          simp [consumedOriginsList, hc] at horigin
          rcases horigin with rfl | horigin
          · exact hnot
          · exact fun hseen => hfresh origin horigin (by simp [hseen])
      | false =>
        have htail : firstAffineViolationList seen tail = none := by
          simpa [firstAffineViolationList, hc] using h
        simpa [consumedOriginsList, hc] using ih seen htail

private theorem verified_parts {p : Program} (h : ProgramSafe p) :
    firstLocalViolation p.nodes = none ∧ firstAffineViolation p.nodes = none ∧
      firstCapabilityViolation p = none ∧ firstQuantitativeViolation p = none ∧
        firstPathAffineViolation p = none ∧ firstGraphViolation p = none := by
  unfold ProgramSafe at h
  have hverify := h.2.1
  unfold verifyProgram at hverify
  cases hs : firstSemanticViolation p with
  | some v => simp [hs] at hverify
  | none =>
    cases hm : firstSemanticMetadataViolation p with
    | some v => simp [hs, hm] at hverify
    | none =>
      cases h8 : firstV8SecurityViolation p with
      | some v => simp [hs, hm, h8] at hverify
      | none =>
        cases hv : firstLocalViolation p.nodes with
        | some v => simp [hs, hm, h8, hv] at hverify
        | none =>
          cases ha : firstAffineViolation p.nodes with
          | some v => simp [hs, hm, h8, hv, ha] at hverify
          | none =>
            cases hc : firstCapabilityViolation p with
            | some v => simp [hs, hm, h8, hv, ha, hc] at hverify
            | none =>
              cases hq : firstQuantitativeViolation p with
              | some v => simp [hs, hm, h8, hv, ha, hc, hq] at hverify
              | none =>
                cases hp : firstPathAffineViolation p with
                | some v => simp [hs, hm, h8, hv, ha, hc, hq, hp] at hverify
                | none =>
                    exact ⟨rfl, rfl, rfl, rfl, rfl,
                      by simpa [hs, hm, h8, hv, ha, hc, hq, hp] using hverify⟩

private theorem semantic_of_verified {p : Program} (h : ProgramSafe p) :
    SemanticEnvelopeJudgment p := by
  unfold ProgramSafe at h
  have hverify := h.2.1
  have hraw : Semantic.RawRelationalStaticSafe (Semantic.semanticProgramOf p) :=
    (Semantic.rawRelationalStaticSafeB_iff _).mp h.2.2
  unfold verifyProgram at hverify
  cases hs : firstSemanticViolation p with
  | some v => simp [hs] at hverify
  | none =>
    cases hm : firstSemanticMetadataViolation p with
    | some v => simp [hs, hm] at hverify
    | none =>
      cases h8 : firstV8SecurityViolation p with
      | some v => simp [hs, hm, h8] at hverify
      | none => exact ⟨h.1, hs, hm, h8, hraw⟩

private theorem firstLocal_none_complete {nodes : List Node}
    (h : ∀ n ∈ nodes, nodeSafe n = true) :
    firstLocalViolationList nodes = none := by
  induction nodes with
  | nil => rfl
  | cons head tail ih =>
      have hhead : nodeSafe head = true := h head (by simp)
      have htail : ∀ n ∈ tail, nodeSafe n = true := fun n hn => h n (by simp [hn])
      simp [firstLocalViolationList, (localViolation_none_iff head).mpr hhead, ih htail]

private theorem firstAffine_none_complete (seen : List UInt32) (nodes : List Node)
    (hnd : (consumedOriginsList nodes).Nodup)
    (hdisjoint : ∀ origin ∈ consumedOriginsList nodes, origin ∉ seen) :
    firstAffineViolationList seen nodes = none := by
  induction nodes generalizing seen with
  | nil => rfl
  | cons head tail ih =>
      cases hc : consumesOrigin head with
      | false =>
          simp [consumedOriginsList, hc] at hnd hdisjoint
          simpa [firstAffineViolationList, hc] using ih seen hnd hdisjoint
      | true =>
          have hshape : consumedOriginsList (head :: tail) =
              head.origin :: consumedOriginsList tail := by
            simp [consumedOriginsList, hc]
          rw [hshape] at hnd
          obtain ⟨hheadFresh, htailNodup⟩ := List.nodup_cons.mp hnd
          have hnotSeen : head.origin ∉ seen := by
            apply hdisjoint head.origin
            simp [consumedOriginsList, hc]
          have htailDisjoint : ∀ origin ∈ consumedOriginsList tail,
              origin ∉ head.origin :: seen := by
            intro origin horigin hmember
            simp only [List.mem_cons] at hmember
            rcases hmember with heq | hseen
            · exact hheadFresh (heq ▸ horigin)
            · exact hdisjoint origin (by simp [consumedOriginsList, hc, horigin]) hseen
          have htail := ih (head.origin :: seen) htailNodup htailDisjoint
          simpa [firstAffineViolationList, hc, hnotSeen] using htail

/-- Soundness of the decoded production-v8 decision procedure relative to the declarative CSIR
    judgment. -/
theorem verifier_sound {p : Program} (h : ProgramSafe p) : CSIRJudgment p := by
  have parts := verified_parts h
  refine ⟨semantic_of_verified h, ?_, ?_, capability_verifier_sound parts.2.2.1,
    quantitative_verifier_sound parts.2.2.2.1,
    path_affine_verifier_sound parts.2.2.2.2.1,
    graph_verifier_sound parts.2.2.2.2.2⟩
  · exact firstLocal_none_sound (by simpa [firstLocalViolation] using parts.1)
  · have affine := firstAffine_none_sound [] p.nodes.toList
      (by simpa [firstAffineViolation] using parts.2.1)
    simpa [AffineSafe, consumedOrigins] using affine.1

/-- Completeness: every program satisfying the declarative judgment meets the production-v8
    acceptance condition. -/
theorem verifier_complete {p : Program} (h : CSIRJudgment p) : ProgramSafe p := by
  have core := h.2
  have hmanifest : (semanticProgramNode? p).isSome = true := h.1.1
  have hsemantic : firstSemanticViolation p = none := h.1.2.1
  have hmetadata : firstSemanticMetadataViolation p = none := h.1.2.2.1
  have hv8 : firstV8SecurityViolation p = none := h.1.2.2.2.1
  have hraw : Semantic.rawRelationalStaticSafeB (Semantic.semanticProgramOf p) = true :=
    (Semantic.rawRelationalStaticSafeB_iff _).mpr h.1.2.2.2.2
  have hlocal : firstLocalViolation p.nodes = none := by
    simpa [firstLocalViolation] using firstLocal_none_complete core.1
  have haffine : firstAffineViolation p.nodes = none := by
    apply firstAffine_none_complete [] p.nodes.toList
    · simpa [AffineSafe, consumedOrigins] using core.2.1
    · simp
  have hcapability : firstCapabilityViolation p = none :=
    capability_verifier_complete core.2.2.1
  have hquantitative : firstQuantitativeViolation p = none :=
    quantitative_verifier_complete core.2.2.2.1
  have hpath : firstPathAffineViolation p = none :=
    path_affine_verifier_complete core.2.2.2.2.1
  have hgraph : firstGraphViolation p = none :=
    graph_verifier_complete core.2.2.2.2.2
  refine ⟨hmanifest, ?_, hraw⟩
  simp [verifyProgram, hsemantic, hmetadata, hv8, hlocal, haffine, hcapability,
    hquantitative, hpath, hgraph]

theorem verifier_sound_and_complete {p : Program} :
    ProgramSafe p ↔ CSIRJudgment p := ⟨verifier_sound, verifier_complete⟩

private theorem local_safe_of_verified {p : Program} (h : ProgramSafe p) {n : Node}
    (hn : n ∈ p.nodes) : nodeSafe n = true := by
  have hlocal := (verified_parts h).1
  apply firstLocal_none_sound (nodes := p.nodes.toList)
    (by simpa [firstLocalViolation] using hlocal) n
  simpa using hn

/-- The conjunction exported to the claims ledger.  It is intentionally stated as named
    properties rather than as a test count. -/
theorem joint_security_of_verified {p : Program} (h : ProgramSafe p) :
    V8SecurityJudgment p ∧ SemanticEnvelopeJudgment p ∧ AuthorityConfined p ∧ FlowsClean p ∧
      ReleasesAuthorized p ∧ CTPolicySafe p ∧
      AffineSafe p ∧ CapabilityJudgment p ∧ QuantitativeJudgment p ∧
        PathAffineJudgment p ∧ TaintGraphJudgment p ∧
          (TaintSolution p (graphLabels p) ∧
            ∀ candidate, TaintSolution p candidate →
              LabelsBelowCells (p.nodes.size + 1) (graphLabels p) candidate) := by
  have hlocal : ∀ n ∈ p.nodes, nodeSafe n = true := fun n hn =>
    local_safe_of_verified h hn
  have hsemantic := semantic_of_verified h
  have hrawB : Semantic.rawRelationalStaticSafeB (Semantic.semanticProgramOf p) = true :=
    (Semantic.rawRelationalStaticSafeB_iff _).mpr hsemantic.2.2.2.2
  have hv8 : V8SecurityJudgment p :=
    v8_semantic_verifier_sound_and_complete.mp
      ⟨hsemantic.1, hsemantic.2.1, hsemantic.2.2.1, hsemantic.2.2.2.1, hrawB⟩
  refine ⟨hv8, hsemantic, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn hop
    have hs := hlocal n hn
    simp [nodeSafe, hop, Bool.and_eq_true] at hs
    exact ⟨hs.1.1, hs.1.2, hs.2⟩
  · intro n hn hop
    have hs := hlocal n hn
    rcases hop with hop | hop
    · simpa [nodeSafe, hop] using hs
    · simp [nodeSafe, hop, Bool.and_eq_true] at hs
      exact hs.2
  · intro n hn hop
    have hs := hlocal n hn
    simp only [nodeSafe, hop] at hs
    generalize hk : capKindOf n = kind at hs
    cases kind with
    | none => simp at hs
    | some kind =>
        generalize ha : n.labelA = a at hs ⊢
        generalize hb : n.labelB = b at hs ⊢
        cases kind <;> cases a <;> cases b <;>
          simp_all [Bool.and_eq_true, Label.eqb, Label.neqb]
  · intro n hn hop
    have hs := hlocal n hn
    rcases hop with hop | hop
    · generalize ha : n.labelA = a at hs ⊢
      cases a <;> simp_all [nodeSafe, Label.eqb, Label.neqb]
    · simp [nodeSafe, hop, Bool.and_eq_true] at hs
      generalize ha : n.labelA = a at hs ⊢
      cases a <;> simp_all [Label.eqb, Label.neqb]
  · have haffine := (verified_parts h).2.1
    have hsound := firstAffine_none_sound [] p.nodes.toList
      (by simpa [firstAffineViolation] using haffine)
    simpa [AffineSafe, consumedOrigins, consumedOriginsList] using hsound.1
  · exact capability_verifier_sound (verified_parts h).2.2.1
  · exact quantitative_verifier_sound (verified_parts h).2.2.2.1
  · exact path_affine_verifier_sound (verified_parts h).2.2.2.2.1
  · exact graph_verifier_sound (verified_parts h).2.2.2.2.2
  · exact graphLabels_is_least_solution
      (graph_verifier_sound (verified_parts h).2.2.2.2.2)

def RawSecretCTStaticJudgment (p : Program) : Prop :=
  ∀ instruction ∈ p.nodes.toList, instruction.op = .semInstruction →
    semanticRawSecretCTInstructionSafe p (buildSemanticIndex p) (semanticLabels p)
      instruction = true

theorem raw_secretCT_instruction_safe_of_v8 {p : Program} (h : V8SecurityJudgment p)
    {instruction : Node} (hmem : instruction ∈ p.nodes.toList)
    (hop : instruction.op = .semInstruction) :
    semanticRawSecretCTInstructionSafe p (buildSemanticIndex p) (semanticLabels p)
      instruction = true := by
  have hnode := h.2.2.2.1 instruction hmem
  unfold SemanticNodeSecure at hnode
  rw [hop] at hnode
  cases hflow : semanticInstructionFlowViolation p (buildSemanticIndex p)
      (semanticLabels p) instruction with
  | some violation => simp [hflow] at hnode
  | none =>
      cases hcap : semanticInstructionCapabilityViolation p (buildSemanticIndex p) instruction with
      | some violation => simp [hflow, hcap] at hnode
      | none =>
          unfold semanticRawSecretCTViolation at hnode
          simp [hflow, hcap, hop] at hnode
          exact hnode (by decide)

theorem raw_secretCT_static_judgment_of_verified {p : Program} (h : ProgramSafe p) :
    RawSecretCTStaticJudgment p := by
  intro instruction hmem hop
  exact raw_secretCT_instruction_safe_of_v8 (joint_security_of_verified h).1 hmem hop

/-- The second, decoded-machine decision in the linked native verifier is exactly the static
    premise consumed by the unsanitized lockstep proof. -/
theorem raw_secretCT_static_safe_of_v8_verified {p : Program} (h : ProgramSafe p) :
    Semantic.SecretCTStaticSafe (Semantic.semanticProgramOf p) :=
  (Semantic.rawRelationalStaticSafeB_iff _).mp h.2.2 |>.1

theorem raw_public_control_static_safe_of_v8_verified {p : Program} (h : ProgramSafe p) :
    Semantic.PublicControlStaticSafe (Semantic.semanticProgramOf p) :=
  (Semantic.rawRelationalStaticSafeB_iff _).mp h.2.2 |>.2.1

theorem raw_public_halt_static_safe_of_v8_verified {p : Program} (h : ProgramSafe p) :
    Semantic.PublicHaltStaticSafe (Semantic.semanticProgramOf p) :=
  (Semantic.rawRelationalStaticSafeB_iff _).mp h.2.2 |>.2.2

theorem raw_secretCT_step_lockstep_of_v8_verified {p : Program} (h : ProgramSafe p) :
    Semantic.RawSecretCTStepPolicy (Semantic.semanticProgramOf p) :=
  Semantic.raw_secretCT_step_lockstep_of_static_safe
    (raw_secretCT_static_safe_of_v8_verified h)

theorem raw_secretCT_delimited_release_trace_equality_of_verified {p : Program}
    (hverified : ProgramSafe p) {fuel : Nat} {left right : Semantic.State}
    (hwleft : Semantic.StateWellFormed (Semantic.semanticProgramOf p) left)
    (hwright : Semantic.StateWellFormed (Semantic.semanticProgramOf p) right)
    (hlow : Semantic.SecretCTLowEquivalent (Semantic.semanticProgramOf p) left right)
    (hrelease : Semantic.ReleaseAlignedRaw (Semantic.semanticProgramOf p) fuel left right) :
    Semantic.publicEvents
        (Semantic.runPrefix (Semantic.semanticProgramOf p) fuel left).events =
      Semantic.publicEvents
        (Semantic.runPrefix (Semantic.semanticProgramOf p) fuel right).events :=
  Semantic.raw_secretCT_delimited_release_trace_equality
    (raw_secretCT_step_lockstep_of_v8_verified hverified)
    hwleft hwright hlow hrelease

/-! ## Raw relational theorem boundary

The former sanitized corollaries were intentionally removed together with the `safeMode` machine.
The production SecretCT corollary above is derived from the decoded-machine decision now compiled
into the native verifier.  The production Public corollary is exported separately from
`RawClaimSurface` after the V9 occurrence verifier derives the structured-region weak bisimulation;
no old theorem name can silently preserve the sanitized claim.
-/

/-! ## Delimited-release trace recomposition

`PublicSkeleton` removes explicit release nodes; `ReleaseTrace` retains them.  This single-run
recomposition lemma is retained as encoder plumbing and is not a substitute for the raw two-run
results in `SemanticSecurity`.
-/

def releaseTrace (p : Program) : List Node :=
  p.nodes.toList.filter fun n => n.op == .declassify

def publicSkeleton (p : Program) : List Node :=
  p.nodes.toList.filter fun n => n.op != .declassify

def publicTrace (p : Program) : List Node := publicSkeleton p ++ releaseTrace p

def LowEquivalent (p q : Program) : Prop := publicSkeleton p = publicSkeleton q

theorem delimited_release_trace_recomposition {p q : Program}
    (_hp : ProgramSafe p) (_hq : ProgramSafe q)
    (hlow : LowEquivalent p q) (hrelease : releaseTrace p = releaseTrace q) :
    publicTrace p = publicTrace q := by
  change publicSkeleton p = publicSkeleton q at hlow
  unfold publicTrace
  rw [hlow, hrelease]

/-! ## Non-vacuity and load-bearing mutants -/

def safeRelease : Node :=
  { op := .declassify, labelA := .secret, labelB := .pub, flags := 1,
    origin := 7, actual := 0, required := 0, ceiling := 0, aux := 1, nodeId := 1 }

def ctBranch : Node :=
  { op := .ctUse, labelA := .secretCT, labelB := .pub, flags := 0,
    origin := 0, actual := 0, required := 0, ceiling := 0, aux := 20, nodeId := 2 }

def reusedRelease : Program := ⟨#[safeRelease, { safeRelease with nodeId := 3 }]⟩

theorem safe_release_accepts : verifyProgram ⟨#[safeRelease]⟩ = none := by decide
theorem ct_branch_rejects : verifyProgram ⟨#[ctBranch]⟩ = some ⟨.ctPolicy, 2, 20⟩ := by
  decide
theorem reused_release_rejects :
    verifyProgram reusedRelease = some ⟨.affine, 3, 7⟩ := by decide

def graphCtSeed : Node :=
  { op := .taintSeed, labelA := .secretCT, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 0, ceiling := 0, aux := 0, nodeId := 1 }

def graphPublicCell (cell nodeId : UInt32) : Node :=
  { op := .taintSeed, labelA := .pub, labelB := .pub, flags := 1,
    origin := cell, actual := 0, required := 0, ceiling := 0, aux := 0, nodeId }

def reverseOrderedLoopGraph : Program := ⟨#[
  graphCtSeed,
  graphPublicCell 2 2,
  graphPublicCell 3 3,
  { op := .taintEdge, labelA := .pub, labelB := .pub, flags := 1,
    origin := 2, actual := 3, required := 0, ceiling := 0, aux := 0, nodeId := 4 },
  { op := .taintEdge, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 0, aux := 0, nodeId := 5 },
  { op := .taintEdge, labelA := .pub, labelB := .pub, flags := 1,
    origin := 3, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 6 },
  { op := .taintCtUse, labelA := .pub, labelB := .pub, flags := 1,
    origin := 3, actual := 0, required := 0, ceiling := 0, aux := 21, nodeId := 7 }
]⟩

/- A reverse-ordered cyclic graph needs multiple passes; the linked algorithm still derives the
   loop-carried SecretCT label and rejects the CT-sensitive use. -/
set_option maxRecDepth 10000 in
theorem loop_backedge_taint_rejects :
    verifyProgram reverseOrderedLoopGraph = some ⟨.ctPolicy, 7, 21⟩ := by decide

def pcSinkNode : Node :=
  { op := .taintSink, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 0, aux := 20, nodeId := 3 }

def pcJoinGraph : Program := ⟨#[
  graphPublicCell 1 1,
  { graphCtSeed with origin := 2, nodeId := 2 },
  pcSinkNode
]⟩

def mutantGraphSinkWithoutPc (labels : Array Label) (n : Node) : Bool :=
  if n.op == .taintSink then (labelAt labels n.origin).flowsTo n.labelB
  else graphNodeSafe labels n

theorem missing_pc_join_mutant_readmits_violation :
    mutantGraphSinkWithoutPc (graphLabels pcJoinGraph) pcSinkNode = true := by
  decide

theorem real_graph_checker_rejects_missing_pc_join :
    verifyProgram pcJoinGraph = some ⟨.flow, 3, 20⟩ := by decide

def capabilityOrigin (mask nodeId : UInt32) : Node :=
  { op := .capOrigin, labelA := .pub, labelB := .pub, flags := 1,
    origin := 0, actual := nodeId, required := 0, ceiling := mask, aux := 0, nodeId }

def restrictedCapabilityNode : Node :=
  { op := .capRestrict, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 1, ceiling := 3, aux := 0, nodeId := 2 }

def restrictedCapabilitySink : Node :=
  { op := .capSink, labelA := .pub, labelB := .pub, flags := 1,
    origin := 2, actual := 0, required := 2, ceiling := 3, aux := 0, nodeId := 3 }

def restrictedCapabilityProgram : Program := ⟨#[
  capabilityOrigin 3 1, restrictedCapabilityNode, restrictedCapabilitySink
]⟩

theorem capability_restriction_rejects_missing_authority :
    verifyProgram restrictedCapabilityProgram = some ⟨.authority, 3, 0⟩ := by decide

def forgedCapabilityProgram : Program := ⟨#[
  { op := .fixedCT, labelA := .pub, labelB := .pub, flags := 1,
    origin := 0, actual := 0, required := 0, ceiling := 0, aux := 0, nodeId := 1 },
  { op := .capRestrict, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 1, ceiling := 3, aux := 0, nodeId := 2 }
]⟩

theorem capability_forgery_rejects :
    verifyProgram forgedCapabilityProgram = some ⟨.legitimacy, 2, 0⟩ := by decide

def slotAuthorityMeetProgram : Program := ⟨#[
  capabilityOrigin 3 1,
  { op := .capRestrict, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 1, ceiling := 3, aux := 0, nodeId := 2 },
  { op := .capSlot, labelA := .pub, labelB := .pub, flags := 0,
    origin := 0, actual := 3, required := 0, ceiling := 3, aux := 0, nodeId := 3 },
  { op := .capSlotPut, labelA := .pub, labelB := .pub, flags := 1,
    origin := 2, actual := 3, required := 0, ceiling := 3, aux := 0, nodeId := 4 },
  { op := .capSlotTake, labelA := .pub, labelB := .pub, flags := 1,
    origin := 3, actual := 5, required := 0, ceiling := 3, aux := 0, nodeId := 5 },
  { op := .capSink, labelA := .pub, labelB := .pub, flags := 1,
    origin := 5, actual := 0, required := 2, ceiling := 3, aux := 0, nodeId := 6 }
]⟩

theorem slot_authority_meet_rejects :
    verifyProgram slotAuthorityMeetProgram = some ⟨.authority, 6, 0⟩ := by decide

def emptySlotTakeProgram : Program := ⟨#[
  { op := .capSlot, labelA := .pub, labelB := .pub, flags := 0,
    origin := 0, actual := 1, required := 0, ceiling := 3, aux := 0, nodeId := 1 },
  { op := .capSlotTake, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 3, aux := 0, nodeId := 2 },
  { op := .capSink, labelA := .pub, labelB := .pub, flags := 1,
    origin := 2, actual := 0, required := 1, ceiling := 3, aux := 0, nodeId := 3 }
]⟩

/-- An empty slot take is a guarded runtime trap. The static graph checks the
    possible successful continuation conservatively instead of rejecting the program. -/
theorem empty_slot_take_accepts_guarded_continuation :
    verifyProgram emptySlotTakeProgram = none := by decide

def emptySlotTakeExcessAuthorityProgram : Program := ⟨#[
  { op := .capSlot, labelA := .pub, labelB := .pub, flags := 0,
    origin := 0, actual := 1, required := 0, ceiling := 3, aux := 0, nodeId := 1 },
  { op := .capSlotTake, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 3, aux := 0, nodeId := 2 },
  { op := .capSink, labelA := .pub, labelB := .pub, flags := 1,
    origin := 2, actual := 0, required := 4, ceiling := 3, aux := 0, nodeId := 3 }
]⟩

theorem empty_slot_take_still_enforces_authority_ceiling :
    verifyProgram emptySlotTakeExcessAuthorityProgram = some ⟨.authority, 3, 0⟩ := by decide

def mutantCapabilitySinkNoMask (states : Array CapState) (n : Node) : Bool :=
  if n.op == .capSink then capSourceReady states n.origin && capKindMatches (capStateAt states n.origin) n
  else capNodeSafe states n

theorem capability_mask_mutant_readmits_violation :
    let originStates := applyCapabilityNode (emptyCapStates restrictedCapabilityProgram)
      (capabilityOrigin 3 1)
    let restrictedStates := applyCapabilityNode originStates
      restrictedCapabilityNode
    mutantCapabilitySinkNoMask restrictedStates restrictedCapabilitySink = true := by
  decide

def pathForkNode (nodeId arms : UInt32) : Node :=
  { op := .pathFork, labelA := .pub, labelB := .pub, flags := 1,
    origin := 0, actual := 0, required := 0, ceiling := 0, aux := arms, nodeId }

def pathArmNode (nodeId : UInt32) (fallsThrough : Bool) : Node :=
  { op := .pathArm, labelA := .pub, labelB := .pub,
    flags := if fallsThrough then 1 else 0,
    origin := 0, actual := 0, required := 0, ceiling := 0, aux := 0, nodeId }

def pathJoinNode (nodeId : UInt32) (fallsThrough : Bool) : Node :=
  { op := .pathJoin, labelA := .pub, labelB := .pub,
    flags := if fallsThrough then 1 else 0,
    origin := 0, actual := 0, required := 0, ceiling := 0, aux := 0, nodeId }

def pathConsumeNode (origin nodeId : UInt32) : Node :=
  { op := .capSink, labelA := .pub, labelB := .pub, flags := 1,
    origin, actual := 0, required := 0, ceiling := 3, aux := 0, nodeId }

def alternativeConsumptionProgram : Program := ⟨#[
  capabilityOrigin 3 1,
  pathForkNode 2 2,
  pathConsumeNode 1 3,
  pathArmNode 4 true,
  pathConsumeNode 1 5,
  pathJoinNode 6 true
]⟩

theorem alternative_path_consumption_accepts :
    verifyProgram alternativeConsumptionProgram = none := by decide

def samePathDoubleConsumptionProgram : Program := ⟨#[
  capabilityOrigin 3 1,
  pathForkNode 2 2,
  pathConsumeNode 1 3,
  pathConsumeNode 1 4,
  pathArmNode 5 true,
  pathJoinNode 6 true
]⟩

theorem same_path_double_consumption_rejects :
    verifyProgram samePathDoubleConsumptionProgram = some ⟨.affine, 4, 1⟩ := by decide

def useAfterMayConsumeProgram : Program := ⟨#[
  capabilityOrigin 3 1,
  pathForkNode 2 2,
  pathConsumeNode 1 3,
  pathArmNode 4 true,
  pathJoinNode 5 true,
  pathConsumeNode 1 6
]⟩

theorem use_after_may_consume_join_rejects :
    verifyProgram useAfterMayConsumeProgram = some ⟨.affine, 6, 1⟩ := by decide

def divergentConsumptionProgram : Program := ⟨#[
  capabilityOrigin 3 1,
  pathForkNode 2 2,
  pathConsumeNode 1 3,
  pathArmNode 4 false,
  pathJoinNode 5 true,
  pathConsumeNode 1 6
]⟩

theorem divergent_arm_does_not_poison_join :
    verifyProgram divergentConsumptionProgram = none := by decide

def pathLoopNode (op : Op) (nodeId : UInt32) : Node :=
  { op, labelA := .pub, labelB := .pub, flags := 1,
    origin := 0, actual := 0, required := 0, ceiling := 0, aux := 0, nodeId }

def loopBackedgeConsumptionProgram : Program := ⟨#[
  capabilityOrigin 3 1,
  pathLoopNode .pathLoop 2,
  pathConsumeNode 1 3,
  pathLoopNode .pathBack 4,
  pathLoopNode .pathLoopJoin 5
]⟩

theorem loop_backedge_consumption_rejects :
    verifyProgram loopBackedgeConsumptionProgram = some ⟨.affine, 4, 1⟩ := by decide

def breakConsumptionProgram : Program := ⟨#[
  capabilityOrigin 3 1,
  pathLoopNode .pathLoop 2,
  pathConsumeNode 1 3,
  pathLoopNode .pathBreak 4,
  pathLoopNode .pathLoopJoin 5
]⟩

theorem single_break_consumption_accepts :
    verifyProgram breakConsumptionProgram = none := by decide

def useAfterBreakConsumptionProgram : Program := ⟨#[
  capabilityOrigin 3 1,
  pathLoopNode .pathLoop 2,
  pathConsumeNode 1 3,
  pathLoopNode .pathBreak 4,
  pathLoopNode .pathLoopJoin 5,
  pathConsumeNode 1 6
]⟩

theorem use_after_break_consumption_rejects :
    verifyProgram useAfterBreakConsumptionProgram = some ⟨.affine, 6, 1⟩ := by decide

def untouchedLoopProgram : Program := ⟨#[
  capabilityOrigin 3 1,
  pathLoopNode .pathLoop 2,
  pathLoopNode .pathBack 3,
  pathLoopNode .pathLoopJoin 4,
  pathConsumeNode 1 5
]⟩

theorem untouched_loop_preserves_head_capability :
    verifyProgram untouchedLoopProgram = none := by decide

def mutantPathAffineNoBack (state : PathAffineState) (n : Node) : Option Violation :=
  if n.op == .pathBack then none else pathAffineViolation state n

theorem loop_backedge_mutant_readmits_repetition :
    let s0 := emptyPathAffineState loopBackedgeConsumptionProgram
    let s1 := applyPathAffineNode s0 (capabilityOrigin 3 1)
    let s2 := applyPathAffineNode s1 (pathLoopNode .pathLoop 2)
    let s3 := applyPathAffineNode s2 (pathConsumeNode 1 3)
    mutantPathAffineNoBack s3 (pathLoopNode .pathBack 4) = none ∧
      pathAffineViolation s3 (pathLoopNode .pathBack 4) = some ⟨.affine, 4, 1⟩ := by
  decide

def mutantNodeSafeNoCT (n : Node) : Bool :=
  if n.op == .ctUse then true else nodeSafe n

theorem ct_mutant_readmits_violation : mutantNodeSafeNoCT ctBranch = true := by decide

def mutantNodeSafeNoAuthority (n : Node) : Bool :=
  if n.op == .authority then true else nodeSafe n

def badAuthority : Node :=
  { op := .authority, labelA := .pub, labelB := .pub, flags := 1,
    origin := 9, actual := 1, required := 3, ceiling := 1, aux := 0, nodeId := 4 }

theorem authority_mutant_readmits_violation : mutantNodeSafeNoAuthority badAuthority = true := by
  decide
theorem real_checker_rejects_bad_authority : nodeSafe badAuthority = false := by decide

def exactIntCell (value : Int) (nodeId : UInt32) : Node :=
  let magnitude := value.natAbs
  { op := .intCell, labelA := .pub, labelB := .pub,
    flags := if value < 0 then 7 else 5,
    origin := 0, actual := nodeId,
    required := UInt32.ofNat magnitude,
    ceiling := 0, aux := 0, nodeId }

def guardedSplitProgram : Program := ⟨#[
  capabilityOrigin 3 1,
  exactIntCell 5 2,
  { op := .capSplit, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 3, required := 3, ceiling := 3, aux := 0, nodeId := 3 },
  { op := .quantityUse, labelA := .pub, labelB := .pub, flags := 3,
    origin := 1, actual := 3, required := 2, ceiling := 0, aux := 1, nodeId := 4 }
]⟩

theorem guarded_split_witness_accepts : verifyProgram guardedSplitProgram = none := by decide

def guardedSplitOrigin : Node := capabilityOrigin 3 1
def guardedSplitAmount : Node := exactIntCell 5 2
def guardedSplitOperation : Node :=
  { op := .capSplit, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 3, required := 3, ceiling := 3, aux := 0, nodeId := 3 }
def guardedSplitLink : Node :=
  { op := .quantityUse, labelA := .pub, labelB := .pub, flags := 3,
    origin := 1, actual := 3, required := 2, ceiling := 0, aux := 1, nodeId := 4 }

def missingQuantityGuardProgram : Program := ⟨#[
  guardedSplitOrigin, guardedSplitAmount, guardedSplitOperation, { guardedSplitLink with flags := 1 }
]⟩

theorem missing_quantity_guard_mutant_rejects :
    verifyProgram missingQuantityGuardProgram = some ⟨.malformed, 4, 1⟩ := by decide

def wrongQuantitySourceProgram : Program := ⟨#[
  guardedSplitOrigin, guardedSplitAmount, guardedSplitOperation, { guardedSplitLink with origin := 2 }
]⟩

theorem wrong_quantity_source_mutant_rejects :
    verifyProgram wrongQuantitySourceProgram = some ⟨.malformed, 4, 1⟩ := by decide

def inconsistentLiteralConstraintProgram : Program := ⟨#[
  exactIntCell 1 1,
  { op := .diffLe, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 0, ceiling := 0, aux := 0, nodeId := 2 }
]⟩

set_option maxRecDepth 10000 in
theorem contradictory_literal_bound_rejects :
    verifyProgram inconsistentLiteralConstraintProgram = some ⟨.capabilityGraph, 0, 1⟩ := by
  decide

/-- Cell-to-cell constraints are outside the v6 literal-RHS grammar.  They must fail closed rather
    than silently extending the fragment beyond the classifier completeness theorem. -/
def crossCellDifferenceProgram : Program := ⟨#[
  exactIntCell 1 1,
  exactIntCell 2 2,
  { op := .diffLe, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 0, aux := 0, nodeId := 3 }
]⟩

theorem unsupported_cross_cell_constraint_rejects :
    verifyProgram crossCellDifferenceProgram = some ⟨.malformed, 3, 0⟩ := by decide

def mutantQuantitativeEdgesWithoutRefinements (p : Program) : List DiffEdge :=
  p.nodes.toList.flatMap fun n =>
    if n.op == .diffLe then [] else quantitativeEdgesForNode n

def mutantDifferenceConsistentWithoutRefinements (p : Program) : Bool :=
  let edges := mutantQuantitativeEdgesWithoutRefinements p
  let initial := Array.replicate (p.nodes.size + 1) (0 : Int)
  let settled := relaxDiffPasses edges (intCellCount p + 1) initial
  !(relaxDiffPass edges settled).2

set_option maxRecDepth 10000 in
theorem omitted_refinement_bound_mutant_readmits_contradiction :
    mutantDifferenceConsistentWithoutRefinements inconsistentLiteralConstraintProgram = true ∧
      differenceConsistent inconsistentLiteralConstraintProgram = false := by decide

def i64MinCell : Node :=
  { op := .intCell, labelA := .pub, labelB := .pub, flags := 7,
    origin := 0, actual := 1, required := 0, ceiling := 2147483648, aux := 0, nodeId := 1 }

theorem i64_min_sign_magnitude_witness :
    signedMagnitude i64MinCell = i64Min := by decide

def graphSeedAt (label : Label) (cell nodeId : UInt32) : Node :=
  { op := .taintSeed, labelA := label, labelB := .pub, flags := 1,
    origin := cell, actual := 0, required := 0, ceiling := 0, aux := 0, nodeId }

def graphEdgeAt (source target nodeId : UInt32) : Node :=
  { op := .taintEdge, labelA := .pub, labelB := .pub, flags := 1,
    origin := source, actual := target, required := 0, ceiling := 0, aux := 0, nodeId }

def diamondDuplicateGraph : Program := ⟨#[
  graphSeedAt .internal 1 1,
  graphSeedAt .secret 2 2,
  graphPublicCell 3 3,
  graphEdgeAt 1 3 4,
  graphEdgeAt 2 3 5,
  graphEdgeAt 1 3 6
]⟩

theorem diamond_and_duplicate_edges_compute_the_join :
    labelAt (graphLabels diamondDuplicateGraph) 3 = .secret ∧
      verifyProgram diamondDuplicateGraph = none := by decide

def maximumHeightGraph : Program := ⟨#[
  graphSeedAt .internal 1 1,
  graphSeedAt .secret 2 2,
  graphSeedAt .secretCT 3 3,
  graphPublicCell 4 4,
  graphEdgeAt 1 4 5,
  graphEdgeAt 2 4 6,
  graphEdgeAt 3 4 7
]⟩

theorem maximum_height_witness_reaches_secret_ct :
    labelAt (graphLabels maximumHeightGraph) 4 = .secretCT ∧
      verifyProgram maximumHeightGraph = none := by decide

def underfueledGraphLabels (p : Program) : Array Label :=
  let cellCount := p.nodes.size + 1
  saturateGraphWorklist (graphAdjacency p) 1
    ((List.range cellCount).map UInt32.ofNat) (graphSeedLabels p)

theorem under_fueled_worklist_is_a_detected_false_rejection :
    graphComputedSolutionSafe maximumHeightGraph (underfueledGraphLabels maximumHeightGraph) =
      false ∧ verifyProgram maximumHeightGraph = none := by decide

def mutantGraphNodeSafeMissingEdgeCheck (labels : Array Label) (n : Node) : Bool :=
  if n.op == .taintEdge then true else graphNodeSafe labels n

def mutantUnderfueledGraphAccepts (p : Program) : Bool :=
  let labels := underfueledGraphLabels p
  p.nodes.toList.all fun n =>
    graphNodeWellFormed p n && mutantGraphNodeSafeMissingEdgeCheck labels n

theorem missing_edge_and_postfix_checks_readmit_the_ct_leak :
    mutantUnderfueledGraphAccepts reverseOrderedLoopGraph = true ∧
      verifyProgram reverseOrderedLoopGraph = some ⟨.ctPolicy, 7, 21⟩ := by decide

/-! ## CSIR v8 semantic-policy witnesses and load-bearing mutants -/

def semanticManifest (functions values blocks instructions operands : UInt32) : Node :=
  { op := .semProgram, labelA := .pub, labelB := .pub, flags := 1,
    origin := functions, actual := blocks, required := instructions, ceiling := operands,
    aux := values, nodeId := 1 }

def minimalSemanticFunction : Node :=
  { op := .semFunction, labelA := .pub, labelB := .pub, flags := 0,
    origin := 1, actual := 1, required := 1, ceiling := 0, aux := 0, nodeId := 2 }

def minimalSemanticBlock : Node :=
  { op := .semBlock, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 1, ceiling := 0, aux := 0, nodeId := 3 }

def minimalSemanticHalt : Node :=
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 30, nodeId := 4 }

def minimalSemanticProgram : Program := ⟨#[
  semanticManifest 1 0 1 1 0, minimalSemanticFunction, minimalSemanticBlock, minimalSemanticHalt,
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 5 }
]⟩

theorem canonical_semantic_envelope_accepts : verifyProgram minimalSemanticProgram = none := by
  unfold verifyProgram
  rw [show firstSemanticViolation minimalSemanticProgram = none by decide]
  rw [show firstSemanticMetadataViolation minimalSemanticProgram = none by decide]
  rw [show firstV8SecurityViolation minimalSemanticProgram = none by decide]
  decide

def semanticStateReadProgram : Program := ⟨#[
  semanticManifest 1 2 1 2 4,
  { minimalSemanticFunction with required := 1, ceiling := 2 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 3 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 0, aux := 0, nodeId := 4 },
  { minimalSemanticBlock with required := 2, nodeId := 5 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 2, ceiling := 4, aux := 9, nodeId := 6 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 6, actual := 0, required := 1, ceiling := 0, aux := 0, nodeId := 7 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 3,
    origin := 6, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 8 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 3,
    origin := 6, actual := 2, required := 0, ceiling := 0, aux := 0, nodeId := 9 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 3,
    origin := 6, actual := 3, required := 0, ceiling := 0, aux := 0, nodeId := 10 },
  { minimalSemanticHalt with nodeId := 11 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 12 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 3, ceiling := 0, aux := 3, nodeId := 13 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 1, ceiling := 0, aux := 1, nodeId := 14 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 1, ceiling := 0, aux := 1, nodeId := 15 }
]⟩

theorem derived_state_contract_accepts : verifyProgram semanticStateReadProgram = none := by
  unfold verifyProgram
  rw [show firstSemanticViolation semanticStateReadProgram = none by
    set_option maxRecDepth 10000 in decide]
  rw [show firstSemanticMetadataViolation semanticStateReadProgram = none by
    set_option maxRecDepth 10000 in decide]
  rw [show firstV8SecurityViolation semanticStateReadProgram = none by
    set_option maxRecDepth 10000 in decide]
  decide

def forgedStateInstructionLabelOperand : Node :=
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 3,
    origin := 6, actual := 3, required := 3, ceiling := 0, aux := 0, nodeId := 10 }

def forgedStateInstructionLabelProgram : Program :=
  { semanticStateReadProgram with nodes :=
      semanticStateReadProgram.nodes.set! 9 forgedStateInstructionLabelOperand }

/-- The compatibility label embedded in a state instruction is not authoritative. A disagreement
    with the declared state-contract join is malformed rather than a runtime label choice. -/
theorem forged_state_instruction_label_rejects :
    verifyProgram forgedStateInstructionLabelProgram = some ⟨.malformed, 6, 9⟩ := by
  unfold verifyProgram
  rw [show firstSemanticViolation forgedStateInstructionLabelProgram =
    some ⟨.malformed, 6, 9⟩ by
      set_option maxRecDepth 10000 in decide]

def wrongSemanticCountProgram : Program :=
  { minimalSemanticProgram with nodes := (minimalSemanticProgram.nodes.set! 0
      (semanticManifest 1 0 1 2 0)) }

theorem wrong_semantic_constructor_count_rejects :
    verifyProgram wrongSemanticCountProgram = some ⟨.malformed, 1, 0⟩ := by decide

def missingSemanticTargetProgram : Program := ⟨#[
  semanticManifest 1 0 1 1 1,
  minimalSemanticFunction,
  minimalSemanticBlock,
  { minimalSemanticHalt with aux := 4, ceiling := 1 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 1,
    origin := 4, actual := 0, required := 2, ceiling := 0, aux := 0, nodeId := 5 }
]⟩

theorem missing_cfg_target_mutant_rejects :
    verifyProgram missingSemanticTargetProgram = some ⟨.malformed, 5, 0⟩ := by decide

def noncontiguousSemanticOperandProgram : Program :=
  { missingSemanticTargetProgram with nodes := (missingSemanticTargetProgram.nodes.set! 4
      { op := .semOperand, labelA := .pub, labelB := .pub, flags := 1,
        origin := 4, actual := 1, required := 1, ceiling := 0, aux := 0, nodeId := 5 }) }

theorem noncontiguous_operand_mutant_rejects :
    verifyProgram noncontiguousSemanticOperandProgram = some ⟨.malformed, 0, 7⟩ := by decide

def wrongSemanticArityProgram : Program := ⟨#[
  semanticManifest 1 0 1 1 1,
  minimalSemanticFunction,
  minimalSemanticBlock,
  { minimalSemanticHalt with ceiling := 1 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 3,
    origin := 4, actual := 0, required := 0, ceiling := 0, aux := 0, nodeId := 5 }
]⟩

theorem wrong_instruction_arity_mutant_rejects :
    verifyProgram wrongSemanticArityProgram = some ⟨.malformed, 4, 30⟩ := by decide

/-- A dispatch wrapper has no value operand of its own, while each arm-test dispatch selects its
    condition at operand zero.  This witness pins both shapes and prevents the source projection
    from attaching an arm policy to the unconditional catch-all jump that ends the chain. -/
def semanticDispatchProgram : Program := ⟨#[
  semanticManifest 1 1 3 3 3,
  { minimalSemanticFunction with required := 3, ceiling := 1 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 3, ceiling := 0, aux := 0, nodeId := 3 },
  { minimalSemanticBlock with required := 1, nodeId := 4 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 3, aux := 32, nodeId := 5 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 5, actual := 0, required := 1, ceiling := 0, aux := 0, nodeId := 6 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 1,
    origin := 5, actual := 1, required := 2, ceiling := 0, aux := 0, nodeId := 7 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 1,
    origin := 5, actual := 2, required := 3, ceiling := 0, aux := 0, nodeId := 8 },
  { minimalSemanticBlock with actual := 2, nodeId := 9 },
  { minimalSemanticHalt with actual := 2, nodeId := 10 },
  { minimalSemanticBlock with actual := 3, nodeId := 11 },
  { minimalSemanticHalt with actual := 3, nodeId := 12 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 13 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 1, ceiling := 0, aux := 1, nodeId := 14 },
  { op := .semPolicyClass, labelA := .pub, labelB := .pub, flags := 1,
    origin := 5, actual := 1, required := 23, ceiling := 0, aux := 3, nodeId := 15 }
]⟩

theorem semantic_dispatch_policy_accepts : verifyProgram semanticDispatchProgram = none := by decide

def missingSemanticDispatchPolicyProgram : Program :=
  { semanticDispatchProgram with nodes := semanticDispatchProgram.nodes.extract 0 14 }

theorem missing_semantic_dispatch_policy_rejects :
    verifyProgram missingSemanticDispatchPolicyProgram = some ⟨.malformed, 5, 8⟩ := by decide

def policyOnUnconditionalJumpProgram : Program :=
  { semanticDispatchProgram with nodes := semanticDispatchProgram.nodes.set! 14 (
      { op := .semPolicyClass, labelA := .pub, labelB := .pub, flags := 1,
        origin := 10, actual := 0, required := 23, ceiling := 0, aux := 3, nodeId := 15 } : Node) }

theorem policy_on_unconditional_jump_rejects :
    verifyProgram policyOnUnconditionalJumpProgram = some ⟨.malformed, 15, 3⟩ := by decide

/-- A structured branch raises the pc only in its arms. Its explicit merge restores the enclosing
    pc; arm jumps therefore cannot make an unrelated Public value permanently Secret. -/
def structuredPcRestoreProgram : Program := ⟨#[
  semanticManifest 1 2 4 4 7,
  { minimalSemanticFunction with required := 4, ceiling := 2 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 1, ceiling := 0, aux := 0, nodeId := 3 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 4, ceiling := 0, aux := 0, nodeId := 4 },
  { minimalSemanticBlock with actual := 1, nodeId := 5 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 4, aux := 3, nodeId := 6 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 6, actual := 0, required := 1, ceiling := 0, aux := 0, nodeId := 7 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 1,
    origin := 6, actual := 1, required := 2, ceiling := 0, aux := 0, nodeId := 8 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 1,
    origin := 6, actual := 2, required := 3, ceiling := 0, aux := 0, nodeId := 9 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 1,
    origin := 6, actual := 3, required := 4, ceiling := 0, aux := 0, nodeId := 10 },
  { minimalSemanticBlock with actual := 2, nodeId := 11 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 1, aux := 4, nodeId := 12 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 1,
    origin := 12, actual := 0, required := 4, ceiling := 0, aux := 0, nodeId := 13 },
  { minimalSemanticBlock with actual := 3, nodeId := 14 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 3, required := 0, ceiling := 1, aux := 4, nodeId := 15 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 1,
    origin := 15, actual := 0, required := 4, ceiling := 0, aux := 0, nodeId := 16 },
  { minimalSemanticBlock with actual := 4, nodeId := 17 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 4, required := 0, ceiling := 1, aux := 28, nodeId := 18 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 18, actual := 0, required := 2, ceiling := 0, aux := 0, nodeId := 19 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 20 },
  { op := .semLabelContract, labelA := .secret, labelB := .secret, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 21 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 1, ceiling := 0, aux := 1, nodeId := 22 },
  { op := .semPolicyClass, labelA := .pub, labelB := .pub, flags := 1,
    origin := 6, actual := 1, required := 20, ceiling := 0, aux := 0, nodeId := 23 }
]⟩

theorem structured_pc_restore_accepts : verifyProgram structuredPcRestoreProgram = none := by
  set_option maxRecDepth 10000 in decide

/-- The legacy structured-path check allowed a Secret arm to return successfully before its
    declared merge.  At top level that arm suppresses the later Public output while both runs
    still halt, so termination-insensitive Public noninterference is false.  V8 now permits early
    successful exits only after control reaches a verifier-derived Public continuation. -/
def secretArmEarlyOutput : Node :=
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 1, aux := 28, nodeId := 12 }

def secretArmEarlyOutputOperand : Node :=
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 12, actual := 0, required := 1, ceiling := 0, aux := 0, nodeId := 13 }

def secretArmReturnContract : Node :=
  { op := .semLabelContract, labelA := .secret, labelB := .secret, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 20 }

def secretArmSuccessfulEscapeProgram : Program :=
  let nodes := structuredPcRestoreProgram.nodes.set! 11 secretArmEarlyOutput
  let nodes := nodes.set! 12 secretArmEarlyOutputOperand
  let nodes := nodes.set! 19 secretArmReturnContract
  { structuredPcRestoreProgram with nodes }

theorem legacy_secret_arm_successful_escape_was_accepted :
    verifyProgram secretArmSuccessfulEscapeProgram = none := by
  set_option maxRecDepth 10000 in decide

theorem secret_arm_successful_escape_breaks_the_public_path_check :
    semanticStructuredPathsOK secretArmSuccessfulEscapeProgram
      (buildSemanticIndex secretArmSuccessfulEscapeProgram)
      (semanticLabels secretArmSuccessfulEscapeProgram) 1 4 4 true 17
        (Array.replicate 5 false) [2] = false := by
  set_option maxRecDepth 10000 in decide

/-- A callee reached under a non-Public caller pc is outside the caller's block-level path walk.
    Its derived block label therefore carries the load: allowing this halt would let one Secret
    arm terminate the whole machine while another returns to the merge. -/
def nonPublicHaltSemanticProgram : Semantic.SemanticProgram :=
  { functions := #[]
    instructions := #[{
      op := .halt, id := 1, functionId := 1, blockId := 1, destination := 0,
      firstOperand := 0, operandCount := 0, target := 1, blockLabel := .secret,
      resultLabel := .pub, aux := 0 }]
    operands := #[]
    valueLabels := #[.pub] }

theorem non_public_callee_halt_mutant_rejects :
    Semantic.publicHaltStaticSafeB nonPublicHaltSemanticProgram = false := by
  decide

def missingStructuredPcRestoreProgram : Program :=
  { structuredPcRestoreProgram with nodes := structuredPcRestoreProgram.nodes.set! 9 (
      { op := .semOperand, labelA := .pub, labelB := .pub, flags := 1,
        origin := 6, actual := 3, required := 3, ceiling := 0, aux := 0, nodeId := 10 } : Node) }

theorem missing_structured_pc_restore_rejects :
    verifyProgram missingStructuredPcRestoreProgram = some ⟨.flow, 18, 1⟩ := by
  set_option maxRecDepth 10000 in decide

def semanticCtSourceProgram : Program := ⟨#[
  semanticManifest 1 2 1 2 1,
  { minimalSemanticFunction with required := 1, ceiling := 2 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 3 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 0, aux := 0, nodeId := 4 },
  { minimalSemanticBlock with required := 2, nodeId := 5 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 2, ceiling := 1, aux := 2, nodeId := 6 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 6, actual := 0, required := 1, ceiling := 0, aux := 0, nodeId := 7 },
  { minimalSemanticHalt with nodeId := 8 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 9 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 10 },
  { op := .semLabelContract, labelA := .secretCT, labelB := .secretCT, flags := 1,
    origin := 1, actual := 2, required := 1, ceiling := 0, aux := 1, nodeId := 11 },
  { op := .semPolicyClass, labelA := .pub, labelB := .pub, flags := 1,
    origin := 6, actual := 1, required := 30, ceiling := 0, aux := 10, nodeId := 12 }
]⟩

theorem public_ct_source_accepts : verifyProgram semanticCtSourceProgram = none := by decide

def missingCtSourcePolicyProgram : Program :=
  { semanticCtSourceProgram with nodes := semanticCtSourceProgram.nodes.extract 0 11 }

theorem missing_ct_source_policy_rejects :
    verifyProgram missingCtSourcePolicyProgram = some ⟨.malformed, 6, 8⟩ := by decide

def internalCtSourceProgram : Program :=
  { semanticCtSourceProgram with nodes := semanticCtSourceProgram.nodes.set! 9 (
      { op := .semLabelContract, labelA := .internal, labelB := .internal, flags := 1,
        origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 10 } : Node) }

theorem internal_ct_source_rejects_t030 :
    verifyProgram internalCtSourceProgram = some ⟨.ctPolicy, 6, 30⟩ := by decide

/-- A host call with no value arguments still carries an explicit FFI policy record.  Its name is
    encoded by immediate operands, so the empty value-selection mask is meaningful rather than an
    omitted policy decision. -/
def zeroArgumentFfiProgram : Program := ⟨#[
  semanticManifest 1 1 1 2 2,
  { minimalSemanticFunction with ceiling := 1 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 3 },
  { minimalSemanticBlock with required := 2, nodeId := 4 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 1, ceiling := 2, aux := 15, nodeId := 5 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 3,
    origin := 5, actual := 0, required := 1, ceiling := 0, aux := 0, nodeId := 6 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 3,
    origin := 5, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 7 },
  { minimalSemanticHalt with nodeId := 8 },
  { op := .semLabelContract, labelA := .internal, labelB := .internal, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 9 },
  { op := .semLabelContract, labelA := .internal, labelB := .internal, flags := 1,
    origin := 1, actual := 1, required := 1, ceiling := 0, aux := 1, nodeId := 10 },
  { op := .semPolicyClass, labelA := .pub, labelB := .pub, flags := 1,
    origin := 5, actual := 0, required := 27, ceiling := 0, aux := 7, nodeId := 11 }
]⟩

theorem zero_argument_ffi_policy_accepts : verifyProgram zeroArgumentFfiProgram = none := by decide

def missingZeroArgumentFfiPolicyProgram : Program :=
  { zeroArgumentFfiProgram with nodes := zeroArgumentFfiProgram.nodes.extract 0 10 }

theorem missing_zero_argument_ffi_policy_rejects :
    verifyProgram missingZeroArgumentFfiPolicyProgram = some ⟨.malformed, 5, 8⟩ := by decide

/-- A concrete aggregate label describes field payloads, not the identity of the allocation that
    contains them.  A fixed-offset field load therefore retains an explicit T025 class with an
    empty value-selection mask; dynamic address and index instructions select their operands. -/
def fixedFieldAddressProgram : Program := ⟨#[
  semanticManifest 1 2 1 2 3,
  { minimalSemanticFunction with required := 1, ceiling := 2 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 3 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 0, aux := 0, nodeId := 4 },
  { minimalSemanticBlock with required := 2, nodeId := 5 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 2, ceiling := 3, aux := 17, nodeId := 6 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 6, actual := 0, required := 1, ceiling := 0, aux := 0, nodeId := 7 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 3,
    origin := 6, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 8 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 3,
    origin := 6, actual := 2, required := 0, ceiling := 0, aux := 0, nodeId := 9 },
  { minimalSemanticHalt with nodeId := 10 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 11 },
  { op := .semLabelContract, labelA := .secretCT, labelB := .secretCT, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 12 },
  { op := .semLabelContract, labelA := .secretCT, labelB := .secretCT, flags := 1,
    origin := 1, actual := 2, required := 1, ceiling := 0, aux := 1, nodeId := 13 },
  { op := .semPolicyClass, labelA := .pub, labelB := .pub, flags := 1,
    origin := 6, actual := 0, required := 25, ceiling := 0, aux := 5, nodeId := 14 }
]⟩

theorem fixed_field_address_policy_accepts : verifyProgram fixedFieldAddressProgram = none := by decide

def missingFixedFieldAddressPolicyProgram : Program :=
  { fixedFieldAddressProgram with nodes := fixedFieldAddressProgram.nodes.extract 0 13 }

theorem missing_fixed_field_address_policy_rejects :
    verifyProgram missingFixedFieldAddressPolicyProgram = some ⟨.malformed, 6, 8⟩ := by decide

/-- Spawn payloads cross the actor boundary and remain subject to T028, but the returned actor
    identity is not data-derived from those payloads.  A Secret capability may therefore initialize
    a Secret actor parameter without falsely tainting the separately Public actor handle. -/
def secretActorSpawnPayloadProgram : Program := ⟨#[
  semanticManifest 1 2 1 2 3,
  { minimalSemanticFunction with required := 1, ceiling := 2 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 3 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 0, aux := 0, nodeId := 4 },
  { minimalSemanticBlock with required := 2, nodeId := 5 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 2, ceiling := 3, aux := 8, nodeId := 6 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 6, actual := 0, required := 1, ceiling := 0, aux := 0, nodeId := 7 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 3,
    origin := 6, actual := 1, required := 1, ceiling := 0, aux := 0, nodeId := 8 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 3,
    origin := 6, actual := 2, required := 0, ceiling := 0, aux := 0, nodeId := 9 },
  { minimalSemanticHalt with nodeId := 10 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 11 },
  { op := .semLabelContract, labelA := .secret, labelB := .secret, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 12 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 1, ceiling := 0, aux := 1, nodeId := 13 },
  { op := .semPolicyClass, labelA := .pub, labelB := .pub, flags := 1,
    origin := 6, actual := 1, required := 28, ceiling := 0, aux := 8, nodeId := 14 }
]⟩

theorem secret_actor_spawn_payload_public_handle_accepts :
    verifyProgram secretActorSpawnPayloadProgram = none := by decide

def missingActorSpawnPolicyProgram : Program :=
  { secretActorSpawnPayloadProgram with nodes := secretActorSpawnPayloadProgram.nodes.extract 0 13 }

theorem missing_actor_spawn_policy_rejects :
    verifyProgram missingActorSpawnPolicyProgram = some ⟨.malformed, 6, 8⟩ := by decide

/-- Deserialize is the other side of the actor-boundary distinction: unlike spawn and ask, its
    result is data-derived from the input buffer, so Secret input cannot satisfy a Public result
    contract.  This pair makes suppression of every actor-boundary result edge theorem-breaking. -/
def secretActorDeserializeProgram : Program := ⟨#[
  semanticManifest 1 3 1 2 2,
  { minimalSemanticFunction with required := 1, ceiling := 3 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 3 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 0, aux := 0, nodeId := 4 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 3, required := 0, ceiling := 0, aux := 0, nodeId := 5 },
  { minimalSemanticBlock with required := 2, nodeId := 6 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 3, ceiling := 2, aux := 8, nodeId := 7 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 7, actual := 0, required := 1, ceiling := 0, aux := 0, nodeId := 8 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 7, actual := 1, required := 2, ceiling := 0, aux := 0, nodeId := 9 },
  { minimalSemanticHalt with nodeId := 10 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 11 },
  { op := .semLabelContract, labelA := .secret, labelB := .secret, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 12 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 0, ceiling := 0, aux := 0, nodeId := 13 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 3, required := 1, ceiling := 0, aux := 1, nodeId := 14 },
  { op := .semPolicyClass, labelA := .pub, labelB := .pub, flags := 1,
    origin := 7, actual := 3, required := 28, ceiling := 0, aux := 8, nodeId := 15 }
]⟩

theorem secret_actor_deserialize_payload_public_value_rejects :
    verifyProgram secretActorDeserializeProgram = some ⟨.flow, 14, 1⟩ := by decide

/-- An abortive effect transfer is implemented by a runtime return from an evidence closure, but
    it is not a source-level output of the performing function.  The semantic opcode keeps the
    Secret handler payload on the effect trace without checking it against that function's Public
    normal-return contract. -/
def abortiveEffectTransferProgram : Program := ⟨#[
  semanticManifest 1 1 1 1 1,
  { minimalSemanticFunction with required := 1, ceiling := 1 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 3 },
  { minimalSemanticBlock with required := 1, nodeId := 4 },
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 1, aux := 36, nodeId := 5 },
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 5, actual := 0, required := 1, ceiling := 0, aux := 0, nodeId := 6 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 7 },
  { op := .semLabelContract, labelA := .secret, labelB := .secret, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 8 }
]⟩

theorem abortive_effect_transfer_accepts :
    verifyProgram abortiveEffectTransferProgram = none := by decide

def abortiveEffectAsOutputMutant : Program :=
  { abortiveEffectTransferProgram with nodes := abortiveEffectTransferProgram.nodes.set! 4 (
      { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
        origin := 1, actual := 1, required := 0, ceiling := 1, aux := 28, nodeId := 5 } : Node) }

theorem abortive_effect_as_output_mutant_rejects :
    verifyProgram abortiveEffectAsOutputMutant = some ⟨.flow, 5, 1⟩ := by decide

/-! A dynamic closure selector is a control dependency.  This compact graph witness does not rely
    on Rust projection: the selector seed must taint every possible callee entry directly in the
    Lean least solution.  Replacing `addSemanticClosureEdges` with the old direct-call helper drops
    exactly that edge. -/

def secretClosureInstruction : Node :=
  { op := .semInstruction, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 2, ceiling := 1, aux := 7, nodeId := 6 }

def secretClosureSelectorGraph : Program := ⟨#[
  semanticManifest 2 2 2 3 1,
  { op := .semFunction, labelA := .pub, labelB := .pub, flags := 0,
    origin := 1, actual := 1, required := 2, ceiling := 2, aux := 0, nodeId := 2 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 1, required := 7, ceiling := 0, aux := 0, nodeId := 3 },
  { op := .semValue, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 2, required := 7, ceiling := 0, aux := 0, nodeId := 4 },
  { minimalSemanticBlock with origin := 1, actual := 1, required := 2, nodeId := 5 },
  secretClosureInstruction,
  { op := .semOperand, labelA := .pub, labelB := .pub, flags := 0,
    origin := 6, actual := 0, required := 1, ceiling := 0, aux := 0, nodeId := 7 },
  { minimalSemanticHalt with origin := 1, actual := 1, nodeId := 8 },
  { op := .semFunction, labelA := .pub, labelB := .pub, flags := 0,
    origin := 2, actual := 1, required := 1, ceiling := 0, aux := 0, nodeId := 9 },
  { minimalSemanticBlock with origin := 2, actual := 1, required := 1, nodeId := 10 },
  { minimalSemanticHalt with origin := 2, actual := 1, nodeId := 11 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 1, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 12 },
  { op := .semLabelContract, labelA := .pub, labelB := .pub, flags := 1,
    origin := 2, actual := 0, required := 2, ceiling := 0, aux := 2, nodeId := 13 },
  { op := .semLabelContract, labelA := .secret, labelB := .secret, flags := 1,
    origin := 1, actual := 1, required := 0, ceiling := 0, aux := 0, nodeId := 14 },
  { op := .semLabelContract, labelA := .secret, labelB := .secret, flags := 1,
    origin := 1, actual := 2, required := 1, ceiling := 0, aux := 1, nodeId := 15 },
  { op := .semPolicyClass, labelA := .pub, labelB := .pub, flags := 1,
    origin := 6, actual := 1, required := 25, ceiling := 0, aux := 5, nodeId := 16 }
]⟩

theorem secret_closure_selector_taints_every_callee_entry :
    labelAt (semanticLabels secretClosureSelectorGraph) 10 = .secret := by
  set_option maxRecDepth 10000 in decide

def closureCallerPcEdgeMutant : Array (List UInt32) :=
  let p := secretClosureSelectorGraph
  let index := buildSemanticIndex p
  addSemanticCallEdges p index secretClosureInstruction 5 4
    (Array.replicate (p.nodes.size + 1) [])

theorem direct_call_only_mutant_omits_the_dynamic_callee_edge :
    !(closureCallerPcEdgeMutant.getD 3 []).contains 10 ∧
      !(closureCallerPcEdgeMutant.getD 5 []).contains 10 := by decide

end LambdaSigil.Combined
