import LambdaSigil.V9OccurrenceDataflow
import LambdaSigil.V9BoundaryContractsSecurity
import LambdaSigil.DecoderNodeIds

/-!
# Least semantic labels extending source and exact host-result seeds

Canonical source cells are derived from actual boundary extraction's per-record checks. The
unchanged semantic adjacency and four-times-cell-count worklist then yield a least solution
containing all old source seeds and the new host seeds. No fixed point or relational policy is
assumed. This layer does not turn declaration extraction into host approval or production safety.
-/

namespace LambdaSigil.Combined.V9.OccurrenceDataflowSecurity

open BoundaryContracts OccurrenceDataflow SemanticDataflow SemanticIndexBounds

theorem extracted_base_has_canonical_node_ids {program : Program} {contracts : Index}
    (h : BoundaryContracts.extract? program = some contracts) : CanonicalNodeIds program.base := by
  obtain ⟨source, _, hchecks⟩ := extracted_components h
  intro position hposition
  have hbound : position < program.base.nodes.size := by simpa using hposition
  have hrow := checked_record hchecks hbound
  simp only [recordMatches, Array.getElem?_eq_getElem hbound] at hrow
  cases hsite : contracts.sites[position]? with
  | none => simp [hsite] at hrow
  | some site =>
      simp only [hsite, Bool.and_eq_true, beq_iff_eq] at hrow
      simpa using hrow.1

theorem analyzed_components {program : Program} {analysis : Analysis}
    (h : analyze? program = some analysis) :
    BoundaryContracts.extract? program = some analysis.contracts ∧
      analysis.semanticIndex = buildSemanticIndex program.base ∧
      hostSeeds? program analysis.contracts analysis.semanticIndex = some analysis.hostSeeds ∧
      analysis.seeds = seededLabels program analysis.semanticIndex analysis.hostSeeds ∧
      analysis.labels = saturate program analysis.semanticIndex analysis.seeds ∧
      hostSeedsFlowB analysis.hostSeeds analysis.labels = true := by
  unfold analyze? at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨contracts, hcontracts, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨seeds, hseeds, h⟩ := h
  split at h
  · cases h
    exact ⟨hcontracts, rfl, hseeds, rfl, rfl, by assumption⟩
  · cases h

theorem applyHostSeeds_preserves_source (seeds : Array HostSeed) (labels : Array Label) :
    ArrayFlows labels (applyHostSeeds seeds labels) := by
  unfold applyHostSeeds
  rw [← Array.foldl_toList]
  induction seeds.toList generalizing labels with
  | nil => exact ArrayFlows.refl labels
  | cons seed seeds ih =>
      exact (ArrayFlows.raise labels seed.cell seed.label).trans (ih _)

theorem seededLabels_size (program : Program) (index : SemanticIndex) (seeds : Array HostSeed) :
    (seededLabels program index seeds).size = semanticTaintCellCount program.base := by
  exact (applyHostSeeds_preserves_source seeds
    (semanticSeedLabelsWithIndex program.base index)).1.symm.trans
      (semanticSeedLabelsWithIndex_size program.base index)

theorem saturate_preserves_seeds (program : Program) (index : SemanticIndex) (seeds : Array Label) :
    ArrayFlows seeds (saturate program index seeds) :=
  saturateGraphWorklist_inflationary _ _ _ _

def ExtendedSolution (program : Program) (index : SemanticIndex) (seeds : Array HostSeed)
    (labels : Array Label) : Prop :=
  Solution (semanticTaintAdjacencyWithIndex program.base index) (seededLabels program index seeds) labels

theorem saturate_extended_seeds_is_least {program : Program} {index : SemanticIndex}
    {seeds : Array HostSeed}
    (hbounds : IndexCellBounds (semanticTaintCellCount program.base) index) :
    ExtendedSolution program index seeds (saturate program index (seededLabels program index seeds)) ∧
      ∀ candidate, ExtendedSolution program index seeds candidate →
        ArrayFlows (saturate program index (seededLabels program index seeds)) candidate := by
  have hsize := seededLabels_size program index seeds
  have hgraph := semanticTaintAdjacencyWithIndex_well_formed program.base index hbounds
  have hgraph' : AdjacencyWellFormed (seededLabels program index seeds).size
      (semanticTaintAdjacencyWithIndex program.base index) := by simpa [hsize] using hgraph
  have hclosed := initial_work_edges_closed hgraph'
  have hseed := saturate_preserves_seeds program index (seededLabels program index seeds)
  have hresultSize : (saturate program index (seededLabels program index seeds)).size =
      (seededLabels program index seeds).size := hseed.1.symm
  have hedges : EdgesClosed (semanticTaintAdjacencyWithIndex program.base index)
      (saturate program index (seededLabels program index seeds)) := by
    simpa only [saturate, hsize] using hclosed
  refine ⟨⟨hseed, hgraph', ?_⟩, ?_⟩
  · intro source hsource target htarget
    exact hedges source (by simpa [hresultSize] using hsource) target htarget
  · intro candidate hcandidate
    unfold saturate
    apply saturateGraphWorklist_below_solution hcandidate rfl hcandidate.1
    intro cell hcell
    simp only [List.mem_map, List.mem_range] at hcell
    obtain ⟨source, hsource, rfl⟩ := hcell
    have hmod : (UInt32.ofNat source).toNat ≤ source := Nat.mod_le _ _
    rw [hsize]
    omega

theorem analyzed_labels_are_least {program : Program} {analysis : Analysis}
    (h : analyze? program = some analysis) :
    ExtendedSolution program analysis.semanticIndex analysis.hostSeeds analysis.labels ∧
      ∀ candidate, ExtendedSolution program analysis.semanticIndex analysis.hostSeeds candidate →
        ArrayFlows analysis.labels candidate := by
  obtain ⟨hcontracts, hindex, _, hseeds, hlabels, _⟩ := analyzed_components h
  have hbounds : IndexCellBounds (semanticTaintCellCount program.base) analysis.semanticIndex := by
    rw [hindex]
    exact buildSemanticIndex_cell_bounds_of_canonical (extracted_base_has_canonical_node_ids hcontracts)
  simpa [hlabels, hseeds] using saturate_extended_seeds_is_least (seeds := analysis.hostSeeds) hbounds

theorem analyzed_labels_preserve_source_seeds {program : Program} {analysis : Analysis}
    (h : analyze? program = some analysis) :
    ArrayFlows (semanticSeedLabels program.base) analysis.labels := by
  obtain ⟨_, hindex, _, hseeds, hlabels, _⟩ := analyzed_components h
  have hsource := applyHostSeeds_preserves_source analysis.hostSeeds
    (semanticSeedLabelsWithIndex program.base analysis.semanticIndex)
  have hresult := saturate_preserves_seeds program analysis.semanticIndex analysis.seeds
  rw [← hlabels] at hresult
  rw [hseeds] at hresult
  simpa [semanticSeedLabels, hindex] using hsource.trans hresult

theorem analyzed_host_seeds_flow {program : Program} {analysis : Analysis}
    (h : analyze? program = some analysis) {seed : HostSeed} (hseed : seed ∈ analysis.hostSeeds) :
    seed.cell.toNat < analysis.labels.size ∧
      seed.label.flowsTo (labelAt analysis.labels seed.cell) = true := by
  have hchecks := (analyzed_components h).2.2.2.2.2
  rw [hostSeedsFlowB, Array.all_eq_true_iff_forall_mem] at hchecks
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using hchecks seed hseed

/-- A result seed names the actual indexed semValue destination and the extracted host result
    label. Neither an instruction ID nor a function-local value ID is substituted for its cell. -/
theorem hostSeed_has_exact_destination {program : Program} {contracts : Index}
    {index : SemanticIndex} {owner : Node} {seed : HostSeed}
    (h : hostSeed? program contracts index owner = some (some seed)) :
    owner.op = .semInstruction ∧ owner.aux = 15 ∧ owner.required ≠ 0 ∧
      ∃ position contract result value,
        site? contracts owner.nodeId = some ⟨owner.nodeId, owner.origin, .ffi position contract⟩ ∧
        contract.results.size = 1 ∧ contract.results[0]? = some result ∧
        indexedSemanticValueNode? index owner.origin owner.required = some value ∧
        value.op = .semValue ∧ value.origin = owner.origin ∧ value.actual = owner.required ∧
        seed = ⟨owner.nodeId, owner.origin, owner.required, value.nodeId, result.label⟩ := by
  unfold hostSeed? at h
  split at h
  · cases h
  · rename_i howner
    have howner' : owner.op = .semInstruction ∧ owner.aux = 15 := by
      have hparts : ¬(owner.op != .semInstruction) = true ∧ owner.aux = 15 := by
        simpa only [Bool.or_eq_true, bne_iff_ne, not_or, ne_eq, not_not] using howner
      have hop : ∀ op : Op, ¬(op != .semInstruction) = true → op = .semInstruction := by
        intro op
        cases op <;> decide
      exact ⟨hop owner.op hparts.1, hparts.2⟩
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨site, hsite, h⟩ := h
    split at h
    · cases h
    · rename_i hidentity
      have hidentity' : site.owner = owner.nodeId ∧ site.functionId = owner.origin := by
        simpa only [Bool.or_eq_true, bne_iff_ne, not_or, ne_eq, not_not] using hidentity
      cases hkind : site.kind with
      | ordinary op => simp [hkind] at h
      | actor position contract => simp [hkind] at h
      | ffi position contract =>
          simp only [hkind] at h
          split at h
          · split at h <;> cases h
          · rename_i hrequired
            split at h
            · cases h
            · rename_i hresults
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨result, hresult, value, hvalue, h⟩ := h
              split at h
              · cases h
              · rename_i hvalueIdentity
                have hvalueIdentity' : value.op = .semValue ∧ value.origin = owner.origin ∧
                    value.actual = owner.required := by
                  have hparts : ¬(value.op != .semValue) = true ∧ value.origin = owner.origin ∧
                      value.actual = owner.required := by
                    simpa only [Bool.or_eq_true, bne_iff_ne, not_or, ne_eq, not_not, and_assoc]
                      using hvalueIdentity
                  have hop : ∀ op : Op, ¬(op != .semValue) = true → op = .semValue := by
                    intro op
                    cases op <;> decide
                  exact ⟨hop value.op hparts.1, hparts.2⟩
                cases h
                refine ⟨howner'.1, howner'.2, ?_, position, contract, result, value, ?_, ?_,
                  hresult, hvalue, hvalueIdentity'.1, hvalueIdentity'.2.1,
                  hvalueIdentity'.2.2, rfl⟩
                · simpa only [beq_iff_eq] using hrequired
                · cases site
                  simp_all only
                · simpa only [bne_iff_ne, ne_eq, not_not] using hresults

/-- A successful iterative fold contains the exact result seed of every source owner it
    traversed. This proof is independent of the final `hostSeedsFlowB` postcheck, so omitting a
    computed seed cannot be smuggled in as an assumed premise. -/
theorem collected_host_seed_is_present {program : Program} {contracts : Index}
    {index : SemanticIndex} {seeds : Array HostSeed}
    (h : collectHostSeeds? program contracts index = some seeds)
    {owner : Node} (howner : owner ∈ program.base.nodes) {seed : HostSeed}
    (hseed : hostSeed? program contracts index owner = some (some seed)) : seed ∈ seeds := by
  have fold_none : ∀ nodes : List Node,
      nodes.foldl (collectHostSeedStep? program contracts index) none = none := by
    intro nodes
    induction nodes with
    | nil => rfl
    | cons head tail ih =>
        rw [List.foldl_cons]
        change tail.foldl (collectHostSeedStep? program contracts index) none = none
        exact ih
  have fold_complete : ∀ (nodes : List Node) (initial result : Array HostSeed),
      nodes.foldl (collectHostSeedStep? program contracts index) (some initial) = some result →
        (∀ candidate ∈ initial, candidate ∈ result) ∧
          ∀ candidateOwner ∈ nodes, ∀ candidateSeed,
            hostSeed? program contracts index candidateOwner = some (some candidateSeed) →
              candidateSeed ∈ result := by
    intro nodes
    induction nodes with
    | nil =>
        intro initial result hresult
        cases hresult
        exact ⟨fun _ hcandidate => hcandidate, by simp⟩
    | cons head tail ih =>
        intro initial result hresult
        rw [List.foldl_cons] at hresult
        cases hhead : hostSeed? program contracts index head with
        | none =>
            have hstep : collectHostSeedStep? program contracts index (some initial) head = none := by
              simp [collectHostSeedStep?, hhead]
            rw [hstep, fold_none] at hresult
            cases hresult
        | some headSeed =>
            cases headSeed with
            | none =>
                have hstep : collectHostSeedStep? program contracts index (some initial) head =
                    some initial := by simp [collectHostSeedStep?, hhead]
                rw [hstep] at hresult
                have htail := ih initial result hresult
                refine ⟨htail.1, ?_⟩
                intro candidateOwner hcandidateOwner candidateSeed hcandidateSeed
                rcases List.mem_cons.mp hcandidateOwner with rfl | htailOwner
                · rw [hhead] at hcandidateSeed
                  cases hcandidateSeed
                · exact htail.2 candidateOwner htailOwner candidateSeed hcandidateSeed
            | some headSeed =>
                have hstep : collectHostSeedStep? program contracts index (some initial) head =
                    some (initial.push headSeed) := by simp [collectHostSeedStep?, hhead]
                rw [hstep] at hresult
                have htail := ih (initial.push headSeed) result hresult
                refine ⟨?_, ?_⟩
                · intro candidate hcandidate
                  exact htail.1 candidate (by simp [hcandidate])
                · intro candidateOwner hcandidateOwner candidateSeed hcandidateSeed
                  rcases List.mem_cons.mp hcandidateOwner with rfl | htailOwner
                  · rw [hhead] at hcandidateSeed
                    cases hcandidateSeed
                    exact htail.1 headSeed (by simp)
                  · exact htail.2 candidateOwner htailOwner candidateSeed hcandidateSeed
  unfold collectHostSeeds? at h
  rw [← Array.foldl_toList] at h
  exact (fold_complete program.base.nodes.toList #[] seeds h).2
    owner (by simpa using howner) seed hseed

theorem analyzed_owner_result_flows {program : Program} {analysis : Analysis}
    (h : analyze? program = some analysis) {owner : Node}
    (howner : owner ∈ program.base.nodes) {seed : HostSeed}
    (hseed : hostSeed? program analysis.contracts analysis.semanticIndex owner = some (some seed)) :
    seed.cell.toNat < analysis.labels.size ∧
      seed.label.flowsTo (labelAt analysis.labels seed.cell) = true := by
  apply analyzed_host_seeds_flow h
  exact collected_host_seed_is_present (analyzed_components h).2.2.1 howner hseed

end LambdaSigil.Combined.V9.OccurrenceDataflowSecurity
