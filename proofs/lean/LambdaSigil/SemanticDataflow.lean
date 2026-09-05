import LambdaSigil.SemanticSecurity

/-!
# Semantic-label worklist invariants

The decoded machine uses its own adjacency and seed arrays, including closure-summary cells.
These lemmas concern that actual worklist rather than the legacy graph carried in separate CSIR
records. Seed preservation and the lower-than-every-solution property hold for every fuel budget;
they do not by themselves establish that an exhausted worklist is a solution. No production
acceptance rule, fuel budget, or relational claim is changed in this module.
-/

namespace LambdaSigil.Combined.SemanticDataflow

private theorem label_flows_refl (label : Label) : label.flowsTo label = true := by
  cases label <;> decide

private theorem label_flows_trans {a b c : Label} (hab : a.flowsTo b = true)
    (hbc : b.flowsTo c = true) : a.flowsTo c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [Label.flowsTo, Label.rank]

private theorem label_flows_lub_left (a b : Label) : a.flowsTo (a.lub b) = true := by
  cases a <;> cases b <;> decide

private theorem label_lub_flows {a b c : Label} (ha : a.flowsTo c = true)
    (hb : b.flowsTo c = true) : (a.lub b).flowsTo c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [Label.flowsTo, Label.lub, Label.rank]

/-- Shape-preserving pointwise information order, indexed by the machine's real cell type. -/
def ArrayFlows (lower upper : Array Label) : Prop :=
  lower.size = upper.size ∧ ∀ cell : UInt32, cell.toNat < lower.size →
    (labelAt lower cell).flowsTo (labelAt upper cell) = true

theorem ArrayFlows.refl (labels : Array Label) : ArrayFlows labels labels :=
  ⟨rfl, fun cell _ => label_flows_refl (labelAt labels cell)⟩

theorem ArrayFlows.trans {lower middle upper : Array Label}
    (hleft : ArrayFlows lower middle) (hright : ArrayFlows middle upper) :
    ArrayFlows lower upper := by
  refine ⟨hleft.1.trans hright.1, ?_⟩
  intro cell hcell
  exact label_flows_trans (hleft.2 cell hcell)
    (hright.2 cell (by simpa [← hleft.1] using hcell))

theorem ArrayFlows.raise (labels : Array Label) (cell : UInt32) (incoming : Label) :
    ArrayFlows labels (raiseCell labels cell incoming) := by
  refine ⟨by simp [raiseCell], ?_⟩
  intro observed hbound
  have hget := Array.getElem_setIfInBounds (xs := labels) (i := cell.toNat)
    (a := (labelAt labels cell).lub incoming) (j := observed.toNat) hbound
  by_cases heq : cell.toNat = observed.toNat
  · have hcell : cell = observed := UInt32.ext heq
    subst cell
    simpa [raiseCell, labelAt, Array.getD, hbound, hget] using
      label_flows_lub_left (labelAt labels observed) incoming
  · simpa [raiseCell, labelAt, Array.getD, hbound, hget, heq] using
      label_flows_refl (labelAt labels observed)

theorem ArrayFlows.set_below {lower upper : Array Label} (h : ArrayFlows lower upper)
    (cell : UInt32) (raised : Label)
    (hvalue : raised.flowsTo (labelAt upper cell) = true) :
    ArrayFlows (lower.setIfInBounds cell.toNat raised) upper := by
  refine ⟨by simpa using h.1, ?_⟩
  intro observed hbound
  have hbound' : observed.toNat < lower.size := by simpa using hbound
  have hget := Array.getElem_setIfInBounds (xs := lower) (i := cell.toNat)
    (a := raised) (j := observed.toNat) hbound'
  by_cases heq : cell.toNat = observed.toNat
  · have hcell : cell = observed := UInt32.ext heq
    subst cell
    simpa [labelAt, Array.getD, hbound', hget] using hvalue
  · simpa [labelAt, Array.getD, hbound', hget, heq] using h.2 observed hbound'

theorem relaxTargets_inflationary (source : Label) (targets : List UInt32)
    (labels : Array Label) (work : List UInt32) :
    ArrayFlows labels (relaxTargets source targets labels work).1 := by
  induction targets generalizing labels work with
  | nil => exact ArrayFlows.refl labels
  | cons target rest ih =>
      simp only [relaxTargets]
      split
      · exact ih labels work
      · exact (ArrayFlows.raise labels target source).trans
          (ih (raiseCell labels target source) (target :: work))

theorem saturateGraphWorklist_inflationary (adjacency : Array (List UInt32))
    (fuel : Nat) (work : List UInt32) (labels : Array Label) :
    ArrayFlows labels (saturateGraphWorklist adjacency fuel work labels) := by
  induction fuel generalizing work labels with
  | zero => exact ArrayFlows.refl labels
  | succ fuel ih =>
      cases work with
      | nil => exact ArrayFlows.refl labels
      | cons cell work =>
          exact (relaxTargets_inflationary (labelAt labels cell)
            (adjacency.getD cell.toNat []) labels work).trans (ih _ _)

/-- All graph endpoints fit the seed array. This is a structural condition, not a fixed-point
    premise; the semantic decoder's cell-allocation and edge constructors must discharge it. -/
def AdjacencyWellFormed (count : Nat) (adjacency : Array (List UInt32)) : Prop :=
  ∀ source : UInt32, source.toNat < count →
    ∀ target ∈ adjacency.getD source.toNat [], target.toNat < count

def WorkValid (count : Nat) (work : List UInt32) : Prop :=
  ∀ cell ∈ work, cell.toNat < count

/-- An algorithm-independent candidate solution contains every seed and closes every edge. -/
def Solution (adjacency : Array (List UInt32)) (seeds labels : Array Label) : Prop :=
  ArrayFlows seeds labels ∧ AdjacencyWellFormed seeds.size adjacency ∧
    ∀ source : UInt32, source.toNat < seeds.size →
      ∀ target ∈ adjacency.getD source.toNat [],
        (labelAt labels source).flowsTo (labelAt labels target) = true

theorem relaxTargets_below_solution {count : Nat} {sourceCell : UInt32}
    {sourceLabel : Label} {targets : List UInt32} {labels solution : Array Label}
    {work : List UInt32} (hsize : labels.size = count)
    (hbelow : ArrayFlows labels solution)
    (hsource : sourceLabel.flowsTo (labelAt solution sourceCell) = true)
    (hedges : ∀ target ∈ targets, target.toNat < count ∧
      (labelAt solution sourceCell).flowsTo (labelAt solution target) = true) :
    ArrayFlows (relaxTargets sourceLabel targets labels work).1 solution := by
  induction targets generalizing labels work with
  | nil => exact hbelow
  | cons target rest ih =>
      have hedge := hedges target (by simp)
      have hold := hbelow.2 target (by simpa [hsize] using hedge.1)
      have hraised : ((labelAt labels target).lub sourceLabel).flowsTo
          (labelAt solution target) = true :=
        label_lub_flows hold (label_flows_trans hsource hedge.2)
      have hrest : ∀ candidate ∈ rest, candidate.toNat < count ∧
          (labelAt solution sourceCell).flowsTo (labelAt solution candidate) = true := by
        intro candidate hc
        exact hedges candidate (by simp [hc])
      simp only [relaxTargets]
      split
      · exact ih hsize hbelow hrest
      · exact ih (by simpa using hsize) (hbelow.set_below target _ hraised) hrest

theorem relaxTargets_preserves_work_valid {count : Nat} {source : Label}
    {targets work : List UInt32} {labels : Array Label} (hw : WorkValid count work)
    (ht : ∀ target ∈ targets, target.toNat < count) :
    WorkValid count (relaxTargets source targets labels work).2 := by
  induction targets generalizing labels work with
  | nil => exact hw
  | cons target rest ih =>
      have htarget := ht target (by simp)
      have hrest : ∀ candidate ∈ rest, candidate.toNat < count := by
        intro candidate hc
        exact ht candidate (by simp [hc])
      simp only [relaxTargets]
      split
      · exact ih hw hrest
      · apply ih _ hrest
        intro cell hc
        simp only [List.mem_cons] at hc
        exact hc.elim (fun he => he ▸ htarget) (hw cell)

theorem saturateGraphWorklist_below_solution {adjacency : Array (List UInt32)}
    {seeds solution labels : Array Label} {fuel : Nat} {work : List UInt32}
    (hsolution : Solution adjacency seeds solution) (hsize : labels.size = seeds.size)
    (hbelow : ArrayFlows labels solution) (hw : WorkValid seeds.size work) :
    ArrayFlows (saturateGraphWorklist adjacency fuel work labels) solution := by
  induction fuel generalizing work labels with
  | zero => exact hbelow
  | succ fuel ih =>
      cases work with
      | nil => exact hbelow
      | cons cell work =>
          have hcell : cell.toNat < seeds.size := hw cell (by simp)
          have hsource := hbelow.2 cell (by simpa [hsize] using hcell)
          have htargets : ∀ target ∈ adjacency.getD cell.toNat [],
              target.toNat < seeds.size ∧
                (labelAt solution cell).flowsTo (labelAt solution target) = true := by
            intro target ht
            exact ⟨hsolution.2.1 cell hcell target ht, hsolution.2.2 cell hcell target ht⟩
          have hbelow' := relaxTargets_below_solution (work := work)
            hsize hbelow hsource htargets
          have hwrest : WorkValid seeds.size work := by
            intro candidate hc
            exact hw candidate (by simp [hc])
          have hw' := relaxTargets_preserves_work_valid (source := labelAt labels cell)
            (labels := labels) hwrest (fun target ht => (htargets target ht).1)
          exact ih (hbelow'.1.trans hsolution.1.1.symm) hbelow' hw'

/-- Remaining strict label rises. The lattice has ranks zero through three. -/
def remainingRank : List Label → Nat
  | [] => 0
  | label :: rest => 3 - label.rank + remainingRank rest

theorem remainingRank_le (labels : List Label) : remainingRank labels ≤ 3 * labels.length := by
  induction labels with
  | nil => simp [remainingRank]
  | cons label rest ih => simp only [remainingRank, List.length_cons]; omega

private theorem rank_lub_strict_of_changed {old source : Label}
    (h : (old.lub source).eqb old ≠ true) : old.rank < (old.lub source).rank := by
  cases old <;> cases source <;> simp_all [Label.lub, Label.eqb, Label.rank]

private theorem remainingRank_set_decreases (labels : List Label) (index : Nat)
    (raised : Label) (hindex : index < labels.length)
    (hraise : (labels.getD index .pub).rank < raised.rank) :
    remainingRank (labels.set index raised) + 1 ≤ remainingRank labels := by
  induction labels generalizing index with
  | nil => simp at hindex
  | cons label rest ih =>
      cases index with
      | zero =>
          simp only [List.getD_cons_zero] at hraise
          have hrank : raised.rank ≤ 3 := by cases raised <;> decide
          simp only [List.set_cons_zero, remainingRank]
          omega
      | succ index =>
          have hbound : index < rest.length := by simpa using hindex
          have hraise' : (rest.getD index .pub).rank < raised.rank := by simpa using hraise
          have hrest := ih index hbound hraise'
          simp only [List.set_cons_succ, remainingRank]
          omega

/-- Queue length plus the number of remaining strict rises pays for every future dequeue. -/
def workPotential (labels : Array Label) (work : List UInt32) : Nat :=
  work.length + remainingRank labels.toList

theorem relaxTargets_potential_le {source : Label} {targets work : List UInt32}
    {labels : Array Label} (htargets : ∀ target ∈ targets, target.toNat < labels.size) :
    workPotential (relaxTargets source targets labels work).1
        (relaxTargets source targets labels work).2 ≤ workPotential labels work := by
  induction targets generalizing labels work with
  | nil => exact Nat.le_refl _
  | cons target rest ih =>
      have htarget := htargets target (by simp)
      have hrest : ∀ candidate ∈ rest, candidate.toNat < labels.size := by
        intro candidate hc
        exact htargets candidate (by simp [hc])
      simp only [relaxTargets]
      split
      · exact ih hrest
      · rename_i hchanged
        have hstrict := rank_lub_strict_of_changed hchanged
        have hdecrease := remainingRank_set_decreases labels.toList target.toNat
          ((labelAt labels target).lub source) (by simpa using htarget)
          (by simpa [labelAt] using hstrict)
        have hrest' : ∀ candidate ∈ rest,
            candidate.toNat < (labels.setIfInBounds target.toNat
              ((labelAt labels target).lub source)).size := by simpa using hrest
        have htail := ih (work := target :: work) hrest'
        simp only [workPotential, List.length_cons, Array.toList_setIfInBounds] at *
        omega

/-- Operational completion means that the bounded evaluator has no pending source when fuel is
    zero. It is independent of any assumed graph solution or relational policy. -/
def WorklistFinished (adjacency : Array (List UInt32)) :
    Nat → List UInt32 → Array Label → Prop
  | 0, work, _ => work = []
  | _ + 1, [], _ => True
  | fuel + 1, cell :: work, labels =>
      let next := relaxTargets (labelAt labels cell) (adjacency.getD cell.toNat []) labels work
      WorklistFinished adjacency fuel next.2 next.1

theorem worklist_finished_of_potential {adjacency : Array (List UInt32)}
    {fuel : Nat} {labels : Array Label} {work : List UInt32}
    (hgraph : AdjacencyWellFormed labels.size adjacency) (hw : WorkValid labels.size work)
    (hfuel : workPotential labels work ≤ fuel) :
    WorklistFinished adjacency fuel work labels := by
  induction fuel generalizing labels work with
  | zero =>
      have hlength : work.length = 0 := by unfold workPotential at hfuel; omega
      cases work with
      | nil => rfl
      | cons cell rest => simp at hlength
  | succ fuel ih =>
      cases work with
      | nil => trivial
      | cons cell work =>
          have hcell := hw cell (by simp)
          have htargets := hgraph cell hcell
          have hsize := (relaxTargets_inflationary (labelAt labels cell)
            (adjacency.getD cell.toNat []) labels work).1
          have hgraph' : AdjacencyWellFormed
              (relaxTargets (labelAt labels cell) (adjacency.getD cell.toNat []) labels work).1.size
              adjacency := by rw [← hsize]; exact hgraph
          have hwrest : WorkValid labels.size work := by
            intro candidate hc
            exact hw candidate (by simp [hc])
          have hw' := relaxTargets_preserves_work_valid (source := labelAt labels cell)
            (labels := labels) hwrest htargets
          have hbudget := relaxTargets_potential_le (source := labelAt labels cell)
            (work := work) htargets
          apply ih hgraph' (by rw [← hsize]; exact hw')
          simp only [workPotential, List.length_cons] at hfuel hbudget ⊢
          omega

theorem initial_work_finished {adjacency : Array (List UInt32)} {labels : Array Label}
    (hgraph : AdjacencyWellFormed labels.size adjacency) :
    WorklistFinished adjacency (4 * labels.size)
      ((List.range labels.size).map UInt32.ofNat) labels := by
  apply worklist_finished_of_potential hgraph
  · intro cell hcell
    simp only [List.mem_map, List.mem_range] at hcell
    obtain ⟨source, hs, rfl⟩ := hcell
    have hmod : (UInt32.ofNat source).toNat ≤ source := Nat.mod_le _ _
    exact Nat.lt_of_le_of_lt hmod hs
  · have hbudget := remainingRank_le labels.toList
    simp only [workPotential, List.length_map, List.length_range]
    simp only [Array.length_toList] at hbudget
    omega

theorem relaxTargets_preserves_pending_members (source : Label) (targets : List UInt32)
    (labels : Array Label) (work : List UInt32) :
    ∀ cell ∈ work, cell ∈ (relaxTargets source targets labels work).2 := by
  induction targets generalizing labels work with
  | nil => intro cell hcell; exact hcell
  | cons target rest ih =>
      simp only [relaxTargets]
      split
      · exact ih labels work
      · intro cell hcell
        exact ih _ (target :: work) cell (by simp [hcell])

private theorem labelAt_set_ne (labels : Array Label) (cell observed : UInt32)
    (raised : Label) (hne : cell ≠ observed) :
    labelAt (labels.setIfInBounds cell.toNat raised) observed = labelAt labels observed := by
  have hne' : cell.toNat ≠ observed.toNat := fun heq => hne (UInt32.ext heq)
  by_cases hbound : observed.toNat < labels.size
  · have hget := Array.getElem_setIfInBounds (xs := labels) (i := cell.toNat)
      (a := raised) (j := observed.toNat) hbound
    simp [labelAt, Array.getD, hbound, hget, hne']
  · simp [labelAt, Array.getD, hbound]

private theorem labelAt_set_self (labels : Array Label) (cell : UInt32) (raised : Label)
    (hbound : cell.toNat < labels.size) :
    labelAt (labels.setIfInBounds cell.toNat raised) cell = raised := by
  simp [labelAt, Array.getD, hbound]

/-- An altered cell is always rescheduled. Thus a source absent from the resulting queue retains
    its old label, even while the labels of its outgoing targets rise. -/
theorem relaxTargets_unchanged_if_not_pending (source : Label) (targets : List UInt32)
    (labels : Array Label) (work : List UInt32) (cell : UInt32)
    (habsent : cell ∉ (relaxTargets source targets labels work).2) :
    labelAt (relaxTargets source targets labels work).1 cell = labelAt labels cell := by
  induction targets generalizing labels work with
  | nil => rfl
  | cons target rest ih =>
      simp only [relaxTargets] at habsent ⊢
      by_cases heq : ((labelAt labels target).lub source).eqb (labelAt labels target) = true
      · simp only [heq] at habsent ⊢
        exact ih labels work habsent
      · simp only [heq] at habsent ⊢
        have hne : target ≠ cell := by
          intro heq
          subst target
          exact habsent (relaxTargets_preserves_pending_members source rest _ (cell :: work)
            cell (by simp))
        exact (ih _ (target :: work) habsent).trans (labelAt_set_ne labels target cell _ hne)

private theorem incoming_flows_unchanged {old source : Label}
    (heq : (old.lub source).eqb old = true) : source.flowsTo old = true := by
  cases old <;> cases source <;> simp_all [Label.lub, Label.eqb, Label.flowsTo, Label.rank]

private theorem label_flows_lub_right (a b : Label) : b.flowsTo (a.lub b) = true := by
  cases a <;> cases b <;> decide

theorem relaxTargets_covers_targets {source : Label} {targets : List UInt32}
    {labels : Array Label} {work : List UInt32}
    (htargets : ∀ target ∈ targets, target.toNat < labels.size) :
    ∀ target ∈ targets,
      source.flowsTo (labelAt (relaxTargets source targets labels work).1 target) = true := by
  induction targets generalizing labels work with
  | nil => simp
  | cons head rest ih =>
      have hhead := htargets head (by simp)
      have hrest : ∀ target ∈ rest, target.toNat < labels.size := by
        intro target ht
        exact htargets target (by simp [ht])
      intro target htarget
      simp only [List.mem_cons] at htarget
      simp only [relaxTargets]
      split
      · rename_i heq
        rcases htarget with heqTarget | htarget
        · subst target
          exact label_flows_trans (incoming_flows_unchanged heq)
            ((relaxTargets_inflationary source rest labels work).2 head hhead)
        · exact ih hrest target htarget
      · rcases htarget with heqTarget | htarget
        · subst target
          have hbound : head.toNat <
              (labels.setIfInBounds head.toNat ((labelAt labels head).lub source)).size := by
            simpa using hhead
          have hflow := (relaxTargets_inflationary source rest
            (labels.setIfInBounds head.toNat ((labelAt labels head).lub source))
            (head :: work)).2 head hbound
          rw [labelAt_set_self labels head _ hhead] at hflow
          exact label_flows_trans (label_flows_lub_right _ _) hflow
        · exact ih (by simpa using hrest) target htarget

/-- Every edge is already satisfied unless its source remains scheduled. This is the operational
    invariant connecting an empty worklist to the algorithm-independent solution judgment. -/
def PendingEdges (adjacency : Array (List UInt32)) (labels : Array Label)
    (work : List UInt32) : Prop :=
  ∀ source : UInt32, source.toNat < labels.size →
    ∀ target ∈ adjacency.getD source.toNat [],
      (labelAt labels source).flowsTo (labelAt labels target) = true ∨ source ∈ work

theorem relaxTargets_preserves_pending_edges {adjacency : Array (List UInt32)}
    {labels : Array Label} {cell : UInt32} {work : List UInt32}
    (hcell : cell.toNat < labels.size)
    (hgraph : AdjacencyWellFormed labels.size adjacency)
    (hpending : PendingEdges adjacency labels (cell :: work)) :
    let next := relaxTargets (labelAt labels cell) (adjacency.getD cell.toNat []) labels work
    PendingEdges adjacency next.1 next.2 := by
  dsimp only
  intro source hsource target htarget
  let next := relaxTargets (labelAt labels cell) (adjacency.getD cell.toNat []) labels work
  by_cases hqueued : source ∈ next.2
  · exact Or.inr hqueued
  · apply Or.inl
    have hinflation := relaxTargets_inflationary (labelAt labels cell)
      (adjacency.getD cell.toNat []) labels work
    have hsource' : source.toNat < labels.size := by
      simpa only [← hinflation.1] using hsource
    have hunchanged := relaxTargets_unchanged_if_not_pending (labelAt labels cell)
      (adjacency.getD cell.toNat []) labels work source hqueued
    rw [hunchanged]
    by_cases heq : source = cell
    · subst source
      exact relaxTargets_covers_targets (hgraph cell hcell) target htarget
    · have hnotWork : source ∉ cell :: work := by
        intro hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with heq' | hmem
        · exact heq heq'
        · exact hqueued (relaxTargets_preserves_pending_members (labelAt labels cell)
            (adjacency.getD cell.toNat []) labels work source hmem)
      have hold := (hpending source hsource' target htarget).resolve_right hnotWork
      exact label_flows_trans hold (hinflation.2 target (hgraph source hsource' target htarget))

def EdgesClosed (adjacency : Array (List UInt32)) (labels : Array Label) : Prop :=
  ∀ source : UInt32, source.toNat < labels.size →
    ∀ target ∈ adjacency.getD source.toNat [],
      (labelAt labels source).flowsTo (labelAt labels target) = true

theorem saturateGraphWorklist_closed_of_finished {adjacency : Array (List UInt32)}
    {fuel : Nat} {labels : Array Label} {work : List UInt32}
    (hgraph : AdjacencyWellFormed labels.size adjacency) (hw : WorkValid labels.size work)
    (hpending : PendingEdges adjacency labels work)
    (hfinished : WorklistFinished adjacency fuel work labels) :
    EdgesClosed adjacency (saturateGraphWorklist adjacency fuel work labels) := by
  induction fuel generalizing labels work with
  | zero =>
      have hwork : work = [] := hfinished
      subst work
      intro source hsource target htarget
      exact (hpending source hsource target htarget).resolve_right (by simp)
  | succ fuel ih =>
      cases work with
      | nil =>
          intro source hsource target htarget
          exact (hpending source hsource target htarget).resolve_right (by simp)
      | cons cell work =>
          have hcell := hw cell (by simp)
          have hinflation := relaxTargets_inflationary (labelAt labels cell)
            (adjacency.getD cell.toNat []) labels work
          have hwrest : WorkValid labels.size work := by
            intro candidate hc
            exact hw candidate (by simp [hc])
          have hw' := relaxTargets_preserves_work_valid (source := labelAt labels cell)
            (labels := labels) hwrest (hgraph cell hcell)
          exact ih (by rw [← hinflation.1]; exact hgraph)
            (by rw [← hinflation.1]; exact hw')
            (relaxTargets_preserves_pending_edges hcell hgraph hpending) hfinished

theorem initial_work_edges_closed {adjacency : Array (List UInt32)} {labels : Array Label}
    (hgraph : AdjacencyWellFormed labels.size adjacency) :
    EdgesClosed adjacency (saturateGraphWorklist adjacency (4 * labels.size)
      ((List.range labels.size).map UInt32.ofNat) labels) := by
  apply saturateGraphWorklist_closed_of_finished hgraph
  · intro cell hcell
    simp only [List.mem_map, List.mem_range] at hcell
    obtain ⟨source, hs, rfl⟩ := hcell
    have hmod : (UInt32.ofNat source).toNat ≤ source := Nat.mod_le _ _
    exact Nat.lt_of_le_of_lt hmod hs
  · intro source hsource target _
    apply Or.inr
    exact List.mem_map.mpr ⟨source.toNat, List.mem_range.mpr hsource, by simp⟩
  · exact initial_work_finished hgraph

theorem seedSemanticNode_size (p : Program) (index : SemanticIndex)
    (labels : Array Label) (node : Node) :
    (seedSemanticNode p index labels node).size = labels.size := by
  unfold seedSemanticNode
  split <;> try rfl
  · split <;> try rfl
    split <;> try rfl
    split <;> try simp [raiseCell]
    split <;> simp
  · split <;> try rfl
    all_goals split <;> simp [raiseCell]

theorem semanticSeedLabelsWithIndex_size (p : Program) (index : SemanticIndex) :
    (semanticSeedLabelsWithIndex p index).size = semanticTaintCellCount p := by
  unfold semanticSeedLabelsWithIndex
  generalize hlabels : Array.replicate (semanticTaintCellCount p) Label.pub = initial
  have hinitial : initial.size = semanticTaintCellCount p := by rw [← hlabels]; simp
  rw [← Array.foldl_toList]
  have hfold : ∀ (nodes : List Node) (labels : Array Label),
      (nodes.foldl (seedSemanticNode p index) labels).size = labels.size := by
    intro nodes
    induction nodes with
    | nil => intro labels; rfl
    | cons node rest ih =>
        intro labels
        simpa [List.foldl_cons, seedSemanticNode_size] using
          ih (seedSemanticNode p index labels node)
  exact (hfold p.nodes.toList initial).trans hinitial

/-- Every semantic seed, including state and release seeds, survives the production worklist. -/
theorem semanticLabels_seed_inclusion (p : Program) :
    ArrayFlows (semanticSeedLabels p) (semanticLabels p) := by
  unfold semanticLabels semanticLabelsWithIndex semanticSeedLabels
  exact saturateGraphWorklist_inflationary _ _ _ _

def SemanticSolution (p : Program) (labels : Array Label) : Prop :=
  Solution (semanticTaintAdjacency p) (semanticSeedLabels p) labels

/-- The actual decoded-label computation is below every solution of its semantic graph, not
    merely every solution of the legacy graph. Edge closure of the computed result is separate. -/
theorem semanticLabels_below_every_solution {p : Program} {solution : Array Label}
    (hsolution : SemanticSolution p solution) :
    ArrayFlows (semanticLabels p) solution := by
  unfold semanticLabels semanticLabelsWithIndex
  apply saturateGraphWorklist_below_solution
      (adjacency := semanticTaintAdjacencyWithIndex p (buildSemanticIndex p))
      (seeds := semanticSeedLabels p) hsolution rfl hsolution.1
  intro cell hcell
  simp only [List.mem_map, List.mem_range] at hcell
  obtain ⟨source, hs, rfl⟩ := hcell
  have hmod : (UInt32.ofNat source).toNat ≤ source := Nat.mod_le _ _
  simpa [semanticSeedLabels, semanticSeedLabelsWithIndex_size] using Nat.lt_of_le_of_lt hmod hs

theorem semanticLabels_size (p : Program) :
    (semanticLabels p).size = semanticTaintCellCount p :=
  (semanticLabels_seed_inclusion p).1.symm.trans
    (semanticSeedLabelsWithIndex_size p (buildSemanticIndex p))

/-- With bounded endpoints, the production semantic worklist closes every actual decoded edge
    using its unchanged four-times-cell-count budget. No computed fixed point is assumed. -/
theorem semanticLabels_edges_closed {p : Program}
    (hgraph : AdjacencyWellFormed (semanticTaintCellCount p) (semanticTaintAdjacency p)) :
    EdgesClosed (semanticTaintAdjacency p) (semanticLabels p) := by
  have hseedsize : (semanticSeedLabels p).size = semanticTaintCellCount p :=
    semanticSeedLabelsWithIndex_size p (buildSemanticIndex p)
  have hgraph' : AdjacencyWellFormed (semanticSeedLabels p).size (semanticTaintAdjacency p) := by
    rw [hseedsize]
    exact hgraph
  simpa only [semanticLabels, semanticLabelsWithIndex, semanticSeedLabels,
    semanticTaintAdjacency, semanticSeedLabelsWithIndex_size] using initial_work_edges_closed hgraph'

/-- Leastness for the graph the raw semantic decoder actually consumes. The remaining production
    connection is the unary source/index endpoint invariant in `hgraph`, not a relational policy
    or a claim that the computed labels already form a fixed point. -/
theorem semanticLabels_is_least_solution {p : Program}
    (hgraph : AdjacencyWellFormed (semanticTaintCellCount p) (semanticTaintAdjacency p)) :
    SemanticSolution p (semanticLabels p) ∧
      ∀ candidate, SemanticSolution p candidate → ArrayFlows (semanticLabels p) candidate := by
  have hseedsize : (semanticSeedLabels p).size = semanticTaintCellCount p :=
    semanticSeedLabelsWithIndex_size p (buildSemanticIndex p)
  refine ⟨⟨semanticLabels_seed_inclusion p, ?_, ?_⟩,
    fun _ hcandidate => semanticLabels_below_every_solution hcandidate⟩
  · simpa only [hseedsize] using hgraph
  · intro source hsource target htarget
    exact semanticLabels_edges_closed hgraph source
      (by simpa only [hseedsize, semanticLabels_size] using hsource) target htarget

/-- Only target-bearing index fields need bounds. Return cells and argument source cells do not
    become unchecked targets merely because they are used to build an outgoing edge. -/
structure IndexCellBounds (count : Nat) (index : SemanticIndex) : Prop where
  block : ∀ functionId blockId cell,
    semanticBlockCell? index functionId blockId = some cell → cell.toNat < count
  value : ∀ functionId valueId cell,
    semanticValueCell? index functionId valueId = some cell → cell.toNat < count
  parameter : ∀ (functionId cell : UInt32),
    cell ∈ index.parameterCells.getD functionId.toNat [] → cell.toNat < count

theorem addSemanticEdge_preserves_bounds {count : Nat} {adjacency : Array (List UInt32)}
    (hgraph : AdjacencyWellFormed count adjacency) (source target : UInt32)
    (htarget : target.toNat < count) :
    AdjacencyWellFormed count (addSemanticEdge adjacency source target) := by
  unfold addSemanticEdge
  split
  · exact hgraph
  · intro observed hobserved candidate hcandidate
    by_cases hbound : observed.toNat < adjacency.size
    · have hget := Array.getElem_setIfInBounds (xs := adjacency) (i := source.toNat)
        (a := target :: adjacency.getD source.toNat []) (j := observed.toNat) hbound
      by_cases heq : source.toNat = observed.toNat
      · have hsource : source = observed := UInt32.ext heq
        subst source
        have hmem : candidate ∈ target :: adjacency.getD observed.toNat [] := by
          simpa [Array.getD, hbound] using hcandidate
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hcandidate
        · exact htarget
        · exact hgraph observed hobserved candidate hcandidate
      · have hmem : candidate ∈ adjacency.getD observed.toNat [] := by
          simpa [Array.getD, hbound, hget, heq] using hcandidate
        exact hgraph observed hobserved candidate hmem
    · simp [Array.getD, hbound] at hcandidate

theorem addSemanticSourceCells_preserves_bounds {count : Nat}
    {adjacency : Array (List UInt32)} (hgraph : AdjacencyWellFormed count adjacency)
    (target : UInt32) (htarget : target.toNat < count) (sources : List UInt32) :
    AdjacencyWellFormed count (addSemanticSourceCells adjacency target sources) := by
  induction sources generalizing adjacency with
  | nil => exact hgraph
  | cons source rest ih =>
      exact ih (addSemanticEdge_preserves_bounds hgraph source target htarget)

theorem addSemanticOperandValueEdges_preserves_bounds {count : Nat}
    {adjacency : Array (List UInt32)} (p : Program) (index : SemanticIndex)
    (owner target : UInt32) (htarget : target.toNat < count)
    (position remaining : Nat) (hgraph : AdjacencyWellFormed count adjacency) :
    AdjacencyWellFormed count
      (addSemanticOperandValueEdges p index owner target position remaining adjacency) := by
  induction remaining generalizing position adjacency with
  | zero => exact hgraph
  | succ remaining ih =>
      simp only [addSemanticOperandValueEdges]
      apply ih
      split <;> try exact hgraph
      split <;> try exact hgraph
      split <;> try exact hgraph
      exact addSemanticEdge_preserves_bounds hgraph _ target htarget

theorem addSemanticControlEdgeAt_preserves_bounds {count : Nat}
    {adjacency : Array (List UInt32)} (p : Program) {index : SemanticIndex}
    (hbounds : IndexCellBounds count index) (instruction : Node)
    (source : UInt32) (position : Nat) (hgraph : AdjacencyWellFormed count adjacency) :
    AdjacencyWellFormed count
      (addSemanticControlEdgeAt p index instruction source position adjacency) := by
  unfold addSemanticControlEdgeAt
  split <;> try exact hgraph
  split <;> try exact hgraph
  split <;> try exact hgraph
  apply addSemanticEdge_preserves_bounds hgraph
  exact hbounds.block _ _ _ (by assumption)

theorem addSemanticControlEdges_preserves_bounds {count : Nat}
    {adjacency : Array (List UInt32)} (p : Program) {index : SemanticIndex}
    (hbounds : IndexCellBounds count index) (instruction : Node)
    (source : UInt32) (position remaining : Nat) (hgraph : AdjacencyWellFormed count adjacency) :
    AdjacencyWellFormed count
      (addSemanticControlEdges p index instruction source position remaining adjacency) := by
  induction remaining generalizing position adjacency with
  | zero => exact hgraph
  | succ remaining ih =>
      simp only [addSemanticControlEdges]
      apply ih
      exact addSemanticControlEdgeAt_preserves_bounds p hbounds instruction source position hgraph

theorem addSemanticCallArgumentEdges_preserves_bounds {count : Nat}
    {adjacency : Array (List UInt32)} (p : Program) (index : SemanticIndex)
    (instruction : Node) (position : Nat) (parameters : List UInt32)
    (hparameters : ∀ cell ∈ parameters, cell.toNat < count)
    (hgraph : AdjacencyWellFormed count adjacency) :
    AdjacencyWellFormed count
      (addSemanticCallArgumentEdges p index instruction position parameters adjacency) := by
  induction parameters generalizing position adjacency with
  | nil => exact hgraph
  | cons parameter rest ih =>
      have hparameter := hparameters parameter (by simp)
      have hrest : ∀ cell ∈ rest, cell.toNat < count := by
        intro cell hcell
        exact hparameters cell (by simp [hcell])
      simp only [addSemanticCallArgumentEdges]
      apply ih _ hrest
      split <;> try exact hgraph
      split <;> try exact hgraph
      exact addSemanticEdge_preserves_bounds hgraph _ parameter hparameter

theorem addSemanticCallEdges_preserves_bounds {count : Nat}
    {adjacency : Array (List UInt32)} (p : Program) {index : SemanticIndex}
    (hbounds : IndexCellBounds count index) (instruction : Node) (caller destination : UInt32)
    (hdestination : destination.toNat < count) (hgraph : AdjacencyWellFormed count adjacency) :
    AdjacencyWellFormed count
      (addSemanticCallEdges p index instruction caller destination adjacency) := by
  unfold addSemanticCallEdges
  split <;> try exact hgraph
  split <;> try exact hgraph
  rename_i callee hcallee hkind
  have hentry : AdjacencyWellFormed count
      (match indexedSemanticFunctionNode? index callee.required with
      | some function => match semanticBlockCell? index callee.required function.actual with
        | some entry => addSemanticEdge adjacency caller entry
        | none => adjacency
      | none => adjacency) := by
    split <;> try exact hgraph
    split <;> try exact hgraph
    apply addSemanticEdge_preserves_bounds hgraph
    exact hbounds.block _ _ _ (by assumption)
  have harguments := addSemanticCallArgumentEdges_preserves_bounds p index instruction 1
    (index.parameterCells.getD callee.required.toNat [])
    (hbounds.parameter callee.required) hentry
  have hreturned := addSemanticSourceCells_preserves_bounds harguments destination hdestination
    (index.returnCells.getD callee.required.toNat [])
  by_cases hzero : destination = 0
  · cases hfunction : indexedSemanticFunctionNode? index callee.required with
    | none => simpa [hzero, hfunction] using harguments
    | some function =>
        cases hblock : semanticBlockCell? index callee.required function.actual <;>
          simpa [hzero, hfunction, hblock] using harguments
  · cases hfunction : indexedSemanticFunctionNode? index callee.required with
    | none => simpa [hzero, hfunction] using hreturned
    | some function =>
        cases hblock : semanticBlockCell? index callee.required function.actual <;>
          simpa [hzero, hfunction, hblock] using hreturned

theorem semanticDynamicEntryCell_bound (p : Program) :
    (semanticDynamicEntryCell p).toNat < semanticTaintCellCount p := by
  have hmod : (semanticDynamicEntryCell p).toNat ≤ p.nodes.size + 1 := Nat.mod_le _ _
  unfold semanticTaintCellCount
  omega

theorem semanticDynamicReturnCell_bound (p : Program) :
    (semanticDynamicReturnCell p).toNat < semanticTaintCellCount p := by
  have hmod : (semanticDynamicReturnCell p).toNat ≤ p.nodes.size + 2 := Nat.mod_le _ _
  unfold semanticTaintCellCount
  omega

theorem semanticDynamicArgumentCell_bound (p : Program) (position : Nat)
    (hposition : position < semanticMaxClosureArgumentCount p) :
    (semanticDynamicArgumentCell p position).toNat < semanticTaintCellCount p := by
  have hmod : (semanticDynamicArgumentCell p position).toNat ≤ p.nodes.size + 3 + position :=
    Nat.mod_le _ _
  unfold semanticTaintCellCount
  omega

theorem addSemanticClosureArgumentInputs_preserves_bounds
    {adjacency : Array (List UInt32)} (p : Program) (index : SemanticIndex)
    (instruction : Node) (position remaining : Nat) (hposition : 0 < position)
    (hrange : position - 1 + remaining ≤ semanticMaxClosureArgumentCount p)
    (hgraph : AdjacencyWellFormed (semanticTaintCellCount p) adjacency) :
    AdjacencyWellFormed (semanticTaintCellCount p)
      (addSemanticClosureArgumentInputs p index instruction position remaining adjacency) := by
  induction remaining generalizing position adjacency with
  | zero => exact hgraph
  | succ remaining ih =>
      simp only [addSemanticClosureArgumentInputs]
      apply ih _ (by omega) (by omega)
      split <;> try exact hgraph
      split <;> try exact hgraph
      exact addSemanticEdge_preserves_bounds hgraph _ _
        (semanticDynamicArgumentCell_bound p (position - 1) (by omega))

theorem addSemanticClosureEdges_preserves_bounds
    {adjacency : Array (List UInt32)} (p : Program) (index : SemanticIndex)
    (instruction : Node) (caller destination : UInt32)
    (harity : instruction.ceiling.toNat - 1 ≤ semanticMaxClosureArgumentCount p)
    (hdestination : destination.toNat < semanticTaintCellCount p)
    (hgraph : AdjacencyWellFormed (semanticTaintCellCount p) adjacency) :
    AdjacencyWellFormed (semanticTaintCellCount p)
      (addSemanticClosureEdges p index instruction caller destination adjacency) := by
  unfold addSemanticClosureEdges
  have hentry := addSemanticEdge_preserves_bounds hgraph caller (semanticDynamicEntryCell p)
    (semanticDynamicEntryCell_bound p)
  have hselector := addSemanticEdge_preserves_bounds hentry
    (match semanticOperandValueIdAt? p instruction.nodeId 0 with
      | some valueId => (semanticValueCell? index instruction.origin valueId).getD caller
      | none => caller)
    (semanticDynamicEntryCell p) (semanticDynamicEntryCell_bound p)
  have harguments := addSemanticClosureArgumentInputs_preserves_bounds p index instruction
    1 (instruction.ceiling.toNat - 1) (by decide) (by simpa using harity) hselector
  have hreturned := addSemanticEdge_preserves_bounds harguments (semanticDynamicReturnCell p)
    destination hdestination
  by_cases hzero : destination = 0
  · cases hvalue : semanticOperandValueIdAt? p instruction.nodeId 0 <;>
      simpa [hzero, hvalue] using harguments
  · cases hvalue : semanticOperandValueIdAt? p instruction.nodeId 0 <;>
      simpa [hzero, hvalue] using hreturned

theorem addSemanticDynamicParameterSummaries_preserves_bounds
    {count : Nat} {adjacency : Array (List UInt32)} (p : Program) (position : Nat)
    (parameters : List UInt32) (hparameters : ∀ cell ∈ parameters, cell.toNat < count)
    (hgraph : AdjacencyWellFormed count adjacency) :
    AdjacencyWellFormed count
      (addSemanticDynamicParameterSummaries p position parameters adjacency) := by
  induction parameters generalizing position adjacency with
  | nil => exact hgraph
  | cons parameter rest ih =>
      have hparameter := hparameters parameter (by simp)
      have hrest : ∀ cell ∈ rest, cell.toNat < count := by
        intro cell hcell
        exact hparameters cell (by simp [hcell])
      exact ih _ hrest (addSemanticEdge_preserves_bounds hgraph _ parameter hparameter)

theorem addSemanticDynamicFunctionSummaries_preserves_bounds
    {adjacency : Array (List UInt32)} (p : Program) {index : SemanticIndex}
    (hbounds : IndexCellBounds (semanticTaintCellCount p) index) (function : Node)
    (hgraph : AdjacencyWellFormed (semanticTaintCellCount p) adjacency) :
    AdjacencyWellFormed (semanticTaintCellCount p)
      (addSemanticDynamicFunctionSummaries p index adjacency function) := by
  unfold addSemanticDynamicFunctionSummaries
  split <;> try exact hgraph
  have hentry : AdjacencyWellFormed (semanticTaintCellCount p)
      (match semanticBlockCell? index function.origin function.actual with
      | some entry => addSemanticEdge adjacency (semanticDynamicEntryCell p) entry
      | none => adjacency) := by
    split <;> try exact hgraph
    rename_i entry hentry
    exact addSemanticEdge_preserves_bounds hgraph _ entry
      (hbounds.block function.origin function.actual entry hentry)
  have hparameters := addSemanticDynamicParameterSummaries_preserves_bounds p 0
    (index.parameterCells.getD function.origin.toNat []) (hbounds.parameter function.origin) hentry
  exact addSemanticSourceCells_preserves_bounds hparameters (semanticDynamicReturnCell p)
    (semanticDynamicReturnCell_bound p) _

theorem semanticInstructionTaintEdges_preserves_bounds
    {adjacency : Array (List UInt32)} (p : Program) {index : SemanticIndex}
    (hbounds : IndexCellBounds (semanticTaintCellCount p) index)
    (restores : Array Bool) (instruction : Node)
    (harity : decodeSemanticInstrOp? instruction.aux = some .closure →
      instruction.ceiling.toNat - 1 ≤ semanticMaxClosureArgumentCount p)
    (hgraph : AdjacencyWellFormed (semanticTaintCellCount p) adjacency) :
    AdjacencyWellFormed (semanticTaintCellCount p)
      (semanticInstructionTaintEdges p index restores adjacency instruction) := by
  have hzero : (0 : UInt32).toNat < semanticTaintCellCount p := by
    simp only [semanticTaintCellCount, UInt32.toNat_zero]
    omega
  have hdestination :
      (if instruction.required == 0 then 0 else
        (semanticValueCell? index instruction.origin instruction.required).getD 0).toNat <
          semanticTaintCellCount p := by
    split
    · exact hzero
    · cases hvalue : semanticValueCell? index instruction.origin instruction.required with
      | none => exact hzero
      | some cell => exact hbounds.value _ _ _ hvalue
  unfold semanticInstructionTaintEdges
  split <;> try exact hgraph
  rename_i op hop
  dsimp only
  generalize hblock : (semanticBlockCell? index instruction.origin instruction.actual).getD 0 = block
  generalize hdest : (if instruction.required == 0 then 0 else
    (semanticValueCell? index instruction.origin instruction.required).getD 0) = destination
  rw [hdest] at hdestination
  generalize hbase : (if destination == 0 then adjacency else
    addSemanticEdge adjacency block destination) = base
  have hbaseBound : AdjacencyWellFormed (semanticTaintCellCount p) base := by
    rw [← hbase]
    split
    · exact hgraph
    · exact addSemanticEdge_preserves_bounds hgraph block destination hdestination
  generalize hvalues : (if destination == 0 || op == .release || op == .releaseCT || op == .stateRead
    then base else if op == .actorBoundary && semanticOperandKindCount p instruction.nodeId 3 != 0
    then base else addSemanticOperandValueEdges p index instruction.nodeId destination
      0 instruction.ceiling.toNat base) = values
  have hvaluesBound : AdjacencyWellFormed (semanticTaintCellCount p) values := by
    rw [← hvalues]
    split
    · exact hbaseBound
    · split
      · exact hbaseBound
      · exact addSemanticOperandValueEdges_preserves_bounds p index instruction.nodeId
          destination hdestination 0 instruction.ceiling.toNat hbaseBound
  split
  · by_cases hmerge : instruction.ceiling = 4 <;> simp [hmerge]
    all_goals
      repeat' apply addSemanticControlEdgeAt_preserves_bounds p hbounds
      exact hvaluesBound
  · split
    · by_cases hflat : instruction.ceiling = 2
      · simp only [hflat, beq_self_eq_true, if_true]
        apply addSemanticControlEdgeAt_preserves_bounds p hbounds
        exact addSemanticControlEdgeAt_preserves_bounds p hbounds _ _ _ hvaluesBound
      · simp only [beq_eq_false_iff_ne.mpr hflat, Bool.false_eq_true, if_false]
        by_cases hmerge : instruction.ceiling = 4 <;> simp [hmerge]
        all_goals
          repeat' apply addSemanticControlEdgeAt_preserves_bounds p hbounds
          exact hvaluesBound
    · split
      · exact addSemanticControlEdgeAt_preserves_bounds p hbounds _ _ _
          (addSemanticControlEdgeAt_preserves_bounds p hbounds _ _ _
            (addSemanticControlEdgeAt_preserves_bounds p hbounds _ _ _ hvaluesBound))
      · split
        · split <;> try exact hvaluesBound
          split <;> try exact hvaluesBound
          split <;> try exact hvaluesBound
          apply addSemanticEdge_preserves_bounds hvaluesBound
          exact hbounds.block _ _ _ (by assumption)
        · split
          · exact addSemanticCallEdges_preserves_bounds p hbounds instruction block destination
              hdestination hvaluesBound
          · split
            · have hclosure : op = .closure := by simpa using
                (show (op == .closure) = true from by assumption)
              exact addSemanticClosureEdges_preserves_bounds p index instruction block destination
                (harity (hop.trans (congrArg some hclosure))) hdestination hvaluesBound
            · exact hvaluesBound

private theorem foldl_max_ge_initial {α : Type} (value : α → Nat) (nodes : List α) (initial : Nat) :
    initial ≤ nodes.foldl (fun current node => max current (value node)) initial := by
  induction nodes generalizing initial with
  | nil => exact Nat.le_refl _
  | cons node rest ih =>
      exact Nat.le_trans (Nat.le_max_left initial (value node)) (ih _)

private theorem member_le_foldl_max {α : Type} (value : α → Nat) (nodes : List α)
    (initial : Nat) (node : α) (hnode : node ∈ nodes) :
    value node ≤ nodes.foldl (fun current item => max current (value item)) initial := by
  induction nodes generalizing initial with
  | nil => simp at hnode
  | cons head rest ih =>
      simp only [List.mem_cons] at hnode
      rcases hnode with rfl | hnode
      · exact Nat.le_trans (Nat.le_max_right initial (value node))
          (foldl_max_ge_initial value rest _)
      · exact ih _ hnode

private def closureArity (instruction : Node) : Nat :=
  if instruction.op == .semInstruction && decodeSemanticInstrOp? instruction.aux == some .closure
  then instruction.ceiling.toNat - 1 else 0

private theorem op_semInstruction_beq_iff (op : Op) :
    (op == .semInstruction) = true ↔ op = .semInstruction := by
  cases op <;> decide

private theorem semanticMaxClosureArgumentCount_eq_fold (p : Program) :
    semanticMaxClosureArgumentCount p =
      p.nodes.toList.foldl (fun current instruction => max current (closureArity instruction)) 0 := by
  unfold semanticMaxClosureArgumentCount
  rw [← Array.foldl_toList]
  congr 1
  funext current instruction
  unfold closureArity
  split <;> simp_all

theorem semanticClosureArity_bound {p : Program} {instruction : Node}
    (hmember : instruction ∈ p.nodes.toList) (hinstruction : instruction.op = .semInstruction)
    (hclosure : decodeSemanticInstrOp? instruction.aux = some .closure) :
    instruction.ceiling.toNat - 1 ≤ semanticMaxClosureArgumentCount p := by
  rw [semanticMaxClosureArgumentCount_eq_fold]
  have hbound := member_le_foldl_max closureArity p.nodes.toList 0 instruction hmember
  simpa [closureArity, hinstruction, hclosure,
    show (Op.semInstruction == Op.semInstruction) = true from by decide] using hbound

theorem foldl_preserves_adjacency_bounds {count : Nat}
    (nodes : List Node) (transform : Array (List UInt32) → Node → Array (List UInt32))
    (htransform : ∀ node ∈ nodes, ∀ adjacency,
      AdjacencyWellFormed count adjacency → AdjacencyWellFormed count (transform adjacency node))
    (adjacency : Array (List UInt32)) (hgraph : AdjacencyWellFormed count adjacency) :
    AdjacencyWellFormed count (nodes.foldl transform adjacency) := by
  induction nodes generalizing adjacency with
  | nil => exact hgraph
  | cons head rest ih =>
      apply ih
      · intro node hnode
        exact htransform node (by simp [hnode])
      · exact htransform head (by simp) adjacency hgraph

/-- Actual semantic graph construction preserves bounded endpoints, including direct calls and
    closure summary cells. The only supplied premises describe source-derived index lookups. -/
theorem semanticTaintAdjacencyWithIndex_well_formed (p : Program) (index : SemanticIndex)
    (hbounds : IndexCellBounds (semanticTaintCellCount p) index) :
    AdjacencyWellFormed (semanticTaintCellCount p) (semanticTaintAdjacencyWithIndex p index) := by
  unfold semanticTaintAdjacencyWithIndex
  simp only [← Array.foldl_toList]
  apply foldl_preserves_adjacency_bounds
  · intro instruction hmember adjacency hgraph
    split
    · rename_i hop
      have hinstruction : instruction.op = .semInstruction :=
        (op_semInstruction_beq_iff _).mp hop
      exact semanticInstructionTaintEdges_preserves_bounds p hbounds _ instruction
        (semanticClosureArity_bound hmember hinstruction) hgraph
    · exact hgraph
  · apply foldl_preserves_adjacency_bounds
    · intro function _ adjacency hgraph
      exact addSemanticDynamicFunctionSummaries_preserves_bounds p hbounds function hgraph
    · intro source hsource target htarget
      simp [Array.getD] at htarget

theorem semanticLabels_is_least_solution_of_index_bounds {p : Program}
    (hbounds : IndexCellBounds (semanticTaintCellCount p) (buildSemanticIndex p)) :
    SemanticSolution p (semanticLabels p) ∧
      ∀ candidate, SemanticSolution p candidate → ArrayFlows (semanticLabels p) candidate :=
  semanticLabels_is_least_solution
    (semanticTaintAdjacencyWithIndex_well_formed p (buildSemanticIndex p) hbounds)

private def reverseChainAdjacency : Array (List UInt32) := #[[], [], [1], [2]]
private def reverseChainSeeds : Array Label := #[.pub, .pub, .pub, .secret]
private def reverseChainWork : List UInt32 := [0, 1, 2, 3]

/-- Mutation witness: one initial pass leaves the reverse chain unsaturated. The edge detector
    observes the missing propagation instead of treating seed preservation as sufficient. -/
theorem shortened_worklist_fuel_does_not_close_edges :
    ¬ EdgesClosed reverseChainAdjacency
      (saturateGraphWorklist reverseChainAdjacency 4 reverseChainWork reverseChainSeeds) := by
  intro hclosed
  have hbad := hclosed 2 (by decide +kernel) 1 (by decide +kernel)
  have hfalse : (labelAt
      (saturateGraphWorklist reverseChainAdjacency 4 reverseChainWork reverseChainSeeds) 2).flowsTo
      (labelAt
      (saturateGraphWorklist reverseChainAdjacency 4 reverseChainWork reverseChainSeeds) 1) = false := by
    decide +kernel
  rw [hfalse] at hbad
  cases hbad

theorem full_worklist_fuel_propagates_reverse_chain :
    saturateGraphWorklist reverseChainAdjacency 16 reverseChainWork reverseChainSeeds =
      #[.pub, .secret, .secret, .secret] := by
  decide +kernel

end LambdaSigil.Combined.SemanticDataflow
