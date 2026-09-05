import Init

/-!
# Combined SIGIL security kernel

This module is deliberately `Init`-only.  It is both imported by the metatheory and compiled to
native code for the production verifier.  Keeping the executable definitions here makes the
proved `verify` function and the linked `verify` function definitionally the same program.

The wire format is a fixed-width, fail-closed security IR.  Version eight carries both the
load-bearing v6 security obligations and a canonical resolved semantic envelope with declarative
contracts and policy metadata. Rust owns the source-to-CSIR projection; this kernel owns validation
of every record that projection emits.
Spans remain on the Rust side and are correlated through `nodeId`.
-/

namespace LambdaSigil.Combined

def wireVersion : UInt32 := 8
def headerBytes : Nat := 12
def nodeBytes : Nat := 32
def maxWireBytes : Nat := 64 * 1024 * 1024
def maxNodes : Nat := 1_000_000

inductive Label where
  | pub | internal | secret | secretCT
  deriving Repr, BEq, DecidableEq

def Label.rank : Label → Nat
  | .pub => 0
  | .internal => 1
  | .secret => 2
  | .secretCT => 3

def Label.flowsTo (source sink : Label) : Bool := source.rank ≤ sink.rank

def Label.lub (left right : Label) : Label :=
  if left.rank ≤ right.rank then right else left

/-- A transparent equality test used by the security kernel.  Keeping it separate from the
    derived `BEq` instance makes the proof of the native decision procedure independent of
    typeclass implementation details. -/
def Label.eqb : Label → Label → Bool
  | .pub, .pub | .internal, .internal | .secret, .secret | .secretCT, .secretCT => true
  | _, _ => false

def Label.neqb (left right : Label) : Bool := !(left.eqb right)

inductive CapKind where
  | ordinary
  | declassify
  | declassifyCT
  deriving Repr, BEq, DecidableEq

inductive Op where
  | flow
  | authority
  | declassify
  | ctUse
  | boundary
  | fixedCT
  | effect
  | consume
  /-- Seed a verifier-owned taint cell (`origin`) with `labelA`. -/
  | taintSeed
  /-- Add a monotone flow constraint from cell `origin` to cell `actual`. -/
  | taintEdge
  /-- Require `lub(value cell origin, pc cell actual)` to flow to `labelB`. -/
  | taintSink
  /-- Require the value/pc cells not to contain `SecretCT`; `aux` is T020--T033. -/
  | taintCtUse
  /-- Validate a downgrade from cell `origin` and seed output cell `actual` with `labelB`. -/
  | taintRelease
  /-- Introduce a legitimate capability at fresh cell `actual`. -/
  | capOrigin
  /-- Move a capability through an authority restriction into fresh cell `actual`. -/
  | capRestrict
  /-- Move a capability through a quantitative split into fresh cell `actual`. -/
  | capSplit
  /-- Derive a non-consuming quantitative draw into fresh cell `actual`. -/
  | capDraw
  /-- Require a derived capability to carry `required` authority under `ceiling`. -/
  | capSink
  /-- Validate a capability-gated release from derived cell `origin`. -/
  | capRelease
  /-- Introduce an empty authority-meet slot at fresh cell `actual`. -/
  | capSlot
  /-- Contribute capability `origin` to slot `actual`'s authority meet. -/
  | capSlotPut
  /-- Derive a capability at fresh cell `actual` from occupied slot `origin`. -/
  | capSlotTake
  /-- Meet two control-flow alternatives (`origin`, `required`) at fresh cell `actual`. -/
  | capMeet
  /-- Begin a syntactic control-flow fork with `aux` alternatives. -/
  | pathFork
  /-- Finish one non-final alternative; flag bit zero says whether it reaches the join. -/
  | pathArm
  /-- Finish the final alternative and join all fallthrough consumption states. -/
  | pathJoin
  /-- Begin a loop and snapshot the capability cells live at its head. -/
  | pathLoop
  /-- Check a repeatable condition/body/continue edge against the loop-head snapshot. -/
  | pathBack
  /-- Record a `break` path which reaches the loop exit. -/
  | pathBreak
  /-- Finish a loop and join its zero-iteration and recorded `break` exits. -/
  | pathLoopJoin
  /-- Introduce a signed i64 amount cell; exact literals carry sign-magnitude payloads. -/
  | intCell
  /-- Add the normalized difference constraint `origin - actual ≤ signed(required, ceiling)`. -/
  | diffLe
  /-- Link a split/draw to its amount and mandatory guest/host guards. -/
  | quantityUse
  /-- Declare the unique v8 semantic section and its constructor counts. -/
  | semProgram
  /-- Declare one resolved function. -/
  | semFunction
  /-- Declare one typed SSA value owned by a resolved function. -/
  | semValue
  /-- Declare one basic block owned by a resolved function. -/
  | semBlock
  /-- Declare one semantic instruction; `aux` selects `SemanticInstrOp`. -/
  | semInstruction
  /-- Declare one operand in the contiguous slice immediately after its instruction. -/
  | semOperand
  /-- Declare a value, parameter, return, or state label contract. -/
  | semLabelContract
  /-- Declare a numeric capability type and its full BV32 authority mask. -/
  | semCapabilityType
  /-- Tie a security-policy class and selected operand window to an instruction. -/
  | semPolicyClass
  /-- Tie a normalized refinement fact to a semantic SSA value. -/
  | semRefinementFact
  /-- Require the guest signed-negative guard and host balance check for split/draw. -/
  | semRuntimeGuard
  deriving Repr, BEq, DecidableEq

/-- The stable semantic instruction classes carried by v8.  These codes intentionally mirror the
    standalone small-step model in `SemanticSecurity.lean`; the native kernel decodes them without
    importing Mathlib. -/
inductive SemanticInstrOp where
  | scalar | aggregate | project
  | branch | jump | loop
  | call | closure
  | actorBoundary | stateRead | stateWrite
  | slotNew | slotPut | slotTake
  | effect | ffi | allocation | address
  | capMint | capRestrict | capSplit | capDraw | capExercise
  | release | releaseCT
  | ctEq | ctSelect | ctLt
  | output | trap | halt
  | range | dispatch | index | divRem | stringCompare
  | abortiveEffect
  deriving Repr, BEq, DecidableEq

def decodeSemanticInstrOp? : UInt32 → Option SemanticInstrOp
  | 0 => some .scalar
  | 1 => some .aggregate
  | 2 => some .project
  | 3 => some .branch
  | 4 => some .jump
  | 5 => some .loop
  | 6 => some .call
  | 7 => some .closure
  | 8 => some .actorBoundary
  | 9 => some .stateRead
  | 10 => some .stateWrite
  | 11 => some .slotNew
  | 12 => some .slotPut
  | 13 => some .slotTake
  | 14 => some .effect
  | 15 => some .ffi
  | 16 => some .allocation
  | 17 => some .address
  | 18 => some .capMint
  | 19 => some .capRestrict
  | 20 => some .capSplit
  | 21 => some .capDraw
  | 22 => some .capExercise
  | 23 => some .release
  | 24 => some .releaseCT
  | 25 => some .ctEq
  | 26 => some .ctSelect
  | 27 => some .ctLt
  | 28 => some .output
  | 29 => some .trap
  | 30 => some .halt
  | 31 => some .range
  | 32 => some .dispatch
  | 33 => some .index
  | 34 => some .divRem
  | 35 => some .stringCompare
  | 36 => some .abortiveEffect
  | _ => none

def Op.isIntCell : Op → Bool
  | .intCell => true
  | _ => false

structure Node where
  op : Op
  labelA : Label
  labelB : Label
  flags : UInt8
  origin : UInt32
  actual : UInt32
  required : UInt32
  ceiling : UInt32
  aux : UInt32
  nodeId : UInt32
  deriving Repr, BEq, DecidableEq

structure Program where
  nodes : Array Node
  deriving Repr, BEq, DecidableEq

inductive ViolationKind where
  | malformed
  | flow
  | legitimacy
  | authority
  | affine
  | declassification
  | ctPolicy
  | effect
  | taintGraph
  | capabilityGraph
  deriving Repr, BEq, DecidableEq

structure Violation where
  kind : ViolationKind
  nodeId : UInt32
  detail : UInt32 := 0
  deriving Repr, BEq, DecidableEq

def hasFlag (flags mask : UInt8) : Bool := (flags &&& mask) == mask

def maskSubset (actual ceiling : UInt32) : Bool := (actual &&& ceiling) == actual
def maskContains (actual required : UInt32) : Bool := (actual &&& required) == required

def capKindOf (n : Node) : Option CapKind :=
  match n.aux with
  | 0 => some .ordinary
  | 1 => some .declassify
  | 2 => some .declassifyCT
  | _ => none

/-- All security facts local to a single CSIR node.  Cross-node affinity is checked separately. -/
def nodeSafe (n : Node) : Bool :=
  match n.op with
  | .flow => n.labelA.flowsTo n.labelB
  | .authority =>
      hasFlag n.flags 0x01 && maskSubset n.actual n.ceiling &&
        maskContains n.actual n.required
  | .declassify =>
      let common := hasFlag n.flags 0x01 && maskSubset n.actual n.ceiling
      match capKindOf n with
      | some .declassify =>
          common && n.labelA.neqb .secretCT && n.labelB.eqb .pub
      | some .declassifyCT =>
          common && n.labelA.eqb .secretCT && n.labelB.eqb .secret
      | _ => false
  | .ctUse => n.labelA.neqb .secretCT
  | .boundary => n.labelA.neqb .secretCT && n.labelA.flowsTo n.labelB
  | .fixedCT => true
  | .effect => hasFlag n.flags 0x01
  | .consume => hasFlag n.flags 0x01
  | .taintSeed | .taintEdge | .taintSink | .taintCtUse | .taintRelease
  | .capOrigin | .capRestrict | .capSplit | .capDraw | .capSink | .capRelease
  | .capSlot | .capSlotPut | .capSlotTake | .capMeet => true
  | .pathFork =>
      n.flags == 1 && n.origin == 0 && n.actual == 0 && n.required == 0 && n.aux.toNat ≥ 2
  | .pathArm | .pathJoin =>
      (n.flags == 0 || n.flags == 1) && n.origin == 0 && n.actual == 0 &&
        n.required == 0 && n.aux == 0
  | .pathLoop | .pathBack | .pathBreak | .pathLoopJoin =>
      n.flags == 1 && n.origin == 0 && n.actual == 0 && n.required == 0 && n.aux == 0
  | .intCell | .diffLe | .quantityUse => true
  | .semProgram | .semFunction | .semValue | .semBlock | .semInstruction
  | .semOperand | .semLabelContract | .semCapabilityType | .semPolicyClass
  | .semRefinementFact | .semRuntimeGuard => true

def consumesOrigin (n : Node) : Bool :=
  match n.op with
  | .declassify | .consume => true
  | .authority => hasFlag n.flags 0x02
  | _ => false

def localViolation (n : Node) : Option Violation :=
  if nodeSafe n then none else
  match n.op with
  | .flow | .boundary => some ⟨ViolationKind.flow, n.nodeId, 0⟩
  | .authority =>
      if !hasFlag n.flags 0x01 then some ⟨.legitimacy, n.nodeId, 0⟩
      else some ⟨ViolationKind.authority, n.nodeId, 0⟩
  | .declassify => some ⟨.declassification, n.nodeId, 0⟩
  | .ctUse => some ⟨.ctPolicy, n.nodeId, n.aux⟩
  | .effect => some ⟨ViolationKind.effect, n.nodeId, 0⟩
  | .consume => some ⟨.legitimacy, n.nodeId, 0⟩
  | .fixedCT => none
  | .taintSeed | .taintEdge | .taintSink | .taintCtUse | .taintRelease
  | .capOrigin | .capRestrict | .capSplit | .capDraw | .capSink | .capRelease
  | .capSlot | .capSlotPut | .capSlotTake | .capMeet => none
  | .pathFork | .pathArm | .pathJoin | .pathLoop | .pathBack | .pathBreak
  | .pathLoopJoin => some ⟨.affine, n.nodeId, n.aux⟩
  | .intCell | .diffLe | .quantityUse => none
  | .semProgram | .semFunction | .semValue | .semBlock | .semInstruction
  | .semOperand | .semLabelContract | .semCapabilityType | .semPolicyClass
  | .semRefinementFact | .semRuntimeGuard => none

/-! ## Verifier-owned finite-lattice taint graph

Cell zero is the distinguished Public cell.  Every other cell identifier must be in
`1 .. p.nodes.size`; this keeps allocation bounded by the already checked node ceiling.  Seeds and
release outputs establish lower bounds.  Edges are saturated for enough whole-program passes to
propagate all three possible strict lattice increases through a worst-case reverse-ordered graph,
including cyclic loop back-edges.
-/

def graphRefValid (p : Program) (cell : UInt32) : Bool := cell.toNat ≤ p.nodes.size

def graphTargetValid (p : Program) (cell : UInt32) : Bool :=
  cell != 0 && graphRefValid p cell

def labelAt (labels : Array Label) (cell : UInt32) : Label :=
  labels.getD cell.toNat .pub

def raiseCell (labels : Array Label) (cell : UInt32) (incoming : Label) : Array Label :=
  let index := cell.toNat
  labels.setIfInBounds index ((labelAt labels cell).lub incoming)

def seedGraphNode (labels : Array Label) (n : Node) : Array Label :=
  match n.op with
  | .taintSeed => raiseCell labels n.origin n.labelA
  | .taintRelease => raiseCell labels n.actual n.labelB
  | _ => labels

def graphSeedLabels (p : Program) : Array Label :=
  p.nodes.foldl seedGraphNode (Array.replicate (p.nodes.size + 1) .pub)

def addGraphEdge (adjacency : Array (List UInt32)) (n : Node) : Array (List UInt32) :=
  match n.op with
  | .taintEdge =>
      let outgoing := adjacency.getD n.origin.toNat []
      adjacency.setIfInBounds n.origin.toNat (n.actual :: outgoing)
  | _ => adjacency

def graphAdjacency (p : Program) : Array (List UInt32) :=
  p.nodes.foldl addGraphEdge (Array.replicate (p.nodes.size + 1) [])

def relaxTargets (source : Label) : List UInt32 → Array Label → List UInt32 →
    Array Label × List UInt32
  | [], labels, work => (labels, work)
  | target :: rest, labels, work =>
      let old := labelAt labels target
      let raised := old.lub source
      if raised.eqb old then relaxTargets source rest labels work
      else relaxTargets source rest (labels.setIfInBounds target.toNat raised) (target :: work)

def saturateGraphWorklist (adjacency : Array (List UInt32)) :
    Nat → List UInt32 → Array Label → Array Label
  | 0, _, labels => labels
  | _ + 1, [], labels => labels
  | fuel + 1, cell :: work, labels =>
      let source := labelAt labels cell
      let targets := adjacency.getD cell.toNat []
      let (labels, work) := relaxTargets source targets labels work
      saturateGraphWorklist adjacency fuel work labels

def graphLabels (p : Program) : Array Label :=
  let cellCount := p.nodes.size + 1
  let initialWork := (List.range cellCount).map UInt32.ofNat
  /- Every cell is processed once initially and can then be re-enqueued only when its label makes
     one of the three possible strict increases.  The post-fixpoint edge check below remains the
     fail-closed backstop for this operational bound. -/
  saturateGraphWorklist (graphAdjacency p) (4 * cellCount) initialWork (graphSeedLabels p)

/-- Executable post-fixpoint backstop for the bounded worklist.  It checks both the aggregate seed
    lower bound and every normalized adjacency edge, so reducing the worklist fuel cannot silently
    readmit a leak. -/
def labelsBelowCellsBool (cellCount : Nat) (lower upper : Array Label) : Bool :=
  lower.size == cellCount && upper.size == cellCount &&
    (List.range cellCount).all fun cell =>
      (labelAt lower (UInt32.ofNat cell)).flowsTo
        (labelAt upper (UInt32.ofNat cell))

def adjacencyCellSafeWith (adjacency : Array (List UInt32)) (p : Program)
    (labels : Array Label) (source : Nat) : Bool :=
  let sourceCell := UInt32.ofNat source
  adjacency.getD source [] |>.all fun target =>
    target.toNat < p.nodes.size + 1 &&
      (labelAt labels sourceCell).flowsTo (labelAt labels target)

def adjacencyCellSafe (p : Program) (labels : Array Label) (source : Nat) : Bool :=
  adjacencyCellSafeWith (graphAdjacency p) p labels source

def graphComputedSolutionSafe (p : Program) (labels : Array Label) : Bool :=
  let cellCount := p.nodes.size + 1
  let adjacency := graphAdjacency p
  p.nodes.size ≤ maxNodes &&
    labelsBelowCellsBool cellCount (graphSeedLabels p) labels &&
    (List.range cellCount).all (adjacencyCellSafeWith adjacency p labels)

def graphNodeWellFormed (p : Program) (n : Node) : Bool :=
  match n.op with
  | .taintSeed => graphTargetValid p n.origin
  | .taintEdge => graphRefValid p n.origin && graphTargetValid p n.actual
  | .taintSink | .taintCtUse => graphRefValid p n.origin && graphRefValid p n.actual
  | .taintRelease =>
      graphRefValid p n.origin && graphTargetValid p n.actual &&
        ((n.aux == 1 && n.labelB.eqb .pub) || (n.aux == 2 && n.labelB.eqb .secret))
  | _ => true

def graphNodeSafe (labels : Array Label) (n : Node) : Bool :=
  let observed := (labelAt labels n.origin).lub (labelAt labels n.actual)
  match n.op with
  | .taintSeed => n.labelA.flowsTo (labelAt labels n.origin)
  | .taintEdge => (labelAt labels n.origin).flowsTo (labelAt labels n.actual)
  | .taintSink =>
      if n.labelB.eqb .secretCT then observed.eqb .pub || observed.eqb .secretCT
      else observed.flowsTo n.labelB
  | .taintCtUse => observed.neqb .secretCT
  | .taintRelease =>
      let outputSeeded := n.labelB.flowsTo (labelAt labels n.actual)
      if n.aux == 1 then outputSeeded && (labelAt labels n.origin).neqb .secretCT
      else if n.aux == 2 then outputSeeded && (labelAt labels n.origin).eqb .secretCT
      else false
  | _ => true

def graphViolation (p : Program) (labels : Array Label) (n : Node) : Option Violation :=
  if !graphNodeWellFormed p n then some ⟨.malformed, n.nodeId, n.aux⟩
  else if graphNodeSafe labels n then none
  else match n.op with
    | .taintSink => some ⟨.flow, n.nodeId, n.aux⟩
    | .taintCtUse => some ⟨.ctPolicy, n.nodeId, n.aux⟩
    | .taintRelease => some ⟨.declassification, n.nodeId, n.aux⟩
    | _ => some ⟨.taintGraph, n.nodeId, n.aux⟩

def firstGraphViolationList (p : Program) (labels : Array Label) : List Node → Option Violation
  | [] => none
  | n :: rest =>
      match graphViolation p labels n with
      | some v => some v
      | none => firstGraphViolationList p labels rest

def firstGraphViolation (p : Program) : Option Violation :=
  let labels := graphLabels p
  match firstGraphViolationList p labels p.nodes.toList with
  | some violation => some violation
  | none =>
      if graphComputedSolutionSafe p labels then none
      else some ⟨.taintGraph, 0, 1⟩

/-! ## Verifier-owned capability derivation

Capability cells are canonical SSA-style derivations: every newly produced capability or slot is
stored at the producing node's own identifier.  Origins are limited to the four projection classes
validated below (parameter/capture, actor state, mint, and verified call result).  Restriction,
split, draw, control-flow meet, slot put/take, sinks, and release gates are interpreted here from
the derived state; Rust does not provide a legitimacy bit or an already-computed authority mask.

Slot cells accumulate the bitwise meet of every preceding put.  This is the conservative authority
rule used at control-flow joins.  Quantitative split/fuel arithmetic remains a separate obligation;
branch- and loop-sensitive consumption is checked below.
-/

structure CapState where
  initialized : Bool := false
  isSlot : Bool := false
  occupied : Bool := false
  kind : CapKind := .ordinary
  mask : UInt32 := 0
  deriving Repr, BEq, DecidableEq

def emptyCapStates (p : Program) : Array CapState :=
  Array.replicate (p.nodes.size + 1) {}

def capStateAt (states : Array CapState) (cell : UInt32) : CapState :=
  states.getD cell.toNat {}

def capKindMatches (state : CapState) (n : Node) : Bool :=
  match capKindOf n with
  | some kind => state.kind == kind
  | none => false

def capSourceReady (states : Array CapState) (cell : UInt32) : Bool :=
  let state := capStateAt states cell
  state.initialized && !state.isSlot

def capSlotReady (states : Array CapState) (cell : UInt32) : Bool :=
  let state := capStateAt states cell
  state.initialized && state.isSlot

def capFreshTarget (p : Program) (n : Node) : Bool :=
  graphTargetValid p n.actual && n.actual == n.nodeId

def capPriorRef (n : Node) (cell : UInt32) : Bool :=
  cell != 0 && cell.toNat < n.nodeId.toNat

def capOriginClassValid (flags : UInt8) : Bool :=
  flags == 1 || flags == 2 || flags == 3 || flags == 4

def capNodeWellFormed (p : Program) (n : Node) : Bool :=
  let kindOK := (capKindOf n).isSome
  match n.op with
  | .capOrigin => capFreshTarget p n && kindOK && capOriginClassValid n.flags
  | .capRestrict | .capSplit | .capDraw =>
      capFreshTarget p n && capPriorRef n n.origin && kindOK &&
        maskSubset n.required n.ceiling
  | .capSink | .capRelease => capPriorRef n n.origin && kindOK
  | .capSlot => capFreshTarget p n && kindOK && (n.flags == 0 || n.flags == 1)
  | .capSlotPut => capPriorRef n n.origin && capPriorRef n n.actual && kindOK
  | .capSlotTake => capFreshTarget p n && capPriorRef n n.origin && kindOK
  | .capMeet =>
      capFreshTarget p n && capPriorRef n n.origin && capPriorRef n n.required && kindOK
  | _ => true

def capNodeSafe (states : Array CapState) (n : Node) : Bool :=
  let source := capStateAt states n.origin
  match n.op with
  | .capOrigin | .capSlot => true
  | .capRestrict | .capSplit | .capDraw =>
      capSourceReady states n.origin && capKindMatches source n &&
        maskSubset source.mask n.ceiling
  | .capSink =>
      capSourceReady states n.origin && capKindMatches source n &&
        maskSubset source.mask n.ceiling && maskContains source.mask n.required
  | .capRelease =>
      capSourceReady states n.origin && capKindMatches source n &&
        maskSubset source.mask n.ceiling && maskContains source.mask n.required &&
        (n.aux == 1 || n.aux == 2)
  | .capSlotPut =>
      let slot := capStateAt states n.actual
      capSourceReady states n.origin && capSlotReady states n.actual &&
        capKindMatches source n && capKindMatches slot n &&
        maskSubset source.mask n.ceiling
  | .capSlotTake =>
      /- Slot emptiness is a guarded runtime condition: an empty take traps and
         has no continuation. Check the possible successful continuation at the
         slot's conservative authority mask without requiring static occupancy. -/
      capSlotReady states n.origin && capKindMatches source n &&
        maskSubset source.mask n.ceiling
  | .capMeet =>
      let right := capStateAt states n.required
      capSourceReady states n.origin && capSourceReady states n.required &&
        capKindMatches source n && capKindMatches right n &&
        maskSubset source.mask n.ceiling && maskSubset right.mask n.ceiling
  | _ => true

def capDerivedState (kind : CapKind) (mask : UInt32) : CapState :=
  { initialized := true, kind, mask }

def applyCapabilityNode (states : Array CapState) (n : Node) : Array CapState :=
  let kind := (capKindOf n).getD .ordinary
  let source := capStateAt states n.origin
  match n.op with
  | .capOrigin =>
      states.setIfInBounds n.actual.toNat (capDerivedState kind n.ceiling)
  | .capRestrict =>
      states.setIfInBounds n.actual.toNat (capDerivedState kind (source.mask &&& n.required))
  | .capSplit | .capDraw =>
      states.setIfInBounds n.actual.toNat (capDerivedState kind source.mask)
  | .capSlot =>
      states.setIfInBounds n.actual.toNat
        { initialized := true, isSlot := true, occupied := hasFlag n.flags 1, kind,
          mask := n.ceiling }
  | .capSlotPut =>
      let oldSlot := capStateAt states n.actual
      let newMask := if oldSlot.occupied then oldSlot.mask &&& source.mask else source.mask
      states.setIfInBounds n.actual.toNat
        { initialized := true, isSlot := true, occupied := true, kind, mask := newMask }
  | .capSlotTake =>
      states.setIfInBounds n.actual.toNat (capDerivedState kind source.mask)
  | .capMeet =>
      let right := capStateAt states n.required
      states.setIfInBounds n.actual.toNat (capDerivedState kind (source.mask &&& right.mask))
  | _ => states

def capabilityViolation (p : Program) (states : Array CapState) (n : Node) : Option Violation :=
  if !capNodeWellFormed p n then some ⟨.malformed, n.nodeId, n.aux⟩
  else if capNodeSafe states n then none
  else match n.op with
    | .capOrigin | .capRestrict | .capSplit | .capDraw | .capSlot | .capSlotPut
    | .capSlotTake | .capMeet => some ⟨.legitimacy, n.nodeId, n.aux⟩
    | .capSink => some ⟨.authority, n.nodeId, n.aux⟩
    | .capRelease => some ⟨.declassification, n.nodeId, n.aux⟩
    | _ => some ⟨.capabilityGraph, n.nodeId, n.aux⟩

def firstCapabilityViolationList (p : Program) :
    Array CapState → List Node → Option Violation
  | _, [] => none
  | states, n :: rest =>
      match capabilityViolation p states n with
      | some v => some v
      | none => firstCapabilityViolationList p (applyCapabilityNode states n) rest

def firstCapabilityViolation (p : Program) : Option Violation :=
  firstCapabilityViolationList p (emptyCapStates p) p.nodes.toList

/-! ## Guarded quantitative split/draw obligations

Integer payloads use a sign bit (`flags & 0x02`) and an unsigned 64-bit magnitude split across
`required`/`ceiling`.  Difference nodes denote `origin - actual ≤ constant`.  Cell zero is the
distinguished arithmetic zero.  The executable consistency classifier is Bellman--Ford with an
implicit super-source: all distances begin at zero and a relaxation after `cellCount` passes is a
negative-cycle witness.  Exact amount literals and every integer cell's i64 range are inserted as
derived edges, so `i64::MIN` and strict-bound normalization do not overflow the wire format.
-/

structure DiffEdge where
  source : UInt32
  target : UInt32
  weight : Int
  deriving Repr, BEq, DecidableEq

def signedMagnitude (n : Node) : Int :=
  let magnitude64 := (n.ceiling.toUInt64 <<< 32) ||| n.required.toUInt64
  let magnitude := Int.ofNat magnitude64.toNat
  if hasFlag n.flags 0x02 then -magnitude else magnitude

def nodeAt? (p : Program) (cell : UInt32) : Option Node :=
  if cell == 0 then none else p.nodes[cell.toNat - 1]?

def priorIntCell (p : Program) (position cell : UInt32) : Bool :=
  cell != 0 && cell < position &&
    match nodeAt? p cell with
    | some n => n.op.isIntCell && n.actual == cell
    | none => false

def intCellWellFormed (n : Node) : Bool :=
  let exact := hasFlag n.flags 0x04
  let negative := hasFlag n.flags 0x02
  let magnitudeZero := n.required == 0 && n.ceiling == 0
  n.origin == 0 && n.actual == n.nodeId && n.aux == 0 &&
    (n.flags == 1 || n.flags == 5 || n.flags == 7) &&
    (!negative || exact) && (!negative || !magnitudeZero)

def diffNodeWellFormed (p : Program) (n : Node) : Bool :=
  (n.flags == 1 || n.flags == 3) && n.aux == 0 &&
    (n.origin == 0 || priorIntCell p n.nodeId n.origin) &&
    (n.actual == 0 || priorIntCell p n.nodeId n.actual) &&
    -- Version 6 imports only literal-RHS refinements. Their normalized difference forms are
    -- anchored at arithmetic zero. Rejecting cell-to-cell constraints keeps the accepted wire
    -- language exactly aligned with the Rust projection instead of claiming unsupported QF_LIA.
    (n.origin == 0 || n.actual == 0)

def quantityNodeWellFormed (p : Program) (n : Node) : Bool :=
  if n.flags != 0x03 || n.ceiling != 0 || (n.aux != 1 && n.aux != 2) then false else
  if !priorIntCell p n.nodeId n.required then false else
  match nodeAt? p n.actual with
  | none => false
  | some operation =>
      n.actual + 1 == n.nodeId && operation.actual == n.actual &&
        operation.origin == n.origin &&
        ((n.aux == 1 && operation.op == .capSplit) ||
         (n.aux == 2 && operation.op == .capDraw))

def quantityCoverageNode (p : Program) (n : Node) : Bool :=
  if n.op != .capSplit && n.op != .capDraw then true else
  match nodeAt? p (n.nodeId + 1) with
  | some link => link.op == .quantityUse && link.actual == n.nodeId
  | none => false

def quantitativeNodeWellFormed (p : Program) (n : Node) : Bool :=
  match n.op with
  | .intCell => intCellWellFormed n
  | .diffLe => diffNodeWellFormed p n
  | .quantityUse => quantityNodeWellFormed p n
  | _ => quantityCoverageNode p n

def i64Max : Int := Int.ofNat 9223372036854775807
def i64Min : Int := -Int.ofNat 9223372036854775808

def quantitativeEdgesForNode (n : Node) : List DiffEdge :=
  match n.op with
  | .intCell =>
      let bounds :=
        [⟨0, n.actual, i64Max⟩, ⟨n.actual, 0, -i64Min⟩]
      if hasFlag n.flags 0x04 then
        let value := signedMagnitude n
        ⟨0, n.actual, value⟩ :: ⟨n.actual, 0, -value⟩ :: bounds
      else bounds
  | .diffLe => [⟨n.actual, n.origin, signedMagnitude n⟩]
  | _ => []

def quantitativeEdges (p : Program) : List DiffEdge :=
  p.nodes.toList.flatMap quantitativeEdgesForNode

def diffDistance (distances : Array Int) (cell : UInt32) : Int :=
  distances.getD cell.toNat 0

def relaxDiffEdge (base : Array Int) (distances : Array Int × Bool)
    (edge : DiffEdge) : Array Int × Bool :=
  let candidate := diffDistance base edge.source + edge.weight
  let current := diffDistance distances.1 edge.target
  if candidate < current then
    (distances.1.setIfInBounds edge.target.toNat candidate, true)
  else distances

def relaxDiffPass (edges : List DiffEdge) (distances : Array Int) : Array Int × Bool :=
  -- Every candidate is read from the same preceding vector. This is the textbook synchronous
  -- Bellman--Ford recurrence: pass `k + 1` accounts for every walk with at most `k + 1` edges.
  -- The accumulator still takes the minimum of duplicate incoming edges for each target.
  edges.foldl (relaxDiffEdge distances) (distances, false)

def relaxDiffPasses (edges : List DiffEdge) : Nat → Array Int → Array Int
  | 0, distances => distances
  | fuel + 1, distances => relaxDiffPasses edges fuel (relaxDiffPass edges distances).1

def intCellCount (p : Program) : Nat :=
  p.nodes.toList.countP fun n => n.op == .intCell

def bellmanFordDiffDistances (p : Program) : Array Int :=
  let edges := quantitativeEdges p
  let initial := Array.replicate (p.nodes.size + 1) (0 : Int)
  relaxDiffPasses edges (intCellCount p + 1) initial

/-- Greatest imported lower bound for one zero-anchored integer cell. An edge `cell → 0` with
    weight `w` means `-w ≤ cell`; every integer cell also carries the implicit i64 lower bound. -/
def diffLowerBoundFor (edges : List DiffEdge) (cell : UInt32) : Int :=
  edges.foldl (fun lower edge =>
    if edge.source = cell ∧ edge.target = 0 then max lower (-edge.weight) else lower) i64Min

/-- Canonical potential for the accepted literal-RHS fragment: arithmetic zero is normalized to
    zero and each other cell is assigned its greatest lower bound. -/
def intervalDiffDistances (p : Program) : Array Int :=
  let edges := quantitativeEdges p
  Array.ofFn fun cell : Fin (p.nodes.size + 1) =>
    if cell.val = 0 then 0 else diffLowerBoundFor edges cell.val.toUInt32

def diffEdgeSatisfied (distances : Array Int) (edge : DiffEdge) : Bool :=
  diffDistance distances edge.target ≤ diffDistance distances edge.source + edge.weight

/-- Bellman--Ford is the fast path. The interval potential is a complete fallback for the
    fail-closed zero-anchored v6 grammar, so a verifier bug or an unfortunate edge order cannot
    cause a false rejection of a satisfiable emitted constraint set. -/
def settledDiffDistances (p : Program) : Array Int :=
  let edges := quantitativeEdges p
  let bellmanFord := bellmanFordDiffDistances p
  if edges.all (diffEdgeSatisfied bellmanFord) then bellmanFord else intervalDiffDistances p

def differenceConsistent (p : Program) : Bool :=
  let edges := quantitativeEdges p
  if edges.isEmpty then true else
  edges.all (diffEdgeSatisfied (settledDiffDistances p))

def firstQuantitativeMalformed : Program → List Node → Option Violation
  | _, [] => none
  | p, n :: rest =>
      if quantitativeNodeWellFormed p n then firstQuantitativeMalformed p rest
      else some ⟨.malformed, n.nodeId, n.aux⟩

def firstQuantitativeViolation (p : Program) : Option Violation :=
  match firstQuantitativeMalformed p p.nodes.toList with
  | some violation => some violation
  | none =>
      if differenceConsistent p then none
      else some ⟨.capabilityGraph, 0, 1⟩

def firstLocalViolationList : List Node → Option Violation
  | [] => none
  | n :: rest =>
      match localViolation n with
      | some v => some v
      | none => firstLocalViolationList rest

def firstAffineViolationList (seen : List UInt32) : List Node → Option Violation
  | [] => none
  | n :: rest =>
      if consumesOrigin n then
        if seen.contains n.origin then some ⟨.affine, n.nodeId, n.origin⟩
        else firstAffineViolationList (n.origin :: seen) rest
      else firstAffineViolationList seen rest

def firstLocalViolation (nodes : Array Node) : Option Violation :=
  firstLocalViolationList nodes.toList

def firstAffineViolation (nodes : Array Node) : Option Violation :=
  firstAffineViolationList [] nodes.toList

/-! ## Path-sensitive capability consumption

The legacy affine scan above remains the compatibility judgment for the original obligation
records.  The state machine below is the load-bearing affine judgment for verifier-derived
capability cells.  A fork snapshots the incoming consumption set.  Each arm is checked from that
same snapshot, and the join unions only arms which can fall through.  Consequently, consuming one
capability in both alternatives is legal, while consuming it twice along either alternative or
using it after a may-consume join is rejected.

`capMeet` nodes immediately following a join are capability φ-nodes.  They are never an escape
hatch: the result is marked consumed when any represented fallthrough arm supplies a consumed
candidate.  The small `phiWidth` table lets an n-way match be encoded as the canonical left fold
already used for authority meet.

A loop snapshots every capability cell produced before its head which is still available.  Every
repeatable condition/body/`continue` edge must preserve that snapshot; otherwise the next
iteration could consume the same origin again.  `break` states are accumulated separately and
joined with the zero-iteration state at loop exit.  This is deliberately conservative about
loop-carried replacement: consuming a head capability and replacing it before the back-edge is
rejected, matching the existing CFG ownership gate rather than assuming a recursive linear φ.
-/

structure PathFrame where
  base : List UInt32
  arms : List (List UInt32) := []
  remaining : Nat
  loopDepth : Nat
  deriving Repr, BEq, DecidableEq

structure PathLoopFrame where
  base : List UInt32
  carried : List UInt32
  exits : List (List UInt32) := []
  pathDepth : Nat
  deriving Repr, BEq, DecidableEq

structure PathAffineState where
  consumed : List UInt32 := []
  known : List UInt32 := []
  frames : List PathFrame := []
  loops : List PathLoopFrame := []
  pendingArms : List (List UInt32) := []
  phiWidth : List (UInt32 × Nat) := []
  deriving Repr, BEq, DecidableEq

def emptyPathAffineState (_p : Program) : PathAffineState := {}

def addConsumed (origin : UInt32) (consumed : List UInt32) : List UInt32 :=
  if consumed.contains origin then consumed else origin :: consumed

def unionConsumed (left right : List UInt32) : List UInt32 :=
  right.foldl (fun acc origin => addConsumed origin acc) left

def unionConsumedMany (sets : List (List UInt32)) : List UInt32 :=
  sets.foldl unionConsumed []

def affineConsumesCapability (n : Node) : Bool :=
  match n.op with
  | .capRestrict | .capSplit | .capSink | .capRelease | .capSlotPut => true
  | _ => false

def producesCapability (n : Node) : Bool :=
  match n.op with
  | .capOrigin | .capRestrict | .capSplit | .capDraw | .capSlotTake | .capMeet => true
  | _ => false

def firstConsumedCarried : List UInt32 → List UInt32 → Option UInt32
  | [], _ => none
  | cell :: rest, consumed =>
      if consumed.contains cell then some cell else firstConsumedCarried rest consumed

def clearPendingAffine (state : PathAffineState) : PathAffineState :=
  if state.pendingArms.isEmpty then state else { state with pendingArms := [], phiWidth := [] }

def pathAffineInput (state : PathAffineState) (n : Node) : PathAffineState :=
  if n.op == .capMeet then state else clearPendingAffine state

def pathAffineViolation (state : PathAffineState) (n : Node) : Option Violation :=
  let state := pathAffineInput state n
  match n.op with
  | .pathFork =>
      if n.aux.toNat ≥ 2 then none else some ⟨.affine, n.nodeId, n.aux⟩
  | .pathArm =>
      match state.frames with
      | frame :: _ =>
          if frame.remaining > 1 && frame.loopDepth == state.loops.length then none
          else some ⟨.affine, n.nodeId, n.aux⟩
      | [] => some ⟨.affine, n.nodeId, n.aux⟩
  | .pathJoin =>
      match state.frames with
      | frame :: _ =>
          if frame.remaining == 1 && frame.loopDepth == state.loops.length then none
          else some ⟨.affine, n.nodeId, n.aux⟩
      | [] => some ⟨.affine, n.nodeId, n.aux⟩
  | .pathLoop => none
  | .pathBack =>
      match state.loops with
      | frame :: _ =>
          match firstConsumedCarried frame.carried state.consumed with
          | some cell => some ⟨.affine, n.nodeId, cell⟩
          | none => none
      | [] => some ⟨.affine, n.nodeId, 0⟩
  | .pathBreak =>
      match state.loops with
      | _ :: _ => none
      | [] => some ⟨.affine, n.nodeId, 0⟩
  | .pathLoopJoin =>
      match state.loops with
      | frame :: _ =>
          if frame.pathDepth == state.frames.length then none
          else some ⟨.affine, n.nodeId, state.frames.length.toUInt32⟩
      | [] => some ⟨.affine, n.nodeId, 0⟩
  | _ =>
      if affineConsumesCapability n || consumesOrigin n then
        if n.origin == 0 || state.consumed.contains n.origin then
          some ⟨.affine, n.nodeId, n.origin⟩
        else none
      else none

def appendReachableArm (frame : PathFrame) (state : PathAffineState) (n : Node) : PathFrame :=
  if hasFlag n.flags 1 then { frame with arms := frame.arms ++ [state.consumed] } else frame

def phiCandidateAvailable (state : PathAffineState) (cell : UInt32) (arm : Nat) : Bool :=
  !(state.pendingArms.getD arm []).contains cell

def phiWidthAt : List (UInt32 × Nat) → UInt32 → Nat
  | [], _ => 0
  | (cell, width) :: rest, target =>
      if cell == target then width else phiWidthAt rest target

def applyPathAffineNode (state : PathAffineState) (n : Node) : PathAffineState :=
  let state := pathAffineInput state n
  match n.op with
  | .pathFork =>
      { state with frames :=
          { base := state.consumed, remaining := n.aux.toNat,
            loopDepth := state.loops.length } :: state.frames }
  | .pathArm =>
      match state.frames with
      | frame :: rest =>
          let frame := appendReachableArm frame state n
          { state with
            consumed := frame.base
            frames := ({ frame with remaining := frame.remaining - 1 } :: rest) }
      | [] => state
  | .pathJoin =>
      match state.frames with
      | frame :: rest =>
          let frame := appendReachableArm frame state n
          let merged := if frame.arms.isEmpty then frame.base else unionConsumedMany frame.arms
          { state with
            consumed := merged
            frames := rest
            pendingArms := frame.arms }
      | [] => state
  | .pathLoop =>
      let carried := state.known.filter (fun cell => !(state.consumed.contains cell))
      { state with loops :=
          { base := state.consumed, carried, pathDepth := state.frames.length } :: state.loops }
  | .pathBack => state
  | .pathBreak =>
      match state.loops with
      | frame :: rest =>
          { state with loops := { frame with exits := frame.exits ++ [state.consumed] } :: rest }
      | [] => state
  | .pathLoopJoin =>
      match state.loops with
      | frame :: rest =>
          { state with consumed := unionConsumedMany (frame.base :: frame.exits), loops := rest }
      | [] => state
  | .capMeet =>
      let known := addConsumed n.actual state.known
      if state.pendingArms.isEmpty then
        let unavailable := state.consumed.contains n.origin || state.consumed.contains n.required
        { state with
          consumed := if unavailable then addConsumed n.actual state.consumed else state.consumed,
          known }
      else
        let priorWidth := phiWidthAt state.phiWidth n.origin
        let leftWidth := if priorWidth == 0 then 1 else priorWidth
        let leftAvailable :=
          if priorWidth == 0 then phiCandidateAvailable state n.origin 0
          else !state.consumed.contains n.origin
        let rightAvailable := phiCandidateAvailable state n.required leftWidth
        let width := leftWidth + 1
        let phiWidth := (n.actual, width) :: state.phiWidth
        let consumed :=
          if leftAvailable && rightAvailable then state.consumed
          else addConsumed n.actual state.consumed
        { state with consumed, phiWidth, known }
  | _ =>
      let state :=
        if affineConsumesCapability n || consumesOrigin n then
          { state with consumed := addConsumed n.origin state.consumed }
        else state
      if producesCapability n then { state with known := addConsumed n.actual state.known }
      else state

def firstPathAffineViolationList : PathAffineState → List Node → Option Violation
  | state, [] =>
      if state.frames.isEmpty && state.loops.isEmpty then none
      else some ⟨.affine, 0, (state.frames.length + state.loops.length).toUInt32⟩
  | state, n :: rest =>
      match pathAffineViolation state n with
      | some v => some v
      | none => firstPathAffineViolationList (applyPathAffineNode state n) rest

def firstPathAffineViolation (p : Program) : Option Violation :=
  firstPathAffineViolationList (emptyPathAffineState p) p.nodes.toList

/-! ## Version-seven resolved semantic envelope

The semantic section is a canonical suffix beginning with exactly one `semProgram` record.
Functions own value declarations and basic blocks; instructions own a bounded contiguous slice of
operand records.  Reference kinds are value (0), same-function block (1), function (2), and
immediate (3).  This checker is deliberately structural during the dual-gate release: the v6
obligation families above remain load-bearing for security policy while semantic-policy derivation
is proved constructor by constructor.
-/

def Op.isSemantic : Op → Bool
  | .semProgram | .semFunction | .semValue | .semBlock | .semInstruction
  | .semOperand | .semLabelContract | .semCapabilityType | .semPolicyClass
  | .semRefinementFact | .semRuntimeGuard => true
  | _ => false

def semanticSuffixLayoutList : Bool → List Node → Bool
  | started, [] => started
  | false, n :: rest =>
      if n.op == .semProgram then semanticSuffixLayoutList true rest
      else if n.op.isSemantic then false
      else semanticSuffixLayoutList false rest
  | true, n :: rest =>
      if n.op == .semProgram || !n.op.isSemantic then false
      else semanticSuffixLayoutList true rest

/-- The canonical encoder writes a nested preorder stream: manifest, then each function, its
    value declarations, and each block followed by its instructions and their operands.  These
    consumers recognize that exact language.  Keeping the recognizer independent of the global
    lookup checks below prevents a well-referenced but reordered stream from acquiring the same
    certificate fingerprint as the canonical projection. -/
def consumeSemanticOperands (owner : UInt32) : Nat → Nat → List Node → Option (List Node)
  | _, 0, nodes => some nodes
  | _, _ + 1, [] => none
  | position, remaining + 1, n :: rest =>
      if n.op == .semOperand && n.origin == owner && n.actual.toNat == position then
        consumeSemanticOperands owner (position + 1) remaining rest
      else none

def SemanticInstrOp.isTerminator : SemanticInstrOp → Bool
  | .branch | .jump | .loop | .range | .dispatch | .output | .halt | .abortiveEffect => true
  | _ => false

/-- `trap_if` is an ordinary instruction when it has a condition.  The projector uses the same
    opcode with no operands for a type-proved unreachable CFG terminator, whose raw behavior is an
    unconditional trap.  Operand arity makes the two existing wire forms unambiguous. -/
def semanticInstructionIsTerminator (n : Node) (op : SemanticInstrOp) : Bool :=
  op.isTerminator || (op == .trap && n.ceiling == 0)

def consumeSemanticInstructions (functionId blockId : UInt32) :
    Nat → List Node → Option (List Node)
  | 0, nodes => some nodes
  | _ + 1, [] => none
  | remaining + 1, n :: rest =>
      match decodeSemanticInstrOp? n.aux with
      | none => none
      | some instruction =>
          if n.op == .semInstruction && n.origin == functionId && n.actual == blockId &&
              semanticInstructionIsTerminator n instruction == (remaining == 0) then
            match consumeSemanticOperands n.nodeId 0 n.ceiling.toNat rest with
            | none => none
            | some afterOperands =>
                consumeSemanticInstructions functionId blockId remaining afterOperands
          else none

def consumeSemanticBlocks (functionId : UInt32) : Nat → Nat → List Node → Option (List Node)
  | _, 0, nodes => some nodes
  | _, _ + 1, [] => none
  | expectedId, remaining + 1, n :: rest =>
      if n.op == .semBlock && n.origin == functionId && n.actual.toNat == expectedId &&
          n.required != 0 then
        match consumeSemanticInstructions functionId n.actual n.required.toNat rest with
        | none => none
        | some afterInstructions =>
            consumeSemanticBlocks functionId (expectedId + 1) remaining afterInstructions
      else none

def consumeSemanticValues (functionId : UInt32) : Nat → Nat → List Node → Option (List Node)
  | _, 0, nodes => some nodes
  | _, _ + 1, [] => none
  | expectedId, remaining + 1, n :: rest =>
      if n.op == .semValue && n.origin == functionId && n.actual.toNat == expectedId then
        consumeSemanticValues functionId (expectedId + 1) remaining rest
      else none

def consumeSemanticFunctions : Nat → Nat → List Node → Option (List Node)
  | _, 0, nodes => some nodes
  | _, _ + 1, [] => none
  | expectedId, remaining + 1, n :: rest =>
      if n.op == .semFunction && n.origin.toNat == expectedId then
        match consumeSemanticValues n.origin 1 n.ceiling.toNat rest with
        | none => none
        | some afterValues =>
            match consumeSemanticBlocks n.origin 1 n.required.toNat afterValues with
            | none => none
            | some afterBlocks => consumeSemanticFunctions (expectedId + 1) remaining afterBlocks
      else none

def semanticMetadataRank? : Op → Option Nat
  | .semLabelContract => some 0
  | .semCapabilityType => some 1
  | .semPolicyClass => some 2
  | .semRefinementFact => some 3
  | .semRuntimeGuard => some 4
  | _ => none

def semanticMetadataFieldsLE (left right : Node) : Bool :=
  left.origin.toNat < right.origin.toNat ||
  (left.origin == right.origin &&
    (left.actual.toNat < right.actual.toNat ||
    (left.actual == right.actual &&
      (left.ceiling.toNat < right.ceiling.toNat ||
      (left.ceiling == right.ceiling &&
        (left.required.toNat < right.required.toNat ||
        (left.required == right.required &&
          (left.aux.toNat < right.aux.toNat ||
          (left.aux == right.aux && left.flags ≤ right.flags)))))))))

def semanticMetadataLE (left right : Node) : Bool :=
  match semanticMetadataRank? left.op, semanticMetadataRank? right.op with
  | some leftRank, some rightRank =>
      leftRank < rightRank || (leftRank == rightRank && semanticMetadataFieldsLE left right)
  | _, _ => false

def semanticMetadataCanonicalFrom : Option Node → List Node → Bool
  | _, [] => true
  | none, node :: rest =>
      (semanticMetadataRank? node.op).isSome && semanticMetadataCanonicalFrom (some node) rest
  | some previous, node :: rest =>
      semanticMetadataLE previous node && semanticMetadataCanonicalFrom (some node) rest

def semanticSuffixList : List Node → List Node
  | [] => []
  | n :: rest => if n.op.isSemantic then n :: rest else semanticSuffixList rest

def semanticCanonicalLayoutList (nodes : List Node) : Bool :=
  match semanticSuffixList nodes with
  | [] => false
  | manifest :: rest =>
      if manifest.op != .semProgram then false
      else match consumeSemanticFunctions 1 manifest.origin.toNat rest with
        | some metadata => semanticMetadataCanonicalFrom none metadata
        | none => false

def semanticCount (p : Program) (op : Op) : Nat :=
  p.nodes.foldl (fun count n => if n.op == op then count + 1 else count) 0

def semanticProgramNode? (p : Program) : Option Node :=
  p.nodes.find? (fun n => n.op == .semProgram)

def semanticOperandAt? (p : Program) (owner : UInt32) (position : Nat) : Option Node :=
  match p.nodes[owner.toNat + position]? with
  | some n =>
      if n.op == .semOperand && n.origin == owner && n.actual.toNat == position then some n
      else none
  | none => none

/-- One-pass indexes for semantic cross references.  The canonical stream check establishes
    uniqueness and owner ordering before these maps are consulted; the maps make per-record
    validation linear rather than repeatedly scanning the complete CSIR array. -/
structure SemanticIndex where
  functions : Array Node
  valueStarts : Array Nat
  values : Array Node
  blockStarts : Array Nat
  blocks : Array Node
  blockTerminators : Array (Option Node)
  valueContracts : Array Bool
  valueContractNodes : Array (Option Node)
  returnContracts : Array Bool
  returnContractNodes : Array (Option Node)
  parameterCells : Array (List UInt32)
  returnCells : Array (List UInt32)
  policyClasses : Array UInt32
  runtimeGuards : Array Bool
  capabilityTypes : Array (Option Node)
  capabilityTypeCount : Nat
  deriving Repr, BEq, DecidableEq

def emptySemanticIndex (cellCount : Nat) : SemanticIndex :=
  { functions := #[], valueStarts := #[], values := #[], blockStarts := #[], blocks := #[],
    blockTerminators := Array.replicate cellCount none,
    valueContracts := Array.replicate cellCount false,
    valueContractNodes := Array.replicate cellCount none,
    returnContracts := Array.replicate cellCount false,
    returnContractNodes := Array.replicate cellCount none,
    parameterCells := Array.replicate cellCount [],
    returnCells := Array.replicate cellCount [],
    policyClasses := Array.replicate cellCount 0,
    runtimeGuards := Array.replicate cellCount false,
    capabilityTypes := Array.replicate cellCount none,
    capabilityTypeCount := 0 }

def buildSemanticIndex (p : Program) : SemanticIndex :=
  p.nodes.foldl (fun index n =>
    match n.op with
    | .semFunction =>
        { functions := index.functions.push n
          valueStarts := index.valueStarts.push index.values.size
          values := index.values
          blockStarts := index.blockStarts.push index.blocks.size
          blocks := index.blocks
          blockTerminators := index.blockTerminators
          valueContracts := index.valueContracts
          valueContractNodes := index.valueContractNodes
          returnContracts := index.returnContracts
          returnContractNodes := index.returnContractNodes
          parameterCells := index.parameterCells
          returnCells := index.returnCells
          policyClasses := index.policyClasses
          runtimeGuards := index.runtimeGuards
          capabilityTypes := index.capabilityTypes
          capabilityTypeCount := index.capabilityTypeCount }
    | .semValue => { index with values := index.values.push n }
    | .semBlock => { index with blocks := index.blocks.push n }
    | .semInstruction =>
        let functionIndex := n.origin.toNat - 1
        let blockNode := (index.blockStarts[functionIndex]?).bind fun start =>
          (index.functions[functionIndex]?).bind fun function =>
            if n.actual != 0 && n.actual.toNat ≤ function.required.toNat then
              index.blocks[start + n.actual.toNat - 1]?
            else none
        let index := match decodeSemanticInstrOp? n.aux, blockNode with
          | some op, some block =>
              if semanticInstructionIsTerminator n op then
                let blockTerminators := index.blockTerminators.setIfInBounds
                  block.nodeId.toNat (some n)
                { index with blockTerminators := blockTerminators }
              else index
          | _, _ => index
        match decodeSemanticInstrOp? n.aux with
        | some .output =>
            match semanticOperandAt? p n.nodeId 0 with
            | some operand =>
                if operand.flags == 0 then
                  let functionIndex := n.origin.toNat - 1
                  let target := (index.valueStarts[functionIndex]?).bind fun start =>
                    (index.functions[functionIndex]?).bind fun function =>
                      if operand.required != 0 &&
                          operand.required.toNat ≤ function.ceiling.toNat then
                        index.values[start + operand.required.toNat - 1]?
                      else none
                  match target with
                  | some value =>
                    let cells := index.returnCells.getD n.origin.toNat []
                    { index with returnCells :=
                        index.returnCells.setIfInBounds n.origin.toNat (value.nodeId :: cells) }
                  | none => index
                else index
            | none => index
        | _ => index
    | .semLabelContract =>
        if (n.aux == 0 || n.aux == 1) && n.actual != 0 then
          let functionIndex := n.origin.toNat - 1
          let target := (index.valueStarts[functionIndex]?).bind fun start =>
            (index.functions[functionIndex]?).bind fun function =>
              if n.actual.toNat ≤ function.ceiling.toNat then
                (index.values[start + n.actual.toNat - 1]?).map (fun value => value.nodeId.toNat)
              else none
          match target with
          | some cell =>
              let index := { index with valueContracts :=
                index.valueContracts.setIfInBounds cell true }
              let index := { index with valueContractNodes :=
                index.valueContractNodes.setIfInBounds cell (some n) }
              if n.aux == 0 then
                let parameters := index.parameterCells.getD n.origin.toNat []
                let parameterCells := index.parameterCells.setIfInBounds n.origin.toNat
                  (parameters ++ [UInt32.ofNat cell])
                { index with parameterCells := parameterCells }
              else index
          | none => index
        else if n.aux == 2 then
          let index := { index with returnContracts :=
            index.returnContracts.setIfInBounds n.origin.toNat true }
          { index with returnContractNodes :=
              index.returnContractNodes.setIfInBounds n.origin.toNat (some n) }
        else index
    | .semPolicyClass =>
        let bit : UInt32 := 1 <<< n.aux
        let classes := index.policyClasses.getD n.origin.toNat 0
        { index with policyClasses :=
            index.policyClasses.setIfInBounds n.origin.toNat (classes ||| bit) }
    | .semRuntimeGuard =>
        { index with runtimeGuards := index.runtimeGuards.setIfInBounds n.origin.toNat true }
    | .semCapabilityType =>
        let index := { index with capabilityTypes :=
          index.capabilityTypes.setIfInBounds n.actual.toNat (some n) }
        { index with capabilityTypeCount := index.capabilityTypeCount + 1 }
    | _ => index) (emptySemanticIndex (p.nodes.size + 1))

def indexedSemanticFunctionNode? (index : SemanticIndex) (functionId : UInt32) : Option Node :=
  index.functions[functionId.toNat - 1]?

def indexedSemanticBlockNode? (index : SemanticIndex) (functionId blockId : UInt32) : Option Node :=
  let functionIndex := functionId.toNat - 1
  (index.blockStarts[functionIndex]?).bind fun start =>
    (index.functions[functionIndex]?).bind fun function =>
      if blockId != 0 && blockId.toNat ≤ function.required.toNat then
        index.blocks[start + blockId.toNat - 1]?
      else none

def indexedSemanticValueNode? (index : SemanticIndex) (functionId valueId : UInt32) : Option Node :=
  let functionIndex := functionId.toNat - 1
  (index.valueStarts[functionIndex]?).bind fun start =>
    (index.functions[functionIndex]?).bind fun function =>
      if valueId != 0 && valueId.toNat ≤ function.ceiling.toNat then
        index.values[start + valueId.toNat - 1]?
      else none

def semanticOperandKindCountFrom (p : Program) (owner : UInt32) (kind : UInt8) :
    Nat → Nat → Nat → Nat
  | _, 0, count => count
  | position, remaining + 1, count =>
      let count' := match semanticOperandAt? p owner position with
        | some n => if n.flags == kind then count + 1 else count
        | none => count
      semanticOperandKindCountFrom p owner kind (position + 1) remaining count'

def semanticOperandKindCount (p : Program) (owner : UInt32) (kind : UInt8) : Nat :=
  match p.nodes[owner.toNat - 1]? with
  | some instruction => semanticOperandKindCountFrom p owner kind 0 instruction.ceiling.toNat 0
  | none => 0

def semanticOperandKindAt? (p : Program) (owner : UInt32) (position : Nat) : Option UInt8 :=
  (semanticOperandAt? p owner position).map (fun n => n.flags)

def semanticOperandValueIdAt? (p : Program) (owner : UInt32) (position : Nat) : Option UInt32 :=
  match semanticOperandAt? p owner position with
  | some operand => if operand.flags == 0 then some operand.required else none
  | none => none

def semanticDestinationValueKind? (index : SemanticIndex) (n : Node) : Option UInt32 :=
  (indexedSemanticValueNode? index n.origin n.required).map (fun value => value.aux)

def semanticDestinationValueType? (index : SemanticIndex) (n : Node) : Option UInt32 :=
  (indexedSemanticValueNode? index n.origin n.required).map (fun value => value.required)

def semanticOperandValueKindAt? (p : Program) (index : SemanticIndex) (n : Node)
    (position : Nat) : Option UInt32 :=
  (semanticOperandValueIdAt? p n.nodeId position).bind fun valueId =>
    (indexedSemanticValueNode? index n.origin valueId).map (fun value => value.aux)

def semanticOperandValueTypeAt? (p : Program) (index : SemanticIndex) (n : Node)
    (position : Nat) : Option UInt32 :=
  (semanticOperandValueIdAt? p n.nodeId position).bind fun valueId =>
    (indexedSemanticValueNode? index n.origin valueId).map (fun value => value.required)

def semanticCapabilityKind : Option UInt32 → Bool
  | some 2 | some 3 => true
  | _ => false

def semanticOperandKindRun (p : Program) (owner : UInt32) (kind : UInt8) :
    Nat → Nat → Bool
  | _, 0 => true
  | position, remaining + 1 =>
      semanticOperandKindAt? p owner position == some kind &&
        semanticOperandKindRun p owner kind (position + 1) remaining

def semanticInstructionDestinationOK (n : Node) (op : SemanticInstrOp) : Bool :=
  match op with
  | .scalar | .aggregate | .project | .stateRead | .slotNew | .slotTake | .capMint
  | .capRestrict | .capSplit | .capDraw | .release | .releaseCT | .ctEq | .ctSelect | .ctLt =>
      n.required != 0
  | .branch | .jump | .loop | .stateWrite | .slotPut | .effect | .abortiveEffect
  | .capExercise | .output
  | .trap | .halt => n.required == 0
  | .call | .closure | .actorBoundary | .ffi | .allocation | .address | .index
  | .divRem | .stringCompare => true
  | .range | .dispatch => n.required == 0

def semanticInstructionValueKindsOK (p : Program) (index : SemanticIndex) (n : Node)
    (op : SemanticInstrOp) : Bool :=
  let destinationKind := semanticDestinationValueKind? index n
  let destinationType := semanticDestinationValueType? index n
  let operandKind := semanticOperandValueKindAt? p index n
  let operandType := semanticOperandValueTypeAt? p index n
  match op with
  | .scalar => destinationKind == some 0
  | .branch =>
      n.ceiling == 2 || (operandKind 0 == some 0 && operandType 0 == some 1)
  | .loop => operandKind 0 == some 0 && operandType 0 == some 1
  | .capMint => destinationKind == some 2
  | .capRestrict => destinationKind == some 2 && semanticCapabilityKind (operandKind 0)
  | .capSplit | .capDraw =>
      destinationKind == some 2 && semanticCapabilityKind (operandKind 0) &&
        operandKind 1 == some 0 && operandType 1 == some 4
  /- `grant(&cap, ...)` exercises a borrowed capability. AIR represents that borrow as a
     pointer-typed copy value; the retained v6 capability graph carries its provenance. -/
  | .capExercise => operandType 0 == some 7
  | .slotNew => destinationKind == some 4
  | .slotPut => operandKind 0 == some 4 && semanticCapabilityKind (operandKind 1)
  | .slotTake => destinationKind == some 2 && operandKind 0 == some 4
  | .ctEq | .ctLt =>
      destinationKind == some 0 && destinationType == some 1 &&
        operandKind 0 == some 0 && operandKind 1 == some 0
  | .ctSelect =>
      destinationKind == some 0 && operandKind 0 == some 0 && operandType 0 == some 1 &&
        operandKind 1 == some 0 && operandKind 2 == some 0
  | .trap => n.ceiling == 0 || (operandKind 0 == some 0 && operandType 0 == some 1)
  | .divRem | .stringCompare => destinationKind == some 0
  | .range => operandKind 0 == some 0
  | _ => true

def semanticOperandOrderOK (p : Program) (n : Node) (op : SemanticInstrOp) : Bool :=
  let kindAt := semanticOperandKindAt? p n.nodeId
  let values := semanticOperandKindCount p n.nodeId 0
  let immediates := semanticOperandKindCount p n.nodeId 3
  let valueRun := semanticOperandKindRun p n.nodeId 0
  let immediateRun := semanticOperandKindRun p n.nodeId 3
  match op with
  | .scalar | .divRem =>
      (values == 0 && immediates ≥ 1 && immediateRun 0 immediates) ||
      (values == 2 && immediates == 2 && valueRun 0 2 && immediateRun 2 2)
  | .aggregate | .closure | .output | .trap => valueRun 0 values
  | .project => valueRun 0 values
  | .slotTake => kindAt 0 == some 0
  | .branch | .dispatch =>
      (n.ceiling == 2 && kindAt 0 == some 1 && kindAt 1 == some 1) ||
      (n.ceiling == 3 && kindAt 0 == some 0 && kindAt 1 == some 1 && kindAt 2 == some 1) ||
      (n.ceiling == 4 && kindAt 0 == some 0 && kindAt 1 == some 1 && kindAt 2 == some 1 &&
        kindAt 3 == some 1)
  | .jump => kindAt 0 == some 1
  | .loop | .range => kindAt 0 == some 0 && kindAt 1 == some 1 && kindAt 2 == some 1
  | .call => kindAt 0 == some 2 && valueRun 1 values
  | .actorBoundary | .stateRead | .stateWrite | .address | .index | .stringCompare =>
      valueRun 0 values && immediateRun values immediates
  | .slotNew | .effect => immediateRun 0 immediates
  | .abortiveEffect => valueRun 0 1
  | .slotPut | .capSplit | .capDraw | .release | .releaseCT | .ctEq | .ctSelect | .ctLt =>
      valueRun 0 values
  | .ffi => immediateRun 0 immediates && valueRun immediates values
  | .allocation =>
      (values == 0 && immediates == 3 && immediateRun 0 3) ||
      (values == 1 && immediates == 1 && valueRun 0 1 && immediateRun 1 1) ||
      (values == 2 && immediates == 0 && valueRun 0 2) ||
      (immediates ≥ 2 && (values == 1 || values == 2) && immediateRun 0 immediates &&
        valueRun immediates values)
  | .capMint => kindAt 0 == some 3 && kindAt 1 == some 3
  | .capRestrict => kindAt 0 == some 0 && kindAt 1 == some 3
  | .capExercise => kindAt 0 == some 0 && kindAt 1 == some 3
  | .halt => true

def semanticInstructionShapeOK (p : Program) (n : Node) (op : SemanticInstrOp) : Bool :=
  let total := n.ceiling.toNat
  let values := semanticOperandKindCount p n.nodeId 0
  let blocks := semanticOperandKindCount p n.nodeId 1
  let functions := semanticOperandKindCount p n.nodeId 2
  let immediates := semanticOperandKindCount p n.nodeId 3
  let allClassified := values + blocks + functions + immediates == total
  allClassified && match op with
  | .scalar | .divRem => blocks == 0 && functions == 0 &&
      ((values == 0 && immediates ≥ 1) || (values == 2 && immediates == 2))
  | .aggregate => blocks == 0 && functions == 0 && total == values
  | .project => values ≥ 1 && total == values
  | .branch | .dispatch =>
      values ≤ 1 && blocks ≥ 2 && blocks ≤ 3 && total == values + blocks
  | .jump => blocks == 1 && total == 1
  | .loop | .range => values == 1 && blocks == 2 && total == 3
  | .call => functions == 1 && blocks == 0 && total == values + 1
  | .closure => values ≥ 1 && blocks == 0 && functions == 0 && total == values
  | .actorBoundary => blocks == 0 && functions == 0 && total == values + immediates &&
      if n.required == 0 then
        /- Send carries four values plus actor/handler ids. Serialize carries at least the
           message, output buffer, and output length and has no immediate operands. -/
        (values == 4 && immediates == 2) || (values ≥ 3 && immediates == 0)
      else
        /- Ask carries five values plus actor/handler ids; spawn carries fuel/capabilities plus
           actor/supervision data; deserialize carries exactly its buffer and length. -/
        (values == 5 && immediates == 2) ||
          (values ≥ 1 && (immediates == 2 || immediates == 3)) ||
          (values == 2 && immediates == 0)
  | .stateRead => values == 1 && total == values + immediates
  | .stateWrite => values == 2 && total == values + immediates
  | .slotNew => values == 0 && blocks == 0 && functions == 0 && immediates ≥ 2 &&
      total == immediates
  | .slotPut => values == 2 && total == 2
  | .slotTake => values == 1 && total == 1
  | .effect => blocks == 0 && functions == 0 && total == immediates
  | .abortiveEffect => values == 1 && blocks == 0 && functions == 0 &&
      immediates == 0 && total == 1
  | .ffi => blocks == 0 && functions == 0 && immediates ≥ 2 &&
      total == values + immediates
  | .allocation => blocks == 0 && functions == 0 && values ≤ 2 &&
      total == values + immediates
  | .address | .index => blocks == 0 && functions == 0 && values ≥ 1 &&
      total == values + immediates
  | .stringCompare => values == 5 && blocks == 0 && functions == 0 && immediates == 0
  | .capMint => values == 1 && immediates ≥ 2 && total == values + immediates
  | .capRestrict => values == 1 && immediates == 1 && total == 2
  | .capSplit | .capDraw => values == 2 && total == 2
  | .capExercise => values == 1 && immediates == 1 && blocks == 0 && functions == 0 && total == 2
  | .release | .releaseCT => values == 2 && total == 2
  | .ctEq | .ctLt => values == 2 && total == 2
  | .ctSelect => values == 3 && total == 3
  | .output => values ≤ 1 && total == values
  | .trap => values ≤ 1 && total == values
  | .halt => total == 0

def semanticProgramRecordOK (p : Program) (n : Node) : Bool :=
  n.labelA.eqb .pub && n.labelB.eqb .pub && n.flags == 1 && n.aux.toNat ==
      semanticCount p .semValue &&
    n.origin.toNat == semanticCount p .semFunction &&
    n.actual.toNat == semanticCount p .semBlock &&
    n.required.toNat == semanticCount p .semInstruction &&
    n.ceiling.toNat == semanticCount p .semOperand

def semanticFunctionRecordOK (index : SemanticIndex) (n : Node) : Bool :=
  n.labelA.eqb .pub && n.labelB.eqb .pub && n.origin != 0 && n.actual != 0 &&
    n.flags ≤ 4 && n.aux ≤ 1 &&
    (indexedSemanticBlockNode? index n.origin n.actual).isSome

def semanticValueRecordOK (index : SemanticIndex) (n : Node) : Bool :=
  n.labelA.eqb .pub && n.labelB.eqb .pub && n.origin != 0 && n.actual != 0 &&
    n.flags == 1 && n.required ≤ 7 && n.aux ≤ 4 &&
    ((n.aux ≤ 1 && n.ceiling == 0) || (n.aux ≥ 2 && n.ceiling != 0)) &&
    (n.aux == 0 || n.required == 7) &&
    (indexedSemanticFunctionNode? index n.origin).isSome

def semanticBlockRecordOK (index : SemanticIndex) (n : Node) : Bool :=
  n.labelA.eqb .pub && n.labelB.eqb .pub && n.origin != 0 && n.actual != 0 &&
    n.flags == 1 && n.ceiling == 0 && n.aux == 0 &&
    (indexedSemanticFunctionNode? index n.origin).isSome

def semanticDirectCallArityOK (p : Program) (index : SemanticIndex) (n : Node) : Bool :=
  match semanticOperandAt? p n.nodeId 0 with
  | some callee =>
      if callee.flags != 2 then false else
        semanticOperandKindCount p n.nodeId 0 ==
          (index.parameterCells.getD callee.required.toNat []).length
  | none => false

def semanticStateLabelCode? : UInt32 → Option Label
  | 0 => some .pub | 1 => some .internal | 2 => some .secret | 3 => some .secretCT
  | _ => none

def semanticStateContractExistsAtList (offset : UInt32) : List Node → Bool
  | [] => false
  | contract :: rest =>
      (contract.op == .semLabelContract && contract.aux == 3 && contract.flags == 1 &&
        contract.actual == offset) || semanticStateContractExistsAtList offset rest

def semanticStateContractExistsAt (p : Program) (offset : UInt32) : Bool :=
  semanticStateContractExistsAtList offset p.nodes.toList

/-- Actor-state visibility is verifier-derived. All declarations for an offset are joined so an
    instruction cannot select a less restrictive runtime label through its embedded compatibility
    code. The code remains on the wire only for Rust/Lean diagnostic parity. -/
def semanticDeclaredStateLabelAtList (offset : UInt32) (contracts : List Node) : Label :=
  contracts.foldl (fun label contract =>
    if contract.op == .semLabelContract && contract.aux == 3 && contract.flags == 1 &&
        contract.actual == offset then label.lub contract.labelA
    else label) .pub

def semanticDeclaredStateLabelAt (p : Program) (offset : UInt32) : Label :=
  semanticDeclaredStateLabelAtList offset p.nodes.toList

def semanticInstructionStateContractOK (p : Program) (n : Node)
    (op : SemanticInstrOp) : Bool :=
  let positions := match op with
    | .stateRead => some (1, 3)
    | .stateWrite => some (2, 4)
    | _ => none
  match positions with
  | none => true
  | some (offsetPosition, labelPosition) =>
      match semanticOperandAt? p n.nodeId offsetPosition,
          semanticOperandAt? p n.nodeId labelPosition with
      | some offset, some encoded =>
          offset.flags == 3 && offset.ceiling == 0 && encoded.flags == 3 &&
            encoded.ceiling == 0 && semanticStateContractExistsAt p offset.required &&
            semanticStateLabelCode? encoded.required ==
              some (semanticDeclaredStateLabelAt p offset.required)
      | _, _ => false

def semanticInstructionRecordOK (p : Program) (index : SemanticIndex) (n : Node) : Bool :=
  match decodeSemanticInstrOp? n.aux, indexedSemanticFunctionNode? index n.origin with
  | some op, some _ =>
      n.labelA.eqb .pub && n.labelB.eqb .pub && n.flags == 1 &&
        n.origin != 0 && n.actual != 0 &&
        (indexedSemanticBlockNode? index n.origin n.actual).isSome &&
        (n.required == 0 || (indexedSemanticValueNode? index n.origin n.required).isSome) &&
        semanticInstructionShapeOK p n op && semanticInstructionDestinationOK n op &&
        (op != .call || semanticDirectCallArityOK p index n) &&
        semanticInstructionStateContractOK p n op &&
        semanticOperandOrderOK p n op && semanticInstructionValueKindsOK p index n op
  | _, _ => false

def semanticOperandRecordOK (p : Program) (index : SemanticIndex) (n : Node) : Bool :=
  match p.nodes[n.origin.toNat - 1]? with
  | some owner =>
      let contiguousIndex := n.origin.toNat + n.actual.toNat
      n.labelA.eqb .pub && n.labelB.eqb .pub && owner.op == .semInstruction &&
        n.origin != 0 && n.actual.toNat < owner.ceiling.toNat &&
        n.nodeId.toNat - 1 == contiguousIndex && n.flags ≤ 3 &&
        match n.flags with
        | 0 => n.required != 0 && (indexedSemanticValueNode? index owner.origin n.required).isSome
        | 1 => n.required != 0 && (indexedSemanticBlockNode? index owner.origin n.required).isSome
        | 2 => n.required != 0 && (indexedSemanticFunctionNode? index n.required).isSome
        | 3 => true
        | _ => false
  | none => false

def semanticCapabilityTypeNode? (index : SemanticIndex) (typeId : UInt32) : Option Node :=
  index.capabilityTypes[typeId.toNat]?.join

def semanticInstructionOwner? (p : Program) (n : Node) : Option Node :=
  match p.nodes[n.origin.toNat - 1]? with
  | some owner => if owner.op == .semInstruction then some owner else none
  | none => none

def semanticLabelContractRecordOK (index : SemanticIndex) (n : Node) : Bool :=
  n.origin != 0 && n.required == n.aux && n.aux ≤ 3 && n.flags ≤ 2 &&
    (indexedSemanticFunctionNode? index n.origin).isSome &&
    (match n.flags with
    | 0 => n.labelA.eqb .pub && n.labelB.eqb .pub && n.ceiling == 0
    | 1 => n.labelA.eqb n.labelB && n.ceiling == 0
    | 2 => n.labelA.eqb .secret && n.labelB.eqb .secret && n.ceiling == 1
    | _ => false) &&
    (match n.aux with
    | 0 | 1 => n.actual != 0 && (indexedSemanticValueNode? index n.origin n.actual).isSome
    | 2 => n.actual == 0
    | 3 => n.flags == 1
    | _ => false)

def semanticCapabilityTypeRecordOK (index : SemanticIndex) (n : Node) : Bool :=
  n.labelA.eqb .pub && n.labelB.eqb .pub && n.flags == 1 && n.origin == 0 &&
    n.actual != 0 && n.actual.toNat ≤ index.capabilityTypeCount &&
    semanticCapabilityTypeNode? index n.actual == some n && n.aux ≤ 2

def semanticPolicyDiagnostic? : UInt32 → Option UInt32
  | 0 => some 20 | 1 => some 21 | 2 => some 22 | 3 => some 23
  | 4 => some 24 | 5 => some 25 | 6 => some 26 | 7 => some 27
  | 8 => some 28 | 9 => some 29 | 10 => some 30 | 11 => some 31
  | 12 => some 32 | 13 => some 33 | 14 => some 0 | 15 => some 27
  | _ => none

def semanticPolicyClassMatches (classCode : UInt32) (op : SemanticInstrOp) : Bool :=
  match classCode with
  | 0 => op == .branch || op == .project || op == .trap
  | 1 => op == .loop
  | 2 => op == .range
  | 3 => op == .dispatch
  | 4 => op == .index
  | 5 => op == .address || op == .index || op == .closure
  | 6 => op == .divRem
  | 7 => op == .ffi
  | 8 => op == .actorBoundary
  | 9 => op == .allocation
  | 10 => op == .scalar || op == .aggregate || op == .project || op == .call ||
      op == .stateRead || op == .output
  | 11 => op == .release
  | 12 => op == .releaseCT
  | 13 => op == .stringCompare
  | 14 => op == .ctEq || op == .ctSelect || op == .ctLt
  | 15 => op == .capSplit || op == .capDraw
  | _ => false

def semanticSelectedPolicyOperandsOK (p : Program) (owner : Node) :
    Nat → Nat → UInt32 → Bool
  | _, 0, _ => true
  | position, remaining + 1, mask =>
      let selected := (mask &&& 1) == 1
      let selectedOK := if selected then
        position < owner.ceiling.toNat && semanticOperandKindAt? p owner.nodeId position == some 0
      else true
      selectedOK && semanticSelectedPolicyOperandsOK p owner (position + 1) remaining (mask >>> 1)

def semanticPolicyClassRecordOK (p : Program) (n : Node) : Bool :=
  match semanticInstructionOwner? p n, semanticPolicyDiagnostic? n.aux with
  | some owner, some diagnostic =>
      match decodeSemanticInstrOp? owner.aux with
      | some instruction =>
          n.labelA.eqb .pub && n.labelB.eqb .pub && n.flags == 1 &&
            n.required == diagnostic && n.ceiling % 32 == 0 &&
            semanticPolicyClassMatches n.aux instruction &&
            -- Classes whose observed label is not an operand selection may carry an empty
            -- mask: the CT-source class on a call or state read is derived from the callee
            -- return contract or the state contract (`semanticCtSourceObservedLabel`), and the
            -- compiler deliberately emits it without a selection.
            ((n.aux == 3 || n.aux == 5 || n.aux == 7 || n.aux == 14) ||
              (n.aux == 10 && (instruction == .call || instruction == .stateRead)) ||
              n.actual != 0) &&
            semanticSelectedPolicyOperandsOK p owner n.ceiling.toNat 32 n.actual
      | none => false
  | _, _ => false

def semanticRefinementFactRecordOK (_p : Program) (index : SemanticIndex) (n : Node) : Bool :=
  n.origin != 0 && n.actual != 0 && n.flags ≥ 1 && n.flags ≤ 2 && n.aux == 0 &&
    (indexedSemanticValueNode? index n.origin n.actual).isSome &&
    n.labelA.eqb .pub && n.labelB.eqb .pub

def semanticRuntimeGuardRecordOK (p : Program) (n : Node) : Bool :=
  match semanticInstructionOwner? p n with
  | some owner =>
      match decodeSemanticInstrOp? owner.aux with
      | some .capSplit | some .capDraw =>
          n.labelA.eqb .pub && n.labelB.eqb .pub && n.flags == 3 && n.actual == 1 &&
            n.required == 0 && n.ceiling == 0 && n.aux == 0 &&
            semanticOperandKindAt? p owner.nodeId 1 == some 0
      | _ => false
  | none => false

def semanticBlockTerminator? (index : SemanticIndex) (functionId blockId : UInt32) : Option Node := do
  let block ← indexedSemanticBlockNode? index functionId blockId
  index.blockTerminators[block.nodeId.toNat]?.join

/-- Linear bounded structured-path validation. The worklist and block-ID bitmap visit every
    reachable block at most once for one continuation query. A repeated block is an internal cycle;
    every finite exit from that cycle must still pass through a declared continuation or an allowed
    terminal. In the Public check, a successful exit is forbidden precisely while its derived block
    pc is non-Public; a successful exit reached after a verified pc-restoring continuation remains
    legal. Ordinary structured control does not consult `labels`. -/
def semanticStructuredPathsOK (p : Program) (index : SemanticIndex)
    (labels : Array Label) (functionId stopA stopB : UInt32) (rejectSuccessfulExit : Bool) :
    Nat → Array Bool → List UInt32 → Bool
  | _, _, [] => true
  | 0, _, _ => false
  | fuel + 1, visited, blockId :: work =>
      if blockId == stopA || blockId == stopB then
        semanticStructuredPathsOK p index labels functionId stopA stopB rejectSuccessfulExit
          fuel visited work
      else if blockId.toNat ≥ visited.size then false
      else if visited.getD blockId.toNat false then
        semanticStructuredPathsOK p index labels functionId stopA stopB rejectSuccessfulExit
          fuel visited work
      else
        match semanticBlockTerminator? index functionId blockId with
        | none => false
        | some terminator =>
            let visited := visited.setIfInBounds blockId.toNat true
            let recurse := semanticStructuredPathsOK p index labels functionId stopA stopB
              rejectSuccessfulExit fuel visited
            match decodeSemanticInstrOp? terminator.aux with
            | some .jump =>
                match semanticOperandAt? p terminator.nodeId 0 with
                | some target => recurse (target.required :: work)
                | none => false
            | some .branch =>
                match semanticOperandAt? p terminator.nodeId 1,
                    semanticOperandAt? p terminator.nodeId 2 with
                | some left, some right => recurse (left.required :: right.required :: work)
                | _, _ => false
            | some .dispatch =>
                let leftPosition := if terminator.ceiling == 2 then 0 else 1
                let rightPosition := if terminator.ceiling == 2 then 1 else 2
                match semanticOperandAt? p terminator.nodeId leftPosition,
                    semanticOperandAt? p terminator.nodeId rightPosition with
                | some left, some right => recurse (left.required :: right.required :: work)
                | _, _ => false
            | some .loop | some .range =>
                match semanticOperandAt? p terminator.nodeId 1,
                    semanticOperandAt? p terminator.nodeId 2 with
                | some body, some exit => recurse (body.required :: exit.required :: work)
                | _, _ => false
            | some .trap | some .abortiveEffect => recurse work
            | some .output | some .halt =>
                if rejectSuccessfulExit then
                  let blockLabel := (indexedSemanticBlockNode? index functionId blockId).map
                    (fun block => labelAt labels block.nodeId) |>.getD .secretCT
                  if blockLabel.eqb .pub then recurse work else false
                else recurse work
            | _ => false

def semanticStructuredControlRecordOK (p : Program) (index : SemanticIndex) (n : Node) : Bool :=
  let fuel := 4 * index.blocks.size + 1
  let visited := Array.replicate (index.blocks.size + 1) false
  match decodeSemanticInstrOp? n.aux with
  | some .branch =>
      match semanticOperandAt? p n.nodeId 1, semanticOperandAt? p n.nodeId 2 with
      | some left, some right =>
          let merge := if n.ceiling == 4 then
            (semanticOperandAt? p n.nodeId 3).map (fun target => target.required) |>.getD 0
          else 0
          semanticStructuredPathsOK p index #[] n.origin merge merge false fuel visited
            [left.required, right.required]
      | _, _ => false
  | some .dispatch =>
      let leftPosition := if n.ceiling == 2 then 0 else 1
      let rightPosition := if n.ceiling == 2 then 1 else 2
      match semanticOperandAt? p n.nodeId leftPosition,
          semanticOperandAt? p n.nodeId rightPosition with
      | some left, some right =>
          let merge := if n.ceiling == 2 then right.required else
            (semanticOperandAt? p n.nodeId 3).map (fun target => target.required) |>.getD 0
          semanticStructuredPathsOK p index #[] n.origin merge merge false fuel visited
            [left.required, right.required]
      | _, _ => false
  | some .loop | some .range =>
      match semanticOperandAt? p n.nodeId 1, semanticOperandAt? p n.nodeId 2 with
      | some body, some exit =>
          semanticStructuredPathsOK p index #[] n.origin n.actual exit.required false fuel visited
            [body.required]
      | _, _ => false
  | _ => true

def semanticRecordOK (p : Program) (index : SemanticIndex) (n : Node) : Bool :=
  match n.op with
  | .semProgram => semanticProgramRecordOK p n
  | .semFunction => semanticFunctionRecordOK index n
  | .semValue => semanticValueRecordOK index n &&
      (n.ceiling == 0 || (semanticCapabilityTypeNode? index n.ceiling).isSome)
  | .semBlock => semanticBlockRecordOK index n
  | .semInstruction => semanticInstructionRecordOK p index n &&
      semanticStructuredControlRecordOK p index n
  | .semOperand => semanticOperandRecordOK p index n
  | .semLabelContract => semanticLabelContractRecordOK index n
  | .semCapabilityType => semanticCapabilityTypeRecordOK index n
  | .semPolicyClass => semanticPolicyClassRecordOK p n
  | .semRefinementFact => semanticRefinementFactRecordOK p index n
  | .semRuntimeGuard => semanticRuntimeGuardRecordOK p n
  | _ => true

def firstSemanticViolationList (p : Program) (index : SemanticIndex) : List Node → Option Violation
  | [] => none
  | n :: rest =>
      if semanticRecordOK p index n then firstSemanticViolationList p index rest
      else some ⟨.malformed, n.nodeId, n.aux⟩

def firstSemanticViolationWithIndex (p : Program) (index : SemanticIndex) : Option Violation :=
  if semanticCount p .semProgram == 0 &&
      p.nodes.toList.all (fun n => !n.op.isSemantic) then none
  else if !semanticSuffixLayoutList false p.nodes.toList then some ⟨.malformed, 0, 7⟩
  else if !semanticCanonicalLayoutList p.nodes.toList then some ⟨.malformed, 0, 7⟩
  else match semanticProgramNode? p with
    | none => some ⟨.malformed, 0, 7⟩
    | some _ => firstSemanticViolationList p index p.nodes.toList

def firstSemanticViolation (p : Program) : Option Violation :=
  firstSemanticViolationWithIndex p (buildSemanticIndex p)

/-! ## Version-eight semantic-policy derivation -/

def semanticPolicyExists (index : SemanticIndex) (owner classCode : UInt32) : Bool :=
  let classes := index.policyClasses.getD owner.toNat 0
  (classes &&& ((1 : UInt32) <<< classCode)) != 0

def semanticGuardExists (index : SemanticIndex) (owner : UInt32) : Bool :=
  index.runtimeGuards.getD owner.toNat false

def semanticValueContractNode? (index : SemanticIndex) (functionId valueId : UInt32) :
    Option Node :=
  (indexedSemanticValueNode? index functionId valueId).bind fun value =>
    index.valueContractNodes[value.nodeId.toNat]?.join

def semanticInstructionNeedsCtSource (p : Program) (index : SemanticIndex) (n : Node)
    (op : SemanticInstrOp) : Bool :=
  let hasValueSource := semanticOperandKindCount p n.nodeId 0 != 0
  match op with
  | .scalar | .aggregate | .project =>
      hasValueSource &&
        match semanticValueContractNode? index n.origin n.required with
        | some contract => contract.flags == 1 && contract.labelA.eqb .secretCT
        | none => false
  | .output =>
      hasValueSource &&
        match index.returnContractNodes[n.origin.toNat]?.join with
        | some contract => contract.flags == 1 && contract.labelA.eqb .secretCT
        | none => false
  | .call | .stateRead =>
      n.required != 0 &&
        match semanticValueContractNode? index n.origin n.required with
        | some contract => contract.flags == 1 && contract.labelA.eqb .secretCT
        | none => false
  | _ => false

def semanticInstructionMetadataComplete (p : Program) (index : SemanticIndex) (n : Node) : Bool :=
  match decodeSemanticInstrOp? n.aux with
  | none => false
  | some op =>
      let classComplete := match op with
        | .branch => semanticPolicyExists index n.nodeId 0
        | .loop => semanticPolicyExists index n.nodeId 1
        | .range => semanticPolicyExists index n.nodeId 2
        | .dispatch => semanticPolicyExists index n.nodeId 3
        | .index => semanticPolicyExists index n.nodeId 4 && semanticPolicyExists index n.nodeId 5
        | .address => semanticPolicyExists index n.nodeId 5
        | .divRem => semanticPolicyExists index n.nodeId 6
        | .ffi => semanticPolicyExists index n.nodeId 7
        | .actorBoundary => semanticPolicyExists index n.nodeId 8
        | .allocation =>
            if semanticOperandKindCount p n.nodeId 0 == 0 then true
            else semanticPolicyExists index n.nodeId 9
        | .closure => semanticPolicyExists index n.nodeId 5
        | .release => semanticPolicyExists index n.nodeId 11
        | .releaseCT => semanticPolicyExists index n.nodeId 12
        | .stringCompare => semanticPolicyExists index n.nodeId 13
        | .ctEq | .ctSelect | .ctLt => semanticPolicyExists index n.nodeId 14
        | .capSplit | .capDraw =>
            semanticPolicyExists index n.nodeId 15 && semanticGuardExists index n.nodeId
        | _ => true
      classComplete &&
        (!semanticInstructionNeedsCtSource p index n op || semanticPolicyExists index n.nodeId 10)

def semanticValueContractExists (index : SemanticIndex) (functionId valueId : UInt32) : Bool :=
  match indexedSemanticValueNode? index functionId valueId with
  | some value => index.valueContracts.getD value.nodeId.toNat false
  | none => false

def semanticReturnContractExists (index : SemanticIndex) (functionId : UInt32) : Bool :=
  index.returnContracts.getD functionId.toNat false

def semanticMetadataCompleteNode (p : Program) (index : SemanticIndex) (n : Node) : Bool :=
  match n.op with
  | .semFunction => semanticReturnContractExists index n.origin
  | .semValue => semanticValueContractExists index n.origin n.actual
  | .semInstruction => semanticInstructionMetadataComplete p index n
  | _ => true

def firstSemanticMetadataViolationList (p : Program) (index : SemanticIndex) :
    List Node → Option Violation
  | [] => none
  | n :: rest =>
      if semanticMetadataCompleteNode p index n then
        firstSemanticMetadataViolationList p index rest
      else some ⟨.malformed, n.nodeId, 8⟩

def firstSemanticMetadataViolation (p : Program) : Option Violation :=
  firstSemanticMetadataViolationList p (buildSemanticIndex p) p.nodes.toList

def semanticValueCell? (index : SemanticIndex) (functionId valueId : UInt32) : Option UInt32 :=
  (indexedSemanticValueNode? index functionId valueId).map (fun node => node.nodeId)

def semanticBlockCell? (index : SemanticIndex) (functionId blockId : UInt32) : Option UInt32 :=
  (indexedSemanticBlockNode? index functionId blockId).map (fun node => node.nodeId)

def addSemanticEdge (adjacency : Array (List UInt32)) (source target : UInt32) :
    Array (List UInt32) :=
  if source == 0 || target == 0 then adjacency else
    let outgoing := adjacency.getD source.toNat []
    adjacency.setIfInBounds source.toNat (target :: outgoing)

def addSemanticOperandValueEdges (p : Program) (index : SemanticIndex) (owner target : UInt32) :
    Nat → Nat → Array (List UInt32) → Array (List UInt32)
  | _, 0, adjacency => adjacency
  | position, remaining + 1, adjacency =>
      let adjacency := match semanticOperandValueIdAt? p owner position with
        | some valueId =>
            match p.nodes[owner.toNat - 1]? with
            | some instruction =>
                match semanticValueCell? index instruction.origin valueId with
                | some source => addSemanticEdge adjacency source target
                | none => adjacency
            | none => adjacency
        | none => adjacency
      addSemanticOperandValueEdges p index owner target (position + 1) remaining adjacency

def addSemanticControlEdges (p : Program) (index : SemanticIndex) (instruction : Node)
    (controlSource : UInt32) : Nat → Nat → Array (List UInt32) → Array (List UInt32)
  | _, 0, adjacency => adjacency
  | position, remaining + 1, adjacency =>
      let adjacency := match semanticOperandAt? p instruction.nodeId position with
        | some operand =>
            if operand.flags == 1 then
              match semanticBlockCell? index instruction.origin operand.required with
              | some target => addSemanticEdge adjacency controlSource target
              | none => adjacency
            else adjacency
        | none => adjacency
      addSemanticControlEdges p index instruction controlSource (position + 1) remaining adjacency

def addSemanticControlEdgeAt (p : Program) (index : SemanticIndex) (instruction : Node)
    (controlSource : UInt32) (position : Nat) (adjacency : Array (List UInt32)) :
    Array (List UInt32) :=
  match semanticOperandAt? p instruction.nodeId position with
  | some operand =>
      if operand.flags == 1 then
        match semanticBlockCell? index instruction.origin operand.required with
        | some target => addSemanticEdge adjacency controlSource target
        | none => adjacency
      else adjacency
  | none => adjacency

/-- Check that every finite successful path from `work` reaches `stop`. Traps and closed cycles
    cannot witness successful escape; an output/halt before `stop` does. This is the load-bearing
    distinction between a real postdominating continuation and a merely syntactic merge target. -/
def semanticSuccessfulPathsReach (p : Program) (index : SemanticIndex)
    (functionId stop : UInt32) : Nat → Array Bool → List UInt32 → Bool
  | _, _, [] => true
  | 0, _, _ => false
  | fuel + 1, visited, blockId :: work =>
      if blockId == stop then
        semanticSuccessfulPathsReach p index functionId stop fuel visited work
      else if blockId.toNat ≥ visited.size then false
      else if visited.getD blockId.toNat false then
        semanticSuccessfulPathsReach p index functionId stop fuel visited work
      else
        match semanticBlockTerminator? index functionId blockId with
        | none => false
        | some terminator =>
            let visited := visited.setIfInBounds blockId.toNat true
            let recurse := semanticSuccessfulPathsReach p index functionId stop fuel visited
            match decodeSemanticInstrOp? terminator.aux with
            | some .jump =>
                match semanticOperandAt? p terminator.nodeId 0 with
                | some target => recurse (target.required :: work)
                | none => false
            | some .branch =>
                match semanticOperandAt? p terminator.nodeId 1,
                    semanticOperandAt? p terminator.nodeId 2 with
                | some left, some right => recurse (left.required :: right.required :: work)
                | _, _ => false
            | some .dispatch =>
                let leftPosition := if terminator.ceiling == 2 then 0 else 1
                let rightPosition := if terminator.ceiling == 2 then 1 else 2
                match semanticOperandAt? p terminator.nodeId leftPosition,
                    semanticOperandAt? p terminator.nodeId rightPosition with
                | some left, some right => recurse (left.required :: right.required :: work)
                | _, _ => false
            | some .loop | some .range =>
                match semanticOperandAt? p terminator.nodeId 1,
                    semanticOperandAt? p terminator.nodeId 2 with
                | some body, some exit => recurse (body.required :: exit.required :: work)
                | _, _ => false
            | some .trap | some .abortiveEffect => recurse work
            | some .output | some .halt => false
            | _ => false

def semanticSuccessfulPathsReachB (p : Program) (index : SemanticIndex)
    (functionId stop : UInt32) (starts : List UInt32) : Bool :=
  semanticSuccessfulPathsReach p index functionId stop (4 * index.blocks.size + 1)
    (Array.replicate (index.blocks.size + 1) false) starts

/-- Structured merge/exit blocks restore the pc of the enclosing control instruction only when
    the decoded CFG proves they postdominate every successful arm/body path. Incoming arm, break,
    and body jumps then need not carry the inner pc into that continuation. -/
def semanticPcRestoreCells (p : Program) (index : SemanticIndex) : Array Bool :=
  p.nodes.foldl (fun restored instruction =>
    if instruction.op != .semInstruction then restored else
      match decodeSemanticInstrOp? instruction.aux with
      | some .branch =>
          if instruction.ceiling.toNat == 4 then
            match semanticOperandAt? p instruction.nodeId 3 with
            | some operand =>
                match semanticOperandAt? p instruction.nodeId 1,
                    semanticOperandAt? p instruction.nodeId 2,
                    semanticBlockCell? index instruction.origin operand.required with
                | some left, some right, some cell =>
                    if semanticSuccessfulPathsReachB p index instruction.origin operand.required
                        [left.required, right.required] then
                      restored.setIfInBounds cell.toNat true
                    else restored
                | _, _, _ => restored
            | none => restored
          else restored
      | some .dispatch =>
          /- A two-operand dispatch is the flat match wrapper, and its exit is the real
             post-dominator. A four-operand dispatch is one test in the arm chain: operand three
             is only the next test/catch-all target, so restoring there would erase the selector
             pc before the match region actually exits. -/
          if instruction.ceiling.toNat == 2 then
            match semanticOperandAt? p instruction.nodeId 1 with
            | some operand =>
                match semanticOperandAt? p instruction.nodeId 0,
                    semanticBlockCell? index instruction.origin operand.required with
                | some start, some cell =>
                    if semanticSuccessfulPathsReachB p index instruction.origin operand.required
                        [start.required] then
                      restored.setIfInBounds cell.toNat true
                    else restored
                | _, _ => restored
            | none => restored
          else restored
      | some .loop | some .range =>
          match semanticOperandAt? p instruction.nodeId 2 with
          | some operand =>
              match semanticOperandAt? p instruction.nodeId 1,
                  semanticBlockCell? index instruction.origin operand.required with
              | some body, some cell =>
                  if semanticSuccessfulPathsReachB p index instruction.origin operand.required
                      [body.required] then
                    restored.setIfInBounds cell.toNat true
                  else restored
              | _, _ => restored
          | none => restored
      | _ => restored) (Array.replicate (p.nodes.size + 1) false)

def addSemanticSourceCells (adjacency : Array (List UInt32)) (target : UInt32) :
    List UInt32 → Array (List UInt32)
  | [] => adjacency
  | source :: rest => addSemanticSourceCells (addSemanticEdge adjacency source target) target rest

def addSemanticCallArgumentEdges (p : Program) (index : SemanticIndex) (instruction : Node) :
    Nat → List UInt32 → Array (List UInt32) → Array (List UInt32)
  | _, [], adjacency => adjacency
  | position, parameter :: rest, adjacency =>
      let adjacency := match semanticOperandValueIdAt? p instruction.nodeId position with
        | some valueId =>
            match semanticValueCell? index instruction.origin valueId with
            | some source => addSemanticEdge adjacency source parameter
            | none => adjacency
        | none => adjacency
      addSemanticCallArgumentEdges p index instruction (position + 1) rest adjacency

def addSemanticCallEdges (p : Program) (index : SemanticIndex) (instruction : Node)
    (callerBlock destination : UInt32) (adjacency : Array (List UInt32)) :
    Array (List UInt32) :=
  match semanticOperandAt? p instruction.nodeId 0 with
  | some callee =>
      if callee.flags != 2 then adjacency else
        let functionId := callee.required
        let adjacency := match indexedSemanticFunctionNode? index functionId with
          | some function =>
              match semanticBlockCell? index functionId function.actual with
              | some entry => addSemanticEdge adjacency callerBlock entry
              | none => adjacency
          | none => adjacency
        let parameters := index.parameterCells.getD functionId.toNat []
        let adjacency := addSemanticCallArgumentEdges p index instruction 1 parameters adjacency
        if destination == 0 then adjacency
        else addSemanticSourceCells adjacency destination
          (index.returnCells.getD functionId.toNat [])
  | none => adjacency

def semanticMaxClosureArgumentCount (p : Program) : Nat :=
  p.nodes.foldl (fun maximum instruction =>
    if instruction.op == .semInstruction &&
        decodeSemanticInstrOp? instruction.aux == some .closure then
      max maximum (instruction.ceiling.toNat - 1)
    else maximum) 0

/-- Real CSIR cells occupy `0 .. p.nodes.size`.  Dynamic closures use a compact family of
    verifier-owned summary cells: one for all possible entries, one for all possible returns, and
    one per argument position.  This represents exactly the same conservative complete-bipartite
    edge relation as expanding every closure against every function, without quadratic storage or
    construction time. -/
def semanticTaintCellCount (p : Program) : Nat :=
  p.nodes.size + 3 + semanticMaxClosureArgumentCount p

def semanticDynamicEntryCell (p : Program) : UInt32 :=
  UInt32.ofNat (p.nodes.size + 1)

def semanticDynamicReturnCell (p : Program) : UInt32 :=
  UInt32.ofNat (p.nodes.size + 2)

def semanticDynamicArgumentCell (p : Program) (position : Nat) : UInt32 :=
  UInt32.ofNat (p.nodes.size + 3 + position)

def addSemanticClosureArgumentInputs (p : Program) (index : SemanticIndex)
    (instruction : Node) : Nat → Nat → Array (List UInt32) → Array (List UInt32)
  | _, 0, adjacency => adjacency
  | position, remaining + 1, adjacency =>
      let adjacency := match semanticOperandValueIdAt? p instruction.nodeId position with
        | some valueId =>
            match semanticValueCell? index instruction.origin valueId with
            | some source =>
                addSemanticEdge adjacency source (semanticDynamicArgumentCell p (position - 1))
            | none => adjacency
        | none => adjacency
      addSemanticClosureArgumentInputs p index instruction (position + 1) remaining adjacency

/-- A closure target is selected by a runtime table index, so no single callee ID is present in the
    operand slice. The summary edges conservatively connect the caller pc and selector to every
    decoded function entry, each actual argument to the same-position parameter of every possible
    target, and every possible return cell to each closure destination. -/
def addSemanticClosureEdges (p : Program) (index : SemanticIndex) (instruction : Node)
    (callerBlock destination : UInt32) (adjacency : Array (List UInt32)) :
    Array (List UInt32) :=
  let selector := match semanticOperandValueIdAt? p instruction.nodeId 0 with
    | some valueId => (semanticValueCell? index instruction.origin valueId).getD callerBlock
    | none => callerBlock
  let entrySummary := semanticDynamicEntryCell p
  let adjacency := addSemanticEdge (addSemanticEdge adjacency callerBlock entrySummary)
    selector entrySummary
  let adjacency := addSemanticClosureArgumentInputs p index instruction 1
    (instruction.ceiling.toNat - 1) adjacency
  if destination == 0 then adjacency
  else addSemanticEdge adjacency (semanticDynamicReturnCell p) destination

def addSemanticDynamicParameterSummaries (p : Program) :
    Nat → List UInt32 → Array (List UInt32) → Array (List UInt32)
  | _, [], adjacency => adjacency
  | position, parameter :: rest, adjacency =>
      let adjacency := addSemanticEdge adjacency (semanticDynamicArgumentCell p position) parameter
      addSemanticDynamicParameterSummaries p (position + 1) rest adjacency

def addSemanticDynamicFunctionSummaries (p : Program) (index : SemanticIndex)
    (adjacency : Array (List UInt32)) (function : Node) : Array (List UInt32) :=
  if function.op != .semFunction then adjacency else
    let functionId := function.origin
    let adjacency := match semanticBlockCell? index functionId function.actual with
      | some entry => addSemanticEdge adjacency (semanticDynamicEntryCell p) entry
      | none => adjacency
    let adjacency := addSemanticDynamicParameterSummaries p 0
      (index.parameterCells.getD functionId.toNat []) adjacency
    addSemanticSourceCells adjacency (semanticDynamicReturnCell p)
      (index.returnCells.getD functionId.toNat [])

def semanticInstructionTaintEdges (p : Program) (index : SemanticIndex)
    (restoreCells : Array Bool) (adjacency : Array (List UInt32)) (n : Node) :
    Array (List UInt32) :=
  match decodeSemanticInstrOp? n.aux with
  | none => adjacency
  | some op =>
      let blockCell := (semanticBlockCell? index n.origin n.actual).getD 0
      let destination := if n.required == 0 then 0 else
        (semanticValueCell? index n.origin n.required).getD 0
      let adjacency := if destination == 0 then adjacency else addSemanticEdge adjacency blockCell destination
      let adjacency :=
        if destination == 0 || op == .release || op == .releaseCT || op == .stateRead then adjacency
        /- Actor operations share one event class but have two distinct result dependencies.
           Spawn returns an actor identity and ask returns an externally supplied response, so
           neither is data-derived from the outgoing request operands. Deserialize has no
           immediate operands and its decoded result is data-derived from buffer and length.
           The exact actor instruction shapes above make this discriminator fail closed. -/
        else if op == .actorBoundary && semanticOperandKindCount p n.nodeId 3 != 0 then adjacency
        else addSemanticOperandValueEdges p index n.nodeId destination 0 n.ceiling.toNat adjacency
      if op == .branch then
        let condition := match semanticOperandValueIdAt? p n.nodeId 0 with
          | some valueId => (semanticValueCell? index n.origin valueId).getD blockCell
          | none => blockCell
        let adjacency := addSemanticControlEdgeAt p index n blockCell 1 adjacency
        let adjacency := addSemanticControlEdgeAt p index n blockCell 2 adjacency
        let adjacency := addSemanticControlEdgeAt p index n condition 1 adjacency
        let adjacency := addSemanticControlEdgeAt p index n condition 2 adjacency
        if n.ceiling == 4 then addSemanticControlEdgeAt p index n blockCell 3 adjacency
        else adjacency
      else if op == .dispatch then
        if n.ceiling == 2 then
          let adjacency := addSemanticControlEdgeAt p index n blockCell 0 adjacency
          addSemanticControlEdgeAt p index n blockCell 1 adjacency
        else
          let condition := match semanticOperandValueIdAt? p n.nodeId 0 with
            | some valueId => (semanticValueCell? index n.origin valueId).getD blockCell
            | none => blockCell
          let adjacency := addSemanticControlEdgeAt p index n blockCell 1 adjacency
          let adjacency := addSemanticControlEdgeAt p index n blockCell 2 adjacency
          let adjacency := addSemanticControlEdgeAt p index n condition 1 adjacency
          let adjacency := addSemanticControlEdgeAt p index n condition 2 adjacency
          if n.ceiling == 4 then addSemanticControlEdgeAt p index n blockCell 3 adjacency
          else adjacency
      else if op == .loop || op == .range then
        let condition := match semanticOperandValueIdAt? p n.nodeId 0 with
          | some valueId => (semanticValueCell? index n.origin valueId).getD blockCell
          | none => blockCell
        let adjacency := addSemanticControlEdgeAt p index n blockCell 1 adjacency
        let adjacency := addSemanticControlEdgeAt p index n condition 1 adjacency
        addSemanticControlEdgeAt p index n blockCell 2 adjacency
      else if op == .jump then
        match semanticOperandAt? p n.nodeId 0 with
        | some operand =>
            match semanticBlockCell? index n.origin operand.required with
            | some targetCell =>
                if restoreCells.getD targetCell.toNat false || operand.required ≤ n.actual then
                  adjacency
                else addSemanticEdge adjacency blockCell targetCell
            | none => adjacency
        | none => adjacency
      else if op == .call then
        addSemanticCallEdges p index n blockCell destination adjacency
      else if op == .closure then
        addSemanticClosureEdges p index n blockCell destination adjacency
      else adjacency

def semanticTaintAdjacencyWithIndex (p : Program) (index : SemanticIndex) : Array (List UInt32) :=
  let restoreCells := semanticPcRestoreCells p index
  let summaries := p.nodes.foldl (addSemanticDynamicFunctionSummaries p index)
    (Array.replicate (semanticTaintCellCount p) [])
  p.nodes.foldl (fun adjacency node =>
    if node.op == .semInstruction then
      semanticInstructionTaintEdges p index restoreCells adjacency node
    else adjacency) summaries

def semanticTaintAdjacency (p : Program) : Array (List UInt32) :=
  semanticTaintAdjacencyWithIndex p (buildSemanticIndex p)

def labelOfCode? : UInt32 → Option Label
  | 0 => some .pub | 1 => some .internal | 2 => some .secret | 3 => some .secretCT
  | _ => none

def semanticImmediateAt? (p : Program) (owner : UInt32) (position : Nat) : Option UInt32 :=
  match semanticOperandAt? p owner position with
  | some operand => if operand.flags == 3 && operand.ceiling == 0 then some operand.required else none
  | none => none

def seedSemanticNode (p : Program) (index : SemanticIndex) (labels : Array Label) (n : Node) :
    Array Label :=
  match n.op with
  | .semLabelContract =>
      if (n.aux == 0 || n.aux == 1) && n.actual != 0 then
        match semanticValueCell? index n.origin n.actual with
        | some cell =>
            if n.flags == 1 then raiseCell labels cell n.labelA
            else if n.flags == 2 then raiseCell labels cell .secret
            else labels
        | none => labels
      else labels
  | .semInstruction =>
      match decodeSemanticInstrOp? n.aux with
      | some .stateRead =>
          match semanticImmediateAt? p n.nodeId 1,
              semanticValueCell? index n.origin n.required with
          | some offset, some cell =>
              raiseCell labels cell (semanticDeclaredStateLabelAt p offset)
          | _, _ => labels
      | some .release =>
          match semanticValueCell? index n.origin n.required with
          | some cell => raiseCell labels cell .pub
          | none => labels
      | some .releaseCT =>
          match semanticValueCell? index n.origin n.required with
          | some cell => raiseCell labels cell .secret
          | none => labels
      | _ => labels
  | _ => labels

def semanticSeedLabelsWithIndex (p : Program) (index : SemanticIndex) : Array Label :=
  p.nodes.foldl (seedSemanticNode p index) (Array.replicate (semanticTaintCellCount p) .pub)

def semanticSeedLabels (p : Program) : Array Label :=
  semanticSeedLabelsWithIndex p (buildSemanticIndex p)

def semanticLabelsWithIndex (p : Program) (index : SemanticIndex) : Array Label :=
  let cellCount := semanticTaintCellCount p
  let work := (List.range cellCount).map UInt32.ofNat
  saturateGraphWorklist (semanticTaintAdjacencyWithIndex p index) (4 * cellCount) work
    (semanticSeedLabelsWithIndex p index)

def semanticLabels (p : Program) : Array Label :=
  semanticLabelsWithIndex p (buildSemanticIndex p)

def semanticSelectedLabel (p : Program) (index : SemanticIndex) (labels : Array Label)
    (owner : Node) : Nat → Nat → UInt32 → Label → Label
  | _, 0, _, accumulated => accumulated
  | position, remaining + 1, mask, accumulated =>
      let accumulated := if (mask &&& 1) == 1 then
        match semanticOperandValueIdAt? p owner.nodeId position with
        | some valueId =>
            match semanticValueCell? index owner.origin valueId with
            | some cell => accumulated.lub (labelAt labels cell)
            | none => accumulated
        | none => accumulated
      else accumulated
      semanticSelectedLabel p index labels owner (position + 1) remaining (mask >>> 1) accumulated

def semanticCtSourceObservedLabel (p : Program) (index : SemanticIndex) (_labels : Array Label)
    (owner : Node) (fallback pc : Label) : Label :=
  match decodeSemanticInstrOp? owner.aux with
  | some .stateRead =>
      match semanticImmediateAt? p owner.nodeId 1 with
      | some offset => (semanticDeclaredStateLabelAt p offset).lub pc
      | none => fallback
  | some .call =>
      match semanticOperandAt? p owner.nodeId 0 with
      | some callee =>
          if callee.flags != 2 then fallback else
            match index.returnContractNodes[callee.required.toNat]?.join with
            | some contract => contract.labelA.lub pc
            | none => fallback
      | none => fallback
  | _ => fallback

def semanticPolicyViolation (p : Program) (index : SemanticIndex) (labels : Array Label)
    (policy : Node) : Option Violation :=
  match semanticInstructionOwner? p policy with
  | none => some ⟨.malformed, policy.nodeId, 8⟩
  | some owner =>
      let selected := semanticSelectedLabel p index labels owner policy.ceiling.toNat 32
        policy.actual .pub
      let pc := match semanticBlockCell? index owner.origin owner.actual with
        | some cell => labelAt labels cell
        | none => .pub
      let observed := selected.lub pc
      let ctSourceObserved := semanticCtSourceObservedLabel p index labels owner observed pc
      if policy.aux == 14 then none
      else if policy.aux == 10 then
        if ctSourceObserved.eqb .pub || ctSourceObserved.eqb .secretCT then none
        else some ⟨.ctPolicy, owner.nodeId, policy.required⟩
      else if policy.aux == 12 then
        if selected.eqb .secretCT && pc.neqb .secretCT then none
        else some ⟨.ctPolicy, owner.nodeId, policy.required⟩
      else if policy.aux == 15 then
        if observed.eqb .pub then none
        else if observed.eqb .secretCT then some ⟨.ctPolicy, owner.nodeId, policy.required⟩
        else some ⟨.flow, owner.nodeId, 1⟩
      else if observed.neqb .secretCT then none
      else some ⟨.ctPolicy, owner.nodeId, policy.required⟩

def semanticContractViolation (index : SemanticIndex) (labels : Array Label) (n : Node) :
    Option Violation :=
  if (n.aux == 0 || n.aux == 1) && n.actual != 0 then
    match semanticValueCell? index n.origin n.actual with
    | none => some ⟨.malformed, n.nodeId, 8⟩
    | some cell =>
        let actual := labelAt labels cell
        if n.flags == 0 then none
        else if n.flags == 1 then
          if actual.flowsTo n.labelA then none else some ⟨.flow, n.nodeId, 1⟩
        else if actual.neqb .secretCT then none else some ⟨.ctPolicy, n.nodeId, 30⟩
  else none

/-- A leaf return can end a private computation without escaping a Public continuation when the
    whole function cannot change any Public scalar/aggregate cell or shared state. This is a
    deliberately narrow sufficient condition, not a claim that function kind proves a call frame.
    Calls, releases, capability/state/external operations and whole-machine halts remain outside
    this class. In particular a private return followed by a Public write cannot qualify. -/
def semanticPrivateLeafInstructionB (p : Program) (index : SemanticIndex)
    (labels : Array Label) (n : Node) : Bool :=
  let privateDestination := n.required == 0 ||
    match semanticValueCell? index n.origin n.required with
    | some cell => (labelAt labels cell).neqb .pub
    | none => false
  privateDestination && match decodeSemanticInstrOp? n.aux with
    | some .scalar | some .aggregate | some .project | some .branch | some .jump |
      some .loop | some .range | some .dispatch | some .divRem |
      some .stringCompare | some .ctEq | some .ctSelect | some .ctLt => true
    | some .address | some .index => n.required != 0
    | some .trap => n.ceiling == 0
    | some .output =>
        n.ceiling == 1 && match semanticOperandValueIdAt? p n.nodeId 0 with
        | some valueId =>
            match semanticValueCell? index n.origin valueId with
            | some cell => (labelAt labels cell).neqb .pub
            | none => false
        | none => false
    | _ => false

/-- Build the leaf-return classification once, outside all per-region path walks. Missing owners,
    zero-operand returns, unsupported operations and missing output witnesses fail closed. -/
def semanticPrivateLeafReturnFunctions (p : Program) (index : SemanticIndex)
    (labels : Array Label) : Array Bool := Id.run do
  let count := index.functions.size + 1
  let mut eligible := Array.replicate count false
  let mut hasOutput := Array.replicate count false
  for function in index.functions do
    eligible := eligible.setIfInBounds function.origin.toNat
      (function.flags == 1 || function.flags == 4)
  for n in p.nodes do
    if n.op == .semInstruction then
      eligible := eligible.setIfInBounds n.origin.toNat
        (eligible.getD n.origin.toNat false && semanticPrivateLeafInstructionB p index labels n)
      if n.aux == 28 then hasOutput := hasOutput.setIfInBounds n.origin.toNat true
  return eligible.mapIdx fun function allowed => allowed && hasOutput.getD function false

def semanticPublicControlContinuationOK (p : Program) (index : SemanticIndex)
    (labels : Array Label) (n : Node) : Bool :=
  let block := (semanticBlockCell? index n.origin n.actual).map (labelAt labels) |>.getD .pub
  let selector := match semanticOperandValueIdAt? p n.nodeId 0 with
    | some valueId =>
        block.lub ((semanticValueCell? index n.origin valueId).map (labelAt labels) |>.getD block)
    | none => block
  let fuel := 4 * index.blocks.size + 1
  let visited := Array.replicate (index.blocks.size + 1) false
  match decodeSemanticInstrOp? n.aux with
  | some .dispatch =>
      if n.ceiling == 2 then
        match semanticOperandAt? p n.nodeId 0, semanticOperandAt? p n.nodeId 1 with
        | some start, some exit =>
            semanticStructuredPathsOK p index labels n.origin exit.required exit.required true
              fuel visited [start.required]
        | _, _ => false
      else if selector.eqb .pub then true else
        match semanticOperandAt? p n.nodeId 1, semanticOperandAt? p n.nodeId 2,
            semanticOperandAt? p n.nodeId 3 with
        | some left, some right, some merge =>
            semanticStructuredPathsOK p index labels n.origin merge.required merge.required true
              fuel visited [left.required, right.required]
        | _, _, _ => false
  | some .branch =>
      if selector.eqb .pub then true else
        match semanticOperandAt? p n.nodeId 1, semanticOperandAt? p n.nodeId 2,
            semanticOperandAt? p n.nodeId 3 with
        | some left, some right, some merge =>
            semanticStructuredPathsOK p index labels n.origin merge.required merge.required true fuel
              visited [left.required, right.required]
        | _, _, _ => false
  | some .loop | some .range =>
      if selector.eqb .pub then true else
        match semanticOperandAt? p n.nodeId 1, semanticOperandAt? p n.nodeId 2 with
        | some body, some exit =>
            semanticStructuredPathsOK p index labels n.origin n.actual exit.required true fuel visited
              [body.required]
        | _, _ => false
  | _ => true

def semanticInstructionFlowViolation (p : Program) (index : SemanticIndex) (labels : Array Label)
    (n : Node) : Option Violation :=
  match decodeSemanticInstrOp? n.aux with
  | some .stateWrite =>
      match semanticOperandValueIdAt? p n.nodeId 1,
          semanticImmediateAt? p n.nodeId 2 with
      | some valueId, some offset =>
          match semanticValueCell? index n.origin valueId with
          | some cell =>
              let pc := (semanticBlockCell? index n.origin n.actual).map
                (labelAt labels) |>.getD .pub
              let sink := semanticDeclaredStateLabelAt p offset
              if (labelAt labels cell).lub pc |>.flowsTo sink then none
              else some ⟨.flow, n.nodeId, 1⟩
          | none => some ⟨.malformed, n.nodeId, 8⟩
      | _, _ => some ⟨.malformed, n.nodeId, 8⟩
  | some .output =>
      match index.returnContractNodes[n.origin.toNat]?.join with
      | none => some ⟨.malformed, n.nodeId, 8⟩
      | some contract =>
          match semanticOperandValueIdAt? p n.nodeId 0 with
          | none => none
          | some valueId =>
              match semanticValueCell? index n.origin valueId with
              | some cell =>
                  let pc := (semanticBlockCell? index n.origin n.actual).map
                    (labelAt labels) |>.getD .pub
                  let actual := (labelAt labels cell).lub pc
                  if contract.flags == 1 then
                    if actual.flowsTo contract.labelA then none else some ⟨.flow, n.nodeId, 1⟩
                  else if contract.flags == 2 && actual.eqb .secretCT then
                    some ⟨.ctPolicy, n.nodeId, 30⟩
                  else none
              | none => some ⟨.malformed, n.nodeId, 8⟩
  | _ => none

def semanticValueTypeIdAt? (p : Program) (index : SemanticIndex) (instruction : Node)
    (position : Nat) : Option UInt32 :=
  (semanticOperandValueIdAt? p instruction.nodeId position).bind fun valueId =>
    (indexedSemanticValueNode? index instruction.origin valueId).map (fun value => value.ceiling)

def semanticDestinationTypeId? (index : SemanticIndex) (instruction : Node) : Option UInt32 :=
  (indexedSemanticValueNode? index instruction.origin instruction.required).map
    (fun value => value.ceiling)

def semanticCapabilityInstructionOK (p : Program) (index : SemanticIndex) (n : Node) : Bool :=
  let destinationType := semanticDestinationTypeId? index n
  let operandType := semanticValueTypeIdAt? p index n
  match decodeSemanticInstrOp? n.aux with
  | some .capMint =>
      match destinationType with
      | some typeId => typeId != 0 && (semanticCapabilityTypeNode? index typeId).isSome
      | none => false
  | some .capRestrict =>
      match destinationType, operandType 0, semanticImmediateAt? p n.nodeId 1 with
      | some destination, some source, some restriction =>
          destination != 0 && destination == source &&
            match semanticCapabilityTypeNode? index destination with
            | some declaration => maskSubset restriction declaration.ceiling
            | none => false
      | _, _, _ => false
  | some .capSplit | some .capDraw =>
      match destinationType, operandType 0 with
      | some destination, some source => destination != 0 && destination == source
      | _, _ => false
  | some .slotPut =>
      match operandType 0, operandType 1 with
      | some slotType, some capType => slotType != 0 && slotType == capType
      | _, _ => false
  | some .slotTake =>
      match destinationType, operandType 0 with
      | some capType, some slotType => capType != 0 && capType == slotType
      | _, _ => false
  | some .release | some .releaseCT =>
      match operandType 1 with
      | some typeId =>
          match semanticCapabilityTypeNode? index typeId with
          | some declaration =>
              if n.aux == 23 then declaration.aux == 1 else declaration.aux == 2
          | none => false
      | none => false
  | some _ => true
  | none => false

def semanticInstructionCapabilityViolation (p : Program) (index : SemanticIndex) (n : Node) :
    Option Violation :=
  if semanticCapabilityInstructionOK p index n then none
  else some ⟨.capabilityGraph, n.nodeId, n.aux⟩

def semanticValueOperandLabelAt (p : Program) (index : SemanticIndex) (labels : Array Label)
    (instruction : Node) (position : Nat) : Option Label := do
  let valueId ← semanticOperandValueIdAt? p instruction.nodeId position
  let cell ← semanticValueCell? index instruction.origin valueId
  pure (labelAt labels cell)

def semanticValueOperandsAvoidSecretCT (p : Program) (index : SemanticIndex)
    (labels : Array Label) (instruction : Node) : Nat → Bool
  | 0 => true
  | remaining + 1 =>
      let position := instruction.ceiling.toNat - (remaining + 1)
      let current := match semanticOperandKindAt? p instruction.nodeId position with
        | some 0 =>
            (semanticValueOperandLabelAt p index labels instruction position).all
              (fun label => label.neqb .secretCT)
        | some _ => true
        | none => false
      current && semanticValueOperandsAvoidSecretCT p index labels instruction remaining

def semanticControlOperandAvoidsSecretCT (p : Program) (index : SemanticIndex)
    (labels : Array Label) (instruction : Node) (op : SemanticInstrOp) : Bool :=
  let controls := op == .branch || op == .loop || op == .range || op == .closure ||
    op == .trap || (op == .dispatch && instruction.ceiling != 2)
  !controls ||
    (semanticValueOperandLabelAt p index labels instruction 0).all
      (fun label => label.neqb .secretCT)

def semanticRawResultDependenciesSafe (p : Program) (index : SemanticIndex)
    (labels : Array Label) (instruction : Node) (op : SemanticInstrOp) : Bool :=
  let destination := if instruction.required == 0 then none else
    (semanticValueCell? index instruction.origin instruction.required).map (labelAt labels)
  match destination with
  | none => true
  | some .secretCT => true
  | some _ =>
      match op with
      | .ffi | .actorBoundary | .call | .closure | .release | .releaseCT => true
      | .stateRead =>
          match semanticImmediateAt? p instruction.nodeId 1 with
          | some offset => (semanticDeclaredStateLabelAt p offset).neqb .secretCT
          | none => false
      | _ => semanticValueOperandsAvoidSecretCT p index labels instruction
        instruction.ceiling.toNat

def semanticRawStateWriteSafe (p : Program) (index : SemanticIndex) (labels : Array Label)
    (instruction : Node) (op : SemanticInstrOp) : Bool :=
  if op != .stateWrite then true else
    match semanticImmediateAt? p instruction.nodeId 2 with
    | none => false
    | some offset =>
        let sink := semanticDeclaredStateLabelAt p offset
        sink.eqb .secretCT ||
          ((semanticValueOperandLabelAt p index labels instruction 1).all
              (fun label => label.neqb .secretCT) &&
            ((semanticBlockCell? index instruction.origin instruction.actual).map
              (labelAt labels)).all (fun label => label.neqb .secretCT))

/-- Executable constructor typing used by the raw SecretCT lockstep proof. It contains no Rust
    verdict bit: every fact is recomputed from decoded operands, contracts, CFG pc labels, and the
    Lean least-label result. -/
def semanticRawSecretCTInstructionSafe (p : Program) (index : SemanticIndex)
    (labels : Array Label) (instruction : Node) : Bool :=
  match decodeSemanticInstrOp? instruction.aux with
  | none => false
  | some op =>
      semanticControlOperandAvoidsSecretCT p index labels instruction op &&
        semanticRawResultDependenciesSafe p index labels instruction op &&
        semanticRawStateWriteSafe p index labels instruction op

def semanticRawSecretCTViolation (p : Program) (index : SemanticIndex) (labels : Array Label)
    (n : Node) : Option Violation :=
  if n.op != .semInstruction || semanticRawSecretCTInstructionSafe p index labels n then none
  else some ⟨.ctPolicy, n.nodeId, 30⟩

def firstV8SecurityViolationList (p : Program) (index : SemanticIndex) (labels : Array Label) :
    List Node → Option Violation
  | [] => none
  | n :: rest =>
      let violation := match n.op with
        | .semPolicyClass => semanticPolicyViolation p index labels n
        | .semLabelContract => semanticContractViolation index labels n
        | .semInstruction =>
            match semanticInstructionFlowViolation p index labels n with
            | some violation => some violation
            | none =>
                match semanticInstructionCapabilityViolation p index n with
                | some violation => some violation
                | none => semanticRawSecretCTViolation p index labels n
        | _ => none
      match violation with
      | some violation => some violation
      | none => firstV8SecurityViolationList p index labels rest

def firstV8SecurityViolation (p : Program) : Option Violation :=
  let index := buildSemanticIndex p
  firstV8SecurityViolationList p index (semanticLabels p) p.nodes.toList

def verifyProgramWithContext (p : Program) (index : SemanticIndex) (labels : Array Label) :
    Option Violation :=
  match firstSemanticViolationWithIndex p index with
  | some v => some v
  | none =>
      match firstSemanticMetadataViolationList p index p.nodes.toList with
      | some v => some v
      | none =>
        match firstV8SecurityViolationList p index labels p.nodes.toList with
        | some v => some v
        | none =>
          match firstLocalViolation p.nodes with
          | some v => some v
          | none =>
            match firstAffineViolation p.nodes with
            | some v => some v
            | none =>
              match firstCapabilityViolation p with
              | some v => some v
              | none =>
                match firstQuantitativeViolation p with
                  | some v => some v
                  | none =>
                    match firstPathAffineViolation p with
                      | some v => some v
                      | none => firstGraphViolation p

def verifyProgram (p : Program) : Option Violation :=
  match firstSemanticViolation p with
  | some v => some v
  | none =>
      match firstSemanticMetadataViolation p with
      | some v => some v
      | none =>
        match firstV8SecurityViolation p with
        | some v => some v
        | none =>
          match firstLocalViolation p.nodes with
          | some v => some v
          | none =>
            match firstAffineViolation p.nodes with
            | some v => some v
            | none =>
              match firstCapabilityViolation p with
              | some v => some v
              | none =>
                match firstQuantitativeViolation p with
                  | some v => some v
                  | none =>
                    match firstPathAffineViolation p with
                      | some v => some v
                      | none => firstGraphViolation p

private def readU8? (bytes : ByteArray) (offset : Nat) : Option UInt8 :=
  if h : offset < bytes.size then some (bytes.get offset h) else none

private def readU32? (bytes : ByteArray) (offset : Nat) : Option UInt32 := do
  let a ← readU8? bytes offset
  let b ← readU8? bytes (offset + 1)
  let c ← readU8? bytes (offset + 2)
  let d ← readU8? bytes (offset + 3)
  return a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) |||
    (d.toUInt32 <<< 24)

private def decodeLabel? : UInt8 → Option Label
  | 0 => some .pub
  | 1 => some .internal
  | 2 => some .secret
  | 3 => some .secretCT
  | _ => none

private def decodeOp? : UInt8 → Option Op
  | 0 => some .flow
  | 1 => some .authority
  | 2 => some .declassify
  | 3 => some .ctUse
  | 4 => some .boundary
  | 5 => some .fixedCT
  | 6 => some .effect
  | 7 => some .consume
  | 8 => some .taintSeed
  | 9 => some .taintEdge
  | 10 => some .taintSink
  | 11 => some .taintCtUse
  | 12 => some .taintRelease
  | 13 => some .capOrigin
  | 14 => some .capRestrict
  | 15 => some .capSplit
  | 16 => some .capDraw
  | 17 => some .capSink
  | 18 => some .capRelease
  | 19 => some .capSlot
  | 20 => some .capSlotPut
  | 21 => some .capSlotTake
  | 22 => some .capMeet
  | 23 => some .pathFork
  | 24 => some .pathArm
  | 25 => some .pathJoin
  | 26 => some .pathLoop
  | 27 => some .pathBack
  | 28 => some .pathBreak
  | 29 => some .pathLoopJoin
  | 30 => some .intCell
  | 31 => some .diffLe
  | 32 => some .quantityUse
  | 33 => some .semProgram
  | 34 => some .semFunction
  | 35 => some .semValue
  | 36 => some .semBlock
  | 37 => some .semInstruction
  | 38 => some .semOperand
  | 39 => some .semLabelContract
  | 40 => some .semCapabilityType
  | 41 => some .semPolicyClass
  | 42 => some .semRefinementFact
  | 43 => some .semRuntimeGuard
  | _ => none

private def decodeNode? (bytes : ByteArray) (offset : Nat) : Option Node := do
  let op ← readU8? bytes offset >>= decodeOp?
  let labelA ← readU8? bytes (offset + 1) >>= decodeLabel?
  let labelB ← readU8? bytes (offset + 2) >>= decodeLabel?
  let flags ← readU8? bytes (offset + 3)
  let origin ← readU32? bytes (offset + 4)
  let actual ← readU32? bytes (offset + 8)
  let required ← readU32? bytes (offset + 12)
  let ceiling ← readU32? bytes (offset + 16)
  let aux ← readU32? bytes (offset + 20)
  let nodeId ← readU32? bytes (offset + 24)
  let reserved ← readU32? bytes (offset + 28)
  if reserved != 0 then none else
    some { op, labelA, labelB, flags, origin, actual, required, ceiling, aux, nodeId }

private def magicOK (bytes : ByteArray) : Bool :=
  bytes.size ≥ 4 &&
    (readU8? bytes 0 == some 0x43) &&
    (readU8? bytes 1 == some 0x53) &&
    (readU8? bytes 2 == some 0x49) &&
    (readU8? bytes 3 == some 0x52)

def decode (bytes : ByteArray) : Option Program := do
  if bytes.size > maxWireBytes || bytes.size < headerBytes || !magicOK bytes then none else
  let version ← readU32? bytes 4
  if version != wireVersion then none else
  let count32 ← readU32? bytes 8
  let count := count32.toNat
  if count > maxNodes then none else
  if bytes.size != headerBytes + count * nodeBytes then none else
  let mut nodes := #[]
  for i in [0:count] do
    let n ← decodeNode? bytes (headerBytes + i * nodeBytes)
    if n.nodeId != UInt32.ofNat (i + 1) then none
    nodes := nodes.push n
  return ⟨nodes⟩

def ViolationKind.code : ViolationKind → UInt32
  | .malformed => 1
  | .flow => 2
  | .legitimacy => 3
  | .authority => 4
  | .affine => 5
  | .declassification => 6
  | .ctPolicy => 7
  | .effect => 8
  | .taintGraph => 9
  | .capabilityGraph => 10

/-- Packed native verdict: zero is verified; otherwise code:16, detail:16, node-id:32. -/
def packViolation (v : Violation) : UInt64 :=
  (v.nodeId.toUInt64 <<< 32) ||| ((v.detail &&& 0xffff).toUInt64 <<< 16) |||
    v.kind.code.toUInt64

def verifyBytes (bytes : ByteArray) : UInt64 :=
  match decode bytes with
  | none => packViolation ⟨.malformed, 0, 0⟩
  | some p =>
      match semanticProgramNode? p with
      | none => packViolation ⟨.malformed, 0, 7⟩
      | some _ => (verifyProgram p).map packViolation |>.getD 0

@[export sigil_csir_verify]
def exportedVerify (bytes : ByteArray) : UInt64 := verifyBytes bytes

end LambdaSigil.Combined
