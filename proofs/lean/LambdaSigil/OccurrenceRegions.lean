import LambdaSigil.SemanticKernel

/-!
# Executable CFG and checked successful-path escape foundation

This Init-only module builds intraprocedural edges from decoded instruction targets and checks
local evidence for successful-path postdominators. Each function has its own synthetic return
vertex. A callee return is not a root output observation, and calls retain separate invocation
sites rather than losing their effects in the caller-continuation edge.

The checked parent index is an internal algorithm boundary, not an accepted wire certificate.
There is no production caller or complete immediate-postdominator constructor yet. Its ancestry
test walks parent links, so this foundation is not the performance-qualified region index. The
checks prove sound reported continuations, not completeness of control dependence: using an
incomplete tree to approve occurrences would be unsound. Proofs live in OccurrenceRegionSecurity.
-/

namespace LambdaSigil.Combined.OccurrenceRegions

open Semantic

structure ControlGraph where
  successors : Array (List Nat)
  successfulExits : List Nat
  deriving Repr, Inhabited

def ControlGraph.size (graph : ControlGraph) : Nat := graph.successors.size

def ControlGraph.wellFormedB (graph : ControlGraph) : Bool :=
  graph.successfulExits.all (fun exit => exit < graph.size &&
    (graph.successors.getD exit []).isEmpty) &&
  graph.successors.all (fun targets => targets.all (fun target => target < graph.size))

/-- A function's synthetic return is distinct from all instructions and from other functions'
    returns. Whether a real output is observable depends on the active root/frame context and
    must be established by the later raw-path correspondence, not by this local graph. -/
def functionReturn (p : SemanticProgram) (functionId : UInt32) : Nat :=
  p.instructions.size + (functionId.toNat - 1)

/-- Actual targets only: merge markers and numeric comparisons between blocks are absent.
    Calls summarize successful return to their real next instruction; invocation influence and
    nonreturning callees are separate obligations, retained by `callSites` below. Conditional
    traps retain their successful edge; unconditional trap/abortive nodes have no success edge.
    A callee-local halt is a conservative terminal edge here, not evidence of a normal return:
    the raw machine retains its frame and the successful-execution contract excludes that case.
    Malformed targets are retained here and rejected by the whole-graph check, never dropped. -/
def instructionSuccessors (p : SemanticProgram) (pc : Nat) (instruction : Instruction) :
    List Nat :=
  match instruction.op with
  | .output | .halt => [functionReturn p instruction.functionId]
  | .abortiveEffect => []
  | .trap => if instruction.operandCount == 0 then [] else [pc + 1]
  | .branch | .loop | .range => [instruction.target.toNat, instruction.alternate.toNat]
  | .dispatch => if instruction.operandCount == 2 then [instruction.target.toNat]
      else [instruction.target.toNat, instruction.alternate.toNat]
  | .jump => [instruction.target.toNat]
  | .call | .closure | .scalar | .aggregate | .project | .actorBoundary | .stateRead
  | .stateWrite | .slotNew | .slotPut | .slotTake | .effect | .ffi | .allocation
  | .address | .index | .capMint | .capRestrict | .capSplit | .capDraw | .capExercise
  | .release | .releaseCT | .ctEq | .ctSelect | .ctLt | .divRem | .stringCompare => [pc + 1]

def decodedControlGraph (p : SemanticProgram) : ControlGraph :=
  { successors := (p.instructions.mapIdx (instructionSuccessors p)) ++
      Array.replicate p.functions.size []
    successfulExits := List.range' p.instructions.size p.functions.size }

/-- These sites require a separate complete invocation summary. They are never converted into
    observable output actions merely because a helper has a Public return contract. -/
def callSites (p : SemanticProgram) : Array Nat :=
  (List.range p.instructions.size).filter (fun pc =>
    match p.instructions[pc]? with
    | some instruction => instruction.op == .call || instruction.op == .closure
    | none => false) |>.toArray

def decodedControlGraphWellFormedB (p : SemanticProgram) : Bool :=
  (decodedControlGraph p).wellFormedB &&
  (List.range p.functions.size).all (fun position =>
    match p.functions[position]? with
    | none => false
    | some function => function.id.toNat == position + 1 &&
        match p.instructions[function.firstInstruction.toNat]? with
        | some entry => entry.functionId == function.id
        | none => false) &&
  (List.range p.instructions.size).all (fun pc =>
    match p.instructions[pc]? with
    | none => false
    | some instruction =>
        instruction.functionId != 0 && instruction.functionId.toNat ≤ p.functions.size &&
        (instructionSuccessors p pc instruction).all (fun target =>
          if target < p.instructions.size then
            match p.instructions[target]? with
            | some next => next.functionId == instruction.functionId
            | none => false
          else target == functionReturn p instruction.functionId &&
            (instruction.op == .output || instruction.op == .halt)))

/-- Success ranks are decreasing witnesses to a successful exit. Their backwards-closure check
    also prevents silently omitting any vertex of a successful path. Parent links report only
    claimed postdominators; neither these arrays nor supplied merge operands are trusted. -/
structure EscapeIndex where
  parent : Array Nat
  successRank : Array (Option Nat)
  deriving Repr, Inhabited

def EscapeIndex.parentAt (index : EscapeIndex) (node : Nat) : Nat :=
  index.parent.getD node node

def EscapeIndex.rankAt (index : EscapeIndex) (node : Nat) : Option Nat :=
  index.successRank.getD node none

def EscapeIndex.liveB (index : EscapeIndex) (node : Nat) : Bool := (index.rankAt node).isSome

def ancestorWithin (index : EscapeIndex) (candidate : Nat) : Nat → Nat → Bool
  | 0, node => candidate == node
  | fuel + 1, node => candidate == node ||
      ancestorWithin index candidate fuel (index.parentAt node)

def ancestorB (index : EscapeIndex) (candidate node : Nat) : Bool :=
  ancestorWithin index candidate index.parent.size node

def rankDecreasesB (index : EscapeIndex) (rank node : Nat) : Bool :=
  match index.rankAt node with
  | none => false
  | some nextRank => nextRank < rank

def successJustifiedB (graph : ControlGraph) (index : EscapeIndex) (node : Nat) : Bool :=
  match index.rankAt node with
  | none => true
  | some rank => graph.successfulExits.contains node ||
      (graph.successors.getD node []).any (rankDecreasesB index rank)

def parentRankedB (graph : ControlGraph) (index : EscapeIndex) (node : Nat) : Bool :=
  match index.rankAt node with
  | none => true
  | some rank => graph.successfulExits.contains node ||
      (index.parentAt node < graph.size && rankDecreasesB index rank (index.parentAt node))

def edgeParentB (index : EscapeIndex) (source target : Nat) : Bool :=
  !index.liveB target || (index.liveB source && ancestorB index (index.parentAt source) target)

/-- Soundness checks use only root, rank, and individual edge conditions. They contain no
    assumed path-postdominance result and no relational output/state equality. Failure is closed:
    malformed arrays, invented reachability, missing successful nodes, or unjustified parents
    reject the entire candidate. Exact-tree completeness and an internal constructor remain open.
-/
def escapeIndexChecks (graph : ControlGraph) (index : EscapeIndex) : Bool :=
  graph.wellFormedB && index.parent.size == graph.size &&
    index.successRank.size == graph.size &&
    graph.successfulExits.all (fun exit => index.parentAt exit == exit &&
      index.rankAt exit == some 0) &&
    (List.range graph.size).all (fun node => successJustifiedB graph index node &&
      parentRankedB graph index node &&
      (graph.successors.getD node []).all (edgeParentB index node))

/-- A positive repetition witness, not a complete classifier: some successful successor must
    return to this controller. A candidate whose tree is incomplete may miss such witnesses. -/
def repeatsB (graph : ControlGraph) (index : EscapeIndex) (controller : Nat) : Bool :=
  controller < graph.size && (graph.successors.getD controller []).any
    (fun successor => index.liveB successor && ancestorB index controller successor)

end LambdaSigil.Combined.OccurrenceRegions
