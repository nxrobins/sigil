import LambdaSigil.V9OccurrenceDataflow
import LambdaSigil.RankedDecodedOccurrence

/-!
# Root-entry seeds for v9 invocation influence

External root declarations contribute entry-occurrence lower bounds before the existing bounded
invocation worklist runs. They are not ceilings on internal calls, and return-occurrence labels
are not entry seeds. Canonical role-zero internal declarations contribute no boundary seed.

Root/function correspondence and final root-entry constraints are independently checked against
the actual declarations. Existing local call-site seeds are raised, never replaced. This is an
internal analysis layer, not production acceptance, host approval, or Public noninterference.
-/

namespace LambdaSigil.Combined.V9.OccurrenceDataflowInvocation

open Semantic OccurrenceInvocation

def roleZeroCanonicalB (root : FunctionRootContract) : Bool :=
  root.entryOccurrence.eqb .pub && root.returnOccurrence.eqb .pub &&
    root.actorType == 0 && root.handlerId == 0 && !root.isEntry

/-- The function array and the contract roots must agree position by position. Equality with
    program roots prevents a helper caller from substituting a different entry-seed table. -/
def rootLayoutChecks (program : Program) (contracts : BoundaryContracts.Index)
    (machine : SemanticProgram) : Bool :=
  functionLayoutB machine && decide (contracts.roots = program.roots) &&
    contracts.roots.size == machine.functions.size &&
    (List.range contracts.roots.size).all (fun position =>
      match contracts.roots[position]?, machine.functions[position]? with
      | some root, some function =>
          root.functionId.toNat == position + 1 && function.id == root.functionId &&
            (root.role != 0 || roleZeroCanonicalB root)
      | _, _ => false)

def seedRootEntry (labels : Array Label) (root : FunctionRootContract) : Array Label :=
  if root.role == 0 then labels else raiseCell labels root.functionId root.entryOccurrence

def seedRootLabels (roots : Array FunctionRootContract) (labels : Array Label) : Array Label :=
  roots.foldl seedRootEntry labels

def seedRootEntries? (program : Program) (contracts : BoundaryContracts.Index)
    (machine : SemanticProgram) (plan : InvocationPlan) : Option InvocationPlan :=
  if rootLayoutChecks program contracts machine &&
      plan.seeds.size == invocationCellCount machine &&
      plan.adjacency.size == invocationCellCount machine then
    some { plan with seeds := seedRootLabels contracts.roots plan.seeds }
  else none

/-- Entry declarations are lower bounds on possible invocation influence. In particular a
    Public entry declaration never caps a private internal invocation of the same function. -/
def rootEntryChecks (program : Program) (contracts : BoundaryContracts.Index)
    (machine : SemanticProgram) (labels : Array Label) : Bool :=
  rootLayoutChecks program contracts machine && labels.size == invocationCellCount machine &&
    contracts.roots.all (fun root => root.role == 0 ||
      root.entryOccurrence.flowsTo (labelAt labels root.functionId))

structure StateContractEntry where
  functionId : UInt32
  offset : UInt32
  label : Label
  /-- Canonical node ID of an exact-key declaration whose label is `label`.  Because the label
      lattice is a chain, the coalesced lub is always witnessed by one member of its group. -/
  witnessNodeId : UInt32
  deriving Repr

structure Analysis where
  dataflow : OccurrenceDataflow.Analysis
  localAnalysis : DecodedOccurrence.Analysis
  labels : Array Label
  /-- Exact declaration-derived state ceilings, sorted by `(functionId, offset)`.  Building and
      coalescing this once gives every state write a binary lookup rather than a record scan. -/
  stateContracts : Array StateContractEntry
  deriving Repr

def stateContractDeclarationB (contract : Node) : Bool :=
  contract.op == .semLabelContract && contract.aux == 3 && contract.flags == 1

private def collectStateContract (functionCount : Nat)
    (entries : Array StateContractEntry) (contract : Node) : Array StateContractEntry :=
  if stateContractDeclarationB contract && contract.origin != 0 &&
      contract.origin.toNat ≤ functionCount then
    entries.push ⟨contract.origin, contract.actual, contract.labelA, contract.nodeId⟩
  else entries

private def stateContractEntryLE (left right : StateContractEntry) : Bool :=
  left.functionId < right.functionId ||
    (left.functionId == right.functionId && left.offset ≤ right.offset)

private def mergeStateContractEntry (entries : Array StateContractEntry)
    (entry : StateContractEntry) : Array StateContractEntry :=
  match entries.back? with
  | some previous =>
      if previous.functionId == entry.functionId && previous.offset == entry.offset then
        let joined := previous.label.lub entry.label
        let witnessNodeId :=
          if joined == previous.label then previous.witnessNodeId else entry.witnessNodeId
        entries.setIfInBounds (entries.size - 1)
          { previous with label := joined, witnessNodeId }
      else entries.push entry
  | none => entries.push entry

/-- One-pass exact `(functionId, state offset)` declaration index.  Function IDs are one-based,
    then merge-sort and one-pass coalescing make each pair unique.  Malformed/out-of-range
    declarations cannot acquire an entry; the retained semantic verifier independently rejects
    them before this analysis can authorize a program. -/
def buildStateContractIndex (program : Program) (functionCount : Nat) :
    Array StateContractEntry :=
  let collected := program.base.nodes.foldl (collectStateContract functionCount) #[]
  (collected.mergeSort stateContractEntryLE).foldl mergeStateContractEntry #[]

def binarySearchStateContract (index : Array StateContractEntry)
    (functionId offset : UInt32) : Nat → Nat → Nat → Option Label
  | 0, _, _ => none
  | fuel + 1, lower, upper =>
      if lower ≥ upper then none
      else
        let middle := lower + (upper - lower) / 2
        match index[middle]? with
        | none => none
        | some entry =>
            if entry.functionId == functionId && entry.offset == offset then some entry.label
            else if entry.functionId < functionId ||
                (entry.functionId == functionId && entry.offset < offset) then
              binarySearchStateContract index functionId offset fuel (middle + 1) upper
            else binarySearchStateContract index functionId offset fuel lower middle

def stateLabelForFunctionAt? (index : Array StateContractEntry)
    (functionId offset : UInt32) : Option Label :=
  binarySearchStateContract index functionId offset (index.size + 1) 0 index.size

/-- Forward half of the optimized-index postcheck. Each declaration is visited once and performs
    one binary lookup, proving that the returned exact-key sink is an upper bound. The reverse
    witness check below is also required: without it, a higher label borrowed from another key
    could pass this direction and authorize a write. -/
def stateContractRecordCoveredB (functionCount : Nat) (index : Array StateContractEntry)
    (contract : Node) : Bool :=
  if stateContractDeclarationB contract then
    contract.origin != 0 && contract.origin.toNat ≤ functionCount &&
      match stateLabelForFunctionAt? index contract.origin contract.actual with
      | none => false
      | some sink => contract.labelA.flowsTo sink
  else true

/-- Reverse/exact-key half of the optimized-index check.  Every returned index label carries a
    constant-time source witness with the same function, offset, and label.  Together with the
    declaration-to-lookup upper-bound check above, this pins the lookup result to the exact
    declared lub and prevents a higher label from another actor authorizing a write. -/
def stateContractEntryWitnessedB (program : Program) (entry : StateContractEntry) : Bool :=
  entry.witnessNodeId != 0 &&
    match program.base.nodes[entry.witnessNodeId.toNat - 1]? with
    | none => false
    | some contract =>
        contract.nodeId == entry.witnessNodeId && stateContractDeclarationB contract &&
          contract.origin == entry.functionId && contract.actual == entry.offset &&
          contract.labelA == entry.label

def stateContractIndexChecks (program : Program) (functionCount : Nat)
    (index : Array StateContractEntry) : Bool :=
  program.base.nodes.all (stateContractRecordCoveredB functionCount index) &&
    index.all (stateContractEntryWitnessedB program)

/-- The only public pipeline input is the decoded v9 program. Both local occurrence and call
    extraction use the machine assembled from its source and exact host-result labels. -/
def analyze? (program : Program) : Option Analysis := do
  let dataflow ← OccurrenceDataflow.analyze? program
  let machine := OccurrenceDataflow.semanticProgram program dataflow
  let stateContracts := buildStateContractIndex program machine.functions.size
  let localAnalysis ← RankedDecodedOccurrence.analyze? machine
  let plan ← invocationPlan? machine localAnalysis.frontiers
  let rootedPlan ← seedRootEntries? program dataflow.contracts machine plan
  let labels := computeInvocationLabels machine rootedPlan
  if stateContractIndexChecks program machine.functions.size stateContracts &&
      rootEntryChecks program dataflow.contracts machine labels &&
      invocationChecks machine localAnalysis.frontiers labels then
    some ⟨dataflow, localAnalysis, labels, stateContracts⟩
  else none

end LambdaSigil.Combined.V9.OccurrenceDataflowInvocation
