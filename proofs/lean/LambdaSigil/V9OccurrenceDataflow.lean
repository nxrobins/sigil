import LambdaSigil.V9BoundaryContracts
import LambdaSigil.SemanticKernel

/-!
# Host-result seeds for the v9 semantic dataflow graph

Boundary extraction supplies exact decoded host identities, signatures and result contracts.
Each result seed resolves the actual function-local value declaration through the semantic index
and checks its identity before using the declaration's global cell. Missing/mismatched extraction
rejects; it does not silently omit a result. Legacy bindings retain an Internal result policy.

Existing source seeds and the actual semantic adjacency are preserved. Only the initial label
array is extended, and saturation retains the existing four-times-cell-count work budget. The
machine below is separately assembled from that label array; historical v8 decoding, checking,
and raw semantics are not changed. This is not production acceptance or Public noninterference.
-/

namespace LambdaSigil.Combined.V9.OccurrenceDataflow

open BoundaryContracts

structure HostSeed where
  owner : UInt32
  functionId : UInt32
  valueId : UInt32
  cell : UInt32
  label : Label
  deriving Repr, BEq, DecidableEq

/-- Exact destination identity is additional to ABI matching: the dataflow cell is the actual
    semValue record, not a Rust label, a function-local number, or the FFI instruction's node ID. -/
def hostSeed? (_program : Program) (contracts : Index) (index : SemanticIndex) (owner : Node) :
    Option (Option HostSeed) := do
  if owner.op != .semInstruction || owner.aux != 15 then some none else do
  let site ← site? contracts owner.nodeId
  if site.owner != owner.nodeId || site.functionId != owner.origin then none
  match site.kind with
  | .ffi _ contract =>
      if owner.required == 0 then
        if contract.results.isEmpty then some none else none
      else do
        if contract.results.size != 1 then none
        let result ← contract.results[0]?
        let value ← indexedSemanticValueNode? index owner.origin owner.required
        if value.op != .semValue || value.origin != owner.origin || value.actual != owner.required then none
        some (some ⟨owner.nodeId, owner.origin, owner.required, value.nodeId, result.label⟩)
  | _ => none

def collectHostSeedStep? (program : Program) (contracts : Index)
    (index : SemanticIndex) (collected : Option (Array HostSeed)) (owner : Node) :
    Option (Array HostSeed) := do
  let seeds ← collected
  let seed ← hostSeed? program contracts index owner
  some (match seed with | none => seeds | some seed => seeds.push seed)

/-- Scan the production record array directly. In particular, do not convert the array to a
    recursively consumed list: canonical programs may contain one million records. The optional
    accumulator is absorbing after the first malformed host site, so later records cannot turn a
    failure back into acceptance. -/
def collectHostSeeds? (program : Program) (contracts : Index) (index : SemanticIndex) :
    Option (Array HostSeed) :=
  program.base.nodes.foldl (collectHostSeedStep? program contracts index) (some #[])

def hostSeeds? (program : Program) (contracts : Index) (index : SemanticIndex) :
    Option (Array HostSeed) := collectHostSeeds? program contracts index

def applyHostSeeds (seeds : Array HostSeed) (labels : Array Label) : Array Label :=
  seeds.foldl (fun current seed => raiseCell current seed.cell seed.label) labels

def seededLabels (program : Program) (index : SemanticIndex) (seeds : Array HostSeed) :
    Array Label := applyHostSeeds seeds (semanticSeedLabelsWithIndex program.base index)

def saturate (program : Program) (index : SemanticIndex) (seeds : Array Label) : Array Label :=
  let count := semanticTaintCellCount program.base
  saturateGraphWorklist (semanticTaintAdjacencyWithIndex program.base index) (4 * count)
    ((List.range count).map UInt32.ofNat) seeds

def hostSeedsFlowB (seeds : Array HostSeed) (labels : Array Label) : Bool :=
  seeds.all (fun seed => seed.cell.toNat < labels.size &&
    seed.label.flowsTo (labelAt labels seed.cell))

structure Analysis where
  contracts : Index
  semanticIndex : SemanticIndex
  hostSeeds : Array HostSeed
  seeds : Array Label
  labels : Array Label
  deriving Repr

def analyze? (program : Program) : Option Analysis := do
  let contracts ← BoundaryContracts.extract? program
  let index := buildSemanticIndex program.base
  let hostSeeds ← hostSeeds? program contracts index
  let seeds := seededLabels program index hostSeeds
  let labels := saturate program index seeds
  if hostSeedsFlowB hostSeeds labels then some ⟨contracts, index, hostSeeds, seeds, labels⟩ else none

/-- This is a new v9-derived candidate machine, not an alteration of semanticProgramOf. -/
def semanticProgram (program : Program) (analysis : Analysis) : Semantic.SemanticProgram :=
  Semantic.semanticProgramOfWith program.base analysis.semanticIndex analysis.labels

end LambdaSigil.Combined.V9.OccurrenceDataflow
