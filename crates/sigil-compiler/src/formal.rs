//! Canonical Combined Security IR projection and mandatory Lean verdict.
//!
//! The projection is intentionally total over the resolved typed vocabulary:
//! every statement and expression variant is classified below. The linked Lean
//! kernel decodes and checks the exact bytes fingerprinted in the report.
//!
//! Model version 9 retains the verifier-owned taint, capability, and quantitative cells from v6,
//! the complete v8 semantic prefix, and adds mandatory occurrence and host-boundary declarations
//! projected from AIR. The Lean kernel computes their cyclic finite-lattice fixed point, then checks
//! sinks, pc-taint-sensitive operations, and both declassification stages from
//! the derived labels. It also derives capability legitimacy, BV32 authority
//! attenuation, control-flow meet, and slot meet from origin/edge records.
//! Branch and loop markers make capability consumption path-sensitive across
//! `if`/`match` joins, loop back-edges, `continue`, and `break` exits.
//! Split/draw amounts are linked to signed integer cells and mandatory guest/host
//! guards. A Lean difference-constraint classifier consumes exact literals and
//! preserved literal-RHS refinement bounds without making dynamic balance a
//! compile-time fiction.

use sha2::{Digest, Sha256};
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

use crate::air::{
    AirFunction, AirFunctionKind, AirLabelContract, AirPolicyClass, AirProgram, AirReleaseStage,
    AirStmt, AirTerminator, AirType, AirValue, AirValueKind, BlockId, FuncId, VarId,
};
use crate::ast::{BinaryOp, Literal, RefinementOp, RefinementRhs, TaintLabel};
use crate::diagnostics::{Diagnostic, codes};
use crate::registries::AuthorityRegistry;
use crate::span::Span;
use crate::type_check::Type;
use crate::typed_ast::{
    TypedBlock, TypedExpr, TypedExprKind, TypedFStringPart, TypedIntrinsicKind, TypedProgram,
    TypedStmt,
};

pub const CSIR_MODEL_VERSION: u32 = 9;
const RETAINED_V8_PREFIX_VERSION: u32 = 8;
const HEADER_BYTES: usize = 12;
const NODE_BYTES: usize = 32;
const MAX_WIRE_BYTES: usize = 64 * 1024 * 1024;
const MAX_NODES: usize = 1_000_000;

const CHECKER_KERNEL_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/CombinedKernel.lean");
const SEMANTIC_KERNEL_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/SemanticKernel.lean");
const HOST_PROFILE_KERNEL_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/HostProfileKernel.lean");
const HOST_PROFILE_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/HostProfileSecurity.lean");
const OCCURRENCE_WIRE_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceWire.lean");
const OCCURRENCE_WIRE_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceWireSecurity.lean");
const OCCURRENCE_REGIONS_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceRegions.lean");
const OCCURRENCE_REGION_CONSTRUCTION_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceRegionConstruction.lean");
const OCCURRENCE_TRANSFER_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceTransfer.lean");
const OCCURRENCE_TRANSFER_CONSTRUCTION_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceTransferConstruction.lean");
const DECODED_OCCURRENCE_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/DecodedOccurrence.lean");
const ANCESTOR_INTERVALS_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/AncestorIntervals.lean");
const INTERVAL_ESCAPE_CHECKS_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/IntervalEscapeChecks.lean");
const PRIORITY_OCCURRENCE_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PriorityOccurrence.lean");
const OCCURRENCE_INVOCATION_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceInvocation.lean");
const RANKED_DECODED_OCCURRENCE_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/RankedDecodedOccurrence.lean");
const V9_BOUNDARY_CONTRACTS_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/V9BoundaryContracts.lean");
const V9_OCCURRENCE_DATAFLOW_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/V9OccurrenceDataflow.lean");
const V9_OCCURRENCE_DATAFLOW_INVOCATION_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/V9OccurrenceDataflowInvocation.lean");
const OCCURRENCE_ACTIVATION_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceActivation.lean");
const V9_OCCURRENCE_KERNEL_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/V9OccurrenceKernel.lean");
const V9_OCCURRENCE_KERNEL_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/V9OccurrenceKernelSecurity.lean");
const V9_OCCURRENCE_DATAFLOW_INVOCATION_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/V9OccurrenceDataflowInvocationSecurity.lean");
const V9_OCCURRENCE_DATAFLOW_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/V9OccurrenceDataflowSecurity.lean");
const RANKED_DECODED_OCCURRENCE_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/RankedDecodedOccurrenceSecurity.lean");
const OCCURRENCE_INVOCATION_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceInvocationSecurity.lean");
const DECODED_OCCURRENCE_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/DecodedOccurrenceSecurity.lean");
const PRIORITY_OCCURRENCE_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PriorityOccurrenceSecurity.lean");
const OCCURRENCE_TRANSFER_CONSTRUCTION_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceTransferConstructionSecurity.lean");
const OCCURRENCE_TRANSFER_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceTransferSecurity.lean");
const OCCURRENCE_REGION_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceRegionSecurity.lean");
const INTERVAL_ESCAPE_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/IntervalEscapeSecurity.lean");
const ANCESTOR_INTERVAL_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/AncestorIntervalSecurity.lean");
const V9_BOUNDARY_CONTRACTS_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/V9BoundaryContractsSecurity.lean");
const OCCURRENCE_REFERENCE_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceReference.lean");
const NATIVE_BRIDGE_BUILD_SOURCE: &[u8] = include_bytes!("../../sigil-formal-bridge/build.rs");
const NATIVE_BRIDGE_C_SOURCE: &[u8] = include_bytes!("../../sigil-formal-bridge/native/bridge.c");
const NATIVE_BRIDGE_RUST_SOURCE: &[u8] = include_bytes!("../../sigil-formal-bridge/src/lib.rs");
const CHECKER_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/CombinedSecurity.lean");
const PRIVATE_LEAF_RETURN_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PrivateLeafReturnSecurity.lean");
const SEMANTIC_PROOF_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/SemanticSecurity.lean");
const SEMANTIC_DATAFLOW_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/SemanticDataflow.lean");
const SEMANTIC_INDEX_BOUNDS_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/SemanticIndexBounds.lean");
const DECODER_NODE_IDS_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/DecoderNodeIds.lean");
const RELEASE_SYNCHRONIZATION_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/ReleaseSynchronization.lean");
const PUBLIC_REGION_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicRegionSecurity.lean");
const PUBLIC_FRAME_BOUND_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicFrameBoundSecurity.lean");
const PUBLIC_FRAME_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicFrameSecurity.lean");
const PUBLIC_LOCAL_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicLocalSecurity.lean");
const PUBLIC_TRACE_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicTraceSecurity.lean");
const PUBLIC_WEAK_ALIGNMENT_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicWeakAlignment.lean");
const PUBLIC_RELEASE_SYNCHRONIZATION_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicReleaseSynchronization.lean");
const DECODED_OCCURRENCE_PREFIX_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/DecodedOccurrencePrefix.lean");
const PUBLIC_REGION_CONVERGENCE_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicRegionConvergence.lean");
const PUBLIC_PRIVATE_SEGMENT_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicPrivateSegmentSecurity.lean");
const PUBLIC_MATCHING_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicMatchingSecurity.lean");
const PUBLIC_STEP_CLASSIFICATION_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicStepClassification.lean");
const PUBLIC_EXECUTION_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicExecutionSecurity.lean");
const PUBLIC_NONPUBLIC_STEP_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicNonpublicStepSecurity.lean");
const PUBLIC_MATCHED_PROGRESS_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicMatchedProgressSecurity.lean");
const PUBLIC_PRIVATE_RELEASE_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicPrivateReleaseSecurity.lean");
const PUBLIC_CONTINUATION_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicContinuationSecurity.lean");
const PUBLIC_SAME_CONTROL_PROGRESS_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicSameControlProgressSecurity.lean");
const PUBLIC_RELEASE_PROGRESS_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicReleaseProgressSecurity.lean");
const PUBLIC_DISPATCHER_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicDispatcherSecurity.lean");
const PUBLIC_CONTROLLER_SEGMENT_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicControllerSegmentSecurity.lean");
const PUBLIC_PRIVATE_INVOCATION_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicPrivateInvocationSecurity.lean");
const PUBLIC_SYNTHETIC_RETURN_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicSyntheticReturnSecurity.lean");
const PUBLIC_BISIMULATION_SECURITY_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/PublicBisimulationSecurity.lean");
const RAW_CLAIM_SURFACE_SOURCE: &[u8] =
    include_bytes!("../../../proofs/lean/LambdaSigil/RawClaimSurface.lean");
const LEAN_TOOLCHAIN: &str = include_str!("../../../proofs/lean/lean-toolchain");

const CHECKER_EVIDENCE_SOURCES: [&[u8]; 70] = [
    CHECKER_KERNEL_SOURCE,
    SEMANTIC_KERNEL_SOURCE,
    CHECKER_PROOF_SOURCE,
    PRIVATE_LEAF_RETURN_PROOF_SOURCE,
    SEMANTIC_PROOF_SOURCE,
    SEMANTIC_DATAFLOW_SOURCE,
    SEMANTIC_INDEX_BOUNDS_SOURCE,
    DECODER_NODE_IDS_SOURCE,
    RELEASE_SYNCHRONIZATION_SOURCE,
    PUBLIC_REGION_SECURITY_SOURCE,
    PUBLIC_FRAME_BOUND_SECURITY_SOURCE,
    PUBLIC_FRAME_SECURITY_SOURCE,
    PUBLIC_LOCAL_SECURITY_SOURCE,
    PUBLIC_TRACE_SECURITY_SOURCE,
    PUBLIC_WEAK_ALIGNMENT_SOURCE,
    PUBLIC_RELEASE_SYNCHRONIZATION_SOURCE,
    DECODED_OCCURRENCE_PREFIX_SOURCE,
    PUBLIC_REGION_CONVERGENCE_SOURCE,
    PUBLIC_PRIVATE_SEGMENT_SECURITY_SOURCE,
    PUBLIC_MATCHING_SECURITY_SOURCE,
    PUBLIC_STEP_CLASSIFICATION_SOURCE,
    PUBLIC_EXECUTION_SECURITY_SOURCE,
    PUBLIC_NONPUBLIC_STEP_SECURITY_SOURCE,
    PUBLIC_MATCHED_PROGRESS_SECURITY_SOURCE,
    PUBLIC_PRIVATE_RELEASE_SECURITY_SOURCE,
    PUBLIC_CONTINUATION_SECURITY_SOURCE,
    PUBLIC_SAME_CONTROL_PROGRESS_SECURITY_SOURCE,
    PUBLIC_RELEASE_PROGRESS_SECURITY_SOURCE,
    PUBLIC_DISPATCHER_SECURITY_SOURCE,
    PUBLIC_CONTROLLER_SEGMENT_SECURITY_SOURCE,
    PUBLIC_PRIVATE_INVOCATION_SECURITY_SOURCE,
    PUBLIC_SYNTHETIC_RETURN_SECURITY_SOURCE,
    PUBLIC_BISIMULATION_SECURITY_SOURCE,
    RAW_CLAIM_SURFACE_SOURCE,
    HOST_PROFILE_KERNEL_SOURCE,
    HOST_PROFILE_PROOF_SOURCE,
    OCCURRENCE_WIRE_SOURCE,
    OCCURRENCE_WIRE_PROOF_SOURCE,
    OCCURRENCE_REGIONS_SOURCE,
    OCCURRENCE_REGION_CONSTRUCTION_SOURCE,
    OCCURRENCE_TRANSFER_SOURCE,
    OCCURRENCE_TRANSFER_CONSTRUCTION_SOURCE,
    DECODED_OCCURRENCE_SOURCE,
    ANCESTOR_INTERVALS_SOURCE,
    INTERVAL_ESCAPE_CHECKS_SOURCE,
    PRIORITY_OCCURRENCE_SOURCE,
    OCCURRENCE_INVOCATION_SOURCE,
    RANKED_DECODED_OCCURRENCE_SOURCE,
    V9_BOUNDARY_CONTRACTS_SOURCE,
    V9_OCCURRENCE_DATAFLOW_SOURCE,
    V9_OCCURRENCE_DATAFLOW_INVOCATION_SOURCE,
    OCCURRENCE_ACTIVATION_SOURCE,
    V9_OCCURRENCE_KERNEL_SOURCE,
    V9_OCCURRENCE_KERNEL_PROOF_SOURCE,
    V9_OCCURRENCE_DATAFLOW_INVOCATION_PROOF_SOURCE,
    V9_OCCURRENCE_DATAFLOW_PROOF_SOURCE,
    RANKED_DECODED_OCCURRENCE_PROOF_SOURCE,
    OCCURRENCE_INVOCATION_PROOF_SOURCE,
    DECODED_OCCURRENCE_PROOF_SOURCE,
    PRIORITY_OCCURRENCE_PROOF_SOURCE,
    OCCURRENCE_TRANSFER_CONSTRUCTION_PROOF_SOURCE,
    OCCURRENCE_TRANSFER_PROOF_SOURCE,
    OCCURRENCE_REGION_PROOF_SOURCE,
    INTERVAL_ESCAPE_PROOF_SOURCE,
    ANCESTOR_INTERVAL_PROOF_SOURCE,
    V9_BOUNDARY_CONTRACTS_PROOF_SOURCE,
    OCCURRENCE_REFERENCE_SOURCE,
    NATIVE_BRIDGE_BUILD_SOURCE,
    NATIVE_BRIDGE_C_SOURCE,
    NATIVE_BRIDGE_RUST_SOURCE,
];

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "json", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "json", serde(deny_unknown_fields))]
pub struct FormalSecurityReport {
    pub model_version: u32,
    pub lean_toolchain: String,
    pub checker_source_fingerprint: String,
    pub csir_fingerprint: String,
    pub checked_functions: u64,
    pub checked_nodes: u64,
    pub checked_capabilities: u64,
    pub checked_flows: u64,
    pub checked_releases: u64,
    pub checked_ct_operations: u64,
    /// Prevents safe code outside this module from manufacturing a report.
    /// Deserialized certificate claims receive the zero-sized default seal and
    /// are still untrusted until the runtime gate compares them to a freshly
    /// verified report.
    #[cfg_attr(feature = "json", serde(skip))]
    verified_seal: VerifiedSeal,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct VerifiedSeal;

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
enum Label {
    Public = 0,
    Internal = 1,
    Secret = 2,
    SecretCt = 3,
}

impl From<TaintLabel> for Label {
    fn from(value: TaintLabel) -> Self {
        match value {
            TaintLabel::Public => Self::Public,
            TaintLabel::Internal => Self::Internal,
            TaintLabel::Secret => Self::Secret,
            TaintLabel::SecretCT => Self::SecretCt,
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
enum Op {
    Flow = 0,
    Authority = 1,
    Declassify = 2,
    CtUse = 3,
    Boundary = 4,
    FixedCt = 5,
    Effect = 6,
    Consume = 7,
    TaintSeed = 8,
    TaintEdge = 9,
    TaintSink = 10,
    TaintCtUse = 11,
    TaintRelease = 12,
    CapOrigin = 13,
    CapRestrict = 14,
    CapSplit = 15,
    CapDraw = 16,
    CapSink = 17,
    CapRelease = 18,
    CapSlot = 19,
    CapSlotPut = 20,
    CapSlotTake = 21,
    CapMeet = 22,
    PathFork = 23,
    PathArm = 24,
    PathJoin = 25,
    PathLoop = 26,
    PathBack = 27,
    PathBreak = 28,
    PathLoopJoin = 29,
    IntCell = 30,
    DiffLe = 31,
    QuantityUse = 32,
    SemProgram = 33,
    SemFunction = 34,
    SemValue = 35,
    SemBlock = 36,
    SemInstruction = 37,
    SemOperand = 38,
    SemLabelContract = 39,
    SemCapabilityType = 40,
    SemPolicyClass = 41,
    SemRefinementFact = 42,
    SemRuntimeGuard = 43,
}

#[derive(Debug, Clone, Copy)]
#[repr(u32)]
#[allow(dead_code)] // State/release classes become live as policy derivation moves out of v6 records.
enum SemanticInstrOp {
    Scalar = 0,
    Aggregate = 1,
    Project = 2,
    Branch = 3,
    Jump = 4,
    Loop = 5,
    Call = 6,
    Closure = 7,
    ActorBoundary = 8,
    StateRead = 9,
    StateWrite = 10,
    SlotNew = 11,
    SlotPut = 12,
    SlotTake = 13,
    Effect = 14,
    Ffi = 15,
    Allocation = 16,
    Address = 17,
    CapMint = 18,
    CapRestrict = 19,
    CapSplit = 20,
    CapDraw = 21,
    CapExercise = 22,
    Release = 23,
    ReleaseCt = 24,
    CtEq = 25,
    CtSelect = 26,
    CtLt = 27,
    Output = 28,
    Trap = 29,
    Halt = 30,
    Range = 31,
    Dispatch = 32,
    Index = 33,
    DivRem = 34,
    StringCompare = 35,
    AbortiveEffect = 36,
}

#[derive(Debug, Clone, Copy)]
enum SemanticOperand {
    Value(VarId),
    Block(BlockId),
    Function(FuncId),
    Immediate(u64),
}

#[derive(Debug, Default, Clone, Copy)]
struct SemanticCounts {
    functions: u32,
    values: u32,
    blocks: u32,
    instructions: u32,
    operands: u32,
}

type ReachingDefinitions = BTreeMap<VarId, BTreeSet<VarId>>;

/// Security-only SSA reconstruction for the semantic CSIR suffix.
///
/// Runtime AIR deliberately keeps mutable locals because Wasm locals are mutable. Treating one
/// AIR `VarId` as one monotone taint cell, however, turns every strong update into a permanent
/// label increase and conflates definitions from dead or mutually-exclusive paths. The semantic
/// projection therefore gives parameters, assignments, and CFG join phis distinct value IDs. It
/// contains only def-use and predecessor information; labels are still derived exclusively by
/// Lean.
#[derive(Debug)]
struct SemanticSsaPlan {
    declarations: Vec<(VarId, VarId)>,
    initial_versions: BTreeMap<VarId, VarId>,
    fixed_versions: BTreeMap<VarId, VarId>,
    definition_versions: BTreeMap<(BlockId, u32), VarId>,
    block_entries: BTreeMap<BlockId, BTreeMap<VarId, VarId>>,
    phis: BTreeMap<BlockId, Vec<(VarId, VarId, Vec<VarId>)>>,
}

#[derive(Debug, Clone, Copy)]
struct SemanticTerminatorSecurity {
    declared_policy: Option<AirPolicyClass>,
    return_contract: AirLabelContract,
    abortive_transfer: bool,
    semantically_unreachable: bool,
}

struct SemanticProjectionContext<'a> {
    counts: &'a mut SemanticCounts,
    function_id: u32,
    block_id: u32,
    uses: &'a BTreeMap<VarId, VarId>,
    fixed_versions: &'a BTreeMap<VarId, VarId>,
}

fn semantic_successors(terminator: &AirTerminator) -> Vec<BlockId> {
    match terminator {
        AirTerminator::Return(_) | AirTerminator::Unreachable => Vec::new(),
        AirTerminator::Jump(target) => vec![*target],
        AirTerminator::Loop {
            body_block,
            exit_block,
            ..
        } => vec![*body_block, *exit_block],
        AirTerminator::Branch {
            then_block,
            else_block,
            ..
        } => vec![*then_block, *else_block],
        // `exit` is a structured post-dominator, not a direct runtime successor.
        AirTerminator::Dispatch { start, .. } => vec![*start],
    }
}

fn union_reaching_definitions(target: &mut ReachingDefinitions, source: &ReachingDefinitions) {
    for (variable, definitions) in source {
        target
            .entry(*variable)
            .or_default()
            .extend(definitions.iter().copied());
    }
}

fn build_semantic_ssa_plan(
    function: &crate::air::AirFunction,
    bases: &[VarId],
) -> Result<SemanticSsaPlan, String> {
    let mut next_value = 0_u32;
    let mut declarations = Vec::new();
    let mut initial_versions = BTreeMap::new();
    for base in bases {
        let version = VarId(next_value);
        next_value = next_value
            .checked_add(1)
            .ok_or("semantic SSA value identifier overflow")?;
        initial_versions.insert(*base, version);
        declarations.push((version, *base));
    }

    let mut blocks = function.blocks.iter().collect::<Vec<_>>();
    blocks.sort_by_key(|block| block.id.0);
    let known_blocks = blocks.iter().map(|block| block.id).collect::<BTreeSet<_>>();
    let mut definition_versions = BTreeMap::new();
    let mut definitions_by_base = BTreeMap::<VarId, Vec<VarId>>::new();
    let mut block_generators = BTreeMap::<BlockId, BTreeMap<VarId, VarId>>::new();
    for block in &blocks {
        let generators = block_generators.entry(block.id).or_default();
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            if let Some(base) = air_stmt_destination(statement) {
                if !initial_versions.contains_key(&base) {
                    return Err(format!(
                        "semantic block {} defines undeclared AIR value {}",
                        block.id.0, base.0
                    ));
                }
                let version = VarId(next_value);
                next_value = next_value
                    .checked_add(1)
                    .ok_or("semantic SSA value identifier overflow")?;
                let statement_index = u32::try_from(statement_index)
                    .map_err(|_| "semantic statement index exceeds u32")?;
                definition_versions.insert((block.id, statement_index), version);
                definitions_by_base.entry(base).or_default().push(version);
                generators.insert(base, version);
                declarations.push((version, base));
            }
        }
    }

    let parameter_bases = function
        .params
        .iter()
        .map(|(variable, _)| *variable)
        .collect::<BTreeSet<_>>();
    let tracked_bases = bases
        .iter()
        .copied()
        .filter(|base| {
            let definition_count = definitions_by_base.get(base).map_or(0, Vec::len);
            if parameter_bases.contains(base) {
                definition_count != 0
            } else {
                definition_count > 1
            }
        })
        .collect::<BTreeSet<_>>();
    let fixed_versions = bases
        .iter()
        .copied()
        .filter(|base| !tracked_bases.contains(base))
        .map(|base| {
            let version = definitions_by_base
                .get(&base)
                .and_then(|definitions| definitions.first())
                .copied()
                .unwrap_or(initial_versions[&base]);
            (base, version)
        })
        .collect::<BTreeMap<_, _>>();
    for generators in block_generators.values_mut() {
        generators.retain(|base, _| tracked_bases.contains(base));
    }

    let mut predecessors = blocks
        .iter()
        .map(|block| (block.id, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    for block in &blocks {
        if function
            .security
            .semantic_unreachable_blocks
            .contains(&block.id)
        {
            continue;
        }
        for successor in semantic_successors(&block.terminator) {
            if !known_blocks.contains(&successor) {
                return Err(format!(
                    "semantic block {} targets missing block {}",
                    block.id.0, successor.0
                ));
            }
            if !function
                .security
                .semantic_unreachable_blocks
                .contains(&successor)
            {
                predecessors.entry(successor).or_default().insert(block.id);
            }
        }
    }

    let initial_reaching = initial_versions
        .iter()
        .filter(|(base, _)| tracked_bases.contains(base))
        .map(|(base, version)| (*base, BTreeSet::from([*version])))
        .collect::<ReachingDefinitions>();
    let mut inputs = blocks
        .iter()
        .map(|block| (block.id, ReachingDefinitions::new()))
        .collect::<BTreeMap<_, _>>();
    let mut outputs = inputs.clone();
    let iteration_limit = blocks
        .len()
        .checked_mul(
            definition_versions
                .len()
                .saturating_add(bases.len())
                .saturating_add(1),
        )
        .and_then(|bound| bound.checked_add(1))
        .ok_or("semantic SSA convergence bound overflow")?;
    let mut converged = false;
    for _ in 0..iteration_limit {
        let mut changed = false;
        for block in &blocks {
            let mut input = ReachingDefinitions::new();
            if block.id == function.entry_block {
                union_reaching_definitions(&mut input, &initial_reaching);
            }
            for predecessor in predecessors.get(&block.id).into_iter().flatten() {
                if let Some(output) = outputs.get(predecessor) {
                    union_reaching_definitions(&mut input, output);
                }
            }
            let mut output = input.clone();
            if let Some(generators) = block_generators.get(&block.id) {
                for (base, version) in generators {
                    output.insert(*base, BTreeSet::from([*version]));
                }
            }
            changed |= inputs.get(&block.id) != Some(&input);
            changed |= outputs.get(&block.id) != Some(&output);
            inputs.insert(block.id, input);
            outputs.insert(block.id, output);
        }
        if !changed {
            converged = true;
            break;
        }
    }
    if !converged {
        return Err("semantic SSA reaching-definition analysis did not converge".to_owned());
    }

    let mut phi_ids = BTreeMap::<(BlockId, VarId), VarId>::new();
    for block in &blocks {
        let input = inputs.get(&block.id).cloned().unwrap_or_default();
        for base in &tracked_bases {
            let definitions = input
                .get(base)
                .cloned()
                .unwrap_or_else(|| BTreeSet::from([initial_versions[base]]));
            if definitions.len() > 1 {
                let phi = VarId(next_value);
                next_value = next_value
                    .checked_add(1)
                    .ok_or("semantic SSA value identifier overflow")?;
                phi_ids.insert((block.id, *base), phi);
                declarations.push((phi, *base));
            }
        }
    }

    let mut block_entries = BTreeMap::new();
    for block in &blocks {
        let input = inputs.get(&block.id).cloned().unwrap_or_default();
        let mut entry = BTreeMap::new();
        for base in &tracked_bases {
            let definitions = input
                .get(base)
                .cloned()
                .unwrap_or_else(|| BTreeSet::from([initial_versions[base]]));
            let version = phi_ids.get(&(block.id, *base)).copied().unwrap_or_else(|| {
                *definitions
                    .first()
                    .expect("one reaching definition when no phi was allocated")
            });
            entry.insert(*base, version);
        }
        block_entries.insert(block.id, entry);
    }

    let mut phis = BTreeMap::<BlockId, Vec<(VarId, VarId, Vec<VarId>)>>::new();
    for ((block, base), phi) in phi_ids {
        let mut sources = BTreeSet::new();
        if block == function.entry_block {
            sources.insert(initial_versions[&base]);
        }
        for predecessor in predecessors.get(&block).into_iter().flatten() {
            let source = block_generators
                .get(predecessor)
                .and_then(|generators| generators.get(&base))
                .copied()
                .or_else(|| {
                    block_entries
                        .get(predecessor)
                        .and_then(|entry| entry.get(&base))
                        .copied()
                })
                .unwrap_or(initial_versions[&base]);
            sources.insert(source);
        }
        if sources.is_empty() {
            sources.insert(initial_versions[&base]);
        }
        phis.entry(block)
            .or_default()
            .push((phi, base, sources.into_iter().collect()));
    }

    Ok(SemanticSsaPlan {
        declarations,
        initial_versions,
        fixed_versions,
        definition_versions,
        block_entries,
        phis,
    })
}

#[derive(Debug, Clone, Copy)]
struct Node {
    op: Op,
    label_a: Label,
    label_b: Label,
    flags: u8,
    origin: u32,
    actual: u32,
    required: u32,
    ceiling: u32,
    aux: u32,
    node_id: u32,
}

impl Node {
    fn ordinary(op: Op, aux: u32) -> Self {
        Self {
            op,
            label_a: Label::Public,
            label_b: Label::Public,
            flags: 1,
            origin: 0,
            actual: 0,
            required: 0,
            ceiling: u32::MAX,
            aux,
            node_id: 0,
        }
    }
}

#[derive(Default)]
struct Projector {
    nodes: Vec<Node>,
    pending_semantic_metadata: Vec<Node>,
    spans: BTreeMap<u32, Span>,
    functions: u64,
    occurrence_ffi: Vec<crate::formal_v9::FfiBinding>,
    occurrence_actors: Vec<crate::formal_v9::ActorBinding>,
}

#[derive(Clone)]
struct GraphEnv {
    bindings: BTreeMap<String, u32>,
    contracts: BTreeMap<String, Label>,
    pc: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CapCell {
    id: u32,
    kind: u32,
    ceiling: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SlotCell {
    id: u32,
    kind: u32,
    ceiling: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CapabilityValue {
    Cap(CapCell),
    Slot(SlotCell),
    Other,
}

#[derive(Clone, Default)]
struct CapabilityEnv {
    bindings: BTreeMap<String, CapabilityValue>,
    diverged: bool,
    loop_depth: usize,
}

impl GraphEnv {
    fn public() -> Self {
        Self {
            bindings: BTreeMap::new(),
            contracts: BTreeMap::new(),
            pc: 0,
        }
    }

    fn lookup(&self, name: &str) -> u32 {
        self.bindings.get(name).copied().unwrap_or(0)
    }
}

fn semantic_ref(id: u32, class: &str) -> Result<u32, String> {
    id.checked_add(1)
        .ok_or_else(|| format!("semantic {class} identifier overflow"))
}

fn semantic_len(len: usize, class: &str) -> Result<u32, String> {
    u32::try_from(len).map_err(|_| format!("semantic {class} count exceeds u32"))
}

fn air_type_code(ty: AirType) -> u32 {
    match ty {
        AirType::Unit => 0,
        AirType::Bool => 1,
        AirType::I32 => 2,
        AirType::U32 => 3,
        AirType::I64 => 4,
        AirType::U64 => 5,
        AirType::F64 => 6,
        AirType::Ptr => 7,
    }
}

fn air_value_kind_code(kind: &AirValueKind) -> u32 {
    match kind {
        AirValueKind::Copy => 0,
        AirValueKind::Linear => 1,
        AirValueKind::Cap(_) => 2,
        AirValueKind::StateCap(_) => 3,
        AirValueKind::Slot(_) => 4,
    }
}

fn air_capability_type_name(kind: &AirValueKind) -> Option<&str> {
    match kind {
        AirValueKind::Cap(name) | AirValueKind::StateCap(name) | AirValueKind::Slot(name) => {
            Some(name)
        }
        AirValueKind::Copy | AirValueKind::Linear => None,
    }
}

fn stable_name_word(name: &str) -> u32 {
    let digest = Sha256::digest(name.as_bytes());
    u32::from_le_bytes([digest[0], digest[1], digest[2], digest[3]])
}

fn air_function_kind_code(kind: &AirFunctionKind) -> u8 {
    match kind {
        AirFunctionKind::ModuleInit => 0,
        AirFunctionKind::ModuleFunction => 1,
        AirFunctionKind::ActorInit { .. } => 2,
        AirFunctionKind::ActorHandler { .. } => 3,
        AirFunctionKind::Closure => 4,
    }
}

fn air_policy_class_code(class: AirPolicyClass) -> u32 {
    match class {
        AirPolicyClass::Branch => 0,
        AirPolicyClass::Loop => 1,
        AirPolicyClass::Range => 2,
        AirPolicyClass::Dispatch => 3,
        AirPolicyClass::Index => 4,
        AirPolicyClass::Address => 5,
        AirPolicyClass::DivRem => 6,
        AirPolicyClass::Ffi => 7,
        AirPolicyClass::ActorBoundary => 8,
        AirPolicyClass::Allocation => 9,
        AirPolicyClass::CtSource => 10,
        AirPolicyClass::Release => 11,
        AirPolicyClass::ReleaseCt => 12,
        AirPolicyClass::StringCompare => 13,
        AirPolicyClass::FixedCt => 14,
        AirPolicyClass::Quantity => 15,
    }
}

fn air_policy_diagnostic(class: AirPolicyClass) -> u32 {
    match class {
        AirPolicyClass::Branch => 20,
        AirPolicyClass::Loop => 21,
        AirPolicyClass::Range => 22,
        AirPolicyClass::Dispatch => 23,
        AirPolicyClass::Index => 24,
        AirPolicyClass::Address => 25,
        AirPolicyClass::DivRem => 26,
        AirPolicyClass::Ffi | AirPolicyClass::Quantity => 27,
        AirPolicyClass::ActorBoundary => 28,
        AirPolicyClass::Allocation => 29,
        AirPolicyClass::CtSource => 30,
        AirPolicyClass::Release => 31,
        AirPolicyClass::ReleaseCt => 32,
        AirPolicyClass::StringCompare => 33,
        AirPolicyClass::FixedCt => 0,
    }
}

fn binary_op_code(op: BinaryOp) -> u64 {
    match op {
        BinaryOp::Add => 0,
        BinaryOp::Sub => 1,
        BinaryOp::Mul => 2,
        BinaryOp::Div => 3,
        BinaryOp::Mod => 4,
        BinaryOp::Shl => 5,
        BinaryOp::Shr => 6,
        BinaryOp::BitAnd => 7,
        BinaryOp::BitOr => 8,
        BinaryOp::LogicalAnd => 9,
        BinaryOp::LogicalOr => 10,
        BinaryOp::Lt => 11,
        BinaryOp::LtEq => 12,
        BinaryOp::Gt => 13,
        BinaryOp::GtEq => 14,
        BinaryOp::Eq => 15,
        BinaryOp::NotEq => 16,
    }
}

fn string_immediates(value: &str) -> Vec<SemanticOperand> {
    let bytes = value.as_bytes();
    let mut operands = Vec::with_capacity(2 + bytes.len().div_ceil(8));
    operands.push(SemanticOperand::Immediate(3));
    operands.push(SemanticOperand::Immediate(bytes.len() as u64));
    for chunk in bytes.chunks(8) {
        let mut word = [0_u8; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        operands.push(SemanticOperand::Immediate(u64::from_le_bytes(word)));
    }
    operands
}

fn air_stmt_destination(statement: &AirStmt) -> Option<VarId> {
    match statement {
        AirStmt::Assign { dst, .. }
        | AirStmt::LoadField { dst, .. }
        | AirStmt::StateRead { dst, .. }
        | AirStmt::SecurityRelease { dst, .. }
        | AirStmt::ResultTry { dst, .. }
        | AirStmt::OptionTry { dst, .. }
        | AirStmt::ArrayOrSliceContains { dst, .. }
        | AirStmt::StrBytesEq { dst, .. }
        | AirStmt::SliceOptionElem { dst, .. }
        | AirStmt::SpawnActor { dst, .. }
        | AirStmt::CapRestrict { dst, .. }
        | AirStmt::CapSplit { dst, .. }
        | AirStmt::CapDraw { dst, .. }
        | AirStmt::CapMint { dst, .. }
        | AirStmt::SlotNew { dst, .. }
        | AirStmt::PromoteBytes { dst, .. }
        | AirStmt::BumpAlloc { dst, .. }
        | AirStmt::IntrinsicAlloc { dst, .. }
        | AirStmt::IntrinsicLoad8 { dst, .. }
        | AirStmt::IntrinsicCtEq { dst, .. }
        | AirStmt::IntrinsicCtSelect { dst, .. }
        | AirStmt::IntrinsicCtLt { dst, .. }
        | AirStmt::LoadDynamic { dst, .. }
        | AirStmt::WrapI64 { dst, .. }
        | AirStmt::ExtendU32 { dst, .. }
        | AirStmt::SignExtendI32 { dst, .. }
        | AirStmt::Borrow { dst, .. }
        | AirStmt::SlotTake { dst_cap: dst, .. } => Some(*dst),
        AirStmt::RegionBegin { save_var: dst, .. } => Some(*dst),
        AirStmt::MessageAsk { dst, .. } => Some(*dst),
        AirStmt::Call { dst, .. }
        | AirStmt::CallIndirect { dst, .. }
        | AirStmt::ExternCall { dst, .. } => *dst,
        AirStmt::DeserializeMessage { dst, .. } => Some(*dst),
        _ => None,
    }
}

impl Projector {
    fn push(&mut self, mut node: Node) -> Result<u32, String> {
        if self.nodes.len() >= MAX_NODES {
            return Err(format!(
                "CSIR projection exceeds the {MAX_NODES}-node ceiling"
            ));
        }
        let node_id = u32::try_from(self.nodes.len() + 1)
            .map_err(|_| "CSIR node identifier overflow".to_string())?;
        node.node_id = node_id;
        self.nodes.push(node);
        Ok(node_id)
    }

    fn queue_semantic_metadata(&mut self, node: Node) {
        self.pending_semantic_metadata.push(node);
    }

    fn queue_policy(&mut self, owner: u32, class: AirPolicyClass, operand_mask: u32) {
        let mut node = Node::ordinary(Op::SemPolicyClass, air_policy_class_code(class));
        node.origin = owner;
        node.actual = operand_mask;
        node.required = air_policy_diagnostic(class);
        node.ceiling = 0;
        node.aux = air_policy_class_code(class);
        self.queue_semantic_metadata(node);
    }

    fn queue_policy_positions(
        &mut self,
        owner: u32,
        class: AirPolicyClass,
        positions: impl IntoIterator<Item = usize>,
    ) -> Result<(), String> {
        let mut windows = BTreeMap::<u32, u32>::new();
        for position in positions {
            let position = u32::try_from(position)
                .map_err(|_| "semantic policy operand position exceeds u32".to_owned())?;
            let base = position / 32 * 32;
            *windows.entry(base).or_default() |= 1_u32 << (position - base);
        }
        for (base, mask) in windows {
            let mut node = Node::ordinary(Op::SemPolicyClass, air_policy_class_code(class));
            node.origin = owner;
            node.actual = mask;
            node.required = air_policy_diagnostic(class);
            node.ceiling = base;
            node.aux = air_policy_class_code(class);
            self.queue_semantic_metadata(node);
        }
        Ok(())
    }

    fn queue_runtime_guard(&mut self, owner: u32, amount_position: u32) {
        let mut node = Node::ordinary(Op::SemRuntimeGuard, 0);
        node.flags = 0x03; // guest signed-negative guard and host balance check
        node.origin = owner;
        node.actual = amount_position;
        node.ceiling = 0;
        self.queue_semantic_metadata(node);
    }

    fn queue_exact_refinement(&mut self, function_id: u32, value: VarId, literal: i64) {
        let magnitude = literal.unsigned_abs();
        let mut node = Node::ordinary(Op::SemRefinementFact, 0);
        node.flags = if literal < 0 { 2 } else { 1 };
        node.origin = function_id;
        node.actual = value.0.saturating_add(1);
        node.required = magnitude as u32;
        node.ceiling = (magnitude >> 32) as u32;
        self.queue_semantic_metadata(node);
    }

    fn flush_semantic_metadata(&mut self) -> Result<(), String> {
        let mut pending = std::mem::take(&mut self.pending_semantic_metadata);
        pending.sort_by_key(|node| {
            (
                node.op as u8,
                node.origin,
                node.actual,
                node.ceiling,
                node.required,
                node.aux,
                node.flags,
            )
        });
        for node in pending {
            let owner_span = matches!(node.op, Op::SemPolicyClass | Op::SemRuntimeGuard)
                .then(|| self.spans.get(&node.origin).copied())
                .flatten();
            let node_id = self.push(node)?;
            if let Some(span) = owner_span {
                self.spans.insert(node_id, span);
            }
        }
        Ok(())
    }

    fn queue_statement_policy(&mut self, owner: u32, statement: &AirStmt) -> Result<(), String> {
        match statement {
            AirStmt::StoreField { .. } | AirStmt::LoadField { .. } => {
                // Record payload labels describe the data behind the pointer, not the identity of
                // the aggregate allocation.  A fixed field offset therefore has no data-dependent
                // address operand.  Keep the T025 class explicit with an empty selection window;
                // dynamic index/pointer operations below continue to select their address inputs.
                self.queue_policy(owner, AirPolicyClass::Address, 0);
            }
            AirStmt::StateRead { .. } | AirStmt::StateWrite { .. } => {}
            AirStmt::SecurityRelease { stage, .. } => match stage {
                AirReleaseStage::Ordinary => {
                    self.queue_policy(owner, AirPolicyClass::Release, 0b1);
                }
                AirReleaseStage::ConstantTime => {
                    self.queue_policy(owner, AirPolicyClass::ReleaseCt, 0b1);
                }
            },
            AirStmt::MessageSend { .. } => {
                self.queue_policy_positions(owner, AirPolicyClass::ActorBoundary, 0..4)?;
            }
            AirStmt::MessageAsk { .. } => {
                self.queue_policy_positions(owner, AirPolicyClass::ActorBoundary, 0..5)?;
            }
            AirStmt::SpawnActor { caps, .. } => {
                self.queue_policy_positions(
                    owner,
                    AirPolicyClass::ActorBoundary,
                    0..caps.len().saturating_add(1),
                )?;
            }
            AirStmt::SerializeMessage { args, .. } => {
                self.queue_policy_positions(
                    owner,
                    AirPolicyClass::ActorBoundary,
                    0..args.len().saturating_add(3),
                )?;
            }
            AirStmt::DeserializeMessage { .. } => {
                self.queue_policy_positions(owner, AirPolicyClass::ActorBoundary, 0..2)?;
            }
            AirStmt::ResultTry { .. } | AirStmt::OptionTry { .. } | AirStmt::TrapIf { .. } => {
                self.queue_policy(owner, AirPolicyClass::Branch, 0b1);
            }
            AirStmt::ArrayOrSliceContains { .. } => {
                self.queue_policy(owner, AirPolicyClass::Address, 0b11);
            }
            AirStmt::StrBytesEq { .. } => {
                self.queue_policy(owner, AirPolicyClass::StringCompare, 0b1_1111);
            }
            AirStmt::SliceOptionElem { .. } => {
                self.queue_policy(owner, AirPolicyClass::Address, 0b11);
            }
            AirStmt::CapSplit { .. } | AirStmt::CapDraw { .. } => {
                self.queue_policy(owner, AirPolicyClass::Quantity, 0b10);
                self.queue_runtime_guard(owner, 1);
            }
            AirStmt::PromoteBytes { .. } => {
                self.queue_policy(owner, AirPolicyClass::Allocation, 0b10);
            }
            AirStmt::IntrinsicAlloc { .. } => {
                self.queue_policy(owner, AirPolicyClass::Allocation, 0b1);
            }
            AirStmt::IntrinsicLoad8 { .. } | AirStmt::IntrinsicStore8 { .. } => {
                self.queue_policy(owner, AirPolicyClass::Address, 0b1);
            }
            AirStmt::IntrinsicCtEq { .. }
            | AirStmt::IntrinsicCtSelect { .. }
            | AirStmt::IntrinsicCtLt { .. } => {
                self.queue_policy(owner, AirPolicyClass::FixedCt, 0);
            }
            AirStmt::LoadDynamic { .. } | AirStmt::StoreDynamic { .. } => {
                self.queue_policy(owner, AirPolicyClass::Address, 0b1);
                self.queue_policy(owner, AirPolicyClass::Index, 0b10);
            }
            AirStmt::CallIndirect { .. } => {
                self.queue_policy(owner, AirPolicyClass::Address, 0b1);
            }
            AirStmt::ExternCall {
                extern_name, args, ..
            } => {
                let first = string_immediates(extern_name).len();
                if args.is_empty() {
                    // A zero-argument host call still has an FFI policy class even though it has
                    // no tainted value operands to select.  Keeping the zero mask makes the class
                    // explicit and lets Lean distinguish a safe empty input set from missing
                    // projection metadata.
                    self.queue_policy(owner, AirPolicyClass::Ffi, 0);
                } else {
                    self.queue_policy_positions(
                        owner,
                        AirPolicyClass::Ffi,
                        first..first.saturating_add(args.len()),
                    )?;
                }
            }
            AirStmt::RegionBegin { name, .. } => {
                let first = string_immediates(name).len();
                self.queue_policy_positions(owner, AirPolicyClass::Allocation, [first])?;
            }
            AirStmt::RegionEnd { name, .. } => {
                let first = string_immediates(name).len();
                self.queue_policy_positions(owner, AirPolicyClass::Allocation, [first])?;
            }
            AirStmt::Assign { .. }
            | AirStmt::Call { .. }
            | AirStmt::FuelDecrement { .. }
            | AirStmt::CapRestrict { .. }
            | AirStmt::CapMint { .. }
            | AirStmt::SlotNew { .. }
            | AirStmt::SlotPut { .. }
            | AirStmt::SlotTake { .. }
            | AirStmt::BumpAlloc { .. }
            | AirStmt::WrapI64 { .. }
            | AirStmt::ExtendU32 { .. }
            | AirStmt::SignExtendI32 { .. }
            | AirStmt::Borrow { .. }
            | AirStmt::GrantBegin { .. }
            | AirStmt::GrantEnd { .. } => {}
        }
        Ok(())
    }

    fn push_semantic_instruction(
        &mut self,
        counts: &mut SemanticCounts,
        function_id: u32,
        block_id: u32,
        op: SemanticInstrOp,
        destination: Option<VarId>,
        operands: Vec<SemanticOperand>,
    ) -> Result<u32, String> {
        let operand_count = semantic_len(operands.len(), "operand")?;
        let mut instruction = Node::ordinary(Op::SemInstruction, op as u32);
        instruction.origin = function_id;
        instruction.actual = block_id;
        instruction.required = match destination {
            Some(var) => semantic_ref(var.0, "value")?,
            None => 0,
        };
        instruction.ceiling = operand_count;
        instruction.aux = op as u32;
        let owner = self.push(instruction)?;
        counts.instructions = counts
            .instructions
            .checked_add(1)
            .ok_or("semantic instruction count overflow")?;

        for (position, operand) in operands.into_iter().enumerate() {
            let mut node = Node::ordinary(Op::SemOperand, 0);
            node.origin = owner;
            node.actual = semantic_len(position, "operand position")?;
            node.ceiling = 0;
            match operand {
                SemanticOperand::Value(var) => {
                    node.flags = 0;
                    node.required = semantic_ref(var.0, "value")?;
                }
                SemanticOperand::Block(block) => {
                    node.flags = 1;
                    node.required = semantic_ref(block.0, "block")?;
                }
                SemanticOperand::Function(function) => {
                    node.flags = 2;
                    node.required = semantic_ref(function.0, "function")?;
                }
                SemanticOperand::Immediate(value) => {
                    node.flags = 3;
                    node.required = value as u32;
                    node.ceiling = (value >> 32) as u32;
                }
            }
            self.push(node)?;
            counts.operands = counts
                .operands
                .checked_add(1)
                .ok_or("semantic operand count overflow")?;
        }
        Ok(owner)
    }

    fn project_semantic_value(
        &mut self,
        counts: &mut SemanticCounts,
        function_id: u32,
        var: VarId,
        ty: AirType,
        kind: &AirValueKind,
        cap_type_ids: &BTreeMap<String, u32>,
    ) -> Result<(), String> {
        let mut node = Node::ordinary(Op::SemValue, air_value_kind_code(kind));
        node.origin = function_id;
        node.actual = semantic_ref(var.0, "value")?;
        node.required = air_type_code(ty);
        node.ceiling = match air_capability_type_name(kind) {
            Some(name) => *cap_type_ids
                .get(name)
                .ok_or_else(|| format!("semantic capability type `{name}` is undeclared"))?,
            None => 0,
        };
        node.aux = air_value_kind_code(kind);
        self.push(node)?;
        counts.values = counts
            .values
            .checked_add(1)
            .ok_or("semantic value count overflow")?;
        Ok(())
    }

    fn queue_label_contract(
        &mut self,
        function_id: u32,
        subject: u32,
        role: u32,
        contract: AirLabelContract,
    ) {
        let (flags, label, flow_group) = match contract {
            AirLabelContract::Inferred => (0, Label::Public, 0),
            AirLabelContract::Concrete(label) => (1, Label::from(label), 0),
            AirLabelContract::Flow => (2, Label::Secret, 1),
        };
        let mut node = Node::ordinary(Op::SemLabelContract, role);
        node.flags = flags;
        node.label_a = label;
        node.label_b = label;
        node.origin = function_id;
        node.actual = subject;
        node.required = role;
        node.ceiling = flow_group;
        node.aux = role;
        self.queue_semantic_metadata(node);
    }

    fn rename_semantic_operands(
        operands: Vec<SemanticOperand>,
        uses: &BTreeMap<VarId, VarId>,
        fixed_versions: &BTreeMap<VarId, VarId>,
    ) -> Result<Vec<SemanticOperand>, String> {
        operands
            .into_iter()
            .map(|operand| match operand {
                SemanticOperand::Value(base) => uses
                    .get(&base)
                    .or_else(|| fixed_versions.get(&base))
                    .copied()
                    .map(SemanticOperand::Value)
                    .ok_or_else(|| {
                        format!(
                            "semantic instruction reads AIR value {} without a reaching definition",
                            base.0
                        )
                    }),
                other => Ok(other),
            })
            .collect()
    }

    fn project_semantic_air_value(
        &mut self,
        context: &mut SemanticProjectionContext<'_>,
        dst: VarId,
        value: &AirValue,
    ) -> Result<u32, String> {
        let (op, operands) = match value {
            AirValue::IntLit(value) => (
                SemanticInstrOp::Scalar,
                vec![
                    SemanticOperand::Immediate(0),
                    SemanticOperand::Immediate(*value as u64),
                ],
            ),
            AirValue::FloatLit(value) => (
                SemanticInstrOp::Scalar,
                vec![
                    SemanticOperand::Immediate(1),
                    SemanticOperand::Immediate(value.to_bits()),
                ],
            ),
            AirValue::BoolLit(value) => (
                SemanticInstrOp::Scalar,
                vec![
                    SemanticOperand::Immediate(2),
                    SemanticOperand::Immediate(u64::from(u8::from(*value))),
                ],
            ),
            AirValue::StrLit(value) => (SemanticInstrOp::Scalar, string_immediates(value)),
            AirValue::UnitLit => (SemanticInstrOp::Scalar, vec![SemanticOperand::Immediate(4)]),
            AirValue::Var(var) => (SemanticInstrOp::Project, vec![SemanticOperand::Value(*var)]),
            AirValue::Binary { lhs, op, rhs } => (
                if matches!(op, BinaryOp::Div | BinaryOp::Mod) {
                    SemanticInstrOp::DivRem
                } else {
                    SemanticInstrOp::Scalar
                },
                vec![
                    SemanticOperand::Value(*lhs),
                    SemanticOperand::Value(*rhs),
                    SemanticOperand::Immediate(5),
                    SemanticOperand::Immediate(binary_op_code(*op)),
                ],
            ),
            AirValue::RecordConstruct { fields } => (
                SemanticInstrOp::Aggregate,
                fields
                    .iter()
                    .map(|(_, var)| SemanticOperand::Value(*var))
                    .collect(),
            ),
        };
        let operands =
            Self::rename_semantic_operands(operands, context.uses, context.fixed_versions)?;
        let owner = self.push_semantic_instruction(
            context.counts,
            context.function_id,
            context.block_id,
            op,
            Some(dst),
            operands,
        )?;
        if let AirValue::Binary {
            op: BinaryOp::Div | BinaryOp::Mod,
            ..
        } = value
        {
            self.queue_policy(owner, AirPolicyClass::DivRem, 0b11);
        }
        if let AirValue::IntLit(literal) = value {
            self.queue_exact_refinement(context.function_id, dst, *literal);
        }
        Ok(owner)
    }

    fn project_semantic_stmt(
        &mut self,
        context: &mut SemanticProjectionContext<'_>,
        security: &crate::air::AirSecurityMetadata,
        statement: &AirStmt,
        semantic_destination: Option<VarId>,
    ) -> Result<u32, String> {
        let (op, destination, operands) = match statement {
            AirStmt::Assign { dst, val } => {
                let destination = semantic_destination.ok_or_else(|| {
                    format!(
                        "semantic assignment to AIR value {} has no SSA definition",
                        dst.0
                    )
                })?;
                let owner = self.project_semantic_air_value(context, destination, val)?;
                if matches!(
                    security.value_contracts.get(dst),
                    Some(AirLabelContract::Concrete(TaintLabel::SecretCT))
                ) {
                    let positions = match val {
                        AirValue::Var(_) => 0..1,
                        AirValue::Binary { .. } => 0..2,
                        AirValue::RecordConstruct { fields } => 0..fields.len(),
                        AirValue::IntLit(_)
                        | AirValue::FloatLit(_)
                        | AirValue::BoolLit(_)
                        | AirValue::StrLit(_)
                        | AirValue::UnitLit => 0..0,
                    };
                    self.queue_policy_positions(owner, AirPolicyClass::CtSource, positions)?;
                }
                return Ok(owner);
            }
            AirStmt::StoreField {
                base_ptr,
                offset,
                val,
                ty,
            } => (
                SemanticInstrOp::Address,
                None,
                vec![
                    SemanticOperand::Value(*base_ptr),
                    SemanticOperand::Value(*val),
                    SemanticOperand::Immediate(u64::from(*offset)),
                    SemanticOperand::Immediate(u64::from(air_type_code(*ty))),
                ],
            ),
            AirStmt::LoadField {
                dst,
                base_ptr,
                offset,
                ty,
            } => (
                SemanticInstrOp::Address,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*base_ptr),
                    SemanticOperand::Immediate(u64::from(*offset)),
                    SemanticOperand::Immediate(u64::from(air_type_code(*ty))),
                ],
            ),
            AirStmt::StateRead {
                dst,
                state_ptr,
                offset,
                ty,
                label,
            } => (
                SemanticInstrOp::StateRead,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*state_ptr),
                    SemanticOperand::Immediate(u64::from(*offset)),
                    SemanticOperand::Immediate(u64::from(air_type_code(*ty))),
                    SemanticOperand::Immediate(u64::from(Label::from(*label) as u8)),
                ],
            ),
            AirStmt::StateWrite {
                state_ptr,
                offset,
                val,
                ty,
                label,
            } => (
                SemanticInstrOp::StateWrite,
                None,
                vec![
                    SemanticOperand::Value(*state_ptr),
                    SemanticOperand::Value(*val),
                    SemanticOperand::Immediate(u64::from(*offset)),
                    SemanticOperand::Immediate(u64::from(air_type_code(*ty))),
                    SemanticOperand::Immediate(u64::from(Label::from(*label) as u8)),
                ],
            ),
            AirStmt::SecurityRelease {
                dst,
                src,
                cap,
                cap_scratch: _,
                stage,
            } => (
                match stage {
                    AirReleaseStage::Ordinary => SemanticInstrOp::Release,
                    AirReleaseStage::ConstantTime => SemanticInstrOp::ReleaseCt,
                },
                Some(*dst),
                vec![SemanticOperand::Value(*src), SemanticOperand::Value(*cap)],
            ),
            AirStmt::Call { dst, func, args } => {
                let mut operands = Vec::with_capacity(args.len() + 1);
                operands.push(SemanticOperand::Function(*func));
                operands.extend(args.iter().copied().map(SemanticOperand::Value));
                (SemanticInstrOp::Call, *dst, operands)
            }
            AirStmt::FuelDecrement { amount } => (
                SemanticInstrOp::Effect,
                None,
                vec![SemanticOperand::Immediate(u64::from(*amount))],
            ),
            AirStmt::MessageSend {
                target,
                msg,
                actor_type,
                handler,
                payload_buf,
                payload_len,
            } => (
                SemanticInstrOp::ActorBoundary,
                None,
                vec![
                    SemanticOperand::Value(*target),
                    SemanticOperand::Value(*msg),
                    SemanticOperand::Value(*payload_buf),
                    SemanticOperand::Value(*payload_len),
                    SemanticOperand::Immediate(u64::from(actor_type.0)),
                    SemanticOperand::Immediate(u64::from(handler.0)),
                ],
            ),
            AirStmt::MessageAsk {
                dst,
                target,
                msg,
                actor_type,
                handler,
                payload_buf,
                payload_len,
                timeout,
            } => (
                SemanticInstrOp::ActorBoundary,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*target),
                    SemanticOperand::Value(*msg),
                    SemanticOperand::Value(*payload_buf),
                    SemanticOperand::Value(*payload_len),
                    SemanticOperand::Value(*timeout),
                    SemanticOperand::Immediate(u64::from(actor_type.0)),
                    SemanticOperand::Immediate(u64::from(handler.0)),
                ],
            ),
            AirStmt::ResultTry { dst, src } | AirStmt::OptionTry { dst, src } => (
                SemanticInstrOp::Project,
                Some(*dst),
                vec![SemanticOperand::Value(*src)],
            ),
            AirStmt::ArrayOrSliceContains {
                dst,
                base_ptr,
                len,
                needle,
                idx,
                elem,
            } => (
                SemanticInstrOp::Address,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*base_ptr),
                    SemanticOperand::Value(*len),
                    SemanticOperand::Value(*needle),
                    SemanticOperand::Value(*idx),
                    SemanticOperand::Immediate(u64::from(air_type_code(*elem))),
                ],
            ),
            AirStmt::StrBytesEq {
                dst,
                lhs_data,
                lhs_len,
                rhs_data,
                rhs_len,
                idx,
            } => (
                SemanticInstrOp::StringCompare,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*lhs_data),
                    SemanticOperand::Value(*lhs_len),
                    SemanticOperand::Value(*rhs_data),
                    SemanticOperand::Value(*rhs_len),
                    SemanticOperand::Value(*idx),
                ],
            ),
            AirStmt::SliceOptionElem {
                dst,
                data_ptr,
                len,
                is_last,
                elem,
            } => (
                SemanticInstrOp::Address,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*data_ptr),
                    SemanticOperand::Value(*len),
                    SemanticOperand::Immediate(u64::from(u8::from(*is_last))),
                    SemanticOperand::Immediate(u64::from(air_type_code(*elem))),
                ],
            ),
            AirStmt::SpawnActor {
                dst,
                actor_type,
                caps,
                fuel_cap,
                supervision,
            } => {
                let mut operands = Vec::with_capacity(caps.len() + 3);
                operands.push(SemanticOperand::Value(*fuel_cap));
                operands.extend(caps.iter().copied().map(SemanticOperand::Value));
                operands.push(SemanticOperand::Immediate(u64::from(actor_type.0)));
                match supervision {
                    crate::air::AirSupervisionStrategy::Stop => {
                        operands.push(SemanticOperand::Immediate(0));
                    }
                    crate::air::AirSupervisionStrategy::Restart { max_restarts } => {
                        operands.push(SemanticOperand::Immediate(1));
                        operands.push(SemanticOperand::Immediate(u64::from(*max_restarts)));
                    }
                }
                (SemanticInstrOp::ActorBoundary, Some(*dst), operands)
            }
            AirStmt::CapRestrict {
                dst,
                src,
                restriction_mask,
            } => (
                SemanticInstrOp::CapRestrict,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*src),
                    SemanticOperand::Immediate(u64::from(*restriction_mask)),
                ],
            ),
            AirStmt::CapSplit { dst, src, amount } => (
                SemanticInstrOp::CapSplit,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*src),
                    SemanticOperand::Value(*amount),
                ],
            ),
            AirStmt::CapDraw { dst, src, amount } => (
                SemanticInstrOp::CapDraw,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*src),
                    SemanticOperand::Value(*amount),
                ],
            ),
            AirStmt::CapMint {
                dst,
                cap_name,
                params,
                target,
            } => {
                let mut operands = string_immediates(cap_name);
                operands.push(SemanticOperand::Value(*target));
                operands.extend(
                    params
                        .iter()
                        .map(|value| SemanticOperand::Immediate(*value as u64)),
                );
                (SemanticInstrOp::CapMint, Some(*dst), operands)
            }
            AirStmt::SlotNew { dst, cap_type } => (
                SemanticInstrOp::SlotNew,
                Some(*dst),
                string_immediates(cap_type),
            ),
            AirStmt::SlotPut { slot, cap } => (
                SemanticInstrOp::SlotPut,
                None,
                vec![SemanticOperand::Value(*slot), SemanticOperand::Value(*cap)],
            ),
            AirStmt::SlotTake { dst_cap, slot } => (
                SemanticInstrOp::SlotTake,
                Some(*dst_cap),
                vec![SemanticOperand::Value(*slot)],
            ),
            AirStmt::SerializeMessage {
                msg,
                args,
                dst_buf,
                dst_len,
            } => {
                let mut operands = Vec::with_capacity(args.len() + 3);
                operands.push(SemanticOperand::Value(*msg));
                operands.extend(args.iter().copied().map(SemanticOperand::Value));
                operands.push(SemanticOperand::Value(*dst_buf));
                operands.push(SemanticOperand::Value(*dst_len));
                (SemanticInstrOp::ActorBoundary, None, operands)
            }
            AirStmt::DeserializeMessage {
                src_buf,
                src_len,
                dst,
            } => (
                SemanticInstrOp::ActorBoundary,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*src_buf),
                    SemanticOperand::Value(*src_len),
                ],
            ),
            AirStmt::PromoteBytes { dst, src, len } => (
                SemanticInstrOp::Allocation,
                Some(*dst),
                vec![SemanticOperand::Value(*src), SemanticOperand::Value(*len)],
            ),
            AirStmt::BumpAlloc {
                dst,
                size_bytes,
                align,
                persistent,
            } => (
                SemanticInstrOp::Allocation,
                Some(*dst),
                vec![
                    SemanticOperand::Immediate(u64::from(*size_bytes)),
                    SemanticOperand::Immediate(u64::from(*align)),
                    SemanticOperand::Immediate(u64::from(u8::from(*persistent))),
                ],
            ),
            AirStmt::IntrinsicAlloc {
                dst,
                size,
                persistent,
            } => (
                SemanticInstrOp::Allocation,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*size),
                    SemanticOperand::Immediate(u64::from(u8::from(*persistent))),
                ],
            ),
            AirStmt::IntrinsicLoad8 { dst, ptr } => (
                SemanticInstrOp::Address,
                Some(*dst),
                vec![SemanticOperand::Value(*ptr)],
            ),
            AirStmt::IntrinsicStore8 { ptr, val } => (
                SemanticInstrOp::Address,
                None,
                vec![SemanticOperand::Value(*ptr), SemanticOperand::Value(*val)],
            ),
            AirStmt::IntrinsicCtEq { dst, lhs, rhs } => (
                SemanticInstrOp::CtEq,
                Some(*dst),
                vec![SemanticOperand::Value(*lhs), SemanticOperand::Value(*rhs)],
            ),
            AirStmt::IntrinsicCtSelect {
                dst,
                cond,
                then_val,
                else_val,
            } => (
                SemanticInstrOp::CtSelect,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*cond),
                    SemanticOperand::Value(*then_val),
                    SemanticOperand::Value(*else_val),
                ],
            ),
            AirStmt::IntrinsicCtLt { dst, lhs, rhs } => (
                SemanticInstrOp::CtLt,
                Some(*dst),
                vec![SemanticOperand::Value(*lhs), SemanticOperand::Value(*rhs)],
            ),
            AirStmt::LoadDynamic {
                dst,
                base_ptr,
                index,
                elem_size,
                ty,
                offset,
            } => (
                SemanticInstrOp::Index,
                Some(*dst),
                vec![
                    SemanticOperand::Value(*base_ptr),
                    SemanticOperand::Value(*index),
                    SemanticOperand::Immediate(u64::from(*elem_size)),
                    SemanticOperand::Immediate(u64::from(air_type_code(*ty))),
                    SemanticOperand::Immediate(u64::from(*offset)),
                ],
            ),
            AirStmt::StoreDynamic {
                base_ptr,
                index,
                elem_size,
                val,
                ty,
                offset,
            } => (
                SemanticInstrOp::Index,
                None,
                vec![
                    SemanticOperand::Value(*base_ptr),
                    SemanticOperand::Value(*index),
                    SemanticOperand::Value(*val),
                    SemanticOperand::Immediate(u64::from(*elem_size)),
                    SemanticOperand::Immediate(u64::from(air_type_code(*ty))),
                    SemanticOperand::Immediate(u64::from(*offset)),
                ],
            ),
            AirStmt::TrapIf { cond } => (
                SemanticInstrOp::Trap,
                None,
                vec![SemanticOperand::Value(*cond)],
            ),
            AirStmt::WrapI64 { dst, src }
            | AirStmt::ExtendU32 { dst, src }
            | AirStmt::SignExtendI32 { dst, src }
            | AirStmt::Borrow { dst, src, .. } => (
                SemanticInstrOp::Project,
                Some(*dst),
                vec![SemanticOperand::Value(*src)],
            ),
            AirStmt::CallIndirect {
                dst,
                table_index,
                args,
                ..
            } => {
                let mut operands = Vec::with_capacity(args.len() + 1);
                operands.push(SemanticOperand::Value(*table_index));
                operands.extend(args.iter().copied().map(SemanticOperand::Value));
                (SemanticInstrOp::Closure, *dst, operands)
            }
            AirStmt::GrantBegin { grant_id, cap_var } => (
                SemanticInstrOp::CapExercise,
                None,
                vec![
                    SemanticOperand::Value(*cap_var),
                    SemanticOperand::Immediate(u64::from(*grant_id)),
                ],
            ),
            AirStmt::GrantEnd { grant_id } => (
                SemanticInstrOp::Effect,
                None,
                vec![SemanticOperand::Immediate(u64::from(*grant_id))],
            ),
            AirStmt::ExternCall {
                dst,
                extern_name,
                args,
            } => {
                let mut operands = string_immediates(extern_name);
                operands.extend(args.iter().copied().map(SemanticOperand::Value));
                (SemanticInstrOp::Ffi, *dst, operands)
            }
            AirStmt::RegionBegin {
                name,
                limit_var,
                save_var,
            } => {
                let mut operands = string_immediates(name);
                operands.push(SemanticOperand::Value(*limit_var));
                (SemanticInstrOp::Allocation, Some(*save_var), operands)
            }
            AirStmt::RegionEnd {
                name,
                limit_var,
                save_var,
            } => {
                let mut operands = string_immediates(name);
                operands.push(SemanticOperand::Value(*limit_var));
                operands.push(SemanticOperand::Value(*save_var));
                (SemanticInstrOp::Allocation, None, operands)
            }
        };
        let destination = match destination {
            Some(base) => Some(semantic_destination.ok_or_else(|| {
                format!(
                    "semantic definition of AIR value {} has no SSA version",
                    base.0
                )
            })?),
            None => {
                if semantic_destination.is_some() {
                    return Err(
                        "semantic SSA plan assigns a destination to a destination-free instruction"
                            .to_owned(),
                    );
                }
                None
            }
        };
        let operands =
            Self::rename_semantic_operands(operands, context.uses, context.fixed_versions)?;
        let owner = self.push_semantic_instruction(
            context.counts,
            context.function_id,
            context.block_id,
            op,
            destination,
            operands,
        )?;
        self.queue_statement_policy(owner, statement)?;
        // Preserve declared instruction identity for the separate v9 envelope.
        // These records are not part of v8 bytes or its acceptance judgment.
        if let AirStmt::ExternCall {
            extern_name, args, ..
        } = statement
        {
            self.occurrence_ffi.push(crate::formal_v9::FfiBinding {
                owner,
                profile_operation: 0,
                first_argument: semantic_len(string_immediates(extern_name).len(), "FFI prefix")?,
                parameter_count: semantic_len(args.len(), "FFI parameter")?,
                result_count: u32::from(destination.is_some()),
            });
        }
        if let Some(operation) = statement.actor_operation() {
            self.occurrence_actors.push(crate::formal_v9::ActorBinding {
                owner,
                subtype: operation as u32,
            });
        }
        let ct_result = match statement {
            AirStmt::StateRead { dst, .. } => Some(*dst),
            AirStmt::Call { dst, .. } => *dst,
            _ => None,
        };
        if ct_result.is_some_and(|dst| {
            matches!(
                security.value_contracts.get(&dst),
                Some(AirLabelContract::Concrete(TaintLabel::SecretCT))
            )
        }) {
            // The Lean checker derives the source label from the state contract or callee return
            // contract.  The zero operand mask is intentional: Rust supplies no computed verdict.
            self.queue_policy(owner, AirPolicyClass::CtSource, 0);
        }
        Ok(owner)
    }

    fn project_semantic_terminator(
        &mut self,
        context: &mut SemanticProjectionContext<'_>,
        terminator: &AirTerminator,
        security: SemanticTerminatorSecurity,
    ) -> Result<u32, String> {
        let SemanticTerminatorSecurity {
            declared_policy,
            return_contract,
            abortive_transfer,
            semantically_unreachable,
        } = security;
        let (op, operands) = if semantically_unreachable {
            // This is an impossible source edge, not successful program termination.  Encoding
            // it as `halt` made the raw relational machine treat a projection invariant failure
            // as an ordinary successful run.  A zero-operand trap is failure-atomic and keeps
            // successful-halt premises honest.
            (SemanticInstrOp::Trap, Vec::new())
        } else {
            match terminator {
                AirTerminator::Return(value) => (
                    if abortive_transfer {
                        SemanticInstrOp::AbortiveEffect
                    } else {
                        SemanticInstrOp::Output
                    },
                    value.iter().copied().map(SemanticOperand::Value).collect(),
                ),
                AirTerminator::Jump(target) => {
                    (SemanticInstrOp::Jump, vec![SemanticOperand::Block(*target)])
                }
                AirTerminator::Loop {
                    cond,
                    body_block,
                    exit_block,
                } => (
                    if matches!(declared_policy, Some(AirPolicyClass::Range)) {
                        SemanticInstrOp::Range
                    } else {
                        SemanticInstrOp::Loop
                    },
                    vec![
                        SemanticOperand::Value(*cond),
                        SemanticOperand::Block(*body_block),
                        SemanticOperand::Block(*exit_block),
                    ],
                ),
                AirTerminator::Branch {
                    cond,
                    then_block,
                    else_block,
                    merge_block,
                } => {
                    let mut operands = vec![
                        SemanticOperand::Value(*cond),
                        SemanticOperand::Block(*then_block),
                        SemanticOperand::Block(*else_block),
                    ];
                    operands.extend(merge_block.iter().copied().map(SemanticOperand::Block));
                    (
                        if matches!(declared_policy, Some(AirPolicyClass::Dispatch)) {
                            SemanticInstrOp::Dispatch
                        } else {
                            SemanticInstrOp::Branch
                        },
                        operands,
                    )
                }
                AirTerminator::Dispatch { start, exit } => (
                    SemanticInstrOp::Dispatch,
                    vec![
                        SemanticOperand::Block(*start),
                        SemanticOperand::Block(*exit),
                    ],
                ),
                AirTerminator::Unreachable => (SemanticInstrOp::Trap, Vec::new()),
            }
        };
        let operands =
            Self::rename_semantic_operands(operands, context.uses, context.fixed_versions)?;
        let owner = self.push_semantic_instruction(
            context.counts,
            context.function_id,
            context.block_id,
            op,
            None,
            operands,
        )?;
        if !abortive_transfer
            && matches!(
                (terminator, return_contract),
                (
                    AirTerminator::Return(Some(_)),
                    AirLabelContract::Concrete(TaintLabel::SecretCT)
                )
            )
        {
            self.queue_policy(owner, AirPolicyClass::CtSource, 0b1);
        }
        match declared_policy {
            Some(AirPolicyClass::Branch) if matches!(terminator, AirTerminator::Branch { .. }) => {
                self.queue_policy(owner, AirPolicyClass::Branch, 0b1);
            }
            Some(AirPolicyClass::Loop) if matches!(terminator, AirTerminator::Loop { .. }) => {
                self.queue_policy(owner, AirPolicyClass::Loop, 0b1);
            }
            Some(AirPolicyClass::Range) if matches!(terminator, AirTerminator::Loop { .. }) => {
                self.queue_policy(owner, AirPolicyClass::Range, 0b1);
            }
            Some(AirPolicyClass::Dispatch)
                if matches!(
                    terminator,
                    AirTerminator::Branch { .. } | AirTerminator::Dispatch { .. }
                ) =>
            {
                let mask = u32::from(matches!(terminator, AirTerminator::Branch { .. }));
                self.queue_policy(owner, AirPolicyClass::Dispatch, mask);
            }
            Some(_) => {
                return Err(format!(
                    "semantic block {} carries a non-control policy class",
                    context.block_id
                ));
            }
            None if matches!(
                terminator,
                AirTerminator::Branch { .. }
                    | AirTerminator::Loop { .. }
                    | AirTerminator::Dispatch { .. }
            ) =>
            {
                return Err(format!(
                    "semantic block {} is missing its control-policy classification",
                    context.block_id
                ));
            }
            None => {}
        }
        Ok(owner)
    }

    fn project_semantic_program(
        &mut self,
        program: &AirProgram,
        authority_registry: &AuthorityRegistry,
    ) -> Result<(), String> {
        let cap_names = program
            .functions
            .iter()
            .flat_map(|function| function.value_kinds.values())
            .filter_map(air_capability_type_name)
            .map(str::to_owned)
            .collect::<BTreeSet<_>>();
        let cap_type_ids = cap_names
            .iter()
            .enumerate()
            .map(|(index, name)| {
                u32::try_from(index + 1)
                    .map(|id| (name.clone(), id))
                    .map_err(|_| "semantic capability type count exceeds u32".to_owned())
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        for (name, type_id) in &cap_type_ids {
            let mut declaration = Node::ordinary(Op::SemCapabilityType, cap_kind_for_name(name));
            declaration.actual = *type_id;
            declaration.required = stable_name_word(name);
            declaration.ceiling = authority_registry.full_mask(name);
            declaration.aux = cap_kind_for_name(name);
            self.queue_semantic_metadata(declaration);
        }

        let manifest_index = self.nodes.len();
        let mut manifest = Node::ordinary(Op::SemProgram, 0);
        manifest.ceiling = 0;
        self.push(manifest)?;
        let mut counts = SemanticCounts::default();

        for (function_index, function) in program.functions.iter().enumerate() {
            let function_id = semantic_ref(
                u32::try_from(function_index)
                    .map_err(|_| "semantic function identifier exceeds u32")?,
                "function",
            )?;
            counts.functions = counts
                .functions
                .checked_add(1)
                .ok_or("semantic function count overflow")?;

            let mut base_declarations = BTreeMap::<VarId, (AirType, AirValueKind)>::new();
            let mut declared = BTreeSet::new();
            for (var, ty) in function.params.iter().chain(function.locals.iter()) {
                if !declared.insert(*var) {
                    return Err(format!(
                        "semantic function {function_id} declares value {} twice",
                        var.0
                    ));
                }
                let kind = function.value_kinds.get(var).ok_or_else(|| {
                    format!(
                        "semantic function {function_id} has no value-kind declaration for {}",
                        var.0
                    )
                })?;
                base_declarations.insert(*var, (*ty, kind.clone()));
            }
            let base_ids = base_declarations.keys().copied().collect::<Vec<_>>();
            let ssa = build_semantic_ssa_plan(function, &base_ids)?;

            let ring_code = u32::from(u8::from(matches!(function.ring, crate::ast::Ring::Outer)));
            let mut function_node = Node::ordinary(Op::SemFunction, ring_code);
            function_node.flags = air_function_kind_code(&function.kind);
            function_node.origin = function_id;
            function_node.actual = semantic_ref(function.entry_block.0, "entry block")?;
            function_node.required = semantic_len(function.blocks.len(), "block")?;
            function_node.ceiling = semantic_len(ssa.declarations.len(), "value")?;
            function_node.aux = ring_code;
            self.push(function_node)?;

            let parameter_ids = function
                .params
                .iter()
                .map(|(var, _)| *var)
                .collect::<BTreeSet<_>>();
            for (var, base) in &ssa.declarations {
                let (ty, kind) = base_declarations.get(base).ok_or_else(|| {
                    format!(
                        "semantic SSA value {} refers to undeclared AIR value {}",
                        var.0, base.0
                    )
                })?;
                self.project_semantic_value(
                    &mut counts,
                    function_id,
                    *var,
                    *ty,
                    kind,
                    &cap_type_ids,
                )?;
                let contract = function
                    .security
                    .value_contracts
                    .get(base)
                    .copied()
                    .ok_or_else(|| {
                        format!(
                            "semantic function {function_id} has no declarative label contract for AIR value {}",
                            base.0
                        )
                    })?;
                let role = if parameter_ids.contains(base)
                    && ssa.initial_versions.get(base) == Some(var)
                {
                    0
                } else {
                    1
                };
                self.queue_label_contract(
                    function_id,
                    semantic_ref(var.0, "value")?,
                    role,
                    contract,
                );
            }
            self.queue_label_contract(function_id, 0, 2, function.security.return_contract);
            for (offset, label) in &function.security.state_contracts {
                self.queue_label_contract(
                    function_id,
                    *offset,
                    3,
                    AirLabelContract::Concrete(*label),
                );
            }

            let mut blocks = function.blocks.iter().collect::<Vec<_>>();
            blocks.sort_by_key(|block| block.id.0);
            for block in blocks {
                let block_id = semantic_ref(block.id.0, "block")?;
                let phis = ssa.phis.get(&block.id).cloned().unwrap_or_default();
                let mut block_node = Node::ordinary(Op::SemBlock, 0);
                block_node.origin = function_id;
                block_node.actual = block_id;
                block_node.required = semantic_len(
                    phis.len()
                        .saturating_add(block.stmts.len())
                        .saturating_add(1),
                    "block instruction",
                )?;
                block_node.ceiling = 0;
                self.push(block_node)?;
                counts.blocks = counts
                    .blocks
                    .checked_add(1)
                    .ok_or("semantic block count overflow")?;
                let mut uses = ssa.block_entries.get(&block.id).cloned().ok_or_else(|| {
                    format!("semantic block {} has no SSA entry environment", block.id.0)
                })?;
                for (phi, base, sources) in phis {
                    let operands = sources.into_iter().map(SemanticOperand::Value).collect();
                    let owner = self.push_semantic_instruction(
                        &mut counts,
                        function_id,
                        block_id,
                        SemanticInstrOp::Project,
                        Some(phi),
                        operands,
                    )?;
                    self.spans.insert(owner, function.def_span);
                    uses.insert(base, phi);
                }
                for (statement_index, statement) in block.stmts.iter().enumerate() {
                    let statement_index_u32 = u32::try_from(statement_index)
                        .map_err(|_| "semantic statement index exceeds u32")?;
                    let base_destination = air_stmt_destination(statement);
                    let semantic_destination = match base_destination {
                        Some(_) => Some(
                            *ssa.definition_versions
                                .get(&(block.id, statement_index_u32))
                                .ok_or_else(|| {
                                    format!(
                                        "semantic statement {} in block {} has no SSA definition",
                                        statement_index, block.id.0
                                    )
                                })?,
                        ),
                        None => None,
                    };
                    let mut context = SemanticProjectionContext {
                        counts: &mut counts,
                        function_id,
                        block_id,
                        uses: &uses,
                        fixed_versions: &ssa.fixed_versions,
                    };
                    let owner = self.project_semantic_stmt(
                        &mut context,
                        &function.security,
                        statement,
                        semantic_destination,
                    )?;
                    let span = function
                        .security
                        .statement_spans
                        .get(&(block.id, statement_index as u32))
                        .copied()
                        .or_else(|| {
                            air_stmt_destination(statement)
                                .and_then(|destination| function.var_span(destination))
                        })
                        .unwrap_or(function.def_span);
                    self.spans.insert(owner, span);
                    if let (Some(base), Some(version)) = (base_destination, semantic_destination) {
                        uses.insert(base, version);
                    }
                }
                let mut context = SemanticProjectionContext {
                    counts: &mut counts,
                    function_id,
                    block_id,
                    uses: &uses,
                    fixed_versions: &ssa.fixed_versions,
                };
                let terminator = self.project_semantic_terminator(
                    &mut context,
                    &block.terminator,
                    SemanticTerminatorSecurity {
                        declared_policy: function.security.control_policy.get(&block.id).copied(),
                        return_contract: function.security.return_contract,
                        abortive_transfer: function
                            .security
                            .abortive_transfer_blocks
                            .contains(&block.id),
                        semantically_unreachable: function
                            .security
                            .semantic_unreachable_blocks
                            .contains(&block.id)
                            || (matches!(block.terminator, AirTerminator::Return(None))
                                && function.ret != AirType::Unit),
                    },
                )?;
                self.spans.insert(
                    terminator,
                    function
                        .security
                        .terminator_spans
                        .get(&block.id)
                        .copied()
                        .unwrap_or(function.def_span),
                );
            }
        }

        let manifest = self
            .nodes
            .get_mut(manifest_index)
            .ok_or("semantic manifest disappeared during projection")?;
        manifest.origin = counts.functions;
        manifest.actual = counts.blocks;
        manifest.required = counts.instructions;
        manifest.ceiling = counts.operands;
        manifest.aux = counts.values;
        self.functions = u64::from(counts.functions);
        self.flush_semantic_metadata()?;
        Ok(())
    }

    fn structural(&mut self, class: u32) -> Result<(), String> {
        self.push(Node::ordinary(Op::Effect, class)).map(|_| ())
    }

    fn ct_use(&mut self, class: u32) -> Result<(), String> {
        let mut node = Node::ordinary(Op::CtUse, class);
        node.flags = 0;
        self.push(node).map(|_| ())
    }

    fn boundary(&mut self, class: u32) -> Result<(), String> {
        self.push(Node::ordinary(Op::Boundary, class)).map(|_| ())
    }

    fn authority(&mut self, mask: u32, class: u32) -> Result<(), String> {
        let mut node = Node::ordinary(Op::Authority, class);
        node.actual = mask;
        node.required = mask;
        self.push(node).map(|_| ())
    }

    fn consume(&mut self, class: u32) -> Result<(), String> {
        let node = Node::ordinary(Op::Consume, class);
        let origin = self.push(node)?;
        self.nodes.last_mut().expect("just pushed").origin = origin;
        Ok(())
    }

    fn cap_origin(&mut self, kind: u32, ceiling: u32, source_class: u8) -> Result<CapCell, String> {
        let mut node = Node::ordinary(Op::CapOrigin, kind);
        node.flags = source_class;
        node.ceiling = ceiling;
        node.aux = kind;
        let id = self.push(node)?;
        self.nodes.last_mut().expect("just pushed").actual = id;
        Ok(CapCell { id, kind, ceiling })
    }

    fn cap_restrict(&mut self, source: CapCell, restriction: u32) -> Result<CapCell, String> {
        let mut node = Node::ordinary(Op::CapRestrict, source.kind);
        node.origin = source.id;
        node.required = restriction;
        node.ceiling = source.ceiling;
        node.aux = source.kind;
        let id = self.push(node)?;
        self.nodes.last_mut().expect("just pushed").actual = id;
        Ok(CapCell {
            id,
            kind: source.kind,
            ceiling: source.ceiling,
        })
    }

    fn cap_derive(&mut self, op: Op, source: CapCell) -> Result<CapCell, String> {
        let mut node = Node::ordinary(op, source.kind);
        node.origin = source.id;
        node.ceiling = source.ceiling;
        node.aux = source.kind;
        let id = self.push(node)?;
        self.nodes.last_mut().expect("just pushed").actual = id;
        Ok(CapCell {
            id,
            kind: source.kind,
            ceiling: source.ceiling,
        })
    }

    fn cap_sink(&mut self, source: CapCell, required: u32, class: u32) -> Result<(), String> {
        let mut node = Node::ordinary(Op::CapSink, source.kind);
        node.origin = source.id;
        node.required = required;
        node.ceiling = source.ceiling;
        node.aux = source.kind;
        node.label_a = Label::Public;
        node.label_b = Label::Public;
        node.flags = u8::try_from(class.min(u32::from(u8::MAX))).unwrap_or(u8::MAX);
        self.push(node).map(|_| ())
    }

    fn cap_release(&mut self, source: CapCell, required: u32) -> Result<(), String> {
        let mut node = Node::ordinary(Op::CapRelease, source.kind);
        node.origin = source.id;
        node.required = required;
        node.ceiling = source.ceiling;
        node.aux = source.kind;
        self.push(node).map(|_| ())
    }

    fn cap_slot(&mut self, kind: u32, ceiling: u32, occupied: bool) -> Result<SlotCell, String> {
        let mut node = Node::ordinary(Op::CapSlot, kind);
        node.flags = u8::from(occupied);
        node.ceiling = ceiling;
        node.aux = kind;
        let id = self.push(node)?;
        self.nodes.last_mut().expect("just pushed").actual = id;
        Ok(SlotCell { id, kind, ceiling })
    }

    fn cap_slot_put(&mut self, slot: SlotCell, source: CapCell) -> Result<(), String> {
        if slot.kind != source.kind || slot.ceiling != source.ceiling {
            return Err("capability slot type/mask mismatch reached CSIR projection".to_owned());
        }
        let mut node = Node::ordinary(Op::CapSlotPut, source.kind);
        node.origin = source.id;
        node.actual = slot.id;
        node.ceiling = source.ceiling;
        node.aux = source.kind;
        self.push(node).map(|_| ())
    }

    fn cap_slot_take(&mut self, slot: SlotCell) -> Result<CapCell, String> {
        let mut node = Node::ordinary(Op::CapSlotTake, slot.kind);
        node.origin = slot.id;
        node.ceiling = slot.ceiling;
        node.aux = slot.kind;
        let id = self.push(node)?;
        self.nodes.last_mut().expect("just pushed").actual = id;
        Ok(CapCell {
            id,
            kind: slot.kind,
            ceiling: slot.ceiling,
        })
    }

    fn cap_meet(&mut self, left: CapCell, right: CapCell) -> Result<CapCell, String> {
        if left.kind != right.kind || left.ceiling != right.ceiling {
            return Err("capability control-flow meet has incompatible types".to_owned());
        }
        let mut node = Node::ordinary(Op::CapMeet, left.kind);
        node.origin = left.id;
        node.required = right.id;
        node.ceiling = left.ceiling;
        node.aux = left.kind;
        let id = self.push(node)?;
        self.nodes.last_mut().expect("just pushed").actual = id;
        Ok(CapCell {
            id,
            kind: left.kind,
            ceiling: left.ceiling,
        })
    }

    fn path_fork(&mut self, arms: usize) -> Result<(), String> {
        let arm_count =
            u32::try_from(arms).map_err(|_| "capability path arm count exceeds u32".to_owned())?;
        if arm_count < 2 {
            return Err("capability path fork requires at least two arms".to_owned());
        }
        let node = Node::ordinary(Op::PathFork, arm_count);
        self.push(node).map(|_| ())
    }

    fn path_arm(&mut self, falls_through: bool) -> Result<(), String> {
        let mut node = Node::ordinary(Op::PathArm, 0);
        node.flags = u8::from(falls_through);
        self.push(node).map(|_| ())
    }

    fn path_join(&mut self, falls_through: bool) -> Result<(), String> {
        let mut node = Node::ordinary(Op::PathJoin, 0);
        node.flags = u8::from(falls_through);
        self.push(node).map(|_| ())
    }

    fn path_loop(&mut self) -> Result<(), String> {
        self.push(Node::ordinary(Op::PathLoop, 0)).map(|_| ())
    }

    fn path_back(&mut self) -> Result<(), String> {
        self.push(Node::ordinary(Op::PathBack, 0)).map(|_| ())
    }

    fn path_break(&mut self) -> Result<(), String> {
        self.push(Node::ordinary(Op::PathBreak, 0)).map(|_| ())
    }

    fn path_loop_join(&mut self) -> Result<(), String> {
        self.push(Node::ordinary(Op::PathLoopJoin, 0)).map(|_| ())
    }

    fn set_signed_magnitude(node: &mut Node, value: i128) -> Result<(), String> {
        let negative = value < 0;
        let magnitude = value.unsigned_abs();
        let magnitude = u64::try_from(magnitude)
            .map_err(|_| "CSIR difference constant exceeds sign-magnitude u64".to_owned())?;
        node.required = magnitude as u32;
        node.ceiling = (magnitude >> 32) as u32;
        if negative {
            node.flags |= 0x02;
        }
        Ok(())
    }

    fn diff_le(&mut self, lhs: u32, rhs: u32, constant: i128) -> Result<(), String> {
        let mut node = Node::ordinary(Op::DiffLe, 0);
        node.origin = lhs;
        node.actual = rhs;
        Self::set_signed_magnitude(&mut node, constant)?;
        self.push(node).map(|_| ())
    }

    fn int_cell(&mut self, expression: &TypedExpr) -> Result<u32, String> {
        let mut node = Node::ordinary(Op::IntCell, 0);
        let exact = match &expression.kind {
            TypedExprKind::Literal(Literal::Int(value)) => Some(*value),
            _ => None,
        };
        if let Some(value) = exact {
            node.flags |= 0x04;
            Self::set_signed_magnitude(&mut node, i128::from(value))?;
        } else {
            node.flags = 1;
            node.required = 0;
            node.ceiling = 0;
        }
        let cell = self.push(node)?;
        self.nodes.last_mut().expect("just pushed").actual = cell;

        if let Some(clauses) = &expression.refinement {
            for clause in clauses {
                let RefinementRhs::Literal(bound) = clause.rhs else {
                    continue;
                };
                let bound = i128::from(bound);
                match clause.op {
                    RefinementOp::Le => self.diff_le(cell, 0, bound)?,
                    RefinementOp::Lt => self.diff_le(cell, 0, bound - 1)?,
                    RefinementOp::Ge => self.diff_le(0, cell, -bound)?,
                    RefinementOp::Gt => self.diff_le(0, cell, -(bound + 1))?,
                    RefinementOp::Eq => {
                        self.diff_le(cell, 0, bound)?;
                        self.diff_le(0, cell, -bound)?;
                    }
                    RefinementOp::Ne => {}
                }
            }
        }
        Ok(cell)
    }

    fn quantity_use(
        &mut self,
        op: Op,
        source: CapCell,
        child: CapCell,
        amount: u32,
    ) -> Result<(), String> {
        let mut node = Node::ordinary(Op::QuantityUse, 0);
        node.flags = 0x03; // unconditional signed guard + host balance check
        node.origin = source.id;
        node.actual = child.id;
        node.required = amount;
        node.ceiling = 0;
        node.aux = match op {
            Op::CapSplit => 1,
            Op::CapDraw => 2,
            _ => return Err("quantity link must name cap split or draw".to_owned()),
        };
        self.push(node).map(|_| ())
    }

    fn graph_seed(&mut self, label: Label) -> Result<u32, String> {
        let mut node = Node::ordinary(Op::TaintSeed, 0);
        node.label_a = label;
        let cell = self.push(node)?;
        self.nodes.last_mut().expect("just pushed").origin = cell;
        Ok(cell)
    }

    fn graph_edge(&mut self, source: u32, target: u32) -> Result<(), String> {
        let mut node = Node::ordinary(Op::TaintEdge, 0);
        node.origin = source;
        node.actual = target;
        self.push(node).map(|_| ())
    }

    fn graph_join<I>(&mut self, cells: I) -> Result<u32, String>
    where
        I: IntoIterator<Item = u32>,
    {
        let mut inputs = Vec::new();
        for cell in cells {
            if cell != 0 && !inputs.contains(&cell) {
                inputs.push(cell);
            }
        }
        match inputs.as_slice() {
            [] => Ok(0),
            [only] => Ok(*only),
            _ => {
                let target = self.graph_seed(Label::Public)?;
                for source in inputs {
                    self.graph_edge(source, target)?;
                }
                Ok(target)
            }
        }
    }

    fn graph_with_pc(&mut self, value: u32, pc: u32) -> Result<u32, String> {
        self.graph_join([value, pc])
    }

    fn graph_sink(
        &mut self,
        value: u32,
        pc: u32,
        declared: Label,
        class: u32,
    ) -> Result<(), String> {
        let mut node = Node::ordinary(Op::TaintSink, class);
        node.origin = value;
        node.actual = pc;
        node.label_b = declared;
        self.push(node).map(|_| ())
    }

    fn graph_ct_use(&mut self, value: u32, pc: u32, class: u32) -> Result<(), String> {
        let mut node = Node::ordinary(Op::TaintCtUse, class);
        node.origin = value;
        node.actual = pc;
        self.push(node).map(|_| ())
    }

    fn graph_release(&mut self, input: u32, output: Label, stage: u32) -> Result<u32, String> {
        let mut node = Node::ordinary(Op::TaintRelease, stage);
        node.origin = input;
        node.label_b = output;
        node.aux = stage;
        let cell = self.push(node)?;
        self.nodes.last_mut().expect("just pushed").actual = cell;
        Ok(cell)
    }

    fn project_program(
        &mut self,
        program: &TypedProgram,
        authority_registry: &AuthorityRegistry,
    ) -> Result<(), String> {
        for module in &program.modules {
            for function in &module.functions {
                self.functions += 1;
                let mut ret = Node::ordinary(Op::Flow, 1);
                ret.label_b = function.ret_taint.into();
                self.push(ret)?;
                for param in function.params.iter().chain(function.captures.iter()) {
                    let mut flow = Node::ordinary(Op::Flow, 2);
                    flow.label_b = param.taint.into();
                    self.push(flow)?;
                }
                self.project_block(&function.body)?;
            }
        }
        self.project_taint_graph(program)?;
        self.project_capability_graph(program, authority_registry)?;
        Ok(())
    }

    fn project_block(&mut self, block: &TypedBlock) -> Result<(), String> {
        for statement in &block.statements {
            self.project_stmt(statement)?;
        }
        Ok(())
    }

    fn project_stmts(&mut self, statements: &[TypedStmt]) -> Result<(), String> {
        for statement in statements {
            self.project_stmt(statement)?;
        }
        Ok(())
    }

    fn project_stmt(&mut self, statement: &TypedStmt) -> Result<(), String> {
        match statement {
            TypedStmt::Let(stmt) => {
                self.structural(100)?;
                self.project_expr(&stmt.value)
            }
            TypedStmt::Assign(stmt) => {
                self.structural(101)?;
                self.project_expr(&stmt.place)?;
                self.project_expr(&stmt.value)
            }
            TypedStmt::Expr(stmt) => {
                self.structural(102)?;
                self.project_expr(&stmt.expr)
            }
            TypedStmt::If(stmt) => {
                self.ct_use(20)?;
                self.project_expr(&stmt.condition)?;
                self.project_block(&stmt.then_branch)?;
                self.project_block(&stmt.else_branch)
            }
            TypedStmt::Match(stmt) => {
                self.ct_use(22)?;
                self.project_expr(&stmt.scrutinee)?;
                for arm in &stmt.arms {
                    if let Some(guard) = &arm.guard {
                        self.ct_use(20)?;
                        self.project_expr(guard)?;
                    }
                    self.project_block(&arm.body)?;
                }
                Ok(())
            }
            TypedStmt::While(stmt) => {
                self.ct_use(21)?;
                self.project_expr(&stmt.condition)?;
                self.project_block(&stmt.body)
            }
            TypedStmt::ForIn(stmt) => {
                self.ct_use(21)?;
                self.project_expr(&stmt.iterable)?;
                self.project_stmts(&stmt.body)
            }
            TypedStmt::ForRange(stmt) => {
                self.ct_use(21)?;
                self.project_expr(&stmt.start)?;
                self.project_expr(&stmt.end)?;
                self.project_stmts(&stmt.body)
            }
            TypedStmt::Return(stmt) => {
                self.structural(103)?;
                if let Some(value) = &stmt.value {
                    self.project_expr(value)?;
                }
                Ok(())
            }
            TypedStmt::Break(_) => self.structural(104),
            TypedStmt::Continue(_) => self.structural(105),
        }
    }

    fn project_exprs(&mut self, expressions: &[TypedExpr]) -> Result<(), String> {
        for expression in expressions {
            self.project_expr(expression)?;
        }
        Ok(())
    }

    fn project_expr(&mut self, expression: &TypedExpr) -> Result<(), String> {
        match &expression.kind {
            TypedExprKind::Literal(_) => self.structural(200),
            TypedExprKind::Local(_) => self.structural(201),
            TypedExprKind::StateField(_) => self.boundary(202),
            TypedExprKind::Call(call) => {
                self.structural(203)?;
                self.project_exprs(&call.args)
            }
            TypedExprKind::Intrinsic(intrinsic) => {
                self.project_intrinsic(&intrinsic.kind)?;
                self.project_exprs(&intrinsic.args)
            }
            TypedExprKind::ResultCtor(ctor) => {
                self.structural(205)?;
                self.project_expr(&ctor.value)
            }
            TypedExprKind::EnumConstruct(ctor) => {
                self.structural(206)?;
                self.project_exprs(&ctor.fields)
            }
            TypedExprKind::Try(expr) => {
                self.ct_use(20)?;
                self.project_expr(&expr.value)
            }
            TypedExprKind::Send(send) => {
                self.boundary(27)?;
                self.project_exprs(&send.args)
            }
            TypedExprKind::Ask(ask) => {
                self.boundary(27)?;
                self.project_exprs(&ask.args)?;
                self.project_expr(&ask.timeout)
            }
            TypedExprKind::Spawn(spawn) => {
                self.boundary(27)?;
                self.project_exprs(&spawn.args)
            }
            TypedExprKind::Binary(binary) => {
                if matches!(binary.op, BinaryOp::Div | BinaryOp::Mod) {
                    self.ct_use(24)?;
                } else if matches!(binary.op, BinaryOp::Eq | BinaryOp::NotEq) {
                    self.ct_use(25)?;
                } else {
                    self.structural(212)?;
                }
                self.project_expr(&binary.lhs)?;
                self.project_expr(&binary.rhs)
            }
            TypedExprKind::RecordConstruct(record) => {
                self.structural(213)?;
                for (_, value) in &record.fields {
                    self.project_expr(value)?;
                }
                Ok(())
            }
            TypedExprKind::FieldAccess(field) => {
                self.structural(214)?;
                self.project_expr(&field.object)
            }
            TypedExprKind::CapRestrict(restrict) => self.authority(restrict.restriction_mask, 215),
            TypedExprKind::CapSplit(split) => {
                self.authority(0, 216)?;
                self.project_expr(&split.amount)
            }
            TypedExprKind::CapDraw(draw) => {
                self.authority(0, 217)?;
                self.project_expr(&draw.amount)
            }
            TypedExprKind::Mint(mint) => {
                self.authority(0, 218)?;
                self.project_expr(&mint.target)
            }
            TypedExprKind::ArrayLit(array) => {
                self.ct_use(28)?;
                self.project_exprs(&array.elements)
            }
            TypedExprKind::Index(index) => {
                self.ct_use(23)?;
                self.project_expr(&index.array)?;
                self.project_expr(&index.index)
            }
            TypedExprKind::Slice(slice) => {
                self.ct_use(23)?;
                self.project_expr(&slice.array)?;
                if let Some(start) = &slice.start {
                    self.project_expr(start)?;
                }
                if let Some(end) = &slice.end {
                    self.project_expr(end)?;
                }
                Ok(())
            }
            TypedExprKind::ClosureConstruct(_) => self.structural(222),
            TypedExprKind::Borrow(borrow) => {
                self.structural(223)?;
                self.project_expr(&borrow.inner)
            }
            TypedExprKind::Grant(grant) => {
                self.authority(0, 224)?;
                self.project_expr(&grant.cap)?;
                self.project_expr(&grant.body)
            }
            TypedExprKind::Handle(handle) => {
                self.structural(225)?;
                self.project_block(&handle.body)
            }
            TypedExprKind::Perform(perform) => {
                self.structural(226)?;
                self.project_exprs(&perform.args)
            }
            TypedExprKind::ClauseHandle(handle) => {
                self.structural(227)?;
                self.project_expr(&handle.scrutinee)?;
                for clause in &handle.clauses {
                    self.project_block(&clause.body)?;
                }
                Ok(())
            }
            TypedExprKind::Resume(resume) => {
                self.structural(228)?;
                self.project_expr(&resume.value)
            }
            TypedExprKind::Declassify(declassify) => {
                let mut node = Node::ordinary(Op::Declassify, 1);
                node.label_a = Label::Secret;
                node.label_b = Label::Public;
                node.aux = 1;
                let origin = self.push(node)?;
                self.nodes.last_mut().expect("just pushed").origin = origin;
                self.project_expr(&declassify.value)?;
                self.project_expr(&declassify.cap)
            }
            TypedExprKind::DeclassifyCt(declassify) => {
                let mut node = Node::ordinary(Op::Declassify, 2);
                node.label_a = Label::SecretCt;
                node.label_b = Label::Secret;
                node.aux = 2;
                let origin = self.push(node)?;
                self.nodes.last_mut().expect("just pushed").origin = origin;
                self.project_expr(&declassify.value)?;
                self.project_expr(&declassify.cap)
            }
            TypedExprKind::ExternCall(call) => {
                self.ct_use(26)?;
                self.boundary(26)?;
                self.project_exprs(&call.args)
            }
            TypedExprKind::Region(region) => {
                self.ct_use(28)?;
                self.project_expr(&region.limit)?;
                self.project_block(&region.body)
            }
            TypedExprKind::IndirectCall(call) => {
                self.structural(233)?;
                self.project_exprs(&call.args)
            }
            TypedExprKind::FString(string) => {
                self.ct_use(25)?;
                for part in &string.parts {
                    match part {
                        TypedFStringPart::Literal(_) => self.structural(234)?,
                        TypedFStringPart::Hole(hole) => self.project_expr(hole)?,
                    }
                }
                Ok(())
            }
        }
    }

    fn project_intrinsic(&mut self, intrinsic: &TypedIntrinsicKind) -> Result<(), String> {
        match intrinsic {
            TypedIntrinsicKind::CtEq => self.fixed_ct(30),
            TypedIntrinsicKind::CtSelect => self.fixed_ct(31),
            TypedIntrinsicKind::CtLt => self.fixed_ct(32),
            TypedIntrinsicKind::Alloc
            | TypedIntrinsicKind::U256FromI64 { .. }
            | TypedIntrinsicKind::U256Make
            | TypedIntrinsicKind::StrSubstr { .. }
            | TypedIntrinsicKind::StrFromRaw { .. } => self.ct_use(28),
            TypedIntrinsicKind::Load8
            | TypedIntrinsicKind::Store8
            | TypedIntrinsicKind::StrByteAt { .. }
            | TypedIntrinsicKind::VecStore { .. }
            | TypedIntrinsicKind::VecLoad { .. } => self.ct_use(23),
            TypedIntrinsicKind::SlotNew { .. } | TypedIntrinsicKind::SlotPut => {
                self.authority(0, 240)
            }
            TypedIntrinsicKind::SlotTake => self.consume(240),
            TypedIntrinsicKind::U256Limb { .. }
            | TypedIntrinsicKind::TrapIf
            | TypedIntrinsicKind::Trap
            | TypedIntrinsicKind::ArrayLen { .. }
            | TypedIntrinsicKind::SliceLen
            | TypedIntrinsicKind::ArrayIsEmpty { .. }
            | TypedIntrinsicKind::SliceIsEmpty
            | TypedIntrinsicKind::ArrayContains { .. }
            | TypedIntrinsicKind::SliceContains { .. }
            | TypedIntrinsicKind::SliceFirst { .. }
            | TypedIntrinsicKind::SliceLast { .. }
            | TypedIntrinsicKind::StrLen
            | TypedIntrinsicKind::StrAsOutput
            | TypedIntrinsicKind::StrIsEmpty
            | TypedIntrinsicKind::IntConvert { .. } => self.structural(241),
        }
    }

    fn fixed_ct(&mut self, class: u32) -> Result<(), String> {
        let mut node = Node::ordinary(Op::FixedCt, class);
        node.label_a = Label::SecretCt;
        self.push(node).map(|_| ())
    }
}

impl Projector {
    fn project_taint_graph(&mut self, program: &TypedProgram) -> Result<(), String> {
        for function in program.modules.iter().flat_map(|module| &module.functions) {
            let mut env = GraphEnv::public();
            for param in function.params.iter().chain(&function.captures) {
                // @Flow ranges over Public/Internal/Secret. Seeding it at the
                // greatest admissible label checks all three instantiations in
                // one monotone graph; SecretCT is deliberately excluded.
                let seed = if param.flow {
                    Label::Secret
                } else {
                    param.taint.into()
                };
                let cell = self.graph_seed(seed)?;
                env.bindings.insert(param.name.clone(), cell);
                env.contracts.insert(param.name.clone(), param.taint.into());
            }
            self.project_graph_block(&function.body, &mut env, function, program)?;
        }
        Ok(())
    }

    fn project_graph_block(
        &mut self,
        block: &TypedBlock,
        env: &mut GraphEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
    ) -> Result<(Option<u32>, bool), String> {
        self.project_graph_scoped_stmts(&block.statements, env, current_fn, program)
    }

    fn project_graph_stmts(
        &mut self,
        statements: &[TypedStmt],
        env: &mut GraphEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
    ) -> Result<(Option<u32>, bool), String> {
        self.project_graph_scoped_stmts(statements, env, current_fn, program)
    }

    fn project_graph_scoped_stmts(
        &mut self,
        statements: &[TypedStmt],
        env: &mut GraphEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
    ) -> Result<(Option<u32>, bool), String> {
        let mut tail = None;
        let mut shadowed: BTreeMap<String, (Option<u32>, Option<Label>)> = BTreeMap::new();
        let mut diverged = false;
        for statement in statements {
            if let TypedStmt::Let(stmt) = statement {
                shadowed.entry(stmt.name.clone()).or_insert_with(|| {
                    (
                        env.bindings.get(&stmt.name).copied(),
                        env.contracts.get(&stmt.name).copied(),
                    )
                });
            }
            let (value, statement_diverged) =
                self.project_graph_stmt(statement, env, current_fn, program)?;
            tail = value;
            if statement_diverged {
                diverged = true;
                break;
            }
        }
        for (name, (binding, contract)) in shadowed {
            match binding {
                Some(cell) => {
                    env.bindings.insert(name.clone(), cell);
                }
                None => {
                    env.bindings.remove(&name);
                }
            }
            match contract {
                Some(label) => {
                    env.contracts.insert(name, label);
                }
                None => {
                    env.contracts.remove(&name);
                }
            }
        }
        Ok((tail, diverged))
    }

    fn merge_graph_envs(
        &mut self,
        base: &GraphEnv,
        variants: &[GraphEnv],
    ) -> Result<GraphEnv, String> {
        let mut merged = base.clone();
        for name in base.bindings.keys() {
            let mut cells = Vec::with_capacity(variants.len());
            for variant in variants {
                cells.push(variant.lookup(name));
            }
            if !cells.is_empty() {
                merged
                    .bindings
                    .insert(name.clone(), self.graph_join(cells)?);
            }
        }
        Ok(merged)
    }

    fn loop_graph_head(&mut self, pre: &GraphEnv) -> Result<GraphEnv, String> {
        let mut head = pre.clone();
        for (name, source) in &pre.bindings {
            let target = self.graph_seed(Label::Public)?;
            self.graph_edge(*source, target)?;
            head.bindings.insert(name.clone(), target);
        }
        Ok(head)
    }

    fn close_loop_back_edges(&mut self, head: &GraphEnv, body: &GraphEnv) -> Result<(), String> {
        for (name, target) in &head.bindings {
            self.graph_edge(body.lookup(name), *target)?;
        }
        Ok(())
    }

    fn project_graph_stmt(
        &mut self,
        statement: &TypedStmt,
        env: &mut GraphEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
    ) -> Result<(Option<u32>, bool), String> {
        match statement {
            TypedStmt::Let(stmt) => {
                let value = self.project_graph_expr(&stmt.value, env, current_fn, program)?;
                let polymorphic = current_fn.ret_flow || current_fn.params.iter().any(|p| p.flow);
                let declared = stmt
                    .taint
                    .map(Label::from)
                    .or((!polymorphic).then_some(Label::Public));
                if let Some(label) = declared {
                    self.graph_sink(value, env.pc, label, 1)?;
                    let binding = self.graph_seed(label)?;
                    self.graph_edge(value, binding)?;
                    env.bindings.insert(stmt.name.clone(), binding);
                    env.contracts.insert(stmt.name.clone(), label);
                } else {
                    env.bindings.insert(stmt.name.clone(), value);
                }
                Ok((None, false))
            }
            TypedStmt::Assign(stmt) => {
                let value = self.project_graph_expr(&stmt.value, env, current_fn, program)?;
                let effective = self.graph_with_pc(value, env.pc)?;
                match &stmt.place.kind {
                    TypedExprKind::Local(name) => {
                        let assigned = if stmt.op.is_some() {
                            self.graph_join([env.lookup(name), effective])?
                        } else {
                            effective
                        };
                        env.bindings.insert(name.clone(), assigned);
                    }
                    TypedExprKind::StateField(name) => {
                        let declared = env.contracts.get(name).copied().unwrap_or(Label::Public);
                        self.graph_sink(effective, env.pc, declared, 1)?;
                    }
                    _ => {
                        if let Some(root) = graph_place_root_state(&stmt.place) {
                            let declared =
                                env.contracts.get(root).copied().unwrap_or(Label::Public);
                            self.graph_sink(effective, env.pc, declared, 1)?;
                        } else if let Some(root) = graph_place_root_local(&stmt.place) {
                            let raised = self.graph_join([env.lookup(root), effective])?;
                            env.bindings.insert(root.to_owned(), raised);
                        }
                    }
                }
                Ok((None, false))
            }
            TypedStmt::Expr(stmt) => {
                let value = self.project_graph_expr(&stmt.expr, env, current_fn, program)?;
                Ok((Some(value), false))
            }
            TypedStmt::If(stmt) => {
                let condition =
                    self.project_graph_expr(&stmt.condition, env, current_fn, program)?;
                self.graph_ct_use(condition, env.pc, 20)?;
                let branch_pc = self.graph_join([env.pc, condition])?;
                let pre = env.clone();
                let mut then_env = pre.clone();
                then_env.pc = branch_pc;
                let (_, then_diverged) = self.project_graph_block(
                    &stmt.then_branch,
                    &mut then_env,
                    current_fn,
                    program,
                )?;
                let mut else_env = pre.clone();
                else_env.pc = branch_pc;
                let (_, else_diverged) = self.project_graph_block(
                    &stmt.else_branch,
                    &mut else_env,
                    current_fn,
                    program,
                )?;
                let fallthrough: Vec<GraphEnv> =
                    [(then_env, then_diverged), (else_env, else_diverged)]
                        .into_iter()
                        .filter_map(|(candidate, diverged)| (!diverged).then_some(candidate))
                        .collect();
                if !fallthrough.is_empty() {
                    *env = self.merge_graph_envs(&pre, &fallthrough)?;
                }
                env.pc = pre.pc;
                Ok((None, then_diverged && else_diverged))
            }
            TypedStmt::Match(stmt) => {
                let scrutinee =
                    self.project_graph_expr(&stmt.scrutinee, env, current_fn, program)?;
                self.graph_ct_use(scrutinee, env.pc, 23)?;
                let pre = env.clone();
                let mut selection_pc = self.graph_join([env.pc, scrutinee])?;
                let mut fallthrough = Vec::new();
                let mut all_diverge = !stmt.arms.is_empty();
                for arm in &stmt.arms {
                    let mut arm_env = pre.clone();
                    arm_env.pc = selection_pc;
                    graph_bind_pattern(&arm.pattern, scrutinee, &mut arm_env);
                    if let Some(guard) = &arm.guard {
                        let guard_cell =
                            self.project_graph_expr(guard, &mut arm_env, current_fn, program)?;
                        self.graph_ct_use(guard_cell, selection_pc, 23)?;
                        selection_pc = self.graph_join([selection_pc, guard_cell])?;
                        arm_env.pc = selection_pc;
                    }
                    let (_, diverged) =
                        self.project_graph_block(&arm.body, &mut arm_env, current_fn, program)?;
                    graph_restore_pattern(&arm.pattern, &pre, &mut arm_env);
                    all_diverge &= diverged;
                    if !diverged {
                        fallthrough.push(arm_env);
                    }
                }
                if !fallthrough.is_empty() {
                    *env = self.merge_graph_envs(&pre, &fallthrough)?;
                }
                env.pc = pre.pc;
                Ok((None, all_diverge))
            }
            TypedStmt::While(stmt) => {
                let pre = env.clone();
                let mut head = self.loop_graph_head(&pre)?;
                let condition =
                    self.project_graph_expr(&stmt.condition, &mut head, current_fn, program)?;
                self.graph_ct_use(condition, head.pc, 21)?;
                let mut body = head.clone();
                body.pc = self.graph_join([pre.pc, condition])?;
                self.project_graph_block(&stmt.body, &mut body, current_fn, program)?;
                self.close_loop_back_edges(&head, &body)?;
                head.pc = pre.pc;
                *env = head;
                Ok((None, false))
            }
            TypedStmt::ForIn(stmt) => {
                let iterable = self.project_graph_expr(&stmt.iterable, env, current_fn, program)?;
                self.graph_ct_use(iterable, env.pc, 22)?;
                let pre = env.clone();
                let mut head = self.loop_graph_head(&pre)?;
                let mut body = head.clone();
                body.pc = self.graph_join([pre.pc, iterable])?;
                let prior_loop_var = body.bindings.get(&stmt.var).copied();
                body.bindings.insert(stmt.var.clone(), iterable);
                self.project_graph_stmts(&stmt.body, &mut body, current_fn, program)?;
                match prior_loop_var {
                    Some(cell) => {
                        body.bindings.insert(stmt.var.clone(), cell);
                    }
                    None => {
                        body.bindings.remove(&stmt.var);
                    }
                }
                self.close_loop_back_edges(&head, &body)?;
                head.pc = pre.pc;
                *env = head;
                Ok((None, false))
            }
            TypedStmt::ForRange(stmt) => {
                let start = self.project_graph_expr(&stmt.start, env, current_fn, program)?;
                let end = self.project_graph_expr(&stmt.end, env, current_fn, program)?;
                let bounds = self.graph_join([start, end])?;
                self.graph_ct_use(bounds, env.pc, 22)?;
                let pre = env.clone();
                let mut head = self.loop_graph_head(&pre)?;
                let mut body = head.clone();
                body.pc = self.graph_join([pre.pc, bounds])?;
                let prior_loop_var = body.bindings.get(&stmt.var).copied();
                body.bindings.insert(stmt.var.clone(), bounds);
                self.project_graph_stmts(&stmt.body, &mut body, current_fn, program)?;
                match prior_loop_var {
                    Some(cell) => {
                        body.bindings.insert(stmt.var.clone(), cell);
                    }
                    None => {
                        body.bindings.remove(&stmt.var);
                    }
                }
                self.close_loop_back_edges(&head, &body)?;
                head.pc = pre.pc;
                *env = head;
                Ok((None, false))
            }
            TypedStmt::Return(stmt) => {
                if let Some(value) = &stmt.value {
                    let cell = self.project_graph_expr(value, env, current_fn, program)?;
                    if !current_fn.ret_flow {
                        let declared = current_fn.effective_return_taint().into();
                        self.graph_sink(cell, env.pc, declared, 1)?;
                    }
                }
                Ok((None, true))
            }
            TypedStmt::Break(_) | TypedStmt::Continue(_) => Ok((None, true)),
        }
    }

    fn project_graph_exprs(
        &mut self,
        expressions: &[TypedExpr],
        env: &mut GraphEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
    ) -> Result<Vec<u32>, String> {
        expressions
            .iter()
            .map(|expression| self.project_graph_expr(expression, env, current_fn, program))
            .collect()
    }

    fn project_graph_expr(
        &mut self,
        expression: &TypedExpr,
        env: &mut GraphEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
    ) -> Result<u32, String> {
        let base = self.project_graph_expr_base(expression, env, current_fn, program)?;
        self.graph_with_pc(base, env.pc)
    }

    fn project_graph_expr_base(
        &mut self,
        expression: &TypedExpr,
        env: &mut GraphEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
    ) -> Result<u32, String> {
        match &expression.kind {
            TypedExprKind::Literal(_) => Ok(0),
            TypedExprKind::Local(name) | TypedExprKind::StateField(name) => Ok(env.lookup(name)),
            TypedExprKind::Call(call) => {
                let callee = graph_find_function(program, &call.callee)?;
                let args = self.project_graph_exprs(&call.args, env, current_fn, program)?;
                if args.len() != callee.params.len() {
                    return Err(format!(
                        "typed call `{}` has {} arguments but {} parameters",
                        call.callee,
                        args.len(),
                        callee.params.len()
                    ));
                }
                for (arg, param) in args.iter().zip(&callee.params) {
                    if param.flow {
                        self.graph_ct_use(*arg, 0, 30)?;
                    } else {
                        self.graph_sink(*arg, 0, param.taint.into(), 1)?;
                    }
                }
                let ret = if callee.ret_flow {
                    0
                } else {
                    self.graph_seed(callee.ret_taint.into())?
                };
                self.graph_join(args.into_iter().chain([ret]))
            }
            TypedExprKind::Intrinsic(intrinsic) => {
                let args = self.project_graph_exprs(&intrinsic.args, env, current_fn, program)?;
                match intrinsic.kind {
                    TypedIntrinsicKind::Alloc => {
                        if let Some(size) = args.first() {
                            self.graph_ct_use(*size, env.pc, 29)?;
                        }
                    }
                    TypedIntrinsicKind::Load8 | TypedIntrinsicKind::Store8 => {
                        if let Some(address) = args.first() {
                            self.graph_ct_use(*address, env.pc, 25)?;
                        }
                    }
                    TypedIntrinsicKind::VecStore { .. } | TypedIntrinsicKind::VecLoad { .. } => {
                        let address = self.graph_join(args.iter().take(2).copied())?;
                        self.graph_ct_use(address, env.pc, 25)?;
                    }
                    TypedIntrinsicKind::StrByteAt { .. } => {
                        if let Some(index) = args.get(1) {
                            self.graph_ct_use(*index, env.pc, 24)?;
                        }
                    }
                    TypedIntrinsicKind::CtEq
                    | TypedIntrinsicKind::CtSelect
                    | TypedIntrinsicKind::CtLt
                    | TypedIntrinsicKind::SlotNew { .. }
                    | TypedIntrinsicKind::SlotPut
                    | TypedIntrinsicKind::SlotTake
                    | TypedIntrinsicKind::U256FromI64 { .. }
                    | TypedIntrinsicKind::U256Make
                    | TypedIntrinsicKind::U256Limb { .. }
                    | TypedIntrinsicKind::TrapIf
                    | TypedIntrinsicKind::Trap
                    | TypedIntrinsicKind::ArrayLen { .. }
                    | TypedIntrinsicKind::SliceLen
                    | TypedIntrinsicKind::ArrayIsEmpty { .. }
                    | TypedIntrinsicKind::SliceIsEmpty
                    | TypedIntrinsicKind::ArrayContains { .. }
                    | TypedIntrinsicKind::SliceContains { .. }
                    | TypedIntrinsicKind::SliceFirst { .. }
                    | TypedIntrinsicKind::SliceLast { .. }
                    | TypedIntrinsicKind::StrLen
                    | TypedIntrinsicKind::StrAsOutput
                    | TypedIntrinsicKind::StrIsEmpty
                    | TypedIntrinsicKind::IntConvert { .. }
                    | TypedIntrinsicKind::StrSubstr { .. }
                    | TypedIntrinsicKind::StrFromRaw { .. } => {}
                }
                self.graph_join(args)
            }
            TypedExprKind::ResultCtor(ctor) => {
                self.project_graph_expr(&ctor.value, env, current_fn, program)
            }
            TypedExprKind::EnumConstruct(ctor) => {
                let fields = self.project_graph_exprs(&ctor.fields, env, current_fn, program)?;
                self.graph_join(fields)
            }
            TypedExprKind::Try(expr) => {
                self.project_graph_expr(&expr.value, env, current_fn, program)
            }
            TypedExprKind::Send(send) => {
                let args = self.project_graph_exprs(&send.args, env, current_fn, program)?;
                self.graph_actor_payload(program, &send.actor, Some(&send.handler), &args, env.pc)?;
                self.graph_join(args)
            }
            TypedExprKind::Ask(ask) => {
                let args = self.project_graph_exprs(&ask.args, env, current_fn, program)?;
                self.graph_actor_payload(program, &ask.actor, Some(&ask.handler), &args, env.pc)?;
                let timeout = self.project_graph_expr(&ask.timeout, env, current_fn, program)?;
                self.graph_ct_use(timeout, env.pc, 28)?;
                self.graph_join(args.into_iter().chain([timeout]))
            }
            TypedExprKind::Spawn(spawn) => {
                let args = self.project_graph_exprs(&spawn.args, env, current_fn, program)?;
                self.graph_actor_payload(program, &spawn.actor, None, &args, env.pc)?;
                Ok(0)
            }
            TypedExprKind::Binary(binary) => {
                let lhs = self.project_graph_expr(&binary.lhs, env, current_fn, program)?;
                let rhs = if matches!(binary.op, BinaryOp::LogicalAnd | BinaryOp::LogicalOr) {
                    self.graph_ct_use(lhs, env.pc, 20)?;
                    let mut rhs_env = env.clone();
                    rhs_env.pc = self.graph_join([env.pc, lhs])?;
                    self.project_graph_expr(&binary.rhs, &mut rhs_env, current_fn, program)?
                } else {
                    self.project_graph_expr(&binary.rhs, env, current_fn, program)?
                };
                let operands = self.graph_join([lhs, rhs])?;
                if matches!(binary.op, BinaryOp::Div | BinaryOp::Mod) {
                    self.graph_ct_use(operands, env.pc, 26)?;
                }
                if matches!(binary.op, BinaryOp::Eq | BinaryOp::NotEq)
                    && matches!(binary.lhs.ty, crate::type_check::Type::Str)
                    && matches!(binary.rhs.ty, crate::type_check::Type::Str)
                {
                    self.graph_ct_use(operands, env.pc, 33)?;
                }
                Ok(operands)
            }
            TypedExprKind::RecordConstruct(record) => {
                let mut cells = Vec::with_capacity(record.fields.len());
                for (_, field) in &record.fields {
                    cells.push(self.project_graph_expr(field, env, current_fn, program)?);
                }
                self.graph_join(cells)
            }
            TypedExprKind::FieldAccess(field) => {
                self.project_graph_expr(&field.object, env, current_fn, program)
            }
            TypedExprKind::CapSplit(split) => {
                let amount = self.project_graph_expr(&split.amount, env, current_fn, program)?;
                self.graph_ct_use(amount, env.pc, 27)?;
                self.graph_sink(amount, env.pc, Label::Public, 216)?;
                Ok(0)
            }
            TypedExprKind::CapDraw(draw) => {
                let amount = self.project_graph_expr(&draw.amount, env, current_fn, program)?;
                self.graph_ct_use(amount, env.pc, 27)?;
                self.graph_sink(amount, env.pc, Label::Public, 217)?;
                Ok(0)
            }
            TypedExprKind::CapRestrict(_) => Ok(0),
            TypedExprKind::Mint(mint) => {
                self.project_graph_expr(&mint.target, env, current_fn, program)?;
                Ok(0)
            }
            TypedExprKind::ArrayLit(array) => {
                let elements =
                    self.project_graph_exprs(&array.elements, env, current_fn, program)?;
                self.graph_join(elements)
            }
            TypedExprKind::Index(index) => {
                let array = self.project_graph_expr(&index.array, env, current_fn, program)?;
                let subscript = self.project_graph_expr(&index.index, env, current_fn, program)?;
                self.graph_ct_use(subscript, env.pc, 24)?;
                self.graph_join([array, subscript])
            }
            TypedExprKind::Slice(slice) => {
                let mut cells =
                    vec![self.project_graph_expr(&slice.array, env, current_fn, program)?];
                if let Some(start) = &slice.start {
                    let cell = self.project_graph_expr(start, env, current_fn, program)?;
                    self.graph_ct_use(cell, env.pc, 24)?;
                    cells.push(cell);
                }
                if let Some(end) = &slice.end {
                    let cell = self.project_graph_expr(end, env, current_fn, program)?;
                    self.graph_ct_use(cell, env.pc, 24)?;
                    cells.push(cell);
                }
                self.graph_join(cells)
            }
            TypedExprKind::ClosureConstruct(closure) => self.graph_join(
                closure
                    .captures
                    .iter()
                    .map(|capture| env.lookup(&capture.name)),
            ),
            TypedExprKind::Borrow(borrow) => {
                self.project_graph_expr(&borrow.inner, env, current_fn, program)
            }
            TypedExprKind::Grant(grant) => {
                let cap = self.project_graph_expr(&grant.cap, env, current_fn, program)?;
                let body = self.project_graph_expr(&grant.body, env, current_fn, program)?;
                self.graph_join([cap, body])
            }
            TypedExprKind::Handle(handle) => Ok(self
                .project_graph_block(&handle.body, env, current_fn, program)?
                .0
                .unwrap_or(0)),
            TypedExprKind::Perform(perform) => {
                let args = self.project_graph_exprs(&perform.args, env, current_fn, program)?;
                let op = program
                    .effect_ops
                    .get(&perform.effect)
                    .and_then(|ops| ops.iter().find(|op| op.name == perform.op))
                    .ok_or_else(|| {
                        format!(
                            "typed effect operation `{}.{}` was not found",
                            perform.effect, perform.op
                        )
                    })?;
                if args.len() != op.param_taints.len() {
                    return Err(format!(
                        "typed effect operation `{}.{}` has mismatched arity",
                        perform.effect, perform.op
                    ));
                }
                for (arg, declared) in args.iter().zip(&op.param_taints) {
                    self.graph_sink(*arg, env.pc, (*declared).into(), 1)?;
                }
                self.graph_join(args)
            }
            TypedExprKind::ClauseHandle(handle) => {
                let mut values =
                    vec![self.project_graph_expr(&handle.scrutinee, env, current_fn, program)?];
                for clause in &handle.clauses {
                    let op = program
                        .effect_ops
                        .get(&clause.effect)
                        .and_then(|ops| ops.iter().find(|op| op.name == clause.op))
                        .ok_or_else(|| {
                            format!(
                                "typed effect operation `{}.{}` was not found",
                                clause.effect, clause.op
                            )
                        })?;
                    if clause.binders.len() != op.param_taints.len() {
                        return Err(format!(
                            "typed effect clause `{}.{}` has mismatched arity",
                            clause.effect, clause.op
                        ));
                    }
                    let mut clause_env = env.clone();
                    for (binder, label) in clause.binders.iter().zip(&op.param_taints) {
                        let cell = self.graph_seed((*label).into())?;
                        clause_env.bindings.insert(binder.clone(), cell);
                    }
                    if let Some(value) = self
                        .project_graph_block(&clause.body, &mut clause_env, current_fn, program)?
                        .0
                    {
                        values.push(value);
                    }
                }
                self.graph_join(values)
            }
            TypedExprKind::Resume(resume) => {
                self.project_graph_expr(&resume.value, env, current_fn, program)
            }
            TypedExprKind::Declassify(declassify) => {
                let value = self.project_graph_expr(&declassify.value, env, current_fn, program)?;
                self.project_graph_expr(&declassify.cap, env, current_fn, program)?;
                self.graph_release(value, Label::Public, 1)
            }
            TypedExprKind::DeclassifyCt(declassify) => {
                let value = self.project_graph_expr(&declassify.value, env, current_fn, program)?;
                self.project_graph_expr(&declassify.cap, env, current_fn, program)?;
                self.graph_release(value, Label::Secret, 2)
            }
            TypedExprKind::ExternCall(call) => {
                let args = self.project_graph_exprs(&call.args, env, current_fn, program)?;
                for arg in &args {
                    self.graph_ct_use(*arg, env.pc, 27)?;
                    self.graph_sink(*arg, env.pc, Label::Internal, 27)?;
                }
                let result = self.graph_seed(Label::Internal)?;
                self.graph_join(args.into_iter().chain([result]))
            }
            TypedExprKind::Region(region) => {
                let limit = self.project_graph_expr(&region.limit, env, current_fn, program)?;
                self.graph_ct_use(limit, env.pc, 29)?;
                Ok(self
                    .project_graph_block(&region.body, env, current_fn, program)?
                    .0
                    .unwrap_or(0))
            }
            TypedExprKind::IndirectCall(call) => {
                let callee = env.lookup(&call.callee_local);
                let args = self.project_graph_exprs(&call.args, env, current_fn, program)?;
                for arg in &args {
                    self.graph_sink(*arg, env.pc, Label::Public, 1)?;
                }
                self.graph_join(args.into_iter().chain([callee]))
            }
            TypedExprKind::FString(string) => {
                let mut holes = Vec::new();
                for part in &string.parts {
                    if let TypedFStringPart::Hole(hole) = part {
                        holes.push(self.project_graph_expr(hole, env, current_fn, program)?);
                    }
                }
                self.graph_join(holes)
            }
        }
    }

    fn graph_actor_payload(
        &mut self,
        program: &TypedProgram,
        actor: &str,
        handler: Option<&str>,
        args: &[u32],
        pc: u32,
    ) -> Result<(), String> {
        let target = program
            .modules
            .iter()
            .flat_map(|module| &module.functions)
            .find(|function| match (&function.kind, handler) {
                (
                    crate::typed_ast::TypedFunctionKind::ActorHandler {
                        actor: candidate_actor,
                        handler: candidate_handler,
                        ..
                    },
                    Some(handler),
                ) => candidate_actor == actor && candidate_handler == handler,
                (
                    crate::typed_ast::TypedFunctionKind::ActorInit {
                        actor: candidate_actor,
                        ..
                    },
                    None,
                ) => candidate_actor == actor,
                _ => false,
            })
            .ok_or_else(|| match handler {
                Some(handler) => format!("typed actor handler `{actor}.{handler}` was not found"),
                None => format!("typed actor initializer `{actor}` was not found"),
            })?;
        if args.len() != target.params.len() {
            return Err(format!(
                "typed actor boundary `{actor}` has {} arguments but {} parameters",
                args.len(),
                target.params.len()
            ));
        }
        for (arg, param) in args.iter().zip(&target.params) {
            self.graph_ct_use(*arg, pc, 28)?;
            self.graph_sink(*arg, pc, param.taint.into(), 28)?;
        }
        Ok(())
    }
}

fn graph_find_function<'a>(
    program: &'a TypedProgram,
    name: &str,
) -> Result<&'a crate::typed_ast::TypedFunction, String> {
    program
        .modules
        .iter()
        .flat_map(|module| &module.functions)
        .find(|function| function.name == name)
        .ok_or_else(|| format!("typed call target `{name}` was not found"))
}

fn graph_place_root_local(place: &TypedExpr) -> Option<&str> {
    match &place.kind {
        TypedExprKind::Local(name) => Some(name),
        TypedExprKind::FieldAccess(field) => graph_place_root_local(&field.object),
        TypedExprKind::Index(index) => graph_place_root_local(&index.array),
        _ => None,
    }
}

fn graph_place_root_state(place: &TypedExpr) -> Option<&str> {
    match &place.kind {
        TypedExprKind::StateField(name) => Some(name),
        TypedExprKind::FieldAccess(field) => graph_place_root_state(&field.object),
        TypedExprKind::Index(index) => graph_place_root_state(&index.array),
        _ => None,
    }
}

fn graph_bind_pattern(pattern: &crate::typed_ast::TypedPattern, cell: u32, env: &mut GraphEnv) {
    use crate::typed_ast::TypedPattern;
    match pattern {
        TypedPattern::Binding(name) => {
            env.bindings.insert(name.clone(), cell);
        }
        TypedPattern::EnumVariant { bindings, .. } => {
            for (name, _) in bindings {
                env.bindings.insert(name.clone(), cell);
            }
        }
        TypedPattern::Array {
            elem_binds, rest, ..
        } => {
            for (name, _) in elem_binds {
                if let Some(name) = name {
                    env.bindings.insert(name.clone(), cell);
                }
            }
            if let Some((Some(name), _)) = rest {
                env.bindings.insert(name.clone(), cell);
            }
        }
        TypedPattern::Literal(_) | TypedPattern::Range { .. } | TypedPattern::Wildcard => {}
    }
}

fn graph_restore_pattern(
    pattern: &crate::typed_ast::TypedPattern,
    pre: &GraphEnv,
    env: &mut GraphEnv,
) {
    let mut names: Vec<&str> = Vec::new();
    match pattern {
        crate::typed_ast::TypedPattern::Binding(name) => names.push(name),
        crate::typed_ast::TypedPattern::EnumVariant { bindings, .. } => {
            names.extend(bindings.iter().map(|(name, _)| name.as_str()));
        }
        crate::typed_ast::TypedPattern::Array {
            elem_binds, rest, ..
        } => {
            names.extend(elem_binds.iter().filter_map(|(name, _)| name.as_deref()));
            if let Some((Some(name), _)) = rest {
                names.push(name);
            }
        }
        crate::typed_ast::TypedPattern::Literal(_)
        | crate::typed_ast::TypedPattern::Range { .. }
        | crate::typed_ast::TypedPattern::Wildcard => {}
    }
    for name in names {
        match pre.bindings.get(name).copied() {
            Some(cell) => {
                env.bindings.insert(name.to_owned(), cell);
            }
            None => {
                env.bindings.remove(name);
            }
        }
        match pre.contracts.get(name).copied() {
            Some(label) => {
                env.contracts.insert(name.to_owned(), label);
            }
            None => {
                env.contracts.remove(name);
            }
        }
    }
}

fn capability_pattern_names(pattern: &crate::typed_ast::TypedPattern) -> Vec<&str> {
    match pattern {
        crate::typed_ast::TypedPattern::Binding(name) => vec![name],
        crate::typed_ast::TypedPattern::EnumVariant { bindings, .. } => {
            bindings.iter().map(|(name, _)| name.as_str()).collect()
        }
        crate::typed_ast::TypedPattern::Array {
            elem_binds, rest, ..
        } => {
            let mut names: Vec<&str> = elem_binds
                .iter()
                .filter_map(|(name, _)| name.as_deref())
                .collect();
            if let Some((Some(name), _)) = rest {
                names.push(name);
            }
            names
        }
        crate::typed_ast::TypedPattern::Literal(_)
        | crate::typed_ast::TypedPattern::Range { .. }
        | crate::typed_ast::TypedPattern::Wildcard => Vec::new(),
    }
}

fn capability_bind_pattern(pattern: &crate::typed_ast::TypedPattern, env: &mut CapabilityEnv) {
    for name in capability_pattern_names(pattern) {
        env.bindings.insert(name.to_owned(), CapabilityValue::Other);
    }
}

fn capability_restore_pattern(
    pattern: &crate::typed_ast::TypedPattern,
    pre: &CapabilityEnv,
    env: &mut CapabilityEnv,
) {
    for name in capability_pattern_names(pattern) {
        match pre.bindings.get(name).copied() {
            Some(value) => {
                env.bindings.insert(name.to_owned(), value);
            }
            None => {
                env.bindings.remove(name);
            }
        }
    }
}

fn cap_kind_for_name(name: &str) -> u32 {
    match name {
        "Declassify" => 1,
        "DeclassifyCT" => 2,
        _ => 0,
    }
}

fn cap_descriptor(ty: &Type, registry: &AuthorityRegistry) -> Option<(u32, u32)> {
    match ty {
        Type::Cap(name, _) => Some((cap_kind_for_name(name), registry.full_mask(name))),
        _ => None,
    }
}

fn slot_descriptor(ty: &Type, registry: &AuthorityRegistry) -> Option<(u32, u32)> {
    match ty {
        Type::Named(name, args) if name == "Slot" && args.len() == 1 => {
            cap_descriptor(&args[0], registry)
        }
        _ => None,
    }
}

impl Projector {
    fn project_capability_graph(
        &mut self,
        program: &TypedProgram,
        registry: &AuthorityRegistry,
    ) -> Result<(), String> {
        for function in program.modules.iter().flat_map(|module| &module.functions) {
            let mut env = CapabilityEnv::default();
            for param in function.params.iter().chain(&function.captures) {
                let value = if let Some((kind, ceiling)) = cap_descriptor(&param.ty, registry) {
                    CapabilityValue::Cap(self.cap_origin(kind, ceiling, 1)?)
                } else if let Some((kind, ceiling)) = slot_descriptor(&param.ty, registry) {
                    // A slot crossing a verified function boundary may be empty or full.  For
                    // authority safety, treating it as full with the type ceiling is conservative;
                    // runtime empty/full linearity remains a separate gate.
                    CapabilityValue::Slot(self.cap_slot(kind, ceiling, true)?)
                } else {
                    CapabilityValue::Other
                };
                env.bindings.insert(param.name.clone(), value);
            }
            self.project_capability_block(&function.body, &mut env, function, program, registry)?;
        }
        Ok(())
    }

    fn merge_capability_envs(
        &mut self,
        base: &CapabilityEnv,
        variants: &[CapabilityEnv],
    ) -> Result<CapabilityEnv, String> {
        let mut merged = base.clone();
        for (name, base_value) in &base.bindings {
            let mut candidates = variants.iter();
            let mut value = candidates
                .next()
                .and_then(|variant| variant.bindings.get(name).copied())
                .unwrap_or(*base_value);
            for variant in candidates {
                let candidate = variant.bindings.get(name).copied().unwrap_or(*base_value);
                value = match (value, candidate) {
                    (CapabilityValue::Cap(left), CapabilityValue::Cap(right)) => {
                        CapabilityValue::Cap(self.cap_meet(left, right)?)
                    }
                    (CapabilityValue::Slot(left), CapabilityValue::Slot(right))
                        if left == right =>
                    {
                        CapabilityValue::Slot(left)
                    }
                    (CapabilityValue::Other, CapabilityValue::Other) => CapabilityValue::Other,
                    _ => {
                        return Err(format!(
                            "capability control-flow shape mismatch for binding `{name}`"
                        ));
                    }
                };
            }
            merged.bindings.insert(name.clone(), value);
        }
        merged.diverged = false;
        Ok(merged)
    }

    fn project_capability_block(
        &mut self,
        block: &TypedBlock,
        env: &mut CapabilityEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
        registry: &AuthorityRegistry,
    ) -> Result<(), String> {
        self.project_capability_scoped_stmts(&block.statements, env, current_fn, program, registry)
    }

    fn project_capability_scoped_stmts(
        &mut self,
        statements: &[TypedStmt],
        env: &mut CapabilityEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
        registry: &AuthorityRegistry,
    ) -> Result<(), String> {
        let mut shadowed: BTreeMap<String, Option<CapabilityValue>> = BTreeMap::new();
        for statement in statements {
            if env.diverged {
                break;
            }
            if let TypedStmt::Let(stmt) = statement {
                shadowed
                    .entry(stmt.name.clone())
                    .or_insert_with(|| env.bindings.get(&stmt.name).copied());
            }
            self.project_capability_stmt(statement, env, current_fn, program, registry)?;
        }
        for (name, value) in shadowed {
            match value {
                Some(value) => {
                    env.bindings.insert(name, value);
                }
                None => {
                    env.bindings.remove(&name);
                }
            }
        }
        Ok(())
    }

    fn project_capability_stmts(
        &mut self,
        statements: &[TypedStmt],
        env: &mut CapabilityEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
        registry: &AuthorityRegistry,
    ) -> Result<(), String> {
        self.project_capability_scoped_stmts(statements, env, current_fn, program, registry)
    }

    fn project_capability_stmt(
        &mut self,
        statement: &TypedStmt,
        env: &mut CapabilityEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
        registry: &AuthorityRegistry,
    ) -> Result<(), String> {
        match statement {
            TypedStmt::Let(stmt) => {
                let value =
                    self.project_capability_expr(&stmt.value, env, current_fn, program, registry)?;
                env.bindings.insert(stmt.name.clone(), value);
            }
            TypedStmt::Assign(stmt) => {
                let value =
                    self.project_capability_expr(&stmt.value, env, current_fn, program, registry)?;
                self.project_capability_expr(&stmt.place, env, current_fn, program, registry)?;
                if let TypedExprKind::Local(name) = &stmt.place.kind {
                    env.bindings.insert(name.clone(), value);
                }
            }
            TypedStmt::Expr(stmt) => {
                self.project_capability_expr(&stmt.expr, env, current_fn, program, registry)?;
            }
            TypedStmt::If(stmt) => {
                self.project_capability_expr(&stmt.condition, env, current_fn, program, registry)?;
                if env.diverged {
                    return Ok(());
                }
                let base = env.clone();
                self.path_fork(2)?;
                let mut then_env = base.clone();
                self.project_capability_block(
                    &stmt.then_branch,
                    &mut then_env,
                    current_fn,
                    program,
                    registry,
                )?;
                self.path_arm(!then_env.diverged)?;
                let mut else_env = base.clone();
                self.project_capability_block(
                    &stmt.else_branch,
                    &mut else_env,
                    current_fn,
                    program,
                    registry,
                )?;
                self.path_join(!else_env.diverged)?;
                let all_diverge = then_env.diverged && else_env.diverged;
                let fallthrough: Vec<CapabilityEnv> = [then_env, else_env]
                    .into_iter()
                    .filter(|candidate| !candidate.diverged)
                    .collect();
                if !fallthrough.is_empty() {
                    *env = self.merge_capability_envs(&base, &fallthrough)?;
                }
                env.diverged = all_diverge;
            }
            TypedStmt::Match(stmt) => {
                self.project_capability_expr(&stmt.scrutinee, env, current_fn, program, registry)?;
                if env.diverged {
                    return Ok(());
                }
                let base = env.clone();
                let path_sensitive = stmt.arms.len() >= 2;
                if path_sensitive {
                    self.path_fork(stmt.arms.len())?;
                }
                let mut variants = Vec::with_capacity(stmt.arms.len());
                let mut all_diverge = !stmt.arms.is_empty();
                for (index, arm) in stmt.arms.iter().enumerate() {
                    let mut arm_env = base.clone();
                    capability_bind_pattern(&arm.pattern, &mut arm_env);
                    if let Some(guard) = &arm.guard {
                        self.project_capability_expr(
                            guard,
                            &mut arm_env,
                            current_fn,
                            program,
                            registry,
                        )?;
                    }
                    self.project_capability_block(
                        &arm.body,
                        &mut arm_env,
                        current_fn,
                        program,
                        registry,
                    )?;
                    capability_restore_pattern(&arm.pattern, &base, &mut arm_env);
                    all_diverge &= arm_env.diverged;
                    if path_sensitive {
                        if index + 1 == stmt.arms.len() {
                            self.path_join(!arm_env.diverged)?;
                        } else {
                            self.path_arm(!arm_env.diverged)?;
                        }
                    }
                    if !arm_env.diverged {
                        variants.push(arm_env);
                    }
                }
                if !variants.is_empty() {
                    *env = self.merge_capability_envs(&base, &variants)?;
                }
                env.diverged = all_diverge;
            }
            TypedStmt::While(stmt) => {
                self.path_loop()?;
                let outer_loop_depth = env.loop_depth;
                env.loop_depth += 1;
                self.project_capability_expr(&stmt.condition, env, current_fn, program, registry)?;
                if env.diverged {
                    self.path_loop_join()?;
                    env.loop_depth = outer_loop_depth;
                    return Ok(());
                }
                // The condition is evaluated at every visit to the loop head.  It therefore
                // must preserve every capability live before the first evaluation.
                self.path_back()?;
                let base = env.clone();
                let mut body = base.clone();
                self.project_capability_block(
                    &stmt.body, &mut body, current_fn, program, registry,
                )?;
                if !body.diverged {
                    self.path_back()?;
                }
                self.path_loop_join()?;
                *env = self.merge_capability_envs(&base, &[base.clone(), body])?;
                env.diverged = false;
                env.loop_depth = outer_loop_depth;
            }
            TypedStmt::ForIn(stmt) => {
                self.project_capability_expr(&stmt.iterable, env, current_fn, program, registry)?;
                if env.diverged {
                    return Ok(());
                }
                self.path_loop()?;
                let outer_loop_depth = env.loop_depth;
                let base = env.clone();
                let mut body = base.clone();
                body.loop_depth += 1;
                let prior_loop_var = body.bindings.get(&stmt.var).copied();
                body.bindings
                    .insert(stmt.var.clone(), CapabilityValue::Other);
                self.project_capability_stmts(
                    &stmt.body, &mut body, current_fn, program, registry,
                )?;
                match prior_loop_var {
                    Some(value) => {
                        body.bindings.insert(stmt.var.clone(), value);
                    }
                    None => {
                        body.bindings.remove(&stmt.var);
                    }
                }
                if !body.diverged {
                    self.path_back()?;
                }
                self.path_loop_join()?;
                *env = self.merge_capability_envs(&base, &[base.clone(), body])?;
                env.diverged = false;
                env.loop_depth = outer_loop_depth;
            }
            TypedStmt::ForRange(stmt) => {
                self.project_capability_expr(&stmt.start, env, current_fn, program, registry)?;
                self.project_capability_expr(&stmt.end, env, current_fn, program, registry)?;
                if env.diverged {
                    return Ok(());
                }
                self.path_loop()?;
                let outer_loop_depth = env.loop_depth;
                let base = env.clone();
                let mut body = base.clone();
                body.loop_depth += 1;
                let prior_loop_var = body.bindings.get(&stmt.var).copied();
                body.bindings
                    .insert(stmt.var.clone(), CapabilityValue::Other);
                self.project_capability_stmts(
                    &stmt.body, &mut body, current_fn, program, registry,
                )?;
                match prior_loop_var {
                    Some(value) => {
                        body.bindings.insert(stmt.var.clone(), value);
                    }
                    None => {
                        body.bindings.remove(&stmt.var);
                    }
                }
                if !body.diverged {
                    self.path_back()?;
                }
                self.path_loop_join()?;
                *env = self.merge_capability_envs(&base, &[base.clone(), body])?;
                env.diverged = false;
                env.loop_depth = outer_loop_depth;
            }
            TypedStmt::Return(stmt) => {
                if let Some(expr) = &stmt.value {
                    let value =
                        self.project_capability_expr(expr, env, current_fn, program, registry)?;
                    if let CapabilityValue::Cap(cap) = value {
                        let (_, required) =
                            cap_descriptor(&current_fn.ret, registry).ok_or_else(|| {
                                "capability return value has a non-capability function contract"
                                    .to_owned()
                            })?;
                        self.cap_sink(cap, required, 4)?;
                    }
                }
                env.diverged = true;
            }
            TypedStmt::Break(_) => {
                if env.loop_depth == 0 {
                    return Err("break escaped type checking without an enclosing loop".to_owned());
                }
                self.path_break()?;
                env.diverged = true;
            }
            TypedStmt::Continue(_) => {
                if env.loop_depth == 0 {
                    return Err(
                        "continue escaped type checking without an enclosing loop".to_owned()
                    );
                }
                self.path_back()?;
                env.diverged = true;
            }
        }
        Ok(())
    }

    fn project_capability_args(
        &mut self,
        args: &[TypedExpr],
        env: &mut CapabilityEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
        registry: &AuthorityRegistry,
        sink_class: u32,
    ) -> Result<(), String> {
        for arg in args {
            let value = self.project_capability_expr(arg, env, current_fn, program, registry)?;
            if let CapabilityValue::Cap(cap) = value
                && let Some((_, required)) = cap_descriptor(&arg.ty, registry)
            {
                self.cap_sink(cap, required, sink_class)?;
            }
        }
        Ok(())
    }

    fn boundary_capability_result(
        &mut self,
        ty: &Type,
        registry: &AuthorityRegistry,
    ) -> Result<CapabilityValue, String> {
        if let Some((kind, ceiling)) = cap_descriptor(ty, registry) {
            Ok(CapabilityValue::Cap(self.cap_origin(kind, ceiling, 4)?))
        } else if let Some((kind, ceiling)) = slot_descriptor(ty, registry) {
            Ok(CapabilityValue::Slot(self.cap_slot(kind, ceiling, true)?))
        } else {
            Ok(CapabilityValue::Other)
        }
    }

    #[allow(clippy::too_many_lines)]
    fn project_capability_expr(
        &mut self,
        expression: &TypedExpr,
        env: &mut CapabilityEnv,
        current_fn: &crate::typed_ast::TypedFunction,
        program: &TypedProgram,
        registry: &AuthorityRegistry,
    ) -> Result<CapabilityValue, String> {
        match &expression.kind {
            TypedExprKind::Literal(_) => Ok(CapabilityValue::Other),
            TypedExprKind::Local(name) => Ok(env
                .bindings
                .get(name)
                .copied()
                .unwrap_or(CapabilityValue::Other)),
            TypedExprKind::StateField(name) => {
                if let Some(value) = env.bindings.get(name).copied() {
                    Ok(value)
                } else if let Some((kind, ceiling)) = cap_descriptor(&expression.ty, registry) {
                    Ok(CapabilityValue::Cap(self.cap_origin(kind, ceiling, 2)?))
                } else if let Some((kind, ceiling)) = slot_descriptor(&expression.ty, registry) {
                    Ok(CapabilityValue::Slot(self.cap_slot(kind, ceiling, true)?))
                } else {
                    Ok(CapabilityValue::Other)
                }
            }
            TypedExprKind::Call(call) => {
                self.project_capability_args(&call.args, env, current_fn, program, registry, 1)?;
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::IndirectCall(call) => {
                self.project_capability_args(&call.args, env, current_fn, program, registry, 1)?;
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::Intrinsic(intrinsic) => match &intrinsic.kind {
                TypedIntrinsicKind::SlotNew { cap_type } => {
                    let kind = cap_kind_for_name(cap_type);
                    Ok(CapabilityValue::Slot(self.cap_slot(
                        kind,
                        registry.full_mask(cap_type),
                        false,
                    )?))
                }
                TypedIntrinsicKind::SlotPut => {
                    if intrinsic.args.len() != 2 {
                        return Err("slot_put arity changed after type checking".to_owned());
                    }
                    let slot = self.project_capability_expr(
                        &intrinsic.args[0],
                        env,
                        current_fn,
                        program,
                        registry,
                    )?;
                    let cap = self.project_capability_expr(
                        &intrinsic.args[1],
                        env,
                        current_fn,
                        program,
                        registry,
                    )?;
                    match (slot, cap) {
                        (CapabilityValue::Slot(slot), CapabilityValue::Cap(cap)) => {
                            self.cap_slot_put(slot, cap)?;
                            Ok(CapabilityValue::Other)
                        }
                        _ => Err("slot_put lost its typed slot/capability operands".to_owned()),
                    }
                }
                TypedIntrinsicKind::SlotTake => {
                    if intrinsic.args.len() != 1 {
                        return Err("slot_take arity changed after type checking".to_owned());
                    }
                    match self.project_capability_expr(
                        &intrinsic.args[0],
                        env,
                        current_fn,
                        program,
                        registry,
                    )? {
                        CapabilityValue::Slot(slot) => {
                            Ok(CapabilityValue::Cap(self.cap_slot_take(slot)?))
                        }
                        _ => Err("slot_take lost its typed slot operand".to_owned()),
                    }
                }
                TypedIntrinsicKind::Trap => {
                    self.project_capability_args(
                        &intrinsic.args,
                        env,
                        current_fn,
                        program,
                        registry,
                        5,
                    )?;
                    env.diverged = true;
                    Ok(CapabilityValue::Other)
                }
                _ => {
                    self.project_capability_args(
                        &intrinsic.args,
                        env,
                        current_fn,
                        program,
                        registry,
                        5,
                    )?;
                    self.boundary_capability_result(&expression.ty, registry)
                }
            },
            TypedExprKind::ResultCtor(ctor) => {
                self.project_capability_expr(&ctor.value, env, current_fn, program, registry)
            }
            TypedExprKind::EnumConstruct(ctor) => {
                self.project_capability_args(&ctor.fields, env, current_fn, program, registry, 6)?;
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::Try(inner) => {
                self.project_capability_expr(&inner.value, env, current_fn, program, registry)
            }
            TypedExprKind::Send(send) => {
                self.project_capability_args(&send.args, env, current_fn, program, registry, 2)?;
                Ok(CapabilityValue::Other)
            }
            TypedExprKind::Ask(ask) => {
                self.project_capability_args(&ask.args, env, current_fn, program, registry, 2)?;
                self.project_capability_expr(&ask.timeout, env, current_fn, program, registry)?;
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::Spawn(spawn) => {
                self.project_capability_args(&spawn.args, env, current_fn, program, registry, 3)?;
                Ok(CapabilityValue::Other)
            }
            TypedExprKind::Binary(binary) => {
                self.project_capability_expr(&binary.lhs, env, current_fn, program, registry)?;
                self.project_capability_expr(&binary.rhs, env, current_fn, program, registry)?;
                Ok(CapabilityValue::Other)
            }
            TypedExprKind::RecordConstruct(record) => {
                for (_, field) in &record.fields {
                    self.project_capability_expr(field, env, current_fn, program, registry)?;
                }
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::FieldAccess(field) => {
                self.project_capability_expr(&field.object, env, current_fn, program, registry)?;
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::CapRestrict(restrict) => {
                let source = match env.bindings.get(&restrict.cap).copied() {
                    Some(CapabilityValue::Cap(cap)) => cap,
                    _ => {
                        return Err(format!(
                            "capability restriction source `{}` has no derived origin",
                            restrict.cap
                        ));
                    }
                };
                Ok(CapabilityValue::Cap(
                    self.cap_restrict(source, restrict.restriction_mask)?,
                ))
            }
            TypedExprKind::CapSplit(split) => {
                self.project_capability_expr(&split.amount, env, current_fn, program, registry)?;
                let amount = self.int_cell(&split.amount)?;
                let source = match env.bindings.get(&split.cap).copied() {
                    Some(CapabilityValue::Cap(cap)) => cap,
                    _ => {
                        return Err(format!(
                            "capability split source `{}` has no derived origin",
                            split.cap
                        ));
                    }
                };
                let child = self.cap_derive(Op::CapSplit, source)?;
                self.quantity_use(Op::CapSplit, source, child, amount)?;
                Ok(CapabilityValue::Cap(child))
            }
            TypedExprKind::CapDraw(draw) => {
                self.project_capability_expr(&draw.amount, env, current_fn, program, registry)?;
                let amount = self.int_cell(&draw.amount)?;
                let source = match env.bindings.get(&draw.cap).copied() {
                    Some(CapabilityValue::Cap(cap)) => cap,
                    _ => {
                        return Err(format!(
                            "capability draw source `{}` has no derived origin",
                            draw.cap
                        ));
                    }
                };
                let child = self.cap_derive(Op::CapDraw, source)?;
                self.quantity_use(Op::CapDraw, source, child, amount)?;
                Ok(CapabilityValue::Cap(child))
            }
            TypedExprKind::Mint(mint) => {
                self.project_capability_expr(&mint.target, env, current_fn, program, registry)?;
                let (kind, ceiling) = cap_descriptor(&expression.ty, registry)
                    .ok_or_else(|| "mint produced a non-capability typed value".to_owned())?;
                Ok(CapabilityValue::Cap(self.cap_origin(kind, ceiling, 3)?))
            }
            TypedExprKind::ArrayLit(array) => {
                for element in &array.elements {
                    self.project_capability_expr(element, env, current_fn, program, registry)?;
                }
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::Index(index) => {
                self.project_capability_expr(&index.array, env, current_fn, program, registry)?;
                self.project_capability_expr(&index.index, env, current_fn, program, registry)?;
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::Slice(slice) => {
                self.project_capability_expr(&slice.array, env, current_fn, program, registry)?;
                if let Some(start) = &slice.start {
                    self.project_capability_expr(start, env, current_fn, program, registry)?;
                }
                if let Some(end) = &slice.end {
                    self.project_capability_expr(end, env, current_fn, program, registry)?;
                }
                Ok(CapabilityValue::Other)
            }
            TypedExprKind::ClosureConstruct(closure) => {
                for capture in &closure.captures {
                    if let Some(CapabilityValue::Cap(cap)) =
                        env.bindings.get(&capture.name).copied()
                    {
                        self.cap_sink(cap, cap.ceiling, 7)?;
                    }
                }
                Ok(CapabilityValue::Other)
            }
            TypedExprKind::Borrow(borrow) => {
                self.project_capability_expr(&borrow.inner, env, current_fn, program, registry)
            }
            TypedExprKind::Grant(grant) => {
                self.project_capability_expr(&grant.cap, env, current_fn, program, registry)?;
                self.project_capability_expr(&grant.body, env, current_fn, program, registry)
            }
            TypedExprKind::Handle(handle) => {
                self.project_capability_block(&handle.body, env, current_fn, program, registry)?;
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::Perform(perform) => {
                self.project_capability_args(&perform.args, env, current_fn, program, registry, 8)?;
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::ClauseHandle(handle) => {
                self.project_capability_expr(
                    &handle.scrutinee,
                    env,
                    current_fn,
                    program,
                    registry,
                )?;
                let base = env.clone();
                let mut variants = Vec::with_capacity(handle.clauses.len());
                for clause in &handle.clauses {
                    let mut clause_env = base.clone();
                    self.project_capability_block(
                        &clause.body,
                        &mut clause_env,
                        current_fn,
                        program,
                        registry,
                    )?;
                    variants.push(clause_env);
                }
                variants.insert(0, base.clone());
                *env = self.merge_capability_envs(&base, &variants)?;
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::Resume(resume) => {
                self.project_capability_expr(&resume.value, env, current_fn, program, registry)
            }
            TypedExprKind::Declassify(declassify) => {
                self.project_capability_expr(
                    &declassify.value,
                    env,
                    current_fn,
                    program,
                    registry,
                )?;
                match self.project_capability_expr(
                    &declassify.cap,
                    env,
                    current_fn,
                    program,
                    registry,
                )? {
                    CapabilityValue::Cap(cap) => self.cap_release(cap, cap.ceiling)?,
                    _ => return Err("ordinary declassification lost its capability".to_owned()),
                }
                Ok(CapabilityValue::Other)
            }
            TypedExprKind::DeclassifyCt(declassify) => {
                self.project_capability_expr(
                    &declassify.value,
                    env,
                    current_fn,
                    program,
                    registry,
                )?;
                match self.project_capability_expr(
                    &declassify.cap,
                    env,
                    current_fn,
                    program,
                    registry,
                )? {
                    CapabilityValue::Cap(cap) => self.cap_release(cap, cap.ceiling)?,
                    _ => return Err("CT declassification lost its capability".to_owned()),
                }
                Ok(CapabilityValue::Other)
            }
            TypedExprKind::ExternCall(call) => {
                self.project_capability_args(&call.args, env, current_fn, program, registry, 9)?;
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::Region(region) => {
                self.project_capability_expr(&region.limit, env, current_fn, program, registry)?;
                self.project_capability_block(&region.body, env, current_fn, program, registry)?;
                self.boundary_capability_result(&expression.ty, registry)
            }
            TypedExprKind::FString(string) => {
                for part in &string.parts {
                    if let TypedFStringPart::Hole(hole) = part {
                        self.project_capability_expr(hole, env, current_fn, program, registry)?;
                    }
                }
                Ok(CapabilityValue::Other)
            }
        }
    }
}

fn encode(nodes: &[Node]) -> Result<Vec<u8>, String> {
    let encoded_node_count = nodes.len();
    if encoded_node_count > MAX_NODES {
        return Err(format!(
            "CSIR projection exceeds the {MAX_NODES}-node ceiling"
        ));
    }
    let capacity = HEADER_BYTES
        .checked_add(
            encoded_node_count
                .checked_mul(NODE_BYTES)
                .ok_or("CSIR size overflow")?,
        )
        .ok_or("CSIR size overflow")?;
    if capacity > MAX_WIRE_BYTES {
        return Err(format!(
            "CSIR projection exceeds the {MAX_WIRE_BYTES}-byte ceiling"
        ));
    }
    let count = u32::try_from(encoded_node_count).map_err(|_| "CSIR node count overflow")?;
    let mut bytes = Vec::with_capacity(capacity);
    bytes.extend_from_slice(b"CSIR");
    // V9 is an envelope around an exact historical-v8 prefix. The outer encoder rewrites the
    // final framing to 9 only after it has validated and copied this complete prefix.
    bytes.extend_from_slice(&RETAINED_V8_PREFIX_VERSION.to_le_bytes());
    bytes.extend_from_slice(&count.to_le_bytes());
    for node in nodes {
        bytes.extend_from_slice(&[
            node.op as u8,
            node.label_a as u8,
            node.label_b as u8,
            node.flags,
        ]);
        for word in [
            node.origin,
            node.actual,
            node.required,
            node.ceiling,
            node.aux,
            node.node_id,
            0,
        ] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
    }
    debug_assert_eq!(bytes.len(), capacity);
    Ok(bytes)
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut result = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        write!(&mut result, "{byte:02x}").expect("writing to String cannot fail");
    }
    result
}

fn checker_source_fingerprint() -> String {
    fingerprint_checker_sources(&CHECKER_EVIDENCE_SOURCES)
}

fn fingerprint_checker_sources(sources: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    for source in sources {
        hasher.update((source.len() as u64).to_le_bytes());
        hasher.update(source);
    }
    format!("{:x}", hasher.finalize())
}

fn internal_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic::error(codes::I013, message, Some(Span::default()))
}

fn internal_error_at(message: impl Into<String>, span: Span) -> Diagnostic {
    Diagnostic::error(codes::I013, message, Some(span))
}

/// Project complete occurrence declarations without approving the program.
///
/// This API supplies bytes for decoder parity and the production v9 verifier. It
/// never constructs evidence or bypasses `verify_with_context`'s authorization
/// fence. Current exposed roots receive Public occurrence defaults; return
/// payload labels never declare a private root. No private actor endpoint is
/// inferred from an actor name, type, message payload, or return annotation.
/// Per-instantiation projection of taint-polymorphic (`@Flow`) functions.
///
/// The v8 semantic kernel seeds a `@Flow` contract at `@Secret`, so a direct call from Public or
/// Internal code would receive a Secret result and fail its own contract. The type checker earns
/// polymorphism by re-checking each `@Flow` body once per admissible label; this pass makes the
/// projection say the same thing. For every instantiation label a call site actually resolved to
/// (recorded by `taint_check::flow_call_instantiations`), the callee is projected as one more
/// function whose `@Flow` contracts are the concrete label, and the call is routed to it. Every
/// clone is an ordinary function to the kernel: its parameter contracts refuse an argument above
/// the instantiation, its return contract refuses a body that launders, and its `$`-prefixed
/// export name makes it an internal root. Nothing here is a computed verdict; a site the recorder
/// does not know keeps the `@Secret`-seeded original, which can only over-taint, and the original
/// stays the exported function with its declared `@Flow` contracts.
///
/// Scope: a `@Flow` function that constructs a closure is left uninstantiated (its closures would
/// need the same treatment), so its callers keep today's conservative verdict.
fn instantiate_flow_functions<'a>(
    program: &TypedProgram,
    air: &'a AirProgram,
) -> Result<Cow<'a, AirProgram>, String> {
    fn has_flow_contract(function: &AirFunction) -> bool {
        matches!(function.security.return_contract, AirLabelContract::Flow)
            || function
                .security
                .value_contracts
                .values()
                .any(|contract| matches!(contract, AirLabelContract::Flow))
    }
    fn constructs_closures(function: &AirFunction) -> bool {
        function
            .debug_names
            .values()
            .any(|name| name == "__closure_id")
    }
    fn instance_tag(label: TaintLabel) -> Result<&'static str, String> {
        match label {
            TaintLabel::Public => Ok("pub"),
            TaintLabel::Internal => Ok("internal"),
            other => Err(format!(
                "@Flow instantiation at @{other:?} has no projected instance"
            )),
        }
    }

    let targets = air
        .functions
        .iter()
        .enumerate()
        .filter(|(_, function)| has_flow_contract(function) && !constructs_closures(function))
        .map(|(index, _)| index)
        .collect::<BTreeSet<_>>();
    if targets.is_empty() {
        return Ok(Cow::Borrowed(air));
    }
    let sites = crate::taint_check::flow_call_instantiations(program);
    let pristine = air.functions.clone();
    let mut functions = air.functions.clone();
    let mut instances = BTreeMap::<(usize, TaintLabel), FuncId>::new();
    // (function to route, the `@Flow` instantiation context its calls were recorded under)
    let mut pending = (0..pristine.len())
        .map(|index| {
            let context = targets
                .contains(&index)
                .then(|| (pristine[index].name.clone(), TaintLabel::Secret));
            (index, context)
        })
        .collect::<Vec<_>>();
    while let Some((index, context)) = pending.pop() {
        // Gather first: the routing below may append clones to `functions`.
        let mut routed = Vec::new();
        {
            let function = &functions[index];
            for block in &function.blocks {
                for (position, statement) in block.stmts.iter().enumerate() {
                    let AirStmt::Call { func, .. } = statement else {
                        continue;
                    };
                    let callee = usize::try_from(func.0).map_err(|_| "callee id exceeds usize")?;
                    if !targets.contains(&callee) {
                        continue;
                    }
                    let stmt_index =
                        u32::try_from(position).map_err(|_| "statement index exceeds u32")?;
                    let Some(span) = function
                        .security
                        .statement_spans
                        .get(&(block.id, stmt_index))
                    else {
                        continue;
                    };
                    let recorded = sites.label(
                        context
                            .as_ref()
                            .map(|(name, label)| (name.as_str(), *label)),
                        *span,
                    );
                    let Some(label) = recorded else { continue };
                    if label == TaintLabel::Secret {
                        continue;
                    }
                    routed.push((block.id, position, callee, label));
                }
            }
        }
        let mut edits = Vec::new();
        for (block_id, position, callee, label) in routed {
            let tag = instance_tag(label)?;
            let target = match instances.get(&(callee, label)) {
                Some(target) => *target,
                None => {
                    let original = &pristine[callee];
                    let mut clone = original.clone();
                    clone.name = format!("{}$flow${tag}", original.name);
                    clone.export_name = format!("${}$flow${tag}", original.export_name);
                    clone.security.externally_callable = false;
                    for contract in clone.security.value_contracts.values_mut() {
                        if matches!(contract, AirLabelContract::Flow) {
                            *contract = AirLabelContract::Concrete(label);
                        }
                    }
                    if matches!(clone.security.return_contract, AirLabelContract::Flow) {
                        clone.security.return_contract = AirLabelContract::Concrete(label);
                    }
                    let id = FuncId(
                        u32::try_from(functions.len())
                            .map_err(|_| "instantiated function count exceeds u32")?,
                    );
                    functions.push(clone);
                    instances.insert((callee, label), id);
                    pending.push((functions.len() - 1, Some((original.name.clone(), label))));
                    id
                }
            };
            edits.push((block_id, position, target));
        }
        for (block_id, position, target) in edits {
            let block = functions[index]
                .blocks
                .iter_mut()
                .find(|block| block.id == block_id)
                .ok_or("edited block vanished")?;
            if let AirStmt::Call { func, .. } = &mut block.stmts[position] {
                *func = target;
            }
        }
    }
    if instances.is_empty() {
        return Ok(Cow::Borrowed(air));
    }
    Ok(Cow::Owned(AirProgram { functions }))
}

pub fn project_v9_declarations(
    program: &TypedProgram,
    air: &AirProgram,
    authority_registry: &AuthorityRegistry,
    context: &crate::compiler_context::CompilerContext,
) -> Result<Vec<u8>, String> {
    let air = instantiate_flow_functions(program, air)?;
    let mut projector = Projector::default();
    projector.project_program(program, authority_registry)?;
    projector.project_semantic_program(&air, authority_registry)?;
    project_v9_from_projector(&mut projector, &air, context)
}

fn project_v9_from_projector(
    projector: &mut Projector,
    air: &AirProgram,
    context: &crate::compiler_context::CompilerContext,
) -> Result<Vec<u8>, String> {
    use crate::formal_v9::{self, FunctionRootContract};
    use sigil_abi::host_contract::SecurityLabel;
    let base = encode(&projector.nodes)?;
    let mut roots = Vec::with_capacity(air.functions.len());
    for (position, function) in air.functions.iter().enumerate() {
        let mut actor_count = 0;
        for block in &function.blocks {
            for (index, statement) in block.stmts.iter().enumerate() {
                let operation = statement.actor_operation();
                let recorded = function
                    .security
                    .actor_operations
                    .get(&(block.id, semantic_len(index, "actor statement")?))
                    .copied();
                if operation != recorded {
                    return Err(
                        "v9 actor metadata does not match the actual AIR instruction".into(),
                    );
                }
                actor_count += usize::from(operation.is_some());
            }
        }
        if actor_count != function.security.actor_operations.len() {
            return Err("v9 actor metadata contains an unowned instruction".into());
        }
        let internal = !function.security.externally_callable
            || matches!(function.kind, AirFunctionKind::Closure)
            || function.export_name.starts_with('$');
        let (actor_type, handler_id, is_entry) = if internal {
            (0, 0, false)
        } else {
            match &function.kind {
                AirFunctionKind::ActorInit {
                    actor_type,
                    is_entry,
                    ..
                } => (actor_type.0, 0, *is_entry),
                AirFunctionKind::ActorHandler {
                    actor_type,
                    handler_id,
                    is_entry,
                    ..
                } => (actor_type.0, handler_id.0, *is_entry),
                AirFunctionKind::ModuleInit
                | AirFunctionKind::ModuleFunction
                | AirFunctionKind::Closure => (0, 0, false),
            }
        };
        roots.push(FunctionRootContract {
            function_id: semantic_len(position + 1, "root function")?,
            role: if internal {
                0
            } else {
                air_function_kind_code(&function.kind) + 1
            },
            actor_type,
            handler_id,
            is_entry,
            export_name: function.export_name.clone(),
            entry_occurrence: SecurityLabel::Public,
            return_occurrence: SecurityLabel::Public,
        });
    }
    let legacy = formal_v9::encode(
        &base,
        None,
        &projector.occurrence_ffi,
        &projector.occurrence_actors,
        &roots,
    )
    .map_err(|error| error.to_string())?;
    let Some(profile) = context.host_profile() else {
        return Ok(legacy);
    };
    let decoded = formal_v9::decode(&legacy).map_err(|error| error.to_string())?;
    for (binding, identity) in projector
        .occurrence_ffi
        .iter_mut()
        .zip(decoded.foreign_identities)
    {
        context
            .resolve_extern(&identity.name, &identity.params, &identity.results)
            .map_err(|error| error.to_string())?;
        let index = profile
            .operations()
            .binary_search_by(|operation| {
                (operation.module.as_str(), operation.name.as_str())
                    .cmp(&("ffi", identity.name.as_str()))
            })
            .map_err(|_| "resolved host operation is absent from its canonical profile")?;
        binding.profile_operation = semantic_len(index + 1, "host operation")?;
    }
    formal_v9::encode(
        &base,
        Some(profile),
        &projector.occurrence_ffi,
        &projector.occurrence_actors,
        &roots,
    )
    .map_err(|error| error.to_string())
}

/// Project the resolved typed program, call the linked Lean verifier, and
/// construct evidence only after a zero verdict.
pub fn verify(
    program: &TypedProgram,
    air: &AirProgram,
    authority_registry: &AuthorityRegistry,
) -> Result<FormalSecurityReport, Vec<Diagnostic>> {
    verify_with_context(
        program,
        air,
        authority_registry,
        &crate::compiler_context::CompilerContext::default(),
    )
}

/// Verify against the embedding's immutable declaration context. The production v9 verdict
/// re-verifies the exact v8 prefix before enforcing occurrence-aware boundary ceilings; decoding
/// or hashing declarations alone can never authorize a program.
pub fn verify_with_context(
    program: &TypedProgram,
    air: &AirProgram,
    authority_registry: &AuthorityRegistry,
    context: &crate::compiler_context::CompilerContext,
) -> Result<FormalSecurityReport, Vec<Diagnostic>> {
    let air = instantiate_flow_functions(program, air).map_err(|error| {
        vec![internal_error(format!(
            "formal @Flow instantiation failed: {error}"
        ))]
    })?;
    let mut projector = Projector::default();
    projector
        .project_program(program, authority_registry)
        .map_err(|error| {
            vec![internal_error(format!(
                "formal CSIR projection failed: {error}"
            ))]
        })?;
    projector
        .project_semantic_program(&air, authority_registry)
        .map_err(|error| {
            vec![internal_error(format!(
                "formal semantic CSIR projection failed: {error}"
            ))]
        })?;
    let bytes = project_v9_from_projector(&mut projector, &air, context).map_err(|error| {
        vec![internal_error(format!(
            "formal CSIR v9 projection failed: {error}"
        ))]
    })?;
    let checked_node_count = bytes
        .len()
        .checked_sub(HEADER_BYTES)
        .filter(|payload| payload % NODE_BYTES == 0)
        .map(|payload| payload / NODE_BYTES)
        .ok_or_else(|| {
            vec![internal_error(
                "formal CSIR v9 projection returned a noncanonical record length",
            )]
        })?;
    let verdict = sigil_formal_bridge::verify_v9(&bytes).map_err(|error| {
        vec![internal_error(format!(
            "formal Lean verifier infrastructure failure: {error}"
        ))]
    })?;
    if verdict != 0 {
        let code = verdict & 0xffff;
        let detail = (verdict >> 16) & 0xffff;
        let node_id = verdict >> 32;
        let span = u32::try_from(node_id)
            .ok()
            .and_then(|node| projector.spans.get(&node).copied())
            .unwrap_or_default();
        #[cfg(debug_assertions)]
        let component = u32::try_from(node_id)
            .ok()
            .and_then(|node| node.checked_sub(1))
            .and_then(|index| projector.nodes.get(index as usize))
            .map(|node| {
                let owner = matches!(
                    node.op,
                    Op::SemPolicyClass | Op::SemRuntimeGuard | Op::SemOperand
                )
                .then(|| node.origin.checked_sub(1))
                .flatten()
                .and_then(|index| projector.nodes.get(index as usize));
                let operands = matches!(node.op, Op::SemInstruction)
                    .then(|| {
                        let start = node.node_id as usize;
                        let end = start.saturating_add(node.ceiling as usize);
                        projector.nodes.get(start..end)
                    })
                    .flatten();
                format!(", record={node:?}, owner={owner:?}, operands={operands:?}")
            })
            .unwrap_or_default();
        #[cfg(not(debug_assertions))]
        let component = String::new();
        return Err(vec![internal_error_at(
            format!(
                "formal Lean verifier rejected compiler-produced CSIR: code={code}, detail={detail}, node={node_id}{component}"
            ),
            span,
        )]);
    }
    Ok(FormalSecurityReport {
        model_version: CSIR_MODEL_VERSION,
        lean_toolchain: LEAN_TOOLCHAIN.trim().to_owned(),
        checker_source_fingerprint: checker_source_fingerprint(),
        csir_fingerprint: sha256_hex(&bytes),
        checked_functions: projector.functions,
        checked_nodes: checked_node_count as u64,
        checked_capabilities: projector
            .nodes
            .iter()
            .filter(|node| {
                matches!(
                    node.op,
                    Op::Authority
                        | Op::Consume
                        | Op::Declassify
                        | Op::CapOrigin
                        | Op::CapRestrict
                        | Op::CapSplit
                        | Op::CapDraw
                        | Op::CapSink
                        | Op::CapRelease
                        | Op::CapSlot
                        | Op::CapSlotPut
                        | Op::CapSlotTake
                        | Op::CapMeet
                        | Op::PathFork
                        | Op::PathArm
                        | Op::PathJoin
                        | Op::PathLoop
                        | Op::PathBack
                        | Op::PathBreak
                        | Op::PathLoopJoin
                        | Op::QuantityUse
                        | Op::SemCapabilityType
                        | Op::SemRefinementFact
                        | Op::SemRuntimeGuard
                ) || matches!(node.op, Op::SemInstruction)
                    && matches!(
                        node.aux,
                        x if x == SemanticInstrOp::CapMint as u32
                            || x == SemanticInstrOp::CapRestrict as u32
                            || x == SemanticInstrOp::CapSplit as u32
                            || x == SemanticInstrOp::CapDraw as u32
                            || x == SemanticInstrOp::CapExercise as u32
                            || x == SemanticInstrOp::SlotNew as u32
                            || x == SemanticInstrOp::SlotPut as u32
                            || x == SemanticInstrOp::SlotTake as u32
                    )
            })
            .count() as u64,
        checked_flows: projector
            .nodes
            .iter()
            .filter(|node| {
                matches!(
                    node.op,
                    Op::Flow
                        | Op::Boundary
                        | Op::TaintEdge
                        | Op::TaintSink
                        | Op::SemLabelContract
                        | Op::SemPolicyClass
                )
            })
            .count() as u64,
        checked_releases: projector
            .nodes
            .iter()
            .filter(|node| {
                matches!(node.op, Op::Declassify | Op::TaintRelease | Op::CapRelease)
                    || matches!(node.op, Op::SemInstruction)
                        && matches!(
                            node.aux,
                            x if x == SemanticInstrOp::Release as u32
                                || x == SemanticInstrOp::ReleaseCt as u32
                        )
            })
            .count() as u64,
        checked_ct_operations: projector
            .nodes
            .iter()
            .filter(|node| {
                matches!(
                    node.op,
                    Op::CtUse | Op::FixedCt | Op::TaintCtUse | Op::SemPolicyClass
                ) || matches!(node.op, Op::SemInstruction)
                    && matches!(
                        node.aux,
                        x if x == SemanticInstrOp::CtEq as u32
                            || x == SemanticInstrOp::CtSelect as u32
                            || x == SemanticInstrOp::CtLt as u32
                            || x == SemanticInstrOp::Branch as u32
                            || x == SemanticInstrOp::Loop as u32
                            || x == SemanticInstrOp::Range as u32
                            || x == SemanticInstrOp::Dispatch as u32
                            || x == SemanticInstrOp::Index as u32
                            || x == SemanticInstrOp::Address as u32
                            || x == SemanticInstrOp::DivRem as u32
                            || x == SemanticInstrOp::StringCompare as u32
                    )
            })
            .count() as u64,
        verified_seal: VerifiedSeal,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const RUST_FORMAL_SOURCE: &str = include_str!("formal.rs");
    const LEAN_KERNEL_SOURCE: &str =
        include_str!("../../../proofs/lean/LambdaSigil/CombinedKernel.lean");
    const LEAN_SEMANTIC_KERNEL_SOURCE: &str =
        include_str!("../../../proofs/lean/LambdaSigil/SemanticKernel.lean");
    const LEAN_RAW_CLAIM_SURFACE_SOURCE: &str =
        include_str!("../../../proofs/lean/LambdaSigil/RawClaimSurface.lean");
    const LEAN_PUBLIC_EXECUTION_SOURCE: &str =
        include_str!("../../../proofs/lean/LambdaSigil/PublicExecutionSecurity.lean");
    const LEAN_PUBLIC_BISIMULATION_SOURCE: &str =
        include_str!("../../../proofs/lean/LambdaSigil/PublicBisimulationSecurity.lean");
    const LEAN_SEMANTIC_SOURCE: &str =
        include_str!("../../../proofs/lean/LambdaSigil/SemanticSecurity.lean");
    const LEAN_V9_INVOCATION_ANALYSIS_SOURCE: &str =
        include_str!("../../../proofs/lean/LambdaSigil/V9OccurrenceDataflowInvocation.lean");
    const LEAN_V9_OCCURRENCE_DATAFLOW_SOURCE: &str =
        include_str!("../../../proofs/lean/LambdaSigil/V9OccurrenceDataflow.lean");
    const LEAN_PRIORITY_OCCURRENCE_SOURCE: &str =
        include_str!("../../../proofs/lean/LambdaSigil/PriorityOccurrence.lean");
    const LEAN_V9_OCCURRENCE_KERNEL_SOURCE: &str =
        include_str!("../../../proofs/lean/LambdaSigil/V9OccurrenceKernel.lean");
    const NATIVE_BRIDGE_BUILD_SOURCE: &str = include_str!("../../sigil-formal-bridge/build.rs");

    #[test]
    fn checker_fingerprint_binds_every_native_v9_dependency_and_proof() {
        let expected_sources: [&[u8]; 70] = [
            include_bytes!("../../../proofs/lean/LambdaSigil/CombinedKernel.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/SemanticKernel.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/CombinedSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PrivateLeafReturnSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/SemanticSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/SemanticDataflow.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/SemanticIndexBounds.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/DecoderNodeIds.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/ReleaseSynchronization.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicRegionSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicFrameBoundSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicFrameSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicLocalSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicTraceSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicWeakAlignment.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicReleaseSynchronization.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/DecodedOccurrencePrefix.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicRegionConvergence.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicPrivateSegmentSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicMatchingSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicStepClassification.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicExecutionSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicNonpublicStepSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicMatchedProgressSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicPrivateReleaseSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicContinuationSecurity.lean"),
            include_bytes!(
                "../../../proofs/lean/LambdaSigil/PublicSameControlProgressSecurity.lean"
            ),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicReleaseProgressSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicDispatcherSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicControllerSegmentSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicPrivateInvocationSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicSyntheticReturnSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PublicBisimulationSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/RawClaimSurface.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/HostProfileKernel.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/HostProfileSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceWire.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceWireSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceRegions.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceRegionConstruction.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceTransfer.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceTransferConstruction.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/DecodedOccurrence.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/AncestorIntervals.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/IntervalEscapeChecks.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PriorityOccurrence.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceInvocation.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/RankedDecodedOccurrence.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/V9BoundaryContracts.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/V9OccurrenceDataflow.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/V9OccurrenceDataflowInvocation.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceActivation.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/V9OccurrenceKernel.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/V9OccurrenceKernelSecurity.lean"),
            include_bytes!(
                "../../../proofs/lean/LambdaSigil/V9OccurrenceDataflowInvocationSecurity.lean"
            ),
            include_bytes!("../../../proofs/lean/LambdaSigil/V9OccurrenceDataflowSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/RankedDecodedOccurrenceSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceInvocationSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/DecodedOccurrenceSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/PriorityOccurrenceSecurity.lean"),
            include_bytes!(
                "../../../proofs/lean/LambdaSigil/OccurrenceTransferConstructionSecurity.lean"
            ),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceTransferSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceRegionSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/IntervalEscapeSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/AncestorIntervalSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/V9BoundaryContractsSecurity.lean"),
            include_bytes!("../../../proofs/lean/LambdaSigil/OccurrenceReference.lean"),
            include_bytes!("../../sigil-formal-bridge/build.rs"),
            include_bytes!("../../sigil-formal-bridge/native/bridge.c"),
            include_bytes!("../../sigil-formal-bridge/src/lib.rs"),
        ];
        assert_eq!(CHECKER_EVIDENCE_SOURCES, expected_sources);
        let current = checker_source_fingerprint();
        assert_eq!(current, fingerprint_checker_sources(&expected_sources));
        for index in 0..expected_sources.len() {
            let mut changed = expected_sources[index].to_vec();
            changed.push(b' ');
            let mut candidate = expected_sources;
            candidate[index] = &changed;
            assert_ne!(
                current,
                fingerprint_checker_sources(&candidate),
                "proof dependency {index} must invalidate previously derived evidence"
            );
        }
    }

    #[test]
    fn every_fresh_native_v9_module_is_in_the_checker_fingerprint_inventory() {
        let modules = [
            "OccurrenceRegions",
            "OccurrenceRegionConstruction",
            "OccurrenceTransfer",
            "OccurrenceTransferConstruction",
            "DecodedOccurrence",
            "AncestorIntervals",
            "IntervalEscapeChecks",
            "PriorityOccurrence",
            "OccurrenceInvocation",
            "RankedDecodedOccurrence",
            "V9BoundaryContracts",
            "V9OccurrenceDataflow",
            "V9OccurrenceDataflowInvocation",
            "OccurrenceActivation",
            "V9OccurrenceKernel",
        ];
        for module in modules {
            assert!(
                NATIVE_BRIDGE_BUILD_SOURCE.contains(&format!("LambdaSigil.{module}")),
                "the native bridge must compile {module} from this source build"
            );
            assert!(
                RUST_FORMAL_SOURCE.contains(&format!("LambdaSigil/{module}.lean")),
                "the report fingerprint must bind native module {module}"
            );
        }
        assert!(
            RUST_FORMAL_SOURCE.contains("LambdaSigil/V9OccurrenceKernelSecurity.lean"),
            "the report fingerprint must also bind the executable verifier's proof"
        );
    }

    fn lean_decoder_entries(definition: &str) -> Vec<(u32, String)> {
        let marker = format!("def {definition}");
        let source = LEAN_KERNEL_SOURCE
            .split_once(&marker)
            .unwrap_or_else(|| panic!("Lean kernel is missing {definition}"))
            .1;
        let mut entries = Vec::new();
        for line in source.lines().skip(1) {
            let line = line.trim();
            if line == "| _ => none" {
                break;
            }
            let Some((code, constructor)) = line
                .strip_prefix("| ")
                .and_then(|line| line.split_once(" => some ."))
            else {
                continue;
            };
            entries.push((
                code.parse::<u32>()
                    .unwrap_or_else(|_| panic!("invalid code in Lean {definition}: {line}")),
                constructor.to_owned(),
            ));
        }
        assert!(
            !entries.is_empty(),
            "Lean decoder parser found no entries in {definition}"
        );
        entries
    }

    fn lean_source_between(start: &str, end: &str) -> &'static str {
        lean_source_between_in(LEAN_KERNEL_SOURCE, start, end)
    }

    fn lean_source_between_in(source: &'static str, start: &str, end: &str) -> &'static str {
        source
            .split_once(start)
            .unwrap_or_else(|| panic!("Lean kernel is missing `{start}`"))
            .1
            .split_once(end)
            .unwrap_or_else(|| panic!("Lean kernel is missing `{end}` after `{start}`"))
            .0
    }

    #[test]
    fn v9_public_proof_surface_is_pinned_and_fingerprint_bound() {
        for (name, source) in [
            ("PublicExecutionSecurity", PUBLIC_EXECUTION_SECURITY_SOURCE),
            (
                "PublicBisimulationSecurity",
                PUBLIC_BISIMULATION_SECURITY_SOURCE,
            ),
        ] {
            assert!(
                CHECKER_EVIDENCE_SOURCES.contains(&source),
                "the checker fingerprint must bind the production Public proof source `{name}`"
            );
        }

        for (theorem, contract) in [
            (
                "raw_public_weak_bisimulation_of_v9_verified",
                "RawPublicWeakBisimulationV9Contract",
            ),
            (
                "raw_public_delimited_release_noninterference_of_v9_verified",
                "RawPublicDelimitedReleaseNoninterferenceV9Contract",
            ),
        ] {
            assert!(
                LEAN_PUBLIC_BISIMULATION_SOURCE.contains(&format!("theorem {theorem}")),
                "the production Public theorem `{theorem}` is missing"
            );
            let declaration = LEAN_PUBLIC_BISIMULATION_SOURCE
                .split_once(&format!("theorem {theorem}"))
                .unwrap_or_else(|| panic!("missing production Public theorem `{theorem}`"))
                .1;
            assert!(
                declaration
                    .trim_start()
                    .starts_with(&format!(":\n    {contract}")),
                "the production Public theorem `{theorem}` no longer exposes its pinned contract"
            );
        }

        let claim_surface = LEAN_RAW_CLAIM_SURFACE_SOURCE
            .split_once("theorem public_delimited_release_noninterference")
            .expect("RawClaimSurface exports the production V9 Public theorem")
            .1;
        for required in [
            "(leftFuel rightFuel : Nat)",
            "PublicExecutionConclusion (rawSemanticProgram program analysis) leftResult rightResult",
            "raw_public_delimited_release_noninterference_of_v9_verified",
            "program analysis root leftFuel rightFuel left right leftResult rightResult",
        ] {
            assert!(
                claim_surface.contains(required),
                "the Public claim surface lost `{required}`"
            );
        }

        let weak_contract = lean_source_between_in(
            LEAN_PUBLIC_EXECUTION_SOURCE,
            "def RawPublicWeakBisimulationV9Contract",
            "/-- Budgeted Public noninterference contract.",
        );
        for required in [
            "(leftSteps rightSteps : Nat)",
            "SuccessfulExecution (rawSemanticProgram program analysis) root leftSteps left leftResult",
            "SuccessfulExecution (rawSemanticProgram program analysis) root rightSteps right rightResult",
            "FinitePublicAlignment (rawSemanticProgram program analysis)\n      leftSteps left rightSteps right",
        ] {
            assert!(
                weak_contract.contains(required),
                "the weak-bisimulation contract lost `{required}`"
            );
        }

        let public_contract = lean_source_between_in(
            LEAN_PUBLIC_EXECUTION_SOURCE,
            "def RawPublicDelimitedReleaseNoninterferenceV9Contract",
            "/-- The budgeted production result",
        );
        for required in [
            "(leftFuel rightFuel : Nat)",
            "SuccessfulRun (rawSemanticProgram program analysis) root leftFuel left leftResult",
            "SuccessfulRun (rawSemanticProgram program analysis) root rightFuel right rightResult",
            "PublicExecutionConclusion (rawSemanticProgram program analysis) leftResult rightResult",
        ] {
            assert!(
                public_contract.contains(required),
                "the Public noninterference contract lost `{required}`"
            );
        }

        let conclusion = lean_source_between_in(
            LEAN_PUBLIC_EXECUTION_SOURCE,
            "structure PublicExecutionConclusion",
            "/-- Generic raw alignment closes",
        );
        for required in [
            "projection : publicProjection machine left.state = publicProjection machine right.state",
            "boundaryTrace : publicBoundaryTrace left.events = publicBoundaryTrace right.events",
        ] {
            assert!(
                conclusion.contains(required),
                "the complete Public conclusion lost `{required}`"
            );
        }
        for forbidden in ["exported", "exportedResult", "returnValue"] {
            assert!(
                !conclusion.contains(forbidden),
                "the complete Public conclusion regressed to `{forbidden}`-only state"
            );
        }

        for required in [
            "structure PublicBoundaryObservation",
            "kind : EventKind",
            "site : UInt32",
            "payload : Option Int",
            "event.kind.eqb .output || event.kind.eqb .boundary",
            "events.filterMap publicBoundaryObservation?",
        ] {
            assert!(
                LEAN_SEMANTIC_SOURCE.contains(required),
                "the ordered output/boundary observation lost `{required}`"
            );
        }

        for forbidden in [
            "leftSteps = rightSteps",
            "rightSteps = leftSteps",
            "leftFuel = rightFuel",
            "rightFuel = leftFuel",
            "RelationalPolicy",
            "AssumedPolicy",
            "assumedPolicy",
            "safeMode",
            "observedPayload",
        ] {
            assert!(
                !weak_contract.contains(forbidden)
                    && !public_contract.contains(forbidden)
                    && !LEAN_PUBLIC_BISIMULATION_SOURCE.contains(forbidden)
                    && !claim_surface.contains(forbidden),
                "the production Public proof surface reintroduced the escape `{forbidden}`"
            );
        }
    }

    #[test]
    fn raw_semantics_cannot_regress_to_label_sanitization() {
        for forbidden in [
            "safeMode",
            "observedPayload",
            "relational_policy_of_safe_mode",
        ] {
            assert!(
                !LEAN_SEMANTIC_SOURCE.contains(forbidden)
                    && !LEAN_SEMANTIC_KERNEL_SOURCE.contains(forbidden),
                "raw production semantics reintroduced the sanitized symbol `{forbidden}`"
            );
        }
        for required in [
            "def addSemanticClosureEdges",
            "else if op == .closure then",
            "addSemanticClosureEdges p index n blockCell destination adjacency",
            "def semanticStructuredPathsOK",
            "def semanticPublicControlContinuationOK",
            "def semanticInstructionIsTerminator",
            "(op == .trap && n.ceiling == 0)",
            "let blockLabel := (indexedSemanticBlockNode? index functionId blockId).map",
            "if blockLabel.eqb .pub then recurse work else false",
        ] {
            assert!(
                LEAN_KERNEL_SOURCE.contains(required),
                "semantic taint graph lost the dynamic-closure dependency `{required}`"
            );
        }

        let terminator_projection = RUST_FORMAL_SOURCE
            .split_once("fn project_semantic_terminator")
            .expect("Rust projector defines project_semantic_terminator")
            .1
            .split_once("fn project_semantic_program")
            .expect("semantic terminator projection precedes the program projection")
            .0;
        assert!(
            terminator_projection
                .contains("AirTerminator::Unreachable => (SemanticInstrOp::Trap, Vec::new())"),
            "unreachable AIR must remain a raw trap, never successful termination"
        );
        assert!(
            !terminator_projection
                .contains("AirTerminator::Unreachable => (SemanticInstrOp::Halt, Vec::new())"),
            "unreachable AIR was unsafely remapped to successful halt"
        );

        let next_pc = LEAN_SEMANTIC_SOURCE
            .split_once("def nextPc")
            .expect("semantic machine defines nextPc")
            .1
            .split_once("def binaryPayload")
            .expect("nextPc is followed by binaryPayload")
            .0;
        assert!(next_pc.contains("operand.payload = 0"));
        assert!(!next_pc.contains("operand.label"));
        assert!(!next_pc.contains("blockLabel"));

        let events = LEAN_SEMANTIC_SOURCE
            .split_once("def instructionEvents")
            .expect("semantic machine defines instructionEvents")
            .1
            .split_once("def step")
            .expect("instructionEvents is followed by step")
            .0;
        assert!(events.contains("kind := .release, payload"));
        assert!(!events.contains("payload := 0, site := i.id, stage"));
        assert!(
            LEAN_SEMANTIC_SOURCE.contains("theorem state_well_formed_preserved"),
            "the raw constructor-preservation theorem is load-bearing"
        );
        for required in [
            "def secretCTStaticSafeB",
            "def publicControlStaticSafeB",
            "def publicHaltStaticSafeB",
            "def RawRelationalStaticSafe",
            "def rawRelationalStaticSafeB",
            "def verifyProgramWithRawSemantics",
            "@[export sigil_csir_verify_semantic]",
        ] {
            assert!(
                LEAN_SEMANTIC_KERNEL_SOURCE.contains(required),
                "the Init-only production semantic kernel is missing `{required}`"
            );
        }
        assert!(
            LEAN_RAW_CLAIM_SURFACE_SOURCE
                .contains("theorem secretCT_delimited_release_trace_equality"),
            "the production SecretCT theorem signature left the claim-surface module"
        );
        for required in [
            "theorem secretCTStaticSafeB_iff",
            "theorem publicControlStaticSafeB_iff",
            "theorem publicHaltStaticSafeB_iff",
            "theorem rawRelationalStaticSafeB_iff",
            "theorem raw_secretCT_step_lockstep_of_static_safe",
            "theorem raw_secretCT_delimited_release_trace_equality_of_static_safe",
        ] {
            assert!(
                LEAN_SEMANTIC_SOURCE.contains(required),
                "the raw theorem module is missing `{required}`"
            );
        }
    }

    fn encode_obligations(nodes: &[Node]) -> Vec<u8> {
        let mut nodes = nodes.to_vec();
        let mut manifest = Node::ordinary(Op::SemProgram, 0);
        manifest.node_id = u32::try_from(nodes.len() + 1).unwrap();
        manifest.ceiling = 0;
        nodes.push(manifest);
        encode(&nodes).unwrap()
    }

    fn minimal_semantic_program() -> Vec<Node> {
        let mut manifest = Node::ordinary(Op::SemProgram, 0);
        manifest.node_id = 1;
        manifest.origin = 1;
        manifest.actual = 1;
        manifest.required = 1;
        manifest.ceiling = 0;

        let mut function = Node::ordinary(Op::SemFunction, 0);
        function.node_id = 2;
        function.flags = 0;
        function.origin = 1;
        function.actual = 1;
        function.required = 1;
        function.ceiling = 0;

        let mut block = Node::ordinary(Op::SemBlock, 0);
        block.node_id = 3;
        block.origin = 1;
        block.actual = 1;
        block.required = 1;
        block.ceiling = 0;

        let mut halt = Node::ordinary(Op::SemInstruction, SemanticInstrOp::Halt as u32);
        halt.node_id = 4;
        halt.origin = 1;
        halt.actual = 1;
        halt.required = 0;
        halt.ceiling = 0;
        halt.aux = SemanticInstrOp::Halt as u32;
        let mut return_contract = Node::ordinary(Op::SemLabelContract, 2);
        return_contract.node_id = 5;
        return_contract.flags = 1;
        return_contract.origin = 1;
        return_contract.required = 2;
        return_contract.aux = 2;
        return_contract.ceiling = 0;
        vec![manifest, function, block, halt, return_contract]
    }

    fn secret_arm_successful_escape_program() -> Vec<Node> {
        fn record(op: Op, aux: u32, id: u32, origin: u32, actual: u32) -> Node {
            let mut node = Node::ordinary(op, aux);
            node.node_id = id;
            node.origin = origin;
            node.actual = actual;
            node.ceiling = 0;
            node
        }

        let mut manifest = record(Op::SemProgram, 2, 1, 1, 4);
        manifest.required = 4;
        manifest.ceiling = 7;

        let mut function = record(Op::SemFunction, 0, 2, 1, 1);
        function.flags = 0;
        function.required = 4;
        function.ceiling = 2;

        let mut selector = record(Op::SemValue, 0, 3, 1, 1);
        selector.required = 1;
        let mut result = record(Op::SemValue, 0, 4, 1, 2);
        result.required = 4;

        let mut entry = record(Op::SemBlock, 0, 5, 1, 1);
        entry.required = 1;
        let mut branch = record(Op::SemInstruction, SemanticInstrOp::Branch as u32, 6, 1, 1);
        branch.ceiling = 4;

        let mut nodes = vec![manifest, function, selector, result, entry, branch];
        for (id, position, flags, required) in
            [(7, 0, 0, 1), (8, 1, 1, 2), (9, 2, 1, 3), (10, 3, 1, 4)]
        {
            let mut operand = record(Op::SemOperand, 0, id, 6, position);
            operand.flags = flags;
            operand.required = required;
            nodes.push(operand);
        }

        let mut left = record(Op::SemBlock, 0, 11, 1, 2);
        left.required = 1;
        let mut early_output = record(Op::SemInstruction, SemanticInstrOp::Output as u32, 12, 1, 2);
        early_output.ceiling = 1;
        let mut early_value = record(Op::SemOperand, 0, 13, 12, 0);
        early_value.flags = 0;
        early_value.required = 1;

        let mut right = record(Op::SemBlock, 0, 14, 1, 3);
        right.required = 1;
        let mut right_jump = record(Op::SemInstruction, SemanticInstrOp::Jump as u32, 15, 1, 3);
        right_jump.ceiling = 1;
        let mut right_target = record(Op::SemOperand, 0, 16, 15, 0);
        right_target.flags = 1;
        right_target.required = 4;

        let mut merge = record(Op::SemBlock, 0, 17, 1, 4);
        merge.required = 1;
        let mut final_output = record(Op::SemInstruction, SemanticInstrOp::Output as u32, 18, 1, 4);
        final_output.ceiling = 1;
        let mut final_value = record(Op::SemOperand, 0, 19, 18, 0);
        final_value.flags = 0;
        final_value.required = 2;

        let mut return_contract = record(Op::SemLabelContract, 2, 20, 1, 0);
        return_contract.flags = 1;
        return_contract.required = 2;
        return_contract.label_a = Label::Secret;
        return_contract.label_b = Label::Secret;
        let mut selector_contract = record(Op::SemLabelContract, 0, 21, 1, 1);
        selector_contract.flags = 1;
        selector_contract.label_a = Label::Secret;
        selector_contract.label_b = Label::Secret;
        let mut result_contract = record(Op::SemLabelContract, 1, 22, 1, 2);
        result_contract.flags = 1;
        result_contract.required = 1;
        let mut branch_policy = record(Op::SemPolicyClass, 0, 23, 6, 1);
        branch_policy.flags = 1;
        branch_policy.required = 20;

        nodes.extend([
            left,
            early_output,
            early_value,
            right,
            right_jump,
            right_target,
            merge,
            final_output,
            final_value,
            return_contract,
            selector_contract,
            result_contract,
            branch_policy,
        ]);
        nodes
    }

    fn flat_match_catch_all_escape_program() -> Vec<Node> {
        fn record(op: Op, aux: u32, id: u32, origin: u32, actual: u32) -> Node {
            let mut node = Node::ordinary(op, aux);
            node.node_id = id;
            node.origin = origin;
            node.actual = actual;
            node.ceiling = 0;
            node
        }

        let mut manifest = record(Op::SemProgram, 2, 1, 1, 5);
        manifest.required = 5;
        manifest.ceiling = 9;

        let mut function = record(Op::SemFunction, 0, 2, 1, 1);
        function.required = 5;
        function.ceiling = 2;

        let mut selector = record(Op::SemValue, 0, 3, 1, 1);
        selector.required = 1;
        let mut result = record(Op::SemValue, 0, 4, 1, 2);
        result.required = 4;

        let mut wrapper_block = record(Op::SemBlock, 0, 5, 1, 1);
        wrapper_block.required = 1;
        let mut wrapper = record(
            Op::SemInstruction,
            SemanticInstrOp::Dispatch as u32,
            6,
            1,
            1,
        );
        wrapper.ceiling = 2;
        let mut wrapper_start = record(Op::SemOperand, 0, 7, 6, 0);
        wrapper_start.flags = 1;
        wrapper_start.required = 2;
        let mut wrapper_exit = record(Op::SemOperand, 0, 8, 6, 1);
        wrapper_exit.flags = 1;
        wrapper_exit.required = 5;

        let mut test_block = record(Op::SemBlock, 0, 9, 1, 2);
        test_block.required = 1;
        let mut dispatch = record(
            Op::SemInstruction,
            SemanticInstrOp::Dispatch as u32,
            10,
            1,
            2,
        );
        dispatch.ceiling = 4;
        let mut dispatch_selector = record(Op::SemOperand, 0, 11, 10, 0);
        dispatch_selector.flags = 0;
        dispatch_selector.required = 1;
        let mut first_arm = record(Op::SemOperand, 0, 12, 10, 1);
        first_arm.flags = 1;
        first_arm.required = 3;
        let mut catch_all = record(Op::SemOperand, 0, 13, 10, 2);
        catch_all.flags = 1;
        catch_all.required = 4;
        let mut local_merge = record(Op::SemOperand, 0, 14, 10, 3);
        local_merge.flags = 1;
        local_merge.required = 4;

        let mut first_arm_block = record(Op::SemBlock, 0, 15, 1, 3);
        first_arm_block.required = 1;
        let mut first_arm_jump = record(Op::SemInstruction, SemanticInstrOp::Jump as u32, 16, 1, 3);
        first_arm_jump.ceiling = 1;
        let mut first_arm_exit = record(Op::SemOperand, 0, 17, 16, 0);
        first_arm_exit.flags = 1;
        first_arm_exit.required = 5;

        let mut catch_all_block = record(Op::SemBlock, 0, 18, 1, 4);
        catch_all_block.required = 1;
        let mut early_output = record(Op::SemInstruction, SemanticInstrOp::Output as u32, 19, 1, 4);
        early_output.ceiling = 1;
        let mut early_value = record(Op::SemOperand, 0, 20, 19, 0);
        early_value.flags = 0;
        early_value.required = 1;

        let mut exit_block = record(Op::SemBlock, 0, 21, 1, 5);
        exit_block.required = 1;
        let mut final_output = record(Op::SemInstruction, SemanticInstrOp::Output as u32, 22, 1, 5);
        final_output.ceiling = 1;
        let mut final_value = record(Op::SemOperand, 0, 23, 22, 0);
        final_value.flags = 0;
        final_value.required = 2;

        let mut return_contract = record(Op::SemLabelContract, 2, 24, 1, 0);
        return_contract.flags = 1;
        return_contract.required = 2;
        return_contract.label_a = Label::Secret;
        return_contract.label_b = Label::Secret;
        let mut selector_contract = record(Op::SemLabelContract, 0, 25, 1, 1);
        selector_contract.flags = 1;
        selector_contract.label_a = Label::Secret;
        selector_contract.label_b = Label::Secret;
        let mut result_contract = record(Op::SemLabelContract, 1, 26, 1, 2);
        result_contract.flags = 1;
        result_contract.required = 1;

        let mut wrapper_policy = record(Op::SemPolicyClass, 3, 27, 6, 0);
        wrapper_policy.flags = 1;
        wrapper_policy.required = 23;
        let mut dispatch_policy = record(Op::SemPolicyClass, 3, 28, 10, 1);
        dispatch_policy.flags = 1;
        dispatch_policy.required = 23;

        vec![
            manifest,
            function,
            selector,
            result,
            wrapper_block,
            wrapper,
            wrapper_start,
            wrapper_exit,
            test_block,
            dispatch,
            dispatch_selector,
            first_arm,
            catch_all,
            local_merge,
            first_arm_block,
            first_arm_jump,
            first_arm_exit,
            catch_all_block,
            early_output,
            early_value,
            exit_block,
            final_output,
            final_value,
            return_contract,
            selector_contract,
            result_contract,
            wrapper_policy,
            dispatch_policy,
        ]
    }

    fn secret_arm_callee_halt_program() -> Vec<Node> {
        fn record(op: Op, aux: u32, id: u32, origin: u32, actual: u32) -> Node {
            let mut node = Node::ordinary(op, aux);
            node.node_id = id;
            node.origin = origin;
            node.actual = actual;
            node.ceiling = 0;
            node
        }

        let mut manifest = record(Op::SemProgram, 2, 1, 2, 5);
        manifest.required = 6;
        manifest.ceiling = 8;

        let mut caller = record(Op::SemFunction, 0, 2, 1, 1);
        caller.required = 4;
        caller.ceiling = 2;
        let mut selector = record(Op::SemValue, 0, 3, 1, 1);
        selector.required = 1;
        let mut output_value = record(Op::SemValue, 0, 4, 1, 2);
        output_value.required = 4;

        let mut entry = record(Op::SemBlock, 0, 5, 1, 1);
        entry.required = 1;
        let mut branch = record(Op::SemInstruction, SemanticInstrOp::Branch as u32, 6, 1, 1);
        branch.ceiling = 4;

        let mut nodes = vec![manifest, caller, selector, output_value, entry, branch];
        for (id, position, flags, required) in
            [(7, 0, 0, 1), (8, 1, 1, 2), (9, 2, 1, 3), (10, 3, 1, 4)]
        {
            let mut operand = record(Op::SemOperand, 0, id, 6, position);
            operand.flags = flags;
            operand.required = required;
            nodes.push(operand);
        }

        let mut secret_arm = record(Op::SemBlock, 0, 11, 1, 2);
        secret_arm.required = 2;
        let mut call = record(Op::SemInstruction, SemanticInstrOp::Call as u32, 12, 1, 2);
        call.ceiling = 1;
        let mut callee_operand = record(Op::SemOperand, 0, 13, 12, 0);
        callee_operand.flags = 2;
        callee_operand.required = 2;
        let mut secret_jump = record(Op::SemInstruction, SemanticInstrOp::Jump as u32, 14, 1, 2);
        secret_jump.ceiling = 1;
        let mut secret_target = record(Op::SemOperand, 0, 15, 14, 0);
        secret_target.flags = 1;
        secret_target.required = 4;

        let mut other_arm = record(Op::SemBlock, 0, 16, 1, 3);
        other_arm.required = 1;
        let mut other_jump = record(Op::SemInstruction, SemanticInstrOp::Jump as u32, 17, 1, 3);
        other_jump.ceiling = 1;
        let mut other_target = record(Op::SemOperand, 0, 18, 17, 0);
        other_target.flags = 1;
        other_target.required = 4;

        let mut merge = record(Op::SemBlock, 0, 19, 1, 4);
        merge.required = 1;
        let mut output = record(Op::SemInstruction, SemanticInstrOp::Output as u32, 20, 1, 4);
        output.ceiling = 1;
        let mut output_operand = record(Op::SemOperand, 0, 21, 20, 0);
        output_operand.flags = 0;
        output_operand.required = 2;

        let mut callee = record(Op::SemFunction, 0, 22, 2, 1);
        callee.required = 1;
        let mut callee_block = record(Op::SemBlock, 0, 23, 2, 1);
        callee_block.required = 1;
        let halt = record(Op::SemInstruction, SemanticInstrOp::Halt as u32, 24, 2, 1);

        let mut caller_return = record(Op::SemLabelContract, 2, 25, 1, 0);
        caller_return.required = 2;
        let mut selector_contract = record(Op::SemLabelContract, 0, 26, 1, 1);
        selector_contract.label_a = Label::Secret;
        selector_contract.label_b = Label::Secret;
        let mut output_contract = record(Op::SemLabelContract, 1, 27, 1, 2);
        output_contract.required = 1;
        let mut callee_return = record(Op::SemLabelContract, 2, 28, 2, 0);
        callee_return.required = 2;
        let mut branch_policy = record(Op::SemPolicyClass, 0, 29, 6, 1);
        branch_policy.required = 20;

        nodes.extend([
            secret_arm,
            call,
            callee_operand,
            secret_jump,
            secret_target,
            other_arm,
            other_jump,
            other_target,
            merge,
            output,
            output_operand,
            callee,
            callee_block,
            halt,
            caller_return,
            selector_contract,
            output_contract,
            callee_return,
            branch_policy,
        ]);
        nodes
    }

    fn ct_source_semantic_program(source_label: Label, include_policy: bool) -> Vec<Node> {
        let mut manifest = Node::ordinary(Op::SemProgram, 0);
        manifest.origin = 1;
        manifest.actual = 1;
        manifest.required = 2;
        manifest.ceiling = 1;
        manifest.aux = 2;

        let mut function = Node::ordinary(Op::SemFunction, 0);
        function.flags = 0;
        function.origin = 1;
        function.actual = 1;
        function.required = 1;
        function.ceiling = 2;

        let mut source = Node::ordinary(Op::SemValue, 0);
        source.origin = 1;
        source.actual = 1;
        source.ceiling = 0;
        let mut destination = source;
        destination.actual = 2;

        let mut block = Node::ordinary(Op::SemBlock, 0);
        block.origin = 1;
        block.actual = 1;
        block.required = 2;
        block.ceiling = 0;

        let mut project = Node::ordinary(Op::SemInstruction, SemanticInstrOp::Project as u32);
        project.origin = 1;
        project.actual = 1;
        project.required = 2;
        project.ceiling = 1;

        let mut operand = Node::ordinary(Op::SemOperand, 0);
        operand.flags = 0;
        operand.origin = 6;
        operand.actual = 0;
        operand.required = 1;
        operand.ceiling = 0;

        let mut halt = Node::ordinary(Op::SemInstruction, SemanticInstrOp::Halt as u32);
        halt.origin = 1;
        halt.actual = 1;
        halt.required = 0;
        halt.ceiling = 0;

        let mut return_contract = Node::ordinary(Op::SemLabelContract, 2);
        return_contract.flags = 1;
        return_contract.origin = 1;
        return_contract.required = 2;
        return_contract.aux = 2;
        return_contract.ceiling = 0;

        let mut source_contract = Node::ordinary(Op::SemLabelContract, 0);
        source_contract.flags = 1;
        source_contract.label_a = source_label;
        source_contract.label_b = source_label;
        source_contract.origin = 1;
        source_contract.actual = 1;
        source_contract.ceiling = 0;

        let mut destination_contract = Node::ordinary(Op::SemLabelContract, 1);
        destination_contract.flags = 1;
        destination_contract.label_a = Label::SecretCt;
        destination_contract.label_b = Label::SecretCt;
        destination_contract.origin = 1;
        destination_contract.actual = 2;
        destination_contract.required = 1;
        destination_contract.aux = 1;
        destination_contract.ceiling = 0;

        let mut nodes = vec![
            manifest,
            function,
            source,
            destination,
            block,
            project,
            operand,
            halt,
            return_contract,
            source_contract,
            destination_contract,
        ];
        if include_policy {
            let mut policy = Node::ordinary(Op::SemPolicyClass, 10);
            policy.origin = 6;
            policy.actual = 1;
            policy.required = 30;
            policy.ceiling = 0;
            nodes.push(policy);
        }
        for (index, node) in nodes.iter_mut().enumerate() {
            node.node_id = u32::try_from(index + 1).expect("semantic test node id fits u32");
        }
        nodes
    }

    fn cap_restrict_semantic_program(include_mask: bool, value_kind: u32) -> Vec<Node> {
        let operand_count = if include_mask { 2 } else { 1 };
        let mut manifest = Node::ordinary(Op::SemProgram, 0);
        manifest.origin = 1;
        manifest.actual = 1;
        manifest.required = 2;
        manifest.ceiling = operand_count;
        manifest.aux = 2;

        let mut function = Node::ordinary(Op::SemFunction, 0);
        function.flags = 0;
        function.origin = 1;
        function.actual = 1;
        function.required = 1;
        function.ceiling = 2;

        let mut source = Node::ordinary(Op::SemValue, value_kind);
        source.origin = 1;
        source.actual = 1;
        source.required = 7;
        source.ceiling = if value_kind == 2 { 1 } else { 0 };
        let mut destination = source;
        destination.actual = 2;

        let mut block = Node::ordinary(Op::SemBlock, 0);
        block.origin = 1;
        block.actual = 1;
        block.required = 2;
        block.ceiling = 0;

        let mut restrict = Node::ordinary(Op::SemInstruction, SemanticInstrOp::CapRestrict as u32);
        restrict.origin = 1;
        restrict.actual = 1;
        restrict.required = 2;
        restrict.ceiling = operand_count;

        let mut source_operand = Node::ordinary(Op::SemOperand, 0);
        source_operand.flags = 0;
        source_operand.actual = 0;
        source_operand.required = 1;
        source_operand.ceiling = 0;

        let mut halt = Node::ordinary(Op::SemInstruction, SemanticInstrOp::Halt as u32);
        halt.origin = 1;
        halt.actual = 1;
        halt.ceiling = 0;

        let mut nodes = vec![manifest, function, source, destination, block, restrict];
        source_operand.origin = 6;
        nodes.push(source_operand);
        if include_mask {
            let mut mask = Node::ordinary(Op::SemOperand, 0);
            mask.flags = 3;
            mask.origin = 6;
            mask.actual = 1;
            mask.required = 0xffff_ffff;
            mask.ceiling = 0;
            nodes.push(mask);
        }
        nodes.push(halt);

        for (subject, role) in [(0, 2), (1, 1), (2, 1)] {
            let mut contract = Node::ordinary(Op::SemLabelContract, role);
            contract.flags = 1;
            contract.origin = 1;
            contract.actual = subject;
            contract.required = role;
            contract.ceiling = 0;
            contract.aux = role;
            nodes.push(contract);
        }
        let mut capability_type = Node::ordinary(Op::SemCapabilityType, 0);
        capability_type.actual = 1;
        capability_type.required = 0x1234_5678;
        capability_type.ceiling = u32::MAX;
        capability_type.aux = 0;
        nodes.push(capability_type);
        for (index, node) in nodes.iter_mut().enumerate() {
            node.node_id = u32::try_from(index + 1).expect("semantic test node id fits u32");
        }
        nodes
    }

    #[test]
    fn canonical_empty_encoding_is_stable() {
        assert_eq!(encode(&[]).unwrap(), b"CSIR\x08\0\0\0\0\0\0\0");
    }

    #[test]
    fn rust_and_lean_wire_opcode_tables_are_identical() {
        let operations = [
            (Op::Flow as u32, "flow"),
            (Op::Authority as u32, "authority"),
            (Op::Declassify as u32, "declassify"),
            (Op::CtUse as u32, "ctUse"),
            (Op::Boundary as u32, "boundary"),
            (Op::FixedCt as u32, "fixedCT"),
            (Op::Effect as u32, "effect"),
            (Op::Consume as u32, "consume"),
            (Op::TaintSeed as u32, "taintSeed"),
            (Op::TaintEdge as u32, "taintEdge"),
            (Op::TaintSink as u32, "taintSink"),
            (Op::TaintCtUse as u32, "taintCtUse"),
            (Op::TaintRelease as u32, "taintRelease"),
            (Op::CapOrigin as u32, "capOrigin"),
            (Op::CapRestrict as u32, "capRestrict"),
            (Op::CapSplit as u32, "capSplit"),
            (Op::CapDraw as u32, "capDraw"),
            (Op::CapSink as u32, "capSink"),
            (Op::CapRelease as u32, "capRelease"),
            (Op::CapSlot as u32, "capSlot"),
            (Op::CapSlotPut as u32, "capSlotPut"),
            (Op::CapSlotTake as u32, "capSlotTake"),
            (Op::CapMeet as u32, "capMeet"),
            (Op::PathFork as u32, "pathFork"),
            (Op::PathArm as u32, "pathArm"),
            (Op::PathJoin as u32, "pathJoin"),
            (Op::PathLoop as u32, "pathLoop"),
            (Op::PathBack as u32, "pathBack"),
            (Op::PathBreak as u32, "pathBreak"),
            (Op::PathLoopJoin as u32, "pathLoopJoin"),
            (Op::IntCell as u32, "intCell"),
            (Op::DiffLe as u32, "diffLe"),
            (Op::QuantityUse as u32, "quantityUse"),
            (Op::SemProgram as u32, "semProgram"),
            (Op::SemFunction as u32, "semFunction"),
            (Op::SemValue as u32, "semValue"),
            (Op::SemBlock as u32, "semBlock"),
            (Op::SemInstruction as u32, "semInstruction"),
            (Op::SemOperand as u32, "semOperand"),
            (Op::SemLabelContract as u32, "semLabelContract"),
            (Op::SemCapabilityType as u32, "semCapabilityType"),
            (Op::SemPolicyClass as u32, "semPolicyClass"),
            (Op::SemRefinementFact as u32, "semRefinementFact"),
            (Op::SemRuntimeGuard as u32, "semRuntimeGuard"),
        ];
        let semantic_instructions = [
            (SemanticInstrOp::Scalar as u32, "scalar"),
            (SemanticInstrOp::Aggregate as u32, "aggregate"),
            (SemanticInstrOp::Project as u32, "project"),
            (SemanticInstrOp::Branch as u32, "branch"),
            (SemanticInstrOp::Jump as u32, "jump"),
            (SemanticInstrOp::Loop as u32, "loop"),
            (SemanticInstrOp::Call as u32, "call"),
            (SemanticInstrOp::Closure as u32, "closure"),
            (SemanticInstrOp::ActorBoundary as u32, "actorBoundary"),
            (SemanticInstrOp::StateRead as u32, "stateRead"),
            (SemanticInstrOp::StateWrite as u32, "stateWrite"),
            (SemanticInstrOp::SlotNew as u32, "slotNew"),
            (SemanticInstrOp::SlotPut as u32, "slotPut"),
            (SemanticInstrOp::SlotTake as u32, "slotTake"),
            (SemanticInstrOp::Effect as u32, "effect"),
            (SemanticInstrOp::Ffi as u32, "ffi"),
            (SemanticInstrOp::Allocation as u32, "allocation"),
            (SemanticInstrOp::Address as u32, "address"),
            (SemanticInstrOp::CapMint as u32, "capMint"),
            (SemanticInstrOp::CapRestrict as u32, "capRestrict"),
            (SemanticInstrOp::CapSplit as u32, "capSplit"),
            (SemanticInstrOp::CapDraw as u32, "capDraw"),
            (SemanticInstrOp::CapExercise as u32, "capExercise"),
            (SemanticInstrOp::Release as u32, "release"),
            (SemanticInstrOp::ReleaseCt as u32, "releaseCT"),
            (SemanticInstrOp::CtEq as u32, "ctEq"),
            (SemanticInstrOp::CtSelect as u32, "ctSelect"),
            (SemanticInstrOp::CtLt as u32, "ctLt"),
            (SemanticInstrOp::Output as u32, "output"),
            (SemanticInstrOp::Trap as u32, "trap"),
            (SemanticInstrOp::Halt as u32, "halt"),
            (SemanticInstrOp::Range as u32, "range"),
            (SemanticInstrOp::Dispatch as u32, "dispatch"),
            (SemanticInstrOp::Index as u32, "index"),
            (SemanticInstrOp::DivRem as u32, "divRem"),
            (SemanticInstrOp::StringCompare as u32, "stringCompare"),
            (SemanticInstrOp::AbortiveEffect as u32, "abortiveEffect"),
        ];

        assert_eq!(Op::SemRuntimeGuard as usize + 1, operations.len());
        assert_eq!(
            SemanticInstrOp::AbortiveEffect as usize + 1,
            semantic_instructions.len()
        );
        assert_eq!(
            lean_decoder_entries("decodeOp?"),
            operations
                .iter()
                .map(|(code, name)| (*code, (*name).to_owned()))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            lean_decoder_entries("decodeSemanticInstrOp?"),
            semantic_instructions
                .iter()
                .map(|(code, name)| (*code, (*name).to_owned()))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn lean_kernel_caches_whole_program_indexes_outside_inner_loops() {
        let graph_solution =
            lean_source_between("def graphComputedSolutionSafe", "def firstGraphViolation");
        assert!(
            graph_solution.contains("let adjacency := graphAdjacency p"),
            "the graph verifier must build its whole-program adjacency index once"
        );
        assert!(
            graph_solution.contains("adjacencyCellSafeWith adjacency p labels"),
            "each graph cell must consume the cached adjacency index"
        );
        assert!(
            !graph_solution.contains("adjacencyCellSafe p labels"),
            "rebuilding graph adjacency inside every cell is quadratic"
        );

        // The verifier region ends where the wire decoder begins (`readU8?`, public since the
        // kernel-cheap twin in DecoderStream.lean relates it to its stream reader).
        let semantic_verifier = lean_source_between("def semanticFunctionRecordOK", "def readU8?");
        for cached_consumer in [
            "firstSemanticViolationList p index p.nodes.toList",
            "firstSemanticMetadataViolationList p index p.nodes.toList",
            "firstV8SecurityViolationList p index labels p.nodes.toList",
        ] {
            assert!(
                semantic_verifier.contains(cached_consumer),
                "the semantic verifier must share its cross-reference index and labels: `{cached_consumer}`"
            );
        }
        for forbidden_scan in [
            "semanticOwnedCount p",
            "semanticBlockInstructionCount p",
            "semanticOwnerOperandCount p",
            "semanticFunctionNode? p",
            "semanticBlockNode? p",
            "semanticValueNode? p",
        ] {
            assert!(
                !semantic_verifier.contains(forbidden_scan),
                "semantic record validation reintroduced whole-program scan `{forbidden_scan}`"
            );
        }

        let semantic_index = lean_source_between(
            "structure SemanticIndex",
            "def indexedSemanticFunctionNode?",
        );
        for required_flat_index in [
            "valueStarts : Array Nat",
            "blockStarts : Array Nat",
            "valueContracts : Array Bool",
            "valueContractNodes : Array (Option Node)",
            "returnContracts : Array Bool",
            "returnContractNodes : Array (Option Node)",
            "policyClasses : Array UInt32",
            "runtimeGuards : Array Bool",
            "capabilityTypes : Array (Option Node)",
        ] {
            assert!(
                semantic_index.contains(required_flat_index),
                "semantic cross references must retain flat per-function offsets: `{required_flat_index}`"
            );
        }
        assert!(
            !semantic_index.contains("Array (Array Node)"),
            "nested persistent arrays copy accumulated per-function indexes and can become quadratic"
        );

        let metadata_verifier =
            lean_source_between("def semanticPolicyExists", "def semanticValueCell?");
        assert!(
            !metadata_verifier.contains("p.nodes.foldl"),
            "metadata completeness must use the one-pass semantic index, not rescan all records"
        );

        let structured_paths = lean_source_between(
            "def semanticStructuredPathsOK",
            "def semanticStructuredControlRecordOK",
        );
        assert!(
            structured_paths.contains("Nat → Array Bool → List UInt32 → Bool")
                && structured_paths.contains("visited.setIfInBounds"),
            "structured-CFG validation must retain its linear block bitmap/worklist"
        );
        assert!(
            !structured_paths.contains("visited.contains"),
            "a linear visited-list scan inside structured DFS is quadratic on sibling CFGs"
        );
        assert!(
            structured_paths.contains("labelAt labels block.nodeId")
                && structured_paths.contains("if blockLabel.eqb .pub then recurse work else false"),
            "Public path validation must distinguish a secret-region exit from a successful exit after pc restoration"
        );

        let public_control = lean_source_between(
            "def semanticPublicControlContinuationOK",
            "def semanticInstructionFlowViolation",
        );
        assert!(
            public_control.contains("block.lub")
                && public_control.contains("fuel visited [start.required]"),
            "nested selectors and flat match wrappers must retain their derived-pc early-exit checks"
        );

        let pc_restore =
            lean_source_between("def semanticPcRestoreCells", "def addSemanticSourceCells");
        assert!(
            pc_restore.contains("if instruction.ceiling.toNat == 2 then")
                && pc_restore.contains("else restored")
                && !pc_restore.contains("if instruction.ceiling.toNat == 2 then 1 else 3"),
            "only the flat match wrapper exit is a pc-restoring continuation; an inner arm-test else target is not"
        );

        let closure_edges = lean_source_between(
            "def semanticMaxClosureArgumentCount",
            "def semanticInstructionTaintEdges",
        );
        for summary in [
            "semanticDynamicEntryCell",
            "semanticDynamicReturnCell",
            "semanticDynamicArgumentCell",
            "addSemanticDynamicFunctionSummaries",
        ] {
            assert!(
                closure_edges.contains(summary),
                "dynamic closure taint must retain compact complete-bipartite summary `{summary}`"
            );
        }
        assert!(
            !closure_edges.contains("p.nodes.foldl (fun adjacency function"),
            "materializing every closure×function taint edge is quadratic"
        );

        for semantic_cache in [
            "sourceIndex : SemanticIndex",
            "policySelections : Array (List PolicySelection)",
            "verifyProgramWithContext p index labels",
        ] {
            assert!(
                LEAN_SEMANTIC_KERNEL_SOURCE.contains(semantic_cache),
                "the raw decoder must retain cached semantic data: `{semantic_cache}`"
            );
        }
        assert!(
            !LEAN_SEMANTIC_KERNEL_SOURCE.contains("p.source.nodes.any fun policy"),
            "rescanning every policy record for every instruction/class pair is quadratic"
        );

        let state_index = lean_source_between_in(
            LEAN_V9_INVOCATION_ANALYSIS_SOURCE,
            "def buildStateContractIndex",
            "def stateLabelForFunctionAt?",
        );
        assert!(
            state_index.contains("program.base.nodes.foldl (collectStateContract functionCount)")
                && state_index.contains("collected.mergeSort stateContractEntryLE")
                && state_index.contains("foldl mergeStateContractEntry"),
            "v9 analysis must collect once, sort exact pair keys, and coalesce once"
        );
        let state_lookup = lean_source_between_in(
            LEAN_V9_INVOCATION_ANALYSIS_SOURCE,
            "def stateLabelForFunctionAt?",
            "def stateContractRecordCoveredB",
        );
        assert!(
            state_lookup.contains("binarySearchStateContract")
                && !state_lookup.contains("program.base.nodes")
                && !state_lookup.contains("filterMap")
                && !state_lookup.contains("foldl"),
            "state-write lookup must be an exact binary search, never a state-surface scan"
        );
        let state_binary_search = lean_source_between_in(
            LEAN_V9_INVOCATION_ANALYSIS_SOURCE,
            "def binarySearchStateContract",
            "def stateLabelForFunctionAt?",
        );
        assert!(
            state_binary_search
                .contains("entry.functionId == functionId && entry.offset == offset")
                && state_binary_search.contains("fuel (middle + 1) upper")
                && state_binary_search.contains("fuel lower middle"),
            "the state-contract scaling canary requires exact-pair equality and a shrinking binary-search interval"
        );
        let state_postcheck = lean_source_between_in(
            LEAN_V9_INVOCATION_ANALYSIS_SOURCE,
            "def stateContractRecordCoveredB",
            "def analyze?",
        );
        assert!(
            state_postcheck.contains("program.base.nodes.all")
                && state_postcheck.contains("stateLabelForFunctionAt? index")
                && state_postcheck.contains("contract.labelA.flowsTo sink")
                && state_postcheck.contains("index.all (stateContractEntryWitnessedB program)")
                && state_postcheck.contains("contract.origin == entry.functionId")
                && state_postcheck.contains("contract.actual == entry.offset")
                && state_postcheck.contains("contract.labelA == entry.label"),
            "the optimized state index must retain both O(records log N) declaration coverage and exact-key reverse witnesses"
        );
        let state_write = lean_source_between_in(
            LEAN_V9_OCCURRENCE_KERNEL_SOURCE,
            "def stateWriteOccurrenceOK",
            "/-- The checked site",
        );
        assert!(
            state_write.contains("analysis.stateContracts")
                && !state_write.contains("program.base.nodes.toList")
                && !state_write.contains("program.base.nodes.foldl"),
            "per-write policy checking must consume the precomputed index, not rescan CSIR"
        );
        let v9_analysis = lean_source_between_in(
            LEAN_V9_INVOCATION_ANALYSIS_SOURCE,
            "def analyze?",
            "end LambdaSigil.Combined.V9.OccurrenceDataflowInvocation",
        );
        assert_eq!(
            v9_analysis
                .matches("buildStateContractIndex program")
                .count(),
            1,
            "the v9 analysis must build the state-contract index exactly once"
        );

        let cached_root_return = lean_source_between_in(
            LEAN_V9_OCCURRENCE_KERNEL_SOURCE,
            "def rootReturnOKWithDecoded",
            "def rootReturnOK (",
        );
        assert!(
            !cached_root_return.contains("OccurrenceDataflow.semanticProgram"),
            "the production root-return core must consume the shared decoded machine, not reconstruct it per output"
        );
        let cached_instruction_check = lean_source_between_in(
            LEAN_V9_OCCURRENCE_KERNEL_SOURCE,
            "def instructionOccurrenceOKWithDecoded",
            "/-- The checked site",
        );
        assert!(
            cached_instruction_check.contains("rootReturnOKWithDecoded")
                && !cached_instruction_check.contains("rootReturnOK program"),
            "the production instruction check must route output sites through the cached decoded-machine path"
        );
        let cached_policy_loop = lean_source_between_in(
            LEAN_V9_OCCURRENCE_KERNEL_SOURCE,
            "def occurrencePolicyChecksWithMachines",
            "def occurrencePolicyChecks (",
        );
        assert!(
            cached_policy_loop.contains("instructionOccurrenceOKWithDecoded")
                && !cached_policy_loop.contains("instructionOccurrenceOK program"),
            "the production occurrence loop must not invoke a wrapper that reconstructs the decoded machine"
        );
        let v9_verifier = lean_source_between_in(
            LEAN_V9_OCCURRENCE_KERNEL_SOURCE,
            "def verifyProgram (program",
            "def verifyBytes",
        );
        assert_eq!(
            v9_verifier
                .matches("let decoded := OccurrenceDataflow.semanticProgram")
                .count(),
            1,
            "the production v9 verifier must decode the semantic machine exactly once"
        );
        assert_eq!(
            v9_verifier
                .matches("let machine := rawSemanticProgramFromDecoded")
                .count(),
            1,
            "the production v9 verifier must raise the occurrence-aware machine exactly once"
        );
        for cached_consumer in [
            "occurrencePolicyChecksWithMachines program analysis decoded machine",
            "firstOccurrenceViolationWithMachines program analysis decoded machine",
        ] {
            assert!(
                v9_verifier.contains(cached_consumer),
                "the production v9 verifier must thread both cached machines into `{cached_consumer}`"
            );
        }
        for forbidden_wrapper in [
            "occurrencePolicyChecks program analysis",
            "firstOccurrenceViolation program analysis",
        ] {
            assert!(
                !v9_verifier.contains(forbidden_wrapper),
                "the production v9 verifier must not call rebuilding wrapper `{forbidden_wrapper}`"
            );
        }

        let operand_count = lean_source_between(
            "def semanticOperandKindCountFrom",
            "def semanticOperandKindCount",
        );
        assert!(
            operand_count.contains(
                "semanticOperandKindCountFrom p owner kind (position + 1) remaining count'"
            ),
            "bounded operand traversal must remain tail-recursive at the one-million-record ceiling"
        );
    }

    #[test]
    fn v9_whole_program_collectors_remain_stack_safe() {
        let legacy_state_label_join = lean_source_between(
            "def semanticDeclaredStateLabelAtList",
            "def semanticDeclaredStateLabelAt",
        );
        assert!(
            legacy_state_label_join.contains("contracts.foldl")
                && !legacy_state_label_join
                    .contains("semanticDeclaredStateLabelAtList offset rest")
                && !legacy_state_label_join.contains("let tail"),
            "the retained-v8 state-label join must remain an iterative fold over the full record set"
        );

        let priority_edge_count = lean_source_between_in(
            LEAN_PRIORITY_OCCURRENCE_SOURCE,
            "def edgeCount",
            "structure Seeds",
        );
        assert!(
            priority_edge_count.contains("adjacency.foldl")
                && !priority_edge_count.contains("adjacency.toList")
                && !priority_edge_count.contains("List.sum"),
            "priority-occurrence fuel accounting must remain a direct, stack-safe array fold"
        );

        let host_seed_collection = lean_source_between_in(
            LEAN_V9_OCCURRENCE_DATAFLOW_SOURCE,
            "def collectHostSeedStep?",
            "def saturate",
        );
        for required in [
            "collected : Option (Array HostSeed)",
            "let seeds ← collected",
            "seeds.push seed",
            "program.base.nodes.foldl",
            "(some #[])",
            "seeds : Array HostSeed",
        ] {
            assert!(
                host_seed_collection.contains(required),
                "the v9 host-seed collector lost its stack-safe, fail-closed array invariant: `{required}`"
            );
        }
        assert!(
            !host_seed_collection.contains("program.base.nodes.toList")
                && !host_seed_collection.contains("List HostSeed"),
            "the v9 host-seed collector must not recreate a recursively consumed whole-program list"
        );

        let state_contract_collection = lean_source_between_in(
            LEAN_V9_INVOCATION_ANALYSIS_SOURCE,
            "def buildStateContractIndex",
            "def stateLabelForFunctionAt?",
        );
        assert!(
            state_contract_collection
                .contains("program.base.nodes.foldl (collectStateContract functionCount)")
                && state_contract_collection.contains("foldl mergeStateContractEntry")
                && !state_contract_collection.contains("program.base.nodes.toList"),
            "the v9 state-contract collectors must remain direct array folds"
        );
    }

    fn large_single_function_program(value_count: u32) -> Vec<Node> {
        assert!(
            value_count > 0,
            "large semantic fixture needs at least one value"
        );

        let mut manifest = Node::ordinary(Op::SemProgram, 0);
        manifest.node_id = 1;
        manifest.origin = 1;
        manifest.actual = 1;
        manifest.required = 1;
        manifest.ceiling = 0;
        manifest.aux = value_count;

        let mut function = Node::ordinary(Op::SemFunction, 0);
        function.node_id = 2;
        function.flags = 0;
        function.origin = 1;
        function.actual = 1;
        function.required = 1;
        function.ceiling = value_count;

        let mut nodes = Vec::with_capacity(value_count as usize * 2 + 5);
        nodes.extend([manifest, function]);
        for value_id in 1..=value_count {
            let mut value = Node::ordinary(Op::SemValue, 0);
            value.node_id = value_id + 2;
            value.origin = 1;
            value.actual = value_id;
            value.required = 4;
            value.ceiling = 0;
            nodes.push(value);
        }

        let mut block = Node::ordinary(Op::SemBlock, 0);
        block.node_id = value_count + 3;
        block.origin = 1;
        block.actual = 1;
        block.required = 1;
        block.ceiling = 0;
        nodes.push(block);

        let mut halt = Node::ordinary(Op::SemInstruction, SemanticInstrOp::Halt as u32);
        halt.node_id = value_count + 4;
        halt.origin = 1;
        halt.actual = 1;
        halt.ceiling = 0;
        nodes.push(halt);

        let mut return_contract = Node::ordinary(Op::SemLabelContract, 2);
        return_contract.node_id = value_count + 5;
        return_contract.flags = 1;
        return_contract.origin = 1;
        return_contract.actual = 0;
        return_contract.required = 2;
        return_contract.ceiling = 0;
        return_contract.aux = 2;
        nodes.push(return_contract);
        for value_id in 1..=value_count {
            let mut contract = Node::ordinary(Op::SemLabelContract, 1);
            contract.node_id = value_count + 5 + value_id;
            contract.flags = 1;
            contract.origin = 1;
            contract.actual = value_id;
            contract.required = 1;
            contract.ceiling = 0;
            contract.aux = 1;
            nodes.push(contract);
        }
        nodes
    }

    #[test]
    fn linked_lean_indexes_large_single_function_without_nested_copying() {
        const VALUE_COUNT: u32 = 65_536;
        let nodes = large_single_function_program(VALUE_COUNT);
        let bytes = encode(&nodes).expect("large canonical semantic program encodes");
        assert_eq!(sigil_formal_bridge::verify(&bytes), Ok(0));
    }

    #[test]
    fn linked_v9_verifier_handles_moderate_record_array_without_recursive_collectors() {
        const VALUE_COUNT: u32 = 16_384;
        const EXPECTED_BASE_RECORDS: usize = VALUE_COUNT as usize * 2 + 5;

        let legacy = encode(&large_single_function_program(VALUE_COUNT))
            .expect("moderate canonical v8 prefix encodes");
        assert_eq!(
            legacy.len(),
            HEADER_BYTES + EXPECTED_BASE_RECORDS * NODE_BYTES
        );
        let root = crate::formal_v9::FunctionRootContract {
            function_id: 1,
            role: 1,
            actor_type: 0,
            handler_id: 0,
            export_name: "stack_safe_fixture".into(),
            is_entry: false,
            entry_occurrence: sigil_abi::host_contract::SecurityLabel::Public,
            return_occurrence: sigil_abi::host_contract::SecurityLabel::Public,
        };
        let bytes = crate::formal_v9::encode(&legacy, None, &[], &[], &[root])
            .expect("moderate canonical v9 envelope encodes");
        assert!(
            bytes.len() < 2 * 1024 * 1024,
            "the generated stack canary must remain a moderate in-memory fixture"
        );
        assert_eq!(sigil_formal_bridge::verify_v9(&bytes), Ok(0));
    }

    #[test]
    fn linked_lean_rejects_v8_without_a_semantic_manifest() {
        assert_ne!(sigil_formal_bridge::verify(&encode(&[]).unwrap()), Ok(0));
    }

    #[test]
    fn linked_lean_accepts_canonical_v8_semantic_envelope() {
        let bytes =
            encode(&minimal_semantic_program()).expect("bounded canonical v8 fixture encodes");
        assert_eq!(
            sigil_formal_bridge::verify(&bytes).expect("native verifier executes"),
            0
        );
    }

    #[test]
    fn linked_lean_rejects_secret_arm_successful_escape_before_merge() {
        let bytes = encode(&secret_arm_successful_escape_program())
            .expect("bounded escape fixture encodes");
        let verdict = sigil_formal_bridge::verify(&bytes).expect("native verifier executes");
        assert_eq!(
            verdict & 0xffff,
            1,
            "the relational gate fails closed as I013"
        );
        assert_eq!(verdict >> 32, 6, "the verdict retains the branch site");
    }

    fn private_leaf_return_program() -> Vec<Node> {
        let mut nodes = secret_arm_successful_escape_program();
        nodes[1].flags = 1;
        nodes[21].label_a = Label::Secret;
        nodes[21].label_b = Label::Secret;
        nodes
    }

    #[test]
    fn linked_lean_private_leaf_exception_requires_every_return_to_be_private() {
        let nodes = private_leaf_return_program();
        let verdict = |nodes: &[Node]| {
            sigil_formal_bridge::verify(&encode(nodes).expect("bounded semantic fixture encodes"))
                .expect("native verifier executes")
        };
        assert_eq!(
            verdict(&nodes),
            0,
            "a private leaf may return from either arm"
        );
        for function_kind in [0, 2, 3] {
            let mut root = nodes.clone();
            root[1].flags = function_kind;
            assert_eq!(verdict(&root) >> 32, 6, "root kinds retain the escape gate");
        }
        let mut public_return = nodes;
        public_return[21].label_a = Label::Public;
        public_return[21].label_b = Label::Public;
        assert_eq!(
            verdict(&public_return) >> 32,
            6,
            "a private return may not suppress a later Public return"
        );
    }

    #[test]
    fn linked_lean_private_leaf_cannot_skip_a_public_destination() {
        let mut nodes = private_leaf_return_program();
        nodes[0].aux += 1;
        nodes[0].required += 1;
        nodes[0].ceiling += 1;
        nodes[1].ceiling += 1;
        nodes[16].required += 1;
        let mut value = Node::ordinary(Op::SemValue, 0);
        value.node_id = 24;
        value.origin = 1;
        value.actual = 3;
        value.required = 4;
        value.ceiling = 0;
        let mut write = Node::ordinary(Op::SemInstruction, SemanticInstrOp::Scalar as u32);
        write.node_id = 25;
        write.origin = 1;
        write.actual = 4;
        write.required = 3;
        write.ceiling = 1;
        let mut immediate = Node::ordinary(Op::SemOperand, 0);
        immediate.node_id = 26;
        immediate.flags = 3;
        immediate.origin = 25;
        immediate.required = 7;
        immediate.ceiling = 0;
        // Insert using temporary IDs, then rebase both identities and owner references.
        // The mutant stays canonical: structural refusal would not exercise the leaf rule.
        nodes.insert(17, immediate);
        nodes.insert(17, write);
        nodes.insert(4, value);
        let mut contract = Node::ordinary(Op::SemLabelContract, 1);
        contract.node_id = 27;
        contract.origin = 1;
        contract.actual = 3;
        contract.required = 1;
        contract.ceiling = 0;
        let policy = nodes
            .iter()
            .position(|node| matches!(node.op, Op::SemPolicyClass))
            .expect("fixture contains its branch policy");
        nodes.insert(policy, contract);
        let ids = nodes
            .iter()
            .enumerate()
            .map(|(position, node)| {
                (
                    node.node_id,
                    u32::try_from(position + 1).expect("small fixture"),
                )
            })
            .collect::<BTreeMap<_, _>>();
        for node in &mut nodes {
            node.node_id = ids[&node.node_id];
            if matches!(node.op, Op::SemOperand | Op::SemPolicyClass) {
                node.origin = ids[&node.origin];
            }
        }
        let bytes = encode(&nodes).expect("bounded canonical public-write mutant encodes");
        let verdict = sigil_formal_bridge::verify(&bytes).expect("native verifier executes");
        assert_eq!(verdict & 0xffff, 2, "the semantic flow check rejects");
        assert_eq!(
            (verdict >> 16) & 0xffff,
            1,
            "the public destination reports a semantic sink-flow violation"
        );
        assert_eq!(
            verdict >> 32,
            26,
            "the destination contract identifies the public write reached under private control"
        );
    }

    #[test]
    fn linked_lean_private_leaf_distinguishes_index_reads_from_dynamic_stores() {
        let fixture = |store: bool| {
            let mut nodes = private_leaf_return_program();
            let value_count = if store { 3 } else { 2 };
            nodes[0].required += 1;
            nodes[0].ceiling += value_count + 3;
            nodes[16].required += 1;
            let mut operation = Node::ordinary(Op::SemInstruction, SemanticInstrOp::Index as u32);
            operation.node_id = 24;
            operation.origin = 1;
            operation.actual = 4;
            operation.required = if store { 0 } else { 2 };
            operation.ceiling = value_count + 3;
            let mut inserted = vec![operation];
            for position in 0..value_count + 3 {
                let mut operand = Node::ordinary(Op::SemOperand, 0);
                operand.node_id = 25 + position;
                operand.flags = 0;
                operand.origin = 24;
                operand.actual = position;
                operand.ceiling = 0;
                if position < value_count {
                    operand.required = 2;
                } else {
                    operand.flags = 3;
                    // The actual LoadDynamic/StoreDynamic immediate layout: size, type, offset.
                    operand.required = [8, 4, 0][(position - value_count) as usize];
                }
                inserted.push(operand);
            }
            nodes.splice(17..17, inserted);
            for (class, code) in [(4, 24), (5, 25)] {
                let mut policy = Node::ordinary(Op::SemPolicyClass, class);
                policy.node_id = 31 + class;
                policy.origin = 24;
                policy.actual = 3;
                policy.required = code;
                policy.ceiling = 0;
                nodes.push(policy);
            }
            let ids = nodes
                .iter()
                .enumerate()
                .map(|(position, node)| {
                    (
                        node.node_id,
                        u32::try_from(position + 1).expect("small fixture"),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            for node in &mut nodes {
                node.node_id = ids[&node.node_id];
                if matches!(node.op, Op::SemOperand | Op::SemPolicyClass) {
                    node.origin = ids[&node.origin];
                }
            }
            encode(&nodes).expect("canonical index read/store fixture encodes")
        };
        assert_eq!(sigil_formal_bridge::verify(&fixture(false)), Ok(0));
        let verdict =
            sigil_formal_bridge::verify(&fixture(true)).expect("native verifier executes");
        assert_eq!(
            verdict & 0xffff,
            1,
            "a dynamic store is not a private leaf read"
        );
        assert_eq!(
            (verdict >> 16) & 0xffff,
            9,
            "not a malformed-record refusal"
        );
        assert_eq!(verdict >> 32, 6, "the branch cannot skip the dynamic store");
    }

    #[test]
    fn linked_lean_rejects_secret_flat_match_catch_all_escape() {
        let bytes = encode(&flat_match_catch_all_escape_program())
            .expect("bounded flat-match fixture encodes");
        let verdict = sigil_formal_bridge::verify(&bytes).expect("native verifier executes");
        assert_eq!(verdict & 0xffff, 1, "the relational gate fails closed");
        assert_eq!(
            verdict >> 32,
            6,
            "the enclosing flat-match wrapper identifies the escaping region"
        );
    }

    #[test]
    fn linked_lean_rejects_a_secret_arm_callee_that_halts_instead_of_returning() {
        let bytes =
            encode(&secret_arm_callee_halt_program()).expect("bounded callee-halt fixture encodes");
        let verdict = sigil_formal_bridge::verify(&bytes).expect("native verifier executes");
        assert_eq!(verdict & 0xffff, 1, "the relational gate fails closed");
        assert_eq!(verdict >> 32, 24, "the verdict identifies the callee halt");
    }

    #[test]
    fn linked_lean_enforces_direct_t030_ct_source_policy() {
        let public = encode(&ct_source_semantic_program(Label::Public, true))
            .expect("bounded Public CT-source fixture encodes");
        assert_eq!(
            sigil_formal_bridge::verify(&public).expect("native verifier executes"),
            0
        );

        let internal = encode(&ct_source_semantic_program(Label::Internal, true))
            .expect("bounded Internal CT-source fixture encodes");
        let internal_verdict =
            sigil_formal_bridge::verify(&internal).expect("native verifier executes");
        assert_eq!(
            internal_verdict & 0xffff,
            7,
            "T030 is a CT-policy violation"
        );
        assert_eq!((internal_verdict >> 16) & 0xffff, 30);
        assert_eq!(internal_verdict >> 32, 6);

        let missing = encode(&ct_source_semantic_program(Label::Public, false))
            .expect("bounded missing-policy fixture encodes");
        let missing_verdict =
            sigil_formal_bridge::verify(&missing).expect("native verifier executes");
        assert_eq!(
            missing_verdict & 0xffff,
            1,
            "missing T030 metadata is malformed"
        );
        assert_eq!((missing_verdict >> 16) & 0xffff, 8);
        assert_eq!(missing_verdict >> 32, 6);
    }

    #[test]
    fn linked_lean_rejects_noncanonical_v8_semantic_metadata() {
        let mut nodes = minimal_semantic_program();
        nodes[3].label_a = Label::Internal;
        let verdict = sigil_formal_bridge::verify(&encode(&nodes).unwrap()).unwrap();
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 4);
    }

    #[test]
    fn linked_lean_rejects_v8_block_without_a_terminator() {
        let mut nodes = minimal_semantic_program();
        // A zero-operand trap is now the canonical unconditional-trap terminator used for
        // type-proved unreachable AIR.  Use a valid zero-operand nonterminator for this layout
        // mutant so the test continues to isolate the missing-terminator condition.
        nodes[3].aux = SemanticInstrOp::Effect as u32;
        let bytes = encode(&nodes).expect("malformed semantic fixture still encodes");
        let verdict =
            sigil_formal_bridge::verify(&bytes).expect("linked verifier returns a verdict");
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 0);
    }

    #[test]
    fn linked_lean_rejects_v8_reordered_owner_records() {
        let mut nodes = minimal_semantic_program();
        nodes.swap(1, 2);
        for (index, node) in nodes.iter_mut().enumerate() {
            node.node_id = u32::try_from(index + 1).expect("semantic test node id fits u32");
        }
        let bytes = encode(&nodes).expect("reordered semantic fixture still encodes");
        let verdict =
            sigil_formal_bridge::verify(&bytes).expect("linked verifier returns a verdict");
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 0);
    }

    #[test]
    fn linked_lean_rejects_v8_reordered_sibling_values() {
        let mut nodes = minimal_semantic_program();
        nodes[0].aux = 2;
        nodes[1].ceiling = 2;

        let mut first = Node::ordinary(Op::SemValue, 0);
        first.origin = 1;
        first.actual = 1;
        first.required = 1;
        let mut second = first;
        second.actual = 2;
        nodes.splice(2..2, [second, first]);
        for (index, node) in nodes.iter_mut().enumerate() {
            node.node_id = u32::try_from(index + 1).expect("semantic test node id fits u32");
        }

        let bytes = encode(&nodes).expect("reordered semantic fixture still encodes");
        let verdict =
            sigil_formal_bridge::verify(&bytes).expect("linked verifier returns a verdict");
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 0);
    }

    #[test]
    fn linked_lean_rejects_v8_reordered_sibling_blocks() {
        let nodes = minimal_semantic_program();
        let mut manifest = nodes[0];
        manifest.actual = 2;
        manifest.required = 2;
        let mut function = nodes[1];
        function.required = 2;
        let first_block = nodes[2];
        let first_halt = nodes[3];
        let mut second_block = first_block;
        second_block.actual = 2;
        let mut second_halt = first_halt;
        second_halt.actual = 2;
        let mut reordered = vec![
            manifest,
            function,
            second_block,
            second_halt,
            first_block,
            first_halt,
        ];
        for (index, node) in reordered.iter_mut().enumerate() {
            node.node_id = u32::try_from(index + 1).expect("semantic test node id fits u32");
        }

        let bytes = encode(&reordered).expect("reordered semantic fixture still encodes");
        let verdict =
            sigil_formal_bridge::verify(&bytes).expect("linked verifier returns a verdict");
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 0);
    }

    #[test]
    fn linked_lean_rejects_v8_terminator_destination() {
        let mut nodes = minimal_semantic_program();
        nodes[0].aux = 1;
        nodes[1].ceiling = 1;
        let mut value = Node::ordinary(Op::SemValue, 0);
        value.node_id = 3;
        value.origin = 1;
        value.actual = 1;
        value.required = 1;
        value.ceiling = 0;
        nodes.insert(2, value);
        nodes[3].node_id = 4;
        nodes[4].node_id = 5;
        nodes[4].required = 1;
        nodes[5].node_id = 6;
        let bytes = encode(&nodes).expect("terminator fixture encodes");
        let verdict =
            sigil_formal_bridge::verify(&bytes).expect("linked verifier returns a verdict");
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 5);
    }

    #[test]
    fn linked_lean_rejects_v8_wrong_operand_order() {
        let mut manifest = Node::ordinary(Op::SemProgram, 0);
        manifest.node_id = 1;
        manifest.origin = 1;
        manifest.actual = 3;
        manifest.required = 3;
        manifest.ceiling = 3;
        manifest.aux = 1;

        let mut function = Node::ordinary(Op::SemFunction, 0);
        function.node_id = 2;
        function.flags = 0;
        function.origin = 1;
        function.actual = 1;
        function.required = 3;
        function.ceiling = 1;

        let mut value = Node::ordinary(Op::SemValue, 0);
        value.node_id = 3;
        value.origin = 1;
        value.actual = 1;
        value.required = 1;
        value.ceiling = 0;

        let mut entry = Node::ordinary(Op::SemBlock, 0);
        entry.node_id = 4;
        entry.origin = 1;
        entry.actual = 1;
        entry.required = 1;
        entry.ceiling = 0;

        let mut loop_instruction = Node::ordinary(Op::SemInstruction, SemanticInstrOp::Loop as u32);
        loop_instruction.node_id = 5;
        loop_instruction.origin = 1;
        loop_instruction.actual = 1;
        loop_instruction.ceiling = 3;
        loop_instruction.aux = SemanticInstrOp::Loop as u32;

        let operands = [(1_u8, 2_u32), (0, 1), (1, 3)].into_iter().enumerate().map(
            |(position, (kind, target))| {
                let mut operand = Node::ordinary(Op::SemOperand, 0);
                operand.node_id =
                    u32::try_from(6 + position).expect("semantic test node id fits u32");
                operand.flags = kind;
                operand.origin = 5;
                operand.actual = u32::try_from(position).expect("operand position fits u32");
                operand.required = target;
                operand
            },
        );

        let mut body = Node::ordinary(Op::SemBlock, 0);
        body.node_id = 9;
        body.origin = 1;
        body.actual = 2;
        body.required = 1;
        body.ceiling = 0;
        let mut body_halt = Node::ordinary(Op::SemInstruction, SemanticInstrOp::Halt as u32);
        body_halt.node_id = 10;
        body_halt.origin = 1;
        body_halt.actual = 2;
        body_halt.ceiling = 0;
        body_halt.aux = SemanticInstrOp::Halt as u32;

        let mut exit = Node::ordinary(Op::SemBlock, 0);
        exit.node_id = 11;
        exit.origin = 1;
        exit.actual = 3;
        exit.required = 1;
        exit.ceiling = 0;
        let mut exit_halt = Node::ordinary(Op::SemInstruction, SemanticInstrOp::Halt as u32);
        exit_halt.node_id = 12;
        exit_halt.origin = 1;
        exit_halt.actual = 3;
        exit_halt.ceiling = 0;
        exit_halt.aux = SemanticInstrOp::Halt as u32;

        let mut nodes = vec![manifest, function, value, entry, loop_instruction];
        nodes.extend(operands);
        nodes.extend([body, body_halt, exit, exit_halt]);
        let bytes = encode(&nodes).expect("operand-order fixture encodes");
        let verdict =
            sigil_formal_bridge::verify(&bytes).expect("linked verifier returns a verdict");
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 5);
    }

    #[test]
    fn linked_lean_rejects_v8_cap_restrict_without_mask() {
        let bytes =
            encode(&cap_restrict_semantic_program(false, 2)).expect("capability fixture encodes");
        let verdict =
            sigil_formal_bridge::verify(&bytes).expect("linked verifier returns a verdict");
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 6);
    }

    #[test]
    fn linked_lean_rejects_v8_cap_restrict_over_copy_values() {
        let bytes =
            encode(&cap_restrict_semantic_program(true, 0)).expect("capability fixture encodes");
        let verdict =
            sigil_formal_bridge::verify(&bytes).expect("linked verifier returns a verdict");
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 6);
    }

    #[test]
    fn linked_lean_rejects_wrong_v8_semantic_constructor_count() {
        let mut nodes = minimal_semantic_program();
        nodes[0].required = 2;
        let verdict = sigil_formal_bridge::verify(&encode(&nodes).unwrap()).unwrap();
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 1);
    }

    #[test]
    fn linked_lean_rejects_noncontiguous_v8_operand_slice() {
        let mut nodes = minimal_semantic_program();
        nodes[0].ceiling = 1;
        nodes[3].aux = SemanticInstrOp::Jump as u32;
        nodes[3].ceiling = 1;
        let mut operand = Node::ordinary(Op::SemOperand, 0);
        operand.node_id = 5;
        operand.flags = 1;
        operand.origin = 4;
        operand.actual = 1;
        operand.required = 1;
        operand.ceiling = 0;
        nodes.insert(4, operand);
        nodes[5].node_id = 6;
        let verdict = sigil_formal_bridge::verify(&encode(&nodes).unwrap()).unwrap();
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 0);
    }

    #[test]
    fn linked_lean_rejects_missing_v8_cfg_target() {
        let mut nodes = minimal_semantic_program();
        nodes[0].ceiling = 1;
        nodes[3].aux = SemanticInstrOp::Jump as u32;
        nodes[3].ceiling = 1;
        let mut operand = Node::ordinary(Op::SemOperand, 0);
        operand.node_id = 5;
        operand.flags = 1;
        operand.origin = 4;
        operand.actual = 0;
        operand.required = 2;
        operand.ceiling = 0;
        nodes.insert(4, operand);
        nodes[5].node_id = 6;
        let verdict = sigil_formal_bridge::verify(&encode(&nodes).unwrap()).unwrap();
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 5);
    }

    #[test]
    fn planted_bad_authority_is_rejected_by_linked_lean() {
        let mut bad = Node::ordinary(Op::Authority, 0);
        bad.node_id = 1;
        bad.actual = 1;
        bad.required = 3;
        bad.ceiling = 1;
        let bytes = encode_obligations(&[bad]);
        let verdict = sigil_formal_bridge::verify(&bytes).unwrap();
        assert_eq!(verdict & 0xffff, 4);
        assert_eq!(verdict >> 32, 1);
    }

    #[test]
    fn linked_lean_derives_transitive_taint_instead_of_trusting_a_sink_label() {
        let mut seed = Node::ordinary(Op::TaintSeed, 0);
        seed.node_id = 1;
        seed.origin = 1;
        seed.label_a = Label::SecretCt;

        let mut middle = Node::ordinary(Op::TaintSeed, 0);
        middle.node_id = 2;
        middle.origin = 2;

        let mut edge = Node::ordinary(Op::TaintEdge, 0);
        edge.node_id = 3;
        edge.origin = 1;
        edge.actual = 2;

        let mut use_site = Node::ordinary(Op::TaintCtUse, 20);
        use_site.node_id = 4;
        use_site.origin = 2;
        use_site.actual = 0;

        let verdict =
            sigil_formal_bridge::verify(&encode_obligations(&[seed, middle, edge, use_site]))
                .unwrap();
        assert_eq!(verdict & 0xffff, 7);
        assert_eq!((verdict >> 16) & 0xffff, 20);
        assert_eq!(verdict >> 32, 4);
    }

    #[test]
    fn linked_lean_rejects_out_of_bounds_taint_cells_fail_closed() {
        let mut seed = Node::ordinary(Op::TaintSeed, 0);
        seed.node_id = 1;
        seed.origin = 3;
        let verdict = sigil_formal_bridge::verify(&encode_obligations(&[seed])).unwrap();
        assert_eq!(verdict & 0xffff, 1);
        assert_eq!(verdict >> 32, 1);
    }

    #[test]
    fn linked_lean_derives_bv32_attenuation_instead_of_trusting_a_mask() {
        let mut projector = Projector::default();
        let origin = projector.cap_origin(0, 0b11, 1).unwrap();
        let restricted = projector.cap_restrict(origin, 0b01).unwrap();
        projector.cap_sink(restricted, 0b10, 1).unwrap();

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes)).unwrap();
        assert_eq!(verdict & 0xffff, 4);
        assert_eq!(verdict >> 32, 3);
    }

    #[test]
    fn linked_lean_rejects_a_capability_derivation_without_a_legitimate_origin() {
        let mut projector = Projector::default();
        projector.structural(0).unwrap();
        let forged = CapCell {
            id: 1,
            kind: 0,
            ceiling: 0b11,
        };
        projector.cap_restrict(forged, 0b01).unwrap();

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes)).unwrap();
        assert_eq!(verdict & 0xffff, 3);
        assert_eq!(verdict >> 32, 2);
    }

    #[test]
    fn linked_lean_slot_take_uses_the_meet_of_put_authorities() {
        let mut projector = Projector::default();
        let origin = projector.cap_origin(0, 0b11, 1).unwrap();
        let restricted = projector.cap_restrict(origin, 0b01).unwrap();
        let slot = projector.cap_slot(0, 0b11, false).unwrap();
        projector.cap_slot_put(slot, restricted).unwrap();
        let taken = projector.cap_slot_take(slot).unwrap();
        projector.cap_sink(taken, 0b10, 1).unwrap();

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes)).unwrap();
        assert_eq!(verdict & 0xffff, 4);
        assert_eq!(verdict >> 32, 6);
    }

    #[test]
    fn linked_lean_accepts_a_guarded_empty_slot_take() {
        let mut projector = Projector::default();
        let slot = projector
            .cap_slot(0, 0b11, false)
            .expect("empty-slot fixture projects");
        let taken = projector
            .cap_slot_take(slot)
            .expect("guarded empty take projects");
        projector
            .cap_sink(taken, 0b01, 1)
            .expect("conservative continuation projects");

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes))
            .expect("linked verifier returns a verdict");
        assert_eq!(verdict, 0);
    }

    #[test]
    fn linked_lean_empty_slot_take_still_enforces_the_ceiling() {
        let mut projector = Projector::default();
        let slot = projector
            .cap_slot(0, 0b11, false)
            .expect("empty-slot fixture projects");
        let taken = projector
            .cap_slot_take(slot)
            .expect("guarded empty take projects");
        projector
            .cap_sink(taken, 0b100, 1)
            .expect("over-ceiling continuation projects");

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes))
            .expect("linked verifier returns a verdict");
        assert_eq!(verdict & 0xffff, 4);
        assert_eq!(verdict >> 32, 3);
    }

    #[test]
    fn linked_lean_accepts_one_consumption_in_each_exclusive_arm() {
        let mut projector = Projector::default();
        let origin = projector.cap_origin(0, 0b11, 1).unwrap();
        projector.path_fork(2).unwrap();
        projector.cap_sink(origin, 0, 1).unwrap();
        projector.path_arm(true).unwrap();
        projector.cap_sink(origin, 0, 1).unwrap();
        projector.path_join(true).unwrap();

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes)).unwrap();
        assert_eq!(verdict, 0);
    }

    #[test]
    fn linked_lean_rejects_two_consumptions_on_one_path() {
        let mut projector = Projector::default();
        let origin = projector.cap_origin(0, 0b11, 1).unwrap();
        projector.path_fork(2).unwrap();
        projector.cap_sink(origin, 0, 1).unwrap();
        projector.cap_sink(origin, 0, 1).unwrap();
        projector.path_arm(true).unwrap();
        projector.path_join(true).unwrap();

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes)).unwrap();
        assert_eq!(verdict & 0xffff, 5);
        assert_eq!(verdict >> 32, 4);
    }

    #[test]
    fn linked_lean_rejects_use_after_a_may_consume_join() {
        let mut projector = Projector::default();
        let origin = projector.cap_origin(0, 0b11, 1).unwrap();
        projector.path_fork(2).unwrap();
        projector.cap_sink(origin, 0, 1).unwrap();
        projector.path_arm(true).unwrap();
        projector.path_join(true).unwrap();
        projector.cap_sink(origin, 0, 1).unwrap();

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes)).unwrap();
        assert_eq!(verdict & 0xffff, 5);
        assert_eq!(verdict >> 32, 6);
    }

    #[test]
    fn linked_lean_rejects_consuming_a_loop_head_capability_on_a_back_edge() {
        let mut projector = Projector::default();
        let origin = projector.cap_origin(0, 0b11, 1).unwrap();
        projector.path_loop().unwrap();
        projector.cap_sink(origin, 0, 1).unwrap();
        projector.path_back().unwrap();
        projector.path_loop_join().unwrap();

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes)).unwrap();
        assert_eq!(verdict & 0xffff, 5);
        assert_eq!(verdict >> 32, 4);
    }

    #[test]
    fn linked_lean_accepts_a_single_consumption_on_a_break_exit() {
        let mut projector = Projector::default();
        let origin = projector.cap_origin(0, 0b11, 1).unwrap();
        projector.path_loop().unwrap();
        projector.cap_sink(origin, 0, 1).unwrap();
        projector.path_break().unwrap();
        projector.path_loop_join().unwrap();

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes)).unwrap();
        assert_eq!(verdict, 0);
    }

    #[test]
    fn linked_lean_carries_break_consumption_to_the_loop_exit() {
        let mut projector = Projector::default();
        let origin = projector.cap_origin(0, 0b11, 1).unwrap();
        projector.path_loop().unwrap();
        projector.cap_sink(origin, 0, 1).unwrap();
        projector.path_break().unwrap();
        projector.path_loop_join().unwrap();
        projector.cap_sink(origin, 0, 1).unwrap();

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes)).unwrap();
        assert_eq!(verdict & 0xffff, 5);
        assert_eq!(verdict >> 32, 6);
    }

    #[test]
    fn linked_lean_rejects_cross_nested_path_and_loop_markers() {
        let mut projector = Projector::default();
        projector.cap_origin(0, 0b11, 1).unwrap();
        projector.path_loop().unwrap();
        projector.path_fork(2).unwrap();
        projector.path_loop_join().unwrap();

        let verdict = sigil_formal_bridge::verify(&encode_obligations(&projector.nodes)).unwrap();
        assert_eq!(verdict & 0xffff, 5);
        assert_eq!((verdict >> 16) & 0xffff, 1);
        assert_eq!(verdict >> 32, 4);
    }
}
