//! The AIR: SIGIL's post-typecheck IR, a CFG of basic blocks holding typed
//! statements over `VarId`s, plus `lower`, which flattens a `TypedProgram`
//! into it for the capability/ownership verifiers and the Wasm backend.
//!
//! * **Deterministic lowering.** The lowering state keeps its maps ordered
//!   (accidental iteration stays deterministic), and a `FuncId` is the
//!   function's position in the flattened module-function vector, the index
//!   base that `wasm.rs` and the self-hosted emitter (`selfhost/air.sigil`)
//!   build on. The shadow must stay byte-identical downstream, so lowering
//!   changes are contract changes against `docs/specs/sh-air.md`;
//!   `FUEL_MULT_CLAMP` (2^40) keeps the shared fuel arithmetic
//!   representable on both sides.
//! * **Heap layout.** The closure/slice/str/Option layout constants are the
//!   single source of truth: construct-site stores, access-site loads, and
//!   `wasm.rs`'s Option-tag emission all read them by name.
//! * **Span side-channels.** `debug_names`/`debug_spans`/`def_span` are the
//!   capability verifier's only source anchors for C001/C002/C003/C004
//!   diagnostics; the hand-written `AirFunction` Debug omits the span maps
//!   so `snap_air.rs` goldens pin structure, not raw byte offsets.
//!
//! No diagnostics leave this file: user-rejectable input was refused by an
//! earlier pass (effect-handler nodes are gated with E004 before AIR), so
//! an impossible input here panics (an `ICE:`-prefixed pass-contract
//! violation, or an unreachable arm citing the guard that makes it dead),
//! never silently wrong AIR. Pinned by `tests/snap_air.rs` and
//! `sigil-runtime/tests/air_differential.rs`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::{
    ast::{BinaryOp, Literal, Ring, TaintLabel},
    span::Span,
    type_check::{
        Type, TypeSubstitution, TypedArrayLitExpr, TypedAskExpr, TypedAssignStmt, TypedBinaryExpr,
        TypedBlock, TypedCallExpr, TypedCapDrawExpr, TypedCapRestrictExpr, TypedCapSplitExpr,
        TypedClosureConstructExpr, TypedEnumConstructExpr, TypedExpr, TypedExprKind,
        TypedExternCallExpr, TypedFieldAccessExpr, TypedFunction, TypedFunctionKind,
        TypedGrantExpr, TypedHandleExpr, TypedIfStmt, TypedIndexExpr, TypedIndirectCallExpr,
        TypedIndirectCallKind, TypedIntrinsicExpr, TypedIntrinsicKind, TypedLetStmt, TypedMatchArm,
        TypedMintExpr, TypedParam, TypedPattern, TypedProgram, TypedRecordConstructExpr,
        TypedRegionExpr, TypedResultCtorExpr, TypedSendExpr, TypedSliceExpr, TypedSpawnExpr,
        TypedStmt, TypedTryExpr, apply_subst,
    },
};

/// Lookup-only compiler state. Keeping these maps ordered makes accidental
/// future iteration deterministic without obscuring their intended use.
type LookupMap<K, V> = BTreeMap<K, V>;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct AirProgram {
    pub functions: Vec<AirFunction>,
}

/// Declarative taint contract retained at the AIR boundary for CSIR v8.
///
/// These are inputs to the Lean analysis, never Rust-computed verdicts.  An
/// inferred value has no fixed label; a concrete value is both seeded at and
/// bounded by its declared label; a flow value belongs to the function's
/// `@Flow` group, which the kernel seeds at `@Secret` for the exported
/// original while `formal::instantiate_flow_functions` projects one concrete
/// instance per instantiation label the call sites resolve to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AirLabelContract {
    Inferred,
    Concrete(TaintLabel),
    Flow,
}

/// Security-sensitive instruction classes whose distinctions would otherwise
/// be erased by ordinary AIR lowering.  The numeric T-code is deliberately not
/// stored here: CSIR owns the stable wire code and Rust/Lean parity tests pin the
/// mapping in one place.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AirPolicyClass {
    Branch,
    Loop,
    Range,
    Dispatch,
    Index,
    Address,
    DivRem,
    Ffi,
    ActorBoundary,
    Allocation,
    CtSource,
    Release,
    ReleaseCt,
    StringCompare,
    FixedCt,
    Quantity,
}

/// Structural actor-operation identity reserved for the occurrence-aware
/// projection. These are not policy labels or v8 opcodes; zero is reserved for
/// non-actor instructions. Renumbering requires reviewing the future wire
/// mapping and `tests/air_actor_operations.rs` together.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u32)]
pub enum AirActorOperation {
    Send = 1,
    Ask = 2,
    Spawn = 3,
    Serialize = 4,
    Deserialize = 5,
}

/// Security facts preserved by lowering but ignored by runtime codegen.
///
/// Maps are ordered because their canonical projection is certificate-bound.
/// Source spans remain a side table: `formal.rs` associates them with stable
/// CSIR node IDs but does not put byte offsets into the encoded program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AirSecurityMetadata {
    /// Source/runtime callability. This is projected into the v9 root contract
    /// and consumed by Wasm export selection; it is never a derived taint verdict.
    pub externally_callable: bool,
    pub value_contracts: BTreeMap<VarId, AirLabelContract>,
    pub return_contract: AirLabelContract,
    pub control_policy: BTreeMap<BlockId, AirPolicyClass>,
    pub state_contracts: BTreeMap<u32, TaintLabel>,
    pub statement_spans: BTreeMap<(BlockId, u32), Span>,
    pub terminator_spans: BTreeMap<BlockId, Span>,
    /// Exact constructors in pre-memory/fuel AIR, keyed like statement spans.
    /// V8 does not encode this pending-v9 side table. It does not classify an
    /// operation as private or establish any runtime-provider approval.
    pub actor_operations: BTreeMap<(BlockId, u32), AirActorOperation>,
    /// Blocks whose runtime `return` implements an abortive effect transfer rather than a
    /// source-level function output. Kept outside structural AIR snapshots and runtime codegen.
    pub abortive_transfer_blocks: BTreeSet<BlockId>,
    /// Type-impossible CFG blocks retained solely to keep runtime lowering structurally total
    /// (currently the fallthrough after an exhaustively checked match). The semantic CSIR
    /// projection emits `halt` for these blocks and excludes their dead definitions from joins.
    pub semantic_unreachable_blocks: BTreeSet<BlockId>,
}

impl Default for AirSecurityMetadata {
    fn default() -> Self {
        Self {
            externally_callable: true,
            value_contracts: BTreeMap::new(),
            return_contract: AirLabelContract::Concrete(TaintLabel::Public),
            control_policy: BTreeMap::new(),
            state_contracts: BTreeMap::new(),
            statement_spans: BTreeMap::new(),
            terminator_spans: BTreeMap::new(),
            actor_operations: BTreeMap::new(),
            abortive_transfer_blocks: BTreeSet::new(),
            semantic_unreachable_blocks: BTreeSet::new(),
        }
    }
}

impl AirSecurityMetadata {
    /// Capture constructor identities only after lowering has finalized block
    /// statements. Later runtime passes may move statement indexes; the formal
    /// gate consumes this pre-memory/fuel cut, not the rewritten runtime AIR.
    pub(crate) fn record_actor_operations(&mut self, blocks: &[AirBlock]) {
        let mut operations = BTreeMap::new();
        for block in blocks {
            for (index, statement) in block.stmts.iter().enumerate() {
                if let Some(operation) = statement.actor_operation() {
                    let index = u32::try_from(index)
                        .expect("ICE: AIR actor statement index exceeds the CSIR index width");
                    assert!(
                        operations.insert((block.id, index), operation).is_none(),
                        "ICE: lowering must assign unique AIR actor operation sites"
                    );
                }
            }
        }
        self.actor_operations = operations;
    }
}

#[derive(Clone, PartialEq)]
pub struct AirFunction {
    pub name: String,
    pub export_name: String,
    pub ring: Ring,
    pub kind: AirFunctionKind,
    pub params: Vec<(VarId, AirType)>,
    pub ret: AirType,
    pub locals: Vec<(VarId, AirType)>,
    /// `value_kinds` and `debug_names` use BTreeMap for deterministic Debug
    /// iteration. AIR snapshot tests (`snap_air.rs`) walk these maps via Debug.
    /// Lookup-only consumers (`var_kind`, `var_label`) use `.get()`; codegen
    /// never iterates these maps.
    pub value_kinds: BTreeMap<VarId, AirValueKind>,
    pub debug_names: BTreeMap<VarId, String>,
    pub blocks: Vec<AirBlock>,
    pub entry_block: BlockId,
    /// Source span of the function declaration. The capability verifier
    /// runs over the span-free AIR, so a whole-function cap verdict
    /// (the C002 global-Unsat / C004 global-Unknown probes, which have no
    /// single offending `VarId`) has no per-var anchor; it points here
    /// instead. Synthetic for hand-built AIR (the cap-verifier unit
    /// fixtures), real for lowered functions.
    pub def_span: Span,
    /// Def-site source span per `VarId`, parallel to `debug_names`.
    /// Populated during lowering: `lower_expr_into` records each
    /// destination's originating expression span; params and closure
    /// captures use the enclosing function's span. The capability
    /// verifier looks this up (`var_span`) to attach a source location to
    /// C001/C002/C003/C004 diagnostics, which would otherwise be
    /// `span: None` (the verifier sees only `VarId`s + `debug_names`).
    /// Like `debug_names`, a `BTreeMap` for deterministic Debug
    /// iteration; codegen never reads it.
    pub debug_spans: BTreeMap<VarId, Span>,
    /// Static execution multiplicity per block, indexed by `BlockId` — the
    /// product of enclosing FOR-RANGE-with-literal-bounds trip counts, `None`
    /// under any unbounded loop. Fuel-pass metadata ONLY (weights decrement
    /// sites into the worst-case-cost `recommended_budget`); codegen never
    /// reads it, and like `def_span`/`debug_spans` it is deliberately OMITTED
    /// from the hand-written `Debug` so `snap_air` goldens don't churn.
    /// Empty for hand-built AIR (cap-verifier unit fixtures) — the fuel pass
    /// reads out-of-bounds as `None` (fail-closed: never a ceiling).
    pub block_static_multiplicity: Vec<Option<u64>>,
    /// Declarative security metadata, including pending-v9 actor identities.
    /// Runtime lowering and Wasm emission do not consult it.
    pub security: AirSecurityMetadata,
}

/// Hand-written `Debug` that reproduces the `derive(Debug)` output for
/// every field EXCEPT the capability-diagnostic span side-channels
/// (`def_span`, `debug_spans`). Those carry raw byte offsets that would
/// (a) churn the `snap_air` golden snapshots on any fixture edit and
/// (b) add pure noise to a structural-IR snapshot whose job is to catch
/// block/stmt/value encoding regressions. Omitting them keeps `snap_air`
/// byte-identical to the pre-span-fix output. `debug_struct(...).finish()`
/// formats identically to the derive in both `{:?}` and `{:#?}` modes.
///
/// MAINTENANCE: when adding a NON-span field to `AirFunction`, add a
/// matching `.field(...)` line here too, or it won't appear in snapshots.
/// (`block_static_multiplicity` is deliberately omitted like the spans —
/// fuel-pass metadata, not structural IR.)
impl fmt::Debug for AirFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AirFunction")
            .field("name", &self.name)
            .field("export_name", &self.export_name)
            .field("ring", &self.ring)
            .field("kind", &self.kind)
            .field("params", &self.params)
            .field("ret", &self.ret)
            .field("locals", &self.locals)
            .field("value_kinds", &self.value_kinds)
            .field("debug_names", &self.debug_names)
            .field("blocks", &self.blocks)
            .field("entry_block", &self.entry_block)
            // Security metadata is certificate-bound but intentionally absent
            // from long-standing runtime AIR snapshots.
            .finish()
    }
}

impl AirFunction {
    pub fn var_type(&self, var: VarId) -> AirType {
        if let Some((_, ty)) = self.params.iter().find(|(id, _)| *id == var) {
            return *ty;
        }

        if let Some((_, ty)) = self.locals.iter().find(|(id, _)| *id == var) {
            return *ty;
        }

        AirType::Unit
    }

    pub fn var_kind(&self, var: VarId) -> AirValueKind {
        self.value_kinds
            .get(&var)
            .cloned()
            .unwrap_or(AirValueKind::Copy)
    }

    pub fn var_label(&self, var: VarId) -> String {
        self.debug_names
            .get(&var)
            .cloned()
            .unwrap_or_else(|| format!("v{}", var.0))
    }

    /// Def-site source span of `var`, if one was recorded during
    /// lowering. Used by the capability verifier to locate C001-C004
    /// violations in source. `None` for hand-built AIR with no span map
    /// (the cap-verifier unit fixtures) or a `VarId` that never reached
    /// `lower_expr_into` (e.g. a backend-synthesized scratch local).
    pub fn var_span(&self, var: VarId) -> Option<Span> {
        self.debug_spans.get(&var).copied()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct AirBlock {
    pub id: BlockId,
    pub stmts: Vec<AirStmt>,
    pub terminator: AirTerminator,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AirStmt {
    Assign {
        dst: VarId,
        val: AirValue,
    },
    StoreField {
        base_ptr: VarId,
        offset: u32,
        val: VarId,
        ty: AirType,
    },
    LoadField {
        dst: VarId,
        base_ptr: VarId,
        offset: u32,
        ty: AirType,
    },
    /// A read from actor state. Kept distinct from an ordinary field load so
    /// CSIR v8 can derive the declared state-source label. Wasm emission is
    /// identical to `LoadField`.
    StateRead {
        dst: VarId,
        state_ptr: VarId,
        offset: u32,
        ty: AirType,
        label: TaintLabel,
    },
    /// A write to actor state. Kept distinct from an ordinary field store so
    /// the semantic verifier owns the state-sink check. Wasm emission is
    /// identical to `StoreField`.
    StateWrite {
        state_ptr: VarId,
        offset: u32,
        val: VarId,
        ty: AirType,
        label: TaintLabel,
    },
    /// A runtime-transparent, capability-consuming release retained through
    /// AIR. `src` is copied to `dst`; `cap` is copied to `cap_scratch` exactly
    /// as the pre-v8 ownership move-site was, preserving the affine runtime
    /// shape while exposing the release stage to CSIR.
    SecurityRelease {
        dst: VarId,
        src: VarId,
        cap: VarId,
        cap_scratch: VarId,
        stage: AirReleaseStage,
    },
    Call {
        dst: Option<VarId>,
        func: FuncId,
        args: Vec<VarId>,
    },
    FuelDecrement {
        amount: u32,
    },
    MessageSend {
        target: VarId,
        msg: VarId,
        actor_type: ActorTypeId,
        handler: HandlerId,
        payload_buf: VarId,
        payload_len: VarId,
    },
    MessageAsk {
        dst: VarId,
        target: VarId,
        msg: VarId,
        actor_type: ActorTypeId,
        handler: HandlerId,
        payload_buf: VarId,
        payload_len: VarId,
        timeout: VarId,
    },
    ResultTry {
        dst: VarId,
        src: VarId,
    },
    /// PR OptTry / N9-OptTry: `?` operator on `Option<T>`. DISTINCT
    /// variant from `ResultTry` (forbidden to type-alias per N9-OptTry)
    /// because Option's tag-discriminated layout demands inverted-
    /// semantics: tag=1 means None (short-circuit), tag=0 means Some
    /// (extract payload). The wasm emission shape mirrors ResultTry's
    /// (load-tag → If-Eqz-short-circuit → load-payload-into-dst)
    /// but uses the Option-specific tag constants OPTION_NONE_TAG /
    /// OPTION_SOME_TAG.
    OptionTry {
        dst: VarId,
        src: VarId,
    },
    /// Phase-1 completion: `arr.contains(x)` / `slc.contains(x)` for a SCALAR
    /// element. A wasm-internal bounded scan loop with width-dispatched
    /// equality (the OptionTry/ResultTry "structured-wasm-inside-one-AirStmt"
    /// hatch, since `lower_intrinsic_expr` is straight-line and cannot emit a
    /// `Loop` terminator). `base_ptr` is the array allocation (`skip_header =
    /// true` → element addr adds the 4-byte u32 length header) or a slice's
    /// data_ptr (`skip_header = false` → already past the header); `len` is
    /// the element count, loaded ONCE before the loop; `needle` is the value
    /// to find; `elem` selects the load width + Eq opcode (I32Eq for 4-byte
    /// {i32,u32,bool}; I64Eq for 8-byte {i64,u64}; F64Eq for f64). `dst` is
    /// the bool result (1 = found, 0 = not). The scan is statically
    /// length-bounded with no Alloc/Call → fuel-exempt; `len` is read once and
    /// `idx` strictly increments, so the loop provably terminates.
    ArrayOrSliceContains {
        dst: VarId,
        /// For an array, the array pointer (header at offset 0); for a slice,
        /// its `data_ptr`. BOTH read elements at a baked `+4` offset: a slice's
        /// `data_ptr` is `underlying_arr_ptr + start*elem_size` (NOT advanced
        /// past the array's 4-byte length header), so the same `+4` lands on
        /// element `idx` for arrays AND slices (see `index_base_and_bounds`).
        base_ptr: VarId,
        len: VarId,
        needle: VarId,
        /// A fresh u32 scratch local for the loop counter (the wasm `loop`
        /// needs a counter that persists across iterations; all wasm locals
        /// come from AIR `VarId`s, so it is allocated by the lowering arm).
        idx: VarId,
        elem: AirType,
    },
    /// AG-S1-M (retired): `a == b` on `str` by CONTENT. `dst = (lhs_len ==
    /// rhs_len) && every byte matches`. Rides the same
    /// "structured-wasm-inside-one-AirStmt" hatch as `ArrayOrSliceContains`,
    /// because the binary-expr lowering is straight-line and cannot emit a
    /// `Loop` terminator.
    ///
    /// The four operands are PRE-LOADED by the lowering arm from each side's
    /// str header (`data_ptr` u32 @0, `len` u32 @4), so this variant performs
    /// no field loads of its own and `ownership.rs` sees ordinary reads.
    ///
    /// UNLIKE `ArrayOrSliceContains` this is NOT fuel-exempt. That exemption
    /// rests on an array's length being a compile-time constant; a `str`'s
    /// length is a runtime value, so the scan is not statically bounded.
    /// `wasm.rs` therefore emits an in-loop `fuel_decrement` (1 per byte, plus
    /// 1 for the O(1) length check), and `fuel::insert` treats it like
    /// `CallIndirect` — contributing a floor and CLEARING
    /// `is_workload_ceiling`, since the trip count is invisible to the static
    /// WCC formula. Charging a constant instead would look like metering while
    /// providing none.
    ///
    /// NB `data_ptr` points at byte 0 of the content — unlike an array pointer
    /// there is no length header to skip, so the byte loads use offset 0, not
    /// the `+4` that `ArrayOrSliceContains` bakes in.
    StrBytesEq {
        dst: VarId,
        lhs_data: VarId,
        lhs_len: VarId,
        rhs_data: VarId,
        rhs_len: VarId,
        /// A fresh u32 scratch local for the loop counter, allocated by the
        /// lowering arm (same reason as `ArrayOrSliceContains::idx`).
        idx: VarId,
    },
    /// Phase-1 completion: `slc.first()` / `slc.last()` → `Option<T>`. `dst`
    /// is a PRE-ALLOCATED `Option` struct (the `lower_intrinsic_expr` arm
    /// emits the `BumpAlloc` before this stmt, sized from the enum registry);
    /// this fills it via a runtime branch: `if len == 0 { tag = None } else {
    /// e = load data_ptr[idx] (idx = 0 for first, len-1 for last); tag = Some;
    /// payload@4 = e }`. Tags are the locked Some=`OPTION_SOME_TAG` /
    /// None=`OPTION_NONE_TAG` layout; `elem` is the payload load/store width.
    /// `is_last` is a COMPILE-TIME flag (the variant), not a runtime value.
    SliceOptionElem {
        dst: VarId,
        data_ptr: VarId,
        len: VarId,
        is_last: bool,
        elem: AirType,
    },
    SpawnActor {
        dst: VarId,
        actor_type: ActorTypeId,
        caps: Vec<VarId>,
        fuel_cap: VarId,
        supervision: AirSupervisionStrategy,
    },
    CapRestrict {
        dst: VarId,
        src: VarId,
        restriction_mask: u32,
    },
    CapSplit {
        dst: VarId,
        src: VarId,
        amount: VarId,
    },
    /// `cap.draw(amount)` — like `CapSplit` at the runtime layer (same
    /// host import is emitted in `wasm.rs`), but the ownership checker
    /// does NOT mark `src` as moved. Introduced in step 10 for axis-1
    /// rate-limit expressibility. The Z3 conservation logic treats this
    /// the same as `CapSplit` for now — soundness preserved, conservation
    /// is the same per-call invariant.
    CapDraw {
        dst: VarId,
        src: VarId,
        amount: VarId,
    },
    /// Capabilities-as-values: `mint <CapType>[(deadlines)] for <target>` —
    /// the sanctioned capability constructor. Unlike `Assign{RecordConstruct}`
    /// (which the C001 verifier rejects for a cap dst), `CapMint` is a
    /// legitimate cap SOURCE. The Z3 oracle seeds its `dst` legitimate (the
    /// mint authority gate is discharged at type-check, before AIR — see the
    /// SpawnActor precedent). `cap_name` is the minted authority cap-type
    /// name; `params` the (erased) deadline literals; `target` is provenance
    /// only and value-erased at the wasm boundary.
    CapMint {
        dst: VarId,
        cap_name: String,
        params: Vec<i64>,
        target: VarId,
    },
    /// `slot_new::<T>()` — construct an empty `Slot<T>`. Emits a
    /// BumpAlloc-like 8-byte cell and stores tag=0 at offset 0. The
    /// `cap_type` is preserved so the Z3 layer knows which authority
    /// the future SlotTake should propagate.
    SlotNew {
        dst: VarId,
        cap_type: String,
    },
    /// `slot_put(slot, cap)` — mutate the slot in place to hold `cap`.
    /// Wasm emission inserts a runtime trap if the slot is already
    /// full (tag != 0). The cap is consumed (ownership.rs marks it
    /// moved).
    SlotPut {
        slot: VarId,
        cap: VarId,
    },
    /// `slot_take(slot) -> Cap` — read the cap out and clear the slot.
    /// Wasm emission inserts a runtime trap if the slot is empty
    /// (tag == 0). The Z3 source rule constrains `dst_cap`'s
    /// authority to the conservative meet (bitwise AND) of every
    /// SlotPut's authority for this slot — sound for multi-branch
    /// puts without a phi-merge encoding.
    SlotTake {
        dst_cap: VarId,
        slot: VarId,
    },
    SerializeMessage {
        msg: VarId,
        args: Vec<VarId>,
        dst_buf: VarId,
        dst_len: VarId,
    },
    DeserializeMessage {
        src_buf: VarId,
        src_len: VarId,
        dst: VarId,
    },
    /// PPS-2a: allocate `len` bytes on the PERSISTENT channel and copy `len` bytes from `src`
    /// into them, yielding the new pointer in `dst`. The byte-buffer analogue of a persistent
    /// `BumpAlloc`: a `str`'s payload has a RUNTIME length, so promotion cannot be a fixed
    /// sequence of field copies. Emitted only by state-store promotion; never by user code.
    PromoteBytes {
        dst: VarId,
        src: VarId,
        len: VarId,
    },
    BumpAlloc {
        dst: VarId,
        size_bytes: u32,
        align: u32,
        /// PPS-0: route this header allocation to `alloc_persistent`. True ONLY inside a
        /// state-backed mono instance (suffix [`STATE_VEC_MONO_SUFFIX`]) — a `Map`'s rehash
        /// replaces its interior `Vec` HEADERS, which are record constructs (BumpAlloc), not
        /// `alloc` intrinsics. False everywhere else, so every existing record construct and the
        /// whole stateless capstone stay byte-identical.
        persistent: bool,
    },
    IntrinsicAlloc {
        dst: VarId,
        size: VarId,
        /// AGG2b-2: route this allocation to the `alloc_persistent` host channel (the B1
        /// floor-raise) instead of `alloc`. True ONLY inside a state-backed `Vec<scalar>` mono
        /// instance (name suffix [`STATE_VEC_MONO_SUFFIX`]); false everywhere else — so every
        /// existing alloc, and the entire stateless self-host capstone, lowers byte-identically.
        persistent: bool,
    },
    IntrinsicLoad8 {
        dst: VarId,
        ptr: VarId,
    },
    IntrinsicStore8 {
        ptr: VarId,
        val: VarId,
    },
    /// Phase 2H §3.5: branch-free constant-time equality.
    /// Emits `i64.eqz` over `i64.xor(a, b)`. No conditional branch.
    IntrinsicCtEq {
        dst: VarId,
        lhs: VarId,
        rhs: VarId,
    },
    /// Phase 2H §3.5: branch-free select.
    /// Emits `f ^ ((t ^ f) & -c)` where `c` is `cond as i64`.
    /// Never lowered to Wasm `select` (which some backends compile
    /// to a CPU branch on certain ISAs).
    IntrinsicCtSelect {
        dst: VarId,
        cond: VarId,
        then_val: VarId,
        else_val: VarId,
    },
    /// Phase 2H §3.5: branch-free signed less-than.
    /// Emits `((a - b) >> 63) & 1`. Constant shift amount; data-independent.
    IntrinsicCtLt {
        dst: VarId,
        lhs: VarId,
        rhs: VarId,
    },
    LoadDynamic {
        dst: VarId,
        base_ptr: VarId,
        index: VarId,
        elem_size: u32,
        ty: AirType,
        /// Byte offset added to `base_ptr` before `index * elem_size`: `4`
        /// for arrays/slices (skip the length header), `0` for raw buffers
        /// (e.g. a `Vec`'s element buffer, which has no header).
        offset: u32,
    },
    StoreDynamic {
        base_ptr: VarId,
        index: VarId,
        elem_size: u32,
        val: VarId,
        ty: AirType,
        /// See [`AirStmt::LoadDynamic`]'s `offset`.
        offset: u32,
    },
    TrapIf {
        cond: VarId,
    },
    /// Wrap a 64-bit integer to 32-bit (I32WrapI64 in Wasm).
    /// Used for array index narrowing when indices are i64.
    WrapI64 {
        dst: VarId,
        src: VarId,
    },
    /// Zero-extend a 32-bit integer to 64-bit (I64ExtendI32U in Wasm).
    /// Used so the `str` accessors (`len`, `byte_at`) yield i64 — the byte and
    /// length domains are UNSIGNED, so the extension must be zero-fill.
    ExtendU32 {
        dst: VarId,
        src: VarId,
    },
    /// Sign-extend a 32-bit integer to 64-bit (I64ExtendI32S in Wasm). The
    /// SIGNED counterpart of `ExtendU32` — used when an `i32` value widens to
    /// `i64`/`u64` so a negative i32 stays negative (the `.as_i64()`/`.as_u64()`
    /// conversion on an i32 receiver).
    SignExtendI32 {
        dst: VarId,
        src: VarId,
    },
    /// Indirect function call through Wasm table (for closures).
    CallIndirect {
        dst: Option<VarId>,
        /// (param_types, return_type) — used to look up the Wasm type index
        signature: (Vec<AirType>, AirType),
        /// VarId holding the table index (loaded from closure struct offset 0)
        table_index: VarId,
        /// args[0] = env_ptr (the closure struct pointer), rest = user args
        args: Vec<VarId>,
    },
    /// Grant markers for audit trail (bracket a closure call with cap lending)
    GrantBegin {
        grant_id: u32,
        cap_var: VarId,
    },
    GrantEnd {
        grant_id: u32,
    },
    /// Borrow: creates a reference to src. Wasm-equivalent to Assign (pointer copy),
    /// but gives the ownership checker explicit provenance tracking for O007.
    Borrow {
        dst: VarId,
        src: VarId,
        mutable: bool,
    },
    /// FFI extern call: call an imported function by name.
    ExternCall {
        dst: Option<VarId>,
        extern_name: String,
        args: Vec<VarId>,
    },
    /// Region memory begin: snapshot BUMP_PTR into `save_var` when reclamation
    /// is enabled for this function kind.
    RegionBegin {
        name: String,
        limit_var: VarId,
        save_var: VarId,
    },
    /// Region memory end: trap when net allocation exceeds `limit_var`, then
    /// restore BUMP_PTR from `save_var` where reclamation is enabled.
    RegionEnd {
        name: String,
        limit_var: VarId,
        save_var: VarId,
    },
}

impl AirStmt {
    /// Preserve the constructor distinction that the v8 actor-boundary opcode
    /// collapses. The exhaustive non-actor arm forces each new AIR constructor
    /// to make an explicit classification decision; no operand-arity inference
    /// or unknown-constructor fallback can silently erase an actor operation.
    pub const fn actor_operation(&self) -> Option<AirActorOperation> {
        match self {
            Self::MessageSend { .. } => Some(AirActorOperation::Send),
            Self::MessageAsk { .. } => Some(AirActorOperation::Ask),
            Self::SpawnActor { .. } => Some(AirActorOperation::Spawn),
            Self::SerializeMessage { .. } => Some(AirActorOperation::Serialize),
            Self::DeserializeMessage { .. } => Some(AirActorOperation::Deserialize),
            Self::Assign { .. }
            | Self::StoreField { .. }
            | Self::LoadField { .. }
            | Self::StateRead { .. }
            | Self::StateWrite { .. }
            | Self::SecurityRelease { .. }
            | Self::Call { .. }
            | Self::FuelDecrement { .. }
            | Self::ResultTry { .. }
            | Self::OptionTry { .. }
            | Self::ArrayOrSliceContains { .. }
            | Self::StrBytesEq { .. }
            | Self::SliceOptionElem { .. }
            | Self::CapRestrict { .. }
            | Self::CapSplit { .. }
            | Self::CapDraw { .. }
            | Self::CapMint { .. }
            | Self::SlotNew { .. }
            | Self::SlotPut { .. }
            | Self::SlotTake { .. }
            | Self::PromoteBytes { .. }
            | Self::BumpAlloc { .. }
            | Self::IntrinsicAlloc { .. }
            | Self::IntrinsicLoad8 { .. }
            | Self::IntrinsicStore8 { .. }
            | Self::IntrinsicCtEq { .. }
            | Self::IntrinsicCtSelect { .. }
            | Self::IntrinsicCtLt { .. }
            | Self::LoadDynamic { .. }
            | Self::StoreDynamic { .. }
            | Self::TrapIf { .. }
            | Self::WrapI64 { .. }
            | Self::ExtendU32 { .. }
            | Self::SignExtendI32 { .. }
            | Self::CallIndirect { .. }
            | Self::GrantBegin { .. }
            | Self::GrantEnd { .. }
            | Self::Borrow { .. }
            | Self::ExternCall { .. }
            | Self::RegionBegin { .. }
            | Self::RegionEnd { .. } => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AirReleaseStage {
    Ordinary,
    ConstantTime,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AirTerminator {
    Return(Option<VarId>),
    Jump(BlockId),
    Loop {
        cond: VarId,
        body_block: BlockId,
        exit_block: BlockId,
    },
    Branch {
        cond: VarId,
        then_block: BlockId,
        else_block: BlockId,
        merge_block: Option<BlockId>,
    },
    /// Flat `match` dispatch wrapper. Emits a single enclosing wasm `block`; the
    /// arm-test chain is lowered starting at `start` and every arm body ends in a
    /// `Jump(exit)` that the wasm emitter turns into a `br` OUT of this block.
    /// Because the whole match shares ONE enclosing block, the dispatch is FLAT
    /// (each arm is `if (cond) { body; br } ` at the same nesting level) rather
    /// than a deeply nested `if/else` cascade — so neither AIR lowering nor wasm
    /// emission recurses with arm count, and large/long matches no longer
    /// overflow the native stack. The arm-test Branches all carry an EXPLICIT
    /// `merge_block` (their `else` target), so the wasm emitter never has to
    /// compute a merge via the recursive fallthrough walk.
    Dispatch {
        /// First block of the arm-test chain (lowered inside the enclosing block).
        start: BlockId,
        /// Join block after the whole match — arm bodies `Jump` here (→ `br`),
        /// and control continues here once the dispatch block closes.
        exit: BlockId,
    },
    Unreachable,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AirValue {
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StrLit(String),
    UnitLit,
    Var(VarId),
    Binary {
        lhs: VarId,
        op: BinaryOp,
        rhs: VarId,
    },
    RecordConstruct {
        fields: Vec<(String, VarId)>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BlockId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FuncId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ActorTypeId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AirSupervisionStrategy {
    #[default]
    Stop,
    Restart {
        max_restarts: u32,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HandlerId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AirFunctionKind {
    ModuleInit,
    ModuleFunction,
    ActorInit {
        actor: String,
        actor_type: ActorTypeId,
        is_entry: bool,
    },
    ActorHandler {
        actor: String,
        actor_type: ActorTypeId,
        handler: String,
        handler_id: HandlerId,
        is_entry: bool,
    },
    Closure,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AirType {
    Unit,
    Bool,
    I32,
    U32,
    I64,
    U64,
    F64,
    Ptr,
}

impl AirType {
    /// Byte width of this type in linear memory layout.
    pub fn width(self) -> u32 {
        match self {
            Self::I64 | Self::U64 | Self::F64 => 8,
            Self::I32 | Self::U32 | Self::Bool | Self::Ptr => 4,
            Self::Unit => 0,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AirValueKind {
    Copy,
    Linear,
    Cap(String), // carries cap type name for Z3 authority mask lookup
    /// A capability READ from immutable actor state (M4). Carries the cap type
    /// name — treated EXACTLY like `Cap` by the Z3 authority layer (full
    /// authority, sink-probed) so state caps keep their `.restrict`/`.draw`
    /// authority checking. The distinction is for LINEAR-CONSUMPTION only:
    /// `ownership::verify` rejects a CONSUMING move of a `StateCap` inside an
    /// ordinary handler (borrow-only; C010), while permitting it during the
    /// construction phase (`init` / entry `Start`). `grant(&s)` / `s.draw(n)`
    /// are non-consuming and stay legal everywhere.
    StateCap(String),
    /// `Slot<Cap>` — heap pointer that aliases safely under the
    /// single-threaded actor model (INV-11). Carries the inner cap-
    /// type name. Distinguished from `Copy` so the capability verifier
    /// can accept slots alongside caps at SpawnActor (Wall 1 Step 3).
    Slot(String),
}

impl AirValueKind {
    pub fn is_linear(&self) -> bool {
        // Slot is non-linear (heap pointer, multiple references safe under
        // single-threaded actors); the cap INSIDE the slot is the linear
        // value, tracked separately via SlotPut/SlotTake's Z3 source rule.
        // StateCap is linear so the move tracker reaches it (borrow-vs-consume).
        matches!(self, Self::Linear | Self::Cap(_) | Self::StateCap(_))
    }

    pub fn is_cap(&self) -> bool {
        // A StateCap is a cap for authority purposes — the Z3 layer must keep
        // treating it as a full-authority cap or it silently drops out of the
        // authority system (fail-open). Consumption is gated separately.
        matches!(self, Self::Cap(_) | Self::StateCap(_))
    }

    /// The cap type name for a `Cap` or `StateCap`, else `None`. Lets the Z3
    /// layer read the cap type uniformly across both kinds.
    pub fn cap_type_name(&self) -> Option<&str> {
        match self {
            Self::Cap(name) | Self::StateCap(name) => Some(name.as_str()),
            _ => None,
        }
    }

    pub fn is_slot(&self) -> bool {
        matches!(self, Self::Slot(_))
    }
}

/// HOF / N10-HOF: byte offset of the function-table index inside a
/// closure heap struct. Single symbolic constant referenced by
/// BOTH `lower_closure_construct` (StoreField at construction time)
/// AND `lower_indirect_call_expr` (LoadField at dispatch time). If
/// the closure layout ever moves the table_idx field, both sites
/// pick up the new offset in lockstep.
pub const CLOSURE_TABLE_IDX_OFFSET: u32 = 0;

/// PR AF / N13-AF: byte offset of the `data_ptr` field within a
/// fat-pointer slice header. A `Type::Slice` value at runtime is a
/// pointer to an 8-byte BumpAlloc with layout `[data_ptr: u32 @0,
/// len: u32 @4]`.
///
/// `data_ptr` semantics: it is computed so that
/// `LoadDynamic { base_ptr: data_ptr, index, elem_size }` reads the
/// correct slice element. Because `LoadDynamic`'s wasm lowering
/// bakes a `+4` header offset into its `mem_arg` (see
/// `wasm.rs:1112` "address = base_ptr + index * elem_size (with +4
/// baked into mem_arg)"), `data_ptr` is set to:
/// - `arr_ptr` (the array's BumpAlloc start) for `&arr` borrows —
///   LoadDynamic's +4 then skips the array's header to reach
///   element 0.
/// - `arr_ptr + lo*elem_size` for `&arr[lo..hi]` (commit #4) —
///   LoadDynamic's +4 plus the lo-shifted base lands at the
///   first slice element.
pub const SLICE_DATA_PTR_OFFSET: u32 = 0;

/// PR AF / N13-AF: byte offset of the `len` field within a
/// fat-pointer slice header. Read by `slice_len_var` for `.len()`
/// and `.is_empty()` intrinsics and for the bounds checks in the
/// slice operator (commit #4). Drift between this constant and
/// `SLICE_DATA_PTR_OFFSET` is caught by the
/// `slice_layout_constants_are_pinned` unit test.
pub const SLICE_LEN_OFFSET: u32 = 4;

/// PR AF / N19-AF: byte size of the slice header BumpAlloc. 8 bytes
/// total: 4 for `data_ptr` (u32) + 4 for `len` (u32).
pub const SLICE_HEADER_SIZE: u32 = 8;

/// PR AF / N19-AF: alignment of the slice header BumpAlloc.
/// 4-byte alignment matches the u32 field alignment; deliberately
/// NOT 8 (the other heap allocations use 8-byte alignment but the
/// slice header has no 8-byte fields).
pub const SLICE_HEADER_ALIGN: u32 = 4;

/// PR S1 / N20-S1 + N28-S1: byte offset of the `data_ptr` field
/// within a fat-pointer string header. Intentionally identical to
/// `SLICE_DATA_PTR_OFFSET` because the runtime layout of `Type::Str`
/// mirrors `Type::Slice(u8)` — a `str` IS a UTF-8-validated view over
/// bytes. Separate declaration site so call sites can express
/// "this is a Str-layout access" semantically.
pub const STR_DATA_PTR_OFFSET: u32 = 0;

/// PR S1 / N20-S1 + N28-S1: byte offset of the `len` field within a
/// fat-pointer string header. Read by `.len()` / `.is_empty()` and
/// by the slice operator's bounds check. Drift between this and
/// `STR_DATA_PTR_OFFSET` is caught by the `str_layout_constants_are_pinned`
/// unit test.
pub const STR_LEN_OFFSET: u32 = 4;

/// PR S1 / N17-S1: byte size of the string header BumpAlloc. 8 bytes
/// total: 4 for `data_ptr` (u32) + 4 for `len` (u32). Identical to
/// `SLICE_HEADER_SIZE` (intentional layout parity per N20-S1).
pub const STR_HEADER_SIZE: u32 = 8;

/// PR S1 / N17-S1: alignment of the string header BumpAlloc.
/// 4-byte alignment matches the u32 field alignment.
pub const STR_HEADER_ALIGN: u32 = 4;

/// PR OptTry / N15-OptTry: byte offset of the discriminant tag within
/// an Option<T> heap struct. Locked at 0 — the tag is the first field
/// per PR B's generic enum machinery + N28-PRB positional declaration
/// order (Some=variant 0, None=variant 1). Reads via OptionTry's
/// wasm emission reference this constant by name.
pub const OPTION_TAG_OFFSET: u32 = 0;

/// PR OptTry / N15-OptTry: byte size of the Option tag field. 4 bytes
/// (i32). Matches PR B's generic enum tag width — see N28-PRB.
pub const OPTION_TAG_SIZE_BYTES: u32 = 4;

/// PR OptTry / N15-OptTry: byte offset of the payload field within an
/// `Option<T>` heap struct. The Some payload follows the tag at offset
/// 4 (no alignment padding per `flatten_record`'s sequential layout).
pub const OPTION_PAYLOAD_OFFSET: u32 = 4;

/// PR OptTry / N16-OptTry: tag value indicating `Some(_)`. Locked
/// at 0 per `stdlib/sigil/option.sigil`'s positional declaration order
/// (`Some(T)` is variant 0, `None` is variant 1). A pre-flight unit
/// test (`option_variant_indices_locked`, future commit #4) parses the
/// stdlib file and asserts this matches.
pub const OPTION_SOME_TAG: i32 = 0;

/// PR OptTry / N16-OptTry: tag value indicating `None`. Locked at 1
/// per the same positional order as OPTION_SOME_TAG.
pub const OPTION_NONE_TAG: i32 = 1;

/// PR OptTry / N11-OptTry: structural carrier classifier. Returns true
/// iff `ty` is `Type::Named("Option", [_])`. Used by `lower_try_expr`
/// dispatch to choose between `AirStmt::OptionTry` and
/// `AirStmt::ResultTry`. Single canonical helper — CI grep-lint
/// forbids inline `name == "Option"` patterns inside `lower_try_expr`.
pub fn is_option_carrier(ty: &Type) -> bool {
    matches!(ty, Type::Named(name, args) if name == "Option" && args.len() == 1)
}

/// Maps record type name → [(field_name, byte_offset, AirType)]
type FieldRegistry = LookupMap<String, Vec<(String, u32, AirType)>>;

/// Precomputed enum layout info for tagged union codegen.
/// `total_size` already includes the 4-byte tag plus the max payload, so
/// no separate `max_payload_bytes` field is stored.
struct EnumInfo {
    variants: Vec<(String, Vec<AirType>)>,
    total_size: u32,
}

type EnumRegistry = LookupMap<String, EnumInfo>;

/// One actor's state struct layout: `(field, byte_offset, AirType)` in
/// declaration order, plus the total struct size aligned up to 8 bytes.
pub(crate) struct ActorStateLayout {
    pub fields: Vec<(String, u32, AirType)>,
    pub size: u32,
}

/// THE state-field placement authority (SC-4): both AIR lowering (M3) and the
/// `RuntimeActorSpec.state_layout` emitted by the compiler derive every offset
/// and the struct size from this one function, so they can never disagree.
///
/// Actor state fields arrive as the `captures` of an actor's init/handler
/// `TypedFunction` (see `build_actor_captures`); we place them 0-based by
/// width accumulation (NO 4-byte closure table-index prefix — a state struct is
/// not a closure `__env`) and align the total up to 8 (matching the arena /
/// bump-allocator alignment).
pub(crate) fn state_layout_offsets(captures: &[TypedParam]) -> ActorStateLayout {
    let mut offset = 0u32;
    let fields = captures
        .iter()
        .map(|cap| {
            let air_ty = lower_type(&cap.ty);
            let entry = (cap.name.clone(), offset, air_ty);
            offset += air_ty.width();
            entry
        })
        .collect();
    let size = (offset + 7) & !7; // align up to 8
    ActorStateLayout { fields, size }
}

fn build_field_registry(program: &TypedProgram) -> FieldRegistry {
    let mut registry = LookupMap::new();

    // Bare-name entries (non-generic records use these directly; generic
    // records get them too as a fallback for source-record-level
    // metadata, though `lower_field_access` now always uses the mangled
    // name when type_args is non-empty).
    for (type_name, (_type_params, fields)) in &program.records {
        let mut offset = 0u32;
        let entries: Vec<(String, u32, AirType)> = fields
            .iter()
            .map(|(name, ty)| {
                let air_ty = lower_type(ty);
                let width = air_ty.width();
                let entry = (name.clone(), offset, air_ty);
                offset += width;
                entry
            })
            .collect();
        registry.insert(type_name.clone(), entries);
    }

    // PR D follow-up (AG-PRDF-19 closure): per-instantiation entries
    // for generic record types. Walks every TypedFunction's params +
    // ret + body collecting every `Type::Named(name, args)` reference
    // where `args` is non-empty AND `program.records` knows `name`.
    // For each unique instantiation, builds a registry entry keyed by
    // the mangled type name (matching `lower_field_access`'s lookup
    // key at air.rs:1208-1212) with field types substituted against
    // the args.
    //
    // Without this, `lower_field_access` on a generic record's field
    // (e.g., `h.value` for `h: Holder<i64>`) panics with "no field
    // registry for type Holder__i64" — surfaced by the N17 fixture
    // in PR D follow-up commit #1.
    // Registry insertion follows this iteration, so keep it ordered explicitly.
    let mut instantiations: BTreeMap<String, (String, Vec<Type>)> = BTreeMap::new();
    for module in &program.modules {
        for function in &module.functions {
            for param in &function.params {
                collect_named_instantiations(&param.ty, &mut instantiations);
            }
            collect_named_instantiations(&function.ret, &mut instantiations);
            collect_from_typed_block(&function.body, &mut instantiations);
        }
    }

    for (mangled, (name, args)) in &instantiations {
        if let Some((type_params, fields)) = program.records.get(name) {
            // N6-PRDF / N10-PRDF inheritance: only build per-instantiation
            // entries when arity matches; malformed Type::Named with
            // mismatched arity is upstream's problem (T231 / construction
            // checker) and is skipped here to avoid masking.
            if type_params.is_empty() || type_params.len() != args.len() {
                continue;
            }
            let subst: TypeSubstitution = type_params
                .iter()
                .zip(args.iter())
                .map(|(p, a)| (p.clone(), a.clone()))
                .collect();
            let mut offset = 0u32;
            let entries: Vec<(String, u32, AirType)> = fields
                .iter()
                .map(|(fname, fty)| {
                    let substituted = apply_subst(fty, &subst);
                    let air_ty = lower_type(&substituted);
                    let width = air_ty.width();
                    let entry = (fname.clone(), offset, air_ty);
                    offset += width;
                    entry
                })
                .collect();
            registry.insert(mangled.clone(), entries);
        }
    }

    registry
}

/// PR D follow-up: collect `(name, args)` pairs for every
/// `Type::Named(name, args)` reference where `args` is non-empty,
/// recursively descending through nested generic args. Used by
/// `build_field_registry` to enumerate every monomorphized record
/// instantiation that needs a registry entry.
fn collect_named_instantiations(ty: &Type, out: &mut BTreeMap<String, (String, Vec<Type>)>) {
    match ty {
        Type::Named(name, args) => {
            if !args.is_empty() {
                // Key by mangled name so distinct instantiations
                // (e.g., Holder<i64> vs Holder<bool>) each get their
                // own entry. `Type` doesn't implement Eq/Hash, so we
                // cannot use a HashSet<(String, Vec<Type>)>; the
                // ordered mangled-name map is the workaround.
                let mangled = mangle_type(ty);
                out.entry(mangled)
                    .or_insert_with(|| (name.clone(), args.clone()));
            }
            for arg in args {
                collect_named_instantiations(arg, out);
            }
        }
        Type::Array { elem, .. } => collect_named_instantiations(elem, out),
        Type::Ref(inner, _) => collect_named_instantiations(inner, out),
        Type::Slice(inner) => collect_named_instantiations(inner, out),
        Type::Ptr(inner) | Type::MutPtr(inner) => collect_named_instantiations(inner, out),
        Type::Fn(params, ret, _, _) => {
            for p in params {
                collect_named_instantiations(p, out);
            }
            collect_named_instantiations(ret, out);
        }
        // ET-9: recurse into tuple elements to find nested generic records
        // (e.g. `(Holder<i64>, i64)` must register Holder<i64>). No registry
        // entry is emitted for the tuple itself — its read path is on-demand.
        Type::Tuple(elems) => {
            for e in elems {
                collect_named_instantiations(e, out);
            }
        }
        _ => {}
    }
}

/// PR D follow-up: recursively walk a `TypedBlock`, collecting
/// generic-instantiation references from every `TypedExpr.ty` and
/// every statement-level type annotation. Drives the per-instantiation
/// registry build in `build_field_registry`.
fn collect_from_typed_block(block: &TypedBlock, out: &mut BTreeMap<String, (String, Vec<Type>)>) {
    for stmt in &block.statements {
        match stmt {
            TypedStmt::Let(s) => {
                collect_named_instantiations(&s.ty, out);
                collect_from_typed_expr(&s.value, out);
            }
            TypedStmt::Assign(s) => collect_from_typed_expr(&s.value, out),
            TypedStmt::Expr(s) => collect_from_typed_expr(&s.expr, out),
            TypedStmt::If(s) => {
                collect_from_typed_expr(&s.condition, out);
                collect_from_typed_block(&s.then_branch, out);
                collect_from_typed_block(&s.else_branch, out);
            }
            TypedStmt::Match(s) => {
                collect_from_typed_expr(&s.scrutinee, out);
                for arm in &s.arms {
                    if let TypedPattern::EnumVariant { bindings, .. } = &arm.pattern {
                        for (_, bty) in bindings {
                            collect_named_instantiations(bty, out);
                        }
                    }
                    if let Some(guard) = &arm.guard {
                        collect_from_typed_expr(guard, out);
                    }
                    collect_from_typed_block(&arm.body, out);
                }
            }
            TypedStmt::While(s) => {
                collect_from_typed_expr(&s.condition, out);
                collect_from_typed_block(&s.body, out);
            }
            TypedStmt::ForIn(s) => {
                // ForIn has an iterator expr + body; the iterator type
                // contributes generic instantiations the body may
                // reference.
                let _ = s; // touched here to satisfy match exhaustiveness; field walking happens via existing helpers
                collect_typed_for_in(s, out);
            }
            TypedStmt::ForRange(s) => {
                // Range bounds are plain i64 exprs; the body may still
                // reference generic instantiations.
                collect_from_typed_expr(&s.start, out);
                collect_from_typed_expr(&s.end, out);
                for inner in &s.body {
                    collect_from_typed_stmt(inner, out);
                }
            }
            TypedStmt::Return(s) => {
                if let Some(v) = &s.value {
                    collect_from_typed_expr(v, out);
                }
            }
            // break/continue carry no types to collect.
            TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
        }
    }
}

fn collect_typed_for_in(
    s: &crate::type_check::TypedForInStmt,
    out: &mut BTreeMap<String, (String, Vec<Type>)>,
) {
    collect_named_instantiations(&s.elem_type, out);
    collect_from_typed_expr(&s.iterable, out);
    // TypedForInStmt.body is Vec<TypedStmt>, not TypedBlock. Reuse the
    // statement-walker shape by wrapping in a synthetic block-style
    // dispatch.
    for stmt in &s.body {
        collect_from_typed_stmt(stmt, out);
    }
}

/// Statement-level dispatcher extracted so `collect_typed_for_in` can
/// reuse it (its `body` is `Vec<TypedStmt>` rather than `TypedBlock`).
fn collect_from_typed_stmt(stmt: &TypedStmt, out: &mut BTreeMap<String, (String, Vec<Type>)>) {
    match stmt {
        TypedStmt::Let(s) => {
            collect_named_instantiations(&s.ty, out);
            collect_from_typed_expr(&s.value, out);
        }
        TypedStmt::Assign(s) => collect_from_typed_expr(&s.value, out),
        TypedStmt::Expr(s) => collect_from_typed_expr(&s.expr, out),
        TypedStmt::If(s) => {
            collect_from_typed_expr(&s.condition, out);
            collect_from_typed_block(&s.then_branch, out);
            collect_from_typed_block(&s.else_branch, out);
        }
        TypedStmt::Match(s) => {
            collect_from_typed_expr(&s.scrutinee, out);
            for arm in &s.arms {
                if let TypedPattern::EnumVariant { bindings, .. } = &arm.pattern {
                    for (_, bty) in bindings {
                        collect_named_instantiations(bty, out);
                    }
                }
                if let Some(guard) = &arm.guard {
                    collect_from_typed_expr(guard, out);
                }
                collect_from_typed_block(&arm.body, out);
            }
        }
        TypedStmt::While(s) => {
            collect_from_typed_expr(&s.condition, out);
            collect_from_typed_block(&s.body, out);
        }
        TypedStmt::ForIn(s) => collect_typed_for_in(s, out),
        TypedStmt::ForRange(s) => {
            collect_from_typed_expr(&s.start, out);
            collect_from_typed_expr(&s.end, out);
            for inner in &s.body {
                collect_from_typed_stmt(inner, out);
            }
        }
        TypedStmt::Return(s) => {
            if let Some(v) = &s.value {
                collect_from_typed_expr(v, out);
            }
        }
        // break/continue carry no types to collect.
        TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
    }
}

fn collect_from_typed_expr(expr: &TypedExpr, out: &mut BTreeMap<String, (String, Vec<Type>)>) {
    collect_named_instantiations(&expr.ty, out);
    match &expr.kind {
        // A state read carries no nested exprs or type-args of its own.
        TypedExprKind::Literal(_) | TypedExprKind::Local(_) | TypedExprKind::StateField(_) => {}
        // PR-E3: collect monomorph instantiations from f-string holes.
        TypedExprKind::FString(fs) => {
            for part in &fs.parts {
                if let crate::typed_ast::TypedFStringPart::Hole(h) = part {
                    collect_from_typed_expr(h, out);
                }
            }
        }
        TypedExprKind::Call(c) => {
            for a in &c.args {
                collect_from_typed_expr(a, out);
            }
        }
        TypedExprKind::Intrinsic(i) => {
            for a in &i.args {
                collect_from_typed_expr(a, out);
            }
        }
        TypedExprKind::ResultCtor(r) => collect_from_typed_expr(&r.value, out),
        TypedExprKind::EnumConstruct(e) => {
            for f in &e.fields {
                collect_from_typed_expr(f, out);
            }
        }
        TypedExprKind::Try(t) => collect_from_typed_expr(&t.value, out),
        TypedExprKind::Send(s) => {
            for a in &s.args {
                collect_from_typed_expr(a, out);
            }
        }
        TypedExprKind::Ask(a) => {
            for arg in &a.args {
                collect_from_typed_expr(arg, out);
            }
            collect_from_typed_expr(&a.timeout, out);
        }
        TypedExprKind::Spawn(sp) => {
            for a in &sp.args {
                collect_from_typed_expr(a, out);
            }
        }
        TypedExprKind::Binary(b) => {
            collect_from_typed_expr(&b.lhs, out);
            collect_from_typed_expr(&b.rhs, out);
        }
        TypedExprKind::RecordConstruct(r) => {
            for (_, fv) in &r.fields {
                collect_from_typed_expr(fv, out);
            }
        }
        TypedExprKind::FieldAccess(f) => collect_from_typed_expr(&f.object, out),
        TypedExprKind::CapRestrict(_) => {}
        TypedExprKind::CapSplit(c) => collect_from_typed_expr(&c.amount, out),
        TypedExprKind::CapDraw(c) => collect_from_typed_expr(&c.amount, out),
        TypedExprKind::Mint(m) => collect_from_typed_expr(&m.target, out),
        TypedExprKind::ArrayLit(a) => {
            collect_named_instantiations(&a.elem_type, out);
            for e in &a.elements {
                collect_from_typed_expr(e, out);
            }
        }
        TypedExprKind::Index(i) => {
            collect_named_instantiations(&i.elem_type, out);
            collect_from_typed_expr(&i.array, out);
            collect_from_typed_expr(&i.index, out);
        }
        // PR AF commit #1 scaffolding: walk children for type
        // instantiations. Commit #4 wires the real lowering.
        TypedExprKind::Slice(s) => {
            collect_named_instantiations(&s.elem_type, out);
            collect_from_typed_expr(&s.array, out);
            if let Some(start) = &s.start {
                collect_from_typed_expr(start, out);
            }
            if let Some(end) = &s.end {
                collect_from_typed_expr(end, out);
            }
        }
        TypedExprKind::ClosureConstruct(c) => {
            for cap in &c.captures {
                collect_named_instantiations(&cap.ty, out);
            }
            for p in &c.param_types {
                collect_named_instantiations(p, out);
            }
            collect_named_instantiations(&c.ret_type, out);
        }
        TypedExprKind::Borrow(b) => collect_from_typed_expr(&b.inner, out),
        TypedExprKind::Grant(g) => {
            collect_from_typed_expr(&g.cap, out);
            collect_from_typed_expr(&g.body, out);
        }
        // HOF / N9-HOF: explicit IndirectCall arm. Recurse args
        // for nested generic instantiations + scan callee_ty in
        // case a closure's Type::Fn carries a Type::Named with
        // type-args that need monomorphization-table entries
        // (e.g., Fn(Holder<i64>) -> i64).
        TypedExprKind::IndirectCall(c) => {
            collect_named_instantiations(&c.callee_ty, out);
            for a in &c.args {
                collect_from_typed_expr(a, out);
            }
        }
        TypedExprKind::Handle(h) => collect_from_typed_block(&h.body, out),
        // Effect Handlers (EH3, C-VIS): collect monomorph instantiations from the
        // new nodes' sub-expressions (harmless whether or not they are gated).
        TypedExprKind::Perform(p) => {
            for arg in &p.args {
                collect_from_typed_expr(arg, out);
            }
        }
        TypedExprKind::ClauseHandle(c) => {
            collect_from_typed_expr(&c.scrutinee, out);
            for clause in &c.clauses {
                collect_from_typed_block(&clause.body, out);
            }
        }
        TypedExprKind::Resume(r) => collect_from_typed_expr(&r.value, out),
        TypedExprKind::Declassify(d) => {
            collect_from_typed_expr(&d.value, out);
            collect_from_typed_expr(&d.cap, out);
        }
        TypedExprKind::DeclassifyCt(d) => {
            collect_from_typed_expr(&d.value, out);
            collect_from_typed_expr(&d.cap, out);
        }
        TypedExprKind::ExternCall(e) => {
            for a in &e.args {
                collect_from_typed_expr(a, out);
            }
        }
        TypedExprKind::Region(r) => {
            collect_from_typed_expr(&r.limit, out);
            collect_from_typed_block(&r.body, out);
        }
    }
}

fn build_enum_registry(program: &TypedProgram) -> EnumRegistry {
    let mut registry = LookupMap::new();

    for (enum_name, (_type_params, variants)) in &program.enums {
        let mut max_payload = 0u32;
        let lowered_variants: Vec<(String, Vec<AirType>)> = variants
            .iter()
            .map(|(name, payload_types)| {
                let air_types: Vec<AirType> = payload_types.iter().map(lower_type).collect();
                let payload_size: u32 = air_types.iter().map(|ty| ty.width()).sum();
                if payload_size > max_payload {
                    max_payload = payload_size;
                }
                (name.clone(), air_types)
            })
            .collect();

        registry.insert(
            enum_name.clone(),
            EnumInfo {
                variants: lowered_variants,
                total_size: 4 + max_payload,
            },
        );
    }

    registry
}

/// Convert a structural Type into a flat mangled string for registry keys and Wasm export names.
/// Recursive — handles nested generics: Result<Option<i64>, str> → "Result__Option__i64$str".
///
/// R2 (HK3 hardening): multi-argument lists are joined with `$` (a char OUTSIDE
/// the SIGIL identifier grammar, like the `$tuple` prefix), NOT `_`. With `_` the
/// mangle was NON-INJECTIVE — `g<Foo_Bar, X>` and `g<Foo, Bar_X>` both flattened
/// to `…Foo_Bar_X`, fusing two distinct monomorphizations into one. A `$`
/// separator can never appear inside a user type name, so for a fixed arity the
/// argument list is recoverable. The single-argument forms (`Box__i64`) are
/// unchanged. (The `__` infix between a name and its args is reserved from user
/// type names by T271, so an instance key can't collide with a user record.)
pub fn mangle_type(ty: &Type) -> String {
    match ty {
        Type::I32 => "i32".into(),
        Type::U32 => "u32".into(),
        Type::I64 => "i64".into(),
        Type::U64 => "u64".into(),
        Type::F64 => "f64".into(),
        Type::U256 => "u256".into(),
        Type::I256 => "i256".into(),
        Type::Bool => "bool".into(),
        Type::Str => "str".into(),
        Type::Unit => "unit".into(),
        Type::Cap(name, _) => format!("cap_{name}"),
        Type::ActorRef(name) => format!("ActorRef_{name}"),
        Type::Array { elem, size } => format!("Array__{}${size}", mangle_type(elem)),
        Type::Ref(inner, false) => format!("ref_{}", mangle_type(inner)),
        Type::Ref(inner, true) => format!("ref_mut_{}", mangle_type(inner)),
        Type::Slice(inner) => format!("slice__{}", mangle_type(inner)),
        Type::Named(name, args) if args.is_empty() => name.clone(),
        Type::Named(name, args) => {
            // Typestate (NC-1, ST-1): `mangle_type` is STATE-BLIND — phantom state
            // markers are dropped from the mono/instance key so `File<Open>`,
            // `File<Closed>`, and the stripped `File` all key to the SAME nominal
            // (one instance, byte-identical AIR). A nominal whose args are ALL state
            // markers degenerates to the bare name.
            // R2 (HK3): the surviving args join with `$` (outside the identifier
            // grammar) — an injective mangle so distinct instantiations can't fuse.
            let mangled_args: Vec<String> = args
                .iter()
                .filter(|a| !matches!(a, Type::StateMarker(_)))
                .map(mangle_type)
                .collect();
            if mangled_args.is_empty() {
                name.clone()
            } else {
                format!("{}__{}", name, mangled_args.join("$"))
            }
        }
        // ET-2: the `$tuple` prefix carries a `$` (outside the identifier
        // grammar), so a tuple key can NEVER collide with a user record name;
        // the arity prefix + recursive element mangle keep it injective.
        Type::Tuple(elems) => {
            let mangled: Vec<String> = elems.iter().map(mangle_type).collect();
            format!("$tuple{}__{}", elems.len(), mangled.join("$"))
        }
        Type::Generic(name) => {
            panic!("ICE: unresolved generic `{name}` reached mangle_type")
        }
        // HKT erasure boundary: a `TypeCtor` is the binding TARGET of an HKT var
        // and arrives here only as the (already-resolved) head of a monomorphized
        // application, so it mangles to the bare constructor name. A `HktVar` /
        // `HktApp` reaching mangle_type means an HKT var escaped monomorphization
        // — ICE, never a silently-wrong mangled key. (EX-3/EX-4/EX-5.)
        Type::TypeCtor(name) => name.clone(),
        // Typestate (ST-1): `mangle_type` is STATE-BLIND — state args are removed
        // by `strip_state_args` BEFORE the mono/instance key is computed, so a raw
        // StateMarker here means the strip was skipped → ICE, never a silently-wrong
        // `File__Open` key that would split one nominal into two instances.
        Type::StateMarker(name) => {
            panic!("ICE: state marker `{name}` reached mangle_type (strip_state_args skipped)")
        }
        // Effect Handlers (C-NEVER): the abortive bottom type is type-level only.
        // Primary defense = the T279 value-position rejections (the F003 site
        // checks + the whole-program residual gate, type_check/residual.rs), so
        // any residual here is a compiler-invariant violation, not a user error.
        Type::Never => {
            panic!("ICE: Type::Never reached mangle_type (must be erased / gated before AIR)")
        }
        Type::HktVar { name, .. } => {
            panic!("ICE: unresolved higher-kinded var `{name}` reached mangle_type")
        }
        Type::HktApp { ctor, .. } => {
            panic!("ICE: unresolved higher-kinded application `{ctor}<…>` reached mangle_type")
        }
        // PIL: Type::IntLit reaching mangle_type means a generic-fn
        // instantiation or method dispatch was triggered during
        // type-check (before the post-pass walker ran) and the type-arg
        // is still polymorphic. Default to "i64" — equivalent to the
        // walker's eventual default. Mangled names stay deterministic
        // because every IntLit (regardless of value) maps to "i64".
        Type::IntLit(_) => "i64".into(),
        Type::Fn(_, _, _, _) => "fn".into(),
        Type::Ptr(inner) => format!("ptr_{}", mangle_type(inner)),
        Type::MutPtr(inner) => format!("mutptr_{}", mangle_type(inner)),
        // Regions (DEF-2b): a region handle mangles to a stable name; it lowers to i64.
        Type::Region => "Region".into(),
        Type::Error => "error".into(),
    }
}

pub fn lower(program: &TypedProgram) -> AirProgram {
    let typed_functions: Vec<(Ring, &TypedFunction)> = program
        .modules
        .iter()
        .flat_map(|module| module.functions.iter().map(move |f| (module.ring, f)))
        .collect();
    // Builtin fallback resolves suffixes with `keys().find()`, so key order is
    // part of deterministic lowering even though exact-name lookups dominate.
    let function_ids = typed_functions
        .iter()
        .enumerate()
        .map(|(index, (_, function))| (function.name.clone(), FuncId(index as u32)))
        .collect::<BTreeMap<_, _>>();
    let field_registry = build_field_registry(program);
    let enum_registry = build_enum_registry(program);
    let functions = typed_functions
        .into_iter()
        .map(|(ring, function)| {
            lower_function(
                function,
                ring,
                &function_ids,
                &field_registry,
                &enum_registry,
            )
        })
        .collect();

    AirProgram { functions }
}

/// The monomorph-name suffix marking a state-backed `Vec<scalar>` instance: a `push`
/// whose receiver roots at a `mut Vec<scalar>` actor-state field. The impl-method mono site
/// (`type_check::expressions::methods`) appends it to the callee, producing a SEPARATE instance
/// whose grow allocation lowers to `alloc_persistent` instead of `alloc`. `$` and
/// `__` are reserved from user paths (T271), so the suffix cannot collide with a real mangled name.
/// Dead across any state-free module (no `mut Vec<scalar>` state field ⇒ no such instance).
pub(crate) const STATE_VEC_MONO_SUFFIX: &str = "$state";

fn lower_function(
    function: &TypedFunction,
    ring: Ring,
    function_ids: &BTreeMap<String, FuncId>,
    field_registry: &FieldRegistry,
    enum_registry: &EnumRegistry,
) -> AirFunction {
    // M3 ABI: an actor init/handler receives a per-actor STATE POINTER as its
    // leading parameter (`VarId(0)`); the user payload/init params shift to
    // `VarId(1..)`. State fields are read/written on-demand off that pointer
    // (see the `StateField` arms) — NOT via the closure capture-prologue, which
    // assumes a `__env` layout the actor doesn't have. Closures/module functions
    // are unchanged (no state pointer, payload at `VarId(0..)`).
    let is_actor = matches!(
        function.kind,
        TypedFunctionKind::ActorInit { .. } | TypedFunctionKind::ActorHandler { .. }
    );
    let param_base: u32 = if is_actor { 1 } else { 0 };

    let mut params = Vec::<(VarId, AirType)>::new();
    let mut env = LookupMap::<String, VarId>::new();
    let mut value_kinds = BTreeMap::<VarId, AirValueKind>::new();
    let mut debug_names = BTreeMap::<VarId, String>::new();
    let mut debug_spans = BTreeMap::<VarId, Span>::new();
    // `tool_main` is the source language's host bridge.  The compatibility taint
    // checker has always allowed its packed pointer/length result to carry an
    // `@Internal` FFI value back to the embedding host.  Preserve that effective
    // ABI contract in AIR instead of projecting the written default `@Public`
    // annotation and asking the formal verifier to contradict the source policy.
    // This is still a declared semantic input: it does not trust a computed value
    // label or make the output payload publicly observable.
    let mut security = AirSecurityMetadata {
        externally_callable: function.externally_callable,
        return_contract: if function.ret_flow {
            AirLabelContract::Flow
        } else {
            AirLabelContract::Concrete(function.effective_return_taint())
        },
        ..AirSecurityMetadata::default()
    };
    if is_actor {
        // The state pointer: an i32 heap address, non-linear (a plain pointer).
        params.push((VarId(0), AirType::Ptr));
        value_kinds.insert(VarId(0), AirValueKind::Copy);
        debug_names.insert(VarId(0), "__state".to_owned());
        debug_spans.insert(VarId(0), function.span);
        security
            .value_contracts
            .insert(VarId(0), AirLabelContract::Concrete(TaintLabel::Public));
    }
    for (index, param) in function.params.iter().enumerate() {
        let var = VarId(param_base + index as u32);
        params.push((var, lower_type(&param.ty)));
        env.insert(param.name.clone(), var);
        value_kinds.insert(var, classify_value_kind(&param.ty));
        debug_names.insert(var, param.name.clone());
        // TypedParam carries no span of its own; anchor a cap-typed
        // param at the function declaration so a violation on it is
        // still locatable (the function is where the param is declared).
        debug_spans.insert(var, function.span);
        security.value_contracts.insert(
            var,
            if param.flow {
                AirLabelContract::Flow
            } else {
                AirLabelContract::Concrete(param.taint)
            },
        );
    }

    let mut lowerer = FunctionLowerer::new(
        params.len(),
        function_ids,
        field_registry,
        enum_registry,
        value_kinds,
        debug_names,
        debug_spans,
        security,
    );
    // AGG2b-2: a state-backed `Vec<scalar>` mono instance (name suffix `$state`) lowers its
    // grow-alloc to the persistent channel. Detected by name so no extra plumbing threads through
    // the mono pass; false for every ordinary function ⇒ byte-identical alloc lowering elsewhere.
    lowerer.state_backed_alloc = function.name.ends_with(STATE_VEC_MONO_SUFFIX);
    lowerer.in_actor_handler = matches!(function.kind, TypedFunctionKind::ActorHandler { .. });
    if is_actor {
        // State fields are placed 0-based off the state pointer (`VarId(0)`) via
        // `state_layout_offsets` (the single authority, no closure table-index
        // prefix). Record placement + value kind for every actor function.
        let layout = state_layout_offsets(&function.captures);
        for ((_, offset, _), capture) in layout.fields.iter().zip(&function.captures) {
            lowerer
                .security
                .state_contracts
                .insert(*offset, capture.taint);
        }
        lowerer.state_layout = layout
            .fields
            .iter()
            .zip(&function.captures)
            .map(|((name, offset, ty), capture)| {
                // M4: a cap-typed state field READS as a borrow-only `StateCap`
                // (ownership rejects consuming it outside the construction phase,
                // C010). Data fields keep their ordinary kind. `is_construction_phase`
                // in ownership.rs — not the marker — decides where consuming is legal,
                // so the SAME marker is stamped for init and handlers alike.
                let kind = match classify_value_kind(&capture.ty) {
                    AirValueKind::Cap(name) => AirValueKind::StateCap(name),
                    other => other,
                };
                (name.clone(), (*offset, *ty, kind))
            })
            .collect();

        // The `mut`-declared fields are excluded from the
        // load-once prologue below and read fresh per access, so a handler read-after-
        // write reflects the new value. Empty for non-`mut` actors → byte-identical.
        lowerer.mut_state_fields = function
            .captures
            .iter()
            .filter(|c| c.mutability == crate::ast::Mutability::Mut)
            .map(|c| c.name.clone())
            .collect();

        let is_init = matches!(function.kind, TypedFunctionKind::ActorInit { .. });
        if !is_init {
            // HANDLER: load each state field ONCE off the state pointer into an
            // env-bound local (the fixed analogue of the old closure prologue —
            // correct base + 0-based state offsets). Reads/consumes resolve via
            // `env` to this single VarId, so O001 double-spend still fires and the
            // value is the real state. Mutable fields are excluded and loaded fresh below.
            lowerer.state_in_env = true;
            for ((name, offset, ty), capture) in layout.fields.iter().zip(&function.captures) {
                // A `mut` field is not cached in the prologue; it is read fresh
                // per access (below), so a read-after-write is never stale.
                if lowerer.mut_state_fields.contains(name) {
                    continue;
                }
                let kind = lowerer
                    .state_layout
                    .get(name)
                    .map(|(_, _, k)| k.clone())
                    .unwrap_or(AirValueKind::Copy);
                let var = lowerer.fresh_local(*ty, kind, name.clone());
                lowerer.debug_spans.insert(var, function.span);
                lowerer
                    .security
                    .value_contracts
                    .insert(var, AirLabelContract::Concrete(capture.taint));
                lowerer.entry_prologue.push(AirStmt::StateRead {
                    dst: var,
                    state_ptr: VarId(0),
                    offset: *offset,
                    ty: *ty,
                    label: capture.taint,
                });
                env.insert(name.clone(), var);
            }
        }
        // `init` keeps `state_in_env = false`: a `StateField` read is a fresh
        // `LoadField` (reads memory, reflecting prior stores) and a write is a
        // `StoreField` — see the `StateField` arms.
    } else {
        // A closure's captures live in its heap `__env` struct (param 0), packed
        // after the 4-byte table index in declaration order — the exact layout
        // `lower_closure_construct` writes. Bind each capture to a body local AND
        // emit the `LoadField` that reads it out of `__env` as the entry-block
        // prologue; otherwise the local is never initialized and reads as 0.
        let env_ptr = VarId(0);
        let mut capture_offset = CLOSURE_TABLE_IDX_OFFSET + AirType::I32.width();
        for capture in &function.captures {
            let cap_ty = lower_type(&capture.ty);
            let var = lowerer.fresh_local(
                cap_ty,
                classify_value_kind(&capture.ty),
                capture.name.clone(),
            );
            // Captures are loaded from `__env` via a synthetic LoadField (no
            // `lower_expr_into`), so anchor a cap-typed capture at the
            // enclosing function's span — the best location available.
            lowerer.debug_spans.insert(var, function.span);
            lowerer
                .security
                .value_contracts
                .insert(var, AirLabelContract::Concrete(capture.taint));
            lowerer.entry_prologue.push(AirStmt::LoadField {
                dst: var,
                base_ptr: env_ptr,
                offset: capture_offset,
                ty: cap_ty,
            });
            capture_offset += cap_ty.width();
            env.insert(capture.name.clone(), var);
        }
    }
    // Logical operators remain visible to all policy passes and are normalized
    // only at the AIR boundary. The private rewrite uses existing typed
    // Let/If/Assign nodes, which makes short-circuit control flow explicit to
    // capability and ownership verification without expanding the public AST.
    let mut normalized_body = function.body.clone();
    let mut logical_temp = 0u32;
    normalize_logical_block(&mut normalized_body, &mut logical_temp);
    let lowerer = lowerer.lower(&normalized_body.statements, env);

    AirFunction {
        name: function.name.clone(),
        export_name: function.export_name.clone(),
        ring,
        kind: lower_function_kind(&function.kind),
        params,
        ret: lower_type(&function.ret),
        locals: lowerer.locals,
        value_kinds: lowerer.value_kinds,
        debug_names: lowerer.debug_names,
        blocks: lowerer.blocks,
        entry_block: BlockId(0),
        def_span: function.span,
        debug_spans: lowerer.debug_spans,
        block_static_multiplicity: lowerer.block_multiplicity,
        security: lowerer.security,
    }
}

fn synthesized_bool(value: bool, span: Span) -> TypedExpr {
    TypedExpr {
        ty: Type::Bool,
        kind: TypedExprKind::Literal(Literal::Bool(value)),
        span,
        refinement: None,
    }
}

fn synthesized_local(name: &str, span: Span) -> TypedExpr {
    TypedExpr {
        ty: Type::Bool,
        kind: TypedExprKind::Local(name.to_owned()),
        span,
        refinement: None,
    }
}

fn normalize_logical_block(block: &mut crate::typed_ast::TypedBlock, next_temp: &mut u32) {
    let statements = std::mem::take(&mut block.statements);
    block.statements = normalize_logical_statements(statements, next_temp);
}

fn normalize_logical_statements(statements: Vec<TypedStmt>, next_temp: &mut u32) -> Vec<TypedStmt> {
    let mut result = Vec::new();
    for mut stmt in statements {
        let mut prelude = Vec::new();
        match &mut stmt {
            TypedStmt::Let(s) => normalize_logical_expr(&mut s.value, &mut prelude, next_temp),
            TypedStmt::Assign(s) => {
                normalize_logical_expr(&mut s.place, &mut prelude, next_temp);
                normalize_logical_expr(&mut s.value, &mut prelude, next_temp);
            }
            TypedStmt::Expr(s) => normalize_logical_expr(&mut s.expr, &mut prelude, next_temp),
            TypedStmt::Return(s) => {
                if let Some(value) = &mut s.value {
                    normalize_logical_expr(value, &mut prelude, next_temp);
                }
            }
            TypedStmt::If(s) => {
                normalize_logical_expr(&mut s.condition, &mut prelude, next_temp);
                normalize_logical_block(&mut s.then_branch, next_temp);
                normalize_logical_block(&mut s.else_branch, next_temp);
            }
            TypedStmt::Match(s) => {
                normalize_logical_expr(&mut s.scrutinee, &mut prelude, next_temp);
                for arm in &mut s.arms {
                    // Guards are lowered by `lower_bool_branch` so their
                    // short-circuit path stays inside the pattern-success path.
                    normalize_logical_block(&mut arm.body, next_temp);
                }
            }
            TypedStmt::While(s) => {
                let mut condition_prelude = Vec::new();
                normalize_logical_expr(&mut s.condition, &mut condition_prelude, next_temp);
                let mut original_body = s.body.clone();
                normalize_logical_block(&mut original_body, next_temp);
                if !condition_prelude.is_empty() {
                    let span = s.span;
                    let gate = TypedStmt::If(TypedIfStmt {
                        condition: s.condition.clone(),
                        then_branch: original_body,
                        else_branch: crate::typed_ast::TypedBlock {
                            statements: vec![TypedStmt::Break(span)],
                            span,
                            guaranteed_return: false,
                        },
                        span,
                    });
                    condition_prelude.push(gate);
                    s.condition = synthesized_bool(true, span);
                    s.body = crate::typed_ast::TypedBlock {
                        statements: condition_prelude,
                        span,
                        guaranteed_return: false,
                    };
                } else {
                    s.body = original_body;
                }
            }
            TypedStmt::ForIn(s) => {
                normalize_logical_expr(&mut s.iterable, &mut prelude, next_temp);
                s.body = normalize_logical_statements(std::mem::take(&mut s.body), next_temp);
            }
            // Range-for (added on main after this normalizer was written): both
            // bounds are ordinary expressions and the body is a statement list,
            // so it normalizes exactly like `ForIn`. Omitting the arm would have
            // been a silent non-normalization of `&&`/`||` inside a range loop.
            TypedStmt::ForRange(s) => {
                normalize_logical_expr(&mut s.start, &mut prelude, next_temp);
                normalize_logical_expr(&mut s.end, &mut prelude, next_temp);
                s.body = normalize_logical_statements(std::mem::take(&mut s.body), next_temp);
            }
            TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
        }
        result.extend(prelude);
        result.push(stmt);
    }
    result
}

fn normalize_exprs(exprs: &mut [TypedExpr], prelude: &mut Vec<TypedStmt>, next_temp: &mut u32) {
    for expr in exprs {
        normalize_logical_expr(expr, prelude, next_temp);
    }
}

fn normalize_logical_expr(expr: &mut TypedExpr, prelude: &mut Vec<TypedStmt>, next_temp: &mut u32) {
    let logical = match &expr.kind {
        TypedExprKind::Binary(binary)
            if matches!(binary.op, BinaryOp::LogicalAnd | BinaryOp::LogicalOr) =>
        {
            Some((
                binary.op,
                (*binary.lhs).clone(),
                (*binary.rhs).clone(),
                expr.span,
            ))
        }
        _ => None,
    };
    if let Some((op, mut lhs, mut rhs, span)) = logical {
        normalize_logical_expr(&mut lhs, prelude, next_temp);
        let mut rhs_prelude = Vec::new();
        normalize_logical_expr(&mut rhs, &mut rhs_prelude, next_temp);
        let name = format!("__sigil$logic${}", *next_temp);
        *next_temp += 1;
        let initial = matches!(op, BinaryOp::LogicalOr);
        prelude.push(TypedStmt::Let(TypedLetStmt {
            name: name.clone(),
            mutable: true,
            ty: Type::Bool,
            // Synthesized temp — no source annotation to carry.
            taint: None,
            value: synthesized_bool(initial, span),
            span,
        }));
        let assign = TypedStmt::Assign(crate::typed_ast::TypedAssignStmt {
            place: synthesized_local(&name, span),
            op: None,
            value: rhs,
            span,
        });
        rhs_prelude.push(assign);
        let nonempty = crate::typed_ast::TypedBlock {
            statements: rhs_prelude,
            span,
            guaranteed_return: false,
        };
        let empty = crate::typed_ast::TypedBlock {
            statements: Vec::new(),
            span,
            guaranteed_return: false,
        };
        let (then_branch, else_branch) = if matches!(op, BinaryOp::LogicalAnd) {
            (nonempty, empty)
        } else {
            (empty, nonempty)
        };
        prelude.push(TypedStmt::If(TypedIfStmt {
            condition: lhs,
            then_branch,
            else_branch,
            span,
        }));
        *expr = synthesized_local(&name, span);
        return;
    }

    match &mut expr.kind {
        TypedExprKind::Literal(_)
        | TypedExprKind::Local(_)
        | TypedExprKind::CapRestrict(_)
        | TypedExprKind::ClosureConstruct(_) => {}
        TypedExprKind::Call(e) => normalize_exprs(&mut e.args, prelude, next_temp),
        TypedExprKind::Intrinsic(e) => normalize_exprs(&mut e.args, prelude, next_temp),
        TypedExprKind::ResultCtor(e) => normalize_logical_expr(&mut e.value, prelude, next_temp),
        TypedExprKind::EnumConstruct(e) => normalize_exprs(&mut e.fields, prelude, next_temp),
        TypedExprKind::Try(e) => normalize_logical_expr(&mut e.value, prelude, next_temp),
        TypedExprKind::Send(e) => normalize_exprs(&mut e.args, prelude, next_temp),
        TypedExprKind::Ask(e) => {
            normalize_exprs(&mut e.args, prelude, next_temp);
            normalize_logical_expr(&mut e.timeout, prelude, next_temp);
        }
        TypedExprKind::Spawn(e) => normalize_exprs(&mut e.args, prelude, next_temp),
        TypedExprKind::Binary(e) => {
            normalize_logical_expr(&mut e.lhs, prelude, next_temp);
            normalize_logical_expr(&mut e.rhs, prelude, next_temp);
        }
        TypedExprKind::RecordConstruct(e) => {
            for (_, value) in &mut e.fields {
                normalize_logical_expr(value, prelude, next_temp);
            }
        }
        TypedExprKind::FieldAccess(e) => normalize_logical_expr(&mut e.object, prelude, next_temp),
        TypedExprKind::CapSplit(e) => normalize_logical_expr(&mut e.amount, prelude, next_temp),
        TypedExprKind::CapDraw(e) => normalize_logical_expr(&mut e.amount, prelude, next_temp),
        TypedExprKind::ArrayLit(e) => normalize_exprs(&mut e.elements, prelude, next_temp),
        TypedExprKind::Index(e) => {
            normalize_logical_expr(&mut e.array, prelude, next_temp);
            normalize_logical_expr(&mut e.index, prelude, next_temp);
        }
        TypedExprKind::Slice(e) => {
            normalize_logical_expr(&mut e.array, prelude, next_temp);
            if let Some(start) = &mut e.start {
                normalize_logical_expr(start, prelude, next_temp);
            }
            if let Some(end) = &mut e.end {
                normalize_logical_expr(end, prelude, next_temp);
            }
        }
        TypedExprKind::Borrow(e) => normalize_logical_expr(&mut e.inner, prelude, next_temp),
        TypedExprKind::Grant(e) => {
            normalize_logical_expr(&mut e.cap, prelude, next_temp);
            normalize_logical_expr(&mut e.body, prelude, next_temp);
        }
        TypedExprKind::Handle(e) => normalize_logical_block(&mut e.body, next_temp),
        TypedExprKind::Declassify(e) => {
            normalize_logical_expr(&mut e.value, prelude, next_temp);
            normalize_logical_expr(&mut e.cap, prelude, next_temp);
        }
        TypedExprKind::DeclassifyCt(e) => {
            normalize_logical_expr(&mut e.value, prelude, next_temp);
            normalize_logical_expr(&mut e.cap, prelude, next_temp);
        }
        TypedExprKind::ExternCall(e) => normalize_exprs(&mut e.args, prelude, next_temp),
        TypedExprKind::Region(e) => {
            normalize_logical_expr(&mut e.limit, prelude, next_temp);
            normalize_logical_block(&mut e.body, next_temp);
        }
        TypedExprKind::IndirectCall(e) => normalize_exprs(&mut e.args, prelude, next_temp),
        TypedExprKind::FString(e) => {
            for part in &mut e.parts {
                if let crate::typed_ast::TypedFStringPart::Hole(hole) = part {
                    normalize_logical_expr(hole, prelude, next_temp);
                }
            }
        }
        // Variants added on main AFTER this `&&`/`||` normalizer was written.
        // The match is TOTAL on purpose (no `_` arm — the walker-fence
        // discipline), so each must state its recursion explicitly: a
        // sub-expression that is not walked would silently keep a `LogicalAnd`
        // node that AIR lowering cannot represent.
        TypedExprKind::StateField(_) => {}
        TypedExprKind::Mint(e) => normalize_logical_expr(&mut e.target, prelude, next_temp),
        TypedExprKind::Perform(e) => normalize_exprs(&mut e.args, prelude, next_temp),
        TypedExprKind::ClauseHandle(e) => {
            normalize_logical_expr(&mut e.scrutinee, prelude, next_temp);
            for clause in &mut e.clauses {
                normalize_logical_block(&mut clause.body, next_temp);
            }
        }
        TypedExprKind::Resume(e) => normalize_logical_expr(&mut e.value, prelude, next_temp),
    }
}

/// break/continue: the AIR targets of the innermost enclosing loop. `continue` jumps to
/// `continue_target` (the loop header — `Br`-able), after running `continue_incr` (the
/// for-in/for-range index increment, so it advances to the next element rather than
/// re-reading the current one); `break` jumps to `break_target` (the loop exit). The
/// increment carries its WIDTH: for-in counts in `U32` (byte-identical to the
/// pre-range-for AIR), for-range counts in `I64` — the `__one` literal in the shared
/// `Continue` arm must match the counter's type or the add is width-mismatched.
#[derive(Clone, Copy)]
struct LoopFrame {
    break_target: BlockId,
    continue_target: BlockId,
    continue_incr: Option<(VarId, AirType)>,
    /// Static trip bound of this loop, when BOTH range bounds are integer
    /// literals (`for v in 0..64`): `max(0, end - start)`. `None` for while,
    /// for-in, and any range with a non-literal bound (a runtime start can
    /// legally trip MORE than a literal end — e.g. a negative `s` in `s..64`).
    /// Blocks created while an unbounded frame is on the stack get a `None`
    /// multiplicity, which the fuel pass treats as "not a workload ceiling".
    static_k: Option<u64>,
}

/// Multiplicities and worst-case costs saturate here (2^40) instead of at
/// u64::MAX: the selfhost shadow mirrors this arithmetic in i64, so the clamp
/// must be representable — and identical — on both sides (SH-FUEL F2).
pub const FUEL_MULT_CLAMP: u64 = 1 << 40;

/// `a × b` under the shared clamp.
pub fn fuel_mul_clamped(a: u64, b: u64) -> u64 {
    a.saturating_mul(b).min(FUEL_MULT_CLAMP)
}

/// Private emission buffer. Source provenance travels with each instruction,
/// including instructions with no destination (send, unit call, state store).
/// Nested expression lowering restores the caller's span before emitting its
/// own operation, so an argument's span cannot become the enclosing call site.
#[derive(Default)]
struct StatementBuffer {
    entries: Vec<(AirStmt, Option<Span>)>,
    active_span: Option<Span>,
}

impl StatementBuffer {
    fn new() -> Self {
        Self::default()
    }

    fn at(span: Span) -> Self {
        Self {
            active_span: Some(span),
            ..Self::default()
        }
    }

    fn from_at(statements: Vec<AirStmt>, span: Span) -> Self {
        Self {
            entries: statements
                .into_iter()
                .map(|statement| (statement, Some(span)))
                .collect(),
            active_span: Some(span),
        }
    }

    fn push(&mut self, statement: AirStmt) {
        self.entries.push((statement, self.active_span));
    }

    fn with_span<R>(&mut self, span: Span, lower: impl FnOnce(&mut Self) -> R) -> R {
        let previous = self.active_span.replace(span);
        let result = lower(self);
        self.active_span = previous;
        result
    }
}

impl From<Vec<AirStmt>> for StatementBuffer {
    fn from(statements: Vec<AirStmt>) -> Self {
        Self {
            entries: statements
                .into_iter()
                .map(|statement| (statement, None))
                .collect(),
            active_span: None,
        }
    }
}

struct LoweringBlock {
    id: BlockId,
    stmts: StatementBuffer,
    terminator: AirTerminator,
}

fn statement_source_span(statement: &TypedStmt) -> Span {
    match statement {
        TypedStmt::Let(statement) => statement.span,
        TypedStmt::Assign(statement) => statement.span,
        TypedStmt::Expr(statement) => statement.span,
        TypedStmt::If(statement) => statement.span,
        TypedStmt::Match(statement) => statement.span,
        TypedStmt::While(statement) => statement.span,
        // For-in retains the iterable span, not a whole-statement source span.
        TypedStmt::ForIn(statement) => statement.iterable.span,
        TypedStmt::ForRange(statement) => statement.span,
        TypedStmt::Return(statement) => statement.span,
        TypedStmt::Break(span) | TypedStmt::Continue(span) => *span,
    }
}

struct FunctionLowerer<'a> {
    function_ids: &'a BTreeMap<String, FuncId>,
    field_registry: &'a FieldRegistry,
    enum_registry: &'a EnumRegistry,
    locals: Vec<(VarId, AirType)>,
    value_kinds: BTreeMap<VarId, AirValueKind>,
    debug_names: BTreeMap<VarId, String>,
    debug_spans: BTreeMap<VarId, Span>,
    security: AirSecurityMetadata,
    blocks: Vec<LoweringBlock>,
    next_var: u32,
    next_block: u32,
    loop_stack: Vec<LoopFrame>,
    /// Per-block static execution multiplicity, indexed by `BlockId`: the
    /// product of the enclosing loops' `static_k` bounds (`Some(1)` at function
    /// top level), or `None` once any enclosing loop is unbounded. Written at
    /// `fresh_block` from the live stack; the loop arms then override their own
    /// cond/body/incr blocks, which are created BEFORE the frame is pushed
    /// (cond runs K+1 times, body/incr K). Consumed by `fuel::insert` to weight
    /// decrement sites into the worst-case-cost budget.
    block_multiplicity: Vec<Option<u64>>,
    /// Statements prepended to the entry block (BlockId(0)). Used to load a
    /// closure's captures out of its `__env` pointer (param 0) into their
    /// body locals before the body runs — without these loads every captured
    /// variable would read as an uninitialized 0.
    entry_prologue: Vec<AirStmt>,
    /// Actor-state (M3): state field name → (byte offset, AIR type, value kind)
    /// in the per-actor state struct. Non-empty ONLY for actor init/handler
    /// functions, whose AIR has a state pointer as `VarId(0)`. A `StateField`
    /// read lowers to a `LoadField` off that pointer at the field's offset (the
    /// loaded local carries the field's value kind — `Cap(name)` for a cap, so
    /// the Z3 cap layer still recognises it); an `init` write to a `StoreField`.
    /// Empty for closures/module functions (they have no state).
    state_layout: LookupMap<String, (u32, AirType, AirValueKind)>,
    /// True in an actor HANDLER body: each state field is loaded ONCE off the
    /// state pointer into an `env`-bound local by the entry prologue, so repeated
    /// reads/consumes of a state cap reuse the same `VarId` (O001 double-spend
    /// detection works) and read the real state value. False in `init` (state is
    /// being written) and in non-actor bodies, where a `StateField` read is a
    /// fresh `LoadField` and `resolve_name` falls back to `state_layout`.
    state_in_env: bool,
    /// The `mut`-declared state fields from the actor captures.
    /// A `mut` field is EXCLUDED from the load-once prologue and read fresh off the
    /// state pointer per access, so a handler read-after-write sees the new value
    /// (memory reflects prior conditional writes) rather than the stale cached local.
    /// Empty for non-`mut` actors and non-actor bodies — every existing actor keeps
    /// the load-once model and stays byte-identical.
    mut_state_fields: std::collections::HashSet<String>,
    /// True iff this function is a state-backed `Vec<scalar>` mono instance (its name ends
    /// with [`STATE_VEC_MONO_SUFFIX`]). When true, an `alloc` intrinsic in the body lowers to an
    /// `IntrinsicAlloc { persistent: true }` (the `alloc_persistent` channel); false everywhere
    /// else, so every other function's allocs are byte-identical.
    state_backed_alloc: bool,
    /// PPS-1: true while lowering an actor HANDLER (not `init`). A wholesale write of an
    /// aggregate state field in a handler must PROMOTE the value into the persistent heap
    /// first — the freshly-built object lives in the per-dispatch scratch the reset reclaims.
    /// `init` allocates below the persistent floor already, so its lowering is untouched
    /// (and stays byte-identical).
    in_actor_handler: bool,
    /// Set only while lowering a generated abortive evidence call. The enclosing Return records
    /// the block in `AirSecurityMetadata`; any non-return occurrence is an invariant violation.
    abortive_transfer_seen: bool,
}

impl<'a> FunctionLowerer<'a> {
    // The security metadata is a separate, declarative lowering input. Keeping it
    // explicit here prevents it from being reconstructed from mutable lowering
    // state (which would turn verifier inputs into Rust-derived verdicts).
    #[allow(clippy::too_many_arguments)]
    fn new(
        param_count: usize,
        function_ids: &'a BTreeMap<String, FuncId>,
        field_registry: &'a FieldRegistry,
        enum_registry: &'a EnumRegistry,
        value_kinds: BTreeMap<VarId, AirValueKind>,
        debug_names: BTreeMap<VarId, String>,
        debug_spans: BTreeMap<VarId, Span>,
        security: AirSecurityMetadata,
    ) -> Self {
        Self {
            function_ids,
            field_registry,
            enum_registry,
            locals: Vec::new(),
            value_kinds,
            debug_names,
            debug_spans,
            security,
            blocks: Vec::new(),
            next_var: param_count as u32,
            next_block: 1,
            loop_stack: Vec::new(),
            // Seed the entry block (BlockId(0) never passes fresh_block).
            block_multiplicity: vec![Some(1)],
            entry_prologue: Vec::new(),
            state_layout: LookupMap::new(),
            state_in_env: false,
            mut_state_fields: std::collections::HashSet::new(),
            state_backed_alloc: false,
            in_actor_handler: false,
            abortive_transfer_seen: false,
        }
    }

    /// The state pointer for an actor init/handler body — always `VarId(0)`, the
    /// prepended leading parameter (M3 ABI). Only meaningful when `state_layout`
    /// is populated.
    const STATE_PTR: VarId = VarId(0);

    fn lower(
        mut self,
        statements: &[TypedStmt],
        env: LookupMap<String, VarId>,
    ) -> LoweredFunctionBody {
        self.lower_statements(statements, env, BlockId(0), None);
        let blocks = self
            .blocks
            .into_iter()
            .map(|block| {
                if let Some(span) = block.stmts.active_span {
                    self.security.terminator_spans.insert(block.id, span);
                }
                let stmts = block
                    .stmts
                    .entries
                    .into_iter()
                    .enumerate()
                    .map(|(index, (statement, span))| {
                        if let Some(span) = span {
                            let index =
                                u32::try_from(index).expect("ICE: AIR statement index exceeds u32");
                            self.security
                                .statement_spans
                                .insert((block.id, index), span);
                        }
                        statement
                    })
                    .collect();
                AirBlock {
                    id: block.id,
                    stmts,
                    terminator: block.terminator,
                }
            })
            .collect::<Vec<_>>();
        self.security.record_actor_operations(&blocks);
        LoweredFunctionBody {
            locals: self.locals,
            value_kinds: self.value_kinds,
            debug_names: self.debug_names,
            debug_spans: self.debug_spans,
            security: self.security,
            blocks,
            block_multiplicity: self.block_multiplicity,
        }
    }

    /// Product of the enclosing loops' static bounds (clamped), `None` once any
    /// enclosing loop is unbounded.
    fn ambient_multiplicity(&self) -> Option<u64> {
        self.loop_stack.iter().try_fold(1u64, |acc, frame| {
            Some(fuel_mul_clamped(acc, frame.static_k?))
        })
    }

    /// Override a block's recorded multiplicity — used by the loop arms for
    /// their own cond/body/incr blocks, which are created before the frame is
    /// pushed and therefore get the ENCLOSING multiplicity from `fresh_block`.
    fn set_block_multiplicity(&mut self, block: BlockId, mult: Option<u64>) {
        self.block_multiplicity[block.0 as usize] = mult;
    }

    fn lower_statements(
        &mut self,
        statements: &[TypedStmt],
        mut env: LookupMap<String, VarId>,
        mut block_id: BlockId,
        continuation: Option<BlockId>,
    ) {
        // The entry block (BlockId(0), reached only from `lower`) leads with the
        // closure-capture prologue; every other block starts empty. `take` makes
        // this a one-shot — recursive block lowering never re-emits it.
        //
        // DoS hardening: the four control-flow statements (If/Match/While/ForIn)
        // each split the block at a fresh continuation and used to TAIL-RECURSE on
        // `&statements[index + 1..]` to lower the remainder. That made stack depth
        // O(control-flow statements in this block) — a function with a few hundred
        // sibling `if`s overflowed the native stack. The remainder is now lowered by
        // re-entering this `while` loop with `block_id`/`stmts` advanced to the
        // continuation, so the remainder costs O(1) stack. The NESTED lowering of a
        // branch/loop/arm body still recurses, but that depth is bounded by the
        // (parser-limited) statement-nesting depth, not the sibling count. The
        // emitted block sequence and `fresh_block` allocation order are unchanged,
        // so AIR output is byte-identical to the recursive version.
        let mut stmts = if block_id == BlockId(0) {
            StatementBuffer::from(std::mem::take(&mut self.entry_prologue))
        } else {
            StatementBuffer::new()
        };
        let mut index = 0;

        while index < statements.len() {
            self.abortive_transfer_seen = false;
            stmts.active_span = Some(statement_source_span(&statements[index]));
            match &statements[index] {
                TypedStmt::Let(stmt) => {
                    let dst = self.fresh_local(
                        lower_type(&stmt.ty),
                        classify_value_kind(&stmt.ty),
                        stmt.name.clone(),
                    );
                    self.security.value_contracts.insert(
                        dst,
                        match stmt.taint {
                            Some(label) => AirLabelContract::Concrete(label),
                            // An unannotated mutable local has no declared security ceiling. Its
                            // current definition may rise and later be strongly updated on every
                            // live path. CSIR v8 reconstructs those definitions as security-only
                            // SSA values; marking the storage slot Public here would turn inferred
                            // behavior into a fabricated contract.
                            None => AirLabelContract::Inferred,
                        },
                    );
                    self.lower_expr_into(dst, &stmt.value, &env, &mut stmts);
                    env.insert(stmt.name.clone(), dst);
                }
                TypedStmt::Assign(stmt) => {
                    self.lower_assign(stmt, &env, &mut stmts);
                }
                TypedStmt::Expr(stmt) => {
                    self.lower_expr_stmt(&stmt.expr, &env, &mut stmts);
                    // Sound divergence (Tier A): a `Never`-typed statement
                    // (`trap()`) aborts, so control ends here. Terminate the block
                    // with `Unreachable` — wasm `unreachable` poisons the rest of
                    // the block, so a non-unit function whose value is never
                    // produced is still valid. The type checker already dropped any
                    // statements after it (check_block's break on guaranteed_return).
                    if matches!(stmt.expr.ty, Type::Never) {
                        self.blocks.push(LoweringBlock {
                            id: block_id,
                            stmts,
                            terminator: AirTerminator::Unreachable,
                        });
                        return;
                    }
                }
                TypedStmt::If(stmt) => {
                    let cond = self.lower_expr_to_var(&stmt.condition, &env, &mut stmts);
                    stmts.active_span = Some(stmt.condition.span);
                    let then_block = self.fresh_block();
                    let else_block = self.fresh_block();
                    let has_remainder = index + 1 < statements.len();
                    let next_block = if has_remainder {
                        Some(self.fresh_block())
                    } else {
                        continuation
                    };

                    self.security
                        .control_policy
                        .insert(block_id, AirPolicyClass::Branch);
                    self.blocks.push(LoweringBlock {
                        id: block_id,
                        stmts,
                        terminator: AirTerminator::Branch {
                            cond,
                            then_block,
                            else_block,
                            merge_block: next_block,
                        },
                    });

                    self.lower_statements(
                        &stmt.then_branch.statements,
                        env.clone(),
                        then_block,
                        next_block,
                    );
                    self.lower_statements(
                        &stmt.else_branch.statements,
                        env.clone(),
                        else_block,
                        next_block,
                    );

                    // Lower the block remainder iteratively rather than via a tail
                    // recursion (see the function-level note). With a remainder,
                    // `next_block` is the fresh merge block created above; continue
                    // the loop there. Without one, the branch already terminates into
                    // `continuation`, so there is nothing left to do.
                    if has_remainder {
                        block_id = next_block
                            .expect("has_remainder implies a fresh merge block was allocated");
                        stmts = StatementBuffer::new();
                        index += 1;
                        continue;
                    }
                    return;
                }
                TypedStmt::Match(stmt) => {
                    let scrutinee = self.lower_expr_to_var(&stmt.scrutinee, &env, &mut stmts);
                    stmts.active_span = Some(stmt.scrutinee.span);
                    let exit_block = self.fresh_block();
                    self.lower_match_arms(
                        &stmt.arms,
                        scrutinee,
                        env.clone(),
                        block_id,
                        stmts,
                        exit_block,
                    );
                    // Lower the remainder iteratively in the match's exit block
                    // (see the function-level note) instead of tail-recursing.
                    block_id = exit_block;
                    stmts = StatementBuffer::new();
                    index += 1;
                    continue;
                }
                TypedStmt::While(stmt) => {
                    let cond_block = self.fresh_block();
                    let body_block = self.fresh_block();
                    let exit_block = self.fresh_block();
                    // A while's trip count is data-dependent: its cond/body run
                    // an unknowable number of times (fresh_block recorded the
                    // ENCLOSING multiplicity — created pre-push). exit keeps
                    // the ambient level.
                    self.set_block_multiplicity(cond_block, None);
                    self.set_block_multiplicity(body_block, None);

                    self.blocks.push(LoweringBlock {
                        id: block_id,
                        stmts,
                        terminator: AirTerminator::Jump(cond_block),
                    });

                    let mut cond_stmts = StatementBuffer::at(stmt.condition.span);
                    let cond = self.lower_expr_to_var(&stmt.condition, &env, &mut cond_stmts);
                    self.security
                        .control_policy
                        .insert(cond_block, AirPolicyClass::Loop);
                    self.blocks.push(LoweringBlock {
                        id: cond_block,
                        stmts: cond_stmts,
                        terminator: AirTerminator::Loop {
                            cond,
                            body_block,
                            exit_block,
                        },
                    });

                    // break/continue: target this loop. continue → cond_block (the
                    // Br-able loop header); break → exit_block. No index to advance.
                    self.loop_stack.push(LoopFrame {
                        break_target: exit_block,
                        continue_target: cond_block,
                        continue_incr: None,
                        static_k: None,
                    });
                    self.lower_statements(
                        &stmt.body.statements,
                        env.clone(),
                        body_block,
                        Some(cond_block),
                    );
                    self.loop_stack.pop();
                    // Lower the remainder iteratively in the loop's exit block
                    // (see the function-level note) instead of tail-recursing.
                    block_id = exit_block;
                    stmts = StatementBuffer::new();
                    index += 1;
                    continue;
                }
                TypedStmt::ForIn(stmt) => {
                    // Desugar for-in to while loop: __idx = 0; while __idx < __len { var = arr[__idx]; body; __idx += 1; }
                    //
                    // PR AF / N27-AF: the Array vs Slice layout
                    // dispatch lives HERE. Array's layout is
                    // unchanged (length at offset 0, elements at
                    // offset 4+), so the Array path is BYTE-EQUAL to
                    // pre-PR-AF. Slice loads length from
                    // SLICE_LEN_OFFSET via the canonical
                    // `slice_len_var` helper (N14-AF) and uses the
                    // slice's `data_ptr` as the element-load base.
                    // Per the SLICE_DATA_PTR_OFFSET doc-comment, the
                    // fat-pointer's `data_ptr` is set so that
                    // LoadDynamic's built-in +4 header skip lands at
                    // the correct element.
                    let iterable_var = self.lower_expr_to_var(&stmt.iterable, &env, &mut stmts);
                    let elem_air_type = lower_type(&stmt.elem_type);
                    let elem_kind = classify_value_kind(&stmt.elem_type);
                    let elem_size = elem_air_type.width();

                    let idx = self.fresh_local(AirType::U32, AirValueKind::Copy, "__idx");
                    let len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__len");
                    let loop_var = self.fresh_local(elem_air_type, elem_kind, stmt.var.clone());

                    let is_slice = matches!(&stmt.iterable.ty, Type::Slice(_));
                    // `arr` is the base for LoadDynamic element loads.
                    // For Array: the iterable itself (header skip
                    // baked into LoadDynamic). For Slice: the slice's
                    // data_ptr (read via the canonical helper).
                    let arr = if is_slice {
                        self.slice_data_ptr_var(iterable_var, &mut stmts)
                    } else {
                        iterable_var
                    };

                    // Init: __idx = 0.
                    stmts.push(AirStmt::Assign {
                        dst: idx,
                        val: AirValue::IntLit(0),
                    });
                    // __len: Array reads offset 0; Slice reads
                    // SLICE_LEN_OFFSET via the canonical helper.
                    if is_slice {
                        let slice_len = self.slice_len_var(iterable_var, &mut stmts);
                        stmts.push(AirStmt::Assign {
                            dst: len,
                            val: AirValue::Var(slice_len),
                        });
                    } else {
                        stmts.push(AirStmt::LoadField {
                            dst: len,
                            base_ptr: arr,
                            offset: 0,
                            ty: AirType::U32,
                        });
                    }

                    let cond_block = self.fresh_block();
                    let body_block = self.fresh_block();
                    let exit_block = self.fresh_block();
                    // For-in reads its length at runtime (a LoadField even for
                    // `[T; N]`), so its trip count is unbounded for the fuel
                    // pass — cond/body poisoned like a while; exit stays
                    // ambient. (Bounding `[T; N]` iteration is a possible
                    // follow-on; the WCC slice covers literal for-range only.)
                    self.set_block_multiplicity(cond_block, None);
                    self.set_block_multiplicity(body_block, None);

                    self.blocks.push(LoweringBlock {
                        id: block_id,
                        stmts,
                        terminator: AirTerminator::Jump(cond_block),
                    });

                    // Cond block: __idx < __len
                    let cond = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__for_cond");
                    let cond_stmts = vec![AirStmt::Assign {
                        dst: cond,
                        val: AirValue::Binary {
                            lhs: idx,
                            op: BinaryOp::Lt,
                            rhs: len,
                        },
                    }];
                    self.security
                        .control_policy
                        .insert(cond_block, AirPolicyClass::Loop);
                    self.blocks.push(LoweringBlock {
                        id: cond_block,
                        stmts: StatementBuffer::from_at(
                            cond_stmts,
                            statement_source_span(&statements[index]),
                        ),
                        terminator: AirTerminator::Loop {
                            cond,
                            body_block,
                            exit_block,
                        },
                    });

                    // Body preamble block: load var, then continue to user body
                    let body_inner_block = self.fresh_block();
                    self.set_block_multiplicity(body_inner_block, None);
                    let body_preamble = vec![AirStmt::LoadDynamic {
                        dst: loop_var,
                        base_ptr: arr,
                        index: idx,
                        elem_size,
                        ty: elem_air_type,
                        offset: 4,
                    }];
                    self.blocks.push(LoweringBlock {
                        id: body_block,
                        stmts: StatementBuffer::from_at(
                            body_preamble,
                            statement_source_span(&statements[index]),
                        ),
                        terminator: AirTerminator::Jump(body_inner_block),
                    });

                    // Create increment block that jumps back to cond
                    let incr_block = self.fresh_block();
                    self.set_block_multiplicity(incr_block, None);
                    let one = self.fresh_local(AirType::U32, AirValueKind::Copy, "__one");
                    let incr_stmts = vec![
                        AirStmt::Assign {
                            dst: one,
                            val: AirValue::IntLit(1),
                        },
                        AirStmt::Assign {
                            dst: idx,
                            val: AirValue::Binary {
                                lhs: idx,
                                op: BinaryOp::Add,
                                rhs: one,
                            },
                        },
                    ];
                    self.blocks.push(LoweringBlock {
                        id: incr_block,
                        stmts: StatementBuffer::from_at(
                            incr_stmts,
                            statement_source_span(&statements[index]),
                        ),
                        terminator: AirTerminator::Jump(cond_block),
                    });

                    // Lower user body into body_inner_block, continuing to incr_block
                    let mut body_env = env.clone();
                    body_env.insert(stmt.var.clone(), loop_var);
                    // break/continue: continue → cond_block (the Br-able loop header)
                    // AFTER advancing `idx` (so it moves to the next element rather than
                    // re-reading the current one); break → exit_block.
                    self.loop_stack.push(LoopFrame {
                        break_target: exit_block,
                        continue_target: cond_block,
                        continue_incr: Some((idx, AirType::U32)),
                        static_k: None,
                    });
                    self.lower_statements(&stmt.body, body_env, body_inner_block, Some(incr_block));
                    self.loop_stack.pop();

                    // Lower the remainder iteratively in the loop's exit block
                    // (see the function-level note) instead of tail-recursing.
                    block_id = exit_block;
                    stmts = StatementBuffer::new();
                    index += 1;
                    continue;
                }
                TypedStmt::ForRange(stmt) => {
                    // `for v in a..b { body }` — the exclusive i64 range loop:
                    //   v = a; while v < __r_end { body; v += 1; }
                    // Mirrors the ForIn lowering above minus the element load: the
                    // user's `v` IS the counter local (I64 throughout — for-in's U32
                    // machinery is untouched). `start`/`end` are lowered exactly ONCE
                    // into this pre-header block (eval-once for side-effecting
                    // bounds); the cond block re-reads the hoisted `__r_end` local.
                    // Fuel: the `AirTerminator::Loop` back-edge is charged like any
                    // loop — zero fuel changes.
                    let start_var = self.lower_expr_to_var(&stmt.start, &env, &mut stmts);
                    let end_var = self.lower_expr_to_var(&stmt.end, &env, &mut stmts);

                    let loop_var =
                        self.fresh_local(AirType::I64, AirValueKind::Copy, stmt.var.clone());
                    let r_end = self.fresh_local(AirType::I64, AirValueKind::Copy, "__r_end");

                    // Init: v = start; __r_end = end (both hoisted, evaluated once).
                    stmts.push(AirStmt::Assign {
                        dst: loop_var,
                        val: AirValue::Var(start_var),
                    });
                    stmts.push(AirStmt::Assign {
                        dst: r_end,
                        val: AirValue::Var(end_var),
                    });

                    let cond_block = self.fresh_block();
                    let body_block = self.fresh_block();
                    let exit_block = self.fresh_block();
                    // WCC: a range with BOTH bounds integer literals has the
                    // static trip count `max(0, end - start)` — break/continue
                    // only shrink it. Any non-literal bound is unbounded: a
                    // runtime START can trip more than a literal end (negative
                    // `s` in `s..64`), so end-only resolution would be UNSOUND.
                    // The loop's own blocks were created pre-push, so their
                    // fresh_block multiplicity is the enclosing level E —
                    // override: cond runs E×(K+1) (one refuting evaluation),
                    // body E×K; exit stays E. Unbounded → cond/body poisoned.
                    let static_k = match (&stmt.start.kind, &stmt.end.kind) {
                        (
                            TypedExprKind::Literal(Literal::Int(s)),
                            TypedExprKind::Literal(Literal::Int(e)),
                        ) => Some(
                            u64::try_from((*e as i128 - *s as i128).max(0))
                                .map_or(FUEL_MULT_CLAMP, |k| k.min(FUEL_MULT_CLAMP)),
                        ),
                        _ => None,
                    };
                    let enclosing = self.ambient_multiplicity();
                    let (cond_mult, body_mult) = match (enclosing, static_k) {
                        (Some(e), Some(k)) => (
                            Some(fuel_mul_clamped(e, k.saturating_add(1))),
                            Some(fuel_mul_clamped(e, k)),
                        ),
                        _ => (None, None),
                    };
                    self.set_block_multiplicity(cond_block, cond_mult);
                    self.set_block_multiplicity(body_block, body_mult);

                    self.blocks.push(LoweringBlock {
                        id: block_id,
                        stmts,
                        terminator: AirTerminator::Jump(cond_block),
                    });

                    // Cond block: v < __r_end (signed i64 — empty when start >= end).
                    let cond = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__for_cond");
                    let cond_stmts = vec![AirStmt::Assign {
                        dst: cond,
                        val: AirValue::Binary {
                            lhs: loop_var,
                            op: BinaryOp::Lt,
                            rhs: r_end,
                        },
                    }];
                    self.security
                        .control_policy
                        .insert(cond_block, AirPolicyClass::Range);
                    self.blocks.push(LoweringBlock {
                        id: cond_block,
                        stmts: StatementBuffer::from_at(
                            cond_stmts,
                            statement_source_span(&statements[index]),
                        ),
                        terminator: AirTerminator::Loop {
                            cond,
                            body_block,
                            exit_block,
                        },
                    });

                    // Increment block: v += 1, back to the header. `v < end <= i64::MAX`
                    // pre-increment, so the add cannot wrap.
                    let incr_block = self.fresh_block();
                    self.set_block_multiplicity(incr_block, body_mult);
                    let one = self.fresh_local(AirType::I64, AirValueKind::Copy, "__one");
                    let incr_stmts = vec![
                        AirStmt::Assign {
                            dst: one,
                            val: AirValue::IntLit(1),
                        },
                        AirStmt::Assign {
                            dst: loop_var,
                            val: AirValue::Binary {
                                lhs: loop_var,
                                op: BinaryOp::Add,
                                rhs: one,
                            },
                        },
                    ];
                    self.blocks.push(LoweringBlock {
                        id: incr_block,
                        stmts: StatementBuffer::from_at(
                            incr_stmts,
                            statement_source_span(&statements[index]),
                        ),
                        terminator: AirTerminator::Jump(cond_block),
                    });

                    // Lower the user body directly at body_block (no preamble — there
                    // is no element to load), continuing to the increment block.
                    let mut body_env = env.clone();
                    body_env.insert(stmt.var.clone(), loop_var);
                    self.loop_stack.push(LoopFrame {
                        break_target: exit_block,
                        continue_target: cond_block,
                        continue_incr: Some((loop_var, AirType::I64)),
                        static_k,
                    });
                    self.lower_statements(&stmt.body, body_env, body_block, Some(incr_block));
                    self.loop_stack.pop();

                    // Continue iteratively in the exit block (the ForIn discipline).
                    block_id = exit_block;
                    stmts = StatementBuffer::new();
                    index += 1;
                    continue;
                }
                TypedStmt::Break(_) => {
                    // Jump to the innermost loop's exit. The type checker guarantees a
                    // frame exists (T260 otherwise); `Unreachable` is a defensive,
                    // always-valid fallback that never fires on a type-clean program.
                    let target = self.loop_stack.last().map(|f| f.break_target);
                    self.blocks.push(LoweringBlock {
                        id: block_id,
                        stmts,
                        terminator: target.map_or(AirTerminator::Unreachable, AirTerminator::Jump),
                    });
                    return;
                }
                TypedStmt::Continue(_) => {
                    // Advance the loop (for-in: `idx += 1`) then jump to the loop header.
                    let frame = self.loop_stack.last().copied();
                    if let Some((idx, width)) = frame.and_then(|f| f.continue_incr) {
                        // `__one` takes the COUNTER's width: U32 for for-in (the
                        // pre-range-for byte-identical shape), I64 for for-range.
                        let one = self.fresh_local(width, AirValueKind::Copy, "__one");
                        stmts.push(AirStmt::Assign {
                            dst: one,
                            val: AirValue::IntLit(1),
                        });
                        stmts.push(AirStmt::Assign {
                            dst: idx,
                            val: AirValue::Binary {
                                lhs: idx,
                                op: BinaryOp::Add,
                                rhs: one,
                            },
                        });
                    }
                    let target = frame.map(|f| f.continue_target);
                    self.blocks.push(LoweringBlock {
                        id: block_id,
                        stmts,
                        terminator: target.map_or(AirTerminator::Unreachable, AirTerminator::Jump),
                    });
                    return;
                }
                TypedStmt::Return(stmt) => {
                    let value = stmt
                        .value
                        .as_ref()
                        .map(|value| self.lower_expr_to_var(value, &env, &mut stmts));
                    if self.abortive_transfer_seen {
                        self.security.abortive_transfer_blocks.insert(block_id);
                    }
                    let terminator = AirTerminator::Return(value);
                    self.blocks.push(LoweringBlock {
                        id: block_id,
                        stmts,
                        terminator,
                    });
                    return;
                }
            }

            index += 1;
        }

        self.blocks.push(LoweringBlock {
            id: block_id,
            stmts,
            terminator: continuation.map_or(AirTerminator::Return(None), AirTerminator::Jump),
        });
    }

    /// M3: load a state field off the state pointer (`VarId(0)`) into a fresh
    /// local. The AIR width + offset come from `state_layout` (the single
    /// authority). The loaded value is `Copy` (non-linear) in M3; M4 tags a
    /// state CAP read as a borrow-only `StateCap` for the C010 enforcement.
    fn lower_state_read(&mut self, name: &str, stmts: &mut StatementBuffer) -> VarId {
        let (offset, ty, kind) = self
            .state_layout
            .get(name)
            .unwrap_or_else(|| panic!("ICE: no state layout entry for `{name}`"))
            .clone();
        let dst = self.fresh_local(ty, kind, name.to_owned());
        let label = self
            .security
            .state_contracts
            .get(&offset)
            .copied()
            .unwrap_or(TaintLabel::Public);
        self.security
            .value_contracts
            .insert(dst, AirLabelContract::Concrete(label));
        stmts.push(AirStmt::StateRead {
            dst,
            state_ptr: Self::STATE_PTR,
            offset,
            ty,
            label,
        });
        dst
    }

    /// Resolve a value referenced BY NAME (a cap-op receiver `x.draw(_)`, a
    /// send/ask target, a grant cap, a spawn arg): a param/local is its `env`
    /// `VarId`; an actor state field is loaded off the state pointer (M3). The
    /// cap/actor-op nodes store their operand as a bare name, so this is the
    /// single fallback point that lets those operands come from state.
    fn resolve_name(
        &mut self,
        name: &str,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) -> VarId {
        if let Some(v) = env.get(name) {
            *v
        } else if self.state_layout.contains_key(name) {
            self.lower_state_read(name, stmts)
        } else {
            panic!("ICE: unresolved name `{name}` during AIR lowering")
        }
    }

    /// Store `val` into a state field off the state pointer. This is used by
    /// initialization and by permitted writes to mutable fields.
    /// PPS-1 — the promotion primitive. A wholesale aggregate write to a state field in a
    /// HANDLER stores a pointer to an object built in the per-dispatch scratch region, which
    /// the arena reset reclaims: the field would dangle. Promote first — allocate a copy on the
    /// PERSISTENT channel and store the copy's pointer instead.
    ///
    /// v1 covers FLAT FIXED aggregates (records/arrays/tuples of inline scalars — the shapes
    /// `type_check::universe::is_flat_scalar_aggregate` admits, and the only ones T128 now lets
    /// through). Their layout is statically known, so the copy is a fixed sequence of
    /// load/store pairs — no loop, no recursion, no runtime size. Pointer-bearing shapes stay
    /// fenced for PPS-2/3, where promotion becomes transitive.
    ///
    /// Semantics worth stating: promotion COPIES. Storing the same value into two state fields
    /// promotes twice, and the transient original keeps its own identity — records are
    /// reference-semantic everywhere else in the language, so this boundary is the exception.
    fn maybe_promote_aggregate(
        &mut self,
        ty: &Type,
        val: VarId,
        stmts: &mut StatementBuffer,
    ) -> VarId {
        if !self.in_actor_handler {
            return val;
        }
        // PPS-2a: a `str` is a fat pointer — an 8-byte header (`data_ptr@0`, `len@4`) over
        // bytes allocated elsewhere. Promoting it means promoting BOTH: copy the payload to a
        // persistent buffer (runtime length ⇒ `PromoteBytes`), then build a persistent header
        // pointing at the copy. Promoting only the header would leave the state field pointing
        // at bytes the dispatch reset reclaims.
        if matches!(ty, Type::Str) {
            return self.promote_str(val, stmts);
        }
        let Type::Named(type_name, args) = ty else {
            return val;
        };
        if !args.is_empty() {
            return val;
        }
        let Some(fields) = self.field_registry.get(type_name).cloned() else {
            return val;
        };
        self.promote_flat_aggregate(&fields, val, stmts)
    }

    /// PPS-2a/2b: copy a `str`'s payload to a persistent buffer and rebuild its header over the
    /// copy. Both halves of the fat pointer must move — promoting only the header would leave
    /// the reference pointing at bytes the dispatch reset reclaims.
    fn promote_str(&mut self, val: VarId, stmts: &mut StatementBuffer) -> VarId {
        {
            let old_data = self.fresh_local(AirType::Ptr, AirValueKind::Copy, "__promote_str_src");
            stmts.push(AirStmt::LoadField {
                dst: old_data,
                base_ptr: val,
                offset: STR_DATA_PTR_OFFSET,
                ty: AirType::Ptr,
            });
            let len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__promote_str_len");
            stmts.push(AirStmt::LoadField {
                dst: len,
                base_ptr: val,
                offset: STR_LEN_OFFSET,
                ty: AirType::U32,
            });
            let new_data =
                self.fresh_local(AirType::Ptr, AirValueKind::Copy, "__promote_str_bytes");
            stmts.push(AirStmt::PromoteBytes {
                dst: new_data,
                src: old_data,
                len,
            });
            let header = self.fresh_local(AirType::Ptr, AirValueKind::Copy, "__promote_str_hdr");
            stmts.push(AirStmt::BumpAlloc {
                dst: header,
                size_bytes: STR_HEADER_SIZE,
                align: STR_HEADER_ALIGN,
                persistent: true,
            });
            stmts.push(AirStmt::StoreField {
                base_ptr: header,
                offset: STR_DATA_PTR_OFFSET,
                val: new_data,
                ty: AirType::Ptr,
            });
            stmts.push(AirStmt::StoreField {
                base_ptr: header,
                offset: STR_LEN_OFFSET,
                val: len,
                ty: AirType::U32,
            });
            header
        }
    }

    fn promote_flat_aggregate(
        &mut self,
        fields: &[(String, u32, AirType)],
        val: VarId,
        stmts: &mut StatementBuffer,
    ) -> VarId {
        // Flat + fixed: every field an 8-byte-or-narrower scalar cell. The registry's own
        // offsets/types drive the copy, so layout stays single-sourced.
        let total_size: u32 = fields
            .iter()
            .map(|(_, offset, ty)| offset + ty.width())
            .max()
            .unwrap_or(0);
        if total_size == 0 {
            return val;
        }
        let fields = fields.to_vec();
        let promoted = self.fresh_local(AirType::Ptr, AirValueKind::Copy, "__promoted");
        stmts.push(AirStmt::BumpAlloc {
            dst: promoted,
            size_bytes: total_size,
            align: 8,
            // Forced, not inherited: the handler body is not a `$state` instance, but the
            // COPY must outlive the dispatch.
            persistent: true,
        });
        for (field_name, offset, field_ty) in &fields {
            let tmp = self.fresh_local(
                *field_ty,
                AirValueKind::Copy,
                format!("__promote_{field_name}"),
            );
            stmts.push(AirStmt::LoadField {
                dst: tmp,
                base_ptr: val,
                offset: *offset,
                ty: *field_ty,
            });
            stmts.push(AirStmt::StoreField {
                base_ptr: promoted,
                offset: *offset,
                val: tmp,
                ty: *field_ty,
            });
        }
        promoted
    }

    fn lower_state_write(&mut self, name: &str, val: VarId, stmts: &mut StatementBuffer) {
        let (offset, ty, _) = self
            .state_layout
            .get(name)
            .unwrap_or_else(|| panic!("ICE: no state layout entry for `{name}`"));
        let (offset, ty) = (*offset, *ty);
        let label = self
            .security
            .state_contracts
            .get(&offset)
            .copied()
            .unwrap_or(TaintLabel::Public);
        stmts.push(AirStmt::StateWrite {
            state_ptr: Self::STATE_PTR,
            offset,
            val,
            ty,
            label,
        });
    }

    fn lower_expr_to_var(
        &mut self,
        expr: &TypedExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) -> VarId {
        stmts.with_span(expr.span, |stmts| {
            self.lower_expr_to_var_at(expr, env, stmts)
        })
    }

    fn lower_expr_to_var_at(
        &mut self,
        expr: &TypedExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) -> VarId {
        match &expr.kind {
            // M3: a handler's state read reuses the prologue-loaded env local
            // (load-once, so double-spend is tracked); `init` loads fresh (memory
            // reflects prior stores).
            TypedExprKind::StateField(name) => {
                // S2: a `mut` field is not in the load-once env — read it fresh off
                // the state pointer so a read-after-write reflects the new value.
                if self.state_in_env && !self.mut_state_fields.contains(name) {
                    *env.get(name)
                        .expect("ICE: unresolved state field local during AIR lowering")
                } else {
                    self.lower_state_read(name, stmts)
                }
            }
            TypedExprKind::Local(name) => {
                if let Some(v) = env.get(name) {
                    *v
                } else if matches!(expr.ty, Type::Region) {
                    // Regions (DEF-2b PR-7): a LEXICAL region handle used as a value. A
                    // `region NAME { … }` block introduces no value local (it is
                    // BUMP_PTR save/restore), so the handle is not in `env`. The handle is
                    // a runtime i64 (0 = the global heap) and INERT in v1 — there is no
                    // per-region arena (AG-2b-7/AG-2b-12) — so materialize the inert `0` on
                    // demand. Only reached for a handle actually USED as a value (e.g.
                    // `Vec::in_region(NAME)`); a `Region` PARAMETER is in `env` and resolves
                    // above, so existing codegen is byte-identical.
                    self.materialize_region_handle(name, stmts)
                } else {
                    panic!("ICE: unresolved local during AIR lowering")
                }
            }
            _ => {
                let dst = self.fresh_local(
                    lower_type(&expr.ty),
                    classify_value_kind(&expr.ty),
                    String::new(),
                );
                self.lower_expr_into(dst, expr, env, stmts);
                dst
            }
        }
    }

    /// Emit a linear-consumption move-site for a `declassify` /
    /// `declassify_ct` capability (F002).
    ///
    /// Declassification is a pure type-system operation — the value flows
    /// through unchanged — but the capability it names is LINEAR: spec
    /// `docs/specs/secret-ct.md` §3.4 requires "one use per construction",
    /// and the CT011 attack row maps declassify-cap reuse to O001. Linearity
    /// is enforced only over AIR move-sites by `ownership::verify`, so unless
    /// the cap reaches AIR as a move, one owned `Declassify`/`DeclassifyCT`
    /// cap can declassify unbounded secrets (the F002 soundness hole — the
    /// prior lowering dropped `decl.cap` entirely).
    ///
    /// CSIR v8 needs the release to remain explicit, so this helper now only
    /// materializes the capability operand and its dead ownership scratch. The
    /// enclosing `SecurityRelease` remains runtime-transparent while giving
    /// every AIR walker a single honest move-site to classify.
    fn consume_declassify_cap(
        &mut self,
        cap: &TypedExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) -> (VarId, VarId) {
        let cap_var = self.lower_expr_to_var(cap, env, stmts);
        // Mirror the source cap's value-kind so ownership sees the same linear
        // move as the former dead `Assign`; caps are pointer-backed (`Ptr`).
        let kind = self.var_kind(cap_var);
        let sink = self.fresh_local(AirType::Ptr, kind, "__declassify_cap");
        (cap_var, sink)
    }

    /// Regions (DEF-2b PR-7): materialize the INERT i64 value of a lexical region handle
    /// (`0` = the global heap). v1 has a single bump allocator and no per-region arena, so
    /// the handle does not address anything — it exists for the type-level region model and
    /// the forward-compat `Vec`/`Map` `alloc` field. A fresh `i64` local set to the constant
    /// `0`.
    fn materialize_region_handle(&mut self, name: &str, stmts: &mut StatementBuffer) -> VarId {
        let dst = self.fresh_local(AirType::I64, AirValueKind::Copy, name.to_string());
        stmts.push(AirStmt::Assign {
            dst,
            val: AirValue::IntLit(0),
        });
        dst
    }

    fn lower_expr_into(
        &mut self,
        dst: VarId,
        expr: &TypedExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        stmts.with_span(expr.span, |stmts| {
            self.lower_expr_into_at(dst, expr, env, stmts)
        });
    }

    fn lower_expr_into_at(
        &mut self,
        dst: VarId,
        expr: &TypedExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        // Record `dst`'s def-site span (the span of the expression that
        // produces its value) so the capability verifier can locate
        // C001-C004 violations in source. AIR is otherwise span-free.
        // `dst` is single-assignment, so this is its one canonical
        // def-site; recording for non-cap dsts too is harmless (the side
        // map is only consulted for the offending cap `VarId`).
        self.debug_spans.insert(dst, expr.span);
        match &expr.kind {
            // PR-E3: an `f"…{e}…"` lowers HERE (Option 2b) — the typed FString node
            // survives type-check (so the no-stdlib typecheck_differential compares it
            // as `str` → parity) and is folded into a left-associative `str_concat`
            // chain of synthetic typed `Call`s, then lowered via the existing Call
            // machinery. `str_concat` is in `function_ids` because the `FStrBegin`
            // ambient trigger injected `string.sigil`. Chunks are str literals; holes
            // are their already-typed exprs (str — PR-E3a). ≥1 part always (ET-E3).
            TypedExprKind::FString(fs) => {
                use crate::typed_ast::{TypedCallExpr, TypedFStringPart};
                let find_fn = |suffix: &str| -> Option<String> {
                    self.function_ids
                        .keys()
                        .find(|k| k.rsplit("::").next() == Some(suffix))
                        .cloned()
                };
                let concat_name = find_fn("str_concat")
                    .expect("ICE: f-string lowering requires str_concat (string.sigil) in scope");
                // PR-E3b: i64/bool holes auto-convert — an i64 hole wraps in `str_itoa`,
                // a bool hole in `str_of_bool` (both in the ambient-injected string.sigil).
                // A str hole passes through. Type-check already T262'd any other hole type.
                let itoa_name = find_fn("str_itoa");
                let bool_name = find_fn("str_of_bool");
                let mk_lit = |s: &str| TypedExpr {
                    ty: Type::Str,
                    kind: TypedExprKind::Literal(Literal::Str(s.to_string())),
                    span: expr.span,
                    refinement: None,
                };
                let wrap_call = |callee: String, arg: TypedExpr| TypedExpr {
                    ty: Type::Str,
                    kind: TypedExprKind::Call(TypedCallExpr {
                        callee,
                        args: vec![arg],
                    }),
                    span: expr.span,
                    refinement: None,
                };
                let mut acc: Option<TypedExpr> = None;
                for part in &fs.parts {
                    let part_expr = match part {
                        TypedFStringPart::Literal(s) => mk_lit(s),
                        TypedFStringPart::Hole(e) => {
                            let h = (**e).clone();
                            if matches!(h.ty, Type::I64) {
                                wrap_call(
                                    itoa_name.clone().expect(
                                        "ICE: i64 f-string hole requires str_itoa in scope",
                                    ),
                                    h,
                                )
                            } else if matches!(h.ty, Type::Bool) {
                                wrap_call(
                                    bool_name.clone().expect(
                                        "ICE: bool f-string hole requires str_of_bool in scope",
                                    ),
                                    h,
                                )
                            } else {
                                h
                            }
                        }
                    };
                    acc = Some(match acc {
                        None => part_expr,
                        Some(left) => TypedExpr {
                            ty: Type::Str,
                            kind: TypedExprKind::Call(TypedCallExpr {
                                callee: concat_name.clone(),
                                args: vec![left, part_expr],
                            }),
                            span: expr.span,
                            refinement: None,
                        },
                    });
                }
                let chain = acc.unwrap_or_else(|| mk_lit(""));
                self.lower_expr_into(dst, &chain, env, stmts);
            }
            TypedExprKind::Literal(Literal::Int(value)) => {
                // u256 PR-U2 (E9): a small integer literal in u256 context (e.g.
                // `let balance: u256 = 0;`) materializes a fresh 32-byte cell with
                // limb0 = value (type-check guarantees value >= 0 here); otherwise
                // it is an ordinary machine-int constant.
                if matches!(expr.ty, Type::U256) {
                    self.materialize_u256_cell(dst, [*value as u64, 0, 0, 0], stmts);
                } else {
                    stmts.push(AirStmt::Assign {
                        dst,
                        val: AirValue::IntLit(*value),
                    });
                }
            }
            TypedExprKind::Literal(Literal::Int256(limbs)) => {
                // u256 PR-U2: a wide literal materializes its 4 limbs into a fresh
                // 32-byte cell (always u256).
                self.materialize_u256_cell(dst, *limbs, stmts);
            }
            TypedExprKind::Literal(Literal::Bool(value)) => stmts.push(AirStmt::Assign {
                dst,
                val: AirValue::BoolLit(*value),
            }),
            TypedExprKind::Literal(Literal::Float(value)) => stmts.push(AirStmt::Assign {
                dst,
                val: AirValue::FloatLit(*value),
            }),
            TypedExprKind::Literal(Literal::Str(value)) => {
                // PR S1 / N17-S1 + N20-S1 + N28-S1: `Type::Str` runtime
                // layout is an 8-byte fat-pointer header
                // `[data_ptr: u32 @ STR_DATA_PTR_OFFSET=0,
                //   len: u32 @ STR_LEN_OFFSET=4]` mirroring PR AF's
                // `Type::Slice`. String literals back into the WASM
                // static-data section (collected by `wasm.rs:215`'s
                // pass over `AirValue::StrLit` Assigns); each USE
                // allocates a per-call header pointing at the shared
                // static bytes.
                //
                // `AirValue::StrLit(text)` now semantically means
                // "the U32 static-data offset of `text`" rather than
                // "a Ptr to the bytes." The wasm emitter at
                // `wasm.rs:1530` still emits `I32Const(offset)` for
                // this value, but the receiving local is U32-typed
                // (the header's `data_ptr` field).
                let byte_len: u32 = value.len() as u32;
                // dst (Ptr) <- BumpAlloc 8 bytes, align 4.
                stmts.push(AirStmt::BumpAlloc {
                    persistent: self.state_backed_alloc,
                    dst,
                    size_bytes: STR_HEADER_SIZE,
                    align: STR_HEADER_ALIGN,
                });
                // data_ptr_var: U32 = static-data offset of `value`.
                let data_ptr_var =
                    self.fresh_local(AirType::U32, AirValueKind::Copy, "__str_data_ptr");
                stmts.push(AirStmt::Assign {
                    dst: data_ptr_var,
                    val: AirValue::StrLit(value.clone()),
                });
                stmts.push(AirStmt::StoreField {
                    base_ptr: dst,
                    offset: STR_DATA_PTR_OFFSET,
                    val: data_ptr_var,
                    ty: AirType::U32,
                });
                // len_var: U32 = byte length constant.
                let len_var = self.fresh_local(AirType::U32, AirValueKind::Copy, "__str_len");
                stmts.push(AirStmt::Assign {
                    dst: len_var,
                    val: AirValue::IntLit(byte_len as i64),
                });
                stmts.push(AirStmt::StoreField {
                    base_ptr: dst,
                    offset: STR_LEN_OFFSET,
                    val: len_var,
                    ty: AirType::U32,
                });
            }
            // M3: a state read loads the field off the state pointer (`VarId(0)`)
            // directly into `dst`.
            TypedExprKind::StateField(name) => {
                // S2: a `mut` field is read fresh (not from the load-once env cache).
                if self.state_in_env && !self.mut_state_fields.contains(name) {
                    // Handler: copy the prologue-loaded env local into `dst`.
                    let src = *env
                        .get(name)
                        .expect("ICE: unresolved state field local during AIR lowering");
                    stmts.push(AirStmt::Assign {
                        dst,
                        val: AirValue::Var(src),
                    });
                } else {
                    // init: fresh load off the state pointer into `dst`.
                    let (offset, ty, _) = self
                        .state_layout
                        .get(name)
                        .unwrap_or_else(|| panic!("ICE: no state layout entry for `{name}`"));
                    let (offset, ty) = (*offset, *ty);
                    let label = self
                        .security
                        .state_contracts
                        .get(&offset)
                        .copied()
                        .unwrap_or(TaintLabel::Public);
                    self.security
                        .value_contracts
                        .insert(dst, AirLabelContract::Concrete(label));
                    stmts.push(AirStmt::StateRead {
                        dst,
                        state_ptr: Self::STATE_PTR,
                        offset,
                        ty,
                        label,
                    });
                }
            }
            TypedExprKind::Local(name) => {
                let val = if let Some(v) = env.get(name) {
                    AirValue::Var(*v)
                } else if matches!(expr.ty, Type::Region) {
                    // Regions (DEF-2b PR-7): a lexical region handle bound by `let` /
                    // passed as a value — the inert `0` handle (see `materialize_region_handle`).
                    AirValue::IntLit(0)
                } else {
                    panic!("ICE: unresolved local during AIR lowering")
                };
                stmts.push(AirStmt::Assign { dst, val });
            }
            TypedExprKind::Borrow(borrow) => {
                // PR AF / N19-AF + N23-AF: Array→Slice borrow allocates
                // an 8-byte fat-pointer header. Layout:
                //   [data_ptr: u32 @0, len: u32 @4]
                // where `data_ptr` points past the array's 4-byte length
                // prefix at the first element, and `len` is the array's
                // (compile-time known) size. Slice consumers (`for-in`,
                // `.len()`, `.is_empty()`, future indexing) read from
                // this layout via the canonical helpers (N14-AF).
                //
                // Non-slice borrows keep the existing `AirStmt::Borrow`
                // pointer-alias semantics. Per N23-AF the lowering is
                // provenance-agnostic — locals, function-return
                // results, field-access results, and match-arm results
                // all route through the same code path because
                // `borrow.inner.ty` is `Type::Array { size, .. }`
                // regardless of how `inner` was produced.
                let is_array_to_slice = matches!(&borrow.inner.ty, Type::Array { .. })
                    && matches!(&expr.ty, Type::Slice(_));
                if is_array_to_slice {
                    let src = self.lower_expr_to_var(&borrow.inner, env, stmts);
                    let array_size: u32 = match &borrow.inner.ty {
                        Type::Array { size, .. } => *size,
                        _ => unreachable!("guarded by is_array_to_slice"),
                    };
                    // Allocate the 8-byte slice header.
                    stmts.push(AirStmt::BumpAlloc {
                        persistent: self.state_backed_alloc,
                        dst,
                        size_bytes: SLICE_HEADER_SIZE,
                        align: SLICE_HEADER_ALIGN,
                    });
                    // data_ptr = src (the array's BumpAlloc start —
                    // pointing AT the u32 length prefix at offset 0).
                    // LoadDynamic's wasm-emit bakes a +4 header skip
                    // into its mem_arg, so element indexing via
                    // LoadDynamic { base_ptr: data_ptr, index,
                    // elem_size } reads `arr + 4 + index*elem_size`,
                    // i.e., the index-th element. No additional
                    // pointer arithmetic at borrow time.
                    stmts.push(AirStmt::StoreField {
                        base_ptr: dst,
                        offset: SLICE_DATA_PTR_OFFSET,
                        val: src,
                        ty: AirType::Ptr,
                    });
                    // len = compile-time-known array size.
                    let len_var =
                        self.fresh_local(AirType::U32, AirValueKind::Copy, "__slice_len_init");
                    stmts.push(AirStmt::Assign {
                        dst: len_var,
                        val: AirValue::IntLit(array_size as i64),
                    });
                    stmts.push(AirStmt::StoreField {
                        base_ptr: dst,
                        offset: SLICE_LEN_OFFSET,
                        val: len_var,
                        ty: AirType::U32,
                    });
                } else {
                    let src = self.lower_expr_to_var(&borrow.inner, env, stmts);
                    stmts.push(AirStmt::Borrow {
                        dst,
                        src,
                        mutable: borrow.mutable,
                    });
                }
            }
            TypedExprKind::Declassify(decl) => {
                let src = self.fresh_local(
                    lower_type(&decl.value.ty),
                    classify_value_kind(&decl.value.ty),
                    "__release_src",
                );
                self.lower_expr_into(src, &decl.value, env, stmts);
                let (cap, cap_scratch) = self.consume_declassify_cap(&decl.cap, env, stmts);
                self.security
                    .value_contracts
                    .insert(dst, AirLabelContract::Concrete(TaintLabel::Public));
                stmts.push(AirStmt::SecurityRelease {
                    dst,
                    src,
                    cap,
                    cap_scratch,
                    stage: AirReleaseStage::Ordinary,
                });
            }
            TypedExprKind::DeclassifyCt(decl) => {
                let src = self.fresh_local(
                    lower_type(&decl.value.ty),
                    classify_value_kind(&decl.value.ty),
                    "__release_ct_src",
                );
                self.lower_expr_into(src, &decl.value, env, stmts);
                let (cap, cap_scratch) = self.consume_declassify_cap(&decl.cap, env, stmts);
                self.security
                    .value_contracts
                    .insert(dst, AirLabelContract::Concrete(TaintLabel::Secret));
                stmts.push(AirStmt::SecurityRelease {
                    dst,
                    src,
                    cap,
                    cap_scratch,
                    stage: AirReleaseStage::ConstantTime,
                });
            }
            TypedExprKind::Call(call) => self.lower_call_expr(dst, call, env, stmts),
            TypedExprKind::IndirectCall(call) => {
                self.lower_indirect_call_expr(dst, call, env, stmts)
            }
            TypedExprKind::Intrinsic(intrinsic) => {
                self.lower_intrinsic_expr(dst, intrinsic, env, stmts)
            }
            TypedExprKind::Send(send) => self.lower_send_expr(send, env, stmts),
            TypedExprKind::Ask(ask) => self.lower_ask_expr(dst, ask, env, stmts),
            TypedExprKind::Spawn(spawn) => self.lower_spawn_expr(dst, spawn, env, stmts),
            TypedExprKind::Binary(bin) => self.lower_binary_expr(dst, bin, env, stmts),
            TypedExprKind::RecordConstruct(record) => {
                self.lower_record_construct(dst, record, env, stmts)
            }
            TypedExprKind::FieldAccess(access) => self.lower_field_access(dst, access, env, stmts),
            TypedExprKind::EnumConstruct(ctor) => self.lower_enum_construct(dst, ctor, env, stmts),
            TypedExprKind::CapRestrict(restrict) => {
                self.lower_cap_restrict(dst, restrict, env, stmts)
            }
            TypedExprKind::CapSplit(split) => self.lower_cap_split(dst, split, env, stmts),
            TypedExprKind::CapDraw(draw) => self.lower_cap_draw(dst, draw, env, stmts),
            TypedExprKind::Mint(mint) => self.lower_cap_mint(dst, mint, env, stmts),
            TypedExprKind::Grant(grant) => self.lower_grant_expr(dst, grant, env, stmts),
            TypedExprKind::Handle(handle) => self.lower_handle_expr(dst, handle, env, stmts),
            // Effect Handlers (EH3, C-LOWER): the new nodes are gated (E004) by
            // `effect_handler_gate` BEFORE AIR lowering, so they can never reach
            // here. The ICE turns a missed-gate invariant violation into a loud
            // failure rather than a silent miscompile. Real lowering lands in EH4.
            TypedExprKind::Perform(_)
            | TypedExprKind::ClauseHandle(_)
            | TypedExprKind::Resume(_) => {
                unreachable!(
                    "ICE: effect-handler node reached AIR lowering — must be gated (E004) before AIR"
                )
            }
            TypedExprKind::ClosureConstruct(ctor) => {
                self.lower_closure_construct(dst, ctor, env, stmts)
            }
            TypedExprKind::ArrayLit(array_lit) => self.lower_array_lit(dst, array_lit, env, stmts),
            TypedExprKind::Index(index_expr) => self.lower_index_expr(dst, index_expr, env, stmts),
            TypedExprKind::Slice(slice) => self.lower_slice_expr(dst, expr, slice, env, stmts),
            TypedExprKind::ResultCtor(result) => self.lower_result_ctor(dst, result, env, stmts),
            TypedExprKind::Try(try_expr) => self.lower_try_expr(dst, try_expr, env, stmts),
            TypedExprKind::ExternCall(extern_call) => {
                self.lower_extern_call(dst, extern_call, env, stmts)
            }
            TypedExprKind::Region(region) => self.lower_region_expr(dst, region, env, stmts),
        }
    }

    fn lower_call_expr(
        &mut self,
        dst: VarId,
        call: &TypedCallExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        // PPS-2b/3: a pointer-bearing argument STORED by a state-backed collection must be
        // promoted. The single correct point is the innermost storing call — `Vec::push` inside a
        // colored instance — so a `Map`'s insert promotes exactly once (key at `keys.push`,
        // value at `vals.push`) rather than once per frame on the way down. `str` promotes bytes
        // + header (2b); a FLAT record promotes by the PPS-1 field copy (3). Elements with
        // pointer-bearing interiors are fenced at admission, so reaching here with one is
        // impossible by construction.
        // PPS-5 capstone fix: `__set__` is a storing call too — a map INSERT
        // on an existing key overwrites via `vals.set(vidx, val)`, not push,
        // and the transitive coloring already names that instance `$state`.
        // Without this, an overwritten str/record value stored a TRANSIENT
        // pointer (probed: traps after the dispatch).
        let promote_stored_args = call.callee.ends_with(STATE_VEC_MONO_SUFFIX)
            && (call.callee.contains("__push__") || call.callee.contains("__set__"));
        let args = call
            .args
            .iter()
            .map(|arg| {
                let var = self.lower_expr_to_var(arg, env, stmts);
                if !promote_stored_args {
                    return var;
                }
                if matches!(arg.ty, Type::Str) {
                    return self.promote_str(var, stmts);
                }
                if let Type::Named(type_name, type_args) = &arg.ty
                    && type_args.is_empty()
                    && let Some(fields) = self.field_registry.get(type_name).cloned()
                {
                    return self.promote_flat_aggregate(&fields, var, stmts);
                }
                var
            })
            .collect::<Vec<_>>();
        let func = *self.function_ids.get(&call.callee).unwrap_or_else(|| {
            panic!(
                "ICE: unresolved callee `{}` during AIR lowering",
                call.callee
            )
        });
        stmts.push(AirStmt::Call {
            dst: self.call_dst(dst),
            func,
            args,
        });
    }

    /// HOF prerequisite: general closure-call dispatch through a
    /// closure-typed local variable. Mirrors `lower_grant_expr`'s
    /// CallIndirect pattern WITHOUT the GrantBegin/GrantEnd
    /// lifecycle (per N7-HOF; only grant-wrapped dispatch needs
    /// the capability acquisition envelope).
    ///
    /// Steps (per N1/N2/N5/N14-HOF):
    /// 1. Look up `call.callee_local` in env → `closure_var`
    ///    (pointer to the heap-allocated closure struct).
    /// 2. LoadField at `CLOSURE_TABLE_IDX_OFFSET` (N10-HOF) →
    ///    `table_idx` (i32, the func_id of the lambda-lifted
    ///    closure body).
    /// 3. Lower the user-supplied args.
    /// 4. Build the AIR signature via `build_indirect_call_signature`
    ///    (N14-HOF): prepends `AirType::Ptr` for env_ptr at
    ///    position 0, then lowers `callee_ty`'s param-types and
    ///    return-type.
    /// 5. Emit `AirStmt::CallIndirect` with `args[0] = closure_var`
    ///    (N2-HOF env_ptr convention) followed by user args.
    ///
    /// Per N8-HOF: `callee_ty` is statically `Type::Fn(_, _, _)`;
    /// the type-check site only produces IndirectCall when env
    /// returns a Type::Fn local. Debug-assert defends.
    fn lower_indirect_call_expr(
        &mut self,
        dst: VarId,
        call: &TypedIndirectCallExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        debug_assert!(
            matches!(call.callee_ty, Type::Fn(_, _, _, _)),
            "ICE: TypedIndirectCallExpr.callee_ty must be Type::Fn, got {:?}",
            call.callee_ty
        );

        let closure_var = *env.get(&call.callee_local).unwrap_or_else(|| {
            panic!(
                "ICE: unresolved closure-typed local `{}` during AIR lowering",
                call.callee_local
            )
        });

        // LoadField table_idx from closure struct at the canonical offset.
        let table_idx = self.fresh_local(AirType::I32, AirValueKind::Copy, "__closure_table_idx");
        stmts.push(AirStmt::LoadField {
            dst: table_idx,
            base_ptr: closure_var,
            offset: CLOSURE_TABLE_IDX_OFFSET,
            ty: AirType::I32,
        });

        // Lower user-supplied args.
        let user_args: Vec<VarId> = call
            .args
            .iter()
            .map(|arg| self.lower_expr_to_var(arg, env, stmts))
            .collect();

        // Build the AIR signature for CallIndirect's type lookup.
        let signature = build_indirect_call_signature(&call.callee_ty);

        // Prepend closure_var (env_ptr) at args[0] per N2-HOF.
        let mut args = Vec::with_capacity(1 + user_args.len());
        args.push(closure_var);
        args.extend(user_args);

        stmts.push(AirStmt::CallIndirect {
            dst: self.call_dst(dst),
            signature,
            table_index: table_idx,
            args,
        });
        if call.kind == TypedIndirectCallKind::AbortiveEffect {
            self.abortive_transfer_seen = true;
        }
    }

    /// NC1/CM1 — bounds trap for the `Vec<T>` element intrinsics: wrap
    /// `index` and `bound` to u32 and `TrapIf(index >= bound)`. A negative
    /// `index` wraps to a huge u32 and trips the same trap, so no separate
    /// negative-index check is needed; the worst case for a bad index is a
    /// clean wasm trap, never an out-of-buffer access. The caller passes
    /// `len` for reads (only initialized slots) and `cap` for writes (the
    /// allocated slot at `index == len < cap`). (vec.sigil — the only,
    /// grep-enforced caller — passes i64 index/bound, so the wrap is exact.)
    fn emit_vec_bound_trap(&mut self, index: VarId, bound: VarId, stmts: &mut StatementBuffer) {
        let idx32 = self.fresh_local(AirType::U32, AirValueKind::Copy, "__vec_idx32");
        stmts.push(AirStmt::WrapI64 {
            dst: idx32,
            src: index,
        });
        let bound32 = self.fresh_local(AirType::U32, AirValueKind::Copy, "__vec_bound32");
        stmts.push(AirStmt::WrapI64 {
            dst: bound32,
            src: bound,
        });
        let oob = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__vec_oob");
        stmts.push(AirStmt::Assign {
            dst: oob,
            val: AirValue::Binary {
                lhs: idx32,
                op: BinaryOp::GtEq,
                rhs: bound32,
            },
        });
        stmts.push(AirStmt::TrapIf { cond: oob });
    }

    /// UTF-8 boundary enforcement (`substr`): trap if `pos` lands INSIDE a
    /// multi-byte codepoint of the receiver — i.e. `0 < pos < len` AND the byte
    /// at `data_ptr + pos` is a continuation byte `(b & 0xC0) == 0x80`. This is
    /// exactly `!is_char_boundary(pos)` over `pos ∈ [0, len]` — the single
    /// predicate shared with `strings::str_is_char_boundary` (the rail), so the
    /// trap (the floor) can never disagree with it. Branch-free and OOB-safe:
    /// the load offset is `ct_select(pos < len, pos, 0)`, so it NEVER reads
    /// `data_ptr + len` (the `pos == len` boundary) nor anything for an empty
    /// receiver — `data_ptr` itself is always a valid linear address, and the
    /// dummy byte read at a non-interior `pos` is discarded by `interior_pos`.
    /// `pos_i64` / `len_i64` are the i64-domain values already proven `0 ≤ pos ≤
    /// len` by the bounds checks; `data_ptr` is the receiver's `data_ptr` (U32).
    fn emit_str_boundary_trap(
        &mut self,
        data_ptr: VarId,
        pos_i64: VarId,
        len_i64: VarId,
        stmts: &mut StatementBuffer,
    ) {
        let zero = self.fresh_local(AirType::I64, AirValueKind::Copy, "__sb_zero");
        stmts.push(AirStmt::Assign {
            dst: zero,
            val: AirValue::IntLit(0),
        });
        // pos < len — the interior upper bound AND the OOB-safe load guard.
        let lt_len = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__sb_lt_len");
        stmts.push(AirStmt::Assign {
            dst: lt_len,
            val: AirValue::Binary {
                lhs: pos_i64,
                op: BinaryOp::Lt,
                rhs: len_i64,
            },
        });
        // pos > 0 — the interior lower bound (`pos == 0` is always a boundary).
        let gt_zero = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__sb_gt_zero");
        stmts.push(AirStmt::Assign {
            dst: gt_zero,
            val: AirValue::Binary {
                lhs: pos_i64,
                op: BinaryOp::Gt,
                rhs: zero,
            },
        });
        let interior_pos = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__sb_interior_pos");
        stmts.push(AirStmt::Assign {
            dst: interior_pos,
            val: AirValue::Binary {
                lhs: gt_zero,
                op: BinaryOp::BitAnd,
                rhs: lt_len,
            },
        });
        // OOB-safe offset: pos if pos < len, else 0 (a valid in-bounds address
        // whose byte is discarded by `interior_pos`). Never `data_ptr + len`.
        let safe_off = self.fresh_local(AirType::I64, AirValueKind::Copy, "__sb_safe_off");
        stmts.push(AirStmt::IntrinsicCtSelect {
            dst: safe_off,
            cond: lt_len,
            then_val: pos_i64,
            else_val: zero,
        });
        let safe_off_u32 = self.fresh_local(AirType::U32, AirValueKind::Copy, "__sb_safe_off32");
        stmts.push(AirStmt::WrapI64 {
            dst: safe_off_u32,
            src: safe_off,
        });
        let addr = self.fresh_local(AirType::U32, AirValueKind::Copy, "__sb_addr");
        stmts.push(AirStmt::Assign {
            dst: addr,
            val: AirValue::Binary {
                lhs: data_ptr,
                op: BinaryOp::Add,
                rhs: safe_off_u32,
            },
        });
        let byte = self.fresh_local(AirType::I64, AirValueKind::Copy, "__sb_byte");
        stmts.push(AirStmt::IntrinsicLoad8 {
            dst: byte,
            ptr: addr,
        });
        // continuation byte ⟺ (b & 0xC0) == 0x80.
        let c0 = self.fresh_local(AirType::I64, AirValueKind::Copy, "__sb_c0");
        stmts.push(AirStmt::Assign {
            dst: c0,
            val: AirValue::IntLit(0xC0),
        });
        let masked = self.fresh_local(AirType::I64, AirValueKind::Copy, "__sb_masked");
        stmts.push(AirStmt::Assign {
            dst: masked,
            val: AirValue::Binary {
                lhs: byte,
                op: BinaryOp::BitAnd,
                rhs: c0,
            },
        });
        let c80 = self.fresh_local(AirType::I64, AirValueKind::Copy, "__sb_c80");
        stmts.push(AirStmt::Assign {
            dst: c80,
            val: AirValue::IntLit(0x80),
        });
        let is_cont = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__sb_is_cont");
        stmts.push(AirStmt::Assign {
            dst: is_cont,
            val: AirValue::Binary {
                lhs: masked,
                op: BinaryOp::Eq,
                rhs: c80,
            },
        });
        // trap ⟺ interior position AND continuation byte.
        let trap = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__sb_trap");
        stmts.push(AirStmt::Assign {
            dst: trap,
            val: AirValue::Binary {
                lhs: interior_pos,
                op: BinaryOp::BitAnd,
                rhs: is_cont,
            },
        });
        stmts.push(AirStmt::TrapIf { cond: trap });
    }

    fn lower_intrinsic_expr(
        &mut self,
        dst: VarId,
        intrinsic: &TypedIntrinsicExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let args = intrinsic
            .args
            .iter()
            .map(|arg| self.lower_expr_to_var(arg, env, stmts))
            .collect::<Vec<_>>();
        match &intrinsic.kind {
            TypedIntrinsicKind::Alloc => {
                let size = *args
                    .first()
                    .expect("ICE: alloc intrinsic missing size argument");
                stmts.push(AirStmt::IntrinsicAlloc {
                    dst,
                    size,
                    // AGG2b-2: persistent iff this body is a state-backed `Vec<scalar>` instance.
                    persistent: self.state_backed_alloc,
                });
            }
            TypedIntrinsicKind::Load8 => {
                let ptr = *args
                    .first()
                    .expect("ICE: load8 intrinsic missing pointer argument");
                stmts.push(AirStmt::IntrinsicLoad8 { dst, ptr });
            }
            TypedIntrinsicKind::Store8 => {
                let ptr = *args
                    .first()
                    .expect("ICE: store8 intrinsic missing pointer argument");
                let val = *args
                    .get(1)
                    .expect("ICE: store8 intrinsic missing value argument");
                stmts.push(AirStmt::IntrinsicStore8 { ptr, val });
            }
            TypedIntrinsicKind::SlotNew { cap_type } => {
                stmts.push(AirStmt::SlotNew {
                    dst,
                    cap_type: cap_type.clone(),
                });
            }
            TypedIntrinsicKind::SlotPut => {
                let slot = *args
                    .first()
                    .expect("ICE: slot_put intrinsic missing slot argument");
                let cap = *args
                    .get(1)
                    .expect("ICE: slot_put intrinsic missing cap argument");
                stmts.push(AirStmt::SlotPut { slot, cap });
                // slot_put returns unit; dst is a placeholder. Initialize it.
                stmts.push(AirStmt::Assign {
                    dst,
                    val: AirValue::IntLit(0),
                });
            }
            TypedIntrinsicKind::SlotTake => {
                let slot = *args
                    .first()
                    .expect("ICE: slot_take intrinsic missing slot argument");
                stmts.push(AirStmt::SlotTake { dst_cap: dst, slot });
            }
            TypedIntrinsicKind::VecStore { elem } => {
                let base = *args.first().expect("ICE: vec_store missing base");
                let index = *args.get(1).expect("ICE: vec_store missing index");
                let bound = *args.get(2).expect("ICE: vec_store missing bound");
                let val = *args.get(3).expect("ICE: vec_store missing val");
                self.emit_vec_bound_trap(index, bound, stmts);
                // `base` is a Vec's `buf` field — an i64 holding a 32-bit wasm
                // address; narrow it to a Ptr so the dynamic-store address
                // math (all i32) type-checks. (StoreDynamic wraps the index
                // itself; only the base needs this.)
                let base_ptr = self.fresh_local(AirType::Ptr, AirValueKind::Copy, "__vec_base");
                stmts.push(AirStmt::WrapI64 {
                    dst: base_ptr,
                    src: base,
                });
                // Header-less (offset 0), uniform 8-byte slots; `ty: *elem`
                // selects the store opcode/width (an i32 element stores 4
                // bytes inside its 8-byte slot).
                stmts.push(AirStmt::StoreDynamic {
                    base_ptr,
                    index,
                    elem_size: 8,
                    val,
                    ty: *elem,
                    offset: 0,
                });
                // vec_store returns unit; initialize the placeholder dst.
                stmts.push(AirStmt::Assign {
                    dst,
                    val: AirValue::IntLit(0),
                });
            }
            TypedIntrinsicKind::VecLoad { elem } => {
                let base = *args.first().expect("ICE: vec_load missing base");
                let index = *args.get(1).expect("ICE: vec_load missing index");
                let bound = *args.get(2).expect("ICE: vec_load missing bound");
                self.emit_vec_bound_trap(index, bound, stmts);
                // Narrow the i64 `buf` to a Ptr (see VecStore).
                let base_ptr = self.fresh_local(AirType::Ptr, AirValueKind::Copy, "__vec_base");
                stmts.push(AirStmt::WrapI64 {
                    dst: base_ptr,
                    src: base,
                });
                stmts.push(AirStmt::LoadDynamic {
                    dst,
                    base_ptr,
                    index,
                    elem_size: 8,
                    ty: *elem,
                    offset: 0,
                });
            }
            // PR AF / Phase 1.2: `arr.len()` on Array. The receiver
            // is the array's BumpAlloc pointer; length lives at
            // offset 0 (existing array header layout, unchanged by
            // commit #2's slice migration).
            TypedIntrinsicKind::ArrayLen { size: _ } => {
                let arr = *args
                    .first()
                    .expect("ICE: ArrayLen intrinsic missing receiver argument");
                stmts.push(AirStmt::LoadField {
                    dst,
                    base_ptr: arr,
                    offset: 0,
                    ty: AirType::U32,
                });
            }
            // PR AF / Phase 1.2: `slc.len()` on Slice. Routes through
            // the canonical `slice_len_var` helper (N14-AF) which
            // reads `SLICE_LEN_OFFSET` from the fat-pointer header.
            TypedIntrinsicKind::SliceLen => {
                let slc = *args
                    .first()
                    .expect("ICE: SliceLen intrinsic missing receiver argument");
                let len = self.slice_len_var(slc, stmts);
                stmts.push(AirStmt::Assign {
                    dst,
                    val: AirValue::Var(len),
                });
            }
            // PR AF / Phase 1.5: `arr.is_empty()` = `arr.len() == 0`.
            // Emit length-load + compare-with-zero. Uniform shape
            // with SliceIsEmpty modulo the length-load source.
            TypedIntrinsicKind::ArrayIsEmpty { size: _ } => {
                let arr = *args
                    .first()
                    .expect("ICE: ArrayIsEmpty intrinsic missing receiver argument");
                let len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__arr_len");
                stmts.push(AirStmt::LoadField {
                    dst: len,
                    base_ptr: arr,
                    offset: 0,
                    ty: AirType::U32,
                });
                let zero = self.fresh_local(AirType::U32, AirValueKind::Copy, "__zero");
                stmts.push(AirStmt::Assign {
                    dst: zero,
                    val: AirValue::IntLit(0),
                });
                stmts.push(AirStmt::Assign {
                    dst,
                    val: AirValue::Binary {
                        lhs: len,
                        op: BinaryOp::Eq,
                        rhs: zero,
                    },
                });
            }
            TypedIntrinsicKind::SliceIsEmpty => {
                let slc = *args
                    .first()
                    .expect("ICE: SliceIsEmpty intrinsic missing receiver argument");
                let len = self.slice_len_var(slc, stmts);
                let zero = self.fresh_local(AirType::U32, AirValueKind::Copy, "__zero");
                stmts.push(AirStmt::Assign {
                    dst: zero,
                    val: AirValue::IntLit(0),
                });
                stmts.push(AirStmt::Assign {
                    dst,
                    val: AirValue::Binary {
                        lhs: len,
                        op: BinaryOp::Eq,
                        rhs: zero,
                    },
                });
            }
            // Phase-1 completion: `arr.contains(x)` on `Type::Array`. The
            // array length lives in the u32 header at offset 0; the scan loop
            // (emitted in wasm) reads element `idx` at `arr + 4 + idx*width`
            // (skip_header = true).
            TypedIntrinsicKind::ArrayContains { elem } => {
                let arr = *args
                    .first()
                    .expect("ICE: ArrayContains intrinsic missing receiver argument");
                let needle = *args
                    .get(1)
                    .expect("ICE: ArrayContains intrinsic missing needle argument");
                let len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__arr_len");
                stmts.push(AirStmt::LoadField {
                    dst: len,
                    base_ptr: arr,
                    offset: 0,
                    ty: AirType::U32,
                });
                let idx = self.fresh_local(AirType::U32, AirValueKind::Copy, "__contains_idx");
                stmts.push(AirStmt::ArrayOrSliceContains {
                    dst,
                    base_ptr: arr,
                    len,
                    needle,
                    idx,
                    elem: *elem,
                });
            }
            // Phase-1 completion: `slc.contains(x)` on `Type::Slice`. Base ptr
            // + length come from the fat-pointer header; the element load uses
            // offset 0 (data_ptr already points past the header → skip_header
            // = false).
            TypedIntrinsicKind::SliceContains { elem } => {
                let slc = *args
                    .first()
                    .expect("ICE: SliceContains intrinsic missing receiver argument");
                let needle = *args
                    .get(1)
                    .expect("ICE: SliceContains intrinsic missing needle argument");
                let len = self.slice_len_var(slc, stmts);
                let data_ptr = self.slice_data_ptr_var(slc, stmts);
                let idx = self.fresh_local(AirType::U32, AirValueKind::Copy, "__contains_idx");
                stmts.push(AirStmt::ArrayOrSliceContains {
                    dst,
                    base_ptr: data_ptr,
                    len,
                    needle,
                    idx,
                    elem: *elem,
                });
            }
            // Phase-1 completion: `slc.first()` / `slc.last()` on `Type::Slice`
            // → `Option<T>`. Pre-allocate the Option struct here (sized from
            // the enum registry, exactly as `lower_enum_construct` does); the
            // wasm branch fills tag (+ payload) per the runtime length.
            TypedIntrinsicKind::SliceFirst { elem } | TypedIntrinsicKind::SliceLast { elem } => {
                let slc = *args
                    .first()
                    .expect("ICE: Slice first/last intrinsic missing receiver argument");
                let is_last = matches!(intrinsic.kind, TypedIntrinsicKind::SliceLast { .. });
                let len = self.slice_len_var(slc, stmts);
                let data_ptr = self.slice_data_ptr_var(slc, stmts);
                let option_size = self
                    .enum_registry
                    .get("Option")
                    .unwrap_or_else(|| {
                        panic!("ICE: Option enum not registered for slice first/last")
                    })
                    .total_size;
                stmts.push(AirStmt::BumpAlloc {
                    persistent: self.state_backed_alloc,
                    dst,
                    size_bytes: option_size,
                    align: 4,
                });
                stmts.push(AirStmt::SliceOptionElem {
                    dst,
                    data_ptr,
                    len,
                    is_last,
                    elem: *elem,
                });
            }
            // PR S1 / N6-S1: `s.len()` on Type::Str loads the `len`
            // field from the fat-pointer header (offset 4). The
            // header layout is fixed by `STR_LEN_OFFSET`.
            // Phase-3 / integer width conversion. Dispatch on (from, to) widths:
            // same wasm rep → typed copy; 8→4 → WrapI64 (truncate); i32→8 →
            // SignExtendI32; u32→8 → ExtendU32. The dst local carries the target
            // AIR width (set at fresh-local time from the intrinsic's result type).
            TypedIntrinsicKind::IntConvert { from, to } => {
                let src = args[0];
                if from.width() == to.width() {
                    // i32<->u32, i64<->u64, or identity — bits unchanged.
                    stmts.push(AirStmt::Assign {
                        dst,
                        val: AirValue::Var(src),
                    });
                } else if from.width() == 8 {
                    // 8-byte → 4-byte narrow: truncate (wrapping semantics).
                    stmts.push(AirStmt::WrapI64 { dst, src });
                } else if matches!(from, AirType::I32) {
                    // i32 → 8-byte widen: SIGN-extend (preserve negatives).
                    stmts.push(AirStmt::SignExtendI32 { dst, src });
                } else {
                    // u32 → 8-byte widen: ZERO-extend.
                    stmts.push(AirStmt::ExtendU32 { dst, src });
                }
            }
            TypedIntrinsicKind::StrLen => {
                let header = *args
                    .first()
                    .expect("ICE: StrLen intrinsic missing receiver argument");
                // `len` is a u32 field; `.len()` now yields i64, so load the u32
                // then zero-extend into the i64 `dst`.
                let raw = self.fresh_local(AirType::U32, AirValueKind::Copy, "__str_len_u32");
                stmts.push(AirStmt::LoadField {
                    dst: raw,
                    base_ptr: header,
                    offset: STR_LEN_OFFSET,
                    ty: AirType::U32,
                });
                stmts.push(AirStmt::ExtendU32 { dst, src: raw });
            }
            // N-LEX: `s.as_output()` packs the str's fat-pointer header into the
            // forge ABI's output return `(data_ptr << 32) | len`. Loads data_ptr
            // (u32 @0) + len (u32 @4), zero-extends each to i64, then shifts + ors.
            // The host reads the emitted bytes via the positive-return memory path.
            TypedIntrinsicKind::StrAsOutput => {
                let header = *args
                    .first()
                    .expect("ICE: StrAsOutput intrinsic missing receiver argument");
                let dptr_u32 = self.fresh_local(AirType::U32, AirValueKind::Copy, "__out_dptr_u32");
                stmts.push(AirStmt::LoadField {
                    dst: dptr_u32,
                    base_ptr: header,
                    offset: STR_DATA_PTR_OFFSET,
                    ty: AirType::U32,
                });
                let dptr = self.fresh_local(AirType::I64, AirValueKind::Copy, "__out_dptr");
                stmts.push(AirStmt::ExtendU32 {
                    dst: dptr,
                    src: dptr_u32,
                });
                let len_u32 = self.fresh_local(AirType::U32, AirValueKind::Copy, "__out_len_u32");
                stmts.push(AirStmt::LoadField {
                    dst: len_u32,
                    base_ptr: header,
                    offset: STR_LEN_OFFSET,
                    ty: AirType::U32,
                });
                let len = self.fresh_local(AirType::I64, AirValueKind::Copy, "__out_len");
                stmts.push(AirStmt::ExtendU32 {
                    dst: len,
                    src: len_u32,
                });
                let shift = self.fresh_local(AirType::I64, AirValueKind::Copy, "__out_shift");
                stmts.push(AirStmt::Assign {
                    dst: shift,
                    val: AirValue::IntLit(32),
                });
                let shifted = self.fresh_local(AirType::I64, AirValueKind::Copy, "__out_shifted");
                stmts.push(AirStmt::Assign {
                    dst: shifted,
                    val: AirValue::Binary {
                        lhs: dptr,
                        op: BinaryOp::Shl,
                        rhs: shift,
                    },
                });
                stmts.push(AirStmt::Assign {
                    dst,
                    val: AirValue::Binary {
                        lhs: shifted,
                        op: BinaryOp::BitOr,
                        rhs: len,
                    },
                });
            }
            // PR S1 / N6-S1: `s.is_empty()` = `s.len() == 0`.
            TypedIntrinsicKind::StrIsEmpty => {
                let header = *args
                    .first()
                    .expect("ICE: StrIsEmpty intrinsic missing receiver argument");
                let len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__str_len");
                stmts.push(AirStmt::LoadField {
                    dst: len,
                    base_ptr: header,
                    offset: STR_LEN_OFFSET,
                    ty: AirType::U32,
                });
                let zero = self.fresh_local(AirType::U32, AirValueKind::Copy, "__zero");
                stmts.push(AirStmt::Assign {
                    dst: zero,
                    val: AirValue::IntLit(0),
                });
                stmts.push(AirStmt::Assign {
                    dst,
                    val: AirValue::Binary {
                        lhs: len,
                        op: BinaryOp::Eq,
                        rhs: zero,
                    },
                });
            }
            // PR S1 / N16-S1: `s.byte_at(i)` loads one byte from
            // `data_ptr + i` with an explicit `TrapIf i >= len`
            // bounds-check BEFORE the byte load (no modular fallback).
            // Result is U32 (byte zero-extended). The IntrinsicLoad8
            // primitive returns i64; we WrapI64 to U32 to match the
            // declared return type.
            TypedIntrinsicKind::StrByteAt {
                index: idx_air_type,
            } => {
                let header = args[0];
                let idx_raw = args[1];
                // Index width is the type-check stamp `idx_air_type` — no locals
                // scan, no params-miss; type info flows DOWN from type-check.
                // Wrap a 64-bit index down to U32 for arithmetic +
                // bounds-check parity with U32 len.
                let idx = if matches!(idx_air_type, AirType::I64 | AirType::U64) {
                    let w = self.fresh_local(AirType::U32, AirValueKind::Copy, "__byte_at_idx32");
                    stmts.push(AirStmt::WrapI64 {
                        dst: w,
                        src: idx_raw,
                    });
                    w
                } else {
                    idx_raw
                };
                // Load `len` from header (offset 4).
                let len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__byte_at_len");
                stmts.push(AirStmt::LoadField {
                    dst: len,
                    base_ptr: header,
                    offset: STR_LEN_OFFSET,
                    ty: AirType::U32,
                });
                // Bounds check: TrapIf idx >= len (N16-S1: BEFORE byte
                // load, no modular fallback).
                let oob = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__byte_at_oob");
                stmts.push(AirStmt::Assign {
                    dst: oob,
                    val: AirValue::Binary {
                        lhs: idx,
                        op: BinaryOp::GtEq,
                        rhs: len,
                    },
                });
                stmts.push(AirStmt::TrapIf { cond: oob });
                // Load `data_ptr` from header (offset 0).
                let data_ptr =
                    self.fresh_local(AirType::U32, AirValueKind::Copy, "__byte_at_data_ptr");
                stmts.push(AirStmt::LoadField {
                    dst: data_ptr,
                    base_ptr: header,
                    offset: STR_DATA_PTR_OFFSET,
                    ty: AirType::U32,
                });
                // byte_addr = data_ptr + idx.
                let byte_addr =
                    self.fresh_local(AirType::U32, AirValueKind::Copy, "__byte_at_addr");
                stmts.push(AirStmt::Assign {
                    dst: byte_addr,
                    val: AirValue::Binary {
                        lhs: data_ptr,
                        op: BinaryOp::Add,
                        rhs: idx,
                    },
                });
                // `byte_at` now yields i64; the byte is 0-255 (high bits zero),
                // so `IntrinsicLoad8` (which produces i64) writes straight into
                // the i64 `dst` — no wrap. The bounds check above stays u32, so a
                // negative index still wraps to a huge value and traps (ST-2).
                stmts.push(AirStmt::IntrinsicLoad8 {
                    dst,
                    ptr: byte_addr,
                });
            }
            // PR S(strings) / CF-S1: `s.substr(start, end) -> str`. A
            // zero-copy borrowed view: load the receiver's data_ptr/len,
            // check `0 <= start <= end <= len` in the FULL i64 domain (four
            // TrapIfs BEFORE the alloc — a ≥2³² or negative index traps
            // rather than u32-wrapping into a valid-but-wrong window), then
            // BumpAlloc an 8-byte str header pointing into the same bytes.
            TypedIntrinsicKind::StrSubstr {
                start: start_ty,
                end: end_ty,
            } => {
                let header = args[0];
                // Index widths are the type-check stamps `start_ty`/`end_ty` —
                // no locals scan, no params-miss. Widen each to I64 for the
                // i64-domain bounds check; a 32-bit arg is zero-extended (a
                // negative i32 becomes a huge positive that still trips the
                // upper-bound guard → trap).
                let start_i64 = if matches!(start_ty, AirType::I64 | AirType::U64) {
                    args[1]
                } else {
                    let w =
                        self.fresh_local(AirType::I64, AirValueKind::Copy, "__substr_start_i64");
                    stmts.push(AirStmt::ExtendU32 {
                        dst: w,
                        src: args[1],
                    });
                    w
                };
                let end_i64 = if matches!(end_ty, AirType::I64 | AirType::U64) {
                    args[2]
                } else {
                    let w = self.fresh_local(AirType::I64, AirValueKind::Copy, "__substr_end_i64");
                    stmts.push(AirStmt::ExtendU32 {
                        dst: w,
                        src: args[2],
                    });
                    w
                };
                // recv_len (U32 @ offset 4) zero-extended to I64.
                let len_u32 = self.fresh_local(AirType::U32, AirValueKind::Copy, "__substr_len");
                stmts.push(AirStmt::LoadField {
                    dst: len_u32,
                    base_ptr: header,
                    offset: STR_LEN_OFFSET,
                    ty: AirType::U32,
                });
                let len_i64 =
                    self.fresh_local(AirType::I64, AirValueKind::Copy, "__substr_len_i64");
                stmts.push(AirStmt::ExtendU32 {
                    dst: len_i64,
                    src: len_u32,
                });
                let zero = self.fresh_local(AirType::I64, AirValueKind::Copy, "__substr_zero");
                stmts.push(AirStmt::Assign {
                    dst: zero,
                    val: AirValue::IntLit(0),
                });
                // CF-S1: four i64-domain guards, each a TrapIf BEFORE the alloc.
                let g_start_neg =
                    self.fresh_local(AirType::Bool, AirValueKind::Copy, "__substr_start_neg");
                stmts.push(AirStmt::Assign {
                    dst: g_start_neg,
                    val: AirValue::Binary {
                        lhs: start_i64,
                        op: BinaryOp::Lt,
                        rhs: zero,
                    },
                });
                stmts.push(AirStmt::TrapIf { cond: g_start_neg });
                let g_end_neg =
                    self.fresh_local(AirType::Bool, AirValueKind::Copy, "__substr_end_neg");
                stmts.push(AirStmt::Assign {
                    dst: g_end_neg,
                    val: AirValue::Binary {
                        lhs: end_i64,
                        op: BinaryOp::Lt,
                        rhs: zero,
                    },
                });
                stmts.push(AirStmt::TrapIf { cond: g_end_neg });
                let g_start_gt_end =
                    self.fresh_local(AirType::Bool, AirValueKind::Copy, "__substr_start_gt_end");
                stmts.push(AirStmt::Assign {
                    dst: g_start_gt_end,
                    val: AirValue::Binary {
                        lhs: start_i64,
                        op: BinaryOp::Gt,
                        rhs: end_i64,
                    },
                });
                stmts.push(AirStmt::TrapIf {
                    cond: g_start_gt_end,
                });
                let g_end_gt_len =
                    self.fresh_local(AirType::Bool, AirValueKind::Copy, "__substr_end_gt_len");
                stmts.push(AirStmt::Assign {
                    dst: g_end_gt_len,
                    val: AirValue::Binary {
                        lhs: end_i64,
                        op: BinaryOp::Gt,
                        rhs: len_i64,
                    },
                });
                stmts.push(AirStmt::TrapIf { cond: g_end_gt_len });
                // Past the guards: 0 <= start <= end <= len < 2³². Narrow to U32.
                let start_u32 =
                    self.fresh_local(AirType::U32, AirValueKind::Copy, "__substr_start32");
                stmts.push(AirStmt::WrapI64 {
                    dst: start_u32,
                    src: start_i64,
                });
                let end_u32 = self.fresh_local(AirType::U32, AirValueKind::Copy, "__substr_end32");
                stmts.push(AirStmt::WrapI64 {
                    dst: end_u32,
                    src: end_i64,
                });
                // recv data_ptr (U32 @ offset 0).
                let recv_data_ptr =
                    self.fresh_local(AirType::U32, AirValueKind::Copy, "__substr_data_ptr");
                stmts.push(AirStmt::LoadField {
                    dst: recv_data_ptr,
                    base_ptr: header,
                    offset: STR_DATA_PTR_OFFSET,
                    ty: AirType::U32,
                });
                // UTF-8 boundary enforcement: trap if `start` or `end` lands
                // inside a multi-byte codepoint (now that data_ptr is loaded,
                // and BEFORE the alloc — a trap never leaks a header). This is
                // what makes "every `str` is valid UTF-8" an enforced invariant:
                // `substr` is the only producer that could slice off-boundary.
                self.emit_str_boundary_trap(recv_data_ptr, start_i64, len_i64, stmts);
                self.emit_str_boundary_trap(recv_data_ptr, end_i64, len_i64, stmts);
                // Allocate the fresh 8-byte view header (AFTER all six traps).
                stmts.push(AirStmt::BumpAlloc {
                    persistent: self.state_backed_alloc,
                    dst,
                    size_bytes: STR_HEADER_SIZE,
                    align: STR_HEADER_ALIGN,
                });
                // view.data_ptr = recv_data_ptr + start (U32).
                let view_ptr =
                    self.fresh_local(AirType::U32, AirValueKind::Copy, "__substr_view_ptr");
                stmts.push(AirStmt::Assign {
                    dst: view_ptr,
                    val: AirValue::Binary {
                        lhs: recv_data_ptr,
                        op: BinaryOp::Add,
                        rhs: start_u32,
                    },
                });
                stmts.push(AirStmt::StoreField {
                    base_ptr: dst,
                    offset: STR_DATA_PTR_OFFSET,
                    val: view_ptr,
                    ty: AirType::U32,
                });
                // view.len = end - start (U32).
                let view_len =
                    self.fresh_local(AirType::U32, AirValueKind::Copy, "__substr_view_len");
                stmts.push(AirStmt::Assign {
                    dst: view_len,
                    val: AirValue::Binary {
                        lhs: end_u32,
                        op: BinaryOp::Sub,
                        rhs: start_u32,
                    },
                });
                stmts.push(AirStmt::StoreField {
                    base_ptr: dst,
                    offset: STR_LEN_OFFSET,
                    val: view_len,
                    ty: AirType::U32,
                });
            }
            TypedIntrinsicKind::StrFromRaw {
                ptr: ptr_ty,
                len: len_ty,
            } => {
                // Owned-strings PR-1: wrap a raw (ptr, len) into a FRESH str
                // header. Mirrors the string-LITERAL lowering (BumpAlloc 8 bytes;
                // store data_ptr @0, len @4) — the only difference is `data_ptr`
                // is a RUNTIME value (args[0]) rather than a static-data offset.
                // Each arg is normalized to U32 through i64 (a 32-bit arg is
                // zero-extended first); the stdlib call sites pass `alloc`'s i64
                // result + an i64/u32 length, so this is a width-normalize.
                let ptr_i64 = if matches!(ptr_ty, AirType::I64 | AirType::U64) {
                    args[0]
                } else {
                    let w = self.fresh_local(AirType::I64, AirValueKind::Copy, "__strfr_ptr_i64");
                    stmts.push(AirStmt::ExtendU32 {
                        dst: w,
                        src: args[0],
                    });
                    w
                };
                let data_ptr_u32 =
                    self.fresh_local(AirType::U32, AirValueKind::Copy, "__strfr_data_ptr");
                stmts.push(AirStmt::WrapI64 {
                    dst: data_ptr_u32,
                    src: ptr_i64,
                });
                let len_i64 = if matches!(len_ty, AirType::I64 | AirType::U64) {
                    args[1]
                } else {
                    let w = self.fresh_local(AirType::I64, AirValueKind::Copy, "__strfr_len_i64");
                    stmts.push(AirStmt::ExtendU32 {
                        dst: w,
                        src: args[1],
                    });
                    w
                };
                let len_u32 = self.fresh_local(AirType::U32, AirValueKind::Copy, "__strfr_len");
                stmts.push(AirStmt::WrapI64 {
                    dst: len_u32,
                    src: len_i64,
                });
                // Allocate the fresh 8-byte header (AFTER the arg normalizes),
                // then store data_ptr @0 and len @4.
                stmts.push(AirStmt::BumpAlloc {
                    persistent: self.state_backed_alloc,
                    dst,
                    size_bytes: STR_HEADER_SIZE,
                    align: STR_HEADER_ALIGN,
                });
                stmts.push(AirStmt::StoreField {
                    base_ptr: dst,
                    offset: STR_DATA_PTR_OFFSET,
                    val: data_ptr_u32,
                    ty: AirType::U32,
                });
                stmts.push(AirStmt::StoreField {
                    base_ptr: dst,
                    offset: STR_LEN_OFFSET,
                    val: len_u32,
                    ty: AirType::U32,
                });
            }
            TypedIntrinsicKind::U256FromI64 { arg } => {
                // u256 PR-U0: allocate a FRESH 32-byte cell (4× i64 little-endian
                // limbs at offsets 0/8/16/24, align 8) and store limb0 = arg
                // (zero-extended), limbs 1-3 = 0. Fresh-cell discipline (E3): the
                // result is a new allocation, never an aliased mutation. This is
                // the single layout chokepoint for construction (E2).
                let limb0 = if matches!(arg, AirType::I64 | AirType::U64) {
                    args[0]
                } else {
                    let w = self.fresh_local(AirType::I64, AirValueKind::Copy, "__u256_limb0");
                    stmts.push(AirStmt::ExtendU32 {
                        dst: w,
                        src: args[0],
                    });
                    w
                };
                stmts.push(AirStmt::BumpAlloc {
                    persistent: self.state_backed_alloc,
                    dst,
                    size_bytes: 32,
                    align: 8,
                });
                stmts.push(AirStmt::StoreField {
                    base_ptr: dst,
                    offset: 0,
                    val: limb0,
                    ty: AirType::I64,
                });
                let zero = self.fresh_local(AirType::I64, AirValueKind::Copy, "__u256_zero");
                stmts.push(AirStmt::Assign {
                    dst: zero,
                    val: AirValue::IntLit(0),
                });
                stmts.push(AirStmt::StoreField {
                    base_ptr: dst,
                    offset: 8,
                    val: zero,
                    ty: AirType::I64,
                });
                stmts.push(AirStmt::StoreField {
                    base_ptr: dst,
                    offset: 16,
                    val: zero,
                    ty: AirType::I64,
                });
                stmts.push(AirStmt::StoreField {
                    base_ptr: dst,
                    offset: 24,
                    val: zero,
                    ty: AirType::I64,
                });
            }
            TypedIntrinsicKind::U256Make => {
                // Build a FRESH 32-byte cell from four u64 limbs (E2 canonical
                // little-endian layout: limb_k at offset 8k). The stdlib math's
                // result constructor — always a new allocation (E3).
                stmts.push(AirStmt::BumpAlloc {
                    persistent: self.state_backed_alloc,
                    dst,
                    size_bytes: 32,
                    align: 8,
                });
                for (i, &limb) in args.iter().take(4).enumerate() {
                    stmts.push(AirStmt::StoreField {
                        base_ptr: dst,
                        offset: (i as u32) * 8,
                        val: limb,
                        ty: AirType::U64,
                    });
                }
            }
            TypedIntrinsicKind::U256Limb { index } => {
                // Read limb `index` (0..=3) of a u256 as u64 (E2 layout).
                stmts.push(AirStmt::LoadField {
                    dst,
                    base_ptr: args[0],
                    offset: index * 8,
                    ty: AirType::U64,
                });
            }
            TypedIntrinsicKind::TrapIf => {
                // `if cond { unreachable }` — the checked-arithmetic revert (E1).
                stmts.push(AirStmt::TrapIf { cond: args[0] });
            }
            TypedIntrinsicKind::Trap => {
                // `trap()` — unconditional abort. Lowered as a constant-true
                // `TrapIf` (wasm `unreachable`), reusing the existing statement
                // so no new AIR variant / shadow-alphabet entry is needed. `dst`
                // is unused (surface type Unit).
                let always = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__trap");
                stmts.push(AirStmt::Assign {
                    dst: always,
                    val: AirValue::IntLit(1),
                });
                stmts.push(AirStmt::TrapIf { cond: always });
            }
            // Phase 2H §3.5: branch-free constant-time intrinsics.
            TypedIntrinsicKind::CtEq => {
                let lhs = *args.first().expect("ICE: ct_eq missing lhs");
                let rhs = *args.get(1).expect("ICE: ct_eq missing rhs");
                stmts.push(AirStmt::IntrinsicCtEq { dst, lhs, rhs });
            }
            TypedIntrinsicKind::CtSelect => {
                let cond = *args.first().expect("ICE: ct_select missing cond");
                let then_val = *args.get(1).expect("ICE: ct_select missing then");
                let else_val = *args.get(2).expect("ICE: ct_select missing else");
                stmts.push(AirStmt::IntrinsicCtSelect {
                    dst,
                    cond,
                    then_val,
                    else_val,
                });
            }
            TypedIntrinsicKind::CtLt => {
                let lhs = *args.first().expect("ICE: ct_lt missing lhs");
                let rhs = *args.get(1).expect("ICE: ct_lt missing rhs");
                stmts.push(AirStmt::IntrinsicCtLt { dst, lhs, rhs });
            }
        }
    }

    fn lower_send_expr(
        &mut self,
        send: &TypedSendExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let target = self.resolve_name(&send.target, env, stmts);
        let payload_args = send
            .args
            .iter()
            .map(|arg| self.lower_expr_to_var(arg, env, stmts))
            .collect::<Vec<_>>();
        let msg = self.lower_message_record(&payload_args, stmts);
        let (payload_buf, payload_len) = self.lower_message_payload(msg, &payload_args, stmts);
        stmts.push(AirStmt::MessageSend {
            target,
            msg,
            actor_type: actor_type_id(&send.actor),
            handler: handler_id(&send.actor, &send.handler),
            payload_buf,
            payload_len,
        });
    }

    fn lower_ask_expr(
        &mut self,
        dst: VarId,
        ask: &TypedAskExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let target = self.resolve_name(&ask.target, env, stmts);
        let payload_args = ask
            .args
            .iter()
            .map(|arg| self.lower_expr_to_var(arg, env, stmts))
            .collect::<Vec<_>>();
        let msg = self.lower_message_record(&payload_args, stmts);
        let (payload_buf, payload_len) = self.lower_message_payload(msg, &payload_args, stmts);
        let timeout = self.lower_expr_to_var(&ask.timeout, env, stmts);
        stmts.push(AirStmt::MessageAsk {
            dst,
            target,
            msg,
            actor_type: actor_type_id(&ask.actor),
            handler: handler_id(&ask.actor, &ask.handler),
            payload_buf,
            payload_len,
            timeout,
        });
    }

    fn lower_spawn_expr(
        &mut self,
        dst: VarId,
        spawn: &TypedSpawnExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let args = spawn
            .args
            .iter()
            .map(|arg| self.lower_expr_to_var(arg, env, stmts))
            .collect::<Vec<_>>();
        let fuel_cap = args.last().copied().unwrap_or_else(|| {
            let zero = self.fresh_local(AirType::Ptr, AirValueKind::Copy, "empty_fuel");
            stmts.push(AirStmt::Assign {
                dst: zero,
                val: AirValue::IntLit(0),
            });
            zero
        });
        let caps = if args.len() > 1 {
            args[..args.len() - 1].to_vec()
        } else {
            Vec::new()
        };
        let supervision = match spawn.supervision {
            Some(crate::type_check::TypedSupervisionStrategy::Restart { max_restarts }) => {
                AirSupervisionStrategy::Restart { max_restarts }
            }
            _ => AirSupervisionStrategy::Stop,
        };
        stmts.push(AirStmt::SpawnActor {
            dst,
            actor_type: actor_type_id(&spawn.actor),
            caps,
            fuel_cap,
            supervision,
        });
    }

    /// u256 PR-U2: materialize a 256-bit constant into a FRESH 32-byte cell — the
    /// single canonical little-endian layout (E2), limbs stored as i64-bit
    /// patterns (the u64 value's bits). Shared by the wide-literal and
    /// small-literal-in-u256-context lowerings. Always a new allocation (E3).
    fn materialize_u256_cell(&mut self, dst: VarId, limbs: [u64; 4], stmts: &mut StatementBuffer) {
        stmts.push(AirStmt::BumpAlloc {
            persistent: self.state_backed_alloc,
            dst,
            size_bytes: 32,
            align: 8,
        });
        for (i, &limb) in limbs.iter().enumerate() {
            let lv = self.fresh_local(AirType::I64, AirValueKind::Copy, "__u256_lit_limb");
            stmts.push(AirStmt::Assign {
                dst: lv,
                val: AirValue::IntLit(limb as i64),
            });
            stmts.push(AirStmt::StoreField {
                base_ptr: dst,
                offset: (i as u32) * 8,
                val: lv,
                ty: AirType::I64,
            });
        }
    }

    fn lower_binary_expr(
        &mut self,
        dst: VarId,
        expr: &TypedBinaryExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        // u256 PR-U1a: a binary op on two u256 values is checked stdlib multi-limb
        // math — rewrite to a Call (operands lowered once, as the call args).
        // Keyed on the static operand type (E4); `==`/`!=` route to u256_eq/_ne,
        // NEVER the default pointer-eq (two equal-valued distinct cells must
        // compare equal, E3). Well-typed programs only reach this with the ops
        // the type-checker admitted for u256 (add/sub/comparisons/eq); the rest
        // are rejected pre-AIR, so the `_` arm is an ICE guard.
        if matches!(&expr.lhs.ty, Type::U256) && matches!(&expr.rhs.ty, Type::U256) {
            use crate::typed_ast::TypedCallExpr;
            let (suffix, ret) = match expr.op {
                BinaryOp::Add => ("u256_add", Type::U256),
                BinaryOp::Sub => ("u256_sub", Type::U256),
                BinaryOp::Mul => ("u256_mul", Type::U256),
                BinaryOp::Div => ("u256_div", Type::U256),
                BinaryOp::Mod => ("u256_mod", Type::U256),
                BinaryOp::BitAnd => ("u256_and", Type::U256),
                BinaryOp::BitOr => ("u256_or", Type::U256),
                BinaryOp::Shl => ("u256_shl", Type::U256),
                BinaryOp::Shr => ("u256_shr", Type::U256),
                BinaryOp::Lt => ("u256_lt", Type::Bool),
                BinaryOp::LtEq => ("u256_le", Type::Bool),
                BinaryOp::Gt => ("u256_gt", Type::Bool),
                BinaryOp::GtEq => ("u256_ge", Type::Bool),
                BinaryOp::Eq => ("u256_eq", Type::Bool),
                BinaryOp::NotEq => ("u256_ne", Type::Bool),
                BinaryOp::LogicalAnd | BinaryOp::LogicalOr => {
                    unreachable!("logical operators require bool operands")
                } // All BinaryOp variants are covered above (every u256 operator is
                  // backed); a future new operator becomes a compile error here.
            };
            let callee = self
                .function_ids
                .keys()
                .find(|k| k.rsplit("::").next() == Some(suffix))
                .cloned()
                .unwrap_or_else(|| {
                    panic!("ICE: u256 op lowering requires {suffix} (u256.sigil) in scope")
                });
            let call = TypedExpr {
                ty: ret,
                kind: TypedExprKind::Call(TypedCallExpr {
                    callee,
                    args: vec![(*expr.lhs).clone(), (*expr.rhs).clone()],
                }),
                span: expr.lhs.span,
                refinement: None,
            };
            self.lower_expr_into(dst, &call, env, stmts);
            return;
        }
        let lhs = self.lower_expr_to_var(&expr.lhs, env, stmts);
        let rhs = self.lower_expr_to_var(&expr.rhs, env, stmts);
        // Str-Str `==`/`!=` compares BYTES (`AirStmt::StrBytesEq`, PR #699),
        // replacing PR S1's data-ptr comparison — which ignored `len`
        // entirely, so a `substr` view compared EQUAL to its parent while
        // byte-equal strings at distinct sites compared UNEQUAL.
        //
        // KEEP THIS PREDICATE IN STEP WITH the T033/CT018 gate in
        // `taint_check.rs` — taint runs before lowering and must reject a
        // `@SecretCT` operand for exactly the expressions that take this
        // path (the byte scan's early exit is a timing channel). Widening
        // one without the other silently un-guards the loop.
        let is_str_eq = matches!(&expr.lhs.ty, Type::Str)
            && matches!(&expr.rhs.ty, Type::Str)
            && matches!(expr.op, BinaryOp::Eq | BinaryOp::NotEq);
        if is_str_eq {
            let bool_dst = if matches!(expr.op, BinaryOp::Eq) {
                dst
            } else {
                self.fresh_local(AirType::Bool, AirValueKind::Copy, "__str_eq_tmp")
            };
            self.emit_str_bytes_eq(lhs, rhs, bool_dst, stmts);
            // NotEq: invert via xor-with-true. Cheapest BoolLit-based negation.
            if matches!(expr.op, BinaryOp::NotEq) {
                let true_var =
                    self.fresh_local(AirType::Bool, AirValueKind::Copy, "__str_neq_true");
                stmts.push(AirStmt::Assign {
                    dst: true_var,
                    val: AirValue::BoolLit(true),
                });
                stmts.push(AirStmt::Assign {
                    dst,
                    val: AirValue::Binary {
                        lhs: bool_dst,
                        op: BinaryOp::NotEq,
                        rhs: true_var,
                    },
                });
            }
            return;
        }
        stmts.push(AirStmt::Assign {
            dst,
            val: AirValue::Binary {
                lhs,
                op: expr.op,
                rhs,
            },
        });
    }

    fn lower_record_construct(
        &mut self,
        dst: VarId,
        record: &TypedRecordConstructExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let mut fields = record
            .fields
            .iter()
            .map(|(name, expr)| {
                let var = self.lower_expr_to_var(expr, env, stmts);
                (name.clone(), var)
            })
            .collect::<Vec<_>>();
        // Field-order soundness: `memory::flatten_record` assigns offsets by
        // accumulating widths in THIS vec's order, while field reads use the
        // registry's decl-order offsets (`field_base_and_offset`). A construct
        // written out of decl order (`R { y: b, x: a }`) must therefore be
        // normalized to decl order — the value expressions above already
        // evaluated in WRITTEN order, so only the (name, var) pairs move.
        if let Some(decl) = self.field_registry.get(&record.type_name) {
            fields.sort_by_key(|(name, _)| {
                decl.iter()
                    .position(|(dn, _, _)| dn == name)
                    .unwrap_or_else(|| {
                        panic!(
                            "ICE: field `{name}` missing from registry for `{}`",
                            record.type_name
                        )
                    })
            });
        } else {
            // Only synthetic desugars lack a registry entry (tuple constructs,
            // `$tuple2__i64$i64`): they are positional, so vec order IS layout
            // order on both `flatten_record` and the on-demand read path (ET-5).
            // A user record always has an entry (`build_field_registry` covers
            // every `program.records` decl) — anything else here is an ICE.
            assert!(
                record.type_name.starts_with('$'),
                "ICE: non-synthetic record `{}` missing from the field registry",
                record.type_name
            );
        }
        stmts.push(AirStmt::Assign {
            dst,
            val: AirValue::RecordConstruct { fields },
        });
    }

    fn lower_field_access(
        &mut self,
        dst: VarId,
        access: &TypedFieldAccessExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let (base, offset, field_ty) = self.field_base_and_offset(access, env, stmts);
        stmts.push(AirStmt::LoadField {
            dst,
            base_ptr: base,
            offset,
            ty: field_ty,
        });
    }

    /// Shared base-pointer + field-offset resolution for record field
    /// access — used by both the `r.f` READ (`lower_field_access`) and the
    /// `r.f = v` WRITE (`lower_assign`). Lowers the object to its container
    /// pointer exactly once and resolves the field's offset/type from the
    /// registry (mangling generic receivers), so a write lands at the
    /// byte-identical slot the read would. Panics (ICE) on a non-record
    /// receiver or an unregistered field, exactly as the read path always
    /// has (AG2: only concrete monomorphized bodies are lowered).
    fn field_base_and_offset(
        &mut self,
        access: &TypedFieldAccessExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) -> (VarId, u32, AirType) {
        let base = self.lower_expr_to_var(&access.object, env, stmts);

        // Auto-deref: look through references for the underlying type
        let obj_ty = match &access.object.ty {
            Type::Ref(inner, _) => inner.as_ref(),
            other => other,
        };
        // Tuple element read (`$tup.0`): compute the offset ON-DEMAND, bypassing
        // the field registry entirely. ET-5: the SAME `lower_type(elem).width()`
        // layout `flatten_record` lays out on the construct side, so read and
        // write agree by construction. `access.field` is a decimal index that
        // type-check already bounds-checked in range.
        if let Type::Tuple(elems) = obj_ty {
            let idx: usize = access
                .field
                .parse()
                .expect("ICE: non-numeric tuple field index reached AIR");
            let mut offset = 0u32;
            for e in &elems[..idx] {
                offset += lower_type(e).width();
            }
            let field_ty = lower_type(&elems[idx]);
            return (base, offset, field_ty);
        }
        // Look up field offset from registry — mangle if generic
        let type_key = match obj_ty {
            Type::Named(name, args) if args.is_empty() => name.clone(),
            ty @ Type::Named(_, _) => mangle_type(ty),
            _ => panic!("ICE: FieldAccess on non-Named type {:?}", obj_ty),
        };
        let fields = self
            .field_registry
            .get(&type_key)
            .unwrap_or_else(|| panic!("ICE: no field registry for type `{type_key}`"));
        let (_, offset, field_ty) = fields
            .iter()
            .find(|(name, _, _)| name == &access.field)
            .unwrap_or_else(|| {
                panic!(
                    "ICE: no field `{}` in registry for type `{type_key}`",
                    access.field
                )
            });

        (base, *offset, *field_ty)
    }

    fn lower_enum_construct(
        &mut self,
        dst: VarId,
        ctor: &TypedEnumConstructExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let info = self
            .enum_registry
            .get(&ctor.enum_name)
            .unwrap_or_else(|| panic!("ICE: no enum registry for `{}`", ctor.enum_name));

        // Allocate tagged union: tag(4) + max_payload
        stmts.push(AirStmt::BumpAlloc {
            persistent: self.state_backed_alloc,
            dst,
            size_bytes: info.total_size,
            align: 4,
        });

        // Store tag at offset 0
        let tag_var = self.fresh_local(AirType::I32, AirValueKind::Copy, "__enum_tag");
        stmts.push(AirStmt::Assign {
            dst: tag_var,
            val: AirValue::IntLit(ctor.variant_index as i64),
        });
        stmts.push(AirStmt::StoreField {
            base_ptr: dst,
            offset: 0,
            val: tag_var,
            ty: AirType::I32,
        });

        // Store payload fields at offset 4+
        let mut payload_offset = 4u32;
        for field_expr in &ctor.fields {
            let val = self.lower_expr_to_var(field_expr, env, stmts);
            let field_ty = lower_type(&field_expr.ty);
            stmts.push(AirStmt::StoreField {
                base_ptr: dst,
                offset: payload_offset,
                val,
                ty: field_ty,
            });
            payload_offset += field_ty.width();
        }
    }

    fn lower_cap_restrict(
        &mut self,
        dst: VarId,
        restrict: &TypedCapRestrictExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let src = self.resolve_name(&restrict.cap, env, stmts);
        stmts.push(AirStmt::CapRestrict {
            dst,
            src,
            restriction_mask: restrict.restriction_mask,
        });
    }

    fn lower_cap_split(
        &mut self,
        dst: VarId,
        split: &TypedCapSplitExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let src = self.resolve_name(&split.cap, env, stmts);
        let amount = self.lower_expr_to_var(&split.amount, env, stmts);
        stmts.push(AirStmt::CapSplit { dst, src, amount });
    }

    fn lower_cap_draw(
        &mut self,
        dst: VarId,
        draw: &TypedCapDrawExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let src = self.resolve_name(&draw.cap, env, stmts);
        let amount = self.lower_expr_to_var(&draw.amount, env, stmts);
        stmts.push(AirStmt::CapDraw { dst, src, amount });
    }

    /// Capabilities-as-values: lower `mint <CapType>[(deadlines)] for <target>`
    /// to `AirStmt::CapMint`. `dst`'s value-kind is already `Cap(cap_name)`
    /// (the let binding / `lower_expr_to_var` derive it from the `Type::Cap`
    /// via `classify_value_kind` — so both `let c = mint …` and inline
    /// `send(r, mint …)` are linear and verifier-checked). The target is
    /// lowered for its side effects + provenance var; its value is erased at
    /// the wasm boundary.
    fn lower_cap_mint(
        &mut self,
        dst: VarId,
        mint: &TypedMintExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let target = self.lower_expr_to_var(&mint.target, env, stmts);
        stmts.push(AirStmt::CapMint {
            dst,
            cap_name: mint.cap_name.clone(),
            params: mint.params.clone(),
            target,
        });
    }

    fn lower_grant_expr(
        &mut self,
        dst: VarId,
        grant: &TypedGrantExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        // 1. Lower cap expression
        let cap_var = self.lower_expr_to_var(&grant.cap, env, stmts);

        // 2. Lower closure expression (lambda-lifted via existing closure engine)
        let closure_var = self.lower_expr_to_var(&grant.body, env, stmts);

        // 3. Emit grant begin
        stmts.push(AirStmt::GrantBegin {
            grant_id: grant.grant_id,
            cap_var,
        });

        // 4. Load table index from closure struct and call via CallIndirect
        let table_idx = self.fresh_local(AirType::I32, AirValueKind::Copy, "__grant_fn_idx");
        stmts.push(AirStmt::LoadField {
            dst: table_idx,
            base_ptr: closure_var,
            offset: 0,
            ty: AirType::I32,
        });

        // Determine the closure signature from the grant body type
        let (air_params, air_ret) = match &grant.body.ty {
            Type::Fn(params, ret, _, _) => {
                let mut ps = vec![AirType::Ptr]; // env_ptr
                ps.extend(params.iter().map(lower_type));
                (ps, lower_type(ret))
            }
            _ => (vec![AirType::Ptr], AirType::Unit),
        };

        stmts.push(AirStmt::CallIndirect {
            dst: self.call_dst(dst),
            signature: (air_params, air_ret),
            table_index: table_idx,
            args: vec![closure_var, cap_var], // env_ptr + cap arg
        });

        // 5. Emit grant end
        stmts.push(AirStmt::GrantEnd {
            grant_id: grant.grant_id,
        });
    }

    fn lower_handle_expr(
        &mut self,
        dst: VarId,
        handle: &TypedHandleExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        // Handle blocks are transparent at AIR level — effect containment
        // is enforced by the effect checker. We lower the body inline into
        // the calling block; the last expression statement's result → dst.
        // Control-flow statements in handle bodies are rejected at type-
        // check (T068), so the dispatcher below can `unreachable!()`.
        self.lower_scoped_body_inline(dst, &handle.body.statements, env, stmts);
    }

    fn lower_closure_construct(
        &mut self,
        dst: VarId,
        ctor: &TypedClosureConstructExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let func_id = self
            .function_ids
            .get(&ctor.synthesized_name)
            .copied()
            .unwrap_or_else(|| panic!("ICE: missing closure function `{}`", ctor.synthesized_name));

        // Calculate layout: 4 bytes for table_index + capture sizes
        let mut total_size = 4u32;
        for cap in &ctor.captures {
            total_size += lower_type(&cap.ty).width();
        }

        stmts.push(AirStmt::BumpAlloc {
            persistent: self.state_backed_alloc,
            dst,
            size_bytes: total_size,
            align: 4,
        });

        // Store table index (func_id.0) at CLOSURE_TABLE_IDX_OFFSET (N10-HOF)
        let tag_var = self.fresh_local(AirType::I32, AirValueKind::Copy, "__closure_id");
        stmts.push(AirStmt::Assign {
            dst: tag_var,
            val: AirValue::IntLit(func_id.0 as i64),
        });
        stmts.push(AirStmt::StoreField {
            base_ptr: dst,
            offset: CLOSURE_TABLE_IDX_OFFSET,
            val: tag_var,
            ty: AirType::I32,
        });

        // Store captures at offset 4+ (after the table_idx i32 field)
        let mut offset = 4u32;
        for cap in &ctor.captures {
            let val = *env
                .get(&cap.name)
                .unwrap_or_else(|| panic!("ICE: unresolved capture `{}`", cap.name));
            let cap_ty = lower_type(&cap.ty);
            stmts.push(AirStmt::StoreField {
                base_ptr: dst,
                offset,
                val,
                ty: cap_ty,
            });
            offset += cap_ty.width();
        }
    }

    /// PR AF / N14-AF: emit the `LoadField` reading a slice's `len`
    /// field from its fat-pointer header. SOLE site (alongside
    /// `slice_data_ptr_var`) that reads `SLICE_LEN_OFFSET`; helper-
    /// only access enforced by the matching grep-lint. `slice_var`
    /// is a `Type::Slice`-typed local (an `AirType::Ptr` pointing at
    /// the 8-byte header allocation).
    pub(crate) fn slice_len_var(&mut self, slice_var: VarId, stmts: &mut StatementBuffer) -> VarId {
        let len_var = self.fresh_local(AirType::U32, AirValueKind::Copy, "__slice_len");
        stmts.push(AirStmt::LoadField {
            dst: len_var,
            base_ptr: slice_var,
            offset: SLICE_LEN_OFFSET,
            ty: AirType::U32,
        });
        len_var
    }

    /// PR AF / N14-AF: emit the `LoadField` reading a slice's
    /// `data_ptr` field from its fat-pointer header. SOLE site
    /// (alongside `slice_len_var`) that reads `SLICE_DATA_PTR_OFFSET`.
    /// The returned local is an `AirType::Ptr` pointing at the first
    /// element of the underlying array region; element-load via
    /// `LoadDynamic { base_ptr: <returned>, index, elem_size }` does
    /// NOT skip a header (the data_ptr already points past it).
    pub(crate) fn slice_data_ptr_var(
        &mut self,
        slice_var: VarId,
        stmts: &mut StatementBuffer,
    ) -> VarId {
        let data_ptr_var = self.fresh_local(AirType::Ptr, AirValueKind::Copy, "__slice_data_ptr");
        stmts.push(AirStmt::LoadField {
            dst: data_ptr_var,
            base_ptr: slice_var,
            offset: SLICE_DATA_PTR_OFFSET,
            ty: AirType::Ptr,
        });
        data_ptr_var
    }

    fn lower_array_lit(
        &mut self,
        dst: VarId,
        array_lit: &TypedArrayLitExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let elem_air_type = lower_type(&array_lit.elem_type);
        let elem_size = elem_air_type.width();
        let total_size = 4 + (array_lit.elements.len() as u32) * elem_size;

        // Allocate length-prefixed array
        stmts.push(AirStmt::BumpAlloc {
            persistent: self.state_backed_alloc,
            dst,
            size_bytes: total_size,
            align: 8,
        });

        // Store length prefix at offset 0
        let len_var = self.fresh_local(AirType::U32, AirValueKind::Copy, "__arr_len");
        stmts.push(AirStmt::Assign {
            dst: len_var,
            val: AirValue::IntLit(array_lit.elements.len() as i64),
        });
        stmts.push(AirStmt::StoreField {
            base_ptr: dst,
            offset: 0,
            val: len_var,
            ty: AirType::U32,
        });

        // Store each element at static offsets (4 + i * elem_size)
        for (i, elem) in array_lit.elements.iter().enumerate() {
            let val = self.lower_expr_to_var(elem, env, stmts);
            stmts.push(AirStmt::StoreField {
                base_ptr: dst,
                offset: 4 + (i as u32) * elem_size,
                val,
                ty: elem_air_type,
            });
        }
    }

    fn lower_index_expr(
        &mut self,
        dst: VarId,
        index_expr: &TypedIndexExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let (load_base, index, elem_size, elem_air_type) =
            self.index_base_and_bounds(index_expr, env, stmts);

        // Load element at dynamic offset; `offset: 4` skips the array/slice
        // length header.
        stmts.push(AirStmt::LoadDynamic {
            dst,
            base_ptr: load_base,
            index,
            elem_size,
            ty: elem_air_type,
            offset: 4,
        });
    }

    /// Shared address + bounds computation for dynamic element access —
    /// used by both the `arr[i]` READ (`lower_index_expr`) and the
    /// `arr[i] = v` WRITE (`lower_assign`). Evaluates the receiver and the
    /// index exactly ONCE and emits the SAME length-`TrapIf` bounds check
    /// for both callers (NC1/CM1 — the checked length and the accessed
    /// buffer come from one base evaluation, so there is no TOCTOU window).
    /// Returns the load/store base pointer, the (unwrapped) index var, the
    /// element size in bytes, and the element AIR type.
    ///
    /// PR P16 commit #2: dispatch on receiver type. The bounds-check
    /// length-source and the dynamic base_ptr differ per receiver:
    ///
    /// - Array: length is at the array's header (offset 0); the base is
    ///   the array pointer — the wasm layer bakes a `+4` header skip into
    ///   the mem_arg so `index=0` lands at the first element.
    ///
    /// - Slice (N20-P16): length is at `SLICE_LEN_OFFSET` (offset 4) of
    ///   the fat-pointer header; data_ptr is at `SLICE_DATA_PTR_OFFSET`
    ///   (offset 0), and the base is `data_ptr`. The `+4` header skip
    ///   still applies because the slice's data_ptr was computed (in PR AF
    ///   `lower_slice_expr`) as `underlying_arr_ptr + start*elem_size` —
    ///   not advanced past the underlying-array header — so the baked `+4`
    ///   correctly lands on the (start+index)th underlying element.
    fn index_base_and_bounds(
        &mut self,
        index_expr: &TypedIndexExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) -> (VarId, VarId, u32, AirType) {
        let receiver = self.lower_expr_to_var(&index_expr.array, env, stmts);
        let index = self.lower_expr_to_var(&index_expr.index, env, stmts);
        let elem_air_type = lower_type(&index_expr.elem_type);
        let elem_size = elem_air_type.width();

        // Refinement-typed array bounds (v1): a constant index proven
        // in-bounds at type-check (`bounds_proven`, SC-2) elides the runtime
        // bounds check — the length `LoadField`, the index wrap, the `oob`
        // compare, and the `TrapIf` are ALL skipped. Only ever set for an
        // Array receiver (a Slice has no static `N`), so the load base is the
        // array pointer; the element load keeps its `+4` header skip, so the
        // heap layout is unchanged (SC-6 — only the CHECK is removed, never
        // the representation).
        if index_expr.bounds_proven {
            return (receiver, index, elem_size, elem_air_type);
        }

        let (bounds_len_source, load_base) = match &index_expr.array.ty {
            Type::Slice(_) => {
                let len = self.slice_len_var(receiver, stmts);
                let data_ptr = self.slice_data_ptr_var(receiver, stmts);
                (len, data_ptr)
            }
            _ => {
                // Array (or Type::Error fallthrough — the type-check
                // already fired a diagnostic; produce something
                // well-defined to avoid panics during lowering).
                let arr_len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__bounds_len");
                stmts.push(AirStmt::LoadField {
                    dst: arr_len,
                    base_ptr: receiver,
                    offset: 0,
                    ty: AirType::U32,
                });
                (arr_len, receiver)
            }
        };

        // If index is 64-bit, wrap to U32 for the bounds comparison.
        // (Inherits PR AF's bounds-check shape; identical wasm output
        // for Array fixtures pre-PR-P16.)
        let index_air_type = lower_type(&index_expr.index.ty);
        let bounds_index = if matches!(index_air_type, AirType::I64 | AirType::U64) {
            let wrapped = self.fresh_local(AirType::U32, AirValueKind::Copy, "__idx32");
            stmts.push(AirStmt::WrapI64 {
                dst: wrapped,
                src: index,
            });
            wrapped
        } else {
            index
        };
        let oob_cond = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__oob");
        stmts.push(AirStmt::Assign {
            dst: oob_cond,
            val: AirValue::Binary {
                lhs: bounds_index,
                op: BinaryOp::GtEq,
                rhs: bounds_len_source,
            },
        });
        stmts.push(AirStmt::TrapIf { cond: oob_cond });

        (load_base, index, elem_size, elem_air_type)
    }

    /// Lower a place-expression assignment `place op= value` with
    /// single-evaluation semantics (NC2/CM2): each place sub-expression
    /// (base pointer, subscript) is lowered to a temporary exactly once,
    /// and a compound `op=` is a load-op-store *through those same temps* —
    /// never a re-evaluation of the place.
    fn lower_assign(
        &mut self,
        stmt: &TypedAssignStmt,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        match &stmt.place.kind {
            TypedExprKind::Local(name) => {
                let dst = *env
                    .get(name)
                    .expect("ICE: unresolved variable in assignment during AIR lowering");
                // A local compound (`x += e`) was desugared to `x = x op e`
                // at parse time, so `op` is always None for a local here —
                // lower the value straight into the existing slot, byte-
                // identical to the pre-place-assignment lowering (NC5/CM5).
                self.lower_expr_into(dst, &stmt.value, env, stmts);
            }
            // Actor-state assignment. Lower the value, then `StoreField` it off
            // the state pointer at the field's offset so it persists in the actor's
            // arena for later handler reads. `op` is
            // always None (a state place carries no compound-assign desugaring).
            TypedExprKind::StateField(name) => {
                let val = self.lower_expr_to_var(&stmt.value, env, stmts);
                // PPS-1: a handler's wholesale aggregate write promotes into the persistent
                // heap first; scalars and `init` writes pass through untouched.
                let val = self.maybe_promote_aggregate(&stmt.value.ty, val, stmts);
                self.lower_state_write(name, val, stmts);
            }
            TypedExprKind::FieldAccess(access) => {
                let (base, offset, field_ty) = self.field_base_and_offset(access, env, stmts);
                let val = match stmt.op {
                    None => self.lower_expr_to_var(&stmt.value, env, stmts),
                    Some(op) => {
                        // Compound `r.f op= v`: load the current field
                        // through the once-computed base/offset, combine,
                        // store back — no place sub-expression re-evaluated.
                        let cur = self.fresh_local(field_ty, AirValueKind::Copy, "__compound_cur");
                        stmts.push(AirStmt::LoadField {
                            dst: cur,
                            base_ptr: base,
                            offset,
                            ty: field_ty,
                        });
                        let rhs = self.lower_expr_to_var(&stmt.value, env, stmts);
                        let out = self.fresh_local(field_ty, AirValueKind::Copy, "__compound_val");
                        stmts.push(AirStmt::Assign {
                            dst: out,
                            val: AirValue::Binary { lhs: cur, op, rhs },
                        });
                        out
                    }
                };
                stmts.push(AirStmt::StoreField {
                    base_ptr: base,
                    offset,
                    val,
                    ty: field_ty,
                });
            }
            TypedExprKind::Index(index_expr) => {
                let (load_base, index, elem_size, elem_ty) =
                    self.index_base_and_bounds(index_expr, env, stmts);
                let val = match stmt.op {
                    None => self.lower_expr_to_var(&stmt.value, env, stmts),
                    Some(op) => {
                        // Compound `arr[i] op= v`: load through the same
                        // bounds-checked base/index, combine, store back.
                        let cur = self.fresh_local(elem_ty, AirValueKind::Copy, "__compound_cur");
                        stmts.push(AirStmt::LoadDynamic {
                            dst: cur,
                            base_ptr: load_base,
                            index,
                            elem_size,
                            ty: elem_ty,
                            offset: 4,
                        });
                        let rhs = self.lower_expr_to_var(&stmt.value, env, stmts);
                        let out = self.fresh_local(elem_ty, AirValueKind::Copy, "__compound_val");
                        stmts.push(AirStmt::Assign {
                            dst: out,
                            val: AirValue::Binary { lhs: cur, op, rhs },
                        });
                        out
                    }
                };
                stmts.push(AirStmt::StoreDynamic {
                    base_ptr: load_base,
                    index,
                    elem_size,
                    val,
                    ty: elem_ty,
                    offset: 4,
                });
            }
            _ => panic!("ICE: non-place assignment target survived type-check"),
        }
    }

    /// PR AF / Phase 1.3: lower `&arr[lo..hi]` (or its open-range
    /// variants) into a fat-pointer slice header.
    ///
    /// Sequence per N15-AF (source-position pinned):
    /// 1. Materialize `start` (default 0) and `end` (default
    ///    receiver.len()).
    /// 2. Compute `receiver_len`: Array → IntLit(size); Slice →
    ///    `slice_len_var` (N14-AF).
    /// 3. `TrapIf` #1: `start > end`.
    /// 4. `TrapIf` #2: `end > receiver_len`.
    /// 5. `BumpAlloc { size_bytes: 8, align: 4 }` for the slice
    ///    header (N19-AF).
    /// 6. Compute `data_ptr = receiver_base + start * elem_size`,
    ///    where `receiver_base` is the array's BumpAlloc start for
    ///    Array sources or the slice's `data_ptr` (read via
    ///    `slice_data_ptr_var`) for Slice sources. NO extra `+4`
    ///    offset — LoadDynamic's wasm lowering already bakes the
    ///    +4 header skip into its mem_arg, and the `&arr` borrow
    ///    in commit #2 set the precedent (data_ptr = src).
    /// 7. Compute `slice_len = end - start`.
    /// 8. `StoreField` data_ptr at SLICE_DATA_PTR_OFFSET and
    ///    slice_len at SLICE_LEN_OFFSET.
    fn lower_slice_expr(
        &mut self,
        dst: VarId,
        slice_expr: &TypedExpr,
        slice: &TypedSliceExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let elem_air_type = lower_type(&slice.elem_type);
        let elem_size = elem_air_type.width();

        // Receiver's runtime value: for Array, the BumpAlloc start
        // (header at offset 0); for Slice, the fat-pointer struct.
        let receiver_var = self.lower_expr_to_var(&slice.array, env, stmts);

        // Materialize start. Default to 0 if omitted.
        let start = if let Some(start_expr) = &slice.start {
            let raw = self.lower_expr_to_var(start_expr, env, stmts);
            // Coerce 64-bit indices to U32 for the bounds-check
            // comparison. Same pattern as `lower_index_expr`.
            if matches!(lower_type(&start_expr.ty), AirType::I64 | AirType::U64) {
                let wrapped = self.fresh_local(AirType::U32, AirValueKind::Copy, "__slice_start32");
                stmts.push(AirStmt::WrapI64 {
                    dst: wrapped,
                    src: raw,
                });
                wrapped
            } else {
                raw
            }
        } else {
            let z = self.fresh_local(AirType::U32, AirValueKind::Copy, "__slice_start_default");
            stmts.push(AirStmt::Assign {
                dst: z,
                val: AirValue::IntLit(0),
            });
            z
        };

        // Compute receiver_len for both end-default and bounds.
        let receiver_len = match &slice.array.ty {
            Type::Array { size, .. } => {
                let lv = self.fresh_local(AirType::U32, AirValueKind::Copy, "__slice_recv_len");
                stmts.push(AirStmt::Assign {
                    dst: lv,
                    val: AirValue::IntLit(*size as i64),
                });
                lv
            }
            Type::Slice(_) => self.slice_len_var(receiver_var, stmts),
            // Type::Error path: produce a zero len so downstream
            // arithmetic is well-defined; the type-check error
            // already fired.
            _ => {
                let lv = self.fresh_local(AirType::U32, AirValueKind::Copy, "__slice_recv_len_err");
                stmts.push(AirStmt::Assign {
                    dst: lv,
                    val: AirValue::IntLit(0),
                });
                lv
            }
        };

        // Materialize end. Default to receiver_len if omitted.
        let end = if let Some(end_expr) = &slice.end {
            let raw = self.lower_expr_to_var(end_expr, env, stmts);
            if matches!(lower_type(&end_expr.ty), AirType::I64 | AirType::U64) {
                let wrapped = self.fresh_local(AirType::U32, AirValueKind::Copy, "__slice_end32");
                stmts.push(AirStmt::WrapI64 {
                    dst: wrapped,
                    src: raw,
                });
                wrapped
            } else {
                raw
            }
        } else {
            receiver_len
        };

        // N15-AF TrapIf #1: start > end.
        let trap_se = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__slice_trap_se");
        stmts.push(AirStmt::Assign {
            dst: trap_se,
            val: AirValue::Binary {
                lhs: start,
                op: BinaryOp::Gt,
                rhs: end,
            },
        });
        stmts.push(AirStmt::TrapIf { cond: trap_se });

        // N15-AF TrapIf #2: end > receiver_len.
        let trap_el = self.fresh_local(AirType::Bool, AirValueKind::Copy, "__slice_trap_el");
        stmts.push(AirStmt::Assign {
            dst: trap_el,
            val: AirValue::Binary {
                lhs: end,
                op: BinaryOp::Gt,
                rhs: receiver_len,
            },
        });
        stmts.push(AirStmt::TrapIf { cond: trap_el });

        // N19-AF BumpAlloc — 8 bytes, 4-byte aligned. Per N15-AF
        // ordering, this runs AFTER both TrapIfs.
        stmts.push(AirStmt::BumpAlloc {
            persistent: self.state_backed_alloc,
            dst,
            size_bytes: SLICE_HEADER_SIZE,
            align: SLICE_HEADER_ALIGN,
        });

        // Receiver base for data_ptr arithmetic. Array → the
        // BumpAlloc start (data_ptr semantic at offset 0 per the
        // SLICE_DATA_PTR_OFFSET doc-comment). Slice → the source's
        // data_ptr (read via the canonical helper).
        let receiver_base = match &slice.array.ty {
            Type::Slice(_) => self.slice_data_ptr_var(receiver_var, stmts),
            _ => receiver_var,
        };

        // data_ptr = receiver_base + start * elem_size.
        // First compute `start * elem_size`, then add to base.
        let elem_size_var = self.fresh_local(AirType::U32, AirValueKind::Copy, "__elem_size");
        stmts.push(AirStmt::Assign {
            dst: elem_size_var,
            val: AirValue::IntLit(elem_size as i64),
        });
        let byte_offset = self.fresh_local(AirType::U32, AirValueKind::Copy, "__slice_byte_offset");
        stmts.push(AirStmt::Assign {
            dst: byte_offset,
            val: AirValue::Binary {
                lhs: start,
                op: BinaryOp::Mul,
                rhs: elem_size_var,
            },
        });
        let data_ptr = self.fresh_local(AirType::Ptr, AirValueKind::Copy, "__slice_data_ptr_init");
        stmts.push(AirStmt::Assign {
            dst: data_ptr,
            val: AirValue::Binary {
                lhs: receiver_base,
                op: BinaryOp::Add,
                rhs: byte_offset,
            },
        });
        stmts.push(AirStmt::StoreField {
            base_ptr: dst,
            offset: SLICE_DATA_PTR_OFFSET,
            val: data_ptr,
            ty: AirType::Ptr,
        });

        // slice_len = end - start.
        let slice_len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__slice_len_init");
        stmts.push(AirStmt::Assign {
            dst: slice_len,
            val: AirValue::Binary {
                lhs: end,
                op: BinaryOp::Sub,
                rhs: start,
            },
        });
        stmts.push(AirStmt::StoreField {
            base_ptr: dst,
            offset: SLICE_LEN_OFFSET,
            val: slice_len,
            ty: AirType::U32,
        });

        // `slice_expr` is unused except to anchor the AIR call to
        // the typed_ast node; suppress the warning via discard.
        let _ = slice_expr;
    }

    fn lower_result_ctor(
        &mut self,
        dst: VarId,
        result: &TypedResultCtorExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let value = self.lower_expr_to_var(&result.value, env, stmts);
        let tag = self.fresh_local(AirType::Bool, AirValueKind::Copy, "result_tag");
        stmts.push(AirStmt::Assign {
            dst: tag,
            val: AirValue::BoolLit(result.is_ok),
        });
        stmts.push(AirStmt::Assign {
            dst,
            val: AirValue::RecordConstruct {
                fields: vec![("is_ok".to_owned(), tag), ("value".to_owned(), value)],
            },
        });
    }

    fn lower_try_expr(
        &mut self,
        dst: VarId,
        try_expr: &TypedTryExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let src = self.lower_expr_to_var(&try_expr.value, env, stmts);
        // PR OptTry / N11-OptTry: dispatch on the carrier type via
        // structural helpers. Pre-check: `check_try_expr` (type-check
        // layer) admits ONLY Result-Result and Option-Option carrier
        // shapes (plus their error arms); cross-carrier fires T241. So
        // at AIR lowering time, `try_expr.value.ty` is guaranteed to
        // be `Type::Named("Result", _)` OR `Type::Named("Option", _)`.
        // We match structurally; the fallback (`else`) routes to
        // ResultTry to preserve pre-PR-OptTry behavior on any future
        // edge case where check_try_expr fails to gate.
        if is_option_carrier(&try_expr.value.ty) {
            stmts.push(AirStmt::OptionTry { dst, src });
        } else {
            stmts.push(AirStmt::ResultTry { dst, src });
        }
    }

    fn lower_extern_call(
        &mut self,
        dst: VarId,
        extern_call: &TypedExternCallExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let args = extern_call
            .args
            .iter()
            .map(|a| self.lower_expr_to_var(a, env, stmts))
            .collect::<Vec<_>>();
        stmts.push(AirStmt::ExternCall {
            // A unit-returning extern has an EMPTY wasm import result list; passing
            // `Some(unit-dst)` would declare a phantom `(result i32)` import AND
            // `local.set` a unit local that has no wasm slot. `call_dst` → `None` for a
            // unit result (the same fix as the Call/CallIndirect sites).
            dst: self.call_dst(dst),
            extern_name: extern_call.extern_name.clone(),
            args,
        });
    }

    fn lower_region_expr(
        &mut self,
        dst: VarId,
        region: &TypedRegionExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let limit_var = self.lower_expr_to_var(&region.limit, env, stmts);
        // DEF-2a: the BUMP_PTR save slot. Allocated now (inert in PR-0; PR-5's wasm
        // save/restore uses it); a fresh local per region → LIFO unwind for nesting.
        let save_var = self.fresh_local(
            AirType::U32,
            AirValueKind::Copy,
            format!("region_save_{}", region.name),
        );
        stmts.push(AirStmt::RegionBegin {
            name: region.name.clone(),
            limit_var,
            save_var,
        });
        // Lower body inline — last expr goes to dst. Control-flow statements
        // are rejected at type-check (T068).
        self.lower_scoped_body_inline(dst, &region.body.statements, env, stmts);
        stmts.push(AirStmt::RegionEnd {
            name: region.name.clone(),
            limit_var,
            save_var,
        });
    }

    /// Lower the inline body of a `handle` or `region` block into the calling
    /// AirBlock's `stmts`. The last statement (which must be `Expr`) writes
    /// to `dst`; preceding statements may be `Let`, `Assign`, or `Expr` (for
    /// side effects). Control-flow forms are unreachable here because the
    /// type-checker emits T068 for them — if this `unreachable!()` ever
    /// fires, that rejection is incomplete and needs extending. This is the
    /// AIR-side closure for the silently-dropped-statement gap that left
    /// inner cap operations invisible to the proof and ownership layers.
    fn lower_scoped_body_inline(
        &mut self,
        dst: VarId,
        statements: &[TypedStmt],
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        let last_idx = statements.len().saturating_sub(1);
        let mut local_env = env.clone();
        for (i, typed_stmt) in statements.iter().enumerate() {
            let is_last = i == last_idx;
            stmts.with_span(
                statement_source_span(typed_stmt),
                |stmts| match typed_stmt {
                    TypedStmt::Let(stmt) => {
                        let bind = self.fresh_local(
                            lower_type(&stmt.ty),
                            classify_value_kind(&stmt.ty),
                            stmt.name.clone(),
                        );
                        self.lower_expr_into(bind, &stmt.value, &local_env, stmts);
                        local_env.insert(stmt.name.clone(), bind);
                    }
                    TypedStmt::Assign(stmt) => {
                        self.lower_assign(stmt, &local_env, stmts);
                    }
                    TypedStmt::Expr(e) if is_last => {
                        self.lower_expr_into(dst, &e.expr, &local_env, stmts);
                    }
                    TypedStmt::Expr(e) => {
                        self.lower_expr_stmt(&e.expr, &local_env, stmts);
                    }
                    TypedStmt::If(_)
                    | TypedStmt::While(_)
                    | TypedStmt::Match(_)
                    | TypedStmt::ForIn(_)
                    | TypedStmt::ForRange(_)
                    | TypedStmt::Return(_)
                    | TypedStmt::Break(_)
                    | TypedStmt::Continue(_) => {
                        // Step 5: all control-flow forms (including `return`)
                        // are rejected at type-check (T068). If one ever reaches
                        // AIR, the type-check rejection is incomplete and the
                        // panic message will point at the gap.
                        unreachable!(
                            "ICE: control-flow statement reached AIR lowering inside \
                         handle/region body — type-check should have emitted T068"
                        );
                    }
                },
            );
        }
    }

    fn lower_expr_stmt(
        &mut self,
        expr: &TypedExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        stmts.with_span(expr.span, |stmts| self.lower_expr_stmt_at(expr, env, stmts));
    }

    fn lower_expr_stmt_at(
        &mut self,
        expr: &TypedExpr,
        env: &LookupMap<String, VarId>,
        stmts: &mut StatementBuffer,
    ) {
        match &expr.kind {
            TypedExprKind::Send(send) => {
                let target = *env
                    .get(&send.target)
                    .expect("ICE: unresolved local during AIR lowering");
                let payload_args = send
                    .args
                    .iter()
                    .map(|arg| self.lower_expr_to_var(arg, env, stmts))
                    .collect::<Vec<_>>();
                let msg = self.lower_message_record(&payload_args, stmts);
                let (payload_buf, payload_len) =
                    self.lower_message_payload(msg, &payload_args, stmts);
                stmts.push(AirStmt::MessageSend {
                    target,
                    msg,
                    actor_type: actor_type_id(&send.actor),
                    handler: handler_id(&send.actor, &send.handler),
                    payload_buf,
                    payload_len,
                });
            }
            _ => {
                // Sound-divergence guard (Tier A / SC-2): a `Never`-typed statement
                // expression (`trap()`, an abortive `perform`) always aborts, so it
                // needs no real destination. Allocate a dummy `Unit` slot rather than
                // calling `lower_type(Never)` — which KEEPS its ICE as the leak
                // backstop. The Trap/perform lowering ignores `dst` and emits the
                // abort (wasm `unreachable`).
                let dst = if matches!(expr.ty, Type::Never) {
                    self.fresh_local(AirType::Unit, AirValueKind::Copy, String::new())
                } else {
                    self.fresh_local(
                        lower_type(&expr.ty),
                        classify_value_kind(&expr.ty),
                        String::new(),
                    )
                };
                self.lower_expr_into(dst, expr, env, stmts);
            }
        }
    }

    fn lower_message_record(&mut self, args: &[VarId], stmts: &mut StatementBuffer) -> VarId {
        let fields = args
            .iter()
            .enumerate()
            .map(|(index, value)| (format!("arg{index}"), *value))
            .collect::<Vec<_>>();
        let kind = fields.iter().fold(AirValueKind::Copy, |kind, (_, var)| {
            combine_value_kinds(kind, self.var_kind(*var))
        });
        let msg = self.fresh_local(AirType::Ptr, kind, "message");
        stmts.push(AirStmt::Assign {
            dst: msg,
            val: AirValue::RecordConstruct { fields },
        });
        msg
    }

    fn lower_message_payload(
        &mut self,
        msg: VarId,
        args: &[VarId],
        stmts: &mut StatementBuffer,
    ) -> (VarId, VarId) {
        let payload_buf = self.fresh_local(AirType::Ptr, AirValueKind::Copy, "message_buf");
        let payload_len = self.fresh_local(AirType::Ptr, AirValueKind::Copy, "message_len");
        stmts.push(AirStmt::SerializeMessage {
            msg,
            args: args.to_vec(),
            dst_buf: payload_buf,
            dst_len: payload_len,
        });
        (payload_buf, payload_len)
    }

    fn lower_match_arms(
        &mut self,
        arms: &[TypedMatchArm],
        scrutinee: VarId,
        env: LookupMap<String, VarId>,
        block_id: BlockId,
        stmts: StatementBuffer,
        exit_block: BlockId,
    ) {
        // Empty match: nothing to dispatch — fall straight through to the join.
        if arms.is_empty() {
            self.blocks.push(LoweringBlock {
                id: block_id,
                stmts,
                terminator: AirTerminator::Jump(exit_block),
            });
            return;
        }

        // DoS hardening: the arm chain used to be lowered by RECURSING on `rest`
        // (O(arms) native stack) and each dispatch `Branch` carried
        // `merge_block: None`, forcing the wasm emitter to RECONSTRUCT the merge
        // via the recursive `fallthrough_target` walk and to emit the arms as a
        // deeply NESTED `if/else` cascade — so a single many-arm match or a long
        // chain of matches overflowed the stack. The whole dispatch is now wrapped
        // in ONE enclosing block (`AirTerminator::Dispatch`); arm bodies
        // `Jump(exit_block)`, which the wasm emitter turns into a `br` out of that
        // block. The arm tests therefore form a FLAT sibling chain (each arm is
        // `if (cond) { body; br }` at one nesting level) with an EXPLICIT
        // `merge_block`, so this lowering is a simple loop and wasm emission needs
        // no fallthrough computation and no per-arm recursion. The scrutinee was
        // evaluated into `stmts`, which ride on the wrapper block.
        let start = self.fresh_block();
        self.security
            .control_policy
            .insert(block_id, AirPolicyClass::Dispatch);
        self.blocks.push(LoweringBlock {
            id: block_id,
            stmts,
            terminator: AirTerminator::Dispatch {
                start,
                exit: exit_block,
            },
        });

        // `cur` holds the current arm's test; on a no-match it branches to the
        // next arm's test block. A catch-all (or the exhaustive last literal) ends
        // the chain unconditionally.
        let mut cur = start;
        for (idx, arm) in arms.iter().enumerate() {
            let is_last = idx + 1 == arms.len();
            let arm_block = self.fresh_block();

            // Build this arm's environment — add pattern bindings.
            let mut arm_env = env.clone();
            match &arm.pattern {
                TypedPattern::Binding(name) => {
                    arm_env.insert(name.clone(), scrutinee);
                }
                TypedPattern::EnumVariant { bindings, .. } => {
                    // Payload bindings are extracted via LoadField in the arm preamble.
                    for (name, ty) in bindings {
                        if name != "_" {
                            let var = self.fresh_local(
                                lower_type(ty),
                                classify_value_kind(ty),
                                name.clone(),
                            );
                            arm_env.insert(name.clone(), var);
                        }
                    }
                }
                // Array/slice pattern (Phase 5): pre-allocate locals for each named
                // element + the named rest (a `&[T]` slice). Loads happen in the arm
                // preamble below, after the length test passes.
                TypedPattern::Array {
                    elem_binds,
                    rest,
                    elem_ty,
                    ..
                } => {
                    for (name, ty) in elem_binds {
                        if let Some(name) = name {
                            let var = self.fresh_local(
                                lower_type(ty),
                                classify_value_kind(ty),
                                name.clone(),
                            );
                            arm_env.insert(name.clone(), var);
                        }
                    }
                    if let Some((Some(rest_name), _)) = rest {
                        let slice_ty = Type::Slice(Box::new(elem_ty.clone()));
                        let var = self.fresh_local(
                            lower_type(&slice_ty),
                            classify_value_kind(&slice_ty),
                            rest_name.clone(),
                        );
                        arm_env.insert(rest_name.clone(), var);
                    }
                }
                _ => {}
            }

            match &arm.pattern {
                // Catch-all — and the exhaustive last literal, which needs no test
                // because control only reaches it when it must match (preserves the
                // pre-existing optimization). Both end the dispatch chain.
                TypedPattern::Wildcard | TypedPattern::Binding(_) if arm.guard.is_none() => {
                    self.blocks.push(LoweringBlock {
                        id: cur,
                        stmts: StatementBuffer::new(),
                        terminator: AirTerminator::Jump(arm_block),
                    });
                    self.lower_statements(
                        &arm.body.statements,
                        arm_env,
                        arm_block,
                        Some(exit_block),
                    );
                    return;
                }
                TypedPattern::Wildcard | TypedPattern::Binding(_) => {
                    let next = self.fresh_block();
                    self.blocks.push(LoweringBlock {
                        id: cur,
                        stmts: StatementBuffer::new(),
                        terminator: AirTerminator::Jump(arm_block),
                    });
                    self.lower_guarded_match_body(
                        arm,
                        arm_env,
                        arm_block,
                        StatementBuffer::new(),
                        next,
                        exit_block,
                    );
                    cur = next;
                }
                TypedPattern::Literal(_) if is_last && arm.guard.is_none() => {
                    self.blocks.push(LoweringBlock {
                        id: cur,
                        stmts: StatementBuffer::new(),
                        terminator: AirTerminator::Jump(arm_block),
                    });
                    self.lower_statements(
                        &arm.body.statements,
                        arm_env,
                        arm_block,
                        Some(exit_block),
                    );
                    return;
                }
                TypedPattern::Literal(literal) => {
                    let mut test_stmts = StatementBuffer::at(arm.span);
                    let cond = self.lower_match_condition(scrutinee, literal, &mut test_stmts);
                    let next = self.fresh_block();
                    self.security
                        .control_policy
                        .insert(cur, AirPolicyClass::Dispatch);
                    self.blocks.push(LoweringBlock {
                        id: cur,
                        stmts: test_stmts,
                        terminator: AirTerminator::Branch {
                            cond,
                            then_block: arm_block,
                            else_block: next,
                            merge_block: Some(next),
                        },
                    });
                    if arm.guard.is_some() {
                        self.lower_guarded_match_body(
                            arm,
                            arm_env,
                            arm_block,
                            StatementBuffer::new(),
                            next,
                            exit_block,
                        );
                    } else {
                        self.lower_statements(
                            &arm.body.statements,
                            arm_env,
                            arm_block,
                            Some(exit_block),
                        );
                    }
                    cur = next;
                }
                TypedPattern::Range { lo, hi } => {
                    // `lo..=hi` → two sequential bounds checks (no `&&` in SIGIL);
                    // either failure falls through to `next`. The two checks live in
                    // separate blocks but the chain between ARMS stays flat.
                    // Non-integer bounds are fenced upstream by T282. They
                    // used to be coerced to `0` here, which left a
                    // `Ptr >= I64` comparison for the emitter to choke on —
                    // the backstop fired in wasm.rs, naming the backend for
                    // what was really a source-level type error.
                    let lo_val = match lo {
                        Literal::Int(n) => *n,
                        other => panic!(
                            "ICE: non-integer range lower bound {other:?} reached AIR \
                             (type_check T282 must reject it before lowering)"
                        ),
                    };
                    let hi_val = match hi {
                        Literal::Int(n) => *n,
                        other => panic!(
                            "ICE: non-integer range upper bound {other:?} reached AIR \
                             (type_check T282 must reject it before lowering)"
                        ),
                    };

                    let mut lo_stmts = StatementBuffer::at(arm.span);
                    let lo_var = self.fresh_local(AirType::I64, AirValueKind::Copy, "range_lo");
                    lo_stmts.push(AirStmt::Assign {
                        dst: lo_var,
                        val: AirValue::IntLit(lo_val),
                    });
                    let lo_check =
                        self.fresh_local(AirType::Bool, AirValueKind::Copy, "range_lo_check");
                    lo_stmts.push(AirStmt::Assign {
                        dst: lo_check,
                        val: AirValue::Binary {
                            lhs: scrutinee,
                            op: BinaryOp::GtEq,
                            rhs: lo_var,
                        },
                    });

                    let hi_block = self.fresh_block();
                    let next = self.fresh_block();
                    self.security
                        .control_policy
                        .insert(cur, AirPolicyClass::Dispatch);
                    self.blocks.push(LoweringBlock {
                        id: cur,
                        stmts: lo_stmts,
                        terminator: AirTerminator::Branch {
                            cond: lo_check,
                            then_block: hi_block,
                            else_block: next,
                            merge_block: Some(next),
                        },
                    });

                    let mut hi_stmts = StatementBuffer::at(arm.span);
                    let hi_var = self.fresh_local(AirType::I64, AirValueKind::Copy, "range_hi");
                    hi_stmts.push(AirStmt::Assign {
                        dst: hi_var,
                        val: AirValue::IntLit(hi_val),
                    });
                    let hi_check =
                        self.fresh_local(AirType::Bool, AirValueKind::Copy, "range_hi_check");
                    hi_stmts.push(AirStmt::Assign {
                        dst: hi_check,
                        val: AirValue::Binary {
                            lhs: scrutinee,
                            op: BinaryOp::LtEq,
                            rhs: hi_var,
                        },
                    });
                    self.security
                        .control_policy
                        .insert(hi_block, AirPolicyClass::Dispatch);
                    self.blocks.push(LoweringBlock {
                        id: hi_block,
                        stmts: hi_stmts,
                        terminator: AirTerminator::Branch {
                            cond: hi_check,
                            then_block: arm_block,
                            else_block: next,
                            merge_block: Some(next),
                        },
                    });

                    if arm.guard.is_some() {
                        self.lower_guarded_match_body(
                            arm,
                            arm_env,
                            arm_block,
                            StatementBuffer::new(),
                            next,
                            exit_block,
                        );
                    } else {
                        self.lower_statements(
                            &arm.body.statements,
                            arm_env,
                            arm_block,
                            Some(exit_block),
                        );
                    }
                    cur = next;
                }
                TypedPattern::EnumVariant {
                    type_name,
                    variant,
                    bindings,
                    ..
                } => {
                    // Compare tag (stored at offset 0 of the enum value).
                    let mut test_stmts = StatementBuffer::at(arm.span);
                    let tag = self.fresh_local(AirType::I32, AirValueKind::Copy, "__tag");
                    test_stmts.push(AirStmt::LoadField {
                        dst: tag,
                        base_ptr: scrutinee,
                        offset: 0,
                        ty: AirType::I32,
                    });
                    let variant_index = self
                        .enum_registry
                        .get(type_name)
                        .and_then(|info| info.variants.iter().position(|(name, _)| name == variant))
                        .unwrap_or(0) as u32;
                    let expected_tag =
                        self.fresh_local(AirType::I32, AirValueKind::Copy, "__expected_tag");
                    test_stmts.push(AirStmt::Assign {
                        dst: expected_tag,
                        val: AirValue::IntLit(variant_index as i64),
                    });
                    let tag_match =
                        self.fresh_local(AirType::Bool, AirValueKind::Copy, "__tag_match");
                    test_stmts.push(AirStmt::Assign {
                        dst: tag_match,
                        val: AirValue::Binary {
                            lhs: tag,
                            op: BinaryOp::Eq,
                            rhs: expected_tag,
                        },
                    });

                    let next = self.fresh_block();
                    self.security
                        .control_policy
                        .insert(cur, AirPolicyClass::Dispatch);
                    self.blocks.push(LoweringBlock {
                        id: cur,
                        stmts: test_stmts,
                        terminator: AirTerminator::Branch {
                            cond: tag_match,
                            then_block: arm_block,
                            else_block: next,
                            merge_block: Some(next),
                        },
                    });

                    // Payload extraction preamble (only when the variant binds names).
                    if bindings.iter().any(|(name, _)| name != "_") || arm.guard.is_some() {
                        let mut preamble_stmts = StatementBuffer::at(arm.span);
                        let mut payload_offset = 4u32;
                        for (name, ty) in bindings {
                            if name != "_" {
                                let var = arm_env[name];
                                preamble_stmts.push(AirStmt::LoadField {
                                    dst: var,
                                    base_ptr: scrutinee,
                                    offset: payload_offset,
                                    ty: lower_type(ty),
                                });
                            }
                            payload_offset += lower_type(ty).width();
                        }
                        if arm.guard.is_some() {
                            self.lower_guarded_match_body(
                                arm,
                                arm_env,
                                arm_block,
                                preamble_stmts,
                                next,
                                exit_block,
                            );
                        } else {
                            let body_block = self.fresh_block();
                            self.blocks.push(LoweringBlock {
                                id: arm_block,
                                stmts: preamble_stmts,
                                terminator: AirTerminator::Jump(body_block),
                            });
                            self.lower_statements(
                                &arm.body.statements,
                                arm_env,
                                body_block,
                                Some(exit_block),
                            );
                        }
                    } else {
                        self.lower_statements(
                            &arm.body.statements,
                            arm_env,
                            arm_block,
                            Some(exit_block),
                        );
                    }
                    cur = next;
                }
                // Array/slice destructuring `[a, b, ..rest]` (Phase 5). The arm matches
                // iff the runtime length satisfies the pattern's length constraint
                // (no-rest → `len == k`; `..rest` → `len >= k`). On a match, the arm
                // preamble binds each fixed element by constant index and (if named)
                // the rest as a `&[T]` slice over `[k..len)`. Element loads and the
                // rest slice share the for-in/index/slice-expr layout (offset-4 header
                // skip for arrays AND slices, since a slice's data_ptr is not advanced
                // past the underlying header).
                TypedPattern::Array {
                    elem_binds,
                    rest: pat_rest,
                    elem_ty,
                    is_slice,
                } => {
                    let mut test_stmts = StatementBuffer::at(arm.span);
                    let elem_air_type = lower_type(elem_ty);
                    let elem_size = elem_air_type.width();
                    let k = elem_binds.len();

                    // len = scrutinee length: slice fat-pointer len field, or array header.
                    let len = if *is_slice {
                        self.slice_len_var(scrutinee, &mut test_stmts)
                    } else {
                        let l = self.fresh_local(AirType::U32, AirValueKind::Copy, "__arr_pat_len");
                        test_stmts.push(AirStmt::LoadField {
                            dst: l,
                            base_ptr: scrutinee,
                            offset: 0,
                            ty: AirType::U32,
                        });
                        l
                    };
                    let k_var = self.fresh_local(AirType::U32, AirValueKind::Copy, "__arr_pat_k");
                    test_stmts.push(AirStmt::Assign {
                        dst: k_var,
                        val: AirValue::IntLit(k as i64),
                    });
                    let cond =
                        self.fresh_local(AirType::Bool, AirValueKind::Copy, "__arr_pat_match");
                    let op = if pat_rest.is_some() {
                        BinaryOp::GtEq
                    } else {
                        BinaryOp::Eq
                    };
                    test_stmts.push(AirStmt::Assign {
                        dst: cond,
                        val: AirValue::Binary {
                            lhs: len,
                            op,
                            rhs: k_var,
                        },
                    });

                    let next = self.fresh_block();
                    self.security
                        .control_policy
                        .insert(cur, AirPolicyClass::Dispatch);
                    self.blocks.push(LoweringBlock {
                        id: cur,
                        stmts: test_stmts,
                        terminator: AirTerminator::Branch {
                            cond,
                            then_block: arm_block,
                            else_block: next,
                            merge_block: Some(next),
                        },
                    });

                    // Arm preamble: bind fixed elements + the rest slice, then body.
                    let mut preamble = StatementBuffer::at(arm.span);
                    let load_base = if *is_slice {
                        self.slice_data_ptr_var(scrutinee, &mut preamble)
                    } else {
                        scrutinee
                    };
                    for (i, (name, _)) in elem_binds.iter().enumerate() {
                        if let Some(name) = name {
                            let dst = arm_env[name];
                            let idx_var =
                                self.fresh_local(AirType::U32, AirValueKind::Copy, "__arr_pat_idx");
                            preamble.push(AirStmt::Assign {
                                dst: idx_var,
                                val: AirValue::IntLit(i as i64),
                            });
                            preamble.push(AirStmt::LoadDynamic {
                                dst,
                                base_ptr: load_base,
                                index: idx_var,
                                elem_size,
                                ty: elem_air_type,
                                offset: 4,
                            });
                        }
                    }
                    if let Some((Some(rest_name), _)) = pat_rest {
                        let dst = arm_env[rest_name];
                        self.build_rest_slice(
                            dst,
                            scrutinee,
                            *is_slice,
                            k,
                            len,
                            elem_size,
                            &mut preamble,
                        );
                    }
                    if arm.guard.is_some() {
                        self.lower_guarded_match_body(
                            arm, arm_env, arm_block, preamble, next, exit_block,
                        );
                    } else {
                        let body_block = self.fresh_block();
                        self.blocks.push(LoweringBlock {
                            id: arm_block,
                            stmts: preamble,
                            terminator: AirTerminator::Jump(body_block),
                        });
                        self.lower_statements(
                            &arm.body.statements,
                            arm_env,
                            body_block,
                            Some(exit_block),
                        );
                    }
                    cur = next;
                }
            }
        }

        // Fall-through after the last conditional arm (no catch-all / last-literal
        // ended the chain — e.g. an enum match exhaustive by variant coverage). For
        // an exhaustive match this block is unreachable; jump to the join so the
        // function stays well-formed (matches the old recursion's base case).
        self.security.semantic_unreachable_blocks.insert(cur);
        self.blocks.push(LoweringBlock {
            id: cur,
            stmts: StatementBuffer::new(),
            terminator: AirTerminator::Jump(exit_block),
        });
    }

    fn lower_guarded_match_body(
        &mut self,
        arm: &TypedMatchArm,
        env: BTreeMap<String, VarId>,
        guard_block: BlockId,
        preamble: StatementBuffer,
        next_arm: BlockId,
        exit_block: BlockId,
    ) {
        let guard = arm
            .guard
            .as_ref()
            .expect("guarded match lowering requires a guard");
        let body_block = self.fresh_block();
        self.lower_bool_branch(guard, &env, guard_block, preamble, body_block, next_arm);
        self.lower_statements(&arm.body.statements, env, body_block, Some(exit_block));
    }

    fn lower_bool_branch(
        &mut self,
        expr: &TypedExpr,
        env: &BTreeMap<String, VarId>,
        block: BlockId,
        mut stmts: StatementBuffer,
        then_block: BlockId,
        else_block: BlockId,
    ) {
        stmts.active_span = Some(expr.span);
        if let TypedExprKind::Binary(binary) = &expr.kind {
            match binary.op {
                BinaryOp::LogicalAnd => {
                    let rhs_block = self.fresh_block();
                    self.lower_bool_branch(&binary.lhs, env, block, stmts, rhs_block, else_block);
                    self.lower_bool_branch(
                        &binary.rhs,
                        env,
                        rhs_block,
                        StatementBuffer::new(),
                        then_block,
                        else_block,
                    );
                    return;
                }
                BinaryOp::LogicalOr => {
                    let rhs_block = self.fresh_block();
                    self.lower_bool_branch(&binary.lhs, env, block, stmts, then_block, rhs_block);
                    self.lower_bool_branch(
                        &binary.rhs,
                        env,
                        rhs_block,
                        StatementBuffer::new(),
                        then_block,
                        else_block,
                    );
                    return;
                }
                _ => {}
            }
        }
        let cond = self.lower_expr_to_var(expr, env, &mut stmts);
        self.security
            .control_policy
            .insert(block, AirPolicyClass::Branch);
        self.blocks.push(LoweringBlock {
            id: block,
            stmts,
            terminator: AirTerminator::Branch {
                cond,
                then_block,
                else_block,
                merge_block: Some(else_block),
            },
        });
    }

    /// Build a `&[T]` slice fat-pointer over `scrutinee[start..len]` for an
    /// array-pattern `..rest` binding (Phase 5). Mirrors `lower_slice_expr`'s
    /// data-ptr arithmetic (receiver base + `start*elem_size`, `len-start`
    /// length) WITHOUT the bounds `TrapIf`s — the enclosing arm only runs when
    /// the length test guaranteed `len >= start`, so the range is always valid.
    #[allow(clippy::too_many_arguments)]
    fn build_rest_slice(
        &mut self,
        dst: VarId,
        scrutinee: VarId,
        is_slice: bool,
        start: usize,
        len: VarId,
        elem_size: u32,
        stmts: &mut StatementBuffer,
    ) {
        stmts.push(AirStmt::BumpAlloc {
            persistent: self.state_backed_alloc,
            dst,
            size_bytes: SLICE_HEADER_SIZE,
            align: SLICE_HEADER_ALIGN,
        });
        let receiver_base = if is_slice {
            self.slice_data_ptr_var(scrutinee, stmts)
        } else {
            scrutinee
        };
        let start_var = self.fresh_local(AirType::U32, AirValueKind::Copy, "__rest_start");
        stmts.push(AirStmt::Assign {
            dst: start_var,
            val: AirValue::IntLit(start as i64),
        });
        let elem_size_var = self.fresh_local(AirType::U32, AirValueKind::Copy, "__rest_elem_size");
        stmts.push(AirStmt::Assign {
            dst: elem_size_var,
            val: AirValue::IntLit(elem_size as i64),
        });
        let byte_offset = self.fresh_local(AirType::U32, AirValueKind::Copy, "__rest_byte_offset");
        stmts.push(AirStmt::Assign {
            dst: byte_offset,
            val: AirValue::Binary {
                lhs: start_var,
                op: BinaryOp::Mul,
                rhs: elem_size_var,
            },
        });
        let data_ptr = self.fresh_local(AirType::Ptr, AirValueKind::Copy, "__rest_data_ptr");
        stmts.push(AirStmt::Assign {
            dst: data_ptr,
            val: AirValue::Binary {
                lhs: receiver_base,
                op: BinaryOp::Add,
                rhs: byte_offset,
            },
        });
        stmts.push(AirStmt::StoreField {
            base_ptr: dst,
            offset: SLICE_DATA_PTR_OFFSET,
            val: data_ptr,
            ty: AirType::Ptr,
        });
        let rest_len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__rest_len");
        stmts.push(AirStmt::Assign {
            dst: rest_len,
            val: AirValue::Binary {
                lhs: len,
                op: BinaryOp::Sub,
                rhs: start_var,
            },
        });
        stmts.push(AirStmt::StoreField {
            base_ptr: dst,
            offset: SLICE_LEN_OFFSET,
            val: rest_len,
            ty: AirType::U32,
        });
    }

    fn lower_match_condition(
        &mut self,
        scrutinee: VarId,
        literal: &Literal,
        stmts: &mut StatementBuffer,
    ) -> VarId {
        // Str match-arm literals funnel into the same byte comparison
        // as `==` (`AirStmt::StrBytesEq`, PR #699), so a view or
        // constructed scrutinee hits its arm. The pattern side needs
        // NO header: its data pointer is the interned literal and its
        // length is a compile-time constant, so only the scrutinee is
        // read from a header. (The data-ptr era BumpAlloc'd an 8-byte
        // pattern header per arm purely so the comparison could take
        // two headers; byte comparison retired that shape and, with
        // it, the per-arm allocation, its alloc-fuel charge, and — in
        // a state-backed context — a persistent allocation.)
        if let Literal::Str(value) = literal {
            let pat_data =
                self.fresh_local(AirType::U32, AirValueKind::Copy, "__match_str_data_ptr");
            stmts.push(AirStmt::Assign {
                dst: pat_data,
                val: AirValue::StrLit(value.clone()),
            });
            let pat_len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__match_str_len");
            stmts.push(AirStmt::Assign {
                dst: pat_len,
                val: AirValue::IntLit(value.len() as i64),
            });

            let scr_data = self.fresh_local(AirType::U32, AirValueKind::Copy, "__match_scr_data");
            stmts.push(AirStmt::LoadField {
                dst: scr_data,
                base_ptr: scrutinee,
                offset: STR_DATA_PTR_OFFSET,
                ty: AirType::U32,
            });
            let scr_len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__match_scr_len");
            stmts.push(AirStmt::LoadField {
                dst: scr_len,
                base_ptr: scrutinee,
                offset: STR_LEN_OFFSET,
                ty: AirType::U32,
            });

            let cond = self.fresh_local(AirType::Bool, AirValueKind::Copy, "match_cond");
            self.emit_str_bytes_eq_parts(scr_data, scr_len, pat_data, pat_len, cond, stmts);
            return cond;
        }

        let literal_var = self.fresh_local(
            match literal {
                Literal::Int(_) => AirType::I64,
                Literal::Float(_) => AirType::F64,
                Literal::Bool(_) => AirType::Bool,
                Literal::Str(_) => unreachable!("Str handled above"),
                // u256 PR-U2: wide-int match PATTERNS are unsupported (they'd need
                // value-eq like Str); the type-checker rejects them, so this is
                // unreachable. (Wide literals in expression position are supported.)
                Literal::Int256(_) => {
                    unreachable!("wide-int match patterns are rejected at type-check")
                }
            },
            AirValueKind::Copy,
            "match_lit",
        );
        stmts.push(AirStmt::Assign {
            dst: literal_var,
            val: match literal {
                Literal::Int(value) => AirValue::IntLit(*value),
                Literal::Float(value) => AirValue::FloatLit(*value),
                Literal::Bool(value) => AirValue::BoolLit(*value),
                Literal::Str(_) => unreachable!("Str handled above"),
                Literal::Int256(_) => {
                    unreachable!("wide-int match patterns are rejected at type-check")
                }
            },
        });

        let cond = self.fresh_local(AirType::Bool, AirValueKind::Copy, "match_cond");
        stmts.push(AirStmt::Assign {
            dst: cond,
            val: AirValue::Binary {
                lhs: scrutinee,
                op: BinaryOp::Eq,
                rhs: literal_var,
            },
        });
        cond
    }

    /// Emit Str-Str CONTENT equality (`AirStmt::StrBytesEq`, PR #699):
    /// loads `data_ptr` and `len` from each header, then one statement
    /// that compares lengths and — only when they match — scans the
    /// bytes (fuel-metered per iteration in `wasm.rs`; `fuel.rs` also
    /// poisons the workload ceiling, since the trip count is a runtime
    /// length). Stores the boolean verdict into `dst`. `==`, `!=`, and
    /// string-literal `match` arms all funnel here, so the T033/CT018
    /// `@SecretCT` gate and the certified-source fence key on exactly
    /// this lowering. Replaced PR S1's data-ptr comparison (AG-S1-M),
    /// which ignored `len` and called a `substr` view equal to its
    /// parent.
    fn emit_str_bytes_eq(
        &mut self,
        lhs_header: VarId,
        rhs_header: VarId,
        dst: VarId,
        stmts: &mut StatementBuffer,
    ) {
        let lhs_data = self.fresh_local(AirType::U32, AirValueKind::Copy, "__str_eq_lhs_data");
        stmts.push(AirStmt::LoadField {
            dst: lhs_data,
            base_ptr: lhs_header,
            offset: STR_DATA_PTR_OFFSET,
            ty: AirType::U32,
        });
        let lhs_len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__str_eq_lhs_len");
        stmts.push(AirStmt::LoadField {
            dst: lhs_len,
            base_ptr: lhs_header,
            offset: STR_LEN_OFFSET,
            ty: AirType::U32,
        });
        let rhs_data = self.fresh_local(AirType::U32, AirValueKind::Copy, "__str_eq_rhs_data");
        stmts.push(AirStmt::LoadField {
            dst: rhs_data,
            base_ptr: rhs_header,
            offset: STR_DATA_PTR_OFFSET,
            ty: AirType::U32,
        });
        let rhs_len = self.fresh_local(AirType::U32, AirValueKind::Copy, "__str_eq_rhs_len");
        stmts.push(AirStmt::LoadField {
            dst: rhs_len,
            base_ptr: rhs_header,
            offset: STR_LEN_OFFSET,
            ty: AirType::U32,
        });
        self.emit_str_bytes_eq_parts(lhs_data, lhs_len, rhs_data, rhs_len, dst, stmts);
    }

    /// Append the `StrBytesEq` statement over ALREADY-materialized
    /// data/len operands (plus a fresh scratch counter). The operands
    /// may come from header loads (`emit_str_bytes_eq`) or — for a
    /// string-literal match pattern — directly from `AirValue::StrLit`
    /// and the compile-time length, with no 8-byte header in between.
    fn emit_str_bytes_eq_parts(
        &mut self,
        lhs_data: VarId,
        lhs_len: VarId,
        rhs_data: VarId,
        rhs_len: VarId,
        dst: VarId,
        stmts: &mut StatementBuffer,
    ) {
        let idx = self.fresh_local(AirType::U32, AirValueKind::Copy, "__str_eq_idx");
        stmts.push(AirStmt::StrBytesEq {
            dst,
            lhs_data,
            lhs_len,
            rhs_data,
            rhs_len,
            idx,
        });
    }

    fn var_kind(&self, var: VarId) -> AirValueKind {
        self.value_kinds
            .get(&var)
            .cloned()
            .unwrap_or(AirValueKind::Copy)
    }

    /// The `dst: Option<VarId>` for a `Call` / `CallIndirect` AIR statement.
    /// A unit-returning callee has an EMPTY wasm result list (it pushes
    /// nothing onto the operand stack), so the call site must NOT emit a
    /// `local.set` — doing so pops an empty stack and yields invalid wasm
    /// (`type mismatch: expected i32 but nothing on stack`). Returns `None`
    /// for a Unit-typed destination so the wasm call arms skip the store;
    /// `Some(dst)` otherwise. A dst that is not (yet) a known local defaults
    /// to `Some` — the pre-existing, value-returning behavior.
    fn call_dst(&self, dst: VarId) -> Option<VarId> {
        let is_unit = self
            .locals
            .iter()
            .find(|(id, _)| *id == dst)
            .is_some_and(|(_, ty)| *ty == AirType::Unit);
        if is_unit { None } else { Some(dst) }
    }

    fn fresh_local(&mut self, ty: AirType, kind: AirValueKind, label: impl Into<String>) -> VarId {
        let dst = VarId(self.next_var);
        self.next_var += 1;
        self.locals.push((dst, ty));
        self.value_kinds.insert(dst, kind);
        self.security
            .value_contracts
            .entry(dst)
            .or_insert(AirLabelContract::Inferred);
        let label = label.into();
        self.debug_names.insert(
            dst,
            if label.is_empty() {
                format!("v{}", dst.0)
            } else {
                label
            },
        );
        dst
    }

    fn fresh_block(&mut self) -> BlockId {
        let id = BlockId(self.next_block);
        self.next_block += 1;
        self.block_multiplicity.push(self.ambient_multiplicity());
        id
    }
}

struct LoweredFunctionBody {
    locals: Vec<(VarId, AirType)>,
    value_kinds: BTreeMap<VarId, AirValueKind>,
    debug_names: BTreeMap<VarId, String>,
    debug_spans: BTreeMap<VarId, Span>,
    security: AirSecurityMetadata,
    blocks: Vec<AirBlock>,
    block_multiplicity: Vec<Option<u64>>,
}

/// HOF / N14-HOF: build the AIR signature for a CallIndirect against
/// a closure-typed local. Sole constructor of indirect-call signatures
/// for general closure dispatch (the grant path builds its own
/// signature inline since the args shape differs).
///
/// Convention (matches the synth closure body's lifted-params layout
/// at type_check.rs:7319-7323): position 0 is `AirType::Ptr` for the
/// env_ptr (the closure struct pointer); positions 1..N are the
/// lowered Type::Fn param types; return type is the lowered Type::Fn
/// return type.
///
/// Panics if `callee_ty` is not `Type::Fn(_, _, _)` — caller must
/// uphold this invariant (debug_assert in `lower_indirect_call_expr`).
fn build_indirect_call_signature(callee_ty: &Type) -> (Vec<AirType>, AirType) {
    let Type::Fn(params, ret, _, _) = callee_ty else {
        panic!(
            "ICE: build_indirect_call_signature called with non-Type::Fn: {:?}",
            callee_ty
        );
    };
    let mut air_params = Vec::with_capacity(1 + params.len());
    air_params.push(AirType::Ptr); // env_ptr at position 0 (N2-HOF convention)
    air_params.extend(params.iter().map(lower_type));
    let air_ret = lower_type(ret);
    (air_params, air_ret)
}

pub(crate) fn lower_type(ty: &Type) -> AirType {
    match ty {
        Type::Unit | Type::Error => AirType::Unit,
        Type::Bool => AirType::Bool,
        Type::I32 => AirType::I32,
        Type::U32 => AirType::U32,
        Type::I64 => AirType::I64,
        Type::U64 => AirType::U64,
        Type::F64 => AirType::F64,
        // PIL: Type::IntLit reaching lower_type means a record field's
        // substituted type or a generic monomorphization carries
        // unresolved polymorphism (the post-pass walker mutates
        // TypedExpr trees, not field-registry types that are
        // reconstructed from `program.records` during AIR lowering).
        // Default to I64 (equivalent to the walker's fallback). Mangled
        // names + field widths stay deterministic because every IntLit
        // maps to i64 regardless of value.
        Type::IntLit(_) => AirType::I64,
        // Regions (DEF-2b, LD-1): a region handle is an i64 token (`0` = global heap;
        // matches the reserved `Vec.alloc: i64` field). Inert at runtime in v1.
        Type::Region => AirType::I64,
        // HKT (EX-4 defense-in-depth): a higher-kinded var/app/ctor MUST have been
        // erased to a concrete Type::Named before AIR. lower_type otherwise maps an
        // unknown nominal to AirType::Ptr SILENTLY — so an explicit ICE arm here
        // turns would-be silent corruption into a loud failure. The whole-program
        // residual gate (EX-4) is the primary defense; these are the backstop.
        Type::HktVar { name, .. } => {
            panic!("ICE: unresolved higher-kinded var `{name}` reached lower_type")
        }
        Type::HktApp { ctor, .. } => {
            panic!("ICE: unresolved higher-kinded application `{ctor}<…>` reached lower_type")
        }
        Type::TypeCtor(name) => {
            panic!("ICE: bare type-constructor `{name}` reached lower_type (should be erased)")
        }
        // Typestate (ST-1/ST-3 backstop): a state marker MUST be erased by
        // `strip_state_args` before AIR; an explicit ICE turns would-be silent
        // corruption (a zero-size marker lowered as a `Ptr`) into a loud failure.
        Type::StateMarker(name) => {
            panic!("ICE: state marker `{name}` reached lower_type (should be erased)")
        }
        // Effect Handlers (C-NEVER): the abortive bottom type is gated before AIR
        // by the T279 value-position rejections (the F003 site checks + the
        // whole-program residual gate, type_check/residual.rs) — this ICE is the
        // backstop for a compiler-invariant violation, not a user error.
        Type::Never => {
            panic!("ICE: Type::Never reached lower_type (must be erased / gated before AIR)")
        }
        // u256/i256: a 32-byte cell in linear memory (4× i64 limbs), addressed
        // by a pointer — exactly like records/strings (representation P).
        Type::U256
        | Type::I256
        | Type::Str
        | Type::Named(_, _)
        | Type::Cap(_, _)
        | Type::ActorRef(_)
        | Type::Generic(_)
        | Type::Array { .. }
        // Tuple: a heap struct, like a record — represented as a pointer.
        | Type::Tuple(_)
        | Type::Fn(_, _, _, _)
        | Type::Ref(_, _)
        | Type::Slice(_)
        | Type::Ptr(_)
        | Type::MutPtr(_) => AirType::Ptr,
    }
}

fn classify_value_kind(ty: &Type) -> AirValueKind {
    // NB: AirValueKind::Cap carries only the cap's name. Deadline-typed
    // caps (Wall 2 Stage 1) intentionally elide the parameter at the
    // AIR layer — the parameter is a type-check-only artifact, never
    // observable at the wasm boundary. Subtyping is enforced at
    // type-check time before lowering reaches this function.
    match ty {
        Type::Cap(name, _) => AirValueKind::Cap(name.clone()),
        // Built-in `Slot<T>` is a heap pointer; aliasing copies are safe under
        // the actor model's single-threaded execution (INV-11). The cap inside
        // the slot is the linear value, tracked separately via SlotPut /
        // SlotTake. We use a dedicated `Slot(cap_name)` kind (rather than
        // generic Copy) so the capability verifier can accept slots
        // alongside caps at SpawnActor (Wall 1 Step 3). Deadline-typed
        // slot elements (Wall 2 Stage 1) are checked at type-check time
        // before reaching this lowering step; AIR stores name only.
        Type::Named(name, args) if name == "Slot" && args.len() == 1 => {
            let cap_name = match &args[0] {
                Type::Cap(n, _) => n.clone(),
                _ => "<unknown>".to_owned(),
            };
            AirValueKind::Slot(cap_name)
        }
        Type::Named(_, args) => {
            // A value is Linear if any type argument is linear (`Option<cap Fuel>`),
            // OR — typestate (TS2, ST-2) — if any argument is a phantom STATE marker
            // (`File<Open>` = `Named("File", [StateMarker("Open")])`). A typestate
            // value is AFFINE: classifying it Linear makes the EXISTING ownership
            // move-checker fire O001 (use-after-move) / O007 (move-while-borrowed) on
            // use-after-transition — i.e. use-after-revoke / use-after-transfer become
            // compile errors. The marker IS the signal (only a typestate nominal has a
            // `StateMarker` arg), so the context-free classifier needs no universe
            // threading. `AirValueKind` drives ONLY the ownership/capability verifiers
            // (never wasm codegen — `wasm.rs` ignores it), so this does not perturb the
            // byte-identical-AIR erasure gate.
            if args.iter().any(|arg| {
                matches!(arg, Type::StateMarker(_)) || classify_value_kind(arg).is_linear()
            }) {
                AirValueKind::Linear
            } else {
                AirValueKind::Copy
            }
        }
        Type::Array { elem, .. } => {
            if classify_value_kind(elem).is_linear() {
                AirValueKind::Linear
            } else {
                AirValueKind::Copy
            }
        }
        Type::Fn(_, _, is_linear, _) => {
            if *is_linear {
                AirValueKind::Linear
            } else {
                AirValueKind::Copy
            }
        }
        // Borrows are copyable (they're just pointers)
        Type::Ref(_, _) | Type::Slice(_) => AirValueKind::Copy,
        // ET-9 soundness: a tuple containing a cap/linear element is itself
        // Linear (is_linear() already covers Cap), so linear-use tracking
        // isn't defeated by hiding a cap inside a tuple.
        Type::Tuple(elems) => {
            if elems.iter().any(|e| classify_value_kind(e).is_linear()) {
                AirValueKind::Linear
            } else {
                AirValueKind::Copy
            }
        }
        // HKT (EX-4 defense-in-depth): a residual higher-kinded var/app/ctor MUST
        // have been erased to a concrete Type::Named before AIR; an explicit ICE
        // here stops it falling into the `_ => Copy` catch-all (which would
        // mis-classify a cap-bearing application as Copy and defeat linear-use
        // tracking).
        Type::HktVar { name, .. } => {
            panic!("ICE: unresolved higher-kinded var `{name}` reached classify_value_kind")
        }
        Type::HktApp { ctor, .. } => {
            panic!(
                "ICE: unresolved higher-kinded application `{ctor}<…>` reached classify_value_kind"
            )
        }
        Type::TypeCtor(name) => {
            panic!(
                "ICE: bare type-constructor `{name}` reached classify_value_kind (should be erased)"
            )
        }
        // Typestate (ST-2/ST-3): `classify_value_kind` RECURSES into `Named` args, so
        // it legitimately sees a state marker while classifying `File<Open>`. A marker
        // is the NEUTRAL (non-linear) identity element here — it does NOT make its
        // container linear. The affine classification of a typestate VALUE keys on the
        // OUTER nominal (TS2 consults `typestate_nominals`), never on this marker arg.
        Type::StateMarker(_) => AirValueKind::Copy,
        _ => AirValueKind::Copy,
    }
}

fn combine_value_kinds(lhs: AirValueKind, rhs: AirValueKind) -> AirValueKind {
    if lhs.is_cap() || rhs.is_cap() || lhs.is_linear() || rhs.is_linear() {
        AirValueKind::Linear
    } else {
        AirValueKind::Copy
    }
}

fn actor_type_id(name: &str) -> ActorTypeId {
    ActorTypeId(stable_id(name.as_bytes()))
}

fn handler_id(actor: &str, handler: &str) -> HandlerId {
    let mut bytes = Vec::with_capacity(actor.len() + handler.len() + 2);
    bytes.extend_from_slice(actor.as_bytes());
    bytes.push(b':');
    bytes.extend_from_slice(handler.as_bytes());
    HandlerId(stable_id(&bytes))
}

fn lower_function_kind(kind: &TypedFunctionKind) -> AirFunctionKind {
    match kind {
        TypedFunctionKind::ModuleInit => AirFunctionKind::ModuleInit,
        TypedFunctionKind::ModuleFunction => AirFunctionKind::ModuleFunction,
        TypedFunctionKind::ActorInit { actor, is_entry } => AirFunctionKind::ActorInit {
            actor: actor.clone(),
            actor_type: actor_type_id(actor),
            is_entry: *is_entry,
        },
        TypedFunctionKind::ActorHandler {
            actor,
            handler,
            is_entry,
        } => AirFunctionKind::ActorHandler {
            actor: actor.clone(),
            actor_type: actor_type_id(actor),
            handler: handler.clone(),
            handler_id: handler_id(actor, handler),
            is_entry: *is_entry,
        },
        TypedFunctionKind::Closure => AirFunctionKind::Closure,
    }
}

fn stable_id(bytes: &[u8]) -> u32 {
    let mut hash = 0u32;
    for byte in bytes {
        hash = hash.wrapping_mul(33).wrapping_add(*byte as u32);
    }
    hash
}
