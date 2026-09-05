//! The typed tree -- `TypedProgram` and every node the type checker
//! builds: the shared input of the typed-program security passes (taint,
//! effect, ring) and the sole input of AIR lowering. Definitions only --
//! construction lives in `type_check/`, and this file emits no
//! diagnostics.
//!
//! Invariants owned here:
//! - `records`/`enums`/`effect_ops` are `BTreeMap`, never `HashMap`:
//!   snapshot tests (`snap_typecheck.rs`, `workload_snapshots.rs`) walk
//!   the Debug output transitively, and hash iteration order varies.
//! - The str-PRODUCING intrinsics are a closed set of two (`StrSubstr`,
//!   `StrFromRaw`): the in-file `utf8_invariant_tests` match is
//!   exhaustive (no `_`), so a new `TypedIntrinsicKind` variant refuses
//!   to compile until classified against the "every `str` is valid
//!   UTF-8" invariant.
//! - `TypedIndexExpr::bounds_proven` is set only by Z3-free compile-time
//!   comparisons, never from a solver verdict (SC-6: Z3 stays out of the
//!   memory-safety TCB); the `false` default keeps wasm byte-identical.
//! - `TypedExpr::refinement` is compile-time metadata, stripped at AIR
//!   lowering; it never influences emitted wasm bytes
//!   (`determinism_lock.rs` pins byte identity).
//!
//! Governing spec: docs/specs/type-checker-in-sigil.md names this file's
//! `TypedProgram` as the self-hosting differential target.

use std::collections::BTreeMap;

use crate::ast::{BinaryOp, Literal, Ring, TaintLabel};
use crate::name_resolution::DefId;
use crate::registries::{EffectRegistry, EffectSet};
use crate::span::Span;
use crate::type_check::Type;

#[derive(Debug, Clone, PartialEq)]
#[allow(clippy::type_complexity)]
pub struct TypedProgram {
    pub modules: Vec<TypedModule>,
    /// Record type name -> (type_params, fields) for field access lowering.
    ///
    /// BTreeMap (not HashMap) for deterministic Debug iteration: snapshot
    /// tests (`snap_typecheck.rs`, `workload_snapshots.rs`) walk this
    /// transitively, and HashMap iteration order varies across runs.
    /// Lookup complexity is O(log n) vs HashMap O(1), but record counts
    /// max out at ~100 per program in practice.
    pub records: BTreeMap<String, (Vec<String>, Vec<(String, Type)>)>,
    /// Enum name -> (type_params, variants) for tagged union codegen.
    /// BTreeMap for the same determinism reason as `records`.
    pub enums: BTreeMap<String, (Vec<String>, Vec<(String, Vec<Type>)>)>,
    /// Effect name -> effect ID mapping for handle-block resolution
    pub effect_registry: EffectRegistry,
    /// Effect name -> its operations' resolved signatures. Carried from the
    /// type universe so the EH4 effect-handler desugar can thread evidence for an
    /// effect's operations through the call graph (EH4.3) without re-deriving them
    /// from `perform` sites — a function with `E` in its row but no direct `perform`
    /// still needs `E`'s operation signatures to receive evidence parameters.
    pub effect_ops: BTreeMap<String, Vec<EffectOpSig>>,
}

/// An effect operation's resolved signature (name + parameter types + return
/// type), exposed on [`TypedProgram`] for the effect-handler desugar. Mirrors the
/// type checker's internal `EffectOpInfo`. An abortive operation (`-> never`) has
/// `ret == Type::Never`.
#[derive(Debug, Clone, PartialEq)]
pub struct EffectOpSig {
    pub name: String,
    pub params: Vec<Type>,
    /// Declared taint contract for each operation parameter, parallel to `params`.
    pub param_taints: Vec<TaintLabel>,
    pub ret: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedModule {
    pub def_id: DefId,
    pub name: String,
    pub ring: Ring,
    pub trusted: bool,
    pub span: Span,
    pub functions: Vec<TypedFunction>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedFunction {
    pub name: String,
    pub export_name: String,
    pub kind: TypedFunctionKind,
    /// Whether this function is an externally callable module/runtime entry.
    /// Private source helpers and synthesized closures remain callable from AIR
    /// but are not Public root occurrences or Wasm exports.
    pub externally_callable: bool,
    pub params: Vec<TypedParam>,
    pub captures: Vec<TypedParam>,
    pub ret: Type,
    pub ret_taint: TaintLabel,
    /// `-> T @Flow`: the result's label is the lub of the labels supplied to
    /// this function's `@Flow` parameters at the call site, not `ret_taint`.
    ///
    /// TAINT POLYMORPHISM. A `@Flow` signature is a promise about EVERY
    /// admissible label at once — `json::parse_field` handed `@Secret` bytes
    /// returns `@Secret` bytes, and handed `@Public` bytes returns `@Public`.
    /// It is NOT a declassification: no label is ever lowered. Soundness is
    /// established by checking the body once per admissible label with all
    /// `@Flow` positions instantiated to it (see `taint_check::check_function`),
    /// so a body that laundered a `@Flow` value into a `@Public` sink fails at
    /// the `@Internal`/`@Secret` instantiation. `@SecretCT` is excluded: its
    /// constant-time discipline is a property of the CODE, and the same body
    /// cannot be CT and non-CT at once.
    pub ret_flow: bool,
    pub effects: EffectSet,
    pub body: TypedBlock,
    pub span: Span,
}

impl TypedFunction {
    /// The typed identity of the source language's embedding-host entry.
    ///
    /// Type checking normally supplies both mangled forms, while a few synthetic
    /// test/program paths retain a bare name. Keep every security and ABI consumer
    /// on this one predicate so entry preservation cannot drift from taint policy.
    pub(crate) fn is_tool_main_entry(&self) -> bool {
        self.name == "tool_main"
            || self.name.ends_with("::tool_main")
            || self.export_name == "tool_main"
            || self.export_name.ends_with("__tool_main")
    }

    /// `tool_main` returns a packed host-facing value. Its established source
    /// policy permits an `@Internal` FFI result to cross that embedding boundary,
    /// while retaining any stronger explicitly declared result label.
    pub(crate) fn effective_return_taint(&self) -> TaintLabel {
        if self.is_tool_main_entry() {
            self.ret_taint.lub(TaintLabel::Internal)
        } else {
            self.ret_taint
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedFunctionKind {
    ModuleInit,
    ModuleFunction,
    ActorInit {
        actor: String,
        is_entry: bool,
    },
    ActorHandler {
        actor: String,
        handler: String,
        is_entry: bool,
    },
    Closure,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedClosureConstructExpr {
    pub synthesized_name: String,
    pub captures: Vec<TypedCapture>,
    pub param_types: Vec<Type>,
    pub ret_type: Type,
    pub is_linear: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedCapture {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedParam {
    pub name: String,
    pub ty: Type,
    pub taint: TaintLabel,
    /// `@Flow` — this parameter is taint-POLYMORPHIC (see [`TypedFunction::ret_flow`]).
    /// `taint` is then the label of the instantiation currently being checked and
    /// carries no contract of its own; call sites must consult `flow` first.
    pub flow: bool,
    /// MUTABLE-STATE S2: for an actor CAPTURE (a state field), whether it is
    /// declared `mut` — the AIR read model uses it to fresh-`LoadField` a `mut`
    /// field per read (memory reflects prior conditional writes) instead of the
    /// load-once cached env local (which would go stale after a handler write).
    /// `Default` for ordinary params and non-`mut` captures — so every non-`mut`
    /// actor keeps the load-once model and stays byte-identical.
    pub mutability: crate::ast::Mutability,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedBlock {
    pub statements: Vec<TypedStmt>,
    pub span: Span,
    pub guaranteed_return: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedStmt {
    Let(TypedLetStmt),
    Assign(TypedAssignStmt),
    Expr(TypedExprStmt),
    If(TypedIfStmt),
    Match(TypedMatchStmt),
    While(TypedWhileStmt),
    ForIn(TypedForInStmt),
    /// `for v in a..b { … }` — the exclusive range loop (see [`TypedForRangeStmt`]).
    ForRange(TypedForRangeStmt),
    Return(TypedReturnStmt),
    /// `break;` — exit the innermost enclosing loop (the `Span` is the keyword).
    Break(Span),
    /// `continue;` — next iteration of the innermost enclosing loop.
    Continue(Span),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedLetStmt {
    pub name: String,
    pub mutable: bool,
    pub ty: Type,
    /// The `@Label` the source WROTE, if any. `None` means unannotated —
    /// distinct from `Some(Public)`, which is an explicit @Public declaration.
    /// A monomorphic body treats both as a @Public sink (status quo: an
    /// unannotated `let` will not silently absorb an `@Internal` value). Inside
    /// a taint-POLYMORPHIC function there is no fixed label for a local to
    /// default to, so an unannotated one infers from its initializer instead —
    /// see the `Let` arm of `taint_check::check_stmt`.
    pub taint: Option<TaintLabel>,
    pub value: TypedExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedAssignStmt {
    /// The typed place — an lvalue expression (`Local`/`FieldAccess`/`Index`).
    pub place: TypedExpr,
    /// `Some(op)` for a compound `place op= value` on a field/index place
    /// (lowered as load-op-store at AIR). `None` for a simple assignment.
    pub op: Option<BinaryOp>,
    pub value: TypedExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedExprStmt {
    pub expr: TypedExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedIfStmt {
    pub condition: TypedExpr,
    pub then_branch: TypedBlock,
    pub else_branch: TypedBlock,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedMatchStmt {
    pub scrutinee: TypedExpr,
    pub arms: Vec<TypedMatchArm>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedMatchArm {
    pub pattern: TypedPattern,
    pub guard: Option<TypedExpr>,
    pub body: TypedBlock,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedPattern {
    Literal(Literal),
    Range {
        lo: Literal,
        hi: Literal,
    },
    Wildcard,
    Binding(String),
    EnumVariant {
        type_name: String,
        variant: String,
        bindings: Vec<(String, Type)>,
    },
    /// Array/slice destructuring `[a, b, ..rest]` (Phase 5). `elem_binds` pairs
    /// each fixed position's binding name (`None` = wildcard `_`) with the
    /// element type; `rest` is the optional trailing tail (`None` name = `..`),
    /// typed as the slice element type (it binds a `&[T]`). `elem_ty` is the
    /// scrutinee element type (for element/rest loads); `is_slice` selects the
    /// length-read + element-base dispatch (slice fat-pointer vs array header).
    Array {
        elem_binds: Vec<(Option<String>, Type)>,
        rest: Option<(Option<String>, Type)>,
        elem_ty: Type,
        is_slice: bool,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedWhileStmt {
    pub condition: TypedExpr,
    pub body: TypedBlock,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedReturnStmt {
    pub value: Option<TypedExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedExpr {
    pub ty: Type,
    pub kind: TypedExprKind,
    pub span: Span,
    /// Wall 4 Step 2: refinement preservation sidecar (V16).
    ///
    /// Set by `infer_field_access_expr` when reading from an `i64`-typed
    /// field of a refined record (V18). Carries ALL source-side clauses
    /// matching the accessed field name (V16, V26 — a future grammar
    /// relaxation may produce multi-clause attachments via `&&`/`||`;
    /// Step 1 currently produces 0 or 1 clauses per field).
    ///
    /// `None` everywhere else (V1). The CI grep-lint at
    /// `.github/workflows/ci.yml` (Wall 4 Step 2 V10) asserts that
    /// the literal-inline pattern (struct-field followed by Some-literal)
    /// appears in zero source files; callers use the field-shorthand
    /// form after binding the helper's return value. V19 confines
    /// `Option<RefinementClause>` to this file and `type_check.rs`. V24
    /// bans rest-pattern TypedExpr initializers workspace-wide.
    ///
    /// Cloned with the expression (V32: pivots to
    /// `Option<Arc<[RefinementClause]>>` if the bench gate flags > 10pp
    /// regression vs PR #60 baseline). Stripped at AIR lowering — Step 2
    /// refinements are compile-time metadata only and never reach codegen
    /// (V12); the existing `determinism_lock` test guarantees wasm bytes
    /// are byte-identical to Step 1 for all existing fixtures, and
    /// `diagnostic_determinism.rs` (V25) covers the diagnostic-output
    /// determinism the wasm-only gate misses.
    pub refinement: Option<Vec<crate::ast::RefinementClause>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedExprKind {
    Literal(Literal),
    Local(String),
    /// A read of an actor state field (`n` inside a handler/init body where `n`
    /// is declared in `state { … }` and not shadowed by a local). A distinct
    /// node — NOT a `Local` — so every pass is FORCED to decide what a state
    /// access means for it: AIR lowers it to a load off the state pointer (M3),
    /// `check_assign` gates writes by construction phase (M2), ownership treats
    /// state caps as borrow-only in handlers (M4), and taint derives the label
    /// from the field's DECLARED type rather than a local binding. Carries the
    /// field name; the enclosing `TypedExpr.ty` is the field's type.
    StateField(String),
    Call(TypedCallExpr),
    Intrinsic(TypedIntrinsicExpr),
    ResultCtor(TypedResultCtorExpr),
    EnumConstruct(TypedEnumConstructExpr),
    Try(TypedTryExpr),
    Send(TypedSendExpr),
    Ask(TypedAskExpr),
    Spawn(TypedSpawnExpr),
    Binary(TypedBinaryExpr),
    RecordConstruct(TypedRecordConstructExpr),
    FieldAccess(TypedFieldAccessExpr),
    CapRestrict(TypedCapRestrictExpr),
    CapSplit(TypedCapSplitExpr),
    CapDraw(TypedCapDrawExpr),
    Mint(TypedMintExpr),
    ArrayLit(TypedArrayLitExpr),
    Index(TypedIndexExpr),
    /// PR AF: `array[start..end]` slice operator. Wired into the
    /// typed_ast at commit #1 (scaffold); commit #4 enforces
    /// parent-is-immediate-borrow via T238 and emits real AIR.
    Slice(TypedSliceExpr),
    ClosureConstruct(TypedClosureConstructExpr),
    Borrow(TypedBorrowExpr),
    Grant(TypedGrantExpr),
    Handle(TypedHandleExpr),
    /// Effect Handlers (EH3): `perform E.op(args)` — the enclosing `TypedExpr.ty`
    /// is the operation's return type (the resumed value; `Type::Never` for an
    /// abortive operation). Gated before AIR (E004) until the lowering rung.
    Perform(TypedPerformExpr),
    /// Effect Handlers (EH3): the clause form `handle <e> { Op(x) => .. }`.
    /// Gated before AIR until the lowering rung.
    ClauseHandle(TypedClauseHandleExpr),
    /// Effect Handlers (EH3): `resume <value>` inside a scoped clause body.
    Resume(TypedResumeExpr),
    Declassify(TypedDeclassifyExpr),
    DeclassifyCt(TypedDeclassifyCtExpr),
    ExternCall(TypedExternCallExpr),
    Region(TypedRegionExpr),
    /// HOF prerequisite: general closure-call dispatch through a
    /// closure-typed local variable. Distinct from `Call` because
    /// the AIR lowering must emit `AirStmt::CallIndirect` against
    /// the heap-stored function-table index (not a direct
    /// function_ids lookup). `infer_call_expr` produces this
    /// variant when the callee path resolves to a local binding
    /// with `Type::Fn(_, _, _)`. Per N8-HOF, `callee_ty` is
    /// statically Type::Fn (never Type::Error); per N15-HOF,
    /// post-monomorphization `callee_ty` carries concrete types
    /// (no Generic).
    IndirectCall(TypedIndirectCallExpr),
    /// PR-E3: an interpolated string `f"…{e}…"`, typed as `str` with each hole
    /// type-checked (str/i64/bool). A pre-AIR pass (`lower_fstrings`) rewrites this
    /// into a `str_concat` chain of existing nodes, so AIR never lowers it directly.
    FString(TypedFStringExpr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedFStringExpr {
    pub parts: Vec<TypedFStringPart>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedFStringPart {
    /// A literal run (escape-decoded).
    Literal(String),
    /// An interpolation hole — the typed expression (its `ty` drives the
    /// pre-AIR `str_concat`/`itoa`/`str_of_bool` choice). Boxed: a `TypedExpr`
    /// is large, so an unboxed variant skews the `TypedFStringPart` enum size.
    Hole(Box<TypedExpr>),
}

/// HOF prerequisite: payload for closure-call dispatch through a
/// local variable bound to a closure value. AIR's
/// `lower_indirect_call_expr` uses `callee_local` to look up the
/// closure heap pointer in env, loads the table_idx via
/// `CLOSURE_TABLE_IDX_OFFSET`, builds the signature from
/// `callee_ty`, and emits `AirStmt::CallIndirect` with the
/// closure_var as args[0] (env_ptr by N2-HOF convention).
#[derive(Debug, Clone, PartialEq)]
pub struct TypedIndirectCallExpr {
    pub callee_local: String,
    pub callee_ty: Type,
    pub args: Vec<TypedExpr>,
    /// Security/control meaning retained across the effect-handler evidence desugar.  Ordinary
    /// and scoped calls return normally; an abortive effect call transfers control to its handler
    /// even though the runtime implementation uses a return from the evidence closure.
    pub kind: TypedIndirectCallKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypedIndirectCallKind {
    Ordinary,
    ScopedEffect,
    AbortiveEffect,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedDeclassifyExpr {
    pub value: Box<TypedExpr>,
    pub cap: Box<TypedExpr>,
}

/// `declassify_ct(value, cap)` — lowers `@SecretCT → @Secret`.
/// Cap type: `Cap<DeclassifyCT>`, linear (one-use). See spec §3.4.1.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedDeclassifyCtExpr {
    pub value: Box<TypedExpr>,
    pub cap: Box<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedExternCallExpr {
    pub extern_name: String,
    pub args: Vec<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedRegionExpr {
    pub name: String,
    pub limit: Box<TypedExpr>,
    pub body: TypedBlock,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedHandleExpr {
    pub effects: Vec<String>,
    pub body: TypedBlock,
}

/// Effect Handlers (EH3): a typed `perform E.op(args)`. The result type rides
/// the enclosing `TypedExpr.ty` (the operation's return type). Gated before AIR.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedPerformExpr {
    pub effect: String,
    pub op: String,
    pub args: Vec<TypedExpr>,
}

/// Effect Handlers (EH3): a typed clause-form `handle <scrutinee> { .. }`.
/// Gated before AIR.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedClauseHandleExpr {
    pub scrutinee: Box<TypedExpr>,
    pub clauses: Vec<TypedHandleClause>,
}

/// Effect Handlers (EH3): one typed handler clause `E.op(binders) => body`.
/// A body containing `resume` is scoped; a body with none is abortive.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedHandleClause {
    pub effect: String,
    pub op: String,
    pub binders: Vec<String>,
    pub body: TypedBlock,
}

/// Effect Handlers (EH3): a typed `resume <value>` inside a scoped clause body.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedResumeExpr {
    pub value: Box<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedGrantExpr {
    pub cap: Box<TypedExpr>,
    pub body: Box<TypedExpr>,
    pub grant_id: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedBorrowExpr {
    pub inner: Box<TypedExpr>,
    pub mutable: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedCallExpr {
    pub callee: String,
    pub args: Vec<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedIntrinsicExpr {
    pub kind: TypedIntrinsicKind,
    pub args: Vec<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypedIntrinsicKind {
    Alloc,
    Load8,
    Store8,
    /// `u256_from_i64(x)` — construct a `u256` from a non-negative i64: a fresh
    /// 32-byte cell with limb0 = x (zero-extended) and limbs 1-3 = 0. The
    /// minimal U0 constructor; arithmetic/wide-literal construction come later.
    /// `arg` is the lowered AIR type of the operand (for width normalization).
    U256FromI64 {
        arg: crate::air::AirType,
    },
    /// `u256_make(l0, l1, l2, l3)` — build a u256 from four u64 little-endian
    /// limbs. BumpAllocs a fresh 32-byte cell and stores the limbs (E2/E3).
    U256Make,
    /// `u256_limb(v, i)` — read limb `index` (0..=3) of a u256 as u64.
    U256Limb {
        index: u32,
    },
    /// `trap_if(cond)` — `if cond { unreachable }` (the checked-arith revert).
    TrapIf,
    /// `trap()` — unconditional abort (wasm `unreachable`). The explicit
    /// first-class replacement for the `arr[N]`-out-of-bounds-as-trap idiom.
    Trap,
    /// `slot_new::<T>()` — construct an empty `Slot<T>`. The cap-type
    /// name is captured so the AIR / wasm layers know which cap-type
    /// the slot holds.
    SlotNew {
        cap_type: String,
    },
    /// `slot_put(slot, cap)` — mutate the slot in place to hold `cap`.
    /// Runtime-traps if the slot is already full.
    SlotPut,
    /// `slot_take(slot)` — read the cap out and clear the slot.
    /// Runtime-traps if the slot is empty.
    SlotTake,
    /// PR AF / Phase 1.2: `arr.len()` on `Type::Array { size, .. }`.
    /// Carries the compile-time-known `size` so AIR can emit either
    /// a runtime length-load (via `LoadField` offset 0) OR a const
    /// (the implementation emits the LoadField path so the refinement
    /// layer's `LengthOf` queries continue to discharge against the
    /// runtime value; per N16-AF the const-known size is reflected
    /// via the attached refinement on the TypedExpr, not as a
    /// compile-time inlined value).
    ArrayLen {
        size: u32,
    },
    /// PR AF / Phase 1.2: `arr.len()` on `Type::Slice(_)`. AIR
    /// reads `SLICE_LEN_OFFSET` via `slice_len_var` (N14-AF).
    SliceLen,
    /// PR AF / Phase 1.5: `arr.is_empty()` on `Type::Array { size, .. }`.
    /// AIR emits length-load + compare-with-zero; carries `size` to
    /// keep AIR dispatch uniform with `ArrayLen`.
    ArrayIsEmpty {
        size: u32,
    },
    /// PR AF / Phase 1.5: `arr.is_empty()` on `Type::Slice(_)`. AIR
    /// reads slice's len via `slice_len_var` then compares with zero.
    SliceIsEmpty,
    /// Phase-1 completion: `arr.contains(x)` on `Type::Array { .. }` for an
    /// `==`-bearing SCALAR element ({i32,u32,i64,u64,f64,bool}; an `IntLit`
    /// element resolves to i64). AIR emits a wasm-internal scan loop:
    /// `dst=false; load len from header@0; for idx in 0..len { if elem[idx]
    /// == needle { dst=true; break } }`. `elem` (frozen via `lower_type`)
    /// selects the element load width + the equality opcode (I32Eq for
    /// 4-byte {i32,u32,bool}, I64Eq for 8-byte {i64,u64}, F64Eq for f64).
    /// The loop is statically length-bounded (no Alloc/Call) so it is
    /// fuel-exempt. STR elements do NOT use this — they desugar to the
    /// `strings::__sigil_slice_str_contains` content-equality helper.
    ArrayContains {
        elem: crate::air::AirType,
    },
    /// Phase-1 completion: `slc.contains(x)` on `Type::Slice(_)`. Same scan
    /// loop as `ArrayContains` but the base ptr + length come from the slice
    /// fat-pointer header (`slice_data_ptr_var` / `slice_len_var`) and the
    /// element load uses offset 0 (the data ptr already points at element 0).
    SliceContains {
        elem: crate::air::AirType,
    },
    /// Phase-1 completion: `slc.first()` on `Type::Slice(_)`. Slice length is
    /// RUNTIME, so unlike the array fold (`make_first_last_result` builds a
    /// compile-time `Some(arr[k])`/`None`) this needs an AIR runtime branch:
    /// `if len == 0 { None } else { Some(load data[0]) }`, building the
    /// `Option` struct with the EXACT layout of `lower_enum_construct` (tag@0
    /// from the universe Some/None indices, payload@4 width-dispatched).
    /// `elem` (frozen via `lower_type`) is the payload width; works for ANY
    /// element type (the str/record payload is its fat-pointer/Ptr).
    SliceFirst {
        elem: crate::air::AirType,
    },
    /// Phase-1 completion: `slc.last()` on `Type::Slice(_)` — as `SliceFirst`
    /// but loads `data[len-1]` in the non-empty branch.
    SliceLast {
        elem: crate::air::AirType,
    },
    /// PR S1 / N6-S1: `s.len()` on `Type::Str`. AIR loads the
    /// fat-pointer header's `len` field (offset 4) and returns it as
    /// U32. The Str layout is fixed by `STR_LEN_OFFSET` in `air.rs`.
    StrLen,
    /// N-LEX: `s.as_output() -> i64` — pack the str's fat-pointer header into the
    /// forge ABI's output return `(data_ptr << 32) | len`. The sanctioned way for
    /// a pure-SIGIL (inner-ring) tool to emit a built `str` as its byte output:
    /// AIR loads `data_ptr` (u32 @0) + `len` (u32 @4), zero-extends each, and
    /// packs — no FFI (the lexer is inner-ring; FFI is outer-ring), and no raw
    /// `data_ptr` leak to user code (the packed value is only RETURNED, never
    /// dereferenceable in-language). The differential lexer harness reads the
    /// emitted bytes back via the existing positive-return memory-read path.
    StrAsOutput,
    /// PR S1 / N6-S1: `s.is_empty()` on `Type::Str`. AIR loads the
    /// len field then compares with zero, returning Bool.
    StrIsEmpty,
    /// PR S1 / N16-S1: `s.byte_at(i)` on `Type::Str`. AIR loads
    /// `data_ptr` from the header, bounds-checks `i < len` (TrapIf
    /// preceding the byte load — no modular arithmetic), then loads
    /// the byte at `data_ptr + i` and returns it as U32. Explicit
    /// byte access; no UTF-8 boundary check (users opting into byte
    /// access do so deliberately).
    StrByteAt {
        /// Index width frozen at type-check (`lower_type(arg.ty)`). The AIR arm
        /// narrows to U32 from this stamp — type info flows DOWN, never
        /// recovered upward via a locals scan (which also missed params).
        index: crate::air::AirType,
    },
    /// Phase-3 / integer width conversion: `n.as_i32()` / `.as_u32()` /
    /// `.as_i64()` / `.as_u64()` on any machine-integer receiver. `from` is the
    /// receiver's frozen AIR width, `to` is the target. AIR dispatches on the
    /// pair: 8→4 narrow = `WrapI64` (WRAPPING/truncate); u32→8 widen =
    /// `ExtendU32` (zero-fill); i32→8 widen = `SignExtendI32` (sign-fill);
    /// same-wasm-rep reinterpret (i32↔u32, i64↔u64) or identity = a typed copy.
    /// Pure + bounded (no ring/cap implications). Result type is `to`.
    IntConvert {
        from: crate::air::AirType,
        to: crate::air::AirType,
    },
    /// PR S(strings) / CF-S1: `s.substr(start, end) -> str` on `Type::Str`.
    /// A zero-copy borrowed sub-view. AIR loads the receiver's
    /// `data_ptr`/`len`, bounds-checks `0 <= start <= end <= len` in the
    /// FULL i64 domain (four `TrapIf`s BEFORE the alloc — no u32-wrap can
    /// truncate a ≥2³² or negative index into a valid-but-wrong window),
    /// then `BumpAlloc`s a fresh 8-byte str header
    /// `[data_ptr = recv_data_ptr + start, len = end - start]` pointing into
    /// the same bytes. Effect-free, like a string literal.
    StrSubstr {
        /// Start/end index widths frozen at type-check (`lower_type`). The AIR
        /// arm widens each to I64 from these stamps — no locals scan.
        start: crate::air::AirType,
        end: crate::air::AirType,
    },
    /// Owned-strings PR-1 / ET-1: `str_from_raw(ptr, len) -> str` — wrap a raw
    /// `(data_ptr, len)` pair into a FRESH `str` fat-pointer header. The PRIVATE
    /// keystone of owned-string construction: the stdlib `string.sigil` builders
    /// (`str_concat`/`str_join`/`str_itoa`) `alloc` a buffer, fill it via
    /// `store8`, then wrap it here. UNSAFE in the wrong hands — a lying `len`
    /// forges an out-of-bounds view that the `byte_at`/`substr` bounds-checks
    /// trust — so a compile-time module gate (T257) rejects any caller outside
    /// module `string`. AIR mirrors the string-literal header lowering: BumpAlloc
    /// 8 bytes, store `data_ptr` (u32 @0) and `len` (u32 @4); effect-free like
    /// `StrSubstr` (the caller's `! { Alloc }` covers the buffer). The arg widths
    /// are frozen here (`lower_type`) so AIR narrows to U32 without a locals scan.
    StrFromRaw {
        ptr: crate::air::AirType,
        len: crate::air::AirType,
    },
    /// Phase 2H §3.5: `ct_eq(a, b)` — branch-free constant-time equality.
    /// Both operands and the returned bool are `@SecretCT`-compatible.
    /// Lowered to `(a ^ b) == 0` via I64Xor + I64Eqz; never emits any
    /// conditional branch.
    CtEq,
    /// Phase 2H §3.5: `ct_select(cond, t, f)` — branch-free select.
    /// Lowered to `f ^ ((t ^ f) & -c)` where `c` is `cond as i64`; never
    /// to Wasm `select` (which some backends compile to a CPU branch).
    CtSelect,
    /// Phase 2H §3.5: `ct_lt(a, b)` — branch-free signed less-than.
    /// Lowered to `((a - b) >> 63) & 1`; the shift amount is a constant
    /// so the operation is data-independent on every supported CPU.
    CtLt,
    /// `vec_store(base, index, bound, val: T)` — stdlib `Vec<T>` element
    /// write. The element `AirType` is frozen here at type-check from the
    /// concrete `val` argument (never a turbofish), so monomorphization
    /// cannot leak a generic param into a wrong store width. Lowers to a
    /// `bound` `TrapIf` (`index >= bound`) + a header-less `StoreDynamic`
    /// over uniform 8-byte slots. The `bound` is the caller's `cap` (writes
    /// target the allocated slot at `index == len < cap`).
    VecStore {
        elem: crate::air::AirType,
    },
    /// `vec_load(base, index, bound, witness: Vec<T>) -> T` — element read.
    /// Element type frozen from the `Vec<T>` witness's type-arg (mirrors
    /// `slot_take`'s return-from-arg). Lowers to a `bound` `TrapIf` + a
    /// header-less `LoadDynamic`. The `bound` is the caller's `len` (reads
    /// only initialized slots `[0, len)`).
    VecLoad {
        elem: crate::air::AirType,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedEnumConstructExpr {
    pub enum_name: String,
    pub variant_index: u32,
    pub fields: Vec<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedResultCtorExpr {
    pub is_ok: bool,
    pub value: Box<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedTryExpr {
    pub value: Box<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedSendExpr {
    pub target: String,
    pub actor: String,
    pub handler: String,
    pub args: Vec<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedAskExpr {
    pub target: String,
    pub actor: String,
    pub handler: String,
    pub args: Vec<TypedExpr>,
    pub timeout: Box<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedSpawnExpr {
    pub actor: String,
    pub args: Vec<TypedExpr>,
    pub supervision: Option<TypedSupervisionStrategy>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypedSupervisionStrategy {
    Stop,
    Restart { max_restarts: u32 },
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedBinaryExpr {
    pub lhs: Box<TypedExpr>,
    pub op: BinaryOp,
    pub rhs: Box<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedRecordConstructExpr {
    pub type_name: String,
    pub fields: Vec<(String, TypedExpr)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedFieldAccessExpr {
    pub object: Box<TypedExpr>,
    pub field: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedCapRestrictExpr {
    pub cap: String,
    pub restriction_name: String,
    pub restriction_mask: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedCapSplitExpr {
    pub cap: String,
    pub amount: Box<TypedExpr>,
}

/// `cap.draw(amount)` — non-consuming sibling of CapSplit. See
/// `ast::CapDrawExpr` doc for axis-1 motivation.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedCapDrawExpr {
    pub cap: String,
    pub amount: Box<TypedExpr>,
}

/// `mint <CapType>[(deadlines)] for <target>` — the capabilities-as-values
/// constructor. Lowers to `AirStmt::CapMint` (a sanctioned cap source that
/// sidesteps the C001 forgery gate). `authority_var`, when `Some`, names the
/// in-scope minting authority (`&cap <Authority>`) that gated this mint;
/// `None` before the gate (PR-M2) is wired.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedMintExpr {
    pub cap_name: String,
    pub params: Vec<i64>,
    pub authority_var: Option<String>,
    pub target: Box<TypedExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedArrayLitExpr {
    pub elements: Vec<TypedExpr>,
    pub elem_type: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedIndexExpr {
    pub array: Box<TypedExpr>,
    pub index: Box<TypedExpr>,
    pub elem_type: Type,
    /// Refinement-typed array bounds (v1): `true` iff this is a *constant*
    /// index proven in-bounds by a Z3-FREE compile-time comparison — `index`
    /// is a literal `k`, `array.ty` is `Array { size: N }`, and `0 <= k < N`.
    /// When `true`, AIR (`index_base_and_bounds`, Array branch) elides the
    /// runtime bounds `TrapIf`. TWO `true`-setters, both Z3-FREE: the literal constant compare, and the RF-M2 range-loop fact channel (an immutable, never-rebound loop var whose `[0, K)` interval fits the static `N`). Each lives in `infer_index_expr`: `infer_index_expr`'s
    /// constant comparison (SC-2 / C1). NEVER set from a Z3 verdict — Z3 stays
    /// out of the memory-safety TCB (SC-6). Default `false` ⇒ wasm byte-identical.
    pub bounds_proven: bool,
}

/// PR AF: `array[start..end]` slice operator typed form. `elem_type`
/// is the slice's element type (the receiver's element type). Both
/// `start` and `end` are optional in the AST; the type-checker
/// always materializes them to concrete TypedExpr values at AIR
/// time (defaulting `start` → IntLit(0), `end` → `array.len()`).
#[derive(Debug, Clone, PartialEq)]
pub struct TypedSliceExpr {
    pub array: Box<TypedExpr>,
    pub start: Option<Box<TypedExpr>>,
    pub end: Option<Box<TypedExpr>>,
    pub elem_type: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedForInStmt {
    pub var: String,
    pub elem_type: Type,
    pub iterable: TypedExpr,
    pub body: Vec<TypedStmt>,
}

/// `for v in start..end { body }` — the exclusive i64 range loop. `start` and
/// `end` are each evaluated exactly ONCE (the AIR arm lowers them into the loop
/// pre-header); `v` is bound IMMUTABLY at type `i64` (never inserted into the
/// block's `mutables`, so reassignment is T042). The immutability is
/// load-bearing: it is what later lets the range serve as a compile-time bounds
/// fact for `arr[v]` elision without any flow tracking.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedForRangeStmt {
    pub var: String,
    pub start: TypedExpr,
    pub end: TypedExpr,
    pub body: Vec<TypedStmt>,
    pub span: Span,
}

#[cfg(test)]
mod utf8_invariant_tests {
    use super::TypedIntrinsicKind;
    use crate::air::AirType;

    /// ET-3 (UTF-8 boundary enforcement) closed-set gate. The `substr` boundary
    /// trap makes "every `str` is valid UTF-8" an ENFORCED invariant — but only
    /// because every str-PRODUCING intrinsic preserves validity. Those producers
    /// are a CLOSED set of exactly two: `StrSubstr` (now boundary-trapped) and
    /// `StrFromRaw` (T257-private + grep-quarantined to `string.sigil`'s
    /// copy-only builders). String LITERALS (validated by the lexer) are
    /// `TypedExprKind::Literal`, not an intrinsic. This match is EXHAUSTIVE (no
    /// `_`): a new `TypedIntrinsicKind` variant breaks compilation here, forcing
    /// you to classify it — and if it yields a `Type::Str`, to prove it preserves
    /// UTF-8 validity before flipping it to `true`.
    fn produces_str(k: &TypedIntrinsicKind) -> bool {
        match k {
            TypedIntrinsicKind::StrSubstr { .. } | TypedIntrinsicKind::StrFromRaw { .. } => true,
            TypedIntrinsicKind::Alloc
            | TypedIntrinsicKind::Load8
            | TypedIntrinsicKind::Store8
            | TypedIntrinsicKind::SlotNew { .. }
            | TypedIntrinsicKind::SlotPut
            | TypedIntrinsicKind::SlotTake
            | TypedIntrinsicKind::ArrayLen { .. }
            | TypedIntrinsicKind::SliceLen
            | TypedIntrinsicKind::ArrayIsEmpty { .. }
            | TypedIntrinsicKind::SliceIsEmpty
            // Phase-1 completion: `.contains` yields `bool`; slice
            // `.first()`/`.last()` yield `Option<T>` (a Named type) — none
            // produce a bare `Type::Str`, so none affect the UTF-8 invariant.
            | TypedIntrinsicKind::ArrayContains { .. }
            | TypedIntrinsicKind::SliceContains { .. }
            | TypedIntrinsicKind::SliceFirst { .. }
            | TypedIntrinsicKind::SliceLast { .. }
            | TypedIntrinsicKind::StrLen
            | TypedIntrinsicKind::StrAsOutput
            | TypedIntrinsicKind::StrIsEmpty
            | TypedIntrinsicKind::StrByteAt { .. }
            // Phase-3 int width conversion yields a machine integer, never a str.
            | TypedIntrinsicKind::IntConvert { .. }
            | TypedIntrinsicKind::CtEq
            | TypedIntrinsicKind::CtSelect
            | TypedIntrinsicKind::CtLt
            | TypedIntrinsicKind::VecStore { .. }
            // u256 PR-U0/U1: u256 intrinsics yield u256/u64/unit, never a `str` —
            // none affect the UTF-8 invariant.
            | TypedIntrinsicKind::U256FromI64 { .. }
            | TypedIntrinsicKind::U256Make
            | TypedIntrinsicKind::U256Limb { .. }
            | TypedIntrinsicKind::TrapIf
            // `trap()` yields `Type::Unit`, never a `str`.
            | TypedIntrinsicKind::Trap
            | TypedIntrinsicKind::VecLoad { .. } => false,
        }
    }

    #[test]
    fn str_producing_intrinsics_are_closed() {
        let t = AirType::I64;
        assert!(produces_str(&TypedIntrinsicKind::StrSubstr {
            start: t,
            end: t
        }));
        assert!(produces_str(&TypedIntrinsicKind::StrFromRaw {
            ptr: t,
            len: t
        }));
        // Representative non-producers: str-CONSUMING (→ i64) and unrelated.
        assert!(!produces_str(&TypedIntrinsicKind::StrByteAt { index: t }));
        assert!(!produces_str(&TypedIntrinsicKind::Alloc));
    }

    #[test]
    fn tool_main_security_consumers_share_the_typed_policy() {
        let consumers = [
            (
                "air.rs",
                include_str!("air.rs"),
                ".effective_return_taint()",
            ),
            (
                "taint_check.rs",
                include_str!("taint_check.rs"),
                ".effective_return_taint()",
            ),
            (
                "formal.rs",
                include_str!("formal.rs"),
                ".effective_return_taint()",
            ),
            (
                "effect_desugar.rs",
                include_str!("effect_desugar.rs"),
                ".is_tool_main_entry()",
            ),
        ];
        let forbidden_copies = [
            "name == \"tool_main\"",
            "name.ends_with(\"::tool_main\")",
            "export_name == \"tool_main\"",
            "export_name.ends_with(\"__tool_main\")",
        ];

        for (path, source, shared_call) in consumers {
            assert!(
                source.contains(shared_call),
                "{path} stopped consuming the shared TypedFunction tool_main policy"
            );
            for forbidden in forbidden_copies {
                assert!(
                    !source.contains(forbidden),
                    "{path} duplicated the tool_main identity predicate with `{forbidden}`"
                );
            }
        }
    }
}
