//! The surface AST -- the parser's output and the single shape authority
//! for SIGIL's grammar: `Program` -> `Module` -> `Item` -> `Stmt`/`Expr`,
//! plus `TypeExpr`, patterns, and the `TaintLabel`/`Mutability`/`Ring`
//! policy axes. Data definitions plus small policy predicates and row
//! walkers; no diagnostics are constructed in this file.
//!
//! Invariants owned here:
//! - `TaintLabel`'s declaration order IS the flow lattice (Public <
//!   Internal < Secret < SecretCT rides the derived `Ord`: `lub` is
//!   `max`, `can_flow_to` is `<=`). Reordering variants silently
//!   rewrites the information-flow policy.
//! - `Item::name()` returns `None` for `ImplDef`/`StateDef` on purpose:
//!   both attach to an existing type's name, and returning it would trip
//!   name resolution's duplicate-definition check against the type they
//!   extend.
//! - `collect_type_row_names` opens with a full-field `TypeExpr`
//!   destructure (no `..`) -- the walker fence: growing `TypeExpr` breaks
//!   compilation until every row walker handles the new field; the census
//!   half is `tests/row_position_shape_census.rs`.
//!
//! This tree is also the oracle side of the self-hosted parser
//! differential (docs/specs/parser-in-sigil.md;
//! `crates/sigil-runtime/tests/parser_differential.rs`), whose total
//! kind-maps refuse to compile until a new AST variant is mapped -- so
//! growing `Item`/`Stmt`/`Expr` is never a silent act.

use crate::span::Span;

/// Maximum tuple arity (ET-2 Boring Limit). A tuple with more than this many
/// elements is rejected at parse time — bounding mangle-name blowup and
/// registry pressure. Enforced for tuple literals, tuple types, and the
/// `let (..)` destructure name list.
pub const MAX_TUPLE_ARITY: usize = 12;

/// HKT (EX-5 Boring Limit): the maximum arity of a higher-kinded type-parameter
/// kind — the arrow count in `* -> * -> …`. Anchored to the de-facto maximum
/// type-constructor arity across stdlib+selfhost (`Result<T, E>`, `Map<K, V>` =
/// 2). A kind with `> MAX_KIND_ARITY` arrows is rejected at parse time (P027).
pub const MAX_KIND_ARITY: usize = 2;

/// Four-level taint lattice: Public < Internal < Secret < SecretCT.
/// Data at level L can flow to any level ≥ L without declassification.
///
/// `SecretCT` adds an operational constraint beyond confidentiality: any
/// construct whose execution time, memory access pattern, or instruction
/// trace would depend on `SecretCT` data is rejected at compile time.
/// See `docs/specs/secret-ct.md` for the full discipline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum TaintLabel {
    #[default]
    Public,
    Internal,
    Secret,
    SecretCT,
}

impl TaintLabel {
    /// Least upper bound — taint of combining two values.
    pub fn lub(self, other: Self) -> Self {
        std::cmp::max(self, other)
    }

    /// Can data at this taint level flow to a sink at target level?
    /// Public → anything: OK. Secret → Public: REJECTED.
    pub fn can_flow_to(self, target: Self) -> bool {
        self <= target
    }

    /// Is this taint at or above the constant-time discipline threshold?
    /// Used by the taint checker's CT pass to gate branching, indexing,
    /// arithmetic, allocation, FFI, and actor-message constructs on
    /// `@SecretCT` operands.
    pub fn is_ct(self) -> bool {
        self >= TaintLabel::SecretCT
    }
}

/// Mutation authority of a function parameter — the `@ReadOnly` / `@Mut`
/// capability axis (mutation-as-capability epic). ORTHOGONAL to `TaintLabel`:
/// a param may carry both (`@SecretCT @ReadOnly`), each checked independently.
///
/// - `Default` — a bare param. FROZEN since the H5 default-flip (DEF-1): the callee
///   may not mutate through it or leak it to a mutable destination, exactly like
///   `@ReadOnly`. `@Mut` is the opt-up to mutability.
/// - `ReadOnly` — the explicit frozen marker (now the same freeze a bare param
///   gets): write-through is rejected (T251), the value may not escape to a mutable
///   destination (T253), nor co-alias a `@Mut` arg in one call (T255). Fully static.
/// - `Mut` — the explicit-mutable marker and, post-flip, the ONLY mutable state.
///   NEVER collapsed into `Default` (NC-4) — the bit the flip pivots on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Mutability {
    #[default]
    Default,
    ReadOnly,
    Mut,
}

impl Mutability {
    /// Mutation-as-capability: does this state FREEZE the parameter — i.e. make the
    /// write (T251) / escape (T253) / exclusivity (T255) gates restrict mutation
    /// through it? Since DEF-1 (the H5 default-flip) a bare param (`Default`) IS
    /// frozen, exactly like `@ReadOnly`; only an explicit `@Mut` is mutable. Every
    /// gate site (the `check_function_block` readonly seed, the call-arg/method
    /// escape gates, the exclusivity partition) routes its "is this param
    /// restricted?" check through this ONE predicate, so the flip extended all of
    /// them by changing only this line.
    ///
    /// DEF-1 became soundly enforceable once DEF-2c (`docs/specs/exclusivity.md`)
    /// closed AG-1's call-site core (T255). NC-4 keeps `@Mut` represented distinctly
    /// so the flip never has to disambiguate a collapsed bare/`@Mut`.
    pub fn is_frozen(self) -> bool {
        matches!(self, Mutability::ReadOnly | Mutability::Default)
    }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Program {
    pub modules: Vec<Module>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Ring {
    #[default]
    Inner,
    Outer,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub name: String,
    pub ring: Ring,
    pub trusted: bool,
    pub visibility: Visibility,
    pub items: Vec<Item>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Visibility {
    Public,
    #[default]
    Private,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    UseDecl(UseDecl),
    ConstDef(ConstDef),
    FnDef(FnDef),
    ActorDef(ActorDef),
    CapTypeDef(CapTypeDef),
    RecordDef(RecordDef),
    EnumDef(EnumDef),
    ImplDef(ImplDef),
    EffectDecl(EffectDecl),
    ExternFnDecl(ExternFnDecl),
    TraitDef(TraitDef),
    /// PR-E4: a type alias `type Name = TypeExpr;` — a substitutive name for an
    /// existing type, resolved at type-resolution (no new type-system feature).
    TypeAlias(TypeAliasDef),
    /// Typestate (Epic 1): a `state Name { A, B }` declaration — the closed set of
    /// protocol-state markers for the carrier record `Name<@S>`. Type-level only;
    /// emits no code. Like `ImplDef`, it introduces NO new top-level type name
    /// (`name()` is `None`) — it attaches state metadata to the same-named record.
    StateDef(StateDef),
}

/// PR-E4: `type Name = TypeExpr;`. Substitutive only — `Name` resolves to `body`'s
/// resolved `Type` at every use site (recursion-guarded against cyclic aliases).
#[derive(Debug, Clone, PartialEq)]
pub struct TypeAliasDef {
    pub visibility: Visibility,
    pub name: String,
    pub body: TypeExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EffectDecl {
    pub name: String,
    /// Effect Handlers (EH0): the effect's typed OPERATIONS. Empty `Vec` = a
    /// bare *marker* effect (the legacy `effect Name;` form). A non-empty list
    /// makes the effect operation-bearing: bare `handle Name { .. }` becomes
    /// illegal (EH010) and the clause form is required. An operation's
    /// `return_type` is the *resumed-value* type (the forward-compat seam); an
    /// abortive operation declares `-> never`.
    pub ops: Vec<EffectOp>,
    pub span: Span,
}

/// Effect Handlers (EH0): one typed operation of an effect — a
/// `fn`-signature-without-body, modelled on [`TraitMethodSig`]. Operations are
/// not generic in v1 (no type params). The `return_type` is the value a
/// `perform` of this operation evaluates to (the resumed value); `None` means
/// unit, `-> never` marks an abortive-only operation.
#[derive(Debug, Clone, PartialEq)]
pub struct EffectOp {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub span: Span,
}

/// Typestate (Epic 1): `state Name { A, B }`. `name` is the protocol — shared with
/// the carrier record `record Name<@S>`; `states` is the closed, ordered set of
/// zero-size state-marker names. Resolution maps an arg in a stateful nominal's
/// state position to `Type::StateMarker`, gating membership against `states` (ST-5).
#[derive(Debug, Clone, PartialEq)]
pub struct StateDef {
    pub visibility: Visibility,
    pub name: String,
    pub states: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExternFnDecl {
    pub abi: String,
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub ret_taint: Option<TaintLabel>,
    pub effects: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RegionExpr {
    pub name: String,
    pub limit: Box<Expr>,
    pub body: Block,
    pub span: Span,
}

/// A trait declaration — the CONTRACT a `T: TraitName` bound is checked
/// against. v1 (the trait Wall) carries method SIGNATURES only (no default
/// bodies), no trait-level type params, and no super-traits (heuristic 7;
/// `super_traits` is reserved for a later increment and always empty here).
#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    pub visibility: Visibility,
    pub name: String,
    pub methods: Vec<TraitMethodSig>,
    pub super_traits: Vec<String>,
    pub span: Span,
}

/// A single required method on a trait: a signature with no body. Param 0 is
/// the receiver `self`; a `Self` named-type in any param or the return resolves
/// to the implementing type at satisfaction-check time (PR-3b).
#[derive(Debug, Clone, PartialEq)]
pub struct TraitMethodSig {
    pub name: String,
    /// Method-level type parameters (HK2): `fn fmap<A, B>(…)`. Empty for an
    /// ordinary monomorphic trait method (`fn hash(self: Self) -> i64`). A
    /// higher-kinded trait like `Functor` needs these so `fmap` is generic in
    /// its element types.
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub span: Span,
}

impl Item {
    pub fn name(&self) -> Option<&str> {
        match self {
            Self::UseDecl(_) => None,
            Self::ConstDef(def) => Some(&def.name),
            Self::FnDef(def) => Some(&def.name),
            Self::ActorDef(def) => Some(&def.name),
            Self::CapTypeDef(def) => Some(&def.name),
            Self::RecordDef(def) => Some(&def.name),
            Self::EnumDef(def) => Some(&def.name),
            // SIGIL Complete v0 / Phase 6: impl blocks ATTACH methods
            // to an existing named type (record, enum, cap-type) rather
            // than introducing a new top-level name. Returning the
            // type_name here would trigger N002 (duplicate definition)
            // against the record/enum being impl'd against. Returning
            // None lets name resolution skip the duplicate check for
            // impl blocks; downstream `collect_function_sigs` iterates
            // `module.items` directly and handles `Item::ImplDef`
            // explicitly without depending on the name-resolved Vec.
            Self::ImplDef(_) => None,
            Self::EffectDecl(def) => Some(&def.name),
            Self::ExternFnDecl(def) => Some(&def.name),
            // A trait introduces a top-level name (like a record/enum) so a
            // `T: TraitName` bound can resolve it and duplicate names are caught.
            Self::TraitDef(def) => Some(&def.name),
            // PR-E4: an alias introduces a top-level type name; duplicate-name
            // checking + registration both want it.
            Self::TypeAlias(def) => Some(&def.name),
            // Typestate: a `state Name {…}` decl attaches to the same-named record
            // (like ImplDef) — returning None avoids an N002 duplicate against the
            // carrier record `Name<@S>`. The universe collects it via direct
            // `module.items` iteration.
            Self::StateDef(_) => None,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            Self::UseDecl(item) => item.span,
            Self::ConstDef(item) => item.span,
            Self::FnDef(item) => item.span,
            Self::ActorDef(item) => item.span,
            Self::CapTypeDef(item) => item.span,
            Self::RecordDef(item) => item.span,
            Self::EnumDef(item) => item.span,
            Self::ImplDef(item) => item.span,
            Self::EffectDecl(item) => item.span,
            Self::ExternFnDecl(item) => item.span,
            Self::TraitDef(item) => item.span,
            Self::TypeAlias(item) => item.span,
            Self::StateDef(item) => item.span,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Path {
    pub segments: Vec<String>,
    pub type_args: Vec<TypeExpr>,
    pub span: Span,
}

impl Path {
    pub fn display_name(&self) -> String {
        self.segments.join("::")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UseDecl {
    pub visibility: Visibility,
    pub path: Path,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConstDef {
    pub visibility: Visibility,
    pub name: String,
    pub ty: TypeExpr,
    pub value: Literal,
    pub span: Span,
}

/// A generic type-parameter declaration — `T`, or (from the trait epic's
/// bound-parsing PR onward) `T: Hash + Eq`. `bounds` lists the trait names the
/// parameter is constrained by; an empty `bounds` is the unbounded common case.
/// In this PR `bounds` is ALWAYS empty (a representation change only); the
/// `:`-bound parse branch and bound enforcement land in later PRs.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeParam {
    pub name: String,
    pub bounds: Vec<String>,
    /// The parameter's KIND (HKT epic). `Star` for an ordinary value type
    /// parameter (`T`, `T: Hash`); `Constructor { arity }` for a higher-kinded
    /// parameter `<F: * -> *>`. Defaults to `Star` everywhere except the
    /// `parse_kind` branch of `parse_type_params`.
    pub kind: ParamKind,
    pub span: Span,
}

/// The KIND of a type parameter (HKT epic). `Star` is the ordinary `*`-kinded
/// value type parameter (`T`, `T: Hash`); `Constructor { arity }` is a
/// higher-kinded parameter `<F: * -> *>` (arity 1) / `<M: * -> * -> *>`
/// (arity 2), where `arity` is the kind's arrow count (`>= 1`, `<=
/// MAX_KIND_ARITY`). See docs/specs/hkt-in-sigil.md.
#[derive(Debug, Clone, PartialEq)]
pub enum ParamKind {
    Star,
    Constructor {
        arity: usize,
    },
    /// Typestate (Epic 1): a STATE-kinded parameter `<@S>` — a phantom index
    /// ranging over a protocol's closed set of zero-size state markers. Resolved
    /// to `Type::StateMarker(_)` as a `Named` arg; load-bearing for checking,
    /// erased before AIR. See docs/specs/typestate-in-sigil.md.
    State,
}

/// The bare names of a type-parameter list. The trait epic keeps the
/// `universe` / typed representations name-only — bounds live on the AST and are
/// enforced there — so this is the conversion applied at every AST→universe
/// boundary (record/enum/impl sig collection, generic-fn monomorphization).
pub fn type_param_names(params: &[TypeParam]) -> Vec<String> {
    params.iter().map(|p| p.name.clone()).collect()
}

/// Collect every effect-name occurrence in TYPE-position rows reachable
/// through a type annotation — the `FnTypeExpr.effects` lists at any depth
/// (fn params/returns, array elems, tuple elems, generic args; the same
/// recursive shape as `validate_fn_type_effect_rows`). Names are appended in
/// source order; callers filter for the subset they care about.
///
/// WALKER FENCE (Phase 4 sweep): the destructure below is exhaustive — NO
/// `..` — so growing `TypeExpr` breaks this function's compilation until the
/// new field is consciously handled here AND in the sibling walkers
/// (`validate_fn_type_effect_rows`, the validators' shape walks, `overlay_rows`)
/// and in the row-position shape census
/// (`tests/row_position_shape_census.rs`). The sweep found the parser
/// silently DROPPING slice-element structure, which made rows invisible to
/// every walker; the fence + census keep that class dead. `ref_kind` needs no
/// recursion: it is a same-node MODIFIER (the modified element's structure
/// lives in this node's own `fn_type`/`array_type`/`tuple_type`/`path`).
pub fn collect_type_row_names<'a>(ty: &'a TypeExpr, out: &mut Vec<&'a str>) {
    let TypeExpr {
        path,
        ref_kind: _,
        deadline: _,
        span: _,
        fn_type,
        array_type,
        tuple_type,
    } = ty;
    if let Some(ft) = fn_type {
        if let Some(names) = &ft.effects {
            out.extend(names.iter().map(String::as_str));
        }
        for p in &ft.params {
            collect_type_row_names(p, out);
        }
        collect_type_row_names(&ft.return_type, out);
        return;
    }
    if let Some(arr) = array_type {
        collect_type_row_names(&arr.elem, out);
        return;
    }
    if let Some(elems) = tuple_type {
        for e in elems {
            collect_type_row_names(e, out);
        }
        return;
    }
    for arg in &path.type_args {
        collect_type_row_names(arg, out);
    }
}

/// The EFFECT-kinded ("row variable") subset of a fn's type-parameter list
/// (roadmap Phase 4, kind-by-use): a binder counts as effect-kinded when its
/// name occurs in any effect-row position of the SIGNATURE — the declared row
/// (`FnDef.effects`) or any `FnTypeExpr.effects` reachable through the
/// param/return annotations. Order-preserving over `type_params`.
///
/// Kind-by-use is only unambiguous because `validate_effect_row_params`
/// hard-errors the ambiguous shapes first (a name used in BOTH row and type
/// position, a binder shadowing a registered effect, duplicate binder names) —
/// downstream consumers (monomorphization, cert collection) may assume the
/// classification is total and disjoint.
pub fn effect_row_param_names(def: &FnDef) -> Vec<String> {
    if def.type_params.is_empty() {
        return Vec::new();
    }
    let mut occ: Vec<&str> = Vec::new();
    if let Some(names) = &def.effects {
        occ.extend(names.iter().map(String::as_str));
    }
    for p in &def.params {
        collect_type_row_names(&p.ty, &mut occ);
    }
    if let Some(ret) = &def.return_type {
        collect_type_row_names(ret, &mut occ);
    }
    def.type_params
        .iter()
        .filter(|tp| occ.iter().any(|n| *n == tp.name))
        .map(|tp| tp.name.clone())
        .collect()
}

/// The TYPE-kinded complement of [`effect_row_param_names`], order-preserving.
/// This is the list every POSITIONAL consumer on the generic call path must
/// use (turbofish mapping, unify/T150 accounting, `check_bounds`' zip, the
/// subst zip) — zipping the full binder list against type-only concrete args
/// silently misaligns bounds and bindings once an effect-kinded binder exists.
pub fn type_kinded_param_names(def: &FnDef) -> Vec<String> {
    let rows = effect_row_param_names(def);
    def.type_params
        .iter()
        .filter(|tp| !rows.contains(&tp.name))
        .map(|tp| tp.name.clone())
        .collect()
}

/// The higher-kinded subset of a type-parameter list, as `(name, arity)` pairs —
/// the binders that `resolve_type_expr` must treat as `HktVar`/`HktApp` heads
/// (threaded as `in_scope_hkt`). `Star`-kinded params are ordinary generics and
/// are excluded.
pub fn hkt_params(params: &[TypeParam]) -> Vec<(String, usize)> {
    params
        .iter()
        .filter_map(|p| match p.kind {
            ParamKind::Constructor { arity } => Some((p.name.clone(), arity)),
            ParamKind::Star | ParamKind::State => None,
        })
        .collect()
}

/// The STATE-kinded subset of a type-parameter list, as bare names — the binders
/// that `resolve_type_expr_kinded` must treat as `StateMarker` heads (threaded as
/// `in_scope_states`). `Star`/`Constructor` params are excluded. Typestate (Epic 1).
pub fn state_params(params: &[TypeParam]) -> Vec<String> {
    params
        .iter()
        .filter_map(|p| match p.kind {
            ParamKind::State => Some(p.name.clone()),
            ParamKind::Star | ParamKind::Constructor { .. } => None,
        })
        .collect()
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDef {
    pub visibility: Visibility,
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub ret_taint: Option<TaintLabel>,
    /// `-> T @Flow` — the return label follows the `@Flow` arguments rather
    /// than being fixed. Legal only when at least one parameter is `@Flow`
    /// (P021 otherwise): with no `@Flow` input there is nothing for the
    /// result to follow. Mutually exclusive with `ret_taint`.
    pub ret_flow: bool,
    /// Effect row: None = inner ring (no annotation), Some([]) = pure, Some(["Alloc"]) = effectful
    pub effects: Option<Vec<String>>,
    pub body: Block,
    pub span: Span,
    /// Optional `where <param> RELOP <literal>` contract. The parameter must
    /// belong to this function and have type `i64`. Generic functions reject
    /// parameter refinements with T226; closures cannot express this grammar.
    pub param_refinements: Vec<RefinementClause>,
    /// Optional `where @ RELOP <literal>` return contract. The return type
    /// must be `i64`; generic functions and closures share the exclusions above.
    pub return_refinement: Option<RefinementClause>,
    /// Direct `(longer_lived, shorter_lived)` edges from
    /// `where region(a): region(b)`. No transitive closure is inferred.
    pub region_outlives: Vec<(String, String)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ActorDef {
    pub visibility: Visibility,
    pub name: String,
    pub is_entry: bool,
    pub state_fields: Vec<Field>,
    pub init: Option<InitBlock>,
    pub handlers: Vec<Handler>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct InitBlock {
    pub params: Vec<Param>,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Handler {
    pub message_name: String,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CapTypeDef {
    pub visibility: Visibility,
    pub name: String,
    pub authorities: Vec<String>,
    /// Parametric caps (Wall 2 → Wall 3): each entry is one `i64`-typed
    /// type parameter, in positional order. Empty Vec means non-
    /// parametric. Single-element Vec is the legacy Wall 2 form;
    /// multi-element is the Wall 3 form. All parameters must be `i64`
    /// (T198 fires on declaration if not).
    pub params: Vec<CapTypeParam>,
    /// Capabilities-as-values: the minting policy. `None` (the default for
    /// every existing `cap type`) means this cap type is **not mintable** —
    /// `mint` of it is a hard T272 error (fail-closed). `Some` names the
    /// authority cap a `mint` site must hold (and optionally the specific
    /// authority bit). Declared via `cap type Foo mintable_by Admin[::bit] {…}`.
    pub mintable_by: Option<MintPolicy>,
    pub span: Span,
}

/// The minting policy of a `cap type` (capabilities-as-values). To `mint` a
/// cap of this type, the mint site must hold a `&cap <authority_cap>` whose
/// current authority mask carries `authority_name` (when `Some`).
#[derive(Debug, Clone, PartialEq)]
pub struct MintPolicy {
    pub authority_cap: String,
    pub authority_name: Option<String>,
    pub span: Span,
}

/// Type-level parameter declaration on a parametric cap type.
/// Wall 2 → Wall 3: supports `i64` parameters at every position.
#[derive(Debug, Clone, PartialEq)]
pub struct CapTypeParam {
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordDef {
    pub visibility: Visibility,
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub fields: Vec<Field>,
    /// Optional single-clause record refinement. The type checker admits
    /// supported `i64`/`u256` literal and `i64` cross-field shapes.
    pub refinements: Vec<RefinementClause>,
    pub span: Span,
}

/// One comparison on a record field. The parser validates names; declaration
/// validation checks types and RHS shape. `LengthOf` resolves to a literal for
/// fixed arrays, while `Field` routes to the two-value query.
#[derive(Debug, Clone, PartialEq)]
pub struct RefinementClause {
    pub field: String,
    pub op: RefinementOp,
    pub rhs: RefinementRhs,
    pub span: Span,
}

/// Supported refinement RHS shapes. Literal and resolved `LengthOf` clauses use
/// the single-value query; `Field` uses the cross-field query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefinementRhs {
    /// Integer literal RHS. Steps 1+3 single-variable Z3 path.
    Literal(i64),
    /// A wide record-field bound as four little-endian limbs. Parameter,
    /// return, and variant refinements remain `i64`-only.
    LiteralWide([u64; 4]),
    /// Reference to a sibling `i64` field in the same record.
    Field(String),
    /// `<field>.length()` for a directly owned fixed array. Validation
    /// resolves it to `Literal(size as i64)` before query construction.
    LengthOf(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefinementOp {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
    Ne,
}

/// A concrete value for refinement discharge. Keeping wide `u256` literals in a
/// distinct limb-carrying variant makes lossy narrowing unreachable in the encoder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefValue {
    Narrow(i64),
    Wide([u64; 4]),
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumDef {
    pub visibility: Visibility,
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub variants: Vec<EnumVariant>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumVariant {
    pub name: String,
    /// Payload fields are all named or all positional; mixed forms emit T223.
    pub fields: Vec<EnumVariantField>,
    /// Refinements on fully named payloads. Positional payload refinements emit T223.
    pub refinements: Vec<RefinementClause>,
    pub span: Span,
}

/// Wall 4 Step 6: one payload field of an enum variant.
///
/// `name: Some(ident)` for the named form `V(x: i64)`; `name: None` for
/// the positional form `V(i64)`. A variant's `fields` Vec is either
/// all-named or all-positional (mixed rejected at parse time per
/// N4-S6 with T223). Named-payload-with-refinement enables variant
/// refinement clauses to reference payload fields by identifier
/// (e.g., `Positive(x: i64) where x > 0`).
#[derive(Debug, Clone, PartialEq)]
pub struct EnumVariantField {
    pub name: Option<String>,
    pub ty: TypeExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImplDef {
    pub type_name: String,
    /// PR-5 (trait Wall): `Some(trait)` for an explicit `impl Trait for Type`
    /// block, `None` for an inherent `impl Type` block. The methods attach to
    /// `type_name` either way; the trait name drives the orphan/coherence checks.
    pub trait_name: Option<String>,
    /// SIGIL Complete v0 / Phase 6 supremum path: impl-block-level type
    /// parameters. `impl Result<T, E> { ... }` carries
    /// `type_params: vec!["T", "E"]`. Empty Vec for non-generic impl
    /// blocks (`impl Foo { ... }` keeps `vec![]`).
    ///
    /// Method-level `type_params` on `FnDef` inside this block EXTEND
    /// these binders — `impl Result<T, E> { fn map<U>(...) }` means
    /// `map` sees T, E (from impl) plus U (method-local) in scope.
    /// Method-level shadowing of an impl-level name fires T228 at
    /// parse time per N5-V0.
    ///
    /// Per N10-V0 this Vec preserves DECLARATION ORDER via `Vec::push`
    /// in the parser; positional substitution at dispatch time
    /// (commit #3) depends on this ordering invariant.
    pub type_params: Vec<TypeParam>,
    pub methods: Vec<FnDef>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub name: String,
    pub ty: TypeExpr,
    pub span: Span,
    /// An optional leading `mut` on an actor `state {}` field (`Mut`), else
    /// `Default`. Record fields are always `Default`; `mut` in a record is
    /// rejected at parse time with P030.
    pub mutability: Mutability,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub ty: TypeExpr,
    pub taint: Option<TaintLabel>,
    /// `@Flow` — taint-polymorphic parameter: the function accepts a value of
    /// any label in {`@Public`, `@Internal`, `@Secret`} here, and the call
    /// site's result label follows the argument (lub of `@Flow` arguments).
    /// Soundness is per-instantiation: the body is verified once per
    /// admissible label with every `@Flow` position rewritten to it.
    /// Mutually exclusive with a concrete `taint` (P021). Only `fn` items may
    /// use it — extern/trait/actor/effect-op/closure params reject it.
    pub flow: bool,
    /// `@ReadOnly` / `@Mut` mutation-capability axis (mutation-as-capability
    /// epic). `Default` for a bare param. Orthogonal to `taint`.
    pub mutability: Mutability,
    /// Regions (DEF-2b, LD-4): the `@in r` region annotation — the NAME of the
    /// `Region` parameter this value lives in. `None` for an unannotated param.
    /// Parsed in PR-3; the AG-R2 lift (PR-4) reads it via `FunctionSig.param_regions`.
    /// Orthogonal to `taint` and `mutability`.
    pub region: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RefKind {
    Ref(bool), // &T (false) or &mut T (true)
    Slice,     // &[T]
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeExpr {
    pub path: Path,
    pub ref_kind: Option<RefKind>,
    /// Parametric cap usage (Wall 2 → Wall 3): each entry is the bound
    /// `i64` literal at the corresponding position in the declaration.
    /// Empty Vec for non-parametric usage and non-cap types; single-
    /// element Vec for legacy Wall 2 single-deadline form
    /// (`Approval(2030)`); multi-element for Wall 3 multi-param form
    /// (`Limited(2030, 5)`).
    pub deadline: Vec<i64>,
    pub span: Span,
    /// PR B / N29-PRB: function-type syntax `Fn(T1, T2, ...) -> U`. When
    /// `Some(_)`, this `TypeExpr` represents a function type and the
    /// `path`, `ref_kind`, `deadline` fields are ignored (parser sets
    /// `path` to a synthetic single-segment `"Fn"` for diagnostic
    /// rendering only). When `None`, this is a normal nominal type.
    ///
    /// `resolve_type_expr` translates `Some(fn_type)` to
    /// `Type::Fn(params, ret, is_linear, latent_effects)`. Both trailing
    /// fields are currently fixed at the annotation site: `is_linear =
    /// false` (a parameter TYPE captures nothing) and `latent_effects =
    /// EffectSet::empty()`, because the surface grammar has no effect-row
    /// suffix on a function type yet. The existing
    /// `Type::Fn` variant + closure construction (`Expr::Closure`)
    /// + AIR closure-call lowering are unchanged.
    ///
    /// Required by PR B's combinator method signatures:
    /// `fn map<U>(self: Result<T, E>, f: Fn(T) -> U) -> Result<U, E>`.
    pub fn_type: Option<Box<FnTypeExpr>>,
    /// PR P16: array-type syntax `[T; N]`. When `Some(_)`, this
    /// `TypeExpr` represents a sized array type and the `path`,
    /// `ref_kind`, `deadline`, `fn_type` fields are ignored (parser
    /// sets `path` to a synthetic single-segment `"[T; N]"` for
    /// diagnostic rendering only). When `None`, this is a normal
    /// nominal type / fn type / reference / slice as before.
    ///
    /// `resolve_type_expr` translates `Some(array_type)` to
    /// `Type::Array { elem, size }` with substitution of any
    /// in-scope generics in the element type.
    ///
    /// Required for `record BoundedVec { data: [i64; 64], ... }`
    /// and the empty-literal annotation `let x: [i64; 0] = [];`.
    /// Per N3-P16, `size` is admitted only for integer literals in
    /// `0..=65535`; out-of-range fires T239 at parse time.
    pub array_type: Option<Box<ArrayTypeExpr>>,
    /// Tuple-type syntax `(A, B, …)`. When `Some(_)`, this `TypeExpr`
    /// represents a structural tuple type and the `path`, `ref_kind`,
    /// `deadline`, `fn_type`, `array_type` fields are ignored (parser sets
    /// `path` to a synthetic single-segment `"(...)"` for diagnostic
    /// rendering only). `resolve_type_expr` translates it to `Type::Tuple`.
    /// v1 admits arity `2..=MAX_TUPLE_ARITY`; a 1-tuple `(A,)` is rejected at
    /// parse time, and the no-comma `(A)` form is plain grouping (the parser
    /// returns the inner `TypeExpr`, never setting this field).
    pub tuple_type: Option<Vec<TypeExpr>>,
}

/// PR B / N29-PRB: function-type syntax payload (`Fn(T1, T2) -> U`).
/// Used as the inner shape of `TypeExpr::fn_type`. Closures already
/// construct via `Expr::Closure` and lower via the existing AIR
/// pipeline; this struct only adds the TYPE-EXPRESSION surface that
/// admits Fn-typed function parameters.
#[derive(Debug, Clone, PartialEq)]
pub struct FnTypeExpr {
    pub params: Vec<TypeExpr>,
    pub return_type: TypeExpr,
    /// Latent effect-row suffix (`Fn(T) -> U ! { E1, E2 }`, roadmap Phase 3):
    /// the effects the function VALUE performs when applied. `None` = no row
    /// written, which resolves to the EMPTY row (the fail-closed default — an
    /// unannotated `Fn` param promises to perform nothing, so only pure values
    /// satisfy it). Mirrors `FnDef::effects`' `Option<Vec<String>>` shape, but
    /// the resolution policy differs deliberately: an UNREGISTERED name here is
    /// a hard T069 error at the annotation site (`validate_fn_type_effect_rows`),
    /// whereas declaration rows silently drop unknown names (the SH-EFFECT-pinned
    /// registration filter). The new surface is born strict; the legacy one keeps
    /// its documented leniency.
    ///
    /// BINDING (the declaration-return ambiguity): in a function DECLARATION's
    /// return-type position the trailing row binds to the DECLARATION, exactly as
    /// it did before this field existed — the parser suppresses type-row parsing
    /// there (`suppress_fn_type_row`), and parentheses opt into type-binding:
    /// `-> (Fn(i64) -> i64 ! { Alloc })`. P031 (warning) is emitted at the
    /// suppressed site so the binding is never silent.
    pub effects: Option<Vec<String>>,
    pub span: Span,
}

/// PR P16: array-type syntax payload (`[T; N]`). Used as the inner
/// shape of `TypeExpr::array_type`. The `size` field is `u32` and
/// constrained to `0..=65535` at parse time per N3-P16.
#[derive(Debug, Clone, PartialEq)]
pub struct ArrayTypeExpr {
    pub elem: TypeExpr,
    pub size: u32,
    pub span: Span,
}

impl TypeExpr {
    pub fn display_name(&self) -> String {
        if let Some(elems) = &self.tuple_type {
            let inner = elems
                .iter()
                .map(TypeExpr::display_name)
                .collect::<Vec<_>>()
                .join(", ");
            return format!("({inner})");
        }
        let path_name = self.path.display_name();
        let base = if self.path.type_args.is_empty() {
            path_name
        } else {
            let args = self
                .path
                .type_args
                .iter()
                .map(TypeExpr::display_name)
                .collect::<Vec<_>>()
                .join(", ");
            format!("{path_name}<{args}>")
        };
        // Positional rendering of every deadline literal; empty Vec
        // produces no suffix. MC-5 fence: never collapse multi-element
        // to bare name.
        let with_deadline = if self.deadline.is_empty() {
            base
        } else {
            let values = self
                .deadline
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!("{base}({values})")
        };
        match &self.ref_kind {
            None => with_deadline,
            Some(RefKind::Ref(false)) => format!("&{with_deadline}"),
            Some(RefKind::Ref(true)) => format!("&mut {with_deadline}"),
            Some(RefKind::Slice) => format!("&[{with_deadline}]"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub statements: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    /// A wide integer literal that does NOT fit i64 (u256 PR-U2). Carries the
    /// value as 4 little-endian u64 limbs; always types as `u256` (the only
    /// machine type that can hold it; i256 literals are deferred). Produced by
    /// the lexer when `parse::<i64>()` overflows.
    Int256([u64; 4]),
    Float(f64),
    Bool(bool),
    Str(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let(LetStmt),
    /// `let (a, b, …) = value;` — tuple destructuring. The parser produces
    /// this; type-check desugars it into a hidden temp + per-element field
    /// loads (so no `TypedStmt::LetTuple` exists downstream).
    LetTuple(LetTupleStmt),
    Assign(AssignStmt),
    Expr(ExprStmt),
    If(IfStmt),
    Match(MatchStmt),
    While(WhileStmt),
    ForIn(ForInStmt),
    /// `for v in a..b { … }` — see [`ForRangeStmt`].
    ForRange(ForRangeStmt),
    Return(ReturnStmt),
    /// `break;` — exit the innermost enclosing loop. The `Span` is the keyword.
    Break(Span),
    /// `continue;` — skip to the next iteration of the innermost enclosing loop.
    Continue(Span),
}

impl Stmt {
    pub fn span(&self) -> Span {
        match self {
            Self::Let(stmt) => stmt.span,
            Self::LetTuple(stmt) => stmt.span,
            Self::Assign(stmt) => stmt.span,
            Self::Expr(stmt) => stmt.span,
            Self::If(stmt) => stmt.span,
            Self::Match(stmt) => stmt.span,
            Self::While(stmt) => stmt.span,
            Self::ForIn(stmt) => stmt.span,
            Self::ForRange(stmt) => stmt.span,
            Self::Return(stmt) => stmt.span,
            Self::Break(span) | Self::Continue(span) => *span,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetStmt {
    pub name: String,
    pub mutable: bool,
    pub ty: Option<TypeExpr>,
    pub taint: Option<TaintLabel>,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetTupleStmt {
    /// `(name, is_mutable)` for each binding, in positional order — per-binding
    /// `mut` (`let (mut a, b) = …`). Arity must match the RHS tuple's (validated
    /// at type-check → T261). Flat only — nested patterns `let ((a, b), c)` are
    /// an Anti-Goal (AG-2).
    pub bindings: Vec<(String, bool)>,
    /// Optional `: (A, B)` annotation, checked against the RHS before desugar.
    pub ty: Option<TypeExpr>,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AssignStmt {
    /// The place being assigned — an lvalue expression (`Local`/`FieldAccess`/
    /// `Index`), validated at type-check (T247).
    pub target: Expr,
    /// `Some(op)` for a compound assignment `place op= value` on a FIELD or
    /// INDEX place (lowered as load-op-store, NC2). A LOCAL compound is
    /// desugared at parse time, so `op` is always `None` for a local target.
    pub op: Option<BinaryOp>,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExprStmt {
    pub expr: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfStmt {
    pub condition: Expr,
    pub then_branch: Block,
    pub else_branch: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchStmt {
    pub scrutinee: Expr,
    pub arms: Vec<MatchArm>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Literal(LiteralPattern),
    Range(RangePattern),
    Wildcard(Span),
    Binding(BindingPattern),
    EnumVariant(EnumVariantPattern),
    Array(ArrayPattern),
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Self::Literal(pattern) => pattern.span,
            Self::Range(pattern) => pattern.span,
            Self::Wildcard(span) => *span,
            Self::Binding(pattern) => pattern.span,
            Self::EnumVariant(pattern) => pattern.span,
            Self::Array(pattern) => pattern.span,
        }
    }
}

/// An array/slice destructuring pattern: `[a, b, ..rest]`.
///
/// Phase 5 (collection patterns). Elements are bindings or wildcards only
/// (irrefutable — AG-P5-1); the optional `rest` is the LAST element or absent
/// (AG-P5-2), binding the tail as a `&[T]` slice (named) or ignoring it (`..`).
#[derive(Debug, Clone, PartialEq)]
pub struct ArrayPattern {
    pub elements: Vec<ArrayElem>,
    pub rest: Option<RestBind>,
    pub span: Span,
}

/// A single fixed-position element of an [`ArrayPattern`]: a binding or `_`.
#[derive(Debug, Clone, PartialEq)]
pub enum ArrayElem {
    Bind(String, Span),
    Wild(Span),
}

/// The trailing `..rest` (named) or `..` (anonymous) of an [`ArrayPattern`].
#[derive(Debug, Clone, PartialEq)]
pub struct RestBind {
    pub name: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BindingPattern {
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LiteralPattern {
    pub literal: Literal,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RangePattern {
    pub lo: Literal,
    pub hi: Literal,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ForInStmt {
    pub var: String,
    pub iterable: Expr,
    pub body: Block,
    pub span: Span,
}

/// `for v in start..end { body }` — the exclusive integer range loop. A DISTINCT
/// statement from `ForIn` (not an `Option<Expr>` on it) so every exhaustive `Stmt`
/// walker is FORCED to grow an arm (the narrow-int-walker-class defense). The
/// range form exists ONLY in for-header position — there is no general Range
/// expression, type, or value. `..=` is rejected at parse (P029). The loop
/// variable is bound IMMUTABLY (reassignment is T042), which is what later makes
/// the range a trustworthy compile-time bounds fact for `arr[v]` elision.
#[derive(Debug, Clone, PartialEq)]
pub struct ForRangeStmt {
    pub var: String,
    pub start: Expr,
    pub end: Expr,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub condition: Expr,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStmt {
    pub value: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Literal(LiteralExpr),
    Path(PathExpr),
    Call(CallExpr),
    ResultCtor(ResultCtorExpr),
    Try(TryExpr),
    Send(SendExpr),
    Ask(AskExpr),
    Spawn(SpawnExpr),
    Binary(BinaryExpr),
    EnumConstruct(EnumConstructExpr),
    RecordConstruct(RecordConstructExpr),
    FieldAccess(FieldAccessExpr),
    CapRestrict(CapRestrictExpr),
    CapRestrictDeadline(CapRestrictDeadlineExpr),
    CapSplit(CapSplitExpr),
    CapDraw(CapDrawExpr),
    /// Capabilities-as-values: `mint <CapType>[(deadline,…)] for <target>` — the
    /// privileged constructor of a fresh capability value. Gated by holding the
    /// cap type's declared minting authority (`mintable_by`). Sidesteps the C001
    /// forgery gate structurally (it is not a `RecordConstruct`).
    Mint(MintExpr),
    ArrayLit(ArrayLitExpr),
    /// `(a, b, …)` — a tuple literal of ≥2 elements. A no-comma `(e)` is plain
    /// grouping (the parser returns the inner `Expr`, never this node).
    Tuple(TupleExpr),
    Index(IndexExpr),
    /// PR AF: `array[start..end]` slice operator. Per the PR AF spec,
    /// this AST node is produced unconditionally by the parser, but
    /// type-check rejects it with T238 unless its immediate syntactic
    /// parent is an `Expr::Borrow` (so `&arr[1..3]` is admitted but
    /// bare `arr[1..3]` is not). `start` and `end` are both optional
    /// (omitted ends default to 0 and `array.len()` respectively).
    Slice(SliceExpr),
    MethodCall(MethodCallExpr),
    Closure(ClosureExpr),
    Borrow(BorrowExpr),
    Grant(GrantExpr),
    Handle(HandleExpr),
    /// Effect Handlers (EH0): `perform Effect.op(args)`. Gated by E004 until
    /// EH1 (type-check) lands.
    Perform(PerformExpr),
    /// Effect Handlers (EH0): the clause form `handle e { Op(x) => .. }` —
    /// disjoint from `Handle` (C-PATHSEP). Gated by E004 until EH1.
    ClauseHandle(ClauseHandleExpr),
    /// Effect Handlers (EH0): `resume <expr>` inside a scoped clause body.
    Resume(ResumeExpr),
    Declassify(DeclassifyExpr),
    DeclassifyCt(DeclassifyCtExpr),
    Region(RegionExpr),
    /// PR-E3: string interpolation `f"…{e}…"`. The parser produces this node; it is
    /// typed as `str` (each hole checked str/i64/bool) at type-check, then a pre-AIR
    /// pass lowers it to a `str_concat` chain (so AIR/wasm never see this node).
    FString(FStringExpr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct HandleExpr {
    pub effects: Vec<String>,
    pub body: Block,
    pub span: Span,
}

/// Effect Handlers (EH0): `perform <Effect>.<op>(args)` — invoke an effect
/// operation. A first-class typed node kept through type-check (so the effect
/// checker sees it) with pluggable lowering (abortive → `br`; scoped → an
/// evidence call). Parsed contextually on the unambiguous `perform <Ident>.`
/// shape (mirrors the `mint` keyword trick); `perform` stays a plain identifier
/// everywhere else.
#[derive(Debug, Clone, PartialEq)]
pub struct PerformExpr {
    pub effect: String,
    pub effect_span: Span,
    pub op: String,
    pub args: Vec<Expr>,
    pub span: Span,
}

/// Effect Handlers (EH0): `resume <expr>` inside a scoped handler clause —
/// returns the resumed value to the `perform` site. Reserved now (parsed only
/// inside a clause body); general scoped resume is gated until EH5.
#[derive(Debug, Clone, PartialEq)]
pub struct ResumeExpr {
    pub value: Box<Expr>,
    pub span: Span,
}

/// Effect Handlers (EH0): one arm of a clause-form `handle` —
/// `<Effect>.<op>(binders) => <body>`. A body containing `resume` is *scoped*
/// (tail-resume-once); a body with no `resume` is *abortive* (its value becomes
/// the value of the whole `handle`). The body is always a `Block` (a bare
/// expression `=> e` is wrapped as a single-statement block).
#[derive(Debug, Clone, PartialEq)]
pub struct HandleClause {
    pub effect: String,
    pub op: String,
    pub binders: Vec<String>,
    pub body: Block,
    pub span: Span,
}

/// Effect Handlers (EH0): the clause form `handle <scrutinee> { Op(x) => .. }`.
/// A DISTINCT variant from the bare row-widening [`HandleExpr`] (constraint
/// C-PATHSEP) so the legacy inline-lowering path is never fed a clause.
#[derive(Debug, Clone, PartialEq)]
pub struct ClauseHandleExpr {
    pub scrutinee: Box<Expr>,
    pub clauses: Vec<HandleClause>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DeclassifyExpr {
    pub value: Box<Expr>,
    pub cap: Box<Expr>,
    pub target: Option<TaintLabel>,
    pub span: Span,
}

/// Two-step CT declassification: lowers `@SecretCT → @Secret` given a
/// linear `Cap<DeclassifyCT>`. From `@Secret`, the existing `declassify`
/// is required to reach `@Public`. See spec §3.4.1 (E2 declassify input
/// contract).
#[derive(Debug, Clone, PartialEq)]
pub struct DeclassifyCtExpr {
    pub value: Box<Expr>,
    pub cap: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct GrantExpr {
    pub cap: Box<Expr>,
    pub body: Box<Expr>,
    pub span: Span,
}

/// `mint <CapType>[(d0, d1, …)] for <target>` — the privileged capability
/// constructor. `cap_name` names a declared `cap type`; `params` are optional
/// `i64` deadline literals (the same positional deadline params a parametric
/// cap carries); `target` is the resource the capability authorizes (honest
/// provenance in v1 — recorded, not yet enforced per-instance).
#[derive(Debug, Clone, PartialEq)]
pub struct MintExpr {
    pub cap_name: String,
    /// Span of the cap-type name alone, for the unknown/non-mintable diagnostic.
    pub cap_name_span: Span,
    pub params: Vec<i64>,
    pub target: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BorrowExpr {
    pub inner: Box<Expr>,
    pub mutable: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClosureExpr {
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LiteralExpr {
    pub literal: Literal,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PathExpr {
    pub path: Path,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    pub callee: Path,
    pub args: Vec<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResultCtorExpr {
    pub is_ok: bool,
    pub value: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TryExpr {
    pub value: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SendExpr {
    pub target: Path,
    pub message: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AskExpr {
    pub target: Path,
    pub message: Box<Expr>,
    pub timeout: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SpawnExpr {
    pub actor: TypeExpr,
    pub args: Vec<Expr>,
    pub supervision: Option<SupervisionExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SupervisionExpr {
    Stop,
    Restart { max_restarts: Box<Expr> },
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
    pub lhs: Box<Expr>,
    pub op: BinaryOp,
    pub rhs: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumConstructExpr {
    pub enum_name: String,
    pub variant: String,
    pub fields: Vec<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordConstructExpr {
    pub type_name: String,
    pub fields: Vec<(String, Expr)>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldAccessExpr {
    pub object: Box<Expr>,
    pub field: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CapRestrictExpr {
    pub cap: Path,
    pub restriction: String, // compile-time authority name, resolved to bitmask
    pub span: Span,
}

/// Wall 2 Stage 2: `cap.restrict_deadline(D')` — narrows the
/// deadline-typed cap's declared deadline to `D'` (which must be
/// `<=` the source cap's declared deadline; T200 otherwise).
/// Operationally a no-op at the wasm boundary (deadline is type-
/// check only); lowers to a CapRestrict with a full-authority mask
/// to ride existing AIR/Z3 infrastructure.
#[derive(Debug, Clone, PartialEq)]
pub struct CapRestrictDeadlineExpr {
    pub cap: Path,
    pub deadline: i64,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CapSplitExpr {
    pub cap: Path,
    pub amount: Box<Expr>,
    pub span: Span,
}

/// `cap.draw(amount)` — non-consuming sibling of `cap.split(amount)`.
/// Returns a child capability with `amount` units and leaves the parent
/// alive bound to the same name with a reduced balance. Introduced in
/// step 10 to make rate-limit / quota / N-of-M patterns expressible
/// (step 9's design analysis identified this as the smallest missing
/// primitive on axis 1). The semantic difference from `split` is purely
/// in `ownership.rs`: CapDraw does not mark the source as moved.
#[derive(Debug, Clone, PartialEq)]
pub struct CapDrawExpr {
    pub cap: Path,
    pub amount: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumVariantPattern {
    pub type_name: String,
    pub variant: String,
    pub bindings: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayLitExpr {
    pub elements: Vec<Expr>,
    pub span: Span,
}

/// PR-E3: an interpolated string `f"…{e}…"`. `parts` strictly alternates literal
/// runs and holes, ALWAYS starting and ending with a `Literal` (possibly empty) —
/// so an N-hole f-string has exactly `2N+1` parts (ET-E3). The whole expression
/// types as `str`.
#[derive(Debug, Clone, PartialEq)]
pub struct FStringExpr {
    pub parts: Vec<FStringPart>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum FStringPart {
    /// A literal run (already escape-decoded), carrying its byte-range span inside
    /// the `f"…"` so a faithful child node can be emitted for parser-differential.
    Literal(String, Span),
    /// An interpolation hole — a full expression parsed from the `{ … }` contents.
    Hole(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TupleExpr {
    /// The element expressions, in positional order. Always ≥2 (a 1-tuple
    /// `(a,)` is rejected at parse time; `(a)` is grouping, not a tuple).
    pub elements: Vec<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IndexExpr {
    pub array: Box<Expr>,
    pub index: Box<Expr>,
    pub span: Span,
}

/// PR AF: `array[start..end]` slice operator. `start`/`end` are
/// optional to admit the open-range forms `[..end]`, `[start..]`,
/// and `[..]`. Per N18-AF / N22-AF the type-checker enforces that
/// the immediate parent is `Expr::Borrow`; non-borrowed forms fire
/// T238.
#[derive(Debug, Clone, PartialEq)]
pub struct SliceExpr {
    pub array: Box<Expr>,
    pub start: Option<Box<Expr>>,
    pub end: Option<Box<Expr>>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MethodCallExpr {
    pub receiver: Box<Expr>,
    pub method: String,
    pub args: Vec<Expr>,
    /// Whether the source spelled any segment of this call's path with `::`
    /// (e.g. `helpers::add_one(0)` or `sigil::m::f(x)`). The parser treats
    /// `.` and `::` as equivalent path separators structurally, but the
    /// SPELLING carries intent: `::` is module/path syntax, so a shadowing
    /// local must never capture it — name resolution uses this to keep T156
    /// fail-closed for `::`-spelled receivers while letting a `.`-spelled
    /// call resolve to a local whose type services the method. Synthetic
    /// (compiler-built) method calls set `false`.
    pub colon_spelled: bool,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    LogicalAnd,
    LogicalOr,
    Lt,
    LtEq,
    Gt,
    GtEq,
    Eq,
    NotEq,
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Self::Literal(expr) => expr.span,
            Self::Path(expr) => expr.span,
            Self::Call(expr) => expr.span,
            Self::ResultCtor(expr) => expr.span,
            Self::Try(expr) => expr.span,
            Self::Send(expr) => expr.span,
            Self::Ask(expr) => expr.span,
            Self::Spawn(expr) => expr.span,
            Self::Binary(expr) => expr.span,
            Self::EnumConstruct(expr) => expr.span,
            Self::RecordConstruct(expr) => expr.span,
            Self::FieldAccess(expr) => expr.span,
            Self::CapRestrict(expr) => expr.span,
            Self::CapRestrictDeadline(expr) => expr.span,
            Self::CapSplit(expr) => expr.span,
            Self::CapDraw(expr) => expr.span,
            Self::Mint(expr) => expr.span,
            Self::ArrayLit(expr) => expr.span,
            Self::Tuple(expr) => expr.span,
            Self::Index(expr) => expr.span,
            Self::Slice(expr) => expr.span,
            Self::MethodCall(expr) => expr.span,
            Self::Closure(expr) => expr.span,
            Self::Borrow(expr) => expr.span,
            Self::Grant(expr) => expr.span,
            Self::Handle(expr) => expr.span,
            Self::Perform(expr) => expr.span,
            Self::ClauseHandle(expr) => expr.span,
            Self::Resume(expr) => expr.span,
            Self::Declassify(expr) => expr.span,
            Self::DeclassifyCt(expr) => expr.span,
            Self::Region(expr) => expr.span,
            Self::FString(expr) => expr.span,
        }
    }
}
