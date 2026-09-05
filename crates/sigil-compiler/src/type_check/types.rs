//! Type-check data structures, extracted from `mod.rs` in structural
//! extraction PR 12.
//!
//! This file holds the static-shape definitions used throughout the
//! type-check tree:
//!
//!   * `Type` — the public type enum (pub-re-exported by mod.rs to
//!     preserve `crate::type_check::Type` for external callers).
//!   * `FunctionSig`, `HandlerSig`, `ActorSig` — signature records
//!     keyed into `TypeUniverse` by name.
//!   * `TypeUniverse` — the top-level type catalog built by
//!     `universe::collect_type_universe`.
//!   * `MonomorphTracker` — generic instantiation tracking + cap-
//!     borrow context, threaded through every infer/check call.
//!   * `ExpectedTypeGuard`, `BorrowContextGuard` — RAII guards that
//!     save/restore tracker state across recursive calls.
//!   * `MAX_MONOMORPH_DEPTH` — runaway-recursion guard for generic
//!     instantiation.
//!
//! These items are PURE DATA + RAII; no Z3 calls, no I/O, no
//! global state. They're the static substrate the rest of the type
//! check builds on.
//!
//! ## Re-export contract
//!
//! `mod.rs` does `pub use types::Type;` to preserve the public
//! `crate::type_check::Type` path (external callers in `air.rs`,
//! `compiler.rs`, etc. depend on it). Everything else is
//! `pub(super)` — visible only within the `type_check` tree via
//! mod.rs's `use types::*;` private glob.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::ast::TaintLabel;
use crate::registries::{AuthorityRegistry, EffectRegistry, EffectSet};
use crate::typed_ast::TypedFunction;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Unit,
    Bool,
    I32,
    U32,
    I64,
    U64,
    F64,
    /// 256-bit unsigned / signed integers (the Solidity-frontend foundation).
    /// VALUE REPRESENTATION (decision P): a 256-bit value is 32 bytes and cannot
    /// fit a wasm local, so — like every SIGIL aggregate — it lowers to
    /// `AirType::Ptr` (a 4-byte pointer in a local) whose payload is a 32-byte
    /// cell in linear memory: 4× i64 little-endian limbs (limb0 = LSB) at offsets
    /// 0/8/16/24, 8-byte aligned. `U256`/`I256` share the identical
    /// representation; signedness lives only in the chosen stdlib op. All u256
    /// ops are PURE and allocate a FRESH cell (the immutable-value invariant that
    /// makes pointer-aliasing sound). NOT sendable across actor boundaries until
    /// 32-byte serialization lands (a raw pointer is not portable).
    U256,
    I256,
    Str,
    Generic(String),
    Named(String, Vec<Type>),
    /// Capability type. The second field is the positional list of
    /// parametric deadline literals; empty Vec = non-parametric.
    /// Subtyping rule (Wall 2 → Wall 3, `cap_subtype`):
    ///   Names match exactly AND Vec arities match exactly AND every
    ///   position satisfies `actual[i] >= expected[i]` (all-positions
    ///   covariance). Empty Vec ↔ empty Vec is identity. Mixed
    ///   parametric/non-parametric forms (or arity mismatches) are
    ///   NEVER compatible — the arity check is load-bearing.
    Cap(String, Vec<i64>),
    ActorRef(String),
    Array {
        elem: Box<Type>,
        size: u32,
    },
    /// Function type: (param_types, return_type, is_linear, latent_effects)
    ///
    /// `is_linear = true` if the closure captures a linear/cap type (FnOnce semantics).
    ///
    /// `latent_effects` is the row performed WHEN THE FUNCTION IS APPLIED, mirroring the
    /// λ-SIGIL spec's `Ty.arrow A ε B` (`proofs/lean/LambdaSigil/EffectRows.lean`): the row
    /// rides the arrow, so a closure that crosses a function boundary still carries it and
    /// `IndirectCall` can discharge it (E001). Without it a closure built in an `{Alloc}`
    /// context and applied in a `{}` context was caught only by a RUNTIME effect check
    /// (the AG-HOF-A gap).
    ///
    /// ERASED before AIR — `mangle_type` maps every `Type::Fn` to the constant `"fn"`, so
    /// this field causes no wasm byte drift and no symbol-mangling change.
    ///
    /// The field is POSITIONAL (not behind a `..`) on purpose: every construction site is
    /// compiler-forced to state a row, which is this repo's standing defense against the
    /// "walker forgot an arm" class.
    Fn(Vec<Type>, Box<Type>, bool, EffectSet),
    /// Borrowed reference: &T (false) or &mut T (true)
    Ref(Box<Type>, bool),
    /// Borrowed slice: &[T] — always a borrow, no owned unsized arrays
    Slice(Box<Type>),
    /// FFI raw pointer: Ptr<T>
    Ptr(Box<Type>),
    /// FFI mutable raw pointer: MutPtr<T>
    MutPtr(Box<Type>),
    /// Regions (DEF-2b, LD-1): a region handle — a runtime VALUE (an i64; `0` = the
    /// global heap), NOT a type-level lifetime. Produced ONLY by a `region NAME(N){}`
    /// lexical binding or a `Region` parameter (NC-2b-1); SECOND-CLASS (NC-2b-2) and
    /// escape-scored like any aliasable value (a handle must not outlive its region).
    /// AIR lowers it to `I64`; region-polymorphism is passing the handle.
    Region,
    /// Tuple: a structural, anonymous product type `(A, B, …)`. Its RUNTIME
    /// representation is an anonymous record — a heap struct with positional
    /// fields named `"0"`, `"1"`, … — so it reuses `RecordConstruct` /
    /// `FieldAccess` lowering (the construct path is registry-free; the read
    /// path computes offsets on-demand). v1 has NO `.0` surface syntax (the
    /// lexer tokenizes `.0` as a float) — a tuple is read only via a
    /// `let (x, y) = …` destructure. Arity is bounded at 12 (ET-2). Every
    /// `Type::Tuple` match arm MUST recurse into all elements (ET-9).
    Tuple(Vec<Type>),
    /// PIL: polymorphic integer literal carrying the parsed `i64` value.
    /// Produced by `infer_literal_type` for `Literal::Int(_)`. Unifies
    /// with any machine integer type (I32/U32/I64/U64) via
    /// `type_compatible`'s symmetric IntLit arms (N4-PIL/N5-PIL) with
    /// per-literal range-check via `int_literal_fits`. The resolution
    /// walker (`resolve_int_literals_in_expr`) rewrites IntLit nodes to
    /// concrete types at binding sites (N17-PIL); any IntLit reaching
    /// AIR's `lower_type` ICEs with the `resolve_int_literals` hint
    /// (N3-PIL).
    IntLit(i64),
    /// HKT (higher-kinded type) VARIABLE: `F` of kind `* -> *` (arity 1),
    /// `* -> * -> *` (arity 2). Introduced ONLY by a `<F: * -> *>` type-param
    /// binder; `arity` = the kind's arrow count. Like `Type::Generic`, it is a
    /// check-time-only artifact that MUST be erased to a concrete `Type::Named`
    /// (via eager monomorphization) before AIR — it ICEs in
    /// `mangle_type`/`type_compatible` if it ever escapes. The check-time-only
    /// HKT trio (`HktVar`/`HktApp`/`TypeCtor`) is a DISTINCT-variant set so the
    /// exhaustiveness checker flags every `Type` walker that forgot an arm (the
    /// "structural walker forgot an arm" defense). See docs/specs/hkt-in-sigil.md.
    HktVar {
        name: String,
        arity: usize,
    },
    /// HKT APPLICATION: `F<A>`, `M<K, V>`, `F<G<A>>` — a higher-kinded variable
    /// `ctor` applied to `args`. `args.len()` must equal the binder's `arity`
    /// (the use-site/erasure arity gates, EX-1/EX-3/EX-5). Erased by
    /// `apply_subst` (`HktApp` + `F |-> TypeCtor(c)` => `Named(c, args)`).
    HktApp {
        ctor: String,
        args: Vec<Type>,
    },
    /// Transient binding TARGET of an `HktVar`: `F |-> TypeCtor("Vec")`. Lives
    /// ONLY inside a `subst` map and is consumed by `apply_subst` when rebuilding
    /// `HktApp` -> `Named`. Never produced by `resolve_type_expr` from surface
    /// syntax; it has a real arm ONLY in `mangle_type` (`n.clone()`) and ICEs
    /// everywhere else downstream (same erasure discipline as `Generic`).
    TypeCtor(String),
    /// Typestate (Epic 1, lightweight dependent types): a zero-size protocol-state
    /// token (`Open`, `Closed`, `Live`, `Revoked`). Appears ONLY as a phantom
    /// `Named` arg — `File<Open>` is `Named("File", [StateMarker("Open")])` — never
    /// as a value type. A DISTINCT variant (the "structural walker forgot an arm"
    /// defense): it has REAL arms in the CHECKING walkers (`type_compatible` /
    /// `unify_inner` / `apply_subst` / `render_type` compare / bind / substitute /
    /// render it) and ICEs in the VALUE-position walkers (`lower_type` /
    /// `mangle_type` / `classify_value_kind` / `runtime_type`) — it MUST be erased
    /// by `strip_state_args` before AIR. The whole-program `assert_no_residual_state`
    /// gate (T268) is the primary defense; the ICE arms are the backstop.
    /// See docs/specs/typestate-in-sigil.md.
    StateMarker(String),
    /// Effect Handlers (EH3): the bottom type — the return type of an ABORTIVE
    /// effect operation (`fn raise(..) -> never`) and the type of a `perform` of
    /// such an operation (a value never produced, because the operation transfers
    /// control to the handler). NON-DENOTABLE except as an operation return type
    /// (recognized syntactically in `resolve_op_return`). A DISTINCT variant (the
    /// "structural walker forgot an arm" defense): it renders as "never" and is
    /// not sendable / not reassignable, and ICEs in the VALUE-position walkers
    /// (`mangle_type` / `lower_type` / `runtime_type`) — it MUST erase before AIR.
    /// Value-position `Never` (`let x = trap()`, `(trap(), 1)`, `id(trap())`, …)
    /// is REJECTED with T279 (F003): the site checks in `check_let` /
    /// `infer_arg_with_expected` / `infer_tuple_expr` / `infer_array_lit_expr`
    /// reject-and-poison the known channels (poisoning matters because
    /// `mangle_type` runs DURING type-check), and the whole-program residual
    /// gate (`residual::scan_residual_never`, end of `check_with_warnings`)
    /// catches any channel they miss. The ICE arms are the C-NEVER backstop for
    /// compiler-invariant violations, never the primary defense. The ONE legal
    /// `Never` in an error-free typed AST is the top-level type of a bare
    /// expression statement (`trap();`, Tier A) — the divergence hook consumes it.
    Never,
    Error,
}

/// Effect Handlers (EH1/EH3): a registered effect operation. `params` are the
/// resolved parameter types (their count is the arity checked against a
/// `perform`/clause, E007); `ret` is the resolved return type — the value a
/// `perform` evaluates to (the resumed-value type) and the type a `resume` must
/// produce. An abortive operation (`-> never`) has `ret == Type::Never`.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct EffectOpInfo {
    pub(super) name: String,
    pub(super) params: Vec<Type>,
    pub(super) param_taints: Vec<TaintLabel>,
    pub(super) ret: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct FunctionSig {
    pub(super) qualified_name: String,
    pub(super) params: Vec<Type>,
    pub(super) ret: Type,
    /// Owning module name. Used by cross-module dispatch to look up the
    /// callee's ring (cross-ring call → R004) and to thread back to the
    /// declaring source for diagnostics.
    pub(super) module: String,
    /// Source-level visibility of the function. Cross-module calls to a
    /// `Visibility::Private` function emit `T155`.
    pub(super) visibility: crate::ast::Visibility,
    /// Wall 4 Step 7 (N21-S7): per-parameter refinement clauses. `None`
    /// at index i = parameter i is unrefined; `Some(clauses)` carries
    /// that param's declared refinements. Per N7-S7 / V16, each
    /// `Some(_)` Vec contains 0..1 entries.
    ///
    /// Populated by `collect_function_sigs` directly from
    /// `FnDef.param_refinements`. Cross-module dispatch sees these via
    /// `workspace_sigs` (no extra threading).
    pub(super) param_refinements: Vec<Option<Vec<crate::ast::RefinementClause>>>,
    /// Precise closure rows (roadmap Phase 1): the callee's DECLARED effect row,
    /// resolved from `FnDef.effects` at sig collection (the registry is built by
    /// `collect_type_universe`, which runs first). This is what makes a callee's
    /// row reachable DURING type-check — `effects_of_block` needs it to compute a
    /// closure's latent row bottom-up; the post-typing `check_effects` pass reads
    /// rows from `TypedFunction` instead and does not consult this field.
    /// Cross-module dispatch sees it via `workspace_sigs` (no extra threading),
    /// exactly like `param_refinements`. Extern fns record their declared row
    /// too, but `effects_of_block` deliberately does NOT charge extern calls —
    /// parity with `walk_expr_effects`' ExternCall arm (ET-EFF-1).
    pub(super) effects: EffectSet,
    /// Wall 4 Step 7 (N21-S7, N28-S7): return-value refinement clauses
    /// (max 1 per V16). `None` = return value is unrefined; `Some(clauses)`
    /// carries the declared `where @ ...` predicate. Per N14-S7, the
    /// call-site dispatcher attaches this to the call's TypedExpr
    /// `.refinement` sidecar so Step 2 preservation propagates it to
    /// consumers.
    pub(super) return_refinement: Option<Vec<crate::ast::RefinementClause>>,
    /// SIGIL Complete v0 / Phase 6 (supremum path): impl-block-level
    /// type parameters of the owning `impl` block, if this sig was
    /// produced from an impl-block method. Empty Vec for free fns,
    /// extern fns, and methods inside non-generic impl blocks.
    ///
    /// Per N10-V0, declaration order is preserved by `Vec::push` at
    /// sig collection. Dispatch substitution (N9-V0) reads this
    /// alongside the receiver's concrete type-args, builds a positional
    /// substitution map `{impl_type_params[i] → receiver.type_args[i]}`,
    /// and applies it to `params` + `ret` + each `param_refinements`
    /// entry before checking the call.
    pub(super) impl_type_params: Vec<String>,
    /// The METHOD's OWN type parameters (`fn fmap<A, B>(…)`) — distinct from the
    /// impl block's `impl_type_params`. Empty for free fns and monomorphic
    /// methods. Unlike impl params (bound positionally from the receiver's
    /// type-args), these are INFERRED at the call site by unifying the method's
    /// formal params against the actual argument types (the method-dispatch
    /// analog of free-fn generic inference). Without this the method's generics
    /// escape as `Type::Generic` and ICE in `type_compatible`/`mangle_type`.
    pub(super) method_type_params: Vec<String>,
    /// BoundedVec PR-0a: true iff this sig is an ASSOCIATED function — an impl
    /// method whose first parameter is NOT `self` (e.g. `Vec::new`,
    /// `BoundedVec_i64_8::new`). Set at sig collection from the method's params;
    /// `false` for free fns, extern fns, and `self`-receiver methods. The
    /// `Type::method()` associated-fn reroute keys on this so a CONCRETE (non-
    /// generic) record's `::new()` resolves, not only a generic impl's.
    pub(super) is_associated: bool,
    /// Mutation-as-capability (PR-2b): the `@ReadOnly`/`@Mut`/bare mutability of
    /// each parameter, positionally aligned with `params` (incl. `self` at index
    /// 0 for methods). Populated by `collect_function_sigs` from `Param.mutability`;
    /// the call-side escape gate reads it cross-module via `workspace_sigs` (no
    /// extra threading), exactly like `param_refinements`.
    pub(super) param_mutability: Vec<crate::ast::Mutability>,
    /// Regions (DEF-2b, LD-5): per-parameter region annotation, positionally aligned with
    /// `params` (incl. `self` at index 0). `None` for an unannotated param; `In(slot)` for
    /// a value declared `@in r` living in the `Region` param at position `slot`. Populated
    /// by `collect_function_sigs` from `Param.region` (all `None` until PR-3 parses `@in`);
    /// the AG-R2 lift (PR-4) reads it cross-module via `workspace_sigs`, exactly like
    /// `param_mutability`. A param that IS a `Region` is detected by its type at the lift,
    /// not stored here.
    pub(super) param_regions: Vec<ParamRegion>,
    /// Regions (DEF-2b, LD-4 / PR-5): the declared `where region(a): region(b)` outlives
    /// pairs, as `(a_slot, b_slot)` 0-based `Region`-parameter positions meaning
    /// `Param(a_slot)` OUTLIVES `Param(b_slot)`. Populated by `collect_function_sigs` from
    /// `FnDef.region_outlives`; the only thing that makes `Param(a) outlives Param(b)` true
    /// for `a != b` (consulted callee-side in the body's sinks and caller-side as the call's
    /// obligation). DIRECT-PAIR-ONLY — no transitive closure (AG-2b-9). Empty without a
    /// `where region` clause (the common case).
    pub(super) param_region_outlives: Vec<(u32, u32)>,
}

/// Regions (DEF-2b, LD-5 / NC-2b-3): a parameter's region annotation. `In(slot)` names
/// the `Region` parameter (by its 0-based position) that this value lives in — a per-body
/// slot index, meaningful ONLY within its declaring signature (the lift maps it to a
/// caller-side region before comparing). The `where`-relation between two `Region` params
/// is carried separately (PR-5); a `Region` param itself is recognised by its type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ParamRegion {
    None,
    /// `@in r` — the value lives in the `Region` param at this 0-based position. The slot
    /// is read by the AG-R2 lift (PR-4) to map to a caller-side region.
    In(u32),
}

#[derive(Debug, Clone, PartialEq)]
pub(super) struct HandlerSig {
    pub(super) params: Vec<Type>,
    pub(super) ret: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub(super) struct ActorSig {
    pub(super) init_params: Vec<Type>,
    pub(super) handlers: HashMap<String, HandlerSig>,
}

/// Shared, immutable inputs used throughout expression and statement checking.
/// Mutable inference state and diagnostics stay explicit at call sites.
#[derive(Clone, Copy)]
pub(super) struct TypeCheckContext<'a> {
    pub(super) function_sigs: &'a BTreeMap<String, FunctionSig>,
    pub(super) actor_sigs: &'a HashMap<String, ActorSig>,
    pub(super) module_name: &'a str,
    pub(super) universe: &'a TypeUniverse,
}

impl<'a> TypeCheckContext<'a> {
    pub(super) fn new(
        function_sigs: &'a BTreeMap<String, FunctionSig>,
        actor_sigs: &'a HashMap<String, ActorSig>,
        module_name: &'a str,
        universe: &'a TypeUniverse,
    ) -> Self {
        Self {
            function_sigs,
            actor_sigs,
            module_name,
            universe,
        }
    }

    pub(super) fn parts(
        self,
    ) -> (
        &'a BTreeMap<String, FunctionSig>,
        &'a HashMap<String, ActorSig>,
        &'a str,
        &'a TypeUniverse,
    ) {
        (
            self.function_sigs,
            self.actor_sigs,
            self.module_name,
            self.universe,
        )
    }
}

#[derive(Debug, Default)]
#[allow(clippy::type_complexity)]
pub(super) struct TypeUniverse {
    pub(super) actors: HashSet<String>,
    pub(super) caps: HashSet<String>,
    /// Cap-type name → its parameter declaration, if any. A cap is
    /// "parametric" (Wall 2 Stage 1) iff it appears in this map.
    /// Usages of parametric caps must supply a deadline literal;
    /// usages of non-parametric caps must not. Enforced in
    /// `validate_lowered_type` via T196 / T197.
    /// Cap-type name → list of parameter declarations. Empty Vec
    /// means non-parametric. Wall 3 extension of the Wall 2 single-
    /// param `HashMap<String, CapTypeParam>` to a positional list.
    pub(super) parametric_caps: HashMap<String, Vec<crate::ast::CapTypeParam>>,
    /// Capabilities-as-values: cap-type name → its minting policy, for cap
    /// types declared `cap type Foo mintable_by Admin[::bit] {…}`. A cap is
    /// MINTABLE iff it appears here; `mint` of a cap absent from this map is
    /// T272 (fail-closed — every legacy `cap type` is non-mintable).
    pub(super) mintable_caps: HashMap<String, crate::ast::MintPolicy>,
    /// Wall 2 Stage 2: `--build-deadline <N>` reference instant.
    /// When `Some(N)`, every parametric cap-type literal `Cap(D)` in
    /// the source must satisfy `D >= N`; `D < N` fires T199 (the cap
    /// is already past at build time). `None` skips the check.
    pub(super) build_deadline: Option<i64>,
    /// type_name → (type_params, fields_with_possibly_generic_types)
    pub(super) records: HashMap<String, (Vec<String>, Vec<(String, Type)>)>,
    /// Typestate (Epic 1): protocol name → its closed, ordered set of state-marker
    /// names (from `state Name { A, B }`). Consumed by `validate_lowered_type` to
    /// gate a state-position arg's membership (ST-5 → T276).
    pub(super) typestate_states: HashMap<String, Vec<String>>,
    /// Typestate (Epic 1): nominal name → the indices of its STATE-kinded type
    /// parameters (from `record Name<@S>`). Drives `resolve_type_expr_kinded` to
    /// resolve those arg positions to `Type::StateMarker`. A nominal appears here iff
    /// it has ≥1 `@S` param — i.e. the keys ARE the set of "typestate nominals".
    pub(super) typestate_state_positions: HashMap<String, Vec<usize>>,
    /// const_name → (declared_type, literal_value). Module-level `const NAME: T =
    /// LIT;`. Populated in `collect_type_universe`; a const REFERENCE in a fn body
    /// inlines its literal (`infer_path_expr`), since SIGIL `const` is otherwise
    /// declaration-only. Needed by the self-hosted compiler (named token tags /
    /// node kinds).
    pub(super) consts: HashMap<String, (Type, crate::ast::Literal)>,
    /// PR-E4: type-alias name → its UNRESOLVED body `TypeExpr`. `resolve_type_expr`
    /// expands a Named whose name is here by recursively resolving the body (so
    /// transitive aliases + aliases inside composites resolve for free). Only ACYCLIC
    /// aliases live here — cyclic ones are removed during collection (see
    /// `cyclic_aliases`) so the recursive expansion can never loop.
    pub(super) alias_bodies: HashMap<String, crate::ast::TypeExpr>,
    /// PR-E4: aliases that participate in a cycle (`type A = A;`, `type A = B; type B
    /// = A;`). Recorded during collection (where there is no diagnostic channel) and
    /// emitted as T263 by `check_collecting`. Excluded from `alias_bodies`, so a cyclic
    /// alias resolves to an opaque `Named` (never expands) — no infinite recursion.
    pub(super) cyclic_aliases: Vec<(String, crate::span::Span)>,
    /// Wall 4 Step 1: record_name → refinement clauses declared via
    /// `where field RELOP literal`. Empty Vec or missing entry means
    /// the record has no refinements. Populated in pass 2 of
    /// `collect_type_universe`. Consumed at
    /// `infer_record_construct_expr` to drive Z3 satisfiability checks
    /// via `build_refinement_query` in `z3_capability.rs`.
    pub(super) record_refinements: HashMap<String, Vec<crate::ast::RefinementClause>>,
    /// BoundedVec PR-1 (sealing): record_name → its DEFINING module. Populated in
    /// pass 2 of `collect_type_universe`. Read by `infer_record_construct_expr` to
    /// SEAL a record whose defining module is a `bounded_*` stdlib module — it may
    /// be constructed ONLY inside that module (via `new()`/methods), never via a
    /// direct record literal in user code (T258), so a bounded type's `len`
    /// invariant cannot be forged (`BoundedVec_i64_8 { len: 99 }`).
    pub(super) record_modules: HashMap<String, String>,
    /// type_name → (type_params, variants_with_possibly_generic_payload_types)
    pub(super) enums: HashMap<String, (Vec<String>, Vec<(String, Vec<Type>)>)>,
    /// Wall 4 Step 6: `(enum_name, variant_name)` → variant refinement
    /// clauses declared via `where <named_field> RELOP rhs` immediately
    /// after the variant's payload close-paren. Empty Vec or missing
    /// entry means the variant has no refinements. Populated in pass 2
    /// of `collect_type_universe`. Consumed at the
    /// `infer_call_expr` enum-variant branch to drive Z3
    /// satisfiability checks via `check_variant_refinements_at_construction`.
    pub(super) enum_variant_refinements:
        HashMap<(String, String), Vec<crate::ast::RefinementClause>>,
    /// Wall 4 Step 6: `(enum_name, variant_name)` → optional payload
    /// field names. Indexed positionally; `Some(name)` for named
    /// payload fields, `None` for positional. A variant is "all-named"
    /// iff every entry is `Some(_)`. The refinement dispatcher uses
    /// this to map declared field names back to argument positions at
    /// construction time (N9-S6 — the i-th binding maps to the i-th
    /// declared field).
    pub(super) enum_variant_field_names: HashMap<(String, String), Vec<Option<String>>>,
    /// Generic function definitions: fn_name → AST FnDef (for monomorphization)
    pub(super) generic_fns: HashMap<String, crate::ast::FnDef>,
    /// PR D: generic impl-method ASTs + impl-block type-params + owning
    /// module name, keyed by MODULE-QUALIFIED method name (per N8-PRD:
    /// `"{module}::{TypeName}::{method_name}"`). Populated for every
    /// impl method whose enclosing impl block has non-empty
    /// `type_params`. Non-generic impl methods are NOT registered
    /// here.
    ///
    /// Read by `infer_method_call_expr` at dispatch time to fetch the
    /// method's source AST so the body can be re-type-checked with
    /// concrete substituted params, then post-walked via
    /// `apply_subst_to_typed_function` (N1-PRD) so AIR lowering's
    /// `mangle_type` never sees `Type::Generic`.
    pub(super) generic_impl_methods: HashMap<String, (Vec<String>, crate::ast::FnDef, String)>,
    /// Authority registry: cap type name → authority names/bit indices
    pub(super) authority_registry: AuthorityRegistry,
    /// Effect registry: effect name → unique ID
    pub(super) effect_registry: EffectRegistry,
    /// Effect Handlers (EH1): effect name → its declared operations. Empty Vec
    /// (or absent key) = a bare marker effect. Populated from `EffectDecl.ops`.
    /// A `perform E.op(args)` resolves `op` here (E005 unknown op / E006 unknown
    /// effect) and checks its argument count (E007). BTreeMap for deterministic
    /// diagnostic order.
    pub(super) effect_ops: std::collections::BTreeMap<String, Vec<EffectOpInfo>>,
    /// Extern function names (for routing Call → ExternCall)
    pub(super) extern_fns: HashSet<String>,
    /// PR-3a (trait Wall): trait name → its resolved contract. Populated in
    /// pass 2 of `collect_type_universe`. The satisfaction check (PR-3b) verifies
    /// a concrete type provides every required method with a matching signature.
    /// BTreeMap for deterministic iteration (diagnostic order).
    pub(super) traits: std::collections::BTreeMap<String, TraitContract>,
}

/// A trait's resolved contract: required methods (name → (param types incl.
/// `self`, return type)). `Self` in a method type is kept as
/// `Type::Generic("Self")` and substituted to the implementing type when
/// satisfaction is checked (PR-3b).
#[derive(Debug, Clone)]
pub(super) struct TraitContract {
    pub(super) methods: std::collections::BTreeMap<String, (Vec<Type>, Type)>,
    /// HK2: for a HIGHER-KINDED trait (one whose methods use `Self` APPLIED, e.g.
    /// `Functor`'s `self: Self<A>`), the `("Self", arity)` of that implicit
    /// constructor slot. `None` for an ordinary trait (`Self` used bare, like
    /// `Hash`). When `Some`, the stored method `(params, ret)` types carry
    /// `HktApp { ctor: "Self", .. }` for the `Self<…>` positions, and a concrete
    /// `impl Trait for Ctor` is checked by substituting `Self -> TypeCtor(Ctor)`.
    pub(super) hkt_param: Option<(String, usize)>,
}

/// Accumulates monomorphized functions and concrete type layouts during type checking.
/// Drained into TypedProgram at the end of check().
/// One `for v in lo..hi { ... }` compile-time bounds fact - see
/// `MonomorphTracker::range_loop_facts` for the soundness contract.
#[derive(Debug, Clone)]
pub(super) struct RangeLoopFact {
    pub(super) var: String,
    pub(super) lo: i64,
    pub(super) hi_exclusive: i64,
}

pub(crate) struct MonomorphTracker {
    pub(super) functions: Vec<TypedFunction>,
    pub(super) records: HashMap<String, Vec<(String, Type)>>,
    pub(super) enums: HashMap<String, Vec<(String, Vec<Type>)>>,
    pub(super) cache: HashSet<String>,
    pub(super) depth: usize,
    /// Current enclosing function's effects — closures inherit this.
    pub(super) current_effects: EffectSet,
    /// Wall 4 Step 7 / N15-S7, N25-S7: declared return refinement for
    /// the function whose body is currently being type-checked. Set in
    /// `check_function_block` at function entry, cleared at exit. Mirror
    /// of `current_effects`. `check_return` consults this and emits T225
    /// when the returned expression violates it (literal-Sat or
    /// symbolic-no-subsumption). `None` outside any refined function
    /// body (the common case for unrefined fns).
    pub(super) current_return_refinement: Option<Vec<crate::ast::RefinementClause>>,
    // ── Cross-module dispatch context (Phase 5a) ─────────────────────────
    /// Workspace-wide function signature index, keyed by `(module, fn)`.
    /// Built once in `check()` from every module's `collect_function_sigs`.
    /// Cross-module call resolution consults this map.
    ///
    /// Phase 5a-1.6 / I29: BTreeMap (sorted iteration) so output-affecting
    /// code paths (e.g. `resolve_single_segment_in_use_scope`'s candidate
    /// enumeration) are deterministic. G4 (compiler determinism) requires
    /// this; HashMap iteration order would silently break it.
    pub(super) workspace_sigs:
        std::collections::BTreeMap<String, std::collections::BTreeMap<String, FunctionSig>>,
    /// Per-module ring lookup, used to detect cross-ring calls (R004).
    /// BTreeMap per I29.
    pub(super) module_rings: std::collections::BTreeMap<String, crate::ast::Ring>,
    /// `use` aliases for the *currently checking* module — set when we
    /// enter a module's body, restored when leaving. Cross-module call
    /// resolution consults this.
    ///
    /// Phase 5a-1.6 / Op A: kept as owned (clone-per-module). A
    /// borrow-based design would need lifetime annotations propagated
    /// through every body-checker, while a UseScope clone is a
    /// HashMap with typically 0–6 entries — cheap. Revisit when
    /// measurement justifies the refactor.
    pub(super) current_use_scope: crate::name_resolution::UseScope,
    /// Ring of the currently checking module.
    pub(super) current_module_ring: crate::ast::Ring,
    /// Wall 4 Step 6: stack of per-match-arm refinement attachments.
    /// Each entry maps a pattern-bound identifier name to the variant
    /// refinement clauses applicable to that binding (filtered per
    /// N22-S6 to `RefinementRhs::Literal` only — Field/LengthOf clauses
    /// are validated at construction, not propagated through bindings).
    /// `infer_match_stmt` pushes a fresh map at arm entry, populates
    /// it from the matched variant's `enum_variant_refinements`, and
    /// pops on arm exit. Nested `match`/`if let` chains stack
    /// correctly. `infer_path_expr` walks the stack top-down on
    /// single-segment local-variable lookups to attach the refinement
    /// to the returned `TypedExpr.refinement`.
    pub(super) pattern_refinement_stack: Vec<HashMap<String, Vec<crate::ast::RefinementClause>>>,
    /// RANGE-FOR (RF-M2): the MUTATION/SHADOW-PROOF bounds-fact channel - one
    /// entry per lexically-enclosing `for v in 0..K` whose fact survived the
    /// gates (literal-`0` start; `K` resolved Z3-FREE from a literal or an
    /// `arr.len()` on `[T; N]`; `K >= 1`; and the body PRE-SCAN found no
    /// rebinding of `v` anywhere in the body). Soundness is BY CONSTRUCTION,
    /// not flow tracking: the loop var is immutable (T042, and errors abort
    /// before AIR) and never rebound (pre-scan), so `v` is in
    /// `[lo, hi_exclusive)` at every body program point. Closure and
    /// handle-clause bodies are BARRIERED (the channel is `mem::take`n around
    /// their `check_block`) - they are lambda-lifted into DIFFERENT functions
    /// whose binders may shadow the name. Sole writer: the `check_block`
    /// ForRange arm; sole consumer: `infer_index_expr`. Z3 is never consulted
    /// - the elision this feeds stays out of the memory-safety TCB (SC-6).
    pub(super) range_loop_facts: Vec<RangeLoopFact>,
    /// PR A / N15-PRA: expected type at the current expression
    /// position. Set by `check_let` when a let-binding has a type
    /// annotation (e.g., `let h: Holder<i64> = ...`); restored via a
    /// RAII drop-guard when the let's value expression finishes
    /// type-checking. Read by `infer_record_construct_expr` to seed
    /// the substitution map from annotation type-args before field-
    /// value inference runs.
    ///
    /// `None` at function entry and between let bindings. Per AG-PRA-7
    /// the threading is intentionally LIMITED — does not propagate
    /// through `if/else` arms or `match`-arms; only direct
    /// `let x: T = expr` paths surface this expected type to the
    /// construction site.
    pub(super) current_expected_type: Option<Type>,
    /// PR AF / N18-AF + N22-AF: tracks whether the IMMEDIATE
    /// syntactic parent of the expression currently being inferred
    /// is `Expr::Borrow`. Set ONLY inside `BorrowContextGuard::new`
    /// (from `infer_borrow_expr` right before recursing into its
    /// inner expression); cleared by the guard's `Drop`.
    /// `infer_slice_expr` reads this flag to decide whether to fire
    /// T238 — `&arr[0..3]` admits, bare `arr[0..3]` does not.
    ///
    /// CRITICAL: let-annotations, return-type annotations, and
    /// function-arg expected-type DO NOT write this flag.
    /// "Immediate" means EXACTLY the parent `Expr::Borrow` AST
    /// node; any wrapping (a let-binding's value, a return
    /// expression, etc.) clears the flag before recursion.
    pub(super) parent_is_immediate_borrow: bool,
    /// Mutation-as-capability (PR-1, NC-1): names of `@ReadOnly` parameters AND
    /// locals that inherit readonly via propagation (`let b = p` makes `b`
    /// readonly). Seeded from the `@ReadOnly` params in `check_function_block`
    /// (saved/restored around the body like `current_return_refinement`), grown
    /// monotonically in `check_block`'s let-handler, read by the `check_assign`
    /// WRITE gate. ONE append-only set per function body — no branch-sensitive
    /// removal (conservative, fail-closed).
    pub(super) readonly_locals: HashSet<String>,
    /// Regions (DEF-2a, LD-1): birth-DEPTH of each heap value rooted at a local —
    /// the region nesting depth at which it was allocated (absent/0 = function/heap
    /// lifetime; deeper = shorter-lived). Mirrors `readonly_locals` but depth-valued
    /// because regions nest and the escape rule is directional ("point up, never
    /// down", `reject ⟺ birth_depth > scope_depth`). PRUNED on region exit (unlike
    /// the append-only readonly set) and saved/restored across function-body /
    /// monomorph re-entry so depth never leaks across boundaries (NC-R5).
    pub(super) region_locals: HashMap<String, RegionId>,
    /// Regions (DEF-2a): the current region nesting depth (0 outside any region;
    /// `+1` per `region {}` entered). The cursor `region_locals` records against.
    pub(super) current_region_depth: u32,
    /// break/continue: current loop nesting depth (0 outside any loop; `+1` per
    /// `while`/`for-in` body entered). `break`/`continue` are valid iff this is `> 0`.
    pub(super) loop_depth: u32,
    /// Regions (DEF-2b, LD-2/LD-6): the param→region-slot map for the function body
    /// currently being checked. A `Region` parameter maps to its OWN position; an
    /// `@in r` parameter maps to the position of the `Region` parameter `r`. Seeded at
    /// `check_function_block` entry and saved/restored via `mem::take`/`mem::replace`
    /// like `region_locals`, so monomorph re-entry never inherits the caller's region
    /// params (NC-2b-3). `region_of_value` reads it to return `Param(slot)` for these
    /// names, which is what makes the callee honor `@in` (LD-6) and lets the lift map a
    /// region argument to a caller-side `RegionId`. Empty without region params (the
    /// common case) → byte-identical for all pre-DEF-2b code.
    pub(super) current_param_regions: HashMap<String, u32>,
    /// Regions (DEF-2b, LD-4 / PR-5): the declared `where region(a): region(b)` outlives
    /// pairs of the function body currently being checked, as `(a_slot, b_slot)` meaning
    /// `Param(a_slot)` outlives `Param(b_slot)`. Seeded from the sig's
    /// `param_region_outlives` at `check_function_block` entry and saved/restored like
    /// `current_param_regions`. Consulted by `check_region_escape` — the ONLY thing that
    /// makes `Param(a) outlives Param(b)` true for `a != b` (DIRECT-PAIR-ONLY, AG-2b-9).
    /// Empty without a `where region` clause → byte-identical for all pre-PR-5 code.
    pub(super) current_region_outlives: Vec<(u32, u32)>,
    /// Exclusivity (DEF-2c, LD-1): the alias-origin map for the function body currently being
    /// checked — a binding → the ROOT local whose heap object it aliases (`let b = <aliasable
    /// place>` records `b → resolve(root(place))`; any other RHS makes `b` its own root, so a
    /// re-binding clears a stale alias — NC-2c-4 write-per-`let`). Seeded EMPTY at every
    /// function-body entry (a parameter is its own origin — the callee cannot know caller
    /// aliasing), grown in `check_block`'s let-handler, saved/restored via `mem::take` like
    /// `readonly_locals`. Read by the call/method exclusivity gate to resolve a `let`-laundered
    /// argument (`let y = x; f(x, y)`) back to its root before the frozen×mutable overlap test.
    /// Empty when nothing aliasable is let-bound (the common case) → byte-identical.
    pub(super) alias_origin: HashMap<String, String>,
    /// Actor-state (immutable-after-init): state field name → declared type, for
    /// the function body currently being checked. Non-empty ONLY inside an actor
    /// `init`/handler body (seeded/restored in `check_function_block` like
    /// `readonly_locals`). State fields are deliberately NOT seeded into the type
    /// env, so `infer_path_expr` resolves params/locals FIRST (any binding
    /// naturally shadows) and falls back to this map only for an otherwise-unbound
    /// name — which it then emits as a `TypedExprKind::StateField`. Empty for
    /// module functions, closures, and methods.
    pub(super) state_fields: HashMap<String, Type>,
    /// The subset of `state_fields` declared `mut`.
    /// A handler write to one of these is PERMITTED (T123 relaxed); a write to any
    /// other state field is still rejected. Empty for non-actor bodies and for
    /// actors with no `mut` fields.
    pub(super) mut_state_fields: std::collections::HashSet<String>,
    /// PPS-0: nonzero while building a STATE-BACKED mono instance's body. A `Map`'s persistence
    /// needs allocations made in CALLEES (`ensure_buckets`/`grow`/`filled`, and the interior
    /// `Vec::push`es), not just at the routed call site — so any generic instance built beneath a
    /// state-backed one is itself state-backed. Zero everywhere else, so a state-free module never
    /// sees a `$state` instance and stays byte-identical.
    pub(super) state_mono_depth: usize,
    /// Which construction/handler context the current body is — gates state
    /// writes (M2: writable iff `Init`) and, later, state-cap consumption
    /// (M4: consumable iff `Init`/`EntryStart`). `Free` for non-actor bodies.
    pub(super) body_kind: BodyKind,
}

/// The construction/handler context of the function body being checked.
/// Distinguishes the two boot-time carve-out predicates: state WRITE is allowed
/// iff `Init`; state-cap CONSUME (M4) iff `Init | EntryStart`. Every other
/// handler is steady-state and borrow-only.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(super) enum BodyKind {
    /// Module function, closure, impl method — no actor state in scope.
    #[default]
    Free,
    /// An actor `init` block — state is writable here (the sole write site).
    Init,
    /// The entry actor's `Start` handler — the boot handler. State is read-only
    /// (populated by the runtime), but state caps may be consumed here (M4).
    EntryStart,
    /// An ordinary message handler — state read-only, state caps borrow-only.
    Handler,
}

/// The lifetime region of an aliasable value. `Global` is longest-lived,
/// `Lexical(d)` becomes shorter-lived as `d` increases, and `Param(slot)` is
/// supplied through a function's `Region` parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RegionId {
    Global,
    /// A region passed through a `Region` or `@in r` parameter.
    Param(u32),
    Lexical(u32),
}

impl RegionId {
    /// Map depth zero to `Global` and positive depths to lexical regions.
    pub(super) fn from_depth(depth: u32) -> Self {
        if depth == 0 {
            RegionId::Global
        } else {
            RegionId::Lexical(depth)
        }
    }

    /// Return whether a value in `self` may flow into `sink`. Distinct parameter
    /// regions are incomparable here; direct `where region` edges are checked separately.
    pub(super) fn outlives_or_equal(self, sink: RegionId) -> bool {
        use RegionId::*;
        match (self, sink) {
            (Global, _) => true,            // Global outlives everything
            (_, Global) => false,           // only Global reaches a fn-lifetime sink
            (Param(a), Param(b)) => a == b, // distinct param regions incomparable (pre-PR-5)
            (Param(_), Lexical(_)) => true, // a passed-in region outlives any body region
            (Lexical(_), Param(_)) => false,
            (Lexical(a), Lexical(b)) => a <= b, // DEF-2a: shallower outlives deeper
        }
    }
}

impl MonomorphTracker {
    pub(super) fn new() -> Self {
        Self {
            functions: Vec::new(),
            records: HashMap::new(),
            enums: HashMap::new(),
            cache: HashSet::new(),
            depth: 0,
            current_effects: EffectSet::empty(),
            current_return_refinement: None,
            workspace_sigs: std::collections::BTreeMap::new(),
            module_rings: std::collections::BTreeMap::new(),
            current_use_scope: crate::name_resolution::UseScope::default(),
            current_module_ring: crate::ast::Ring::Inner,
            pattern_refinement_stack: Vec::new(),
            range_loop_facts: Vec::new(),
            current_expected_type: None,
            parent_is_immediate_borrow: false,
            readonly_locals: HashSet::new(),
            region_locals: HashMap::new(),
            current_region_depth: 0,
            loop_depth: 0,
            current_param_regions: HashMap::new(),
            current_region_outlives: Vec::new(),
            alias_origin: HashMap::new(),
            state_fields: HashMap::new(),
            mut_state_fields: HashSet::new(),
            state_mono_depth: 0,
            body_kind: BodyKind::Free,
        }
    }
}

/// PR A / N15-PRA: RAII guard for the let-annotation expected-type
/// context. Constructed by `check_let` before recursing into the
/// value expression; `Drop` restores the prior `current_expected_type`
/// so nested or sibling let bindings see the right context (no leak).
/// Borrows the tracker mutably so the caller accesses the tracker
/// via `guard.tracker_mut()` while the guard is live.
pub(super) struct ExpectedTypeGuard<'a> {
    pub(super) tracker: &'a mut MonomorphTracker,
    pub(super) previous: Option<Type>,
}

impl<'a> ExpectedTypeGuard<'a> {
    pub(super) fn push(tracker: &'a mut MonomorphTracker, new: Option<Type>) -> Self {
        let previous = tracker.current_expected_type.take();
        tracker.current_expected_type = new;
        Self { tracker, previous }
    }

    /// Access the wrapped tracker. Use via `guard.tracker_mut()` to
    /// pass into functions that need `&mut MonomorphTracker` while
    /// preserving the guard's drop-on-scope-exit behavior.
    pub(super) fn tracker_mut(&mut self) -> &mut MonomorphTracker {
        self.tracker
    }
}

impl Drop for ExpectedTypeGuard<'_> {
    fn drop(&mut self) {
        self.tracker.current_expected_type = self.previous.take();
    }
}

/// PR AF / N18-AF + N22-AF: RAII guard for the
/// `parent_is_immediate_borrow` flag. `infer_borrow_expr`
/// constructs the guard with `enter()` IMMEDIATELY before recursing
/// into its inner expression; the guard's `Drop` restores the prior
/// flag value when the inner inference returns.
///
/// Per N22-AF, this struct is the SOLE writer of
/// `MonomorphTracker.parent_is_immediate_borrow`. Two writer sites
/// total: `enter()` (set true) and `Drop::drop` (restore prior).
/// CI grep-lint in commit #6 enforces this canonicality.
///
/// Critical correctness note: ANY recursion into a non-Borrow
/// child of a Borrow expression must clear the flag first. The
/// current `infer_borrow_expr` only has one direct child (`inner`),
/// so the guard's enter()-drop-on-recursion-return pattern works
/// uniformly. Future modifications to `infer_borrow_expr` that
/// add additional children (e.g., side conditions) must scope each
/// to its own guard frame.
pub(super) struct BorrowContextGuard<'a> {
    pub(super) tracker: &'a mut MonomorphTracker,
    pub(super) previous: bool,
}

impl<'a> BorrowContextGuard<'a> {
    /// Set `parent_is_immediate_borrow = true`; return a guard
    /// whose `Drop` restores the prior value.
    pub(super) fn enter(tracker: &'a mut MonomorphTracker) -> Self {
        let previous = tracker.parent_is_immediate_borrow;
        tracker.parent_is_immediate_borrow = true;
        Self { tracker, previous }
    }

    pub(super) fn tracker_mut(&mut self) -> &mut MonomorphTracker {
        self.tracker
    }
}

impl Drop for BorrowContextGuard<'_> {
    fn drop(&mut self) {
        self.tracker.parent_is_immediate_borrow = self.previous;
    }
}

pub(super) const MAX_MONOMORPH_DEPTH: usize = 64;

#[cfg(test)]
mod region_lattice_tests {
    use super::RegionId;

    /// Regions (DEF-2b, NC-2b-6): pin the outlives lattice over all 9 `RegionId ×
    /// RegionId` cells — reflexivity, totality, and directionality — INCLUDING the
    /// `Param` arms that PR-0 does not yet construct. A flipped arm (the highest-risk
    /// silent-drift bug in the PR-0 refactor) fails this test before it can detonate in
    /// PR-4. `outlives_or_equal(a, b)` ⟺ a value living in `a` may flow into a sink in `b`.
    #[test]
    fn region_outlives_lattice_is_total_and_directional() {
        use RegionId::{Global, Lexical, Param};

        // The full 9-cell truth table (a, b, a.outlives_or_equal(b)).
        let cells = [
            // Global outlives everything (longest-lived).
            (Global, Global, true),
            (Global, Param(0), true),
            (Global, Lexical(1), true),
            // Only Global reaches a Global (function-lifetime) sink.
            (Param(0), Global, false),
            (Lexical(1), Global, false),
            // A passed-in region outlives any region opened in this body.
            (Param(0), Lexical(1), true),
            (Lexical(1), Param(0), false),
            // Distinct param regions are incomparable (pre-PR-5); identity holds.
            (Param(0), Param(0), true),
            (Param(0), Param(1), false),
            // DEF-2a lexical rule: shallower (smaller depth) outlives deeper.
            (Lexical(1), Lexical(1), true),
            (Lexical(1), Lexical(2), true),
            (Lexical(2), Lexical(1), false),
        ];
        for (a, b, expected) in cells {
            assert_eq!(
                a.outlives_or_equal(b),
                expected,
                "outlives_or_equal({a:?}, {b:?}) should be {expected}"
            );
        }

        // Reflexivity: a value may always flow into its OWN region (load-bearing — every
        // same-region store relies on it; AG-2b-9 keeps this an invariant, not a goal).
        for r in [Global, Param(0), Param(7), Lexical(1), Lexical(5)] {
            assert!(r.outlives_or_equal(r), "reflexivity must hold for {r:?}");
        }

        // `from_depth` collapses 0 → Global, d>0 → Lexical(d) (the DEF-2a byte-identity).
        assert_eq!(RegionId::from_depth(0), Global);
        assert_eq!(RegionId::from_depth(1), Lexical(1));
        assert_eq!(RegionId::from_depth(3), Lexical(3));
    }
}

#[cfg(test)]
mod type_check_context_tests {
    use std::collections::{BTreeMap, HashMap};

    use proptest::prelude::*;

    use super::{ActorSig, FunctionSig, TypeCheckContext, TypeUniverse};

    proptest! {
        #[test]
        fn context_borrows_shared_catalogs_without_changing_module_name(
            module_name in "[A-Za-z_][A-Za-z0-9_]{0,31}",
        ) {
            let function_sigs = BTreeMap::<String, FunctionSig>::new();
            let actor_sigs = HashMap::<String, ActorSig>::new();
            let universe = TypeUniverse::default();
            let context = TypeCheckContext::new(
                &function_sigs,
                &actor_sigs,
                &module_name,
                &universe,
            );

            prop_assert!(std::ptr::eq(context.function_sigs, &function_sigs));
            prop_assert!(std::ptr::eq(context.actor_sigs, &actor_sigs));
            prop_assert!(std::ptr::eq(context.universe, &universe));
            prop_assert_eq!(context.module_name, module_name.as_str());
        }
    }
}
