//! Type-universe construction passes.
//!
//! Pure setup-pass functions called from `check_with_options` BEFORE
//! body type-checking begins. They take read-only inputs (AST, an
//! already-built universe where applicable) and produce data structures
//! the body checker consults.
//!
//! ## Functions
//!
//! - [`collect_type_universe`] — walks every AST item once to build the
//!   `TypeUniverse` (actors, caps, records, enums, generic fns, etc.).
//!   Two passes: (1) collect type names, (2) resolve fields/variants.
//! - [`collect_actor_sigs`] — walks `ActorDef` items, builds an
//!   `ActorSig` map keyed by actor name.
//! - [`collect_function_sigs`] — walks one module's items, builds a
//!   `FunctionSig` BTreeMap consulted by cross-module dispatch.
//!   Increments the I16 `COLLECT_FUNCTION_SIGS_CALL_COUNT` thread-local
//!   so the single-pass-discipline test can verify it runs once per
//!   module.
//! - [`build_actor_env`] / [`build_actor_captures`] — derive per-actor
//!   scope helpers from declared state fields.
//!
//! Extracted from `type_check/mod.rs` in structural-extraction PR 2.
//! Verbatim move — zero logic change. The shadow CI gate from PR 2.0
//! validates byte-equality of every diagnostic produced downstream.

use std::collections::HashMap;

use super::{
    ActorSig, COLLECT_FUNCTION_SIGS_CALL_COUNT, FunctionSig, HandlerSig, ParamRegion,
    ReassignRejection, TraitContract, Type, TypeUniverse, classify_reassign_rejection,
    resolve_type, resolve_type_expr, resolve_type_expr_kinded, type_is_reassignable,
};
use crate::ast::{ActorDef, Item, Mutability};
use crate::diagnostics::{Diagnostic, codes};
use crate::registries::{AuthorityRegistry, EffectRegistry};
use crate::typed_ast::TypedParam;

/// PR-E4: collect every `type Name = Body;` alias, detect cycles via DFS over the
/// alias-reference graph, and populate `universe.alias_bodies` (acyclic only) +
/// `universe.cyclic_aliases` (the rest, reported as T263 by `check_collecting`). A
/// duplicate alias name is an N002 caught in name-resolution; here first-def wins.
fn collect_type_aliases(program: &crate::ast::Program, universe: &mut TypeUniverse) {
    use std::collections::HashSet;
    let mut bodies: HashMap<String, (crate::ast::TypeExpr, crate::span::Span)> = HashMap::new();
    for module in &program.modules {
        for item in &module.items {
            if let Item::TypeAlias(def) = item {
                bodies
                    .entry(def.name.clone())
                    .or_insert_with(|| (def.body.clone(), def.span));
            }
        }
    }
    if bodies.is_empty() {
        return;
    }
    let names: HashSet<String> = bodies.keys().cloned().collect();
    let mut edges: HashMap<String, Vec<String>> = HashMap::new();
    for (name, (body, _)) in &bodies {
        let mut refs = Vec::new();
        collect_alias_refs(body, &names, &mut refs);
        edges.insert(name.clone(), refs);
    }
    let cyclic = find_cyclic_aliases(&names, &edges);
    for (name, (body, span)) in bodies {
        if cyclic.contains(&name) {
            universe.cyclic_aliases.push((name, span));
        } else {
            universe.alias_bodies.insert(name, body);
        }
    }
}

/// PR-E4: append every alias-name (∈ `aliases`) referenced anywhere in `ty` — the
/// nominal path name, its type-args, and any fn/array/tuple sub-types — so the cycle
/// detector sees a COMPLETE edge set (a missed edge could leave a cyclic alias in
/// `alias_bodies` and hang the recursive `resolve_type_expr` expansion).
fn collect_alias_refs(
    ty: &crate::ast::TypeExpr,
    aliases: &std::collections::HashSet<String>,
    out: &mut Vec<String>,
) {
    if let Some(fnt) = &ty.fn_type {
        for p in &fnt.params {
            collect_alias_refs(p, aliases, out);
        }
        collect_alias_refs(&fnt.return_type, aliases, out);
        return;
    }
    if let Some(arr) = &ty.array_type {
        collect_alias_refs(&arr.elem, aliases, out);
        return;
    }
    if let Some(elems) = &ty.tuple_type {
        for e in elems {
            collect_alias_refs(e, aliases, out);
        }
        return;
    }
    let name = ty.path.display_name();
    if aliases.contains(&name) {
        out.push(name);
    }
    for arg in &ty.path.type_args {
        collect_alias_refs(arg, aliases, out);
    }
}

/// PR-E4: the set of alias names lying ON a cycle in the alias-reference graph
/// (iterative 3-color DFS; a back edge marks every node from the target up to the
/// current node). A name that merely REACHES a cycle is NOT flagged — once the cyclic
/// target is excluded from `alias_bodies` it resolves to an opaque `Named`.
fn find_cyclic_aliases(
    names: &std::collections::HashSet<String>,
    edges: &HashMap<String, Vec<String>>,
) -> std::collections::HashSet<String> {
    use std::collections::HashSet;
    let mut cyclic: HashSet<String> = HashSet::new();
    let mut color: HashMap<String, u8> = HashMap::new(); // 0=unvisited, 1=on-stack, 2=done
    for start in names {
        if color.get(start).copied().unwrap_or(0) != 0 {
            continue;
        }
        let mut stack: Vec<(String, usize)> = vec![(start.clone(), 0)];
        color.insert(start.clone(), 1);
        while let Some((node, idx)) = stack.last().cloned() {
            let node_edges = edges.get(&node).map(Vec::as_slice).unwrap_or(&[]);
            if idx < node_edges.len() {
                stack.last_mut().unwrap().1 += 1;
                let next = node_edges[idx].clone();
                match color.get(&next).copied().unwrap_or(0) {
                    0 => {
                        color.insert(next.clone(), 1);
                        stack.push((next, 0));
                    }
                    1 => {
                        let pos = stack.iter().position(|(n, _)| n == &next).unwrap();
                        for (n, _) in &stack[pos..] {
                            cyclic.insert(n.clone());
                        }
                    }
                    _ => {}
                }
            } else {
                color.insert(node, 2);
                stack.pop();
            }
        }
    }
    cyclic
}

/// HK2: the arity of an APPLIED `Self` (`Self<A>` → 1, `Self<K, V>` → 2) found
/// anywhere in a trait's method signatures, or `None` if `Self` is only ever used
/// bare (an ordinary trait like `Hash`). A `Some(n)` makes the trait HIGHER-KINDED:
/// `Self` is its implicit `* -> …` constructor slot.
fn trait_self_arity(def: &crate::ast::TraitDef) -> Option<usize> {
    fn scan(ty: &crate::ast::TypeExpr, found: &mut Option<usize>) {
        if let Some(elems) = &ty.tuple_type {
            for e in elems {
                scan(e, found);
            }
        }
        if let Some(fn_ty) = &ty.fn_type {
            for p in &fn_ty.params {
                scan(p, found);
            }
            scan(&fn_ty.return_type, found);
        }
        if let Some(arr) = &ty.array_type {
            scan(&arr.elem, found);
        }
        if ty.path.segments.len() == 1
            && ty.path.segments[0] == "Self"
            && !ty.path.type_args.is_empty()
        {
            *found = Some(ty.path.type_args.len());
        }
        for a in &ty.path.type_args {
            scan(a, found);
        }
    }
    let mut found = None;
    for m in &def.methods {
        for p in &m.params {
            scan(&p.ty, &mut found);
        }
        if let Some(ret) = &m.return_type {
            scan(ret, &mut found);
        }
    }
    found
}

/// Effect Handlers (EH3): resolve an effect operation's return type. `None` (no
/// `->`) is unit; a bare `never` is the abortive bottom `Type::Never`
/// (recognized HERE only — `never` is non-denotable in general type position);
/// everything else resolves normally.
fn resolve_op_return(ret: Option<&crate::ast::TypeExpr>, universe: &TypeUniverse) -> Type {
    match ret {
        None => Type::Unit,
        Some(te) => {
            if te.ref_kind.is_none()
                && te.fn_type.is_none()
                && te.path.segments.len() == 1
                && te.path.segments[0] == "never"
            {
                Type::Never
            } else {
                resolve_type_expr(te, universe, &HashMap::new(), &[])
            }
        }
    }
}

pub(super) fn collect_type_universe(program: &crate::ast::Program) -> TypeUniverse {
    let mut universe = TypeUniverse {
        actors: std::collections::HashSet::new(),
        caps: std::collections::HashSet::new(),
        parametric_caps: HashMap::new(),
        mintable_caps: HashMap::new(),
        build_deadline: None,
        records: HashMap::new(),
        typestate_states: HashMap::new(),
        typestate_state_positions: HashMap::new(),
        consts: HashMap::new(),
        alias_bodies: HashMap::new(),
        cyclic_aliases: Vec::new(),
        record_modules: HashMap::new(),
        record_refinements: HashMap::new(),
        enums: HashMap::new(),
        enum_variant_refinements: HashMap::new(),
        enum_variant_field_names: HashMap::new(),
        generic_fns: HashMap::new(),
        generic_impl_methods: HashMap::new(),
        authority_registry: AuthorityRegistry::default(),
        extern_fns: std::collections::HashSet::new(),
        effect_registry: {
            let mut reg = EffectRegistry::default();
            reg.register("FFI"); // built-in
            reg.register("Unsafe"); // built-in
            reg
        },
        effect_ops: std::collections::BTreeMap::new(),
        traits: std::collections::BTreeMap::new(),
    };

    // PR-E4: collect type-alias bodies + detect cycles BEFORE field resolution
    // (pass 2) expands aliases via `resolve_type_expr` — a cyclic alias left in
    // `alias_bodies` would recurse forever. Cyclic aliases are EXCLUDED from
    // `alias_bodies` (so they resolve to an opaque `Named`, never expanding) and
    // recorded in `cyclic_aliases` for `check_collecting` to report as T263.
    collect_type_aliases(program, &mut universe);

    // Pass 1: collect type names (needed for lower_type resolution)
    for module in &program.modules {
        for item in &module.items {
            match item {
                Item::ActorDef(def) => {
                    universe.actors.insert(def.name.clone());
                }
                Item::CapTypeDef(def) => {
                    universe.caps.insert(def.name.clone());
                    universe
                        .authority_registry
                        .register(&def.name, &def.authorities);
                    // Wall 2 → Wall 3: register every parametric cap
                    // by its full parameter list. Non-parametric caps
                    // (empty params) are excluded — validate_lowered_type
                    // distinguishes "not in map" from "in map with N
                    // params" to drive T196/T197/T201.
                    if !def.params.is_empty() {
                        universe
                            .parametric_caps
                            .insert(def.name.clone(), def.params.clone());
                    }
                    // Capabilities-as-values: record the minting policy so
                    // `mint` can gate on it. Absent ⇒ non-mintable (T272).
                    if let Some(policy) = &def.mintable_by {
                        universe
                            .mintable_caps
                            .insert(def.name.clone(), policy.clone());
                    }
                }
                Item::ConstDef(def) => {
                    // `const NAME: T = LIT;` — a const value is a LITERAL, so the
                    // declared type is a primitive (i64/f64/bool/str), resolvable
                    // with the partial pass-1 universe. A const REFERENCE inlines
                    // this literal in `infer_path_expr` (SIGIL `const` is otherwise
                    // declaration-only). Last write wins on a duplicate name; a
                    // declared-vs-value type mismatch is the T040 in `check()`.
                    let ty = resolve_type_expr(&def.ty, &universe, &HashMap::new(), &[]);
                    universe.consts.insert(
                        format!("{}::{}", module.name, def.name),
                        (ty.clone(), def.value.clone()),
                    );
                    universe
                        .consts
                        .insert(def.name.clone(), (ty, def.value.clone()));
                }
                Item::StateDef(def) => {
                    // Typestate (Epic 1): a `state Name { A, B }` protocol → its closed,
                    // ordered marker set. Last write wins on a duplicate name.
                    universe
                        .typestate_states
                        .insert(def.name.clone(), def.states.clone());
                }
                Item::RecordDef(def) => {
                    // Typestate (Epic 1): record the indices of STATE-kinded params
                    // (`record File<@S>`) in Pass 1 — only positions are needed, and
                    // having them BEFORE Pass-2 field resolution lets a field typed
                    // `Stateful<Marker>` resolve its state arg correctly regardless of
                    // declaration order.
                    let state_positions: Vec<usize> = def
                        .type_params
                        .iter()
                        .enumerate()
                        .filter(|(_, p)| matches!(p.kind, crate::ast::ParamKind::State))
                        .map(|(i, _)| i)
                        .collect();
                    if !state_positions.is_empty() {
                        universe
                            .typestate_state_positions
                            .insert(def.name.clone(), state_positions);
                    }
                }
                _ => {}
            }
        }
    }

    // Pass 2: resolve record field types (lower_type needs actors/caps from pass 1)
    for module in &program.modules {
        for item in &module.items {
            match item {
                Item::RecordDef(def) => {
                    let fields = def
                        .fields
                        .iter()
                        .map(|f| {
                            (
                                f.name.clone(),
                                resolve_type_expr(
                                    &f.ty,
                                    &universe,
                                    &HashMap::new(),
                                    &crate::ast::type_param_names(&def.type_params),
                                ),
                            )
                        })
                        .collect();
                    universe.records.insert(
                        def.name.clone(),
                        (crate::ast::type_param_names(&def.type_params), fields),
                    );
                    // BoundedVec PR-1 (sealing): remember each record's defining
                    // module so `infer_record_construct_expr` can construction-seal
                    // a `bounded_*` record to its own module (T258).
                    universe
                        .record_modules
                        .insert(def.name.clone(), module.name.clone());
                    // Wall 4 Step 1: carry refinement clauses through the
                    // type universe so `infer_record_construct_expr` can
                    // discharge them. Empty Vec when the record has no
                    // `where` clause — the common case.
                    //
                    // Wall 4 Step 5 commit #2: declaration-time T217
                    // validation runs in `check()` AFTER this universe
                    // pass completes (we don't have diagnostics access
                    // here). See `validate_refinement_shapes_at_decls`.
                    if !def.refinements.is_empty() {
                        universe
                            .record_refinements
                            .insert(def.name.clone(), def.refinements.clone());
                    }
                }
                Item::EnumDef(def) => {
                    let variants = def
                        .variants
                        .iter()
                        .map(|v| {
                            let payload: Vec<Type> = v
                                .fields
                                .iter()
                                .map(|f| {
                                    // Wall 4 Step 6: variant field is
                                    // now `EnumVariantField { name, ty,
                                    // span }`; resolve from `.ty`.
                                    resolve_type_expr(
                                        &f.ty,
                                        &universe,
                                        &HashMap::new(),
                                        &crate::ast::type_param_names(&def.type_params),
                                    )
                                })
                                .collect();
                            (v.name.clone(), payload)
                        })
                        .collect();
                    universe.enums.insert(
                        def.name.clone(),
                        (crate::ast::type_param_names(&def.type_params), variants),
                    );

                    // Wall 4 Step 6: record per-variant refinements +
                    // payload field names. The construction-site
                    // dispatcher at `infer_call_expr`'s enum-variant
                    // branch consults these maps. Empty / missing
                    // entries are the common case (refinement-less
                    // variants) and represented absent.
                    for v in &def.variants {
                        let key = (def.name.clone(), v.name.clone());
                        if !v.refinements.is_empty() {
                            universe
                                .enum_variant_refinements
                                .insert(key.clone(), v.refinements.clone());
                        }
                        let field_names: Vec<Option<String>> =
                            v.fields.iter().map(|f| f.name.clone()).collect();
                        universe.enum_variant_field_names.insert(key, field_names);
                    }
                }
                Item::FnDef(def) if !def.type_params.is_empty() => {
                    universe.generic_fns.insert(def.name.clone(), def.clone());
                }
                // PR D: register every method that needs dispatch-time
                // monomorphization for later body re-checking. A method needs it
                // if the IMPL block is generic (`impl Box<T>`) OR the METHOD has
                // its OWN type parameters (`fn fmap<A, B>` — including on a
                // NON-generic impl like `impl Functor for Box`, the HK2 case).
                // A truly monomorphic method (neither) compiles once via the
                // pre-PR-D one-shot path and is NOT registered.
                //
                // Key per N8-PRD: MODULE-QUALIFIED to disambiguate
                // identically-named impls across modules.
                Item::ImplDef(impl_def)
                    if !impl_def.type_params.is_empty()
                        || impl_def.methods.iter().any(|m| !m.type_params.is_empty()) =>
                {
                    for method in &impl_def.methods {
                        if impl_def.type_params.is_empty() && method.type_params.is_empty() {
                            continue; // monomorphic method — one-shot path
                        }
                        let key =
                            format!("{}::{}::{}", module.name, impl_def.type_name, method.name);
                        universe.generic_impl_methods.insert(
                            key,
                            (
                                crate::ast::type_param_names(&impl_def.type_params),
                                method.clone(),
                                module.name.clone(),
                            ),
                        );
                    }
                }
                Item::EffectDecl(def) => {
                    universe.effect_registry.register(&def.name);
                    // Effect Handlers (EH1/EH3): record the effect's operations
                    // with resolved parameter/return types so a `perform`/clause
                    // can arity-check (E007), type its arguments, bind its clause
                    // binders, and type `resume`. Resolved in pass 2, so every
                    // nominal type an operation references is already known. An
                    // abortive operation's `-> never` return maps to `Type::Never`
                    // (recognized syntactically here — `never` is non-denotable
                    // elsewhere).
                    if !def.ops.is_empty() {
                        let ops = def
                            .ops
                            .iter()
                            .map(|op| crate::type_check::types::EffectOpInfo {
                                name: op.name.clone(),
                                params: op
                                    .params
                                    .iter()
                                    .map(|p| {
                                        resolve_type_expr(&p.ty, &universe, &HashMap::new(), &[])
                                    })
                                    .collect(),
                                param_taints: op
                                    .params
                                    .iter()
                                    .map(|p| p.taint.unwrap_or(crate::ast::TaintLabel::Public))
                                    .collect(),
                                ret: resolve_op_return(op.return_type.as_ref(), &universe),
                            })
                            .collect();
                        universe.effect_ops.insert(def.name.clone(), ops);
                    }
                }
                Item::ExternFnDecl(def) => {
                    universe.extern_fns.insert(def.name.clone());
                }
                Item::TraitDef(def) => {
                    // PR-3a: register the trait contract. Method param/return
                    // types resolve with "Self" in scope, so a `Self` named-type
                    // becomes `Generic("Self")` — substituted to the implementing
                    // type at satisfaction time (PR-3b).
                    //
                    // HK2: a trait is HIGHER-KINDED if any method uses `Self`
                    // APPLIED (`Self<A>`); then `Self` is the implicit constructor
                    // slot of that arity, threaded as an HKT binder so `Self<A>`
                    // resolves to `HktApp { ctor: "Self", .. }` (a concrete
                    // `impl Trait for Box` then substitutes `Self -> TypeCtor(Box)`).
                    let hkt_param = trait_self_arity(def).map(|arity| ("Self".to_string(), arity));
                    let in_scope_hkt: Vec<(String, usize)> =
                        hkt_param.clone().into_iter().collect();
                    let mut methods = std::collections::BTreeMap::new();
                    for m in &def.methods {
                        // The method's own type params (`A`, `B`) are ordinary
                        // generics in scope; `Self` is an in-scope GENERIC only for
                        // an ordinary trait — for a higher-kinded trait it is the
                        // HKT binder threaded via `in_scope_hkt`.
                        let mut in_scope_generics = crate::ast::type_param_names(&m.type_params);
                        if hkt_param.is_none() {
                            in_scope_generics.push("Self".to_string());
                        }
                        let params: Vec<Type> = m
                            .params
                            .iter()
                            .map(|p| {
                                resolve_type_expr_kinded(
                                    &p.ty,
                                    &universe,
                                    &HashMap::new(),
                                    &in_scope_generics,
                                    &in_scope_hkt,
                                )
                            })
                            .collect();
                        let ret = m
                            .return_type
                            .as_ref()
                            .map(|ty| {
                                resolve_type_expr_kinded(
                                    ty,
                                    &universe,
                                    &HashMap::new(),
                                    &in_scope_generics,
                                    &in_scope_hkt,
                                )
                            })
                            .unwrap_or(Type::Unit);
                        methods.insert(m.name.clone(), (params, ret));
                    }
                    universe
                        .traits
                        .insert(def.name.clone(), TraitContract { methods, hkt_param });
                }
                _ => {}
            }
        }
    }

    universe
}

pub(super) fn collect_actor_sigs(
    program: &crate::ast::Program,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) -> HashMap<String, ActorSig> {
    let mut actors = HashMap::new();

    for module in &program.modules {
        for item in &module.items {
            let Item::ActorDef(def) = item else {
                continue;
            };

            let init_params = def
                .init
                .as_ref()
                .map(|init| {
                    init.params
                        .iter()
                        .map(|param| resolve_type(&param.ty, universe, diagnostics))
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            let handlers = def
                .handlers
                .iter()
                .map(|handler| {
                    (
                        handler.message_name.clone(),
                        HandlerSig {
                            params: handler
                                .params
                                .iter()
                                .map(|param| resolve_type(&param.ty, universe, diagnostics))
                                .collect(),
                            ret: handler
                                .return_type
                                .as_ref()
                                .map(|ty| resolve_type(ty, universe, diagnostics))
                                .unwrap_or(Type::Unit),
                        },
                    )
                })
                .collect::<HashMap<_, _>>();

            actors.insert(
                def.name.clone(),
                ActorSig {
                    init_params,
                    handlers,
                },
            );
        }
    }

    actors
}

/// Regions (DEF-2b, LD-5 / NC-2b-3): resolve each param's `@in r` annotation to a
/// `ParamRegion`, positionally aligned with `params` (mirroring `param_mutability`).
/// `@in r` becomes `In(slot)` where `slot` is the 0-based POSITION of the `Region`
/// parameter named `r` — a per-signature slot the AG-R2 lift (PR-4) maps to a caller-side
/// region before any compare. The parser (P024) has already validated that `r` names a
/// `Region` param, so the position always resolves; the `unwrap_or(None)` is defensive.
pub(super) fn param_regions_of(params: &[crate::ast::Param]) -> Vec<ParamRegion> {
    params
        .iter()
        .map(|p| match &p.region {
            Some(r) => params
                .iter()
                .position(|q| q.name == *r)
                .map(|slot| ParamRegion::In(slot as u32))
                .unwrap_or(ParamRegion::None),
            None => ParamRegion::None,
        })
        .collect()
}

/// Regions (DEF-2b, LD-4 / PR-5): resolve the `where region(a): region(b)` name pairs into
/// `(a_slot, b_slot)` 0-based `Region`-parameter positions (`Param(a_slot)` outlives
/// `Param(b_slot)`). A pair naming an unknown parameter is dropped — the parser already
/// emitted P025 for it (the program will not compile), so the slot table stays consistent.
pub(super) fn param_region_outlives_of(
    params: &[crate::ast::Param],
    region_outlives: &[(String, String)],
) -> Vec<(u32, u32)> {
    region_outlives
        .iter()
        .filter_map(|(a, b)| {
            let a_slot = params.iter().position(|q| q.name == *a)? as u32;
            let b_slot = params.iter().position(|q| q.name == *b)? as u32;
            Some((a_slot, b_slot))
        })
        .collect()
}

pub(super) fn collect_function_sigs(
    module: &crate::ast::Module,
    universe: &TypeUniverse,
) -> std::collections::BTreeMap<String, FunctionSig> {
    COLLECT_FUNCTION_SIGS_CALL_COUNT.with(|c| c.set(c.get() + 1));

    let mut sigs = std::collections::BTreeMap::new();

    for item in &module.items {
        match item {
            Item::FnDef(def) if def.type_params.is_empty() => {
                // Wall 4 Step 7 / N21-S7: populate per-param and return
                // refinements. Per N3-S7, FnDef.param_refinements LHS
                // references param names by identifier; we map by name
                // here. Per N7-S7 single clause per where, so each
                // param maps to at most one Vec entry.
                let param_refinements: Vec<Option<Vec<crate::ast::RefinementClause>>> = def
                    .params
                    .iter()
                    .map(|param| {
                        let matching: Vec<crate::ast::RefinementClause> = def
                            .param_refinements
                            .iter()
                            .filter(|c| c.field == param.name)
                            .cloned()
                            .collect();
                        if matching.is_empty() {
                            None
                        } else {
                            Some(matching)
                        }
                    })
                    .collect();
                let return_refinement = def.return_refinement.as_ref().map(|c| vec![c.clone()]);

                sigs.insert(
                    def.name.clone(),
                    FunctionSig {
                        qualified_name: format!("{}::{}", module.name, def.name),
                        // Declared row, resolved eagerly — the registry was built by
                        // collect_type_universe, which runs before sig collection.
                        effects: super::resolve_effect_row(&def.effects, universe),
                        params: def
                            .params
                            .iter()
                            .map(|param| {
                                resolve_type_expr(&param.ty, universe, &HashMap::new(), &[])
                            })
                            .collect(),
                        ret: def
                            .return_type
                            .as_ref()
                            .map(|ty| resolve_type_expr(ty, universe, &HashMap::new(), &[]))
                            .unwrap_or(Type::Unit),
                        module: module.name.clone(),
                        visibility: def.visibility,
                        param_refinements,
                        return_refinement,
                        impl_type_params: Vec::new(),
                        method_type_params: Vec::new(),
                        is_associated: false, // free fn — not an impl associated fn
                        param_mutability: def.params.iter().map(|p| p.mutability).collect(),
                        param_regions: param_regions_of(&def.params),
                        param_region_outlives: param_region_outlives_of(
                            &def.params,
                            &def.region_outlives,
                        ),
                    },
                );
            }
            Item::ImplDef(impl_def) => {
                // SIGIL Complete v0 / Phase 6 (N11-V0, N15-V0): build
                // the impl-block-level generic-binder scope BEFORE
                // resolving method param/return types. The scope is the
                // impl block's `type_params: Vec<String>` (N10-V0).
                // Methods inside this block resolve `Type::Generic("T")`
                // references against this scope at sig-collection time
                // (not at dispatch time); dispatch (N9-V0) then
                // positional-substitutes the resolved generics against
                // the receiver's concrete type-args.
                let impl_generic_scope: Vec<String> =
                    crate::ast::type_param_names(&impl_def.type_params);
                for method in &impl_def.methods {
                    // SIGIL Complete v0 / Phase 6 supremum path: methods
                    // in impl blocks declare `self` EXPLICITLY in their
                    // param list (`pub fn read(self: Counter) -> i64`).
                    // Pre-v0 sig collection ALSO prepended a synthetic
                    // `self`, doubling-up when method sources declared
                    // self explicitly. The supremum-path convention
                    // is: explicit-self in source; no synthetic prepend.
                    //
                    // Combine impl-block-level + method-level type_params
                    // for resolve_type_expr scope. Method-level binders
                    // extend impl-level — both sets are in scope when
                    // resolving each method param type.
                    let mut combined_generic_scope: Vec<String> = impl_generic_scope.clone();
                    combined_generic_scope
                        .extend(method.type_params.iter().map(|p| p.name.clone()));
                    let params: Vec<Type> = method
                        .params
                        .iter()
                        .map(|param| {
                            resolve_type_expr(
                                &param.ty,
                                universe,
                                &HashMap::new(),
                                &combined_generic_scope,
                            )
                        })
                        .collect();

                    // Wall 4 Step 7 / N18-S7 (impl-method refinement
                    // inheritance): same as free fn. With explicit-self
                    // convention, param_refinements is no longer offset
                    // by 1 — it aligns 1:1 with method.params.
                    let mut method_param_refinements: Vec<
                        Option<Vec<crate::ast::RefinementClause>>,
                    > = Vec::with_capacity(method.params.len());
                    for param in &method.params {
                        let matching: Vec<crate::ast::RefinementClause> = method
                            .param_refinements
                            .iter()
                            .filter(|c| c.field == param.name)
                            .cloned()
                            .collect();
                        method_param_refinements.push(if matching.is_empty() {
                            None
                        } else {
                            Some(matching)
                        });
                    }
                    let method_return_refinement =
                        method.return_refinement.as_ref().map(|c| vec![c.clone()]);

                    let method_key = format!("{}::{}", impl_def.type_name, method.name);
                    sigs.insert(
                        method_key,
                        FunctionSig {
                            qualified_name: format!(
                                "{}::{}__{}",
                                module.name, impl_def.type_name, method.name
                            ),
                            // Declared row of the impl method (same `! { E }` surface as
                            // free fns — FnDef.effects).
                            effects: super::resolve_effect_row(&method.effects, universe),
                            params,
                            ret: method
                                .return_type
                                .as_ref()
                                .map(|ty| {
                                    resolve_type_expr(
                                        ty,
                                        universe,
                                        &HashMap::new(),
                                        &combined_generic_scope,
                                    )
                                })
                                .unwrap_or(Type::Unit),
                            module: module.name.clone(),
                            // Methods inherit visibility from impl block context.
                            // For now treat impl methods as public — cross-module
                            // method dispatch is not yet supported (impl resolution
                            // is type-driven, not module-path-driven).
                            visibility: crate::ast::Visibility::Public,
                            param_refinements: method_param_refinements,
                            return_refinement: method_return_refinement,
                            // SIGIL Complete v0 / Phase 6 (N9-V0, N10-V0):
                            // carry the impl block's type_params on the sig
                            // so the call-site dispatcher can build a
                            // positional substitution against the receiver's
                            // concrete type-args. Empty Vec for non-generic
                            // impl blocks (backward-compat).
                            impl_type_params: crate::ast::type_param_names(&impl_def.type_params),
                            method_type_params: crate::ast::type_param_names(&method.type_params),
                            // BoundedVec PR-0a: an ASSOCIATED fn (no `self` receiver,
                            // e.g. `new`/`with_capacity`) — drives the `Type::method()`
                            // reroute for CONCRETE records, not only generic impls.
                            is_associated: method.params.first().is_none_or(|p| p.name != "self"),
                            param_mutability: method.params.iter().map(|p| p.mutability).collect(),
                            param_regions: param_regions_of(&method.params),
                            param_region_outlives: param_region_outlives_of(
                                &method.params,
                                &method.region_outlives,
                            ),
                        },
                    );
                }
            }
            Item::ExternFnDecl(def) => {
                // Wall 4 Step 7 / N19-S7: extern fns reject refinement.
                // The parser doesn't admit `where` on `extern "C" fn`
                // (it routes through `parse_extern_fn_decl`, not
                // `parse_fn`), so `param_refinements`/`return_refinement`
                // are always empty here. Initialize defensively.
                let extern_param_refinements = vec![None; def.params.len()];

                sigs.insert(
                    def.name.clone(),
                    FunctionSig {
                        qualified_name: format!("{}::{}", module.name, def.name),
                        // Extern rows are a plain Vec (no None/Some([]) distinction —
                        // ast.rs:197). Recorded for completeness; `effects_of_block`
                        // deliberately does NOT charge extern calls (parity with
                        // walk_expr_effects' ExternCall arm, ET-EFF-1).
                        effects: super::resolve_effect_row(&Some(def.effects.clone()), universe),
                        params: def
                            .params
                            .iter()
                            .map(|param| {
                                resolve_type_expr(&param.ty, universe, &HashMap::new(), &[])
                            })
                            .collect(),
                        ret: def
                            .return_type
                            .as_ref()
                            .map(|ty| resolve_type_expr(ty, universe, &HashMap::new(), &[]))
                            .unwrap_or(Type::Unit),
                        module: module.name.clone(),
                        // `extern "C"` declarations are module-private by
                        // language design — they're the trusted-FFI surface
                        // and tools should not call them across modules.
                        visibility: crate::ast::Visibility::Private,
                        param_refinements: extern_param_refinements,
                        return_refinement: None,
                        impl_type_params: Vec::new(),
                        method_type_params: Vec::new(),
                        is_associated: false, // extern fn
                        param_mutability: def.params.iter().map(|p| p.mutability).collect(),
                        param_regions: param_regions_of(&def.params),
                        // Extern fn declarations have no body, hence no `where region`.
                        param_region_outlives: Vec::new(),
                    },
                );
            }
            _ => {}
        }
    }

    sigs
}

pub(super) fn build_actor_env(
    actor: &ActorDef,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) -> HashMap<String, Type> {
    build_actor_captures(actor, universe, diagnostics)
        .into_iter()
        .map(|capture| (capture.name, capture.ty))
        .collect()
}

pub(super) fn build_actor_captures(
    actor: &ActorDef,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<TypedParam> {
    actor
        .state_fields
        .iter()
        .map(|field| TypedParam {
            flow: false,
            name: field.name.clone(),
            ty: resolve_type(&field.ty, universe, diagnostics),
            taint: crate::ast::TaintLabel::Public,
            // S2: preserve the `mut` marker into the capture so AIR can fresh-load it.
            mutability: field.mutability,
        })
        .collect()
}

/// State values must persist across message dispatches. Inline scalars live in the state slot,
/// capabilities live in the host capability table, and aggregates initialized once live below
/// the actor's persistent floor. Mutable flat fixed aggregates update that storage in place;
/// mutable `Vec<scalar>` growth uses the state-backed persistent allocation channel. Mutable
/// cap/ref/borrow/Fn/Ptr-bearing fields are C011, while mutable aggregate shapes without a
/// complete persistence path are C012. A non-`mut` capability field remains the sanctioned
/// borrow-only state cap (C010).
///
/// Called ONCE per actor (unlike `build_actor_captures`, which runs per env/captures build) so
/// each diagnostic fires exactly once per offending field.
pub(super) fn check_state_field_types(
    actor: &ActorDef,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for field in &actor.state_fields {
        // Resolve WITHOUT emitting (build_actor_captures already surfaced any type-resolution
        // error for this field); this pass only judges persistence shape.
        let mut sink = Vec::new();
        let ty = resolve_type(&field.ty, universe, &mut sink);
        let is_mut = field.mutability == Mutability::Mut;
        if !type_is_reassignable(&ty, universe) {
            // Cap/ref/borrow/Fn/Ptr-bearing. A `mut` such field is C011 (overwriting drops the
            // cap's linearity). A NON-`mut` cap field is the intended borrow-only state cap,
            // persisted via the capability table — allowed, untouched here.
            if is_mut {
                let cause = match classify_reassign_rejection(&ty, universe) {
                    ReassignRejection::CapBearing => "capability-bearing",
                    ReassignRejection::RefBearing => "reference-bearing",
                    ReassignRejection::Other => "not plain reassignable data",
                };
                diagnostics.push(Diagnostic::error(
                    codes::C011,
                    format!(
                        "`mut` state field `{}` must be plain reassignable data, but its type is {}",
                        field.name, cause
                    ),
                    Some(field.span),
                ));
            }
        } else if is_mut
            && !is_inline_scalar(&ty)
            && !is_flat_scalar_aggregate(&ty, universe)
            && !is_persistable_scalar_vec(&ty, universe)
            && !is_persistable_scalar_map(&ty, universe)
            // PPS-2a: a `mut str` field is promotable — the store copies the payload bytes to a
            // persistent buffer and rebuilds the header over the copy, so both halves of the fat
            // pointer outlive the dispatch.
            && !matches!(ty, Type::Str)
        {
            // A non-`mut` aggregate persists (AGG-1: written only in `init`, below the persistent
            // floor). A `mut` FLAT-FIXED aggregate persists in place (AGG-2a); a `mut` `str`
            // persists by store-promotion (PPS-2a); `Vec`/`Map` persist when every ELEMENT
            // (Vec element, Map key/value) is a promotable element — inline scalar, `str`, or a
            // flat scalar record (PPS-0..3: state-backed routing + promotion at the storing
            // `push`). What remains fenced is an element the field copy cannot deep-copy: a
            // record with a POINTER-BEARING interior (str/Vec/record fields), a nested
            // collection, a nested record field, or 256-bit values.
            diagnostics.push(Diagnostic::error(
                codes::C012,
                format!(
                    "`mut` state field `{}` must be an inline scalar, `str`, a flat fixed \
                     aggregate (a record/array/tuple of scalars), or a `Vec`/`Map` whose \
                     elements are scalars, `str`, or flat scalar records; an element with a \
                     pointer-bearing interior (a record containing str/Vec/record fields), a \
                     nested collection, or a 256-bit value is not yet preserved across \
                     dispatches",
                    field.name
                ),
                Some(field.span),
            ));
        }
    }
}

/// A value of this type lives directly in a flat slot (no heap pointer). The inline scalars: a
/// state field of this type persists in the state-region slot; a `mut` such field is reassignable
/// in place. Aggregates / `str` / 256-bit values lower to a heap pointer instead.
/// A `mut` `Vec<T>` state field with `T` an inline scalar is the shape whose grow-`push`
/// routes to the state-backed `alloc_persistent` channel (AGG2b-2), so its buffer survives the AL-2
/// reset and it persists across dispatches. `Vec<aggregate>`, `Map`, `str`, and 256-bit stay fenced
/// (each needs per-element persistent allocation the single-header stamp does not cover).
/// A `mut Vec<T>` state field whose element is persistable: an inline scalar (stored by value,
/// AGG-2b) or a `str` (header + payload promoted at the storing `push`, PPS-2b/3).
///
/// PPS-3 resolved the `Vec<str>` trap PPS-2b recorded: the shape was admitted at the C012 seam
/// but the ROUTING gate still required a scalar element, so a state `Vec<str>` was never routed
/// to a `$state` instance — its buffer grew transiently and the promotion (which keys on the
/// `$state` callee) never fired. Routing now shares this predicate, so admission and routing
/// cannot drift apart again.
pub(super) fn is_persistable_scalar_vec(ty: &Type, universe: &TypeUniverse) -> bool {
    matches!(ty, Type::Named(name, args)
        if name == "Vec" && args.len() == 1 && is_promotable_element(&args[0], universe))
}

/// PPS-0: a `mut Map<scalar, scalar>` state field. Its interior is five `Vec`s allocated by the
/// stdlib's own methods, so a state-rooted mutating call is persisted by MONOMORPH COLORING (the
/// `$state` instance plus the inherited depth), with no per-element promotion — the reason this is
/// the epic's first slice. Aggregate keys/values still need the promotion primitive (PPS-1+) and
/// stay fenced.
pub(super) fn is_persistable_scalar_map(ty: &Type, universe: &TypeUniverse) -> bool {
    matches!(ty, Type::Named(name, args)
        if name == "Map"
            && args.len() == 2
            && is_promotable_element(&args[0], universe)
            && is_promotable_element(&args[1], universe))
}

/// An element a state-backed collection can hold persistently — an inline scalar (stored by
/// value), a `str` (header + payload promoted at the storing `push`, PPS-2b), or a FLAT scalar
/// record (promoted at the storing `push` by the PPS-1 field copy, PPS-3). Elements whose own
/// interiors hold pointers (records containing a `str`/`Vec`, nested collections) still need a
/// looped transitive walk and stay fenced.
pub(super) fn is_promotable_element(ty: &Type, universe: &TypeUniverse) -> bool {
    is_inline_scalar(ty) || matches!(ty, Type::Str) || is_flat_scalar_aggregate(ty, universe)
}

pub(super) fn is_inline_scalar(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Bool | Type::I32 | Type::U32 | Type::I64 | Type::U64 | Type::F64
    )
}

/// AGG-2a: a FLAT FIXED aggregate — a record / array / tuple whose fields/elements are all inline
/// scalars (one level, no nested aggregate, no `Vec`/`Map`). Such a field's object is allocated in
/// `init` (below the persistent floor, so it persists) and is mutated IN PLACE by a handler
/// (`d.f = …`, `a[i] = …` StoreField into that persistent object — no new allocation). A `mut`
/// flat-fixed field is therefore permitted; a `mut` nested / dynamic (`Vec`/`Map`) aggregate is not
/// (it needs a handler-time persistent allocation — the AGG-2b half). Only CONCRETE records
/// (non-generic) are recognized here; a generic-record state field stays conservatively fenced.
pub(super) fn is_flat_scalar_aggregate(ty: &Type, universe: &TypeUniverse) -> bool {
    match ty {
        Type::Array { elem, .. } => is_inline_scalar(elem),
        Type::Tuple(elems) => !elems.is_empty() && elems.iter().all(is_inline_scalar),
        Type::Named(name, args) => {
            if args.is_empty()
                && let Some((type_params, fields)) = universe.records.get(name)
                && type_params.is_empty()
            {
                return !fields.is_empty() && fields.iter().all(|(_, fty)| is_inline_scalar(fty));
            }
            false
        }
        _ => false,
    }
}

/// Every mutable actor state field must be assigned exactly once, unconditionally,
/// at the top level of `init`; otherwise a handler
/// could read an uninitialised (zero) value (hazard H7-B). T124 = a field assigned more
/// than once (double-init); T125 = a declared field not assigned at the top level
/// (missing, or assigned only inside an `if`/`while` — not definitely assigned). The
/// ENTRY actor is EXEMPT: its state is populated at bootstrap, not by an `init` block.
pub(super) fn check_state_field_definite_assignment(
    actor: &ActorDef,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Entry-actor state is bootstrap-populated (the M5 carve-out), not init-assigned.
    if actor.is_entry || actor.state_fields.is_empty() {
        return;
    }
    // The top-level count is a sound definite-assignment
    // proxy ONLY if `init` runs to completion. An early `return` lets init FINISH while
    // skipping the counted top-level assignment — dead code after an unconditional
    // `return` (`return; n = 5;`), or a guarded return before it (`if c { return; } n = 5;`)
    // — leaving a `mut` field at its zero slot, which a handler reads back (hazard H7-B).
    // Divergence (trap/infinite loop) is NOT a hole (init never completes → the actor is
    // never constructed → no handler runs), so `return` is the ONLY construct to reject.
    // The walk descends control-flow blocks but NOT expressions, so a `return` inside a
    // `grant` closure (which exits the closure, not init) stays legal. Gated to actors
    // with a `mut` field — the ones F3 covers.
    let has_mut_field = actor
        .state_fields
        .iter()
        .any(|f| f.mutability == Mutability::Mut);
    if has_mut_field
        && let Some(init) = &actor.init
        && let Some(span) = first_init_return(&init.body.statements)
    {
        diagnostics.push(Diagnostic::error(
            codes::T126,
            "an `init` block must not `return` — it must run to completion so every `mut` \
             state field is definitely assigned; move the assignment before any early exit"
                .to_string(),
            Some(span),
        ));
    }
    let field_names: std::collections::HashSet<&str> =
        actor.state_fields.iter().map(|f| f.name.as_str()).collect();
    // Count TOP-LEVEL `field = expr` assignments (nested in an `if`/`while` does NOT
    // count — the boring definite-assignment limit: unconditional top-level only).
    let mut counts: HashMap<String, usize> = HashMap::new();
    if let Some(init) = &actor.init {
        for stmt in &init.body.statements {
            if let crate::ast::Stmt::Assign(a) = stmt
                && let Some(name) = bare_lvalue_name(&a.target)
                && field_names.contains(name)
            {
                *counts.entry(name.to_string()).or_insert(0) += 1;
            }
        }
    }
    for field in &actor.state_fields {
        // S2 scope: F3 applies to `mut` fields — the ones the read model reads back and
        // whose uninit value (0) would be a silent wrong DATA answer (H7-B). A NON-`mut`
        // field keeps its pre-S2 discipline (M2 immutable-after-init + M4 cap-borrow),
        // including the established empty-init cap pattern (`init(f) {}` for a state cap
        // populated by the caller); full non-`mut` definite-assignment is the M6 milestone.
        if field.mutability != Mutability::Mut {
            continue;
        }
        let n = counts.get(&field.name).copied().unwrap_or(0);
        if n == 0 {
            diagnostics.push(Diagnostic::error(
                codes::T125,
                format!(
                    "actor state field `{}` is not definitely assigned in `init` — assign it \
                     exactly once, unconditionally, at the top level of `init`",
                    field.name
                ),
                Some(field.span),
            ));
        } else if n > 1 {
            diagnostics.push(Diagnostic::error(
                codes::T124,
                format!(
                    "actor state field `{}` is assigned {n} times in `init` — assign it exactly once",
                    field.name
                ),
                Some(field.span),
            ));
        }
    }
}

/// The span of the first `return` STATEMENT reachable in `init`'s own control flow,
/// or `None`. Descends `if`/`while`/`for`/`match` statement bodies (init exits through
/// them) but NOT into expressions — a `return` inside a nested closure/lambda returns
/// from that closure, not from init, so it must be left alone (T126). Total over `Stmt`
/// (no wildcard arm) so a new statement kind forces a decision here.
fn first_init_return(stmts: &[crate::ast::Stmt]) -> Option<crate::span::Span> {
    use crate::ast::Stmt;
    for stmt in stmts {
        let found = match stmt {
            Stmt::Return(r) => Some(r.span),
            Stmt::If(s) => first_init_return(&s.then_branch.statements)
                .or_else(|| first_init_return(&s.else_branch.statements)),
            Stmt::While(s) => first_init_return(&s.body.statements),
            Stmt::ForIn(s) => first_init_return(&s.body.statements),
            Stmt::ForRange(s) => first_init_return(&s.body.statements),
            Stmt::Match(s) => s
                .arms
                .iter()
                .find_map(|arm| first_init_return(&arm.body.statements)),
            // No statement-level sub-body to descend; any `return` inside these lives
            // in an expression (a nested closure), which exits that closure, not init.
            Stmt::Let(_)
            | Stmt::LetTuple(_)
            | Stmt::Assign(_)
            | Stmt::Expr(_)
            | Stmt::Break(_)
            | Stmt::Continue(_) => None,
        };
        if found.is_some() {
            return found;
        }
    }
    None
}

/// The single bare name of an lvalue path expression (`n`), or `None` for any other
/// place shape (`r.f`, `a[i]`, a multi-segment or generic path).
fn bare_lvalue_name(expr: &crate::ast::Expr) -> Option<&str> {
    if let crate::ast::Expr::Path(pe) = expr
        && pe.path.segments.len() == 1
        && pe.path.type_args.is_empty()
    {
        return Some(pe.path.segments[0].as_str());
    }
    None
}
