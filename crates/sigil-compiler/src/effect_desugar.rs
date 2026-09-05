//! Effect-handler lowering pass (EH4): the evidence-passing desugar.
//!
//! Runs AFTER the typed-program security passes and BEFORE the E004 gate +
//! `air::lower`. It rewrites the effect-handler typed AST into ordinary
//! closure-passing typed AST (closures + indirect calls + calls), so the AIR
//! lowering needs no new nodes. See the "Appendix: EH4 Lowering Design" in
//! `docs/specs/effect-handlers-in-sigil.md` and its `LC-*` constraints.
//!
//! INCREMENTAL-SAFETY INVARIANT (LC-PARTITION): the desugar transforms only the
//! shapes it supports; everything it leaves behind is rejected by the post-desugar
//! gate (`effect_check::check_effect_handlers_gated`), and any node that slips past
//! both hits the `air::lower` `unreachable!`. So an incomplete desugar is always a
//! loud rejection or ICE, never a silent miscompile.
//!
//! EH4.3a (this slice): SCOPED propagation through the call graph. Evidence for a
//! handled effect `E` is threaded through every E-FUNCTION (a function whose row
//! contains `E`), not just the direct scrutinee:
//!
//! - every non-entry E-function gains one evidence parameter `$ev$E$op` per operation
//!   of `E` (canonical effect-then-op-sorted order);
//! - `perform E.op(args)` becomes an `IndirectCall` (scoped) / a `return` (abortive,
//!   EH4.2, direct-performer only);
//! - a direct `Call` to an E-function forwards the caller's own evidence parameters;
//! - the `handle g(args) { … }` site BUILDS the clause closures and appends them to
//!   `g`'s call — it is the evidence SOURCE; functions on the path FORWARD.
//!
//! Soundness rests on the effect-leak invariant (`effect_check.rs`): every call to an
//! E-function either sits in another E-function (forward) or is a handle scrutinee
//! (build), so evidence is always available. Pure functions (no effect row) are never
//! touched — byte-identical AIR holds for them.
//!
//! KEY MODEL DISTINCTION: SCOPED evidence is PER-EFFECT UNIFORM (the closure returns
//! the op's declared return; it threads through every E-function). ABORTIVE evidence
//! is PER-HANDLE (the closure returns the SCRUTINEE's return type = the handle's
//! type), so it cannot thread as a closure return. A NON-propagating abortive effect
//! (direct performer only) reproduces EH4.2 (`perform` -> `return $ev(args)`). A
//! PROPAGATING abortive effect (an abortive op reached through an intermediate TAIL
//! call) is lowered by EH4.3c (`lower_abortive_propagation`) via a synthesized
//! `$EhResult$<H>` discriminated-union return + a `$eh_unwrap` helper.
//!
//! Anything outside this (multi-effect functions, NON-tail abortive propagation,
//! effectful closures/actors, generic or address-taken effectful functions,
//! indirect/nested calls to E-functions, multiple modules) is left for the E004 gate.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::ast::{Ring, TaintLabel};
use crate::registries::{EffectRegistry, EffectSet};
use crate::type_check::{Type, TypedProgram};
use crate::type_check_v2::refinement::visit_block_constructs;
use crate::typed_ast::{
    EffectOpSig, TypedBlock, TypedCallExpr, TypedClosureConstructExpr, TypedEnumConstructExpr,
    TypedExpr, TypedExprKind, TypedFunction, TypedFunctionKind, TypedIndirectCallExpr,
    TypedIndirectCallKind, TypedMatchArm, TypedMatchStmt, TypedModule, TypedParam, TypedPattern,
    TypedReturnStmt, TypedStmt,
};

/// A synthesized enum to register in [`TypedProgram::enums`]:
/// `(name, (type_params, variants))` where each variant is `(name, payload_types)`.
/// EH4.3c's `$EhResult$<H>` enums flow through this.
type SynthEnum = (String, (Vec<String>, Vec<(String, Vec<Type>)>));

/// Rewrite the effect-handler surface into evidence-passing closures, in place.
/// A no-op for any construct EH4.x does not yet handle (those stay E004-gated).
pub fn desugar_effect_handlers(program: &mut TypedProgram) {
    // The effect operation signatures + registry are immutable program data; clone
    // them out before borrowing `program.modules` mutably.
    let effect_ops = program.effect_ops.clone();
    let registry = program.effect_registry.clone();
    // EH4.3d cross-ring gate: each function's ring (its module's ring). A synthesized
    // clause closure lives in the handle's ring; an `IndirectCall` to it from a
    // performer in a different ring would hit the wrong per-ring wasm table, so an
    // effect spanning rings is gated (LC-MM-RING).
    let fn_ring: BTreeMap<String, Ring> = program
        .modules
        .iter()
        .flat_map(|m| m.functions.iter().map(move |f| (f.name.clone(), m.ring)))
        .collect();
    // EH4.3c synthesizes `$EhResult$<H>` enums; collect them and register them in
    // `program.enums` after the mutable module loops.
    let mut new_enums: Vec<SynthEnum> = Vec::new();

    // EH4.3d: the scoped + direct-abortive threading is PROGRAM-WIDE — a handler in one
    // module can wrap a performer in another, same-ring module (callee names are
    // module-qualified, effect IDs + AIR `function_ids` are program-wide). The analysis
    // runs once over ALL modules; the transforms then run per-module using it.
    let threading = analyze(&program.modules, &effect_ops, &registry, &fn_ring);
    if !threading.is_empty() {
        // Pass B (performers + propagators) across all modules.
        for module in &mut program.modules {
            for f in &mut module.functions {
                let Some(effs) = threading.fn_effects.get(&f.name).cloned() else {
                    continue;
                };
                let f_ret = f.ret.clone();
                for e in &effs {
                    for op in &threading.effects[e].ops {
                        f.params.push(TypedParam {
                            flow: false,
                            mutability: crate::ast::Mutability::Default,
                            name: op.ev_name.clone(),
                            ty: ev_ty_for(op, &f_ret),
                            taint: TaintLabel::Public,
                        });
                    }
                }
                rewrite_scoped_and_forwarding(&mut f.body.statements, &effs, &threading);
                rewrite_abortive_returns(&mut f.body.statements, &f_ret, &effs, &threading);
            }
        }
        // Pass C (handles) across all modules; synthesized closures are appended to the
        // handle's own module (named `{module}::$eh_clause_N`, resolved program-wide).
        for module in &mut program.modules {
            let module_name = module.name.clone();
            let mut counter = module.functions.len();
            let mut new_closures: Vec<TypedFunction> = Vec::new();
            for f in &mut module.functions {
                rewrite_handles(
                    &mut f.body.statements,
                    &threading,
                    &module_name,
                    &mut counter,
                    &mut new_closures,
                );
            }
            module.functions.extend(new_closures);
        }
    }

    // EH4.3c abortive PROPAGATION stays PER-MODULE: `lower_abortive_propagation` only
    // sees one module's functions and rewrites the chain in place. A single-module chain
    // in each module is lowered; multi-module abortive propagation is deferred (AG-MM-3).
    // The per-module pass cannot, on its own, detect a chain function reached from a
    // DIFFERENT module — that foreign caller would be left at the stale (pre-rewrite)
    // signature (ROOT-B). So compute program-wide call counts here (every `Call`'s callee
    // across all modules) and hand them down: `ehr_analyze` gates any effect whose chain
    // is called cross-module, so its handler nodes survive to the E004 gate instead.
    let mut program_all_calls: HashMap<String, usize> = HashMap::new();
    for module in &program.modules {
        for f in &module.functions {
            visit_block_constructs(&f.body, &mut |ex: &TypedExpr| {
                if let TypedExprKind::Call(c) = &ex.kind {
                    *program_all_calls.entry(c.callee.clone()).or_insert(0) += 1;
                }
            });
        }
    }
    for module in &mut program.modules {
        lower_abortive_propagation(
            module,
            &effect_ops,
            &registry,
            &program_all_calls,
            &mut new_enums,
        );
    }
    for (name, def) in new_enums {
        program.enums.insert(name, def);
    }
}

/// One operation of a threaded effect, with its declared signature.
struct OpInfo {
    name: String,
    /// The evidence parameter name `$ev$E$op` (`$` is outside the identifier grammar,
    /// so it can never collide with a user name).
    ev_name: String,
    params: Vec<Type>,
    param_taints: Vec<TaintLabel>,
    /// The operation's DECLARED return type (`Type::Never` for an abortive op).
    ret: Type,
    /// `ret == Type::Never`.
    abortive: bool,
}

/// The evidence-threading plan for one handled user effect `E`.
struct EffectPlan {
    ops: Vec<OpInfo>, // sorted by operation name
}

/// The per-module threading result: the eligible handled effects and, per function,
/// the threaded effects in its row (the E-functions). After the 4.3a single-effect
/// gate, each function maps to exactly one effect.
struct Threading {
    effects: BTreeMap<String, EffectPlan>,
    fn_effects: BTreeMap<String, Vec<String>>,
}

impl Threading {
    fn is_empty(&self) -> bool {
        self.effects.is_empty()
    }
}

/// The synthesized clause closure's declared return type (and the `IndirectCall`
/// result type at a scoped perform site): the op's declared return for a scoped op,
/// the OWNER's return type for an abortive op (the handle's type — LC-ABORT-TY).
fn closure_ret_for(op: &OpInfo, owner_ret: &Type) -> Type {
    if op.abortive {
        owner_ret.clone()
    } else {
        op.ret.clone()
    }
}

/// The evidence parameter / closure type `Fn(op_params) -> closure_ret`.
fn ev_ty_for(op: &OpInfo, owner_ret: &Type) -> Type {
    // Empty latent row: the handler-evidence closures this desugar synthesizes are built
    // AFTER `check_effects` has run, so their row is never consulted by the E001 gate.
    Type::Fn(
        op.params.clone(),
        Box::new(closure_ret_for(op, owner_ret)),
        false,
        EffectSet::empty(),
    )
}

// ── Pass A: eligibility analysis (immutable, program-wide) ───────────────────

/// A clause-handle whose scrutinee is a direct call, recorded for analysis.
struct HandleRec {
    /// The effects discharged (the union of the clauses' effects).
    effects: BTreeSet<String>,
    /// The scrutinee call's callee name.
    scrutinee_callee: String,
    /// The handle expression's type = the scrutinee's return type (the abortive
    /// clauses' value type — LC-ABORT-TY).
    scrutinee_ty: Type,
    /// Every clause has an eligible (simple, capture-free) body.
    eligible: bool,
    /// `(effect, op, is_resume, value_type)` for each clause.
    clauses: Vec<(String, String, bool, Type)>,
    /// The ring of the module containing this handle (EH4.3d cross-ring gate: a
    /// synthesized clause closure lives in the handle's ring, so an `IndirectCall` to
    /// it from a performer in a different ring would hit the wrong wasm table).
    ring: Ring,
}

fn analyze(
    modules: &[TypedModule],
    effect_ops: &BTreeMap<String, Vec<EffectOpSig>>,
    registry: &EffectRegistry,
    fn_ring: &BTreeMap<String, Ring>,
) -> Threading {
    let empty = Threading {
        effects: BTreeMap::new(),
        fn_effects: BTreeMap::new(),
    };

    // 1. Deep walk over ALL modules: collect handle records (with the ring of the
    //    enclosing module), all call counts, scrutinee call counts, deep perform counts.
    let mut handles: Vec<HandleRec> = Vec::new();
    let mut all_calls: HashMap<String, usize> = HashMap::new();
    let mut scrutinee_calls: HashMap<String, usize> = HashMap::new();
    let mut deep_performs: HashMap<String, usize> = HashMap::new();
    for module in modules {
        for f in &module.functions {
            visit_block_constructs(&f.body, &mut |e: &TypedExpr| match &e.kind {
                TypedExprKind::Call(c) => {
                    *all_calls.entry(c.callee.clone()).or_insert(0) += 1;
                }
                TypedExprKind::Perform(p) => {
                    *deep_performs.entry(p.effect.clone()).or_insert(0) += 1;
                }
                TypedExprKind::ClauseHandle(h) => {
                    if let TypedExprKind::Call(c) = &h.scrutinee.kind {
                        *scrutinee_calls.entry(c.callee.clone()).or_insert(0) += 1;
                        let mut effects = BTreeSet::new();
                        let mut clauses = Vec::new();
                        let mut eligible = !h.clauses.is_empty();
                        for clause in &h.clauses {
                            effects.insert(clause.effect.clone());
                            match clause_shape(clause) {
                                Some((is_resume, value)) => {
                                    if !resume_is_simple(value, &clause.binders) {
                                        eligible = false;
                                    }
                                    clauses.push((
                                        clause.effect.clone(),
                                        clause.op.clone(),
                                        is_resume,
                                        value.ty.clone(),
                                    ));
                                }
                                None => eligible = false,
                            }
                        }
                        handles.push(HandleRec {
                            effects,
                            scrutinee_callee: c.callee.clone(),
                            scrutinee_ty: e.ty.clone(),
                            eligible,
                            clauses,
                            ring: module.ring,
                        });
                    }
                }
                _ => {}
            });
        }
    }
    if handles.is_empty() {
        return empty;
    }

    // 2. Statement-level call + perform counts (the nested-position gate: a call /
    //    perform that is NOT statement-level would not be reached by the rewrite
    //    walkers, so its effect is gated whole).
    let mut stmt_calls: HashMap<String, usize> = HashMap::new();
    let mut stmt_performs: HashMap<String, usize> = HashMap::new();
    for module in modules {
        for f in &module.functions {
            for_each_stmt_expr_ref(&f.body.statements, &mut |e: &TypedExpr| match &e.kind {
                TypedExprKind::Call(c) => {
                    *stmt_calls.entry(c.callee.clone()).or_insert(0) += 1;
                }
                TypedExprKind::Perform(p) => {
                    *stmt_performs.entry(p.effect.clone()).or_insert(0) += 1;
                }
                _ => {}
            });
        }
    }

    // 3. Validate each handled effect; collect the eligible ones + their E-functions.
    let handled_effects: BTreeSet<String> = handles
        .iter()
        .flat_map(|h| h.effects.iter().cloned())
        .collect();
    let mut effects: BTreeMap<String, EffectPlan> = BTreeMap::new();
    let mut e_functions_of: BTreeMap<String, Vec<String>> = BTreeMap::new();

    'eff: for effect in &handled_effects {
        // The effect must have operations (a clause-handle effect always does).
        let Some(op_sigs) = effect_ops.get(effect) else {
            continue;
        };
        if op_sigs.is_empty() {
            continue;
        }
        let Some(eff_id) = registry.lookup(effect) else {
            continue;
        };
        let mut ops: Vec<OpInfo> = op_sigs
            .iter()
            .map(|s| OpInfo {
                name: s.name.clone(),
                ev_name: format!("$ev${effect}${}", s.name),
                params: s.params.clone(),
                param_taints: s.param_taints.clone(),
                ret: s.ret.clone(),
                abortive: s.ret == Type::Never,
            })
            .collect();
        ops.sort_by(|a, b| a.name.cmp(&b.name));
        let has_abortive = ops.iter().any(|o| o.abortive);
        let op_names: BTreeSet<&String> = ops.iter().map(|o| &o.name).collect();

        // E-functions = functions (in ANY module) whose row contains this effect.
        let e_funcs: Vec<&TypedFunction> = modules
            .iter()
            .flat_map(|m| m.functions.iter())
            .filter(|f| f.effects.effects.contains(&eff_id))
            .collect();
        if e_funcs.is_empty() {
            continue;
        }

        // LC-MM-RING (EH4.3d): the effect threads only if every E-function AND every
        // function containing a handle of it share ONE ring — a synthesized clause
        // closure lives in the handle's ring, and an `IndirectCall` to it from a
        // performer in a different ring would resolve through the wrong per-ring wasm
        // table. Cross-ring multi-module is gated (AG-MM-1).
        let mut rings: Vec<Ring> = e_funcs
            .iter()
            .filter_map(|f| fn_ring.get(&f.name).copied())
            .collect();
        for hr in handles.iter().filter(|hr| hr.effects.contains(effect)) {
            rings.push(hr.ring);
        }
        if rings.windows(2).any(|w| w[0] != w[1]) {
            continue 'eff;
        }

        // Each E-function must be threadable (a non-entry, non-generic free function)
        // and every call to it must be a direct, statement-level forwarding call or a
        // handle scrutinee (LC-THREAD-DIRECT/EXHAUSTIVE: all_calls == scrutinee +
        // statement-level; a leftover is a nested / indirect call we cannot forward).
        for f in &e_funcs {
            if !is_threadable(f) {
                continue 'eff;
            }
            let ac = all_calls.get(&f.name).copied().unwrap_or(0);
            let sc = scrutinee_calls.get(&f.name).copied().unwrap_or(0);
            let lc = stmt_calls.get(&f.name).copied().unwrap_or(0);
            if ac != sc + lc {
                continue 'eff;
            }
        }

        // Every perform of this effect must be statement-level.
        if deep_performs.get(effect).copied().unwrap_or(0)
            != stmt_performs.get(effect).copied().unwrap_or(0)
        {
            continue 'eff;
        }

        // Every handle of this effect: eligible clauses, exact op coverage, and a
        // shape/type match per clause.
        for hr in handles.iter().filter(|hr| hr.effects.contains(effect)) {
            if !hr.eligible {
                continue 'eff;
            }
            let clause_e_ops: BTreeSet<&String> = hr
                .clauses
                .iter()
                .filter(|(e, _, _, _)| e == effect)
                .map(|(_, o, _, _)| o)
                .collect();
            if clause_e_ops != op_names {
                continue 'eff;
            }
            for (ce, co, is_resume, vty) in &hr.clauses {
                if ce != effect {
                    continue;
                }
                let Some(op) = ops.iter().find(|o| &o.name == co) else {
                    continue 'eff;
                };
                // SHAPE-match: a `resume` clause iff scoped; a value clause iff abortive.
                if *is_resume == op.abortive {
                    continue 'eff;
                }
                // TYPE-match: the clause value must be assignable to the closure's
                // declared return (op return for scoped, scrutinee return for abortive).
                if !crate::type_check::type_compatible(&closure_ret_for(op, &hr.scrutinee_ty), vty)
                {
                    continue 'eff;
                }
            }
        }

        // Abortive effects do not propagate: an abortive op's evidence closure
        // returns the SCRUTINEE's type (per-handle), so forwarding it to a function
        // with a different return type is unsound — the forwarded call_indirect type
        // diverges (trap), or the abort value flows back into the forwarding caller's
        // continuation instead of abandoning it (silent miscompile, sweep root). So
        // every E-function of an abortive effect must be reached ONLY as a direct
        // handle scrutinee: it must BE a scrutinee, and it must NEVER be a forwarding
        // callee (no statement-level call to it from another E-function). Otherwise
        // gate (the general abortive-propagation case is EH4.3c).
        if has_abortive {
            let scrutinees: BTreeSet<&String> = handles
                .iter()
                .filter(|hr| hr.effects.contains(effect))
                .map(|hr| &hr.scrutinee_callee)
                .collect();
            for f in &e_funcs {
                if !scrutinees.contains(&f.name)
                    || stmt_calls.get(&f.name).copied().unwrap_or(0) != 0
                {
                    continue 'eff;
                }
            }
        }

        effects.insert(effect.clone(), EffectPlan { ops });
        e_functions_of.insert(
            effect.clone(),
            e_funcs.iter().map(|f| f.name.clone()).collect(),
        );
    }

    // 4. Build the fn -> threaded-effects map. EH4.3b: a function may be an
    //    E-function for SEVERAL eligible effects (multi-effect); it receives evidence
    //    for each, in the canonical effect-then-op order used everywhere (params,
    //    forwarding, and the handle build). A handle that discharges only a SUBSET of
    //    its scrutinee's threaded effects (partial discharge) is left for the E004
    //    gate: Pass C requires a clause for every operation of every threaded effect
    //    of the scrutinee, so a missing effect's clauses abort the rewrite.
    let mut fn_effects: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (effect, fns) in &e_functions_of {
        for fname in fns {
            fn_effects
                .entry(fname.clone())
                .or_default()
                .push(effect.clone());
        }
    }
    for v in fn_effects.values_mut() {
        v.sort();
        v.dedup();
    }

    Threading {
        effects,
        fn_effects,
    }
}

/// A function is threadable iff it is a non-entry, non-generic free function
/// (`ModuleFunction`). Closures, actor handlers, and entries have fixed ABIs that
/// cannot receive evidence parameters (LC-THREAD-EXPORT / AG-EH43-1).
fn is_threadable(f: &TypedFunction) -> bool {
    matches!(f.kind, TypedFunctionKind::ModuleFunction)
        && !is_entry(f)
        && !f.params.iter().any(|p| type_has_generic(&p.ty))
        && !type_has_generic(&f.ret)
}

/// Whether a type mentions an unresolved generic / higher-kinded variable
/// (LC-THREAD-GENERIC: generic effectful functions are not threaded).
fn type_has_generic(t: &Type) -> bool {
    match t {
        Type::Generic(_) | Type::HktVar { .. } | Type::HktApp { .. } | Type::TypeCtor(_) => true,
        Type::Named(_, args) | Type::Tuple(args) => args.iter().any(type_has_generic),
        Type::Fn(ps, r, _, _) => ps.iter().any(type_has_generic) || type_has_generic(r),
        Type::Ref(inner, _) | Type::Slice(inner) | Type::Ptr(inner) | Type::MutPtr(inner) => {
            type_has_generic(inner)
        }
        Type::Array { elem, .. } => type_has_generic(elem),
        _ => false,
    }
}

fn is_entry(f: &TypedFunction) -> bool {
    // Actor inits/handlers and module init are identified by KIND (robust). The tool
    // entry `tool_main` is identified by NAME — but by the time the desugar runs the
    // name is MANGLED to `<module>::tool_main` and the export to `<module>__tool_main`
    // (type_check builds every ModuleFunction that way), so a bare-string compare
    // misses it and would thread the entry, corrupting its exported ABI (sweep root).
    matches!(
        f.kind,
        TypedFunctionKind::ActorInit { is_entry: true, .. }
            | TypedFunctionKind::ActorHandler { is_entry: true, .. }
            | TypedFunctionKind::ModuleInit
    ) || f.is_tool_main_entry()
}

/// A clause body's shape: `Some((is_resume, value))` where `value` is the resumed
/// expression (`{ resume <e> }`, scoped) or the clause value (`{ <e> }`, abortive).
/// `None` for any other body (ineligible).
fn clause_shape(clause: &crate::typed_ast::TypedHandleClause) -> Option<(bool, &TypedExpr)> {
    let [TypedStmt::Expr(es)] = clause.body.statements.as_slice() else {
        return None;
    };
    match &es.expr.kind {
        TypedExprKind::Resume(r) => Some((true, &r.value)),
        _ => Some((false, &es.expr)),
    }
}

/// A clause value EH4 will inline into a capture-free closure: only literals, the
/// clause's own `binders`, and binary arithmetic of simple sub-expressions. Anything
/// else (a call, indirect call, closure, capability, field access, …) stays gated —
/// a whitelist, not a capture blacklist, is the safe default (sweep roots EH4-H4/H5).
fn resume_is_simple(expr: &TypedExpr, binders: &[String]) -> bool {
    match &expr.kind {
        TypedExprKind::Literal(_) => true,
        TypedExprKind::Local(name) => binders.contains(name),
        TypedExprKind::Binary(b) => {
            resume_is_simple(&b.lhs, binders) && resume_is_simple(&b.rhs, binders)
        }
        _ => false,
    }
}

// ── Pass B helpers: rewrite performs + forward evidence ──────────────────────

/// Rewrite, in every E-function body: each statement-level scoped `perform E.op(args)`
/// into an `IndirectCall` on the matching evidence parameter, and each statement-level
/// direct `Call` to an E-function into a call that forwards the caller's evidence.
fn rewrite_scoped_and_forwarding(stmts: &mut [TypedStmt], effs: &[String], threading: &Threading) {
    for_each_stmt_expr_mut(stmts, &mut |e: &mut TypedExpr| {
        // Scoped perform -> IndirectCall.
        let perf = match &e.kind {
            TypedExprKind::Perform(p) => effs.iter().find_map(|eff| {
                if &p.effect != eff {
                    return None;
                }
                threading.effects[eff]
                    .ops
                    .iter()
                    .find(|op| op.name == p.op && !op.abortive)
                    .map(|op| {
                        (
                            op.ev_name.clone(),
                            Type::Fn(
                                op.params.clone(),
                                Box::new(op.ret.clone()),
                                false,
                                EffectSet::empty(),
                            ),
                            op.ret.clone(),
                            p.args.clone(),
                        )
                    })
            }),
            _ => None,
        };
        if let Some((ev_name, ev_ty, ret, args)) = perf {
            e.kind = TypedExprKind::IndirectCall(TypedIndirectCallExpr {
                callee_local: ev_name,
                callee_ty: ev_ty,
                args,
                kind: TypedIndirectCallKind::ScopedEffect,
            });
            e.ty = ret;
            return;
        }
        // Forwarding call -> append the caller's evidence for the callee's effects.
        let span = e.span;
        let fwd = match &e.kind {
            TypedExprKind::Call(c) => forwarding_args(&c.callee, threading, span),
            _ => None,
        };
        if let Some(extra) = fwd
            && let TypedExprKind::Call(c) = &mut e.kind
        {
            c.args.extend(extra);
        }
    });
}

/// The evidence arguments a caller forwards to a direct call of E-function `callee`:
/// a `Local` reference to the caller's own `$ev$E$op` parameter for each of the
/// callee's threaded operations, in canonical (effect, op) order. `None` if `callee`
/// is not an E-function. Only scoped effects propagate (abortive effects are gated to
/// direct scrutinees), so the forwarded type is always `Fn(op_params) -> op_ret`.
fn forwarding_args(
    callee: &str,
    threading: &Threading,
    span: crate::span::Span,
) -> Option<Vec<TypedExpr>> {
    let effs = threading.fn_effects.get(callee)?;
    let mut args = Vec::new();
    for e in effs {
        for op in &threading.effects[e].ops {
            args.push(TypedExpr {
                ty: Type::Fn(
                    op.params.clone(),
                    Box::new(op.ret.clone()),
                    false,
                    EffectSet::empty(),
                ),
                kind: TypedExprKind::Local(op.ev_name.clone()),
                span,
                refinement: None,
            });
        }
    }
    Some(args)
}

/// EH4.2: rewrite a bare `perform E.op(args);` statement of an ABORTIVE operation into
/// `return $ev$E$op(args);` — the performer calls the clause closure to compute the
/// handle value and returns it, abandoning the rest of its body (LC-ABORT2). Only a
/// `TypedStmt::Expr` whose expression IS the abortive perform is rewritten. Recurses
/// into nested blocks.
fn rewrite_abortive_returns(
    stmts: &mut [TypedStmt],
    f_ret: &Type,
    effs: &[String],
    threading: &Threading,
) {
    for stmt in stmts.iter_mut() {
        match stmt {
            TypedStmt::If(s) => {
                rewrite_abortive_returns(&mut s.then_branch.statements, f_ret, effs, threading);
                rewrite_abortive_returns(&mut s.else_branch.statements, f_ret, effs, threading);
            }
            TypedStmt::While(s) => {
                rewrite_abortive_returns(&mut s.body.statements, f_ret, effs, threading)
            }
            TypedStmt::ForIn(s) => rewrite_abortive_returns(&mut s.body, f_ret, effs, threading),
            TypedStmt::ForRange(s) => rewrite_abortive_returns(&mut s.body, f_ret, effs, threading),
            TypedStmt::Match(s) => {
                for arm in &mut s.arms {
                    rewrite_abortive_returns(&mut arm.body.statements, f_ret, effs, threading);
                }
            }
            _ => {}
        }
        let hit = match stmt {
            TypedStmt::Expr(es) => match &es.expr.kind {
                TypedExprKind::Perform(p) => effs.iter().find_map(|eff| {
                    if &p.effect != eff {
                        return None;
                    }
                    threading.effects[eff]
                        .ops
                        .iter()
                        .find(|op| op.name == p.op && op.abortive)
                        .map(|op| {
                            (
                                op.ev_name.clone(),
                                op.params.clone(),
                                p.args.clone(),
                                es.expr.span,
                            )
                        })
                }),
                _ => None,
            },
            _ => None,
        };
        if let Some((ev_name, op_params, args, span)) = hit {
            *stmt = TypedStmt::Return(TypedReturnStmt {
                value: Some(TypedExpr {
                    ty: f_ret.clone(),
                    kind: TypedExprKind::IndirectCall(TypedIndirectCallExpr {
                        callee_local: ev_name,
                        callee_ty: Type::Fn(
                            op_params,
                            Box::new(f_ret.clone()),
                            false,
                            EffectSet::empty(),
                        ),
                        args,
                        kind: TypedIndirectCallKind::AbortiveEffect,
                    }),
                    span,
                    refinement: None,
                }),
                span,
            });
        }
    }
}

// ── Pass C helpers: rewrite handles + synthesize clause closures ─────────────

fn rewrite_handles(
    stmts: &mut [TypedStmt],
    threading: &Threading,
    module_name: &str,
    counter: &mut usize,
    new_closures: &mut Vec<TypedFunction>,
) {
    for_each_stmt_expr_mut(stmts, &mut |e: &mut TypedExpr| {
        let TypedExprKind::ClauseHandle(h) = &e.kind else {
            return;
        };
        let TypedExprKind::Call(call) = &h.scrutinee.kind else {
            return;
        };
        // The scrutinee must be an E-function we thread; its threaded effects drive
        // the evidence order (the same order Pass B appended its parameters).
        let Some(effs) = threading.fn_effects.get(&call.callee) else {
            return;
        };
        let handle_ty = e.ty.clone();
        // Synthesize one clause closure per (effect, op) in canonical order. Build all
        // first; only mutate `e` once every operation resolved (else leave for the gate).
        let mut synthesized: Vec<(TypedFunction, TypedExpr)> = Vec::new();
        let mut ok = true;
        'build: for eff in effs {
            for op in &threading.effects[eff].ops {
                let Some(clause) = h
                    .clauses
                    .iter()
                    .find(|c| &c.effect == eff && c.op == op.name)
                else {
                    ok = false;
                    break 'build;
                };
                let Some((_, value)) = clause_shape(clause) else {
                    ok = false;
                    break 'build;
                };
                let resume_expr = value.clone();
                let closure_ret = closure_ret_for(op, &handle_ty);

                let closure_id = *counter;
                *counter += 1;
                // A `$`-prefixed name (unspellable by users) that cannot collide with
                // the type-checker's `module::__closure_N` scheme (sweep root EH4-H3).
                let synthesized_name = format!("{module_name}::$eh_clause_{closure_id}");

                let mut params = vec![TypedParam {
                    flow: false,
                    mutability: crate::ast::Mutability::Default,
                    name: "__env".to_owned(),
                    ty: Type::Named("__closure_env".to_owned(), vec![]),
                    taint: TaintLabel::Public,
                }];
                assert_eq!(
                    op.params.len(),
                    op.param_taints.len(),
                    "effect desugar: operation `{}` has mismatched type/taint parameter metadata",
                    op.name
                );
                for ((binder, pty), taint) in clause
                    .binders
                    .iter()
                    .zip(op.params.iter())
                    .zip(op.param_taints.iter())
                {
                    params.push(TypedParam {
                        flow: false,
                        mutability: crate::ast::Mutability::Default,
                        name: binder.clone(),
                        ty: pty.clone(),
                        taint: *taint,
                    });
                }
                let body = TypedBlock {
                    statements: vec![TypedStmt::Return(TypedReturnStmt {
                        value: Some(resume_expr),
                        span: e.span,
                    })],
                    span: e.span,
                    guaranteed_return: true,
                };
                let func = TypedFunction {
                    ret_flow: false,
                    name: synthesized_name.clone(),
                    export_name: format!("$eh_clause_{closure_id}"),
                    kind: TypedFunctionKind::Closure,
                    externally_callable: false,
                    params,
                    captures: Vec::new(),
                    ret: closure_ret.clone(),
                    ret_taint: op
                        .param_taints
                        .iter()
                        .copied()
                        .fold(TaintLabel::Public, TaintLabel::lub),
                    effects: EffectSet::empty(),
                    body,
                    span: e.span,
                };
                let closure_expr = TypedExpr {
                    ty: Type::Fn(
                        op.params.clone(),
                        Box::new(closure_ret),
                        false,
                        EffectSet::empty(),
                    ),
                    kind: TypedExprKind::ClosureConstruct(TypedClosureConstructExpr {
                        synthesized_name,
                        captures: Vec::new(),
                        param_types: op.params.clone(),
                        ret_type: closure_ret_for(op, &handle_ty),
                        is_linear: false,
                    }),
                    span: e.span,
                    refinement: None,
                };
                synthesized.push((func, closure_expr));
            }
        }
        if !ok {
            return;
        }

        // Rewrite `handle g(args){…}` into `g(args, clause_closures…)`.
        let mut args = call.args.clone();
        for (func, closure_expr) in synthesized {
            new_closures.push(func);
            args.push(closure_expr);
        }
        let result_ty = e.ty.clone();
        e.kind = TypedExprKind::Call(TypedCallExpr {
            callee: call.callee.clone(),
            args,
        });
        e.ty = result_ty;
    });

    recurse_blocks_mut(stmts, &mut |inner| {
        rewrite_handles(inner, threading, module_name, counter, new_closures);
    });
}

// ── EH4.3c: abortive propagation via the EhResult discriminated-union return ──

/// An eligible PROPAGATING abortive effect (an abortive `perform` reached through an
/// intermediate tail-call). Lowered via a synthesized `$EhResult$<H>` enum + a
/// `$eh_unwrap` helper. See the spec's "EH4.3c" section.
struct EhrPlan {
    effect: String,
    op_name: String,
    op_params: Vec<Type>,
    op_param_taints: Vec<TaintLabel>,
    /// The abort evidence parameter name (`$ev$E$op`), typed `Fn(op_params) -> H`.
    ev_name: String,
    /// The handle type `H` — every chain function's return type and both enum payloads.
    h_type: Type,
    /// Conservative taint of either a normal chain result or an abort payload.
    h_taint: TaintLabel,
    /// `$EhResult$<H>` — the synthesized concrete enum name.
    enum_name: String,
    /// `<module>::$eh_unwrap_<H>` — the synthesized unwrap helper.
    unwrap_name: String,
    /// The chain functions (rewritten to return the enum).
    e_functions: Vec<String>,
    span: crate::span::Span,
}

#[allow(clippy::type_complexity)]
fn lower_abortive_propagation(
    module: &mut TypedModule,
    effect_ops: &BTreeMap<String, Vec<EffectOpSig>>,
    registry: &EffectRegistry,
    program_all_calls: &HashMap<String, usize>,
    new_enums: &mut Vec<SynthEnum>,
) {
    let plans = ehr_analyze(module, effect_ops, registry, program_all_calls);
    if plans.is_empty() {
        return;
    }

    // Synthesize each distinct `$EhResult$<H>` enum + its `$eh_unwrap_<H>` helper once.
    let mut synth_fns: Vec<TypedFunction> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    for plan in &plans {
        if seen.insert(plan.enum_name.clone()) {
            new_enums.push((
                plan.enum_name.clone(),
                (
                    vec![],
                    vec![
                        ("Normal".to_owned(), vec![plan.h_type.clone()]),
                        ("Aborted".to_owned(), vec![plan.h_type.clone()]),
                    ],
                ),
            ));
            synth_fns.push(synth_unwrap_fn(plan));
        }
    }

    // Transform every chain function: return type -> the enum; gain the abort evidence
    // param; rewrite its body (abortive perform -> `return Aborted(ev(args))`; tail call
    // to a chain function -> propagate; any other `return v` -> `return Normal(v)`).
    for plan in &plans {
        let enum_named = Type::Named(plan.enum_name.clone(), vec![]);
        let ev_ty = Type::Fn(
            plan.op_params.clone(),
            Box::new(plan.h_type.clone()),
            false,
            EffectSet::empty(),
        );
        for fname in &plan.e_functions {
            let Some(f) = module.functions.iter_mut().find(|f| &f.name == fname) else {
                continue;
            };
            f.ret = enum_named.clone();
            f.params.push(TypedParam {
                flow: false,
                mutability: crate::ast::Mutability::Default,
                name: plan.ev_name.clone(),
                ty: ev_ty.clone(),
                taint: TaintLabel::Public,
            });
            ehr_rewrite_body(&mut f.body.statements, plan, &enum_named);
            // The chain function's ABI is now rewritten ((..) -> $EhResult, + the evidence
            // param), so its original public symbol must NOT be exported with that mutated
            // shape. It is only ever called internally (by `name`, via AIR `function_ids`).
            // Mark the EXPORT name `$`-internal so `wasm.rs` drops it from the public ABI
            // (a `$`-prefixed export name cannot collide with a user symbol — `$` is outside
            // the identifier grammar). The `name` / call resolution is untouched.
            if !f.export_name.starts_with('$') {
                f.export_name = format!("$eh_chain${}", f.export_name);
            }
        }
    }

    // Rewrite handles: `<lhs> = handle g(args){ E.op(b) => clauseval }` becomes
    // `<lhs> = $eh_unwrap_<H>(g(args, <clause closure>))`.
    let module_name = module.name.clone();
    let mut counter = module.functions.len() + synth_fns.len();
    let mut new_closures: Vec<TypedFunction> = Vec::new();
    for f in &mut module.functions {
        ehr_rewrite_handles(
            &mut f.body.statements,
            &plans,
            &module_name,
            &mut counter,
            &mut new_closures,
        );
    }
    module.functions.extend(synth_fns);
    module.functions.extend(new_closures);
}

/// A type's identifier-safe suffix for the `$EhResult$<H>` / `$eh_unwrap_<H>` names.
/// `None` for a type that cannot be an enum payload here (gate via LC-EHR-PAYLOAD).
fn ehr_mangle_h(t: &Type) -> Option<String> {
    Some(match t {
        Type::I64 => "i64".to_owned(),
        Type::I32 => "i32".to_owned(),
        Type::U64 => "u64".to_owned(),
        Type::U32 => "u32".to_owned(),
        Type::Bool => "bool".to_owned(),
        Type::Str => "str".to_owned(),
        Type::I256 => "i256".to_owned(),
        Type::U256 => "u256".to_owned(),
        Type::F64 => "f64".to_owned(),
        Type::Named(n, args) if args.is_empty() => format!("N_{n}"),
        _ => return None,
    })
}

/// `fn $eh_unwrap_<H>(__r: $EhResult$<H>) -> H { match __r { Normal(v) => return v,
/// Aborted(p) => return p } }`. Both arms return the payload (both are `H`).
fn synth_unwrap_fn(plan: &EhrPlan) -> TypedFunction {
    let span = plan.span;
    let enum_ty = Type::Named(plan.enum_name.clone(), vec![]);
    let local = |name: &str| TypedExpr {
        ty: plan.h_type.clone(),
        kind: TypedExprKind::Local(name.to_owned()),
        span,
        refinement: None,
    };
    let arm = |variant: &str, bind: &str| TypedMatchArm {
        pattern: TypedPattern::EnumVariant {
            type_name: plan.enum_name.clone(),
            variant: variant.to_owned(),
            bindings: vec![(bind.to_owned(), plan.h_type.clone())],
        },
        guard: None,
        body: TypedBlock {
            statements: vec![TypedStmt::Return(TypedReturnStmt {
                value: Some(local(bind)),
                span,
            })],
            span,
            guaranteed_return: true,
        },
        span,
    };
    let body = TypedBlock {
        statements: vec![TypedStmt::Match(TypedMatchStmt {
            scrutinee: TypedExpr {
                ty: enum_ty.clone(),
                kind: TypedExprKind::Local("__r".to_owned()),
                span,
                refinement: None,
            },
            arms: vec![arm("Normal", "__v"), arm("Aborted", "__p")],
            span,
        })],
        span,
        guaranteed_return: true,
    };
    TypedFunction {
        ret_flow: false,
        name: plan.unwrap_name.clone(),
        // The export name MUST be module-qualified (EH4.3d ROOT-A fix): two same-ring
        // modules each lowering an abortive chain with the same payload `H` would
        // otherwise both export the bare `$eh_unwrap_<H>` and the wasm module fails to
        // validate (duplicate export). `unwrap_name` is already `{module}::$eh_unwrap_<H>`;
        // mirror the normal `::`→`__` export mangling so each module's helper is distinct.
        export_name: plan.unwrap_name.replace("::", "__"),
        kind: TypedFunctionKind::ModuleFunction,
        externally_callable: false,
        params: vec![TypedParam {
            flow: false,
            mutability: crate::ast::Mutability::Default,
            name: "__r".to_owned(),
            ty: enum_ty,
            taint: plan.h_taint,
        }],
        captures: Vec::new(),
        ret: plan.h_type.clone(),
        ret_taint: plan.h_taint,
        effects: EffectSet::empty(),
        body,
        span,
    }
}

/// Rewrite a chain function's body to the `EhResult` discipline.
fn ehr_rewrite_body(stmts: &mut [TypedStmt], plan: &EhrPlan, enum_named: &Type) {
    let ev_ty = Type::Fn(
        plan.op_params.clone(),
        Box::new(plan.h_type.clone()),
        false,
        EffectSet::empty(),
    );
    for stmt in stmts.iter_mut() {
        // Recurse into nested blocks first.
        match stmt {
            TypedStmt::If(s) => {
                ehr_rewrite_body(&mut s.then_branch.statements, plan, enum_named);
                ehr_rewrite_body(&mut s.else_branch.statements, plan, enum_named);
            }
            TypedStmt::While(s) => ehr_rewrite_body(&mut s.body.statements, plan, enum_named),
            TypedStmt::ForIn(s) => ehr_rewrite_body(&mut s.body, plan, enum_named),
            TypedStmt::ForRange(s) => ehr_rewrite_body(&mut s.body, plan, enum_named),
            TypedStmt::Match(s) => {
                for arm in &mut s.arms {
                    ehr_rewrite_body(&mut arm.body.statements, plan, enum_named);
                }
            }
            _ => {}
        }
        // Abortive `perform E.op(args);` -> `return Aborted(ev(args));`.
        let abortive = match stmt {
            TypedStmt::Expr(es) => match &es.expr.kind {
                TypedExprKind::Perform(p) if p.effect == plan.effect && p.op == plan.op_name => {
                    Some((p.args.clone(), es.expr.span))
                }
                _ => None,
            },
            _ => None,
        };
        if let Some((args, span)) = abortive {
            let ev_call = TypedExpr {
                ty: plan.h_type.clone(),
                kind: TypedExprKind::IndirectCall(TypedIndirectCallExpr {
                    callee_local: plan.ev_name.clone(),
                    callee_ty: ev_ty.clone(),
                    args,
                    kind: TypedIndirectCallKind::AbortiveEffect,
                }),
                span,
                refinement: None,
            };
            *stmt = TypedStmt::Return(TypedReturnStmt {
                value: Some(TypedExpr {
                    ty: enum_named.clone(),
                    kind: TypedExprKind::EnumConstruct(TypedEnumConstructExpr {
                        enum_name: plan.enum_name.clone(),
                        variant_index: 1, // Aborted
                        fields: vec![ev_call],
                    }),
                    span,
                    refinement: None,
                }),
                span,
            });
            continue;
        }
        // `return <expr>`: a tail call to a chain function propagates (append `ev`,
        // return the enum directly); any other value is wrapped in `Normal`.
        if let TypedStmt::Return(rs) = stmt
            && let Some(val) = rs.value.take()
        {
            let span = val.span;
            let is_tail =
                matches!(&val.kind, TypedExprKind::Call(c) if plan.e_functions.contains(&c.callee));
            if is_tail {
                let mut call = val;
                if let TypedExprKind::Call(c) = &mut call.kind {
                    c.args.push(TypedExpr {
                        ty: ev_ty.clone(),
                        kind: TypedExprKind::Local(plan.ev_name.clone()),
                        span,
                        refinement: None,
                    });
                }
                call.ty = enum_named.clone();
                rs.value = Some(call);
            } else {
                rs.value = Some(TypedExpr {
                    ty: enum_named.clone(),
                    kind: TypedExprKind::EnumConstruct(TypedEnumConstructExpr {
                        enum_name: plan.enum_name.clone(),
                        variant_index: 0, // Normal
                        fields: vec![val],
                    }),
                    span,
                    refinement: None,
                });
            }
        }
    }
}

/// Rewrite `handle g(args){ E.op(b) => clauseval }` to `$eh_unwrap(g(args, closure))`.
fn ehr_rewrite_handles(
    stmts: &mut [TypedStmt],
    plans: &[EhrPlan],
    module_name: &str,
    counter: &mut usize,
    new_closures: &mut Vec<TypedFunction>,
) {
    for_each_stmt_expr_mut(stmts, &mut |e: &mut TypedExpr| {
        let TypedExprKind::ClauseHandle(h) = &e.kind else {
            return;
        };
        let TypedExprKind::Call(call) = &h.scrutinee.kind else {
            return;
        };
        let Some(plan) = plans.iter().find(|p| p.e_functions.contains(&call.callee)) else {
            return;
        };
        if h.clauses.len() != 1 {
            return;
        }
        let clause = &h.clauses[0];
        if clause.effect != plan.effect || clause.op != plan.op_name {
            return;
        }
        let Some((_, value)) = clause_shape(clause) else {
            return;
        };
        let clause_value = value.clone();

        // Synthesize the clause closure `Fn(op_params) -> H` (body `return clauseval`).
        let closure_id = *counter;
        *counter += 1;
        let synthesized_name = format!("{module_name}::$eh_clause_{closure_id}");
        let mut params = vec![TypedParam {
            flow: false,
            mutability: crate::ast::Mutability::Default,
            name: "__env".to_owned(),
            ty: Type::Named("__closure_env".to_owned(), vec![]),
            taint: TaintLabel::Public,
        }];
        assert_eq!(
            plan.op_params.len(),
            plan.op_param_taints.len(),
            "effect desugar: operation `{}.{}` has mismatched type/taint parameter metadata",
            plan.effect,
            plan.op_name
        );
        for ((binder, pty), taint) in clause
            .binders
            .iter()
            .zip(plan.op_params.iter())
            .zip(plan.op_param_taints.iter())
        {
            params.push(TypedParam {
                flow: false,
                mutability: crate::ast::Mutability::Default,
                name: binder.clone(),
                ty: pty.clone(),
                taint: *taint,
            });
        }
        new_closures.push(TypedFunction {
            ret_flow: false,
            name: synthesized_name.clone(),
            export_name: format!("$eh_clause_{closure_id}"),
            kind: TypedFunctionKind::Closure,
            externally_callable: false,
            params,
            captures: Vec::new(),
            ret: plan.h_type.clone(),
            ret_taint: plan
                .op_param_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub),
            effects: EffectSet::empty(),
            body: TypedBlock {
                statements: vec![TypedStmt::Return(TypedReturnStmt {
                    value: Some(clause_value),
                    span: e.span,
                })],
                span: e.span,
                guaranteed_return: true,
            },
            span: e.span,
        });
        let closure_expr = TypedExpr {
            ty: Type::Fn(
                plan.op_params.clone(),
                Box::new(plan.h_type.clone()),
                false,
                EffectSet::empty(),
            ),
            kind: TypedExprKind::ClosureConstruct(TypedClosureConstructExpr {
                synthesized_name,
                captures: Vec::new(),
                param_types: plan.op_params.clone(),
                ret_type: plan.h_type.clone(),
                is_linear: false,
            }),
            span: e.span,
            refinement: None,
        };

        // `g(orig_args.., closure)` returns the enum; wrap in `$eh_unwrap`.
        let mut inner_args = call.args.clone();
        inner_args.push(closure_expr);
        let inner_call = TypedExpr {
            ty: Type::Named(plan.enum_name.clone(), vec![]),
            kind: TypedExprKind::Call(TypedCallExpr {
                callee: call.callee.clone(),
                args: inner_args,
            }),
            span: e.span,
            refinement: None,
        };
        let result_ty = e.ty.clone();
        e.kind = TypedExprKind::Call(TypedCallExpr {
            callee: plan.unwrap_name.clone(),
            args: vec![inner_call],
        });
        e.ty = result_ty;
    });

    recurse_blocks_mut(stmts, &mut |inner| {
        ehr_rewrite_handles(inner, plans, module_name, counter, new_closures);
    });
}

/// Count `return <call-to-a-chain-function>` (tail-call propagation sites) per callee.
fn ehr_count_tail_calls(
    stmts: &[TypedStmt],
    e_names: &BTreeSet<&String>,
    tail_calls: &mut HashMap<String, usize>,
) {
    for stmt in stmts {
        match stmt {
            TypedStmt::Return(rs) => {
                if let Some(v) = &rs.value
                    && let TypedExprKind::Call(c) = &v.kind
                    && e_names.contains(&c.callee)
                {
                    *tail_calls.entry(c.callee.clone()).or_insert(0) += 1;
                }
            }
            TypedStmt::If(s) => {
                ehr_count_tail_calls(&s.then_branch.statements, e_names, tail_calls);
                ehr_count_tail_calls(&s.else_branch.statements, e_names, tail_calls);
            }
            TypedStmt::While(s) => ehr_count_tail_calls(&s.body.statements, e_names, tail_calls),
            TypedStmt::ForIn(s) => ehr_count_tail_calls(&s.body, e_names, tail_calls),
            TypedStmt::ForRange(s) => ehr_count_tail_calls(&s.body, e_names, tail_calls),
            TypedStmt::Match(s) => {
                for arm in &s.arms {
                    ehr_count_tail_calls(&arm.body.statements, e_names, tail_calls);
                }
            }
            _ => {}
        }
    }
}

/// Find the eligible propagating-abortive effects (LC-EHR-*).
fn ehr_analyze(
    module: &TypedModule,
    effect_ops: &BTreeMap<String, Vec<EffectOpSig>>,
    registry: &EffectRegistry,
    program_all_calls: &HashMap<String, usize>,
) -> Vec<EhrPlan> {
    let mut plans = Vec::new();
    for (effect, ops) in effect_ops {
        // Minimal: a single abortive operation, no scoped ops in the effect.
        if ops.len() != 1 {
            continue;
        }
        let op = &ops[0];
        if op.ret != Type::Never {
            continue;
        }
        let Some(eff_id) = registry.lookup(effect) else {
            continue;
        };
        // Chain functions: row is EXACTLY this one effect (no mixing with scoped /
        // other effects — minimal), all threadable.
        let e_funcs: Vec<&TypedFunction> = module
            .functions
            .iter()
            .filter(|f| f.effects.effects.len() == 1 && f.effects.effects.contains(&eff_id))
            .collect();
        if e_funcs.is_empty() || e_funcs.iter().any(|f| !is_threadable(f)) {
            continue;
        }
        // LC-EHR-RET-UNIFORM + LC-EHR-PAYLOAD: a single payload type `H`.
        let h = e_funcs[0].ret.clone();
        if e_funcs.iter().any(|f| f.ret != h) {
            continue;
        }
        let Some(hmangle) = ehr_mangle_h(&h) else {
            continue;
        };
        let e_names: BTreeSet<&String> = e_funcs.iter().map(|f| &f.name).collect();

        // Scan call positions + handles across the whole module.
        let mut all_calls: HashMap<String, usize> = HashMap::new();
        let mut scrutinee_calls: HashMap<String, usize> = HashMap::new();
        let mut tail_calls: HashMap<String, usize> = HashMap::new();
        let mut handles: Vec<(Type, bool, Option<Type>)> = Vec::new(); // (scrutinee_ty, eligible, clause_value_ty)
        for f in &module.functions {
            visit_block_constructs(&f.body, &mut |ex: &TypedExpr| match &ex.kind {
                TypedExprKind::Call(c) if e_names.contains(&c.callee) => {
                    *all_calls.entry(c.callee.clone()).or_insert(0) += 1;
                }
                TypedExprKind::ClauseHandle(hh) => {
                    if let TypedExprKind::Call(c) = &hh.scrutinee.kind
                        && e_names.contains(&c.callee)
                    {
                        *scrutinee_calls.entry(c.callee.clone()).or_insert(0) += 1;
                        let eligible = hh.clauses.len() == 1
                            && {
                                let cl = &hh.clauses[0];
                                cl.effect == *effect
                                    && cl.op == op.name
                                    && matches!(clause_shape(cl), Some((false, v)) if resume_is_simple(v, &cl.binders))
                            };
                        let cval = hh
                            .clauses
                            .first()
                            .and_then(clause_shape)
                            .map(|(_, v)| v.ty.clone());
                        handles.push((ex.ty.clone(), eligible, cval));
                    }
                }
                _ => {}
            });
            // Tail calls are only counted from CHAIN functions: only those are
            // rewritten to forward `ev`. A tail call to a chain function from a
            // NON-chain caller (e.g. row `{Fail, Other}`, excluded from the chain) is
            // NOT counted here, so it shows up as an unexplained call below and gates
            // — otherwise the un-rewritten non-chain caller would invoke the rewritten
            // chain function with the stale signature (sweep root: non-validating wasm).
            if e_names.contains(&f.name) {
                ehr_count_tail_calls(&f.body.statements, &e_names, &mut tail_calls);
            }
        }

        // LC-EHR-TAIL: every call to a chain function is a handle scrutinee or a tail
        // call FROM ANOTHER CHAIN FUNCTION (so all_calls is fully explained). Any other
        // reach — a non-tail call, or a tail call from a non-chain caller — makes
        // all_calls exceed scrutinee + tail and gates the whole effect.
        let positions_ok = e_funcs.iter().all(|f| {
            all_calls.get(&f.name).copied().unwrap_or(0)
                == scrutinee_calls.get(&f.name).copied().unwrap_or(0)
                    + tail_calls.get(&f.name).copied().unwrap_or(0)
        });
        // Must actually PROPAGATE (a tail call exists) — else the direct case (EH4.2)
        // already handles it and this would steal it.
        let propagates = tail_calls.values().sum::<usize>() > 0;
        // Every handle: eligible, scrutinee type == H, clause value assignable to H.
        let handles_ok = !handles.is_empty()
            && handles.iter().all(|(sty, elig, cval)| {
                *elig
                    && sty == &h
                    && cval
                        .as_ref()
                        .is_none_or(|cv| crate::type_check::type_compatible(&h, cv))
            });
        // All abortive performs statement-level.
        let mut deep = 0usize;
        let mut stmt = 0usize;
        for f in &e_funcs {
            visit_block_constructs(&f.body, &mut |ex: &TypedExpr| {
                if matches!(&ex.kind, TypedExprKind::Perform(p) if p.effect == *effect) {
                    deep += 1;
                }
            });
            for_each_stmt_expr_ref(&f.body.statements, &mut |ex: &TypedExpr| {
                if matches!(&ex.kind, TypedExprKind::Perform(p) if p.effect == *effect) {
                    stmt += 1;
                }
            });
        }
        let performs_ok = deep == stmt && deep > 0;

        // ROOT-B (EH4.3d): a chain function reached from ANOTHER module has a caller this
        // per-module pass will NOT rewrite, so it would invoke the rewritten chain fn with
        // the stale (pre-evidence, pre-enum) signature → non-validating wasm. `all_calls`
        // counts only this module; `program_all_calls` counts every module — so
        // program > intra for any chain fn means a foreign caller exists. Gate the effect
        // (its handler / perform nodes then survive to the E004 gate; multi-module
        // abortive propagation is deferred — AG-MM-3).
        let cross_module_reach = e_funcs.iter().any(|f| {
            program_all_calls.get(&f.name).copied().unwrap_or(0)
                > all_calls.get(&f.name).copied().unwrap_or(0)
        });

        if positions_ok && propagates && handles_ok && performs_ok && !cross_module_reach {
            let op_taint = op
                .param_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            let h_taint = e_funcs
                .iter()
                .map(|function| function.ret_taint)
                .fold(op_taint, TaintLabel::lub);
            plans.push(EhrPlan {
                effect: effect.clone(),
                op_name: op.name.clone(),
                op_params: op.params.clone(),
                op_param_taints: op.param_taints.clone(),
                ev_name: format!("$ev${effect}${}", op.name),
                h_type: h.clone(),
                h_taint,
                enum_name: format!("$EhResult${hmangle}"),
                unwrap_name: format!("{}::$eh_unwrap_{hmangle}", module.name),
                e_functions: e_funcs.iter().map(|f| f.name.clone()).collect(),
                span: e_funcs[0].span,
            });
        }
    }
    plans
}

// ── generic walkers ──────────────────────────────────────────────────────────

/// Apply `f` to each STATEMENT-LEVEL expression (the direct value of a let / assign /
/// expr-stmt / return, and the condition / scrutinee / iterable of control flow),
/// recursing into nested blocks. Does NOT descend into a statement-level expression's
/// sub-expressions (so a `ClauseHandle`'s scrutinee call is not visited here).
fn for_each_stmt_expr_mut(stmts: &mut [TypedStmt], f: &mut impl FnMut(&mut TypedExpr)) {
    for stmt in stmts.iter_mut() {
        match stmt {
            TypedStmt::Let(s) => f(&mut s.value),
            TypedStmt::Assign(s) => f(&mut s.value),
            TypedStmt::Expr(s) => f(&mut s.expr),
            TypedStmt::Return(s) => {
                if let Some(v) = &mut s.value {
                    f(v);
                }
            }
            TypedStmt::If(s) => {
                f(&mut s.condition);
                for_each_stmt_expr_mut(&mut s.then_branch.statements, f);
                for_each_stmt_expr_mut(&mut s.else_branch.statements, f);
            }
            TypedStmt::While(s) => {
                f(&mut s.condition);
                for_each_stmt_expr_mut(&mut s.body.statements, f);
            }
            TypedStmt::ForIn(s) => {
                f(&mut s.iterable);
                for_each_stmt_expr_mut(&mut s.body, f);
            }
            TypedStmt::ForRange(s) => {
                f(&mut s.start);
                f(&mut s.end);
                for_each_stmt_expr_mut(&mut s.body, f);
            }
            TypedStmt::Match(s) => {
                f(&mut s.scrutinee);
                for arm in &mut s.arms {
                    if let Some(g) = &mut arm.guard {
                        f(g);
                    }
                    for_each_stmt_expr_mut(&mut arm.body.statements, f);
                }
            }
            TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
        }
    }
}

/// Run `f` over each nested block's statement list (for recursive rewrites that must
/// not re-process the current level).
fn recurse_blocks_mut(stmts: &mut [TypedStmt], f: &mut impl FnMut(&mut [TypedStmt])) {
    for stmt in stmts.iter_mut() {
        match stmt {
            TypedStmt::If(s) => {
                f(&mut s.then_branch.statements);
                f(&mut s.else_branch.statements);
            }
            TypedStmt::While(s) => f(&mut s.body.statements),
            TypedStmt::ForIn(s) => f(&mut s.body),
            TypedStmt::ForRange(s) => f(&mut s.body),
            TypedStmt::Match(s) => {
                for arm in &mut s.arms {
                    f(&mut arm.body.statements);
                }
            }
            _ => {}
        }
    }
}

/// Immutable analogue of [`for_each_stmt_expr_mut`].
fn for_each_stmt_expr_ref(stmts: &[TypedStmt], f: &mut impl FnMut(&TypedExpr)) {
    for stmt in stmts {
        match stmt {
            TypedStmt::Let(s) => f(&s.value),
            TypedStmt::Assign(s) => f(&s.value),
            TypedStmt::Expr(s) => f(&s.expr),
            TypedStmt::Return(s) => {
                if let Some(v) = &s.value {
                    f(v);
                }
            }
            TypedStmt::If(s) => {
                f(&s.condition);
                for_each_stmt_expr_ref(&s.then_branch.statements, f);
                for_each_stmt_expr_ref(&s.else_branch.statements, f);
            }
            TypedStmt::While(s) => {
                f(&s.condition);
                for_each_stmt_expr_ref(&s.body.statements, f);
            }
            TypedStmt::ForIn(s) => {
                f(&s.iterable);
                for_each_stmt_expr_ref(&s.body, f);
            }
            TypedStmt::ForRange(s) => {
                f(&s.start);
                f(&s.end);
                for_each_stmt_expr_ref(&s.body, f);
            }
            TypedStmt::Match(s) => {
                f(&s.scrutinee);
                for arm in &s.arms {
                    if let Some(g) = &arm.guard {
                        f(g);
                    }
                    for_each_stmt_expr_ref(&arm.body.statements, f);
                }
            }
            TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
        }
    }
}
