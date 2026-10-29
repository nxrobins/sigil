//! Free-call resolution and typed call construction.

use std::collections::HashMap;

use super::super::resolve::{
    apply_subst, default_int_lit_in_type, register_concrete_enum, render_type,
    resolve_int_literals_or_reject, resolve_type_expr, resolve_type_expr_kinded,
    try_array_size_mismatch_diagnostic, try_cap_deadline_diagnostic, try_state_mismatch_diagnostic,
    type_compatible, unify,
};
use super::super::statements::{self, check_function_block};
use super::super::{
    CrossModuleResolution, FunctionSig, MAX_MONOMORPH_DEPTH, MonomorphTracker, ParamRegion,
    RegionId, Type, TypeCheckContext, TypeUniverse, resolve_effect_row_with_vars,
    resolve_function_call_with_context,
};
use super::super::{traits, universe};
use super::intrinsics::{infer_intrinsic_call_expr, resolve_intrinsic_call};
use super::{
    check_generic_aggregate_cap_smuggle, fit_to_instance_slot, infer_arg_with_expected,
    type_is_concrete, type_mentions_generic,
};
use crate::air::mangle_type;
use crate::ast::{CallExpr, TypeExpr};
use crate::diagnostics::{Diagnostic, codes};
use crate::registries::EffectSet;
use crate::span::Span;
use crate::typed_ast::{
    TypedCallExpr, TypedEnumConstructExpr, TypedExpr, TypedExprKind, TypedExternCallExpr,
    TypedFunction, TypedFunctionKind, TypedIndirectCallExpr, TypedIndirectCallKind, TypedParam,
};

pub(super) fn infer_call_expr(
    expr: &CallExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let (function_sigs, _actor_sigs, module_name, universe) = context.parts();
    let callee_name = expr.callee.display_name();
    // PR #136: resolve the callee BEFORE inferring args — the intrinsic decision
    // and the cross-module sig are both arg-independent (CF-I7) — so each arg can
    // be pinned to its concrete parameter type while inferring. This enables
    // nested inference (`f(Vec::new())`) and narrows literals to the param width
    // (#132). Generic-fn / closure fallbacks and intrinsics resolve to
    // `concrete_params = None` and are unaffected.
    let intrinsic_shape = resolve_intrinsic_call(&expr.callee);
    // Clone the concrete param types in a scope that DROPS the resolution's
    // borrow of `tracker` before the `&mut tracker` arg loop; `resolution` is
    // recomputed after the loop (CF-I7: arg-independent ⇒ identical result).
    let (resolved_params, unresolved) = if intrinsic_shape.is_some() {
        (None, false)
    } else {
        match resolve_function_call_with_context(&expr.callee, module_name, function_sigs, tracker)
        {
            Some(CrossModuleResolution::Found(sig)) => (Some(sig.params.clone()), false),
            None => (None, true),
            Some(_) => (None, false),
        }
    };
    // An enum-variant constructor is reached (Fallback 2 of
    // `infer_unresolved_call_expr`) exactly when nothing resolved and no generic fn
    // has this name, so its arguments are pinned to their payload slots here, the
    // way a resolved call's are pinned to its parameters. The construct lays each
    // payload out at its ARGUMENT's width while a `match` reads it at the declared
    // payload type's offsets, so an unpinned `3` in an `i32` slot was stored as 8
    // bytes and every later payload read the wrong bytes (`E::V(3, 40)` with
    // `V(i32, i64)` matched `b` as `40 << 32`). The variant decision is the one
    // Fallback 2 makes again after the loop (`classify_variant_callee`, CF-I7).
    // A generic function's arguments are pinned to its parameters too
    // (`generic_formal_slots`), as far as a turbofish or the arguments before
    // them have bound the type parameters, and a closure-typed local's arguments
    // to its parameter types (`closure_param_slots`). The three follow the order
    // in which `infer_unresolved_call_expr` dispatches after the loop: a generic
    // function, then a variant, then a closure-typed local.
    let slots: ArgSlots = if let Some(params) = resolved_params {
        ArgSlots::Params(params)
    } else if !unresolved {
        ArgSlots::Unpinned
    } else if let Some((_, generic_def)) = universe.generic_fns.get(&callee_name) {
        generic_formal_slots(generic_def, &expr.callee, universe)
    } else {
        match classify_variant_callee(&expr.callee, universe, tracker) {
            VariantCallee::Chosen(enum_name) => {
                variant_payload_slots(&enum_name, &expr.callee, universe, tracker)
            }
            VariantCallee::NotAVariant => closure_param_slots(&expr.callee, &callee_name, env),
            VariantCallee::NoSuchVariant(_) | VariantCallee::Ambiguous(_) => ArgSlots::Unpinned,
        }
    };
    // The bindings a turbofish and the arguments so far make for a generic
    // callee's type parameters, with `unify`'s first-binding-wins order, which
    // Fallback 1 recomputes over the same typed arguments after the loop.
    let mut bindings: HashMap<String, Type> = match &slots {
        ArgSlots::Generic { bound, .. } => bound.clone(),
        ArgSlots::Params(_) | ArgSlots::Unpinned => HashMap::new(),
    };
    let mut typed_args: Vec<TypedExpr> = Vec::with_capacity(expr.args.len());
    for (i, arg) in expr.args.iter().enumerate() {
        let typed = match &slots {
            ArgSlots::Params(params) => infer_arg_with_expected(
                arg,
                params.get(i),
                env,
                current_return,
                context,
                tracker,
                diagnostics,
            ),
            ArgSlots::Generic {
                formals,
                unpin_fn_slots,
                ..
            } => {
                let slot = formals
                    .get(i)
                    .map(|formal| apply_subst(formal, &bindings))
                    .filter(|slot| !(*unpin_fn_slots && type_mentions_fn(slot)));
                let typed = infer_arg_with_expected(
                    arg,
                    slot.as_ref(),
                    env,
                    current_return,
                    context,
                    tracker,
                    diagnostics,
                );
                if let Some(formal) = formals.get(i) {
                    unify(formal, &typed.ty, &mut bindings);
                }
                typed
            }
            ArgSlots::Unpinned => infer_arg_with_expected(
                arg,
                None,
                env,
                current_return,
                context,
                tracker,
                diagnostics,
            ),
        };
        typed_args.push(typed);
    }
    if let Some(shape) = intrinsic_shape {
        return infer_intrinsic_call_expr(
            expr,
            shape,
            typed_args,
            module_name,
            universe,
            diagnostics,
        );
    }

    // Cross-module resolution: distinguish private callees (T155) and
    // cross-ring calls (R004). Recomputed after the arg loop (CF-I7).
    let resolution =
        resolve_function_call_with_context(&expr.callee, module_name, function_sigs, tracker);
    // Phase 5a-1.6 / I21: emit a typed trace event with the dispatch
    // outcome. Payload contains module names, span, and outcome enum —
    // never raw source bytes.
    {
        let empty_candidates: Vec<String> = Vec::new();
        let (outcome, candidates_ref, resolved_ref): (
            crate::trace::DispatchOutcome,
            &[String],
            Option<&str>,
        ) = match &resolution {
            Some(CrossModuleResolution::Found(sig)) => (
                crate::trace::DispatchOutcome::Found,
                empty_candidates.as_slice(),
                Some(sig.qualified_name.as_str()),
            ),
            Some(CrossModuleResolution::Private { .. }) => (
                crate::trace::DispatchOutcome::Private,
                empty_candidates.as_slice(),
                None,
            ),
            Some(CrossModuleResolution::CrossRing { .. }) => (
                crate::trace::DispatchOutcome::CrossRing,
                empty_candidates.as_slice(),
                None,
            ),
            Some(CrossModuleResolution::Ambiguous { candidates, .. }) => (
                crate::trace::DispatchOutcome::Ambiguous,
                candidates.as_slice(),
                None,
            ),
            None => (
                crate::trace::DispatchOutcome::NotFound,
                empty_candidates.as_slice(),
                None,
            ),
        };
        crate::trace::dispatch(&crate::trace::CrossModuleDispatch {
            caller_module: module_name,
            callee_path: &expr.callee.segments,
            outcome,
            span: expr.span,
            candidates: candidates_ref,
            resolved: resolved_ref,
        });
    }

    // Regions (DEF-2a NC-R1 + DEF-2b PR-4, the AG-R2 lift): the call-argument escape
    // sink. Each argument's sink region is computed from the resolved callee's
    // `param_regions`: a `Region`-typed parameter receives a region HANDLE (threading,
    // an allowed position — NC-2b-2 — not a value escaping, so exempt); an `@in r`
    // parameter's value must outlive the region passed at `r`'s slot, mapped to the
    // CALLER-side `RegionId` of that region argument BEFORE comparing (NC-2b-3); every
    // other parameter — and EVERY argument when the callee is unresolved — is a `Global`
    // sink, so an un-annotated function still rejects region values (NC-2b-4,
    // fail-closed). With no region params this is exactly DEF-2a's blanket-`Global`
    // behavior (every `param_regions` entry `None`, every param non-`Region`) →
    // byte-identical. The sink runs whenever region values can exist — inside a region
    // (`depth > 0`) OR when the current function has region params (`@in`/`Region` values
    // can be passed at function depth 0); empty `current_param_regions` + depth 0 (the
    // common case) skips it exactly as DEF-2a did.
    if tracker.current_region_depth > 0 || !tracker.current_param_regions.is_empty() {
        let callee_sig = match &resolution {
            Some(CrossModuleResolution::Found(sig)) => Some(sig),
            _ => None,
        };
        for (i, arg) in typed_args.iter().enumerate() {
            // A region handle threaded into a `Region` parameter is an allowed position,
            // not an escape — skip the lifetime check (the handle cannot outlive itself).
            if callee_sig
                .and_then(|s| s.params.get(i))
                .is_some_and(|t| matches!(t, Type::Region))
            {
                continue;
            }
            let sink = match callee_sig.and_then(|s| s.param_regions.get(i)) {
                Some(ParamRegion::In(slot)) => typed_args
                    .get(*slot as usize)
                    .map(|region_arg| statements::region_of_value(region_arg, tracker))
                    .unwrap_or(RegionId::Global),
                _ => RegionId::Global,
            };
            statements::check_region_escape(
                arg,
                sink,
                "be passed to a function",
                tracker,
                diagnostics,
            );
        }
        // DEF-2b PR-5: the caller's obligation. For each declared `where region(a):
        // region(b)` of the callee, the region argument filling slot `a` must OUTLIVE the
        // region argument filling slot `b` (caller-side, consulting the CALLER's own
        // `where`) — otherwise the caller cannot satisfy the contract the callee's body
        // relies on, so a shorter-lived value could reach a longer-lived sink (NC-2b-4).
        // `check_region_escape(arg_a, region(arg_b))` is exactly "arg_a's region outlives
        // arg_b's region". Inert without a callee `where region` clause.
        if let Some(sig) = callee_sig {
            for &(a, b) in &sig.param_region_outlives {
                if let (Some(arg_a), Some(arg_b)) =
                    (typed_args.get(a as usize), typed_args.get(b as usize))
                {
                    let required = statements::region_of_value(arg_b, tracker);
                    statements::check_region_escape(
                        arg_a,
                        required,
                        "satisfy the callee's `where region(...)`: it must outlive another \
                         region argument",
                        tracker,
                        diagnostics,
                    );
                }
            }
        }
    }

    // Mutation-as-capability (PR-2b, NC-1/NC-3): the call-ARGUMENT escape gate —
    // THE chokepoint for free + cross-module calls (every such call routes through
    // here). A value that ALIASES a `@ReadOnly` object, passed into a
    // NON-`@ReadOnly` parameter, would hand the callee a mutable handle
    // (re-widening authority). Freezing on entry (mutable→`@ReadOnly`) and
    // readonly→readonly are fine; only readonly→mutable is rejected (H6). A
    // primitive-COPY argument (`f(p.x)`) is excluded by `is_aliasable_type`.
    if let Some(CrossModuleResolution::Found(sig)) = &resolution {
        for (i, arg) in typed_args.iter().enumerate() {
            let param_is_frozen = sig
                .param_mutability
                .get(i)
                .copied()
                .is_some_and(crate::ast::Mutability::is_frozen);
            // AGG-4 (aggregate-state hardening): the frozen SOURCE is either a
            // `@ReadOnly` local (the existing gate) OR a read rooted in a NON-`mut`
            // state field — the free/cross-module twin of the method-receiver fix, so
            // `mutate(d)` (mutate = `d @Mut`) on a non-`mut` aggregate state field is
            // rejected too. `mut`-EXEMPT + handler-only.
            let frozen_root = statements::place_root_local(arg)
                .filter(|root| tracker.readonly_locals.contains(*root))
                .or_else(|| {
                    if tracker.body_kind != super::super::BodyKind::Init {
                        statements::place_root_statefield(arg)
                            .filter(|root| !tracker.mut_state_fields.contains(*root))
                    } else {
                        None
                    }
                });
            if !param_is_frozen
                && statements::is_aliasable_type(&arg.ty)
                && let Some(root) = frozen_root
            {
                diagnostics.push(Diagnostic::error(
                    codes::T253,
                    format!(
                        "cannot pass frozen value `{root}` to a mutable parameter of \
                         `{callee_name}`: the call would mutate immutable state or re-widen \
                         authority. Mark that parameter `@ReadOnly`, or pass a copy."
                    ),
                    Some(arg.span),
                ));
            }
            // AGG2b-4 (HOLE-DANGLE, free/cross-module twin): a `mut Vec<scalar>` state
            // field is NOT frozen, so the gate above lets it reach a `@Mut` param (the
            // AGG-2a in-place path). But a `Vec` GROWS: the callee's `xs.push` roots at
            // its OWN param, not a StateField, so the AGG2b-2 `$state` routing can't
            // see it — the grow reallocs the buffer into the transient arena, reclaimed
            // by the AL-2 reset → a dangling read. We cannot prove the callee never
            // grows it (interprocedural), so fail-closed: reject passing a `mut` state
            // `Vec<scalar>` to a `@Mut` param. Scoped to `Vec<scalar>` (the grow-able
            // shape) so a `@Mut` flat-aggregate param (in-place mutation, sound) stays
            // allowed; handler-only (`init` constructs state in place).
            if !param_is_frozen
                && tracker.body_kind != super::super::BodyKind::Init
                && (universe::is_persistable_scalar_vec(&arg.ty, universe)
                    // PPS-0: a `mut Map<scalar, scalar>` state field grows the same way
                    // (buckets, keys, vals), so handing it to a `@Mut` param is the same
                    // fail-closed dangle.
                    || universe::is_persistable_scalar_map(&arg.ty, universe))
                && let Some(root) = statements::place_root_statefield(arg)
                    .filter(|root| tracker.mut_state_fields.contains(*root))
            {
                let shape = if universe::is_persistable_scalar_map(&arg.ty, universe) {
                    "Map"
                } else {
                    "Vec"
                };
                diagnostics.push(Diagnostic::error(
                    codes::T253,
                    format!(
                        "cannot pass the `mut` state {shape} `{root}` to a mutable (`@Mut`) \
                         parameter of `{callee_name}`: the callee could grow it, and a grow \
                         through a non-state binding reallocs into transient memory reclaimed \
                         after the dispatch (a dangling read). Grow the field directly in the \
                         handler, or pass a copy."
                    ),
                    Some(arg.span),
                ));
            }
        }
        // Exclusivity (DEF-2c PR-1, NC-2c-1/2): the call-site frozen×mutable alias gate — the
        // AG-1 closure. If this call hands the SAME heap object to a FROZEN parameter and a
        // MUTABLE one (`f(p, p)`, or `let y = x; f(x, y)` resolved through `alias_origin`), the
        // mutable handle could mutate it under the frozen view, breaking the read-only promise
        // — `T255`. Frozen-ness is the PARAMETER's; un-rooted / scalar args are inert
        // (NC-2c-6). Without a frozen+mutable aliasing pair the partition is empty → no new
        // diagnostic → byte-identical for the corpus (NC-2c-7).
        for (root, span) in statements::exclusivity_partition(
            &typed_args,
            &sig.param_mutability,
            &tracker.alias_origin,
        ) {
            diagnostics.push(Diagnostic::error(
                codes::T255,
                format!(
                    "cannot pass `{root}` as both a frozen (`@ReadOnly`) and a mutable argument \
                     to `{callee_name}`: mutating it through the mutable handle would break the \
                     read-only view of the same object. Pass a copy to one of them."
                ),
                Some(span),
            ));
        }
    }

    match resolution {
        Some(CrossModuleResolution::Private { module, name }) => {
            diagnostics.push(Diagnostic::error(
                codes::T155,
                format!(
                    "cross-module call to private function `{module}::{name}`; only `pub fn` items are callable from another module"
                ),
                Some(expr.span),
            ));
            return TypedExpr {
                ty: Type::Error,
                kind: TypedExprKind::Call(TypedCallExpr {
                    callee: callee_name,
                    args: typed_args,
                }),
                span: expr.span,

                refinement: None,
            };
        }
        Some(CrossModuleResolution::CrossRing {
            module,
            name,
            callee_ring,
        }) => {
            let callee_ring_str = match callee_ring {
                crate::ast::Ring::Inner => "inner",
                crate::ast::Ring::Outer => "outer",
            };
            let caller_ring_str = match tracker.current_module_ring {
                crate::ast::Ring::Inner => "inner",
                crate::ast::Ring::Outer => "outer",
            };
            // The fix depends on the direction. An inner-ring caller can escalate itself to
            // reach FFI-backed code. An outer-ring caller is already in the outer ring, and
            // adding `#[trusted]` does not change its ring, so that advice is no fix: it can only
            // leave the outer ring or stay in it. Leaving means dropping `#[trusted]` too when
            // present, since `#[trusted]` without `#[ring(outer)]` does not parse. The
            // inner-ring text is unchanged, byte for byte.
            let fix = match tracker.current_module_ring {
                crate::ast::Ring::Inner => {
                    "Add `#[ring(outer)] #[trusted]` to the calling module to use FFI-backed stdlib, or call only stdlib modules in the same ring."
                }
                crate::ast::Ring::Outer => {
                    "Outer-ring code cannot call into the inner ring. If the calling module does not need FFI, remove its `#[ring(outer)]` attribute, and `#[trusted]` if present, so it runs in the inner ring; otherwise call only outer-ring modules from it."
                }
            };
            diagnostics.push(Diagnostic::error(
                codes::R004,
                format!(
                    "cross-ring call: `{module}::{name}` lives in {callee_ring_str} ring, but the caller is in {caller_ring_str} ring. {fix}"
                ),
                Some(expr.span),
            ));
            return TypedExpr {
                ty: Type::Error,
                kind: TypedExprKind::Call(TypedCallExpr {
                    callee: callee_name,
                    args: typed_args,
                }),
                span: expr.span,

                refinement: None,
            };
        }
        Some(CrossModuleResolution::Ambiguous { name, candidates }) => {
            diagnostics.push(Diagnostic::error(
                codes::N008,
                format!(
                    "ambiguous reference `{name}`: matches `pub fn` in {} `use`'d modules: [{}]. Disambiguate by qualifying as `<module>::{name}(...)`",
                    candidates.len(),
                    candidates.join(", ")
                ),
                Some(expr.span),
            ));
            return TypedExpr {
                ty: Type::Error,
                kind: TypedExprKind::Call(TypedCallExpr {
                    callee: callee_name,
                    args: typed_args,
                }),
                span: expr.span,

                refinement: None,
            };
        }
        Some(CrossModuleResolution::Found(_)) | None => {}
    }

    let sig = match resolution.and_then(|resolution| match resolution {
        CrossModuleResolution::Found(sig) => Some(sig),
        _ => None,
    }) {
        Some(sig) => sig,
        None => {
            return infer_unresolved_call_expr(
                expr,
                env,
                context,
                tracker,
                diagnostics,
                callee_name,
                typed_args,
            );
        }
    };

    finish_resolved_call_expr(expr, sig, universe, diagnostics, callee_name, typed_args)
}

fn infer_unresolved_call_expr(
    expr: &CallExpr,
    env: &HashMap<String, Type>,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
    callee_name: String,
    mut typed_args: Vec<TypedExpr>,
) -> TypedExpr {
    let (function_sigs, _actor_sigs, module_name, universe) = context.parts();
    // Fallback 1: check generic function registry for monomorphization
    if let Some((definer_module, generic_def)) = universe.generic_fns.get(&callee_name).cloned() {
        // PR-1: the inference layer is name-only; bounds live on the AST.
        // Phase 4 (row polymorphism): every POSITIONAL consumer below zips
        // binders against TYPE-kinded concrete args, so the effect-kinded
        // ("row variable") binders are split out first — zipping the full
        // list would misalign turbofish, T150 accounting, `check_bounds`,
        // and the subst. Row variables are bound separately, from the actual
        // arguments' effect rows (`bind_and_check_effect_rows` below).
        let row_params: Vec<String> = crate::ast::effect_row_param_names(&generic_def);
        let type_param_names: Vec<String> = crate::ast::type_kinded_param_names(&generic_def);
        let type_params = &type_param_names;
        // PR-HK1: the higher-kinded subset of the binders, so a formal `F<A>`
        // resolves to `HktApp` (and unifies a constructor) instead of a bare
        // `Generic("F")` that would drop the `<A>`.
        let hkt = crate::ast::hkt_params(&generic_def.type_params);

        // v1 (Phase 4): no row turbofish, and no positional remap once a row
        // variable exists — `h::<i64>` on `fn h<e, T>` would silently feed
        // `i64` to the wrong binder. Fail closed and fall through to
        // inference (the E011 makes the compile fail regardless).
        let turbofish_blocked = !row_params.is_empty() && !expr.callee.type_args.is_empty();
        if turbofish_blocked {
            diagnostics.push(Diagnostic::error(
                codes::E011,
                format!(
                    "turbofish cannot be used on `{callee_name}` — it has an effect-row \
                     variable; row bindings are inferred from the arguments (v1 restriction)"
                ),
                Some(expr.span),
            ));
        }

        // Resolve type args: turbofish or inference
        let concrete_args: Vec<Type> = if !turbofish_blocked && !expr.callee.type_args.is_empty() {
            turbofish_type_args(&expr.callee, type_params, &hkt, universe)
        } else {
            // Infer via unification
            let formal_types: Vec<Type> = generic_def
                .params
                .iter()
                .map(|p| {
                    resolve_type_expr_kinded(&p.ty, universe, &HashMap::new(), type_params, &hkt)
                })
                .collect();
            let mut bindings = HashMap::new();
            for (formal, actual) in formal_types.iter().zip(typed_args.iter()) {
                unify(formal, &actual.ty, &mut bindings);
            }
            // Return-type-directed inference (fill-unbound-only). If the
            // arguments left any type param unbound, fall back to the
            // expected type (the let-annotation context) by unifying the
            // formal return type against it. `unify` uses `or_insert_with`,
            // so this only FILLS the gaps the arguments left — it never
            // overwrites an arg-derived binding. A genuine arg-vs-annotation
            // conflict (`let b: Box<i64> = f(true)`) leaves every param
            // arg-bound, so this is skipped and the mismatch surfaces at the
            // normal value/annotation compatibility check downstream.
            if type_params.iter().any(|p| !bindings.contains_key(p))
                && let Some(expected) = tracker.current_expected_type.clone()
                && !matches!(expected, Type::Error)
                && let Some(ret_ty) = generic_def.return_type.as_ref()
            {
                let formal_ret =
                    resolve_type_expr_kinded(ret_ty, universe, &HashMap::new(), type_params, &hkt);
                unify(&formal_ret, &expected, &mut bindings);
            }
            type_params
                .iter()
                .map(|p| {
                    bindings.get(p).cloned().unwrap_or_else(|| {
                        diagnostics.push(Diagnostic::error(
                            codes::T150,
                            format!("could not infer type parameter `{p}` — use turbofish"),
                            Some(expr.span),
                        ));
                        Type::Error
                    })
                })
                .collect()
        };

        if !tracker.check_type_work(&concrete_args, expr.span, diagnostics) {
            return super::work_limit_expr(expr.span);
        }

        // PR-3b (CM-T5): enforce trait bounds at the instantiation site,
        // concrete type-args in hand, BEFORE the body is monomorphized — a
        // clean T245/T248 at the call span rather than a deep failure inside
        // the substituted body (CM-T1 / T4). Under eager mono `concrete_args`
        // is fully concrete here.
        // Phase 4: `check_bounds` zips binders positionally against
        // `concrete_args` (type-kinded only), so effect-kinded binders must be
        // filtered out of the slice too — zipping the full list would pair
        // bounds with the wrong args and silently drop trailing bounds.
        let type_kinded_params: Vec<crate::ast::TypeParam> = generic_def
            .type_params
            .iter()
            .filter(|tp| !row_params.contains(&tp.name))
            .cloned()
            .collect();
        traits::check_bounds(
            &type_kinded_params,
            &concrete_args,
            expr.span,
            universe,
            function_sigs,
            module_name,
            tracker,
            diagnostics,
        );

        // Build subst + mangle
        let subst: HashMap<String, Type> = type_params
            .iter()
            .zip(concrete_args.iter())
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        // Narrow every argument to the now-known concrete (substituted)
        // parameter type, and report one that does not fit it
        // (`narrow_generic_arguments`). A generic signature is NOT in
        // `function_sigs`, so the arg loop above pinned an argument only as far
        // as a turbofish or the arguments before it had bound its type
        // parameters (CF-I1): an `IntLit` at a `T` position stayed `IntLit` and
        // would default to i64 by the end-of-typecheck mop-up. When this
        // instance binds T=i32/u32, that default mismatches the i32/u32
        // parameter, and AIR emits an `i64.const` into an i32 call slot — an
        // INVALID wasm module that only fails at instantiation.
        narrow_generic_arguments(
            &generic_def,
            type_params,
            &hkt,
            &subst,
            &callee_name,
            &mut typed_args,
            universe,
            diagnostics,
        );

        // Phase 4 (row polymorphism): bind each row variable from the actual
        // arguments' effect rows (union across occurrences = least solution;
        // an unconstrained variable stays the empty row), then enforce the
        // row-acceptance check this path never had: every Fn-typed formal's
        // row — concrete or variable — must bound its actual's row.
        let row_bindings = bind_and_check_effect_rows(
            &generic_def,
            &row_params,
            &typed_args,
            universe,
            expr.span,
            diagnostics,
        );

        // TS3: state markers are ERASED, so they are dropped from the mono key —
        // a state-polymorphic fn (`fn fd<@S>(f: File<S>)`) collapses to ONE
        // instance regardless of the state (its body is state-agnostic and the
        // state erases before AIR). This is the state-blind-mangle discipline
        // applied to the generic-fn key; it also keeps a bare `StateMarker` out
        // of `mangle_type` (whose StateMarker arm is a fail-closed ICE backstop).
        let mangled_args: Vec<String> = concrete_args
            .iter()
            .filter(|a| !matches!(a, Type::StateMarker(_)))
            .map(mangle_type)
            .collect();
        // Phase 4: one `$!`-prefixed component per row variable in declaration
        // order, `$`-joined NAME-sorted effect names. `$!` is outside
        // `mangle_type`'s output alphabet (`[A-Za-z0-9_$]` with `$` only as a
        // joiner), so the key stays injective; zero row variables emit NO
        // component, keeping every existing mono key byte-identical. Without
        // this, two instantiations at different rows would fuse under
        // cache-before-check and the second caller would silently inherit the
        // first caller's row — the row-fusing launder.
        let row_component: String = row_params
            .iter()
            .map(|p| {
                let mut names: Vec<&str> = row_bindings[p]
                    .effects
                    .iter()
                    .filter_map(|id| universe.effect_registry.name_of(*id))
                    .collect();
                names.sort_unstable();
                format!("$!{}", names.join("$"))
            })
            .collect();
        let mangled = if mangled_args.is_empty() && row_component.is_empty() {
            callee_name.to_string()
        } else {
            // R2: `$`-join (not `_`) so distinct multi-arg instantiations can't
            // fuse — `g<Foo_Bar, X>` and `g<Foo, Bar_X>` produced the same
            // `_`-joined key and silently dropped the second body.
            format!(
                "{}__{}{}",
                callee_name,
                mangled_args.join("$"),
                row_component
            )
        };
        let qualified = format!("{}::{}", module_name, mangled);

        // Cache-before-check: prevents recursive deadlock
        if tracker.reserve_specialization(&qualified, expr.span, diagnostics) {
            // The body is checked once: inside a speculation its report is kept until a
            // real inference uses the instance (`begin_speculation`).
            let attempt = tracker.begin_creation(&qualified);
            let mut own = Vec::new();
            let diagnostics: &mut Vec<Diagnostic> = if attempt.is_some() {
                &mut own
            } else {
                &mut *diagnostics
            };
            // Phase 4: rows written in the return type are instantiated via
            // the AST/Type overlay — the type-subst map is structurally
            // incapable of touching a row (rows are `Vec<String>` on the AST
            // and a resolved row has no variable arm), so skipping this would
            // type a returned closure with the EMPTY row and its application
            // would discharge nothing.
            let mono_ret = generic_def
                .return_type
                .as_ref()
                .map(|ty| {
                    overlay_rows(
                        ty,
                        resolve_type_expr(ty, universe, &subst, &[]),
                        &row_bindings,
                    )
                })
                .unwrap_or(Type::Unit);

            // Note: recursive generic calls resolve via tracker.cache
            // Sig insertion deferred — would need &mut function_sigs

            if tracker.depth >= MAX_MONOMORPH_DEPTH {
                diagnostics.push(Diagnostic::error(
                    codes::T151,
                    format!(
                        "monomorphization depth exceeded ({MAX_MONOMORPH_DEPTH}): `{callee_name}`"
                    ),
                    Some(expr.span),
                ));
            } else {
                tracker.depth += 1;
                let params: Vec<TypedParam> = generic_def
                    .params
                    .iter()
                    .map(|p| TypedParam {
                        flow: false,
                        mutability: crate::ast::Mutability::Default,
                        name: p.name.clone(),
                        // Phase 4: overlay bound row variables into the
                        // parameter's `Type::Fn` rows, so the body's
                        // `IndirectCall` discharge sees the instance's
                        // concrete row.
                        ty: overlay_rows(
                            &p.ty,
                            resolve_type_expr(&p.ty, universe, &subst, &[]),
                            &row_bindings,
                        ),
                        taint: crate::ast::TaintLabel::Public,
                    })
                    .collect();
                // Wall 4 Step 7 / MC-S7-C: generic functions
                // reject refinement at parse-time per N12-S7; the
                // monomorphized body sees no refinements. Defensive
                // empty-slot fill.
                let mono_param_refinements: Vec<Option<Vec<crate::ast::RefinementClause>>> =
                    vec![None; params.len()];
                // Phase 4: the instance's declared row = the written concrete
                // names ∪ each row variable's binding. Computed BEFORE the
                // body check so `current_effects` can carry it.
                let mono_row =
                    resolve_effect_row_with_vars(&generic_def.effects, universe, &row_bindings);
                // Scoped save/restore of `current_effects` for ROW-POLY monos
                // only (byte-identity for everything else): it is assigned
                // once, for non-generic top-level fns, with no save/restore —
                // so without this a closure inside this body would take the
                // CALLER's row as its inference fallback and placeholder.
                let saved_effects = if row_params.is_empty() {
                    None
                } else {
                    Some(std::mem::replace(
                        &mut tracker.current_effects,
                        mono_row.clone(),
                    ))
                };
                // BUG-5b: a free-fn instance body is re-checked in the CALLING
                // module's context (`context` below — its sigs, and the checked
                // module's `use` scope and ring), so its callee names resolve in
                // the caller's scope, not the definer's. The instance is governed
                // by the MEET of the definer and those scopes (round 3 — the
                // definer alone let a trusted generic's `handle Unsafe` discharge
                // a caller's untrusted helper, and an inner-ring generic's
                // exemption hide a caller's FFI chain). Round 2: anything
                // lambda-lifted out of this body is named `{caller}::__closure_N`
                // and needs the same home, so publish it for the lift site;
                // restored after the body so a nested instance of another
                // module's generic cannot leak this home outward.
                let home = tracker.instance_home(&definer_module, module_name);
                let saved_instance_home = tracker.current_instance_home.replace(home.clone());
                let body = check_function_block(
                    &params,
                    &mono_ret,
                    &HashMap::new(),
                    &generic_def.body,
                    context,
                    tracker,
                    diagnostics,
                    &mono_param_refinements,
                    None, // MC-S7-C: generics don't admit return refinement
                    // PR-2b: generic-monomorph re-entry seeds `@ReadOnly` from the
                    // generic def's params (mono preserves param count + order), so
                    // the WRITE/escape gates enforce inside generic bodies too. Inert
                    // for today's corpus (no generic fn carries `@ReadOnly` yet).
                    &generic_def
                        .params
                        .iter()
                        .map(|p| p.mutability)
                        .collect::<Vec<_>>(),
                    // DEF-2b PR-4: mono re-entry seeds region params from the generic
                    // def (mono preserves param count + order; regions aren't
                    // substituted). Inert for today's corpus (no generic fn is
                    // region-poly yet) → byte-identical.
                    &universe::param_regions_of(&generic_def.params),
                    // DEF-2b PR-5: the generic def's `where region` outlives pairs.
                    &universe::param_region_outlives_of(
                        &generic_def.params,
                        &generic_def.region_outlives,
                    ),
                    // A monomorphized generic function has no actor state in scope.
                    &HashMap::new(),
                    &std::collections::HashSet::new(),
                    super::super::BodyKind::Free,
                );
                tracker.current_instance_home = saved_instance_home;
                if let Some(prev) = saved_effects {
                    tracker.current_effects = prev;
                }
                // BUG-5b: `qualified` is prefixed with the CALLING module (a
                // `use`-imported generic instantiates under the caller's name),
                // so the home is recorded beside the instance for the effect and
                // ring walks — keying on the name prefix (or on the filing
                // module) would check an untrusted module's body under a trusted
                // caller's authority (E002 launder).
                tracker.instance_homes.insert(qualified.clone(), home);
                tracker.functions.push(TypedFunction {
                    ret_flow: false,
                    name: qualified.clone(),
                    export_name: mangled.clone(),
                    kind: TypedFunctionKind::ModuleFunction,
                    externally_callable: matches!(
                        generic_def.visibility,
                        crate::ast::Visibility::Public
                    ),
                    params,
                    captures: Vec::new(),
                    ret: mono_ret.clone(),
                    ret_taint: crate::ast::TaintLabel::Public,
                    // PR-0: propagate the generic fn's DECLARED effect row
                    // to the monomorphized instance (see the impl-method
                    // site for the full rationale). Phase 4: with any row
                    // variable's binding unioned in — `check_effects` walks
                    // this body against exactly this row, and the row-keyed
                    // mono name means each instance carries its own.
                    effects: mono_row,
                    body,
                    span: generic_def.span,
                });
                tracker.depth -= 1;
            }
            tracker.end_creation(attempt, &qualified, own);
        }

        // Phase 4: the CALLER-visible return type gets the same row overlay as
        // `mono_ret` — this is the value whose latent row the caller's
        // `IndirectCall` will discharge if the instance returns a closure.
        let ret = generic_def
            .return_type
            .as_ref()
            .map(|ty| {
                overlay_rows(
                    ty,
                    resolve_type_expr(ty, universe, &subst, &[]),
                    &row_bindings,
                )
            })
            .unwrap_or(Type::Unit);

        return TypedExpr {
            ty: ret,
            kind: TypedExprKind::Call(TypedCallExpr {
                callee: qualified,
                args: typed_args,
            }),
            span: expr.span,

            refinement: None,
        };
    }

    // Fallback 2: check if callee is an enum variant constructor.
    //
    // PR B / N22-PRB: bare-variant calls (e.g., `Some(42)`) and
    // qualified-variant calls (`Option::Some(42)`) both route
    // through here. Bare calls scan every enum in
    // `universe.enums` for a variant with the matching name; if
    // multiple enums share the variant name AND no annotation
    // context is in scope, T236 fires.
    //
    // Per N22-PRB the ambiguity check uses BTreeSet for
    // deterministic candidate ordering — stdlib enums do NOT
    // receive precedence.
    //
    // Per N5-PRB the annotation-context disambiguator reads
    // `tracker.current_expected_type` (PR A's expected-type
    // threading; ExpectedTypeGuard manages push/pop at let-
    // binding sites). If the expected type is
    // `Type::Named(enum_name, _)` and that enum has the matching
    // variant, pick it directly without firing T236.
    //
    // Per N14-PRB qualified construction and bare construction
    // produce identical TypedExpr shapes — both route through
    // the SAME `infer_variant_type_args`-equivalent code below.
    {
        let variant_segment = expr.callee.segments.last().cloned().unwrap_or_default();
        // Steps 1 and 2 (candidate enums, then disambiguation) live in
        // `classify_variant_callee`, shared with `infer_call_expr`'s payload-slot
        // pin so the two make the same decision.
        let chosen_enum_name: Option<String> = match classify_variant_callee(
            &expr.callee,
            universe,
            tracker,
        ) {
            VariantCallee::Chosen(enum_name) => Some(enum_name),
            VariantCallee::NotAVariant => None,
            VariantCallee::NoSuchVariant(qual) => {
                // Enum exists but variant doesn't — fire T072 and
                // bail. This is more specific than the bare-variant
                // "not found" path which falls through to T062.
                diagnostics.push(Diagnostic::error(
                    codes::T072,
                    format!("enum `{qual}` has no variant `{variant_segment}`"),
                    Some(expr.span),
                ));
                return TypedExpr {
                    ty: Type::Error,
                    kind: TypedExprKind::Call(TypedCallExpr {
                        callee: callee_name,
                        args: typed_args,
                    }),
                    span: expr.span,
                    refinement: None,
                };
            }
            VariantCallee::Ambiguous(candidate_enums) => {
                // N22-PRB: T236 ambiguous bare variant.
                let listed = candidate_enums
                    .iter()
                    .map(|n| format!("`{n}`"))
                    .collect::<Vec<_>>()
                    .join(", ");
                diagnostics.push(Diagnostic::error(
                            codes::T236,
                            format!(
                                "ambiguous bare variant `{variant_segment}` — found in enums [{listed}]; add a type annotation (`let x: EnumName<...> = {variant_segment}(...)`) or qualify the constructor (`EnumName::{variant_segment}(...)`)"
                            ),
                            Some(expr.span),
                        ));
                return TypedExpr {
                    ty: Type::Error,
                    kind: TypedExprKind::Call(TypedCallExpr {
                        callee: callee_name,
                        args: typed_args,
                    }),
                    span: expr.span,
                    refinement: None,
                };
            }
        };

        // Step 3: if we chose an enum, perform the construction.
        if let Some(enum_name) = chosen_enum_name {
            // Re-borrow universe.enums to get the chosen entry's
            // payload information. Clone the small bits we need so
            // we don't borrow universe across the construction.
            let (type_params, idx, payload_types) = {
                let (type_params, variants) = universe.enums.get(&enum_name).expect(
                    "chosen_enum_name MUST be in universe.enums (we just sourced it from there)",
                );
                let (idx, (_, payload_types)) = variants
                        .iter()
                        .enumerate()
                        .find(|(_, (name, _))| name == &variant_segment)
                        .expect(
                            "variant_segment MUST be a variant of chosen_enum_name (we just sourced it from there)",
                        );
                (type_params.clone(), idx, payload_types.clone())
            };

            if typed_args.len() != payload_types.len() {
                diagnostics.push(Diagnostic::error(
                    codes::T072,
                    format!(
                        "enum variant `{variant_segment}` expects {} field(s), found {}",
                        payload_types.len(),
                        typed_args.len()
                    ),
                    Some(expr.span),
                ));
            }

            // Soundness: the arity check above is the ONLY gate on the payload —
            // there was no per-position TYPE check, so `E::V(true)` for
            // `enum E { V(i64) }` (or any `bool`/`str`/wide value into a
            // concretely-typed payload slot) landed silently with no diagnostic,
            // exactly the record-construction hole. Check each declared payload
            // type against its supplied value, mirroring the function-argument and
            // record-construction paths. A `Generic` payload position (`Some(x)` →
            // `T`) is resolved by the `unify` pass just below, so it is skipped
            // here (feeding it to `type_compatible` would ICE); a concrete payload
            // position of a generic enum (`enum Both<T> { B(T, i64) }`) IS checked.
            // `IntLit` (the IntLit→machine-int flex) and `Error` (cascade) are
            // excluded.
            for (formal, arg) in payload_types.iter().zip(typed_args.iter()) {
                if !type_mentions_generic(formal)
                    && !type_mentions_generic(&arg.ty)
                    && !matches!(arg.ty, Type::IntLit(_) | Type::Error)
                    && !type_compatible(formal, &arg.ty)
                {
                    diagnostics.push(Diagnostic::error(
                        codes::T071,
                        format!(
                            "enum variant `{variant_segment}` payload expected `{}`, found `{}`",
                            render_type(formal),
                            render_type(&arg.ty)
                        ),
                        Some(arg.span),
                    ));
                }
            }
            // CF-I3 for payloads: an integer literal that its concrete declared slot
            // cannot hold (`S::V(5000000000)` for `V(i32)`, or any integer literal
            // for `V(f64)`) is not narrowed by the pin in `infer_call_expr`, so it
            // stays `IntLit` — skipped by the check above — and the end-of-typecheck
            // mop-up would default it to `i64`: 8 bytes stored into a narrower slot,
            // past the end of the cell when that variant is the widest. Reject it,
            // as the record-field path does. A type-parameter position is not
            // checked here: it is pinned to the expected type's instance, and a
            // literal that does not fit leaves the whole value incompatible with
            // that slot, which the slot's own check reports.
            for (formal, arg) in payload_types.iter().zip(typed_args.iter()) {
                if let Type::IntLit(n) = arg.ty
                    && type_is_concrete(formal)
                {
                    diagnostics.push(Diagnostic::error(
                        codes::T071,
                        format!(
                            "enum variant `{variant_segment}` payload expected `{}`, found the \
                             integer literal `{n}`, which does not fit it",
                            render_type(formal)
                        ),
                        Some(arg.span),
                    ));
                }
            }

            // Refinement quarantine (Phase 2): variant refinement discharge now
            // runs in the v2 obligation pass, not inline here.

            // Generic enum: unify payload types to discover type args.
            let (concrete_ty, mangled_name) = if type_params.is_empty() {
                (Type::Named(enum_name.clone(), vec![]), enum_name.clone())
            } else {
                let mut bindings = HashMap::new();
                for (formal, actual) in payload_types.iter().zip(typed_args.iter()) {
                    unify(formal, &actual.ty, &mut bindings);
                }
                // A type parameter no payload binds (`B` in `Either::L(7)`) takes the
                // expected instance's argument, as a unit variant's parameters do (GAP 2).
                // Left unbound it became `Type::Error`, which lowers to zero width, so
                // under `let e: Either<i32, i64>` the construct registered and allocated
                // `Either<i32, error>` (8 bytes) rather than the 12-byte instance its
                // readers use. A parameter a payload did bind keeps that binding, so a
                // payload of the wrong type still mismatches the slot.
                if let Some(instance) = expected_enum_instance(&enum_name, &type_params, tracker) {
                    for (param, arg) in instance {
                        bindings.entry(param).or_insert(arg);
                    }
                }
                let concrete_args: Vec<Type> = type_params
                    .iter()
                    .map(|p| bindings.get(p).cloned().unwrap_or(Type::Error))
                    .collect();
                // SR-032: a payload whose declared type mentions a type parameter is
                // pinned while it is inferred only when the expected type names the
                // instance (`variant_payload_slots`). Otherwise it was typed by its own
                // value, so `let b = B::V((1, 40));` for `enum B<T> { V((i32, T)) }`
                // laid the tuple out as `(i64, i64)` while a `match` read it as
                // `(i32, i64)`, and a closure taking a `(i64, i64)` was stored in a
                // `Fn((i32, i64)) -> T` payload unchecked. Each such payload is fitted
                // to the instance now (`fit_to_instance_slot`), and one stored
                // otherwise is T071, as a concrete payload's mismatch is above.
                let instance: HashMap<String, Type> = type_params
                    .iter()
                    .cloned()
                    .zip(concrete_args.iter().cloned())
                    .collect();
                for (formal, arg) in payload_types.iter().zip(typed_args.iter_mut()) {
                    if !type_mentions_generic(formal) {
                        continue;
                    }
                    let slot = apply_subst(formal, &instance);
                    if !fit_to_instance_slot(arg, &slot, codes::T071, diagnostics) {
                        let mut concrete = slot;
                        default_int_lit_in_type(&mut concrete);
                        diagnostics.push(Diagnostic::error(
                            codes::T071,
                            format!(
                                "enum variant `{variant_segment}` payload expected `{}`, found `{}`",
                                render_type(&concrete),
                                render_type(&arg.ty)
                            ),
                            Some(arg.span),
                        ));
                        arg.ty = Type::Error;
                    }
                }
                let cty = Type::Named(enum_name.clone(), concrete_args.clone());

                // T242: cap-smuggle defense at generic-enum
                // instantiation. T184 fires at enum DECLARATION
                // time on cap-typed payloads; for generic enums
                // (Option<T>, Result<T, E>, user-defined
                // `enum Box<T> { Wrap(T) }`) the payload type at
                // declaration is `Type::Generic(_)` — no cap visible.
                // The substitution above rewrites concrete_args to
                // a concrete cap type; without this check, the
                // match-arm destructure binding loses the cap's
                // restriction provenance, the same Z3 authority-
                // tracker gap T184 closes for concrete payloads.
                //
                // Skip if any concrete_arg is Type::Error to
                // prevent cascade noise from unresolved bindings.
                if !concrete_args.iter().any(|t| matches!(t, Type::Error))
                    && !typed_args.iter().any(|a| matches!(a.ty, Type::Error))
                {
                    check_generic_aggregate_cap_smuggle(
                        &enum_name,
                        &concrete_args,
                        "enum",
                        expr.span,
                        universe,
                        diagnostics,
                    );
                }

                if !tracker.check_type_work([&cty], expr.span, diagnostics) {
                    return super::work_limit_expr(expr.span);
                }
                let mangled = mangle_type(&cty);
                // Re-borrow to get the variants slice for registration.
                let variants_ref = universe
                    .enums
                    .get(&enum_name)
                    .map(|(_, v)| v.clone())
                    .expect("chosen_enum_name MUST be in universe.enums");
                register_concrete_enum(
                    tracker,
                    &mangled,
                    &variants_ref,
                    &type_params,
                    &concrete_args,
                    expr.span,
                    diagnostics,
                );
                (cty, mangled)
            };

            return TypedExpr {
                ty: concrete_ty,
                kind: TypedExprKind::EnumConstruct(TypedEnumConstructExpr {
                    enum_name: mangled_name,
                    variant_index: idx as u32,
                    fields: typed_args,
                }),
                span: expr.span,
                refinement: None,
            };
        }
    }

    // HOF: closure-typed local variable callee. Before T062
    // ("undefined function") fires, check if the callee path
    // is a single segment that resolves in `env` to a
    // `Type::Fn(...)` — e.g., a function parameter declared
    // as `f: Fn(i64) -> i64` or a let-binding to a closure
    // literal. Produces `TypedExprKind::IndirectCall` so AIR
    // emits `AirStmt::CallIndirect` against the closure heap.
    //
    // Per N8-HOF: callee_ty is statically Type::Fn (never
    // Type::Error). The if-let chain guarantees this. Per
    // N4-HOF: T237 fires below if the actual closure is
    // linear but the declared Fn type is non-linear.
    if expr.callee.segments.len() == 1
        && let Some(local_ty) = env.get(&callee_name).cloned()
        && let Type::Fn(fn_params, fn_ret, fn_is_linear, _) = &local_ty
    {
        // HOF / N4-HOF: T237 linearity check.
        // The Fn-typed local was DECLARED via either `Fn(T) -> U`
        // syntax (which always produces is_linear=false per N3-HOF)
        // OR via a closure-literal binding (which derives is_linear
        // from whether the captures contain `Cap<_>`).
        //
        // If the local's type is `Type::Fn(_, _, true)` — linear —
        // and we're invoking it through the general closure-call
        // dispatch path (i.e., NOT inside a grant block), reject
        // with T237. The linear closure must invoke through `grant`
        // for runtime single-use enforcement.
        if *fn_is_linear {
            diagnostics.push(Diagnostic::error(
                    codes::T237,
                    format!(
                        "linear closure-typed local `{callee_name}` (captures `Cap<_>`) cannot be invoked through general closure-call dispatch; use `grant cap, |args| {{ ... }}` instead"
                    ),
                    Some(expr.span),
                ));
            // Still continue with the dispatch so subsequent code
            // type-checks against the closure's return type; the
            // T237 diagnostic is the user-facing block on
            // proceeding to ship the program.
        }
        if typed_args.len() != fn_params.len() {
            diagnostics.push(Diagnostic::error(
                codes::T070,
                format!(
                    "closure-typed local `{callee_name}` expects {} argument(s), found {}",
                    fn_params.len(),
                    typed_args.len()
                ),
                Some(expr.span),
            ));
        }
        for (idx, expected) in fn_params.iter().enumerate() {
            let Some(arg) = typed_args.get_mut(idx) else {
                break;
            };
            // Narrow each argument to the closure's concrete parameter type. The
            // arg loop above pinned it already (`closure_param_slots`), so this
            // is the backstop for a parameter the loop did not see: an `IntLit`
            // left at an i32/u32 closure param would default to i64, and AIR
            // would emit an `i64.const` into a narrow `call_indirect` slot →
            // INVALID wasm. Mirrors the resolved-function-call and generic-call
            // narrowing. A non-fitting / incompatible literal stays `IntLit` and
            // is reported by the `type_compatible` check just below (overflow →
            // T071), exactly as before.
            if type_is_concrete(expected) && type_compatible(expected, &arg.ty) {
                resolve_int_literals_or_reject(arg, expected, codes::T071, diagnostics);
            }
            if !type_compatible(expected, &arg.ty) {
                diagnostics.push(Diagnostic::error(
                        codes::T071,
                        format!(
                            "closure-typed local `{callee_name}` argument #{}: expected `{}`, found `{}`",
                            idx + 1,
                            render_type(expected),
                            render_type(&arg.ty)
                        ),
                        Some(expr.span),
                    ));
            }
        }
        let ret_ty = (**fn_ret).clone();
        return TypedExpr {
            ty: ret_ty,
            kind: TypedExprKind::IndirectCall(TypedIndirectCallExpr {
                callee_local: callee_name,
                callee_ty: local_ty,
                args: typed_args,
                kind: TypedIndirectCallKind::Ordinary,
            }),
            span: expr.span,

            refinement: None,
        };
    }

    diagnostics.push(Diagnostic::error(
        codes::T062,
        format!("undefined function `{callee_name}`"),
        Some(expr.span),
    ));
    TypedExpr {
        ty: Type::Error,
        kind: TypedExprKind::Call(TypedCallExpr {
            callee: callee_name,
            args: typed_args,
        }),
        span: expr.span,

        refinement: None,
    }
}

/// The slots a call's arguments are written to, decided before any argument is
/// inferred (CF-I7: from the callee, the expected type and the bindings in scope,
/// never an argument).
enum ArgSlots {
    /// Each argument takes its slot's type: a resolved function's parameters, an
    /// enum variant's payloads, or a closure-typed local's parameters.
    Params(Vec<Type>),
    /// A generic function, or a generic enum's variant with no instance in view:
    /// each parameter's or payload's declared type with its type parameters free
    /// (`formals`), and the type arguments a turbofish names (`bound`). An
    /// argument is pinned to its formal once the turbofish or the
    /// arguments before it have bound every type parameter the formal mentions:
    /// the construct-slot rule of a resolved call, for the slots a generic call
    /// can already see. Before, no argument of a generic function was pinned, so
    /// `g(true, (1, 40))` for `t: (i32, i64)` laid the tuple out as `(i64, i64)`
    /// while the instance read it as `(i32, i64)`. Fallback 1 narrows the rest
    /// once the instance is known (`narrow_generic_arguments`).
    Generic {
        formals: Vec<Type>,
        bound: HashMap<String, Type>,
        /// Whether a slot that mentions a function type stays unpinned: true for
        /// a generic function, whose closure argument's effect row can bind a row
        /// variable (`type_mentions_fn`). False for a generic enum, which declares
        /// no row variable (E011), so its function-typed payload is pinned like
        /// any other. With the filter, `W::F((1, 40, f), 7)` for
        /// `F((i32, i64, Fn(i64) -> i64), T)` laid the tuple out as `(i64, i64, _)`,
        /// and no fit reached that payload, since its type mentions no type
        /// parameter.
        unpin_fn_slots: bool,
    },
    /// Nothing to pin: an intrinsic, an unknown callee, or a call Fallback 1 or 2
    /// rejects (a row-polymorphic turbofish, an ambiguous or missing variant).
    Unpinned,
}

/// The formals of a generic callee for `ArgSlots::Generic`, with the type
/// arguments its turbofish names, resolved as Fallback 1 resolves them. A
/// turbofish on a function with an effect-row variable is `Unpinned`: Fallback 1
/// rejects it (E011).
fn generic_formal_slots(
    generic_def: &crate::ast::FnDef,
    callee: &crate::ast::Path,
    universe: &TypeUniverse,
) -> ArgSlots {
    let type_params = crate::ast::type_kinded_param_names(generic_def);
    let hkt = crate::ast::hkt_params(&generic_def.type_params);
    let bound: HashMap<String, Type> = if callee.type_args.is_empty() {
        HashMap::new()
    } else if !crate::ast::effect_row_param_names(generic_def).is_empty() {
        return ArgSlots::Unpinned;
    } else {
        type_params
            .iter()
            .cloned()
            .zip(turbofish_type_args(callee, &type_params, &hkt, universe))
            .collect()
    };
    ArgSlots::Generic {
        formals: generic_def
            .params
            .iter()
            .map(|p| resolve_type_expr_kinded(&p.ty, universe, &HashMap::new(), &type_params, &hkt))
            .collect(),
        bound,
        unpin_fn_slots: true,
    }
}

/// A turbofish's type arguments, in order. A higher-kinded parameter
/// (`F: * -> *`) is supplied as a bare constructor NAME (`unwrap::<Box, i64>`):
/// the inference path binds it to `TypeCtor(Box)` via unify, and this mirrors
/// that so the body's `HktApp{F,[A]}` erases to `Named(Box,[A])`. Resolving it
/// normally would yield a malformed 0-arg `Named(Box, [])` (Box has arity 1)
/// that trips the use-site arity gate / path-substitution guard.
fn turbofish_type_args(
    callee: &crate::ast::Path,
    type_params: &[String],
    hkt: &[(String, usize)],
    universe: &TypeUniverse,
) -> Vec<Type> {
    callee
        .type_args
        .iter()
        .enumerate()
        .map(|(i, ta)| {
            if let Some(pname) = type_params.get(i)
                && hkt.iter().any(|(n, _)| n == pname)
            {
                Type::TypeCtor(ta.path.display_name())
            } else {
                resolve_type_expr(ta, universe, &HashMap::new(), &[])
            }
        })
        .collect()
}

/// The parameter types of the closure-typed local a call names, for
/// `ArgSlots::Params`. The closure path of `infer_unresolved_call_expr` reaches
/// exactly this callee once nothing resolved, no generic function has the name
/// and no enum declares it as a variant. Its arguments were inferred unpinned,
/// so `f((1, 40))` for `f: Fn((i32, i64)) -> i64` laid the tuple out as
/// `(i64, i64)`.
fn closure_param_slots(
    callee: &crate::ast::Path,
    callee_name: &str,
    env: &HashMap<String, Type>,
) -> ArgSlots {
    match env.get(callee_name) {
        Some(Type::Fn(params, ..)) if callee.segments.len() == 1 => {
            ArgSlots::Params(params.clone())
        }
        _ => ArgSlots::Unpinned,
    }
}

/// Whether `t` contains a function type anywhere. A generic function's
/// function-typed slot is left unpinned (`ArgSlots::Generic`'s `unpin_fn_slots`),
/// so that no expected type reaches an argument whose closure binds the
/// function's row variable (`bind_and_check_effect_rows`). This is a precaution:
/// closure inference reads no expected type today. Its cost is the parts beside
/// a function type, which are narrowed after inference instead, and an enum
/// construct there, which is built first and is T071 where the instance reads
/// it otherwise.
fn type_mentions_fn(t: &Type) -> bool {
    match t {
        Type::Fn(..) => true,
        Type::Named(_, args) | Type::Tuple(args) => args.iter().any(type_mentions_fn),
        Type::Array { elem, .. } => type_mentions_fn(elem),
        Type::Ref(inner, _) | Type::Slice(inner) | Type::Ptr(inner) | Type::MutPtr(inner) => {
            type_mentions_fn(inner)
        }
        _ => false,
    }
}

/// What a call's callee names among the enum variants: Steps 1 and 2 of Fallback 2.
enum VariantCallee {
    /// The variant's enum: the only enum declaring it, or the one the expected type
    /// names (N5-PRB).
    Chosen(String),
    /// `Q::V` where `Q` is an enum with no variant `V` (T072).
    NoSuchVariant(String),
    /// A bare variant several enums declare, none of them named by the expected type
    /// (T236). The candidates are in `BTreeSet` order (N22-PRB).
    Ambiguous(Vec<String>),
    /// Not a variant constructor: no enum declares the name, the qualifier is not an
    /// enum, or the path has three or more segments.
    NotAVariant,
}

/// Which enum a call's callee constructs. It reads only the callee path, the
/// universe and the expected type, never an argument (CF-I7), so `infer_call_expr`
/// makes the same decision before its argument loop (to pin each argument to its
/// payload slot) that Fallback 2 makes at construction.
fn classify_variant_callee(
    callee: &crate::ast::Path,
    universe: &TypeUniverse,
    tracker: &MonomorphTracker,
) -> VariantCallee {
    let declares = |variants: &[(String, Vec<Type>)], variant: &str| {
        variants.iter().any(|(name, _)| name == variant)
    };
    let candidate_enums: Vec<String> = match callee.segments.as_slice() {
        // Qualified path: only the named enum is a candidate.
        [qual, variant] => match universe.enums.get(qual) {
            Some((_, variants)) if declares(variants, variant) => vec![qual.clone()],
            Some(_) => return VariantCallee::NoSuchVariant(qual.clone()),
            // The qualifier is not an enum: the call falls through to T062.
            None => return VariantCallee::NotAVariant,
        },
        // Bare path: every enum declaring the variant, in BTreeSet order (N22-PRB).
        [variant] => universe
            .enums
            .iter()
            .filter(|(_, (_, variants))| declares(variants, variant))
            .map(|(name, _)| name.clone())
            .collect::<std::collections::BTreeSet<String>>()
            .into_iter()
            .collect(),
        // Three or more segments: not a variant call.
        _ => return VariantCallee::NotAVariant,
    };
    match candidate_enums.as_slice() {
        [] => VariantCallee::NotAVariant,
        [only] => VariantCallee::Chosen(only.clone()),
        // N5-PRB: the expected type picks among several candidates.
        _ => match &tracker.current_expected_type {
            Some(Type::Named(expected, _)) if candidate_enums.contains(expected) => {
                VariantCallee::Chosen(expected.clone())
            }
            _ => VariantCallee::Ambiguous(candidate_enums),
        },
    }
}

/// The slot each argument of a variant constructor is stored into: the variant's
/// declared payload types, with the enum's type parameters substituted from the
/// expected type when it names this enum with fully concrete arguments — the
/// instance a `let` annotation, a return type, a parameter or an enclosing slot
/// asks for, as GAP 1 does for a generic record (`let e: G<i32> = G::V(3)` pins
/// `3` to `i32`, so `unify` binds `T = i32` and the construct is the `G<i32>` the
/// readers expect).
///
/// A generic enum with no instance in view takes `ArgSlots::Generic`: a payload is
/// pinned once the payloads before it bind the type parameters its type mentions,
/// as a generic function's argument is, and a function-typed payload too, since an
/// enum binds no effect-row variable. Before, such a payload was never pinned,
/// so `E::V(x, Some(5))` for `V(T, Option<T>)` with `x: i32` built the `Some` at
/// `Option<i64>`; a payload bound later or only by a literal is fitted to the
/// instance after the construct's bindings are known (`fit_to_instance_slot`).
fn variant_payload_slots(
    enum_name: &str,
    callee: &crate::ast::Path,
    universe: &TypeUniverse,
    tracker: &MonomorphTracker,
) -> ArgSlots {
    let Some(variant) = callee.segments.last() else {
        return ArgSlots::Unpinned;
    };
    let Some((type_params, variants)) = universe.enums.get(enum_name) else {
        return ArgSlots::Unpinned;
    };
    let Some((_, payload_types)) = variants.iter().find(|(name, _)| name == variant) else {
        return ArgSlots::Unpinned;
    };
    match expected_enum_instance(enum_name, type_params, tracker) {
        Some(subst) => ArgSlots::Params(
            payload_types
                .iter()
                .map(|payload| apply_subst(payload, &subst))
                .collect(),
        ),
        None if !type_params.is_empty() => ArgSlots::Generic {
            formals: payload_types.clone(),
            bound: HashMap::new(),
            unpin_fn_slots: false,
        },
        None => ArgSlots::Params(payload_types.clone()),
    }
}

/// The instance of the generic enum `enum_name` that the expected type asks for, as a
/// substitution of its type parameters: present only when the expected type names this
/// enum with one argument per parameter and every argument is concrete (CF-I1), so a
/// type parameter of the enclosing function is never bound into a construct.
fn expected_enum_instance(
    enum_name: &str,
    type_params: &[String],
    tracker: &MonomorphTracker,
) -> Option<HashMap<String, Type>> {
    match &tracker.current_expected_type {
        Some(Type::Named(name, args))
            if !type_params.is_empty()
                && name == enum_name
                && args.len() == type_params.len()
                && args.iter().all(type_is_concrete) =>
        {
            Some(
                type_params
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect(),
            )
        }
        _ => None,
    }
}

/// The diagnostic for argument `idx` of `callee_name`, whose type does not fit
/// the parameter type `expected`: the protocol-aware T266 (typestate), T195 (a
/// capability deadline) or T227 (an array size) where one applies, else T071.
fn argument_mismatch_diagnostic(
    callee_name: &str,
    idx: usize,
    expected: &Type,
    arg: &TypedExpr,
    universe: &TypeUniverse,
) -> Diagnostic {
    let arg_label = format!("argument #{}", idx + 1);
    let site_ctx = format!("function `{callee_name}` argument #{}", idx + 1);
    if let Some(t266) =
        try_state_mismatch_diagnostic(expected, &arg.ty, universe, &site_ctx, arg.span)
    {
        // Typestate (T266): same protocol nominal, wrong state — the
        // protocol-aware form of the generic T071 below.
        t266
    } else if let Some(t195) =
        try_cap_deadline_diagnostic(expected, &arg.ty, &arg_label, &site_ctx, arg.span)
    {
        t195
    } else if let Some(t227) =
        try_array_size_mismatch_diagnostic(expected, &arg.ty, &site_ctx, arg.span)
    {
        t227
    } else {
        Diagnostic::error(
            codes::T071,
            format!(
                "function `{}` expected argument of type `{}`, found `{}`",
                callee_name,
                render_type(expected),
                render_type(&arg.ty)
            ),
            Some(arg.span),
        )
    }
}

/// Fallback 1, once the instance is known: fit each argument of a generic call
/// to its parameter type with the instance's type arguments substituted
/// (`fit_to_instance_slot`), and report one that does not fit.
///
/// The argument loop pins an argument only once a turbofish or the arguments
/// before it have bound the type parameters its formal mentions, and never one
/// whose formal mentions a function type (`type_mentions_fn`). An argument whose
/// parameter is bound later (`g((4, 7), a)` for `t: (i32, T), a: T`), only by a
/// literal (`g(0, (4, 7))`), inside the argument itself (`g((y, 5, 4))` for
/// `t: (T, T, i64)` with `y: i32`), or beside a closure (`g((c, (1, 40)), 0)` for
/// `p: (Fn(i64) -> i64, (i32, i64))`) was inferred with no slot, so its integer
/// literals kept the `i64` default while the instance read the parameter's
/// types. A generic call also had no argument check at all: `g(true, t)` for
/// `t: (i32, i64)`, given a `(i64, i64)`, compiled and read the wrong bytes, and
/// so did a closure taking a `(i64, i64)` for `Fn((i32, i64)) -> T`, at the top
/// level or inside a tuple or an `Option`. Each argument stored otherwise than
/// the instance reads it now gets the resolved call's diagnostic
/// (`argument_mismatch_diagnostic`) and is poisoned to `Type::Error`.
#[allow(clippy::too_many_arguments)]
fn narrow_generic_arguments(
    generic_def: &crate::ast::FnDef,
    type_params: &[String],
    hkt: &[(String, usize)],
    subst: &HashMap<String, Type>,
    callee_name: &str,
    typed_args: &mut [TypedExpr],
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for (i, param) in generic_def.params.iter().enumerate() {
        let Some(arg) = typed_args.get_mut(i) else {
            continue;
        };
        let formal =
            resolve_type_expr_kinded(&param.ty, universe, &HashMap::new(), type_params, hkt);
        let slot = apply_subst(&formal, subst);
        if !fit_to_instance_slot(arg, &slot, codes::T071, diagnostics) {
            let mut concrete = slot;
            default_int_lit_in_type(&mut concrete);
            diagnostics.push(argument_mismatch_diagnostic(
                callee_name,
                i,
                &concrete,
                arg,
                universe,
            ));
            arg.ty = Type::Error;
        }
    }
}

fn finish_resolved_call_expr(
    expr: &CallExpr,
    sig: &FunctionSig,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
    callee_name: String,
    typed_args: Vec<TypedExpr>,
) -> TypedExpr {
    if typed_args.len() != sig.params.len() {
        diagnostics.push(Diagnostic::error(
            codes::T070,
            format!(
                "function `{}` expects {} argument(s), found {}",
                callee_name,
                sig.params.len(),
                typed_args.len()
            ),
            Some(expr.span),
        ));
    }

    for (idx, (arg, expected)) in typed_args.iter().zip(sig.params.iter()).enumerate() {
        if !type_compatible(expected, &arg.ty) {
            diagnostics.push(argument_mismatch_diagnostic(
                &callee_name,
                idx,
                expected,
                arg,
                universe,
            ));
        }
    }

    // Wall 4 Step 7: discharge per-arg refinement obligations.
    // Refinement quarantine (Phase 2): call-arg refinement discharge (T224/T211)
    // now runs in the v2 obligation pass (check_with_warnings), not inline here.

    if matches!(sig.ret, Type::Unit) {
        diagnostics.push(Diagnostic::error(
            codes::T073,
            format!("function `{callee_name}` does not return a value"),
            Some(expr.span),
        ));
    }

    // An extern call is a call that RESOLVED to an extern declaration, so the test is on the
    // resolved signature. Matching the bare callee name against every extern in the program
    // turned a module's own `fn fs_read` into an FFI import whenever any module, even an
    // inner-ring one, declared an extern of that name: untrusted code reached the host with no
    // `#[trusted]` anywhere in the program. FAIL DIRECTION: a resolved local function is never
    // an FFI call; an extern still is.
    //
    // The call is named by the extern's DECLARED name, never by the callee's spelling, because
    // that name is the host import that every later pass binds. A module may call its own extern
    // as `u::fs_read` (or `sigil::u::fs_read`). As an import name that spelling is not an
    // identifier, so the formal gate refused the program with an internal-error code (I013),
    // although the bare spelling compiles. A qualified spelling reaches here only when it names
    // the module the call resolves in (`call_resolve.rs`): an extern is private, so a qualified
    // call into another module stops at T155 in `infer_call_expr`.
    let kind = if let Some(declared) = universe.extern_fns.get(&sig.qualified_name) {
        TypedExprKind::ExternCall(TypedExternCallExpr {
            extern_name: declared.clone(),
            args: typed_args,
        })
    } else {
        TypedExprKind::Call(TypedCallExpr {
            callee: sig.qualified_name.clone(),
            args: typed_args,
        })
    };
    TypedExpr {
        ty: if matches!(sig.ret, Type::Unit) {
            Type::Error
        } else {
            sig.ret.clone()
        },
        kind,
        span: expr.span,

        // Wall 4 Step 7 / N14-S7: attach the callee's declared return
        // refinement to the call's TypedExpr so Step 2 preservation
        // propagates it to consumers (e.g., `let n = make_positive();`
        // sees `n` with refinement on its TypedExpr; N38-S7's
        // check_let_stmt push then carries it into the
        // pattern_refinement_stack frame).
        refinement: sig.return_refinement.clone(),
    }
}

/// Phase 4 (row polymorphism): bind every effect-row variable from the actual
/// arguments, then enforce row acceptance on Fn-typed formals.
///
/// BINDING. For a formal `f: Fn(..) -> .. ! { C…, e }` paired with an actual
/// of type `Fn(.., row)`, the variable's least solution is `row \ C`; across
/// occurrences the solutions UNION (still the least overall — any smaller
/// binding fails the acceptance check on some occurrence). A variable no
/// argument constrains stays the empty row. Only the TOP-LEVEL row of a
/// Fn-typed parameter binds (`validate_effect_row_params` rejects every other
/// occurrence shape, and at most one variable per binding row).
///
/// ACCEPTANCE. The generic call path has no `type_compatible` argument loop,
/// so the row-contravariance rule (`actual ⊆ expected`) historically never ran
/// for generic calls — a concrete `! { }` formal on a generic fn accepted an
/// effectful closure whose effects nothing ever charged (the body's
/// `IndirectCall` discharges the FORMAL's row, not the actual's). Enforced
/// here for every top-level Fn-typed formal, variable or not:
/// `actual_row ⊆ resolve(C) ∪ binding(e)`. For variable rows this holds by
/// construction of the binding; for concrete rows it is a real rejection
/// (E001 at the call site).
fn bind_and_check_effect_rows(
    generic_def: &crate::ast::FnDef,
    row_params: &[String],
    typed_args: &[TypedExpr],
    universe: &TypeUniverse,
    call_span: Span,
    diagnostics: &mut Vec<Diagnostic>,
) -> HashMap<String, EffectSet> {
    let mut bindings: HashMap<String, EffectSet> = row_params
        .iter()
        .map(|p| (p.clone(), EffectSet::empty()))
        .collect();
    // Pass 1: bind.
    for (param, arg) in generic_def.params.iter().zip(typed_args.iter()) {
        let Some(ft) = &param.ty.fn_type else {
            continue;
        };
        let Type::Fn(_, _, _, actual_row) = &arg.ty else {
            continue;
        };
        let Some(names) = &ft.effects else { continue };
        let mut concrete = EffectSet::empty();
        let mut vars: Vec<&String> = Vec::new();
        for n in names {
            if row_params.contains(n) {
                vars.push(n);
            } else if let Some(id) = universe.effect_registry.lookup(n) {
                concrete.effects.insert(id);
            }
        }
        if vars.is_empty() {
            continue;
        }
        let residual: Vec<u32> = actual_row
            .effects
            .difference(&concrete.effects)
            .copied()
            .collect();
        for v in vars {
            if let Some(b) = bindings.get_mut(v.as_str()) {
                b.effects.extend(residual.iter().copied());
            }
        }
    }
    // Pass 2: acceptance.
    for (param, arg) in generic_def.params.iter().zip(typed_args.iter()) {
        let Some(ft) = &param.ty.fn_type else {
            continue;
        };
        let Type::Fn(_, _, _, actual_row) = &arg.ty else {
            continue;
        };
        let mut allowed = EffectSet::empty();
        if let Some(names) = &ft.effects {
            for n in names {
                if let Some(b) = bindings.get(n) {
                    allowed.effects.extend(b.effects.iter().copied());
                } else if let Some(id) = universe.effect_registry.lookup(n) {
                    allowed.effects.insert(id);
                }
            }
        }
        if !actual_row.is_subset_of(&allowed) {
            let missing: Vec<String> = actual_row
                .effects
                .difference(&allowed.effects)
                .filter_map(|id| universe.effect_registry.name_of(*id))
                .map(str::to_owned)
                .collect();
            diagnostics.push(Diagnostic::error(
                codes::E001,
                format!(
                    "undeclared effect(s) {} — the closure argument for `{}` performs \
                     effects its parameter row does not allow",
                    missing.join(", "),
                    param.name
                ),
                Some(call_span),
            ));
        }
    }
    bindings
}

/// Phase 4 (row polymorphism): union each bound row variable's instantiation
/// into the `Type::Fn` rows of a resolved type, walking the formal's AST and
/// the resolved `Type` in lockstep. The shapes agree by construction — the
/// `Type` was resolved FROM this AST — and every guard below fails SAFE to
/// the resolved type unchanged: a position where the shapes diverge (e.g. a
/// substituted `Generic` became a `Fn`) is a position where the formal has no
/// row syntax, so there is nothing to overlay.
///
/// This exists because the type-subst map (`HashMap<String, Type>`) is
/// structurally incapable of substituting into a row: rows are `Vec<String>`
/// on the AST and a resolved `EffectSet` has no variable arm.
fn overlay_rows(
    formal: &TypeExpr,
    resolved: Type,
    row_bindings: &HashMap<String, EffectSet>,
) -> Type {
    if row_bindings.is_empty() {
        return resolved;
    }
    match resolved {
        Type::Fn(params, ret, linear, mut row) if formal.fn_type.is_some() => {
            let ft = formal.fn_type.as_ref().expect("guard checked fn_type");
            if let Some(names) = &ft.effects {
                for n in names {
                    if let Some(b) = row_bindings.get(n) {
                        row.effects.extend(b.effects.iter().copied());
                    }
                }
            }
            let params = if params.len() == ft.params.len() {
                params
                    .into_iter()
                    .zip(ft.params.iter())
                    .map(|(rp, fp)| overlay_rows(fp, rp, row_bindings))
                    .collect()
            } else {
                params
            };
            let ret = overlay_rows(&ft.return_type, *ret, row_bindings);
            Type::Fn(params, Box::new(ret), linear, row)
        }
        Type::Array { elem, size } if formal.array_type.is_some() => {
            let arr = formal.array_type.as_ref().expect("guard checked array");
            Type::Array {
                elem: Box::new(overlay_rows(&arr.elem, *elem, row_bindings)),
                size,
            }
        }
        Type::Tuple(tys)
            if formal
                .tuple_type
                .as_ref()
                .is_some_and(|elems| elems.len() == tys.len()) =>
        {
            let elems = formal.tuple_type.as_ref().expect("guard checked tuple");
            Type::Tuple(
                tys.into_iter()
                    .zip(elems.iter())
                    .map(|(t, f)| overlay_rows(f, t, row_bindings))
                    .collect(),
            )
        }
        Type::Named(name, args)
            if formal.fn_type.is_none()
                && formal.array_type.is_none()
                && formal.tuple_type.is_none()
                && formal.path.type_args.len() == args.len()
                && !args.is_empty() =>
        {
            Type::Named(
                name,
                args.into_iter()
                    .zip(formal.path.type_args.iter())
                    .map(|(a, f)| overlay_rows(f, a, row_bindings))
                    .collect(),
            )
        }
        other => other,
    }
}
