//! Free-call resolution and typed call construction.

use std::collections::HashMap;

use super::super::resolve::{
    register_concrete_enum, render_type, resolve_int_literals_or_reject, resolve_type_expr,
    resolve_type_expr_kinded, try_array_size_mismatch_diagnostic, try_cap_deadline_diagnostic,
    try_state_mismatch_diagnostic, type_compatible, unify,
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
    check_generic_aggregate_cap_smuggle, infer_arg_with_expected, type_is_concrete,
    type_mentions_generic,
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
    // (#132). Generic-fn / enum-ctor / closure fallbacks and intrinsics resolve
    // to `concrete_params = None` and are unaffected.
    let intrinsic_shape = resolve_intrinsic_call(&expr.callee);
    // Clone the concrete param types in a scope that DROPS the resolution's
    // borrow of `tracker` before the `&mut tracker` arg loop; `resolution` is
    // recomputed after the loop (CF-I7: arg-independent ⇒ identical result).
    let concrete_params: Option<Vec<Type>> = if intrinsic_shape.is_some() {
        None
    } else {
        match resolve_function_call_with_context(&expr.callee, module_name, function_sigs, tracker)
        {
            Some(CrossModuleResolution::Found(sig)) => Some(sig.params.clone()),
            _ => None,
        }
    };
    let typed_args = expr
        .args
        .iter()
        .enumerate()
        .map(|(i, arg)| {
            infer_arg_with_expected(
                arg,
                concrete_params.as_ref().and_then(|ps| ps.get(i)),
                env,
                current_return,
                context,
                tracker,
                diagnostics,
            )
        })
        .collect::<Vec<_>>();
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
            diagnostics.push(Diagnostic::error(
                codes::R004,
                format!(
                    "cross-ring call: `{module}::{name}` lives in {callee_ring_str} ring, but the caller is in {caller_ring_str} ring. Add `#[ring(outer)] #[trusted]` to the calling module to use FFI-backed stdlib, or call only stdlib modules in the same ring."
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
    if let Some(generic_def) = universe.generic_fns.get(&callee_name).cloned() {
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
            expr.callee
                .type_args
                .iter()
                .enumerate()
                .map(|(i, ta)| {
                    // HK turbofish: a higher-kinded parameter (`F: * -> *`)
                    // is supplied as a bare constructor NAME
                    // (`unwrap::<Box, i64>`). The inference path binds it to
                    // `TypeCtor(Box)` via unify; mirror that here so the
                    // body's `HktApp{F,[A]}` erases to `Named(Box,[A])`.
                    // Resolving normally would yield a malformed 0-arg
                    // `Named(Box, [])` (Box has arity 1) that trips the
                    // use-site arity gate / path-substitution guard.
                    if let Some(pname) = type_params.get(i)
                        && hkt.iter().any(|(n, _)| n == pname)
                    {
                        Type::TypeCtor(ta.path.display_name())
                    } else {
                        resolve_type_expr(ta, universe, &HashMap::new(), &[])
                    }
                })
                .collect()
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

        // Re-narrow integer-LITERAL arguments to the now-known concrete
        // (substituted) parameter types. A generic signature is NOT in
        // `function_sigs`, so the arg loop above ran with `expected = None`
        // (CF-I1): an `IntLit` arg at a `T` position stayed `IntLit` and
        // would default to i64 by the end-of-typecheck mop-up. When this
        // instance binds T=i32/u32, that default mismatches the i32/u32
        // parameter, and AIR emits an `i64.const` into an i32 call slot —
        // an INVALID wasm module that only fails at instantiation. Mirror
        // the non-generic path's `infer_arg_with_expected` narrowing, now
        // that type-arg inference has supplied the concrete param types.
        for (i, param) in generic_def.params.iter().enumerate() {
            let Some(arg) = typed_args.get_mut(i) else {
                continue;
            };
            if !matches!(arg.ty, Type::IntLit(_)) {
                continue;
            }
            let concrete = resolve_type_expr(&param.ty, universe, &subst, &[]);
            if type_is_concrete(&concrete) && type_compatible(&concrete, &arg.ty) {
                resolve_int_literals_or_reject(arg, &concrete, codes::T071, diagnostics);
            }
        }

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
        if !tracker.cache.contains(&qualified) {
            tracker.cache.insert(qualified.clone());

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
                if let Some(prev) = saved_effects {
                    tracker.current_effects = prev;
                }
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
        // Step 1: collect candidate enum names that contain a
        // variant matching the callee's last segment.
        let variant_segment = expr.callee.segments.last().cloned().unwrap_or_default();
        let qualifier: Option<&String> = if expr.callee.segments.len() == 2 {
            expr.callee.segments.first()
        } else {
            None
        };

        let candidate_enums: Vec<String> = if let Some(qual) = qualifier {
            // Qualified path: only consider the named enum.
            if universe.enums.get(qual).is_some_and(|(_, variants)| {
                variants.iter().any(|(name, _)| name == &variant_segment)
            }) {
                vec![qual.clone()]
            } else if universe.enums.contains_key(qual) {
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
            } else {
                // Qualifier is not a known enum — fall through to
                // T062 below.
                Vec::new()
            }
        } else if expr.callee.segments.len() == 1 {
            // Bare path: scan all enums for matching variant.
            // BTreeSet for deterministic ordering per N22-PRB.
            let mut matches: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
            for (enum_name, (_, variants)) in &universe.enums {
                if variants.iter().any(|(name, _)| name == &variant_segment) {
                    matches.insert(enum_name.clone());
                }
            }
            matches.into_iter().collect()
        } else {
            // 3+ segments — not a variant call.
            Vec::new()
        };

        // Step 2: disambiguate.
        let chosen_enum_name: Option<String> = match candidate_enums.len() {
            0 => None,
            1 => Some(candidate_enums[0].clone()),
            _ => {
                // N5-PRB: prefer annotation context.
                let expected_enum = match &tracker.current_expected_type {
                    Some(Type::Named(name, _)) => Some(name.clone()),
                    _ => None,
                };
                if let Some(exp) = expected_enum
                    && candidate_enums.iter().any(|n| n == &exp)
                {
                    Some(exp)
                } else {
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
                let concrete_args: Vec<Type> = type_params
                    .iter()
                    .map(|p| bindings.get(p).cloned().unwrap_or(Type::Error))
                    .collect();
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
            // Narrow a fitting integer-LITERAL arg to the closure's concrete
            // parameter width. The arg loop above ran with `expected = None`
            // (the callee is a local, not a resolved sig), so an `IntLit` at
            // an i32/u32 closure param stayed `IntLit` and would default to
            // i64 — AIR then emits an `i64.const` into a narrow `call_indirect`
            // slot → INVALID wasm. Mirrors the resolved-function-call and
            // generic-call narrowing. A non-fitting / incompatible literal
            // stays `IntLit` and is reported by the `type_compatible` check
            // just below (overflow → T071), exactly as before.
            if matches!(arg.ty, Type::IntLit(_))
                && type_is_concrete(expected)
                && type_compatible(expected, &arg.ty)
            {
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
            let arg_label = format!("argument #{}", idx + 1);
            let site_ctx = format!("function `{callee_name}` argument #{}", idx + 1);
            if let Some(t266) =
                try_state_mismatch_diagnostic(expected, &arg.ty, universe, &site_ctx, arg.span)
            {
                // Typestate (T266): same protocol nominal, wrong state — the
                // protocol-aware form of the generic T071 below.
                diagnostics.push(t266);
            } else if let Some(t195) =
                try_cap_deadline_diagnostic(expected, &arg.ty, &arg_label, &site_ctx, arg.span)
            {
                diagnostics.push(t195);
            } else if let Some(t227) =
                try_array_size_mismatch_diagnostic(expected, &arg.ty, &site_ctx, arg.span)
            {
                diagnostics.push(t227);
            } else {
                diagnostics.push(Diagnostic::error(
                    codes::T071,
                    format!(
                        "function `{}` expected argument of type `{}`, found `{}`",
                        callee_name,
                        render_type(expected),
                        render_type(&arg.ty)
                    ),
                    Some(arg.span),
                ));
            }
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

    let kind = if universe.extern_fns.contains(&callee_name) {
        TypedExprKind::ExternCall(TypedExternCallExpr {
            extern_name: callee_name,
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
