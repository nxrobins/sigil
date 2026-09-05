//! Type resolution, substitution, unification, comparison, and rendering.
//!
//! Leaf-of-call-graph utilities for the type-checker. Every function
//! here operates on `Type` values (and AST `TypeExpr`s in the case of
//! resolution) producing other `Type` values, predicates, or rendered
//! strings for diagnostics. No callbacks into the body inferers; no
//! mutation of MonomorphTracker.
//!
//! ## Roles
//!
//! - **Type resolution**: `resolve_type`, `resolve_type_expr`,
//!   `validate_lowered_type` — turn AST `TypeExpr` into `Type`,
//!   checking parametric-cap deadlines, registering concrete
//!   instances, validating Generic-binder scope.
//! - **Substitution + unification**: `apply_subst`,
//!   `build_record_construction_subst`,
//!   `build_mono_impl_method_mangled_name`,
//!   `register_concrete_enum`, `unify` — generic-instantiation
//!   primitives consumed by `infer_call_expr` and method dispatch.
//! - **Int literal handling**: `infer_literal_type`,
//!   `int_literal_fits`, `default_int_lit_in_type`,
//!   `resolve_int_literals_in_expr`,
//!   `default_remaining_int_literals_in_{expr,stmt,block}` — the
//!   polymorphic-int-literal machinery from PR PIL.
//! - **Type comparison**: `type_compatible`, `cap_subtype`,
//!   `try_array_size_mismatch_*`, `try_cap_deadline_diagnostic`,
//!   `is_send_type`, `is_runtime_message_abi_type`,
//!   `is_machine_integer_type`, `is_error_code_type`.
//! - **Type analysis**: `type_contains_cap`, `type_is_reassignable`,
//!   `classify_reassign_rejection`.
//! - **Rendering**: `render_type`, `render_binary_op`, `render_literal`.
//!
//! Extracted from `type_check/mod.rs` in structural-extraction PR 3.
//! Verbatim move — zero logic change. The shadow CI gate from PR 2.0
//! validates byte-equality of every diagnostic downstream.

use std::collections::{HashMap, HashSet};

use super::{MonomorphTracker, Type, TypeUniverse, closest_name};
use crate::ast::{BinaryOp, Literal, TypeExpr};
use crate::diagnostics::{Diagnostic, codes};
use crate::registries::EffectSet;
use crate::span::Span;
use crate::typed_ast::{TypedBlock, TypedExpr, TypedExprKind, TypedStmt};

pub(super) fn resolve_type(
    ty: &TypeExpr,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) -> Type {
    let lowered = resolve_type_expr(ty, universe, &HashMap::new(), &[]);
    validate_lowered_type(&lowered, universe, ty.span, diagnostics);
    validate_fn_type_effect_rows(ty, universe, diagnostics);
    lowered
}

/// Hard-error every UNREGISTERED effect name in a `Fn(..) -> .. ! { E }` type
/// row, anywhere in the annotation (fn params/returns, array elems, tuple
/// elems, generic args — the same recursive shape as `collect_alias_refs`).
///
/// This must walk the AST, not the lowered type: `resolve_type_expr` is pure
/// and skips unknown names, so by the time the `Type::Fn` exists the typo'd
/// string is gone. Runs on the AST alongside `validate_lowered_type`.
///
/// Policy (roadmap Phase 3, deliberate asymmetry): TYPE-position rows are
/// STRICT — an unknown name is T069 at the annotation site, matching every
/// expression-position surface (`perform` E006, `handle` T069) and the
/// language-wide unknown-name convention (T066/N007/T067). DECLARATION rows
/// keep their documented silent drop (the SH-EFFECT-pinned registration
/// filter); nothing in the legacy corpus is affected because no `.sigil`
/// source could write a type-position row before this change existed.
pub(super) fn validate_fn_type_effect_rows(
    ty: &TypeExpr,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // WALKER FENCE (Phase 4 sweep): exhaustive destructure, no `..` — a new
    // `TypeExpr` field fails compilation here until consciously handled (see
    // `ast::collect_type_row_names` for the fence rationale and the census).
    let TypeExpr {
        path: _,
        ref_kind: _,
        deadline: _,
        span: _,
        fn_type: _,
        array_type: _,
        tuple_type: _,
    } = ty;
    if let Some(fn_ty) = &ty.fn_type {
        if let Some(names) = &fn_ty.effects {
            for name in names {
                if universe.effect_registry.lookup(name).is_none() {
                    let message = format!("unknown effect `{name}` in `Fn` type effect row");
                    let diag = match closest_name(name, universe.effect_registry.names()) {
                        Some(suggestion) => Diagnostic::error_with_hint(
                            codes::T069,
                            message,
                            Some(fn_ty.span),
                            format!(
                                "did you mean `{suggestion}`? Otherwise declare the effect \
                                 with `effect {name};` somewhere in scope"
                            ),
                        ),
                        None => Diagnostic::error_with_hint(
                            codes::T069,
                            message,
                            Some(fn_ty.span),
                            format!(
                                "declare the effect with `effect {name};` somewhere in \
                                 scope, or check the spelling"
                            ),
                        ),
                    };
                    diagnostics.push(diag);
                }
            }
        }
        for p in &fn_ty.params {
            validate_fn_type_effect_rows(p, universe, diagnostics);
        }
        validate_fn_type_effect_rows(&fn_ty.return_type, universe, diagnostics);
        return;
    }
    if let Some(arr) = &ty.array_type {
        validate_fn_type_effect_rows(&arr.elem, universe, diagnostics);
        return;
    }
    if let Some(elems) = &ty.tuple_type {
        for e in elems {
            validate_fn_type_effect_rows(e, universe, diagnostics);
        }
        return;
    }
    for arg in &ty.path.type_args {
        validate_fn_type_effect_rows(arg, universe, diagnostics);
    }
}

pub(super) fn validate_lowered_type(
    ty: &Type,
    universe: &TypeUniverse,
    span: Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match ty {
        Type::Named(name, _)
            if !universe.records.contains_key(name)
                && !universe.enums.contains_key(name)
                && name != "Option"
                && name != "Result"
                && name != "Slot" =>
        {
            let message = format!("unknown type `{name}`");
            let type_names = universe
                .records
                .keys()
                .chain(universe.enums.keys())
                .chain(universe.caps.iter())
                .map(String::as_str);
            let diag = match closest_name(name, type_names) {
                Some(suggestion) => Diagnostic::error_with_hint(
                    codes::T066,
                    message,
                    Some(span),
                    format!("did you mean `{suggestion}`?"),
                ),
                None => Diagnostic::error(codes::T066, message, Some(span)),
            };
            diagnostics.push(diag);
        }
        Type::ActorRef(actor) if !universe.actors.contains(actor) => {
            let message = format!("unknown actor `{actor}` referenced by `ActorRef`");
            let diag = match closest_name(actor, universe.actors.iter().map(String::as_str)) {
                Some(suggestion) => Diagnostic::error_with_hint(
                    codes::T067,
                    message,
                    Some(span),
                    format!("did you mean `{suggestion}`?"),
                ),
                None => Diagnostic::error(codes::T067, message, Some(span)),
            };
            diagnostics.push(diag);
        }
        Type::Named(name, args) => {
            // Typestate (ST-5 → T276): each STATE-position arg must be a declared
            // marker of `name`'s protocol. `File<Banana>` when `state File { Open,
            // Closed }` rejects — the state space is closed at the `state` decl.
            if let Some(states) = universe.typestate_states.get(name) {
                for arg in args {
                    if let Type::StateMarker(m) = arg
                        && !states.contains(m)
                    {
                        diagnostics.push(Diagnostic::error(
                            codes::T276,
                            format!(
                                "`{m}` is not a declared state of protocol `{name}`; declared states are {{{}}}",
                                states.join(", ")
                            ),
                            Some(span),
                        ));
                    }
                }
            }
            // EX-1 (T231): a known generic record/enum used with the WRONG
            // number of type arguments, at ANY annotation position. The
            // `let`-binding path catches this via `resolve_annotated_let_type`,
            // but function params, record fields, enum payloads, return types,
            // and the composite positions below resolve straight through
            // `resolve_type_expr` — without this gate a malformed
            // `Type::Named(Pair, 1 arg)` survives into the body and trips the
            // N10-PRDF arity assert (debug) / silently leaks a `Generic` into
            // AIR mangling (release). Arity is read from the UNIVERSE's declared
            // type-params, never from the arg-count written at the use site.
            let declared_arity = if let Some((tp, _)) = universe.records.get(name) {
                Some(tp.len())
            } else if let Some((tp, _)) = universe.enums.get(name) {
                Some(tp.len())
            } else {
                match name.as_str() {
                    "Option" | "Slot" => Some(1),
                    "Result" => Some(2),
                    _ => None,
                }
            };
            if let Some(arity) = declared_arity
                && arity != args.len()
                // A bare `Foo` (0 args) for a NON-generic record is fine; only
                // flag when the type is actually parametric or args were given.
                && (arity > 0 || !args.is_empty())
            {
                diagnostics.push(Diagnostic::error(
                    codes::T231,
                    format!(
                        "type `{name}` takes {arity} type argument(s), but {} {} supplied",
                        args.len(),
                        if args.len() == 1 { "was" } else { "were" },
                    ),
                    Some(span),
                ));
            }
            for arg in args {
                validate_lowered_type(arg, universe, span, diagnostics);
            }
        }
        // EX-1: recurse into EVERY composite position so a wrong-arity `Named`
        // nested inside a tuple / array / slice / reference / Fn-type is caught
        // too (the pre-EX-1 funnel only descended `Named` args).
        Type::Tuple(elems) => {
            for elem in elems {
                validate_lowered_type(elem, universe, span, diagnostics);
            }
        }
        Type::Array { elem, .. } => validate_lowered_type(elem, universe, span, diagnostics),
        // F1: Ptr is a recurse-into-inner position exactly like Ref/Slice/MutPtr;
        // its omission here was the asymmetric twin of the MutPtr arm.
        Type::Slice(inner) | Type::Ref(inner, _) | Type::Ptr(inner) | Type::MutPtr(inner) => {
            // Phase 4 sweep (T281): a reference or slice of a STRUCTURAL type
            // (fn / tuple / array) has no supported v1 shape. This used to be
            // silently unreachable — the parser and the ref-branch
            // reconstruction both dropped the element's structure, so
            // `&[Fn(..) ! { E }]` degraded to a nominal `Fn` slice and the row
            // (typos and variables included) vanished without a diagnostic.
            // The AST and resolution are faithful now; this is the loud gate,
            // fail-closed for every structural target rather than silently
            // enabling AIR-untested shapes.
            if matches!(
                inner.as_ref(),
                Type::Fn(..) | Type::Tuple(_) | Type::Array { .. }
            ) {
                diagnostics.push(Diagnostic::error(
                    codes::T281,
                    "references and slices of function, tuple, or array types are not \
                     supported — pass the value directly or store it in a record field"
                        .to_string(),
                    Some(span),
                ));
            }
            validate_lowered_type(inner, universe, span, diagnostics)
        }
        Type::Fn(params, ret, _, _) => {
            for p in params {
                validate_lowered_type(p, universe, span, diagnostics);
            }
            validate_lowered_type(ret, universe, span, diagnostics);
        }
        // Wall 2 → Wall 3: enforce parametric vs non-parametric
        // consistency AND arity match AND build-deadline at every
        // position.
        //
        //   T196: parametric cap (decl_arity > 0) referenced with empty
        //         value list.
        //   T197: non-parametric cap (decl_arity == 0) referenced with
        //         non-empty value list.
        //   T201: parametric cap referenced with the wrong number of
        //         values (M != N, both > 0).
        //   T199: any literal `D < BUILD_NOW` — fires ONCE PER POSITION
        //         (multi-fire pinned behavior per the v2 plan).
        Type::Cap(name, deadline) => {
            let decl_params = universe.parametric_caps.get(name);
            let decl_arity = decl_params.map_or(0, |v| v.len());
            let used_arity = deadline.len();
            match (decl_arity, used_arity) {
                (0, 0) => {} // non-parametric, no values — OK
                (0, _) => {
                    let vals = deadline
                        .iter()
                        .map(|d| d.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    diagnostics.push(Diagnostic::error(
                        codes::T197,
                        format!(
                            "capability `{name}` is non-parametric; remove the `({vals})` argument or declare the cap as `cap type {name}(<param>: i64) {{}}` to make it parametric"
                        ),
                        Some(span),
                    ));
                }
                (n, 0) => {
                    let param_names = decl_params
                        .map(|v| {
                            v.iter()
                                .map(|p| p.name.clone())
                                .collect::<Vec<_>>()
                                .join(", ")
                        })
                        .unwrap_or_default();
                    diagnostics.push(Diagnostic::error(
                        codes::T196,
                        format!(
                            "parametric capability `{name}` requires {n} `i64` literal value(s) at this position; declared parameters are ({param_names}). Write `{name}(<v1>, <v2>, ...)` instead of bare `{name}`"
                        ),
                        Some(span),
                    ));
                }
                (n, m) if n != m => {
                    // T201: arity mismatch. Message contains cap name,
                    // declared arity, used arity, AND declared param
                    // names (MC-10 fence).
                    let param_names = decl_params
                        .map(|v| {
                            v.iter()
                                .map(|p| p.name.clone())
                                .collect::<Vec<_>>()
                                .join(", ")
                        })
                        .unwrap_or_default();
                    diagnostics.push(Diagnostic::error_with_hint(
                        codes::T201,
                        format!(
                            "capability `{name}` declared with {n} parameter(s) ({param_names}); usage supplies {m} value(s). Arity must match exactly."
                        ),
                        Some(span),
                        format!(
                            "supply exactly {n} `i64` literal(s) at this position, matching the declared parameter list ({param_names})",
                        ),
                    ));
                }
                _ => {
                    // Arities match AND > 0: per-position build-deadline
                    // check (MC-2 fence — multi-fire one T199 per
                    // stale position).
                    if let Some(build_now) = universe.build_deadline {
                        for (idx, d) in deadline.iter().enumerate() {
                            if *d < build_now {
                                let position_name = decl_params
                                    .and_then(|v| v.get(idx))
                                    .map(|p| p.name.as_str())
                                    .unwrap_or("<position>");
                                diagnostics.push(Diagnostic::error_with_hint(
                                    codes::T199,
                                    format!(
                                        "capability `{name}` parameter `{position_name}` at position {idx} declares `{d}`, which is past the build-time reference (`--build-deadline {build_now}`); the cap would be stale before any program execution"
                                    ),
                                    Some(span),
                                    format!(
                                        "widen position {idx} to a value `>= {build_now}`, raise `--build-deadline` (or drop the flag if non-time parameters are intentional), or restructure so the cap is narrowed via `restrict_deadline(...)` at runtime. NOTE: the build-deadline check is uniform across ALL parameters; only apply `--build-deadline` when your caps are time-parametric.",
                                    ),
                                ));
                            }
                        }
                    }
                }
            }
        }
        _ => {}
    }
}

pub(super) fn resolve_type_expr(
    ty: &TypeExpr,
    universe: &TypeUniverse,
    subst: &HashMap<String, Type>,
    in_scope_generics: &[String],
) -> Type {
    resolve_type_expr_kinded(ty, universe, subst, in_scope_generics, &[])
}

/// HKT-aware core of `resolve_type_expr`. `in_scope_hkt` lists the higher-kinded
/// type-parameter binders currently in scope as `(name, arity)` pairs (from
/// `ast::hkt_params`). A use of such a binder resolves to `Type::HktVar` (bare
/// `F`) or `Type::HktApp` (applied `F<A>`) — NOT a bare `Type::Generic`, which
/// would silently drop the `<…>` arguments. Callers without HKT binders in scope
/// go through the `&[]` wrapper above (the common case).
pub(super) fn resolve_type_expr_kinded(
    ty: &TypeExpr,
    universe: &TypeUniverse,
    subst: &HashMap<String, Type>,
    in_scope_generics: &[String],
    in_scope_hkt: &[(String, usize)],
) -> Type {
    // Phase 4 sweep: the three STRUCTURE branches below (tuple / fn / array)
    // are guarded on `ref_kind.is_none()`. A `&`/`&[..]`-modified node keeps
    // its element's structure on the SAME node (the same-node-modifier
    // convention), so without the guard a `&[Fn(..)]` would resolve as a bare
    // `Fn` — the reference silently dropped. Modified nodes fall through to
    // the reference/slice branch, which resolves the faithful inner (and
    // `validate_lowered_type` then rejects ref/slice-of-fn with T281).
    //
    // Tuple-type syntax `(A, B, …)` → `Type::Tuple`, resolving each element
    // against the current substitution / in-scope-generics (so a tuple of
    // generics like `(T, i64)` propagates `Type::Generic` to monomorphization).
    if ty.ref_kind.is_none()
        && let Some(elems) = &ty.tuple_type
    {
        let resolved: Vec<Type> = elems
            .iter()
            .map(|e| resolve_type_expr_kinded(e, universe, subst, in_scope_generics, in_scope_hkt))
            .collect();
        return Type::Tuple(resolved);
    }

    // PR B / N29-PRB: function-type syntax `Fn(T1, T2, ...) -> U`.
    // Translates to the existing `Type::Fn(params, ret, EffectSet)`
    // variant. The closure-construction side (Expr::Closure) and the
    // call-site (Type::Fn dispatch) are already wired; this is the
    // type-EXPRESSION-side bridge admitting Fn-typed parameters in
    // function signatures.
    if ty.ref_kind.is_none()
        && let Some(fn_ty) = &ty.fn_type
    {
        let params: Vec<Type> = fn_ty
            .params
            .iter()
            .map(|p| resolve_type_expr_kinded(p, universe, subst, in_scope_generics, in_scope_hkt))
            .collect();
        let ret = resolve_type_expr_kinded(
            &fn_ty.return_type,
            universe,
            subst,
            in_scope_generics,
            in_scope_hkt,
        );
        // is_linear = false: Fn(T) -> U as a parameter TYPE doesn't
        // capture; the closure-construction site sets is_linear based
        // on its actual captures at construction time. The parameter's
        // type only encodes the call shape.
        //
        // Latent row (roadmap Phase 3): `Fn(T) -> U ! { E }` resolves its written
        // row; no row written = the EMPTY row (fail-closed — an unannotated `Fn`
        // parameter promises to perform NOTHING when applied, so it is callable
        // from any context and only PURE values satisfy it, via the contravariant
        // check in `type_compatible`).
        //
        // An UNREGISTERED name is skipped here — this function is pure (no
        // diagnostics sink) — and reported as a hard T069 by
        // `validate_fn_type_effect_rows`, which `resolve_type` runs on the same
        // AST node. The skip is sound in isolation (a smaller resolved row only
        // tightens acceptance and loosens discharge by the same amount — no
        // false accept is constructible), but soundness is not the bar: the
        // typo'd annotation would silently reject the very closures it was
        // written to admit, so the validator makes it a compile error at the
        // annotation site. TYPE rows are born strict; DECLARATION rows keep
        // their documented silent-drop (the SH-EFFECT-pinned registration
        // filter) — see `resolve_effect_row`.
        let mut latent = EffectSet::empty();
        if let Some(names) = &fn_ty.effects {
            for name in names {
                if let Some(id) = universe.effect_registry.lookup(name) {
                    latent.effects.insert(id);
                }
            }
        }
        return Type::Fn(params, Box::new(ret), false, latent);
    }

    // PR P16 / N3-P16: array-type syntax `[T; N]`. The size is
    // already validated at parse time (0..=65535); resolve the
    // element type recursively against the current substitution /
    // in-scope-generics. Generic-element arrays (`[T; 3]` where T
    // is in_scope) propagate `Type::Generic("T")` through the
    // returned `Type::Array.elem`; the eventual monomorphization
    // walks via PR D's `apply_subst` machinery (AG-P16-S).
    if ty.ref_kind.is_none()
        && let Some(arr_ty) = &ty.array_type
    {
        let elem = resolve_type_expr_kinded(
            &arr_ty.elem,
            universe,
            subst,
            in_scope_generics,
            in_scope_hkt,
        );
        return Type::Array {
            elem: Box::new(elem),
            size: arr_ty.size,
        };
    }

    // Check for reference/slice type annotations. The stripped inner PRESERVES
    // the element's structure (fn/array/tuple) — reconstructing from `path`
    // alone was the second, independent structure-dropper (the parser's slice
    // branch was the first): a preserved `&[Fn(..)]` element would have been
    // re-degraded to the nominal `Fn` right here.
    if let Some(ref_kind) = &ty.ref_kind {
        let inner = resolve_type_expr_kinded(
            &TypeExpr {
                path: ty.path.clone(),
                ref_kind: None,
                deadline: ty.deadline.clone(),
                span: ty.span,
                fn_type: ty.fn_type.clone(),
                array_type: ty.array_type.clone(),
                tuple_type: ty.tuple_type.clone(),
            },
            universe,
            subst,
            in_scope_generics,
            in_scope_hkt,
        );
        return match ref_kind {
            crate::ast::RefKind::Ref(mutable) => Type::Ref(Box::new(inner), *mutable),
            crate::ast::RefKind::Slice => Type::Slice(Box::new(inner)),
        };
    }

    let name = ty.path.display_name();

    // 1. Check substitution map first (concrete instantiation). HKT body-side
    //    erasure: when a higher-kinded `F` is bound to `TypeCtor("Vec")` and used
    //    applied as `F<A>`, rebuild the concrete `Named("Vec", [A])` here. (The
    //    binding is only ever `TypeCtor` once monomorphization runs, PR-HK1; until
    //    then `subst` carries no `TypeCtor` and this stays inert.)
    if let Some(concrete) = subst.get(&name) {
        if let Type::TypeCtor(cname) = concrete
            && !ty.path.type_args.is_empty()
        {
            let args: Vec<Type> = ty
                .path
                .type_args
                .iter()
                .map(|a| {
                    resolve_type_expr_kinded(a, universe, subst, in_scope_generics, in_scope_hkt)
                })
                .collect();
            return Type::Named(cname.clone(), args);
        }
        return concrete.clone();
    }

    // 2. In-scope higher-kinded binder: bare `F` → `HktVar`, applied `F<A>` →
    //    `HktApp`. This MUST precede the ordinary-generic check below (which emits
    //    a bare `Generic` and would silently DROP the `<…>` arguments) and must
    //    preserve the type arguments.
    if let Some((_, arity)) = in_scope_hkt.iter().find(|(n, _)| n == &name) {
        let args: Vec<Type> = ty
            .path
            .type_args
            .iter()
            .map(|a| resolve_type_expr_kinded(a, universe, subst, in_scope_generics, in_scope_hkt))
            .collect();
        if args.is_empty() {
            return Type::HktVar {
                name,
                arity: *arity,
            };
        }
        return Type::HktApp { ctor: name, args };
    }

    // 3. If it's an in-scope generic parameter, emit Generic
    if in_scope_generics.contains(&name) {
        return Type::Generic(name);
    }

    // 3b. Typestate (Epic 1): a stateful nominal (`record File<@S>`) resolves its
    //     STATE-position args to `Type::StateMarker` (a phantom protocol index);
    //     ordinary positions recurse normally. Membership in the protocol's closed
    //     state set is gated by `validate_lowered_type` (ST-5 → T276), so resolution
    //     is permissive here (any name in a state position becomes a marker) and the
    //     diagnostic-carrying validator rejects strays.
    if let Some(state_positions) = universe.typestate_state_positions.get(&name) {
        let args: Vec<Type> = ty
            .path
            .type_args
            .iter()
            .enumerate()
            .map(|(i, a)| {
                if state_positions.contains(&i) {
                    // TS3: resolve the state-position arg through the normal path so a
                    // STATE BINDER (`fn fd<@S>(f: File<S>)` — `S` in_scope) stays
                    // POLYMORPHIC (`Type::Generic`, reusing the generic unify/subst
                    // channel), and a binder already bound by the mono subst becomes
                    // its concrete `StateMarker`. Anything else (a concrete marker
                    // name `Open`, or a stray) is a state MARKER — gated against the
                    // protocol's closed set by `validate_lowered_type` (ST-5/T276).
                    match resolve_type_expr_kinded(
                        a,
                        universe,
                        subst,
                        in_scope_generics,
                        in_scope_hkt,
                    ) {
                        poly @ Type::Generic(_) => poly,
                        marker @ Type::StateMarker(_) => marker,
                        _ => Type::StateMarker(a.display_name()),
                    }
                } else {
                    resolve_type_expr_kinded(a, universe, subst, in_scope_generics, in_scope_hkt)
                }
            })
            .collect();
        return Type::Named(name, args);
    }

    // 4. Resolve type args recursively
    let args: Vec<Type> = ty
        .path
        .type_args
        .iter()
        .map(|a| resolve_type_expr_kinded(a, universe, subst, in_scope_generics, in_scope_hkt))
        .collect();

    match name.as_str() {
        "unit" => Type::Unit,
        "bool" => Type::Bool,
        "i32" => Type::I32,
        "u32" => Type::U32,
        "i64" => Type::I64,
        "u64" => Type::U64,
        "f64" => Type::F64,
        "u256" => Type::U256,
        "i256" => Type::I256,
        "str" => Type::Str,
        // Regions (DEF-2b, LD-1): `Region` is a built-in handle type (no type args).
        "Region" => Type::Region,
        "ActorRef" if !args.is_empty() => Type::ActorRef(ty.path.type_args[0].display_name()),
        // Wall 2 Stage 1: propagate the deadline literal from the
        // usage's TypeExpr into Type::Cap. Validation that the cap is
        // (non-)parametric in a way consistent with `ty.deadline`
        // happens in `validate_lowered_type` (which sees the diagnostic
        // channel). resolve_type_expr is "best-effort" — it produces
        // the most natural Type given the inputs, then validation flags
        // semantic violations.
        // PR-E4: a type alias expands to its (module-level) body, resolved with an
        // EMPTY subst / generic scope (the body is defined at module scope, so the
        // use-site's substitutions must not leak in). `alias_bodies` holds only
        // ACYCLIC aliases (cyclic ones were excluded during collection), so this
        // recursion always terminates; the body itself recurses through nested
        // aliases. An alias is non-parametric — any `args` here are ignored.
        n if universe.alias_bodies.contains_key(n) => {
            let body = &universe.alias_bodies[n];
            resolve_type_expr(body, universe, &HashMap::new(), &[])
        }
        n if universe.caps.contains(n) => Type::Cap(n.to_owned(), ty.deadline.clone()),
        n => Type::Named(n.to_owned(), args),
    }
}

/// Register a concrete enum instantiation in the monomorphization tracker.
pub(super) fn register_concrete_enum(
    tracker: &mut MonomorphTracker,
    mangled: &str,
    variants: &[(String, Vec<Type>)],
    type_params: &[String],
    concrete_args: &[Type],
) {
    if tracker.cache.contains(mangled) {
        return;
    }
    tracker.cache.insert(mangled.to_owned());
    let subst: HashMap<String, Type> = type_params
        .iter()
        .zip(concrete_args.iter())
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let concrete_variants = variants
        .iter()
        .map(|(vname, vtypes)| {
            (
                vname.clone(),
                vtypes.iter().map(|t| apply_subst(t, &subst)).collect(),
            )
        })
        .collect();
    tracker.enums.insert(mangled.to_owned(), concrete_variants);
}

/// Apply a substitution map to a resolved Type tree (not an AST TypeExpr).
/// PR D / N5-PRD: SINGLE canonical helper for mangling impl-method
/// monomorphization names. Format:
/// `"{qualified_name}__{mangle_type(arg_0)}_{mangle_type(arg_1)}_..."`.
/// Uses the existing `air::mangle_type` for each receiver type-arg
/// to ensure cross-cutting consistency (same mangling that AIR
/// uses for wasm export names).
///
/// CI grep-lint asserts the new monomorphization code in
/// `infer_method_call_expr` calls ONLY this helper (not a
/// hand-rolled `format!`).
pub(super) fn build_mono_impl_method_mangled_name(
    qualified_name: &str,
    receiver_type_args: &[Type],
) -> String {
    // TS3: state markers are ERASED, so they are dropped from the impl-method mono
    // key (state-blind, exactly like the free-fn key) — a state-polymorphic method
    // (`impl File<@S> { fn peek(self: File<S>) }`) collapses to ONE instance
    // regardless of the state, and a bare `StateMarker` never reaches
    // `mangle_type`'s fail-closed ICE arm. (Applies to BOTH the receiver state args
    // and any state in the method's own type-args — this is the single chokepoint
    // for every impl-method mono name.)
    let mangled_args: Vec<String> = receiver_type_args
        .iter()
        .filter(|a| !matches!(a, Type::StateMarker(_)))
        .map(crate::air::mangle_type)
        .collect();
    if mangled_args.is_empty() {
        return qualified_name.to_string();
    }
    // R2: `$`-join (not `_`) — keep impl-method instance names injective, matching
    // `air::mangle_type` and the free-fn mono key.
    format!("{}__{}", qualified_name, mangled_args.join("$"))
}

/// Apply a type-parameter substitution to a `Type`, replacing
/// `Type::Generic(name)` with `subst[name]` recursively through
/// `Type::Named`, `Type::Array`, `Type::Ref`, `Type::Slice`,
/// `Type::Tuple`, and `Type::Fn` (params + return).
///
/// Promoted from `fn` to `pub(crate) fn` in PR D follow-up so AIR's
/// `build_field_registry` can substitute generic record field types
/// when constructing per-instantiation registry entries for
/// monomorphized record types (AG-PRDF-19's "third escape" needs
/// access to this function from the AIR layer).
pub(crate) fn apply_subst(ty: &Type, subst: &HashMap<String, Type>) -> Type {
    match ty {
        Type::Generic(name) => subst.get(name).cloned().unwrap_or_else(|| ty.clone()),
        Type::Named(name, args) => Type::Named(
            name.clone(),
            args.iter().map(|a| apply_subst(a, subst)).collect(),
        ),
        Type::Array { elem, size } => Type::Array {
            elem: Box::new(apply_subst(elem, subst)),
            size: *size,
        },
        Type::Ref(inner, mutable) => Type::Ref(Box::new(apply_subst(inner, subst)), *mutable),
        Type::Slice(inner) => Type::Slice(Box::new(apply_subst(inner, subst))),
        // F1: substitute generics nested inside FFI pointers too — without these
        // arms a `Ptr<T>` / `MutPtr<T>` falls to the `other => other.clone()`
        // catch-all below, leaving `T` unsubstituted to ICE in mangle_type.
        Type::Ptr(inner) => Type::Ptr(Box::new(apply_subst(inner, subst))),
        Type::MutPtr(inner) => Type::MutPtr(Box::new(apply_subst(inner, subst))),
        // ET-9: substitute generics INSIDE a tuple — a generic impl method
        // returning `(T, T)` must have its `T`s replaced, else `Type::Generic`
        // reaches mangle_type and ICEs.
        Type::Tuple(elems) => Type::Tuple(elems.iter().map(|e| apply_subst(e, subst)).collect()),
        // Substitute generics INSIDE a closure type — a generic fn/method with a
        // param `f: Fn(T) -> U` monomorphized at T/U must have those `T`/`U`s
        // replaced in BOTH params and return, else `Type::Generic` reaches
        // mangle_type / AIR and ICEs. (Shipped closures-as-params use fully
        // concrete Fn types, so this is the previously-unexercised generic case.)
        // The latent effect row is carried through substitution unchanged: substituting a
        // TYPE variable cannot change which effects the function performs when applied.
        Type::Fn(params, ret, linear, effects) => Type::Fn(
            params.iter().map(|p| apply_subst(p, subst)).collect(),
            Box::new(apply_subst(ret, subst)),
            *linear,
            effects.clone(),
        ),
        // HKT (PR-HK1): the ERASURE arm. With `F |-> TypeCtor("Vec")` in `subst`,
        // an application `F<A>` collapses to the concrete `Named("Vec", args)` — the
        // check-time-only HKT var is gone before AIR. The bound ctor's arity matched
        // the application's arg count at the (arity-gated) `unify_inner` that produced
        // the binding, so `new_args.len()` is arity-correct by construction; a
        // wrong-arity escapee (via a non-unify binding path) is caught loudly by the
        // EX-4 residual gate / `mangle_type` ICE before AIR. A still-unbound ctor
        // stays a symbolic `HktApp` (recursing into args).
        Type::HktVar { name, .. } => subst.get(name).cloned().unwrap_or_else(|| ty.clone()),
        Type::HktApp { ctor, args } => {
            let new_args: Vec<Type> = args.iter().map(|a| apply_subst(a, subst)).collect();
            match subst.get(ctor) {
                Some(Type::TypeCtor(cname)) => Type::Named(cname.clone(), new_args),
                // `F` bound directly to a concrete nullary `Named` (e.g. via
                // return-directed inference) — graft the args onto its head.
                Some(Type::Named(cname, base)) if base.is_empty() => {
                    Type::Named(cname.clone(), new_args)
                }
                _ => Type::HktApp {
                    ctor: ctor.clone(),
                    args: new_args,
                },
            }
        }
        Type::TypeCtor(_) => ty.clone(),
        other => other.clone(),
    }
}

/// PR A — Generic record CONSTRUCTION substitution: a discovered or
/// declared binding for a generic record's type parameter, with
/// provenance for diagnostic emission.
///
#[derive(Debug, Clone)]
struct SubstBinding {
    ty: Type,
    /// True when this binding came from a let-annotation
    /// (`let h: Holder<i64> = ...`). Pinned bindings are immutable
    /// during field-value inference per N3-PRA: a subsequent field
    /// that infers a different type for this param produces a
    /// PinnedAnnotationViolated fault (T071-style), NOT a Conflict
    /// fault (T234).
    pinned: bool,
}

/// PR A — A single substitution-building failure surfaced by
/// `build_record_construction_subst`. Per N8-PRA the helper returns
/// `Vec<RecordSubstFault>` so a single call surfaces multiple
/// failures (e.g., one Conflict on `T` AND one Unresolved on `U`)
/// rather than the two-error masking problem of a single-error enum.
///
/// Per N9-PRA all matches against this enum are exhaustive — no
/// `_ =>` wildcards. CI grep-lint forbids the wildcard pattern
/// against `RecordSubstFault`.
///
#[derive(Debug, Clone)]
pub(super) enum RecordSubstFault {
    /// N5-PRA + T234: two or more fields produced INCOMPATIBLE
    /// bindings for the same type-param. Fires AT MOST ONCE per
    /// conflicting param (subsequent conflicting bindings on the
    /// same param do NOT add additional Conflict entries — see
    /// `fired_conflicts` in `build_record_construction_subst`).
    /// Per N14-PRA: caller marks the param's subst entry as
    /// `Type::Error` to prevent downstream cascade.
    Conflict {
        param: String,
        /// All (field_name, inferred_ty) pairs that contributed
        /// bindings for this param, in source order. The diagnostic
        /// renders this Vec to show every contributor without
        /// arbitrarily blaming one side.
        bindings: Vec<(String, Type)>,
    },
    /// T233: type-param has no binding after walking all supplied
    /// fields AND no annotation was supplied to pin it. Common for
    /// phantom-T records.
    Unresolved { param: String },
    /// N3-PRA + T071-style: a field value's inferred type doesn't
    /// match the annotation-pinned param. Fires per offending field
    /// (NOT per param) because the user can see which field is
    /// wrong directly from the annotation's ground truth.
    PinnedAnnotationViolated {
        param: String,
        annotated: Type,
        field_name: String,
        field_ty: Type,
    },
}

/// PR A — Build a type-param substitution map for a generic record
/// construction site. Per N7-PRA the algorithm is strict two-pass:
///
/// **Pass 1 (annotation seed)**: if `seed` is supplied (from a
/// `let x: RecordName<ConcreteArgs> = ...` annotation), insert each
/// `{type_param[i] → ConcreteArg[i]}` binding as PINNED. Pinned
/// bindings are immutable during pass 2.
///
/// **Pass 2 (field-value inference)**: walk each declared field in
/// source order. For each field, call `unify(declared_ty, value_ty,
/// &mut local)` (N10-PRA — reuse the canonical unifier, no
/// reimplementation). Merge each local binding into the subst with
/// insert-time conflict detection (N2-PRA):
///   - if pinned and incompatible → PinnedAnnotationViolated fault
///     (T071-style at caller)
///   - if inferred and incompatible → Conflict fault (T234 at
///     caller), keyed by param name so only ONE fires per param
///     (N5-PRA). Param's subst entry is marked `Type::Error` to
///     prevent cascade (N14-PRA).
///   - if first binding → insert
///
/// **Pass 3 (unresolved check)**: any type-param not in subst →
/// Unresolved fault (T233 at caller).
///
/// **Early-return (N12-PRA)**: non-generic records (`type_params`
/// empty) return `Ok(HashMap::new())` immediately. This preserves
/// pre-PR-A behavior byte-for-byte.
// N2-PRA `#[must_use]` intent is honored structurally by the
// returned `Result<_, _>` (Rust marks `Result` as `must_use` already).
// `clippy::double_must_use` forbids an explicit `#[must_use]` on
// functions returning `Result`. The constraint's intent ("callers
// MUST match the outcome") is enforced by Rust's must_use lint on
// `Result` itself.
pub(super) fn build_record_construction_subst(
    type_params: &[String],
    declared_fields: &[(String, Type)],
    typed_values: &[(String, TypedExpr)],
    seed: Option<&HashMap<String, Type>>,
) -> Result<HashMap<String, Type>, Vec<RecordSubstFault>> {
    // N12-PRA: early-return for non-generic records.
    if type_params.is_empty() {
        return Ok(HashMap::new());
    }

    let mut subst: HashMap<String, SubstBinding> = HashMap::new();
    let mut faults: Vec<RecordSubstFault> = Vec::new();
    let mut fired_conflicts: HashSet<String> = HashSet::new();
    // Track which field contributed each successful binding so the
    // Conflict fault can list every contributor (no arbitrary blame).
    let mut contributors: HashMap<String, Vec<(String, Type)>> = HashMap::new();

    // Pass 1: seed from annotation.
    if let Some(annotation_subst) = seed {
        for (k, v) in annotation_subst {
            subst.insert(
                k.clone(),
                SubstBinding {
                    ty: v.clone(),
                    pinned: true,
                },
            );
        }
    }

    // Map field names to their typed values (declaration order may
    // not match construction order; match by name).
    let value_by_name: HashMap<&str, &TypedExpr> =
        typed_values.iter().map(|(n, e)| (n.as_str(), e)).collect();

    // Pass 2: walk declared fields in source order (N11-PRA).
    for (field_name, declared_ty) in declared_fields {
        let Some(value) = value_by_name.get(field_name.as_str()) else {
            // Field not supplied at construction; existing arity/missing-
            // field check (outside this helper) handles the diagnostic.
            continue;
        };
        let value_ty = &value.ty;

        // N10-PRA: call the canonical unifier, do not reimplement.
        let mut local_bindings: HashMap<String, Type> = HashMap::new();
        unify(declared_ty, value_ty, &mut local_bindings);

        // N2-PRA: insert-time conflict detection. Each local binding
        // is checked against the existing subst entry (if any).
        for (param, new_ty) in local_bindings {
            // Record contributor regardless of merge outcome — the
            // Conflict fault wants the full list.
            contributors
                .entry(param.clone())
                .or_default()
                .push((field_name.clone(), new_ty.clone()));

            match subst.get(&param) {
                Some(existing) if existing.pinned => {
                    // N3-PRA: annotation pinned. Field-value-vs-annotation
                    // mismatch routes to T071-style at caller.
                    if !type_compatible(&existing.ty, &new_ty) {
                        faults.push(RecordSubstFault::PinnedAnnotationViolated {
                            param: param.clone(),
                            annotated: existing.ty.clone(),
                            field_name: field_name.clone(),
                            field_ty: new_ty,
                        });
                    }
                    // Annotation wins; subst entry stays pinned.
                }
                Some(existing) => {
                    // Inferred from prior field. Check consistency.
                    if !type_compatible(&existing.ty, &new_ty) {
                        // N5-PRA: fire Conflict ONCE per param.
                        if fired_conflicts.insert(param.clone()) {
                            faults.push(RecordSubstFault::Conflict {
                                param: param.clone(),
                                bindings: contributors.get(&param).cloned().unwrap_or_default(),
                            });
                            // N14-PRA: mark Type::Error to prevent cascade.
                            subst.insert(
                                param.clone(),
                                SubstBinding {
                                    ty: Type::Error,
                                    pinned: false,
                                },
                            );
                        }
                        // Subsequent conflicts on same param: skip diagnostic,
                        // keep Type::Error.
                    }
                    // else: agrees with existing, no-op.
                }
                None => {
                    // First binding for this param.
                    subst.insert(
                        param,
                        SubstBinding {
                            ty: new_ty,
                            pinned: false,
                        },
                    );
                }
            }
        }
    }

    // Pass 3: any type-param not bound is unresolved.
    for param in type_params {
        if !subst.contains_key(param) {
            faults.push(RecordSubstFault::Unresolved {
                param: param.clone(),
            });
        }
    }

    if faults.is_empty() {
        Ok(subst.into_iter().map(|(k, b)| (k, b.ty)).collect())
    } else {
        Err(faults)
    }
}

/// Structural unifier: walks type trees and binds Generic("T") to concrete types.
pub(super) fn unify(formal: &Type, actual: &Type, bindings: &mut HashMap<String, Type>) {
    unify_inner(formal, actual, bindings, false);
}

/// `nested` is true once we have descended through at least one structural
/// constructor (`Named`/`Array`/`Ref`/`Slice`/`Fn`/`Tuple`). It gates the
/// literal-yields-to-concrete upgrade below: a bare TOP-LEVEL scalar argument
/// must NOT override a prior integer-literal binding (that preserves existing
/// call-inference parity — e.g. `id2(5, n: u32)` keeps T bound to the literal,
/// matching the self-hosted oracle), but a concrete type recovered from INSIDE
/// a structural argument — most importantly a closure parameter `Fn(i32)->i32`
/// — must, so argument order can't pick the wrong monomorphization instance.
fn unify_inner(formal: &Type, actual: &Type, bindings: &mut HashMap<String, Type>, nested: bool) {
    match (formal, actual) {
        (Type::Generic(name), ty) => match bindings.get(name) {
            None => {
                bindings.insert(name.clone(), ty.clone());
            }
            // A prior binding from a polymorphic integer LITERAL is WEAK. A
            // concrete (non-literal) type found NESTED inside a structural
            // argument is a STRONGER constraint and replaces it. Gated on
            // `nested` so top-level scalar args keep first-binding-wins
            // semantics (differential parity); only nested positions — which
            // had NO unify arm at all before (closures/tuples contributed
            // nothing) — gain this precedence, so no previously-checked program
            // changes meaning.
            Some(Type::IntLit(_)) if nested && !matches!(ty, Type::IntLit(_)) => {
                bindings.insert(name.clone(), ty.clone());
            }
            Some(_) => {}
        },
        (Type::Named(f, f_args), Type::Named(a, a_args)) if f == a => {
            for (fa, aa) in f_args.iter().zip(a_args.iter()) {
                unify_inner(fa, aa, bindings, true);
            }
        }
        (Type::Array { elem: f, .. }, Type::Array { elem: a, .. }) => {
            unify_inner(f, a, bindings, true)
        }
        (Type::Ref(f, _), Type::Ref(a, _)) => unify_inner(f, a, bindings, true),
        (Type::Slice(f), Type::Slice(a)) => unify_inner(f, a, bindings, true),
        // F1: recover type params nested inside FFI pointers, mirroring Ref/Slice.
        (Type::Ptr(f), Type::Ptr(a)) => unify_inner(f, a, bindings, true),
        (Type::MutPtr(f), Type::MutPtr(a)) => unify_inner(f, a, bindings, true),
        // Bind type params appearing INSIDE a closure type — a generic fn/method
        // with a param `f: Fn(T) -> U` must recover T/U from a closure ARGUMENT
        // (`Fn(i32)->i32` ⇒ T=i32). Without this arm the closure arg contributes
        // NO binding, so the type param falls to whatever the other (often
        // literal) arguments default it to. Recurse params + return.
        (Type::Fn(f_params, f_ret, _, _), Type::Fn(a_params, a_ret, _, _)) => {
            for (fp, ap) in f_params.iter().zip(a_params.iter()) {
                unify_inner(fp, ap, bindings, true);
            }
            unify_inner(f_ret, a_ret, bindings, true);
        }
        // Bind type params inside a tuple argument — `f: (T, U)` ⇒ from `(i32, str)`.
        (Type::Tuple(f_elems), Type::Tuple(a_elems)) => {
            for (fe, ae) in f_elems.iter().zip(a_elems.iter()) {
                unify_inner(fe, ae, bindings, true);
            }
        }
        // HKT (PR-HK1): a higher-kinded application `F<A>` (formal) unified against
        // a rigid concrete `Named("Vec", [i64])` (the actual is ALWAYS rigid under
        // eager mono — INV-1) decomposes into TWO bindings: the constructor head
        // `F |-> TypeCtor("Vec")` AND a recursive unify of the arguments
        // (`A |-> i64`). ARITY-GATED — `F<A>` (1 arg) against a 2-arg ctor like
        // `Result<i64, str>` matches NO arm, leaving `F` unbound → a clean T150 at
        // the call site (the EX-5/EX-1 use-site arity rejection for the free-fn
        // path). First-binding-wins on the head, mirroring the `Generic` arm.
        (Type::HktApp { ctor, args: f_args }, Type::Named(a_name, a_args))
            if f_args.len() == a_args.len() =>
        {
            if !bindings.contains_key(ctor) {
                bindings.insert(ctor.clone(), Type::TypeCtor(a_name.clone()));
            }
            for (fa, aa) in f_args.iter().zip(a_args.iter()) {
                unify_inner(fa, aa, bindings, true);
            }
        }
        // A bare higher-kinded var `F` (formal) against a concrete `Named` head
        // binds the constructor (covers a rare un-applied `F` position). The guard
        // gives first-binding-wins: an already-bound `F` falls through to the
        // no-op catch-all, exactly like the `Generic` arm.
        (Type::HktVar { name, .. }, Type::Named(a_name, _)) if !bindings.contains_key(name) => {
            bindings.insert(name.clone(), Type::TypeCtor(a_name.clone()));
        }
        // Nested HKT, both sides symbolic with the same already-pinned ctor:
        // `F<A>` vs `F<i64>` ⇒ zip-unify the arguments.
        (Type::HktApp { ctor: fc, args: fa }, Type::HktApp { ctor: ac, args: aa })
            if fc == ac && fa.len() == aa.len() =>
        {
            for (f, a) in fa.iter().zip(aa.iter()) {
                unify_inner(f, a, bindings, true);
            }
        }
        _ => {}
    }
}

pub(super) fn infer_literal_type(literal: &Literal) -> Type {
    match literal {
        // PIL: integer literals are polymorphic, carrying the parsed i64
        // value. Unifies with any machine integer type via
        // `type_compatible`'s IntLit arms (N4-PIL/N5-PIL). Resolves to a
        // concrete type at the containing binding site via the walker
        // (N17-PIL) or defaults to I64 via the final post-pass.
        Literal::Int(n) => Type::IntLit(*n),
        // u256 PR-U2: a wide literal doesn't fit i64, so it is NOT polymorphic —
        // it types directly as `u256` (the only machine type that holds it; i256
        // literals are deferred).
        Literal::Int256(_) => Type::U256,
        Literal::Float(_) => Type::F64,
        Literal::Bool(_) => Type::Bool,
        Literal::Str(_) => Type::Str,
    }
}

// PIL: `coerce_int_literal` helper was DELETED in this PR. Pre-PIL it
// was the in-place type-rewriter for the let-binding + binary-op
// coercion sites; PIL replaces it with first-class polymorphic integer
// literals (`Type::IntLit(i64)`) plus `type_compatible`'s symmetric
// IntLit ↔ machine-integer arms (N4/N5-PIL) and the resolution walker
// (`resolve_int_literals_in_expr` + `default_remaining_int_literals_*`).
// The 4-type range table moved to `int_literal_fits`.

// PR S1 / N5-S1 invariant: `Type::Str` is sendable in S1 under the
// "static-data-backed only" invariant. Pre-S1, Str was a bare i32
// offset into static WASM data, trivially safe to send. Post-S1
// (commit #2 fat-pointer migration), Str is an 8-byte header
// `[data_ptr: u32, len: u32]` allocated per-use via BumpAlloc; the
// `data_ptr` field still points at static data (literals are the only
// Str production path in S1). Cross-actor send carries the HEADER
// pointer; the receiving actor reads `data_ptr` and `len` and follows
// into static memory (shared across actors per existing single-table
// WASM linear memory). PR S2 (owned String via `! { Alloc }`)
// revisits this with ownership-transfer marshalling — owned Strs
// reference per-actor BumpAlloc'd bytes that DON'T cross actor
// boundaries safely, and sending one would require either a deep
// copy or refusing the send. That's documented as AG-S1-I.
pub(super) fn is_send_type(ty: &Type) -> bool {
    match ty {
        Type::Unit
        | Type::Bool
        | Type::I32
        | Type::U32
        | Type::I64
        | Type::U64
        | Type::F64
        | Type::Str
        | Type::Cap(_, _)
        | Type::ActorRef(_)
        | Type::Error => true,
        Type::Array { elem: inner, .. } => is_send_type(inner),
        Type::Named(_, args) => args.iter().all(is_send_type),
        Type::Tuple(elems) => elems.iter().all(is_send_type),
        // u256/i256 are pointer-backed 32-byte cells in per-actor memory; a raw
        // pointer is not portable across actors. Fail-closed (E7) until 32-byte
        // value-serialization lands — analogous to owned Str (AG-S1-I).
        Type::U256 | Type::I256 => false,
        Type::Fn(_, _, _, _) => false, // closures can't cross actor boundaries
        Type::Ref(_, _) | Type::Slice(_) => false, // borrows can't cross actor boundaries
        Type::Ptr(_) | Type::MutPtr(_) => false, // raw pointers can't cross actor boundaries
        Type::Region => false,         // region handles can't cross actor boundaries (AG-2b-3)
        Type::Generic(_) => true,
        // HKT: a higher-kinded var is symbolic (conservatively sendable, joining
        // Generic); an application's sendability follows its arguments; a bare
        // TypeCtor is a transient subst-only target never reached in a real
        // sendable position (conservatively true). These erase before AIR.
        Type::HktVar { .. } | Type::TypeCtor(_) => true,
        // Typestate: a phantom state marker is type-level only (AND-identity over a
        // Named's args). Cross-actor state-laundering is gated separately by T274 (TS4).
        Type::StateMarker(_) => true,
        Type::HktApp { args, .. } => args.iter().all(is_send_type),
        // PIL: IntLit is a polymorphic literal; sendability is whatever
        // the eventual concrete type resolves to. Conservatively treat
        // as sendable (the post-resolution type will be a machine
        // integer, all of which are sendable).
        Type::IntLit(_) => true,
        // Effect Handlers (C-NEVER): the abortive bottom is type-level only and
        // gated before AIR; conservatively not sendable.
        Type::Never => false,
    }
}

pub(super) fn is_runtime_message_abi_type(ty: &Type) -> bool {
    // PIL: IntLit is admitted here — `actor.ask(Handler(4, true), ...)`
    // passes IntLit-typed literal args through the call-site check; the
    // walker resolves IntLit to a concrete machine integer before AIR
    // and the runtime sees the resolved type. Without this, T118 fires
    // with a misleading "found `i64`" message because render_type maps
    // IntLit → "i64".
    matches!(
        ty,
        Type::Bool
            | Type::I32
            | Type::U32
            | Type::I64
            | Type::U64
            | Type::F64
            | Type::IntLit(_)
            | Type::ActorRef(_)
            | Type::Cap(_, _)
            | Type::Error
    )
}

/// PIL: recursively rewrite any nested `Type::IntLit` inside a `Type` to
/// `Type::I64`. Required because IntLit can appear inside compound types
/// like `Array { elem: IntLit, size }`, `Slice(IntLit)`, `Named(_, [IntLit])`,
/// etc. — those would NOT be caught by a top-level `expr.ty == IntLit`
/// check. Used by the final post-pass walker to default orphan IntLits
/// in every position, including nested type-args.
pub(super) fn default_int_lit_in_type(ty: &mut Type) {
    match ty {
        Type::IntLit(_) => *ty = Type::I64,
        Type::Array { elem, .. } => default_int_lit_in_type(elem.as_mut()),
        Type::Slice(inner) | Type::Ref(inner, _) | Type::Ptr(inner) | Type::MutPtr(inner) => {
            default_int_lit_in_type(inner.as_mut());
        }
        Type::Named(_, args) => {
            // Cap's "args" are i64 deadlines (not Types) so they can't
            // contain IntLit and don't need traversal here.
            for arg in args {
                default_int_lit_in_type(arg);
            }
        }
        Type::Fn(params, ret, _, _) => {
            for p in params {
                default_int_lit_in_type(p);
            }
            default_int_lit_in_type(ret.as_mut());
        }
        // ET-1/PIL: a tuple literal `(1, 2)` carries `Tuple([IntLit, IntLit])`
        // as its expr.ty; the orphan defaulter must rewrite each element to I64.
        Type::Tuple(elems) => {
            for e in elems {
                default_int_lit_in_type(e);
            }
        }
        // HKT: an IntLit could ride inside a symbolic application `F<…>`; recurse
        // into the args so it is defaulted like any other position.
        Type::HktApp { args, .. } => {
            for a in args {
                default_int_lit_in_type(a);
            }
        }
        _ => {}
    }
}

/// PIL / N17-PIL: context-sensitive walker that resolves `Type::IntLit`
/// leaves in a TypedExpr tree against a concrete target type. Called
/// from binding sites (check_let, check_return, infer_call_expr's arg
/// loop, infer_record_construct_expr's field loop, infer_array_lit_expr's
/// element loop) after `type_compatible` has succeeded with the same
/// target. A final invocation with target=`Type::I64` at the end of
/// type-check defaults any orphan IntLit.
///
/// PROPAGATES target INTO: binop operands (both `lhs` and `rhs`),
/// because `1 + 2` carries IntLit at the binop's top AND at both
/// operand leaves; without per-leaf rewriting, the operand `LoadField`s
/// would emit against IntLit and AIR's lower_type would ICE (N3-PIL).
///
/// DOES NOT PROPAGATE INTO: call args, method/extern call args, index
/// expressions, field accesses, record-construct fields, array literal
/// elements, slice operator bounds, cast inner expressions, closure
/// constructions, grant/handle/region/declassify bodies — those each
/// have their own targets and resolve INDEPENDENTLY at their own
/// type-check sites against those targets (N17-PIL). SIGIL's if/match
/// are STATEMENTS (not expressions); their branches resolve at the
/// statement-walker level, not via expression-target propagation.
///
/// N20-PIL: range-check happens at EACH IntLit leaf visit, not just at
/// the binding-site outermost expression. Failure at any leaf returns
/// `false` so the caller can emit T243 at the offending leaf's span.
/// The caller is responsible for the diagnostic emission; the walker
/// mutates eagerly so callers see partial progress on failure.
pub(super) fn resolve_int_literals_in_expr(expr: &mut TypedExpr, target: &Type) -> bool {
    let mut ok = true;
    if let Type::IntLit(n) = expr.ty {
        if int_literal_fits(n, target) {
            expr.ty = target.clone();
        } else {
            // Range-fit failure. Leave expr.ty as IntLit so a caller
            // (via `resolve_int_literals_or_reject` /
            // `first_overflowing_int_literal`) can extract the literal
            // value + span for its diagnostic.
            ok = false;
        }
    }
    // Per N17-PIL: propagate target into binop operands only.
    if let TypedExprKind::Binary(bin) = &mut expr.kind {
        ok &= resolve_int_literals_in_expr(&mut bin.lhs, target);
        ok &= resolve_int_literals_in_expr(&mut bin.rhs, target);
    }
    // SIGIL Complete v0 / Phase 1 array-stride fix: when an array/slice
    // literal is checked against an annotated `[T; N]` (let) or `&[T]`
    // (slice-coerced arg/let) slot, propagate the ELEMENT target `T`
    // into each integer-literal element AND into the carried
    // `elem_type`. Without this, an all-int-literal array's `elem_type`
    // (and each element's `.ty`) stays `Type::IntLit` and is later
    // defaulted to `I64` (width 8) by `default_remaining_int_literals_*`.
    // `lower_array_lit` then stores at an 8-byte stride (and as `i64`
    // values) while every reader — `index_base_and_bounds`, the for-in
    // desugar, `.contains` — uses the ANNOTATED element width (e.g.
    // `i32` → 4), corrupting all element access (a[0] coincidentally
    // survives). Resolving BOTH the elements and `elem_type` keeps the
    // stored stride, the stored value's AIR type, and the reader width
    // mutually consistent at the annotated `T`.
    if let TypedExprKind::ArrayLit(arr) = &mut expr.kind {
        let elem_target = match target {
            Type::Array { elem, .. } => Some((**elem).clone()),
            Type::Slice(elem) => Some((**elem).clone()),
            _ => None,
        };
        if let Some(elem_target) = elem_target {
            for elem in &mut arr.elements {
                ok &= resolve_int_literals_in_expr(elem, &elem_target);
            }
            // Resolve the carried `elem_type` (drives AIR storage stride)
            // and keep `expr.ty`'s element in sync. Only rewrite when the
            // current element type is an unresolved `IntLit` so a genuine
            // element-type mismatch on an already-concrete element type
            // (caught elsewhere as T140/T071) is never masked.
            if matches!(arr.elem_type, Type::IntLit(_)) {
                arr.elem_type = elem_target.clone();
            }
            if let Type::Array { elem, .. } = &mut expr.ty
                && matches!(**elem, Type::IntLit(_))
            {
                **elem = elem_target;
            }
        }
    }
    ok
}

/// PIL / N20-PIL follow-through: resolve `Type::IntLit` leaves in `expr`
/// against `target` (delegating to `resolve_int_literals_in_expr`), and
/// REJECT the first leaf that does not fit instead of dropping the
/// failure signal on the floor.
///
/// `resolve_int_literals_in_expr` returns `false` when a binop operand
/// literal overflows `target` — the case the caller's top-level
/// `type_compatible` guard cannot see, because the *outer* expression's
/// IntLit (e.g. `0` in `0 - 2147483648`) fits and is narrowed while the
/// offending leaf (`2147483648`) stays `IntLit`. Left unreported, that
/// leaf is defaulted to i64 by the end-of-typecheck mop-up pass, and AIR
/// then emits a width-mismatched `i32.sub` — an INVALID wasm module that
/// only fails at instantiation. Emitting `code` here turns it into a
/// clean compile error (the "T243 emission deferred to commit #4/#5" the
/// let / arg sites left open as `let _ = …`), so codegen is never
/// reached. `code` is the calling site's own mismatch code (T041 for a
/// let binding, T045 for an assignment, T071 for a call argument /
/// record field), so a binary-leaf overflow reports identically to the
/// single-literal `let n: i32 = 2147483648` case.
pub(super) fn resolve_int_literals_or_reject(
    expr: &mut TypedExpr,
    target: &Type,
    code: codes::DiagnosticCode,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if resolve_int_literals_in_expr(expr, target) {
        return;
    }
    // `resolve_int_literals_in_expr` returned false: some IntLit leaf did
    // not fit `target`. Only a CONCRETE machine-integer target has a
    // finite range a literal can actually overflow. When `target` is
    // itself `Type::IntLit` — an un-annotated `let seed = 1;`, whose
    // inferred binding type IS the value's own IntLit — or `Type::Error`
    // from an upstream failure, `int_literal_fits` returns false for
    // EVERY leaf, which is benign: the leaves stay IntLit and default to
    // i64 later, exactly as the pre-fix `let _ = resolve(…)` allowed.
    // Don't manufacture an out-of-range diagnostic there. (`resolve`
    // above still ran for its leaf-narrowing side effect in every case.)
    if !matches!(target, Type::I32 | Type::U32 | Type::I64 | Type::U64) {
        return;
    }
    if let Some((value, span)) = first_overflowing_int_literal(expr, target) {
        diagnostics.push(Diagnostic::error(
            code,
            format!(
                "integer literal `{value}` is out of range for `{}`",
                render_type(target)
            ),
            Some(span),
        ));
    }
}

/// Find the first `Type::IntLit` leaf in `expr` — top-level or a binop
/// operand, mirroring `resolve_int_literals_in_expr`'s recursion — whose
/// value does not fit `target`. Walked only on the failure path (after
/// `resolve_int_literals_in_expr` returned `false`), so the second walk
/// is off the happy path. Returns the literal value + its span for the
/// diagnostic.
fn first_overflowing_int_literal(expr: &TypedExpr, target: &Type) -> Option<(i64, Span)> {
    if let Type::IntLit(n) = expr.ty
        && !int_literal_fits(n, target)
    {
        return Some((n, expr.span));
    }
    if let TypedExprKind::Binary(bin) = &expr.kind {
        return first_overflowing_int_literal(&bin.lhs, target)
            .or_else(|| first_overflowing_int_literal(&bin.rhs, target));
    }
    None
}

/// PIL: default-fallback variant of the walker that rewrites any IntLit
/// in the typed_ast to `Type::I64`. Called as the final pass at the end
/// of type-check (compile_source_with_options) to mop up orphan
/// IntLits — e.g., expression statements whose value is discarded, or
/// any IntLit that escaped a binding-site resolution. Always succeeds
/// because every i64 literal value trivially fits I64.
///
/// Differs from `resolve_int_literals_in_expr` only in (a) target is
/// hard-coded I64, (b) recurses into EVERY sub-expression position (not
/// just binop operands) to guarantee no orphan IntLit slips through to
/// AIR's lower_type ICE (N3-PIL backstop).
pub(super) fn default_remaining_int_literals_in_expr(expr: &mut TypedExpr) {
    // Rewrite IntLit at every depth inside expr.ty (top-level OR nested
    // inside Array { elem: IntLit, ... }, Slice(IntLit), Named with
    // IntLit type-arg, Fn signature with IntLit param/ret, etc.).
    default_int_lit_in_type(&mut expr.ty);
    // Recurse into every sub-expression position. The walker doesn't
    // know about target propagation here — it's just hunting for orphan
    // IntLits and defaulting them.
    match &mut expr.kind {
        TypedExprKind::Literal(_) | TypedExprKind::Local(_) | TypedExprKind::StateField(_) => {}
        TypedExprKind::Binary(b) => {
            default_remaining_int_literals_in_expr(&mut b.lhs);
            default_remaining_int_literals_in_expr(&mut b.rhs);
        }
        TypedExprKind::Call(c) => {
            for arg in &mut c.args {
                default_remaining_int_literals_in_expr(arg);
            }
        }
        // Effect Handlers (EH3, C-VIS): descend into the new nodes' sub-expressions.
        TypedExprKind::Perform(p) => {
            for arg in &mut p.args {
                default_remaining_int_literals_in_expr(arg);
            }
        }
        TypedExprKind::ClauseHandle(c) => {
            default_remaining_int_literals_in_expr(&mut c.scrutinee);
            for clause in &mut c.clauses {
                default_remaining_int_literals_in_block(&mut clause.body);
            }
        }
        TypedExprKind::Resume(r) => {
            default_remaining_int_literals_in_expr(&mut r.value);
        }
        TypedExprKind::IndirectCall(c) => {
            for arg in &mut c.args {
                default_remaining_int_literals_in_expr(arg);
            }
        }
        TypedExprKind::Intrinsic(i) => {
            for arg in &mut i.args {
                default_remaining_int_literals_in_expr(arg);
            }
        }
        TypedExprKind::ResultCtor(r) => {
            default_remaining_int_literals_in_expr(&mut r.value);
        }
        TypedExprKind::EnumConstruct(e) => {
            for payload in &mut e.fields {
                default_remaining_int_literals_in_expr(payload);
            }
        }
        TypedExprKind::Try(t) => {
            default_remaining_int_literals_in_expr(&mut t.value);
        }
        TypedExprKind::Send(s) => {
            for arg in &mut s.args {
                default_remaining_int_literals_in_expr(arg);
            }
        }
        TypedExprKind::Ask(a) => {
            for arg in &mut a.args {
                default_remaining_int_literals_in_expr(arg);
            }
        }
        TypedExprKind::Spawn(s) => {
            for arg in &mut s.args {
                default_remaining_int_literals_in_expr(arg);
            }
        }
        TypedExprKind::RecordConstruct(r) => {
            for (_, field_expr) in &mut r.fields {
                default_remaining_int_literals_in_expr(field_expr);
            }
        }
        TypedExprKind::FieldAccess(f) => {
            default_remaining_int_literals_in_expr(&mut f.object);
        }
        TypedExprKind::CapRestrict(_) => {}
        TypedExprKind::CapSplit(s) => {
            default_remaining_int_literals_in_expr(&mut s.amount);
        }
        TypedExprKind::CapDraw(d) => {
            default_remaining_int_literals_in_expr(&mut d.amount);
        }
        TypedExprKind::Mint(m) => {
            default_remaining_int_literals_in_expr(&mut m.target);
        }
        TypedExprKind::ArrayLit(a) => {
            // PIL: TypedArrayLitExpr carries `elem_type: Type` separately
            // from each element's `.ty`. AIR's `lower_array_lit` calls
            // `lower_type(&array_lit.elem_type)` to compute per-element
            // width; if elem_type carries IntLit, that ICEs (N3-PIL).
            // Walk both the elem_type AND each element.
            default_int_lit_in_type(&mut a.elem_type);
            for elem in &mut a.elements {
                default_remaining_int_literals_in_expr(elem);
            }
        }
        // PR-E3: default int-literals inside f-string interpolation holes.
        TypedExprKind::FString(fs) => {
            for part in &mut fs.parts {
                if let crate::typed_ast::TypedFStringPart::Hole(h) = part {
                    default_remaining_int_literals_in_expr(h);
                }
            }
        }
        TypedExprKind::Index(idx) => {
            // PIL: TypedIndexExpr also carries `elem_type` for AIR
            // load-element width computation.
            default_int_lit_in_type(&mut idx.elem_type);
            default_remaining_int_literals_in_expr(&mut idx.array);
            default_remaining_int_literals_in_expr(&mut idx.index);
        }
        TypedExprKind::Slice(s) => {
            // PIL: TypedSliceExpr also carries `elem_type`.
            default_int_lit_in_type(&mut s.elem_type);
            default_remaining_int_literals_in_expr(&mut s.array);
            if let Some(start) = &mut s.start {
                default_remaining_int_literals_in_expr(start.as_mut());
            }
            if let Some(end) = &mut s.end {
                default_remaining_int_literals_in_expr(end.as_mut());
            }
        }
        // PIL: closure construction lambdas are lifted to top-level
        // TypedFunction entries during type-check; the lifted body is
        // walked separately via `default_remaining_int_literals_in_function`.
        // Nothing to do here.
        TypedExprKind::ClosureConstruct(_) => {}
        TypedExprKind::Borrow(b) => {
            default_remaining_int_literals_in_expr(&mut b.inner);
        }
        TypedExprKind::Grant(g) => {
            default_remaining_int_literals_in_expr(&mut g.cap);
            default_remaining_int_literals_in_expr(&mut g.body);
        }
        TypedExprKind::Handle(h) => {
            default_remaining_int_literals_in_block(&mut h.body);
        }
        TypedExprKind::Declassify(d) => {
            default_remaining_int_literals_in_expr(&mut d.value);
            default_remaining_int_literals_in_expr(&mut d.cap);
        }
        TypedExprKind::DeclassifyCt(d) => {
            default_remaining_int_literals_in_expr(&mut d.value);
            default_remaining_int_literals_in_expr(&mut d.cap);
        }
        TypedExprKind::ExternCall(e) => {
            for arg in &mut e.args {
                default_remaining_int_literals_in_expr(arg);
            }
        }
        TypedExprKind::Region(r) => {
            default_remaining_int_literals_in_expr(&mut r.limit);
            default_remaining_int_literals_in_block(&mut r.body);
        }
    }
}

/// PIL: per-statement walker. Recurses into nested expressions and
/// blocks. Used by both `default_remaining_int_literals_in_block`
/// (for TypedBlock.statements) and `ForIn`'s `body: Vec<TypedStmt>`.
pub(super) fn default_remaining_int_literals_in_stmt(stmt: &mut TypedStmt) {
    match stmt {
        TypedStmt::Let(l) => {
            // The let-binding's own .ty may carry IntLit when the
            // binding was unannotated (e.g., `let arr = [10, 20, 30];`
            // — the array's element-type unified to IntLit). Default it
            // here so downstream consumers (mostly AIR lowering of
            // local references) see a concrete type.
            default_int_lit_in_type(&mut l.ty);
            default_remaining_int_literals_in_expr(&mut l.value);
        }
        TypedStmt::Assign(a) => default_remaining_int_literals_in_expr(&mut a.value),
        TypedStmt::Expr(e) => default_remaining_int_literals_in_expr(&mut e.expr),
        TypedStmt::If(i) => {
            default_remaining_int_literals_in_expr(&mut i.condition);
            default_remaining_int_literals_in_block(&mut i.then_branch);
            default_remaining_int_literals_in_block(&mut i.else_branch);
        }
        TypedStmt::Match(m) => {
            default_remaining_int_literals_in_expr(&mut m.scrutinee);
            for arm in &mut m.arms {
                if let Some(g) = &mut arm.guard {
                    default_remaining_int_literals_in_expr(g);
                }
                default_remaining_int_literals_in_block(&mut arm.body);
            }
        }
        TypedStmt::While(w) => {
            default_remaining_int_literals_in_expr(&mut w.condition);
            default_remaining_int_literals_in_block(&mut w.body);
        }
        TypedStmt::ForIn(f) => {
            default_remaining_int_literals_in_expr(&mut f.iterable);
            // ForIn's body is Vec<TypedStmt> directly (not TypedBlock).
            for body_stmt in &mut f.body {
                default_remaining_int_literals_in_stmt(body_stmt);
            }
        }
        TypedStmt::ForRange(f) => {
            default_remaining_int_literals_in_expr(&mut f.start);
            default_remaining_int_literals_in_expr(&mut f.end);
            for body_stmt in &mut f.body {
                default_remaining_int_literals_in_stmt(body_stmt);
            }
        }
        TypedStmt::Return(r) => {
            if let Some(v) = &mut r.value {
                default_remaining_int_literals_in_expr(v);
            }
        }
        // break/continue have no int literals to default.
        TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
    }
}

/// PIL: recursive walker over a TypedBlock that defaults all orphan
/// IntLits to I64. Walks every statement; for each, recurses into its
/// expression(s) and nested blocks. Companion to
/// `default_remaining_int_literals_in_expr`.
pub(super) fn default_remaining_int_literals_in_block(block: &mut TypedBlock) {
    for stmt in &mut block.statements {
        default_remaining_int_literals_in_stmt(stmt);
    }
}

/// PIL / N4-PIL: range-check helper for `Type::IntLit` unification.
/// Returns `true` iff the literal value `n` fits in the destination's
/// integer range. Used by `type_compatible`'s IntLit arms.
///
/// The 4 type ranges (mirror of the deleted `coerce_int_literal`'s
/// in-range check, lifted into a reusable predicate per N4-PIL):
/// - `I64`: always fits (i64 is the lexer's parse target).
/// - `U64`: requires `n >= 0` (u64 values > i64::MAX are unreachable
///   from an i64 literal — out-of-range literals are rejected at the
///   parser level).
/// - `I32`: `[i32::MIN, i32::MAX]` cast to i64 bounds.
/// - `U32`: `[0, u32::MAX]` cast to i64 bounds.
///
/// Non-integer targets return `false` — IntLit doesn't unify with
/// Bool/Str/Named/etc.
pub(super) fn int_literal_fits(n: i64, target: &Type) -> bool {
    match target {
        Type::I64 => true,
        Type::U64 => n >= 0,
        Type::I32 => n >= (i32::MIN as i64) && n <= (i32::MAX as i64),
        Type::U32 => n >= 0 && n <= (u32::MAX as i64),
        // u256 PR-U2 (E9): a small NON-NEGATIVE integer literal coerces into
        // u256 context (`let balance: u256 = 0;`). i256 stays inert (no literal
        // coercion) until it has value-semantics.
        Type::U256 => n >= 0,
        _ => false,
    }
}

pub(crate) fn type_compatible(expected: &Type, actual: &Type) -> bool {
    match (expected, actual) {
        (Type::Error, _) | (_, Type::Error) => true,
        // PR A: same-named Type::Generic comparisons are legitimate
        // inside the body of a generic impl method, where field
        // access on `self: Holder<T>` returns `T` and the method's
        // declared return type is also `T`. Pre-PR-A this always
        // ICEd because no body-level generic context existed; PR
        // #73 added generic impl bodies but the type_compatible
        // defense wasn't updated. We accept Generic == Generic when
        // the names match (they're the same parameter in scope).
        (Type::Generic(a), Type::Generic(b)) => a == b,
        (Type::Generic(_), _) | (_, Type::Generic(_)) => {
            panic!("ICE: Type::Generic escaped monomorphization into type_compatible")
        }
        // HKT (EX-4/V3): higher-kinded types are check-time-only and MUST be erased
        // to a concrete Type::Named before any concrete compatibility check. A
        // same-shape symbolic pair is legitimate inside a (future) symbolic
        // generic-over-F body — accept by structural equality, exactly like the
        // Generic == Generic carve-out above; any other pairing means an HKT var
        // escaped monomorphization → ICE (never the silent `_ => expected==actual`).
        (Type::HktVar { .. } | Type::HktApp { .. } | Type::TypeCtor(_), _)
        | (_, Type::HktVar { .. } | Type::HktApp { .. } | Type::TypeCtor(_))
            if expected == actual =>
        {
            true
        }
        (Type::HktVar { .. } | Type::HktApp { .. } | Type::TypeCtor(_), _)
        | (_, Type::HktVar { .. } | Type::HktApp { .. } | Type::TypeCtor(_)) => {
            panic!("ICE: HKT type escaped monomorphization into type_compatible")
        }
        // Typestate (ST-3): state markers compare by EXACT equality — `File<Open>`
        // ≠ `File<Closed>` (the invariant we want), `File<Open>` = `File<Open>`.
        // A REAL arm, NOT an ICE: markers flow through here as `Named` args on every
        // typestate comparison (the Named arm recurses `type_compatible` over args).
        // A marker vs a non-marker falls to the structural catch-all → unequal → false.
        (Type::StateMarker(a), Type::StateMarker(b)) => a == b,
        // PIL / N5-PIL: IntLit ↔ IntLit always compatible REGARDLESS
        // of value equality (N16-PIL: no value-equality check). Both
        // sides are polymorphic; the walker resolves them at the
        // containing binding site's target.
        (Type::IntLit(_), Type::IntLit(_)) => true,
        // PIL / N4-PIL: symmetric IntLit ↔ machine-integer unification
        // with per-literal range-check via `int_literal_fits`.
        // Non-machine-integer targets return false (no implicit
        // conversion to Bool, Str, etc.).
        (Type::IntLit(n), target) | (target, Type::IntLit(n)) => int_literal_fits(*n, target),
        // Wall 2 Stage 1: deadline-typed capability subtyping.
        // The covariant rule is `Cap(N, Some(D_a)) <: Cap(N, Some(D_b))`
        // iff `D_a >= D_b` — a longer-lived cap is acceptable wherever
        // a shorter-lived one is required, but not the reverse.
        // Non-parametric forms are NEVER compatible with parametric
        // forms (the `_ => false` arm in cap_subtype is load-bearing).
        (Type::Cap(_, _), Type::Cap(_, _)) => cap_subtype(actual, expected),
        (Type::Named(n1, a1), Type::Named(n2, a2)) => {
            n1 == n2
                && a1.len() == a2.len()
                && a1.iter().zip(a2.iter()).all(|(e, a)| type_compatible(e, a))
        }
        // SIGIL Complete v0 / Phase 1.1: array size MUST match (per
        // T227). Pre-v0 the size field was discarded via `..`, which
        // made `LengthOf` refinements and every fixed-size-array
        // contract unsound. Slice coercion (`&[T; N] -> &[T]`) is
        // handled by the dedicated Slice-vs-Array arm below; this
        // arm is array-to-array only.
        (
            Type::Array {
                elem: expected_elem,
                size: expected_size,
            },
            Type::Array {
                elem: actual_elem,
                size: actual_size,
            },
        ) => expected_size == actual_size && type_compatible(expected_elem, actual_elem),
        // HOF / N4-HOF: Type::Fn linearity respected. A linear
        // closure (`Type::Fn(_, _, true)` — captures cap values)
        // CANNOT satisfy a non-linear parameter (`Type::Fn(_, _, false)`).
        // Reverse direction (non-linear satisfying linear) is OK
        // (a multi-use closure trivially satisfies a single-use
        // requirement; FnOnce-subtypes-Fn pattern).
        //
        // T237 is emitted at the call site when the rejection is on
        // this linearity dimension specifically (see infer_call_expr's
        // arg-loop; the call-site code distinguishes T237 from T071
        // by re-checking is_linear).
        (
            Type::Fn(p1, r1, is_linear_expected, eff_expected),
            Type::Fn(p2, r2, is_linear_actual, eff_actual),
        ) => {
            // Linearity rule: passing a linear closure to a non-linear
            // parameter is rejected; all other combinations OK.
            // Equivalent to !(*is_linear_actual && !*is_linear_expected)
            // but clippy::nonminimal_bool prefers the De Morgan form.
            let linearity_ok = !*is_linear_actual || *is_linear_expected;
            // Effect rule (AG-HOF-A): a closure may perform NO MORE than the arrow it is
            // being passed as promises, so the row is CONTRAVARIANT in the actual type.
            // `{} ⊆ {Alloc}` — a pure closure satisfies an effectful arrow. `{Alloc} ⊄ {}`
            // — an effectful closure does NOT satisfy a pure one. Without this check the
            // annotation is a laundering channel: assigning an effectful closure to a
            // pure-typed parameter would erase the row the `IndirectCall` gate reads.
            let effects_ok = eff_actual.is_subset_of(eff_expected);
            linearity_ok
                && effects_ok
                && p1.len() == p2.len()
                && p1.iter().zip(p2.iter()).all(|(e, a)| type_compatible(e, a))
                && type_compatible(r1, r2)
        }
        (Type::Ref(a, _), Type::Ref(b, _)) => type_compatible(a, b),
        (Type::Slice(a), Type::Slice(b)) => type_compatible(a, b),
        // &[T; N] is compatible with &[T] (slice coercion)
        (
            Type::Slice(expected_elem),
            Type::Array {
                elem: actual_elem, ..
            },
        ) => type_compatible(expected_elem, actual_elem),
        // Tuples: arity must match exactly AND every position is compatible.
        (Type::Tuple(e_elems), Type::Tuple(a_elems)) => {
            e_elems.len() == a_elems.len()
                && e_elems
                    .iter()
                    .zip(a_elems.iter())
                    .all(|(e, a)| type_compatible(e, a))
        }
        _ => expected == actual,
    }
}

/// SIGIL Complete v0 / Phase 1.1 helper: detect the array-size-only
/// mismatch sub-case. Returns `Some((expected_size, actual_size))` iff
/// both `expected` and `actual` are `Type::Array` with the SAME element
/// type but DIFFERENT sizes. The element-type match is required so the
/// helper doesn't shadow generic type-mismatch diagnostics on
/// `[i64; 3]` vs `[Str; 3]` cases.
///
/// Per N3-V0, call sites that emit a generic `T071`-shaped type-mismatch
/// after a `!type_compatible(...)` check route through this helper FIRST;
/// `Some(_)` → emit `T227` with the named-size detail, `None` → fall
/// back to the generic mismatch.
pub(super) fn try_array_size_mismatch_detail(expected: &Type, actual: &Type) -> Option<(u32, u32)> {
    match (expected, actual) {
        (
            Type::Array {
                elem: expected_elem,
                size: expected_size,
            },
            Type::Array {
                elem: actual_elem,
                size: actual_size,
            },
        ) if type_compatible(expected_elem, actual_elem) && expected_size != actual_size => {
            Some((*expected_size, *actual_size))
        }
        _ => None,
    }
}

/// SIGIL Complete v0 / Phase 1.1: emit a `T227` array-size-mismatch
/// diagnostic at the given span if the (expected, actual) pair is an
/// array-size-only mismatch; returns `None` otherwise (caller should
/// fall back to the generic type-mismatch path).
pub(super) fn try_array_size_mismatch_diagnostic(
    expected: &Type,
    actual: &Type,
    context: &str,
    span: crate::span::Span,
) -> Option<Diagnostic> {
    let (expected_size, actual_size) = try_array_size_mismatch_detail(expected, actual)?;
    Some(Diagnostic::error(
        codes::T227,
        format!(
            "{context}: array size mismatch — expected `{}`, found `{}` ({} elements vs {} elements)",
            render_type(expected),
            render_type(actual),
            expected_size,
            actual_size,
        ),
        Some(span),
    ))
}

/// Wall 2 → Wall 3: parametric cap subtyping rule.
///
/// `cap_subtype(actual, expected)` is true iff `actual` is acceptable
/// wherever `expected` is required. All-positions covariance: each
/// `actual[i] >= expected[i]`.
///
///   * Names must match exactly.
///   * Arities (`Vec` lengths) must match exactly. The arity check is
///     load-bearing (MC-1 fence) — without it, a `zip`-based loop
///     would silently truncate to the shorter Vec and accept mixed
///     arities. Mixed parametric/non-parametric forms become the
///     special case `0 vs N != 0`.
///   * Every position satisfies `actual >= expected`. Reflexivity
///     (`Cap(name, vec) <: Cap(name, vec)`) holds for any vec because
///     `>=` is reflexive on i64 (INV-15 fence).
pub(crate) fn cap_subtype(actual: &Type, expected: &Type) -> bool {
    let (Type::Cap(a_name, a_vec), Type::Cap(e_name, e_vec)) = (actual, expected) else {
        return false;
    };
    if a_name != e_name {
        return false;
    }
    // MC-1 fence: arity check FIRST.
    if a_vec.len() != e_vec.len() {
        return false;
    }
    // All-positions covariance.
    a_vec.iter().zip(e_vec.iter()).all(|(a, e)| a >= e)
}

/// Wall 2 Stage 1: route same-name cap mismatches to T195 with a
/// deadline-specific message. Returns `Some(diagnostic)` when both
/// types are `Type::Cap` with the same name but incompatible
/// deadline / parametric shapes. Callers fall through to their
/// existing generic diagnostic (T071, T095, etc.) when this returns
/// `None`.
///
/// The message contains the variable name, the actual and expected
/// deadlines (when present), the site context, and a fix template
/// — all four pieces are mandated by INV-8 and pinned by message-
/// content tests in `tests/diagnostic_messages.rs`.
/// Typestate (Epic 1, T266): if `expected` and `actual` are the SAME typestate
/// nominal differing only in a STATE-position marker (`File<Open>` vs
/// `File<Closed>`), produce the protocol-aware wrong-state diagnostic. Returns
/// `None` for a non-typestate or different-nominal mismatch — the caller then emits
/// its generic T071. `site_context` names the operation, e.g. "function `read`".
pub(super) fn try_state_mismatch_diagnostic(
    expected: &Type,
    actual: &Type,
    universe: &TypeUniverse,
    site_context: &str,
    span: Span,
) -> Option<Diagnostic> {
    let (Type::Named(e_name, e_args), Type::Named(a_name, a_args)) = (expected, actual) else {
        return None;
    };
    if e_name != a_name {
        return None;
    }
    let positions = universe.typestate_state_positions.get(e_name)?;
    for &i in positions {
        if let (Some(Type::StateMarker(want)), Some(Type::StateMarker(found))) =
            (e_args.get(i), a_args.get(i))
            && want != found
        {
            return Some(Diagnostic::error(
                codes::T266,
                format!(
                    "{site_context} requires `{e_name}` in state `{want}`, found state `{found}`"
                ),
                Some(span),
            ));
        }
    }
    None
}

pub(super) fn try_cap_deadline_diagnostic(
    expected: &Type,
    actual: &Type,
    var_name: &str,
    site_context: &str,
    span: Span,
) -> Option<Diagnostic> {
    let (Type::Cap(e_name, e_vec), Type::Cap(a_name, a_vec)) = (expected, actual) else {
        return None;
    };
    // Different cap names: a regular type-name mismatch, not a
    // deadline issue. Let the caller emit its generic diagnostic.
    if e_name != a_name {
        return None;
    }
    let e_arity = e_vec.len();
    let a_arity = a_vec.len();
    // Both non-parametric: no T195 — caller's generic path handles
    // other shapes.
    if e_arity == 0 && a_arity == 0 {
        return None;
    }
    let fix_hint = "widen the target's expected deadline at each failing position so the source cap is acceptable, or narrow the source cap with `restrict_deadline(...)` (single-parameter only)";
    let message = if a_arity != e_arity {
        // Arity mismatch: surface alongside T201.
        format!(
            "capability `{var_name}` has arity {a_arity} but {site_context} expects arity {e_arity}; parametric and non-parametric forms (and different parameter counts) are distinct types"
        )
    } else {
        // Same arity, same name — at least one position fails
        // covariance. MC-3 fence: enumerate EVERY failing position.
        let mut failures: Vec<String> = Vec::new();
        for (idx, (a, e)) in a_vec.iter().zip(e_vec.iter()).enumerate() {
            if a < e {
                failures.push(format!("position {idx} ({a} < required {e})"));
            }
        }
        if failures.is_empty() {
            return None; // No failures — caller's check was redundant.
        }
        format!(
            "deadline-typed capability `{var_name}` cannot satisfy {site_context}: covariance fails at {}",
            failures.join(", ")
        )
    };
    Some(Diagnostic::error_with_hint(
        codes::T195,
        message,
        Some(span),
        fix_hint.to_owned(),
    ))
}

pub(super) fn is_machine_integer_type(ty: &Type) -> bool {
    // PIL: `Type::IntLit` is included here because IntLit unifies with
    // any machine integer type via `type_compatible`'s symmetric arms
    // (N4-PIL). Sites that test "is this an integer type?" — array
    // index, range bound, fuel-draw amount, timeout — should accept
    // IntLit at type-check time; the resolution walker rewrites IntLit
    // to a concrete machine integer before AIR lowering. Per N6-PIL,
    // refinement-LHS predicates remain STRICTLY `matches!(_, Type::I64)`
    // and do NOT route through this helper.
    matches!(
        ty,
        Type::I32 | Type::U32 | Type::I64 | Type::U64 | Type::IntLit(_) | Type::Error
    )
}

/// ErrorCode is u32 — the only error type allowed to cross the ring boundary.
pub(super) fn is_error_code_type(ty: &Type) -> bool {
    matches!(ty, Type::U32 | Type::Error)
}

/// True if `ty` is a capability or transitively contains one (array of
/// caps, tuple/closure carrying a cap, generic instantiation with a cap
/// argument, etc.). Used by T183 (record fields), T184 (enum payloads),
/// T186 (array elements), and T242 (generic-aggregate instantiation) —
/// every aggregate slot that, when projected/destructured/indexed/called,
/// yields a cap whose restriction provenance Z3's authority tracker loses
/// (it sees a fresh full-authority cap). The recursion MUST cover every
/// OWNED-value position; a missing arm silently reopens the smuggling
/// channel those gates exist to close.
///
/// Does NOT count references (`&Fuel`), slices, or raw pointers as
/// containing a cap — those are borrows / pointers tracked by the
/// ownership system, not owned linear values. `Tuple` and `Fn`, by
/// contrast, ARE owned positions: a `(Fuel, i64)` field destructures to a
/// fresh cap binding, and a `Fn(Fuel) -> _` / `Fn(_) -> Fuel` closure
/// passes or produces a cap across the indirect-call boundary — so both
/// are counted (params AND return for `Fn`).
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn type_contains_cap(ty: &Type) -> bool {
    match ty {
        Type::Cap(_, _) => true,
        Type::Array { elem, .. } => type_contains_cap(elem),
        Type::Named(_, args) => args.iter().any(type_contains_cap),
        Type::Tuple(elems) => elems.iter().any(type_contains_cap),
        Type::Fn(params, ret, _, _) => {
            params.iter().any(type_contains_cap) || type_contains_cap(ret)
        }
        // HKT (INV-4, cap-smuggling defense): an application's cap content follows
        // its arguments — a cap hidden in `F<cap Fuel>` must be found. A symbolic
        // var / bare ctor carries no cap. (Defense-in-depth: the inner construction
        // is already blocked by T186/T242, but this closes the walker arm.)
        Type::HktApp { args, .. } => args.iter().any(type_contains_cap),
        Type::HktVar { .. } | Type::TypeCtor(_) => false,
        // Borrow/pointer channels — deliberately NOT cap-carrying (see the fn
        // doc: a cap cannot be consumed through a borrow; raw pointers are
        // extern-context-gated).
        Type::Ref(_, _) | Type::Slice(_) | Type::Ptr(_) | Type::MutPtr(_) => false,
        // Leaves: no nested type to carry an owned cap. Every arm is explicit
        // (no `_`) so a future `Type` variant fails to compile here until it
        // is classified — the "walker forgot an arm" defense (F005). The
        // historical Tuple/Fn miss behind T183/T184/T186/T242 smuggling was
        // exactly a wildcard swallowing a new aggregate.
        Type::Unit
        | Type::Bool
        | Type::I32
        | Type::U32
        | Type::I64
        | Type::U64
        | Type::F64
        | Type::U256
        | Type::I256
        | Type::Str
        | Type::Generic(_)
        | Type::ActorRef(_)
        | Type::Region
        | Type::IntLit(_)
        | Type::StateMarker(_)
        | Type::Never
        | Type::Error => false,
    }
}

/// F003 / value-position `trap()` (Tier A): true if `ty` IS, or transitively
/// CONTAINS, the bottom type `Never` — the type of a diverging expression
/// (`trap()`, an abortive `perform`). `Never` has NO value, so it is legal ONLY
/// as a bare expression STATEMENT (`trap();`), where the return checker reads it
/// as a terminating path (SC-1, see `check_block`). Used AS a value — bound to a
/// `let`, stored in a tuple/array element, or passed as a call/record/enum
/// argument — it must be REJECTED at type-check (T279), because a residual
/// `Never` reaching AIR's `lower_type`/`mangle_type` hits the C-NEVER backstop
/// `panic!` (an ICE / release DoS on legal-looking source).
///
/// UNLIKE `type_contains_cap` (which skips `Ref`/`Slice`/`Ptr` because a cap
/// cannot be consumed through a borrow), this is an ICE-PREVENTION gate: it walks
/// EVERY structural carrier `lower_type`/`mangle_type` recurses through, so no
/// residual `Never` can slip past any channel. False positives are impossible —
/// no legal type contains `Never` (it originates only from `trap()` / an abortive
/// `perform`), so the wider walk is pure defense-in-depth.
///
/// TOTAL match, no `_` arm (the F005 "walker forgot an arm" defense): a future
/// `Type` variant that carries a nested type fails to compile here until it is
/// classified, instead of silently failing OPEN (returning `false` and letting a
/// hidden `Never` ride into `mangle_type`/`lower_type`'s ICE).
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn type_contains_never(ty: &Type) -> bool {
    match ty {
        Type::Never => true,
        Type::Array { elem, .. } => type_contains_never(elem),
        Type::Named(_, args) => args.iter().any(type_contains_never),
        Type::Tuple(elems) => elems.iter().any(type_contains_never),
        Type::Fn(params, ret, _, _) => {
            params.iter().any(type_contains_never) || type_contains_never(ret)
        }
        Type::Ref(inner, _) | Type::Slice(inner) | Type::Ptr(inner) | Type::MutPtr(inner) => {
            type_contains_never(inner)
        }
        Type::HktApp { args, .. } => args.iter().any(type_contains_never),
        // Leaves: no nested type to carry a `Never`. `Error` is deliberately
        // `false` — it is the cascade-suppressing POISON the T279 sites rewrite
        // a `Never` into, so treating it as never-free is what prevents
        // double-diagnosis.
        Type::Unit
        | Type::Bool
        | Type::I32
        | Type::U32
        | Type::I64
        | Type::U64
        | Type::F64
        | Type::U256
        | Type::I256
        | Type::Str
        | Type::Generic(_)
        | Type::Cap(_, _)
        | Type::ActorRef(_)
        | Type::Region
        | Type::IntLit(_)
        | Type::HktVar { .. }
        | Type::TypeCtor(_)
        | Type::StateMarker(_)
        | Type::Error => false,
    }
}

/// Typestate (TS4, ST-6 / BL-2): true if `ty` IS, or transitively CONTAINS (through
/// the same aggregate channels as `type_contains_cap`), a TYPESTATE nominal — a type
/// declared with a `@S` state parameter (`File<Open>`, `File<Closed>`, `File<S>`,
/// bare `File`). Such values are AFFINE (Linear, TS2); storing one in an aggregate
/// (record field / enum payload / array / generic-aggregate) and extracting it twice
/// via LoadField/destructure/Index would mint two handles from one and DEFEAT the
/// use-after-transition guarantee (the exact smuggle `T183` closes for caps). The
/// boring limit is to forbid the storage outright (`T275`). Mirrors the
/// `type_contains_cap` walker arm-for-arm; keyed on the universe (NOT the
/// `StateMarker` arg) so a state-polymorphic field `File<S>` is caught too.
/// Ref/Slice are NOT smuggle channels (a borrow can't be consumed), matching caps.
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn type_contains_typestate(ty: &Type, universe: &TypeUniverse) -> bool {
    match ty {
        Type::Named(name, args) => {
            universe.typestate_state_positions.contains_key(name)
                || args.iter().any(|a| type_contains_typestate(a, universe))
        }
        Type::Array { elem, .. } => type_contains_typestate(elem, universe),
        Type::Tuple(elems) => elems.iter().any(|e| type_contains_typestate(e, universe)),
        Type::Fn(params, ret, _, _) => {
            params.iter().any(|p| type_contains_typestate(p, universe))
                || type_contains_typestate(ret, universe)
        }
        Type::HktApp { args, .. } => args.iter().any(|a| type_contains_typestate(a, universe)),
        // Ref/Slice are NOT smuggle channels (a borrow can't be consumed),
        // matching caps; raw pointers are extern-context-gated.
        Type::Ref(_, _) | Type::Slice(_) | Type::Ptr(_) | Type::MutPtr(_) => false,
        // Leaves. `StateMarker` itself is `false` on purpose — this walker
        // keys on the typestate NOMINAL (via `universe`), not the phantom
        // marker arg (see the fn doc). Explicit arms, no `_`: the "walker
        // forgot an arm" defense (F005).
        Type::Unit
        | Type::Bool
        | Type::I32
        | Type::U32
        | Type::I64
        | Type::U64
        | Type::F64
        | Type::U256
        | Type::I256
        | Type::Str
        | Type::Generic(_)
        | Type::Cap(_, _)
        | Type::ActorRef(_)
        | Type::Region
        | Type::IntLit(_)
        | Type::HktVar { .. }
        | Type::TypeCtor(_)
        | Type::StateMarker(_)
        | Type::Never
        | Type::Error => false,
    }
}

/// True if `ty` IS, or transitively CONTAINS, a 256-bit integer (`u256`/`i256`).
/// Walks tuples, arrays, refs/slices/ptrs, Fn params+return, and — via `universe`
/// — record fields and enum payloads (with generic substitution), so a u256
/// hidden in `record Pair { x: u256 }` or `(u256, i64)` is found. A `seen` set
/// breaks cycles on self-/mutually-recursive records (which the language allows).
///
/// Used by the `==`/`!=` fail-closed guard (E3/E6): a bare `u256 == u256` is
/// value-compared by the `lower_binary_expr` fast-path, but every OTHER wide-int
/// comparison shape (a bare `i256`, or a u256/i256 nested in an aggregate) would
/// otherwise fall through to pointer-eq — silently wrong for value types.
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn type_contains_wide_int(ty: &Type, universe: &TypeUniverse) -> bool {
    fn inner(
        ty: &Type,
        universe: &TypeUniverse,
        seen: &mut std::collections::HashSet<String>,
    ) -> bool {
        match ty {
            Type::U256 | Type::I256 => true,
            Type::Array { elem, .. } => inner(elem, universe, seen),
            Type::Tuple(elems) => elems.iter().any(|e| inner(e, universe, seen)),
            Type::Ref(t, _) | Type::Slice(t) | Type::Ptr(t) | Type::MutPtr(t) => {
                inner(t, universe, seen)
            }
            Type::Fn(params, ret, _, _) => {
                params.iter().any(|p| inner(p, universe, seen)) || inner(ret, universe, seen)
            }
            Type::Named(name, args) => {
                if args.iter().any(|a| inner(a, universe, seen)) {
                    return true;
                }
                // Cycle guard: a self-/mutually-recursive record adds no new field
                // types on revisit, so returning false there is sound.
                if !seen.insert(name.clone()) {
                    return false;
                }
                if let Some((type_params, fields)) = universe.records.get(name) {
                    let subst: HashMap<String, Type> = type_params
                        .iter()
                        .cloned()
                        .zip(args.iter().cloned())
                        .collect();
                    return fields
                        .iter()
                        .any(|(_, ft)| inner(&apply_subst(ft, &subst), universe, seen));
                }
                if let Some((type_params, variants)) = universe.enums.get(name) {
                    let subst: HashMap<String, Type> = type_params
                        .iter()
                        .cloned()
                        .zip(args.iter().cloned())
                        .collect();
                    return variants.iter().any(|(_, payloads)| {
                        payloads
                            .iter()
                            .any(|p| inner(&apply_subst(p, &subst), universe, seen))
                    });
                }
                false
            }
            // HKT application: erased before any reachable `==`/`!=` site,
            // but classified (recurse args) rather than wildcarded — the
            // "walker forgot an arm" defense (F005).
            Type::HktApp { args, .. } => args.iter().any(|a| inner(a, universe, seen)),
            // Leaves: no nested type to carry a 256-bit integer. Explicit
            // arms, no `_` — a future `Type` variant must be classified here
            // before this compiles.
            Type::Unit
            | Type::Bool
            | Type::I32
            | Type::U32
            | Type::I64
            | Type::U64
            | Type::F64
            | Type::Str
            | Type::Generic(_)
            | Type::Cap(_, _)
            | Type::ActorRef(_)
            | Type::Region
            | Type::IntLit(_)
            | Type::HktVar { .. }
            | Type::TypeCtor(_)
            | Type::StateMarker(_)
            | Type::Never
            | Type::Error => false,
        }
    }
    inner(ty, universe, &mut std::collections::HashSet::new())
}

/// True if values of type `ty` can be reassigned via `let mut x: T = ...; x = ...;`
/// without breaking borrow-tracker invariants (INV-1), capability linearity, or
/// the Z3 authority tracker (INV-3). Walks user-defined records and enums via
/// `universe` so refs hidden inside named aggregates are also rejected — a
/// `record Wrapper { r: &i64 }` correctly comes out non-reassignable even
/// though `Wrapper` itself is `Type::Named("Wrapper", [])`.
///
/// Rejects: any type that transitively owns a capability, a borrow, a slice,
/// a raw pointer, a function value, or a generic type variable.
/// Accepts: primitives, ActorRef, arrays of reassignable elements, and user-
/// defined records/enums whose entire structural footprint is reassignable
/// after generic substitution.
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn type_is_reassignable(ty: &Type, universe: &TypeUniverse) -> bool {
    match ty {
        Type::Unit
        | Type::Bool
        | Type::I32
        | Type::U32
        | Type::I64
        | Type::U64
        | Type::F64
        // u256/i256 own no cap/borrow; reassigning rebinds the pointer to a
        // fresh cell (the immutable-value discipline) — freely reassignable.
        | Type::U256
        | Type::I256
        | Type::Str
        | Type::ActorRef(_)
        | Type::Error => true,
        // PIL: IntLit is a polymorphic integer literal; reassignability
        // follows the eventual concrete machine integer type (all of
        // which are reassignable). Accept.
        Type::IntLit(_) => true,
        Type::Cap(_, _)
        | Type::Ref(_, _)
        | Type::Slice(_)
        | Type::Ptr(_)
        | Type::MutPtr(_)
        | Type::Fn(_, _, _, _)
        // Regions (DEF-2b, NC-2b-2): a `Region` value is second-class — a fixed handle,
        // never reassigned (`let mut r: Region; r = …` is rejected).
        | Type::Region
        // HKT: a higher-kinded var/app/ctor is symbolic (conservatively
        // non-reassignable, joining Generic); it erases before AIR.
        | Type::HktVar { .. }
        | Type::HktApp { .. }
        | Type::TypeCtor(_)
        | Type::Generic(_) => false,
        // Typestate (TS0): a phantom state marker is NEUTRAL to reassignability
        // (AND-identity over Named args) — `File<Open>` reassigns exactly like
        // `File`. The TS4 policy "typestate nominals are non-reassignable" (ST-6)
        // keys on the nominal NAME, not on this marker arg.
        Type::StateMarker(_) => true,
        // Effect Handlers (C-NEVER): the abortive bottom is gated before AIR;
        // conservatively non-reassignable (joins Generic).
        Type::Never => false,
        Type::Array { elem, .. } => type_is_reassignable(elem, universe),
        Type::Tuple(elems) => elems.iter().all(|e| type_is_reassignable(e, universe)),
        Type::Named(name, args) => {
            if !args.iter().all(|a| type_is_reassignable(a, universe)) {
                return false;
            }
            // PR B commit #4: the hardcoded `if name == "Result"` special
            // case was deleted here. Pre-PR-B, Result lived only as a
            // compiler-internal `Type::Named("Result", _)` shape — it
            // wasn't in `universe.enums` so the generic enum branch
            // below couldn't see it, hence the bespoke return-true.
            // With PR B's ambient stdlib include, `universe.enums`
            // now contains Result whenever any input source uses
            // `Ok(...)` / `Err(...)` / `?` — so the generic branch
            // handles Result uniformly. The compiler's hardcoded
            // Result-shape (TypedExprKind::ResultCtor, AIR
            // lower_result_ctor's is_ok-tagged flat layout, the `?`
            // operator's special unification) is PRESERVED per the
            // PR B Hybrid scope; only this reassignability fallback
            // gets removed.
            if let Some((type_params, fields)) = universe.records.get(name) {
                let subst: HashMap<String, Type> = type_params
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect();
                return fields.iter().all(|(_, field_ty)| {
                    type_is_reassignable(&apply_subst(field_ty, &subst), universe)
                });
            }
            if let Some((type_params, variants)) = universe.enums.get(name) {
                let subst: HashMap<String, Type> = type_params
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect();
                return variants.iter().all(|(_, payloads)| {
                    payloads.iter().all(|payload_ty| {
                        type_is_reassignable(&apply_subst(payload_ty, &subst), universe)
                    })
                });
            }
            // Unknown named type — be conservative.
            false
        }
    }
}

/// Why a type was rejected for reassignment. Drives the branched T043 message.
pub(super) enum ReassignRejection {
    CapBearing,
    RefBearing,
    Other,
}

pub(super) fn classify_reassign_rejection(ty: &Type, universe: &TypeUniverse) -> ReassignRejection {
    fn walk(ty: &Type, universe: &TypeUniverse) -> Option<ReassignRejection> {
        match ty {
            Type::Cap(_, _) => Some(ReassignRejection::CapBearing),
            Type::Ref(_, _) | Type::Slice(_) => Some(ReassignRejection::RefBearing),
            Type::Ptr(_) | Type::MutPtr(_) | Type::Fn(_, _, _, _) | Type::Generic(_) => {
                Some(ReassignRejection::Other)
            }
            Type::Array { elem, .. } => walk(elem, universe),
            Type::Tuple(elems) => {
                for e in elems {
                    if let Some(r) = walk(e, universe) {
                        return Some(r);
                    }
                }
                None
            }
            Type::Named(name, args) => {
                for arg in args {
                    if let Some(r) = walk(arg, universe) {
                        return Some(r);
                    }
                }
                // PR B commit #4: hardcoded `if name == "Result"`
                // special case deleted here (symmetric with
                // `type_is_reassignable`). With ambient stdlib
                // include, Result is in `universe.enums` and the
                // generic enum branch below handles it uniformly.
                if let Some((type_params, fields)) = universe.records.get(name) {
                    let subst: HashMap<String, Type> = type_params
                        .iter()
                        .cloned()
                        .zip(args.iter().cloned())
                        .collect();
                    for (_, field_ty) in fields {
                        if let Some(r) = walk(&apply_subst(field_ty, &subst), universe) {
                            return Some(r);
                        }
                    }
                    return None;
                }
                if let Some((type_params, variants)) = universe.enums.get(name) {
                    let subst: HashMap<String, Type> = type_params
                        .iter()
                        .cloned()
                        .zip(args.iter().cloned())
                        .collect();
                    for (_, payloads) in variants {
                        for payload_ty in payloads {
                            if let Some(r) = walk(&apply_subst(payload_ty, &subst), universe) {
                                return Some(r);
                            }
                        }
                    }
                    return None;
                }
                Some(ReassignRejection::Other)
            }
            _ => None,
        }
    }
    walk(ty, universe).unwrap_or(ReassignRejection::Other)
}

pub(super) fn render_type(ty: &Type) -> String {
    match ty {
        Type::Unit => "unit".to_owned(),
        Type::Bool => "bool".to_owned(),
        Type::I32 => "i32".to_owned(),
        Type::U32 => "u32".to_owned(),
        Type::I64 => "i64".to_owned(),
        Type::U64 => "u64".to_owned(),
        Type::F64 => "f64".to_owned(),
        Type::U256 => "u256".to_owned(),
        Type::I256 => "i256".to_owned(),
        Type::Str => "str".to_owned(),
        Type::Generic(name) => name.clone(),
        Type::Named(name, args) if args.is_empty() => name.clone(),
        Type::Named(name, args) => {
            let arg_strs: Vec<String> = args.iter().map(render_type).collect();
            format!("{}<{}>", name, arg_strs.join(", "))
        }
        Type::Tuple(elems) => {
            let strs: Vec<String> = elems.iter().map(render_type).collect();
            format!("({})", strs.join(", "))
        }
        Type::Cap(name, params) if params.is_empty() => name.clone(),
        Type::Cap(name, params) => {
            // Positional rendering, MC-5 fence.
            let vals = params
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!("{name}({vals})")
        }
        Type::ActorRef(actor) => format!("ActorRef<{actor}>"),
        Type::Array { elem, size } => format!("[{}; {}]", render_type(elem), size),
        Type::Ref(inner, false) => format!("&{}", render_type(inner)),
        Type::Ref(inner, true) => format!("&mut {}", render_type(inner)),
        Type::Slice(inner) => format!("&[{}]", render_type(inner)),
        Type::Fn(params, ret, _, effects) => {
            let param_strs: Vec<String> = params.iter().map(render_type).collect();
            // Mark a non-empty latent row. `render_type` has no `EffectRegistry`, so the
            // effects cannot be NAMED here — but rendering nothing is strictly worse: an
            // effect-row mismatch would otherwise print as
            // "expected fn(i64) -> i64, found fn(i64) -> i64", which reads as a
            // contradiction. The marker at least tells the reader the mismatch is the
            // effect dimension; the E001 path names the specific effects.
            let row = if effects.effects.is_empty() {
                String::new()
            } else {
                " ! { .. }".to_owned()
            };
            format!(
                "fn({}) -> {}{}",
                param_strs.join(", "),
                render_type(ret),
                row
            )
        }
        Type::Ptr(inner) => format!("Ptr<{}>", render_type(inner)),
        Type::MutPtr(inner) => format!("MutPtr<{}>", render_type(inner)),
        Type::Region => "Region".to_owned(),
        // HKT: render `F`, `F<A>`, or the bare constructor name for diagnostics.
        Type::HktVar { name, .. } => name.clone(),
        Type::HktApp { ctor, args } => {
            let arg_strs: Vec<String> = args.iter().map(render_type).collect();
            format!("{}<{}>", ctor, arg_strs.join(", "))
        }
        Type::TypeCtor(name) => name.clone(),
        // Typestate: render the bare marker name (`File<Open>` shows `Open` via the
        // Named arm's arg rendering).
        Type::StateMarker(name) => name.clone(),
        Type::Never => "never".to_owned(),
        // PIL: polymorphic integer literal renders as "i64" in
        // diagnostics — IntLit eventually defaults to I64 (or coerces
        // to a wider integer type) via the resolution walker, so
        // showing the user a polymorphic-internal name like
        // `<int literal N>` would be confusing. Diagnostics that
        // specifically need the literal value (e.g., T243 range-fit
        // failure) use the value directly via `int_literal_fits`'s
        // inputs, not via render_type.
        Type::IntLit(_) => "i64".to_owned(),
        Type::Error => "<error>".to_owned(),
    }
}

pub(super) fn render_binary_op(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Add => "+",
        BinaryOp::Sub => "-",
        BinaryOp::Mul => "*",
        BinaryOp::Div => "/",
        BinaryOp::Mod => "%",
        BinaryOp::Shl => "<<",
        BinaryOp::Shr => ">>",
        BinaryOp::BitAnd => "&",
        BinaryOp::BitOr => "|",
        BinaryOp::LogicalAnd => "&&",
        BinaryOp::LogicalOr => "||",
        BinaryOp::Lt => "<",
        BinaryOp::LtEq => "<=",
        BinaryOp::Gt => ">",
        BinaryOp::GtEq => ">=",
        BinaryOp::Eq => "==",
        BinaryOp::NotEq => "!=",
    }
}

pub(super) fn render_literal(literal: &Literal) -> String {
    match literal {
        Literal::Int(value) => value.to_string(),
        // u256 PR-U2: render a wide literal as big-endian hex (a faithful,
        // dependency-free rendering for diagnostics).
        Literal::Int256(l) => format!("0x{:016x}{:016x}{:016x}{:016x}", l[3], l[2], l[1], l[0]),
        Literal::Float(value) => value.to_string(),
        Literal::Bool(value) => value.to_string(),
        Literal::Str(value) => format!("\"{value}\""),
    }
}

#[cfg(test)]
mod ptr_walker_tests {
    //! F1 regression (bug sweep): the structural type-walkers must recurse into
    //! `Ptr`/`MutPtr` exactly as they do for `Ref`/`Slice`. A missed arm leaves a
    //! nested `Type::Generic` unsubstituted, which later ICEs in `mangle_type`
    //! (air.rs: `panic!("ICE: unresolved generic …")`).
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn apply_subst_recurses_through_ptr_and_mutptr() {
        let subst = HashMap::from([("T".to_string(), Type::I64)]);

        assert_eq!(
            apply_subst(&Type::Ptr(Box::new(Type::Generic("T".to_string()))), &subst),
            Type::Ptr(Box::new(Type::I64)),
        );
        assert_eq!(
            apply_subst(
                &Type::MutPtr(Box::new(Type::Generic("T".to_string()))),
                &subst
            ),
            Type::MutPtr(Box::new(Type::I64)),
        );

        // Deeply nested: Ptr<(T, &T)> must substitute every occurrence.
        let nested = Type::Ptr(Box::new(Type::Tuple(vec![
            Type::Generic("T".to_string()),
            Type::Ref(Box::new(Type::Generic("T".to_string())), false),
        ])));
        let expected = Type::Ptr(Box::new(Type::Tuple(vec![
            Type::I64,
            Type::Ref(Box::new(Type::I64), false),
        ])));
        assert_eq!(apply_subst(&nested, &subst), expected);
    }

    #[test]
    fn unify_inner_binds_generic_through_ptr_and_mutptr() {
        let mut b = HashMap::new();
        unify_inner(
            &Type::Ptr(Box::new(Type::Generic("T".to_string()))),
            &Type::Ptr(Box::new(Type::U64)),
            &mut b,
            false,
        );
        assert_eq!(b.get("T"), Some(&Type::U64));

        let mut b2 = HashMap::new();
        unify_inner(
            &Type::MutPtr(Box::new(Type::Generic("U".to_string()))),
            &Type::MutPtr(Box::new(Type::Bool)),
            &mut b2,
            false,
        );
        assert_eq!(b2.get("U"), Some(&Type::Bool));
    }
}

/// Walker-fence truth tables (the "walker forgot an arm" class, F005 —
/// PRs #29/#89/#343/#418/#463): pin the SEMANTIC classification of every
/// structural channel for the universe-free security walkers. The
/// compile-time half of the fence is the walkers' TOTAL matches (a new
/// `Type` variant fails to compile until classified); this pins the runtime
/// half, so a future arm can't be mis-classified without a red test.
#[cfg(test)]
mod walker_fence_tests {
    use super::*;

    fn cap() -> Type {
        Type::Cap("Fuel".into(), Vec::new())
    }

    #[test]
    fn cap_walker_finds_every_owned_channel() {
        assert!(type_contains_cap(&cap()));
        assert!(type_contains_cap(&Type::Array {
            elem: Box::new(cap()),
            size: 2,
        }));
        assert!(type_contains_cap(&Type::Named("Box".into(), vec![cap()])));
        assert!(type_contains_cap(&Type::Tuple(vec![Type::I64, cap()])));
        // Nested aggregate — the recursion must descend.
        assert!(type_contains_cap(&Type::Tuple(vec![Type::Tuple(vec![
            cap()
        ])])));
        // Closure: param AND return position.
        assert!(type_contains_cap(&Type::Fn(
            vec![cap()],
            Box::new(Type::I64),
            false,
            EffectSet::empty()
        )));
        assert!(type_contains_cap(&Type::Fn(
            vec![],
            Box::new(cap()),
            false,
            EffectSet::empty()
        )));
        // HKT application (INV-4).
        assert!(type_contains_cap(&Type::HktApp {
            ctor: "F".into(),
            args: vec![cap()],
        }));
    }

    #[test]
    fn cap_walker_borrow_and_pointer_exclusions_hold() {
        // Documented exclusions: a cap cannot be CONSUMED through a borrow;
        // raw pointers are extern-context-gated. If one of these flips to
        // true, the borrow story changed — re-audit T183/T184/T186/T242 and
        // the ownership tracker TOGETHER, not just this table.
        assert!(!type_contains_cap(&Type::Ref(Box::new(cap()), false)));
        assert!(!type_contains_cap(&Type::Ref(Box::new(cap()), true)));
        assert!(!type_contains_cap(&Type::Slice(Box::new(cap()))));
        assert!(!type_contains_cap(&Type::Ptr(Box::new(cap()))));
        assert!(!type_contains_cap(&Type::MutPtr(Box::new(cap()))));
    }

    #[test]
    fn cap_walker_leaves_are_cap_free() {
        for leaf in [
            Type::Unit,
            Type::Bool,
            Type::I32,
            Type::U32,
            Type::I64,
            Type::U64,
            Type::F64,
            Type::U256,
            Type::I256,
            Type::Str,
            Type::Generic("T".into()),
            Type::ActorRef("A".into()),
            Type::Region,
            Type::IntLit(7),
            Type::HktVar {
                name: "F".into(),
                arity: 1,
            },
            Type::TypeCtor("Vec".into()),
            Type::StateMarker("Open".into()),
            Type::Never,
            Type::Error,
        ] {
            assert!(!type_contains_cap(&leaf), "{leaf:?} must not carry a cap");
        }
    }

    #[test]
    fn never_walker_walks_every_structural_carrier() {
        assert!(type_contains_never(&Type::Never));
        assert!(type_contains_never(&Type::Ref(
            Box::new(Type::Never),
            false
        )));
        assert!(type_contains_never(&Type::Slice(Box::new(Type::Never))));
        assert!(type_contains_never(&Type::Ptr(Box::new(Type::Never))));
        assert!(type_contains_never(&Type::MutPtr(Box::new(Type::Never))));
        assert!(type_contains_never(&Type::Tuple(vec![
            Type::I64,
            Type::Never
        ])));
        assert!(type_contains_never(&Type::Fn(
            vec![Type::Never],
            Box::new(Type::Unit),
            false,
            EffectSet::empty()
        )));
        assert!(type_contains_never(&Type::HktApp {
            ctor: "F".into(),
            args: vec![Type::Never],
        }));
        // The poison rule: `Error` is deliberately never-free (it is the
        // cascade-suppressing poison T279 sites rewrite a Never into).
        assert!(!type_contains_never(&Type::Error));
    }
}
