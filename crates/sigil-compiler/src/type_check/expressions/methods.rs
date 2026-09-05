//! Method-call rerouting, built-ins, user methods, and associated functions.

use std::collections::HashMap;

use super::super::resolve::{
    apply_subst, build_mono_impl_method_mangled_name, is_machine_integer_type, render_type,
    type_compatible, unify,
};
use super::super::statements::{self, check_function_block};
use super::super::{
    FunctionSig, MAX_MONOMORPH_DEPTH, MonomorphTracker, ParamRegion, RegionId, Type,
    TypeCheckContext, make_array_len_refinement, make_first_last_result, resolve_effect_row,
    universe,
};
use super::{
    infer_arg_with_expected, infer_call_expr, infer_expr, type_is_concrete, type_mentions_generic,
};
use crate::ast::{Literal, MethodCallExpr};
use crate::diagnostics::{Diagnostic, Severity, codes};
use crate::typed_ast::{
    TypedCallExpr, TypedExpr, TypedExprKind, TypedFunction, TypedFunctionKind, TypedIntrinsicExpr,
    TypedIntrinsicKind, TypedParam,
};

fn try_reroute_method_call_expr(
    expr: &MethodCallExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<TypedExpr> {
    let universe = context.universe;
    // PR B / N14-PRB: enum-variant qualified construction reroute.
    // The parser produces a MethodCallExpr for `Option::Some(42)`
    // because `parse_path_from_first` collects all `::`-joined
    // segments greedily then `try_parse_actor_op_expr` peels the
    // last segment as the "method" and routes through method-call
    // dispatch. Before doing module-name disambiguation (below),
    // check whether this is actually a qualified enum-variant
    // constructor — if the receiver is a 1-segment path matching
    // a known enum name, reroute to `infer_call_expr` with a
    // synthesized 2-segment Path callee. The Fallback 2 block in
    // `infer_call_expr` then performs the variant lookup uniformly
    // with bare-variant calls, preserving N14-PRB's "qualified and
    // bare produce identical TypedExpr shape" invariant. When
    // `expr.method` is NOT a variant of the named enum, the
    // routing still fires so that T072 (unknown variant) emerges
    // from the canonical site rather than T060 ("undefined local")
    // from the fallthrough method-call dispatch.
    if let crate::ast::Expr::Path(receiver_path) = expr.receiver.as_ref() {
        let segs = &receiver_path.path.segments;
        if segs.len() == 1
            && let Some(qualifier) = segs.first()
            && universe.enums.contains_key(qualifier)
        {
            // Rebuild as `Expr::Call { callee: Path[qualifier, method], args }`
            // and route through `infer_call_expr`. The synthetic
            // CallExpr borrows `args` via clone to avoid lifetime
            // gymnastics; arg expressions are typically small and
            // this only fires on the qualified-variant path.
            let synthetic_callee = crate::ast::Path {
                segments: vec![qualifier.clone(), expr.method.clone()],
                type_args: vec![],
                span: expr.span,
            };
            let synthetic_call = crate::ast::CallExpr {
                callee: synthetic_callee,
                args: expr.args.clone(),
                span: expr.span,
            };
            return Some(infer_call_expr(
                &synthetic_call,
                env,
                current_return,
                context,
                tracker,
                diagnostics,
            ));
        }
    }

    None
}

pub(super) fn infer_method_call_expr(
    expr: &MethodCallExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let (function_sigs, _actor_sigs, module_name, universe) = context.parts();
    if let Some(rerouted) =
        try_reroute_method_call_expr(expr, env, current_return, context, tracker, diagnostics)
    {
        return rerouted;
    }

    // PR C1: type-name → associated-function reroute. `Vec::new()` parses as a
    // MethodCallExpr with a 1-segment Path receiver. If that name is a record
    // (not shadowed by a local) and the named impl method takes no `self`, this
    // is an associated-function call (e.g. a constructor) — resolve it through
    // the impl registry rather than treating `Vec` as a value/module. Must run
    // BEFORE the module-name reroute below: a record name is not a module, so
    // that path would reject it and fall through to receiver inference → T060.
    // (Self-methods invoked as `Vec::push(v, x)` are NOT rerouted here — they
    // fall through; AG-C1.)
    if let crate::ast::Expr::Path(receiver_path) = expr.receiver.as_ref()
        && receiver_path.path.segments.len() == 1
        && let Some(type_name) = receiver_path.path.segments.first()
        && universe.records.contains_key(type_name)
        && !env.contains_key(type_name)
    {
        // CF-C1: a local impl wins; otherwise exactly one sibling module may
        // define the associated function (cross-module / ambient `Vec`). The
        // sig is OWNED so the `&workspace_sigs` borrow ends before the mono.
        let assoc_key = format!("{type_name}::{}", expr.method);
        let resolved: Option<FunctionSig> = match function_sigs.get(&assoc_key) {
            Some(s) => Some(s.clone()),
            None => match crate::type_check::call_resolve::resolve_impl_member_global(
                &assoc_key,
                module_name,
                tracker,
            ) {
                crate::type_check::call_resolve::GlobalImplVerdict::Found(s) => Some(s),
                crate::type_check::call_resolve::GlobalImplVerdict::Ambiguous(mods) => {
                    diagnostics.push(Diagnostic::error(
                        codes::T244,
                        format!(
                            "ambiguous associated function `{}` for type `{type_name}`: defined in modules [{}]; a type's impl must live in exactly one module",
                            expr.method,
                            mods.join(", ")
                        ),
                        Some(expr.span),
                    ));
                    return TypedExpr {
                        ty: Type::Error,
                        kind: TypedExprKind::Literal(Literal::Int(0)),
                        span: expr.span,
                        refinement: None,
                    };
                }
                crate::type_check::call_resolve::GlobalImplVerdict::None => None,
            },
        };
        // Reroute ONLY a no-`self` associated fn (AG-C1). A self-method invoked
        // as `Vec::push(v, x)` falls through to the normal dispatch paths.
        // BoundedVec PR-0a: keyed on `sig.is_associated` (set at sig collection
        // from the method's first param ≠ `self`) so a CONCRETE record's `::new()`
        // resolves, not only a generic impl's (the generic path's sigs are
        // is_associated too, so it is unchanged). The outer guard already
        // restricts this arm to record TYPE names (`universe.records` + not a
        // shadowing local), so it never captures an enum-variant ctor or module.
        if let Some(sig) = resolved
            && sig.is_associated
        {
            return infer_associated_fn_call(
                type_name,
                &sig,
                expr,
                env,
                current_return,
                context,
                tracker,
                diagnostics,
            );
        }
    }

    // Phase 5a: the parser produces MethodCall for both `obj.method(args)`
    // (true method call) and `module::fn(args)` / `crate::module::fn(args)`
    // (cross-module function call) because `parse_path_from_first` treats
    // `::` and `.` as equivalent path separators. Disambiguate semantically:
    // if the receiver is a Path with 1 segment (module) or 2 segments
    // (crate::module) AND the first segment looks like a module name (not
    // a local variable), route to cross-module function dispatch.
    if let crate::ast::Expr::Path(receiver_path) = expr.receiver.as_ref() {
        let segs = &receiver_path.path.segments;
        let first = segs.first();
        let module_segment = match segs.len() {
            1 => first.cloned(), // `module::method(...)`
            // `crate::module::method(...)` — pull the module out of the
            // 2-segment receiver. The crate segment is informational
            // (we have one crate today, conventionally `sigil`).
            2 => segs.get(1).cloned(),
            _ => None,
        };
        if let Some(receiver_module) = module_segment {
            // Only route if receiver isn't shadowed by a local variable
            // AND the segment looks like a module (in workspace, or a
            // use-imported alias, or a self-reference).
            let is_module = receiver_module == module_name
                || tracker
                    .workspace_sigs
                    .contains_key(receiver_module.as_str())
                || tracker.current_use_scope.lookup(&receiver_module).is_some();
            let is_shadowed = first.map(|f| env.contains_key(f.as_str())).unwrap_or(false);
            // Phase 5a-1.6 / I21: reroute trace event with the decision
            // outcome. Helps engineers debug why a `obj.method(args)`
            // call was treated one way vs. the other.
            let reroute_outcome = match (is_module, is_shadowed) {
                (true, false) => crate::trace::RerouteOutcome::Routed,
                (true, true) => crate::trace::RerouteOutcome::ShadowedRejected,
                (false, _) => crate::trace::RerouteOutcome::NotModule,
            };
            crate::trace::reroute(&crate::trace::MethodCallReroute {
                caller_module: module_name,
                receiver: &receiver_module,
                method: &expr.method,
                outcome: reroute_outcome,
                span: expr.span,
            });
            if is_module && !is_shadowed {
                return infer_cross_module_call_via_methodcall(
                    &receiver_module,
                    expr,
                    env,
                    current_return,
                    context,
                    tracker,
                    diagnostics,
                );
            }
            // Module name shadowed by a local: by lexical scoping the NEAREST
            // binding wins when it can actually service the call. Speculatively
            // resolve `local.method(args)` into a scratch buffer and COMMIT it
            // iff the resolution is fully clean (no error diagnostics, non-Error
            // type) — e.g. stdlib `let bi: i64 = ...; bi.as_u64()` co-compiled
            // with a user `module bi;` (any of the ~dozens of short stdlib
            // method-receiver locals collide this way; a foreign frontend emits
            // such module names from user file stems). SOUND BY CONSTRUCTION:
            // this branch previously ALWAYS errored (T156), so committing only
            // widens acceptance on an always-error path — no program that
            // compiled before resolves differently — and the committed path is
            // the ordinary, fully type/cap/effect-checked local method
            // resolution. On the discard path compilation fails with T156, so
            // any speculative tracker state is unreachable (errors abort
            // pre-AIR). TWO LOAD-BEARING INVARIANTS (adversarial review
            // P6/P7, pinned by `mono_poison_rejected_in_both_orderings`):
            // (1) the speculation threads the REAL tracker, so a discarded
            // run still populates the mono cache — safe ONLY because the
            // discard always leaves T156 in the main buffer; (2) a commit
            // may cache-hit a mono instance whose body-check errored at an
            // EARLIER unshadowed site — safe ONLY because that first
            // instantiation left its Error in the main buffer. A refactor
            // that reorders/parallelizes function checking or dedups
            // diagnostics must re-establish both.
            if is_module && is_shadowed {
                // SPELLING GATE: the parser folds `.` and `::` into one path
                // shape, but the spelling carries intent — `helpers::f(x)` /
                // `sigil::m::f(x)` is module/path syntax, and letting a
                // shadowing local capture it would be a silent wrong-target
                // resolution (the local's method, a field chain, or even a
                // primitive builtin would hijack an explicitly-qualified
                // call, and the T156 hint's own `sigil::m::f(...)` bypass
                // would be self-defeating). Only a `.`-spelled call may
                // resolve to the local; `::` keeps T156 fail-closed.
                if !expr.colon_spelled {
                    let mut scratch: Vec<Diagnostic> = Vec::new();
                    let spec_receiver = infer_expr(
                        &expr.receiver,
                        env,
                        current_return,
                        context,
                        tracker,
                        &mut scratch,
                    );
                    if !matches!(spec_receiver.ty, Type::Error) {
                        let resolved = try_infer_builtin_method_expr(
                            expr,
                            env,
                            current_return,
                            context,
                            tracker,
                            &mut scratch,
                            spec_receiver,
                        );
                        let clean = !matches!(resolved.ty, Type::Error)
                            && scratch.iter().all(|d| d.severity() != Severity::Error);
                        if clean {
                            // Propagate any non-error scratch diagnostics
                            // (warnings).
                            diagnostics.extend(scratch);
                            return resolved;
                        }
                    }
                }
                // T156: the local CANNOT service the call (its type lacks the
                // method / the resolution errored) — the module was plausibly
                // intended. Fire proactively so the user gets a helpful
                // diagnostic instead of a confusing T132 ("no method `read` on
                // type `<X>`"). The speculative diagnostics are discarded: the
                // shadowing itself is the actionable error.
                diagnostics.push(Diagnostic::error(
                    codes::T156,
                    format!(
                        "module `{}` is shadowed by a local variable of the same name; rename the local, or qualify the call as `sigil::{}::{}(...)` to bypass the local-name lookup",
                        receiver_module, receiver_module, expr.method
                    ),
                    Some(expr.span),
                ));
                return TypedExpr {
                    ty: Type::Error,
                    kind: TypedExprKind::Literal(Literal::Int(0)),
                    span: expr.span,

                    refinement: None,
                };
            }
        }
    }

    let receiver = infer_expr(
        &expr.receiver,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );

    try_infer_builtin_method_expr(
        expr,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
        receiver,
    )
}

fn try_infer_builtin_method_expr(
    expr: &MethodCallExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
    receiver: TypedExpr,
) -> TypedExpr {
    let universe = context.universe;
    // PR AF / N24-AF: intrinsic pre-check for array/slice methods.
    // Strict type-match against `Type::Array { .. } | Type::Slice(_)`
    // (no Named/Ref wrapping per N24-AF) ensures a user-defined
    // `impl Wrap { fn len(...) -> i64 }` over a record wrapping an
    // array continues to dispatch via function_sigs. `expr.args`
    // must be empty (both `.len()` and `.is_empty()` are zero-arg).
    if expr.args.is_empty() {
        match (&receiver.ty, expr.method.as_str()) {
            (Type::Array { size, .. }, "len") => {
                let size = *size;
                // V10 / N16-AF: attach `@ == size` refinement via
                // the single canonical builder (returns
                // `Option<Vec<...>>`) and use field-shorthand
                // `refinement,` per the Wall 4 Step 2 V10 lint.
                let refinement = make_array_len_refinement(size, expr.span);
                return TypedExpr {
                    ty: Type::U32,
                    kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                        kind: TypedIntrinsicKind::ArrayLen { size },
                        args: vec![receiver],
                    }),
                    span: expr.span,
                    refinement,
                };
            }
            (Type::Slice(_), "len") => {
                return TypedExpr {
                    ty: Type::U32,
                    kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                        kind: TypedIntrinsicKind::SliceLen,
                        args: vec![receiver],
                    }),
                    span: expr.span,
                    refinement: None,
                };
            }
            (Type::Array { size, .. }, "is_empty") => {
                let size = *size;
                return TypedExpr {
                    ty: Type::Bool,
                    kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                        kind: TypedIntrinsicKind::ArrayIsEmpty { size },
                        args: vec![receiver],
                    }),
                    span: expr.span,
                    refinement: None,
                };
            }
            (Type::Slice(_), "is_empty") => {
                return TypedExpr {
                    ty: Type::Bool,
                    kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                        kind: TypedIntrinsicKind::SliceIsEmpty,
                        args: vec![receiver],
                    }),
                    span: expr.span,
                    refinement: None,
                };
            }
            // PR S1 / N6-S1: Str intrinsics. The receiver is a
            // fat-pointer header (per N17-S1); AIR loads the
            // len/data_ptr fields via STR_LEN_OFFSET / STR_DATA_PTR_OFFSET.
            (Type::Str, "len") => {
                return TypedExpr {
                    ty: Type::I64,
                    kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                        kind: TypedIntrinsicKind::StrLen,
                        args: vec![receiver],
                    }),
                    span: expr.span,
                    refinement: None,
                };
            }
            // N-LEX: `s.as_output() -> i64` — pack the str header into the forge
            // ABI's output return `(data_ptr << 32) | len`. The inner-ring,
            // FFI-free way for a pure-SIGIL tool to emit a built `str` as its
            // byte output (the differential lexer harness's token-stream
            // transfer). See TypedIntrinsicKind::StrAsOutput.
            (Type::Str, "as_output") => {
                return TypedExpr {
                    ty: Type::I64,
                    kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                        kind: TypedIntrinsicKind::StrAsOutput,
                        args: vec![receiver],
                    }),
                    span: expr.span,
                    refinement: None,
                };
            }
            (Type::Str, "is_empty") => {
                return TypedExpr {
                    ty: Type::Bool,
                    kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                        kind: TypedIntrinsicKind::StrIsEmpty,
                        args: vec![receiver],
                    }),
                    span: expr.span,
                    refinement: None,
                };
            }
            // PR P16 commit #3 / N15-P16 + Phase-1 completion: `.first()`
            // and `.last()` on Array (compile-time fold) AND Slice (runtime
            // branch) via the canonical builder `make_first_last_result` —
            // single attachment site for all four. The Array fold is
            // byte-identical to before; the Slice path emits a
            // `SliceFirst`/`SliceLast` intrinsic (runtime `if len==0` branch).
            (Type::Array { .. } | Type::Slice(_), "first") => {
                return make_first_last_result(
                    receiver,
                    /* is_first = */ true,
                    universe,
                    diagnostics,
                    expr.span,
                );
            }
            (Type::Array { .. } | Type::Slice(_), "last") => {
                return make_first_last_result(
                    receiver,
                    /* is_first = */ false,
                    universe,
                    diagnostics,
                    expr.span,
                );
            }
            _ => {}
        }
    }

    // Phase-3 / integer width conversions: `n.as_i32()` / `.as_u32()` /
    // `.as_i64()` / `.as_u64()` on any machine-int receiver → an `IntConvert`
    // intrinsic. Result type = the target width; the source width is frozen
    // from the receiver so AIR can pick wrap/extend/copy. Zero-arg, pure (no
    // cap). Placed before the `.contains` / `.byte_at` / str-method arms; a
    // non-`as_*` method on an int receiver falls through unchanged.
    if expr.args.is_empty()
        && matches!(
            &receiver.ty,
            Type::I32 | Type::U32 | Type::I64 | Type::U64 | Type::IntLit(_)
        )
    {
        let target: Option<Type> = match expr.method.as_str() {
            "as_i32" => Some(Type::I32),
            "as_u32" => Some(Type::U32),
            "as_i64" => Some(Type::I64),
            "as_u64" => Some(Type::U64),
            _ => None,
        };
        if let Some(to_ty) = target {
            // An un-annotated integer-literal receiver (`let n = 100;`) has type
            // `IntLit` at method-call time; it defaults to i64 (its natural
            // width) for the source-width stamp — consistent with `.contains`.
            let from_ty = if matches!(receiver.ty, Type::IntLit(_)) {
                Type::I64
            } else {
                receiver.ty.clone()
            };
            let from_air = crate::air::lower_type(&from_ty);
            let to_air = crate::air::lower_type(&to_ty);
            return TypedExpr {
                ty: to_ty,
                kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                    kind: TypedIntrinsicKind::IntConvert {
                        from: from_air,
                        to: to_air,
                    },
                    args: vec![receiver],
                }),
                span: expr.span,
                refinement: None,
            };
        }
    }

    // Phase-1 completion: `.contains(x)` on Array/Slice — a 1-arg method.
    // Scalar elements ({i32,u32,i64,u64,f64,bool}; an IntLit element/needle
    // defaults to i64) lower to a wasm-internal scan-loop intrinsic with
    // width-dispatched equality; `str` elements desugar to the
    // `strings::__sigil_slice_str_contains` CONTENT-equality helper (NEVER
    // `str_contains`, which is SUBSTRING search); composite elements are
    // rejected with the reserved T240. A `str` RECEIVER never reaches this
    // arm — its `.contains` is the substring str-method desugar further down,
    // gated on `Type::Str`.
    if expr.args.len() == 1
        && expr.method == "contains"
        && matches!(&receiver.ty, Type::Array { .. } | Type::Slice(_))
    {
        let is_slice = matches!(&receiver.ty, Type::Slice(_));
        let elem: Type = match &receiver.ty {
            Type::Array { elem, .. } => (**elem).clone(),
            Type::Slice(inner) => (**inner).clone(),
            _ => unreachable!("gated by the matches! above"),
        };
        // An already-errored element propagates `Error` WITHOUT a (spurious,
        // cascading) T240 — the real error is upstream.
        if matches!(elem, Type::Error) {
            return TypedExpr {
                ty: Type::Error,
                kind: TypedExprKind::Literal(Literal::Int(0)),
                span: expr.span,
                refinement: None,
            };
        }
        // `str` elements: desugar to the content-equality stdlib helper. Wrap
        // the receiver in `&recv` so an Array coerces to `&[str]` (borrow→slice
        // is provenance-agnostic, so a temporary receiver coerces too); a Slice
        // passes through idempotently. Routes through `infer_call_expr`
        // (cross-module resolution + arity/effect checks surface THERE).
        if matches!(elem, Type::Str) {
            let borrowed_recv = crate::ast::Expr::Borrow(crate::ast::BorrowExpr {
                inner: Box::new((*expr.receiver).clone()),
                mutable: false,
                span: expr.span,
            });
            let synthetic_callee = crate::ast::Path {
                segments: vec![
                    "strings".to_string(),
                    "__sigil_slice_str_contains".to_string(),
                ],
                type_args: vec![],
                span: expr.span,
            };
            let synthetic_call = crate::ast::CallExpr {
                callee: synthetic_callee,
                args: vec![borrowed_recv, expr.args[0].clone()],
                span: expr.span,
            };
            return infer_call_expr(
                &synthetic_call,
                env,
                current_return,
                context,
                tracker,
                diagnostics,
            );
        }
        // Scalar (`==`-bearing) elements — {i32,u32,i64,u64,f64,bool} (plus an
        // `IntLit` element via `is_machine_integer_type`). The needle is
        // inferred WITH expected-type = elem so an `IntLit` narrows to the
        // element width (the width-identity invariant: needle width == element
        // width == load width == Eq opcode).
        if is_machine_integer_type(&elem) || matches!(elem, Type::Bool | Type::F64) {
            let arg = infer_arg_with_expected(
                &expr.args[0],
                Some(&elem),
                env,
                current_return,
                context,
                tracker,
                diagnostics,
            );
            if !type_compatible(&elem, &arg.ty) {
                diagnostics.push(Diagnostic::error(
                    codes::T071,
                    format!(
                        "`.contains(x)` needle type `{}` does not match element type `{}`",
                        render_type(&arg.ty),
                        render_type(&elem)
                    ),
                    Some(expr.span),
                ));
                return TypedExpr {
                    ty: Type::Error,
                    kind: TypedExprKind::Literal(Literal::Int(0)),
                    span: expr.span,
                    refinement: None,
                };
            }
            // Freeze the element AIR width. An un-annotated array literal's
            // element is `IntLit` (the receiver was never bound to a typed
            // slot); default it to i64 — matching the IntLit needle's default,
            // so both element-load and needle compare at 8 bytes.
            let elem_concrete = if matches!(elem, Type::IntLit(_)) {
                Type::I64
            } else {
                elem.clone()
            };
            let elem_air = crate::air::lower_type(&elem_concrete);
            let kind = if is_slice {
                TypedIntrinsicKind::SliceContains { elem: elem_air }
            } else {
                TypedIntrinsicKind::ArrayContains { elem: elem_air }
            };
            return TypedExpr {
                ty: Type::Bool,
                kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                    kind,
                    args: vec![receiver, arg],
                }),
                span: expr.span,
                refinement: None,
            };
        }
        // Composite element (record/enum/Named/ref/tuple/nested array-or-slice/
        // generic/Unit): no built-in element `==` — the reserved T240.
        diagnostics.push(Diagnostic::error(
            codes::T240,
            format!(
                "`.contains(x)` is not admitted for element type `{}`; only scalar (i32/u32/i64/u64/f64/bool) and `str` elements are comparable",
                render_type(&elem)
            ),
            Some(expr.span),
        ));
        return TypedExpr {
            ty: Type::Error,
            kind: TypedExprKind::Literal(Literal::Int(0)),
            span: expr.span,
            refinement: None,
        };
    }

    // PR S1 / N16-S1: `.byte_at(i)` on Type::Str — 1-arg intrinsic.
    // Bounds-check `i < s.len()` via explicit TrapIf at AIR time;
    // no modular fallback. Result is U32 (the byte value).
    if expr.args.len() == 1 && matches!(&receiver.ty, Type::Str) && expr.method == "byte_at" {
        let arg = infer_expr(
            &expr.args[0],
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        );
        // Coerce / validate the index arg as integer-typed. PIL: route
        // through `is_machine_integer_type` to accept `Type::IntLit(_)`
        // alongside the four machine integer types; the post-pass
        // walker rewrites IntLit to a concrete machine type before AIR.
        if !is_machine_integer_type(&arg.ty) {
            diagnostics.push(Diagnostic::error(
                codes::T071,
                format!(
                    "`.byte_at(i)` requires an integer index; got `{}`",
                    render_type(&arg.ty)
                ),
                Some(expr.span),
            ));
            return TypedExpr {
                ty: Type::Error,
                kind: TypedExprKind::Literal(Literal::Int(0)),
                span: expr.span,
                refinement: None,
            };
        }
        return TypedExpr {
            ty: Type::I64,
            kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                kind: TypedIntrinsicKind::StrByteAt {
                    index: crate::air::lower_type(&arg.ty),
                },
                args: vec![receiver, arg],
            }),
            span: expr.span,
            refinement: None,
        };
    }

    // PR S(strings) / CF-S1: `.substr(start, end)` on Type::Str — a 2-arg
    // intrinsic returning a borrowed `str` view into the receiver's bytes.
    // Both args are machine integers; the bounds (`0 <= start <= end <= len`)
    // are enforced in AIR with i64-domain `TrapIf`s before the header alloc,
    // so a ≥2³² / negative index traps rather than wrapping. Mirrors the
    // `.byte_at` block above (which is the 1-arg sibling).
    if expr.args.len() == 2 && matches!(&receiver.ty, Type::Str) && expr.method == "substr" {
        let start = infer_expr(
            &expr.args[0],
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        );
        let end = infer_expr(
            &expr.args[1],
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        );
        for (label, arg) in [("start", &start), ("end", &end)] {
            if !is_machine_integer_type(&arg.ty) {
                diagnostics.push(Diagnostic::error(
                    codes::T071,
                    format!(
                        "`.substr({label}, …)` requires an integer index; got `{}`",
                        render_type(&arg.ty)
                    ),
                    Some(expr.span),
                ));
                return TypedExpr {
                    ty: Type::Error,
                    kind: TypedExprKind::Literal(Literal::Int(0)),
                    span: expr.span,
                    refinement: None,
                };
            }
        }
        return TypedExpr {
            ty: Type::Str,
            kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                kind: TypedIntrinsicKind::StrSubstr {
                    start: crate::air::lower_type(&start.ty),
                    end: crate::air::lower_type(&end.ty),
                },
                args: vec![receiver, start, end],
            }),
            span: expr.span,
            refinement: None,
        };
    }

    // PR S(strings) / method dispatch: string ops on a `str` receiver desugar to
    // the injected `strings` module's free fns, with the receiver prepended as
    // the implicit first arg — `s.find(n)` / `s.contains(n)` / `s.starts_with(p)`
    // / `s.ends_with(p)` / `s.split(d)` (1-arg) and `s.trim()` / `s.parse_i64()`
    // (0-arg). `len`/`is_empty`/`byte_at`/`substr` stay intrinsics; these compose
    // at the SIGIL level over them. Gated on `Type::Str`, so a same-named method
    // on a user type is never hijacked. A synthetic
    // `strings::str_<method>(self, args...)` call routes through `infer_call_expr`
    // (cross-module resolution + arg-count/effect checks — a wrong arity surfaces
    // THERE, not here); re-inferring the receiver is idempotent (a non-`str`
    // receiver never reaches here). Supersedes the old `.contains()` deferral.
    // The str-method → stdlib-module table (PR S2 generalization). Borrowing
    // views (find/contains/…/parse_i64) route to `strings`; owned builders
    // (concat) route to `string` (the SEPARATE owned-construction module). Both
    // desugar to `<module>::str_<method>(self, args…)` with the receiver
    // prepended. Gated on `Type::Str`, so a same-named method on a user type is
    // never hijacked.
    let str_method_module: Option<&str> = match expr.method.as_str() {
        "find" | "contains" | "starts_with" | "ends_with" | "split_on" | "trim" | "parse_i64"
        | "is_char_boundary" | "bytes_eq"
        // Phase-3 completion: narrow/unsigned parsers + case-insensitive eq +
        // head/rest split. Each desugars to `strings::str_<method>(self, args…)`.
        | "parse_u64" | "parse_i32" | "parse_u32" | "eq_ignore_case" | "split_first" => {
            Some("strings")
        }
        "concat" | "join" => Some("string"),
        _ => None,
    };
    if matches!(&receiver.ty, Type::Str)
        && let Some(target_module) = str_method_module
    {
        let synthetic_callee = crate::ast::Path {
            segments: vec![target_module.to_string(), format!("str_{}", expr.method)],
            type_args: vec![],
            span: expr.span,
        };
        let mut synthetic_args = Vec::with_capacity(expr.args.len() + 1);
        synthetic_args.push((*expr.receiver).clone());
        synthetic_args.extend(expr.args.iter().cloned());
        let synthetic_call = crate::ast::CallExpr {
            callee: synthetic_callee,
            args: synthetic_args,
            span: expr.span,
        };
        return infer_call_expr(
            &synthetic_call,
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        );
    }

    // Owned-strings PR S2: `n.itoa()` on an `i64` receiver → the `string`
    // module's `str_itoa`. An i64-receiver method — i64 has no user impls to
    // hijack, and an i64 subject has no str-method slot — routed like the str
    // builders, with the receiver becoming the sole argument. (Free-function
    // `itoa(n)` would need a `use sigil::string;` that ambient injection never
    // adds, so the method form is the collision-safe spelling.)
    if matches!(&receiver.ty, Type::I64) && expr.method == "itoa" && expr.args.is_empty() {
        let synthetic_callee = crate::ast::Path {
            segments: vec!["string".to_string(), "str_itoa".to_string()],
            type_args: vec![],
            span: expr.span,
        };
        let synthetic_call = crate::ast::CallExpr {
            callee: synthetic_callee,
            args: vec![(*expr.receiver).clone()],
            span: expr.span,
        };
        return infer_call_expr(
            &synthetic_call,
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        );
    }

    // Phase-3 completion: `.to_string()` on any int receiver → the `string`
    // module. i64 → `str_itoa`; i32/u32 widen to i64 (via `.as_i64()`, which
    // sign-/zero-extends) then `str_itoa`; u64 → the dedicated unsigned
    // `str_utoa_u64` (a u64 ≥ 2^63 cannot widen to i64). Pure (Alloc covered by
    // the builder). `i64.itoa()` remains as the legacy alias above.
    if matches!(&receiver.ty, Type::I64 | Type::I32 | Type::U32 | Type::U64)
        && expr.method == "to_string"
        && expr.args.is_empty()
    {
        let (fn_name, arg_expr): (&str, crate::ast::Expr) = match &receiver.ty {
            Type::U64 => ("str_utoa_u64", (*expr.receiver).clone()),
            Type::I64 => ("str_itoa", (*expr.receiver).clone()),
            // i32 / u32: widen to i64 first via `.as_i64()`, then format.
            _ => (
                "str_itoa",
                crate::ast::Expr::MethodCall(crate::ast::MethodCallExpr {
                    receiver: Box::new((*expr.receiver).clone()),
                    method: "as_i64".to_string(),
                    args: vec![],
                    colon_spelled: false,
                    span: expr.span,
                }),
            ),
        };
        let synthetic_callee = crate::ast::Path {
            segments: vec!["string".to_string(), fn_name.to_string()],
            type_args: vec![],
            span: expr.span,
        };
        let synthetic_call = crate::ast::CallExpr {
            callee: synthetic_callee,
            args: vec![arg_expr],
            span: expr.span,
        };
        return infer_call_expr(
            &synthetic_call,
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        );
    }

    // Owned-strings PR S3: `ptr.from_bytes(len)` / `ptr.valid_up_to(len)` on an
    // i64 receiver → the `string` module's `str_from_bytes` / `str_valid_up_to`.
    // Mirrors the itoa arm (i64 receiver — no user impls to hijack) but carries ONE
    // trailing arg, the byte length, so the receiver becomes arg 0 and `len` arg 1.
    // `from_bytes` validates untrusted bytes into an OWNED `Option<str>`;
    // `valid_up_to` returns the leading-valid-byte count (the rail). Routed through
    // `infer_call_expr`; arity/effect checks surface there against the signature.
    if matches!(&receiver.ty, Type::I64)
        && matches!(expr.method.as_str(), "from_bytes" | "valid_up_to")
        && expr.args.len() == 1
    {
        let synthetic_callee = crate::ast::Path {
            segments: vec!["string".to_string(), format!("str_{}", expr.method)],
            type_args: vec![],
            span: expr.span,
        };
        let mut synthetic_args = Vec::with_capacity(2);
        synthetic_args.push((*expr.receiver).clone());
        synthetic_args.extend(expr.args.iter().cloned());
        let synthetic_call = crate::ast::CallExpr {
            callee: synthetic_callee,
            args: synthetic_args,
            span: expr.span,
        };
        return infer_call_expr(
            &synthetic_call,
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        );
    }

    // PR-3c (trait Wall): the built-in primitive impls. `(str|i64|bool).hash()`
    // / `.eq(other)` desugar to the matching `traits::{prim}_{method}` free fn
    // (str: DJB2 / byte-eq; i64/bool: identity / native `==`) — the closed
    // `{str,i64,bool} × {hash,eq}` table (CM-T7). Gated on the exact primitive +
    // method, BEFORE the T130 arm, so a same-named method on a user type is never
    // hijacked. Mirrors the str-method dispatch above; arity/effect checks happen
    // in `infer_call_expr` against the synthetic call.
    if matches!(&receiver.ty, Type::I64 | Type::Str | Type::Bool)
        && matches!(expr.method.as_str(), "hash" | "eq")
    {
        let prim = match &receiver.ty {
            Type::Str => "str",
            Type::I64 => "i64",
            Type::Bool => "bool",
            _ => unreachable!(),
        };
        let synthetic_callee = crate::ast::Path {
            segments: vec!["traits".to_string(), format!("{prim}_{}", expr.method)],
            type_args: vec![],
            span: expr.span,
        };
        let mut synthetic_args = Vec::with_capacity(expr.args.len() + 1);
        synthetic_args.push((*expr.receiver).clone());
        synthetic_args.extend(expr.args.iter().cloned());
        let synthetic_call = crate::ast::CallExpr {
            callee: synthetic_callee,
            args: synthetic_args,
            span: expr.span,
        };
        return infer_call_expr(
            &synthetic_call,
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        );
    }

    infer_user_method_expr(
        expr,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
        receiver,
    )
}

fn infer_user_method_expr(
    expr: &MethodCallExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
    receiver: TypedExpr,
) -> TypedExpr {
    let (function_sigs, actor_sigs, module_name, universe) = context.parts();
    // Look up method in function registry
    let type_name = match &receiver.ty {
        Type::Named(name, _) => name.clone(),
        Type::Cap(name, _) => name.clone(),
        Type::Error => "<error>".to_owned(),
        other => {
            diagnostics.push(Diagnostic::error(
                codes::T130,
                format!(
                    "cannot call method `.{}()` on type `{}`",
                    expr.method,
                    render_type(other)
                ),
                Some(expr.span),
            ));
            "<error>".to_owned()
        }
    };

    let method_key = format!("{}::{}", type_name, expr.method);
    // PR C2 / CF-C1: resolve locally first (the current module always wins),
    // then fall back to a global scan of sibling modules so a method on a type
    // defined elsewhere (e.g. ambient `Vec`) resolves. ≥2 defining modules is a
    // hard ambiguity (T244), never first-match-wins. The found sig is OWNED so
    // the `&workspace_sigs` borrow ends before the `&mut tracker` mono below.
    let mut ambiguity_reported = false;
    let resolved_method_sig: Option<FunctionSig> = match function_sigs.get(&method_key) {
        Some(s) => Some(s.clone()),
        None => match crate::type_check::call_resolve::resolve_impl_member_global(
            &method_key,
            module_name,
            tracker,
        ) {
            crate::type_check::call_resolve::GlobalImplVerdict::Found(s) => Some(s),
            crate::type_check::call_resolve::GlobalImplVerdict::Ambiguous(mods) => {
                diagnostics.push(Diagnostic::error(
                    codes::T244,
                    format!(
                        "ambiguous method `{}` for type `{type_name}`: defined in modules [{}]; a type's impl must live in exactly one module",
                        expr.method,
                        mods.join(", ")
                    ),
                    Some(expr.span),
                ));
                ambiguity_reported = true;
                None
            }
            crate::type_check::call_resolve::GlobalImplVerdict::None => None,
        },
    };
    // PR #132: the (substituted, self-excluded) parameter types, captured out
    // of the dispatch block so the arg loop can pin + narrow against them.
    let mut arg_expected: Vec<Type> = Vec::new();
    let (callee, ret_type) = if let Some(sig) = resolved_method_sig.as_ref() {
        // SIGIL Complete v0 / Phase 6 supremum-path dispatch substitution.
        //
        // The sig's `params` and `ret` carry impl-block-level
        // `Type::Generic("T")` references (per N11-V0/N15-V0 — resolved
        // at sig-collection time). At dispatch we positional-substitute
        // them against the receiver's concrete type-args (N9-V0).
        //
        // For non-generic impl blocks `impl_type_params` is empty and
        // `subst` collapses to identity — pre-v0 behavior preserved
        // (N17-V0 backward-compat).
        let receiver_type_args: Vec<Type> = match &receiver.ty {
            Type::Named(_, args) => args.clone(),
            _ => Vec::new(),
        };

        // N7-V0: T231 — arity check. If the impl block declares N
        // type_params, the receiver's concrete type-args MUST be N.
        // Otherwise substitution silently mis-binds.
        if !sig.impl_type_params.is_empty()
            && receiver_type_args.len() != sig.impl_type_params.len()
        {
            diagnostics.push(Diagnostic::error(
                codes::T231,
                format!(
                    "method `.{}()` dispatch: receiver type `{}` has {} type argument(s) but the `impl {}<{}>` block declares {} type parameter(s)",
                    expr.method,
                    render_type(&receiver.ty),
                    receiver_type_args.len(),
                    type_name,
                    sig.impl_type_params.join(", "),
                    sig.impl_type_params.len(),
                ),
                Some(expr.span),
            ));
        }

        // N8-V0: T232 — unresolved-generic check. Every entry in the
        // receiver's type-args must be either concrete OR a
        // `Type::Generic("X")` whose `X` is bound in the current
        // monomorphization scope. The simple bound condition is
        // satisfied when tracker.current_type_params contains the
        // name (today, infer_method_call_expr doesn't track that
        // scope explicitly; defer enforcement to a future PR and
        // surface only the structural defense here — any
        // `Type::Generic("_unresolved_outer")` is rejected. Concrete
        // and known-scope generics flow through). This conservative
        // check fires only on the pathological identity-substitution
        // case where the receiver type itself escaped without ever
        // being bound to a concrete monomorphization site.
        for arg in &receiver_type_args {
            if matches!(arg, Type::Generic(_)) && sig.impl_type_params.is_empty() {
                // Receiver carries a generic but the impl block has
                // no binders to absorb it — this is the silent
                // identity-substitution scenario N8-V0 closes.
                diagnostics.push(Diagnostic::error(
                    codes::T232,
                    format!(
                        "method `.{}()` dispatch: receiver type `{}` carries an unresolved generic — the enclosing function must declare the relevant `<T>` in its type parameters, or supply a concrete type via turbofish at the receiver's construction site",
                        expr.method,
                        render_type(&receiver.ty),
                    ),
                    Some(expr.span),
                ));
            }
        }

        // N9-V0: positional substitution. Build `{impl_type_params[i] →
        // receiver_type_args[i]}` and apply to params + ret.
        // Substitution is identity when impl_type_params is empty.
        let mut subst: HashMap<String, Type> = HashMap::new();
        let n = sig.impl_type_params.len().min(receiver_type_args.len());
        for (i, arg) in receiver_type_args.iter().enumerate().take(n) {
            subst.insert(sig.impl_type_params[i].clone(), arg.clone());
        }

        let mut substituted_params: Vec<Type> =
            sig.params.iter().map(|p| apply_subst(p, &subst)).collect();
        let mut substituted_ret = apply_subst(&sig.ret, &subst);

        // GENERIC IMPL METHODS: infer the method's OWN type parameters (distinct
        // from the impl block's, already positional-substituted above) by unifying
        // the impl-substituted formal params against the actual receiver +
        // argument types — the method-dispatch analog of free-fn generic
        // inference. Without this a method generic like `fmap<A, B>`'s `B` stays
        // `Type::Generic` in `substituted_params`/`substituted_ret`, builds a
        // non-concrete mono body, and ICEs in `type_compatible` / `mangle_type`
        // (the AG-PRD-7 limitation the mono-body comment below acknowledges).
        // Args are typed here into a SUPPRESSED diagnostic sink PURELY for
        // inference; the real per-arg validation + narrowing happens in the arg
        // loop below, against the now-concrete expecteds.
        // The method's own generics, in declaration order, as the concrete types
        // they were inferred to — used to make the monomorphized instance's
        // mangled name unique (two `fmap` calls with different result element
        // types must NOT collide on the same `__Box_i64` name).
        let mut method_concrete_args: Vec<Type> = Vec::new();
        if !sig.method_type_params.is_empty() {
            let mut method_bindings: HashMap<String, Type> = HashMap::new();
            if let Some(self_formal) = substituted_params.first() {
                unify(self_formal, &receiver.ty, &mut method_bindings);
            }
            let mut sink: Vec<Diagnostic> = Vec::new();
            for (i, arg) in expr.args.iter().enumerate() {
                let formal = substituted_params.get(i + 1);
                let typed = infer_arg_with_expected(
                    arg,
                    formal,
                    env,
                    current_return,
                    context,
                    tracker,
                    &mut sink,
                );
                if let Some(f) = formal {
                    unify(f, &typed.ty, &mut method_bindings);
                }
            }
            // Keep ONLY the method's own params — impl params were already
            // resolved, and a stray binding must not leak into the body.
            method_bindings.retain(|k, _| sig.method_type_params.iter().any(|p| p == k));
            // R3 (HK3 hardening): EVERY method-generic must get a binding. An
            // ill-typed Fn-argument (`b.fmap(inc)` where `inc` is undefined or a
            // bare fn name) leaves the result generic `B` unconstrained by unify;
            // default it to `Type::Error` so `apply_subst` ERASES it below.
            // Without this, a residual `Generic("B")` survives in `substituted_ret`
            // and ICEs in `type_compatible` ("Generic escaped monomorphization").
            // The arg's own error surfaces cleanly in the arg-validation loop.
            for name in &sig.method_type_params {
                method_bindings.entry(name.clone()).or_insert(Type::Error);
            }
            method_concrete_args = sig
                .method_type_params
                .iter()
                .map(|name| method_bindings.get(name).cloned().unwrap_or(Type::Error))
                .collect();
            substituted_params = substituted_params
                .iter()
                .map(|p| apply_subst(p, &method_bindings))
                .collect();
            substituted_ret = apply_subst(&substituted_ret, &method_bindings);
            // Extend the impl `subst` so a method-generic-typed annotation inside
            // the monomorphized body (`let r: B = …`) erases too.
            for (k, v) in method_bindings {
                subst.insert(k, v);
            }
        }

        // Validate args (excluding implicit self) against substituted
        // params so call sites against `Result<i64, MyErr>` see
        // `i64`-typed param slots, not `T`-typed ones.
        let expected_params = if substituted_params.len() > 1 {
            &substituted_params[1..]
        } else {
            &[]
        };
        if expr.args.len() != expected_params.len() {
            diagnostics.push(Diagnostic::error(
                codes::T131,
                format!(
                    "method `{}` expects {} argument(s), found {}",
                    expr.method,
                    expected_params.len(),
                    expr.args.len()
                ),
                Some(expr.span),
            ));
        }

        // PR D: AIR-monomorphization for generic impl methods.
        //
        // If the impl block was generic, the method body emitted at
        // typed_ast build (type_check.rs:680+) still carries
        // `Type::Generic("T")` placeholders. Without per-instantiation
        // mono, AIR lowering's `mangle_type` would ICE on those
        // generics. Mirror the free-fn path at lines 3658-3801.
        //
        // For non-generic impl methods (empty impl_type_params),
        // skip the mono entirely — the one-shot typed_ast emission is
        // already correct (no generics in the body to escape).
        let callee = if !sig.impl_type_params.is_empty() || !sig.method_type_params.is_empty() {
            // N8-PRD: module-qualified key for cross-module
            // disambiguation. Format must match
            // collect_type_universe's insertion.
            let qualified_method_key = format!("{}::{}::{}", sig.module, type_name, expr.method);

            // N5-PRD: single canonical helper for mangled name. Mangle over the
            // impl generics (from the receiver) AND the method's own inferred
            // generics, so instances at different method-generic bindings get
            // distinct instance names.
            let mangle_args: Vec<Type> = receiver_type_args
                .iter()
                .cloned()
                .chain(method_concrete_args.iter().cloned())
                .collect();
            let base_mangled =
                build_mono_impl_method_mangled_name(&sig.qualified_name, &mangle_args);
            // A `push` whose receiver roots at a `mut Vec<scalar>` actor-state field is
            // routed to a SEPARATE, state-backed mono instance (suffix `$state`) whose grow-alloc
            // lowers to `alloc_persistent` so the buffer survives the per-dispatch
            // reset. Gate: method==push ∧ receiver.ty == Vec<scalar> ∧ the receiver's place-root is
            // a `mut` state field. Dead across any state-free module (place_root_statefield → None),
            // so the shared instance and the whole stateless capstone stay byte-identical (P1). `$`
            // / `__` are reserved from user paths (T271), so the suffix cannot collide.
            let receiver_is_state_rooted = statements::place_root_statefield(&receiver)
                .is_some_and(|root| tracker.mut_state_fields.contains(root));
            // PPS-3: the element predicate is `universe::is_persistable_scalar_vec` — which now
            // admits `str` as well as inline scalars. AGG-2b restricted this to scalars because
            // it had no way to persist a pointer-bearing element; PPS-2b's promotion at the
            // storing `push` supplies exactly that. Leaving the gate scalar-only was why a state
            // `Vec<str>` trapped: it was never routed to `$state`, so its buffer grew transiently
            // AND the promotion (which keys on the `$state` callee) never fired — one cause, two
            // symptoms.
            let routes_to_persistent_vec = expr.method == "push"
                && universe::is_persistable_scalar_vec(&receiver.ty, universe)
                && receiver_is_state_rooted;
            // PPS-0: a MUTATING `Map<scalar, scalar>` method on a state-rooted receiver routes the
            // same way. Unlike `Vec::push` (one alloc, in the routed body), a `Map`'s allocations
            // are all in callees — `ensure_buckets`/`grow`/`filled` and their interior `Vec`
            // pushes — so the routed instance ALSO raises `state_mono_depth`, and every generic
            // instance built beneath it inherits the suffix (see the body-build bracket below).
            let routes_to_persistent_map =
                universe::is_persistable_scalar_map(&receiver.ty, universe)
                    && matches!(
                        expr.method.as_str(),
                        "insert" | "ensure_buckets" | "grow" | "filled"
                    )
                    && receiver_is_state_rooted;
            // Inheritance: anything built while inside a state-backed body is state-backed too.
            let inherits_state_backing = tracker.state_mono_depth > 0;
            let routes_to_persistent =
                routes_to_persistent_vec || routes_to_persistent_map || inherits_state_backing;
            let mangled_callee = if routes_to_persistent {
                format!("{base_mangled}{}", crate::air::STATE_VEC_MONO_SUFFIX)
            } else {
                base_mangled
            };

            // N6-PRD: atomic check-and-insert via the cache.
            // `insert` returns true iff the value was NEW. On true:
            // build the mono body. On false: cache hit, skip.
            if tracker.cache.insert(mangled_callee.clone()) {
                // Look up method AST (N10-PRD: never silently fall back).
                if let Some((impl_type_params_decl, method_def, method_module)) = universe
                    .generic_impl_methods
                    .get(&qualified_method_key)
                    .cloned()
                {
                    // N7-PRD: depth budget bracket. Increment BEFORE
                    // body build, decrement after (with cache cleanup
                    // on overflow per the constraint matrix).
                    tracker.depth += 1;
                    if tracker.depth > MAX_MONOMORPH_DEPTH {
                        diagnostics.push(Diagnostic::error(
                            codes::T150,
                            format!(
                                "method `{}::{}` monomorphization recursion exceeded {} depth — likely a self-referential generic impl",
                                type_name, expr.method, MAX_MONOMORPH_DEPTH
                            ),
                            Some(expr.span),
                        ));
                        tracker.depth -= 1;
                        // N7-PRD cache cleanup: remove the poisoned
                        // entry so retries don't see a stale name.
                        tracker.cache.remove(&mangled_callee);
                    } else {
                        // N9-PRD: arity defense before zip.
                        if substituted_params.len() != method_def.params.len() {
                            diagnostics.push(Diagnostic::error(
                                codes::I012,
                                format!(
                                    "internal: substituted_params arity ({}) != method_def.params arity ({}) for `{}::{}`",
                                    substituted_params.len(),
                                    method_def.params.len(),
                                    type_name,
                                    expr.method
                                ),
                                Some(expr.span),
                            ));
                            tracker.depth -= 1;
                            tracker.cache.remove(&mangled_callee);
                        } else {
                            // Build concrete TypedParams from the
                            // substituted sig + the method AST's
                            // param names + taints.
                            let mono_params: Vec<TypedParam> = substituted_params
                                .iter()
                                .zip(method_def.params.iter())
                                .map(|(ty, p)| TypedParam {
                                    flow: false,
                                    mutability: crate::ast::Mutability::Default,
                                    name: p.name.clone(),
                                    ty: ty.clone(),
                                    taint: p.taint.unwrap_or(crate::ast::TaintLabel::Public),
                                })
                                .collect();

                            // Build combined generic scope (impl + method)
                            // so the body's type-check resolves both
                            // levels — note that the method-level params
                            // become Type::Generic("U") placeholders
                            // resolved later via apply_subst from N1-PRD's
                            // walker (AG-PRD-7 acknowledges this v1 limit).
                            // Per AG-PRD-7 refinements drop.
                            let mono_param_refinements: Vec<
                                Option<Vec<crate::ast::RefinementClause>>,
                            > = vec![None; mono_params.len()];

                            // Re-type-check the body against concrete env.
                            // PR D N1-PRD's intent: the field-access fix
                            // upstream substitutes field types against
                            // receiver type-args, so the body's intermediate
                            // expression types come out concrete via env
                            // propagation. (Future PR may add a full
                            // apply_subst_to_typed_function walker for
                            // expression-kinds the field-fix doesn't cover.)
                            //
                            // CF-D9: a cross-module-monomorphized method body
                            // must resolve names in its DEFINING module's scope
                            // — its own free functions (e.g. map.sigil's
                            // `map_filled_i64`) and private sibling methods
                            // (`find_slot`/`grow`/…) — NOT the caller's. The
                            // module_name arg below is already `&method_module`;
                            // `function_sigs` must align with it. Pre-fix the
                            // caller's per-module sigs leaked through, so a
                            // stdlib method calling a same-module free fn or a
                            // private sibling failed T062/T132 the moment it was
                            // injected as a sibling module (map.sigil is the
                            // first such stdlib — vec/option methods call
                            // neither a free fn nor a private sibling, so this is
                            // a no-op for them: byte-identical). Clone to drop
                            // the immutable `tracker` borrow before the
                            // `&mut tracker` arg; fall back to the caller's sigs
                            // if the defining module is somehow unregistered.
                            let defining_sigs =
                                tracker.workspace_sigs.get(method_module.as_str()).cloned();
                            let method_context = TypeCheckContext::new(
                                defining_sigs.as_ref().unwrap_or(function_sigs),
                                actor_sigs,
                                &method_module,
                                universe,
                            );
                            // PPS-0: raise the state-mono depth for the DURATION of this body
                            // build when this instance is state-backed. Every generic instance
                            // built beneath it (a `Map`'s `ensure_buckets` → `filled` →
                            // `Vec::with_capacity`/`push` chain) then inherits the `$state`
                            // suffix, so allocations in callees land on the persistent channel
                            // too. Restored below, so a sibling non-state call after this one is
                            // routed normally.
                            if routes_to_persistent {
                                tracker.state_mono_depth += 1;
                            }
                            let body = check_function_block(
                                &mono_params,
                                &substituted_ret,
                                &HashMap::new(),
                                &method_def.body,
                                method_context,
                                tracker,
                                diagnostics,
                                &mono_param_refinements,
                                None,
                                // PR-2b: mono re-entry seeds @ReadOnly from the method def
                                // (mono preserves param count + order).
                                &method_def
                                    .params
                                    .iter()
                                    .map(|p| p.mutability)
                                    .collect::<Vec<_>>(),
                                // DEF-2b PR-4: mono re-entry seeds region params from the
                                // method def (mono preserves param count + order).
                                &universe::param_regions_of(&method_def.params),
                                // DEF-2b PR-5: the method def's `where region` outlives pairs.
                                &universe::param_region_outlives_of(
                                    &method_def.params,
                                    &method_def.region_outlives,
                                ),
                                // A monomorphized method has no actor state in scope.
                                &HashMap::new(),
                                &std::collections::HashSet::new(),
                                super::super::BodyKind::Free,
                            );

                            if routes_to_persistent {
                                tracker.state_mono_depth -= 1;
                            }

                            // N13-PRD: tracker.functions append-only.
                            // N11-PRD: export_name = mangled_callee so
                            // wasm emission resolves the call.
                            tracker.functions.push(TypedFunction {
                                ret_flow: false,
                                name: mangled_callee.clone(),
                                export_name: mangled_callee.clone(),
                                kind: TypedFunctionKind::ModuleFunction,
                                externally_callable: matches!(
                                    method_def.visibility,
                                    crate::ast::Visibility::Public
                                ),
                                params: mono_params,
                                captures: Vec::new(),
                                ret: substituted_ret.clone(),
                                ret_taint: crate::ast::TaintLabel::Public,
                                // PR-0: propagate the method's DECLARED effect
                                // row to the monomorphized instance. Empty here
                                // would (a) spuriously trip E001 on an
                                // effect-gated intrinsic in this body, and
                                // (b) let callers escape the effect requirement.
                                effects: resolve_effect_row(&method_def.effects, universe),
                                body,
                                span: method_def.span,
                            });

                            // Mark used so the inner block doesn't dead-
                            // code warn on the loop var.
                            let _ = impl_type_params_decl;
                        }
                        tracker.depth -= 1;
                    }
                } else {
                    // N10-PRD: NEVER silently fall back. Fire I011 if the
                    // method is in function_sigs (we already passed that
                    // lookup) but missing from generic_impl_methods.
                    diagnostics.push(Diagnostic::error(
                        codes::I011,
                        format!(
                            "internal: impl method `{}::{}` present in function_sigs but missing from generic_impl_methods (collection bug)",
                            type_name, expr.method
                        ),
                        Some(expr.span),
                    ));
                    tracker.cache.remove(&mangled_callee);
                }
            }
            // Use the mangled name as the call's callee (whether we
            // just built it or hit cache).
            mangled_callee
        } else {
            // Non-generic impl method — pre-PR-D path.
            sig.qualified_name.clone()
        };

        arg_expected = expected_params.to_vec();
        (callee, substituted_ret)
    } else {
        // Suppress the generic "no method" error when a precise cross-module
        // ambiguity (T244) was already reported for this same call.
        if !ambiguity_reported {
            diagnostics.push(Diagnostic::error(
                codes::T132,
                format!("no method `{}` found for type `{}`", expr.method, type_name),
                Some(expr.span),
            ));
        }
        (
            format!("{module_name}::{type_name}_{}", expr.method),
            Type::Error,
        )
    };

    // Type-check arguments, pinning each to its (substituted, self-excluded)
    // parameter type so a nested generic call infers (CF-I4) and an `IntLit`
    // narrows to the concrete width (#132). `arg_expected[i]` aligns with
    // `expr.args[i]` — self is NOT in `arg_expected` (CF-I2).
    let mut typed_args = vec![receiver]; // receiver is implicit first arg
    for (i, arg) in expr.args.iter().enumerate() {
        let expected = arg_expected.get(i);
        let typed = infer_arg_with_expected(
            arg,
            expected,
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        );
        // CF-I3 / CF-I8: a literal that did NOT fit its concrete param stays
        // `IntLit`; reject it here (the method path had no per-arg type check,
        // only the arity check above). Same predicate as the call path.
        if let Some(p) = expected
            && type_is_concrete(p)
            && matches!(typed.ty, Type::IntLit(_))
        {
            diagnostics.push(Diagnostic::error(
                codes::T071,
                format!(
                    "method `{}` expected argument #{} of type `{}`, found `{}`",
                    expr.method,
                    i + 1,
                    render_type(p),
                    render_type(&typed.ty)
                ),
                Some(typed.span),
            ));
        }
        // Soundness fix: the IntLit arm above ONLY catches an int LITERAL that
        // overflowed its param. A NON-literal arg of an incompatible concrete
        // type — a `str`/`bool`/record passed where a machine int (`i64`/`i32`/
        // `u32`/`u64`) is expected — previously slipped through with NO
        // diagnostic, then produced INVALID wasm at instantiation (the
        // method-arg check was IntLit-only, unlike the strict free-call path at
        // `infer_call_expr`). Mirror that path here for the machine-int param
        // direction: when the formal param is a concrete machine int and the
        // actual arg is a concrete, non-IntLit, incompatible type, reject with
        // T071 at the arg span. Excluding `IntLit` (handled above) and
        // `Generic`/`Error` keeps the IntLit→machine-int flex AND avoids feeding
        // an escaped generic into `type_compatible` (which would ICE). Scoped to
        // machine-int params — composite/str param directions are unchanged.
        if let Some(p) = expected
            && matches!(p, Type::I32 | Type::U32 | Type::I64 | Type::U64)
            && !matches!(typed.ty, Type::IntLit(_) | Type::Generic(_) | Type::Error)
            && !type_compatible(p, &typed.ty)
        {
            diagnostics.push(Diagnostic::error(
                codes::T071,
                format!(
                    "method `{}` expected argument #{} of type `{}`, found `{}`",
                    expr.method,
                    i + 1,
                    render_type(p),
                    render_type(&typed.ty)
                ),
                Some(typed.span),
            ));
        }
        // Closure-signature soundness (iteration.md AG-6): a `Fn`-typed
        // parameter — every iterator adapter (`.map`/`.filter`/`.fold`/…) takes
        // one — must receive a closure whose FULL signature matches: arity,
        // param types, return type, AND linearity. The two arms above check
        // only IntLit-fit and machine-int params, so a mistyped closure
        // (`Fn(i64) -> bool` for a `Fn(i64) -> i64` param, a wrong arity like
        // `fold`'s 1-vs-2 args, or a wrong param type `Fn(str) -> …`) slipped
        // through to AIR — either silently accepted or ICE'ing the wasm backend
        // at `call_indirect`. Route it through the SAME `type_compatible`
        // `Type::Fn` arm the strict free-call path (`infer_call_expr`) uses →
        // T071. Scoped to a `Type::Fn` EXPECTED param so the IntLit/scalar
        // method-arg flex (generics epic, 102 differential tests) is untouched;
        // the `!type_mentions_generic` screen on BOTH sides keeps an
        // unsubstituted generic out of `type_compatible`'s ICE arm. `IntLit`
        // (a non-closure arg in a closure slot) is already reported by the
        // first arm above, so it is excluded here to avoid a duplicate T071.
        if let Some(p) = expected
            && matches!(p, Type::Fn(..))
            && !type_mentions_generic(p)
            && !matches!(typed.ty, Type::IntLit(_) | Type::Error)
            && !type_mentions_generic(&typed.ty)
            && !type_compatible(p, &typed.ty)
        {
            diagnostics.push(Diagnostic::error(
                codes::T071,
                format!(
                    "method `{}` expected argument #{} of type `{}`, found `{}`",
                    expr.method,
                    i + 1,
                    render_type(p),
                    render_type(&typed.ty)
                ),
                Some(typed.span),
            ));
        }
        typed_args.push(typed);
    }
    // Note: receiver consumed — Phase 1 has no &self borrows

    // Regions (DEF-2a, NC-R1/NC-R2): the method receiver + arg escape sink. The ONE
    // exemption to "a region value reaches no function" is the RECEIVER position of an
    // allowlisted self-containing stdlib collection method (`v.push(x)`, `v.get(i)`,
    // `m.insert(k, x)`) — proven to keep `self` in-region — which is what makes a
    // region-scoped `Vec`/`Map` usable. When allowlisted, the receiver (`typed_args[0]`)
    // is exempt and each non-self ARG is checked against the RECEIVER's depth: an arg
    // born in a DEEPER region, appended into a longer-lived container, would dangle once
    // the deeper region is reclaimed (`reject ⟺ birth_depth(arg) > recv_depth`); a
    // same-or-shallower arg is fine. Every non-allowlisted method (user-defined,
    // non-listed stdlib) keeps the conservative rule — receiver AND args at scope 0 (the
    // callee may store any of them at function lifetime).
    if tracker.current_region_depth > 0 || !tracker.current_param_regions.is_empty() {
        if statements::is_region_safe_stdlib_method(&type_name, &expr.method) {
            let recv_region = typed_args
                .first()
                .map(|recv| statements::region_of_value(recv, tracker))
                .unwrap_or(RegionId::Global);
            for arg in typed_args.iter().skip(1) {
                statements::check_region_escape(
                    arg,
                    recv_region,
                    "be stored into a longer-lived collection",
                    tracker,
                    diagnostics,
                );
            }
        } else {
            // DEF-2b PR-4 (the AG-R2 lift, mirror of the free-call sink): a non-allowlisted
            // user method may declare `@in r` params, so each argument's sink region comes
            // from the resolved method sig — a `Region`-typed param receives a threaded
            // handle (exempt, NC-2b-2); an `@in r` param's value must outlive the region at
            // `r`'s slot (caller-side, NC-2b-3); everything else — and every arg when the
            // method sig is unresolved — is a `Global` sink (NC-2b-4). The receiver
            // (`typed_args[0]`, bound to `self`) is never `Region`-typed nor `@in`, so it
            // stays a `Global` sink. No region params → DEF-2a's blanket `Global` →
            // byte-identical.
            let callee_sig = resolved_method_sig.as_ref();
            for (i, arg) in typed_args.iter().enumerate() {
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
                    "be the receiver or argument of a method",
                    tracker,
                    diagnostics,
                );
            }
        }
    }

    // Mutation-as-capability (PR-3, NC-1/NC-3): the METHOD-call receiver + arg gate
    // — the last sink in the closed set. `typed_args[0]` is the receiver (bound to
    // the method's `self`), `[1..]` the explicit args; `param_mutability` aligns
    // positionally (self at index 0). A readonly-rooted aliasable value flowing into
    // a non-`@ReadOnly` parameter re-widens authority — so calling a plain-`self`
    // MUTATOR (`v.push(x)`) on a `@ReadOnly` receiver, or passing a readonly value
    // into a mutable method arg, is T253. A read method declares `@ReadOnly self`
    // (stdlib: vec/map reads), so reading through a frozen value (`v.get(i)`,
    // `m.len()`) stays legal. Mirrors the `infer_call_expr` chokepoint; the
    // cross-module-synthetic and str/trait reroutes are gated there instead.
    if let Some(sig) = resolved_method_sig.as_ref() {
        for (i, arg) in typed_args.iter().enumerate() {
            let param_is_frozen = sig
                .param_mutability
                .get(i)
                .copied()
                .is_some_and(crate::ast::Mutability::is_frozen);
            // AGG-4 (aggregate-state hardening): the frozen SOURCE is either a
            // `@ReadOnly` local (the existing launder gate) OR a read rooted in a
            // NON-`mut` state field. Records/arrays are reference-semantic, so
            // `b.push(x)` on a non-`mut` aggregate state field (push = `@Mut self`)
            // would mutate the immutable state THROUGH the receiver — the direct
            // analogue of the `let e = d` alias-write launder, but with no
            // intervening `let` for the readonly-propagation to catch. `mut`-EXEMPT
            // (a `mut` aggregate IS the intended AGG-2a in-place path) and
            // handler-only (`init` legitimately mutates state during construction).
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
                let position = if i == 0 {
                    "the receiver of".to_string()
                } else {
                    format!("argument #{i} of")
                };
                diagnostics.push(Diagnostic::error(
                    codes::T253,
                    format!(
                        "cannot pass frozen value `{root}` as {position} `{type_name}::{}`: \
                         that parameter is mutable, so the call could mutate immutable state or a \
                         `@ReadOnly` value. Use a method with `@ReadOnly self`, or pass a copy.",
                        expr.method
                    ),
                    Some(arg.span),
                ));
            }
            // AGG2b-4 (HOLE-DANGLE, method-arg twin of the free-call gate): a `mut
            // Vec<scalar>` state field passed as a `@Mut` ARG (index >= 1) to a method
            // could be grown inside the callee via a non-state binding → a mis-routed
            // realloc that dangles after the AL-2 reset. Fail-closed reject. Index 0
            // (the receiver) is EXEMPT — a `@Mut self` grow on the state field itself
            // (`v.push(x)`) is the intended AGG2b-2 `$state`-routed direct path.
            if i >= 1
                && !param_is_frozen
                && tracker.body_kind != super::super::BodyKind::Init
                && (universe::is_persistable_scalar_vec(&arg.ty, universe)
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
                        "cannot pass the `mut` state {shape} `{root}` as argument #{i} of \
                         `{type_name}::{}`: the callee could grow it, and a grow through a \
                         non-state binding reallocs into transient memory reclaimed after the \
                         dispatch (a dangling read). Grow the field directly, or pass a copy.",
                        expr.method
                    ),
                    Some(arg.span),
                ));
            }
        }
        // Exclusivity (DEF-2c PR-2, NC-2c-1): the METHOD-call analogue of the
        // call-arg gate. `typed_args[0]` is the receiver (bound to `self`), `[1..]`
        // the explicit args, and `param_mutability` aligns positionally — so the
        // SAME helper closes AG-1 here. If one participant (receiver OR arg) reaches
        // a FROZEN parameter and an OVERLAPPING one reaches a MUTABLE parameter of
        // this call, mutating through the mutable handle would break the frozen view
        // → T255. The receiver naturally participates at index 0, so `v.store(v)`
        // with `store(@ReadOnly self, b @Mut)` (or the mutable-receiver reverse) is
        // caught. No frozen+mutable aliasing pair ⇒ empty partition ⇒ byte-identical
        // (NC-2c-7).
        for (root, span) in statements::exclusivity_partition(
            &typed_args,
            &sig.param_mutability,
            &tracker.alias_origin,
        ) {
            diagnostics.push(Diagnostic::error(
                codes::T255,
                format!(
                    "cannot pass `{root}` as both a frozen (`@ReadOnly`) and a mutable \
                     argument to `{type_name}::{}`: mutating it through the mutable handle \
                     would break the read-only view of the same object. Pass a copy to one \
                     of them.",
                    expr.method
                ),
                Some(span),
            ));
        }
    }

    TypedExpr {
        ty: ret_type,
        kind: TypedExprKind::Call(TypedCallExpr {
            callee,
            args: typed_args,
        }),
        span: expr.span,

        refinement: None,
    }
}

/// PR C1: resolve an associated-function call `Type::method(args)` (a no-`self`
/// impl method, e.g. a constructor). Mirrors the generic-impl method
/// monomorphization in `infer_method_call_expr` but with NO receiver: the call
/// carries exactly the impl fn's declared parameters (CF-C2), and the generic
/// type parameter `T` is bound from the arguments and then — when the arguments
/// leave it unbound (the phantom-`T` constructor case) — from the expected
/// (annotation) type via the return type (AG-C2: no expected type ⇒ T150).
#[allow(clippy::too_many_arguments)]
fn infer_associated_fn_call(
    type_name: &str,
    sig: &FunctionSig,
    expr: &MethodCallExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let (function_sigs, actor_sigs, _module_name, universe) = context.parts();
    // The reroute already resolved `sig` — locally, or via the global sibling
    // scan (PR C2) — and confirmed it is a no-`self` associated function.

    // 1. Type-check arguments. CF-C2: NO receiver is prepended — `typed_args`
    //    starts empty and holds only the call's explicit arguments.
    let mut typed_args: Vec<TypedExpr> = Vec::new();
    for (i, arg) in expr.args.iter().enumerate() {
        // PR #132/#135: pin to the formal param type (concrete formals like
        // `n: i64` narrow a literal; a generic formal `T` is filtered by CF-I1).
        let expected = sig.params.get(i);
        let typed = infer_arg_with_expected(
            arg,
            expected,
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        );
        // CF-I3: reject a non-fitting literal (the assoc-fn path had only the
        // arity check below).
        if let Some(p) = expected
            && type_is_concrete(p)
            && matches!(typed.ty, Type::IntLit(_))
        {
            diagnostics.push(Diagnostic::error(
                codes::T071,
                format!(
                    "associated function `{type_name}::{}` expected argument #{} of type `{}`, found `{}`",
                    expr.method,
                    i + 1,
                    render_type(p),
                    render_type(&typed.ty)
                ),
                Some(typed.span),
            ));
        }
        typed_args.push(typed);
    }
    // Note (PR-3): no `@ReadOnly` ESCAPE gate (T253) here. This path is reached ONLY
    // by a no-`self` associated fn of a GENERIC impl (e.g. `Vec::new`, `Map::new`,
    // `with_capacity`) — every such stdlib constructor takes only non-aliasable
    // args (nothing / `i64`), so the escape gate's condition (a readonly-rooted
    // ALIASABLE arg flowing in) is unreachable today. NC-3's closed binding set is
    // {free, cross-module-synthetic, true-method, str/trait reroute, indirect}; the
    // associated-fn constructor is deliberately not in it. The true-method escape
    // gate (which DOES carry the arg check) lives in `infer_method_call_expr`.

    // Exclusivity (DEF-2c PR-2, NC-2c-1): UNLIKE the escape gate above, the INTRA-call
    // exclusivity gate IS applied here. The escape gate needs a value already in
    // `readonly_locals`; this gate needs only that ONE object reach a FROZEN param and
    // an OVERLAPPING object reach a MUTABLE param of THIS call — a conflict the call
    // itself creates, independent of any pre-existing frozen local. So a user
    // `Foo::make(a @ReadOnly, b @Mut)` called `Foo::make(p, p)` is caught → T255. The
    // closed exclusivity surface (NC-2c-1) therefore INCLUDES the associated-fn
    // constructor. `typed_args` aligns with `sig.param_mutability` directly (no
    // receiver). Inert (empty partition) when every arg is non-aliasable — the stdlib
    // constructor case — so byte-identical for today's corpus (NC-2c-7).
    for (root, span) in
        statements::exclusivity_partition(&typed_args, &sig.param_mutability, &tracker.alias_origin)
    {
        diagnostics.push(Diagnostic::error(
            codes::T255,
            format!(
                "cannot pass `{root}` as both a frozen (`@ReadOnly`) and a mutable argument \
                 to `{type_name}::{}`: mutating it through the mutable handle would break the \
                 read-only view of the same object. Pass a copy to one of them.",
                expr.method
            ),
            Some(span),
        ));
    }

    // 2. Arity check against ALL params (no implicit self to exclude).
    if typed_args.len() != sig.params.len() {
        diagnostics.push(Diagnostic::error(
            codes::T131,
            format!(
                "associated function `{type_name}::{}` expects {} argument(s), found {}",
                expr.method,
                sig.params.len(),
                typed_args.len()
            ),
            Some(expr.span),
        ));
    }

    // 3. Bind the impl type params. Unify each formal param against its arg
    //    (binds `T` when it appears in a param), then fill any still-unbound
    //    param from the expected type via the return type — the exact
    //    return-type-directed step `infer_call_expr` uses, replicated here
    //    because associated-fn calls do not flow through that path.
    let mut subst: HashMap<String, Type> = HashMap::new();
    for (formal, actual) in sig.params.iter().zip(typed_args.iter()) {
        unify(formal, &actual.ty, &mut subst);
    }
    if sig.impl_type_params.iter().any(|p| !subst.contains_key(p))
        && let Some(expected) = tracker.current_expected_type.clone()
        && !matches!(expected, Type::Error)
    {
        unify(&sig.ret, &expected, &mut subst);
    }
    for p in &sig.impl_type_params {
        if !subst.contains_key(p) {
            // AG-C2: no annotation / expected type to bind `T` (and turbofish
            // on an associated fn does not parse) — fail closed.
            diagnostics.push(Diagnostic::error(
                codes::T150,
                format!("could not infer type parameter `{p}` — use turbofish"),
                Some(expr.span),
            ));
            subst.insert(p.clone(), Type::Error);
        }
    }

    let substituted_params: Vec<Type> = sig.params.iter().map(|p| apply_subst(p, &subst)).collect();
    let substituted_ret = apply_subst(&sig.ret, &subst);

    // CF-C2: the emitted call carries exactly the impl fn's params — never a
    // synthetic receiver. A delta here is an ICE, not a malformed call to AIR.
    debug_assert_eq!(
        typed_args.len(),
        substituted_params.len(),
        "CF-C2: associated-fn arg count must equal param count (no receiver prepended)"
    );

    // 4. Monomorphize the body (mirror the generic-impl method mono block).
    //    Non-generic impls skip mono: the one-shot emission is already concrete.
    let callee = if !sig.impl_type_params.is_empty() {
        let type_args: Vec<Type> = sig
            .impl_type_params
            .iter()
            .map(|p| subst.get(p).cloned().unwrap_or(Type::Error))
            .collect();
        let qualified_method_key = format!("{}::{}::{}", sig.module, type_name, expr.method);
        let base_mangled = build_mono_impl_method_mangled_name(&sig.qualified_name, &type_args);
        // PPS-0: an ASSOCIATED function called from inside a state-backed body is itself
        // state-backed. `Map::insert` reaches `Vec::with_capacity` through
        // `ensure_buckets`/`grow` → `filled`; without this the pre-sized bucket BUFFER (and its
        // header) allocate transiently while every surrounding instance is persistent — the exact
        // dangle the PPS-0 rehash test caught. Same inheritance rule as the method path; zero
        // effect outside a state-backed build (`state_mono_depth == 0`).
        let inherits_state_backing = tracker.state_mono_depth > 0;
        let mangled_callee = if inherits_state_backing {
            format!("{base_mangled}{}", crate::air::STATE_VEC_MONO_SUFFIX)
        } else {
            base_mangled
        };
        if tracker.cache.insert(mangled_callee.clone()) {
            if let Some((_decl, method_def, method_module)) = universe
                .generic_impl_methods
                .get(&qualified_method_key)
                .cloned()
            {
                tracker.depth += 1;
                if tracker.depth > MAX_MONOMORPH_DEPTH {
                    diagnostics.push(Diagnostic::error(
                        codes::T150,
                        format!(
                            "associated function `{type_name}::{}` monomorphization recursion exceeded {} depth",
                            expr.method, MAX_MONOMORPH_DEPTH
                        ),
                        Some(expr.span),
                    ));
                    tracker.depth -= 1;
                    tracker.cache.remove(&mangled_callee);
                } else if substituted_params.len() != method_def.params.len() {
                    diagnostics.push(Diagnostic::error(
                        codes::I012,
                        format!(
                            "internal: substituted_params arity ({}) != method_def.params arity ({}) for `{type_name}::{}`",
                            substituted_params.len(),
                            method_def.params.len(),
                            expr.method
                        ),
                        Some(expr.span),
                    ));
                    tracker.depth -= 1;
                    tracker.cache.remove(&mangled_callee);
                } else {
                    let mono_params: Vec<TypedParam> = substituted_params
                        .iter()
                        .zip(method_def.params.iter())
                        .map(|(ty, p)| TypedParam {
                            flow: false,
                            mutability: crate::ast::Mutability::Default,
                            name: p.name.clone(),
                            ty: ty.clone(),
                            taint: p.taint.unwrap_or(crate::ast::TaintLabel::Public),
                        })
                        .collect();
                    let mono_param_refinements: Vec<Option<Vec<crate::ast::RefinementClause>>> =
                        vec![None; mono_params.len()];
                    // CF-D9 (assoc-fn path): mirror the impl-method monomorph fix
                    // — a cross-module-monomorphized associated-fn body must
                    // resolve names in its DEFINING module's scope. map.sigil's
                    // `with_capacity` calls same-module free fns
                    // (`map_slots_for` / `map_filled_i64`); pre-fix the
                    // caller's sigs leaked through, failing T062. Vec's
                    // `new`/`with_capacity` call no vec free fn, so this is a
                    // no-op for them (byte-identical). Clone to drop the
                    // immutable `tracker` borrow before the `&mut tracker` arg.
                    let defining_sigs = tracker.workspace_sigs.get(method_module.as_str()).cloned();
                    if inherits_state_backing {
                        tracker.state_mono_depth += 1;
                    }
                    let method_context = TypeCheckContext::new(
                        defining_sigs.as_ref().unwrap_or(function_sigs),
                        actor_sigs,
                        &method_module,
                        universe,
                    );
                    let body = check_function_block(
                        &mono_params,
                        &substituted_ret,
                        &HashMap::new(),
                        &method_def.body,
                        method_context,
                        tracker,
                        diagnostics,
                        &mono_param_refinements,
                        None,
                        // PR-2b: mono re-entry seeds @ReadOnly from the method def
                        // (mono preserves param count + order).
                        &method_def
                            .params
                            .iter()
                            .map(|p| p.mutability)
                            .collect::<Vec<_>>(),
                        // DEF-2b PR-4: mono re-entry seeds region params from the method
                        // def (mono preserves param count + order).
                        &universe::param_regions_of(&method_def.params),
                        // DEF-2b PR-5: the method def's `where region` outlives pairs.
                        &universe::param_region_outlives_of(
                            &method_def.params,
                            &method_def.region_outlives,
                        ),
                        // A monomorphized method has no actor state in scope.
                        &HashMap::new(),
                        &std::collections::HashSet::new(),
                        super::super::BodyKind::Free,
                    );
                    if inherits_state_backing {
                        tracker.state_mono_depth -= 1;
                    }
                    tracker.functions.push(TypedFunction {
                        ret_flow: false,
                        name: mangled_callee.clone(),
                        export_name: mangled_callee.clone(),
                        kind: TypedFunctionKind::ModuleFunction,
                        externally_callable: matches!(
                            method_def.visibility,
                            crate::ast::Visibility::Public
                        ),
                        params: mono_params,
                        captures: Vec::new(),
                        ret: substituted_ret.clone(),
                        ret_taint: crate::ast::TaintLabel::Public,
                        // CF-C4: carry the method's declared effect row so the
                        // caller is effect-gated (an effectful constructor like
                        // `with_capacity ! { Alloc }` must require Alloc).
                        effects: resolve_effect_row(&method_def.effects, universe),
                        body,
                        span: method_def.span,
                    });
                    tracker.depth -= 1;
                }
            } else {
                diagnostics.push(Diagnostic::error(
                    codes::I011,
                    format!(
                        "internal: associated function `{type_name}::{}` present in function_sigs but missing from generic_impl_methods (collection bug)",
                        expr.method
                    ),
                    Some(expr.span),
                ));
                tracker.cache.remove(&mangled_callee);
            }
        }
        mangled_callee
    } else {
        sig.qualified_name.clone()
    };

    TypedExpr {
        ty: substituted_ret,
        kind: TypedExprKind::Call(TypedCallExpr {
            callee,
            args: typed_args,
        }),
        span: expr.span,
        refinement: None,
    }
}

/// Reroute a parser-produced `MethodCall` through cross-module function
/// dispatch when the "receiver" is actually a module name. Constructs an
/// equivalent `Call` AST node and runs the standard call-site logic.
fn infer_cross_module_call_via_methodcall(
    receiver_module: &str,
    expr: &MethodCallExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    // Build a synthetic Path: <receiver_module>::<method>
    let synthetic_callee = crate::ast::Path {
        segments: vec![receiver_module.to_owned(), expr.method.clone()],
        type_args: Vec::new(),
        span: expr.span,
    };
    let synthetic_call = crate::ast::CallExpr {
        callee: synthetic_callee,
        args: expr.args.clone(),
        span: expr.span,
    };
    infer_call_expr(
        &synthetic_call,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    )
}
