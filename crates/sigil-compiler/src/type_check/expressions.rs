//! Expression inference from AST nodes to typed expressions.
//!
//! `infer_expr` dispatches each expression form to the corresponding
//! `infer_*` routine. Built-in free-call intrinsics are isolated in the
//! `intrinsics` submodule; method intrinsics remain with method dispatch.

use std::collections::{HashMap, HashSet};

use super::capability_tc::{
    check_ask_expr, check_send_expr, check_spawn_expr, infer_cap_draw_expr,
    infer_cap_restrict_deadline_expr, infer_cap_restrict_expr, infer_cap_split_expr,
    infer_declassify_ct_expr, infer_declassify_expr, infer_grant_expr, infer_handle_expr,
    infer_mint_expr, infer_region_expr,
};
use super::resolve::{
    RecordSubstFault, apply_subst, build_record_construction_subst, infer_literal_type,
    is_machine_integer_type, register_concrete_enum, render_binary_op, render_type,
    resolve_int_literals_in_expr, resolve_int_literals_or_reject, resolve_type_expr,
    try_array_size_mismatch_diagnostic, type_compatible, type_contains_cap, type_contains_never,
    type_contains_typestate, type_contains_wide_int,
};
use super::statements::check_block;
use super::{
    BorrowContextGuard, ExpectedTypeGuard, MonomorphTracker, Type, TypeCheckContext, TypeUniverse,
    find_free_vars, lookup_pattern_refinement, undefined_local_diagnostic_with_edit,
};
use crate::air::mangle_type;
use crate::ast::{
    ArrayLitExpr, BinaryExpr, BinaryOp, BorrowExpr, ClosureExpr, Expr, FieldAccessExpr, IndexExpr,
    Literal, PathExpr, RecordConstructExpr, RefinementOp, RefinementRhs, ResultCtorExpr, TryExpr,
    TupleExpr,
};
use crate::diagnostics::{Diagnostic, codes};
use crate::typed_ast::{
    TypedArrayLitExpr, TypedBinaryExpr, TypedBlock, TypedBorrowExpr, TypedCapture,
    TypedClauseHandleExpr, TypedClosureConstructExpr, TypedEnumConstructExpr, TypedExpr,
    TypedExprKind, TypedFieldAccessExpr, TypedFunction, TypedFunctionKind, TypedHandleClause,
    TypedIndexExpr, TypedParam, TypedPerformExpr, TypedRecordConstructExpr, TypedResultCtorExpr,
    TypedResumeExpr, TypedSliceExpr, TypedTryExpr,
};

mod calls;
use calls::infer_call_expr;
mod intrinsics;
mod methods;
use methods::infer_method_call_expr;

/// Effect Handlers (EH1): shape-check a `perform E.op(args)`. Emits E006 (unknown
/// effect), E005 (unknown operation), or E007 (arg-count mismatch). A WELL-FORMED
/// perform is still rejected with E004 ("not yet lowered") and returns a
/// `Type::Error` placeholder, so it never reaches AIR — the byte-identical-AIR
/// invariant holds until the lowering rungs (EH3/EH5) replace the gate. Argument
/// expressions are type-checked so their own errors surface.
fn infer_perform_expr(
    expr: &crate::ast::PerformExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let universe = context.universe;
    let mut typed_args: Vec<TypedExpr> = expr
        .args
        .iter()
        .map(|arg| infer_expr(arg, env, current_return, context, tracker, diagnostics))
        .collect();

    let placeholder = TypedExpr {
        ty: Type::Error,
        kind: TypedExprKind::Literal(Literal::Int(0)),
        span: expr.span,
        refinement: None,
    };

    // E006: the named effect must be declared.
    if universe.effect_registry.lookup(&expr.effect).is_none() {
        diagnostics.push(Diagnostic::error(
            codes::E006,
            format!("unknown effect `{}` in `perform`", expr.effect),
            Some(expr.effect_span),
        ));
        return placeholder;
    }

    // E005 (unknown operation) / E007 (arity) — and on success, the operation's
    // return type (the resumed-value type) becomes the perform's type.
    let ret = match universe
        .effect_ops
        .get(&expr.effect)
        .and_then(|ops| ops.iter().find(|o| o.name == expr.op))
    {
        None => {
            diagnostics.push(Diagnostic::error(
                codes::E005,
                format!("effect `{}` has no operation `{}`", expr.effect, expr.op),
                Some(expr.span),
            ));
            return placeholder;
        }
        Some(op) => {
            if expr.args.len() != op.params.len() {
                diagnostics.push(Diagnostic::error(
                    codes::E007,
                    format!(
                        "operation `{}.{}` expects {} argument(s), got {}",
                        expr.effect,
                        expr.op,
                        op.params.len(),
                        expr.args.len()
                    ),
                    Some(expr.span),
                ));
                return placeholder;
            }
            // Each argument must match the operation's DECLARED parameter type
            // (mirrors `infer_call_expr`'s T071). This is load-bearing for the EH4
            // desugar: it reads the operation signature off the `perform` site, so an
            // unchecked arg type (e.g. `perform E.op(true)` for `op(p: i64)`) would
            // build a mistyped evidence closure → invalid wasm / ICE / a silent
            // miscompile (a `u64` arg selecting unsigned division). Run during
            // inference so an `IntLit` arg is still range-checked (not yet defaulted
            // to i64), avoiding over-rejection of `perform E.op(99)` for narrow ops.
            let mut had_mismatch = false;
            for (expected, arg) in op.params.iter().zip(typed_args.iter_mut()) {
                if !type_compatible(expected, &arg.ty) {
                    had_mismatch = true;
                    diagnostics.push(Diagnostic::error(
                        codes::T071,
                        format!(
                            "operation `{}.{}` expected argument of type `{}`, found `{}`",
                            expr.effect,
                            expr.op,
                            render_type(expected),
                            render_type(&arg.ty)
                        ),
                        Some(arg.span),
                    ));
                } else {
                    // Narrow a fitting `IntLit` argument to the DECLARED parameter
                    // type. The EH4 desugar reads the operation's parameter types off
                    // this `Perform` node; if a literal stayed `IntLit` it would
                    // `mangle_type` to i64 against a narrow-int (i32/u32) parameter and
                    // the synthesized evidence closure / IndirectCall would be
                    // width-mismatched → non-validating wasm (EH4.2 sweep D1). Mirrors
                    // the call-argument path's `resolve_int_literals_in_expr`.
                    resolve_int_literals_in_expr(arg, expected);
                }
            }
            if had_mismatch {
                return placeholder;
            }
            op.ret.clone()
        }
    };

    // Well-formed: a real typed `Perform` node whose type is the operation's
    // return type. The E004 "not yet lowered" gate runs as a POST-type-check pass
    // (`effect_handler_gate`) so the effect checker can see this node first; the
    // node never reaches AIR, so byte-identical AIR holds until EH4.
    TypedExpr {
        ty: ret,
        kind: TypedExprKind::Perform(TypedPerformExpr {
            effect: expr.effect.clone(),
            op: expr.op.clone(),
            args: typed_args,
        }),
        span: expr.span,
        refinement: None,
    }
}

/// Effect Handlers (EH3): check + type a clause-form `handle <scrutinee> { E.op(x)
/// => .. }`. Resolves each clause's effect/operation (E006/E005), binder arity
/// (E007), and verifies coverage as an exact set (E008). Clause BODIES are
/// type-checked, with each binder bound to the operation's parameter type. A
/// well-formed clause-handle becomes a real `TypedExprKind::ClauseHandle`; the
/// E004 "not yet lowered" gate runs as a POST-type-check pass
/// (`effect_handler_gate`) so the effect checker can see the node first. On any
/// error it returns a `Type::Error` placeholder (no node).
fn infer_clause_handle_expr(
    expr: &crate::ast::ClauseHandleExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let universe = context.universe;
    let typed_scrutinee = infer_expr(
        &expr.scrutinee,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    let result_ty = typed_scrutinee.ty.clone();

    let placeholder = TypedExpr {
        ty: Type::Error,
        kind: TypedExprKind::Literal(Literal::Int(0)),
        span: expr.span,
        refinement: None,
    };

    let mut covered: Vec<(String, String)> = Vec::new();
    let mut typed_clauses: Vec<TypedHandleClause> = Vec::new();
    let mut had_error = false;

    for clause in &expr.clauses {
        if universe.effect_registry.lookup(&clause.effect).is_none() {
            diagnostics.push(Diagnostic::error(
                codes::E006,
                format!("unknown effect `{}` in handle clause", clause.effect),
                Some(clause.span),
            ));
            had_error = true;
            continue;
        }
        // Resolve the operation; clone its parameter types so the universe borrow
        // is released before the clause body is checked.
        let op_params: Option<Vec<Type>> = universe
            .effect_ops
            .get(&clause.effect)
            .and_then(|ops| ops.iter().find(|o| o.name == clause.op))
            .map(|o| o.params.clone());
        let op_params = match op_params {
            None => {
                diagnostics.push(Diagnostic::error(
                    codes::E005,
                    format!(
                        "effect `{}` has no operation `{}`",
                        clause.effect, clause.op
                    ),
                    Some(clause.span),
                ));
                had_error = true;
                continue;
            }
            Some(params) => {
                if clause.binders.len() != params.len() {
                    diagnostics.push(Diagnostic::error(
                        codes::E007,
                        format!(
                            "handle clause for `{}.{}` binds {} value(s), but the operation has {} parameter(s)",
                            clause.effect,
                            clause.op,
                            clause.binders.len(),
                            params.len()
                        ),
                        Some(clause.span),
                    ));
                    had_error = true;
                }
                params
            }
        };
        if covered
            .iter()
            .any(|(e, o)| e == &clause.effect && o == &clause.op)
        {
            diagnostics.push(Diagnostic::error(
                codes::E008,
                format!(
                    "duplicate handle clause for `{}.{}`",
                    clause.effect, clause.op
                ),
                Some(clause.span),
            ));
            had_error = true;
        } else {
            covered.push((clause.effect.clone(), clause.op.clone()));
        }

        // Type the clause body with each binder bound to its operation parameter
        // type (zip stops at the shorter on an arity mismatch — already E007'd).
        let mut clause_env = env.clone();
        for (binder, pty) in clause.binders.iter().zip(op_params.iter()) {
            clause_env.insert(binder.clone(), pty.clone());
        }
        // RF-M2 BARRIER: clause bodies are evidence-passing closures (a
        // DIFFERENT function post-desugar) whose binders may shadow an
        // enclosing range-loop var — same fail-closed treatment as closures.
        let saved_range_facts = std::mem::take(&mut tracker.range_loop_facts);
        let mut clause_mutables = HashSet::new();
        let typed_body = check_block(
            &clause.body,
            &mut clause_env,
            &mut clause_mutables,
            current_return,
            context,
            tracker,
            diagnostics,
            false,
        );
        tracker.range_loop_facts = saved_range_facts;
        typed_clauses.push(TypedHandleClause {
            effect: clause.effect.clone(),
            op: clause.op.clone(),
            binders: clause.binders.clone(),
            body: typed_body,
        });
    }

    // Coverage (E008): every operation of each discharged effect must have a clause.
    let handled: std::collections::BTreeSet<&String> = covered.iter().map(|(e, _)| e).collect();
    for eff in handled {
        if let Some(ops) = universe.effect_ops.get(eff) {
            for op in ops {
                if !covered.iter().any(|(e, o)| e == eff && o == &op.name) {
                    diagnostics.push(Diagnostic::error(
                        codes::E008,
                        format!("handle does not cover operation `{}.{}`", eff, op.name),
                        Some(expr.span),
                    ));
                    had_error = true;
                }
            }
        }
    }

    if had_error {
        return placeholder;
    }

    // Well-formed: a real typed `ClauseHandle`. The handle's type is the
    // scrutinee's type (the resumed result for scoped clauses; abortive result
    // typing is refined in EH4). Gated by the post-type-check effect_handler_gate.
    TypedExpr {
        ty: result_ty,
        kind: TypedExprKind::ClauseHandle(TypedClauseHandleExpr {
            scrutinee: Box::new(typed_scrutinee),
            clauses: typed_clauses,
        }),
        span: expr.span,
        refinement: None,
    }
}

/// Effect Handlers (EH3): type a `resume <value>` inside a scoped clause body.
/// `resume` transfers control back to the `perform` site, so the expression does
/// not fall through — its type is the bottom `Type::Never`. (The check that the
/// resumed value matches the operation's return type lands with scoped lowering,
/// EH4.) Gated before AIR.
fn infer_resume_expr(
    expr: &crate::ast::ResumeExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let value = infer_expr(
        &expr.value,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    TypedExpr {
        ty: Type::Never,
        kind: TypedExprKind::Resume(TypedResumeExpr {
            value: Box::new(value),
        }),
        span: expr.span,
        refinement: None,
    }
}

pub(super) fn infer_expr(
    expr: &Expr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    match expr {
        Expr::Literal(expr) => TypedExpr {
            ty: infer_literal_type(&expr.literal),
            kind: TypedExprKind::Literal(expr.literal.clone()),
            span: expr.span,

            refinement: None,
        },
        Expr::Path(expr) => {
            infer_path_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::ResultCtor(expr) => {
            check_result_ctor_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Try(expr) => check_try_expr(expr, env, current_return, context, tracker, diagnostics),
        Expr::Send(expr) => {
            check_send_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Ask(expr) => check_ask_expr(expr, env, current_return, context, tracker, diagnostics),
        Expr::Spawn(expr) => {
            check_spawn_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Call(expr) => {
            infer_call_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Binary(expr) => {
            infer_binary_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        // `Expr::EnumConstruct` (the UNTYPED AST node) is never produced: the
        // trusted parser does not emit it (parser.rs has zero references — see the
        // `UNHANDLED` arm in parser_differential.rs and docs/specs/parser-in-sigil.md),
        // no foreign frontend builds it, and no desugar pass constructs it. Real
        // enum construction is inferred from a call (`Some(x)`, `V(x)`) or a path
        // (a nullary variant) and emits the TYPED `TypedExprKind::EnumConstruct`
        // directly in `infer_call_expr` / `infer_path_expr`. This is an AP11
        // "no unwired paths" backstop: if a frontend/desugar ever starts emitting
        // this node, whoever wires it up MUST route payload fields through the
        // value-position `never` (T279) guard in `infer_arg_with_expected` — else a
        // `trap()` payload reaches AIR's C-NEVER `lower_type`/`mangle_type` and ICEs.
        Expr::EnumConstruct(expr) => unreachable!(
            "Expr::EnumConstruct is never produced by the parser, a frontend, or a \
             desugar pass; enum construction builds the typed node directly in \
             infer_call_expr/infer_path_expr (got `{}::{}`)",
            expr.enum_name, expr.variant
        ),
        Expr::RecordConstruct(expr) => {
            infer_record_construct_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::FieldAccess(expr) => {
            infer_field_access_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::CapRestrict(expr) => {
            infer_cap_restrict_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::CapRestrictDeadline(expr) => infer_cap_restrict_deadline_expr(
            expr,
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        ),
        Expr::CapSplit(expr) => {
            infer_cap_split_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::CapDraw(expr) => {
            infer_cap_draw_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Mint(expr) => {
            infer_mint_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::ArrayLit(expr) => {
            infer_array_lit_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Tuple(expr) => {
            infer_tuple_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Index(expr) => {
            infer_index_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Slice(slice) => {
            infer_slice_expr(slice, env, current_return, context, tracker, diagnostics)
        }
        Expr::MethodCall(expr) => {
            infer_method_call_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Closure(expr) => {
            infer_closure_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Borrow(expr) => {
            infer_borrow_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Grant(expr) => {
            infer_grant_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Handle(expr) => {
            infer_handle_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        // Effect Handlers (EH1): `perform E.op(args)` is shape-checked here —
        // E006 (unknown effect), E005 (unknown operation), E007 (wrong arg
        // count). A WELL-FORMED perform is still rejected with E004 ("not yet
        // lowered") so it never reaches AIR; the gate moves to the lowering rung
        // (EH3/EH5). Clause-`handle` and `resume` stay E004-gated until EH2+.
        Expr::Perform(e) => {
            infer_perform_expr(e, env, current_return, context, tracker, diagnostics)
        }
        // Effect Handlers (EH2): a clause-form `handle e { Op(x) => .. }` is
        // checked here — clause effect/operation resolution (E006/E005), binder
        // arity (E007), and coverage (E008). A WELL-FORMED clause-handle is still
        // gated with E004 (lowering lands in EH3/EH5). Clause bodies are not
        // typed in this rung (their binder types need operation parameter types,
        // deferred), so `resume` inside them is not reached.
        Expr::ClauseHandle(e) => {
            infer_clause_handle_expr(e, env, current_return, context, tracker, diagnostics)
        }
        Expr::Resume(e) => infer_resume_expr(e, env, current_return, context, tracker, diagnostics),
        Expr::Declassify(expr) => {
            infer_declassify_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::DeclassifyCt(expr) => {
            infer_declassify_ct_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::Region(expr) => {
            infer_region_expr(expr, env, current_return, context, tracker, diagnostics)
        }
        Expr::FString(expr) => {
            infer_fstring_expr(expr, env, current_return, context, tracker, diagnostics)
        }
    }
}

/// PR-E3 (Option 2b): an `f"…{e}…"` string types as `str`; each interpolation hole
/// is type-checked and must be `str` (PR-E3a; PR-E3b widens to i64/bool). A
/// non-stringifiable hole emits T262 at the hole's span (ET-E10).
///
/// This returns the typed `FString` node — it does NOT lower here. Lowering to a
/// `str_concat` chain happens in AIR (`lower_expr_into`), which has `function_ids`
/// (str_concat is injected by the `FStrBegin` ambient trigger) — cross-module
/// str_concat resolution is awkward at type-check, and the no-stdlib
/// `typecheck_differential` never runs AIR, so it compares this `str`-typed node
/// directly → parity. AIR/wasm thus gain ONE lowering arm (not the originally-planned
/// pre-AIR pass); the differential parity that Option 2b buys is preserved either way.
fn infer_fstring_expr(
    expr: &crate::ast::FStringExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    use crate::ast::FStringPart;
    use crate::typed_ast::{TypedFStringExpr, TypedFStringPart};
    let mut parts: Vec<TypedFStringPart> = Vec::with_capacity(expr.parts.len());
    for part in &expr.parts {
        match part {
            FStringPart::Literal(text, _span) => {
                parts.push(TypedFStringPart::Literal(text.clone()));
            }
            FStringPart::Hole(hole) => {
                let typed = infer_expr(hole, env, current_return, context, tracker, diagnostics);
                // PR-E3b accepts str / i64 / bool holes (i64 auto-converts via
                // `str_itoa`, bool via `str_of_bool` at the pre-AIR lowering). An
                // `Error`-typed hole already reported its own diagnostic, so don't pile
                // on T262 there. Any other type (f64, composite, …) is not stringifiable.
                if !matches!(typed.ty, Type::Str | Type::I64 | Type::Bool | Type::Error) {
                    diagnostics.push(Diagnostic::error(
                        codes::T262,
                        "interpolation hole must be `str`, `i64`, or `bool`",
                        Some(hole.span()),
                    ));
                }
                parts.push(TypedFStringPart::Hole(Box::new(typed)));
            }
        }
    }
    // The typed FString node SURVIVES to AIR, where `lower_fstring` folds the parts
    // into a `str_concat` chain (function_ids holds str_concat via the FStrBegin
    // ambient trigger). The no-stdlib `typecheck_differential` never runs AIR, so it
    // compares this `str` node directly → parity. (Doc comment above explains why
    // lowering happens at AIR, not here: cross-module str_concat resolution.)
    TypedExpr {
        ty: Type::Str,
        kind: TypedExprKind::FString(TypedFStringExpr { parts }),
        span: expr.span,
        refinement: None,
    }
}

pub(super) fn infer_path_expr(
    expr: &PathExpr,
    env: &HashMap<String, Type>,
    _current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let universe = context.universe;
    let name = expr.path.display_name();

    // PR B / N14-PRB: qualified unit-variant construction reroute.
    // `Option::None` (with no parens) parses as `Expr::Path` with
    // 2 segments. If segments[0] is a known enum AND segments[1]
    // is a unit (zero-payload) variant of that enum, construct
    // the variant directly. Routes through the same TypedExpr
    // shape as `Option::None()` would (had grammar admitted parens
    // on unit variants).
    //
    // For non-unit variants, this path emits T070 (missing args)
    // by NOT matching; the user's invocation lacks the required
    // parens + args and the existing T060/T062 cascade fires as
    // a generic "unresolved path" diagnostic. T070 specific
    // "variant requires N payload args" is left to a future UX
    // polish.
    if expr.path.segments.len() == 2 {
        let qualifier = &expr.path.segments[0];
        let variant_segment = &expr.path.segments[1];
        if let Some((type_params, variants)) = universe.enums.get(qualifier)
            && let Some((idx, (_, payload_types))) = variants
                .iter()
                .enumerate()
                .find(|(_, (n, _))| n == variant_segment)
            && payload_types.is_empty()
        {
            // A unit variant has no payload from which to infer generic arguments. Resolve them
            // from the expected type when available and register the same concrete layout used by
            // qualified construction; otherwise retain Error placeholders for normal diagnostics.
            let (concrete_ty, mangled_name) = if type_params.is_empty() {
                (Type::Named(qualifier.clone(), vec![]), qualifier.clone())
            } else {
                let concrete_args = if let Some(Type::Named(exp_name, exp_args)) =
                    &tracker.current_expected_type
                    && exp_name == qualifier
                    && exp_args.len() == type_params.len()
                {
                    exp_args.clone()
                } else {
                    vec![Type::Error; type_params.len()]
                };
                let cty = Type::Named(qualifier.clone(), concrete_args.clone());
                let mangled = mangle_type(&cty);
                let variants_clone = variants.clone();
                let type_params_clone = type_params.clone();
                register_concrete_enum(
                    tracker,
                    &mangled,
                    &variants_clone,
                    &type_params_clone,
                    &concrete_args,
                );
                (cty, mangled)
            };
            return TypedExpr {
                ty: concrete_ty,
                kind: TypedExprKind::EnumConstruct(TypedEnumConstructExpr {
                    enum_name: mangled_name,
                    variant_index: idx as u32,
                    fields: Vec::new(),
                }),
                span: expr.span,
                refinement: None,
            };
        }
    }

    // Single-segment or fully-qualified: direct variable lookup
    if let Some(ty) = env.get(&name).cloned() {
        // Wall 4 Step 6: pattern-match refinement narrowing. If this
        // identifier was bound by a `match`/`if let` arm whose variant
        // carried Literal-RHS refinements (per N22-S6), attach them
        // here. Walks the stack top-down so inner `match` scopes
        // shadow outer ones. Per N15-S6, the attachment happens
        // BEFORE the arm body type-checks; this read is inside the
        // arm body so the stack frame is already populated.
        let refinement = lookup_pattern_refinement(tracker, &name);
        // Actor-state (M2): a bare name declared in the enclosing actor's
        // `state { … }` lowers to a distinct `TypedExprKind::StateField` (NOT a
        // `Local`) — forcing every pass to decide what a state access means (AIR:
        // load off the state pointer; check_assign: write gated by construction
        // phase; ownership: borrow-only caps; taint: label from the declared field
        // type). A binding cannot shadow a state field (N006 for params; the
        // let/pattern-shadow guard rejects the rest), so membership is exact.
        let kind = if tracker.state_fields.contains_key(&name) {
            TypedExprKind::StateField(name)
        } else {
            TypedExprKind::Local(name)
        };
        return TypedExpr {
            ty,
            kind,
            span: expr.span,
            refinement,
        };
    }

    // Multi-segment: first segment as variable, rest as field access chain
    // Handles point.x, rect.top_left.x, etc.
    if expr.path.segments.len() >= 2 {
        let base_name = &expr.path.segments[0];
        if let Some(base_ty) = env.get(base_name).cloned() {
            let mut current_ty = base_ty;
            // Actor-state: a multi-segment base that NAMES a state field lowers to
            // `StateField`, symmetric with the single-segment path above (line ~685).
            // Before this, a dotted/indexed base (`d.v`, `a[i]`) resolved to a bare
            // `Local`, hiding the state root from every state-aware pass: the T001
            // taint sink-check and the T123 immutability gate (both keyed on a
            // `StateField` root) missed write-throughs, and AIR lowering could not
            // resolve the base local for a `mut` aggregate field (an ICE). Routing it
            // through `StateField` closes the projected-place launder AND the ICE; a
            // NON-`mut` field still reads from the prologue env slot (byte-identical).
            let base_kind = if tracker.state_fields.contains_key(base_name) {
                TypedExprKind::StateField(base_name.clone())
            } else {
                TypedExprKind::Local(base_name.clone())
            };
            let mut current_expr = TypedExpr {
                ty: current_ty.clone(),
                kind: base_kind,
                span: expr.span,

                refinement: None,
            };

            for segment in expr.path.segments.iter().skip(1) {
                // Auto-deref: look through references
                let derefed_ty = match &current_ty {
                    Type::Ref(inner, _) => inner.as_ref(),
                    other => other,
                };
                match derefed_ty {
                    Type::Named(type_name, type_args) => {
                        if let Some((type_params, fields)) = universe.records.get(type_name) {
                            // EX-1 (HK3 hardening): a wrong-arity generic record
                            // (`Pair<i64>` against `record Pair<A, B>`) is now
                            // rejected upstream with T231 (validate_lowered_type
                            // / resolve_annotated_let_type). Type-checking still
                            // CONTINUES past an error to collect more, so this
                            // site can still SEE the malformed `Type::Named`. It
                            // must NOT panic (the old N10-PRDF debug_assert) and
                            // must NOT fall through to the un-substituted
                            // `field_ty` (which would leak a `Generic` into AIR
                            // mangling in release) — the arity-mismatch branch
                            // below yields `Type::Error` instead.
                            if let Some((_, field_ty)) = fields.iter().find(|(n, _)| n == segment) {
                                // Wall 4 Step 2: clone type_name into an owned
                                // String BEFORE mutating `current_ty` so the
                                // borrow checker is happy when we call the
                                // refinement helper after the reassignment.
                                let source_record_name: String = type_name.clone();
                                // PR D follow-up: substitute the field's
                                // declared type against the receiver's
                                // concrete type-args. Adapted to
                                // mutable-state context: `current_ty` is the
                                // loop variable for path segments; this
                                // substitution feeds into segment N+1's
                                // pattern match per N11-PRDF.
                                //
                                // Necessary HERE (in addition to
                                // `infer_field_access_expr` which got the
                                // same fix in PR D commit #2) because
                                // `self.value` parses as `Expr::Path`, not
                                // `Expr::FieldAccess`, and routes through
                                // this function. Without substitution here,
                                // generic impl method bodies produce
                                // `Type::Generic("T")` at every dotted-path
                                // field access, escaping into AIR's
                                // mangle_type and ICEing.
                                //
                                // N6-PRDF gate: substitution applies
                                // whenever both type_params and type_args
                                // are non-empty AND arity-matched. There is
                                // NO fast-path bypass on all-top-level-
                                // concrete type_args because nested generic
                                // field types (`inner: Inner<T>`) still need
                                // substitution.
                                //
                                // N7-PRDF: the fallthrough branch is sound
                                // only when `type_params.is_empty()` —
                                // non-generic records. The defensive assert
                                // above catches malformed type_args on
                                // generic records (N10-PRDF) so the
                                // fallthrough path never sees them.
                                current_ty = if type_params.is_empty() {
                                    // Non-generic record: the field type is
                                    // already concrete.
                                    field_ty.clone()
                                } else if type_params.len() == type_args.len() {
                                    let subst: HashMap<String, Type> = type_params
                                        .iter()
                                        .zip(type_args.iter())
                                        .map(|(p, a)| (p.clone(), a.clone()))
                                        .collect();
                                    apply_subst(field_ty, &subst)
                                } else {
                                    // Malformed arity (T231 fired upstream).
                                    // Don't substitute against a mismatched
                                    // arg list — that would leak `Generic` into
                                    // AIR; surface `Error` and let checking
                                    // continue.
                                    Type::Error
                                };
                                // Attach refinement on the path-chain
                                // FieldAccess via the V1 single-location
                                // helper (same as `infer_field_access_expr`).
                                // `idx.value` parses as `Expr::Path`, not
                                // `Expr::FieldAccess`, so this is the
                                // attachment point for dotted-path access.
                                let refinement = compute_field_access_refinement(
                                    universe,
                                    Some(source_record_name.as_str()),
                                    segment,
                                    &current_ty,
                                );
                                current_expr = TypedExpr {
                                    ty: current_ty.clone(),
                                    kind: TypedExprKind::FieldAccess(TypedFieldAccessExpr {
                                        object: Box::new(current_expr),
                                        field: segment.clone(),
                                    }),
                                    span: expr.span,

                                    refinement,
                                };
                            } else {
                                diagnostics.push(Diagnostic::error(
                                    codes::T120,
                                    format!("type `{type_name}` has no field `{segment}`"),
                                    Some(expr.span),
                                ));
                                return TypedExpr {
                                    ty: Type::Error,
                                    kind: TypedExprKind::Literal(Literal::Int(0)),
                                    span: expr.span,

                                    refinement: None,
                                };
                            }
                        } else {
                            diagnostics.push(Diagnostic::error(
                                codes::T121,
                                format!("type `{type_name}` is not a record type"),
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
                    Type::Error => {
                        return TypedExpr {
                            ty: Type::Error,
                            kind: TypedExprKind::Literal(Literal::Int(0)),
                            span: expr.span,

                            refinement: None,
                        };
                    }
                    other => {
                        diagnostics.push(Diagnostic::error(
                            codes::T122,
                            format!(
                                "cannot access field `.{segment}` on non-record type `{}`",
                                render_type(other)
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

            return current_expr;
        }
    }

    // Fallback: check if name is a no-payload enum variant (e.g., None)
    if expr.path.segments.len() == 1 {
        for (enum_name, (type_params, variants)) in &universe.enums {
            if let Some((idx, _)) = variants
                .iter()
                .enumerate()
                .find(|(_, (vname, ptypes))| vname == &name && ptypes.is_empty())
            {
                // GAP 2: a no-payload variant (`None`) carries no value to infer
                // its enum's type params from, so bind them from
                // `current_expected_type` — but ONLY when it names THIS enum
                // (CF-A1 enum identity), with matching arity (CF-A1), and FULLY
                // CONCRETE args (CF-A2). A non-matching / wrong-arity / abstract /
                // un-threaded expected type falls back to argless `vec![]`
                // (fail-closed: the downstream return/let check then emits
                // T049/T041), so an abstract `V` is never bound into the typed AST.
                let resolved_args = match &tracker.current_expected_type {
                    Some(Type::Named(exp_enum, exp_args))
                        if exp_enum == enum_name
                            && !exp_args.is_empty()
                            && exp_args.len() == type_params.len()
                            && exp_args.iter().all(type_is_concrete) =>
                    {
                        exp_args.clone()
                    }
                    _ => Vec::new(),
                };
                // CF-A1 fail-fast: a wrong-arity bind would ICE in AIR `mangle_type`;
                // catch it at the source instead of emitting a malformed type.
                debug_assert!(
                    resolved_args.is_empty() || resolved_args.len() == type_params.len(),
                    "ICE: bare variant `{name}` of `{enum_name}` resolved {} args but the enum declares {} type params",
                    resolved_args.len(),
                    type_params.len(),
                );
                let concrete_ty = Type::Named(enum_name.clone(), resolved_args.clone());
                let lowered_enum_name = if type_params.is_empty() || resolved_args.is_empty() {
                    enum_name.clone()
                } else {
                    let mangled = mangle_type(&concrete_ty);
                    register_concrete_enum(
                        tracker,
                        &mangled,
                        variants,
                        type_params,
                        &resolved_args,
                    );
                    mangled
                };
                return TypedExpr {
                    ty: concrete_ty,
                    kind: TypedExprKind::EnumConstruct(TypedEnumConstructExpr {
                        enum_name: lowered_enum_name,
                        variant_index: idx as u32,
                        fields: Vec::new(),
                    }),
                    span: expr.span,

                    refinement: None,
                };
            }
        }
    }

    // Module-level const: a bare reference inlines the const's declared literal
    // value (SIGIL `const` is otherwise declaration-only — `collect_type_universe`
    // populated `universe.consts`). The declared type is authoritative, so e.g. a
    // `const T: i64 = 9` used where a `u32` is expected errors like any i64.
    if let Some((const_ty, value)) = universe.consts.get(&name) {
        return TypedExpr {
            ty: const_ty.clone(),
            kind: TypedExprKind::Literal(value.clone()),
            span: expr.span,
            refinement: None,
        };
    }

    // Truly undefined. Bare-identifier site → attach a structured edit (the
    // span covers exactly the identifier, so the suggestion is a safe drop-in).
    diagnostics.push(undefined_local_diagnostic_with_edit(
        &name,
        format!("undefined local `{name}`"),
        env,
        expr.span,
    ));
    TypedExpr {
        ty: Type::Error,
        kind: TypedExprKind::Literal(Literal::Int(0)),
        span: expr.span,

        refinement: None,
    }
}

/// CF-I1: a type may be pinned as an expected type / narrowed against ONLY if it
/// is FULLY concrete — no `Generic` anywhere, including nested (`Vec<T>` must NOT
/// pin, or fill-unbound would bind an inner call's param to the outer `T`).
fn type_is_concrete(t: &Type) -> bool {
    match t {
        Type::Generic(_) | Type::Error | Type::IntLit(_) => false,
        Type::Named(_, args) => args.iter().all(type_is_concrete),
        Type::Array { elem, .. } => type_is_concrete(elem),
        Type::Fn(params, ret, _, _) => params.iter().all(type_is_concrete) && type_is_concrete(ret),
        Type::Ref(inner, _) | Type::Slice(inner) | Type::Ptr(inner) | Type::MutPtr(inner) => {
            type_is_concrete(inner)
        }
        // Scalar leaves, `Cap` (deadline literals are i64, no nested Type),
        // `ActorRef`, `Str`, `Unit` are concrete.
        _ => true,
    }
}

/// True iff `t` contains a `Type::Generic` anywhere in its structure
/// (recursing through every composite — including `Tuple`, which
/// `type_is_concrete` does NOT descend into).
///
/// The method-call closure-arg check uses this as an ICE-guard on BOTH
/// sides before routing a `Type::Fn` argument through `type_compatible`:
/// that function's `(Generic, _) | (_, Generic)` arm is a deliberate panic
/// (a generic must never survive monomorphization into compatibility
/// checking), so an unsubstituted generic — e.g. a closure literal
/// `fn(x: T) -> T` written against an enclosing `<T>` whose receiver
/// never bound concretely (already T231/T232) — must be screened OUT
/// rather than fed in.
fn type_mentions_generic(t: &Type) -> bool {
    match t {
        Type::Generic(_) => true,
        Type::Named(_, args) => args.iter().any(type_mentions_generic),
        Type::Array { elem, .. } => type_mentions_generic(elem),
        Type::Fn(params, ret, _, _) => {
            params.iter().any(type_mentions_generic) || type_mentions_generic(ret)
        }
        Type::Ref(inner, _) | Type::Slice(inner) | Type::Ptr(inner) | Type::MutPtr(inner) => {
            type_mentions_generic(inner)
        }
        Type::Tuple(elems) => elems.iter().any(type_mentions_generic),
        _ => false,
    }
}

/// PR #132/#135: infer a call/field argument with an EXPECTED type pinned —
/// two complementary effects, both reusing existing machinery.
///
/// - **Mechanism 1 (CF-I1/CF-I4):** when `target` is a CONCRETE type (not
///   `Generic`/`Error`/`Unit`), push it as `current_expected_type` for the
///   duration of THIS inference only (RAII, block-scoped), so a nested generic
///   call (`Vec::new()`) can fill its unbound type param from the slot's type.
/// - **Mechanism 2 (CF-I3, narrow half):** afterward, narrow a *fitting*
///   `IntLit` leaf to the concrete target (the same `resolve_int_literals_in_expr`
///   the let-binding site uses). A NON-fitting literal stays `IntLit` and is
///   caught by the caller's downstream `type_compatible` check (overflow → hard
///   error), exactly like `check_let`.
fn infer_arg_with_expected(
    arg: &crate::ast::Expr,
    target: Option<&Type>,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    // CF-I1: only a FULLY-concrete type may pin or narrow.
    let pin = target.filter(|&t| type_is_concrete(t));
    // CF-I4: the guard scopes EXACTLY this one inference; Drop restores prior.
    let mut typed = {
        let mut guard = ExpectedTypeGuard::push(tracker, pin.cloned());
        infer_expr(
            arg,
            env,
            current_return,
            context,
            guard.tracker_mut(),
            diagnostics,
        )
    };
    if let Some(t) = pin
        && type_compatible(t, &typed.ty)
    {
        // Narrow fitting IntLit leaves to the pinned target, and REJECT a
        // non-fitting binop leaf (e.g. `f(0 - 2147483648)` for an i32
        // param) as T071 instead of letting it default to i64 and emit a
        // width-mismatched binary op (INVALID wasm). Mirrors the
        // single-literal `f(2147483648)` overflow, which is already T071.
        // The complementary top-level-stays-IntLit case (where this guard's
        // `type_compatible` is false) is caught by callers' own T071 arms.
        resolve_int_literals_or_reject(&mut typed, t, codes::T071, diagnostics);
    }
    // F003 / value-position `trap()` (Tier A): an argument-like position — a call
    // argument, a record-field value, an enum payload, a method argument (every
    // caller of this shared helper) — cannot receive a DIVERGING value. A `never`
    // arg (`id(trap())`, `Some(trap())`, `Box { val: trap() }`) is the inference
    // hole: against a GENERIC parameter `type_compatible` does not reject it, so
    // `unify` binds the type param to `Never` and the resulting monomorphization
    // key ICEs at `mangle_type` — a TYPE-CHECK-TIME `mangle_type` call, so a bare
    // diagnostic cannot stop the pipeline in time. Reject it (T279) AND POISON the
    // argument to `Type::Error`, which mangles/lowers cleanly and suppresses the
    // cascade, so inference proceeds without the ICE. An aggregate whose element
    // is `never` was already poisoned at its own tuple/array construction site, so
    // `type_contains_never` is false here and we do not double-diagnose it.
    if type_contains_never(&typed.ty) {
        diagnostics.push(Diagnostic::error(
            codes::T279,
            "cannot pass the diverging value `trap()` as an argument: it has type \
             `never` (the bottom type) and produces no value. Use `trap();` as a \
             standalone statement for its divergence instead of passing it."
                .to_string(),
            Some(typed.span),
        ));
        typed.ty = Type::Error;
    }
    typed
}

pub(super) fn infer_binary_expr(
    expr: &BinaryExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let universe = context.universe;
    let lhs = infer_expr(
        &expr.lhs,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    let rhs = infer_expr(
        &expr.rhs,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    // PIL: integer literal resolution in binary ops. Both operands may
    // carry `Type::IntLit(_)` (either side, plus the both-literals case
    // `1 + 2`). Unify via type_compatible (which accepts symmetric
    // IntLit ↔ machine-integer with range-check, and IntLit ↔ IntLit
    // regardless of value per N16-PIL). If unification succeeds AND
    // one side is concrete, rewrite the IntLit side's type via the
    // walker to that concrete type. If BOTH are IntLit, leave them as
    // IntLit — the final post-pass walker defaults to I64.
    let (mut lhs, mut rhs) = (lhs, rhs);
    if matches!(lhs.ty, Type::IntLit(_)) && !matches!(rhs.ty, Type::IntLit(_)) {
        let _ = resolve_int_literals_in_expr(&mut lhs, &rhs.ty);
    } else if matches!(rhs.ty, Type::IntLit(_)) && !matches!(lhs.ty, Type::IntLit(_)) {
        let _ = resolve_int_literals_in_expr(&mut rhs, &lhs.ty);
    }
    let ty = match expr.op {
        BinaryOp::LogicalAnd | BinaryOp::LogicalOr => {
            if !matches!(lhs.ty, Type::Bool | Type::Error)
                || !matches!(rhs.ty, Type::Bool | Type::Error)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T054,
                    format!(
                        "operator `{}` requires `bool` operands, found `{}` and `{}`",
                        render_binary_op(expr.op),
                        render_type(&lhs.ty),
                        render_type(&rhs.ty)
                    ),
                    Some(expr.span),
                ));
                Type::Error
            } else {
                Type::Bool
            }
        }
        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div
            if matches!(lhs.ty, Type::U256) && matches!(rhs.ty, Type::U256) =>
        {
            // u256 PR-U1: `+`/`-`/`*`/`/` are backed by checked stdlib multi-limb
            // math (lowered to a Call in lower_binary_expr). i256 arithmetic is
            // deferred (E4): a mixed or i256 operand falls through to the numeric
            // arm below and is rejected. (`%` is handled in the bit-op arm.)
            Type::U256
        }
        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div => {
            // PIL: use type_compatible instead of `==` so that
            // IntLit ↔ IntLit (both literals with different values)
            // unifies as numeric-compatible. Both-IntLit binops keep
            // the operands as IntLit and let the post-pass walker
            // default them to I64.
            let operands_ok = type_compatible(&lhs.ty, &rhs.ty)
                && matches!(
                    lhs.ty,
                    Type::I32
                        | Type::U32
                        | Type::I64
                        | Type::U64
                        | Type::F64
                        | Type::IntLit(_)
                        | Type::Error
                );
            if !operands_ok {
                diagnostics.push(Diagnostic::error(
                    codes::T054,
                    format!(
                        "operator `{}` requires matching numeric operands, found `{}` and `{}`",
                        render_binary_op(expr.op),
                        render_type(&lhs.ty),
                        render_type(&rhs.ty)
                    ),
                    Some(expr.span),
                ));
                Type::Error
            } else {
                lhs.ty.clone()
            }
        }
        BinaryOp::Mod | BinaryOp::Shl | BinaryOp::Shr | BinaryOp::BitAnd | BinaryOp::BitOr
            if matches!(lhs.ty, Type::U256) && matches!(rhs.ty, Type::U256) =>
        {
            // u256 PR-U1c/U1c-2: `%` (long division), `<<`/`>>` (logical shift),
            // `&`/`|` (limb-wise bitwise) are backed by stdlib and lowered to a
            // u256_* Call. (i256 falls through to the integer arm and is rejected.)
            Type::U256
        }
        BinaryOp::Shl | BinaryOp::Shr | BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::Mod => {
            // Bit operators and modulo require matching integer operands.
            // (Wasm has no f64.rem; f64 modulo is also rare in capability code.)
            // Floats and bools are rejected at type-check (T054 reused).
            // PIL: use type_compatible (admits IntLit ↔ IntLit and
            // IntLit ↔ machine-integer with range-check); add IntLit
            // to the integer-class accept set so two-literal bitops
            // like `1 & 2` and `1 << 2` resolve via the walker.
            let operands_ok = type_compatible(&lhs.ty, &rhs.ty)
                && matches!(
                    lhs.ty,
                    Type::I32 | Type::U32 | Type::I64 | Type::U64 | Type::IntLit(_) | Type::Error
                );
            if !operands_ok {
                diagnostics.push(Diagnostic::error(
                    codes::T054,
                    format!(
                        "operator `{}` requires matching integer operands, found `{}` and `{}`",
                        render_binary_op(expr.op),
                        render_type(&lhs.ty),
                        render_type(&rhs.ty)
                    ),
                    Some(expr.span),
                ));
                Type::Error
            } else {
                lhs.ty.clone()
            }
        }
        BinaryOp::Lt | BinaryOp::LtEq | BinaryOp::Gt | BinaryOp::GtEq
            if matches!(lhs.ty, Type::U256) && matches!(rhs.ty, Type::U256) =>
        {
            // u256 PR-U1a: relational comparisons are backed by stdlib
            // (unsigned multi-limb compare), lowered to a Call. Result is bool.
            Type::Bool
        }
        BinaryOp::Lt | BinaryOp::LtEq | BinaryOp::Gt | BinaryOp::GtEq => {
            // PIL: same fix as additive/bitop arms — type_compatible
            // accepts IntLit ↔ IntLit + IntLit ↔ machine integer with
            // range-check, and IntLit is added to the integer-class
            // accept set. Otherwise `if x > 0` where x is IntLit fires
            // T054 spuriously.
            let operands_ok = type_compatible(&lhs.ty, &rhs.ty)
                && matches!(
                    lhs.ty,
                    Type::I32
                        | Type::U32
                        | Type::I64
                        | Type::U64
                        | Type::F64
                        | Type::IntLit(_)
                        | Type::Error
                );
            if !operands_ok {
                diagnostics.push(Diagnostic::error(
                    codes::T054,
                    format!(
                        "operator `{}` requires matching numeric operands, found `{}` and `{}`",
                        render_binary_op(expr.op),
                        render_type(&lhs.ty),
                        render_type(&rhs.ty)
                    ),
                    Some(expr.span),
                ));
                Type::Error
            } else {
                Type::Bool
            }
        }
        BinaryOp::Eq | BinaryOp::NotEq
            if (!matches!(lhs.ty, Type::U256) && type_contains_wide_int(&lhs.ty, universe))
                || (!matches!(rhs.ty, Type::U256) && type_contains_wide_int(&rhs.ty, universe)) =>
        {
            // u256 PR-U1 (E3/E6 fail-closed): a bare `u256 == u256` is value-
            // compared by the lower_binary_expr fast-path (u256_eq). Every OTHER
            // wide-int comparison shape — a bare `i256`, or u256/i256 nested in a
            // tuple/record/enum/array — would fall through to the default
            // pointer-eq (I32Eq on cell pointers), silently WRONG for value types.
            // Reject until structural value-equality covers those shapes.
            let off = if !matches!(lhs.ty, Type::U256) && type_contains_wide_int(&lhs.ty, universe)
            {
                &lhs.ty
            } else {
                &rhs.ty
            };
            diagnostics.push(Diagnostic::error(
                codes::T055,
                format!(
                    "`{}` on `{}` is not supported: i256, and aggregates containing u256/i256, have \
                     no value-equality yet — compare the u256 fields individually",
                    render_binary_op(expr.op),
                    render_type(off)
                ),
                Some(expr.span),
            ));
            Type::Error
        }
        BinaryOp::Eq | BinaryOp::NotEq => {
            let compatible = type_compatible(&lhs.ty, &rhs.ty) || type_compatible(&rhs.ty, &lhs.ty);
            if !compatible {
                diagnostics.push(Diagnostic::error(
                    codes::T055,
                    format!(
                        "operator `{}` requires comparable operands, found `{}` and `{}`",
                        render_binary_op(expr.op),
                        render_type(&lhs.ty),
                        render_type(&rhs.ty)
                    ),
                    Some(expr.span),
                ));
                Type::Error
            } else {
                Type::Bool
            }
        }
    };

    TypedExpr {
        ty,
        kind: TypedExprKind::Binary(TypedBinaryExpr {
            lhs: Box::new(lhs),
            op: expr.op,
            rhs: Box::new(rhs),
        }),
        span: expr.span,

        refinement: None,
    }
}

pub(super) fn infer_record_construct_expr(
    expr: &RecordConstructExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let (module_name, universe) = (context.module_name, context.universe);
    // Capture expected-type context BEFORE recursing into fields
    // (fields may have their own constructions that mutate the slot).
    // PR A / N15-PRA: this is the let-annotation context threaded from
    // `check_let`. Used to seed the subst map for generic record
    // construction.
    let expected_at_entry = tracker.current_expected_type.clone();

    // BoundedVec PR-1 (sealing, T258): a record whose DEFINING module is a
    // `bounded_*` stdlib module is construction-SEALED — it may be built only
    // inside that module (via `new()` / its methods), never via a direct record
    // literal in user code, so a bounded type's `len` invariant cannot be forged
    // (`BoundedVec_i64_8 { len: 99 }`). The fixed `[i64;N]` backing already makes
    // any element access memory-safe (a bad index traps); this gate guarantees
    // INTEGRITY — the `len <= N` claim is trustworthy. `new()`'s own literal lives
    // in the defining module, so `def_mod == module_name` there → allowed.
    if let Some(def_mod) = universe.record_modules.get(&expr.type_name)
        && def_mod.starts_with("bounded_")
        && def_mod != module_name
    {
        diagnostics.push(Diagnostic::error(
            codes::T258,
            format!(
                "cannot construct sealed record `{}` outside its defining module \
                 `{def_mod}` — bounded collections are construction-sealed so their \
                 length invariant cannot be forged. Use `{}::new()` and the methods \
                 instead of a record literal.",
                expr.type_name, expr.type_name
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

    // PR #135: a field's declared type is the expected type for its value, so a
    // nested generic construction (`items: Vec::new()`) infers. Pushed ONLY when
    // fully concrete (CF-I1) — a generic field type stays unresolved here and is
    // handled by the PR-A construction subst below (CF-I5: no second seed). The
    // lookup is cloned to drop the `&universe` borrow before the `&mut tracker`
    // loop.
    let record_decl = universe.records.get(&expr.type_name).cloned();

    // GAP 1: when this record is GENERIC and `current_expected_type` names it with
    // concrete args, substitute the declared FIELD types so a generic field
    // (`vals: Vec<V>`) becomes concrete (`Vec<i64>`) and its nested construction
    // (`Vec::new()`) infers. CF-B1: a non-generic record has `type_params` empty ⇒
    // subst is None ⇒ field types are byte-identical to pre-fix (the CF-I3
    // IntLit-overflow guard below is therefore unchanged). CF-A2: only built when
    // the expected args are fully concrete. CF-B2: the substituted type is exactly
    // what flows into `infer_arg_with_expected` (which pushes it as the field's
    // ExpectedTypeGuard), so it also reaches a bare-variant field value.
    let construction_subst: Option<HashMap<String, Type>> =
        record_decl.as_ref().and_then(|(type_params, _)| {
            if type_params.is_empty() {
                return None;
            }
            let Some(Type::Named(name, args)) = expected_at_entry.as_ref() else {
                return None;
            };
            if name == &expr.type_name
                && !args.is_empty()
                && args.len() == type_params.len()
                && args.iter().all(type_is_concrete)
            {
                Some(
                    type_params
                        .iter()
                        .zip(args.iter())
                        .map(|(p, a)| (p.clone(), a.clone()))
                        .collect(),
                )
            } else {
                None
            }
        });
    let declared_by_name: HashMap<&str, Type> = record_decl
        .as_ref()
        .map(|(_, fields)| {
            fields
                .iter()
                .map(|(n, t)| {
                    let resolved = construction_subst
                        .as_ref()
                        .map(|s| apply_subst(t, s))
                        .unwrap_or_else(|| t.clone());
                    (n.as_str(), resolved)
                })
                .collect()
        })
        .unwrap_or_default();
    // Field names whose ORIGINAL (pre-substitution) declared type mentions a
    // generic parameter. The general field-value/field-type soundness check
    // below skips these: a generic-parameter field (`val: T`) under an
    // annotation that pins `T` is already validated by
    // `build_record_construction_subst` (it emits the T071
    // `PinnedAnnotationViolated` fault), and an UN-annotated one stays generic
    // post-subst (so the `type_mentions_generic` screen would skip it anyway).
    // Concrete fields of a generic record (`b: i64` in `record P<T> { a: T, b: i64 }`)
    // are NOT in this set, so they remain covered.
    let orig_generic_fields: std::collections::HashSet<&str> = record_decl
        .as_ref()
        .map(|(_, fields)| {
            fields
                .iter()
                .filter(|(_, t)| type_mentions_generic(t))
                .map(|(n, _)| n.as_str())
                .collect()
        })
        .unwrap_or_default();

    // Type-check each field's value expression first.
    let typed_fields: Vec<(String, TypedExpr)> = expr
        .fields
        .iter()
        .map(|(name, value)| {
            // CF-I5: looked up by field NAME, never positional.
            let expected = declared_by_name.get(name.as_str());
            let typed = infer_arg_with_expected(
                value,
                expected,
                env,
                current_return,
                context,
                tracker,
                diagnostics,
            );
            // CF-I3: a field literal that did NOT fit its concrete type stays
            // `IntLit`; reject it (else it defaults to i64 into a narrower slot).
            if let Some(p) = expected
                && type_is_concrete(p)
                && matches!(typed.ty, Type::IntLit(_))
            {
                diagnostics.push(Diagnostic::error(
                    codes::T071,
                    format!(
                        "field `{name}` of `{}` expects `{}`, found an out-of-range integer literal",
                        expr.type_name,
                        render_type(p)
                    ),
                    Some(typed.span),
                ));
            }
            // Soundness: the IntLit arm above ONLY catches an out-of-range integer
            // LITERAL. A non-literal field value of an incompatible concrete type — a
            // `bool`/`str` into an `i64` field, a `u256` into an `i256` field, etc. —
            // previously landed silently in the typed field with NO diagnostic, the
            // record-construction path having no general field-value/field-type check
            // (unlike the function-argument path in `infer_call_expr`, which routes
            // every arg through `type_compatible`). A wrong-typed value then reached
            // AIR and produced invalid wasm / a mistyped field. Mirror the call path:
            // when the declared field type and the actual value type are both fully
            // concrete (no unresolved generic on either side — `Type::Generic` escaping
            // into `type_compatible` ICEs) and incompatible, reject with T071. `IntLit`
            // (handled by the arm above; the IntLit→machine-int flex must survive) and
            // `Error` (cascade-suppression; already reported upstream) are excluded.
            if let Some(p) = expected
                && !orig_generic_fields.contains(name.as_str())
                && !type_mentions_generic(p)
                && !type_mentions_generic(&typed.ty)
                && !matches!(typed.ty, Type::IntLit(_) | Type::Error)
                && !type_compatible(p, &typed.ty)
            {
                let site_ctx = format!("field `{name}` of `{}`", expr.type_name);
                if let Some(t227) =
                    try_array_size_mismatch_diagnostic(p, &typed.ty, &site_ctx, typed.span)
                {
                    diagnostics.push(t227);
                } else {
                    diagnostics.push(Diagnostic::error(
                        codes::T071,
                        format!(
                            "field `{name}` of `{}` expected `{}`, found `{}`",
                            expr.type_name,
                            render_type(p),
                            render_type(&typed.ty)
                        ),
                        Some(typed.span),
                    ));
                }
            }
            (name.clone(), typed)
        })
        .collect();

    // PR A / Phase 6: generic record construction substitution.
    //
    // Look up the record's declared type_params + field types from
    // the universe. For non-generic records (type_params empty),
    // N12-PRA mandates an early-return path that produces byte-
    // identical output to pre-PR-A.
    let (substituted_type_args, refinement_check_safe) = if let Some((
        type_params,
        declared_fields,
    )) =
        universe.records.get(&expr.type_name)
    {
        if type_params.is_empty() {
            // N12-PRA: non-generic record, pre-PR-A behavior.
            (Vec::new(), true)
        } else {
            // Generic record: build substitution from
            // annotation (if any) + field-value inference.
            //
            // PR A / N4-PRA: seed the subst from the expected
            // type's args ONLY if the annotation matches this
            // record's name AND arity.
            let seed_map: Option<HashMap<String, Type>> =
                expected_at_entry.as_ref().and_then(|expected| {
                    if let Type::Named(name, args) = expected {
                        if name == &expr.type_name
                            && !args.is_empty()
                            && args.len() == type_params.len()
                        {
                            Some(
                                type_params
                                    .iter()
                                    .zip(args.iter())
                                    .map(|(p, a)| (p.clone(), a.clone()))
                                    .collect(),
                            )
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                });

            let subst_result = build_record_construction_subst(
                type_params,
                declared_fields,
                &typed_fields,
                seed_map.as_ref(),
            );

            match subst_result {
                Ok(subst) => {
                    // N6-PRA: build resolved type-args by reading
                    // the subst map. Each type_param maps to its
                    // discovered concrete type; missing entries
                    // (shouldn't happen on Ok branch) → Type::Error.
                    let resolved: Vec<Type> = type_params
                        .iter()
                        .map(|p| subst.get(p).cloned().unwrap_or(Type::Error))
                        .collect();
                    (resolved, true)
                }
                Err(faults) => {
                    // Emit a diagnostic per fault. Exhaustive match
                    // per N9-PRA — no `_ =>` wildcard.
                    for fault in &faults {
                        match fault {
                            RecordSubstFault::Conflict { param, bindings } => {
                                // N5-PRA + T234: describe the
                                // conflict, name every contributor,
                                // don't blame one side.
                                let contributors_text = bindings
                                    .iter()
                                    .map(|(field, ty)| {
                                        format!("field `{field}` binds `{}`", render_type(ty))
                                    })
                                    .collect::<Vec<_>>()
                                    .join("; ");
                                diagnostics.push(Diagnostic::error(
                                        codes::T234,
                                        format!(
                                            "type parameter `{param}` has conflicting inferences at construction of `{}`: {contributors_text}. The fields binding `{param}` disagree on its concrete type. To fix: (a) pick one consistent type across all fields binding `{param}` — change the offending field's value type to match; OR (b) if the fields are genuinely independent shapes, split `{}<{param}>` into a multi-param generic like `{}<T, U>` so each field binds its own slot; OR (c) add an explicit type annotation `let x: {}<ConcreteType> = ...;` so one binding pins the slot and the others must match.",
                                            expr.type_name, expr.type_name, expr.type_name, expr.type_name
                                        ),
                                        Some(expr.span),
                                    ));
                            }
                            RecordSubstFault::Unresolved { param } => {
                                // Typestate (ST-4, T269): an unpinnable STATE param is
                                // the protocol-aware form — the phantom state must be
                                // fixed by the expected type, never inferred from fields.
                                let is_state_param = universe
                                    .typestate_state_positions
                                    .get(&expr.type_name)
                                    .zip(universe.records.get(&expr.type_name))
                                    .is_some_and(|(positions, (tparams, _))| {
                                        tparams
                                            .iter()
                                            .position(|p| p == param)
                                            .is_some_and(|idx| positions.contains(&idx))
                                    });
                                if is_state_param {
                                    diagnostics.push(Diagnostic::error(
                                        codes::T269,
                                        format!(
                                            "the protocol state of `{}` cannot be inferred at construction — pin it with an expected type (a `let x: {}<State> = …` annotation, a return type, or a call argument); a typestate is never defaulted to a state",
                                            expr.type_name, expr.type_name
                                        ),
                                        Some(expr.span),
                                    ));
                                } else {
                                    diagnostics.push(Diagnostic::error(
                                        codes::T233,
                                        format!(
                                            "type parameter `{param}` cannot be inferred from field values at construction of `{}` — add an explicit type annotation: `let x: {}<...> = {} {{ ... }};`",
                                            expr.type_name, expr.type_name, expr.type_name
                                        ),
                                        Some(expr.span),
                                    ));
                                }
                            }
                            RecordSubstFault::PinnedAnnotationViolated {
                                param,
                                annotated,
                                field_name,
                                field_ty,
                            } => {
                                // N3-PRA: T071-style at the field
                                // position. Re-use T071 (function
                                // argument type mismatch) for the
                                // field-value-vs-annotation case
                                // since both have the same shape
                                // (expected vs found).
                                diagnostics.push(Diagnostic::error(
                                        codes::T071,
                                        format!(
                                            "field `{field_name}` of `{}` expected `{}` (from annotation-pinned type parameter `{param}`), found `{}`",
                                            expr.type_name,
                                            render_type(annotated),
                                            render_type(field_ty)
                                        ),
                                        Some(expr.span),
                                    ));
                            }
                        }
                    }
                    // N14-PRA: result-type carries Type::Error at
                    // conflicting positions to prevent cascade.
                    // Build best-effort resolved args from any
                    // successful bindings; missing → Type::Error.
                    let resolved: Vec<Type> = type_params
                        .iter()
                        .map(|p| {
                            // Try to recover any non-conflicting
                            // binding via re-running the helper
                            // discarding Errs; for simplicity, use
                            // Type::Error for every param when any
                            // fault fired. Downstream short-circuits
                            // on Type::Error.
                            let _ = p;
                            Type::Error
                        })
                        .collect();
                    (resolved, false)
                }
            }
        }
    } else {
        // Record not in universe — likely a typo or undefined
        // record. Existing diagnostics fire elsewhere; produce
        // empty type-args for the result (pre-PR-A behavior).
        (Vec::new(), true)
    };

    // Cap-smuggle defense at instantiation time (axis 6 — fewer
    // escape hatches). T183 fires structurally at record DECLARATION
    // time when a declared field type contains a cap. With PR #75's
    // generic-record-construction substitution, a record like
    // `record Holder<T> { value: T }` has `value: Type::Generic("T")`
    // at declaration — no cap, T183 silent. At construction-site
    // (`Holder<Fuel> { value: cap }`) the subst rewrites the field
    // type to a concrete cap, but no second cap-check runs. The
    // resulting `h.value` field-projection (and any subsequent
    // call/return that consumes it) loses the cap's restriction
    // provenance — Z3's authority tracker sees a fresh full-authority
    // cap, same gap T183 closes for concrete-field-typed records.
    //
    // The check is gated on substitution success (any_field_error /
    // !refinement_check_safe) for the same cascade-prevention reason
    // as the refinement check below.
    if refinement_check_safe
        && !typed_fields
            .iter()
            .any(|(_, e)| matches!(e.ty, Type::Error))
    {
        check_generic_aggregate_cap_smuggle(
            &expr.type_name,
            &substituted_type_args,
            "record",
            expr.span,
            universe,
            diagnostics,
        );
    }

    // Wall 4 Step 1: refinement satisfiability check at the single
    // construction-site entry per V15. The CI grep-lint asserts this is
    // the only call site of `check_refinement`; reassignment lowering
    // (per V5 fixture 27) funnels through here too.
    //
    // PR A / N14-PRA: skip the refinement check if any field's type
    // is Type::Error OR if substitution failed. This prevents cascade
    // from T233/T234 emission into refinement violation noise.
    // Refinement quarantine (Phase 2): record refinement discharge now runs in
    // the v2 obligation pass; v2 does its own Error-field / safety gating over
    // the typed program, so the construction-site guards are no longer needed.
    let _ = refinement_check_safe;

    // Mutation-as-capability (PR-2c, NC-1): the record-CONSTRUCT escape sink — the
    // "record-wrap launder" NC-1 is forged to kill. A value rooted in a `@ReadOnly`
    // param, stored into a (mutable) record field, would let `r.field.x = 10` mutate
    // the frozen object through the fresh record. Reject readonly-rooted aliasable
    // field values with T253; a primitive-copy field (`x: p.n`) is excluded by
    // `is_aliasable_type`. There is no readonly record type (AG-6), so a constructed
    // record is always mutable — the escape is unconditional.
    for (field_name, field_value) in &typed_fields {
        if super::statements::is_aliasable_type(&field_value.ty)
            && let Some(root) = super::statements::place_root_local(field_value)
            && tracker.readonly_locals.contains(root)
        {
            diagnostics.push(Diagnostic::error(
                codes::T253,
                format!(
                    "cannot store `@ReadOnly` value `{root}` into field `{field_name}` of `{}`: \
                     the record handle is mutable, so the field could be mutated, re-widening \
                     authority. Pass a copy.",
                    expr.type_name
                ),
                Some(field_value.span),
            ));
        }
    }

    // Regions (DEF-2a NC-R1 + DEF-2b LD-6): the record-field escape sink (scope-depth =
    // the record's birth scope, `current_region_depth` → `Global` at function scope). A
    // field born deeper than the record would dangle once the deeper region is reclaimed;
    // and at function depth 0 a `@in r` value stored into a function-lifetime record (then
    // returned) would leak past `r` — caught here because the record's scope is `Global`
    // and `Param(slot)` does not outlive it. Runs whenever region values can exist (in a
    // region OR the fn has region params); empty + depth 0 skips it as DEF-2a did.
    if tracker.current_region_depth > 0 || !tracker.current_param_regions.is_empty() {
        for (_field_name, field_value) in &typed_fields {
            super::statements::check_region_escape(
                field_value,
                super::RegionId::from_depth(tracker.current_region_depth),
                "be stored in a record field",
                tracker,
                diagnostics,
            );
        }
    }

    TypedExpr {
        ty: Type::Named(expr.type_name.clone(), substituted_type_args),
        kind: TypedExprKind::RecordConstruct(TypedRecordConstructExpr {
            type_name: expr.type_name.clone(),
            fields: typed_fields,
        }),
        span: expr.span,

        refinement: None,
    }
}

/// T242 (cap-smuggling through a generic aggregate at instantiation
/// time): fires when any of the substituted type-arguments of a
/// generic aggregate (record, enum, future Vec, etc.) contains a
/// capability type after substitution. Sibling to T183/T184/T186 —
/// those three fire on declarations; this fires on instantiations.
///
/// The recursive `type_contains_cap` walks `Type::Named` args, so
/// nested occurrences (`Option<Option<Cap>>`,
/// `Box<Holder<Cap>>`) all rejecting at this single check.
pub(super) fn check_generic_aggregate_cap_smuggle(
    aggregate_name: &str,
    substituted_type_args: &[Type],
    aggregate_kind: &str,
    span: crate::span::Span,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for (idx, arg) in substituted_type_args.iter().enumerate() {
        if type_contains_cap(arg) {
            diagnostics.push(Diagnostic::error(
                codes::T242,
                format!(
                    "{aggregate_kind} `{aggregate_name}` is instantiated with type-argument position {idx} = `{}`, which contains a capability — generic aggregates cannot carry caps because field-projection / pattern-destructure / index on the resulting value bypasses Z3's authority tracker (same channel T183/T184/T186 close for concrete cap-typed payloads). Pass the cap by name through actor messages or function arguments, or use a non-cap surrogate (e.g., an `i64` amount) inside the aggregate and dispatch on a separate cap held in actor state.",
                    render_type(arg)
                ),
                Some(span),
            ));
        }
        // Typestate (TS4, ST-6 / BL-2): the generic-aggregate channel — `Vec<File<Open>>`,
        // `Option<File<Open>>` — is the instantiation-time sibling of T183/T184/T186. An
        // affine typestate value carried inside it can be projected/indexed twice → T275.
        if type_contains_typestate(arg, universe) {
            diagnostics.push(Diagnostic::error(
                codes::T275,
                format!(
                    "{aggregate_kind} `{aggregate_name}` is instantiated with type-argument position {idx} = `{}`, which contains a typestate value — a typestate value is affine, and field-projection / destructure / index on the aggregate can extract it more than once, defeating the use-after-transition guarantee (the instantiation-time sibling of the T183/T184/T186 channel). Pass the value by name through function arguments instead of inside a generic aggregate.",
                    render_type(arg)
                ),
                Some(span),
            ));
        }
    }
}
pub(super) fn infer_field_access_expr(
    expr: &FieldAccessExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let universe = context.universe;
    let object = infer_expr(
        &expr.object,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );

    // Auto-deref: look through references for field access
    let obj_ty = match &object.ty {
        Type::Ref(inner, _) => inner.as_ref(),
        other => other,
    };
    // Capture the source record's name (post auto-deref) for Wall 4 Step 2
    // refinement attachment below. None when the receiver isn't a named
    // record type.
    let source_record_name: Option<&String> = match obj_ty {
        Type::Named(name, _) => Some(name),
        _ => None,
    };
    let field_ty = match obj_ty {
        Type::Named(type_name, type_args) => {
            if let Some((type_params, fields)) = universe.records.get(type_name) {
                if let Some((_, ty)) = fields.iter().find(|(n, _)| n == &expr.field) {
                    // PR D: substitute the field's declared type against
                    // the receiver's concrete type-args. Without this,
                    // a field declared as `value: T` returns `Type::Generic("T")`
                    // even when accessed through a concrete `Holder<i64>`
                    // receiver — which then escapes into AIR's mangle_type
                    // and ICEs.
                    //
                    // Substitution is identity when the receiver has empty
                    // type-args (non-generic records) — pre-PR-D byte-
                    // equality preserved.
                    if !type_params.is_empty()
                        && !type_args.is_empty()
                        && type_params.len() == type_args.len()
                    {
                        let subst: HashMap<String, Type> = type_params
                            .iter()
                            .zip(type_args.iter())
                            .map(|(p, a)| (p.clone(), a.clone()))
                            .collect();
                        apply_subst(ty, &subst)
                    } else {
                        ty.clone()
                    }
                } else {
                    diagnostics.push(Diagnostic::error(
                        codes::T120,
                        format!("type `{type_name}` has no field `{}`", expr.field),
                        Some(expr.span),
                    ));
                    Type::Error
                }
            } else {
                diagnostics.push(Diagnostic::error(
                    codes::T121,
                    format!("type `{type_name}` is not a record type"),
                    Some(expr.span),
                ));
                Type::Error
            }
        }
        Type::Tuple(elems) => {
            // Tuple element read (`$tup.0`). v1 only produces this from the
            // LetTuple desugar (surface `.0` is deferred, AG-1), so `expr.field`
            // is always a synthesized decimal index; bounds-check defensively.
            match expr.field.parse::<usize>() {
                Ok(idx) if idx < elems.len() => elems[idx].clone(),
                _ => {
                    diagnostics.push(Diagnostic::error(
                        codes::T261,
                        format!(
                            "tuple index `.{}` is out of range for a {}-tuple",
                            expr.field,
                            elems.len()
                        ),
                        Some(expr.span),
                    ));
                    Type::Error
                }
            }
        }
        Type::Error => Type::Error,
        other => {
            diagnostics.push(Diagnostic::error(
                codes::T122,
                format!(
                    "cannot access field `.{}` on non-record type `{}`",
                    expr.field,
                    render_type(other)
                ),
                Some(expr.span),
            ));
            Type::Error
        }
    };

    // Wall 4 Step 2: refinement preservation through field reads.
    //
    // This is THE single attachment site for `TypedExpr.refinement` —
    // every other TypedExpr in the workspace must set `refinement: None`
    // (V1). CI grep-lints (V10, V19, V24) enforce that no other call site
    // inlines a non-None attachment, or routes refinement clauses through
    // intermediate `Option<RefinementClause>` values.
    //
    // V18 gates attachment on field_ty == Type::I64. Refinements on
    // non-i64 fields are already impossible (Step 1's V12 parser-level
    // check), so the debug_assert! below is defensive — in release
    // builds non-i64 fields silently attach None.
    //
    // V16 + V26: collect ALL clauses whose `field` matches the accessed
    // field name. Step 1's current grammar produces 0 or 1 clauses per
    // field, but the Vec storage is forward-compatible with `&&`/`||`
    // grammar relaxation. The construction-site dispatcher iterates
    // destination clauses one at a time and uses an ∃-quantified match:
    // for each required clause d, ∃ s ∈ supplied. refinements_match(s, d).
    let refinement = compute_field_access_refinement(
        universe,
        source_record_name.map(|s| s.as_str()),
        &expr.field,
        &field_ty,
    );

    TypedExpr {
        ty: field_ty,
        kind: TypedExprKind::FieldAccess(TypedFieldAccessExpr {
            object: Box::new(object),
            field: expr.field.clone(),
        }),
        span: expr.span,

        refinement,
    }
}

/// Wall 4 Step 2 V1 single-source-location for refinement attachment.
///
/// Looks up the source record's declared refinement clauses for the
/// accessed field. Returns `Some(Vec)` when ALL of:
///   1. The receiver type is a `Type::Named(record_name, _)`
///      (the `record_name` arg captures this; pass `None` otherwise).
///   2. The accessed field's type is `Type::I64` (V18 gate).
///   3. The record has at least one refinement clause matching the
///      accessed field name.
///
/// Returns `None` otherwise. Two production call sites consume this:
///   * `infer_field_access_expr` — handles `expr.field` syntax.
///   * `infer_path_expr`'s segment chain — handles `obj.f.g.h` paths
///     parsed as `Expr::Path` (the parser routes multi-segment dotted
///     access through Path, not FieldAccess).
///
/// V1 + V10: this helper is the ONLY place in the codebase that
/// produces a non-None value for `TypedExpr.refinement`. The V10 CI
/// grep-lint asserts the inline literal-attachment pattern appears in
/// zero source files (callers use field-shorthand after binding this
/// helper's return value). V19's `Option<RefinementClause>` confinement
/// lint catches indirect bindings in files other than `typed_ast.rs`
/// and `type_check.rs`.
pub(super) fn compute_field_access_refinement(
    universe: &TypeUniverse,
    record_name: Option<&str>,
    field_name: &str,
    field_ty: &Type,
) -> Option<Vec<crate::ast::RefinementClause>> {
    // PR-U3: refinement fields are now `i64` OR `u256` (refinement.rs:136). A read
    // of a refined u256 field must propagate its clause exactly like i64 — the
    // pre-U3 `field_ty == I64` assumption would `debug_assert!`-ICE here on a
    // legal `record Src { amount: u256 } where amount >= N` field read. Only these
    // two types carry refinements; any OTHER non-i64/u256 field still hits the
    // V18 defensive invariant (a clause there is a parser/gate bug).
    if !matches!(*field_ty, Type::I64 | Type::U256) {
        debug_assert!(
            record_name
                .and_then(|name| universe.record_refinements.get(name))
                .is_none_or(|cs| cs.iter().all(|c| c.field != field_name)),
            "Wall 4 Step 2 V18 invariant: refinement clause attached to field `{}` \
             of type {:?} (not i64/u256) — the field-type gate should have rejected \
             this. Investigate the where-clause validation.",
            field_name,
            field_ty,
        );
        return None;
    }

    let name = record_name?;
    let clauses: Vec<_> = universe
        .record_refinements
        .get(name)
        .map(|all| {
            all.iter()
                // Wall 4 Step 4 N2: Step 2 attachment SKIPS clauses
                // whose RHS is `Field(_)` or `LengthOf(_)`. Only
                // `Literal(_)` clauses propagate through field reads.
                // Cross-field and length-of refinements are validated
                // EXCLUSIVELY at the construction site (Step 4's
                // dispatcher) and at subsumption (Step 3's helper),
                // never via Step 2's preservation. This closes the
                // cross-record name-collision scenario by construction.
                .filter(|c| {
                    // PR-U3-b: a wide (LiteralWide) bound propagates through a u256
                    // field read exactly like a small Literal bound.
                    c.field == field_name
                        && matches!(
                            c.rhs,
                            crate::ast::RefinementRhs::Literal(_)
                                | crate::ast::RefinementRhs::LiteralWide(_)
                        )
                })
                .cloned()
                .collect()
        })
        .unwrap_or_default();
    if clauses.is_empty() {
        None
    } else {
        Some(clauses)
    }
}

/// Infer a tuple literal `(a, b, …)` → `Type::Tuple([T_a, T_b, …])`. Each
/// element is inferred INDEPENDENTLY — no homogeneity check (unlike arrays) and
/// no expected-type threading (AG-3: a non-`i64` int element defaults to `i64`
/// like every other PIL, via the orphan defaulter + `default_int_lit_in_type`'s
/// tuple arm). The value lowers through the record machinery: a `RecordConstruct`
/// with a mangled tuple `type_name` (unforgeable `$tuple…` prefix, ET-2) and
/// positional field names "0","1",… synthesized as `String`s — never lexed, so
/// surface `.0` stays deferred (AG-1).
pub(super) fn infer_tuple_expr(
    expr: &TupleExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let typed_elements: Vec<TypedExpr> = expr
        .elements
        .iter()
        .map(|elem| infer_expr(elem, env, current_return, context, tracker, diagnostics))
        .collect();
    // F003 / value-position `trap()` (Tier A): a tuple ELEMENT cannot be a
    // diverging value — `(trap(), 1)` builds a `(never, i64)` whose `never` limb
    // recurses into `mangle_type` (called just below for `type_name`, DURING
    // type-check) and ICEs at the C-NEVER backstop, with no expected element type
    // to reject it against (tuple elements infer independently — see AG-3 above).
    // Reject each `never` element (T279) AND POISON it to `Type::Error` in the
    // element-type vector so the `mangle_type` below is `never`-free; Error mangles
    // cleanly and suppresses the cascade. Caught in EVERY context (let-bound,
    // nested, an argument). Mirrors the T186 (cap) / T275 (typestate) aggregate-
    // element gates in `infer_array_lit_expr`.
    let elem_tys: Vec<Type> = typed_elements
        .iter()
        .enumerate()
        .map(|(i, e)| {
            if type_contains_never(&e.ty) {
                diagnostics.push(Diagnostic::error(
                    codes::T279,
                    format!(
                        "tuple element {i} is the diverging value `trap()` (type `never`), \
                         which produces no value and cannot be stored. Use `trap();` as a \
                         standalone statement for its divergence instead.",
                    ),
                    Some(expr.elements[i].span()),
                ));
                Type::Error
            } else {
                e.ty.clone()
            }
        })
        .collect();
    let tuple_ty = Type::Tuple(elem_tys);
    // type_name is INERT for tuples (the construct path / `flatten_record`
    // ignore it; the read path keys on `Type::Tuple`, not this string) — but we
    // give it the real injective mangle anyway for consistency + debuggability.
    let type_name = mangle_type(&tuple_ty);
    let fields: Vec<(String, TypedExpr)> = typed_elements
        .into_iter()
        .enumerate()
        .map(|(i, e)| (i.to_string(), e))
        .collect();
    TypedExpr {
        ty: tuple_ty,
        kind: TypedExprKind::RecordConstruct(TypedRecordConstructExpr { type_name, fields }),
        span: expr.span,
        refinement: None,
    }
}

pub(super) fn infer_array_lit_expr(
    expr: &ArrayLitExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let universe = context.universe;
    if expr.elements.is_empty() {
        // PR AF / N17-AF / Phase 1.4: admit `let x: [T; 0] = []`
        // when the let-annotation (threaded via PR A's
        // `current_expected_type`) is EXACTLY a zero-sized array of
        // some element type. Pattern-matches `size: 0` literally —
        // any other expected-type shape falls through to T089.
        if let Some(Type::Array { elem, size: 0 }) = &tracker.current_expected_type {
            let elem_clone = (**elem).clone();
            return TypedExpr {
                ty: Type::Array {
                    elem: Box::new(elem_clone.clone()),
                    size: 0,
                },
                kind: TypedExprKind::ArrayLit(TypedArrayLitExpr {
                    elements: Vec::new(),
                    elem_type: elem_clone,
                }),
                span: expr.span,
                refinement: None,
            };
        }
        // Also admit `let x: &[T] = &[]` paths where the expected
        // type is a Slice: produce a `Type::Array { size: 0 }` and
        // let the existing Array→Slice coercion handle the borrow.
        if let Some(Type::Slice(elem)) = &tracker.current_expected_type {
            let elem_clone = (**elem).clone();
            return TypedExpr {
                ty: Type::Array {
                    elem: Box::new(elem_clone.clone()),
                    size: 0,
                },
                kind: TypedExprKind::ArrayLit(TypedArrayLitExpr {
                    elements: Vec::new(),
                    elem_type: elem_clone,
                }),
                span: expr.span,
                refinement: None,
            };
        }
        diagnostics.push(Diagnostic::error(
            codes::T089,
            "cannot infer type of empty array literal",
            Some(expr.span),
        ));
        return TypedExpr {
            ty: Type::Error,
            kind: TypedExprKind::Literal(Literal::Int(0)),
            span: expr.span,

            refinement: None,
        };
    }

    let typed_elements: Vec<TypedExpr> = expr
        .elements
        .iter()
        .map(|elem| infer_expr(elem, env, current_return, context, tracker, diagnostics))
        .collect();

    let mut elem_type = typed_elements[0].ty.clone();
    // F003 / value-position `trap()` (Tier A): an array whose element type is
    // `never` — `[trap()]`, or any literal whose element 0 is `trap()` — infers
    // element type `never`, which recurses into `lower_type` (and any type-check-
    // time `mangle_type` if the array is passed to a generic) and ICEs at the
    // C-NEVER backstop. Reject it (T279) AND POISON `elem_type` to `Type::Error`
    // BEFORE the homogeneity loop below, so a trailing element is compared against
    // `Error` (compatible, cascade-suppressed) rather than double-reported as a
    // T140 mismatch. Mirrors the T186 (cap) / T275 (typestate) element gates that
    // follow, walking the same `elem_type`. (A LATER `never` element on a concrete
    // element 0 — `[1, trap()]` — is still a T140 homogeneity mismatch, unchanged.)
    if type_contains_never(&elem_type) {
        diagnostics.push(Diagnostic::error(
            codes::T279,
            "array literal has the diverging value `trap()` (type `never`) as its \
             element type — `never` produces no value and cannot be stored in an \
             array. Use `trap();` as a standalone statement for its divergence instead."
                .to_string(),
            Some(expr.span),
        ));
        elem_type = Type::Error;
    }
    for (i, elem) in typed_elements.iter().enumerate().skip(1) {
        if !type_compatible(&elem_type, &elem.ty) {
            let expected = render_type(&elem_type);
            let actual = render_type(&elem.ty);
            diagnostics.push(Diagnostic::error(
                codes::T140,
                format!(
                    "array element {i} has type `{actual}`, expected `{expected}` (cast with `<expr> as {expected}` to match, or change element 0's type to `{actual}`)",
                ),
                Some(expr.elements[i].span()),
            ));
        }
    }

    // T186 (step 32, axis-6 fifth touch): reject cap-typed array
    // elements. Companion to T183 (records) and T184 (enum payloads):
    // arrays are the third aggregate-smuggling channel — `arr[i]`
    // produces a fresh cap binding that Z3's authority tracker
    // treats as full authority, losing any restriction the cap
    // carried before being placed in the array.
    if type_contains_cap(&elem_type) {
        diagnostics.push(Diagnostic::error(
            codes::T186,
            format!(
                "array literal has cap-typed element `{}` — capabilities cannot be stored in arrays because Index bypasses Z3's authority tracker (the same aggregate-smuggling channel T183 closes for records and T184 closes for enum payloads). Pass each cap by name through actor messages or function arguments, or store an `i64` surrogate per slot instead.",
                render_type(&elem_type),
            ),
            Some(expr.span),
        ));
    }
    // Typestate (TS4, ST-6 / BL-2): an affine typestate element indexed twice
    // (`arr[i]` twice) would mint two handles from one → T275 (same channel as T186).
    if type_contains_typestate(&elem_type, universe) {
        diagnostics.push(Diagnostic::error(
            codes::T275,
            format!(
                "array literal has typestate-typed element `{}` — a typestate value is affine, and indexing the array can extract it more than once, defeating the use-after-transition guarantee (the same aggregate-smuggling channel T186 closes for caps). Pass each value by name through function arguments instead of an array.",
                render_type(&elem_type),
            ),
            Some(expr.span),
        ));
    }

    let size = typed_elements.len() as u32;
    TypedExpr {
        ty: Type::Array {
            elem: Box::new(elem_type.clone()),
            size,
        },
        kind: TypedExprKind::ArrayLit(TypedArrayLitExpr {
            elements: typed_elements,
            elem_type,
        }),
        span: expr.span,

        refinement: None,
    }
}

pub(super) fn infer_index_expr(
    expr: &IndexExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let array = infer_expr(
        &expr.array,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    let index = infer_expr(
        &expr.index,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );

    let elem_type = match &array.ty {
        Type::Array { elem, .. } => (**elem).clone(),
        // PR P16 commit #2: slice indexing. Admits `Type::Slice(elem)`
        // receiver alongside `Type::Array`. AIR's `lower_index_expr`
        // dispatches per receiver-type at the AIR layer using the
        // PR AF `slice_data_ptr_var` + `slice_len_var` helpers
        // (N20-P16: Slice arm passes `mem_arg.offset = 0` to
        // LoadDynamic; Array arm continues `+4` header skip).
        Type::Slice(elem) => (**elem).clone(),
        Type::Error => Type::Error,
        other => {
            diagnostics.push(Diagnostic::error(
                codes::T141,
                format!(
                    "cannot index into non-array, non-slice type `{}`",
                    render_type(other)
                ),
                Some(expr.array.span()),
            ));
            Type::Error
        }
    };

    // Enforce integer indices for array access. PIL: route through
    // `is_machine_integer_type` (admits IntLit alongside the machine
    // integer types); the post-pass walker rewrites IntLit before AIR.
    if !is_machine_integer_type(&index.ty) {
        diagnostics.push(Diagnostic::error(
            codes::T142,
            format!(
                "array index must be an integer type, found `{}`",
                render_type(&index.ty)
            ),
            Some(expr.index.span()),
        ));
    }

    // Refinement-typed array bounds (v1) — SC-2: TWO `true`-setters, both
    // Z3-FREE (typed_ast.rs `bounds_proven` doc). (a) A LITERAL index on a
    // fixed array `[T; N]` decided by a constant comparison: in-bounds
    // (`0 <= k < N`) ⇒ proven, so AIR elides the runtime `TrapIf`;
    // out-of-bounds ⇒ T278 compile error (reject > runtime trap). (b) RF-M2:
    // a bare Local certified by the range-loop fact channel (immutable +
    // never-rebound, `v ∈ [lo, hi)`), decided by a plain i64 interval
    // compare against the static `N`. Z3 is never consulted on either path,
    // so a build with the `solver` feature OFF behaves identically and Z3
    // stays out of the memory-safety TCB (SC-6). Slices have no static `N`,
    // so they never reach either arm and keep their runtime check.
    let mut bounds_proven = false;
    if let Type::Array { size, .. } = &array.ty
        && let TypedExprKind::Literal(Literal::Int(k)) = &index.kind
    {
        let n = *size as i64;
        let k = *k;
        if k >= 0 && k < n {
            bounds_proven = true;
        } else if n == 0 {
            diagnostics.push(Diagnostic::error(
                codes::T278,
                format!(
                    "array index `{k}` is out of bounds for `[{}; 0]` — the array is empty and has no valid indices. This access always traps at runtime.",
                    render_type(&elem_type),
                ),
                Some(expr.index.span()),
            ));
        } else {
            diagnostics.push(Diagnostic::error(
                codes::T278,
                format!(
                    "array index `{k}` is out of bounds for `[{}; {size}]` — valid indices are `0..={}`. This access always traps at runtime; use an index `< {size}` or a larger array.",
                    render_type(&elem_type),
                    n - 1,
                ),
                Some(expr.index.span()),
            ));
        }
    }

    // RANGE-FOR (RF-M2/M3): the second `bounds_proven` setter — equally
    // Z3-FREE. The index is a bare `Local` the range-loop channel certifies as
    // IMMUTABLE + NEVER-REBOUND with `v ∈ [lo, hi)` (innermost fact first;
    // the pre-scan refuses nested same-name loops, so a hit is unambiguous).
    // M3 TIGHTENS the channel interval with the index's COMPOSED narrowing
    // clauses (`if v < 5 { … }` guards) — sound to trust HERE precisely
    // because the channel hit certifies the name is never mutated or rebound
    // in the loop body (without that certificate the general stack is the
    // V4-W4S10 stale-frame class and is never consulted for elision). All
    // clause RHS on this path are `Literal(i64)` (extract_narrowing_predicate
    // produces nothing else); any other RHS is IGNORED, never trusted.
    // Decision (plain i64 compares): empty interval ⇒ unreachable code, no
    // claim; interval ⊆ [0, N) ⇒ elide; interval entirely >= N ⇒ T278 (the
    // same per-execution "always traps when executed" claim as the literal
    // path — a guard that SHRINKS the interval can only make this more
    // precise, never a false reject); straddle ⇒ the runtime-trap floor.
    if !bounds_proven
        && let Type::Array { size, .. } = &array.ty
        && let TypedExprKind::Local(idx_name) = &index.kind
        && let Some(fact) = tracker
            .range_loop_facts
            .iter()
            .rev()
            .find(|f| f.var == *idx_name)
    {
        let mut lo = fact.lo;
        let mut hi = fact.hi_exclusive - 1; // inclusive upper bound
        if let Some(clauses) = &index.refinement {
            for clause in clauses {
                if clause.field != *idx_name {
                    continue;
                }
                let RefinementRhs::Literal(v) = clause.rhs else {
                    continue; // non-literal RHS: ignore, never trust
                };
                match clause.op {
                    RefinementOp::Ge => lo = lo.max(v),
                    RefinementOp::Gt => lo = lo.max(v.saturating_add(1)),
                    RefinementOp::Lt => hi = hi.min(v.saturating_sub(1)),
                    RefinementOp::Le => hi = hi.min(v),
                    RefinementOp::Eq => {
                        lo = lo.max(v);
                        hi = hi.min(v);
                    }
                    RefinementOp::Ne => {}
                }
            }
        }
        let n = i64::from(*size);
        if lo > hi {
            // Contradictory guards — this access is unreachable; make no
            // claim either way (the trap floor stays, harmlessly).
        } else if lo >= 0 && hi < n {
            bounds_proven = true;
        } else if lo >= n {
            diagnostics.push(Diagnostic::error(
                codes::T278,
                format!(
                    "loop index `{idx_name}` is provably out of bounds for `[{}; {size}]` — its proven range here is `{lo}..={hi}`, but valid indices are `0..={}`. This access always traps when executed; tighten the loop bound or guard the index below `{size}`.",
                    render_type(&elem_type),
                    n - 1,
                ),
                Some(expr.index.span()),
            ));
        }
    }

    TypedExpr {
        ty: elem_type.clone(),
        kind: TypedExprKind::Index(TypedIndexExpr {
            array: Box::new(array),
            index: Box::new(index),
            elem_type,
            bounds_proven,
        }),
        span: expr.span,

        refinement: None,
    }
}

pub(super) fn infer_closure_expr(
    closure_expr: &ClosureExpr,
    env: &HashMap<String, Type>,
    _current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let (module_name, universe) = (context.module_name, context.universe);
    // 1. Type-check params
    let param_types: Vec<Type> = closure_expr
        .params
        .iter()
        .map(|p| resolve_type_expr(&p.ty, universe, &HashMap::new(), &[]))
        .collect();

    let ret_type = closure_expr
        .return_type
        .as_ref()
        .map(|ty| resolve_type_expr(ty, universe, &HashMap::new(), &[]))
        .unwrap_or(Type::Unit);

    // 2. Capture analysis: find free variables in the closure body
    let mut inner_bound: HashSet<String> = HashSet::new();
    for p in &closure_expr.params {
        inner_bound.insert(p.name.clone());
    }
    let free_vars = find_free_vars(&closure_expr.body, &inner_bound);

    // 3. Filter to only variables that exist in the outer environment
    let captures: Vec<TypedCapture> = free_vars
        .iter()
        .filter_map(|name| {
            env.get(name).map(|ty| TypedCapture {
                name: name.clone(),
                ty: ty.clone(),
            })
        })
        .collect();

    // Actor-state (M4, SC-1 / T127): a closure is lambda-lifted to a top-level
    // function whose ABI carries an `__env` pointer at `VarId(0)` — NOT the actor
    // state pointer. So an actor state field is UNREACHABLE inside a closure body;
    // lowering a state read there would hit `lower_state_read`'s "no state layout
    // entry" ICE. Reject fail-closed BEFORE lowering. This also closes the closure
    // laundering channel the adversarial hunt found: a closure that captured a
    // state CAP and consumed it (directly, or as a `grant` body) would otherwise
    // bypass the borrow-only C010 check entirely. Captures are sorted for a
    // deterministic diagnostic order. The `grant(&field, fn(r: &Cap) { … })` borrow
    // pattern is UNAFFECTED: `field` is the grant's cap argument (evaluated in the
    // handler), not a free variable of the closure body, so it is not captured.
    {
        let mut state_captures: Vec<&str> = captures
            .iter()
            .filter(|c| tracker.state_fields.contains_key(&c.name))
            .map(|c| c.name.as_str())
            .collect();
        state_captures.sort_unstable();
        for field in state_captures {
            diagnostics.push(Diagnostic::error(
                codes::T127,
                format!(
                    "closure captures actor state field `{field}`, which is not accessible \
                     inside a closure (a closure runs with no access to the actor's state \
                     pointer). Read a data field into a local before the closure, or borrow a \
                     capability with `grant(&{field}, …)` instead of capturing it",
                ),
                Some(closure_expr.span),
            ));
        }
    }

    // 4. Determine linearity
    // Typestate (TS4, ST-6): a closure capturing an AFFINE value — a cap OR a
    // typestate value — is itself linear (FnOnce). This makes calling it twice a
    // use-after-move (O001) and passing it to a non-linear `Fn` parameter a T237,
    // closing the closure-capture double-CONSUME vector for typestate (it already
    // held for caps). `universe` distinguishes a typestate nominal from a plain one.
    let is_linear = captures
        .iter()
        .any(|c| matches!(c.ty, Type::Cap(_, _)) || type_contains_typestate(&c.ty, universe));

    // 5. Lambda-lift: create a synthesized function.
    //
    // `closure_id` MUST be reserved (the slot pushed) BEFORE the body is
    // type-checked. `check_block` recurses into any closure DEFINED INSIDE this
    // body, and each nested closure also takes `tracker.functions.len()` as its
    // id. If the push were deferred until after `check_block` (as the original
    // code did), a closure nested in this body would observe the SAME `len()` —
    // because THIS closure isn't pushed yet — so both would be named
    // `<module>::__closure_<id>`. `function_ids` (air.rs) is keyed by name, so
    // the collision makes the inner closure's construct resolve to the OUTER
    // function id; the inner indirect-call then re-invokes the outer closure and
    // infinite-recurses. Reserving the slot up front gives every closure a
    // distinct id.
    let closure_id = tracker.functions.len();
    let synthesized_name = format!("{}::__closure_{}", module_name, closure_id);

    // Build params: env_ptr (Ptr) + user params
    let mut lifted_params = vec![TypedParam {
        flow: false,
        mutability: crate::ast::Mutability::Default,
        name: "__env".to_owned(),
        ty: Type::Named("__closure_env".to_owned(), vec![]),
        taint: crate::ast::TaintLabel::Public,
    }];
    lifted_params.extend(closure_expr.params.iter().map(|p| TypedParam {
        flow: false,
        mutability: crate::ast::Mutability::Default,
        name: p.name.clone(),
        ty: resolve_type_expr(&p.ty, universe, &HashMap::new(), &[]),
        taint: p.taint.unwrap_or(crate::ast::TaintLabel::Public),
    }));

    // Build the closure body's scope (captures + params) BEFORE reserving the
    // slot, since the reservation moves `lifted_params`/`captures` into the
    // pushed function.
    let mut closure_env = HashMap::new();
    for cap in &captures {
        closure_env.insert(cap.name.clone(), cap.ty.clone());
    }
    for p in &lifted_params {
        closure_env.insert(p.name.clone(), p.ty.clone());
    }

    // Reserve the slot with a placeholder body (patched in after `check_block`).
    // Nothing reads another function's body during checking, so the placeholder
    // is never observed.
    tracker.functions.push(TypedFunction {
        ret_flow: false,
        name: synthesized_name.clone(),
        export_name: format!("__closure_{}", closure_id),
        kind: TypedFunctionKind::Closure,
        externally_callable: false,
        params: lifted_params,
        captures: captures
            .iter()
            .map(|c| TypedParam {
                flow: false,
                mutability: crate::ast::Mutability::Default,
                name: c.name.clone(),
                ty: c.ty.clone(),
                taint: crate::ast::TaintLabel::Public,
            })
            .collect(),
        ret: ret_type.clone(),
        ret_taint: crate::ast::TaintLabel::Public,
        // PLACEHOLDER — overwritten with the body's INFERRED row right after
        // `check_block` (alongside the `.body` patch below). The enclosing row is
        // only what a nested closure's fail-closed callee-miss path would see in
        // the window before the patch.
        effects: tracker.current_effects.clone(),
        body: TypedBlock {
            statements: Vec::new(),
            span: closure_expr.span,
            guaranteed_return: false,
        },
        span: closure_expr.span,
    });

    // Type-check the closure body with captures + params in scope. Nested
    // closures push into `tracker.functions` here, taking ids > `closure_id`.
    // RF-M2 BARRIER: the closure body is lambda-lifted into a DIFFERENT
    // function whose params/locals may shadow an enclosing range-loop var —
    // empty the bounds-fact channel for the duration (fail-closed: no
    // enclosing-loop elision inside any closure).
    let saved_range_facts = std::mem::take(&mut tracker.range_loop_facts);
    let mut closure_mutables = HashSet::new();
    let body = check_block(
        &closure_expr.body,
        &mut closure_env,
        &mut closure_mutables,
        &ret_type,
        context,
        tracker,
        diagnostics,
        !matches!(ret_type, Type::Unit),
    );
    tracker.range_loop_facts = saved_range_facts;

    // Patch the type-checked body into the reserved slot. `closure_id` stays in
    // bounds: `check_block` only ever GROWS `tracker.functions`.
    tracker.functions[closure_id].body = body;

    // Latent effect row = what the body ACTUALLY performs, inferred bottom-up
    // (roadmap Phase 1 — this replaced the interim inherit-the-enclosing-row
    // over-approximation).
    //
    // The body is fully typed at this point, and nested closures were finalized
    // during `check_block` (post-order), so a single pass suffices: a closure
    // cannot self-reference, a named callee contributes its DECLARED row (which
    // cuts any cycle through the defining function), and an applied inner closure
    // contributes the latent row already fixed on its own `Type::Fn`. Callee names
    // that resolve nowhere fail CLOSED by charging the enclosing declared row —
    // degrading, for that call only, to the old over-approximation.
    //
    // The same row is recorded on BOTH the lifted `TypedFunction` and the
    // `Type::Fn`, so the type and the function agree by construction, and
    // `check_effects`' later walk of the lifted body against this row becomes an
    // independent cross-check of the inference: an UNDER-approximation (the
    // false-accept direction — the AG-HOF-A class) fires a loud E001/E010 in the
    // closure body; an over-approximation is silent imprecision, never
    // unsoundness. Mirrors λ-SIGIL's `Typing` (synthesis) + `Chk` (checking) and
    // `Chk.complete` (`proofs/lean/LambdaSigil/EffectRows.lean`).
    let inferred_row = {
        let infer_ctx = super::effect_infer::EffectInferCtx {
            functions: &tracker.functions,
            function_sigs: context.function_sigs,
            workspace_sigs: &tracker.workspace_sigs,
            effect_registry: &context.universe.effect_registry,
            module_name: context.module_name,
            fallback: &tracker.current_effects,
        };
        super::effect_infer::effects_of_block(&tracker.functions[closure_id].body, &infer_ctx)
    };
    tracker.functions[closure_id].effects = inferred_row.clone();

    let closure_ty = Type::Fn(
        param_types.clone(),
        Box::new(ret_type.clone()),
        is_linear,
        inferred_row,
    );

    TypedExpr {
        ty: closure_ty,
        kind: TypedExprKind::ClosureConstruct(TypedClosureConstructExpr {
            synthesized_name,
            captures,
            param_types,
            ret_type,
            is_linear,
        }),
        span: closure_expr.span,

        refinement: None,
    }
}

pub(super) fn infer_borrow_expr(
    borrow_expr: &BorrowExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    // PR AF / N18-AF + N22-AF: set `parent_is_immediate_borrow`
    // while recursing into the borrowed expression so
    // `infer_slice_expr` can distinguish `&arr[0..3]` (admitted)
    // from bare `arr[0..3]` (T238). The guard's `Drop` restores
    // the prior value when this recursion returns.
    let mut guard = BorrowContextGuard::enter(tracker);
    let inner = infer_expr(
        &borrow_expr.inner,
        env,
        current_return,
        context,
        guard.tracker_mut(),
        diagnostics,
    );
    drop(guard);

    // Determine result type based on inner type
    let result_ty = match &inner.ty {
        // &[T; N] coerces to &[T] (slice)
        Type::Array { elem, .. } => Type::Slice(elem.clone()),
        // PR AF: `&arr[0..3]` already produces a Slice via
        // `infer_slice_expr`; the outer Borrow is idempotent on
        // Slice-typed inner expressions (slicing is itself a
        // borrowed view). Returns the inner Slice unchanged so the
        // user-facing type is `&[T]` not `&&[T]`.
        Type::Slice(elem) => Type::Slice(elem.clone()),
        // Primitives cannot be borrowed (no memory address for Wasm locals)
        Type::I32
        | Type::U32
        | Type::I64
        | Type::U64
        | Type::F64
        | Type::Bool
        | Type::Str
        | Type::Unit => {
            diagnostics.push(Diagnostic::error(
                codes::T133,
                format!(
                    "cannot borrow primitive type `{}`; only heap-allocated types can be borrowed",
                    render_type(&inner.ty)
                ),
                Some(borrow_expr.span),
            ));
            Type::Error
        }
        Type::Error => Type::Error,
        // Heap-allocated types (records, enums, named) → &T
        other => Type::Ref(Box::new(other.clone()), borrow_expr.mutable),
    };

    TypedExpr {
        ty: result_ty,
        kind: TypedExprKind::Borrow(TypedBorrowExpr {
            inner: Box::new(inner),
            mutable: borrow_expr.mutable,
        }),
        span: borrow_expr.span,

        refinement: None,
    }
}

/// PR AF / Phase 1.3: type-check `&arr[0..3]` (and the open-range
/// variants `[..3]`, `[0..]`, `[..]`). Per N18-AF, the slice
/// operator is admitted ONLY when its immediate syntactic parent is
/// `Expr::Borrow`; bare `arr[0..3]` fires T238 from the canonical
/// single emission site (N5-AF).
///
/// The receiver must be `Type::Array { elem, .. } | Type::Slice(_)`;
/// `start` and `end` (when present) are integer-typed and admitted
/// in the natural lattice (u32/i64) — the AIR layer is responsible
/// for any wrapping. Result type is `Type::Slice(elem)`. AIR's
/// `lower_slice_expr` (commit #4) computes the slice header via
/// view-semantics; no copy.
///
/// Recursing into start/end children clears the
/// `parent_is_immediate_borrow` flag because those grandchildren are
/// NOT in immediate-borrow context (the borrow's direct child is
/// THIS slice, not the bound expressions).
pub(super) fn infer_slice_expr(
    slice: &crate::ast::SliceExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    // N18-AF: read the immediate-borrow flag BEFORE any recursion
    // (which would clear it via the child-context guard below).
    let parent_is_borrow = tracker.parent_is_immediate_borrow;

    // Clear the flag while recursing into children — neither the
    // array receiver nor the bounds are in IMMEDIATE-borrow context.
    // Save/restore via a manual scope (lighter than a guard struct
    // because the children are siblings, not nested).
    let saved_flag = std::mem::replace(&mut tracker.parent_is_immediate_borrow, false);

    let typed_array = infer_expr(
        &slice.array,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    let typed_start = slice.start.as_ref().map(|e| {
        Box::new(infer_expr(
            e,
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        ))
    });
    let typed_end = slice.end.as_ref().map(|e| {
        Box::new(infer_expr(
            e,
            env,
            current_return,
            context,
            tracker,
            diagnostics,
        ))
    });

    // Restore the flag (it was already cleared by `replace` to
    // false, so this is a no-op when `saved_flag == false`; if a
    // future code path sets the flag mid-inference, the restore
    // pattern is correct).
    tracker.parent_is_immediate_borrow = saved_flag;

    // Validate receiver type.
    let elem_type = match &typed_array.ty {
        Type::Array { elem, .. } => (**elem).clone(),
        Type::Slice(elem) => (**elem).clone(),
        Type::Error => Type::Error,
        other => {
            diagnostics.push(Diagnostic::error(
                codes::T130,
                format!(
                    "slice operator requires an array or slice receiver, found `{}`",
                    render_type(other)
                ),
                Some(slice.span),
            ));
            Type::Error
        }
    };

    // Validate bound types when present. PIL: route through
    // `is_machine_integer_type` (admits IntLit + Error).
    for bound in [&typed_start, &typed_end].into_iter().flatten() {
        if !is_machine_integer_type(&bound.ty) {
            diagnostics.push(Diagnostic::error(
                codes::T142,
                format!(
                    "slice bound must be an integer, found `{}`",
                    render_type(&bound.ty)
                ),
                Some(bound.span),
            ));
        }
    }

    // N5-AF + N18-AF: T238 fires from THIS single canonical site
    // when the immediate parent was not `Expr::Borrow`. Suppress if
    // the receiver was Type::Error to avoid cascading diagnostics
    // on already-broken upstream expressions.
    if !parent_is_borrow && !matches!(elem_type, Type::Error) {
        diagnostics.push(Diagnostic::error(
            codes::T238,
            "slice operator requires a borrow: write `&arr[0..3]` not `arr[0..3]`",
            Some(slice.span),
        ));
    }

    TypedExpr {
        ty: Type::Slice(Box::new(elem_type.clone())),
        kind: TypedExprKind::Slice(TypedSliceExpr {
            array: Box::new(typed_array),
            start: typed_start,
            end: typed_end,
            elem_type,
        }),
        span: slice.span,
        refinement: None,
    }
}

pub(super) fn check_result_ctor_expr(
    expr: &ResultCtorExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let value = infer_expr(
        &expr.value,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    let ty = if expr.is_ok {
        Type::Named("Result".into(), vec![value.ty.clone(), Type::Error])
    } else {
        Type::Named("Result".into(), vec![Type::Error, value.ty.clone()])
    };

    // T242: cap-smuggle defense at Result ctor. The hardcoded
    // `try_parse_result_ctor` parser shortcut (AG-PRB-B) means
    // `Ok(cap)` / `Err(cap)` bypasses the generic enum-variant
    // construction path that PR #75 already guards. Check the
    // value's type for cap-containment to close the same channel
    // for the syntactic shortcut.
    if !matches!(value.ty, Type::Error) && type_contains_cap(&value.ty) {
        let variant_name = if expr.is_ok { "Ok" } else { "Err" };
        diagnostics.push(Diagnostic::error(
            codes::T242,
            format!(
                "`Result::{variant_name}(_)` instantiated with capability-typed value `{}` — generic aggregates cannot carry caps because field-projection / pattern-destructure / index on the resulting value bypasses Z3's authority tracker (same channel T183/T184/T186 close for concrete cap-typed payloads). Pass the cap by name through actor messages or function arguments, or use a non-cap surrogate (e.g., an `i64` amount) inside the Result and dispatch on a separate cap held in actor state.",
                render_type(&value.ty)
            ),
            Some(expr.span),
        ));
    }

    TypedExpr {
        ty,
        kind: TypedExprKind::ResultCtor(TypedResultCtorExpr {
            is_ok: expr.is_ok,
            value: Box::new(value),
        }),
        span: expr.span,

        refinement: None,
    }
}

pub(super) fn check_try_expr(
    expr: &TryExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let value = infer_expr(
        &expr.value,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );

    // PR OptTry: `?` admits BOTH `Result<T, E>` and `Option<T>` carriers
    // with a strict same-carrier rule. Arm order is load-bearing per
    // N8-OptTry: the cross-carrier arm (T241) MUST precede the generic
    // "wrong return type" / "not a carrier" arms so cross-carrier
    // mismatches surface with the actionable T241 conversion hint
    // instead of bleeding onto T181 / T182.
    let ty = match (&value.ty, current_return) {
        // Result<T, E>? in Result<_, E>-returning function — existing logic.
        (Type::Named(vn, v_args), Type::Named(rn, r_args))
            if vn == "Result" && rn == "Result" && v_args.len() >= 2 && r_args.len() >= 2 =>
        {
            if type_compatible(&r_args[1], &v_args[1]) {
                v_args[0].clone() // ok type
            } else {
                diagnostics.push(Diagnostic::error(
                    codes::T180,
                    format!(
                        "`?` found error type `{}`, but enclosing function returns `Result<_, {}>`",
                        render_type(&v_args[1]),
                        render_type(&r_args[1])
                    ),
                    Some(expr.span),
                ));
                Type::Error
            }
        }
        // PR OptTry / N8-OptTry: Option<T>? in Option<U>-returning function —
        // unify on the payload type T; result is the unwrapped T.
        (Type::Named(vn, v_args), Type::Named(rn, r_args))
            if vn == "Option" && rn == "Option" && v_args.len() == 1 && r_args.len() == 1 =>
        {
            if type_compatible(&r_args[0], &v_args[0]) {
                v_args[0].clone() // Some payload type
            } else {
                // AG-OptTry-S: payload-type mismatch fires existing T071.
                diagnostics.push(Diagnostic::error(
                    codes::T071,
                    format!(
                        "`?` found `Option<{}>`, but enclosing function returns `Option<{}>`",
                        render_type(&v_args[0]),
                        render_type(&r_args[0])
                    ),
                    Some(expr.span),
                ));
                Type::Error
            }
        }
        // PR OptTry / N8-OptTry: cross-carrier mismatch — T241 with
        // direction-specific actionable hint. This arm MUST precede the
        // "not a Result-returning fn" arm below so cross-carrier cases
        // get T241 instead of T181 (per N8-OptTry routing exclusivity).
        (Type::Named(vn, _), Type::Named(rn, _))
            if (vn == "Option" && rn == "Result") || (vn == "Result" && rn == "Option") =>
        {
            let conversion_hint = if vn == "Option" {
                "use `.ok_or(err)` to convert Option to Result before applying `?`"
            } else {
                "use `.ok()` to convert Result to Option before applying `?`"
            };
            diagnostics.push(Diagnostic::error(
                codes::T241,
                format!(
                    "`?` on `{}<...>` is not allowed in a function returning `{}<...>` — {}",
                    vn, rn, conversion_hint,
                ),
                Some(expr.span),
            ));
            Type::Error
        }
        // Result<_>-? in something that's neither Result nor Option.
        (Type::Named(vn, _), other) if vn == "Result" => {
            diagnostics.push(Diagnostic::error(
                codes::T181,
                format!(
                    "`?` requires the enclosing function to return `Result<_, E>`, found `{}`",
                    render_type(other)
                ),
                Some(expr.span),
            ));
            Type::Error
        }
        // PR OptTry: Option-? in something that's neither Option nor Result.
        (Type::Named(vn, _), other) if vn == "Option" => {
            diagnostics.push(Diagnostic::error(
                codes::T181,
                format!(
                    "`?` requires the enclosing function to return `Option<T>`, found `{}`",
                    render_type(other)
                ),
                Some(expr.span),
            ));
            Type::Error
        }
        // Non-carrier value with `?`.
        (other, _) => {
            diagnostics.push(Diagnostic::error(
                codes::T182,
                format!(
                    "`?` requires a `Result<T, E>` or `Option<T>` value, found `{}`",
                    render_type(other)
                ),
                Some(expr.value.span()),
            ));
            Type::Error
        }
    };

    TypedExpr {
        ty,
        kind: TypedExprKind::Try(TypedTryExpr {
            value: Box::new(value),
        }),
        span: expr.span,

        refinement: None,
    }
}
