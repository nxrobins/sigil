//! Type-check-time capability expression inference.
//!
//! Handles the `cap.restrict()` / `cap.split()` / `cap.draw()` family
//! of expressions — the type-check half of the capability flow. The
//! complementary AIR-time flow proof lives in `crate::air_capability_v2`
//! (the sole prover); this module type-checks the SHAPE of cap operations
//! before any flow proof runs.
//!
//! ## Functions (all `pub(super)`)
//!
//! - `infer_cap_restrict_expr` — `cap.restrict("BurnOnly")`. Resolves
//!   the restriction name to a bitmask via the AuthorityRegistry.
//! - `infer_cap_restrict_deadline_expr` — `cap.restrict("BurnOnly",
//!   deadline=42)` — variant with parametric-cap deadline literal.
//! - `infer_cap_split_expr` — `cap.split(amount)`. Wall 2 split.
//! - `infer_cap_draw_expr` — `cap.draw(amount)` (non-consuming
//!   sibling of split; axis-1 motivation).
//!
//! Each function returns a `TypedExpr` carrying the resulting cap
//! type. Authority bitmask discharge / flow soundness is the
//! responsibility of `air_capability_v2::verify_air_capabilities`
//! post-AIR (the sole prover since AIR-cap quarantine PR 5).
//!
//! Extracted from `type_check/mod.rs` in structural-extraction PR 4.
//! Verbatim move — zero logic change. The shadow CI gate from PR 2.0
//! validates byte-equality of every diagnostic downstream.

use std::collections::{HashMap, HashSet};

use super::resolve::{
    is_error_code_type, is_machine_integer_type, is_runtime_message_abi_type, is_send_type,
    render_type, try_cap_deadline_diagnostic, type_compatible,
};
use super::{
    HandlerSig, MonomorphTracker, RegionId, Type, TypeCheckContext, check_block, closest_name,
    infer_expr, undefined_local_diagnostic,
};
use crate::ast::{
    AskExpr, CapDrawExpr, CapRestrictExpr, CapSplitExpr, DeclassifyExpr, Expr, GrantExpr,
    HandleExpr, Literal, MintExpr, RegionExpr, SendExpr, SpawnExpr,
};
use crate::diagnostics::{Diagnostic, codes};
use crate::span::Span;
use crate::typed_ast::{
    TypedAskExpr, TypedBlock, TypedCapDrawExpr, TypedCapRestrictExpr, TypedCapSplitExpr,
    TypedDeclassifyCtExpr, TypedDeclassifyExpr, TypedExpr, TypedExprKind, TypedGrantExpr,
    TypedHandleExpr, TypedMintExpr, TypedRegionExpr, TypedSendExpr, TypedSpawnExpr, TypedStmt,
    TypedSupervisionStrategy,
};

pub(super) fn infer_cap_restrict_expr(
    expr: &CapRestrictExpr,
    env: &HashMap<String, Type>,
    _current_return: &Type,
    context: TypeCheckContext<'_>,
    _tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let universe = context.universe;
    let cap_name = expr.cap.display_name();
    let cap_ty = env.get(&cap_name).cloned().unwrap_or_else(|| {
        diagnostics.push(undefined_local_diagnostic(
            &cap_name,
            format!("undefined local `{cap_name}`"),
            env,
            expr.cap.span,
        ));
        Type::Error
    });

    if !matches!(cap_ty, Type::Cap(_, _) | Type::Error) {
        diagnostics.push(Diagnostic::error(
            codes::T100,
            format!(
                "`.restrict()` requires a capability, found `{}`",
                render_type(&cap_ty)
            ),
            Some(expr.cap.span),
        ));
    }

    // Resolve restriction name to bitmask via AuthorityRegistry
    let cap_type_name = match &cap_ty {
        Type::Cap(name, _) => name.clone(),
        _ => "<unknown>".to_owned(),
    };
    let restriction_mask = match universe
        .authority_registry
        .restriction_mask(&cap_type_name, &expr.restriction)
    {
        Ok(mask) => mask,
        Err(msg) => {
            diagnostics.push(Diagnostic::error(codes::T101, msg, Some(expr.span)));
            0
        }
    };

    TypedExpr {
        ty: cap_ty,
        kind: TypedExprKind::CapRestrict(TypedCapRestrictExpr {
            cap: cap_name,
            restriction_name: expr.restriction.clone(),
            restriction_mask,
        }),
        span: expr.span,

        refinement: None,
    }
}

pub(super) fn infer_cap_restrict_deadline_expr(
    expr: &crate::ast::CapRestrictDeadlineExpr,
    env: &HashMap<String, Type>,
    _current_return: &Type,
    context: TypeCheckContext<'_>,
    _tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let universe = context.universe;
    let cap_name = expr.cap.display_name();
    let cap_ty = env.get(&cap_name).cloned().unwrap_or_else(|| {
        diagnostics.push(undefined_local_diagnostic(
            &cap_name,
            format!("undefined local `{cap_name}`"),
            env,
            expr.cap.span,
        ));
        Type::Error
    });

    let (cap_type_name, orig_params) = match &cap_ty {
        Type::Cap(name, params) => (name.clone(), params.clone()),
        Type::Error => ("<error>".to_owned(), Vec::new()),
        other => {
            diagnostics.push(Diagnostic::error(
                codes::T100,
                format!(
                    "`.restrict_deadline()` requires a capability, found `{}`",
                    render_type(other)
                ),
                Some(expr.cap.span),
            ));
            ("<error>".to_owned(), Vec::new())
        }
    };

    // Wall 2 → Wall 3: `restrict_deadline` is single-parameter narrowing.
    //   * arity 0 (non-parametric): T200 (existing "non-parametric" variant)
    //   * arity 1 (single-param): narrow position 0 (Stage 1 behavior)
    //   * arity > 1 (multi-param): T200 (new MULTI-PARAMETER variant —
    //     MC-8 fence requires distinguishable message)
    let narrowed_params: Vec<i64> = match orig_params.len() {
        0 if matches!(cap_ty, Type::Cap(_, _)) => {
            diagnostics.push(Diagnostic::error(
                codes::T200,
                format!(
                    "`.restrict_deadline()` requires a parametric (deadline-typed) cap; `{cap_type_name}` is non-parametric. Declare the cap as `cap type {cap_type_name}(<param>: i64) {{}}` to enable deadline narrowing."
                ),
                Some(expr.span),
            ));
            Vec::new()
        }
        n if n > 1 => {
            // INV-8a/8b fence: dedicated multi-parameter variant message.
            let param_render = orig_params
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            diagnostics.push(Diagnostic::error_with_hint(
                codes::T200,
                format!(
                    "`.restrict_deadline()` on multi-parameter cap `{cap_type_name}({param_render})` is not supported in Wall 3 Stage 1; multi-parameter narrowing is future work"
                ),
                Some(expr.span),
                "split the parameters into separate single-parameter cap types, or wait for the multi-parameter narrowing intrinsic in a future stage".to_owned(),
            ));
            orig_params.clone()
        }
        1 => {
            let d_orig = orig_params[0];
            if expr.deadline > d_orig {
                diagnostics.push(Diagnostic::error_with_hint(
                    codes::T200,
                    format!(
                        "`.restrict_deadline({})` would extend `{cap_type_name}({d_orig})`'s deadline; restrict_deadline can only narrow",
                        expr.deadline,
                    ),
                    Some(expr.span),
                    format!(
                        "pass a value `<= {d_orig}` to narrow, or drop the call entirely to keep the original deadline",
                    ),
                ));
                vec![d_orig]
            } else {
                vec![expr.deadline]
            }
        }
        _ => Vec::new(),
    };

    // Wall 2 Stage 3: close the narrowing escape hatch (only fires on
    // single-parameter caps since multi-param already rejected above).
    if orig_params.len() == 1
        && let Some(build_now) = universe.build_deadline
        && expr.deadline < build_now
    {
        diagnostics.push(Diagnostic::error_with_hint(
            codes::T199,
            format!(
                "`.restrict_deadline({})` narrows `{cap_type_name}` past the build-time reference (`--build-deadline {build_now}`); the resulting cap would be stale before any program execution",
                expr.deadline,
            ),
            Some(expr.span),
            format!(
                "pass a value `>= {build_now}` to keep the result valid at build time, or raise `--build-deadline` (or drop the flag) if intentional staleness is needed",
            ),
        ));
    }

    // Lower as a no-op authority restrict (full mask). Downstream type-
    // checks see Cap(name, narrowed_params) and route through the Stage
    // 1 subtyping rule (now generalized to all positions).
    let full_mask = universe.authority_registry.full_mask(&cap_type_name);
    TypedExpr {
        ty: Type::Cap(cap_type_name.clone(), narrowed_params),
        kind: TypedExprKind::CapRestrict(TypedCapRestrictExpr {
            cap: cap_name,
            restriction_name: format!("__deadline_{}", expr.deadline),
            restriction_mask: full_mask,
        }),
        span: expr.span,

        refinement: None,
    }
}

pub(super) fn infer_cap_split_expr(
    expr: &CapSplitExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let cap_name = expr.cap.display_name();
    let cap_ty = env.get(&cap_name).cloned().unwrap_or_else(|| {
        diagnostics.push(undefined_local_diagnostic(
            &cap_name,
            format!("undefined local `{cap_name}`"),
            env,
            expr.cap.span,
        ));
        Type::Error
    });

    if !matches!(cap_ty, Type::Cap(_, _) | Type::Error) {
        diagnostics.push(Diagnostic::error(
            codes::T102,
            format!(
                "`.split()` requires a capability, found `{}`",
                render_type(&cap_ty)
            ),
            Some(expr.cap.span),
        ));
    }

    let amount = infer_expr(
        &expr.amount,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    // PIL: route through `is_machine_integer_type` (admits IntLit + Error).
    if !is_machine_integer_type(&amount.ty) {
        diagnostics.push(Diagnostic::error(
            codes::T103,
            format!(
                "`.split()` amount must be `i64`, found `{}`",
                render_type(&amount.ty)
            ),
            Some(expr.amount.span()),
        ));
    }

    TypedExpr {
        ty: cap_ty,
        kind: TypedExprKind::CapSplit(TypedCapSplitExpr {
            cap: cap_name,
            amount: Box::new(amount),
        }),
        span: expr.span,

        refinement: None,
    }
}

/// Type-check `mint <CapType>[(deadlines)] for <target>` — the
/// capabilities-as-values constructor. The result type is the minted
/// `Type::Cap`. The minting-authority GATE (T273) is layered on in PR-M2;
/// this validates mintability (T272), deadline arity (T196/T197/T201), and
/// the target resource (T277).
pub(super) fn infer_mint_expr(
    expr: &MintExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let universe = context.universe;
    // Fail-closed mintability: a cap type is mintable iff it declared a
    // `mintable_by` policy. Both an unknown name and a policy-less cap → T272.
    let policy = universe.mintable_caps.get(&expr.cap_name);
    let mintable = policy.is_some();
    if !mintable {
        let detail = if universe.caps.contains(&expr.cap_name) {
            format!(
                "capability type `{}` is not mintable; declare it `cap type {} mintable_by <Authority> {{ … }}`",
                expr.cap_name, expr.cap_name
            )
        } else {
            format!("`{}` is not a declared capability type", expr.cap_name)
        };
        diagnostics.push(Diagnostic::error(
            codes::T272,
            detail,
            Some(expr.cap_name_span),
        ));
    }

    // Gate (T273): minting requires holding the cap type's declared minting
    // authority as an in-scope immutable borrow `&cap <Authority>`. Fail-closed:
    // absence of the authority is a hard error here, BEFORE AIR — so the Z3
    // oracle may trust any mint that reaches it (the `CapMint` legitimacy arm
    // asserts legitimacy unconditionally). "You need a capability to grant a
    // capability." The deeper check — that the held authority's *runtime
    // flow-mask* still carries the named mint bit — is a follow-on: a `&cap`
    // borrow is `AirValueKind::Copy`, not authority-tracked, so its mask is not
    // visible to type-check or the current Z3 layer (harden E3, documented).
    let mut authority_var: Option<String> = None;
    if let Some(policy) = policy {
        let mut held: Vec<String> = env
            .iter()
            .filter_map(|(name, ty)| match ty {
                Type::Ref(inner, false)
                    if matches!(&**inner, Type::Cap(n, _) if *n == policy.authority_cap) =>
                {
                    Some(name.clone())
                }
                _ => None,
            })
            .collect();
        held.sort(); // deterministic selection
        authority_var = held.into_iter().next();
        if authority_var.is_none() {
            diagnostics.push(Diagnostic::error(
                codes::T273,
                format!(
                    "`mint {}` requires an in-scope immutable borrow of its minting authority `{}` (a `&{}` parameter)",
                    expr.cap_name, policy.authority_cap, policy.authority_cap
                ),
                Some(expr.span),
            ));
        }
    }

    // Deadline arity (parametric caps): non-parametric + deadline → T197;
    // parametric + none → T196; parametric + wrong count → T201. (Deadline
    // staleness, T199/T200, is PR-M4.)
    match universe.parametric_caps.get(&expr.cap_name) {
        None => {
            if !expr.params.is_empty() {
                diagnostics.push(Diagnostic::error(
                    codes::T197,
                    format!(
                        "non-parametric capability `{}` cannot be minted with a deadline literal",
                        expr.cap_name
                    ),
                    Some(expr.span),
                ));
            }
        }
        Some(decl) => {
            if expr.params.is_empty() {
                diagnostics.push(Diagnostic::error(
                    codes::T196,
                    format!(
                        "parametric capability `{}` must be minted with {} deadline literal(s)",
                        expr.cap_name,
                        decl.len()
                    ),
                    Some(expr.span),
                ));
            } else if expr.params.len() != decl.len() {
                diagnostics.push(Diagnostic::error(
                    codes::T201,
                    format!(
                        "capability `{}` takes {} deadline parameter(s), but {} were supplied",
                        expr.cap_name,
                        decl.len(),
                        expr.params.len()
                    ),
                    Some(expr.span),
                ));
            } else if let Some(build_now) = universe.build_deadline {
                // Static revocation-by-expiry: a minted deadline that is
                // already past the build-time reference would be stale before
                // any execution (T199) — mirrors the cap-annotation check in
                // `validate_lowered_type`. One diagnostic per stale position.
                for (idx, d) in expr.params.iter().enumerate() {
                    if *d < build_now {
                        let position_name = decl
                            .get(idx)
                            .map(|p| p.name.as_str())
                            .unwrap_or("<position>");
                        diagnostics.push(Diagnostic::error(
                            codes::T199,
                            format!(
                                "minting capability `{}` parameter `{}` at position {} declares `{}`, which is past the build-time reference (`--build-deadline {}`); the cap would be stale before any program execution",
                                expr.cap_name, position_name, idx, d, build_now
                            ),
                            Some(expr.span),
                        ));
                    }
                }
            }
        }
    }

    // Target: the resource the capability authorizes. Honest provenance in
    // v1 (recorded, not enforced per-instance) — must be a nominal resource,
    // never a cap/primitive/ref/tuple.
    let typed_target = infer_expr(
        &expr.target,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    if !matches!(typed_target.ty, Type::Named(_, _) | Type::Error) {
        diagnostics.push(Diagnostic::error(
            codes::T277,
            format!(
                "`mint … for <target>` target must be a resource (a record/actor value), found `{}`",
                render_type(&typed_target.ty)
            ),
            Some(expr.target.span()),
        ));
    }

    let ty = if mintable {
        Type::Cap(expr.cap_name.clone(), expr.params.clone())
    } else {
        Type::Error
    };

    TypedExpr {
        ty,
        kind: TypedExprKind::Mint(TypedMintExpr {
            cap_name: expr.cap_name.clone(),
            params: expr.params.clone(),
            authority_var,
            target: Box::new(typed_target),
        }),
        span: expr.span,
        refinement: None,
    }
}

/// Type-check `cap.draw(amount)`. Structurally identical to `infer_cap_split_expr`
/// — the divergence is at the ownership layer (CapDraw doesn't move the
/// parent). T102/T103 are reused because the type-correctness conditions on
/// receiver and amount are the same.
pub(super) fn infer_cap_draw_expr(
    expr: &CapDrawExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let cap_name = expr.cap.display_name();
    let cap_ty = env.get(&cap_name).cloned().unwrap_or_else(|| {
        diagnostics.push(undefined_local_diagnostic(
            &cap_name,
            format!("undefined local `{cap_name}`"),
            env,
            expr.cap.span,
        ));
        Type::Error
    });

    if !matches!(cap_ty, Type::Cap(_, _) | Type::Error) {
        diagnostics.push(Diagnostic::error(
            codes::T102,
            format!(
                "`.draw()` requires a capability, found `{}`",
                render_type(&cap_ty)
            ),
            Some(expr.cap.span),
        ));
    }

    let amount = infer_expr(
        &expr.amount,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    // PIL: route through `is_machine_integer_type` (admits IntLit + Error).
    if !is_machine_integer_type(&amount.ty) {
        diagnostics.push(Diagnostic::error(
            codes::T103,
            format!(
                "`.draw()` amount must be `i64`, found `{}`",
                render_type(&amount.ty)
            ),
            Some(expr.amount.span()),
        ));
    }

    TypedExpr {
        ty: cap_ty,
        kind: TypedExprKind::CapDraw(TypedCapDrawExpr {
            cap: cap_name,
            amount: Box::new(amount),
        }),
        span: expr.span,

        refinement: None,
    }
}

// ── Scoped-body expressions (PR 5) ────────────────────────────────────
//
// Expressions whose body is a TypedBlock subject to scoped-control-flow
// restrictions: grant, handle, declassify, declassify_ct, region. All
// rely on `reject_control_flow_in_scoped_body` to refuse early
// `return` / `break` / `continue` inside the body (the block must
// fall through to the scope's exit so cap discharge / effect
// containment is well-defined).
//
// Extracted from `type_check/mod.rs` in structural-extraction PR 5.
// Verbatim move — zero logic change.

pub(super) fn infer_grant_expr(
    grant_expr: &GrantExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    // 1. Type-check cap expression — must be a borrow of a cap
    let cap_typed = infer_expr(
        &grant_expr.cap,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    match &cap_typed.ty {
        Type::Ref(inner, false) if matches!(inner.as_ref(), Type::Cap(_, _)) => {}
        Type::Slice(_) => {
            diagnostics.push(Diagnostic::error(
                codes::T104,
                "grant requires an immutable borrow of a capability (&cap T), not a slice",
                Some(grant_expr.cap.span()),
            ));
        }
        Type::Error => {}
        _ => {
            diagnostics.push(Diagnostic::error(
                codes::T105,
                format!(
                    "grant requires an immutable borrow of a capability (&cap T), found `{}`",
                    render_type(&cap_typed.ty)
                ),
                Some(grant_expr.cap.span()),
            ));
        }
    }

    // 2. Type-check body expression — must be a closure
    let body_typed = infer_expr(
        &grant_expr.body,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );

    // 3. Determine return type from closure
    let grant_ret_ty = match &body_typed.ty {
        Type::Fn(params, ret, _, _) if params.len() == 1 => {
            // Verify closure param matches cap borrow type
            if !type_compatible(&params[0], &cap_typed.ty) {
                diagnostics.push(Diagnostic::error(
                    codes::T106,
                    "grant closure parameter must match the borrowed capability type",
                    Some(grant_expr.body.span()),
                ));
            }
            *ret.clone()
        }
        Type::Fn(params, _, _, _) => {
            diagnostics.push(Diagnostic::error(
                codes::T107,
                format!(
                    "grant body must be a single-parameter closure, found {} parameters",
                    params.len()
                ),
                Some(grant_expr.body.span()),
            ));
            Type::Error
        }
        Type::Error => Type::Error,
        _ => {
            diagnostics.push(Diagnostic::error(
                codes::T108,
                "grant body must be a closure",
                Some(grant_expr.body.span()),
            ));
            Type::Error
        }
    };

    // 4. R005: ErrorCode sanitization — cross-ring Result errors must be u32.
    //
    // PR B commit #4: the `name == "Result"` check here is PRESERVED
    // as a security invariant (AG-PRB-D). R005 is structurally about
    // cross-ring return-types whose error arm crosses the trust
    // boundary; the Result-shape hardcoding here is the canonical
    // site that enforces "errors crossing ring boundaries MUST be
    // u32 ErrorCodes" — independent of whether `Result` is a
    // user-defined stdlib enum (post-PR-B) or a compiler intrinsic
    // (pre-PR-B). Deleting this check would silently admit
    // arbitrary error types across the trust boundary; future
    // tooling depends on the u32 contract.
    if let Type::Named(ref name, ref args) = grant_ret_ty
        && name == "Result"
        && args.len() == 2
        && !is_error_code_type(&args[1])
    {
        diagnostics.push(Diagnostic::error(
            codes::T109,
            format!(
                "cross-ring return errors must use ErrorCode (u32), found `{}`",
                render_type(&args[1])
            ),
            Some(grant_expr.span),
        ));
    }

    // 5. Assign grant ID
    let grant_id = tracker.functions.len() as u32; // simple unique ID

    TypedExpr {
        ty: grant_ret_ty,
        kind: TypedExprKind::Grant(TypedGrantExpr {
            cap: Box::new(cap_typed),
            body: Box::new(body_typed),
            grant_id,
        }),
        span: grant_expr.span,

        refinement: None,
    }
}

/// Reject control-flow statements (`if`, `while`, `match`, `for`, `return`)
/// inside a `handle` or `region` body. These bodies are lowered inline
/// within a single AIR basic block; control-flow forms have no semantic
/// home there without a separate proof framework for cross-block effect/
/// region scoping (or, for `return`, for propagating block termination up
/// through `lower_expr_into`). Closing this gap as a hard error replaces
/// the previous behavior where AIR silently dropped these statements,
/// leaving them invisible to the proof layer and the ownership checker.
/// T068.
///
/// Step 5 of the supremum loop extended this rejection to include
/// `return`. The previous lenience was for legacy test placeholder code;
/// rejecting now forces clean structure (put the return AFTER the handle,
/// not inside). If a real user policy needs early-return semantics from
/// a handle scope, the right fix is to properly lower it through the AIR
/// terminator path — a multi-function refactor that should be its own
/// iteration, not a silent escape hatch.
pub(super) fn reject_control_flow_in_scoped_body(
    body: &TypedBlock,
    construct: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for stmt in &body.statements {
        let (kind_name, span) = match stmt {
            TypedStmt::If(s) => ("if", s.span),
            TypedStmt::While(s) => ("while", s.span),
            TypedStmt::Match(s) => ("match", s.span),
            TypedStmt::ForIn(s) => ("for", s.iterable.span),
            TypedStmt::ForRange(s) => ("for", s.span),
            TypedStmt::Return(s) => ("return", s.span),
            TypedStmt::Break(span) => ("break", *span),
            TypedStmt::Continue(span) => ("continue", *span),
            TypedStmt::Let(_) | TypedStmt::Assign(_) | TypedStmt::Expr(_) => continue,
        };
        let hint = match kind_name {
            "return" => "Put the `return` AFTER the `handle`/`region` block, not inside it.",
            _ => "Extract control flow into a helper function and call it from the body.",
        };
        diagnostics.push(Diagnostic::error_with_hint(
            codes::T068,
            format!("`{kind_name}` is not allowed inside a `{construct}` body"),
            Some(span),
            hint,
        ));
    }
}

pub(super) fn infer_handle_expr(
    handle_expr: &HandleExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let universe = context.universe;
    // Resolve effect names — verify they exist in the registry
    for eff_name in &handle_expr.effects {
        if universe.effect_registry.lookup(eff_name).is_none() {
            diagnostics.push(Diagnostic::error(
                codes::T069,
                format!("unknown effect `{eff_name}`"),
                Some(handle_expr.span),
            ));
        } else if universe
            .effect_ops
            .get(eff_name)
            .is_some_and(|ops| !ops.is_empty())
        {
            // Effect Handlers (EH2, C-BARE): the bare row-widening `handle E { .. }`
            // form cannot give an operation-bearing effect's operations a meaning;
            // the clause form `handle <e> { E.op(x) => .. }` is required.
            diagnostics.push(Diagnostic::error(
                codes::E009,
                format!(
                    "effect `{eff_name}` declares operations — use the clause form `handle <expr> {{ {eff_name}.op(x) => ... }}`"
                ),
                Some(handle_expr.span),
            ));
        }
    }

    // Type-check the body block (new scope — clone env)
    let mut handle_env = env.clone();
    let mut handle_mutables = HashSet::new();
    let typed_body = check_block(
        &handle_expr.body,
        &mut handle_env,
        &mut handle_mutables,
        current_return,
        context,
        tracker,
        diagnostics,
        false, // don't enforce full return in handle body
    );

    reject_control_flow_in_scoped_body(&typed_body, "handle", diagnostics);

    // Handle block type = last expression type (or Unit)
    let body_ty = typed_body
        .statements
        .last()
        .and_then(|s| match s {
            TypedStmt::Expr(e) => Some(e.expr.ty.clone()),
            TypedStmt::Return(_) => Some(Type::Unit),
            _ => None,
        })
        .unwrap_or(Type::Unit);

    TypedExpr {
        ty: body_ty,
        kind: TypedExprKind::Handle(TypedHandleExpr {
            effects: handle_expr.effects.clone(),
            body: typed_body,
        }),
        span: handle_expr.span,

        refinement: None,
    }
}

pub(super) fn infer_declassify_expr(
    d: &DeclassifyExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let value = infer_expr(&d.value, env, current_return, context, tracker, diagnostics);
    let cap = infer_expr(&d.cap, env, current_return, context, tracker, diagnostics);
    if !matches!(cap.ty, Type::Cap(ref c, _) if c == "Declassify") {
        diagnostics.push(Diagnostic::error(
            codes::T110,
            format!(
                "declassify requires capability `Cap<Declassify>`, found `{}`",
                render_type(&cap.ty)
            ),
            Some(d.span),
        ));
    }
    let ty = value.ty.clone();
    TypedExpr {
        ty,
        kind: TypedExprKind::Declassify(TypedDeclassifyExpr {
            value: Box::new(value),
            cap: Box::new(cap),
        }),
        span: d.span,

        refinement: None,
    }
}

/// `declassify_ct(value, cap)` — lowers `@SecretCT → @Secret`. Cap type:
/// `Cap<DeclassifyCT>`, linear. See spec §3.4.1 / Phase B.
pub(super) fn infer_declassify_ct_expr(
    d: &crate::ast::DeclassifyCtExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let value = infer_expr(&d.value, env, current_return, context, tracker, diagnostics);
    let cap = infer_expr(&d.cap, env, current_return, context, tracker, diagnostics);
    if !matches!(cap.ty, Type::Cap(ref c, _) if c == "DeclassifyCT") {
        diagnostics.push(Diagnostic::error(
            codes::T110,
            format!(
                "declassify_ct requires capability `Cap<DeclassifyCT>`, found `{}`",
                render_type(&cap.ty)
            ),
            Some(d.span),
        ));
    }
    let ty = value.ty.clone();
    TypedExpr {
        ty,
        kind: TypedExprKind::DeclassifyCt(TypedDeclassifyCtExpr {
            value: Box::new(value),
            cap: Box::new(cap),
        }),
        span: d.span,

        refinement: None,
    }
}

pub(super) fn infer_region_expr(
    r: &RegionExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let limit = infer_expr(&r.limit, env, current_return, context, tracker, diagnostics);
    // Limit must be numeric
    // PIL: route through `is_machine_integer_type` (admits IntLit).
    if !is_machine_integer_type(&limit.ty) {
        diagnostics.push(Diagnostic::error(
            codes::T111,
            format!(
                "region limit must be numeric, found `{}`",
                render_type(&limit.ty)
            ),
            Some(r.limit.span()),
        ));
    }
    // Enter a deeper lexical lifetime for allocations in the body.
    let prev_region_depth = tracker.current_region_depth;
    tracker.current_region_depth = prev_region_depth + 1;

    let mut region_env = env.clone();
    let mut region_mutables = HashSet::new();
    // The region name is a handle whose lifetime is this lexical block.
    region_env.insert(r.name.clone(), Type::Region);
    tracker.region_locals.insert(
        r.name.clone(),
        RegionId::Lexical(tracker.current_region_depth),
    );
    let typed_body = check_block(
        &r.body,
        &mut region_env,
        &mut region_mutables,
        current_return,
        context,
        tracker,
        diagnostics,
        false,
    );
    reject_control_flow_in_scoped_body(&typed_body, "region", diagnostics);

    // `region` is statement-only, so its trailing value is discarded. Escape checks
    // apply to the body-internal call, return, construction, and assignment sinks.

    let ty = typed_body
        .statements
        .last()
        .and_then(|s| match s {
            TypedStmt::Expr(e) => Some(e.expr.ty.clone()),
            TypedStmt::Return(_) => Some(Type::Unit),
            _ => None,
        })
        .unwrap_or(Type::Unit);

    // Prune closed-region locals and restore the enclosing lexical depth.
    let exited_depth = tracker.current_region_depth;
    tracker
        .region_locals
        .retain(|_, rid| !matches!(rid, RegionId::Lexical(d) if *d >= exited_depth));
    tracker.current_region_depth = prev_region_depth;

    TypedExpr {
        ty,
        kind: TypedExprKind::Region(TypedRegionExpr {
            name: r.name.clone(),
            limit: Box::new(limit),
            body: typed_body,
        }),
        span: r.span,

        refinement: None,
    }
}

// ── Message-dispatch expressions (PR 6) ──────────────────────────────
//
// Actor-message dispatch type-checking: send (one-way), ask (request-
// reply), spawn (actor instantiation), plus shared helpers for
// validating handler/init parameter argument types and resolving the
// target actor.
//
// All three message kinds share validate_dispatch_args for per-argument
// type compatibility checking. infer_target_actor resolves the actor
// path. check_message_dispatch / check_ask_dispatch are the per-kind
// dispatchers consulted by check_send_expr / check_ask_expr.
//
// Note: these are ACTOR-MESSAGE dispatch helpers. Function-call
// cross-module dispatch (CrossModuleResolution + friends) stays in
// mod.rs — that's a separate axis.
//
// Extracted from `type_check/mod.rs` in structural-extraction PR 6.
// Verbatim move — zero logic change.

pub(super) fn check_send_expr(
    expr: &SendExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let target_name = expr.target.display_name();
    let target = infer_target_actor(&expr.target, env, diagnostics);
    let (actor_name, handler_name, args) = check_message_dispatch(
        "send",
        target.as_ref(),
        &expr.message,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );

    TypedExpr {
        ty: Type::Unit,
        kind: TypedExprKind::Send(TypedSendExpr {
            target: target_name,
            actor: actor_name,
            handler: handler_name,
            args,
        }),
        span: expr.span,

        refinement: None,
    }
}

pub(super) fn check_ask_expr(
    expr: &AskExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let target_name = expr.target.display_name();
    let target = infer_target_actor(&expr.target, env, diagnostics);
    let (actor_name, handler_name, args, ret) = check_ask_dispatch(
        target.as_ref(),
        &expr.message,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    let timeout = infer_expr(
        &expr.timeout,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );
    // PIL: route through `is_machine_integer_type` (admits IntLit + Error).
    if !is_machine_integer_type(&timeout.ty) {
        diagnostics.push(Diagnostic::error(
            codes::T093,
            format!(
                "`ask` timeout must be `i64`, found `{}`",
                render_type(&timeout.ty)
            ),
            Some(expr.timeout.span()),
        ));
    }

    TypedExpr {
        ty: ret,
        kind: TypedExprKind::Ask(TypedAskExpr {
            target: target_name,
            actor: actor_name,
            handler: handler_name,
            args,
            timeout: Box::new(timeout),
        }),
        span: expr.span,

        refinement: None,
    }
}

pub(super) fn check_spawn_expr(
    expr: &SpawnExpr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let actor_sigs = context.actor_sigs;
    let actor_name = expr.actor.display_name();
    let typed_args = expr
        .args
        .iter()
        .map(|arg| infer_expr(arg, env, current_return, context, tracker, diagnostics))
        .collect::<Vec<_>>();

    match actor_sigs.get(&actor_name) {
        Some(actor) => {
            if typed_args.len() != actor.init_params.len() {
                diagnostics.push(Diagnostic::error(
                    codes::T094,
                    format!(
                        "spawn of actor `{}` expects {} init argument(s), found {}",
                        actor_name,
                        actor.init_params.len(),
                        typed_args.len()
                    ),
                    Some(expr.span),
                ));
            }

            for (idx, (arg, expected)) in
                typed_args.iter().zip(actor.init_params.iter()).enumerate()
            {
                if !type_compatible(expected, &arg.ty) {
                    let arg_label = format!("init argument #{}", idx + 1);
                    let site_ctx =
                        format!("spawn of actor `{actor_name}` init argument #{}", idx + 1);
                    if let Some(t195) = try_cap_deadline_diagnostic(
                        expected, &arg.ty, &arg_label, &site_ctx, arg.span,
                    ) {
                        diagnostics.push(t195);
                    } else {
                        diagnostics.push(Diagnostic::error(
                            codes::T095,
                            format!(
                                "spawn of actor `{}` expected init argument of type `{}`, found `{}`",
                                actor_name,
                                render_type(expected),
                                render_type(&arg.ty)
                            ),
                            Some(arg.span),
                        ));
                    }
                }

                // Spawn args must be either caps (existing) or `Slot<Cap>`
                // (Wall 1 Step 3 — slots are the linear container for the
                // M-of-N quorum pattern). Both shapes lower to i32 at the
                // wasm boundary and are accepted by the actor's init.
                let is_slot_cap = matches!(
                    &arg.ty,
                    Type::Named(name, args)
                        if name == "Slot"
                            && args.len() == 1
                            && matches!(args[0], Type::Cap(_, _))
                );
                if !matches!(arg.ty, Type::Cap(_, _) | Type::Error) && !is_slot_cap {
                    diagnostics.push(Diagnostic::error(
                        codes::T096,
                        format!(
                            "spawn init arguments must be capability-typed or `Slot<Cap>`, found `{}`",
                            render_type(&arg.ty)
                        ),
                        Some(arg.span),
                    ));
                }
            }
        }
        None => {
            let message = format!("unknown actor `{}` in spawn expression", actor_name);
            let diag = match closest_name(&actor_name, actor_sigs.keys().map(String::as_str)) {
                Some(suggestion) => Diagnostic::error_with_hint(
                    codes::T064,
                    message,
                    Some(expr.actor.span),
                    format!("did you mean `{suggestion}`?"),
                ),
                None => Diagnostic::error(codes::T064, message, Some(expr.actor.span)),
            };
            diagnostics.push(diag);
        }
    }

    // Validate supervision strategy
    let supervision = expr.supervision.as_ref().map(|sup| match sup {
        crate::ast::SupervisionExpr::Stop => TypedSupervisionStrategy::Stop,
        crate::ast::SupervisionExpr::Restart { max_restarts } => {
            // max_restarts must be a compile-time integer literal
            match &**max_restarts {
                Expr::Literal(lit) => match &lit.literal {
                    Literal::Int(n) if *n > 0 && *n <= i32::MAX as i64 => {
                        TypedSupervisionStrategy::Restart {
                            max_restarts: *n as u32,
                        }
                    }
                    Literal::Int(n) => {
                        diagnostics.push(Diagnostic::error(
                            codes::T170,
                            format!(
                                "supervision `max_restarts` must be between 1 and {}, found `{n}`",
                                i32::MAX
                            ),
                            Some(max_restarts.span()),
                        ));
                        TypedSupervisionStrategy::Stop
                    }
                    _ => {
                        diagnostics.push(Diagnostic::error(
                            codes::T171,
                            "supervision `max_restarts` must be an integer literal",
                            Some(max_restarts.span()),
                        ));
                        TypedSupervisionStrategy::Stop
                    }
                },
                _ => {
                    diagnostics.push(Diagnostic::error(
                        codes::T172,
                        "supervision `max_restarts` must be a compile-time integer literal",
                        Some(max_restarts.span()),
                    ));
                    TypedSupervisionStrategy::Stop
                }
            }
        }
    });

    TypedExpr {
        ty: Type::ActorRef(actor_name.clone()),
        kind: TypedExprKind::Spawn(TypedSpawnExpr {
            actor: actor_name,
            args: typed_args,
            supervision,
        }),
        span: expr.span,

        refinement: None,
    }
}

pub(super) fn infer_target_actor(
    target: &crate::ast::Path,
    env: &HashMap<String, Type>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<String> {
    let target_name = target.display_name();
    match env.get(&target_name) {
        Some(Type::ActorRef(actor)) => Some(actor.clone()),
        Some(Type::Error) => None,
        Some(other) => {
            diagnostics.push(Diagnostic::error(
                codes::T097,
                format!(
                    "message target `{}` must be `ActorRef<T>`, found `{}`",
                    target_name,
                    render_type(other)
                ),
                Some(target.span),
            ));
            None
        }
        None => {
            diagnostics.push(undefined_local_diagnostic(
                &target_name,
                format!("undefined local `{}`", target_name),
                env,
                target.span,
            ));
            None
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_message_dispatch(
    op_name: &str,
    target_actor: Option<&String>,
    message: &Expr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> (String, String, Vec<TypedExpr>) {
    let actor_sigs = context.actor_sigs;
    let Some((handler_name, message_args, span)) =
        parse_message_call(message, op_name, diagnostics)
    else {
        return ("<error>".to_owned(), "<error>".to_owned(), Vec::new());
    };

    let typed_args = message_args
        .iter()
        .map(|arg| infer_expr(arg, env, current_return, context, tracker, diagnostics))
        .collect::<Vec<_>>();

    let Some(actor_name) = target_actor.cloned() else {
        return ("<error>".to_owned(), handler_name, typed_args);
    };

    let Some(actor) = actor_sigs.get(&actor_name) else {
        let message = format!("unknown actor `{}`", actor_name);
        let diag = match closest_name(&actor_name, actor_sigs.keys().map(String::as_str)) {
            Some(suggestion) => Diagnostic::error_with_hint(
                codes::T064,
                message,
                Some(span),
                format!("did you mean `{suggestion}`?"),
            ),
            None => Diagnostic::error(codes::T064, message, Some(span)),
        };
        diagnostics.push(diag);
        return (actor_name, handler_name, typed_args);
    };

    let Some(handler) = actor.handlers.get(&handler_name) else {
        let message = format!("actor `{}` has no handler `{}`", actor_name, handler_name);
        let diag = match closest_name(&handler_name, actor.handlers.keys().map(String::as_str)) {
            Some(suggestion) => Diagnostic::error_with_hint(
                codes::T065,
                message,
                Some(span),
                format!("did you mean `{suggestion}`?"),
            ),
            None => Diagnostic::error(codes::T065, message, Some(span)),
        };
        diagnostics.push(diag);
        return (actor_name, handler_name, typed_args);
    };

    validate_dispatch_args(
        op_name,
        &actor_name,
        &handler_name,
        &typed_args,
        handler,
        diagnostics,
    );
    (actor_name, handler_name, typed_args)
}

pub(super) fn check_ask_dispatch(
    target_actor: Option<&String>,
    message: &Expr,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> (String, String, Vec<TypedExpr>, Type) {
    let actor_sigs = context.actor_sigs;
    let (actor_name, handler_name, typed_args) = check_message_dispatch(
        "ask",
        target_actor,
        message,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );

    let ret = actor_sigs
        .get(&actor_name)
        .and_then(|actor| actor.handlers.get(&handler_name))
        .map(|handler| handler.ret.clone())
        .unwrap_or(Type::Error);

    if matches!(ret, Type::Unit) {
        diagnostics.push(Diagnostic::error(
            codes::T098,
            format!(
                "`ask` requires handler `{}` on actor `{}` to return a value",
                handler_name, actor_name
            ),
            Some(message.span()),
        ));
        return (actor_name, handler_name, typed_args, Type::Error);
    }

    if !is_send_type(&ret) {
        diagnostics.push(Diagnostic::error(
            codes::T099,
            format!(
                "`ask` requires handler `{}` on actor `{}` to return a `Send` type, found `{}`",
                handler_name,
                actor_name,
                render_type(&ret)
            ),
            Some(message.span()),
        ));
    }

    if !is_runtime_message_abi_type(&ret) {
        diagnostics.push(Diagnostic::error(
            codes::T112,
            format!(
                "`ask` currently supports runtime-returnable handler types of `bool`, `i64`, `ActorRef<T>`, or cap types, found `{}`",
                render_type(&ret)
            ),
            Some(message.span()),
        ));
    }

    (actor_name, handler_name, typed_args, ret)
}

pub(super) fn parse_message_call<'a>(
    message: &'a Expr,
    op_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<(String, &'a [Expr], Span)> {
    let Expr::Call(call) = message else {
        diagnostics.push(Diagnostic::error(
            codes::T113,
            format!("`{}` expects a message constructor call", op_name),
            Some(message.span()),
        ));
        return None;
    };

    match call.callee.segments.as_slice() {
        [handler] => Some((handler.clone(), call.args.as_slice(), call.span)),
        _ => {
            diagnostics.push(Diagnostic::error(
                codes::T114,
                format!(
                    "`{}` message constructors must be simple calls like `Name(...)`",
                    op_name
                ),
                Some(call.span),
            ));
            None
        }
    }
}

pub(super) fn validate_dispatch_args(
    op_name: &str,
    actor_name: &str,
    handler_name: &str,
    typed_args: &[TypedExpr],
    handler: &HandlerSig,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if typed_args.len() != handler.params.len() {
        diagnostics.push(Diagnostic::error(
            codes::T115,
            format!(
                "`{}` to handler `{}` on actor `{}` expects {} argument(s), found {}",
                op_name,
                handler_name,
                actor_name,
                handler.params.len(),
                typed_args.len()
            ),
            typed_args.last().map(|arg| arg.span),
        ));
    }

    for (idx, (arg, expected)) in typed_args.iter().zip(handler.params.iter()).enumerate() {
        if !type_compatible(expected, &arg.ty) {
            let arg_label = format!("argument #{}", idx + 1);
            let site_ctx = format!(
                "`{op_name}` to handler `{handler_name}` on actor `{actor_name}` argument #{}",
                idx + 1
            );
            if let Some(t195) =
                try_cap_deadline_diagnostic(expected, &arg.ty, &arg_label, &site_ctx, arg.span)
            {
                diagnostics.push(t195);
            } else {
                diagnostics.push(Diagnostic::error(
                    codes::T116,
                    format!(
                        "`{}` to handler `{}` on actor `{}` expected argument of type `{}`, found `{}`",
                        op_name,
                        handler_name,
                        actor_name,
                        render_type(expected),
                        render_type(&arg.ty)
                    ),
                    Some(arg.span),
                ));
            }
        }

        if !is_send_type(&arg.ty) {
            diagnostics.push(Diagnostic::error(
                codes::T117,
                format!(
                    "`{}` to handler `{}` on actor `{}` requires `Send` message arguments, found `{}`",
                    op_name,
                    handler_name,
                    actor_name,
                    render_type(&arg.ty)
                ),
                Some(arg.span),
            ));
        }

        if !is_runtime_message_abi_type(&arg.ty) {
            diagnostics.push(Diagnostic::error(
                codes::T118,
                format!(
                    "`{}` to handler `{}` on actor `{}` currently supports runtime-serializable arguments of `bool`, `i64`, `ActorRef<T>`, or cap types, found `{}`",
                    op_name,
                    handler_name,
                    actor_name,
                    render_type(&arg.ty)
                ),
                Some(arg.span),
            ));
        }
    }
}
