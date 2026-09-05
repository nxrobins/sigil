//! Effect checker pass.
//!
//! Validates that outer-ring functions only call functions whose effects
//! are a subset of their own declared effect row. Inner-ring functions
//! are exempt (actor model handles effects implicitly).
//!
//! `handle Effect1, Effect2 { ... }` blocks expand the available effect set
//! within their body — callees requiring those effects become legal.
//!
//! `handle Unsafe { ... }` is only legal inside `#[trusted]` modules (E002).

use crate::{
    ast::Ring,
    diagnostics::{Diagnostic, codes},
    type_check::{
        EffectSet, Type, TypedExpr, TypedExprKind, TypedIntrinsicKind, TypedProgram, TypedStmt,
    },
    type_check_v2::refinement::visit_block_constructs,
};

/// Effect Handlers (EH3): the staged-rollout gate. A well-formed `perform` /
/// clause-form `handle` / `resume` now produces a real typed node (so the
/// security passes can walk it — constraint C-VIS), but its LOWERING is not
/// implemented until EH4. This pass — run AFTER the typed-program checks and
/// BEFORE AIR — rejects any such node with E004, so it never reaches AIR and the
/// byte-identical-AIR invariant holds. Removed/narrowed as the lowering lands.
pub fn check_effect_handlers_gated(program: &TypedProgram) -> Result<(), Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    for module in &program.modules {
        for function in &module.functions {
            // `module.functions` carries EVERY body (module fns, actor init /
            // handlers, lambda-lifted closures), so this is comprehensive.
            visit_block_constructs(&function.body, &mut |e: &TypedExpr| {
                let what = match &e.kind {
                    TypedExprKind::Perform(_) => "perform",
                    TypedExprKind::ClauseHandle(_) => "clause-form handle",
                    TypedExprKind::Resume(_) => "resume",
                    _ => return,
                };
                diagnostics.push(Diagnostic::error(
                    codes::E004,
                    format!(
                        "`{what}` is well-formed, but effect-handler lowering is not implemented yet (E004)"
                    ),
                    Some(e.span),
                ));
            });
        }
    }
    if diagnostics.is_empty() {
        Ok(())
    } else {
        Err(diagnostics)
    }
}

pub fn check_effects(program: &TypedProgram) -> Result<(), Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();

    for module in &program.modules {
        if module.ring == Ring::Inner {
            continue; // inner ring exempt
        }
        for function in &module.functions {
            walk_stmts(
                &function.body.statements,
                &function.effects,
                module.trusted,
                program,
                &mut diagnostics,
            );
        }
    }

    if diagnostics.is_empty() {
        Ok(())
    } else {
        Err(diagnostics)
    }
}

fn walk_stmts(
    stmts: &[TypedStmt],
    caller_effects: &EffectSet,
    trusted: bool,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for stmt in stmts {
        match stmt {
            TypedStmt::Let(s) => {
                walk_expr_effects(&s.value, caller_effects, trusted, program, diagnostics)
            }
            TypedStmt::Assign(s) => {
                walk_expr_effects(&s.value, caller_effects, trusted, program, diagnostics)
            }
            TypedStmt::Expr(s) => {
                walk_expr_effects(&s.expr, caller_effects, trusted, program, diagnostics)
            }
            TypedStmt::If(s) => {
                walk_expr_effects(&s.condition, caller_effects, trusted, program, diagnostics);
                walk_stmts(
                    &s.then_branch.statements,
                    caller_effects,
                    trusted,
                    program,
                    diagnostics,
                );
                walk_stmts(
                    &s.else_branch.statements,
                    caller_effects,
                    trusted,
                    program,
                    diagnostics,
                );
            }
            TypedStmt::While(s) => {
                walk_expr_effects(&s.condition, caller_effects, trusted, program, diagnostics);
                walk_stmts(
                    &s.body.statements,
                    caller_effects,
                    trusted,
                    program,
                    diagnostics,
                );
            }
            TypedStmt::ForIn(s) => {
                walk_expr_effects(&s.iterable, caller_effects, trusted, program, diagnostics);
                walk_stmts(&s.body, caller_effects, trusted, program, diagnostics);
            }
            TypedStmt::ForRange(s) => {
                walk_expr_effects(&s.start, caller_effects, trusted, program, diagnostics);
                walk_expr_effects(&s.end, caller_effects, trusted, program, diagnostics);
                walk_stmts(&s.body, caller_effects, trusted, program, diagnostics);
            }
            TypedStmt::Match(s) => {
                walk_expr_effects(&s.scrutinee, caller_effects, trusted, program, diagnostics);
                for arm in &s.arms {
                    if let Some(g) = &arm.guard {
                        walk_expr_effects(g, caller_effects, trusted, program, diagnostics);
                    }
                    walk_stmts(
                        &arm.body.statements,
                        caller_effects,
                        trusted,
                        program,
                        diagnostics,
                    );
                }
            }
            TypedStmt::Return(s) => {
                if let Some(v) = &s.value {
                    walk_expr_effects(v, caller_effects, trusted, program, diagnostics);
                }
            }
            // break/continue invoke nothing — no effects.
            TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
        }
    }
}

fn walk_expr_effects(
    expr: &crate::type_check::TypedExpr,
    caller_effects: &EffectSet,
    trusted: bool,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match &expr.kind {
        TypedExprKind::Call(call) => {
            // Find the callee's effects
            if let Some(callee_fn) = find_function(program, &call.callee)
                && !callee_fn.effects.is_subset_of(caller_effects)
            {
                let missing: Vec<String> = callee_fn
                    .effects
                    .effects
                    .difference(&caller_effects.effects)
                    .map(|id| {
                        program
                            .effect_registry
                            .name_of(*id)
                            .unwrap_or("?")
                            .to_owned()
                    })
                    .collect();
                diagnostics.push(Diagnostic::error(
                    codes::E001,
                    format!(
                        "undeclared effect(s) {} — callee `{}` requires effects not in caller's row",
                        missing.join(", "),
                        call.callee
                    ),
                    Some(expr.span),
                ));
            }
            // Walk args
            for arg in &call.args {
                walk_expr_effects(arg, caller_effects, trusted, program, diagnostics);
            }
        }
        TypedExprKind::Intrinsic(intrinsic) => {
            for arg in &intrinsic.args {
                walk_expr_effects(arg, caller_effects, trusted, program, diagnostics);
            }
            if matches!(intrinsic.kind, TypedIntrinsicKind::Alloc)
                && let Some(alloc_id) = program.effect_registry.lookup("Alloc")
                && !caller_effects.effects.contains(&alloc_id)
            {
                diagnostics.push(Diagnostic::error(
                    codes::E001,
                    "undeclared effect(s) Alloc — intrinsic `alloc` requires `Alloc` in the caller's row",
                    Some(expr.span),
                ));
            }
        }
        TypedExprKind::Binary(b) => {
            walk_expr_effects(&b.lhs, caller_effects, trusted, program, diagnostics);
            walk_expr_effects(&b.rhs, caller_effects, trusted, program, diagnostics);
        }
        TypedExprKind::Borrow(b) => {
            walk_expr_effects(&b.inner, caller_effects, trusted, program, diagnostics);
        }
        TypedExprKind::Grant(g) => {
            walk_expr_effects(&g.cap, caller_effects, trusted, program, diagnostics);
            walk_expr_effects(&g.body, caller_effects, trusted, program, diagnostics);
        }
        TypedExprKind::Declassify(d) => {
            walk_expr_effects(&d.value, caller_effects, trusted, program, diagnostics);
            walk_expr_effects(&d.cap, caller_effects, trusted, program, diagnostics);
        }
        TypedExprKind::DeclassifyCt(d) => {
            walk_expr_effects(&d.value, caller_effects, trusted, program, diagnostics);
            walk_expr_effects(&d.cap, caller_effects, trusted, program, diagnostics);
        }
        TypedExprKind::Handle(h) => {
            // E002: handle Unsafe requires #[trusted] module
            if h.effects.iter().any(|e| e == "Unsafe") && !trusted {
                diagnostics.push(Diagnostic::error(
                    codes::E002,
                    "handle Unsafe is only allowed in #[trusted] modules (E002)",
                    Some(expr.span),
                ));
            }

            // Expand available effects: caller_effects ∪ handled effects
            let mut expanded = caller_effects.clone();
            for eff_name in &h.effects {
                if let Some(eff_id) = program.effect_registry.lookup(eff_name) {
                    expanded.effects.insert(eff_id);
                }
            }

            // Walk handle body with expanded effects
            walk_stmts(&h.body.statements, &expanded, trusted, program, diagnostics);
        }
        // Effect Handlers (EH3.3): a `perform E.op(..)` requires `E` to be
        // available in the caller's row (or expanded by an enclosing handler) —
        // else it is an ORPHAN perform (C-ORPHAN, E010). Inner-ring functions are
        // skipped by `check_effects`, so this is an outer-ring check.
        TypedExprKind::Perform(p) => {
            if let Some(eff_id) = program.effect_registry.lookup(&p.effect)
                && !caller_effects.effects.contains(&eff_id)
            {
                diagnostics.push(Diagnostic::error(
                    codes::E010,
                    format!(
                        "`perform {}.{}` requires effect `{}`, which is not in this function's effect row — declare `! {{ {} }}` or wrap the computation in a `handle` that discharges it",
                        p.effect, p.op, p.effect, p.effect
                    ),
                    Some(expr.span),
                ));
            }
            for arg in &p.args {
                walk_expr_effects(arg, caller_effects, trusted, program, diagnostics);
            }
        }
        // Effect Handlers (EH3.3): clause-aware DISCHARGE (C-DISCHARGE). The
        // handled effects become available to the SCRUTINEE (the handled
        // computation), so the scrutinee's use of them is no longer a leak; every
        // OTHER effect of the scrutinee still propagates. Clause BODIES run in the
        // handler's (caller's) context, so they keep the caller's row.
        TypedExprKind::ClauseHandle(c) => {
            let mut expanded = caller_effects.clone();
            for clause in &c.clauses {
                if let Some(eff_id) = program.effect_registry.lookup(&clause.effect) {
                    expanded.effects.insert(eff_id);
                }
            }
            walk_expr_effects(&c.scrutinee, &expanded, trusted, program, diagnostics);
            for clause in &c.clauses {
                walk_stmts(
                    &clause.body.statements,
                    caller_effects,
                    trusted,
                    program,
                    diagnostics,
                );
            }
        }
        TypedExprKind::Resume(r) => {
            walk_expr_effects(&r.value, caller_effects, trusted, program, diagnostics);
        }
        TypedExprKind::ArrayLit(a) => {
            for elem in &a.elements {
                walk_expr_effects(elem, caller_effects, trusted, program, diagnostics);
            }
        }
        // PR-E3: an f-string's effects are those of its interpolation holes.
        TypedExprKind::FString(fs) => {
            for part in &fs.parts {
                if let crate::typed_ast::TypedFStringPart::Hole(h) = part {
                    walk_expr_effects(h, caller_effects, trusted, program, diagnostics);
                }
            }
        }
        TypedExprKind::Index(i) => {
            walk_expr_effects(&i.array, caller_effects, trusted, program, diagnostics);
            walk_expr_effects(&i.index, caller_effects, trusted, program, diagnostics);
        }
        // PR AF / N20-AF: slice operator emits no new effects.
        // Bounds-check arithmetic is pure. Walk the children so
        // any effect-emitting sub-expressions (e.g., a function
        // call as the `end` bound) are accounted for.
        TypedExprKind::Slice(s) => {
            walk_expr_effects(&s.array, caller_effects, trusted, program, diagnostics);
            if let Some(start) = &s.start {
                walk_expr_effects(start, caller_effects, trusted, program, diagnostics);
            }
            if let Some(end) = &s.end {
                walk_expr_effects(end, caller_effects, trusted, program, diagnostics);
            }
        }
        TypedExprKind::RecordConstruct(r) => {
            for (_, field) in &r.fields {
                walk_expr_effects(field, caller_effects, trusted, program, diagnostics);
            }
        }
        TypedExprKind::FieldAccess(f) => {
            walk_expr_effects(&f.object, caller_effects, trusted, program, diagnostics);
        }
        TypedExprKind::EnumConstruct(e) => {
            for field in &e.fields {
                walk_expr_effects(field, caller_effects, trusted, program, diagnostics);
            }
        }
        TypedExprKind::ExternCall(ext) => {
            for arg in &ext.args {
                walk_expr_effects(arg, caller_effects, trusted, program, diagnostics);
            }
        }
        TypedExprKind::Region(r) => {
            walk_expr_effects(&r.limit, caller_effects, trusted, program, diagnostics);
            walk_stmts(
                &r.body.statements,
                caller_effects,
                trusted,
                program,
                diagnostics,
            );
        }
        TypedExprKind::ResultCtor(r) => {
            walk_expr_effects(&r.value, caller_effects, trusted, program, diagnostics);
        }
        TypedExprKind::Try(t) => {
            walk_expr_effects(&t.value, caller_effects, trusted, program, diagnostics);
        }
        TypedExprKind::Send(s) => {
            for arg in &s.args {
                walk_expr_effects(arg, caller_effects, trusted, program, diagnostics);
            }
        }
        TypedExprKind::Ask(a) => {
            for arg in &a.args {
                walk_expr_effects(arg, caller_effects, trusted, program, diagnostics);
            }
            walk_expr_effects(&a.timeout, caller_effects, trusted, program, diagnostics);
        }
        TypedExprKind::Spawn(s) => {
            for arg in &s.args {
                walk_expr_effects(arg, caller_effects, trusted, program, diagnostics);
            }
        }
        // HOF / AG-HOF-A: APPLICATION is where a closure's latent effect row is
        // DISCHARGED. The row rides the arrow type (`Type::Fn(.., latent)`), so a closure
        // that crossed a function boundary still carries it and the laundering this arm
        // used to permit — construct in an `{Alloc}` context, return, apply in a `{}`
        // context — is now a compile-time rejection rather than a runtime trap.
        //
        // Mirrors the λ-SIGIL rule `Γ ⊢ f : A -[ε]-> B, Γ ⊢ a : A ⟹ Γ ⊢ f a : B ! ε`
        // (`Chk.app_latent_bounded`, proofs/lean/LambdaSigil/EffectRows.lean).
        //
        // Per N9-HOF this arm is explicit (no `_ =>` wildcard absorbs IndirectCall).
        TypedExprKind::IndirectCall(call) => {
            for arg in &call.args {
                walk_expr_effects(arg, caller_effects, trusted, program, diagnostics);
            }
            let Type::Fn(_, _, _, latent) = &call.callee_ty else {
                // FAIL CLOSED. Type-checking is expected to give an indirect callee a
                // function type; if that ever stops holding we must not silently skip the
                // discharge — silently skipping is precisely the bug this arm fixes.
                diagnostics.push(Diagnostic::error(
                    codes::E001,
                    format!(
                        "cannot determine the latent effect row of `{}` (callee is not a \
                         function type) — refusing to skip the effect check",
                        call.callee_local
                    ),
                    Some(expr.span),
                ));
                return;
            };
            if !latent.is_subset_of(caller_effects) {
                let missing: Vec<String> = latent
                    .effects
                    .difference(&caller_effects.effects)
                    .map(|id| {
                        program
                            .effect_registry
                            .name_of(*id)
                            .unwrap_or("?")
                            .to_owned()
                    })
                    .collect();
                // The row a closure carries is INFERRED from its body
                // (`type_check/effect_infer.rs`, roadmap Phase 1), so the effects named
                // here are ones the closure genuinely performs when applied — with one
                // honest caveat worth surfacing: a call whose callee could not be
                // resolved charges the DEFINING function's declared row (the fail-closed
                // miss path), which can over-state the row. The fix in either case is
                // the same: declare the effect here, or discharge it with a `handle`.
                diagnostics.push(Diagnostic::error(
                    codes::E001,
                    format!(
                        "undeclared effect(s) {} — applying closure `{}` performs effects \
                         not in this function's row; declare them here (`! {{ {} }}`) or \
                         wrap the application in a `handle` that discharges them",
                        missing.join(", "),
                        call.callee_local,
                        missing.join(", ")
                    ),
                    Some(expr.span),
                ));
            }
        }
        // Capabilities-as-values: `mint` itself is pure (no effect); walk the
        // target for any effects in the resource expression.
        TypedExprKind::Mint(m) => {
            walk_expr_effects(&m.target, caller_effects, trusted, program, diagnostics);
        }
        // Leaf expressions — no sub-expressions to check.
        //
        // `ClosureConstruct` stays a leaf DELIBERATELY: constructing a closure performs no
        // effects (only applying it does — see the `IndirectCall` arm), and the closure's
        // body is not skipped either, because lambda-lifting makes it a real
        // `TypedFunction` that `check_effects` walks against its own recorded row. The
        // AG-HOF-A bug was never construction; it was the missing discharge at application.
        TypedExprKind::Literal(_)
        | TypedExprKind::Local(_)
        | TypedExprKind::StateField(_)
        | TypedExprKind::ClosureConstruct(_)
        | TypedExprKind::CapRestrict(_)
        | TypedExprKind::CapSplit(_)
        | TypedExprKind::CapDraw(_) => {}
    }
}

fn find_function<'a>(
    program: &'a TypedProgram,
    name: &str,
) -> Option<&'a crate::type_check::TypedFunction> {
    program
        .modules
        .iter()
        .flat_map(|m| m.functions.iter())
        .find(|f| f.name == name)
}
