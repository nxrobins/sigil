//! Bottom-up effect-row inference for closure bodies (roadmap Phase 1).
//!
//! `effect_check::walk_expr_effects` is a top-down CHECKER: it threads the caller's
//! declared row downward and emits E001/E010 where the body needs more. This module is
//! its adjoint — a bottom-up SYNTHESIZER that computes the row a just-typed block
//! actually performs, so a closure's latent row (`Type::Fn`'s 4th field) can be
//! precise instead of inheriting the enclosing function's declared row wholesale.
//!
//! The two are deliberately independent implementations of one semantics, and they
//! compose into a one-directional cross-check: `check_effects` walks every lifted
//! closure against the row recorded here, so an inference UNDER-approximation (the
//! false-accept direction — the AG-HOF-A class) makes the walk fire a loud E001/E010
//! inside the closure body. An over-approximation is silent imprecision, never
//! unsoundness. This mirrors the mechanized architecture exactly: λ-SIGIL's `Typing`
//! synthesizes a row and `Chk` checks `ε ⊆ δ`, with `Chk.complete` the theorem that a
//! synthesized row always checks against itself
//! (`proofs/lean/LambdaSigil/EffectRows.lean`).
//!
//! ## Parity contract with the checker
//!
//! Arm-for-arm parity with `walk_expr_effects`, including its deliberate exclusions:
//!
//! * `ExternCall` is NOT charged (ET-EFF-1: externs are outside the effect-subset
//!   discipline; the checker walks only their args).
//! * `ClosureConstruct` contributes NOTHING (construction is pure — λ-SIGIL's `lam`
//!   rule; the constructed closure's own row rides its `Type::Fn` and is discharged
//!   at application via the `IndirectCall` arm).
//! * `Handle`/`ClauseHandle` SUBTRACT what they discharge — the exact dual of the
//!   checker's row EXPANSION at the same nodes.
//! * An unregistered effect name resolves to nothing, matching
//!   `resolve_effect_row`'s silent-drop (the SH-EFFECT-pinned registration filter).
//!
//! ## Selfhost shadow
//!
//! The SH-EFFECT shadow (`selfhost/effect_check.sigil`) treats closures as full leaves
//! and does not model this inference; its differential corpus deliberately contains no
//! closure fixtures, so parity holds. Any FUTURE closure fixture added to that corpus
//! will need the shadow to mirror this inference first. (The note lives here rather
//! than in the `.sigil` source because the composed selfhost source is byte-pinned by
//! PIN-7 — `pin_certified_artifact_digest` — and a comment there churns a certified
//! artifact.)
//!
//! ## Fail-closed callee resolution
//!
//! A `Call`'s callee is resolved through, in order: the tracker's already-lifted
//! functions (monomorphized instances and earlier closures carry module-qualified
//! names), the current module's `FunctionSig`s (bare and `Type::method` keys, with
//! the current-module `mod::` prefix stripped), then `workspace_sigs` for a
//! `module::name` split. A name that resolves NOWHERE unions the enclosing
//! function's declared row instead — degrading, for that call, to exactly the
//! pre-Phase-1 over-approximation rather than silently dropping effects.

use std::collections::BTreeMap;

use crate::registries::{EffectRegistry, EffectSet};
use crate::typed_ast::{
    TypedBlock, TypedExpr, TypedExprKind, TypedFStringPart, TypedFunction, TypedIntrinsicKind,
    TypedStmt,
};

use super::types::FunctionSig;

/// Everything the inferencer can consult at type-check time. Built at the closure
/// construction site from the tracker + `TypeCheckContext` — there is no
/// `TypedProgram` yet, which is why this cannot simply reuse `effect_check`'s
/// `find_function`.
pub(super) struct EffectInferCtx<'a> {
    /// `tracker.functions` — closures and monomorphized instances lifted so far.
    /// Post-order guarantees a nested closure's row is final before its parent's
    /// is computed.
    pub(super) functions: &'a [TypedFunction],
    /// Current module's signatures (bare names + `Type::method` keys), now carrying
    /// the declared row.
    pub(super) function_sigs: &'a BTreeMap<String, FunctionSig>,
    /// Cross-module signatures, keyed `module -> name -> sig`.
    pub(super) workspace_sigs: &'a BTreeMap<String, BTreeMap<String, FunctionSig>>,
    pub(super) effect_registry: &'a EffectRegistry,
    /// The current module — used to strip a `mod::` qualification before the
    /// bare-name sig lookup.
    pub(super) module_name: &'a str,
    /// The enclosing function's declared row: the fail-closed answer for any
    /// callee that cannot be resolved.
    pub(super) fallback: &'a EffectSet,
}

impl<'a> EffectInferCtx<'a> {
    /// The declared row of a named callee, or `None` if the name resolves nowhere.
    fn callee_row(&self, callee: &str) -> Option<EffectSet> {
        // 1. Already-lifted functions (mono instances, earlier closures).
        if let Some(f) = self.functions.iter().find(|f| f.name == callee) {
            return Some(f.effects.clone());
        }
        // 2. Current-module sigs: as written, and with the current module's
        //    qualification stripped (typed callees are frequently qualified).
        if let Some(sig) = self.function_sigs.get(callee) {
            return Some(sig.effects.clone());
        }
        if let Some(bare) = callee.strip_prefix(&format!("{}::", self.module_name))
            && let Some(sig) = self.function_sigs.get(bare)
        {
            return Some(sig.effects.clone());
        }
        // 3. Cross-module: split on the FIRST `::`. (A `Type::method` key was
        //    already tried verbatim in step 2, so reaching here with one means the
        //    "module" segment is a type name and the lookup simply misses.)
        if let Some((module, name)) = callee.split_once("::")
            && let Some(sig) = self.workspace_sigs.get(module).and_then(|m| m.get(name))
        {
            return Some(sig.effects.clone());
        }
        None
    }
}

/// The effect row a fully-typed block performs. Bottom-up, single pass.
pub(super) fn effects_of_block(block: &TypedBlock, ctx: &EffectInferCtx<'_>) -> EffectSet {
    effects_of_stmts(&block.statements, ctx)
}

fn effects_of_stmts(stmts: &[TypedStmt], ctx: &EffectInferCtx<'_>) -> EffectSet {
    let mut row = EffectSet::empty();
    for stmt in stmts {
        // Arm-for-arm with `effect_check::walk_stmts` — no wildcard, so a new
        // statement kind fails to compile here until classified (walker-fence
        // discipline).
        match stmt {
            TypedStmt::Let(s) => union(&mut row, effects_of_expr(&s.value, ctx)),
            TypedStmt::Assign(s) => union(&mut row, effects_of_expr(&s.value, ctx)),
            TypedStmt::Expr(s) => union(&mut row, effects_of_expr(&s.expr, ctx)),
            TypedStmt::If(s) => {
                union(&mut row, effects_of_expr(&s.condition, ctx));
                union(&mut row, effects_of_stmts(&s.then_branch.statements, ctx));
                union(&mut row, effects_of_stmts(&s.else_branch.statements, ctx));
            }
            TypedStmt::While(s) => {
                union(&mut row, effects_of_expr(&s.condition, ctx));
                union(&mut row, effects_of_stmts(&s.body.statements, ctx));
            }
            TypedStmt::ForIn(s) => {
                union(&mut row, effects_of_expr(&s.iterable, ctx));
                union(&mut row, effects_of_stmts(&s.body, ctx));
            }
            TypedStmt::ForRange(s) => {
                union(&mut row, effects_of_expr(&s.start, ctx));
                union(&mut row, effects_of_expr(&s.end, ctx));
                union(&mut row, effects_of_stmts(&s.body, ctx));
            }
            TypedStmt::Match(s) => {
                union(&mut row, effects_of_expr(&s.scrutinee, ctx));
                for arm in &s.arms {
                    if let Some(g) = &arm.guard {
                        union(&mut row, effects_of_expr(g, ctx));
                    }
                    union(&mut row, effects_of_stmts(&arm.body.statements, ctx));
                }
            }
            TypedStmt::Return(s) => {
                if let Some(v) = &s.value {
                    union(&mut row, effects_of_expr(v, ctx));
                }
            }
            // break/continue invoke nothing — no effects.
            TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
        }
    }
    row
}

fn effects_of_expr(expr: &TypedExpr, ctx: &EffectInferCtx<'_>) -> EffectSet {
    let mut row = EffectSet::empty();
    match &expr.kind {
        TypedExprKind::Call(call) => {
            for arg in &call.args {
                union(&mut row, effects_of_expr(arg, ctx));
            }
            match ctx.callee_row(&call.callee) {
                Some(callee_row) => union(&mut row, callee_row),
                // FAIL CLOSED: an unresolvable callee contributes the enclosing
                // function's declared row — the pre-Phase-1 over-approximation —
                // rather than nothing.
                None => union(&mut row, ctx.fallback.clone()),
            }
        }
        TypedExprKind::Intrinsic(intrinsic) => {
            for arg in &intrinsic.args {
                union(&mut row, effects_of_expr(arg, ctx));
            }
            if matches!(intrinsic.kind, TypedIntrinsicKind::Alloc)
                && let Some(alloc_id) = ctx.effect_registry.lookup("Alloc")
            {
                row.effects.insert(alloc_id);
            }
        }
        TypedExprKind::Binary(b) => {
            union(&mut row, effects_of_expr(&b.lhs, ctx));
            union(&mut row, effects_of_expr(&b.rhs, ctx));
        }
        TypedExprKind::Borrow(b) => union(&mut row, effects_of_expr(&b.inner, ctx)),
        TypedExprKind::Grant(g) => {
            union(&mut row, effects_of_expr(&g.cap, ctx));
            union(&mut row, effects_of_expr(&g.body, ctx));
        }
        TypedExprKind::Declassify(d) => {
            union(&mut row, effects_of_expr(&d.value, ctx));
            union(&mut row, effects_of_expr(&d.cap, ctx));
        }
        TypedExprKind::DeclassifyCt(d) => {
            union(&mut row, effects_of_expr(&d.value, ctx));
            union(&mut row, effects_of_expr(&d.cap, ctx));
        }
        TypedExprKind::Handle(h) => {
            // The dual of the checker's EXPANSION: the body's row, minus what this
            // handler discharges. An unregistered name discharges nothing (silent-
            // drop parity with resolve_effect_row).
            let mut body_row = effects_of_stmts(&h.body.statements, ctx);
            for eff_name in &h.effects {
                if let Some(eff_id) = ctx.effect_registry.lookup(eff_name) {
                    body_row.effects.remove(&eff_id);
                }
            }
            union(&mut row, body_row);
        }
        TypedExprKind::Perform(p) => {
            // A `perform E.op` charges E — the row half of the E010 obligation.
            if let Some(eff_id) = ctx.effect_registry.lookup(&p.effect) {
                row.effects.insert(eff_id);
            }
            for arg in &p.args {
                union(&mut row, effects_of_expr(arg, ctx));
            }
        }
        TypedExprKind::ClauseHandle(c) => {
            // Scrutinee effects minus the discharged clauses; clause BODIES run in
            // the surrounding context and keep their full row.
            let mut scrutinee_row = effects_of_expr(&c.scrutinee, ctx);
            for clause in &c.clauses {
                if let Some(eff_id) = ctx.effect_registry.lookup(&clause.effect) {
                    scrutinee_row.effects.remove(&eff_id);
                }
            }
            union(&mut row, scrutinee_row);
            for clause in &c.clauses {
                union(&mut row, effects_of_stmts(&clause.body.statements, ctx));
            }
        }
        TypedExprKind::Resume(r) => union(&mut row, effects_of_expr(&r.value, ctx)),
        TypedExprKind::ArrayLit(a) => {
            for elem in &a.elements {
                union(&mut row, effects_of_expr(elem, ctx));
            }
        }
        TypedExprKind::FString(fs) => {
            for part in &fs.parts {
                if let TypedFStringPart::Hole(h) = part {
                    union(&mut row, effects_of_expr(h, ctx));
                }
            }
        }
        TypedExprKind::Index(i) => {
            union(&mut row, effects_of_expr(&i.array, ctx));
            union(&mut row, effects_of_expr(&i.index, ctx));
        }
        TypedExprKind::Slice(s) => {
            union(&mut row, effects_of_expr(&s.array, ctx));
            if let Some(start) = &s.start {
                union(&mut row, effects_of_expr(start, ctx));
            }
            if let Some(end) = &s.end {
                union(&mut row, effects_of_expr(end, ctx));
            }
        }
        TypedExprKind::RecordConstruct(r) => {
            for (_, field) in &r.fields {
                union(&mut row, effects_of_expr(field, ctx));
            }
        }
        TypedExprKind::FieldAccess(f) => union(&mut row, effects_of_expr(&f.object, ctx)),
        TypedExprKind::EnumConstruct(e) => {
            for field in &e.fields {
                union(&mut row, effects_of_expr(field, ctx));
            }
        }
        // ET-EFF-1 parity: externs are NOT charged; only their args are walked.
        TypedExprKind::ExternCall(ext) => {
            for arg in &ext.args {
                union(&mut row, effects_of_expr(arg, ctx));
            }
        }
        TypedExprKind::Region(r) => {
            union(&mut row, effects_of_expr(&r.limit, ctx));
            union(&mut row, effects_of_stmts(&r.body.statements, ctx));
        }
        TypedExprKind::ResultCtor(r) => union(&mut row, effects_of_expr(&r.value, ctx)),
        TypedExprKind::Try(t) => union(&mut row, effects_of_expr(&t.value, ctx)),
        TypedExprKind::Send(s) => {
            for arg in &s.args {
                union(&mut row, effects_of_expr(arg, ctx));
            }
        }
        TypedExprKind::Ask(a) => {
            for arg in &a.args {
                union(&mut row, effects_of_expr(arg, ctx));
            }
            union(&mut row, effects_of_expr(&a.timeout, ctx));
        }
        TypedExprKind::Spawn(s) => {
            for arg in &s.args {
                union(&mut row, effects_of_expr(arg, ctx));
            }
        }
        TypedExprKind::IndirectCall(call) => {
            for arg in &call.args {
                union(&mut row, effects_of_expr(arg, ctx));
            }
            // Application discharges the callee's LATENT row into this one —
            // λ-SIGIL's app rule.
            if let crate::type_check::Type::Fn(_, _, _, latent) = &call.callee_ty {
                union(&mut row, latent.clone());
            } else {
                // FAIL CLOSED: a non-Fn indirect callee cannot happen after
                // type-check, but if it ever does, charge the enclosing row
                // rather than nothing (the checker's arm errors on this shape).
                union(&mut row, ctx.fallback.clone());
            }
        }
        TypedExprKind::Mint(m) => union(&mut row, effects_of_expr(&m.target, ctx)),
        // Leaves. `ClosureConstruct` deliberately contributes nothing:
        // construction is pure (λ-SIGIL's `lam`); the inner closure's row rides
        // its own `Type::Fn` and joins this row only if the body APPLIES it.
        TypedExprKind::Literal(_)
        | TypedExprKind::Local(_)
        | TypedExprKind::StateField(_)
        | TypedExprKind::ClosureConstruct(_)
        | TypedExprKind::CapRestrict(_)
        | TypedExprKind::CapSplit(_)
        | TypedExprKind::CapDraw(_) => {}
    }
    row
}

fn union(into: &mut EffectSet, from: EffectSet) {
    into.effects.extend(from.effects);
}
