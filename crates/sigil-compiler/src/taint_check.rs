//! Taint checker pass — static information flow tracking.
//!
//! Prevents `@Secret` data from reaching `@Public` sinks without
//! explicit declassification via a consumed `Declassify` capability.
//!
//! Three-level lattice: `Public < Internal < Secret`.
//! - Value flow: `lub(@Secret, @Public) → @Secret` at every operation
//! - Implicit flow: pc-taint stack for control-dependence
//! - Sink checking: grant returns, function returns reject tainted data

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};

use crate::span::Span;

use crate::{
    ast::TaintLabel,
    diagnostics::{Diagnostic, codes},
    type_check::{
        TypedBlock, TypedExpr, TypedExprKind, TypedFunction, TypedIntrinsicKind, TypedProgram,
        TypedStmt,
    },
};

/// Per-variable taint binding — scalar or per-field for records.
#[derive(Debug, Clone, PartialEq)]
enum TaintBinding {
    Scalar(TaintLabel),
    Record(HashMap<String, TaintLabel>),
}

impl TaintBinding {
    fn label(&self) -> TaintLabel {
        match self {
            TaintBinding::Scalar(t) => *t,
            TaintBinding::Record(fields) => fields
                .values()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub),
        }
    }
}

#[derive(Clone)]
struct TaintEnv {
    bindings: HashMap<String, TaintBinding>,
    pc_taint: TaintLabel,
    /// Taint of reaching the current continuation after a control-dependent early exit. Unlike
    /// `pc_taint`, which is scoped to a branch/arm/loop body, this survives for the remainder of
    /// the enclosing block. Example: after `if secret { break }`, statements on the fall-through
    /// path are control-dependent on `secret` even though the lexical `if` body has ended.
    continuation_taint: TaintLabel,
    /// Taint env captured at each `break` / `continue` reachable in the CURRENT loop (task #252,
    /// root cause 1). A `break` jumps to the loop EXIT and a `continue` to the loop HEAD, so those
    /// envs must be joined into the post-loop / loop-head state — otherwise a secret captured then
    /// `break`/`continue`d is lost when the checker keeps applying the statements the exit skipped.
    /// A loop installs fresh (empty) collectors so nested loops each own their own break/continue.
    break_envs: Vec<HashMap<String, TaintBinding>>,
    continue_envs: Vec<HashMap<String, TaintBinding>>,
    /// Set by `break` / `continue` / `return`: the rest of the enclosing block is UNREACHABLE, so
    /// `check_block`/`check_stmts` stop. Otherwise the checker would apply the (taint-lowering)
    /// strong updates of code the early exit skips, and a leak would vanish. Reset per branch / arm
    /// / loop-body by the construct that owns the control flow.
    diverged: bool,
    // M6 — region-based memory taint (intra-procedural alias analysis).
    // Each `alloc` is a fresh region; a pointer local carries its source's
    // region (`let q = out` / `let q = out + i` copy the region);
    // `store8(p, secret)` taints p's REGION; and `lookup` folds the
    // region's CURRENT taint into every read. So a pointer aliased BEFORE
    // a secret store still sees the taint (the M5b gap), while rebinding a
    // pointer to a fresh alloc correctly drops the old region (no false
    // positive). Holes documented as the next boundary: pointers stored
    // through memory and reloaded, and interprocedural aliasing.
    region_of: HashMap<String, u32>,
    region_taint: HashMap<u32, TaintLabel>,
    next_region: u32,
}

impl TaintEnv {
    fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            pc_taint: TaintLabel::Public,
            continuation_taint: TaintLabel::Public,
            break_envs: Vec::new(),
            continue_envs: Vec::new(),
            diverged: false,
            region_of: HashMap::new(),
            region_taint: HashMap::new(),
            next_region: 0,
        }
    }

    fn lookup(&self, name: &str) -> TaintLabel {
        let value = self
            .bindings
            .get(name)
            .map(|b| b.label())
            .unwrap_or(TaintLabel::Public);
        // M6 — fold the pointed-to region's current taint. This is what
        // makes an alias see a secret stored through a sibling pointer.
        let region = self
            .region_of
            .get(name)
            .and_then(|r| self.region_taint.get(r))
            .copied()
            .unwrap_or(TaintLabel::Public);
        value.lub(region)
    }

    /// Mint a fresh region id for an `alloc` site.
    fn fresh_region(&mut self) -> u32 {
        let r = self.next_region;
        self.next_region += 1;
        r
    }

    /// Record (or clear) the region a local points into. Clearing on a
    /// non-pointer rebind is essential — otherwise a reused name keeps a
    /// stale region and a later store would taint the wrong value.
    fn set_region(&mut self, name: &str, region: Option<u32>) {
        match region {
            Some(r) => {
                self.region_of.insert(name.to_owned(), r);
            }
            None => {
                self.region_of.remove(name);
            }
        }
    }

    /// Raise a region's taint (a store of a tainted value into it).
    fn taint_region(&mut self, region: u32, taint: TaintLabel) {
        let slot = self
            .region_taint
            .entry(region)
            .or_insert(TaintLabel::Public);
        *slot = slot.lub(taint);
    }

    /// The region a pointer expression points into: a local's region, or
    /// the base local's region through `+`/`-` address arithmetic. `None`
    /// for a fresh `alloc` (the caller mints one) or an untracked pointer.
    fn region_of_expr(&self, expr: &crate::typed_ast::TypedExpr) -> Option<u32> {
        match &expr.kind {
            crate::typed_ast::TypedExprKind::Local(name) => self.region_of.get(name).copied(),
            crate::typed_ast::TypedExprKind::Binary(b)
                if matches!(b.op, crate::ast::BinaryOp::Add | crate::ast::BinaryOp::Sub) =>
            {
                self.region_of_expr(&b.lhs)
                    .or_else(|| self.region_of_expr(&b.rhs))
            }
            _ => None,
        }
    }

    fn lookup_field(&self, name: &str, field: &str) -> TaintLabel {
        match self.bindings.get(name) {
            Some(TaintBinding::Record(fields)) => {
                fields.get(field).copied().unwrap_or(TaintLabel::Public)
            }
            Some(TaintBinding::Scalar(t)) => *t,
            None => TaintLabel::Public,
        }
    }

    fn bind(&mut self, name: &str, taint: TaintLabel) {
        self.bindings
            .insert(name.to_owned(), TaintBinding::Scalar(taint));
    }

    fn bind_record(&mut self, name: &str, fields: HashMap<String, TaintLabel>) {
        self.bindings
            .insert(name.to_owned(), TaintBinding::Record(fields));
    }

    fn effective_pc(&self) -> TaintLabel {
        self.pc_taint.lub(self.continuation_taint)
    }

    fn child_scope(&self) -> Self {
        Self {
            bindings: self.bindings.clone(),
            pc_taint: self.pc_taint,
            continuation_taint: self.continuation_taint,
            break_envs: Vec::new(),
            continue_envs: Vec::new(),
            diverged: false,
            // M6 regions are FUNCTION-scoped, not block-scoped: a pointer bound
            // outside a branch keeps its region (and that region's accumulated
            // taint) inside, so a child scope inherits all three. `next_region`
            // carries forward so a fresh `alloc` in the child cannot collide
            // with a region the parent already minted.
            region_of: self.region_of.clone(),
            region_taint: self.region_taint.clone(),
            next_region: self.next_region,
        }
    }
}

/// Join a per-variable binding across two control-flow paths — the least upper bound, so a taint
/// present on EITHER path is preserved at the merge and can never be lowered by the other path
/// (SC-T1). Records join field-by-field; a field absent on one side takes that side's overall
/// label as a sound floor.
fn join_binding(a: &TaintBinding, b: &TaintBinding) -> TaintBinding {
    match (a, b) {
        (TaintBinding::Record(fa), TaintBinding::Record(fb)) => {
            let mut out = HashMap::new();
            for k in fa.keys().chain(fb.keys()) {
                let la = fa.get(k).copied().unwrap_or_else(|| a.label());
                let lb = fb.get(k).copied().unwrap_or_else(|| b.label());
                out.insert(k.clone(), la.lub(lb));
            }
            TaintBinding::Record(out)
        }
        _ => TaintBinding::Scalar(a.label().lub(b.label())),
    }
}

/// Replace `env.bindings` with the join of several branch-result maps, keeping ONLY names that
/// existed in `pre` (bindings introduced inside a branch do not escape it — SC-T2). Each surviving
/// name's taint is the lub over every branch; a branch that never rebound the name contributes its
/// pre-branch value. `branches` must be non-empty.
fn merge_branch_bindings(
    env: &mut TaintEnv,
    pre: &HashMap<String, TaintBinding>,
    branches: &[HashMap<String, TaintBinding>],
) {
    let mut merged = HashMap::with_capacity(pre.len());
    for (name, pre_b) in pre {
        let mut acc = branches[0].get(name).unwrap_or(pre_b).clone();
        for br in &branches[1..] {
            acc = join_binding(&acc, br.get(name).unwrap_or(pre_b));
        }
        merged.insert(name.clone(), acc);
    }
    env.bindings = merged;
}

/// Join `pre`, `base`, and every env in `others` (all restricted to `pre`'s names, SC-T2), returning
/// the lub. `pre` is ALWAYS a floor: for the fixpoint it is the zero-iteration path (the loop body
/// may not run, so the pre-loop state survives — SC-T3); for the break-join `head ⊒ pre` already, so
/// flooring is a harmless no-op there. A name missing from an env contributes its `pre` value.
fn join_envs_into(
    base: &HashMap<String, TaintBinding>,
    others: &[HashMap<String, TaintBinding>],
    pre: &HashMap<String, TaintBinding>,
) -> HashMap<String, TaintBinding> {
    let mut out = HashMap::with_capacity(pre.len());
    for (name, pre_b) in pre {
        let mut acc = join_binding(pre_b, base.get(name).unwrap_or(pre_b));
        for o in others {
            acc = join_binding(&acc, o.get(name).unwrap_or(pre_b));
        }
        out.insert(name.clone(), acc);
    }
    out
}

fn apply_restore(map: &mut HashMap<String, TaintBinding>, name: &str, old: &Option<TaintBinding>) {
    match old {
        Some(b) => {
            map.insert(name.to_owned(), b.clone());
        }
        None => {
            map.remove(name);
        }
    }
}

/// Restore the outer bindings for names a block lexically shadowed (task #252, root cause 3). A
/// `let x` inside a block shadows any outer `x` and is dropped at block end; because `TaintEnv` is
/// one flat map with no scope stack, the shadow overwrites the outer entry, so a merge would keep
/// the (higher) shadow taint and reject a safe program. Restoring the captured outer value —
/// `Some(b)` for a shadow, `None` for a genuinely new name that must be removed — fixes that.
///
/// The restore also applies to any `break`/`continue` envs CAPTURED DURING this block (the slices
/// from `break_base`/`continue_base`): a shadow is out of scope at the loop exit / head those envs
/// flow to, so the value they carry for a shadowed name must be the OUTER binding, not the shadow.
/// Without this a `while c { y = 0; let y = s; break; }` captures the inner `y = s` and false-rejects
/// on the outer (public) `y`.
fn restore_shadowed(
    env: &mut TaintEnv,
    shadowed: Vec<(String, Option<TaintBinding>)>,
    break_base: usize,
    continue_base: usize,
) {
    for (name, old) in shadowed.into_iter().rev() {
        apply_restore(&mut env.bindings, &name, &old);
        for be in env.break_envs[break_base..].iter_mut() {
            apply_restore(be, &name, &old);
        }
        for ce in env.continue_envs[continue_base..].iter_mut() {
            apply_restore(ce, &name, &old);
        }
    }
}

/// The names a pattern binds (for restoring an arm-scoped pattern binding that collides with an
/// outer variable — task #252, root cause 3). Mirrors `bind_pattern_taint`.
fn pattern_bound_names(pattern: &crate::type_check::TypedPattern) -> Vec<String> {
    use crate::type_check::TypedPattern;
    let mut out = Vec::new();
    match pattern {
        TypedPattern::Binding(name) => out.push(name.clone()),
        TypedPattern::EnumVariant { bindings, .. } => {
            for (name, _) in bindings {
                out.push(name.clone());
            }
        }
        TypedPattern::Array {
            elem_binds, rest, ..
        } => {
            for (name, _) in elem_binds {
                if let Some(name) = name {
                    out.push(name.clone());
                }
            }
            if let Some((Some(rest_name), _)) = rest {
                out.push(rest_name.clone());
            }
        }
        TypedPattern::Literal(_) | TypedPattern::Range { .. } | TypedPattern::Wildcard => {}
    }
    out
}

/// Bounded fixpoint for a loop's control-flow join (SC-T3, X-T2). A loop body may run ZERO times, so
/// the state after the loop is the least fixpoint of `I = pre ⊔ body(I) ⊔ continue-paths(I)`: the
/// LUB of the pre-loop (zero-iteration) state, the fall-through effect of every iteration, and the
/// state at each `continue` (which jumps back to the head). The taint lattice is finite, so this
/// converges (for all-@Public code — the whole compiler — the first pass already converges).
///
/// Diagnostics are SUPPRESSED here (a throwaway sink): the body is re-run to propagate second-order
/// taint (`x = y; y = secret` needs a second pass before `x` is seen as secret), and emitting each
/// pass's diagnostics would duplicate them. The CALLER runs one real diagnostic pass from the
/// returned fixpoint head — the soundest point, since every taint that can reach the body across
/// iterations is present there — and separately folds in the `break` paths for the loop EXIT.
///
/// `run_body` runs the loop body against a scratch env (binding the loop variable and, for `while`,
/// re-deriving the guard's pc-taint from the current head). Only names present in `pre` survive into
/// the returned map — loop-body-local names do not escape (SC-T2). The bound is sized to the binding
/// count: each non-converging pass raises ≥1 binding by ≥1 lattice level and there are ≤ `pre.len()`
/// bindings, so `pre.len() * 4 + 4` passes always suffice (a copy chain of length N needs ~N). It
/// fails LOUD in debug and CLOSED in release (top-taint) if convergence is somehow not reached.
fn loop_fixpoint(
    pre: &HashMap<String, TaintBinding>,
    pc_taint: TaintLabel,
    continuation_taint: TaintLabel,
    mut run_body: impl FnMut(&mut TaintEnv, &mut Vec<Diagnostic>),
) -> HashMap<String, TaintBinding> {
    let max_iters = pre.len().saturating_mul(4) + 4;
    let mut head = pre.clone();
    let mut sink = Vec::new();
    for _ in 0..max_iters {
        let mut env = TaintEnv::new();
        env.bindings = head.clone();
        env.pc_taint = pc_taint;
        env.continuation_taint = continuation_taint;
        run_body(&mut env, &mut sink);
        // I' = pre ⊔ fall-through(I) ⊔ (⊔ continue paths), restricted to pre's names (SC-T2). The
        // join with `pre` (never dropped) is the zero-iteration path (SC-T3); the continue paths are
        // the iterations that jumped back to the head early via `continue`.
        let next = join_envs_into(&env.bindings, &env.continue_envs, pre);
        if next == head {
            return next;
        }
        head = next;
    }
    // Unreachable given the size-scaled bound; a hit means a monotonicity bug. Fail LOUD in debug,
    // and fail CLOSED in release: top-taint every pre name so nothing is under-tainted (X-T2).
    debug_assert!(
        false,
        "taint loop fixpoint did not converge within {max_iters} iterations"
    );
    pre.keys()
        .map(|k| (k.clone(), TaintBinding::Scalar(TaintLabel::Secret)))
        .collect()
}

/// One call site to a taint-polymorphic (`@Flow`) callee, keyed by the checking context
/// and the call expression's span. The context is the `@Flow` function instance whose body
/// was being checked (`None` for ordinary functions), so a closure body checked inside an
/// instantiation records under that instantiation.
pub type FlowCallSite = (Option<(String, TaintLabel)>, (usize, usize, u32));

/// The instantiation label every `@Flow` call site resolved to during the per-label body
/// checks: the join of all argument taints, exactly the label the call's result carries.
/// `formal.rs` projects one concrete instance of the callee per label that actually occurs,
/// so the Lean kernel checks the same instantiations the type checker did; a site that is
/// absent here falls back to the `@Secret`-seeded original, which can only over-taint.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FlowCallInstantiations {
    pub sites: BTreeMap<FlowCallSite, TaintLabel>,
}

impl FlowCallInstantiations {
    /// The recorded instantiation for a call at `span` checked under `context`.
    pub fn label(&self, context: Option<(&str, TaintLabel)>, span: Span) -> Option<TaintLabel> {
        let key = (
            context.map(|(name, label)| (name.to_owned(), label)),
            (span.start, span.end, span.source.0),
        );
        self.sites.get(&key).copied()
    }
}

struct FlowRecorder {
    context: Option<(String, TaintLabel)>,
    sites: BTreeMap<FlowCallSite, TaintLabel>,
}

thread_local! {
    /// Active only inside `flow_call_instantiations`; `None` during ordinary checking, so the
    /// diagnostic pass never pays for or depends on recording.
    static FLOW_RECORDER: RefCell<Option<FlowRecorder>> = const { RefCell::new(None) };
}

fn set_flow_context(context: Option<(String, TaintLabel)>) {
    FLOW_RECORDER.with(|recorder| {
        if let Some(recorder) = recorder.borrow_mut().as_mut() {
            recorder.context = context;
        }
    });
}

fn record_flow_call(span: Span, label: TaintLabel) {
    FLOW_RECORDER.with(|recorder| {
        if let Some(recorder) = recorder.borrow_mut().as_mut() {
            let key = (
                recorder.context.clone(),
                (span.start, span.end, span.source.0),
            );
            recorder
                .sites
                .entry(key)
                .and_modify(|existing| *existing = existing.lub(label))
                .or_insert(label);
        }
    });
}

/// Re-run the per-instantiation checks with the call-site recorder armed and return every
/// `@Flow` call site's instantiation label. Diagnostics are discarded: the caller has already
/// run `check_taints`, and a program that fails it never reaches the formal projection.
pub fn flow_call_instantiations(program: &TypedProgram) -> FlowCallInstantiations {
    FLOW_RECORDER.with(|recorder| {
        *recorder.borrow_mut() = Some(FlowRecorder {
            context: None,
            sites: BTreeMap::new(),
        });
    });
    let mut diagnostics = Vec::new();
    for module in &program.modules {
        for function in &module.functions {
            if matches!(function.kind, crate::typed_ast::TypedFunctionKind::Closure) {
                continue;
            }
            check_function(function, program, &mut diagnostics);
        }
    }
    let sites = FLOW_RECORDER.with(|recorder| {
        recorder
            .borrow_mut()
            .take()
            .map(|recorder| recorder.sites)
            .unwrap_or_default()
    });
    FlowCallInstantiations { sites }
}

pub fn check_taints(program: &TypedProgram) -> Result<(), Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();

    for module in &program.modules {
        for function in &module.functions {
            // Closures are checked at their construct site (see
            // `TypedExprKind::ClosureConstruct` in `compute_expr_taint`)
            // with their capture taints propagated from the enclosing
            // scope (spec §3.7, E4). Skipping them here avoids a
            // double-check with all-@Public captures that would miss
            // CT violations inside closure bodies.
            if matches!(function.kind, crate::typed_ast::TypedFunctionKind::Closure) {
                continue;
            }
            check_function(function, program, &mut diagnostics);
        }
    }

    if diagnostics.is_empty() {
        Ok(())
    } else {
        Err(diagnostics)
    }
}

/// The labels a `@Flow` signature quantifies over. `@SecretCT` is deliberately
/// absent: constant-time is a property of the CODE (branching, indexing, and
/// allocation are all restricted under it), so one body cannot satisfy both the
/// CT and non-CT disciplines. A `@SecretCT` argument to a `@Flow` parameter is
/// rejected at the call site (T030) rather than silently checked as `@Secret`.
const FLOW_INSTANTIATIONS: [TaintLabel; 3] =
    [TaintLabel::Public, TaintLabel::Internal, TaintLabel::Secret];

fn check_function(
    function: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Taint polymorphism: a `@Flow` signature promises the body is safe at EVERY
    // admissible label, so check it once per label with the `@Flow` positions
    // (parameters and, if declared, the return) instantiated to that label. This
    // is what earns the right to skip the parameter check at call sites — a body
    // that laundered a `@Flow` value into a `@Public` sink passes the `@Public`
    // instantiation but fails at `@Internal`.
    //
    // Only the FIRST failing instantiation is reported: a genuine leak fails at
    // every label, and emitting it three times would bury the signal. The label
    // is named in the message so the failing instantiation is never a guess.
    if function.ret_flow || function.params.iter().any(|p| p.flow) {
        for label in FLOW_INSTANTIATIONS {
            let mut instance = function.clone();
            for param in &mut instance.params {
                if param.flow {
                    param.taint = label;
                }
            }
            if instance.ret_flow {
                instance.ret_taint = label;
            }

            let mut instance_diagnostics = Vec::new();
            set_flow_context(Some((function.name.clone(), label)));
            check_function_body(&instance, program, &mut instance_diagnostics);
            set_flow_context(None);
            if !instance_diagnostics.is_empty() {
                diagnostics.extend(instance_diagnostics.into_iter().map(|d| {
                    d.with_message_prefix(format!(
                        "in the @{label:?} instantiation of taint-polymorphic `{}`: ",
                        function.name
                    ))
                }));
                return;
            }
        }
        return;
    }

    check_function_body(function, program, diagnostics);
}

fn check_function_body(
    function: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut env = TaintEnv::new();

    // Bind parameters with their declared taints
    for param in &function.params {
        env.bind(&param.name, param.taint);
    }
    // Bind captures
    for cap in &function.captures {
        env.bind(&cap.name, cap.taint);
    }

    check_block(&function.body, &mut env, function, program, diagnostics);
}

fn check_block(
    block: &TypedBlock,
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<TaintLabel> {
    check_stmt_seq(&block.statements, env, current_fn, program, diagnostics)
}

/// Walk a statement sequence (a block body or a for-loop body) with two soundness rules from task
/// #252: STOP at the first diverging statement (`break`/`continue`/`return` make the rest of the
/// sequence unreachable, so their taint-lowering strong updates must not be applied on the exit
/// path — root cause 1), and RESTORE any name a `let` here shadowed to its outer binding on exit
/// (a shadow is lexically scoped and must not corrupt the outer variable at a merge — root cause 3).
fn check_stmt_seq(
    stmts: &[TypedStmt],
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<TaintLabel> {
    let break_base = env.break_envs.len();
    let continue_base = env.continue_envs.len();
    let mut shadowed: Vec<(String, Option<TaintBinding>)> = Vec::new();
    let mut tail_taint = None;
    for (index, stmt) in stmts.iter().enumerate() {
        if env.diverged {
            break;
        }
        if let TypedStmt::Let(s) = stmt
            && !shadowed.iter().any(|(n, _)| n == &s.name)
        {
            shadowed.push((s.name.clone(), env.bindings.get(&s.name).cloned()));
        }
        if let TypedStmt::Expr(s) = stmt {
            let expr_taint = compute_expr_taint(&s.expr, env, current_fn, program, diagnostics);
            // M5b/M6 — storing a tainted value through a pointer taints the
            // pointer's REGION (its `alloc` site). `lookup` folds region taint
            // into every read, so `store8(out, secret); return out` AND
            // `let q = out; store8(out, secret); return q` (the alias) both
            // surface the secret at the return → T001. Region-based so
            // rebinding `out` to a fresh alloc drops the old region (no false
            // positive). Boundary: a pointer round-tripped through memory, or
            // across a call, loses its region — the next gap.
            //
            // Lives HERE (not in `check_stmt`) because task #252 relocated
            // expression-statement handling into this sequence walker; the
            // `check_stmt` arm is now `unreachable!`.
            if let TypedExprKind::Intrinsic(intr) = &s.expr.kind
                && matches!(intr.kind, TypedIntrinsicKind::Store8)
                && intr.args.len() == 2
            {
                // Recompute the value taint into a throwaway sink so we do not
                // double-report any diagnostics from arg1's subtree.
                let mut sink = Vec::new();
                let val_taint =
                    compute_expr_taint(&intr.args[1], env, current_fn, program, &mut sink);
                if val_taint > TaintLabel::Public
                    && let Some(region) = env.region_of_expr(&intr.args[0])
                {
                    env.taint_region(region, val_taint);
                }
            }
            if index + 1 == stmts.len() {
                tail_taint = Some(expr_taint);
            }
        } else {
            check_stmt(stmt, env, current_fn, program, diagnostics);
        }
    }
    restore_shadowed(env, shadowed, break_base, continue_base);
    tail_taint
}

fn check_stmt(
    stmt: &TypedStmt,
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match stmt {
        TypedStmt::Let(s) => {
            let expr_taint = compute_expr_taint(&s.value, env, current_fn, program, diagnostics);
            // An unannotated `let` is a @Public DECLARATION in a monomorphic
            // function — that is what makes `let x = <@Internal>;` an error
            // rather than a silent absorb. A taint-POLYMORPHIC body has no
            // fixed label for that default to mean: the same statement is
            // checked at @Public, @Internal and @Secret, and its locals hold
            // whatever the caller's data was. So there, an unannotated local
            // INFERS (binds at `effective` below, which already includes
            // `expr_taint`) and only an explicitly written `@Label` is a sink.
            //
            // This narrows where the early check applies; it does not weaken
            // the guarantee. The local still carries the initializer's taint,
            // so every real sink downstream — the function's own return, an
            // argument to a non-`@Flow` parameter, a store, a grant — still
            // fires. A polymorphic body that leaks is caught there.
            let is_polymorphic = current_fn.ret_flow || current_fn.params.iter().any(|p| p.flow);
            let declared = match s.taint {
                Some(explicit) => explicit,
                None if is_polymorphic => expr_taint,
                None => TaintLabel::Public,
            };

            // CT016 (T030) — source-of-CT (E1): assigning into a @SecretCT
            // binding from @Internal or @Secret is forbidden. Only @Public
            // and @SecretCT sources are permitted in @SecretCT typing position.
            // @Public→@SecretCT is allowed (literals, constants, masks).
            if declared.is_ct()
                && (expr_taint == TaintLabel::Internal || expr_taint == TaintLabel::Secret)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T030,
                    format!(
                        "cannot upcast @{:?} value to @SecretCT binding; source must be @Public or @SecretCT (T030 / CT016)",
                        expr_taint
                    ),
                    Some(s.span),
                ));
            }

            // Check for downgrade violation
            if !expr_taint.can_flow_to(declared) {
                diagnostics.push(Diagnostic::error(
                    codes::T001,
                    format!(
                        "cannot assign @{:?} value to @{:?} binding without declassification (T001)",
                        expr_taint, declared
                    ),
                    Some(s.span),
                ));
            }

            // Bind at effective taint (max of declared and computed)
            let effective = expr_taint.lub(declared).lub(env.effective_pc());
            // Check if value is a record construct — track per-field
            if let TypedExprKind::RecordConstruct(r) = &s.value.kind {
                let mut field_taints = HashMap::new();
                for (fname, fexpr) in &r.fields {
                    let ft = compute_expr_taint(fexpr, env, current_fn, program, diagnostics)
                        .lub(env.effective_pc());
                    field_taints.insert(fname.clone(), ft);
                }
                env.bind_record(&s.name, field_taints);
            } else {
                env.bind(&s.name, effective);
            }
            // M6 — region assignment: a fresh alloc mints a region; a
            // pointer derived from another local inherits its region;
            // anything else clears it (a reused name must not keep a stale
            // region, or a later store would taint the wrong value).
            let region = if is_alloc_expr(&s.value) {
                Some(env.fresh_region())
            } else {
                env.region_of_expr(&s.value)
            };
            env.set_region(&s.name, region);
        }
        TypedStmt::Assign(s) => {
            let expr_taint = compute_expr_taint(&s.value, env, current_fn, program, diagnostics);
            let effective = expr_taint.lub(env.effective_pc());
            // Propagate the assigned taint to the place. A bare local is
            // rebound (flow-sensitive overwrite, as before); a field/index
            // place raises its root container's taint — a sound
            // over-approximation that never under-taints a secret written
            // into an aggregate.
            match &s.place.kind {
                crate::typed_ast::TypedExprKind::Local(name) => {
                    env.bind(name, effective);
                    // M6 — rebinding a pointer local updates its region
                    // (this is what makes rebinding to a fresh alloc drop
                    // the old region and avoid a false positive on aliases).
                    let region = if is_alloc_expr(&s.value) {
                        Some(env.fresh_region())
                    } else {
                        env.region_of_expr(&s.value)
                    };
                    env.set_region(name, region);
                }
                // Actor-state (M2) anti-laundering: a state field is a declared
                // taint SINK (captures are bound at their declared label; state
                // fields carry no annotation, so @Public). Handlers read it back
                // at that label, so storing a higher-taint value into it in `init`
                // would launder a secret across the immutable-state boundary
                // (F007's sibling). Sink-check the value against the field's
                // declared taint instead of flow-sensitively rebinding it.
                crate::typed_ast::TypedExprKind::StateField(name) => {
                    let declared = env.lookup(name);
                    if !effective.can_flow_to(declared) {
                        diagnostics.push(Diagnostic::error(
                            codes::T001,
                            format!(
                                "cannot store @{effective:?} value into actor state field \
                                 `{name}` declared @{declared:?} without declassification (T001)"
                            ),
                            Some(s.span),
                        ));
                    }
                }
                _ => {
                    // AGG-4 (aggregate-state taint hardening): a PROJECTED write into a
                    // state aggregate — `d.v = s`, `a[i] = s` (root is a StateField, not a
                    // Local) — is the taint-axis twin of the T123 projected-place gate. The
                    // bare-`StateField` arm above sink-checks a scalar `n = s`; without this,
                    // routing an @Secret through an aggregate field's projection silently
                    // DROPPED the taint (`place_root_local` returns None on a StateField
                    // root), laundering it to @Public on read-back. Root the place to its
                    // StateField and apply the SAME sink. Checked BEFORE the local fallback,
                    // so a projected LOCAL write (`localrec.f = x`) still rebinds.
                    if let Some(root) = place_root_statefield(&s.place) {
                        let declared = env.lookup(root);
                        if !effective.can_flow_to(declared) {
                            diagnostics.push(Diagnostic::error(
                                codes::T001,
                                format!(
                                    "cannot store @{effective:?} value through actor state \
                                     field `{root}` declared @{declared:?} without \
                                     declassification (T001)"
                                ),
                                Some(s.span),
                            ));
                        }
                    } else if let Some(root) = place_root_local(&s.place) {
                        let raised = effective.lub(env.lookup(root));
                        env.bind(root, raised);
                    }
                }
            }
        }
        TypedStmt::Expr(_) => unreachable!("expression statements are handled by check_stmt_seq"),
        TypedStmt::If(s) => {
            // M3: Implicit flow — push condition taint onto pc-taint
            let cond_taint =
                compute_expr_taint(&s.condition, env, current_fn, program, diagnostics);
            // CT001 (T020) — secret-dependent branch. Reject before descent so
            // pc-taint never holds SecretCT (spec §3.6 invariant).
            if cond_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T020,
                    "secret-dependent branch: `if` condition has taint @SecretCT (T020 / CT001)"
                        .to_string(),
                    Some(s.span),
                ));
                return;
            }
            let outer_pc = env.pc_taint;
            let outer_continuation = env.continuation_taint;
            let branch_pc = outer_pc.lub(cond_taint);

            // CONTROL-FLOW JOIN (task #252, docs/specs/taint-join-soundness.md). Previously both
            // branches ran against the SAME env, so the last branch's strong-update relabels won
            // and a secret assigned on one path vanished at the merge:
            //   `if c { x = s } else { x = 0 }` left x @Public — a T001 fail-open.
            // Snapshot, run each branch from the snapshot, and lub the results so a taint on EITHER
            // path survives. An empty `else_branch` (a bare `if`) leaves its map == `pre`, so the
            // not-taken path correctly contributes the pre-if state.
            let pre = env.bindings.clone();
            env.pc_taint = branch_pc;
            env.continuation_taint = outer_continuation;
            env.diverged = false;
            check_block(&s.then_branch, env, current_fn, program, diagnostics);
            let then_div = env.diverged;
            let then_continuation = env.continuation_taint;
            let then_map = std::mem::replace(&mut env.bindings, pre.clone());
            env.pc_taint = branch_pc;
            env.continuation_taint = outer_continuation;
            env.diverged = false;
            check_block(&s.else_branch, env, current_fn, program, diagnostics);
            let else_div = env.diverged;
            let else_continuation = env.continuation_taint;
            let else_map = std::mem::replace(&mut env.bindings, pre.clone());
            // Merge ONLY the branches that fall through to the code after the `if`. A branch that
            // diverges (`return`/`break`/`continue`) does not reach the merge, so its snapshot must
            // NOT be lubbed in — otherwise the common `if c { return err } else { x = <public> }`
            // over-taints x with the diverging branch's stale pre-value (task #252, the divergence
            // false-reject). A break/continue's state is carried by the loop collectors instead.
            let mut fallthrough: Vec<HashMap<String, TaintBinding>> = Vec::with_capacity(2);
            if !then_div {
                fallthrough.push(then_map);
            }
            if !else_div {
                fallthrough.push(else_map);
            }
            if !fallthrough.is_empty() {
                merge_branch_bindings(env, &pre, &fallthrough);
            }

            env.pc_taint = outer_pc;
            // A continuation inherits nested early-exit dependence from every branch that can
            // reach it. If exactly one branch exits, reaching the continuation also reveals the
            // condition itself (the secret-guarded break/continue/return channel).
            let mut continuation = outer_continuation;
            if !then_div {
                continuation = continuation.lub(then_continuation);
            }
            if !else_div {
                continuation = continuation.lub(else_continuation);
            }
            if then_div != else_div {
                continuation = continuation.lub(cond_taint);
            }
            env.continuation_taint = continuation;
            // The `if` diverges (the code after it is unreachable) only if BOTH branches do.
            env.diverged = then_div && else_div;
        }
        TypedStmt::While(s) => {
            let cond_taint =
                compute_expr_taint(&s.condition, env, current_fn, program, diagnostics);
            // CT002 (T021) — secret-dependent loop.
            if cond_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T021,
                    "secret-dependent loop: `while` condition has taint @SecretCT (T021 / CT002)"
                        .to_string(),
                    Some(s.span),
                ));
                return;
            }
            let outer_pc = env.pc_taint;
            let outer_continuation = env.continuation_taint;
            // CONTROL-FLOW JOIN over the ZERO-ITERATION path (task #252, SC-T3). The body may run
            // zero times, so the post-loop state is the fixpoint of `pre ⊔ body ⊔ continue-paths`,
            // then joined with every `break` for the exit. Without this a variable lowered inside the
            // body (`x = 0`) wrongly reads @Public even when the loop never runs and `x` is still
            // @Secret from before the loop — a T001 fail-open.
            let pre = env.bindings.clone();
            // A loop OWNS its break/continue: install fresh collectors so a break/continue inside
            // binds to THIS loop and an enclosing loop's collectors are untouched (root cause 1).
            let outer_breaks = std::mem::take(&mut env.break_envs);
            let outer_continues = std::mem::take(&mut env.continue_envs);
            let head = loop_fixpoint(&pre, outer_pc, outer_continuation, |e, d| {
                // The `while` guard is re-evaluated EVERY iteration, so if a guard variable becomes
                // tainted inside the loop the body is control-dependent on a secret. Re-derive the
                // guard taint from the CURRENT head each pass and fold it into pc (Lens-E implicit
                // flow). `for` loops fix their count at entry, so they snapshot body_pc once instead.
                let ct = compute_expr_taint(&s.condition, e, current_fn, program, d);
                e.pc_taint = outer_pc.lub(ct);
                check_block(&s.body, e, current_fn, program, d);
            });
            // One real diagnostic pass from the fixpoint head — sinks inside the body must see every
            // taint any iteration can bring, and the guard's fixpoint pc-taint. The guard's own
            // diagnostics were already emitted at the top of the arm, so re-derive its taint into a
            // throwaway sink to avoid a duplicate.
            env.bindings = head.clone();
            let mut guard_sink = Vec::new();
            let head_cond =
                compute_expr_taint(&s.condition, env, current_fn, program, &mut guard_sink);
            // The guard may start Public and become SecretCT through a loop-carried assignment.
            // The entry check above cannot see that second-iteration state, so reject from the
            // stabilized loop head before analysing the body for real. Restore the enclosing
            // collectors first so this fail-closed exit cannot corrupt an outer loop's analysis.
            if head_cond.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T021,
                    "secret-dependent loop: `while` condition has taint @SecretCT (T021 / CT002)"
                        .to_string(),
                    Some(s.span),
                ));
                env.bindings = pre;
                env.pc_taint = outer_pc;
                env.continuation_taint = outer_continuation;
                env.break_envs = outer_breaks;
                env.continue_envs = outer_continues;
                env.diverged = false;
                return;
            }
            env.pc_taint = outer_pc.lub(head_cond);
            env.continuation_taint = outer_continuation;
            env.break_envs = Vec::new();
            env.continue_envs = Vec::new();
            env.diverged = false;
            check_block(&s.body, env, current_fn, program, diagnostics);
            // Post-loop state = the loop-head fixpoint ⊔ every `break` env (break jumps to the exit).
            let breaks = std::mem::take(&mut env.break_envs);
            env.bindings = join_envs_into(&head, &breaks, &pre);
            env.pc_taint = outer_pc;
            env.continuation_taint = outer_continuation;
            // Restore the enclosing loop's collectors; a loop itself does not diverge (code after it
            // is reachable — a `break` exits to there).
            env.break_envs = outer_breaks;
            env.continue_envs = outer_continues;
            env.diverged = false;
        }
        TypedStmt::ForIn(s) => {
            let iter_taint = compute_expr_taint(&s.iterable, env, current_fn, program, diagnostics);
            // CT003 (T022) — secret-dependent iteration count.
            if iter_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T022,
                    "secret-dependent iteration: `for` iterable has taint @SecretCT (T022 / CT003)"
                        .to_string(),
                    Some(s.iterable.span),
                ));
                return;
            }
            let outer_pc = env.pc_taint;
            let outer_continuation = env.continuation_taint;
            let body_pc = outer_pc.lub(iter_taint);
            let var_taint = iter_taint.lub(body_pc);
            // CONTROL-FLOW JOIN over the ZERO-ITERATION path (task #252, SC-T3): a `for` over an
            // empty iterable runs the body zero times, so the post-loop state must join the body
            // effect (plus continue/break paths) with the pre-loop state. The loop variable is
            // re-bound each iteration and does not escape (absent from `pre`, so it is dropped —
            // SC-T2). body_pc is fixed for the whole loop: the iteration count is set at entry, so
            // — unlike `while` — the body is NOT control-dependent on a variable that mutates inside.
            let pre = env.bindings.clone();
            let outer_breaks = std::mem::take(&mut env.break_envs);
            let outer_continues = std::mem::take(&mut env.continue_envs);
            let head = loop_fixpoint(&pre, body_pc, outer_continuation, |e, d| {
                e.bind(&s.var, var_taint);
                check_stmts(&s.body, e, current_fn, program, d);
            });
            env.bindings = head.clone();
            env.pc_taint = body_pc;
            env.continuation_taint = outer_continuation;
            env.break_envs = Vec::new();
            env.continue_envs = Vec::new();
            env.diverged = false;
            env.bind(&s.var, var_taint);
            check_stmts(&s.body, env, current_fn, program, diagnostics);
            let breaks = std::mem::take(&mut env.break_envs);
            env.bindings = join_envs_into(&head, &breaks, &pre);
            // The loop variable is scoped to the body: if its name COLLIDES with an outer variable it
            // is a shadow, so restore the outer binding at the loop exit (a non-colliding name is
            // absent from `pre` and already dropped by join_envs_into). Without this,
            // `for x in it { x = s }` over-taints an outer `x` the body never actually writes.
            apply_restore(&mut env.bindings, &s.var, &pre.get(&s.var).cloned());
            env.pc_taint = outer_pc;
            env.continuation_taint = outer_continuation;
            env.break_envs = outer_breaks;
            env.continue_envs = outer_continues;
            env.diverged = false;
        }
        TypedStmt::ForRange(s) => {
            // The bounds ARE the iteration count — the same CT003 (T022) rule as
            // ForIn's iterable applies to `start` ⊔ `end`.
            let start_taint = compute_expr_taint(&s.start, env, current_fn, program, diagnostics);
            let end_taint = compute_expr_taint(&s.end, env, current_fn, program, diagnostics);
            let bound_taint = start_taint.lub(end_taint);
            if bound_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T022,
                    "secret-dependent iteration: `for` range bound has taint @SecretCT (T022 / CT003)"
                        .to_string(),
                    Some(s.span),
                ));
                return;
            }
            let outer_pc = env.pc_taint;
            let outer_continuation = env.continuation_taint;
            let body_pc = outer_pc.lub(bound_taint);
            let var_taint = bound_taint.lub(body_pc);
            // CONTROL-FLOW JOIN over the ZERO-ITERATION path (task #252, SC-T3): a `for i in a..b`
            // with `a >= b` runs zero times, so the post-loop state must join the body (plus
            // continue/break paths) with the pre-loop state. Same shape as `ForIn` (fixed body_pc).
            let pre = env.bindings.clone();
            let outer_breaks = std::mem::take(&mut env.break_envs);
            let outer_continues = std::mem::take(&mut env.continue_envs);
            let head = loop_fixpoint(&pre, body_pc, outer_continuation, |e, d| {
                e.bind(&s.var, var_taint);
                check_stmts(&s.body, e, current_fn, program, d);
            });
            env.bindings = head.clone();
            env.pc_taint = body_pc;
            env.continuation_taint = outer_continuation;
            env.break_envs = Vec::new();
            env.continue_envs = Vec::new();
            env.diverged = false;
            env.bind(&s.var, var_taint);
            check_stmts(&s.body, env, current_fn, program, diagnostics);
            let breaks = std::mem::take(&mut env.break_envs);
            env.bindings = join_envs_into(&head, &breaks, &pre);
            // The range-loop variable is body-scoped: restore an outer binding it shadows (see ForIn).
            apply_restore(&mut env.bindings, &s.var, &pre.get(&s.var).cloned());
            env.pc_taint = outer_pc;
            env.continuation_taint = outer_continuation;
            env.break_envs = outer_breaks;
            env.continue_envs = outer_continues;
            env.diverged = false;
        }
        TypedStmt::Match(s) => {
            let scrutinee_taint =
                compute_expr_taint(&s.scrutinee, env, current_fn, program, diagnostics);
            // CT004 (T023) — secret-dependent dispatch.
            if scrutinee_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T023,
                    "secret-dependent dispatch: `match` scrutinee has taint @SecretCT (T023 / CT004)"
                        .to_string(),
                    Some(s.span),
                ));
                return;
            }
            let outer_pc = env.pc_taint;
            let outer_continuation = env.continuation_taint;
            // Reaching a later guarded arm depends on every earlier guard being false, so the
            // selection pc accumulates guard taints in source order.
            let mut selection_pc = outer_pc.lub(scrutinee_taint);

            // CONTROL-FLOW JOIN across arms (task #252, SC-T4). Previously every arm ran against the
            // SAME env, so the last arm's strong-update relabels won and a secret bound in an earlier
            // arm vanished at the merge. Snapshot, run each arm from the snapshot, and lub the arm
            // results. Match exhaustiveness (T087, verified before taint check) guarantees SOME arm
            // always runs, so — exactly like `If`'s then/else — the merge is the lub over arms with
            // NO separate fall-through (`pre`) path; adding one would over-taint the common
            // `match c { A => x = 0, B => x = 0 }` and wrongly reject it.
            let pre = env.bindings.clone();
            let mut arm_maps: Vec<HashMap<String, TaintBinding>> = Vec::with_capacity(s.arms.len());
            let mut all_diverge = !s.arms.is_empty();
            let mut continuation = outer_continuation;
            let mut divergence_taint = TaintLabel::Public;
            for arm in &s.arms {
                env.bindings = pre.clone();
                env.pc_taint = selection_pc;
                env.continuation_taint = outer_continuation;
                env.diverged = false;
                let break_base = env.break_envs.len();
                let continue_base = env.continue_envs.len();
                // A pattern binding whose name COLLIDES with an outer variable would otherwise
                // overwrite it in the flat env and survive the merge (root cause 3). Restore those
                // names to their outer (`pre`) value after the arm so only genuine assignments to an
                // outer variable are merged; the pattern binding itself is arm-scoped.
                let pat_names = pattern_bound_names(&arm.pattern);
                bind_pattern_taint(&arm.pattern, scrutinee_taint.lub(env.effective_pc()), env);
                if let Some(g) = &arm.guard {
                    let guard_taint = compute_expr_taint(g, env, current_fn, program, diagnostics);
                    // A SecretCT guard is secret-dependent dispatch just like a SecretCT
                    // scrutinee. Reject before descending to avoid a cascade under a CT pc.
                    if guard_taint.is_ct() {
                        diagnostics.push(Diagnostic::error(
                            codes::T023,
                            "secret-dependent dispatch: `match` guard has taint @SecretCT (T023 / CT004)"
                                .to_string(),
                            Some(g.span),
                        ));
                        env.bindings = pre;
                        env.pc_taint = outer_pc;
                        env.continuation_taint = outer_continuation;
                        env.diverged = false;
                        return;
                    }
                    selection_pc = selection_pc.lub(guard_taint);
                    env.pc_taint = selection_pc;
                }
                check_block(&arm.body, env, current_fn, program, diagnostics);
                let arm_div = env.diverged;
                let arm_control = env.effective_pc();
                all_diverge = all_diverge && arm_div;
                // Restore the collided pattern names in env.bindings AND in any break/continue env
                // captured during this arm — a `break`/`continue` inside a colliding-pattern arm
                // captures the arm-scoped (scrutinee-tainted) binding, which is out of scope at the
                // loop exit/head those envs flow to (the same fix `restore_shadowed` applies to
                // `let` shadows; the pattern channel needed it too).
                for n in &pat_names {
                    let old = pre.get(n).cloned();
                    apply_restore(&mut env.bindings, n, &old);
                    for be in env.break_envs[break_base..].iter_mut() {
                        apply_restore(be, n, &old);
                    }
                    for ce in env.continue_envs[continue_base..].iter_mut() {
                        apply_restore(ce, n, &old);
                    }
                }
                let arm_map = std::mem::replace(&mut env.bindings, pre.clone());
                // Only arms that FALL THROUGH reach the code after the match; a diverging arm
                // (`return`/`break`/`continue`) must not be lubbed in, else its stale pre-value
                // over-taints a variable a falling-through arm lowered (the divergence false-reject).
                if !arm_div {
                    arm_maps.push(arm_map);
                    continuation = continuation.lub(env.continuation_taint);
                } else {
                    divergence_taint = divergence_taint.lub(arm_control);
                }
            }
            if !arm_maps.is_empty() {
                merge_branch_bindings(env, &pre, &arm_maps);
            }
            env.pc_taint = outer_pc;
            env.continuation_taint = if all_diverge {
                outer_continuation
            } else {
                continuation.lub(divergence_taint)
            };
            // The match diverges (code after it is unreachable) only if EVERY arm diverges.
            env.diverged = all_diverge;
        }
        TypedStmt::Break(_) => {
            // `break` jumps to the loop EXIT with the current env; capture it for the post-loop join
            // and mark the rest of this block unreachable (task #252, root cause 1).
            let snap = env.bindings.clone();
            env.break_envs.push(snap);
            env.diverged = true;
        }
        TypedStmt::Continue(_) => {
            // `continue` jumps to the loop HEAD with the current env; the fixpoint folds it in.
            let snap = env.bindings.clone();
            env.continue_envs.push(snap);
            env.diverged = true;
        }
        TypedStmt::Return(s) => {
            // M4: Sink checking — return value must satisfy declared ret_taint
            if let Some(v) = &s.value {
                let return_taint = compute_expr_taint(v, env, current_fn, program, diagnostics);
                // Forge tools intentionally bridge @Internal FFI results back to the host
                // via `tool_main`'s packed ptr/len return. Keep Secret->Public blocked,
                // but allow Internal tool output without forcing an explicit capability.
                let declared = current_fn.effective_return_taint();

                // CT016 (T030) — source-of-CT (E1) at return position.
                if declared.is_ct()
                    && (return_taint == TaintLabel::Internal || return_taint == TaintLabel::Secret)
                {
                    diagnostics.push(Diagnostic::error(
                        codes::T030,
                        format!(
                            "cannot return @{:?} value from @SecretCT function; source must be @Public or @SecretCT (T030 / CT016)",
                            return_taint
                        ),
                        Some(s.span),
                    ));
                }

                if !return_taint.can_flow_to(declared) {
                    diagnostics.push(Diagnostic::error(
                        codes::T001,
                        format!(
                            "returning @{:?} value from function declared @{:?} (T001)",
                            return_taint, declared
                        ),
                        Some(s.span),
                    ));
                }
            }
            // `return` leaves the function; the rest of the enclosing block is unreachable, so its
            // taint updates must not be applied on this path (task #252, root cause 1).
            env.diverged = true;
        }
    }
}

fn check_stmts(
    stmts: &[TypedStmt],
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let _ = check_stmt_seq(stmts, env, current_fn, program, diagnostics);
}

/// The innermost local a place expression writes through (`x` for `x`,
/// `a` for `a.b.c` or `a.b[i]`). Returns `None` for a non-place expr,
/// which the type checker has already rejected (T243). Used to propagate
/// assignment taint to the root container of a field/index write.
fn place_root_local(place: &crate::typed_ast::TypedExpr) -> Option<&str> {
    match &place.kind {
        crate::typed_ast::TypedExprKind::Local(name) => Some(name.as_str()),
        crate::typed_ast::TypedExprKind::FieldAccess(fa) => place_root_local(&fa.object),
        crate::typed_ast::TypedExprKind::Index(ix) => place_root_local(&ix.array),
        _ => None,
    }
}

/// The state field a place writes THROUGH (`d` for `d.f`, `a` for `a[i]`), or
/// `None` for a place not rooted in a state field. The taint-axis twin of
/// `place_root_local`, used to sink-check a projected write into an aggregate
/// state field (AGG-4). Mirrors `type_check::statements::place_root_statefield`
/// (re-added locally — that copy is `pub(super)` and unreachable from here).
fn place_root_statefield(place: &crate::typed_ast::TypedExpr) -> Option<&str> {
    match &place.kind {
        crate::typed_ast::TypedExprKind::StateField(name) => Some(name.as_str()),
        crate::typed_ast::TypedExprKind::FieldAccess(fa) => place_root_statefield(&fa.object),
        crate::typed_ast::TypedExprKind::Index(ix) => place_root_statefield(&ix.array),
        _ => None,
    }
}

/// Whether an expression is an `alloc(...)` intrinsic — an allocation site
/// that mints a fresh M6 region. (`region_of_expr` walks `+`/`-` address
/// arithmetic back to a base local; the M5b `ptr_base_local` helper it
/// replaced is gone.)
fn is_alloc_expr(expr: &crate::typed_ast::TypedExpr) -> bool {
    matches!(
        &expr.kind,
        crate::typed_ast::TypedExprKind::Intrinsic(i)
            if matches!(i.kind, TypedIntrinsicKind::Alloc)
    )
}

fn bind_pattern_taint(
    pattern: &crate::type_check::TypedPattern,
    taint: TaintLabel,
    env: &mut TaintEnv,
) {
    use crate::type_check::TypedPattern;
    match pattern {
        TypedPattern::Binding(name) => {
            env.bind(name, taint);
        }
        TypedPattern::EnumVariant { bindings, .. } => {
            for (name, _) in bindings {
                env.bind(name, taint);
            }
        }
        // Array/slice destructuring (Phase 5): each named element and the named
        // rest slice inherit the scrutinee's taint (they are values read out of it).
        TypedPattern::Array {
            elem_binds, rest, ..
        } => {
            for (name, _) in elem_binds {
                if let Some(name) = name {
                    env.bind(name, taint);
                }
            }
            if let Some((Some(rest_name), _)) = rest {
                env.bind(rest_name, taint);
            }
        }
        TypedPattern::Literal(_) | TypedPattern::Range { .. } | TypedPattern::Wildcard => {}
    }
}

/// Compute the taint of an expression. Folds in pc_taint via lub.
/// CT enforcement (CT005–CT007, CT010, CT014, CT015, CT017) emits
/// diagnostics at the point of detection. See `docs/specs/secret-ct.md`
/// §3.2 and §10.
fn compute_expr_taint(
    expr: &TypedExpr,
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) -> TaintLabel {
    let base = match &expr.kind {
        TypedExprKind::Literal(_) => TaintLabel::Public,

        TypedExprKind::Local(name) => env.lookup(name),

        // A state READ carries the field's declared taint (bound in `env` from
        // the actor captures). The anti-laundering guard is on the WRITE side:
        // an `init` assignment into a state field is taint-sink-checked against
        // the field's declared label (see the Assign handling), so a @Secret
        // value cannot be stored into a @Public state field and read back clean.
        TypedExprKind::StateField(name) => env.lookup(name),

        TypedExprKind::Binary(b) => {
            let l = compute_expr_taint(&b.lhs, env, current_fn, program, diagnostics);
            let r = if matches!(
                b.op,
                crate::ast::BinaryOp::LogicalAnd | crate::ast::BinaryOp::LogicalOr
            ) {
                if l.is_ct() {
                    diagnostics.push(Diagnostic::error(
                        codes::T020,
                        "secret-dependent short-circuit branch: left operand has taint @SecretCT (T020 / CT001)"
                            .to_string(),
                        Some(expr.span),
                    ));
                }
                let mut rhs_env = env.clone();
                rhs_env.pc_taint = rhs_env.pc_taint.lub(l);
                compute_expr_taint(&b.rhs, &mut rhs_env, current_fn, program, diagnostics)
            } else {
                compute_expr_taint(&b.rhs, env, current_fn, program, diagnostics)
            };
            // CT007 (T026) — variable-time division. Reject if either operand
            // has taint @SecretCT (division micro-ops on most CPUs are
            // data-dependent). Sigil currently has no Shl/Shr/Rem BinaryOps,
            // so CT008 is spec-reserved with no current language surface.
            if b.op == crate::ast::BinaryOp::Div && (l.is_ct() || r.is_ct()) {
                diagnostics.push(Diagnostic::error(
                    codes::T026,
                    "variable-time division: operand has taint @SecretCT (T026 / CT007)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            // CT018 (T033) — secret-dependent string content comparison.
            // `str` `==`/`!=` lowers to an early-exit byte loop
            // (`AirStmt::StrBytesEq`), so both its trip count AND the fuel it
            // burns reveal the length of the common prefix.
            //
            // This has to be caught HERE: taint runs on the typed AST, strictly
            // before `air::lower`, so by the time the loop exists the labels are
            // gone. And it has to be a rejection rather than a constant-time
            // lowering — taint results are not carried into lowering, a
            // branch-free compare still leaks `min(len_a, len_b)` through trip
            // count and fuel, and `ct_eq`/`ct_select`/`ct_lt` are integer-only
            // so there is nothing to build one from.
            //
            // KEEP THIS PREDICATE IN STEP WITH `is_str_eq` in `air.rs` — it must
            // gate exactly the expressions that take that lowering. Widening one
            // without the other silently un-guards the loop.
            if matches!(b.op, crate::ast::BinaryOp::Eq | crate::ast::BinaryOp::NotEq)
                && matches!(b.lhs.ty, crate::type_check::Type::Str)
                && matches!(b.rhs.ty, crate::type_check::Type::Str)
                && (l.is_ct() || r.is_ct())
            {
                diagnostics.push(Diagnostic::error(
                    codes::T033,
                    "secret-dependent string content comparison: `str` `==`/`!=` operand has \
                     taint @SecretCT (T033 / CT018)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            l.lub(r)
        }

        TypedExprKind::Call(c) => {
            // Return taint = lub(callee ret_taint, arg taints)
            let arg_taints: Vec<TaintLabel> = c
                .args
                .iter()
                .map(|a| compute_expr_taint(a, env, current_fn, program, diagnostics))
                .collect();
            let args_taint = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            let Some(callee) = find_function(program, &c.callee) else {
                internal_taint_error(
                    format!(
                        "taint checker: typed call target `{}` was not found",
                        c.callee
                    ),
                    expr.span,
                    diagnostics,
                );
                return args_taint.lub(env.effective_pc());
            };
            check_typed_arity(
                &format!("typed call `{}`", c.callee),
                arg_taints.len(),
                callee.params.len(),
                expr.span,
                diagnostics,
            );
            if callee.ret_flow || callee.params.iter().any(|p| p.flow) {
                record_flow_call(expr.span, args_taint);
            }
            for ((arg, arg_taint), param) in c.args.iter().zip(&arg_taints).zip(&callee.params) {
                // Taint polymorphism: a `@Flow` parameter has no fixed label to
                // check against — it accepts any of `FLOW_INSTANTIATIONS`, and
                // the callee's body has been verified at each of them. The
                // argument's label is not discarded: it joins into `args_taint`
                // below, so the result carries it forward. `@SecretCT` is the
                // one label a `@Flow` body was NOT checked at (its CT discipline
                // constrains the code itself), so it is rejected here.
                if param.flow {
                    if arg_taint.is_ct() {
                        diagnostics.push(Diagnostic::error(
                            codes::T030,
                            format!(
                                "cannot pass @SecretCT value to taint-polymorphic function `{}` \
                                 parameter `{}`: `@Flow` does not quantify over @SecretCT, whose \
                                 constant-time discipline constrains the callee's body (T030)",
                                c.callee, param.name
                            ),
                            Some(arg.span),
                        ));
                    }
                    continue;
                }
                check_argument_taint(
                    *arg_taint,
                    param.taint,
                    &format!("function `{}` parameter `{}`", c.callee, param.name),
                    arg.span,
                    diagnostics,
                );
            }
            // AGG2b-4 (HOLE-TAINT): a `push` into a `mut Vec<scalar>` actor-state
            // field routes to a `$state`-suffixed monomorph instance (AGG2b-2). The
            // pushed element lands in the field's PERSISTENT heap and is read back at
            // the field's DECLARED taint, so a higher-taint value pushed in launders
            // to @Public on read-back (the Vec sibling of the F007 message-boundary
            // and the projected-place state-write sinks). The `$state` suffix —
            // reserved from user paths (T271) — marks EXACTLY this store; `args[0]`
            // is the receiver (rooted at the state field), `args[1..]` the pushed
            // value(s). Sink-check each pushed value against the rooted field's
            // declared taint, mirroring the `Assign`-into-`StateField` sink. A bare
            // `v.push(@Secret);` (an `Expr` statement whose value taint is otherwise
            // discarded) is now caught, not just the `let n = v.push(@Secret)` form.
            if c.callee.ends_with(crate::air::STATE_VEC_MONO_SUFFIX)
                && let Some(root) = c.args.first().and_then(place_root_statefield)
            {
                let declared = env.lookup(root);
                for stored in arg_taints.iter().skip(1) {
                    if !stored.can_flow_to(declared) {
                        diagnostics.push(Diagnostic::error(
                            codes::T001,
                            format!(
                                "cannot push @{stored:?} value into actor state Vec `{root}` \
                                 declared @{declared:?} without declassification (T001)"
                            ),
                            Some(expr.span),
                        ));
                    }
                }
            }
            // `-> T @Flow`: the result's label is the one that flowed in. The
            // join over ALL arguments (not just the `@Flow` ones) is the same
            // conservative rule the non-polymorphic path uses — a value the
            // callee could have derived its result from cannot be dropped.
            if callee.ret_flow {
                args_taint
            } else {
                callee.ret_taint.lub(args_taint)
            }
        }

        TypedExprKind::Intrinsic(intrinsic) => {
            // Compute per-arg taints once so CT checks and the join share work.
            let arg_taints: Vec<TaintLabel> = intrinsic
                .args
                .iter()
                .map(|arg| compute_expr_taint(arg, env, current_fn, program, diagnostics))
                .collect();
            let args_taint = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            match &intrinsic.kind {
                TypedIntrinsicKind::Alloc => {
                    // CT015 (T029) — allocation size must not depend on
                    // @SecretCT data (heap layout is observable).
                    if let Some(size_taint) = arg_taints.first()
                        && size_taint.is_ct()
                    {
                        diagnostics.push(Diagnostic::error(
                            codes::T029,
                            "secret-dependent allocation size: alloc(n) with n @SecretCT (T029 / CT015)"
                                .to_string(),
                            Some(expr.span),
                        ));
                    }
                    args_taint
                }
                TypedIntrinsicKind::Load8 | TypedIntrinsicKind::Store8 => {
                    // CT006 (T025) — secret-dependent address. First arg is
                    // the pointer; cache state leaks the access pattern.
                    if let Some(ptr_taint) = arg_taints.first()
                        && ptr_taint.is_ct()
                    {
                        diagnostics.push(Diagnostic::error(
                            codes::T025,
                            "secret-dependent memory address: load8/store8 with ptr @SecretCT (T025 / CT006)"
                                .to_string(),
                            Some(expr.span),
                        ));
                    }
                    args_taint
                }
                // Slot intrinsics inherit lub of inputs, identical to other
                // intrinsics. Future PRs can refine to propagate per-slot
                // stored taint if the use case arises.
                TypedIntrinsicKind::SlotNew { .. } => args_taint,
                TypedIntrinsicKind::SlotPut | TypedIntrinsicKind::SlotTake => args_taint,
                // CT006 (T025) — `vec_load`/`vec_store` are indexed memory
                // access, so a secret-dependent element ADDRESS leaks the
                // access pattern (which slot is touched is cache-observable),
                // exactly like load8/store8. The address is `base` (arg 0) +
                // `index` (arg 1); the bound and the stored value do not affect
                // it. The result inherits the conservative lub of inputs (heap
                // contents are not precisely taint-tracked — same limitation as
                // a load8 from a buffer a secret was stored into).
                TypedIntrinsicKind::VecStore { .. } | TypedIntrinsicKind::VecLoad { .. } => {
                    if arg_taints.iter().take(2).any(|t| t.is_ct()) {
                        diagnostics.push(Diagnostic::error(
                            codes::T025,
                            "secret-dependent memory address: vec_load/vec_store with a @SecretCT base or index (T025 / CT006)"
                                .to_string(),
                            Some(expr.span),
                        ));
                    }
                    args_taint
                }
                // PR AF / N20-AF: array/slice length and is_empty
                // results inherit the receiver's taint via the lub
                // of args. A `.len()` on a `@Secret` array yields a
                // `@Secret` u32. (`.is_empty()` similarly.) This is
                // the conservative join; future PR can downgrade if
                // a `pub fn` boundary needs to declassify.
                TypedIntrinsicKind::ArrayLen { .. }
                | TypedIntrinsicKind::SliceLen
                | TypedIntrinsicKind::ArrayIsEmpty { .. }
                | TypedIntrinsicKind::SliceIsEmpty
                // Phase-1 completion: `.contains(x)` (bool result) and slice
                // `.first()`/`.last()` (`Option<T>`) inherit the receiver's
                // (and needle's) taint via the lub — a `.contains` over a
                // `@Secret` array, or an element pulled from one, is `@Secret`.
                // Same conservative-join policy as `.len()`/`.is_empty()`.
                | TypedIntrinsicKind::ArrayContains { .. }
                | TypedIntrinsicKind::SliceContains { .. }
                | TypedIntrinsicKind::SliceFirst { .. }
                | TypedIntrinsicKind::SliceLast { .. } => args_taint,
                // PR S1 / N20-S1 inheritance: Str intrinsics inherit
                // the receiver's taint via lub. `.len()` /
                // `.is_empty()` / `.byte_at(i)` on a `@Secret` Str
                // yields a `@Secret` U32. Identical policy to
                // Array/Slice intrinsics; PR S2 may declassify at
                // `pub fn` boundaries.
                TypedIntrinsicKind::StrLen
                // N-LEX: `as_output()` packs the header to an i64; the result
                // inherits the receiver's taint, identical policy to `len`.
                | TypedIntrinsicKind::StrAsOutput
                | TypedIntrinsicKind::StrIsEmpty
                | TypedIntrinsicKind::StrByteAt { .. }
                // Phase-3 integer width conversion (`.as_i32()`/etc.) inherits
                // the receiver's taint via lub — narrowing/widening an
                // `@Secret` int keeps it `@Secret`.
                | TypedIntrinsicKind::IntConvert { .. }
                // A substring inherits the receiver's taint (a view of a
                // `@Secret` Str is `@Secret`), identical policy to `byte_at`.
                | TypedIntrinsicKind::StrSubstr { .. }
                // Owned-strings PR-1: `str_from_raw(ptr, len)` taint = lub(ptr,
                // len). The header carries no BYTE taint; owned-string secrecy is
                // preserved at the OUTER builder-call boundary (a call's result
                // taint is lub(callee_ret, args) — taint_check call rule), so
                // `str_concat(@SecretCT a, _)` stays `@SecretCT` regardless.
                | TypedIntrinsicKind::StrFromRaw { .. }
                // u256 PR-U0/U1: u256 intrinsics inherit the lub of their inputs
                // (a u256/limb built from `@Secret` data is `@Secret`). Same
                // conservative-join policy as the other constructors/readers.
                | TypedIntrinsicKind::U256FromI64 { .. }
                | TypedIntrinsicKind::U256Make
                | TypedIntrinsicKind::U256Limb { .. }
                | TypedIntrinsicKind::TrapIf
                | TypedIntrinsicKind::Trap => args_taint,
                // Phase 2H §3.5: CT intrinsics are branch-free constant-time
                // primitives — the output taint is the lub of inputs (standard
                // flow). No CT-rejection rule applies because these are
                // exactly the constructs CT discipline PERMITS over @SecretCT.
                TypedIntrinsicKind::CtEq
                | TypedIntrinsicKind::CtSelect
                | TypedIntrinsicKind::CtLt => args_taint,
            }
        }

        TypedExprKind::FieldAccess(f) => {
            // Try per-field tracking if object is a local
            if let TypedExprKind::Local(name) = &f.object.kind {
                env.lookup_field(name, &f.field)
            } else {
                compute_expr_taint(&f.object, env, current_fn, program, diagnostics)
            }
        }

        TypedExprKind::Index(i) => {
            let arr = compute_expr_taint(&i.array, env, current_fn, program, diagnostics);
            let idx = compute_expr_taint(&i.index, env, current_fn, program, diagnostics);
            // CT005 (T024) — secret-dependent index. The loaded address is
            // observable via cache state; reject any @SecretCT-tainted index.
            if idx.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T024,
                    "secret-dependent index: arr[i] with i @SecretCT (T024 / CT005)".to_string(),
                    Some(expr.span),
                ));
            }
            arr.lub(idx)
        }

        // PR AF / N20-AF: slice taint is the lub of the receiver's
        // taint and the bound expressions' taints (`start`, `end`).
        // Public bounds against a `@Secret` array → result is
        // `@Secret`. Verified at commit #6 by fixture
        // `af_secret_array_slice_stays_secret`.
        TypedExprKind::Slice(s) => {
            let arr = compute_expr_taint(&s.array, env, current_fn, program, diagnostics);
            let start = s
                .start
                .as_ref()
                .map(|e| compute_expr_taint(e, env, current_fn, program, diagnostics))
                .unwrap_or(TaintLabel::Public);
            let end = s
                .end
                .as_ref()
                .map(|e| compute_expr_taint(e, env, current_fn, program, diagnostics))
                .unwrap_or(TaintLabel::Public);
            arr.lub(start).lub(end)
        }

        TypedExprKind::ArrayLit(a) => a
            .elements
            .iter()
            .map(|e| compute_expr_taint(e, env, current_fn, program, diagnostics))
            .fold(TaintLabel::Public, TaintLabel::lub),

        // PR-E3: an f-string's taint is the lub of its hole taints (chunks Public).
        TypedExprKind::FString(fs) => fs
            .parts
            .iter()
            .filter_map(|p| match p {
                crate::typed_ast::TypedFStringPart::Hole(h) => {
                    Some(compute_expr_taint(h, env, current_fn, program, diagnostics))
                }
                crate::typed_ast::TypedFStringPart::Literal(_) => None,
            })
            .fold(TaintLabel::Public, TaintLabel::lub),

        TypedExprKind::RecordConstruct(r) => {
            // Per-field taints are tracked at let-binding time.
            // When used as an expression value, collapse to lub.
            r.fields
                .iter()
                .map(|(_, e)| compute_expr_taint(e, env, current_fn, program, diagnostics))
                .fold(TaintLabel::Public, TaintLabel::lub)
        }

        TypedExprKind::EnumConstruct(e) => e
            .fields
            .iter()
            .map(|f| compute_expr_taint(f, env, current_fn, program, diagnostics))
            .fold(TaintLabel::Public, TaintLabel::lub),

        TypedExprKind::ClosureConstruct(c) => {
            // E4 / §3.7 — Closure capture CT propagation. Look up each
            // capture's source taint from the enclosing TaintEnv and
            // type-check the synthesized closure body under that env.
            // Non-optional: omitting the propagation silently disables CT
            // for closure-using code, which crypto code routinely is.
            let capture_taints: Vec<TaintLabel> =
                c.captures.iter().map(|cap| env.lookup(&cap.name)).collect();

            // Find the lambda-lifted function by synthesized_name.
            let closure_fn = program
                .modules
                .iter()
                .flat_map(|m| m.functions.iter())
                .find(|f| f.name == c.synthesized_name);

            // A missing synthesized function must reject, but malformed or
            // recovered input must not abort the compiler process. I013 keeps
            // this CT boundary fail-closed while preserving diagnostics.
            let Some(closure_fn) = closure_fn else {
                internal_taint_error(
                    format!(
                        "CT closure propagation: synthesized closure `{}` not found in TypedProgram",
                        c.synthesized_name
                    ),
                    expr.span,
                    diagnostics,
                );
                return capture_taints
                    .into_iter()
                    .fold(TaintLabel::Public, TaintLabel::lub)
                    .lub(env.effective_pc());
            };

            // Build a fresh TaintEnv: lifted params bound at their own
            // declared taint; captures bound at the source taints from the
            // enclosing scope.
            let mut closure_env = TaintEnv::new();
            for p in &closure_fn.params {
                closure_env.bind(&p.name, p.taint);
            }
            check_typed_arity(
                &format!("closure `{}` capture list", c.synthesized_name),
                capture_taints.len(),
                closure_fn.captures.len(),
                expr.span,
                diagnostics,
            );
            for (cap, taint) in closure_fn.captures.iter().zip(capture_taints.iter()) {
                closure_env.bind(&cap.name, *taint);
            }

            // Type-check the closure body with propagated taints. Any CT
            // violation inside the body (CT001-CT017) is emitted with the
            // violating statement's span.
            check_block(
                &closure_fn.body,
                &mut closure_env,
                closure_fn,
                program,
                diagnostics,
            );

            // The closure expression's own taint = lub of capture taints
            // (the closure is an opaque fat pointer carrying those values).
            capture_taints
                .into_iter()
                .fold(TaintLabel::Public, TaintLabel::lub)
        }

        TypedExprKind::Borrow(b) => {
            compute_expr_taint(&b.inner, env, current_fn, program, diagnostics)
        }

        TypedExprKind::Grant(g) => {
            // M4: Grant return crosses ring boundary — must be @Public
            let body_taint = compute_expr_taint(&g.body, env, current_fn, program, diagnostics);
            // Note: actual sink check is done at the return-statement level
            // inside the closure body, not here. Here we just propagate.
            let cap_taint = compute_expr_taint(&g.cap, env, current_fn, program, diagnostics);
            body_taint.lub(cap_taint)
        }

        TypedExprKind::Handle(h) => {
            // A handler body is an ordinary lexical block: every statement
            // participates in taint checking and the expression result, when
            // present, determines the handle expression's value taint.
            check_block(&h.body, env, current_fn, program, diagnostics)
                .unwrap_or(TaintLabel::Public)
        }

        // Effect Handlers (EH3, C-VIS): operation parameters are taint boundaries,
        // just like ordinary function parameters. A perform result conservatively
        // carries every argument's taint; clause binders retain their operation
        // parameter contracts, and resume/abort values flow into the handle result.
        TypedExprKind::Perform(p) => {
            let arg_taints: Vec<TaintLabel> = p
                .args
                .iter()
                .map(|arg| compute_expr_taint(arg, env, current_fn, program, diagnostics))
                .collect();
            let result = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            let Some(op) = find_effect_op(program, &p.effect, &p.op) else {
                internal_taint_error(
                    format!(
                        "taint checker: typed effect operation `{}.{}` was not found",
                        p.effect, p.op
                    ),
                    expr.span,
                    diagnostics,
                );
                return result.lub(env.effective_pc());
            };
            check_typed_arity(
                &format!("typed perform `{}.{}`", p.effect, p.op),
                p.args.len(),
                op.param_taints.len(),
                expr.span,
                diagnostics,
            );
            for (index, ((arg, arg_taint), declared)) in p
                .args
                .iter()
                .zip(&arg_taints)
                .zip(&op.param_taints)
                .enumerate()
            {
                check_argument_taint(
                    *arg_taint,
                    *declared,
                    &format!("effect operation `{}.{}` argument {index}", p.effect, p.op),
                    arg.span,
                    diagnostics,
                );
            }
            result
        }
        TypedExprKind::ClauseHandle(c) => {
            let mut result =
                compute_expr_taint(&c.scrutinee, env, current_fn, program, diagnostics);
            for clause in &c.clauses {
                let declared_taints =
                    if let Some(op) = find_effect_op(program, &clause.effect, &clause.op) {
                        check_typed_arity(
                            &format!("typed clause `{}.{}`", clause.effect, clause.op),
                            clause.binders.len(),
                            op.param_taints.len(),
                            expr.span,
                            diagnostics,
                        );
                        op.param_taints.clone()
                    } else {
                        internal_taint_error(
                            format!(
                                "taint checker: typed effect operation `{}.{}` was not found",
                                clause.effect, clause.op
                            ),
                            expr.span,
                            diagnostics,
                        );
                        // Continue the rejected body's analysis at top taint so
                        // recovery never creates an under-tainted traversal.
                        vec![TaintLabel::Secret; clause.binders.len()]
                    };
                let mut clause_env = env.child_scope();
                for (binder, taint) in clause.binders.iter().zip(&declared_taints) {
                    clause_env.bind(binder, *taint);
                }
                if let Some(clause_taint) = check_block(
                    &clause.body,
                    &mut clause_env,
                    current_fn,
                    program,
                    diagnostics,
                ) {
                    result = result.lub(clause_taint);
                }
            }
            result
        }
        TypedExprKind::Resume(r) => {
            compute_expr_taint(&r.value, env, current_fn, program, diagnostics)
        }

        TypedExprKind::Declassify(d) => {
            // CT017 (T031) — declassify input contract (E2): the existing
            // `declassify` accepts only @Public/@Internal/@Secret. @SecretCT
            // inputs require `declassify_ct` first (two-step ladder).
            let value_taint = compute_expr_taint(&d.value, env, current_fn, program, diagnostics);
            // Also evaluate the cap expression for side-effect taint tracking.
            let _ = compute_expr_taint(&d.cap, env, current_fn, program, diagnostics);
            if value_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T031,
                    "cannot declassify a @SecretCT value directly; use `declassify_ct(value, ct_cap)` first (T031 / CT017)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            // Declassification lowers taint to the target level (default: Public)
            // The actual target is stored on the AST DeclassifyExpr, but in the
            // typed AST we default to Public since that's the common case.
            TaintLabel::Public
        }

        TypedExprKind::DeclassifyCt(d) => {
            // declassify_ct lowers @SecretCT → @Secret. Per spec §3.4.1, the
            // input MUST be @SecretCT; @Public/@Internal/@Secret inputs are a
            // user error (they don't need a CT capability to begin with).
            let value_taint = compute_expr_taint(&d.value, env, current_fn, program, diagnostics);
            let _ = compute_expr_taint(&d.cap, env, current_fn, program, diagnostics);
            if !value_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T032,
                    format!(
                        "declassify_ct input must be @SecretCT, found @{:?}; use `declassify(value, cap)` for non-CT data (T032)",
                        value_taint
                    ),
                    Some(expr.span),
                ));
            }
            // Lower @SecretCT → @Secret. Caller still needs `declassify` to
            // reach @Public (two-step chain).
            TaintLabel::Secret
        }

        TypedExprKind::ResultCtor(r) => {
            compute_expr_taint(&r.value, env, current_fn, program, diagnostics)
        }
        TypedExprKind::Try(t) => {
            compute_expr_taint(&t.value, env, current_fn, program, diagnostics)
        }

        TypedExprKind::Send(s) => {
            let arg_taints: Vec<TaintLabel> = s
                .args
                .iter()
                .map(|a| compute_expr_taint(a, env, current_fn, program, diagnostics))
                .collect();
            let payload_taint = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            // CT014 (T028) — @SecretCT payload across actor boundary.
            // Inter-actor CT analysis is anti-goal §9.9; first-cut reject.
            if payload_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T028,
                    "cannot send @SecretCT payload across actor boundary (T028 / CT014)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            // F007 (T001) — plain @Secret/@Internal data-flow across the actor
            // boundary. The receiving handler binds each param at its DECLARED
            // taint (default @Public), so a tainted payload sent to a lower-taint
            // param is silently laundered. Check each arg against the handler's
            // declared param taint, mirroring the assignment/return sink checks.
            check_message_payload_taint(
                &s.actor,
                &s.handler,
                &arg_taints,
                program,
                expr.span,
                diagnostics,
            );
            payload_taint
        }

        TypedExprKind::Ask(a) => {
            let arg_taints: Vec<TaintLabel> = a
                .args
                .iter()
                .map(|arg| compute_expr_taint(arg, env, current_fn, program, diagnostics))
                .collect();
            let args_taint = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            let timeout_taint =
                compute_expr_taint(&a.timeout, env, current_fn, program, diagnostics);
            // CT014 (T028) — @SecretCT payload across actor boundary.
            if args_taint.is_ct() || timeout_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T028,
                    "cannot ask with @SecretCT payload or timeout across actor boundary (T028 / CT014)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            // F007 (T001) — same payload-launder check as `send` on the request
            // path. `ask` delivers `args` to the handler's params identically;
            // the reply flows back through the handler's `ret_taint` (already
            // enforced by the M4 return sink in the handler body), so only the
            // request payload needs a boundary check here.
            check_message_payload_taint(
                &a.actor,
                &a.handler,
                &arg_taints,
                program,
                expr.span,
                diagnostics,
            );
            args_taint.lub(timeout_taint)
        }

        TypedExprKind::Spawn(s) => {
            let arg_taints: Vec<TaintLabel> = s
                .args
                .iter()
                .map(|arg| compute_expr_taint(arg, env, current_fn, program, diagnostics))
                .collect();
            let payload_taint = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            // Spawn is the third actor message boundary alongside send/ask. SecretCT values cannot
            // cross it because the child executes independently of the parent's CT discipline.
            if payload_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T028,
                    "cannot spawn actor with @SecretCT init payload (T028 / CT014)".to_string(),
                    Some(expr.span),
                ));
            }
            // Plain taint must be preserved by the child init signature. Without this sink check a
            // Secret arg delivered to a default-Public init param is rebound as Public in the child.
            check_actor_init_payload_taint(&s.actor, &arg_taints, program, expr.span, diagnostics);
            // The ActorRef itself carries authority, not the data used to initialize the actor.
            TaintLabel::Public
        }

        TypedExprKind::CapSplit(split) => {
            let amount = compute_expr_taint(&split.amount, env, current_fn, program, diagnostics);
            if amount.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T027,
                    "cannot use @SecretCT data as a capability split amount; the host call, trap, and child fuel are observable (T027 / CT010)"
                        .to_string(),
                    Some(split.amount.span),
                ));
            } else if amount != TaintLabel::Public {
                diagnostics.push(Diagnostic::error(
                    codes::T001,
                    format!(
                        "capability split amount must be @Public, found @{amount:?}; the host call, trap, and child fuel are observable (T001)"
                    ),
                    Some(split.amount.span),
                ));
            }
            TaintLabel::Public
        }

        TypedExprKind::CapDraw(draw) => {
            let amount = compute_expr_taint(&draw.amount, env, current_fn, program, diagnostics);
            if amount.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T027,
                    "cannot use @SecretCT data as a capability draw amount; the host call, trap, and child fuel are observable (T027 / CT010)"
                        .to_string(),
                    Some(draw.amount.span),
                ));
            } else if amount != TaintLabel::Public {
                diagnostics.push(Diagnostic::error(
                    codes::T001,
                    format!(
                        "capability draw amount must be @Public, found @{amount:?}; the host call, trap, and child fuel are observable (T001)"
                    ),
                    Some(draw.amount.span),
                ));
            }
            TaintLabel::Public
        }

        TypedExprKind::CapRestrict(_) | TypedExprKind::Mint(_) => {
            // Capabilities-as-values: a minted capability is authority, not
            // data — always @Public-clean (the resource it authorizes is named
            // by `for <target>`, not embedded in the cap value).
            TaintLabel::Public
        }

        TypedExprKind::ExternCall(e) => {
            // CT010 (T027) — @SecretCT passed to FFI. Sigil cannot verify
            // the C side's timing properties; any @SecretCT arg crossing the
            // boundary is rejected. The value boundary itself is @Internal,
            // so ordinary @Secret arguments are rejected with T001 as well.
            let arg_taints: Vec<TaintLabel> = e
                .args
                .iter()
                .map(|arg| compute_expr_taint(arg, env, current_fn, program, diagnostics))
                .collect();
            if arg_taints.iter().any(|taint| taint.is_ct()) {
                diagnostics.push(Diagnostic::error(
                    codes::T027,
                    format!(
                        "cannot pass @SecretCT value to extern fn `{}` (T027 / CT010)",
                        e.extern_name
                    ),
                    Some(expr.span),
                ));
            }
            for (arg, taint) in e.args.iter().zip(&arg_taints) {
                if !taint.is_ct() {
                    check_argument_taint(
                        *taint,
                        TaintLabel::Internal,
                        &format!("extern function `{}` argument", e.extern_name),
                        arg.span,
                        diagnostics,
                    );
                }
            }
            TaintLabel::Internal
        }

        // HOF / N19-HOF: general closure-call dispatch propagates
        // taint as lub(callee_local taint, args taints). The
        // closure body's ret_taint is opaque from the call site
        // (closures don't carry per-fn return-taint annotations
        // at the type level), so we conservatively use the local's
        // taint as a proxy for whatever the closure body returns.
        // Per N9-HOF this arm is explicit (no wildcard).
        TypedExprKind::IndirectCall(call) => {
            let callee_taint = env.lookup(&call.callee_local);
            let arg_taints: Vec<TaintLabel> = call
                .args
                .iter()
                .map(|a| compute_expr_taint(a, env, current_fn, program, diagnostics))
                .collect();
            // `Type::Fn` carries machine types but no taint labels. Until that
            // contract is represented, accepting a non-public argument would let
            // the closure body relabel it through a public parameter. Fail closed.
            for (arg, taint) in call.args.iter().zip(&arg_taints) {
                check_argument_taint(
                    *taint,
                    TaintLabel::Public,
                    &format!(
                        "indirect-call parameter of closure `{}` (function types do not carry taint contracts)",
                        call.callee_local
                    ),
                    arg.span,
                    diagnostics,
                );
            }
            let args_taint = arg_taints
                .into_iter()
                .fold(TaintLabel::Public, TaintLabel::lub);
            callee_taint.lub(args_taint)
        }

        TypedExprKind::Region(r) => {
            // CT015 (T029) — region(n) { ... } with n @SecretCT. Allocation
            // size is observable via heap layout; reject.
            let limit_taint = compute_expr_taint(&r.limit, env, current_fn, program, diagnostics);
            if limit_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T029,
                    "secret-dependent region size: region(n) with n @SecretCT (T029 / CT015)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            check_block(&r.body, env, current_fn, program, diagnostics)
                .unwrap_or(TaintLabel::Public)
        }
    };

    // Fold in lexical pc-taint and any control dependence that survives an early exit.
    base.lub(env.effective_pc())
}

fn find_function<'a>(program: &'a TypedProgram, name: &str) -> Option<&'a TypedFunction> {
    program
        .modules
        .iter()
        .flat_map(|m| m.functions.iter())
        .find(|f| f.name == name)
}

fn find_effect_op<'a>(
    program: &'a TypedProgram,
    effect: &str,
    op: &str,
) -> Option<&'a crate::typed_ast::EffectOpSig> {
    program
        .effect_ops
        .get(effect)
        .and_then(|ops| ops.iter().find(|candidate| candidate.name == op))
}

/// Reject a malformed typed-AST invariant without aborting the compiler.
/// Source-owned arity diagnostics (T070/E007/T094/T115) should have stopped
/// production first; reaching this helper is therefore an integrity failure.
fn internal_taint_error(
    message: String,
    span: crate::span::Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    diagnostics.push(Diagnostic::error(codes::I013, message, Some(span)));
}

fn check_typed_arity(
    boundary: &str,
    actual: usize,
    expected: usize,
    span: crate::span::Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if actual != expected {
        internal_taint_error(
            format!(
                "taint checker: {boundary} has {actual} values but target has {expected} parameters"
            ),
            span,
            diagnostics,
        );
    }
}

fn check_argument_taint(
    source: TaintLabel,
    declared: TaintLabel,
    boundary: &str,
    span: crate::span::Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if declared.is_ct() && matches!(source, TaintLabel::Internal | TaintLabel::Secret) {
        diagnostics.push(Diagnostic::error(
            codes::T030,
            format!(
                "cannot pass @{source:?} value to @SecretCT {boundary}; source must be @Public or @SecretCT (T030 / CT016)"
            ),
            Some(span),
        ));
    }
    if !source.can_flow_to(declared) {
        diagnostics.push(Diagnostic::error(
            codes::T001,
            format!(
                "cannot pass @{source:?} value to {boundary} declared @{declared:?} without declassification (T001)"
            ),
            Some(span),
        ));
    }
}

/// Resolve the declared parameter taints of an actor handler `(actor, handler)`.
///
/// Handlers are lowered to `TypedFunction`s tagged
/// `TypedFunctionKind::ActorHandler`, whose `params` are exactly the message
/// payload parameters (in declaration order), each carrying its source-declared
/// taint (default @Public). A missing match after type checking is an internal
/// pipeline inconsistency; callers fail closed rather than skipping the boundary.
fn find_handler_param_taints<'a>(
    program: &'a TypedProgram,
    actor: &str,
    handler: &str,
) -> Option<&'a [crate::typed_ast::TypedParam]> {
    program
        .modules
        .iter()
        .flat_map(|m| m.functions.iter())
        .find(|f| {
            matches!(
                &f.kind,
                crate::typed_ast::TypedFunctionKind::ActorHandler { actor: a, handler: h, .. }
                    if a == actor && h == handler
            )
        })
        .map(|f| f.params.as_slice())
}

/// Resolve the declared parameter taints of an actor's init block. A spawn with arguments has
/// already been checked against that init signature by type checking, so a miss here is an internal
/// pipeline inconsistency and must not silently bypass the taint boundary.
fn find_actor_init_param_taints<'a>(
    program: &'a TypedProgram,
    actor: &str,
) -> Option<&'a [crate::typed_ast::TypedParam]> {
    program
        .modules
        .iter()
        .flat_map(|m| m.functions.iter())
        .find(|f| {
            matches!(
                &f.kind,
                crate::typed_ast::TypedFunctionKind::ActorInit { actor: a, .. } if a == actor
            )
        })
        .map(|f| f.params.as_slice())
}

fn check_actor_init_payload_taint(
    actor: &str,
    arg_taints: &[TaintLabel],
    program: &TypedProgram,
    span: crate::span::Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let Some(params) = find_actor_init_param_taints(program, actor) else {
        // Actors without an explicit init legitimately accept no arguments.
        if arg_taints.is_empty() {
            return;
        }
        internal_taint_error(
            format!(
                "taint checker: spawn target `{actor}` has arguments but no typed actor-init function"
            ),
            span,
            diagnostics,
        );
        return;
    };
    check_typed_arity(
        &format!("spawn target `{actor}` argument list"),
        arg_taints.len(),
        params.len(),
        span,
        diagnostics,
    );
    for (arg_taint, param) in arg_taints.iter().zip(params.iter()) {
        // SecretCT is rejected by T028 at the boundary; avoid a redundant T001 at the same site.
        if arg_taint.is_ct() {
            continue;
        }
        if !arg_taint.can_flow_to(param.taint) {
            diagnostics.push(Diagnostic::error(
                codes::T001,
                format!(
                    "cannot spawn @{arg_taint:?} value into actor `{actor}` init parameter `{}` declared @{:?} without declassification (T001)",
                    param.name, param.taint
                ),
                Some(span),
            ));
        }
    }
}

/// F007 sink: reject a message payload arg whose computed taint cannot flow to
/// the receiving handler's declared parameter taint.
///
/// Without this check a `@Secret` value sent to a handler with the default
/// `@Public` param is silently laundered to `@Public` inside the receiver
/// (the handler binds params at their declared taint), defeating every
/// downstream taint sink. This mirrors the assignment/return `can_flow_to`
/// checks at the actor message boundary.
fn check_message_payload_taint(
    actor: &str,
    handler: &str,
    arg_taints: &[TaintLabel],
    program: &TypedProgram,
    span: crate::span::Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let Some(params) = find_handler_param_taints(program, actor, handler) else {
        internal_taint_error(
            format!("taint checker: typed actor handler `{actor}::{handler}` was not found"),
            span,
            diagnostics,
        );
        return;
    };
    check_typed_arity(
        &format!("message target `{actor}::{handler}` argument list"),
        arg_taints.len(),
        params.len(),
        span,
        diagnostics,
    );
    for (arg_taint, param) in arg_taints.iter().zip(params.iter()) {
        // @SecretCT payloads are already rejected wholesale by the T028 check
        // above (inter-actor CT is anti-goal §9.9); skip them here so a CT arg
        // yields a single T028 diagnostic rather than a redundant T001 too.
        if arg_taint.is_ct() {
            continue;
        }
        if !arg_taint.can_flow_to(param.taint) {
            diagnostics.push(Diagnostic::error(
                codes::T001,
                format!(
                    "cannot send @{:?} value to actor handler `{}::{}` parameter `{}` declared @{:?} without declassification (T001)",
                    arg_taint, actor, handler, param.name, param.taint
                ),
                Some(span),
            ));
        }
    }
}
