//! Modifier and internal-call inlining with capture-safe renaming.

use super::*;

// ── pass 0: modifier inlining (SOL1c) ────────────────────────────────────────

/// Inline every applied `modifier` into the function it guards, replacing the
/// modifier body's single `_` placeholder with the host function body. Runs before
/// all other desugar passes. Fail-closed throughout: an undefined/duplicate modifier,
/// a local collision, or an over-deep merged body is REJECTED — never a silently
/// dropped guard (the existential failure for a security translator, E1).
pub(super) fn inline_modifiers(c: &mut Contract) -> Result<(), FrontendDiag> {
    // Borrow the fields disjointly: the modifier MAP borrows `modifiers`, the fold
    // mutates `functions`, and the collision seed reads `state` — different fields, so
    // the borrows coexist.
    let Contract {
        state,
        modifiers,
        functions,
        ..
    } = c;

    // Build the lookup; a duplicate decl name is ambiguous (FE450).
    let mut map: std::collections::HashMap<&str, &Modifier> = std::collections::HashMap::new();
    for m in modifiers.iter() {
        if map.insert(m.name.as_str(), m).is_some() {
            return Err(FrontendDiag::new(
                codes::FE450_DUPLICATE_MODIFIER_SOL,
                format!("duplicate modifier declaration `{}`", m.name),
                m.span.clone(),
            ));
        }
    }

    // SOL-ACCESS: a contract-global monotonic counter for the `__fe_m<N>_` arg-binding
    // prefixes, so a param binding from one applied (parameterized) modifier can never
    // collide with another's — across functions and across stacked modifiers.
    let mut mod_arg_counter: usize = 0;
    for f in functions.iter_mut() {
        if f.modifiers.is_empty() {
            continue;
        }
        // Resolve every applied modifier (unknown → FE451; never silently drop). Each
        // entry pairs the modifier DECL with its application ARGS (SOL-ACCESS).
        let mut applied: Vec<(&Modifier, &[Expr])> = Vec::with_capacity(f.modifiers.len());
        for app in &f.modifiers {
            match map.get(app.name.as_str()) {
                Some(m) => {
                    // FE453: a modifier with statements AFTER `_` (a suffix) cannot be
                    // faithfully inlined — in Solidity a suffix runs on function EXIT, but
                    // flat inlining makes it dead code when the host body returns (e.g. a
                    // nonReentrant unlock that never clears, bricking the lock). The `_`
                    // must be in tail position.
                    if placeholder_has_suffix(&m.body) {
                        return Err(FrontendDiag::new(
                            codes::FE453_MODIFIER_SUFFIX_SOL,
                            format!(
                                "modifier `{}` has statements after `_` (a suffix); the `_` must be in tail position (SOL1c cannot model code that runs on function exit)",
                                app.name
                            ),
                            f.span.clone(),
                        ));
                    }
                    // SOL-ACCESS: the application arity must match the decl (`onlyRole(x)` on
                    // `modifier onlyRole(bytes32 role)`); a mismatch → FE448 (fail-closed —
                    // never bind the wrong number of args).
                    if m.params.len() != app.args.len() {
                        return Err(FrontendDiag::new(
                            codes::FE448_PARAMETERIZED_MODIFIER_SOL,
                            format!(
                                "modifier `{}` expects {} argument(s) but is applied with {} on `{}`",
                                app.name,
                                m.params.len(),
                                app.args.len(),
                                f.name
                            ),
                            f.span.clone(),
                        ));
                    }
                    applied.push((m, app.args.as_slice()));
                }
                None => {
                    return Err(FrontendDiag::new(
                        codes::FE451_UNDEFINED_MODIFIER_SOL,
                        format!(
                            "function `{}` applies an undefined modifier `{}`",
                            f.name, app.name
                        ),
                        f.span.clone(),
                    ));
                }
            }
        }

        // E4 (FE449): a modifier-introduced local must not collide with ANY name the host
        // body can resolve — params, host locals, **contract state fields**, or another
        // applied modifier's local. Flat inlining merges the scopes, so a collision would
        // silently shadow the name; omitting state fields was a real mistranslation (a
        // modifier-local named like a state field redirects the host's state reads/writes
        // to a dead local). `seen` accumulates so modifier-vs-modifier collisions are
        // caught too. Common guard modifiers declare ZERO locals → never fires for them.
        let mut seen: HashSet<String> = f.params.iter().map(|p| p.name.clone()).collect();
        for sv in state.iter() {
            seen.insert(sv.name.clone());
        }
        collect_local_names(&f.body, &mut seen);
        for (m, _) in &applied {
            let mut mlocals: HashSet<String> = HashSet::new();
            collect_local_names(&m.body, &mut mlocals);
            for ln in &mlocals {
                if seen.contains(ln) {
                    return Err(FrontendDiag::new(
                        codes::FE449_MODIFIER_LOCAL_COLLISION_SOL,
                        format!(
                            "modifier-introduced local `{ln}` collides with a function local/param, a state field, or another modifier's local in `{}`",
                            f.name
                        ),
                        f.span.clone(),
                    ));
                }
            }
            seen.extend(mlocals);
        }

        // SOL-CALLS FE488 class, applied to the modifier pass (found by the SOL-CALLS adversarial
        // review): the FE449 loop above catches a modifier LOCAL colliding with a host name, but NOT
        // the INVERSE — a modifier's un-renamed STATE-FIELD reference captured by a host PARAMETER/LOCAL
        // of the same name. Flat inlining leaves the modifier's `owner` bare; emit's `resolve_name`
        // resolves a bare name LOCAL-first (`state.contains(n) && !locals.contains(n)`), so under a host
        // param `owner` the inlined `require(msg.sender == owner)` guard reads the host's ARGUMENT, not
        // `self.owner` — a silent access-control BYPASS (an attacker calls `f(msg.sender)`). Reject
        // fail-closed when an applied modifier references a state field the host shadows.
        let mut host_names: HashSet<String> = f.params.iter().map(|p| p.name.clone()).collect();
        collect_local_names(&f.body, &mut host_names);
        for (m, _) in &applied {
            for sv in state.iter() {
                if host_names.contains(&sv.name)
                    && m.body
                        .iter()
                        .any(|s| stmt_references_field(s, &sv.name).is_some())
                {
                    return Err(FrontendDiag::new(
                        codes::FE488_STATE_CAPTURE_SOL,
                        format!(
                            "inlining modifier `{}` into `{}` would capture its state-field reference `{}`: the function has a parameter/local named `{}` that shadows the state field, so the spliced guard/access would bind to that local instead of `self.{}` — rename the parameter/local",
                            m.name, f.name, sv.name, sv.name, sv.name
                        ),
                        f.span.clone(),
                    ));
                }
            }
        }

        // Right-fold so the leftmost modifier is outermost: `f() m1 m2 { B }` becomes
        // `m1[_ -> m2[_ -> B]]`. Each `splice` deep-clones the modifier body (it may be
        // applied to several functions) and moves the host body into its single `_`.
        // SOL-ACCESS: for a parameterized modifier, `prepare_modifier_body` binds each
        // param to its application arg EVAL-ONCE via a `let __fe_m<N>_<param> = <arg>;`
        // prelude (fresh N per application) + alpha-renames the body's param refs to those
        // names — so a call-valued arg (`getRoleAdmin(role)`) is evaluated exactly once at
        // the modifier's entry point, and a param can never capture a host name (the
        // `__fe_` prefix is FE420-reserved). A parameterless modifier is spliced verbatim.
        let mut inner = std::mem::take(&mut f.body);
        for (m, args) in applied.iter().rev() {
            let body = prepare_modifier_body(m, args, &mut mod_arg_counter);
            inner = splice(body, inner)?;
        }
        f.body = inner;
        f.modifiers.clear();

        // E1 — the headline guard: after inlining, NO placeholder may remain and the
        // modifier list MUST be empty. A residual placeholder means the splice failed to
        // consume it (internal bug); a security translator must never emit a function whose
        // guard was silently dropped. Fail loud (FE500).
        if has_placeholder(&f.body) {
            return Err(FrontendDiag::new(
                codes::FE500_INTERNAL_MALFORMED_SOL,
                "internal: a modifier `_` placeholder survived inlining",
                f.span.clone(),
            ));
        }

        // E3 — totality: splicing concatenates two ≤MAX_NEST_DEPTH bodies, so the MERGED
        // body can exceed the depth the trusted re-parser (emit's FE500 self-check)
        // survives. Re-bound it HERE, before emit, so a deep-modifier × deep-body input is
        // an FE402 reject, never a native stack overflow.
        if block_depth(&f.body) > MAX_NEST_DEPTH {
            return Err(FrontendDiag::new(
                codes::FE402_TOO_LARGE_SOL,
                format!(
                    "inlined body of `{}` exceeds nesting depth {MAX_NEST_DEPTH}",
                    f.name
                ),
                f.span.clone(),
            ));
        }
    }
    Ok(())
}

// ── SOL-CALLS: inline internal function calls ────────────────────────────────────────────────────

/// The maximum internal-call inline depth — a cycle/too-deep-graph totality backstop (→ FE485).
const MAX_INLINE_DEPTH: u32 = 16;

/// The maximum TOTAL inline expansions per contract — bounds output SIZE, not just recursion DEPTH, so
/// a statement-list fan-out (`f_i(){ f_{i+1}(); f_{i+1}(); }` ≈ 2^16 nodes at depth 16, which stays
/// depth-FLAT so FE402's nesting check never fires) is rejected instead of DoS-ing the translator. Real
/// contracts inline tens of times; 4096 is a generous ceiling. (Found by the SOL-CALLS adversarial review.)
const MAX_INLINE_EXPANSIONS: u32 = 4096;

/// Inline every internal function call. Runs AFTER `inline_modifiers` and BEFORE `lower_sender`, so an
/// inlined `_msgSender()`→`msg.sender` flows through `lower_sender`, and an inlined `_transfer` body's
/// debit/credit flows through `recognize_transfers`. Hygiene (EX-1): every callee's params + locals are
/// alpha-renamed with a fresh `__fe_inl<N>_` prefix, so a callee name can NEVER capture a caller name;
/// params are bound via a let-prelude (never textual substitution). A statement-position void call
/// splices the (renamed) body; an expression-position call inlines ONLY a pure single-`return` callee
/// (`_msgSender()`), else FE486. Recursion/over-depth → FE485; a void callee containing a `return` →
/// FE484 (flat inlining cannot preserve the return-from-callee); an unknown callee → FE401.
pub(super) fn inline_internal_calls(
    c: &mut Contract,
    cap_active: bool,
) -> Result<(), FrontendDiag> {
    // Owned clones of every function, so a callee body can be read while a caller body is mutated.
    let fns: std::collections::HashMap<String, Function> = c
        .functions
        .iter()
        .map(|f| (f.name.clone(), f.clone()))
        .collect();
    let state_names: HashSet<String> = c.state.iter().map(|sv| sv.name.clone()).collect();
    let mut inl = Inliner {
        fns: &fns,
        counter: 0,
        stack: HashSet::new(),
        cap_active,
        state_names,
        caller_shadowed: HashSet::new(),
    };
    for f in c.functions.iter_mut() {
        let body = std::mem::take(&mut f.body);
        inl.stack.clear();
        inl.stack.insert(f.name.clone()); // a function calling itself is a cycle
        inl.set_caller_shadowed(&f.params, &body);
        f.body = inl.block(body, 0)?;
        rebound_inline_depth(&f.body, &f.name)?;
    }
    if let Some(ctor) = c.constructor.as_mut() {
        let body = std::mem::take(&mut ctor.body);
        inl.stack.clear();
        inl.set_caller_shadowed(&ctor.params, &body);
        ctor.body = inl.block(body, 0)?;
        rebound_inline_depth(&ctor.body, "constructor")?;
    }
    Ok(())
}

/// Totality (like `inline_modifiers`): the MERGED body concatenates ≤MAX_NEST_DEPTH bodies, so re-bound
/// it before emit — a deep call graph is an FE402 reject, never a native stack overflow downstream.
pub(super) fn rebound_inline_depth(body: &[Stmt], site: &str) -> Result<(), FrontendDiag> {
    if block_depth(body) > MAX_NEST_DEPTH {
        return Err(FrontendDiag::new(
            codes::FE402_TOO_LARGE_SOL,
            format!("inlined body of `{site}` exceeds nesting depth {MAX_NEST_DEPTH}"),
            0..0,
        ));
    }
    Ok(())
}

/// The inline pass state: the callee table, a monotonic counter for fresh `__fe_inl<N>_` prefixes, and
/// the call stack currently being inlined (a direct/transitive cycle → FE485).
pub(super) struct Inliner<'a> {
    fns: &'a std::collections::HashMap<String, Function>,
    counter: u32,
    stack: HashSet<String>,
    /// SOL-CALLS × SOL-CAP: cap-mode recognized a gate. The cap E-2/H7 data-use gate runs BEFORE this
    /// pass and cannot see through a call, so an internal call could hide a `msg.sender`/owner data-use
    /// from it — fail closed (FE487) on ANY internal call under cap-mode.
    cap_active: bool,
    /// Every contract state-field name (a callee's bare state reference is left un-renamed to stay the
    /// shared record field).
    state_names: HashSet<String>,
    /// The CURRENT caller's params/locals that SHADOW a state field — a callee referencing one would be
    /// captured (its state access silently redirected to the caller's local) → FE488. Reset per caller.
    caller_shadowed: HashSet<String>,
}

impl Inliner<'_> {
    fn fresh_prefix(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("__fe_inl{n}_")
    }

    /// Recompute `caller_shadowed` for a new caller: its params + locals that shadow a state field.
    fn set_caller_shadowed(&mut self, params: &[Param], body: &[Stmt]) {
        let mut names: HashSet<String> = params.iter().map(|p| p.name.clone()).collect();
        collect_local_names(body, &mut names);
        names.retain(|n| self.state_names.contains(n));
        self.caller_shadowed = names;
    }

    /// Inline every call in a statement list; recurse into `if` branches. `depth` bounds inline
    /// recursion (FE485).
    fn block(&mut self, stmts: Vec<Stmt>, depth: u32) -> Result<Vec<Stmt>, FrontendDiag> {
        if depth > MAX_INLINE_DEPTH {
            return Err(fe485_depth());
        }
        let mut out: Vec<Stmt> = Vec::with_capacity(stmts.len());
        for s in stmts {
            // Inline expression-position calls first, hoisting any param let-preludes into `out`.
            let s = self.stmt_exprs(s, depth, &mut out)?;
            match s {
                Stmt::CallStmt { callee, args, span } => {
                    self.void_call(&callee, args, span, depth, &mut out)?;
                }
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    span,
                } => {
                    let then_body = self.block(then_body, depth)?;
                    let else_body = self.block(else_body, depth)?;
                    out.push(Stmt::If {
                        cond,
                        then_body,
                        else_body,
                        span,
                    });
                }
                // SOL-AIRDROP (Rung C): inline internal calls INSIDE the airdrop loop body — the
                // per-leg `_transfer(msg.sender, recipients[i], amounts[i])` must be spliced to its
                // raw debit/credit pair here, so `recognize_airdrop` (a LATER desugar pass) sees the
                // pair, not a residual `CallStmt`. Mirror the `If` body recursion.
                Stmt::AirdropLoop {
                    idx,
                    len_array,
                    body,
                    span,
                } => {
                    let body = self.block(body, depth)?;
                    out.push(Stmt::AirdropLoop {
                        idx,
                        len_array,
                        body,
                        span,
                    });
                }
                other => out.push(other),
            }
        }
        Ok(out)
    }

    /// Splice a statement-position void call: bind params via a let-prelude, alpha-rename the callee
    /// body, splice it (recursing for nested calls).
    fn void_call(
        &mut self,
        callee: &str,
        args: Vec<Expr>,
        span: Range<usize>,
        depth: u32,
        out: &mut Vec<Stmt>,
    ) -> Result<(), FrontendDiag> {
        let (params, body) = match self.fns.get(callee) {
            Some(f) => (f.params.clone(), f.body.clone()),
            None => {
                return Err(FrontendDiag::new(
                    codes::FE401_UNSUPPORTED_SOL,
                    format!(
                        "call to `{callee}`, which is not an internal function in this contract (external/unknown calls are unsupported)"
                    ),
                    span,
                ));
            }
        };
        if self.cap_active {
            return Err(cap_call_conflict(callee, span));
        }
        if self.counter >= MAX_INLINE_EXPANSIONS {
            return Err(fe402_expansions());
        }
        if self.stack.contains(callee) {
            return Err(FrontendDiag::new(
                codes::FE485_CALL_RECURSION_SOL,
                format!(
                    "recursive internal call to `{callee}` (internal-call inlining requires an acyclic call graph)"
                ),
                span,
            ));
        }
        if args.len() != params.len() {
            return Err(FrontendDiag::new(
                codes::FE401_UNSUPPORTED_SOL,
                format!(
                    "call to `{callee}` has {} argument(s) but it declares {} parameter(s)",
                    args.len(),
                    params.len()
                ),
                span,
            ));
        }
        // A `return` in a callee, inlined at a STATEMENT call site, would return from the CALLER —
        // flat inlining cannot preserve the return-from-callee semantics. BUT when the call is a
        // STATEMENT (the return value is discarded), a TAIL-position return with a PURE expr is just
        // "the body ends here" with a thrown-away value — droppable (SOL-ACCESS W4, the OZ
        // `_grantRole`/`_revokeRole` shape: `if (…) { …; return true; } else { return false; }`).
        // `strip_tail_pure_returns` drops exactly those; a non-tail early return, or a return whose
        // expr has a side effect / trap-capable arith (which dropping would lose), keeps FE484.
        let body = if body_has_return(&body) {
            match strip_tail_pure_returns(body) {
                Some(stripped) => stripped,
                None => {
                    return Err(FrontendDiag::new(
                        codes::FE484_CALL_BODY_RETURNS_SOL,
                        format!(
                            "internal function `{callee}` called as a statement contains a non-tail or side-effecting `return`; flat inlining cannot preserve it (the return would exit the caller)"
                        ),
                        span,
                    ));
                }
            }
        } else {
            body
        };
        let prefix = self.fresh_prefix();
        // Alpha-rename the callee's params + locals FIRST (state fields stay bare — the shared record).
        let mut rename: HashSet<String> = params.iter().map(|p| p.name.clone()).collect();
        collect_local_names(&body, &mut rename);
        let renamed = rename_body(body, &rename, &prefix);
        // FE488: a bare state-field name still in the renamed body is a genuine state reference; if the
        // CALLER shadows that field with a param/local, splicing would capture it (emit resolves the bare
        // name to the caller's local, not `self.<field>`). Fail-closed.
        for field in &self.caller_shadowed {
            if renamed
                .iter()
                .any(|s| stmt_references_field(s, field).is_some())
            {
                return Err(fe488_capture(callee, field, span.clone()));
            }
        }
        // let-prelude: bind each param (renamed) to its arg (a CALLER-scope expr, left untouched —
        // evaluated in the caller's scope, before the renamed body runs).
        for (p, a) in params.iter().zip(args) {
            out.push(Stmt::LocalVar {
                name: format!("{prefix}{}", p.name),
                ty: p.ty.clone(),
                value: a,
                span: span.clone(),
            });
        }
        self.stack.insert(callee.to_string());
        let inlined = self.block(renamed, depth + 1)?;
        self.stack.remove(callee);
        out.extend(inlined);
        Ok(())
    }

    /// Rewrite the expression-position calls inside a single statement, hoisting param let-preludes
    /// into `out` (before the statement). The statement-position call (a `CallStmt`) and `if` bodies
    /// are handled by `block`, NOT here.
    fn stmt_exprs(
        &mut self,
        s: Stmt,
        depth: u32,
        out: &mut Vec<Stmt>,
    ) -> Result<Stmt, FrontendDiag> {
        Ok(match s {
            Stmt::Require { cond, span } => Stmt::Require {
                cond: self.expr(cond, depth, out)?,
                span,
            },
            Stmt::Assert { cond, span } => Stmt::Assert {
                cond: self.expr(cond, depth, out)?,
                span,
            },
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => Stmt::Assign {
                target,
                op,
                value: self.expr(value, depth, out)?,
                span,
            },
            Stmt::IndexAssign {
                map,
                key,
                op,
                value,
                span,
            } => Stmt::IndexAssign {
                map,
                key: self.expr(key, depth, out)?,
                op,
                value: self.expr(value, depth, out)?,
                span,
            },
            Stmt::IndexAssign2 {
                map,
                k1,
                k2,
                op,
                value,
                span,
            } => Stmt::IndexAssign2 {
                map,
                k1: self.expr(k1, depth, out)?,
                k2: self.expr(k2, depth, out)?,
                op,
                value: self.expr(value, depth, out)?,
                span,
            },
            Stmt::FieldAssign {
                obj,
                field,
                op,
                value,
                span,
            } => Stmt::FieldAssign {
                obj,
                field,
                op,
                value: self.expr(value, depth, out)?,
                span,
            },
            Stmt::LocalVar {
                name,
                ty,
                value,
                span,
            } => Stmt::LocalVar {
                name,
                ty,
                value: self.expr(value, depth, out)?,
                span,
            },
            Stmt::Return { value, span } => {
                let value = match value {
                    Some(v) => Some(self.expr(v, depth, out)?),
                    None => None,
                };
                Stmt::Return { value, span }
            }
            Stmt::CallStmt { callee, args, span } => {
                let mut new_args = Vec::with_capacity(args.len());
                for a in args {
                    new_args.push(self.expr(a, depth, out)?);
                }
                Stmt::CallStmt {
                    callee,
                    args: new_args,
                    span,
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => Stmt::If {
                cond: self.expr(cond, depth, out)?,
                then_body,
                else_body,
                span,
            },
            // SOL-AIRDROP: the raw loop still exists at inline time. Like `Stmt::If` above, its
            // body is descended by `block` (not here) and the header carries no expr-position
            // operand — so hand the node back unchanged.
            s @ Stmt::AirdropLoop { .. } => s,
            // No inlinable expressions (MapTransfer/Erc20TransferFrom/ReservedBatch/BatchTransfer are
            // produced by LATER passes; Placeholder is removed by the EARLIER inline_modifiers pass —
            // none reach here).
            s @ (Stmt::Revert { .. }
            | Stmt::Unchecked { .. }
            | Stmt::Placeholder { .. }
            | Stmt::MapTransfer { .. }
            | Stmt::Erc20TransferFrom { .. }
            | Stmt::ReservedBatch { .. }
            | Stmt::MapSplitTransfer { .. }
            | Stmt::Erc20Update { .. }
            | Stmt::BatchTransfer { .. }) => s,
        })
    }

    /// Rewrite an expression, inlining any internal-function `Call` (hoisting param let-preludes into
    /// `out`). A `Call` whose callee is NOT a known internal function (a struct constructor, a member
    /// call) is left unchanged for `check` to validate/reject.
    fn expr(&mut self, e: Expr, depth: u32, out: &mut Vec<Stmt>) -> Result<Expr, FrontendDiag> {
        // A statement-level expression is unconditional (sc = false); `expr_sc` threads the
        // short-circuit flag into `&&`/`||` right operands.
        self.expr_sc(e, depth, false, out)
    }

    /// `sc` = this expression sits in a `&&`/`||` short-circuit-CONDITIONAL position (a right operand),
    /// so a value-call's param let-prelude hoisted here would evaluate on a path Solidity may skip.
    fn expr_sc(
        &mut self,
        e: Expr,
        depth: u32,
        sc: bool,
        out: &mut Vec<Stmt>,
    ) -> Result<Expr, FrontendDiag> {
        Ok(match e {
            Expr::Call(callee, args, span) => {
                let mut new_args = Vec::with_capacity(args.len());
                for a in args {
                    new_args.push(self.expr_sc(a, depth, sc, out)?);
                }
                if let Expr::Var(name, _) = callee.as_ref()
                    && self.fns.contains_key(name)
                {
                    let name = name.clone();
                    return self.value_call(&name, new_args, span, depth, sc, out);
                }
                Expr::Call(callee, new_args, span)
            }
            Expr::Bin(op, l, r, span) => {
                // The RIGHT operand of `&&`/`||` is short-circuit-conditional; the left is always
                // evaluated (with the current `sc`).
                let rhs_sc = sc || matches!(op, BinOp::And | BinOp::Or);
                Expr::Bin(
                    op,
                    Box::new(self.expr_sc(*l, depth, sc, out)?),
                    Box::new(self.expr_sc(*r, depth, rhs_sc, out)?),
                    span,
                )
            }
            Expr::Unary(op, b, span) => {
                Expr::Unary(op, Box::new(self.expr_sc(*b, depth, sc, out)?), span)
            }
            Expr::Index(b, k, span) => Expr::Index(
                Box::new(self.expr_sc(*b, depth, sc, out)?),
                Box::new(self.expr_sc(*k, depth, sc, out)?),
                span,
            ),
            Expr::Member(b, m, span) => {
                Expr::Member(Box::new(self.expr_sc(*b, depth, sc, out)?), m, span)
            }
            leaf @ (Expr::Num(..) | Expr::Bool(..) | Expr::Var(..)) => leaf,
        })
    }

    /// Inline an expression-position call: sound ONLY for a pure single-`return` callee. Bind params
    /// (let-prelude, hoisted before the enclosing statement) + substitute the (alpha-renamed) return
    /// expression. A multi-statement (or void) value-return → FE486 (never substitute-and-drop).
    fn value_call(
        &mut self,
        name: &str,
        args: Vec<Expr>,
        span: Range<usize>,
        depth: u32,
        sc: bool,
        out: &mut Vec<Stmt>,
    ) -> Result<Expr, FrontendDiag> {
        if depth > MAX_INLINE_DEPTH {
            return Err(fe485_depth());
        }
        if self.stack.contains(name) {
            return Err(FrontendDiag::new(
                codes::FE485_CALL_RECURSION_SOL,
                format!(
                    "recursive internal call to `{name}` (internal-call inlining requires an acyclic call graph)"
                ),
                span,
            ));
        }
        if self.cap_active {
            return Err(cap_call_conflict(name, span));
        }
        if self.counter >= MAX_INLINE_EXPANSIONS {
            return Err(fe402_expansions());
        }
        let (params, body) = match self.fns.get(name) {
            Some(f) => (f.params.clone(), f.body.clone()),
            None => unreachable!("value_call is only reached when fns contains the callee"),
        };
        if args.len() != params.len() {
            return Err(FrontendDiag::new(
                codes::FE401_UNSUPPORTED_SOL,
                format!(
                    "call to `{name}` has {} argument(s) but it declares {} parameter(s)",
                    args.len(),
                    params.len()
                ),
                span,
            ));
        }
        // FE489: a value-call WITH parameters needs a let-prelude hoisted to the STATEMENT level; in a
        // `&&`/`||` short-circuit operand that prelude would evaluate (and maybe trap on) a path Solidity
        // skips. A 0-parameter call (`_msgSender()`) substitutes in place → always safe.
        if sc && !params.is_empty() {
            return Err(fe489_shortcircuit(name, span));
        }
        // Sound ONLY for a pure single-return body (`_msgSender()` = `return msg.sender;`).
        let ret = match body.as_slice() {
            [Stmt::Return { value: Some(e), .. }] => e.clone(),
            _ => {
                return Err(FrontendDiag::new(
                    codes::FE486_CALL_VALUE_MULTI_SOL,
                    format!(
                        "internal function `{name}` is used as a value but is not a single `return <expr>;` (a multi-statement or void value-return is unsupported in expression position)"
                    ),
                    span,
                ));
            }
        };
        let prefix = self.fresh_prefix();
        // A single-return body has no locals; rename the params only (referenced in the return expr).
        let rename: HashSet<String> = params.iter().map(|p| p.name.clone()).collect();
        let renamed_ret = rename_expr(ret, &rename, &prefix);
        // FE488: a bare state-field name in the substituted return expr that the CALLER shadows would be
        // captured (a getter's `return owner;` returning the caller's `owner` arg). Fail-closed.
        for field in &self.caller_shadowed {
            if expr_references_field(&renamed_ret, field) {
                return Err(fe488_capture(name, field, span.clone()));
            }
        }
        for (p, a) in params.iter().zip(args) {
            out.push(Stmt::LocalVar {
                name: format!("{prefix}{}", p.name),
                ty: p.ty.clone(),
                value: a,
                span: span.clone(),
            });
        }
        self.stack.insert(name.to_string());
        let result = self.expr_sc(renamed_ret, depth + 1, sc, out)?;
        self.stack.remove(name);
        Ok(result)
    }
}

pub(super) fn fe485_depth() -> FrontendDiag {
    FrontendDiag::new(
        codes::FE485_CALL_RECURSION_SOL,
        format!(
            "internal-call inlining exceeded depth {MAX_INLINE_DEPTH} (recursion or a too-deep call graph)"
        ),
        0..0,
    )
}

/// SOL-CALLS × SOL-CAP: an internal call under cap-mode. The cap E-2/H7 data-use gate runs BEFORE this
/// pass and cannot see a `msg.sender`/owner use hidden in a callee body (`log[_msgSender()]` bypasses
/// FE454), so the combination is rejected fail-closed (FE487).
pub(super) fn cap_call_conflict(callee: &str, span: Range<usize>) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE487_CALL_IN_CAP_MODE_SOL,
        format!(
            "internal call to `{callee}` under cap-mode (`// sigil:cap-access-control`): the capability E-2/H7 data-use gate runs before inlining and cannot see a `msg.sender`/owner use hidden inside a callee — remove the directive (use the address model) or the internal call"
        ),
        span,
    )
}

/// SOL-CALLS totality (adversarial review): the fan-out output-size cap. `MAX_INLINE_DEPTH` bounds the
/// recursion tree HEIGHT, but a statement-list fan-out stays depth-flat and expands exponentially.
pub(super) fn fe402_expansions() -> FrontendDiag {
    FrontendDiag::new(
        codes::FE402_TOO_LARGE_SOL,
        format!(
            "internal-call inlining expanded past {MAX_INLINE_EXPANSIONS} call sites (a fan-out call graph); too large to inline"
        ),
        0..0,
    )
}

/// SOL-CALLS × state capture (adversarial review): the caller shadows a state field the callee references.
pub(super) fn fe488_capture(callee: &str, field: &str, span: Range<usize>) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE488_STATE_CAPTURE_SOL,
        format!(
            "inlining `{callee}` would capture its state-field reference `{field}`: the caller has a parameter/local named `{field}` that shadows the state field, so the spliced access would silently bind to that local instead of `self.{field}` — rename the caller's parameter/local"
        ),
        span,
    )
}

/// SOL-CALLS × short-circuit (adversarial review): a param-bearing value-call in a `&&`/`||` operand.
pub(super) fn fe489_shortcircuit(name: &str, span: Range<usize>) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE489_CALL_SHORTCIRCUIT_SOL,
        format!(
            "internal function `{name}` (with parameters) is called inside a `&&`/`||` short-circuit operand; its argument binding would be hoisted out of the guard and evaluated on a path Solidity skips — bind the call to a local before the condition"
        ),
        span,
    )
}

pub(super) fn body_has_return(stmts: &[Stmt]) -> bool {
    stmts.iter().any(stmt_has_return)
}

/// SOL-ACCESS W4: for a value-returning callee inlined at a STATEMENT call site (the
/// return value is discarded), drop every TAIL-position `return <pure-expr>;` — a tail
/// return is just "the body ends here", and the discarded value's PURE expr has no
/// observable effect. Returns the stripped body if EVERY `return` is tail-and-pure;
/// `None` if any return is NON-tail (a mid-body early return = real control flow flat
/// inlining can't model) OR its expr is side-effecting / trap-capable (dropping it would
/// lose that effect) → the caller keeps FE484. Purity reuses `emit_arg_discard_safe`
/// (no call except the pure `_msgSender`/cast shims, no trap-capable arith).
pub(super) fn strip_tail_pure_returns(body: Vec<Stmt>) -> Option<Vec<Stmt>> {
    let n = body.len();
    // Every statement BEFORE the tail must be return-free (a return there is a non-tail
    // early return — control flow that exits the caller, unrepresentable by flat inlining).
    for s in body.iter().take(n.saturating_sub(1)) {
        if stmt_has_return(s) {
            return None;
        }
    }
    let mut out = body;
    match out.pop() {
        None => Some(out),
        Some(Stmt::Return { value, .. }) => match value {
            None => Some(out),
            Some(e) if crate::solidity::parser::emit_arg_discard_safe(&e) => Some(out),
            Some(_) => None, // a side-effecting / trap-capable return expr — keep FE484
        },
        Some(Stmt::If {
            cond,
            then_body,
            else_body,
            span,
        }) => {
            // The tail is an `if` — each branch must itself be tail-and-pure droppable.
            let then_body = strip_tail_pure_returns(then_body)?;
            let else_body = strip_tail_pure_returns(else_body)?;
            out.push(Stmt::If {
                cond,
                then_body,
                else_body,
                span,
            });
            Some(out)
        }
        // A non-return tail statement (and no returns anywhere, per the loop above) — nothing to strip.
        Some(other) => {
            out.push(other);
            Some(out)
        }
    }
}

pub(super) fn stmt_has_return(s: &Stmt) -> bool {
    match s {
        Stmt::Return { .. } => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => then_body.iter().any(stmt_has_return) || else_body.iter().any(stmt_has_return),
        _ => false,
    }
}

/// Alpha-rename every occurrence of a name in `names` (a callee's params + locals) to `<prefix><name>`,
/// across every REFERENCE (a `Var`) and every BINDING/target position. Names NOT in the set (state
/// fields, other functions, `msg`) are untouched — so the callee's shared-state reads/writes still
/// resolve to the same contract fields (the hygiene guarantee, EX-1).
/// SOL-ACCESS: produce the ready-to-splice body of an APPLIED modifier — for a
/// parameterized modifier, alpha-rename its param refs to `__fe_m<N>_<param>` and
/// prepend an EVAL-ONCE `let __fe_m<N>_<param> = <arg>;` prelude (in param order,
/// before the placeholder). `counter` is bumped once per application so distinct
/// applications never share binding names. A parameterless modifier is returned as a
/// verbatim clone (the byte-identical SOL1c path). The caller has already arity-checked.
///
/// EVAL-ONCE is the load-bearing invariant: a call-valued arg (`getRoleAdmin(role)`) is
/// bound to a fresh local ONCE, then every param use in the body reads that local —
/// never re-evaluates the arg (which would double-run a getter / a state read). The
/// arg expressions are the HOST's (spliced verbatim, referencing host params in scope
/// at the modifier's entry point); only the modifier BODY's param refs are renamed, so
/// a modifier param can never capture a host name (`__fe_` is FE420-reserved).
pub(super) fn prepare_modifier_body(m: &Modifier, args: &[Expr], counter: &mut usize) -> Vec<Stmt> {
    if m.params.is_empty() {
        return m.body.clone();
    }
    let n = *counter;
    *counter += 1;
    let prefix = format!("__fe_m{n}_");
    let param_names: HashSet<String> = m.params.iter().map(|p| p.name.clone()).collect();
    // Alpha-rename every param reference in the body to `__fe_m<N>_<param>`.
    let renamed = rename_body(m.body.clone(), &param_names, &prefix);
    // The eval-once binding prelude, in param order (the arg is the host's expression).
    let mut out: Vec<Stmt> = Vec::with_capacity(m.params.len() + renamed.len());
    for (p, arg) in m.params.iter().zip(args.iter()) {
        out.push(Stmt::LocalVar {
            name: format!("{prefix}{}", p.name),
            ty: p.ty.clone(),
            value: arg.clone(),
            span: p.span.clone(),
        });
    }
    out.extend(renamed);
    out
}

pub(super) fn rename_body(stmts: Vec<Stmt>, names: &HashSet<String>, prefix: &str) -> Vec<Stmt> {
    stmts
        .into_iter()
        .map(|s| rename_stmt(s, names, prefix))
        .collect()
}

pub(super) fn rename_name(n: String, names: &HashSet<String>, prefix: &str) -> String {
    if names.contains(&n) {
        format!("{prefix}{n}")
    } else {
        n
    }
}

pub(super) fn rename_stmt(s: Stmt, names: &HashSet<String>, prefix: &str) -> Stmt {
    match s {
        Stmt::Require { cond, span } => Stmt::Require {
            cond: rename_expr(cond, names, prefix),
            span,
        },
        Stmt::Assert { cond, span } => Stmt::Assert {
            cond: rename_expr(cond, names, prefix),
            span,
        },
        Stmt::Revert { span } => Stmt::Revert { span },
        Stmt::Assign {
            target,
            op,
            value,
            span,
        } => Stmt::Assign {
            target: rename_name(target, names, prefix),
            op,
            value: rename_expr(value, names, prefix),
            span,
        },
        Stmt::IndexAssign {
            map,
            key,
            op,
            value,
            span,
        } => Stmt::IndexAssign {
            map: rename_name(map, names, prefix),
            key: rename_expr(key, names, prefix),
            op,
            value: rename_expr(value, names, prefix),
            span,
        },
        Stmt::IndexAssign2 {
            map,
            k1,
            k2,
            op,
            value,
            span,
        } => Stmt::IndexAssign2 {
            map: rename_name(map, names, prefix),
            k1: rename_expr(k1, names, prefix),
            k2: rename_expr(k2, names, prefix),
            op,
            value: rename_expr(value, names, prefix),
            span,
        },
        Stmt::FieldAssign {
            obj,
            field,
            op,
            value,
            span,
        } => Stmt::FieldAssign {
            obj: rename_name(obj, names, prefix),
            field,
            op,
            value: rename_expr(value, names, prefix),
            span,
        },
        Stmt::LocalVar {
            name,
            ty,
            value,
            span,
        } => Stmt::LocalVar {
            name: rename_name(name, names, prefix),
            ty,
            value: rename_expr(value, names, prefix),
            span,
        },
        Stmt::If {
            cond,
            then_body,
            else_body,
            span,
        } => Stmt::If {
            cond: rename_expr(cond, names, prefix),
            then_body: rename_body(then_body, names, prefix),
            else_body: rename_body(else_body, names, prefix),
            span,
        },
        Stmt::Return { value, span } => Stmt::Return {
            value: value.map(|v| rename_expr(v, names, prefix)),
            span,
        },
        // A callee's OWN nested call: the callee name is a function (never a param/local), so it is not
        // renamed; only the args are. It gets its own fresh prefix when `block` inlines it recursively.
        Stmt::CallStmt { callee, args, span } => Stmt::CallStmt {
            callee,
            args: args
                .into_iter()
                .map(|a| rename_expr(a, names, prefix))
                .collect(),
            span,
        },
        // Unreachable here (`unwrap_unchecked` runs FIRST, before any inline/rename), but recurse
        // defensively so a future pass reordering can never leave a body's names un-renamed.
        Stmt::Unchecked { body, span } => Stmt::Unchecked {
            body: rename_body(body, names, prefix),
            span,
        },
        Stmt::Placeholder { span } => Stmt::Placeholder { span },
        // Not present in a pre-inline callee body (produced by a later recognize pass); handled for
        // exhaustiveness so a future reordering can never silently skip the rename.
        Stmt::MapTransfer {
            map,
            from,
            to,
            amount,
            span,
        } => Stmt::MapTransfer {
            map: rename_name(map, names, prefix),
            from: rename_expr(from, names, prefix),
            to: rename_expr(to, names, prefix),
            amount: rename_expr(amount, names, prefix),
            span,
        },
        Stmt::Erc20TransferFrom {
            bal_map,
            alw_map,
            from,
            spender,
            to,
            amount,
            oz5_infinite,
            span,
        } => Stmt::Erc20TransferFrom {
            bal_map: rename_name(bal_map, names, prefix),
            alw_map: rename_name(alw_map, names, prefix),
            from: rename_expr(from, names, prefix),
            spender: rename_expr(spender, names, prefix),
            to: rename_expr(to, names, prefix),
            amount: rename_expr(amount, names, prefix),
            oz5_infinite,
            span,
        },
        // `ReservedBatch` is produced by the LATER `reserve_multi_map` pass; rename (used by the
        // EARLIER inline/unchecked passes) never sees one. Pass through unchanged (defensive).
        resb @ Stmt::ReservedBatch { .. } => resb,
        mst @ Stmt::MapSplitTransfer { .. } => mst,
        // `Erc20Update` is produced by the LATER `recognize_update` pass (post-inline); the
        // rename walkers never see one. Pass through unchanged (defensive).
        eu @ Stmt::Erc20Update { .. } => eu,
        // SOL-AIRDROP: a raw loop can sit in a callee body being inlined — rename its body like
        // an `if` block. `idx`/`len_array` are the loop's own header names (kept unchanged).
        Stmt::AirdropLoop {
            idx,
            len_array,
            body,
            span,
        } => Stmt::AirdropLoop {
            idx,
            len_array,
            body: rename_body(body, names, prefix),
            span,
        },
        // `BatchTransfer` is produced by the LATER `recognize_airdrop` pass; rename never sees
        // one. Pass through unchanged (defensive), like `Erc20Update`.
        bt @ Stmt::BatchTransfer { .. } => bt,
    }
}

pub(super) fn rename_expr(e: Expr, names: &HashSet<String>, prefix: &str) -> Expr {
    match e {
        Expr::Var(name, span) => Expr::Var(rename_name(name, names, prefix), span),
        Expr::Member(b, m, span) => Expr::Member(Box::new(rename_expr(*b, names, prefix)), m, span),
        Expr::Call(c, args, span) => Expr::Call(
            Box::new(rename_expr(*c, names, prefix)),
            args.into_iter()
                .map(|a| rename_expr(a, names, prefix))
                .collect(),
            span,
        ),
        Expr::Index(b, k, span) => Expr::Index(
            Box::new(rename_expr(*b, names, prefix)),
            Box::new(rename_expr(*k, names, prefix)),
            span,
        ),
        Expr::Unary(op, b, span) => Expr::Unary(op, Box::new(rename_expr(*b, names, prefix)), span),
        Expr::Bin(op, l, r, span) => Expr::Bin(
            op,
            Box::new(rename_expr(*l, names, prefix)),
            Box::new(rename_expr(*r, names, prefix)),
            span,
        ),
        leaf @ (Expr::Num(..) | Expr::Bool(..)) => leaf,
    }
}

/// Splice the host function body (`inner`) into the modifier body's single `_`
/// placeholder. The host is moved exactly once (via an `Option` take); a non-consumed
/// host contradicts the parse-time exactly-one-`_` invariant (FE447) → internal FE500.
pub(super) fn splice(mod_body: Vec<Stmt>, inner: Vec<Stmt>) -> Result<Vec<Stmt>, FrontendDiag> {
    let mut host = Some(inner);
    let out = splice_stmts(mod_body, &mut host);
    if host.is_some() {
        return Err(FrontendDiag::new(
            codes::FE500_INTERNAL_MALFORMED_SOL,
            "internal: modifier placeholder not consumed during inlining",
            0..0,
        ));
    }
    Ok(out)
}

/// Walk a (cloned) modifier body, replacing the single `Stmt::Placeholder` with the
/// host body (taken from `host`). Recurses into `if` branches (a `_` may be nested).
pub(super) fn splice_stmts(stmts: Vec<Stmt>, host: &mut Option<Vec<Stmt>>) -> Vec<Stmt> {
    let mut out = Vec::with_capacity(stmts.len());
    for s in stmts {
        match s {
            Stmt::Placeholder { .. } => {
                if let Some(body) = host.take() {
                    out.extend(body);
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => {
                let then_body = splice_stmts(then_body, host);
                let else_body = splice_stmts(else_body, host);
                out.push(Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    span,
                });
            }
            other => out.push(other),
        }
    }
    out
}

/// Collect every `LocalVar` binding name in a statement tree (descending into `if`
/// branches) — for the E4 collision check.
pub(super) fn collect_local_names(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        match s {
            Stmt::LocalVar { name, .. } => {
                out.insert(name.clone());
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_local_names(then_body, out);
                collect_local_names(else_body, out);
            }
            _ => {}
        }
    }
}

/// Whether any `Stmt::Placeholder` remains in a tree (the E1 post-inline assertion).
pub(super) fn has_placeholder(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Placeholder { .. } => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => has_placeholder(then_body) || has_placeholder(else_body),
        _ => false,
    })
}

/// Whether a statement (subtree) contains the placeholder.
pub(super) fn stmt_contains_placeholder(s: &Stmt) -> bool {
    match s {
        Stmt::Placeholder { .. } => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => has_placeholder(then_body) || has_placeholder(else_body),
        _ => false,
    }
}

/// Whether any statement executes AFTER the modifier's `_` placeholder (a "suffix").
/// Such code runs on function EXIT in Solidity (even after a body `return`), which a flat
/// inline cannot model — when the host body returns, the suffix becomes dead code (FE453).
/// Assumes exactly one placeholder (FE447-enforced). Walks to the placeholder's containing
/// statement: anything after it (in this list, or after the containing `if`) is a suffix;
/// if the containing statement is the last and is an `if`, recurse into the branch holding
/// the placeholder. A bare trailing `Placeholder` (tail position) has no suffix.
pub(super) fn placeholder_has_suffix(stmts: &[Stmt]) -> bool {
    for (i, s) in stmts.iter().enumerate() {
        if stmt_contains_placeholder(s) {
            if i + 1 != stmts.len() {
                return true; // statements follow the placeholder's container
            }
            return match s {
                Stmt::Placeholder { .. } => false,
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    if has_placeholder(then_body) {
                        placeholder_has_suffix(then_body)
                    } else {
                        placeholder_has_suffix(else_body)
                    }
                }
                _ => false,
            };
        }
    }
    false
}

/// Combined nesting depth of a statement list, mirroring the parser's `enter()`
/// accounting (statement `if`-nesting + the AST depth of each statement's expressions,
/// added on the same scale). Used post-inline to re-bound the MERGED body (E3) against
/// `MAX_NEST_DEPTH` — conservative (it may reject a body the parser would have, but the
/// only such bodies are adversarially deep). The walk recurses at most ~2×MAX_NEST_DEPTH,
/// far below any stack limit.
pub(super) fn block_depth(stmts: &[Stmt]) -> u32 {
    stmts.iter().map(stmt_depth).max().unwrap_or(0)
}

pub(super) fn stmt_depth(s: &Stmt) -> u32 {
    match s {
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            1 + expr_depth(cond)
                .max(block_depth(then_body))
                .max(block_depth(else_body))
        }
        Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => expr_depth(cond),
        Stmt::Assign { value, .. } | Stmt::LocalVar { value, .. } => expr_depth(value),
        Stmt::IndexAssign { key, value, .. } => expr_depth(key).max(expr_depth(value)),
        Stmt::FieldAssign { value, .. } => expr_depth(value),
        Stmt::IndexAssign2 { k1, k2, value, .. } => {
            expr_depth(k1).max(expr_depth(k2)).max(expr_depth(value))
        }
        Stmt::MapTransfer {
            from, to, amount, ..
        } => expr_depth(from).max(expr_depth(to)).max(expr_depth(amount)),
        Stmt::Erc20TransferFrom {
            from,
            spender,
            to,
            amount,
            ..
        } => expr_depth(from)
            .max(expr_depth(spender))
            .max(expr_depth(to))
            .max(expr_depth(amount)),
        Stmt::Return { value: Some(v), .. } => expr_depth(v),
        // SOL-CALLS: a call is not a nesting statement; its depth is its deepest arg (like Assign).
        Stmt::CallStmt { args, .. } => args.iter().map(expr_depth).max().unwrap_or(0),
        // SOL-AIRDROP: the raw loop is a nesting statement (like `if`); its depth is 1 + the
        // deepest body statement.
        Stmt::AirdropLoop { body, .. } => 1 + block_depth(body),
        Stmt::Return { value: None, .. }
        | Stmt::Revert { .. }
        | Stmt::Unchecked { .. }
        | Stmt::ReservedBatch { .. }
        | Stmt::MapSplitTransfer { .. }
        | Stmt::Erc20Update { .. }
        // SOL-AIRDROP: a `BatchTransfer` is a flat atomic (produced post-fold), not a nesting stmt.
        | Stmt::BatchTransfer { .. }
        | Stmt::Placeholder { .. } => 0,
    }
}

pub(super) fn expr_depth(e: &Expr) -> u32 {
    match e {
        Expr::Num(..) | Expr::Bool(..) | Expr::Var(..) => 1,
        Expr::Member(b, _, _) => 1 + expr_depth(b),
        Expr::Index(b, k, _) => 1 + expr_depth(b).max(expr_depth(k)),
        Expr::Unary(_, x, _) => 1 + expr_depth(x),
        Expr::Bin(_, l, r, _) => 1 + expr_depth(l).max(expr_depth(r)),
        Expr::Call(c, args, _) => {
            let arg_max = args.iter().map(expr_depth).max().unwrap_or(0);
            1 + expr_depth(c).max(arg_max)
        }
    }
}
