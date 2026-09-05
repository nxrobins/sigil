//! Statement-level type checking.
//!
//! Handles the AST-level statement kinds (let/assign/return/if/match/
//! while/for/expr) by recursively calling `infer_expr` from `mod.rs`
//! for sub-expressions and emitting structural diagnostics for shape
//! mismatches (T046/T047/T049, narrowing-related T201/T2xx, etc).
//!
//! Entry points:
//!
//! - `check_function_block` — top-level entry called from
//!   `check_with_options`. Sets up the per-function env + the
//!   refinement-frame stack, then runs `check_block`.
//! - `check_block` — recursive body checker. Routes each statement to
//!   the appropriate `check_*` arm and accumulates the typed result.
//!
//! Per-stmt arms:
//!
//! - `check_let` / `resolve_annotated_let_type` — let-bindings with
//!   optional type annotations + refinement narrowing through patterns
//! - `check_assign` — reassignment, including reassignability checks
//!   for cap-bearing / ref-bearing types
//! - `check_expr_stmt` — bare expression statements
//! - `check_return` — return with optional value; refinement
//!   subsumption against the function's declared return refinement
//! - `check_if` — if/else with flow-sensitive refinement narrowing
//! - `check_match` — match with arm refinement narrowing
//! - `check_while` — while loops
//!
//! Extracted from `type_check/mod.rs` in structural-extraction PR 7.
//! Verbatim move — zero logic change. The shadow CI gate from PR 2.0
//! validates byte-equality of every diagnostic downstream.

use std::collections::{HashMap, HashSet};

use super::resolve::{
    ReassignRejection, apply_subst, classify_reassign_rejection, infer_literal_type,
    render_literal, render_type, resolve_int_literals_or_reject, resolve_type_expr,
    try_array_size_mismatch_diagnostic, try_cap_deadline_diagnostic, type_compatible,
    type_is_reassignable,
};
use super::types::RangeLoopFact;
use super::{
    BodyKind, ExpectedTypeGuard, FunctionSig, MonomorphTracker, ParamRegion, RegionId, Type,
    TypeCheckContext, TypeUniverse, compose_narrowing_frame, extract_narrowing_predicate,
    infer_expr, negate_refinement_clause, type_contains_never,
};
use crate::ast::{
    Block, ExprStmt, LetStmt, LetTupleStmt, Literal, Pattern, RefinementClause, RefinementOp,
    RefinementRhs, ReturnStmt, Stmt, TypeExpr,
};
use crate::diagnostics::{Diagnostic, codes};
use crate::span::Span;
use crate::typed_ast::{
    TypedAssignStmt, TypedBlock, TypedExpr, TypedExprKind, TypedExprStmt, TypedForInStmt,
    TypedForRangeStmt, TypedIfStmt, TypedLetStmt, TypedMatchArm, TypedMatchStmt, TypedParam,
    TypedPattern, TypedReturnStmt, TypedStmt, TypedWhileStmt,
};

/// Iterator protocol (PR-1): resolve `{type_name}::next` exactly as method dispatch
/// does (`expressions.rs::infer_method_call_expr`) — the current module's sigs first,
/// then a cross-module impl scan. Returns the sig only when a SINGLE defining module
/// is found; an ambiguous/absent `next` is "not an iterator here" (a real call would
/// surface T244/T132). Side-effect-free: `resolve_impl_member_global` borrows the
/// tracker immutably.
fn iterator_next_sig(
    type_name: &str,
    function_sigs: &std::collections::BTreeMap<String, FunctionSig>,
    module_name: &str,
    tracker: &MonomorphTracker,
) -> Option<FunctionSig> {
    let key = format!("{type_name}::next");
    match function_sigs.get(&key) {
        Some(s) => Some(s.clone()),
        None => match crate::type_check::call_resolve::resolve_impl_member_global(
            &key,
            module_name,
            tracker,
        ) {
            crate::type_check::call_resolve::GlobalImplVerdict::Found(s) => Some(s),
            _ => None,
        },
    }
}

/// The dumb iterator predicate (ET-1): a `next` taking EXACTLY one parameter (`self`),
/// that `self` is `@Mut`, and the return is `Option<_>` with one type argument. Nothing
/// fuzzier routes a `for`-loop onto the iterator path; a bare `next(self)` (frozen) or a
/// non-`Option` return is NOT an iterator.
fn is_iterator_next_shape(sig: &FunctionSig) -> bool {
    !sig.is_associated
        && sig.params.len() == 1
        && matches!(
            sig.param_mutability.first(),
            Some(crate::ast::Mutability::Mut)
        )
        && matches!(&sig.ret, Type::Named(name, args) if name == "Option" && args.len() == 1)
}

/// Build the untyped `while`+`if` desugar for `for <var> in <iterable> { <body> }`
/// over an iterator. Temps are named off the loop's byte offset (`$for_*_{k}`): the `$`
/// prefix is OUTSIDE the `[A-Za-z_][A-Za-z0-9_]*` identifier grammar, so a user can
/// neither collide with nor reference them, and distinct loops get distinct offsets
/// (ET-3). The shape is:
///
/// ```text
/// let mut $for_it_K  = <iterable>;
/// let mut $for_go_K  = true;
/// while $for_go_K {
///     let $for_opt_K = $for_it_K.next();
///     if $for_opt_K.is_some() {
///         let <var> = $for_opt_K.unwrap_or(0);
///         <body>
///     } else {
///         $for_go_K = false;
///     }
/// }
/// ```
fn build_iterator_desugar(stmt: &crate::ast::ForInStmt) -> Block {
    use crate::ast::{
        AssignStmt, Expr, IfStmt, LiteralExpr, MethodCallExpr, Path, PathExpr, WhileStmt,
    };
    let sp = stmt.span;
    let k = stmt.span.start;
    let it = format!("$for_it_{k}");
    let go = format!("$for_go_{k}");
    let opt = format!("$for_opt_{k}");

    let path = |name: &str| {
        Expr::Path(PathExpr {
            path: Path {
                segments: vec![name.to_string()],
                type_args: Vec::new(),
                span: sp,
            },
            span: sp,
        })
    };
    let bool_lit = |b: bool| {
        Expr::Literal(LiteralExpr {
            literal: Literal::Bool(b),
            span: sp,
        })
    };

    // let mut $it = <iterable>;
    let let_it = Stmt::Let(LetStmt {
        name: it.clone(),
        mutable: true,
        ty: None,
        taint: None,
        value: stmt.iterable.clone(),
        span: sp,
    });
    // let mut $go = true;
    let let_go = Stmt::Let(LetStmt {
        name: go.clone(),
        mutable: true,
        ty: None,
        taint: None,
        value: bool_lit(true),
        span: sp,
    });
    // let $opt = $it.next();
    let let_opt = Stmt::Let(LetStmt {
        name: opt.clone(),
        mutable: false,
        ty: None,
        taint: None,
        value: Expr::MethodCall(MethodCallExpr {
            receiver: Box::new(path(&it)),
            method: "next".to_string(),
            args: Vec::new(),
            colon_spelled: false,
            span: sp,
        }),
        span: sp,
    });
    // then: `let <var> = $opt.unwrap_or(0); <body>`. The Option is destructured with
    // `is_some` + `unwrap_or` inside an `if`, NOT a `match`: a `match` STATEMENT whose
    // arms don't all `return` mis-lowers in the wasm backend today, while `if`/`else`
    // with non-returning branches is the well-trodden path. v1 iterators yield `i64`
    // (AG-4), so the `unwrap_or(0)` default is the right width — and it is never
    // observed, being guarded by `is_some`.
    let mut then_stmts = vec![Stmt::Let(LetStmt {
        name: stmt.var.clone(),
        mutable: false,
        ty: None,
        taint: None,
        value: Expr::MethodCall(MethodCallExpr {
            receiver: Box::new(path(&opt)),
            method: "unwrap_or".to_string(),
            colon_spelled: false,
            args: vec![Expr::Literal(LiteralExpr {
                literal: Literal::Int(0),
                span: sp,
            })],
            span: sp,
        }),
        span: sp,
    })];
    then_stmts.extend(stmt.body.statements.iter().cloned());
    // else: `$go = false;`
    let else_stmts = vec![Stmt::Assign(AssignStmt {
        target: path(&go),
        op: None,
        value: bool_lit(false),
        span: sp,
    })];
    let if_stmt = Stmt::If(IfStmt {
        condition: Expr::MethodCall(MethodCallExpr {
            receiver: Box::new(path(&opt)),
            method: "is_some".to_string(),
            args: Vec::new(),
            colon_spelled: false,
            span: sp,
        }),
        then_branch: Block {
            statements: then_stmts,
            span: sp,
        },
        else_branch: Block {
            statements: else_stmts,
            span: sp,
        },
        span: sp,
    });
    let while_stmt = Stmt::While(WhileStmt {
        condition: path(&go),
        body: Block {
            statements: vec![let_opt, if_stmt],
            span: sp,
        },
        span: sp,
    });

    Block {
        statements: vec![let_it, let_go, while_stmt],
        span: sp,
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_function_block(
    params: &[TypedParam],
    expected_return: &Type,
    outer_bindings: &HashMap<String, Type>,
    block: &Block,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
    // Wall 4 Step 7: per-param refinements (`None` = unrefined, `Some(_)` =
    // refined with Literal-RHS clauses). Per N26-S7, the frame key is the
    // param's declared NAME, not the clause's `field` (the parser already
    // validated those match).
    param_refinements: &[Option<Vec<crate::ast::RefinementClause>>],
    // Wall 4 Step 7 / N15-S7: declared return refinement clauses for
    // this function. The body-level `check_return` consults
    // `tracker.current_return_refinement` (set here) and emits T225 on
    // any `return <expr>` that violates the predicate.
    return_refinement: Option<Vec<crate::ast::RefinementClause>>,
    // Mutation-as-capability (PR-1): the `@ReadOnly`/`@Mut`/bare mutability of
    // each param, positionally aligned with `params` (mirrors
    // `param_refinements`). Seeds the readonly set the WRITE gate reads.
    param_mutability: &[crate::ast::Mutability],
    // Regions (DEF-2b, LD-2/LD-6): the resolved `@in r` slot of each param,
    // positionally aligned with `params` (mirrors `param_mutability`). Seeds
    // `current_param_regions` so a `Region`/`@in r` param resolves to `Param(slot)`
    // inside the body. Empty/`None` without region params → byte-identical.
    param_regions: &[ParamRegion],
    // Regions (DEF-2b, LD-4/PR-5): the resolved `where region(a): region(b)` outlives pairs
    // as `(a_slot, b_slot)`. Seeds `current_region_outlives` so the body's sinks may treat
    // `Param(a_slot)` as outliving `Param(b_slot)`. Empty without a `where region` clause.
    param_region_outlives: &[(u32, u32)],
    // Actor-state (M2): state field name → type, + the body's construction
    // context. Seeds `tracker.state_fields`/`body_kind` (save/restored like
    // `readonly_locals`) so `infer_path_expr` resolves state reads to `StateField`
    // (after params/locals) and `check_assign` gates state writes. Empty +
    // `BodyKind::Free` for every non-actor body. State fields are NOT seeded into
    // `env` — resolution falls back to this map, so any binding shadows naturally.
    state_fields: &HashMap<String, Type>,
    // MUTABLE-STATE S2 / the relax: the subset of `state_fields` declared `mut`.
    // Seeds `tracker.mut_state_fields` (save/restored like `state_fields`) so a
    // handler write to a `mut` field is permitted while every other state field
    // stays immutable-after-init. Empty for non-actor bodies and mut-free actors.
    mut_state_fields: &std::collections::HashSet<String>,
    body_kind: BodyKind,
) -> TypedBlock {
    let mut env = outer_bindings.clone();

    // N35-S7: env-insertion FIRST, then frame push. The original Step 7
    // spec said "before the env-insertion loop"; that was an
    // adversarial-malicious-compliance trap. Frame push goes AFTER so
    // the param names referenced in the frame already exist in env.
    for param in params {
        env.insert(param.name.clone(), param.ty.clone());
    }

    // Wall 4 Step 7 / N9-S7: push a fresh frame onto
    // `tracker.pattern_refinement_stack` populated with each refined
    // param's clauses keyed by the param's declared name. Pop on
    // function exit (N9-S7). Mirrors Step 6's match-arm push/pop
    // pattern. Per A6-S6-equivalent inheritance, no engineered panic-
    // safety (matching Step 6) — if type-check panics mid-body, the
    // pop is skipped; the stress-test invariant assertion catches
    // pollution at next-function entry. See N29-S7 in the spec for the
    // planned RAII drop-guard upgrade (a future cleanup, not load-
    // bearing for first-pass correctness).
    let mut frame: HashMap<String, Vec<crate::ast::RefinementClause>> = HashMap::new();
    for (idx, param) in params.iter().enumerate() {
        if let Some(Some(clauses)) = param_refinements.get(idx)
            && !clauses.is_empty()
        {
            frame.insert(param.name.clone(), clauses.clone());
        }
    }
    tracker.pattern_refinement_stack.push(frame);

    // Wall 4 Step 7 / N15-S7: set the current return refinement so
    // `check_return` can consult it without explicit threading. Save
    // the previous value (for nested function-body checks, e.g.
    // closures or generic monomorphization re-entry) and restore on
    // exit. NOTE: `tracker.current_effects` has NO such save/restore —
    // it is assigned only for non-generic top-level fns (mod.rs) and is
    // stale during mono re-entry; do not model new tracker state on it.
    let prev_return_refinement =
        std::mem::replace(&mut tracker.current_return_refinement, return_refinement);

    // Mutation-as-capability (PR-1, NC-1): seed the readonly set from the
    // `@ReadOnly` params (positional zip with `param_mutability`). Saved +
    // restored around the body like the return refinement, so nested closures
    // and monomorph re-entry never leak readonly names across function boundaries.
    let readonly_seed: HashSet<String> = params
        .iter()
        .zip(param_mutability.iter())
        .filter(|(_, m)| m.is_frozen())
        .map(|(p, _)| p.name.clone())
        .collect();
    let prev_readonly = std::mem::replace(&mut tracker.readonly_locals, readonly_seed);

    // Actor-state (M2): seed the state-field set + body kind for this body, saved
    // and restored like `readonly_locals` so nested closures / monomorph re-entry
    // (which call this with an empty set + `Free`) never inherit an enclosing
    // actor's state context.
    let prev_state_fields = std::mem::replace(&mut tracker.state_fields, state_fields.clone());
    let prev_mut_state_fields =
        std::mem::replace(&mut tracker.mut_state_fields, mut_state_fields.clone());
    let prev_body_kind = std::mem::replace(&mut tracker.body_kind, body_kind);

    // Regions (DEF-2a, NC-R5): reset the region depth state at EVERY function-body
    // entry — crucially including monomorph re-entry. A stdlib collection method
    // (`Vec::push`, `Map::insert`, …) monomorphized from inside a `region {}` block is
    // checked via this same `check_function_block`; without the reset its body would
    // inherit the CALLER's `current_region_depth`, so an inline-construct `return` or a
    // let-bound interior value in the callee would spuriously trip T254 (and the
    // callee's locals would pollute the caller's `region_locals`). Saved + restored via
    // `mem::take`/`mem::replace` exactly like `readonly_locals`, so region birth-depths
    // never leak across a function boundary (the keystone enabler + the both-orders
    // fixture's guarantee). A no-op when entered at depth 0 (the common case): taking an
    // already-empty map and replacing 0 with 0 changes nothing, so non-region
    // compilation stays byte-identical.
    let prev_region_locals = std::mem::take(&mut tracker.region_locals);
    let prev_region_depth = std::mem::replace(&mut tracker.current_region_depth, 0);

    // Regions (DEF-2b, LD-2/LD-6 + NC-2b-3): seed the param→region-slot map. A `Region`
    // parameter denotes its OWN region (slot = its position); an `@in r` parameter lives
    // in the region passed at `r`'s slot (resolved at sig collection). Inside the body,
    // `region_of_value` returns `Param(slot)` for these names — so the callee honors
    // `@in` (a `return`/field-store of an `@in r` value trips T254 via the same lattice,
    // LD-6), and the lift maps a region argument to a caller-side `RegionId` (NC-2b-3).
    // `param_regions` is read positionally with `.get(i)` (tolerant — a short/absent
    // slice fail-closes to no param region, NC-2b-4). Saved/restored via `mem::take` like
    // `region_locals`, so monomorph re-entry never inherits caller region params; empty
    // without region params (the common case) → byte-identical for non-region code.
    let mut param_region_seed: HashMap<String, u32> = HashMap::new();
    for (i, param) in params.iter().enumerate() {
        let slot = if matches!(param.ty, Type::Region) {
            Some(i as u32)
        } else if let Some(ParamRegion::In(s)) = param_regions.get(i) {
            Some(*s)
        } else {
            None
        };
        if let Some(slot) = slot {
            param_region_seed.insert(param.name.clone(), slot);
        }
    }
    let prev_param_regions =
        std::mem::replace(&mut tracker.current_param_regions, param_region_seed);
    // Regions (DEF-2b, PR-5): seed the declared `where region(a): region(b)` pairs for this
    // body. Consulted by `check_region_escape` to allow a `Param(a)`-region value into a
    // `Param(b)`-region sink. Saved/restored like `current_param_regions`; empty without a
    // `where region` clause → byte-identical.
    let prev_region_outlives = std::mem::replace(
        &mut tracker.current_region_outlives,
        param_region_outlives.to_vec(),
    );

    // Exclusivity (DEF-2c, LD-1 / NC-2c-4): seed the alias-origin map EMPTY at every
    // function-body entry — a parameter is its own origin (the callee cannot know caller
    // aliasing). Saved/restored via `mem::take` like `readonly_locals`, so monomorph re-entry
    // never inherits caller aliases; grown in `check_block`'s let-handler below.
    let prev_alias_origin = std::mem::take(&mut tracker.alias_origin);

    let mut mutables = HashSet::new();
    let result = check_block(
        block,
        &mut env,
        &mut mutables,
        expected_return,
        context,
        tracker,
        diagnostics,
        !matches!(expected_return, Type::Unit),
    );

    // Restore previous return refinement (N9-S7 push/pop discipline
    // applies symmetrically to current_return_refinement).
    tracker.current_return_refinement = prev_return_refinement;
    tracker.readonly_locals = prev_readonly;
    // Actor-state (M2): restore the caller's state context.
    tracker.state_fields = prev_state_fields;
    tracker.mut_state_fields = prev_mut_state_fields;
    tracker.body_kind = prev_body_kind;
    // Regions (DEF-2a, NC-R5): restore the caller's region depth state (pairs with the
    // `mem::take`/`mem::replace` save above).
    tracker.region_locals = prev_region_locals;
    tracker.current_region_depth = prev_region_depth;
    // Regions (DEF-2b, NC-2b-3): restore the caller's param→region map.
    tracker.current_param_regions = prev_param_regions;
    // Regions (DEF-2b, PR-5): restore the caller's declared outlives pairs.
    tracker.current_region_outlives = prev_region_outlives;
    // Exclusivity (DEF-2c): restore the caller's alias-origin map.
    tracker.alias_origin = prev_alias_origin;

    // Pop the frame on exit (N9-S7 push/pop pairing).
    tracker.pattern_refinement_stack.pop();
    result
}

/// Build the untyped desugar for `let (a, b, …) = <value>;`:
///
/// ```text
/// let $tup_K = <value>;     // K = byte offset — `$`-hygienic, ET-7
/// let [mut] a = $tup_K.0;   // FieldAccess, field "0" — synthesized, never lexed
/// let [mut] b = $tup_K.1;
/// ```
///
/// The value is bound to ONE hidden temp, so it evaluates exactly once (ET-3).
/// The `$` prefix is outside the `[A-Za-z_][A-Za-z0-9_]*` identifier grammar, so
/// `$tup_K` is unforgeable + unreferenceable by user code (ET-7), and distinct
/// destructures get distinct byte-offset suffixes. The `"0"`/`"1"` field names
/// are synthesized as `String`s — they never pass through the lexer, which is
/// why this ships while surface `.0` stays deferred (AG-1). The caller has
/// already validated arity, so every `$tup_K.i` is in range.
fn build_let_tuple_desugar(stmt: &LetTupleStmt) -> Block {
    use crate::ast::{Expr, FieldAccessExpr, Path, PathExpr};
    let sp = stmt.span;
    let k = stmt.span.start;
    let tup = format!("$tup_{k}");

    let mut statements: Vec<Stmt> = Vec::with_capacity(stmt.bindings.len() + 1);
    // let $tup_K = <value>;  (bound ONCE — ET-3)
    statements.push(Stmt::Let(LetStmt {
        name: tup.clone(),
        mutable: false,
        ty: None,
        taint: None,
        value: stmt.value.clone(),
        span: sp,
    }));
    // let [mut] <name_i> = $tup_K.<i>;
    for (i, (name, is_mut)) in stmt.bindings.iter().enumerate() {
        statements.push(Stmt::Let(LetStmt {
            name: name.clone(),
            mutable: *is_mut,
            ty: None,
            taint: None,
            value: Expr::FieldAccess(FieldAccessExpr {
                object: Box::new(Expr::Path(PathExpr {
                    path: Path {
                        segments: vec![tup.clone()],
                        type_args: Vec::new(),
                        span: sp,
                    },
                    span: sp,
                })),
                field: i.to_string(),
                span: sp,
            }),
            span: sp,
        }));
    }
    Block {
        statements,
        span: sp,
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_block(
    block: &Block,
    env: &mut HashMap<String, Type>,
    mutables: &mut HashSet<String>,
    expected_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
    enforce_full_return: bool,
) -> TypedBlock {
    let (function_sigs, _actor_sigs, module_name, universe) = context.parts();
    let mut statements = Vec::new();
    let mut guaranteed_return = false;

    // Exclusivity (DEF-2c PR-3, NC-2c-4): SCOPE-CORRECT alias map. `alias_origin` is a
    // flat tracker field — UNLIKE the per-block-cloned `env`/`mutables` — and aliasing is
    // NON-MONOTONE under shadowing: an inner-block `let x = <fresh>` REMOVES the outer
    // `x`'s alias, an inner `let x = <outer place>` ADDS one. Either mutation must not
    // leak past this block — a removed alias would MISS a later outer-scope conflict
    // (under-reject = UNSOUND), an added one would SPURIOUSLY fire (over-reject). So
    // snapshot on entry and restore on exit: the block-scope analogue of the cloned `env`.
    // (`readonly_locals` needs no such restore — it is append-only/monotone, so a leaked
    // readonly is only ever more conservative.) For a flat (no-nested-block) block the
    // restore returns the map to a value an outer statement already holds, so single-block
    // behavior — and thus byte-identity — is unchanged; the fix engages only when a nested
    // block shadowed an outer binding.
    let saved_alias_origin = tracker.alias_origin.clone();

    for statement in &block.statements {
        let (typed_stmt, stmt_guaranteed_return) = match statement {
            Stmt::Let(stmt) => {
                let typed = check_let(stmt, env, expected_return, context, tracker, diagnostics);
                // Actor-state (M2, N006): a `let` may not shadow a state field —
                // otherwise a bare name would ambiguously denote the local or the
                // field, and `StateField` membership would be wrong for reads after
                // the binding. Reject (fail-closed), mirroring the param-shadow rule
                // (N006) so state references stay unambiguous.
                if tracker.state_fields.contains_key(&typed.name) {
                    diagnostics.push(Diagnostic::error(
                        codes::N006,
                        format!(
                            "binding `{}` shadows an actor state field; rename it to \
                             keep state references unambiguous",
                            typed.name
                        ),
                        Some(stmt.span),
                    ));
                }
                if typed.mutable {
                    mutables.insert(typed.name.clone());
                }
                // Mutation-as-capability (PR-1, NC-1): readonly PROPAGATION. A
                // `let b = <value rooted in a @ReadOnly local>` makes `b` readonly
                // too, so a later `b.x = …` is caught by the WRITE gate — the fix
                // for the one-line `let b = p; b.x = 10` launder. Append-only.
                //
                // AGG-4 (aggregate-state hardening): the SAME propagation for a `let`
                // bound to an aliasable value rooted in a NON-`mut` state aggregate.
                // Records/arrays are reference-semantic, so `let e = d; e.f = x` (d a
                // non-`mut` state field) would MUTATE the immutable state through the
                // alias — a T123 launder the direct `d.f = x` gate misses (its root is
                // the local `e`, not a StateField). Marking `e` readonly routes the
                // aliased write to the T251 gate and an aliased `@Mut` method call
                // (`e.push(x)`) to the T253 receiver gate. Guarded to `mut`-EXEMPT
                // fields (a `mut` aggregate alias-write is the intended AGG-2a path)
                // and to handlers (`init` legitimately constructs state in place).
                //
                // AGG2b-4 (HOLE-DANGLE): the `mut`-exempt clause above lets a
                // `let e = v` alias of a `mut` FLAT aggregate mutate in place
                // (the AGG-2a path). But a `mut Vec<scalar>` state field GROWS:
                // `e.push(x)` on the alias roots the receiver at the LOCAL `e`, so
                // the AGG2b-2 `$state` routing (keyed on a StateField root) MISSES
                // it — the grow reallocs `v`'s buffer into the TRANSIENT arena via
                // the shared `push`, and the AL-2 reset then reclaims it → the
                // state Vec DANGLES. Fail-closed: mark an alias of a `mut` state
                // `Vec<scalar>` readonly too, so `e.push(x)` (`@Mut self`) is
                // rejected by the T253 receiver gate. Reads (`e.get`, `@ReadOnly
                // self`) stay legal; the user grows the field DIRECTLY (`v.push`,
                // which routes to `$state`). Scoped to `Vec<scalar>` (the grow-able
                // shape) so a `mut` flat-aggregate alias-write stays the AGG-2a
                // path, and to non-`init` handlers.
                if place_root_local(&typed.value)
                    .is_some_and(|root| tracker.readonly_locals.contains(root))
                    || (tracker.body_kind != BodyKind::Init
                        && is_aliasable_type(&typed.value.ty)
                        && place_root_statefield(&typed.value)
                            .is_some_and(|root| !tracker.mut_state_fields.contains(root)))
                    || (tracker.body_kind != BodyKind::Init
                        && (super::universe::is_persistable_scalar_vec(&typed.value.ty, universe)
                            // PPS-0: the same HOLE-DANGLE reasoning for a `mut
                            // Map<scalar, scalar>` state field. An aliased `insert`
                            // roots at the LOCAL, so the state-backed routing misses
                            // it and every interior realloc (buckets, keys, vals) goes
                            // to the transient arena → the map dangles after the
                            // reset. Mark the alias readonly so the `@Mut insert` hits
                            // the T253 receiver gate; reads through the alias stay
                            // legal, and the DIRECT `m.insert(...)` path is untouched.
                            || super::universe::is_persistable_scalar_map(&typed.value.ty, universe))
                        && place_root_statefield(&typed.value)
                            .is_some_and(|root| tracker.mut_state_fields.contains(root)))
                {
                    tracker.readonly_locals.insert(typed.name.clone());
                }
                // Regions (DEF-2a NC-R3 + DEF-2b LD-6): record the bound local's region.
                // A `Lexical` region (DEF-2a) is meaningful only INSIDE a region — an
                // alias of an outer value inherits the OUTER depth (so it can still
                // escape); a fresh in-region allocation is born at the current depth;
                // pruned on region exit (NC-R5). A `Param` region (DEF-2b) is recorded at
                // ANY depth — even at function scope — so a callee cannot launder its
                // `@in r` parameter past `r` via a plain copy (`let b = d; return b`); the
                // region analogue of the `@ReadOnly` `let b = p` propagation above. Global
                // records nothing. A no-op without region params (no `Param` ever arises)
                // → byte-identical for all DEF-2a and pre-region code.
                match region_of_value(&typed.value, tracker) {
                    bd @ RegionId::Lexical(_) if tracker.current_region_depth > 0 => {
                        tracker.region_locals.insert(typed.name.clone(), bd);
                    }
                    bd @ RegionId::Param(_) => {
                        tracker.region_locals.insert(typed.name.clone(), bd);
                    }
                    _ => {}
                }
                // Exclusivity (DEF-2c, LD-1 / NC-2c-4): write-per-`let` alias-origin. A
                // `let b = <aliasable PLACE>` records the root `b` aliases (resolved
                // transitively, so a 2-hop `let z=y; let y=x` chains to `x`); ANY other RHS
                // (fresh construct / call result / scalar) makes `b` its OWN root, so a
                // re-binding clears a stale alias rather than inheriting it (aliasing is
                // non-monotone under shadowing — UNLIKE the append-only `readonly_locals`).
                // Read by the exclusivity gate (PR-1); inert here (populated, unread) →
                // byte-identical.
                if is_aliasable_type(&typed.value.ty)
                    && let Some(root) = place_root_local(&typed.value)
                {
                    let origin = resolve_alias_root(root, &tracker.alias_origin).to_string();
                    tracker.alias_origin.insert(typed.name.clone(), origin);
                } else {
                    tracker.alias_origin.remove(&typed.name);
                }
                (TypedStmt::Let(typed), false)
            }
            Stmt::LetTuple(stmt) => {
                // Tuple destructuring. Infer the RHS once to validate it is a
                // tuple of matching arity; on ANY mismatch emit T261 and bind the
                // names to Error — NEVER build a field-access on a non-tuple
                // (ET-4). On success, desugar into `let $tup = value; let a =
                // $tup.0; …` and check it in THIS scope so `a`/`b` persist (the
                // `$tup` temp persists too but is `$`-hygienic + unobservable,
                // ET-7). The value is bound to one temp → evaluated once (ET-3).
                let value = infer_expr(
                    &stmt.value,
                    env,
                    expected_return,
                    context,
                    tracker,
                    diagnostics,
                );
                // Optional `: (A, B)` annotation — cross-checked against the value.
                if let Some(annotation) = &stmt.ty {
                    let ann_ty = resolve_type_expr(annotation, universe, &HashMap::new(), &[]);
                    if !matches!(value.ty, Type::Error) && !type_compatible(&ann_ty, &value.ty) {
                        diagnostics.push(Diagnostic::error(
                            codes::T261,
                            format!(
                                "tuple `let` is annotated `{}` but the value has type `{}`",
                                render_type(&ann_ty),
                                render_type(&value.ty)
                            ),
                            Some(stmt.span),
                        ));
                    }
                }
                let arity_ok = match &value.ty {
                    Type::Tuple(elems) if elems.len() == stmt.bindings.len() => true,
                    Type::Tuple(elems) => {
                        diagnostics.push(Diagnostic::error(
                            codes::T261,
                            format!(
                                "this `let` binds {} names, but the value is a {}-tuple — the counts must match",
                                stmt.bindings.len(),
                                elems.len()
                            ),
                            Some(stmt.span),
                        ));
                        false
                    }
                    // Already errored upstream — stay quiet (no cascade).
                    Type::Error => false,
                    other => {
                        diagnostics.push(Diagnostic::error(
                            codes::T261,
                            format!(
                                "cannot destructure a value of type `{}` with a tuple pattern `let (..)`; only a tuple can be destructured",
                                render_type(other)
                            ),
                            Some(stmt.value.span()),
                        ));
                        false
                    }
                };
                if arity_ok {
                    let desugar = build_let_tuple_desugar(stmt);
                    let typed = check_block(
                        &desugar,
                        env,
                        mutables,
                        expected_return,
                        context,
                        tracker,
                        diagnostics,
                        false,
                    );
                    statements.extend(typed.statements);
                } else {
                    // ET-4: emit NO field-extraction desugar; bind each name to
                    // Error so a later use doesn't cascade into "unknown name".
                    for (name, _) in &stmt.bindings {
                        env.insert(name.clone(), Type::Error);
                    }
                }
                continue;
            }
            Stmt::Assign(stmt) => {
                let typed = check_assign(
                    stmt,
                    env,
                    mutables,
                    expected_return,
                    context,
                    tracker,
                    diagnostics,
                );
                (TypedStmt::Assign(typed), false)
            }
            Stmt::Expr(stmt) => {
                let typed =
                    check_expr_stmt(stmt, env, expected_return, context, tracker, diagnostics);
                // Sound divergence (Tier A): a statement whose expression type is
                // the bottom type `Never` (e.g. `trap()`, an abortive `perform`)
                // terminates its path. The return checker reads the TYPE, never the
                // syntax (SC-1) — reusing the existing guaranteed-return
                // accumulate / break / T044-suppression machinery below.
                let diverges = matches!(typed.expr.ty, Type::Never);
                (TypedStmt::Expr(typed), diverges)
            }
            Stmt::If(stmt) => {
                let (typed, branch_returns) = check_if(
                    stmt,
                    env,
                    mutables,
                    expected_return,
                    context,
                    tracker,
                    diagnostics,
                );
                (TypedStmt::If(typed), branch_returns)
            }
            Stmt::Match(stmt) => {
                let (typed, branch_returns) = check_match(
                    stmt,
                    env,
                    mutables,
                    expected_return,
                    context,
                    tracker,
                    diagnostics,
                );
                (TypedStmt::Match(typed), branch_returns)
            }
            Stmt::While(stmt) => {
                let typed = check_while(
                    stmt,
                    env,
                    mutables,
                    expected_return,
                    context,
                    tracker,
                    diagnostics,
                );
                (TypedStmt::While(typed), false)
            }
            Stmt::Return(stmt) => {
                let typed = check_return(stmt, expected_return, env, context, tracker, diagnostics);
                (TypedStmt::Return(typed), true)
            }
            Stmt::Break(span) => {
                if tracker.loop_depth == 0 {
                    diagnostics.push(Diagnostic::error(
                        codes::T260,
                        "`break` outside a loop".to_string(),
                        Some(*span),
                    ));
                }
                (TypedStmt::Break(*span), false)
            }
            Stmt::Continue(span) => {
                if tracker.loop_depth == 0 {
                    diagnostics.push(Diagnostic::error(
                        codes::T260,
                        "`continue` outside a loop".to_string(),
                        Some(*span),
                    ));
                }
                (TypedStmt::Continue(*span), false)
            }
            Stmt::ForIn(stmt) => {
                let iterable = infer_expr(
                    &stmt.iterable,
                    env,
                    expected_return,
                    context,
                    tracker,
                    diagnostics,
                );
                let elem_type = match &iterable.ty {
                    Type::Array { elem, .. } => (**elem).clone(),
                    // Iterator path (lean structural protocol): a `Named` type whose
                    // `next` is a valid iterator shape (`next(self @Mut) -> Option<T>`).
                    // `for x in it` desugars to a `while`+`match` over `it.next()`,
                    // reusing all existing lowering — no AIR change, no `break`.
                    Type::Named(type_name, _) => {
                        match iterator_next_sig(type_name, function_sigs, module_name, tracker) {
                            Some(sig) if is_iterator_next_shape(&sig) => {
                                // Check the untyped desugar in a CHILD scope so the
                                // synthetic `$for_*` temps + the loop var never leak,
                                // then splice the typed statements directly into this
                                // block. `check_block` handles all of `$it`'s bookkeeping
                                // (mutables / readonly / region / alias) — ET-6 / ET-10.
                                // A `for` never guarantees return, so no
                                // `guaranteed_return` update — identical to the array
                                // path (ET-6).
                                let desugar = build_iterator_desugar(stmt);
                                let mut it_env = env.clone();
                                let mut it_mutables = mutables.clone();
                                let typed = check_block(
                                    &desugar,
                                    &mut it_env,
                                    &mut it_mutables,
                                    expected_return,
                                    context,
                                    tracker,
                                    diagnostics,
                                    false,
                                );
                                statements.extend(typed.statements);
                                continue;
                            }
                            // ET-1 fail-fast: a `next` of the WRONG shape — reject AT the
                            // loop (abort-before-AIR), never fall through to the array
                            // path or silently iterate.
                            Some(_) => {
                                diagnostics.push(Diagnostic::error(
                                    codes::T259,
                                    format!(
                                        "`for-in` over `{type_name}` requires `next(self @Mut) -> Option<T>`; its `next` has the wrong shape"
                                    ),
                                    Some(stmt.iterable.span()),
                                ));
                                Type::Error
                            }
                            // No `next` at all → not an iterator. Byte-identical to the
                            // pre-iterator `other` arm (same T052 text for any `Named`).
                            None => {
                                diagnostics.push(Diagnostic::error(
                                    codes::T052,
                                    format!(
                                        "`for-in` requires an array, found `{}`",
                                        render_type(&iterable.ty)
                                    ),
                                    Some(stmt.iterable.span()),
                                ));
                                Type::Error
                            }
                        }
                    }
                    Type::Error => Type::Error,
                    other => {
                        diagnostics.push(Diagnostic::error(
                            codes::T052,
                            format!("`for-in` requires an array, found `{}`", render_type(other)),
                            Some(stmt.iterable.span()),
                        ));
                        Type::Error
                    }
                };
                let mut body_env = env.clone();
                body_env.insert(stmt.var.clone(), elem_type.clone());
                let mut body_mutables = mutables.clone();
                // break/continue: the array-path body is one loop level deeper. (The
                // iterator path desugars to a `while`, which increments via check_while.)
                tracker.loop_depth += 1;
                let body = check_block(
                    &stmt.body,
                    &mut body_env,
                    &mut body_mutables,
                    expected_return,
                    context,
                    tracker,
                    diagnostics,
                    false,
                );
                tracker.loop_depth -= 1;
                (
                    TypedStmt::ForIn(TypedForInStmt {
                        var: stmt.var.clone(),
                        elem_type,
                        iterable,
                        body: body.statements,
                    }),
                    false,
                )
            }
            Stmt::ForRange(stmt) => {
                // `for v in a..b { … }` — the exclusive i64 range loop. Bounds are
                // inferred in the OUTER env (the loop var is not in scope in its own
                // bounds) and each evaluated exactly once (the AIR arm hoists them
                // into the loop pre-header). Both must be `i64` (T280); integer
                // literals narrow via PIL so no `IntLit` leaks to AIR.
                let mut range_start = infer_expr(
                    &stmt.start,
                    env,
                    expected_return,
                    context,
                    tracker,
                    diagnostics,
                );
                resolve_int_literals_or_reject(
                    &mut range_start,
                    &Type::I64,
                    codes::T280,
                    diagnostics,
                );
                let mut range_end = infer_expr(
                    &stmt.end,
                    env,
                    expected_return,
                    context,
                    tracker,
                    diagnostics,
                );
                // RF-M2 (UP-LENGTH): `arr.len()` types as `u32`, which would
                // T280-reject the feature's own HEADLINE input
                // (`for i in 0..a.len() { a[i] }`). When the end is the
                // `ArrayLen { size }` intrinsic on a BARE LOCAL receiver,
                // substitute the STATIC size as an `i64` literal: SC-4/T227
                // guarantee allocation-len == N for every `[T; N]` value, so
                // the bound IS the constant - and the loop header now compares
                // against a literal instead of re-loading the length. The
                // bare-Local gate keeps the substitution effect-free (a
                // computed receiver like `f().len()` is NOT dropped - it stays
                // `u32` and rejects T280, loud).
                if let TypedExprKind::Intrinsic(intr) = &range_end.kind
                    && let crate::typed_ast::TypedIntrinsicKind::ArrayLen { size } = &intr.kind
                    && matches!(
                        intr.args.first().map(|r| &r.kind),
                        Some(TypedExprKind::Local(_))
                    )
                {
                    range_end = TypedExpr {
                        ty: Type::I64,
                        kind: TypedExprKind::Literal(Literal::Int(i64::from(*size))),
                        span: range_end.span,
                        refinement: None,
                    };
                }
                resolve_int_literals_or_reject(
                    &mut range_end,
                    &Type::I64,
                    codes::T280,
                    diagnostics,
                );
                for (label, bound, span) in [
                    ("start", &range_start, stmt.start.span()),
                    ("end", &range_end, stmt.end.span()),
                ] {
                    if !matches!(bound.ty, Type::I64 | Type::Error) {
                        diagnostics.push(Diagnostic::error(
                            codes::T280,
                            format!(
                                "range-for {label} bound must be `i64`, found `{}`",
                                render_type(&bound.ty)
                            ),
                            Some(span),
                        ));
                    }
                }
                // Bind the loop var `i64` IMMUTABLY: into the body env only, NEVER
                // into `mutables` — so `v = …` in the body is a hard T042 (the same
                // discipline as ForIn's element var). This immutability is
                // load-bearing: it is what later makes the range a trustworthy
                // compile-time bounds fact for `arr[v]` elision, with no flow
                // tracking (errors abort before AIR).
                let mut body_env = env.clone();
                body_env.insert(stmt.var.clone(), Type::I64);
                let mut body_mutables = mutables.clone();
                // RF-M2: the Z3-FREE bounds fact. Push `v in [0, K)` onto the
                // mutation/shadow-proof channel IFF every gate holds:
                //   * start is the surface literal `0` (v1.1 may widen to any
                //     literal `>= 0` - a one-line change);
                //   * K resolves from the TYPED end - a literal, or the
                //     `ArrayLen { size }` intrinsic (`arr.len()` on `[T; N]`,
                //     whose size comes from the receiver's STATIC type - the
                //     same SC-4/T227 anchor as the literal-index elision);
                //   * K >= 1 (an empty loop makes no claims);
                //   * the body pre-scan finds NO rebinding of `v` (any
                //     rebinding anywhere refuses the WHOLE loop's fact).
                // The same-gated FRESH frame on `pattern_refinement_stack`
                // feeds the diagnostics tier (return/param refinement
                // discharge) - gating it on the pre-scan keeps a shadowed
                // binding from consulting a stale frame (the V4-W4S10 class).
                let range_k = resolve_range_fact_end(&range_end);
                let fact_ok = matches!(&range_start.kind, TypedExprKind::Literal(Literal::Int(0)))
                    && range_k.is_some_and(|k| k >= 1)
                    && !body_rebinds_name(&stmt.body, &stmt.var);
                let mut pushed_fact = false;
                if fact_ok && let Some(k) = range_k {
                    tracker.range_loop_facts.push(RangeLoopFact {
                        var: stmt.var.clone(),
                        lo: 0,
                        hi_exclusive: k,
                    });
                    let mut frame: HashMap<String, Vec<RefinementClause>> = HashMap::new();
                    frame.insert(
                        stmt.var.clone(),
                        vec![
                            RefinementClause {
                                field: stmt.var.clone(),
                                op: RefinementOp::Ge,
                                rhs: RefinementRhs::Literal(0),
                                span: stmt.span,
                            },
                            RefinementClause {
                                field: stmt.var.clone(),
                                op: RefinementOp::Lt,
                                rhs: RefinementRhs::Literal(k),
                                span: stmt.span,
                            },
                        ],
                    );
                    tracker.pattern_refinement_stack.push(frame);
                    pushed_fact = true;
                }
                tracker.loop_depth += 1;
                let body = check_block(
                    &stmt.body,
                    &mut body_env,
                    &mut body_mutables,
                    expected_return,
                    context,
                    tracker,
                    diagnostics,
                    false,
                );
                tracker.loop_depth -= 1;
                if pushed_fact {
                    tracker.range_loop_facts.pop();
                    tracker.pattern_refinement_stack.pop();
                }
                (
                    TypedStmt::ForRange(TypedForRangeStmt {
                        var: stmt.var.clone(),
                        start: range_start,
                        end: range_end,
                        body: body.statements,
                        span: stmt.span,
                    }),
                    false,
                )
            }
        };

        statements.push(typed_stmt);

        if stmt_guaranteed_return {
            guaranteed_return = true;
            break;
        }
    }

    if enforce_full_return && !guaranteed_return {
        diagnostics.push(Diagnostic::error(
            codes::T044,
            format!(
                "missing return value for function returning `{}`",
                render_type(expected_return)
            ),
            Some(block.span),
        ));
    }

    // PR-3: restore the alias map to its pre-block state — block-local `let` aliases go
    // out of scope, and any outer binding this block shadowed is reinstated (NC-2c-4).
    tracker.alias_origin = saved_alias_origin;

    TypedBlock {
        statements,
        span: block.span,
        guaranteed_return,
    }
}

pub(super) fn check_let(
    stmt: &LetStmt,
    env: &mut HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedLetStmt {
    let universe = context.universe;
    // PR A / N15-PRA: thread the let's type annotation as the expected
    // type for the value expression. `infer_record_construct_expr`
    // reads `tracker.current_expected_type` to seed its substitution
    // map from annotation type-args before field-value inference.
    // RAII guard restores the prior expected_type on drop, so nested
    // let bindings + sibling lets don't leak context.
    let expected_for_value = stmt
        .ty
        .as_ref()
        .map(|annotation| resolve_type_expr(annotation, universe, &HashMap::new(), &[]));
    let value = {
        let mut guard = ExpectedTypeGuard::push(tracker, expected_for_value);
        infer_expr(
            &stmt.value,
            env,
            current_return,
            context,
            guard.tracker_mut(),
            diagnostics,
        )
    };
    let mut ty = stmt.ty.as_ref().map_or_else(
        || value.ty.clone(),
        |annotation| {
            resolve_annotated_let_type(&stmt.name, annotation, &value.ty, universe, diagnostics)
        },
    );

    // PIL: integer literal resolution at let-binding site. The
    // value's TypedExpr may carry `Type::IntLit(n)` at the top AND at
    // operand leaves (e.g., `let x: u32 = 1 + 2;`). The PR S1 follow-up
    // `coerce_int_literal` helper handled the top-level case via
    // post-failure mutation; PIL replaces it with the walker which
    // unifies via `type_compatible` first (succeeds for any IntLit that
    // fits the target) and then propagates the target into binop
    // operands recursively per N17-PIL. Range-check failure surfaces
    // through type_compatible (returning false), AND the walker also
    // performs per-leaf range-check (N20-PIL) so a single leaf failure
    // in a binop emits T243 at the offending leaf's span.
    let mut value = value;
    if type_compatible(&ty, &value.ty) {
        // Even when type_compatible passes, IntLit leaves still need
        // rewriting so AIR's lower_type doesn't ICE. The walker also
        // surfaces a range-fit failure for a non-top-level leaf
        // (e.g., `let n: i32 = 0 - 2147483648` — top-level IntLit(0)
        // fits i32 but leaf IntLit(2147483648) doesn't); without
        // rejecting it the leaf defaults to i64 and AIR emits a
        // width-mismatched `i32.sub` (INVALID wasm). Report it as T041
        // (the let-binding mismatch code), same as the single-literal
        // `let n: i32 = 2147483648` overflow.
        resolve_int_literals_or_reject(&mut value, &ty, codes::T041, diagnostics);
    }

    if !type_compatible(&ty, &value.ty) {
        let site_ctx = format!("let-binding `{}`", stmt.name);
        if let Some(t195) =
            try_cap_deadline_diagnostic(&ty, &value.ty, &stmt.name, &site_ctx, stmt.span)
        {
            diagnostics.push(t195);
        } else if let Some(t227) =
            try_array_size_mismatch_diagnostic(&ty, &value.ty, &site_ctx, stmt.span)
        {
            diagnostics.push(t227);
        } else {
            diagnostics.push(Diagnostic::error(
                codes::T041,
                format!(
                    "let binding `{}` expected type `{}`, found `{}`",
                    stmt.name,
                    render_type(&ty),
                    render_type(&value.ty)
                ),
                Some(stmt.span),
            ));
        }
    }

    // F003 / value-position `trap()` (Tier A): a `let` cannot bind a DIVERGING
    // value. A bare `let x = trap()` (no annotation) reaches here with `ty` ==
    // the RHS's `Never` — the only inference position where an un-rejected `never`
    // survives to the binding. Reject it (T279) and POISON the binding to
    // `Type::Error`: `never` is legal only as a bare `trap();` STATEMENT, and a
    // residual `Never` reaching AIR's `lower_type` (or a later type-check-time
    // `mangle_type` if the binding is passed on) ICEs at the C-NEVER backstop.
    // An ANNOTATED clash (`let x: i64 = trap()`) already fired T041 above and
    // leaves `ty == i64`, so `type_contains_never` is false and this does NOT
    // double-diagnose it.
    if type_contains_never(&ty) {
        diagnostics.push(Diagnostic::error(
            codes::T279,
            format!(
                "cannot bind the diverging value `{}` to `{}`: `trap()` has type `never` \
                 (the bottom type) and produces no value. Use `trap();` as a standalone \
                 statement for its divergence instead of binding it.",
                render_type(&value.ty),
                stmt.name,
            ),
            Some(stmt.span),
        ));
        // Error is cascade-suppressing and lowers/mangles cleanly, so no
        // downstream use of `x` re-reports or ICEs.
        ty = Type::Error;
    }

    env.insert(stmt.name.clone(), ty.clone());

    // Wall 4 Step 7 / N38-S7 (CRITICAL): if the RHS expression carries a
    // preserved refinement (e.g., it's a call to a fn with a declared
    // `return_refinement`, or a field-read from a refined record), push
    // that refinement into the current `pattern_refinement_stack` frame
    // keyed by the bound name. Subsequent reads of `n` via
    // `infer_path_expr` then attach the refinement via Step 6's
    // `lookup_pattern_refinement` mechanism.
    //
    // Without this, the cross-function flow
    //   let n: i64 = make_positive();   // n's refinement: @ > 0
    //   validate(n);                     // validate: where x > 0
    // silently fires T211 because the let-binding drops the refinement.
    // This is the load-bearing Step 7 mechanism that closes the
    // adversarial-round-2 UP-S7-I gap. Step 2's preservation modifies
    // only `infer_field_access_expr`; Step 7 extends to let bindings.
    //
    // Per N22-S7-equivalent semantics: reassignments overwrite the
    // frame entry (`frame.insert(...)` last-write-wins). If no frame
    // is on the stack (we're at module top-level or outside any
    // function body), the push is silently a no-op — Step 7 admits
    // refinement only inside fn bodies / actor handlers where the
    // stack has been initialized by `check_function_block`.
    if let Some(ref refinement_clauses) = value.refinement
        && let Some(frame) = tracker.pattern_refinement_stack.last_mut()
    {
        frame.insert(stmt.name.clone(), refinement_clauses.clone());
    }

    TypedLetStmt {
        name: stmt.name.clone(),
        mutable: stmt.mutable,
        ty,
        taint: stmt.taint,
        value,
        span: stmt.span,
    }
}

pub(super) fn check_assign(
    stmt: &crate::ast::AssignStmt,
    env: &HashMap<String, Type>,
    mutables: &HashSet<String>,
    expected_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedAssignStmt {
    let universe = context.universe;
    // Resolve the place (lvalue) by inferring the target expression. This
    // reuses the full expression machinery: a bare local infers to
    // `Local`, a dotted path `a.b.c` to a nested `FieldAccess`, and
    // `arr[i]` to `Index` — so field/index type resolution, generic
    // substitution, and undefined-variable diagnostics all come for free.
    let place = infer_expr(
        &stmt.target,
        env,
        expected_return,
        context,
        tracker,
        diagnostics,
    );

    // When the place itself failed to resolve, a more specific diagnostic
    // already fired; suppress the follow-on checks to report once.
    let place_ok = !matches!(place.ty, Type::Error);

    // NC3 / T243: strict lvalue whitelist. A place is exactly a local, a
    // record field, or an array/slice element — nothing else denotes
    // storage. This whitelist is what makes "lower the base to its
    // container pointer" sound in AIR (every accepted form has an
    // address; no other form does).
    let is_place = matches!(
        place.kind,
        TypedExprKind::Local(_)
            | TypedExprKind::StateField(_)
            | TypedExprKind::FieldAccess(_)
            | TypedExprKind::Index(_)
    );
    if !is_place && place_ok {
        diagnostics.push(Diagnostic::error(
            codes::T243,
            "invalid assignment target: the left side of `=` must be a variable, a field \
             (`r.f`), or an array/slice element (`arr[i]`)"
                .to_string(),
            Some(stmt.span),
        ));
    }

    // Actor-state (M2): a `StateField` place is writable ONLY in `init` — the
    // sole construction-phase write site. In any handler it is rejected (T123):
    // state is immutable after `init`. In `init` the write intentionally bypasses
    // the T042 rebind gate (state fields are not `let mut` locals) and the T043
    // linearity gate (storing an owned cap INTO state is the sanctioned init
    // move, not a stray reassignment of a cap-bearing place). Definite-assignment
    // — exactly one unconditional top-level init write per field (T124/T125) — is
    // a follow-up milestone that lands with the empty-init fixture migration.
    let is_state_place = matches!(&place.kind, TypedExprKind::StateField(_));
    if place_ok
        && let TypedExprKind::StateField(name) = &place.kind
        && tracker.body_kind != BodyKind::Init
        // MUTABLE-STATE S2 / the relax: a handler write is PERMITTED iff the target
        // field is declared `mut` (F1 guarantees a `mut` field is plain reassignable
        // data — no cap/ref to leak). A NON-`mut` field stays immutable-after-init.
        && !tracker.mut_state_fields.contains(name)
    {
        diagnostics.push(Diagnostic::error(
            codes::T123,
            format!(
                "cannot assign to actor state field `{name}` in a handler; \
                 state is immutable after `init` (declare it `mut`, or assign it once in `init`)"
            ),
            Some(stmt.span),
        ));
    }
    // MUTABLE-STATE S3 fix: a write-THROUGH into a state field's interior — `d.f = …`,
    // `a[i] = …`, a projected place whose ROOT is a state field — is a handler-time
    // mutation of state exactly like a bare reassign, so it is immutable-after-init too
    // (T123) UNLESS the root field is declared `mut`. Without this the bare-`StateField`
    // gate above missed it, and `d.v = x` on a NON-`mut` record/array field silently
    // mutated immutable state (the F1 conservation claim). In `init` (construction) a
    // write-through stays permitted. A genuine LOCAL write-through is a different place
    // root (handled by the T042/T251/@ReadOnly gates below), so this is StateField-only.
    if place_ok
        && tracker.body_kind != BodyKind::Init
        && matches!(
            place.kind,
            TypedExprKind::FieldAccess(_) | TypedExprKind::Index(_)
        )
        && let Some(root) = place_root_statefield(&place)
        && !tracker.mut_state_fields.contains(root)
    {
        diagnostics.push(Diagnostic::error(
            codes::T123,
            format!(
                "cannot assign through actor state field `{root}` in a handler; state is \
                 immutable after `init` (declare it `mut`, or assign it once in `init`)"
            ),
            Some(stmt.span),
        ));
    }
    // AGG-2a: a `mut` FLAT-FIXED aggregate state field (a record/array/tuple of scalars) persists
    // when mutated IN PLACE (`d.f = …`, `a[i] = …` StoreField into the init-allocated persistent
    // object). A WHOLESALE reassignment in a handler (`d = <construct>`) stores a pointer to an
    // object built in the per-dispatch scratch, which the reset reclaims.
    //
    // PPS-1 lifts that for the shapes the PROMOTION primitive covers: a flat fixed aggregate
    // write in a handler is lowered as allocate-persistent + field copy (`air::
    // maybe_promote_aggregate`), so the stored pointer addresses a persistent copy. Note the
    // semantics that buys: promotion COPIES, so the transient original keeps its own identity
    // and storing one value into two fields promotes twice.
    //
    // Everything promotion does NOT yet reach — pointer-bearing aggregates (a record holding a
    // `Vec`/`str`/nested record), whose promotion must be transitive (PPS-2/3) — stays rejected
    // (T128). (A scalar `mut` field was always reassignable: its value is inline in the state
    // slot, not a pointer.)
    if place_ok
        && tracker.body_kind != BodyKind::Init
        && let TypedExprKind::StateField(name) = &place.kind
        && tracker.mut_state_fields.contains(name)
        && !super::universe::is_inline_scalar(&place.ty)
        && !super::universe::is_flat_scalar_aggregate(&place.ty, universe)
        // PPS-2a: `str` is immutable, so wholesale replacement is its ONLY update form — and
        // the store promotes payload + header, so the replacement persists.
        && !matches!(place.ty, Type::Str)
    {
        diagnostics.push(Diagnostic::error(
            codes::T128,
            format!(
                "cannot reassign the whole `mut` aggregate state field `{name}` in a handler; \
                 mutate it in place (`{name}.field = …` or `{name}[i] = …`). This shape holds \
                 pointers, so a wholesale reassignment would store an object whose interior \
                 lives in per-dispatch scratch that the arena reset reclaims. Flat aggregates \
                 (records/arrays/tuples of scalars) ARE reassignable — they are promoted into \
                 the persistent heap at the store — but pointer-bearing shapes await transitive \
                 promotion; assign those only in `init`."
            ),
            Some(stmt.span),
        ));
    }

    // T042 gates REBINDING, not mutation. `let mut` controls whether a
    // *name* may be re-pointed (`x = …`); it says nothing about writing
    // *through* a name. SIGIL records and arrays are heap pointers with
    // reference semantics (`let b = a;` aliases the same header), so a
    // field/element store — `x.f = …`, `x[i] = …` — changes the pointed-to
    // heap content while the binding itself is unchanged. That is
    // write-through, not rebinding, so it is permitted regardless of `mut`.
    // Only a bare-local assignment (`x = …`), which re-points the name,
    // requires `let mut`. (Opt-in immutability — a function promising NOT to
    // mutate its argument — is the `@ReadOnly` annotation, enforced by the WRITE
    // gate below (T251): `@ReadOnly` gates mutation THROUGH a place, `mut` gates
    // rebinding the name.)
    if place_ok
        && let TypedExprKind::Local(name) = &place.kind
        && !mutables.contains(name)
    {
        diagnostics.push(Diagnostic::error(
            codes::T042,
            format!("cannot assign to immutable variable `{name}`; declare with `let mut`"),
            Some(stmt.span),
        ));
    }

    // Mutation-as-capability (PR-1, NC-2): the WRITE gate. A write-THROUGH to a
    // place rooted in a `@ReadOnly` value — `p.x = …`, `p[i] = …`, or ANY
    // compound assignment (the gate never reads `stmt.op`) — is forbidden. A
    // bare-local rebinding (`p = …`) is the T042 path above, not a write-through,
    // so this arm fires only for `FieldAccess`/`Index`. Fail-closed: `place` is
    // the T243-whitelisted set and `place_root_local` is total over it.
    if place_ok
        && matches!(
            place.kind,
            TypedExprKind::FieldAccess(_) | TypedExprKind::Index(_)
        )
        && let Some(root) = place_root_local(&place)
        && tracker.readonly_locals.contains(root)
    {
        diagnostics.push(Diagnostic::error(
            codes::T251,
            format!(
                "cannot mutate `{}` through `{}`: `{root}` is `@ReadOnly` — this function \
                 promised not to mutate it. Drop `@ReadOnly`, or copy the value first.",
                root,
                render_place(&place)
            ),
            Some(stmt.span),
        ));
    }

    // NC4 / T043: linearity. Reassignment is permitted only for a place
    // whose type does not transitively own a capability or a borrow — the
    // same predicate locals use, now applied to the resolved place type so
    // cap/ref-bearing fields and elements are caught too. A `StateField` place
    // in `init` is exempt: writing an owned cap into state is the sanctioned
    // construction-phase move (the cap's linearity is still tracked at AIR by
    // `ownership::verify` via the init param's single move into the store).
    if place_ok && !is_state_place && !type_is_reassignable(&place.ty, universe) {
        let message = match classify_reassign_rejection(&place.ty, universe) {
            ReassignRejection::CapBearing => format!(
                "cannot assign to place of type `{}` — values carrying a capability are linear; consume the cap rather than store it",
                render_type(&place.ty)
            ),
            ReassignRejection::RefBearing => format!(
                "cannot assign to place of type `{}` — values holding a borrow are scope-tied; drop the borrow before reassigning",
                render_type(&place.ty)
            ),
            ReassignRejection::Other => format!(
                "cannot assign to place of type `{}` — this type is not yet reassignable",
                render_type(&place.ty)
            ),
        };
        diagnostics.push(Diagnostic::error(codes::T043, message, Some(stmt.span)));
    }

    let mut value = infer_expr(
        &stmt.value,
        env,
        expected_return,
        context,
        tracker,
        diagnostics,
    );

    // PIL: narrow IntLit leaves in the RHS to the place's type. check_assign
    // historically skipped this (unlike check_let), so a binary RHS to a
    // narrow-int place — even an IN-RANGE one like `n = 0 - 5` — kept its
    // operands as IntLit, which the end-of-typecheck mop-up defaulted to
    // i64; AIR then fed an i64 operand to an `i32.sub`, producing INVALID
    // wasm. Resolving here narrows both operands to the place type (valid
    // codegen) and rejects an out-of-range leaf (`n = 0 - 2147483648`) as
    // T045 — the assign mismatch code, same as the single-literal
    // `n = 2147483648` overflow. Guard mirrors the T045 check below:
    // only when the place resolved and the top-level types are compatible.
    if place_ok && !matches!(value.ty, Type::Error) && type_compatible(&place.ty, &value.ty) {
        resolve_int_literals_or_reject(&mut value, &place.ty, codes::T045, diagnostics);
    }

    // Value/place type compatibility. For compound `op=` on a field/index
    // place (`op` is `Some`), `value` is the right operand and the place's
    // own type is the left operand of a same-typed arithmetic op, so the
    // place-vs-value compatibility check is the right gate. (Local compound
    // was desugared to `x = x op rhs` at parse time, so it arrives here with
    // `op == None` and `value` already the full binary expression.)
    if place_ok && !matches!(value.ty, Type::Error) && !type_compatible(&place.ty, &value.ty) {
        let place_desc = render_place(&place);
        let site_ctx = format!("assignment to `{place_desc}`");
        if let Some(t195) =
            try_cap_deadline_diagnostic(&place.ty, &value.ty, &place_desc, &site_ctx, stmt.span)
        {
            diagnostics.push(t195);
        } else if let Some(t227) =
            try_array_size_mismatch_diagnostic(&place.ty, &value.ty, &site_ctx, stmt.span)
        {
            diagnostics.push(t227);
        } else {
            diagnostics.push(Diagnostic::error(
                codes::T045,
                format!(
                    "cannot assign `{}` to place of type `{}`",
                    render_type(&value.ty),
                    render_type(&place.ty)
                ),
                Some(stmt.span),
            ));
        }
    }

    // Mutation-as-capability (PR-2c, NC-1): the assignment-RHS escape sink. Storing
    // a value rooted in a `@ReadOnly` param into a place whose root is NOT readonly
    // (a mutable local/field/element) would create a mutable alias of the frozen
    // object — `q.x = p; q.x.y = 10` launders the write. Rejected with T253. The
    // dual case (LHS root IS readonly) is the WRITE gate's T251 above; this arm is
    // guarded on a non-readonly LHS root so exactly one error fires. A primitive-copy
    // RHS (`q.n = p.n`) is excluded by `is_aliasable_type` (Type::Error too, so an
    // already-mistyped RHS adds no T253 noise). `let b = p` does NOT reach here — it
    // is the SOLE propagate site (check_block), a binding rather than an assignment.
    let lhs_root_readonly =
        place_root_local(&place).is_some_and(|r| tracker.readonly_locals.contains(r));
    if place_ok
        && !lhs_root_readonly
        && is_aliasable_type(&value.ty)
        && let Some(rhs_root) = place_root_local(&value)
        && tracker.readonly_locals.contains(rhs_root)
    {
        diagnostics.push(Diagnostic::error(
            codes::T253,
            format!(
                "cannot store `@ReadOnly` value `{rhs_root}` into `{}`: that place is mutable, \
                 so the stored alias could be mutated, re-widening authority. Pass a copy.",
                render_place(&place)
            ),
            Some(stmt.span),
        ));
    }

    // Regions (DEF-2a, NC-R1): the assignment-RHS escape sink. Storing a value born
    // DEEPER (shorter-lived) than the LHS place would leave a dangling alias once the
    // deeper region is reclaimed — `region r { outer = Foo{} }` stores a region value
    // into a function-lifetime local. scope-depth = the LHS place-root's region depth.
    if place_ok {
        let lhs_region = place_root_local(&place)
            .and_then(|r| tracker.region_locals.get(r).copied())
            .unwrap_or(RegionId::Global);
        check_region_escape(
            &value,
            lhs_region,
            "be stored into a longer-lived place",
            tracker,
            diagnostics,
        );
    }

    TypedAssignStmt {
        place,
        op: stmt.op,
        value,
        span: stmt.span,
    }
}

/// Render a resolved place expression as a human-readable path for
/// diagnostics (`x`, `a.b.c`, `arr[…]`). Falls back to `<place>` for any
/// non-place kind — which only happens on an already-rejected target.
fn render_place(place: &TypedExpr) -> String {
    match &place.kind {
        TypedExprKind::Local(name) => name.clone(),
        TypedExprKind::FieldAccess(fa) => format!("{}.{}", render_place(&fa.object), fa.field),
        TypedExprKind::Index(ix) => format!("{}[…]", render_place(&ix.array)),
        _ => "<place>".to_string(),
    }
}

/// Walk a place/value expression down to its ROOT local binding. Total over the
/// T243-accepted place set (`Local`/`FieldAccess`/`Index`); `None` for any other
/// kind (a call result, literal, construction, …). Mirrors `render_place`'s
/// recursion. Used by the `@ReadOnly` WRITE gate (is this place rooted in a
/// readonly local?) and by `check_block`'s readonly-propagation (is this `let`
/// RHS rooted in a readonly local?).
pub(super) fn place_root_local(expr: &TypedExpr) -> Option<&str> {
    match &expr.kind {
        TypedExprKind::Local(name) => Some(name),
        TypedExprKind::FieldAccess(fa) => place_root_local(&fa.object),
        TypedExprKind::Index(ix) => place_root_local(&ix.array),
        _ => None,
    }
}

/// The name of the state field a place writes THROUGH (`d` for `d.f`, `a` for
/// `a[i]`), or `None` for a place not rooted in a state field. Mirrors
/// `place_root_local` for the `StateField` root; used by the write-through
/// immutability gate (a projected write into a non-`mut` state field is T123).
pub(super) fn place_root_statefield(expr: &TypedExpr) -> Option<&str> {
    match &expr.kind {
        TypedExprKind::StateField(name) => Some(name),
        TypedExprKind::FieldAccess(fa) => place_root_statefield(&fa.object),
        TypedExprKind::Index(ix) => place_root_statefield(&ix.array),
        _ => None,
    }
}

/// True iff a value of this type ALIASES heap state through which the underlying
/// object could be mutated — a record/enum/Vec/Map (`Named`), an array, a borrow
/// or slice, or an FFI pointer. Scalars (`i64`/`bool`/…), `str` (an immutable
/// view), `Unit`, and caps are COPIED/immutable, so returning or passing them
/// does NOT leak mutable access to a `@ReadOnly` object. Used by the escape gate
/// (PR-2) so `return p.x` (an i64 copy) stays legal while `return p` (a record
/// alias) is rejected.
pub(super) fn is_aliasable_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Named(_, _)
            | Type::Array { .. }
            | Type::Ref(_, _)
            | Type::Slice(_)
            | Type::Ptr(_)
            | Type::MutPtr(_)
            | Type::Generic(_)
            // Regions (DEF-2b, LD-3): a `Region` handle is escape-scored — it must not
            // outlive its own region (a handle to a reclaimed region would dangle).
            | Type::Region
    )
}

/// Exclusivity (DEF-2c, NC-2c-3): resolve a binding to the TERMINAL root of its alias chain —
/// the original binding whose heap object it ultimately aliases. Follows `alias_origin`
/// transitively (a 2-hop `let z=y; let y=x` resolves `z → x`). The map is acyclic by
/// construction (a `let` only ever points a NEW name at an EXISTING binding), so the walk
/// terminates; the loop bound (the map size) is a belt against a future bug — NEVER a hang.
pub(super) fn resolve_alias_root<'a>(
    mut name: &'a str,
    alias_origin: &'a HashMap<String, String>,
) -> &'a str {
    for _ in 0..=alias_origin.len() {
        match alias_origin.get(name) {
            Some(origin) => name = origin.as_str(),
            None => return name,
        }
    }
    debug_assert!(
        false,
        "ICE: alias_origin cycle while resolving `{name}` (NC-2c-3)"
    );
    name
}

/// Exclusivity (DEF-2c, the call-site gate — NC-2c-2/5/6): the conflicts in ONE call's
/// argument list — a value reaching a FROZEN parameter while an OVERLAPPING value reaches a
/// MUTABLE parameter, so the mutable handle could break the frozen view of the same object.
/// Frozen-ness is the PARAMETER's (`param_mutability.is_frozen(i)`; an absent/unknown slot is
/// MUTABLE — a frozen co-arg still conflicts, NC-2c-5); overlap is alias-resolved ROOT
/// equality (NC-2c-2 — field stores can make sibling paths alias, so same root is a potential
/// alias); an un-rooted argument (call result / construct / scalar) has no root and is a
/// distinct identity, matched against nothing (NC-2c-6). Returns `(shared root, the MUTABLE
/// argument's span)` per conflict, scanned in argument-index order (deterministic, NC-2c-7).
pub(super) fn exclusivity_partition(
    args: &[TypedExpr],
    param_mutability: &[crate::ast::Mutability],
    alias_origin: &HashMap<String, String>,
) -> Vec<(String, Span)> {
    let frozen = |i: usize| {
        param_mutability
            .get(i)
            .copied()
            .is_some_and(crate::ast::Mutability::is_frozen)
    };
    let mut conflicts = Vec::new();
    for (j, mut_arg) in args.iter().enumerate() {
        // `j` fills a MUTABLE parameter with an aliasable, rooted argument.
        if frozen(j) || !is_aliasable_type(&mut_arg.ty) {
            continue;
        }
        let Some(mut_root) = place_root_local(mut_arg) else {
            continue;
        };
        let mut_root = resolve_alias_root(mut_root, alias_origin);
        // … paired against ANY FROZEN-parameter argument resolving to the same root.
        for (i, frozen_arg) in args.iter().enumerate() {
            if i == j || !frozen(i) || !is_aliasable_type(&frozen_arg.ty) {
                continue;
            }
            if place_root_local(frozen_arg)
                .is_some_and(|r| resolve_alias_root(r, alias_origin) == mut_root)
            {
                conflicts.push((mut_root.to_string(), mut_arg.span));
                break;
            }
        }
    }
    conflicts
}

/// Resolve the region in which a value lives. Rooted places inherit their local or
/// parameter region. An unrooted aliasable value created inside a lexical region is
/// conservatively local to that region; scalars and other non-aliasable values are global.
pub(super) fn region_of_value(expr: &TypedExpr, tracker: &MonomorphTracker) -> RegionId {
    if let Some(root) = place_root_local(expr) {
        // A shadowing lexical local wins over a same-named parameter.
        if let Some(rid) = tracker.region_locals.get(root) {
            return *rid;
        }
        // A bare `Region` or `@in r` parameter denotes its seeded parameter region.
        if let Some(&slot) = tracker.current_param_regions.get(root) {
            return RegionId::Param(slot);
        }
        return RegionId::Global;
    }
    if tracker.current_region_depth > 0
        && (is_aliasable_type(&expr.ty) || str_value_is_region_born(expr))
    {
        return RegionId::Lexical(tracker.current_region_depth);
    }
    RegionId::Global
}

/// String literals live in static data; other string values created inside a region
/// may refer to region-allocated bytes and inherit that lifetime.
fn str_value_is_region_born(expr: &TypedExpr) -> bool {
    matches!(expr.ty, Type::Str) && !matches!(&expr.kind, TypedExprKind::Literal(Literal::Str(_)))
}

/// Return whether a direct `where region(a): region(b)` declaration relates two
/// distinct parameter regions. The language does not infer transitive edges.
pub(super) fn region_outlives_declared(
    value: RegionId,
    sink: RegionId,
    pairs: &[(u32, u32)],
) -> bool {
    matches!(
        (value, sink),
        (RegionId::Param(a), RegionId::Param(b)) if pairs.contains(&(a, b))
    )
}

pub(super) fn check_region_escape(
    operand: &TypedExpr,
    sink: RegionId,
    action: &str,
    tracker: &MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let bd = region_of_value(operand, tracker);
    if !(bd.outlives_or_equal(sink)
        || region_outlives_declared(bd, sink, &tracker.current_region_outlives))
    {
        diagnostics.push(Diagnostic::error(
            codes::T254,
            format!(
                "a value allocated inside a `region` block cannot {action}: the region's \
                 memory is reclaimed when the block exits, so the escaping reference would \
                 dangle. Keep its use inside the region, or copy a scalar out."
            ),
            Some(operand.span),
        ));
    }
}

/// Closed, CI-locked collection methods that keep their receiver in its region:
///
///   * the `@ReadOnly self` reads (`len`/`capacity`/`is_empty`/`get`/`get_or`/
///     `contains`) — already T253-escape-proven not to leak `self`; and
///   * the in-place mutators (`push`/`set`/`insert`) — which only APPEND their
///     value args into `self`'s own buffer and never store `self` (or a
///     longer-lived alias of it) anywhere outside the region.
///
/// Non-receiver arguments are still checked against the receiver's region. User code
/// crosses function boundaries through explicit `@in` contracts. A unit test pins the set.
pub(super) fn is_region_safe_stdlib_method(type_name: &str, method: &str) -> bool {
    matches!(
        (type_name, method),
        ("Vec", "len" | "capacity" | "get" | "push" | "set")
            | (
                "Map",
                "len" | "capacity" | "is_empty" | "get" | "get_or" | "contains" | "insert"
            )
    )
}

pub(super) fn check_expr_stmt(
    stmt: &ExprStmt,
    env: &HashMap<String, Type>,
    current_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExprStmt {
    let expr = infer_expr(
        &stmt.expr,
        env,
        current_return,
        context,
        tracker,
        diagnostics,
    );

    TypedExprStmt {
        expr,
        span: stmt.span,
    }
}

pub(super) fn resolve_annotated_let_type(
    binding_name: &str,
    annotation: &TypeExpr,
    fallback: &Type,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) -> Type {
    // PIL: skip the fast-path when fallback is `Type::IntLit(_)`. The
    // shortcut compares `annotation.display_name()` (string) to
    // `render_type(fallback)` (also a string), and PIL renders IntLit
    // as "i64" for diagnostic UX. That makes the shortcut return the
    // IntLit fallback for `let x: i64 = 42;` instead of resolving the
    // annotation to Type::I64 — breaking downstream checks that pattern-
    // match against `Type::I64` (e.g., `infer_borrow_expr`'s
    // primitive-rejection arm). Routing IntLit through the slow path
    // always resolves the annotation to a concrete machine integer
    // type and preserves the borrow-of-primitive rejection.
    if !matches!(fallback, Type::IntLit(_)) && annotation.display_name() == render_type(fallback) {
        return fallback.clone();
    }

    let annotated = resolve_type_expr(annotation, universe, &HashMap::new(), &[]);

    // PR A / N4-PRA: relax T046 for generic record annotations. The
    // three conditions are ALL required:
    //   (1) `!args.is_empty()` — the annotation supplies type-args
    //   (2) `universe.records.contains_key(name)` — the type is a
    //       known record
    //   (3) `args.len() == record.type_params.len()` — arity matches
    //
    // All three together admit the annotation as a valid generic
    // record context. Non-generic records OR unknown names OR arity
    // mismatches continue to fire T046 per the pre-PR-A path
    // (existing t046 tests preserved).
    if let Type::Named(name, args) = &annotated
        && !args.is_empty()
        && let Some((type_params, _)) = universe.records.get(name)
        && args.len() == type_params.len()
    {
        return annotated;
    }

    // PR B commit #2: same relaxation extended to generic enum
    // annotations. `let x: Option<i64> = Some(42)` and
    // `let r: Result<i64, MyErr> = Ok(7)` are admitted via the
    // same three-condition gate (args supplied, name is a known
    // enum, arity matches). Without this, ambient include of
    // stdlib Option/Result wouldn't help annotation propagation.
    if let Type::Named(name, args) = &annotated
        && !args.is_empty()
        && let Some((type_params, _)) = universe.enums.get(name)
        && args.len() == type_params.len()
    {
        return annotated;
    }

    if matches!(annotated, Type::Named(_, _)) {
        diagnostics.push(Diagnostic::error(
            codes::T046,
            format!(
                "let binding `{binding_name}` annotated `{}` — non-generic record/named annotations are not supported on `let`. For non-generic records, drop the annotation (`let {binding_name} = ...`) and let inference run. For generic records, annotate with concrete type arguments (`let {binding_name}: RecordName<ConcreteType> = ...`). Supported primitive annotations: i32, u32, i64, u64, f64, bool.",
                annotation.display_name(),
            ),
            Some(annotation.span),
        ));
        return fallback.clone();
    }

    annotated
}

pub(super) fn check_return(
    stmt: &ReturnStmt,
    expected_return: &Type,
    env: &HashMap<String, Type>,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedReturnStmt {
    let mut value = stmt.value.as_ref().map(|expr| {
        // Return-position expected-type propagation. Thread the function's
        // (already-substituted, during monomorphization) return type into
        // the returned expression — the same `ExpectedTypeGuard` mechanism
        // `check_let` uses for `let`-binding RHSs. This lets a generic
        // constructor body like `return Vec { … }` seed its phantom type
        // parameter from the return type (`Vec<i64>` after substitution),
        // which a let-annotation in the body cannot do because in-body
        // annotations aren't substituted during monomorphization.
        let mut guard = ExpectedTypeGuard::push(tracker, Some(expected_return.clone()));
        infer_expr(
            expr,
            env,
            expected_return,
            context,
            guard.tracker_mut(),
            diagnostics,
        )
    });

    // PIL / array-stride: narrow IntLit leaves in the returned expression to the
    // function's return type, mirroring check_let. The ExpectedTypeGuard above
    // seeds generic inference (`return Vec { … }`) but does NOT narrow a bare
    // literal/binary's IntLit leaves, nor an array literal's elements — they stay
    // IntLit and default to i64, producing INVALID wasm two ways: a scalar
    // `fn f() -> i32 { return 5; }` returned an i64 local from an i32-signature
    // function, and an array `-> [i32; N]` literal stored its elements at i64
    // stride (the #330 case). Resolving here narrows both (the array elem_type +
    // elements to T; a scalar literal/binary to the return type) and rejects an
    // out-of-range SCALAR leaf (`return 0 - 2147483648`) as T049 — the return
    // mismatch code, same as the single-literal `return 2147483648` overflow.
    // `resolve_int_literals_or_reject`'s machine-int gate means an array/composite
    // return only RESOLVES (no rejection), exactly as the prior ArrayLit-scoped
    // pass did. The selfhost P_K_RETURN mirror pins scalar returns too (it already
    // pinned arrays), so differential parity holds — this supersedes #330's
    // ArrayLit-only scoping now that the scalar deferral is lifted.
    if let Some(v) = &mut value
        && !matches!(v.ty, Type::Error)
        && type_compatible(expected_return, &v.ty)
    {
        resolve_int_literals_or_reject(v, expected_return, codes::T049, diagnostics);
    }

    match (&value, expected_return) {
        (None, Type::Unit) => {}
        (None, expected) => diagnostics.push(Diagnostic::error(
            codes::T047,
            format!(
                "return statement requires a value of type `{}`",
                render_type(expected)
            ),
            Some(stmt.span),
        )),
        (Some(_), Type::Unit) => diagnostics.push(Diagnostic::error(
            codes::T048,
            "unit-returning function cannot return a value",
            Some(stmt.span),
        )),
        (Some(expr), expected) if !type_compatible(expected, &expr.ty) => {
            let site_ctx = "return statement";
            if let Some(t195) =
                try_cap_deadline_diagnostic(expected, &expr.ty, "return value", site_ctx, stmt.span)
            {
                diagnostics.push(t195);
            } else if let Some(t227) =
                try_array_size_mismatch_diagnostic(expected, &expr.ty, site_ctx, stmt.span)
            {
                diagnostics.push(t227);
            } else {
                diagnostics.push(Diagnostic::error(
                    codes::T049,
                    format!(
                        "return expected type `{}`, found `{}`",
                        render_type(expected),
                        render_type(&expr.ty)
                    ),
                    Some(stmt.span),
                ))
            }
        }
        (Some(_), _) => {}
    }

    // Mutation-as-capability (PR-2, NC-1): the RETURN escape gate. A value that
    // ALIASES a `@ReadOnly` object (a heap/reference value rooted in a readonly
    // local) may not be returned — the caller would receive a mutable handle
    // (returns carry no `@ReadOnly` annotation in v1, AG-6), re-widening the
    // authority. A COPY of a primitive field (`return p.x`, an i64) is excluded
    // by `is_aliasable_type`, so getters stay legal.
    if let Some(expr) = &value
        && is_aliasable_type(&expr.ty)
        && let Some(root) = place_root_local(expr)
        && tracker.readonly_locals.contains(root)
    {
        diagnostics.push(Diagnostic::error(
            codes::T253,
            format!(
                "cannot return `{}`: it aliases the `@ReadOnly` value `{root}`, handing the \
                 caller a mutable handle — return a copy, or drop `@ReadOnly`.",
                render_place(expr)
            ),
            Some(stmt.span),
        ));
    }

    // Regions (DEF-2a, NC-R1): the RETURN escape sink (scope-depth 0 — the function
    // boundary outlives any region). Belt-and-suspenders: a region value normally
    // cannot reach here (it can't escape its region, and a region-internal `return`
    // is already T068), but the closed sink-set leaves no gap.
    if let Some(expr) = &value {
        check_region_escape(
            expr,
            RegionId::Global,
            "be returned from the function",
            tracker,
            diagnostics,
        );
    }

    // Refinement quarantine (Phase 2): return-refinement discharge (T225/T211)
    // now runs in the v2 obligation pass (check_with_warnings), over the
    // function's declared `return_refinement`, not inline here.

    TypedReturnStmt {
        value,
        span: stmt.span,
    }
}

pub(super) fn check_if(
    stmt: &crate::ast::IfStmt,
    env: &HashMap<String, Type>,
    mutables: &mut HashSet<String>,
    expected_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> (TypedIfStmt, bool) {
    let condition = infer_expr(
        &stmt.condition,
        env,
        expected_return,
        context,
        tracker,
        diagnostics,
    );
    if !matches!(condition.ty, Type::Bool | Type::Error) {
        diagnostics.push(Diagnostic::error(
            codes::T050,
            format!(
                "if condition must be `bool`, found `{}`",
                render_type(&condition.ty)
            ),
            Some(condition.span),
        ));
    }

    // Wall 4 Step 10: flow-sensitive refinement narrowing.
    //
    // If the if-condition is a recognized refinement-shaped predicate
    // (`<bare-ident> RELOP <int-literal>` or its reversed form), push
    // a narrowing frame onto `pattern_refinement_stack` before
    // checking the then-branch. The negation of the predicate
    // narrows the else-branch.
    //
    // Frame composition (N1-W4S10): when the same name is already
    // narrowed by an enclosing frame, the new frame copies forward
    // the prior clauses (top-down walk) and appends the new one. This
    // is the load-bearing fix for the nested-if conjunction case
    // (`if x > 0 { if x < 100 { need_in_range(x) } }`): without
    // composition, the inner frame would HIDE the outer narrowing
    // under `lookup_pattern_refinement`'s first-match-wins discipline.
    //
    // V4-W4S10 SOUNDNESS GAP: this narrowing does NOT track through
    // reassignment. `if x > 0 { x = 0; need_positive(x); }` admits
    // the call inside the if-body even though `x` is no longer
    // positive — narrowing is per-arm, not per-statement-after-cond.
    // Users should use let-bindings (`let y = x; if y > 0 { ... }`)
    // when reassigning a narrowed variable. Future Step (TBD) will
    // either invalidate the frame on assignment or thread a
    // per-statement environment.
    let narrowing = extract_narrowing_predicate(&stmt.condition);

    let then_pushed = if let Some((name, clause)) = &narrowing {
        let frame =
            compose_narrowing_frame(&tracker.pattern_refinement_stack, name, clause.clone());
        tracker.pattern_refinement_stack.push(frame);
        true
    } else {
        false
    };

    let mut then_env = env.clone();
    let mut then_mutables = mutables.clone();
    let then_branch = check_block(
        &stmt.then_branch,
        &mut then_env,
        &mut then_mutables,
        expected_return,
        context,
        tracker,
        diagnostics,
        false,
    );

    if then_pushed {
        tracker.pattern_refinement_stack.pop();
    }

    let else_pushed = if let Some((name, clause)) = &narrowing {
        let negated = negate_refinement_clause(clause);
        let frame = compose_narrowing_frame(&tracker.pattern_refinement_stack, name, negated);
        tracker.pattern_refinement_stack.push(frame);
        true
    } else {
        false
    };

    let mut else_env = env.clone();
    let mut else_mutables = mutables.clone();
    let else_branch = check_block(
        &stmt.else_branch,
        &mut else_env,
        &mut else_mutables,
        expected_return,
        context,
        tracker,
        diagnostics,
        false,
    );

    if else_pushed {
        tracker.pattern_refinement_stack.pop();
    }

    let guaranteed_return = then_branch.guaranteed_return && else_branch.guaranteed_return;

    (
        TypedIfStmt {
            condition,
            then_branch,
            else_branch,
            span: stmt.span,
        },
        guaranteed_return,
    )
}

pub(super) fn check_match(
    stmt: &crate::ast::MatchStmt,
    env: &HashMap<String, Type>,
    mutables: &mut HashSet<String>,
    expected_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> (TypedMatchStmt, bool) {
    let universe = context.universe;
    // T277 (constant patterns): a bare `Binding` pattern may name a module
    // CONST rather than introduce a binding, so the arm below qualifies it
    // against the current module. `context` is the module carrier here (the
    // agent-framework branch read a local `module_name` that this function,
    // post-extraction, does not have).
    let module_name = context.module_name;
    let scrutinee = infer_expr(
        &stmt.scrutinee,
        env,
        expected_return,
        context,
        tracker,
        diagnostics,
    );

    let mut arms = Vec::new();
    let mut wildcard_seen = false;
    let mut saw_true = false;
    let mut saw_false = false;
    let mut seen_literals = HashMap::<String, Span>::new();
    let mut covered_variants = HashSet::<String>::new();
    let mut has_unguarded_catchall = false;
    // Phase 5 (collection patterns): exhaustiveness over array/slice lengths.
    // `covered_exact` = lengths matched by an unguarded no-rest array arm
    // (`[a, b]` → 2); `min_rest_prefix` = the smallest fixed-prefix length over
    // unguarded `..rest` array arms (`[a, ..r]` → 1; `[..r]` → 0). A slice is
    // exhaustive iff some rest-arm of prefix L exists AND {0..L-1} ⊆ covered_exact;
    // a fixed array `[T; N]` iff N is covered or a rest-arm of prefix ≤ N exists.
    let mut covered_exact = HashSet::<usize>::new();
    let mut min_rest_prefix: Option<usize> = None;

    // Resolve enum variants for the scrutinee type
    let enum_variants: Option<&Vec<(String, Vec<Type>)>> = match &scrutinee.ty {
        Type::Named(name, _) => universe.enums.get(name).map(|(_, variants)| variants),
        _ => None,
    };
    // The scrutinee's element type + fixed size, if it is an array/slice — used
    // by the `Pattern::Array` arm and the collection exhaustiveness check.
    let (scrutinee_elem_ty, scrutinee_array_size): (Option<Type>, Option<usize>) =
        match &scrutinee.ty {
            Type::Array { elem, size } => (Some((**elem).clone()), Some(*size as usize)),
            Type::Slice(elem) => (Some((**elem).clone()), None),
            _ => (None, None),
        };

    for arm in &stmt.arms {
        if has_unguarded_catchall {
            diagnostics.push(Diagnostic::error(
                codes::T080,
                "match arm after catch-all is unreachable",
                Some(arm.span),
            ));
        }

        // Push a new scope for this arm's pattern bindings
        let mut arm_env = env.clone();

        // Wall 4 Step 6 commit #3: push a fresh refinement-narrowing
        // frame for this arm. The EnumVariant pattern below populates
        // it with bindings whose variant carried Literal-RHS
        // refinements (per N22-S6). The frame is popped on arm exit
        // so nested matches stack correctly.
        tracker.pattern_refinement_stack.push(HashMap::new());

        let pattern = match &arm.pattern {
            crate::ast::Pattern::Literal(pattern) => {
                let actual = infer_literal_type(&pattern.literal);
                if !matches!(scrutinee.ty, Type::Error) && !type_compatible(&scrutinee.ty, &actual)
                {
                    diagnostics.push(Diagnostic::error(
                        codes::T081,
                        format!(
                            "match pattern expected `{}`, found `{}`",
                            render_type(&scrutinee.ty),
                            render_type(&actual)
                        ),
                        Some(pattern.span),
                    ));
                }

                let key = render_literal(&pattern.literal);
                if let Some(previous) = seen_literals.insert(key.clone(), pattern.span) {
                    diagnostics.push(Diagnostic::error(
                        codes::T082,
                        format!("duplicate match pattern `{key}`"),
                        Some(previous.join(pattern.span)),
                    ));
                }

                match &pattern.literal {
                    Literal::Bool(true) => saw_true = true,
                    Literal::Bool(false) => saw_false = true,
                    _ => {}
                }

                TypedPattern::Literal(pattern.literal.clone())
            }
            crate::ast::Pattern::Range(pattern) => {
                let lo_ty = infer_literal_type(&pattern.lo);
                let hi_ty = infer_literal_type(&pattern.hi);

                if !matches!(scrutinee.ty, Type::Error) && !type_compatible(&scrutinee.ty, &lo_ty) {
                    diagnostics.push(Diagnostic::error(
                        codes::T081,
                        format!(
                            "match range lower bound expected `{}`, found `{}`",
                            render_type(&scrutinee.ty),
                            render_type(&lo_ty)
                        ),
                        Some(pattern.span),
                    ));
                }
                if !matches!(scrutinee.ty, Type::Error) && !type_compatible(&scrutinee.ty, &hi_ty) {
                    diagnostics.push(Diagnostic::error(
                        codes::T081,
                        format!(
                            "match range upper bound expected `{}`, found `{}`",
                            render_type(&scrutinee.ty),
                            render_type(&hi_ty)
                        ),
                        Some(pattern.span),
                    ));
                }

                // T282: a range lowers to a pair of ordering comparisons,
                // and those are defined only over the machine integer
                // types. The parser reaches this arm for `str` and `bool`
                // bounds too (it shares one arm with literal patterns),
                // and a `str` bound is `type_compatible` with a `str`
                // scrutinee, so T081 above lets it past. Unfenced, AIR
                // coerced such a bound to `0` and the emitter then died on
                // `Ptr >= I64` at the wasm backstop — a backend ICE
                // standing in for a plain source-level error.
                //
                // Both bounds share one span, so this reports ONE
                // diagnostic naming the offending side(s) rather than one
                // per bound — a doubled error on an identical span is
                // noise, and the author wrote a single bad range.
                let lo_bad = !matches!(&pattern.lo, Literal::Int(_));
                let hi_bad = !matches!(&pattern.hi, Literal::Int(_));
                if lo_bad || hi_bad {
                    let lo_ty = render_type(&infer_literal_type(&pattern.lo));
                    let hi_ty = render_type(&infer_literal_type(&pattern.hi));
                    let message = match (lo_bad, hi_bad) {
                        (true, true) if lo_ty == hi_ty => {
                            format!("match range bounds must be integer literals, found `{lo_ty}`")
                        }
                        (true, true) => format!(
                            "match range bounds must be integer literals, found `{lo_ty}` and `{hi_ty}`"
                        ),
                        (true, false) => format!(
                            "match range lower bound must be an integer literal, found `{lo_ty}`"
                        ),
                        (false, true) => format!(
                            "match range upper bound must be an integer literal, found `{hi_ty}`"
                        ),
                        (false, false) => unreachable!("guarded by `lo_bad || hi_bad`"),
                    };
                    diagnostics.push(Diagnostic::error(codes::T282, message, Some(pattern.span)));
                }

                if let (Literal::Int(lo_val), Literal::Int(hi_val)) = (&pattern.lo, &pattern.hi)
                    && lo_val > hi_val
                {
                    diagnostics.push(Diagnostic::error(
                        codes::T190,
                        format!(
                            "range pattern `{}..={}` has lower bound greater than upper bound",
                            lo_val, hi_val
                        ),
                        Some(pattern.span),
                    ));
                }

                TypedPattern::Range {
                    lo: pattern.lo.clone(),
                    hi: pattern.hi.clone(),
                }
            }
            crate::ast::Pattern::Wildcard(_) => {
                if wildcard_seen {
                    diagnostics.push(Diagnostic::error(
                        codes::T083,
                        "duplicate `_` match arm",
                        Some(arm.pattern.span()),
                    ));
                }
                wildcard_seen = true;
                if arm.guard.is_none() {
                    has_unguarded_catchall = true;
                }
                TypedPattern::Wildcard
            }
            crate::ast::Pattern::Binding(pattern) => {
                let qualified_const = format!("{module_name}::{}", pattern.name);
                if let Some((const_ty, literal)) = universe.consts.get(&qualified_const) {
                    if matches!(literal, Literal::Float(_) | Literal::Int256(_)) {
                        diagnostics.push(Diagnostic::error(
                            codes::T277,
                            format!(
                                "constant pattern `{}` has unsupported type `{}`",
                                pattern.name,
                                render_type(const_ty)
                            ),
                            Some(pattern.span),
                        ));
                    }
                    if !matches!(scrutinee.ty, Type::Error)
                        && !type_compatible(&scrutinee.ty, const_ty)
                    {
                        diagnostics.push(Diagnostic::error(
                            codes::T081,
                            format!(
                                "match pattern expected `{}`, found constant `{}` of type `{}`",
                                render_type(&scrutinee.ty),
                                pattern.name,
                                render_type(const_ty)
                            ),
                            Some(pattern.span),
                        ));
                    }

                    let key = render_literal(literal);
                    if let Some(previous) = seen_literals.insert(key.clone(), pattern.span) {
                        diagnostics.push(Diagnostic::error(
                            codes::T082,
                            format!("duplicate match pattern `{key}`"),
                            Some(previous.join(pattern.span)),
                        ));
                    }
                    match literal {
                        Literal::Bool(true) => saw_true = true,
                        Literal::Bool(false) => saw_false = true,
                        _ => {}
                    }
                    TypedPattern::Literal(literal.clone())
                } else {
                    // An unresolved identifier retains the existing binding-pattern
                    // meaning. A visible constant deliberately wins over a binding.
                    arm_env.insert(pattern.name.clone(), scrutinee.ty.clone());
                    if arm.guard.is_none() {
                        has_unguarded_catchall = true;
                    }
                    TypedPattern::Binding(pattern.name.clone())
                }
            }
            crate::ast::Pattern::EnumVariant(pattern) => {
                // Resolve enum type — use type_name if explicit, or infer from scrutinee
                let enum_name = if pattern.type_name.is_empty() {
                    match &scrutinee.ty {
                        Type::Named(name, _) => name.clone(),
                        Type::Error => "<error>".to_owned(),
                        other => {
                            diagnostics.push(Diagnostic::error(
                                codes::T084,
                                format!(
                                    "cannot match variant `{}` against non-enum type `{}`",
                                    pattern.variant,
                                    render_type(other)
                                ),
                                Some(pattern.span),
                            ));
                            "<error>".to_owned()
                        }
                    }
                } else {
                    pattern.type_name.clone()
                };

                // Look up variant payload types, applying generic substitution
                let mut typed_bindings = Vec::new();
                if let Some((type_params, variants)) = universe.enums.get(&enum_name) {
                    // Build substitution map from scrutinee type args
                    let subst_map: HashMap<String, Type> =
                        if let Type::Named(_, args) = &scrutinee.ty {
                            type_params
                                .iter()
                                .zip(args.iter())
                                .map(|(k, v)| (k.clone(), v.clone()))
                                .collect()
                        } else {
                            HashMap::new()
                        };

                    if let Some((_, payload_types)) =
                        variants.iter().find(|(name, _)| name == &pattern.variant)
                    {
                        if pattern.bindings.len() != payload_types.len() {
                            diagnostics.push(Diagnostic::error(
                                codes::T085,
                                format!(
                                    "variant `{}::{}` has {} field(s), pattern binds {}",
                                    enum_name,
                                    pattern.variant,
                                    payload_types.len(),
                                    pattern.bindings.len()
                                ),
                                Some(pattern.span),
                            ));
                        }

                        // Wall 4 Step 6 commit #3: gather variant
                        // refinements + declared field names for
                        // pattern-narrowing attachment per N9-S6.
                        // The i-th binding identifier corresponds to
                        // the i-th declared field name; refinement
                        // clauses are keyed by declared name and
                        // rewritten to the bound identifier name on
                        // attachment (so downstream consumers see the
                        // narrowed binding's name, not the variant's
                        // declared field name).
                        let variant_key = (enum_name.clone(), pattern.variant.clone());
                        let variant_refinements = universe
                            .enum_variant_refinements
                            .get(&variant_key)
                            .cloned()
                            .unwrap_or_default();
                        let variant_field_names = universe
                            .enum_variant_field_names
                            .get(&variant_key)
                            .cloned()
                            .unwrap_or_default();

                        for (idx, (binding_name, ty)) in pattern
                            .bindings
                            .iter()
                            .zip(payload_types.iter())
                            .enumerate()
                        {
                            // Apply generic substitution (e.g., Generic("T") → I64)
                            let resolved_ty = apply_subst(ty, &subst_map);
                            if binding_name != "_" {
                                arm_env.insert(binding_name.clone(), resolved_ty.clone());

                                // Wall 4 Step 6 commit #3 + N22-S6:
                                // attach Literal-RHS refinements to
                                // this binding. Field/LengthOf RHS
                                // clauses are filtered out — they're
                                // validated at construction, not
                                // propagated through bindings.
                                // A13-S6: wildcard `_` patterns
                                // already do NOT bind, so they don't
                                // attach (the `if binding_name != "_"`
                                // guard is the wildcard-narrowing
                                // boundary).
                                if let Some(declared_field) =
                                    variant_field_names.get(idx).and_then(|x| x.as_ref())
                                {
                                    let attached: Vec<crate::ast::RefinementClause> =
                                        variant_refinements
                                            .iter()
                                            .filter(|c| {
                                                c.field == *declared_field
                                                    && matches!(
                                                        c.rhs,
                                                        crate::ast::RefinementRhs::Literal(_)
                                                    )
                                            })
                                            .cloned()
                                            .collect();
                                    if !attached.is_empty()
                                        && let Some(frame) =
                                            tracker.pattern_refinement_stack.last_mut()
                                    {
                                        frame.insert(binding_name.clone(), attached);
                                    }
                                }
                            }
                            typed_bindings.push((binding_name.clone(), resolved_ty));
                        }
                    } else {
                        diagnostics.push(Diagnostic::error(
                            codes::T086,
                            format!("enum `{enum_name}` has no variant `{}`", pattern.variant),
                            Some(pattern.span),
                        ));
                    }
                }

                if arm.guard.is_none() {
                    covered_variants.insert(pattern.variant.clone());
                }

                TypedPattern::EnumVariant {
                    type_name: enum_name,
                    variant: pattern.variant.clone(),
                    bindings: typed_bindings,
                }
            }
            // Array/slice destructuring `[a, b, ..rest]` (Phase 5).
            crate::ast::Pattern::Array(pattern) => {
                let k = pattern.elements.len();
                let has_rest = pattern.rest.is_some();

                // Require an array/slice scrutinee (else T264); `elem_ty` is the
                // element type (Error if the scrutinee is the wrong shape, so the
                // bindings stay typed and don't cascade unknown-variable errors).
                let elem_ty = match &scrutinee_elem_ty {
                    Some(t) => t.clone(),
                    None => {
                        if !matches!(scrutinee.ty, Type::Error) {
                            diagnostics.push(Diagnostic::error(
                                codes::T264,
                                format!(
                                    "array pattern requires an array or slice scrutinee, found `{}`",
                                    render_type(&scrutinee.ty)
                                ),
                                Some(pattern.span),
                            ));
                        }
                        Type::Error
                    }
                };

                // A fixed-size array `[T; N]` makes some lengths impossible (T265).
                if let Some(n) = scrutinee_array_size {
                    let impossible = if has_rest { k > n } else { k != n };
                    if impossible {
                        diagnostics.push(Diagnostic::error(
                            codes::T265,
                            format!(
                                "array pattern with {} fixed element(s){} cannot match `[{}; {}]`",
                                k,
                                if has_rest { " and `..rest`" } else { "" },
                                render_type(&elem_ty),
                                n
                            ),
                            Some(pattern.span),
                        ));
                    }
                }

                // Bind each fixed element to the element type; the rest to `&[T]`.
                let mut elem_binds: Vec<(Option<String>, Type)> = Vec::with_capacity(k);
                for el in &pattern.elements {
                    match el {
                        crate::ast::ArrayElem::Bind(name, _) => {
                            arm_env.insert(name.clone(), elem_ty.clone());
                            elem_binds.push((Some(name.clone()), elem_ty.clone()));
                        }
                        crate::ast::ArrayElem::Wild(_) => {
                            elem_binds.push((None, elem_ty.clone()));
                        }
                    }
                }
                let rest_typed = pattern.rest.as_ref().map(|r| {
                    if let Some(name) = &r.name {
                        arm_env.insert(name.clone(), Type::Slice(Box::new(elem_ty.clone())));
                    }
                    (r.name.clone(), elem_ty.clone())
                });

                // Exhaustiveness bookkeeping (unguarded arms only). A rest-only
                // `[..rest]` (k == 0) matches every length → a true catch-all.
                if arm.guard.is_none() {
                    if has_rest {
                        min_rest_prefix = Some(min_rest_prefix.map_or(k, |p| p.min(k)));
                        if k == 0 {
                            has_unguarded_catchall = true;
                        }
                    } else {
                        covered_exact.insert(k);
                    }
                }

                TypedPattern::Array {
                    elem_binds,
                    rest: rest_typed,
                    elem_ty,
                    is_slice: matches!(scrutinee.ty, Type::Slice(_)),
                }
            }
        };

        // Type-check optional guard
        let guard = arm.guard.as_ref().map(|guard_expr| {
            let typed_guard = infer_expr(
                guard_expr,
                &arm_env,
                expected_return,
                context,
                tracker,
                diagnostics,
            );
            if !matches!(typed_guard.ty, Type::Bool | Type::Error) {
                diagnostics.push(Diagnostic::error(
                    codes::T053,
                    format!(
                        "match guard must be `bool`, found `{}`",
                        render_type(&typed_guard.ty)
                    ),
                    Some(typed_guard.span),
                ));
            }
            typed_guard
        });

        let mut arm_mutables = mutables.clone();
        let body = check_block(
            &arm.body,
            &mut arm_env,
            &mut arm_mutables,
            expected_return,
            context,
            tracker,
            diagnostics,
            false,
        );

        arms.push(TypedMatchArm {
            pattern,
            guard,
            body,
            span: arm.span,
        });

        // Wall 4 Step 6 commit #3: pop the refinement-narrowing frame
        // for this arm. Bindings introduced here are no longer in
        // scope outside the arm body.
        tracker.pattern_refinement_stack.pop();
    }

    // Exhaustiveness check
    let exhaustive = if matches!(scrutinee.ty, Type::Error) {
        false
    } else if has_unguarded_catchall {
        true
    } else if let Some(variants) = enum_variants {
        // All variants must be covered by unguarded arms
        variants
            .iter()
            .all(|(name, _)| covered_variants.contains(name))
    } else if scrutinee_elem_ty.is_some() {
        // Array/slice collection exhaustiveness (Phase 5). For a fixed `[T; N]`,
        // N must be covered by an exact arm or by a rest-arm of prefix ≤ N. For a
        // slice `&[T]` (runtime length), some rest-arm of prefix L must exist AND
        // every shorter length {0..L-1} be covered by an exact arm — e.g.
        // `[head, ..tail]` (L=1) + `[]` (covers 0) is exhaustive.
        match scrutinee_array_size {
            Some(n) => covered_exact.contains(&n) || min_rest_prefix.is_some_and(|p| p <= n),
            None => match min_rest_prefix {
                Some(p) => (0..p).all(|len| covered_exact.contains(&len)),
                None => false,
            },
        }
    } else {
        match scrutinee.ty {
            Type::Bool => saw_true && saw_false,
            _ => false, // integers etc. require wildcard
        }
    };

    if !matches!(scrutinee.ty, Type::Error) && !exhaustive {
        if let Some(variants) = enum_variants {
            let missing: Vec<&str> = variants
                .iter()
                .filter(|(name, _)| !covered_variants.contains(name))
                .map(|(name, _)| name.as_str())
                .collect();
            diagnostics.push(Diagnostic::error(
                codes::T087,
                format!(
                    "non-exhaustive match: missing variant(s) {}",
                    missing.join(", ")
                ),
                Some(stmt.span),
            ));
        } else {
            diagnostics.push(Diagnostic::error(
                codes::T088,
                "non-exhaustive match; add a `_` arm",
                Some(stmt.span),
            ));
        }
    }

    let guaranteed_return = exhaustive
        && arms
            .iter()
            .filter(|arm| arm.guard.is_none())
            .all(|arm| arm.body.guaranteed_return);

    (
        TypedMatchStmt {
            scrutinee,
            arms,
            span: stmt.span,
        },
        guaranteed_return,
    )
}

pub(super) fn check_while(
    stmt: &crate::ast::WhileStmt,
    env: &HashMap<String, Type>,
    mutables: &mut HashSet<String>,
    expected_return: &Type,
    context: TypeCheckContext<'_>,
    tracker: &mut MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedWhileStmt {
    let condition = infer_expr(
        &stmt.condition,
        env,
        expected_return,
        context,
        tracker,
        diagnostics,
    );
    if !matches!(condition.ty, Type::Bool | Type::Error) {
        diagnostics.push(Diagnostic::error(
            codes::T051,
            format!(
                "while condition must be `bool`, found `{}`",
                render_type(&condition.ty)
            ),
            Some(condition.span),
        ));
    }

    let mut body_env = env.clone();
    let mut body_mutables = mutables.clone();
    // break/continue: the body is one loop level deeper.
    tracker.loop_depth += 1;
    let body = check_block(
        &stmt.body,
        &mut body_env,
        &mut body_mutables,
        expected_return,
        context,
        tracker,
        diagnostics,
        false,
    );
    tracker.loop_depth -= 1;

    TypedWhileStmt {
        condition,
        body,
        span: stmt.span,
    }
}

#[cfg(test)]
mod exclusivity_helper_tests {
    use super::resolve_alias_root;
    use std::collections::HashMap;

    /// Exclusivity (DEF-2c, NC-2c-3): `resolve_alias_root` follows the `let`-alias chain to
    /// the TERMINAL root, transitively (so a 2-hop `let z=y; let y=x` resolves `z → x`,
    /// closing the multi-hop launder), and an un-aliased name is its own root. The walk is
    /// bounded by the map size — the map is acyclic by construction, so this never hangs.
    #[test]
    fn resolve_alias_root_walks_to_the_terminal_root() {
        let empty: HashMap<String, String> = HashMap::new();
        assert_eq!(resolve_alias_root("x", &empty), "x");

        let mut m = HashMap::new();
        m.insert("y".to_string(), "x".to_string()); // let y = x
        m.insert("z".to_string(), "y".to_string()); // let z = y
        assert_eq!(resolve_alias_root("z", &m), "x"); // 2-hop → terminal root
        assert_eq!(resolve_alias_root("y", &m), "x");
        assert_eq!(resolve_alias_root("x", &m), "x"); // a root resolves to itself
        assert_eq!(resolve_alias_root("w", &m), "w"); // an un-aliased name is its own root
    }
}

#[cfg(test)]
mod region_allowlist_tests {
    use super::is_region_safe_stdlib_method;

    /// Regions (DEF-2a, NC-R2): the CLOSED-allowlist contract — the `vec_quarantine`
    /// analogue. The exact set of `(Type, method)` pairs a region value may reach as a
    /// method receiver is pinned here. Each ACCEPTED pair is a stdlib collection method
    /// whose `self` is escape-proven (an `@ReadOnly self` read or an append-only in-place
    /// mutator). Each REJECTED pair is a method that could hand `self` (or a longer-lived
    /// alias) out of the region — adding any of them to `is_region_safe_stdlib_method`
    /// fails this test, which is the point: the build breaks before an unsound exemption
    /// can ship. If you add a stdlib method here, you must first prove it keeps `self`
    /// in-region (and move its dangerous siblings into the rejected list).
    #[test]
    fn region_allowlist_is_closed() {
        // The full accepted set (escape-proven self-containing stdlib methods).
        let accepted = [
            ("Vec", "len"),
            ("Vec", "capacity"),
            ("Vec", "get"),
            ("Vec", "push"),
            ("Vec", "set"),
            ("Map", "len"),
            ("Map", "capacity"),
            ("Map", "is_empty"),
            ("Map", "get"),
            ("Map", "get_or"),
            ("Map", "contains"),
            ("Map", "insert"),
        ];
        for (ty, m) in accepted {
            assert!(
                is_region_safe_stdlib_method(ty, m),
                "`{ty}::{m}` must remain on the region receiver-allowlist"
            );
        }

        // Curated dangerous / out-of-scope pairs that must NEVER be exempt: anything
        // that could leak `self` or an interior pointer (`as_ptr`/`as_slice`/`iter`/
        // `drain`/`into_*`/`remove`/`clear`/`entry`), a user-defined type's method, and
        // associated constructors (no `self`, so never a region value to begin with).
        let rejected = [
            ("Vec", "as_ptr"),
            ("Vec", "as_slice"),
            ("Vec", "iter"),
            ("Vec", "drain"),
            ("Vec", "into_raw"),
            ("Vec", "remove"),
            ("Vec", "clear"),
            ("Vec", "new"),
            ("Vec", "with_capacity"),
            ("Map", "entry"),
            ("Map", "iter"),
            ("Map", "remove"),
            ("Map", "keys"),
            ("Map", "values"),
            ("Map", "new"),
            ("Point", "push"),
            ("MyType", "get"),
        ];
        for (ty, m) in rejected {
            assert!(
                !is_region_safe_stdlib_method(ty, m),
                "`{ty}::{m}` must NOT be on the region receiver-allowlist \
                 (it is not escape-proven to keep `self` in-region)"
            );
        }
    }
}

/// RF-M2: resolve a range-for END bound to a compile-time `K`, Z3-FREE. Two
/// forms only (the Boring Limit): a typed integer literal, or the
/// `ArrayLen { size }` intrinsic - `arr.len()` on `[T; N]`, whose `size` is
/// read from the receiver's STATIC type (the SC-4/T227 soundness anchor), so
/// a side-effecting receiver cannot perturb it. Anything else means no fact,
/// i.e. the runtime-trap floor.
fn resolve_range_fact_end(end: &TypedExpr) -> Option<i64> {
    match &end.kind {
        TypedExprKind::Literal(Literal::Int(k)) => Some(*k),
        TypedExprKind::Intrinsic(intr) => match &intr.kind {
            crate::typed_ast::TypedIntrinsicKind::ArrayLen { size } => Some(i64::from(*size)),
            _ => None,
        },
        _ => None,
    }
}

/// RF-M2: the SHADOW-PROOF pre-scan - true iff ANY statement in the body
/// rebinds `name` through any binder form. TOTAL matches over `Stmt` and
/// `Pattern` (the F005 defense: a future binder variant fails to compile here
/// and must be classified). Expressions need no descent: the only
/// expression-level binders are closure params and handle-clause binders,
/// and BOTH contexts are BARRIERED (the fact channel is emptied around their
/// `check_block`). `Assign` is not a binder - assignment MUTATES an existing
/// binding, and mutating the loop var is T042 (errors abort before AIR).
fn body_rebinds_name(block: &Block, name: &str) -> bool {
    block.statements.iter().any(|s| stmt_rebinds_name(s, name))
}

fn stmt_rebinds_name(s: &Stmt, name: &str) -> bool {
    match s {
        Stmt::Let(l) => l.name == name,
        Stmt::LetTuple(lt) => lt.bindings.iter().any(|(n, _)| n == name),
        Stmt::Assign(_) | Stmt::Expr(_) => false,
        Stmt::If(i) => {
            body_rebinds_name(&i.then_branch, name) || body_rebinds_name(&i.else_branch, name)
        }
        Stmt::Match(m) => m.arms.iter().any(|arm| {
            pattern_binds_name(&arm.pattern, name) || body_rebinds_name(&arm.body, name)
        }),
        Stmt::While(w) => body_rebinds_name(&w.body, name),
        Stmt::ForIn(f) => f.var == name || body_rebinds_name(&f.body, name),
        Stmt::ForRange(f) => f.var == name || body_rebinds_name(&f.body, name),
        Stmt::Return(_) | Stmt::Break(_) | Stmt::Continue(_) => false,
    }
}

fn pattern_binds_name(p: &Pattern, name: &str) -> bool {
    match p {
        Pattern::Literal(_) | Pattern::Range(_) | Pattern::Wildcard(_) => false,
        Pattern::Binding(b) => b.name == name,
        Pattern::EnumVariant(e) => e.bindings.iter().any(|b| b == name),
        Pattern::Array(a) => {
            a.elements
                .iter()
                .any(|el| matches!(el, crate::ast::ArrayElem::Bind(n, _) if n == name))
                || a.rest
                    .as_ref()
                    .is_some_and(|r| r.name.as_deref() == Some(name))
        }
    }
}
