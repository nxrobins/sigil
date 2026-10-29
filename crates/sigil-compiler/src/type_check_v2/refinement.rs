//! Pure refinement-obligation collector.
//!
//! Walks a `ResolvedProgram` (for `FnDef`-level return refinement
//! clauses) + `TypedProgram` (for the typed function bodies that
//! contain the return statements) and emits a `RefinementWorkload` of
//! proof obligations the orchestrator must discharge.
//!
//! This file must not import any of:
//! - `z3`
//! - the z3 capability module
//! - the z3 cache module
//!
//! Enforced by `crates/sigil-compiler/tests/quarantine_grep.rs`.
//!
//! ## Coverage
//!
//! The collector covers literal, symbolic, and subsumption checks at return,
//! record-construction, variant-construction, and function-argument sites, and
//! at every store into a refined record's field, which gets the construction
//! site's dispatch (the design-by-contract spec's DBC0-3); a store into a field
//! that a cross-field or `length()` clause joins to a sibling is refused (T216).
//! Cross-field record clauses emit a Z3 obligation for literal pairs and a
//! conservative T216 rejection for symbolic pairs. Declaration-shape errors
//! (T120, T212, T213, T217, and T219) remain in the declaration validator.
//!
//! Variant refined-value subsumption and generic-enum variant refinements are
//! outside the current collector surface. They emit no obligation; the public
//! soundness claims therefore remain limited to the covered refinement forms.

use super::obligations::{RefinementObligation, RefinementWorkload};
use crate::ast::{EnumDef, Item, RecordDef, RefinementClause, RefinementRhs};
use crate::diagnostics::{Diagnostic, codes};
use crate::name_resolution::ResolvedProgram;
use crate::span::Span;
use crate::type_check::Type;
use crate::typed_ast::{
    TypedAssignStmt, TypedBlock, TypedCallExpr, TypedEnumConstructExpr, TypedExpr, TypedExprKind,
    TypedProgram, TypedRecordConstructExpr, TypedReturnStmt, TypedStmt,
};
use std::collections::HashMap;

/// Collect refinement obligations from a resolved + typed program.
///
/// Walks every `TypedReturnStmt` in every typed function, matched with
/// its declaring `FnDef`'s `return_refinement` (if any). Emits one
/// `LiteralFits` per literal return, one `SubsumptionAny` per refined-
/// symbolic return (when syntactic fast-path fails), and one T211 per
/// unrefined-symbolic return.
pub(super) fn collect_refinement_obligations(
    resolved: &ResolvedProgram,
    typed: &TypedProgram,
) -> (Vec<Diagnostic>, RefinementWorkload) {
    let mut diagnostics = Vec::new();
    let mut workload = RefinementWorkload::default();

    // Pre-build name → AST-node maps. Lookups are O(1); we only iterate
    // the maps via `get`, never via .iter() — so HashMap is fine for
    // determinism.
    let mut fn_def_by_name: HashMap<(String, String), &crate::ast::FnDef> = HashMap::new();
    let mut record_def_by_name: HashMap<String, &RecordDef> = HashMap::new();
    let mut enum_def_by_name: HashMap<String, &EnumDef> = HashMap::new();
    for ast_module in &resolved.ast.modules {
        for item in &ast_module.items {
            match item {
                Item::FnDef(def) => {
                    fn_def_by_name.insert((ast_module.name.clone(), def.name.clone()), def);
                }
                Item::ImplDef(impl_def) => {
                    for method in &impl_def.methods {
                        fn_def_by_name
                            .insert((ast_module.name.clone(), method.name.clone()), method);
                    }
                }
                Item::RecordDef(def) => {
                    record_def_by_name.insert(def.name.clone(), def);
                }
                Item::EnumDef(def) => {
                    enum_def_by_name.insert(def.name.clone(), def);
                }
                _ => {}
            }
        }
    }

    for typed_module in &typed.modules {
        for typed_fn in &typed_module.functions {
            // Return-statement walker: needs the declaring FnDef's
            // return_refinement. If the function has none (or isn't found
            // — synthesized module-init etc.), skip this fn for return
            // refinements but still walk it for CrossField below.
            // `typed_fn.name` is module-qualified (e.g. "sigil::bad"); the
            // `fn_def_by_name` map is keyed by the BARE name (`def.name` /
            // `method.name`), which is the last `::` segment. Match on that.
            // The typed name is qualified while the source map uses the bare
            // name. `z3_corpus/55` pins this normalization.
            let bare_fn_name = typed_fn
                .name
                .rsplit("::")
                .next()
                .unwrap_or(typed_fn.name.as_str());
            if let Some(fn_def) =
                fn_def_by_name.get(&(typed_module.name.clone(), bare_fn_name.to_string()))
                && let Some(ret_clause) = &fn_def.return_refinement
            {
                visit_returns(&typed_fn.body, &mut |ret_stmt| {
                    emit_return_refinement_obligations(
                        ret_clause,
                        ret_stmt,
                        &mut diagnostics,
                        &mut workload,
                    );
                });
            }

            // Visit every record construction, variant construction, and call
            // nested in the body. `module_name` keys same-module call lookup.
            let module_name = typed_module.name.as_str();
            visit_block_constructs(&typed_fn.body, &mut |expr| match &expr.kind {
                TypedExprKind::RecordConstruct(rc) => emit_record_construction_obligations(
                    rc,
                    expr.span,
                    &record_def_by_name,
                    &mut diagnostics,
                    &mut workload,
                ),
                TypedExprKind::EnumConstruct(e) => emit_variant_construction_obligations(
                    e,
                    expr.span,
                    &enum_def_by_name,
                    &mut diagnostics,
                    &mut workload,
                ),
                TypedExprKind::Call(c) => emit_call_arg_obligations(
                    c,
                    expr.span,
                    module_name,
                    &fn_def_by_name,
                    &mut diagnostics,
                    &mut workload,
                ),
                _ => {}
            });

            // DBC0-3: every store into a refined record's field is a sink, keyed on
            // the place's record type. A second walk, because the two hooks would
            // borrow the diagnostics and the workload at once.
            visit_block_stmts(&typed_fn.body, &mut |stmt| {
                if let TypedStmt::Assign(store) = stmt {
                    emit_field_store_obligations(
                        store,
                        &record_def_by_name,
                        &mut diagnostics,
                        &mut workload,
                    );
                }
            });
        }
    }

    (diagnostics, workload)
}

/// Return-site dispatch: literals produce `LiteralFits`, refined symbolic
/// values produce `SubsumptionAny` after the syntactic fast path, and symbolic
/// values without a sidecar produce T211 directly. The current AST carries one
/// return clause, so this runs once per return site.
fn emit_return_refinement_obligations(
    ret_clause: &RefinementClause,
    ret_stmt: &TypedReturnStmt,
    diagnostics: &mut Vec<Diagnostic>,
    workload: &mut RefinementWorkload,
) {
    let Some(ret_expr) = &ret_stmt.value else {
        return;
    };

    if let Some(literal_value) = extract_int_literal(ret_expr) {
        // Arm 1: literal-RHS. Emit LiteralFits obligation.
        workload
            .obligations
            .push(RefinementObligation::LiteralFits {
                clause: ret_clause.clone(),
                // PR-U3-b: return refinements stay i64-only (wide deferred).
                value: crate::ast::RefValue::Narrow(literal_value),
                site: ret_stmt.span,
                on_violated: literal_violated_diagnostic(literal_value, ret_clause, ret_stmt.span),
                on_timeout: literal_timeout_diagnostic(literal_value, ret_stmt.span),
            });
        return;
    }

    if let Some(supplied) = &ret_expr.refinement {
        // Arm 2: refined-symbolic. Syntactic fast-path FIRST — if any
        // supplied syntactically matches the declared clause, accept
        // without emitting any obligation (no Z3 work).
        let syntactic_match = supplied
            .iter()
            .any(|s| crate::type_check::refinements_match(s, ret_clause));
        if syntactic_match {
            return;
        }
        // Symbolic residue: emit SubsumptionAny carrying all supplied
        // clauses. The orchestrator will ask Z3 per pair and accept on
        // first Holds.
        workload
            .obligations
            .push(RefinementObligation::SubsumptionAny {
                actual: supplied.clone(),
                expected: ret_clause.clone(),
                site: ret_stmt.span,
                on_violated: symbolic_subsumption_violated_diagnostic(ret_clause, ret_stmt.span),
                on_timeout: symbolic_subsumption_timeout_diagnostic(ret_clause, ret_stmt.span),
            });
        return;
    }

    // Arm 3: symbolic with no refinement sidecar. No Z3 query is
    // possible. Emit T211 directly — this never reaches the orchestrator.
    diagnostics.push(Diagnostic::error(
        codes::T211,
        "return statement is symbolic with no preserved refinement; the declared return refinement requires either a literal value or an upstream expression carrying a subsuming refinement (refined field read or refined-return call result)",
        Some(ret_stmt.span),
    ));
}

/// Recursively visit every `TypedReturnStmt` in a block subtree. Recurses
/// into nested if/match/while/for blocks (where return statements can
/// legitimately appear); does not recurse into expressions or handle, region,
/// or grant bodies, where control-flow validation rejects returns.
fn visit_returns<F: FnMut(&TypedReturnStmt)>(block: &TypedBlock, visit: &mut F) {
    for stmt in &block.statements {
        visit_inner_stmt_returns(stmt, visit);
    }
}

/// Single-statement return walker. Factored out so `ForIn` (whose body
/// is `Vec<TypedStmt>` rather than `TypedBlock`) shares the same
/// recursive arms.
fn visit_inner_stmt_returns<F: FnMut(&TypedReturnStmt)>(stmt: &TypedStmt, visit: &mut F) {
    match stmt {
        TypedStmt::Return(r) => visit(r),
        TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
        TypedStmt::If(s) => {
            visit_returns(&s.then_branch, visit);
            visit_returns(&s.else_branch, visit);
        }
        TypedStmt::Match(s) => {
            for arm in &s.arms {
                visit_returns(&arm.body, visit);
            }
        }
        TypedStmt::While(s) => visit_returns(&s.body, visit),
        TypedStmt::ForIn(s) => {
            for inner in &s.body {
                visit_inner_stmt_returns(inner, visit);
            }
        }
        TypedStmt::ForRange(s) => {
            for inner in &s.body {
                visit_inner_stmt_returns(inner, visit);
            }
        }
        TypedStmt::Let(_) | TypedStmt::Assign(_) | TypedStmt::Expr(_) => {}
    }
}

/// Extract an i64 literal from a typed expression.
fn extract_int_literal(expr: &TypedExpr) -> Option<i64> {
    match &expr.kind {
        TypedExprKind::Literal(crate::ast::Literal::Int(v)) => Some(*v),
        _ => None,
    }
}

/// Render a refinement operator in source-text form.
fn format_refinement_op(op: crate::ast::RefinementOp) -> &'static str {
    match op {
        crate::ast::RefinementOp::Le => "<=",
        crate::ast::RefinementOp::Lt => "<",
        crate::ast::RefinementOp::Ge => ">=",
        crate::ast::RefinementOp::Gt => ">",
        crate::ast::RefinementOp::Eq => "==",
        crate::ast::RefinementOp::Ne => "!=",
    }
}

// Diagnostic constructors are centralized here so each refinement verdict has
// one stable message and span authority.

fn literal_violated_diagnostic(
    literal_value: i64,
    clause: &RefinementClause,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T225,
        format!(
            "function body return statement violates declared return refinement: returned literal `{}` against predicate `{} {} {}`",
            literal_value,
            clause.field,
            format_refinement_op(clause.op),
            crate::type_check::format_refinement_rhs(&clause.rhs),
        ),
        Some(span),
    )
}

fn literal_timeout_diagnostic(literal_value: i64, span: Span) -> Diagnostic {
    Diagnostic::error(
        codes::T225,
        format!(
            "Z3 timed out within rlimit budget while discharging return refinement on literal `{}`",
            literal_value
        ),
        Some(span),
    )
}

fn symbolic_subsumption_violated_diagnostic(clause: &RefinementClause, span: Span) -> Diagnostic {
    Diagnostic::error(
        codes::T225,
        format!(
            "function body return statement violates declared return refinement: returned symbolic value's refinement does not subsume `{} {}`",
            format_refinement_op(clause.op),
            crate::type_check::format_refinement_rhs(&clause.rhs),
        ),
        Some(span),
    )
}

fn symbolic_subsumption_timeout_diagnostic(clause: &RefinementClause, span: Span) -> Diagnostic {
    // Symbolic subsumption intentionally uses the violation message for Timeout;
    // the corpus and precision gates pin this public diagnostic contract.
    symbolic_subsumption_violated_diagnostic(clause, span)
}

// ── Record-construction checks ─────────────────────────────────────────────

/// Emit refinement obligations for one record-construction site. Literal
/// cross-field pairs are discharged by Z3; symbolic pairs reject with T216.
/// Records without an AST definition have no source refinement clauses and are
/// skipped.
fn emit_record_construction_obligations(
    rc: &TypedRecordConstructExpr,
    construction_span: Span,
    record_def_by_name: &HashMap<String, &RecordDef>,
    diagnostics: &mut Vec<Diagnostic>,
    workload: &mut RefinementWorkload,
) {
    let Some(record_def) = record_def_by_name.get(&rc.type_name) else {
        return;
    };
    if record_def.refinements.is_empty() {
        return;
    }

    for clause in &record_def.refinements {
        match &clause.rhs {
            RefinementRhs::Field(rhs_field_name) => {
                // Cross-field clause. Look up both supplied values at the
                // construction site.
                let lhs_supplied = rc
                    .fields
                    .iter()
                    .find(|(n, _)| n == &clause.field)
                    .map(|(_, v)| v);
                let rhs_supplied = rc
                    .fields
                    .iter()
                    .find(|(n, _)| n == rhs_field_name)
                    .map(|(_, v)| v);
                let (Some(lhs), Some(rhs)) = (lhs_supplied, rhs_supplied) else {
                    continue; // construction site doesn't supply both fields
                };
                // The declaration validator owns cross-field shape
                // errors — T212 (LHS field not `i64`/`u256`) and T120/T219 (RHS
                // not a declared `i64` field). v2 owns only the DISCHARGE of a
                // well-shaped clause, so skip when the clause is mis-shaped;
                // otherwise discharge would double-emit alongside the
                // validator. Resolved supplied types equal the declared field
                // types for constructions that reach discharge.
                if !matches!(lhs.ty, Type::I64 | Type::U256) || !matches!(rhs.ty, Type::I64) {
                    continue;
                }
                // Z3 discharge admits only literal-literal pairs. Any symbolic
                // side is a conservative collector-side T216 rejection. Return
                // after that rejection so each construction reports at most one
                // refinement diagnostic.
                let (Some(lhs_value), Some(rhs_value)) =
                    (extract_int_literal(lhs), extract_int_literal(rhs))
                else {
                    diagnostics.push(Diagnostic::error(
                        codes::T216,
                        format!(
                            "cross-field refinement `{} {} {}` cannot be \
                             discharged: at least one of `{}` or `{}` is \
                             symbolic at this construction site. Wall 4 \
                             Step 4 commit #1 admits only literal-literal \
                             cross-field discharging; supply both fields as \
                             integer literals, or drop the cross-field clause.",
                            clause.field,
                            format_refinement_op(clause.op),
                            rhs_field_name,
                            clause.field,
                            rhs_field_name,
                        ),
                        Some(construction_span),
                    ));
                    return;
                };

                workload.obligations.push(RefinementObligation::CrossField {
                    clause: clause.clone(),
                    lhs_value,
                    rhs_value,
                    site: construction_span,
                    on_violated: crossfield_violated_diagnostic(
                        clause,
                        rhs_field_name,
                        lhs_value,
                        rhs_value,
                        construction_span,
                    ),
                    on_timeout: crossfield_timeout_diagnostic(
                        clause,
                        rhs_field_name,
                        lhs_value,
                        rhs_value,
                        construction_span,
                    ),
                });
            }
            _ => {
                // Single-field literal-RHS clause.
                let Some(supplied) = rc
                    .fields
                    .iter()
                    .find(|(n, _)| n == &clause.field)
                    .map(|(_, v)| v)
                else {
                    continue; // field not supplied; other passes catch it
                };
                // The shared `refinement_value_for` authority yields either a
                // narrow i64 or a wide u256 value.
                match (
                    crate::type_check::refinement_value_for(supplied),
                    &supplied.refinement,
                ) {
                    (Some(value), _) => {
                        // Literal values route Violated/Timeout to T210.
                        workload
                            .obligations
                            .push(RefinementObligation::LiteralFits {
                                clause: clause.clone(),
                                value,
                                site: construction_span,
                                on_violated: record_literal_violated_diagnostic(
                                    clause,
                                    value,
                                    construction_span,
                                ),
                                on_timeout: record_literal_timeout_diagnostic(
                                    clause,
                                    value,
                                    construction_span,
                                ),
                            });
                    }
                    (None, Some(supplied_clauses)) => {
                        // Pre-filter the syntactic subsumption fast path. The
                        // residual Z3 check builds the counterexample-bearing T215.
                        let syntactic = supplied_clauses
                            .iter()
                            .any(|s| crate::type_check::refinements_match(s, clause));
                        if !syntactic {
                            workload.obligations.push(
                                RefinementObligation::SubsumptionAtConstruction {
                                    actual: supplied_clauses.clone(),
                                    expected: clause.clone(),
                                    site: construction_span,
                                },
                            );
                        }
                    }
                    (None, None) => {
                        // A symbolic value without a sidecar cannot be queried;
                        // T211 points at the supplied expression.
                        diagnostics.push(record_symbolic_t211_diagnostic(clause, supplied.span));
                    }
                }
            }
        }
    }
}

/// T210 cross-field violation.
fn crossfield_violated_diagnostic(
    clause: &RefinementClause,
    rhs_field_name: &str,
    lhs_value: i64,
    rhs_value: i64,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T210,
        format!(
            "cross-field refinement violated at construction: \
             predicate `{} {} {}` is refutable at the supplied values \
             lhs = {}, rhs = {}",
            clause.field,
            format_refinement_op(clause.op),
            rhs_field_name,
            lhs_value,
            rhs_value,
        ),
        Some(span),
    )
}

/// T210 cross-field timeout.
fn crossfield_timeout_diagnostic(
    clause: &RefinementClause,
    rhs_field_name: &str,
    lhs_value: i64,
    rhs_value: i64,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T210,
        format!(
            "Z3 timed out within rlimit budget while \
             discharging cross-field refinement \
             `{} {} {}` at lhs = {}, rhs = {}",
            clause.field,
            format_refinement_op(clause.op),
            rhs_field_name,
            lhs_value,
            rhs_value,
        ),
        Some(span),
    )
}

/// T210 single-field literal violation.
fn record_literal_violated_diagnostic(
    clause: &RefinementClause,
    value: crate::ast::RefValue,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T210,
        format!(
            "record construction violates refinement: field `{}` supplied with literal `{}`, but predicate `{} {} {}` is refutable",
            clause.field,
            // The shared renderer is the message authority for narrow and wide values.
            crate::type_check::render_ref_value(&value),
            clause.field,
            format_refinement_op(clause.op),
            crate::type_check::format_refinement_rhs(&clause.rhs),
        ),
        Some(span),
    )
}

/// T210 single-field timeout.
fn record_literal_timeout_diagnostic(
    clause: &RefinementClause,
    value: crate::ast::RefValue,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T210,
        format!(
            "Z3 timed out within rlimit budget while discharging refinement on field `{}` against literal `{}`; treat as a budget-exceeded variant of T210 (no counterexample available)",
            clause.field,
            crate::type_check::render_ref_value(&value),
        ),
        Some(span),
    )
}

/// T211 for a symbolic field without preserved refinement evidence.
fn record_symbolic_t211_diagnostic(clause: &RefinementClause, span: Span) -> Diagnostic {
    Diagnostic::error(
        codes::T211,
        format!(
            "refinement check requires literal field value for `{}`; Wall 4 Step 1 does not support symbolic refinement RHS. Construct with an integer literal, or lift the computation into a non-refined intermediate. If the value came from a refined field read, inline it at the construction site (refinement is not preserved through `let` bindings or other intermediate expressions).",
            clause.field
        ),
        Some(span),
    )
}

/// Check one store `place.f = e` against the refinement clauses of the place's record type
/// (the design-by-contract spec's DBC0-3): a field store is a refinement sink with the
/// construction site's dispatch. The rule is keyed on the TYPE of the record `f` belongs to,
/// never on how the place was reached, so a nested field (`a.b.f`), an array element
/// (`arr[i].f`), an actor state field and a store through an `@Mut` parameter are one case.
///   * literal stored → `LiteralFits` carrying the T210 store message;
///   * symbolic value with a fact, past the syntactic fast path →
///     `SubsumptionAtConstruction` (T215, built at discharge);
///   * symbolic value with no fact → T211 at the stored value;
///   * a compound store (`f op= e`) stores the computed `f op e`, a value with no fact → T211;
///   * `f` takes part in a cross-field clause (`lo <= hi`), or is the bound side of a
///     `length()` clause: a store into one field cannot be checked against the clause, because
///     the other side's current value is not tracked, so the store is refused with T216 (the
///     spec's Q3: no new code) and the user reconstructs the record. A store into the array
///     side of a `length()` clause is not joined: the array's length is its type's.
///
/// Fails closed: a store the rule cannot vouch for is a diagnostic, never a silent accept. At
/// most one direct diagnostic per store; obligations are one per matching clause, as at a
/// construction site. Whole values stored into a local, a state field or an element are
/// checked where they were made (z3_corpus #27 for a refined record).
fn emit_field_store_obligations(
    store: &TypedAssignStmt,
    record_def_by_name: &HashMap<String, &RecordDef>,
    diagnostics: &mut Vec<Diagnostic>,
    workload: &mut RefinementWorkload,
) {
    let TypedExprKind::FieldAccess(access) = &store.place.kind else {
        return;
    };
    // The read side looks through a reference receiver (`infer_field_access_expr`); so here.
    let record_name = match &access.object.ty {
        Type::Ref(inner, _) => match inner.as_ref() {
            Type::Named(name, _) => name,
            _ => return,
        },
        Type::Named(name, _) => name,
        _ => return,
    };
    let Some(record_def) = record_def_by_name.get(record_name) else {
        return;
    };
    if record_def.refinements.is_empty() {
        return;
    }
    let field = access.field.as_str();

    for clause in &record_def.refinements {
        let joined = match &clause.rhs {
            RefinementRhs::Field(sibling) => clause.field == field || sibling == field,
            RefinementRhs::LengthOf(_) => clause.field == field,
            RefinementRhs::Literal(_) | RefinementRhs::LiteralWide(_) => false,
        };
        if joined {
            diagnostics.push(field_store_joined_clause_t216_diagnostic(
                clause,
                field,
                record_name,
                store.span,
            ));
            return;
        }
    }

    for clause in &record_def.refinements {
        if clause.field != field {
            continue;
        }
        if store.op.is_some() {
            diagnostics.push(field_store_compound_t211_diagnostic(clause, store.span));
            return;
        }
        match (
            crate::type_check::refinement_value_for(&store.value),
            &store.value.refinement,
        ) {
            (Some(value), _) => {
                workload
                    .obligations
                    .push(RefinementObligation::LiteralFits {
                        clause: clause.clone(),
                        value,
                        site: store.span,
                        on_violated: field_store_literal_violated_diagnostic(
                            clause, value, store.span,
                        ),
                        on_timeout: field_store_literal_timeout_diagnostic(
                            clause, value, store.span,
                        ),
                    });
            }
            (None, Some(stored_clauses)) => {
                let syntactic = stored_clauses
                    .iter()
                    .any(|s| crate::type_check::refinements_match(s, clause));
                if !syntactic {
                    workload
                        .obligations
                        .push(RefinementObligation::SubsumptionAtConstruction {
                            actual: stored_clauses.clone(),
                            expected: clause.clone(),
                            site: store.span,
                        });
                }
            }
            (None, None) => {
                diagnostics.push(field_store_symbolic_t211_diagnostic(
                    clause,
                    store.value.span,
                ));
                return;
            }
        }
    }
}

/// T210 for a literal store the clause refutes.
fn field_store_literal_violated_diagnostic(
    clause: &RefinementClause,
    value: crate::ast::RefValue,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T210,
        format!(
            "field store violates refinement: field `{}` assigned literal `{}`, but predicate `{} {} {}` is refutable",
            clause.field,
            crate::type_check::render_ref_value(&value),
            clause.field,
            format_refinement_op(clause.op),
            crate::type_check::format_refinement_rhs(&clause.rhs),
        ),
        Some(span),
    )
}

/// T210 for a literal store Z3 could not decide within budget.
fn field_store_literal_timeout_diagnostic(
    clause: &RefinementClause,
    value: crate::ast::RefValue,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T210,
        format!(
            "Z3 timed out within rlimit budget while discharging refinement on field `{}` against the stored literal `{}`; treat as a budget-exceeded variant of T210 (no counterexample available)",
            clause.field,
            crate::type_check::render_ref_value(&value),
        ),
        Some(span),
    )
}

/// T211 for a stored value with no fact.
fn field_store_symbolic_t211_diagnostic(clause: &RefinementClause, span: Span) -> Diagnostic {
    Diagnostic::error(
        codes::T211,
        format!(
            "refinement check requires a literal value for the store into field `{}`: the stored value carries no fact for `{} {} {}`. Store an integer literal or a value whose fact implies the predicate, or reconstruct the record.",
            clause.field,
            clause.field,
            format_refinement_op(clause.op),
            crate::type_check::format_refinement_rhs(&clause.rhs),
        ),
        Some(span),
    )
}

/// T211 for a compound store, whose stored value is computed from the field.
fn field_store_compound_t211_diagnostic(clause: &RefinementClause, span: Span) -> Diagnostic {
    Diagnostic::error(
        codes::T211,
        format!(
            "a compound store into field `{}` stores a computed value, which carries no fact for `{} {} {}`. Store the result as an integer literal or a value whose fact implies the predicate, or reconstruct the record.",
            clause.field,
            clause.field,
            format_refinement_op(clause.op),
            crate::type_check::format_refinement_rhs(&clause.rhs),
        ),
        Some(span),
    )
}

/// T216 for a store into a field that a cross-field or `length()` clause joins to a sibling.
fn field_store_joined_clause_t216_diagnostic(
    clause: &RefinementClause,
    field: &str,
    record: &str,
    span: Span,
) -> Diagnostic {
    Diagnostic::error_with_hint(
        codes::T216,
        format!(
            "field `{}` of `{}` takes part in the clause `{} {} {}`, which a store into one field cannot be checked against: the other side's current value is not tracked",
            field,
            record,
            clause.field,
            format_refinement_op(clause.op),
            crate::type_check::format_refinement_rhs(&clause.rhs),
        ),
        Some(span),
        format!(
            "reconstruct the record with every field supplied (`{record} {{ .. }}`), where the clause is checked, instead of storing into `{field}`"
        ),
    )
}

/// Check one variant construction on the supported single-field literal-RHS
/// surface:
///   * literal supplied → LiteralFits with the T220 variant message;
///   * symbolic, no preserved refinement → T211 directly (supplied-expr span);
///   * refined-value subsumption → outside the current collector surface.
///
/// `e.enum_name` is the construction's (possibly mangled) enum name; for
/// non-generic enums it equals the AST `EnumDef.name`, so the lookup hits.
/// Generic enums use a mangled name that does not match the source-definition
/// map and are outside this collector surface.
fn emit_variant_construction_obligations(
    e: &TypedEnumConstructExpr,
    construction_span: Span,
    enum_def_by_name: &HashMap<String, &EnumDef>,
    diagnostics: &mut Vec<Diagnostic>,
    workload: &mut RefinementWorkload,
) {
    let Some(enum_def) = enum_def_by_name.get(&e.enum_name) else {
        return;
    };
    let Some(variant) = enum_def.variants.get(e.variant_index as usize) else {
        return;
    };
    if variant.refinements.is_empty() {
        return;
    }
    let enum_name = &enum_def.name;
    let variant_name = &variant.name;

    for clause in &variant.refinements {
        // Field and LengthOf RHS clauses are handled by declaration validation;
        // discharge owns only single-field literal-RHS clauses here.
        let RefinementRhs::Literal(_) = &clause.rhs else {
            continue;
        };
        // Resolve clause.field → payload position via the variant's named
        // fields, then the positionally-matched supplied arg.
        let Some(idx) = variant
            .fields
            .iter()
            .position(|f| f.name.as_deref() == Some(clause.field.as_str()))
        else {
            continue;
        };
        let Some(supplied) = e.fields.get(idx) else {
            continue;
        };
        match (extract_int_literal(supplied), &supplied.refinement) {
            (Some(value), _) => {
                workload
                    .obligations
                    .push(RefinementObligation::LiteralFits {
                        clause: clause.clone(),
                        // PR-U3-b: variant refinements stay i64-only (wide deferred).
                        value: crate::ast::RefValue::Narrow(value),
                        site: construction_span,
                        on_violated: variant_literal_violated_diagnostic(
                            enum_name,
                            variant_name,
                            clause,
                            value,
                            construction_span,
                        ),
                        on_timeout: variant_literal_timeout_diagnostic(
                            enum_name,
                            variant_name,
                            clause,
                            value,
                            construction_span,
                        ),
                    });
            }
            (None, Some(_supplied_clauses)) => {
                // Variant construction-site subsumption is outside the current
                // collector surface.
            }
            (None, None) => {
                diagnostics.push(variant_symbolic_t211_diagnostic(
                    enum_name,
                    variant_name,
                    clause,
                    supplied.span,
                ));
            }
        }
    }
}

/// T220 variant literal violation.
fn variant_literal_violated_diagnostic(
    enum_name: &str,
    variant_name: &str,
    clause: &RefinementClause,
    value: i64,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T220,
        format!(
            "variant `{enum_name}::{variant_name}` construction violates refinement: payload field `{}` supplied with literal `{}`, but predicate `{} {} {}` is refutable",
            clause.field,
            value,
            clause.field,
            format_refinement_op(clause.op),
            crate::type_check::format_refinement_rhs(&clause.rhs),
        ),
        Some(span),
    )
}

/// T220 variant timeout.
fn variant_literal_timeout_diagnostic(
    enum_name: &str,
    variant_name: &str,
    clause: &RefinementClause,
    value: i64,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T220,
        format!(
            "Z3 timed out within rlimit budget discharging variant `{enum_name}::{variant_name}` refinement on payload field `{}` against literal `{}`",
            clause.field, value,
        ),
        Some(span),
    )
}

/// T211 for a symbolic variant payload without refinement evidence.
fn variant_symbolic_t211_diagnostic(
    enum_name: &str,
    variant_name: &str,
    clause: &RefinementClause,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T211,
        format!(
            "variant `{enum_name}::{variant_name}` refinement check requires literal payload value for `{}`; Wall 4 Step 6 commit #2 does not yet support symbolic payload values (narrowing through pattern matches lands in commit #3)",
            clause.field
        ),
        Some(span),
    )
}

/// T215 record-construction subsumption. Discharge supplies the Z3-dependent
/// counterexample or timeout detail; this function owns stable formatting.
pub(super) fn record_subsumption_t215_diagnostic(
    expected: &RefinementClause,
    actual: &[RefinementClause],
    detail: &str,
    site: Span,
) -> Diagnostic {
    let supplied_summary = actual
        .iter()
        .map(|s| {
            format!(
                "{} {}",
                format_refinement_op(s.op),
                crate::type_check::format_refinement_rhs(&s.rhs)
            )
        })
        .collect::<Vec<_>>()
        .join(" | ");
    Diagnostic::error(
        codes::T215,
        format!(
            "refinement supplied does not match destination's required predicate: field `{}` requires `{} {}`, but the supplied value carries `{}`. {detail}.",
            expected.field,
            format_refinement_op(expected.op),
            crate::type_check::format_refinement_rhs(&expected.rhs),
            supplied_summary,
        ),
        Some(site),
    )
}

/// Check one call expression against the callee's parameter refinements.
/// Pairs each arg with its parameter's refinement clauses:
///   * literal arg → LiteralFits carrying the T224 call-site message;
///   * symbolic arg WITH a refinement failing the syntactic fast-path →
///     SubsumptionAny carrying the (static) T224 subsumption message — both
///     Violated and Timeout verdicts route to the same T224;
///   * symbolic arg with no refinement → T211 directly (arg span).
///
/// The callee is looked up in `fn_def_by_name` by (module, bare name). The
/// callee's module is taken from the qualified callee name — a resolved call
/// carries `sig.qualified_name` = `"<module>::<fn>"` (universe.rs), and module
/// names are single-segment (`^[a-z_][a-z0-9_]*$`), so the qualifier IS the
/// callee's module. Using the CALLER's module here instead was a soundness gap:
/// a cross-module violating call (`math::need_positive(0)` from `main`, `where
/// x > 0`) would miss the lookup and compile silently. `tests/multi_file.rs`
/// pins cross-file T224 coverage. Unqualified calls fall back to the caller's
/// module.
fn emit_call_arg_obligations(
    c: &TypedCallExpr,
    call_span: Span,
    module_name: &str,
    fn_def_by_name: &HashMap<(String, String), &crate::ast::FnDef>,
    diagnostics: &mut Vec<Diagnostic>,
    workload: &mut RefinementWorkload,
) {
    let (callee_module, bare) = match c.callee.rsplit_once("::") {
        // `prefix` is the qualifier before the bare fn name; its last segment is
        // the (single-segment) module — robust even if a path carries extra
        // leading segments.
        Some((prefix, name)) => (prefix.rsplit("::").next().unwrap_or(prefix), name),
        None => (module_name, c.callee.as_str()),
    };
    let Some(fn_def) = fn_def_by_name
        .get(&(callee_module.to_string(), bare.to_string()))
        .or_else(|| fn_def_by_name.get(&(module_name.to_string(), bare.to_string())))
    else {
        return;
    };
    if fn_def.param_refinements.is_empty() {
        return;
    }
    // Messages use the bare callee name even when resolution stores a qualified
    // path such as `sigil::validate`.
    let callee_name = bare;
    let n = c.args.len().min(fn_def.params.len());
    for idx in 0..n {
        let param = &fn_def.params[idx];
        let arg = &c.args[idx];
        // Filter the AST's flat clause list by parameter name while preserving
        // source order.
        for clause in fn_def
            .param_refinements
            .iter()
            .filter(|cl| cl.field == param.name)
        {
            match (extract_int_literal(arg), &arg.refinement) {
                (Some(value), _) => {
                    workload
                        .obligations
                        .push(RefinementObligation::LiteralFits {
                            clause: clause.clone(),
                            // PR-U3-b: call-arg refinements stay i64-only (wide deferred).
                            value: crate::ast::RefValue::Narrow(value),
                            site: call_span,
                            on_violated: callarg_literal_violated_diagnostic(
                                callee_name,
                                idx,
                                clause,
                                value,
                                call_span,
                            ),
                            on_timeout: callarg_literal_timeout_diagnostic(
                                callee_name,
                                idx,
                                clause,
                                value,
                                call_span,
                            ),
                        });
                }
                (None, Some(supplied_clauses)) => {
                    // Symbolic arg carrying a refinement: syntactic fast-path
                    // pre-filter, else SubsumptionAny. The public contract emits
                    // the same T224 for Violated and Timeout, so on_violated ==
                    // on_timeout.
                    let subsumes = supplied_clauses
                        .iter()
                        .any(|s| crate::type_check::refinements_match(s, clause));
                    if !subsumes {
                        let diag =
                            callarg_subsumption_diagnostic(callee_name, idx, clause, call_span);
                        workload
                            .obligations
                            .push(RefinementObligation::SubsumptionAny {
                                actual: supplied_clauses.clone(),
                                expected: clause.clone(),
                                site: call_span,
                                on_violated: diag.clone(),
                                on_timeout: diag,
                            });
                    }
                }
                (None, None) => {
                    diagnostics.push(callarg_t211_diagnostic(callee_name, idx, clause, arg.span));
                }
            }
        }
    }
}

/// T224 call-argument literal violation.
fn callarg_literal_violated_diagnostic(
    callee_name: &str,
    idx: usize,
    clause: &RefinementClause,
    value: i64,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T224,
        format!(
            "function `{callee_name}` call-site violates parameter refinement: argument #{} (param `{}`) supplied with literal `{}`, but predicate `{} {} {}` is refutable",
            idx + 1,
            clause.field,
            value,
            clause.field,
            format_refinement_op(clause.op),
            crate::type_check::format_refinement_rhs(&clause.rhs),
        ),
        Some(span),
    )
}

/// T224 call-argument timeout.
fn callarg_literal_timeout_diagnostic(
    callee_name: &str,
    idx: usize,
    clause: &RefinementClause,
    value: i64,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T224,
        format!(
            "Z3 timed out within rlimit budget discharging function `{callee_name}` call-site refinement on argument #{} (param `{}`) against literal `{}`",
            idx + 1,
            clause.field,
            value,
        ),
        Some(span),
    )
}

/// T224 call-argument subsumption failure.
fn callarg_subsumption_diagnostic(
    callee_name: &str,
    idx: usize,
    clause: &RefinementClause,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T224,
        format!(
            "function `{callee_name}` call-site violates parameter refinement: argument #{} (param `{}`) supplied symbolic value carries a refinement that does not subsume the destination's `{} {}` predicate (Step 3 syntactic match + Z3 subsumption both failed)",
            idx + 1,
            clause.field,
            format_refinement_op(clause.op),
            crate::type_check::format_refinement_rhs(&clause.rhs),
        ),
        Some(span),
    )
}

/// T211 for a symbolic argument without refinement evidence.
fn callarg_t211_diagnostic(
    callee_name: &str,
    idx: usize,
    clause: &RefinementClause,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(
        codes::T211,
        format!(
            "function `{callee_name}` call-site argument #{} (param `{}`) is symbolic with no preserved refinement; Wall 4 Step 7 admits this only when (a) the arg is an integer literal, or (b) the arg carries a preserved refinement from an upstream refined-return call or refined-field read (Step 2/3 + Step 7 N38-S7). Inline a literal or refactor the upstream computation to preserve refinement.",
            idx + 1,
            clause.field,
        ),
        Some(span),
    )
}

// ── Generic TypedExpr visitor ─────────────────────────────────────────

/// Visit every relevant expression in a block subtree. The parent expression
/// span is the construction-site diagnostic anchor.
pub(crate) fn visit_block_constructs<F: FnMut(&TypedExpr)>(block: &TypedBlock, visit: &mut F) {
    visit_block_nodes(block, &mut |_: &TypedStmt| {}, visit);
}

/// Pre-order walk over every statement in `block`, nested blocks included: `if`, `match`
/// and loop bodies, and the blocks expressions carry (`handle`, effect clauses, `region`).
/// Calls the closure on each statement before descending into it.
fn visit_block_stmts<S: FnMut(&TypedStmt)>(block: &TypedBlock, visit: &mut S) {
    visit_block_nodes(block, visit, &mut |_: &TypedExpr| {});
}

/// The one walker under both entries: `on_stmt` sees every statement and `on_expr` every
/// expression, each before its children. Covers every `TypedStmt` and `TypedExprKind`
/// variant with no `_ =>` catch-all, so a block nested in a variant added later cannot be
/// skipped silently: the compiler's exhaustiveness check names the new arm.
fn visit_block_nodes<S: FnMut(&TypedStmt), F: FnMut(&TypedExpr)>(
    block: &TypedBlock,
    on_stmt: &mut S,
    on_expr: &mut F,
) {
    for stmt in &block.statements {
        visit_stmt_nodes(stmt, on_stmt, on_expr);
    }
}

fn visit_stmt_nodes<S: FnMut(&TypedStmt), F: FnMut(&TypedExpr)>(
    stmt: &TypedStmt,
    on_stmt: &mut S,
    on_expr: &mut F,
) {
    on_stmt(stmt);
    match stmt {
        TypedStmt::Let(s) => visit_expr_nodes(&s.value, on_stmt, on_expr),
        TypedStmt::Assign(s) => visit_expr_nodes(&s.value, on_stmt, on_expr),
        TypedStmt::Expr(s) => visit_expr_nodes(&s.expr, on_stmt, on_expr),
        TypedStmt::Return(s) => {
            if let Some(v) = &s.value {
                visit_expr_nodes(v, on_stmt, on_expr);
            }
        }
        TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
        TypedStmt::If(s) => {
            visit_expr_nodes(&s.condition, on_stmt, on_expr);
            visit_block_nodes(&s.then_branch, on_stmt, on_expr);
            visit_block_nodes(&s.else_branch, on_stmt, on_expr);
        }
        TypedStmt::Match(s) => {
            visit_expr_nodes(&s.scrutinee, on_stmt, on_expr);
            for arm in &s.arms {
                if let Some(g) = &arm.guard {
                    visit_expr_nodes(g, on_stmt, on_expr);
                }
                visit_block_nodes(&arm.body, on_stmt, on_expr);
            }
        }
        TypedStmt::While(s) => {
            visit_expr_nodes(&s.condition, on_stmt, on_expr);
            visit_block_nodes(&s.body, on_stmt, on_expr);
        }
        TypedStmt::ForIn(s) => {
            visit_expr_nodes(&s.iterable, on_stmt, on_expr);
            for inner in &s.body {
                visit_stmt_nodes(inner, on_stmt, on_expr);
            }
        }
        TypedStmt::ForRange(s) => {
            visit_expr_nodes(&s.start, on_stmt, on_expr);
            visit_expr_nodes(&s.end, on_stmt, on_expr);
            for inner in &s.body {
                visit_stmt_nodes(inner, on_stmt, on_expr);
            }
        }
    }
}

/// Recursive expression visitor. Calls the closure on the parent
/// expression first (pre-order), then recurses into every sub-expression.
/// The closure dispatches on `expr.kind` — record vs. variant
/// construction. Covers every TypedExprKind variant — the compiler's
/// exhaustiveness check enforces that new variants added in the future are
/// explicitly handled here (no `_ =>` catch-all).
fn visit_expr_nodes<S: FnMut(&TypedStmt), F: FnMut(&TypedExpr)>(
    expr: &TypedExpr,
    on_stmt: &mut S,
    on_expr: &mut F,
) {
    // Visit before recursing so outer construction sites are reported
    // in source order (parent before children).
    on_expr(expr);

    match &expr.kind {
        TypedExprKind::Literal(_) | TypedExprKind::Local(_) | TypedExprKind::StateField(_) => {}
        // PR-E3: recurse into f-string interpolation holes.
        TypedExprKind::FString(fs) => {
            for part in &fs.parts {
                if let crate::typed_ast::TypedFStringPart::Hole(h) = part {
                    visit_expr_nodes(h, on_stmt, on_expr);
                }
            }
        }
        TypedExprKind::Call(c) => {
            for a in &c.args {
                visit_expr_nodes(a, on_stmt, on_expr);
            }
        }
        TypedExprKind::Intrinsic(i) => {
            for a in &i.args {
                visit_expr_nodes(a, on_stmt, on_expr);
            }
        }
        TypedExprKind::ResultCtor(r) => visit_expr_nodes(&r.value, on_stmt, on_expr),
        TypedExprKind::EnumConstruct(e) => {
            for f in &e.fields {
                visit_expr_nodes(f, on_stmt, on_expr);
            }
        }
        TypedExprKind::Try(t) => visit_expr_nodes(&t.value, on_stmt, on_expr),
        TypedExprKind::Send(s) => {
            for a in &s.args {
                visit_expr_nodes(a, on_stmt, on_expr);
            }
        }
        TypedExprKind::Ask(a) => {
            for arg in &a.args {
                visit_expr_nodes(arg, on_stmt, on_expr);
            }
            visit_expr_nodes(&a.timeout, on_stmt, on_expr);
        }
        TypedExprKind::Spawn(s) => {
            for a in &s.args {
                visit_expr_nodes(a, on_stmt, on_expr);
            }
        }
        TypedExprKind::Binary(b) => {
            visit_expr_nodes(&b.lhs, on_stmt, on_expr);
            visit_expr_nodes(&b.rhs, on_stmt, on_expr);
        }
        TypedExprKind::RecordConstruct(rc) => {
            for (_, v) in &rc.fields {
                visit_expr_nodes(v, on_stmt, on_expr);
            }
        }
        TypedExprKind::FieldAccess(fa) => visit_expr_nodes(&fa.object, on_stmt, on_expr),
        TypedExprKind::CapRestrict(_) => {} // no sub-expressions (cap is a String name)
        TypedExprKind::CapSplit(cs) => visit_expr_nodes(&cs.amount, on_stmt, on_expr),
        TypedExprKind::CapDraw(cd) => visit_expr_nodes(&cd.amount, on_stmt, on_expr),
        TypedExprKind::Mint(m) => visit_expr_nodes(&m.target, on_stmt, on_expr),
        TypedExprKind::ArrayLit(al) => {
            for e in &al.elements {
                visit_expr_nodes(e, on_stmt, on_expr);
            }
        }
        TypedExprKind::Index(idx) => {
            visit_expr_nodes(&idx.array, on_stmt, on_expr);
            visit_expr_nodes(&idx.index, on_stmt, on_expr);
        }
        TypedExprKind::Slice(sl) => {
            visit_expr_nodes(&sl.array, on_stmt, on_expr);
            if let Some(s) = &sl.start {
                visit_expr_nodes(s, on_stmt, on_expr);
            }
            if let Some(e) = &sl.end {
                visit_expr_nodes(e, on_stmt, on_expr);
            }
        }
        TypedExprKind::ClosureConstruct(_) => {
            // Closure construction captures locals by name — sub-expressions
            // (the closure body) belong to a separate TypedFunction that's
            // walked at the module level. Don't recurse here.
        }
        TypedExprKind::Borrow(b) => visit_expr_nodes(&b.inner, on_stmt, on_expr),
        TypedExprKind::Grant(g) => {
            visit_expr_nodes(&g.cap, on_stmt, on_expr);
            visit_expr_nodes(&g.body, on_stmt, on_expr);
        }
        TypedExprKind::Handle(h) => visit_block_nodes(&h.body, on_stmt, on_expr),
        // Effect Handlers (EH3, C-VIS): descend into the new nodes.
        TypedExprKind::Perform(p) => {
            for arg in &p.args {
                visit_expr_nodes(arg, on_stmt, on_expr);
            }
        }
        TypedExprKind::ClauseHandle(c) => {
            visit_expr_nodes(&c.scrutinee, on_stmt, on_expr);
            for clause in &c.clauses {
                visit_block_nodes(&clause.body, on_stmt, on_expr);
            }
        }
        TypedExprKind::Resume(r) => visit_expr_nodes(&r.value, on_stmt, on_expr),
        TypedExprKind::Declassify(d) => {
            visit_expr_nodes(&d.value, on_stmt, on_expr);
            visit_expr_nodes(&d.cap, on_stmt, on_expr);
        }
        TypedExprKind::DeclassifyCt(d) => {
            visit_expr_nodes(&d.value, on_stmt, on_expr);
            visit_expr_nodes(&d.cap, on_stmt, on_expr);
        }
        TypedExprKind::ExternCall(e) => {
            for a in &e.args {
                visit_expr_nodes(a, on_stmt, on_expr);
            }
        }
        TypedExprKind::Region(r) => {
            visit_expr_nodes(&r.limit, on_stmt, on_expr);
            visit_block_nodes(&r.body, on_stmt, on_expr);
        }
        TypedExprKind::IndirectCall(ic) => {
            for a in &ic.args {
                visit_expr_nodes(a, on_stmt, on_expr);
            }
        }
    }
}
