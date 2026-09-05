//! Refinement declaration validation, flow-sensitive narrowing, refinement-
//! producing intrinsics, and shared rendering utilities.
//!
//! Z3-backed construction, call, and return discharge lives solely in the
//! pure-then-discharge pipeline under `type_check_v2/`. A confinement test keeps
//! solver calls out of this module.
//!
//! The CI confinement list makes every module that carries the refinement
//! sidecar (`Option<Vec<RefinementClause>>`) explicit.
//!
//! ## Re-export contract
//!
//! `mod.rs` privately imports this module for sibling tests and re-exports the
//! helpers used through `crate::type_check::*` by the discharge and capability
//! modules.

use super::resolve::render_type;
use super::{MonomorphTracker, Type, TypeUniverse};
use crate::ast::Literal;
use crate::diagnostics::{Diagnostic, codes};
use crate::typed_ast::{
    TypedEnumConstructExpr, TypedExpr, TypedExprKind, TypedIndexExpr, TypedIntrinsicExpr,
    TypedIntrinsicKind,
};

// Flow-sensitive narrowing helpers. See `docs/z3-theory-inventory.md` §6c.

/// Build the exact `@ == size` sidecar for an array `.len()` result.
/// This is the sole constructor, and CI confines sidecar attachment sites.
pub(super) fn make_array_len_refinement(
    size: u32,
    span: crate::span::Span,
) -> Option<Vec<crate::ast::RefinementClause>> {
    Some(vec![crate::ast::RefinementClause {
        field: "@".to_string(),
        op: crate::ast::RefinementOp::Eq,
        rhs: crate::ast::RefinementRhs::Literal(size as i64),
        span,
    }])
}

/// PR P16 / N15-P16 + Phase-1 completion: SINGLE canonical builder for
/// `.first()` and `.last()` on BOTH `Type::Array` and `Type::Slice`.
///
/// Array (compile-time size known) → type-check-time fold to an
/// `EnumConstruct("Option", Some/None, [Index(arr, k)])` (the existing
/// `lower_enum_construct` AIR path), BYTE-IDENTICAL to the original PR-P16
/// behaviour: `[T;0]` folds to `None`, else `Some(arr[0])` (first) /
/// `Some(arr[size-1])` (last). The variant index is looked up dynamically
/// from `universe.enums["Option"]` (no hardcode, in case option.sigil
/// reorders).
///
/// Slice (length is RUNTIME) → a `SliceFirst`/`SliceLast` intrinsic whose AIR
/// emits the runtime branch `if len==0 { None } else { Some(load data[idx]) }`,
/// building the `Option` with the exact `lower_enum_construct` layout
/// (Some=0/None=1, payload@4 width-dispatched). Works for ANY element type
/// (the str/record payload is its fat-pointer/Ptr). This retires the
/// AG-P16-W deferral.
///
/// Both paths require `universe.enums.contains_key("Option")` — the lexical
/// ambient-include scan triggers on `Some(`/`None`/`?` user tokens, NOT on
/// intrinsic-synthesized constructors (AG-P16-P) — else T130, return Error.
pub(super) fn make_first_last_result(
    receiver: TypedExpr,
    is_first: bool,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
    span: crate::span::Span,
) -> TypedExpr {
    // Extract the element type (+ compile-time size for Array; Slice has no
    // static size → `None`). The caller's intrinsic pre-check already gated
    // `Type::Array | Type::Slice`; the `_` arm exists only for E0004.
    let (elem, array_size): (Type, Option<u32>) = match &receiver.ty {
        Type::Array { elem, size } => ((**elem).clone(), Some(*size)),
        Type::Slice(inner) => ((**inner).clone(), None),
        _ => {
            // Defensive: the caller's match should already gate this.
            // If we reach here something upstream has a soundness
            // bug — return Type::Error and let downstream cascade.
            return TypedExpr {
                ty: Type::Error,
                kind: TypedExprKind::Literal(Literal::Int(0)),
                span,
                refinement: None,
            };
        }
    };

    // AG-P16-P: Option must be in scope (shared by Array + Slice). The lexical
    // ambient-include scan in `compile_project` triggers on `Some(` / `None` /
    // `?` user-source tokens, NOT on intrinsic-synthesized constructors.
    // Fixtures using `.first()` / `.last()` MUST carry `use sigil::option;`.
    if !universe.enums.contains_key("Option") {
        diagnostics.push(Diagnostic::error(
            codes::T130,
            format!(
                "method `.{}()` returns `Option<T>` but `Option` is not in scope; add `use sigil::option;` at the top of the module",
                if is_first { "first" } else { "last" }
            ),
            Some(span),
        ));
        return TypedExpr {
            ty: Type::Error,
            kind: TypedExprKind::Literal(Literal::Int(0)),
            span,
            refinement: None,
        };
    }

    let option_ty = Type::Named("Option".to_string(), vec![elem.clone()]);

    // Slice: the length is RUNTIME, so emit a width-parametric intrinsic whose
    // AIR builds `if len==0 { None } else { Some(load data[idx]) }`. The
    // `Option` Some/None tags are the locked layout (Some=0/None=1), matched in
    // the wasm emission — so no variant-index threading is needed here.
    let Some(size) = array_size else {
        let kind = if is_first {
            TypedIntrinsicKind::SliceFirst {
                elem: crate::air::lower_type(&elem),
            }
        } else {
            TypedIntrinsicKind::SliceLast {
                elem: crate::air::lower_type(&elem),
            }
        };
        return TypedExpr {
            ty: option_ty,
            kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                kind,
                args: vec![receiver],
            }),
            span,
            refinement: None,
        };
    };

    // Array (size known): the original compile-time fold. Look up Some / None
    // variant indices from the universe. The expected positional layout (per
    // option.sigil): Some=0, None=1. Resolve by name so declaration-order drift
    // cannot silently change the intrinsic.
    let (_, variants) = &universe.enums["Option"];
    let some_index = variants
        .iter()
        .position(|(name, _)| name == "Some")
        .map(|i| i as u32);
    let none_index = variants
        .iter()
        .position(|(name, _)| name == "None")
        .map(|i| i as u32);
    let (some_idx, none_idx) = match (some_index, none_index) {
        (Some(s), Some(n)) => (s, n),
        _ => {
            diagnostics.push(Diagnostic::error(
                codes::T130,
                "stdlib `Option` enum is missing the `Some` or `None` variant; PR B's ambient include must be intact"
                    .to_string(),
                Some(span),
            ));
            return TypedExpr {
                ty: Type::Error,
                kind: TypedExprKind::Literal(Literal::Int(0)),
                span,
                refinement: None,
            };
        }
    };

    if size == 0 {
        // Compile-time fold: `.first()` / `.last()` on `[T; 0]` is
        // always `None`. No array access; no refinement.
        return TypedExpr {
            ty: option_ty,
            kind: TypedExprKind::EnumConstruct(TypedEnumConstructExpr {
                enum_name: "Option".to_string(),
                variant_index: none_idx,
                fields: Vec::new(),
            }),
            span,
            refinement: None,
        };
    }

    // size >= 1: produce `Some(arr[index])` where index = 0 (first)
    // or size-1 (last). The synthesized index expression uses the
    // existing `TypedIndexExpr` machinery — AIR's `lower_index_expr`
    // emits the bounds-check + LoadDynamic.
    let index_val = if is_first { 0i64 } else { (size - 1) as i64 };
    let index_expr = TypedExpr {
        ty: Type::I64,
        kind: TypedExprKind::Literal(Literal::Int(index_val)),
        span,
        refinement: None,
    };

    let elem_load = TypedExpr {
        ty: elem.clone(),
        kind: TypedExprKind::Index(TypedIndexExpr {
            array: Box::new(receiver),
            index: Box::new(index_expr),
            elem_type: elem.clone(),
            // Synthesized `.first()`/`.last()` access: not the SC-2 sole-setter
            // path, so it keeps the runtime trap (conservative; no regression).
            bounds_proven: false,
        }),
        span,
        refinement: None,
    };

    TypedExpr {
        ty: option_ty,
        kind: TypedExprKind::EnumConstruct(TypedEnumConstructExpr {
            enum_name: "Option".to_string(),
            variant_index: some_idx,
            fields: vec![elem_load],
        }),
        span,
        refinement: None,
    }
}

// T240 remains reserved for array `contains`; no implementation is exposed.

/// Negate a refinement comparison. The exhaustive match keeps the operation
/// involutive and forces new operators to define their complement.
pub(super) fn negate_refinement_clause(
    clause: &crate::ast::RefinementClause,
) -> crate::ast::RefinementClause {
    use crate::ast::RefinementOp;
    let op = match clause.op {
        RefinementOp::Lt => RefinementOp::Ge,
        RefinementOp::Le => RefinementOp::Gt,
        RefinementOp::Gt => RefinementOp::Le,
        RefinementOp::Ge => RefinementOp::Lt,
        RefinementOp::Eq => RefinementOp::Ne,
        RefinementOp::Ne => RefinementOp::Eq,
    };
    crate::ast::RefinementClause {
        field: clause.field.clone(),
        op,
        rhs: clause.rhs.clone(),
        span: clause.span,
    }
}

/// Map the six narrowing-eligible comparison operators to refinement operators.
pub(super) fn binary_op_to_refinement_op(
    op: crate::ast::BinaryOp,
) -> Option<crate::ast::RefinementOp> {
    use crate::ast::{BinaryOp as B, RefinementOp as R};
    Some(match op {
        B::Lt => R::Lt,
        B::LtEq => R::Le,
        B::Gt => R::Gt,
        B::GtEq => R::Ge,
        B::Eq => R::Eq,
        B::NotEq => R::Ne,
        // Non-comparison ops: not narrowing-eligible.
        B::Add
        | B::Sub
        | B::Mul
        | B::Div
        | B::Mod
        | B::Shl
        | B::Shr
        | B::BitAnd
        | B::BitOr
        | B::LogicalAnd
        | B::LogicalOr => {
            return None;
        }
    })
}

/// Reverse a comparison when normalization swaps its operands.
pub(super) fn flip_refinement_op(op: crate::ast::RefinementOp) -> crate::ast::RefinementOp {
    use crate::ast::RefinementOp;
    match op {
        RefinementOp::Lt => RefinementOp::Gt,
        RefinementOp::Le => RefinementOp::Ge,
        RefinementOp::Gt => RefinementOp::Lt,
        RefinementOp::Ge => RefinementOp::Le,
        RefinementOp::Eq => RefinementOp::Eq,
        RefinementOp::Ne => RefinementOp::Ne,
    }
}

/// One side of a recognized narrowing predicate.
pub(super) enum NarrowingSide {
    /// Bare single-segment identifier (no type-args, no field access).
    Ident(String),
    /// Integer literal, direct or through the parser's `0 - n` desugaring.
    IntLit(i64),
}

/// Classify a bare identifier or integer literal in a narrowing condition.
/// Negative literals may have the parser's one-level `0 - n` shape.
pub(super) fn classify_narrowing_side(e: &crate::ast::Expr) -> Option<NarrowingSide> {
    use crate::ast::{BinaryOp, Expr, Literal};
    match e {
        // Bare single-segment path: `x` (rejects `foo::x`, `x<T>`,
        // record-field access, etc.).
        Expr::Path(p) if p.path.segments.len() == 1 && p.path.type_args.is_empty() => {
            Some(NarrowingSide::Ident(p.path.segments[0].clone()))
        }
        // Positive integer literal: `5`. Rejects bool/float/string per N3-W4S10.
        Expr::Literal(lit) => match &lit.literal {
            Literal::Int(n) => Some(NarrowingSide::IntLit(*n)),
            _ => None,
        },
        // Parser desugars `-5` to `Binary(Sub, Int(0), Int(5))`. Peel
        // ONE level only per N4-W4S10 — nested `Binary(Sub, ..., ...)`
        // shapes (e.g., `0 - x` with x non-literal) reject.
        Expr::Binary(b) if matches!(b.op, BinaryOp::Sub) => {
            let (Expr::Literal(l), Expr::Literal(r)) = (&*b.lhs, &*b.rhs) else {
                return None;
            };
            match (&l.literal, &r.literal) {
                (Literal::Int(0), Literal::Int(n)) => Some(NarrowingSide::IntLit(-n)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Extract `<ident> RELOP <integer>` or its reversed form from an `if`
/// condition. Other shapes do not narrow.
///
/// The reversed-form normalization swap + flips the relop:
/// `5 < x` becomes `(name=x, op=Gt, rhs=5)`. Eq/Ne are self-symmetric.
pub(super) fn extract_narrowing_predicate(
    cond: &crate::ast::Expr,
) -> Option<(String, crate::ast::RefinementClause)> {
    use crate::ast::{BinaryExpr, Expr, RefinementClause, RefinementRhs};
    // Only binary expressions are narrowing candidates.
    let Expr::Binary(BinaryExpr { lhs, op, rhs, span }) = cond else {
        return None;
    };
    let refinement_op = binary_op_to_refinement_op(*op)?;
    let lhs_kind = classify_narrowing_side(lhs)?;
    let rhs_kind = classify_narrowing_side(rhs)?;
    match (lhs_kind, rhs_kind) {
        (NarrowingSide::Ident(name), NarrowingSide::IntLit(n)) => Some((
            name.clone(),
            RefinementClause {
                field: name,
                op: refinement_op,
                rhs: RefinementRhs::Literal(n),
                span: *span,
            },
        )),
        (NarrowingSide::IntLit(n), NarrowingSide::Ident(name)) => {
            // Reversed form: swap sides → flip relop. `5 < x ⇔ x > 5`.
            let flipped = flip_refinement_op(refinement_op);
            Some((
                name.clone(),
                RefinementClause {
                    field: name,
                    op: flipped,
                    rhs: RefinementRhs::Literal(n),
                    span: *span,
                },
            ))
        }
        // Both literals and both identifiers lack a single-variable narrowing.
        _ => None,
    }
}

/// Compose a narrowing frame with the most recent clauses for the same name.
///
/// This is the load-bearing fix for the nested-if conjunction case
/// (`if x > 0 { if x < 100 { need_in_range(x) } }`): without this,
/// `lookup_pattern_refinement`'s first-match-wins semantics would hide
/// the outer narrowing under the inner frame. With this, the composed
/// frame contains `[x>0, x<100]` and a single lookup returns both
/// clauses for Z3 to discharge as a conjunction.
///
/// Cross-name visibility comes from `lookup_pattern_refinement` skipping frames
/// that do not contain the requested name.
pub(super) fn compose_narrowing_frame(
    stack: &[std::collections::HashMap<String, Vec<crate::ast::RefinementClause>>],
    name: &str,
    new_clause: crate::ast::RefinementClause,
) -> std::collections::HashMap<String, Vec<crate::ast::RefinementClause>> {
    use std::collections::HashMap;
    let mut frame: HashMap<String, Vec<crate::ast::RefinementClause>> = HashMap::new();
    let mut clauses: Vec<crate::ast::RefinementClause> = Vec::new();

    // Intermediate frames may narrow another variable, so scan for this name.
    for existing in stack.iter().rev() {
        if let Some(prior) = existing.get(name) {
            clauses.extend(prior.iter().cloned());
            break;
        }
    }
    clauses.push(new_clause);
    frame.insert(name.to_string(), clauses);
    frame
}

/// Look up a pattern-bound refinement from inner to outer scope. Stored
/// pattern clauses are literal-RHS only; cross-field shapes do not propagate.
pub(super) fn lookup_pattern_refinement(
    tracker: &MonomorphTracker,
    name: &str,
) -> Option<Vec<crate::ast::RefinementClause>> {
    for frame in tracker.pattern_refinement_stack.iter().rev() {
        if let Some(clauses) = frame.get(name) {
            return Some(clauses.clone());
        }
    }
    None
}

/// Extract the concrete value used by the production single-field discharge path.
/// Wide `u256` literals retain all four limbs; non-literals return `None` and
/// route to preserved-refinement or fail-closed diagnostics.
pub(crate) fn refinement_value_for(expr: &TypedExpr) -> Option<crate::ast::RefValue> {
    match &expr.kind {
        TypedExprKind::Literal(crate::ast::Literal::Int(v)) => {
            Some(crate::ast::RefValue::Narrow(*v))
        }
        TypedExprKind::Literal(crate::ast::Literal::Int256(limbs)) => {
            Some(crate::ast::RefValue::Wide(*limbs))
        }
        _ => None,
    }
}

/// The single diagnostic renderer for narrow and wide refinement values.
/// `Wide` uses the same canonical decimal representation supplied to Z3.
pub(crate) fn render_ref_value(v: &crate::ast::RefValue) -> String {
    match v {
        crate::ast::RefValue::Narrow(n) => n.to_string(),
        crate::ast::RefValue::Wide(limbs) => crate::lexer::u256_to_decimal(*limbs),
    }
}

/// Compare refinement syntax by `(op, rhs)`, independent of the field name.
/// Semantic implication is handled by the Z3 subsumption query, not here.
pub(crate) fn refinements_match(
    supplied: &crate::ast::RefinementClause,
    required: &crate::ast::RefinementClause,
) -> bool {
    // Derived equality includes the RHS variant and payload.
    supplied.op == required.op && supplied.rhs == required.rhs
}

/// Validate refinement RHS shapes at declaration time, including `LengthOf`
/// resolution, so an unused invalid declaration still fails.
pub(super) fn validate_refinement_shapes_at_decls(
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for (type_name, clauses) in &universe.record_refinements {
        let Some((_type_params, declared_fields)) = universe.records.get(type_name) else {
            continue;
        };
        for clause in clauses {
            // LengthOf resolution: emits T217 (non-array RHS) / T213 (oversized
            // array) and returns the resolved (Literal-RHS) clause, or None when it
            // emitted. On None, move to the next clause (this clause is rejected).
            let resolved = match resolve_length_of_for_record(declared_fields, clause, diagnostics)
            {
                Some(c) => c,
                None => continue,
            };
            let clause = &resolved;

            // These shape checks depend only on the declared clause and field
            // types, so they run at declaration time even when the record is never
            // constructed. Precedence is resolver → T212 → T213-wide → T120 →
            // T219, first match per clause. `diagnostic_messages.rs` pins text.

            // T212: single-field refinement LHS must be i64/u256.
            let Some((_, field_ty)) = declared_fields.iter().find(|(n, _)| n == &clause.field)
            else {
                continue;
            };
            if !matches!(field_ty, Type::I64 | Type::U256) {
                diagnostics.push(Diagnostic::error(
                    codes::T212,
                    format!(
                        "refinement clause LHS in record `{type_name}` references field `{}` whose type is `{}`, but Wall 4 admits single-field refinement predicates only on `i64`- or `u256`-typed fields. To fix: (a) change the field's declared type to `i64`/`u256` in the record definition, OR (b) remove the `where {} ...` clause if the constraint isn't load-bearing, OR (c) add an `i64`-typed surrogate field (e.g., `{}_amount: i64`) and refine that one instead.",
                        clause.field, render_type(field_ty), clause.field, clause.field
                    ),
                    Some(clause.span),
                ));
                continue;
            }

            // T213: a wide (> i64) bound is admitted only on a u256 field.
            if matches!(clause.rhs, crate::ast::RefinementRhs::LiteralWide(_))
                && !matches!(field_ty, Type::U256)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T213,
                    format!(
                        "refinement clause on field `{}` uses a wide (> i64) bound, but the field's type is `{}`; a wide refinement bound is admitted only on a `u256` field.",
                        clause.field,
                        render_type(field_ty),
                    ),
                    Some(clause.span),
                ));
                continue;
            }

            // Cross-field clause `where a <op> b`: T120 (RHS field declared) then
            // T219 (RHS field i64).
            if let crate::ast::RefinementRhs::Field(rhs_field_name) = &clause.rhs {
                let Some((_, rhs_field_ty)) =
                    declared_fields.iter().find(|(n, _)| n == rhs_field_name)
                else {
                    diagnostics.push(Diagnostic::error(
                        codes::T120,
                        format!(
                            "cross-field refinement RHS references field `{}` which is not declared on record `{}`",
                            rhs_field_name, type_name
                        ),
                        Some(clause.span),
                    ));
                    continue;
                };
                if !matches!(rhs_field_ty, Type::I64) {
                    diagnostics.push(Diagnostic::error(
                        codes::T219,
                        format!(
                            "cross-field refinement RHS field `{}` has type `{}`; Wall 4 Step 4 admits cross-field clauses only when BOTH LHS and RHS are `i64` (anti-goal A9)",
                            rhs_field_name,
                            render_type(rhs_field_ty),
                        ),
                        Some(clause.span),
                    ));
                    continue;
                }
            }
        }
    }

    // ── Variant (enum) refinement shape checks (Phase-2 relocation) ──────────
    // Relocated verbatim from the construction walker
    // `check_variant_refinements_at_construction`. Declaration-time: reads only
    // the declared variant payload field names (`enum_variant_field_names`) +
    // declared payload types (`universe.enums`). Precedence mirrors the walker
    // (per clause: T222 LHS-i64 → RHS dispatch: LengthOf T221/T217, Field
    // T221/T219). Messages are byte-identical (pinned by diagnostic_messages.rs).
    for ((enum_name, variant_name), clauses) in &universe.enum_variant_refinements {
        if clauses.is_empty() {
            continue;
        }
        let Some(field_names) = universe
            .enum_variant_field_names
            .get(&(enum_name.clone(), variant_name.clone()))
        else {
            continue;
        };
        let Some((_type_params, variants)) = universe.enums.get(enum_name) else {
            continue;
        };
        let Some((_, payload_types)) = variants.iter().find(|(vn, _)| vn == variant_name) else {
            continue;
        };
        let n = field_names.len().min(payload_types.len());
        for clause in clauses {
            let Some(lhs_idx) = (0..n).find(|i| {
                field_names[*i]
                    .as_deref()
                    .map(|s| s == clause.field.as_str())
                    .unwrap_or(false)
            }) else {
                continue;
            };
            // T222: variant refinement LHS payload field must be i64.
            let lhs_ty = &payload_types[lhs_idx];
            if !matches!(lhs_ty, Type::I64) {
                diagnostics.push(Diagnostic::error(
                    codes::T222,
                    format!(
                        "variant `{enum_name}::{variant_name}` refinement references payload field `{}` which has type `{}`; Wall 4 Step 6 admits variant refinements only on `i64`-typed payload fields (per N6-S6 / A9-S6)",
                        clause.field,
                        render_type(lhs_ty),
                    ),
                    Some(clause.span),
                ));
                continue;
            }
            match &clause.rhs {
                crate::ast::RefinementRhs::LengthOf(rhs_field_name) => {
                    let Some(rhs_idx) = (0..n).find(|i| {
                        field_names[*i]
                            .as_deref()
                            .map(|s| s == rhs_field_name.as_str())
                            .unwrap_or(false)
                    }) else {
                        diagnostics.push(Diagnostic::error(
                            codes::T221,
                            format!(
                                "variant `{enum_name}::{variant_name}` refinement RHS `.length()` references payload field `{rhs_field_name}` which is not a named payload field of this variant"
                            ),
                            Some(clause.span),
                        ));
                        continue;
                    };
                    if !matches!(payload_types[rhs_idx], Type::Array { .. }) {
                        diagnostics.push(Diagnostic::error(
                            codes::T217,
                            format!(
                                "variant `{enum_name}::{variant_name}` refinement RHS `{rhs_field_name}.length()` references payload field of type `{}`; only `Type::Array {{ .. }}` payload fields are admitted (per A6-S6, A11-S5)",
                                render_type(&payload_types[rhs_idx]),
                            ),
                            Some(clause.span),
                        ));
                        continue;
                    }
                }
                crate::ast::RefinementRhs::Field(rhs_field_name) => {
                    let Some(rhs_idx) = (0..n).find(|i| {
                        field_names[*i]
                            .as_deref()
                            .map(|s| s == rhs_field_name.as_str())
                            .unwrap_or(false)
                    }) else {
                        diagnostics.push(Diagnostic::error(
                            codes::T221,
                            format!(
                                "variant `{enum_name}::{variant_name}` cross-field refinement RHS `{rhs_field_name}` is not a named payload field of this variant; per N19-S6 references scope to the variant's own payload"
                            ),
                            Some(clause.span),
                        ));
                        continue;
                    };
                    // T219: cross-field RHS payload field must be i64.
                    if !matches!(payload_types[rhs_idx], Type::I64) {
                        diagnostics.push(Diagnostic::error(
                            codes::T219,
                            format!(
                                "variant `{enum_name}::{variant_name}` cross-field refinement RHS field `{rhs_field_name}` has type `{}`; both LHS and RHS must be `i64`",
                                render_type(&payload_types[rhs_idx]),
                            ),
                            Some(clause.span),
                        ));
                        continue;
                    }
                }
                _ => {}
            }
        }
    }
}

/// Resolve `LengthOf(field)` to `Literal(array_size as i64)`. Returns:
///
/// - `Some(clause_clone_with_literal_rhs)` on successful resolution.
/// - `Some(clause)` (unmodified) when the clause's RHS is already
///   `Literal` or `Field` — pass-through.
/// - `None` after emitting T217 for a non-array or T213 for an oversized array.
///
/// Resolution clones the clause. Only directly owned arrays are supported;
/// slices, references, and other types fail closed.
pub(super) fn resolve_length_of_for_record(
    declared_fields: &[(String, Type)],
    clause: &crate::ast::RefinementClause,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<crate::ast::RefinementClause> {
    use crate::ast::RefinementRhs;
    let array_field = match &clause.rhs {
        RefinementRhs::LengthOf(name) => name,
        // Literal and Field pass through unchanged.
        _ => return Some(clause.clone()),
    };

    // Locate the array field; T120 already fires earlier if missing.
    let Some((_, field_ty)) = declared_fields.iter().find(|(n, _)| n == array_field) else {
        // Defensive: parser-level checks should have caught this.
        return Some(clause.clone());
    };

    let array_size = match field_ty {
        Type::Array { size, .. } => *size,
        // A11: Slice / Ref<Array> / any other type fires T217.
        other => {
            diagnostics.push(Diagnostic::error(
                codes::T217,
                format!(
                    "refinement RHS `{}.length()` references field `{}` which has type `{}`; Wall 4 Step 5 admits `.length()` only on directly-owned `Type::Array` fields",
                    array_field,
                    array_field,
                    render_type(other),
                ),
                Some(clause.span),
            ));
            return None;
        }
    };

    // The refinement encoding admits array lengths through i32::MAX.
    let signed_size = array_size as i64;
    if signed_size > i32::MAX as i64 {
        diagnostics.push(Diagnostic::error(
            codes::T213,
            format!(
                "array `{}` has size {} which exceeds i32::MAX ({}); the QF_LIA encoding the Z3 refinement solver uses can't represent constraints over arrays this large. To fix: (a) split the array into multiple fixed-size chunks (e.g., `[T; 1024]` records grouped into a parent record); OR (b) drop the `LengthOf` refinement on this field and rely on per-index runtime bounds-check; OR (c) reduce the declared size to ≤ 2147483647 if the upper bound is theoretical rather than load-bearing.",
                array_field,
                array_size,
                i32::MAX,
            ),
            Some(clause.span),
        ));
        return None;
    }

    // Resolved: replace LengthOf with Literal(array_size as i64).
    Some(crate::ast::RefinementClause {
        field: clause.field.clone(),
        op: clause.op,
        rhs: RefinementRhs::Literal(signed_size),
        span: clause.span,
    })
}

/// Render a refinement RHS for diagnostics:
/// - `Literal(v)` → `"5"`
/// - `LiteralWide(limbs)` → its canonical decimal representation
/// - `Field(name)` → `"hi"`
/// - `LengthOf(name)` → `"len.length()"`
pub(crate) fn format_refinement_rhs(rhs: &crate::ast::RefinementRhs) -> String {
    match rhs {
        crate::ast::RefinementRhs::Literal(v) => v.to_string(),
        crate::ast::RefinementRhs::LiteralWide(limbs) => crate::lexer::u256_to_decimal(*limbs),
        crate::ast::RefinementRhs::Field(name) => name.clone(),
        crate::ast::RefinementRhs::LengthOf(name) => format!("{name}.length()"),
    }
}
