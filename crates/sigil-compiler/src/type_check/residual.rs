//! F003 defense-in-depth: the whole-program residual-`Never` gate.
//!
//! The T279 SITE checks (`check_let` / `infer_arg_with_expected` /
//! `infer_tuple_expr` / `infer_array_lit_expr`) reject-and-POISON every known
//! channel through which a value-position `never` (`trap()`, an abortive
//! `perform`) can enter the typed AST. They are the PRIMARY defense and cannot
//! be replaced by this pass: `mangle_type` runs DURING type-check (the tuple
//! `type_name`, the generic monomorphization key), so a `Never` reaching those
//! calls ICEs before any post-pass could run.
//!
//! This gate is the BACKSTOP for every *other* channel — one we missed, or one
//! a future expression form / frontend / desugar adds. It runs at the end of
//! `check_with_warnings`, ONLY on an otherwise error-free program (exactly the
//! inputs that would proceed to AIR), and walks every type-carrying position of
//! the `TypedProgram`. Any residual `Never` in a VALUE position is rejected
//! with T279, so AIR's C-NEVER `panic!` backstops (`lower_type` /
//! `mangle_type`) can never fire on user source. Before this pass existed, the
//! "whole-program residual gate" that the C-NEVER comments referred to was
//! aspirational — the ICE arms were doing primary duty.
//!
//! THE one legal `Never` in an error-free typed AST — and the single carve-out
//! here — is the top-level type of a bare expression STATEMENT (`trap();`,
//! Tier A): its value is discarded, `check_block`'s divergence hook consumes
//! the type, and AIR's `lower_expr_stmt` allocates a phantom `Unit` dst for it
//! (never calling `lower_type(Never)`). The statement's CHILDREN are still
//! scanned — `f(trap());` as a statement is a value-position leak in the
//! argument even though the call's own result is discarded.
//!
//! NOT scanned: `TypedProgram::effect_ops` — an abortive operation's DECLARED
//! signature legitimately has `ret == Type::Never` (`fn raise(..) -> never`);
//! it is a type-level fact consumed by the EH machinery, not a value position.
//!
//! SCOPE BOUNDARY: this gate certifies the typed AST AS OF the end of
//! type-check. Post-typecheck passes that rewrite the `TypedProgram` before
//! AIR (`effect_desugar::desugar_effect_handlers`, which lowers the supported
//! evidence-passing subset and leaves residual forms E004-gated; `lower_fstrings`)
//! own their own output: a desugar that INTRODUCES a value-position `Never`
//! re-opens the ICE and must either preserve `never`-freedom or re-run this scan.
//!
//! Every `match` in this module is TOTAL — no `_` arms (the F005 "walker
//! forgot an arm" defense): a new `TypedStmt` / `TypedExprKind` /
//! `TypedPattern` variant fails to compile here until it is classified,
//! instead of silently failing OPEN (skipping the new variant's children and
//! letting a residual `Never` ride into an AIR ICE).

use super::{Type, render_type, resolve::type_contains_never};
use crate::diagnostics::{Diagnostic, codes};
use crate::span::Span;
use crate::typed_ast::{
    TypedBlock, TypedExpr, TypedExprKind, TypedFStringPart, TypedPattern, TypedProgram, TypedStmt,
};

/// Walk the whole typed program; push a T279 for every residual `Never` in a
/// value position. See the module doc for the statement-position carve-out.
pub(super) fn scan_residual_never(program: &TypedProgram, diagnostics: &mut Vec<Diagnostic>) {
    for module in &program.modules {
        for function in &module.functions {
            for p in &function.params {
                flag_if_never(
                    &p.ty,
                    "function parameter",
                    Some(function.span),
                    diagnostics,
                );
            }
            for c in &function.captures {
                flag_if_never(&c.ty, "closure capture", Some(function.span), diagnostics);
            }
            flag_if_never(
                &function.ret,
                "function return type",
                Some(function.span),
                diagnostics,
            );
            scan_block(&function.body, diagnostics);
        }
    }
    // Declared record/enum types cannot be `never` (`never` is non-denotable in
    // surface syntax), and a monomorphized instance whose args contained a
    // `Never` would have ICE'd at `mangle_type` when its key was built — so
    // these walks are provably-redundant today. Scanned anyway: they are the
    // registries AIR reconstructs field offsets / payload widths from, and a
    // future direct-insertion path must not become a silent hole.
    for (name, (_, fields)) in &program.records {
        for (field, ty) in fields {
            flag_if_never(ty, &format!("field `{name}.{field}`"), None, diagnostics);
        }
    }
    for (name, (_, variants)) in &program.enums {
        for (variant, payloads) in variants {
            for ty in payloads {
                flag_if_never(
                    ty,
                    &format!("payload of `{name}::{variant}`"),
                    None,
                    diagnostics,
                );
            }
        }
    }
}

fn flag_if_never(ty: &Type, context: &str, span: Option<Span>, diagnostics: &mut Vec<Diagnostic>) {
    if type_contains_never(ty) {
        diagnostics.push(Diagnostic::error(
            codes::T279,
            format!(
                "{context} has the diverging type `{}` — `trap()` (or an abortive \
                 `perform`) produces no value, so it cannot be bound, stored, or \
                 passed; use `trap();` as a standalone statement for its divergence. \
                 [residual-`never` gate: this value position escaped the site checks \
                 — worth reporting the source shape so a precise check can be added]",
                render_type(ty),
            ),
            span,
        ));
    }
}

fn scan_block(block: &TypedBlock, diagnostics: &mut Vec<Diagnostic>) {
    for stmt in &block.statements {
        scan_stmt(stmt, diagnostics);
    }
}

fn scan_stmt(stmt: &TypedStmt, diagnostics: &mut Vec<Diagnostic>) {
    match stmt {
        TypedStmt::Let(s) => {
            flag_if_never(&s.ty, "`let` binding type", Some(s.span), diagnostics);
            scan_expr(&s.value, diagnostics);
        }
        TypedStmt::Assign(s) => {
            scan_expr(&s.place, diagnostics);
            scan_expr(&s.value, diagnostics);
        }
        TypedStmt::Expr(s) => {
            // Tier-A carve-out: the TOP-LEVEL type of a bare expression
            // statement may be `Never` (`trap();` — its value is discarded and
            // the divergence hook / phantom-Unit-dst lowering consume it).
            // Children are still value positions.
            scan_expr_children(&s.expr, diagnostics);
        }
        TypedStmt::If(s) => {
            scan_expr(&s.condition, diagnostics);
            scan_block(&s.then_branch, diagnostics);
            scan_block(&s.else_branch, diagnostics);
        }
        TypedStmt::Match(s) => {
            scan_expr(&s.scrutinee, diagnostics);
            for arm in &s.arms {
                scan_pattern(&arm.pattern, arm.span, diagnostics);
                if let Some(guard) = &arm.guard {
                    scan_expr(guard, diagnostics);
                }
                scan_block(&arm.body, diagnostics);
            }
        }
        TypedStmt::While(s) => {
            scan_expr(&s.condition, diagnostics);
            scan_block(&s.body, diagnostics);
        }
        TypedStmt::ForIn(s) => {
            flag_if_never(
                &s.elem_type,
                "`for..in` element type",
                Some(s.iterable.span),
                diagnostics,
            );
            scan_expr(&s.iterable, diagnostics);
            for st in &s.body {
                scan_stmt(st, diagnostics);
            }
        }
        TypedStmt::ForRange(s) => {
            // Both bounds are VALUE positions (an `a..trap()` bound must flag).
            scan_expr(&s.start, diagnostics);
            scan_expr(&s.end, diagnostics);
            for st in &s.body {
                scan_stmt(st, diagnostics);
            }
        }
        TypedStmt::Return(s) => {
            if let Some(value) = &s.value {
                scan_expr(value, diagnostics);
            }
        }
        TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
    }
}

/// A VALUE-position expression: its own type must be `never`-free, and so must
/// every child.
fn scan_expr(expr: &TypedExpr, diagnostics: &mut Vec<Diagnostic>) {
    flag_if_never(&expr.ty, "expression", Some(expr.span), diagnostics);
    scan_expr_children(expr, diagnostics);
}

/// Recurse into an expression's children WITHOUT checking `expr.ty` itself —
/// the statement-position carve-out (see `scan_stmt`'s `Expr` arm). Children
/// are always value positions, so they go through `scan_expr`.
fn scan_expr_children(expr: &TypedExpr, diagnostics: &mut Vec<Diagnostic>) {
    match &expr.kind {
        // Actor-state (M2): a state-field read is a leaf like `Local` — its type
        // is the declared field type, already covered by `scan_expr` on the node.
        TypedExprKind::Literal(_) | TypedExprKind::Local(_) | TypedExprKind::StateField(_) => {}
        TypedExprKind::Call(e) => {
            for arg in &e.args {
                scan_expr(arg, diagnostics);
            }
        }
        // `TypedIntrinsicKind` payloads carry only `AirType`/`u32`/`String`
        // stamps — no `Type` children — so the args are the whole surface.
        TypedExprKind::Intrinsic(e) => {
            for arg in &e.args {
                scan_expr(arg, diagnostics);
            }
        }
        TypedExprKind::ResultCtor(e) => scan_expr(&e.value, diagnostics),
        TypedExprKind::EnumConstruct(e) => {
            for field in &e.fields {
                scan_expr(field, diagnostics);
            }
        }
        TypedExprKind::Try(e) => scan_expr(&e.value, diagnostics),
        TypedExprKind::Send(e) => {
            for arg in &e.args {
                scan_expr(arg, diagnostics);
            }
        }
        TypedExprKind::Ask(e) => {
            for arg in &e.args {
                scan_expr(arg, diagnostics);
            }
            scan_expr(&e.timeout, diagnostics);
        }
        TypedExprKind::Spawn(e) => {
            for arg in &e.args {
                scan_expr(arg, diagnostics);
            }
        }
        TypedExprKind::Binary(e) => {
            scan_expr(&e.lhs, diagnostics);
            scan_expr(&e.rhs, diagnostics);
        }
        TypedExprKind::RecordConstruct(e) => {
            for (_, field) in &e.fields {
                scan_expr(field, diagnostics);
            }
        }
        TypedExprKind::FieldAccess(e) => scan_expr(&e.object, diagnostics),
        // Cap name is a `String`; no expression / type children.
        TypedExprKind::CapRestrict(_) => {}
        TypedExprKind::CapSplit(e) => scan_expr(&e.amount, diagnostics),
        TypedExprKind::CapDraw(e) => scan_expr(&e.amount, diagnostics),
        TypedExprKind::Mint(e) => scan_expr(&e.target, diagnostics),
        TypedExprKind::ArrayLit(e) => {
            flag_if_never(
                &e.elem_type,
                "array element type",
                Some(expr.span),
                diagnostics,
            );
            for element in &e.elements {
                scan_expr(element, diagnostics);
            }
        }
        TypedExprKind::Index(e) => {
            flag_if_never(
                &e.elem_type,
                "index element type",
                Some(expr.span),
                diagnostics,
            );
            scan_expr(&e.array, diagnostics);
            scan_expr(&e.index, diagnostics);
        }
        TypedExprKind::Slice(e) => {
            flag_if_never(
                &e.elem_type,
                "slice element type",
                Some(expr.span),
                diagnostics,
            );
            scan_expr(&e.array, diagnostics);
            if let Some(start) = &e.start {
                scan_expr(start, diagnostics);
            }
            if let Some(end) = &e.end {
                scan_expr(end, diagnostics);
            }
        }
        TypedExprKind::ClosureConstruct(e) => {
            for capture in &e.captures {
                flag_if_never(&capture.ty, "closure capture", Some(expr.span), diagnostics);
            }
            for param in &e.param_types {
                flag_if_never(param, "closure parameter", Some(expr.span), diagnostics);
            }
            flag_if_never(
                &e.ret_type,
                "closure return type",
                Some(expr.span),
                diagnostics,
            );
        }
        TypedExprKind::Borrow(e) => scan_expr(&e.inner, diagnostics),
        TypedExprKind::Grant(e) => {
            scan_expr(&e.cap, diagnostics);
            scan_expr(&e.body, diagnostics);
        }
        TypedExprKind::Handle(e) => scan_block(&e.body, diagnostics),
        TypedExprKind::Perform(e) => {
            for arg in &e.args {
                scan_expr(arg, diagnostics);
            }
        }
        TypedExprKind::ClauseHandle(e) => {
            scan_expr(&e.scrutinee, diagnostics);
            for clause in &e.clauses {
                scan_block(&clause.body, diagnostics);
            }
        }
        TypedExprKind::Resume(e) => scan_expr(&e.value, diagnostics),
        TypedExprKind::Declassify(e) => {
            scan_expr(&e.value, diagnostics);
            scan_expr(&e.cap, diagnostics);
        }
        TypedExprKind::DeclassifyCt(e) => {
            scan_expr(&e.value, diagnostics);
            scan_expr(&e.cap, diagnostics);
        }
        TypedExprKind::ExternCall(e) => {
            for arg in &e.args {
                scan_expr(arg, diagnostics);
            }
        }
        TypedExprKind::Region(e) => {
            scan_expr(&e.limit, diagnostics);
            scan_block(&e.body, diagnostics);
        }
        TypedExprKind::IndirectCall(e) => {
            flag_if_never(
                &e.callee_ty,
                "indirect-call signature",
                Some(expr.span),
                diagnostics,
            );
            for arg in &e.args {
                scan_expr(arg, diagnostics);
            }
        }
        TypedExprKind::FString(e) => {
            for part in &e.parts {
                match part {
                    TypedFStringPart::Literal(_) => {}
                    TypedFStringPart::Hole(hole) => scan_expr(hole, diagnostics),
                }
            }
        }
    }
}

fn scan_pattern(pattern: &TypedPattern, span: Span, diagnostics: &mut Vec<Diagnostic>) {
    match pattern {
        TypedPattern::Literal(_)
        | TypedPattern::Range { .. }
        | TypedPattern::Wildcard
        | TypedPattern::Binding(_) => {}
        TypedPattern::EnumVariant { bindings, .. } => {
            for (_, ty) in bindings {
                flag_if_never(ty, "pattern binding", Some(span), diagnostics);
            }
        }
        TypedPattern::Array {
            elem_binds,
            rest,
            elem_ty,
            ..
        } => {
            flag_if_never(
                elem_ty,
                "array-pattern element type",
                Some(span),
                diagnostics,
            );
            for (_, ty) in elem_binds {
                flag_if_never(ty, "array-pattern binding", Some(span), diagnostics);
            }
            if let Some((_, ty)) = rest {
                flag_if_never(ty, "array-pattern rest binding", Some(span), diagnostics);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Literal, Ring, TaintLabel};
    use crate::name_resolution::DefId;
    use crate::registries::{EffectRegistry, EffectSet};
    use crate::typed_ast::{
        TypedBlock, TypedCallExpr, TypedExprStmt, TypedFunction, TypedFunctionKind,
        TypedIntrinsicExpr, TypedIntrinsicKind, TypedLetStmt, TypedModule, TypedReturnStmt,
    };
    use std::collections::BTreeMap;

    fn sp() -> Span {
        Span::new(0, 0)
    }

    /// A `trap()` expression exactly as `infer_intrinsic_call_expr` types it.
    fn trap_expr() -> TypedExpr {
        TypedExpr {
            ty: Type::Never,
            kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr {
                kind: TypedIntrinsicKind::Trap,
                args: vec![],
            }),
            span: sp(),
            refinement: None,
        }
    }

    fn int_expr() -> TypedExpr {
        TypedExpr {
            ty: Type::I64,
            kind: TypedExprKind::Literal(Literal::Int(0)),
            span: sp(),
            refinement: None,
        }
    }

    fn program_with_body(statements: Vec<TypedStmt>) -> TypedProgram {
        TypedProgram {
            modules: vec![TypedModule {
                def_id: DefId(0),
                name: "main".into(),
                ring: Ring::Inner,
                trusted: false,
                span: sp(),
                functions: vec![TypedFunction {
                    ret_flow: false,
                    name: "f".into(),
                    export_name: "f".into(),
                    kind: TypedFunctionKind::ModuleFunction,
                    externally_callable: false,
                    params: vec![],
                    captures: vec![],
                    ret: Type::I64,
                    ret_taint: TaintLabel::Public,
                    effects: EffectSet::empty(),
                    body: TypedBlock {
                        statements,
                        span: sp(),
                        guaranteed_return: true,
                    },
                    span: sp(),
                }],
            }],
            records: BTreeMap::new(),
            enums: BTreeMap::new(),
            effect_registry: EffectRegistry::default(),
            effect_ops: BTreeMap::new(),
        }
    }

    fn t279_count(program: &TypedProgram) -> usize {
        let mut diagnostics = Vec::new();
        scan_residual_never(program, &mut diagnostics);
        diagnostics
            .iter()
            .filter(|d| d.code().as_str() == "T279")
            .count()
    }

    #[test]
    fn statement_position_trap_is_legal() {
        // `trap();` — the Tier-A form. The bare expression statement's TOP-LEVEL
        // `Never` is the one legal survivor; the scan must stay silent.
        let program = program_with_body(vec![TypedStmt::Expr(TypedExprStmt {
            expr: trap_expr(),
            span: sp(),
        })]);
        assert_eq!(t279_count(&program), 0, "Tier-A `trap();` must stay legal");
    }

    #[test]
    fn residual_never_let_binding_is_flagged() {
        // A synthetic leak: a `let` whose binding type survived as `Never`
        // (as if a site check were missing). The gate must flag it.
        let program = program_with_body(vec![TypedStmt::Let(TypedLetStmt {
            name: "x".into(),
            mutable: false,
            ty: Type::Never,
            taint: None,
            value: trap_expr(),
            span: sp(),
        })]);
        assert!(
            t279_count(&program) >= 1,
            "leaked let binding must be flagged"
        );
    }

    #[test]
    fn residual_never_call_arg_in_statement_position_is_flagged() {
        // `f(trap());` as a bare statement: the CALL's own discarded result is
        // fine, but the `never` ARGUMENT is a value position — the carve-out
        // must not extend to children.
        let program = program_with_body(vec![TypedStmt::Expr(TypedExprStmt {
            expr: TypedExpr {
                ty: Type::Unit,
                kind: TypedExprKind::Call(TypedCallExpr {
                    callee: "g".into(),
                    args: vec![trap_expr()],
                }),
                span: sp(),
                refinement: None,
            },
            span: sp(),
        })]);
        assert!(
            t279_count(&program) >= 1,
            "never ARG of a statement-position call must be flagged"
        );
    }

    #[test]
    fn residual_never_inside_aggregate_type_is_flagged() {
        // The nested case: `Never` hidden INSIDE a binding's tuple type — the
        // `type_contains_never` recursion (not just a bare `Never`) has teeth.
        let program = program_with_body(vec![TypedStmt::Let(TypedLetStmt {
            name: "t".into(),
            mutable: false,
            ty: Type::Tuple(vec![Type::Never, Type::I64]),
            taint: None,
            value: int_expr(),
            span: sp(),
        })]);
        assert!(
            t279_count(&program) >= 1,
            "tuple-nested never must be flagged"
        );
    }

    #[test]
    fn residual_never_return_value_is_flagged() {
        // `return <never-expr>` (as if the site rejection were missing).
        let program = program_with_body(vec![TypedStmt::Return(TypedReturnStmt {
            value: Some(trap_expr()),
            span: sp(),
        })]);
        assert!(
            t279_count(&program) >= 1,
            "never return value must be flagged"
        );
    }

    #[test]
    fn clean_program_stays_clean() {
        let program = program_with_body(vec![TypedStmt::Return(TypedReturnStmt {
            value: Some(int_expr()),
            span: sp(),
        })]);
        assert_eq!(t279_count(&program), 0);
    }
}
