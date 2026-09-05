//! Unit tests for `type_check` — extracted from `mod.rs` in structural
//! extraction PR 10.
//!
//! Three test modules, preserved verbatim from their original location:
//!
//! * `step10_narrowing_helpers_tests` — Wall 4 Step 10 commit #1: unit
//!   tests for the predicate recognizer, negation table, and
//!   frame-compose helpers. See `docs/z3-theory-inventory.md` §6c.
//! * `step2_refinement_tests` — Wall 4 Step 2 V17 + V21 + V18: pins
//!   `refinements_match`, `compute_field_access_refinement`'s
//!   attachment behavior, and the V18 i64-only attachment gate.
//! * `pr_a_record_subst_tests` — PR A record-substitution coverage.
//!
//! `super::*` references inside each test module were updated to
//! `super::super::*` to account for the additional `tests` wrapper
//! module. Private items in `type_check/mod.rs` remain accessible:
//! Rust permits descendant modules to see their ancestors' private
//! items, so no `pub(super)` cascade was needed.

// ── Wall 4 Step 2 V17 + V21 + V18: unit tests for refinement helpers ──
//
// Placed at end-of-file per clippy::items_after_test_module — the test
// module must follow all production items in the file. The tests pin
// `refinements_match` (V17 triad), `compute_field_access_refinement`'s
// attachment behavior (V21 source-field-name preservation), and the V18
// i64-only attachment gate (3 cases: bool field, unknown record name,
// no record name).
#[cfg(test)]
mod step10_narrowing_helpers_tests {
    //! Wall 4 Step 10 commit #1: unit tests for the predicate
    //! recognizer, negation table, and frame-compose helpers. See
    //! `docs/z3-theory-inventory.md` §6c.
    //!
    //! Test coverage per N11-W4S10: exactly 12 positive shapes
    //! (6 relops × 2 orderings) + ≥6 negative shapes (both-literal,
    //! both-path, multi-segment path, arith RHS, bool RHS, non-Binary).

    use super::super::{
        binary_op_to_refinement_op, classify_narrowing_side, compose_narrowing_frame,
        extract_narrowing_predicate, flip_refinement_op, negate_refinement_clause,
    };
    use crate::ast::{
        BinaryExpr, BinaryOp, Expr, Literal, LiteralExpr, Path, PathExpr, RefinementClause,
        RefinementOp, RefinementRhs,
    };
    use crate::span::Span;

    fn s() -> Span {
        Span::default()
    }

    fn path_expr(name: &str) -> Expr {
        Expr::Path(PathExpr {
            path: Path {
                segments: vec![name.to_string()],
                type_args: vec![],
                span: s(),
            },
            span: s(),
        })
    }

    fn int_lit(n: i64) -> Expr {
        Expr::Literal(LiteralExpr {
            literal: Literal::Int(n),
            span: s(),
        })
    }

    fn bool_lit(b: bool) -> Expr {
        Expr::Literal(LiteralExpr {
            literal: Literal::Bool(b),
            span: s(),
        })
    }

    fn binary(lhs: Expr, op: BinaryOp, rhs: Expr) -> Expr {
        Expr::Binary(BinaryExpr {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
            span: s(),
        })
    }

    // ── N2-W4S10: negation table closed + involutive ──────────────────

    /// `Lt ↔ Ge` (and inverse).
    #[test]
    fn negate_lt_gives_ge() {
        let c = RefinementClause {
            field: "x".into(),
            op: RefinementOp::Lt,
            rhs: RefinementRhs::Literal(5),
            span: s(),
        };
        let neg = negate_refinement_clause(&c);
        assert_eq!(neg.op, RefinementOp::Ge);
        let back = negate_refinement_clause(&neg);
        assert_eq!(back.op, RefinementOp::Lt);
    }

    #[test]
    fn negate_le_gives_gt() {
        let c = RefinementClause {
            field: "x".into(),
            op: RefinementOp::Le,
            rhs: RefinementRhs::Literal(5),
            span: s(),
        };
        let neg = negate_refinement_clause(&c);
        assert_eq!(neg.op, RefinementOp::Gt);
        assert_eq!(negate_refinement_clause(&neg).op, RefinementOp::Le);
    }

    #[test]
    fn negate_gt_gives_le() {
        let c = RefinementClause {
            field: "x".into(),
            op: RefinementOp::Gt,
            rhs: RefinementRhs::Literal(5),
            span: s(),
        };
        assert_eq!(negate_refinement_clause(&c).op, RefinementOp::Le);
    }

    #[test]
    fn negate_ge_gives_lt() {
        let c = RefinementClause {
            field: "x".into(),
            op: RefinementOp::Ge,
            rhs: RefinementRhs::Literal(5),
            span: s(),
        };
        assert_eq!(negate_refinement_clause(&c).op, RefinementOp::Lt);
    }

    #[test]
    fn negate_eq_gives_ne() {
        let c = RefinementClause {
            field: "x".into(),
            op: RefinementOp::Eq,
            rhs: RefinementRhs::Literal(5),
            span: s(),
        };
        assert_eq!(negate_refinement_clause(&c).op, RefinementOp::Ne);
        let neg = negate_refinement_clause(&c);
        assert_eq!(negate_refinement_clause(&neg).op, RefinementOp::Eq);
    }

    #[test]
    fn negate_ne_gives_eq() {
        let c = RefinementClause {
            field: "x".into(),
            op: RefinementOp::Ne,
            rhs: RefinementRhs::Literal(5),
            span: s(),
        };
        assert_eq!(negate_refinement_clause(&c).op, RefinementOp::Eq);
    }

    /// Field + rhs unchanged by negation; only op flips.
    #[test]
    fn negate_preserves_field_and_rhs() {
        let c = RefinementClause {
            field: "my_var".into(),
            op: RefinementOp::Gt,
            rhs: RefinementRhs::Literal(42),
            span: s(),
        };
        let neg = negate_refinement_clause(&c);
        assert_eq!(neg.field, "my_var");
        assert_eq!(neg.rhs, RefinementRhs::Literal(42));
    }

    // ── binary_op_to_refinement_op: all 6 comparisons map; arith returns None ──

    #[test]
    fn binary_to_refinement_maps_all_six_comparisons() {
        assert_eq!(
            binary_op_to_refinement_op(BinaryOp::Lt),
            Some(RefinementOp::Lt)
        );
        assert_eq!(
            binary_op_to_refinement_op(BinaryOp::LtEq),
            Some(RefinementOp::Le)
        );
        assert_eq!(
            binary_op_to_refinement_op(BinaryOp::Gt),
            Some(RefinementOp::Gt)
        );
        assert_eq!(
            binary_op_to_refinement_op(BinaryOp::GtEq),
            Some(RefinementOp::Ge)
        );
        assert_eq!(
            binary_op_to_refinement_op(BinaryOp::Eq),
            Some(RefinementOp::Eq)
        );
        assert_eq!(
            binary_op_to_refinement_op(BinaryOp::NotEq),
            Some(RefinementOp::Ne)
        );
    }

    #[test]
    fn binary_to_refinement_rejects_arithmetic() {
        for op in [
            BinaryOp::Add,
            BinaryOp::Sub,
            BinaryOp::Mul,
            BinaryOp::Div,
            BinaryOp::Mod,
            BinaryOp::Shl,
            BinaryOp::Shr,
            BinaryOp::BitAnd,
            BinaryOp::BitOr,
        ] {
            assert_eq!(binary_op_to_refinement_op(op), None);
        }
    }

    // ── flip_refinement_op: side-swap normalization ──────────────────

    #[test]
    fn flip_relop_table() {
        assert_eq!(flip_refinement_op(RefinementOp::Lt), RefinementOp::Gt);
        assert_eq!(flip_refinement_op(RefinementOp::Le), RefinementOp::Ge);
        assert_eq!(flip_refinement_op(RefinementOp::Gt), RefinementOp::Lt);
        assert_eq!(flip_refinement_op(RefinementOp::Ge), RefinementOp::Le);
        assert_eq!(flip_refinement_op(RefinementOp::Eq), RefinementOp::Eq);
        assert_eq!(flip_refinement_op(RefinementOp::Ne), RefinementOp::Ne);
    }

    // ── N11-W4S10: 12 positive shapes (6 relops × 2 orderings) ───────

    fn assert_clause(
        cond: Expr,
        expected_name: &str,
        expected_op: RefinementOp,
        expected_rhs: i64,
    ) {
        let result = extract_narrowing_predicate(&cond)
            .unwrap_or_else(|| panic!("expected Some narrowing from {cond:?}"));
        let (name, clause) = result;
        assert_eq!(name, expected_name);
        assert_eq!(clause.field, expected_name);
        assert_eq!(clause.op, expected_op);
        assert_eq!(clause.rhs, RefinementRhs::Literal(expected_rhs));
    }

    #[test]
    fn recognize_lt_ident_first() {
        assert_clause(
            binary(path_expr("x"), BinaryOp::Lt, int_lit(5)),
            "x",
            RefinementOp::Lt,
            5,
        );
    }

    #[test]
    fn recognize_lt_literal_first() {
        // `5 < x` ⇔ `x > 5` (swap + flip)
        assert_clause(
            binary(int_lit(5), BinaryOp::Lt, path_expr("x")),
            "x",
            RefinementOp::Gt,
            5,
        );
    }

    #[test]
    fn recognize_lteq_ident_first() {
        assert_clause(
            binary(path_expr("x"), BinaryOp::LtEq, int_lit(5)),
            "x",
            RefinementOp::Le,
            5,
        );
    }

    #[test]
    fn recognize_lteq_literal_first() {
        // `5 <= x` ⇔ `x >= 5`
        assert_clause(
            binary(int_lit(5), BinaryOp::LtEq, path_expr("x")),
            "x",
            RefinementOp::Ge,
            5,
        );
    }

    #[test]
    fn recognize_gt_ident_first() {
        assert_clause(
            binary(path_expr("x"), BinaryOp::Gt, int_lit(5)),
            "x",
            RefinementOp::Gt,
            5,
        );
    }

    #[test]
    fn recognize_gt_literal_first() {
        // `5 > x` ⇔ `x < 5`
        assert_clause(
            binary(int_lit(5), BinaryOp::Gt, path_expr("x")),
            "x",
            RefinementOp::Lt,
            5,
        );
    }

    #[test]
    fn recognize_gteq_ident_first() {
        assert_clause(
            binary(path_expr("x"), BinaryOp::GtEq, int_lit(5)),
            "x",
            RefinementOp::Ge,
            5,
        );
    }

    #[test]
    fn recognize_gteq_literal_first() {
        // `5 >= x` ⇔ `x <= 5`
        assert_clause(
            binary(int_lit(5), BinaryOp::GtEq, path_expr("x")),
            "x",
            RefinementOp::Le,
            5,
        );
    }

    #[test]
    fn recognize_eq_ident_first() {
        assert_clause(
            binary(path_expr("x"), BinaryOp::Eq, int_lit(5)),
            "x",
            RefinementOp::Eq,
            5,
        );
    }

    #[test]
    fn recognize_eq_literal_first() {
        // Eq is self-symmetric: `5 == x` ⇔ `x == 5`
        assert_clause(
            binary(int_lit(5), BinaryOp::Eq, path_expr("x")),
            "x",
            RefinementOp::Eq,
            5,
        );
    }

    #[test]
    fn recognize_noteq_ident_first() {
        assert_clause(
            binary(path_expr("x"), BinaryOp::NotEq, int_lit(5)),
            "x",
            RefinementOp::Ne,
            5,
        );
    }

    #[test]
    fn recognize_noteq_literal_first() {
        // Ne is self-symmetric: `5 != x` ⇔ `x != 5`
        assert_clause(
            binary(int_lit(5), BinaryOp::NotEq, path_expr("x")),
            "x",
            RefinementOp::Ne,
            5,
        );
    }

    // ── N4-W4S10: negative integer literals via parser's `0 - n` desugaring ──

    #[test]
    fn negative_int_literal_recognized() {
        // `x > -5` parses as `Binary(Gt, Path(x), Binary(Sub, Int(0), Int(5)))`
        let neg_five = binary(int_lit(0), BinaryOp::Sub, int_lit(5));
        assert_clause(
            binary(path_expr("x"), BinaryOp::Gt, neg_five),
            "x",
            RefinementOp::Gt,
            -5,
        );
    }

    #[test]
    fn reversed_with_negative_literal() {
        // `-5 < x` ⇔ `x > -5`
        let neg_five = binary(int_lit(0), BinaryOp::Sub, int_lit(5));
        assert_clause(
            binary(neg_five, BinaryOp::Lt, path_expr("x")),
            "x",
            RefinementOp::Gt,
            -5,
        );
    }

    #[test]
    fn double_neg_rejected() {
        // `--5` parses as `Binary(Sub, Int(0), Binary(Sub, Int(0), Int(5)))`
        // Recognizer peels exactly ONE level (N4-W4S10); double-neg rejects.
        let double_neg = binary(
            int_lit(0),
            BinaryOp::Sub,
            binary(int_lit(0), BinaryOp::Sub, int_lit(5)),
        );
        let cond = binary(path_expr("x"), BinaryOp::Gt, double_neg);
        assert!(extract_narrowing_predicate(&cond).is_none());
    }

    // ── N11-W4S10: ≥6 negative shapes ────────────────────────────────

    #[test]
    fn reject_both_literals() {
        // `5 > 3` — neither side is a variable.
        let cond = binary(int_lit(5), BinaryOp::Gt, int_lit(3));
        assert!(extract_narrowing_predicate(&cond).is_none());
    }

    #[test]
    fn reject_both_paths() {
        // `x > y` — Field-RHS narrowing is anti-goaled (AG-W4S10-2 / V6).
        let cond = binary(path_expr("x"), BinaryOp::Gt, path_expr("y"));
        assert!(extract_narrowing_predicate(&cond).is_none());
    }

    #[test]
    fn reject_multi_segment_path() {
        // `foo::x > 0` — recognizer requires single-segment path.
        let multi_seg = Expr::Path(PathExpr {
            path: Path {
                segments: vec!["foo".to_string(), "x".to_string()],
                type_args: vec![],
                span: s(),
            },
            span: s(),
        });
        let cond = binary(multi_seg, BinaryOp::Gt, int_lit(0));
        assert!(extract_narrowing_predicate(&cond).is_none());
    }

    #[test]
    fn reject_arithmetic_rhs() {
        // `x > 1 + 2` — RHS is Binary(Add, ...) which is not a literal
        // and not the `Sub(0, n)` neg-literal shape.
        let arith = binary(int_lit(1), BinaryOp::Add, int_lit(2));
        let cond = binary(path_expr("x"), BinaryOp::Gt, arith);
        assert!(extract_narrowing_predicate(&cond).is_none());
    }

    #[test]
    fn reject_bool_literal_rhs() {
        // `x == true` — Literal::Bool is not a narrowing-eligible RHS
        // per N3-W4S10. Z3 has no bool refinement.
        let cond = binary(path_expr("x"), BinaryOp::Eq, bool_lit(true));
        assert!(extract_narrowing_predicate(&cond).is_none());
    }

    #[test]
    fn reject_float_literal_rhs() {
        // `x > 0.5` — Literal::Float not narrowing-eligible.
        let cond = binary(
            path_expr("x"),
            BinaryOp::Gt,
            Expr::Literal(LiteralExpr {
                literal: Literal::Float(0.5),
                span: s(),
            }),
        );
        assert!(extract_narrowing_predicate(&cond).is_none());
    }

    #[test]
    fn reject_non_binary_top_level() {
        // Bare path expression: `if x { ... }`. Not narrowing.
        assert!(extract_narrowing_predicate(&path_expr("x")).is_none());
        // Bare literal: `if true { ... }`.
        assert!(extract_narrowing_predicate(&bool_lit(true)).is_none());
        // Bare integer (would be a type error elsewhere): `if 5 { ... }`.
        assert!(extract_narrowing_predicate(&int_lit(5)).is_none());
    }

    #[test]
    fn reject_path_with_type_args() {
        // `x<i64> > 0` — type_args non-empty.
        let path_with_args = Expr::Path(PathExpr {
            path: Path {
                segments: vec!["x".to_string()],
                type_args: vec![crate::ast::TypeExpr {
                    path: Path {
                        segments: vec!["i64".to_string()],
                        type_args: vec![],
                        span: s(),
                    },
                    ref_kind: None,
                    deadline: vec![],
                    span: s(),
                    fn_type: None,
                    array_type: None,
                    tuple_type: None,
                }],
                span: s(),
            },
            span: s(),
        });
        let cond = binary(path_with_args, BinaryOp::Gt, int_lit(0));
        assert!(extract_narrowing_predicate(&cond).is_none());
    }

    // ── N1-W4S10: compose-walks-top-down ─────────────────────────────

    fn lit_clause(field: &str, op: RefinementOp, n: i64) -> RefinementClause {
        RefinementClause {
            field: field.to_string(),
            op,
            rhs: RefinementRhs::Literal(n),
            span: s(),
        }
    }

    #[test]
    fn compose_empty_stack_produces_single_clause() {
        let new_clause = lit_clause("x", RefinementOp::Gt, 0);
        let frame = compose_narrowing_frame(&[], "x", new_clause.clone());
        assert_eq!(frame.get("x").unwrap().len(), 1);
        assert_eq!(frame.get("x").unwrap()[0].op, RefinementOp::Gt);
    }

    #[test]
    fn compose_copies_forward_from_immediate_top() {
        // Outer frame has [x > 0]. New clause is x < 100. Composed
        // frame should contain [x > 0, x < 100].
        use std::collections::HashMap;
        let mut outer: HashMap<String, Vec<RefinementClause>> = HashMap::new();
        outer.insert("x".into(), vec![lit_clause("x", RefinementOp::Gt, 0)]);

        let frame = compose_narrowing_frame(
            std::slice::from_ref(&outer),
            "x",
            lit_clause("x", RefinementOp::Lt, 100),
        );
        let clauses = frame.get("x").unwrap();
        assert_eq!(clauses.len(), 2);
        assert_eq!(clauses[0].op, RefinementOp::Gt);
        assert_eq!(clauses[0].rhs, RefinementRhs::Literal(0));
        assert_eq!(clauses[1].op, RefinementOp::Lt);
        assert_eq!(clauses[1].rhs, RefinementRhs::Literal(100));
    }

    /// The LOAD-BEARING test for N1-W4S10: an intermediate frame with
    /// an UNRELATED variable must not hide the outer narrowing.
    #[test]
    fn compose_walks_past_intermediate_unrelated_frame() {
        // Stack from bottom to top: [(x:>0), (y:>0)]
        // Push (x<100) — should compose [x>0, x<100], NOT [x<100].
        use std::collections::HashMap;
        let mut frame_outer: HashMap<String, Vec<RefinementClause>> = HashMap::new();
        frame_outer.insert("x".into(), vec![lit_clause("x", RefinementOp::Gt, 0)]);
        let mut frame_middle: HashMap<String, Vec<RefinementClause>> = HashMap::new();
        frame_middle.insert("y".into(), vec![lit_clause("y", RefinementOp::Gt, 0)]);

        let stack = vec![frame_outer, frame_middle];
        let composed = compose_narrowing_frame(&stack, "x", lit_clause("x", RefinementOp::Lt, 100));
        let clauses = composed.get("x").unwrap();
        assert_eq!(
            clauses.len(),
            2,
            "compose must walk past intermediate y-only frame and find outer x clauses"
        );
        assert_eq!(clauses[0].op, RefinementOp::Gt);
        assert_eq!(clauses[1].op, RefinementOp::Lt);
    }

    #[test]
    fn compose_finds_most_recent_when_multiple_frames_have_name() {
        // Stack: [(x:>0), (x:>5)]
        // Push (x<100) — should compose with MOST RECENT (top-most)
        // entry, which is (x:>5).
        use std::collections::HashMap;
        let mut frame_outer: HashMap<String, Vec<RefinementClause>> = HashMap::new();
        frame_outer.insert("x".into(), vec![lit_clause("x", RefinementOp::Gt, 0)]);
        let mut frame_middle: HashMap<String, Vec<RefinementClause>> = HashMap::new();
        frame_middle.insert("x".into(), vec![lit_clause("x", RefinementOp::Gt, 5)]);

        let stack = vec![frame_outer, frame_middle];
        let composed = compose_narrowing_frame(&stack, "x", lit_clause("x", RefinementOp::Lt, 100));
        let clauses = composed.get("x").unwrap();
        // Pulls from top-most (x:>5), then appends new (x<100).
        // The deeper (x:>0) is NOT included — it was already shadowed
        // by the middle frame at lookup time, and composition follows
        // the same first-match-wins discipline.
        assert_eq!(clauses.len(), 2);
        assert_eq!(clauses[0].rhs, RefinementRhs::Literal(5));
        assert_eq!(clauses[1].rhs, RefinementRhs::Literal(100));
    }

    // ── classify_narrowing_side direct tests ─────────────────────────

    #[test]
    fn classify_recognizes_path_int_neg_int() {
        assert!(matches!(
            classify_narrowing_side(&path_expr("x")),
            Some(super::super::NarrowingSide::Ident(name)) if name == "x"
        ));
        assert!(matches!(
            classify_narrowing_side(&int_lit(42)),
            Some(super::super::NarrowingSide::IntLit(42))
        ));
        let neg = binary(int_lit(0), BinaryOp::Sub, int_lit(7));
        assert!(matches!(
            classify_narrowing_side(&neg),
            Some(super::super::NarrowingSide::IntLit(-7))
        ));
    }
}

#[cfg(test)]
mod step2_refinement_tests {
    use super::super::*;
    use crate::ast::{RefinementClause, RefinementOp};
    use crate::span::Span;

    fn span() -> Span {
        Span::default()
    }

    fn clause(field: &str, op: RefinementOp, literal: i64) -> RefinementClause {
        RefinementClause {
            field: field.to_owned(),
            op,
            rhs: crate::ast::RefinementRhs::Literal(literal),
            span: span(),
        }
    }

    // V17 triad: pinned behavior for refinements_match.

    #[test]
    fn v17_match_succeeds_for_equal_op_and_literal_ignoring_field_name() {
        // Source's `value >= 0` matches destination's `copy >= 0` —
        // field name is dropped per V2.
        let supplied = clause("value", RefinementOp::Ge, 0);
        let required = clause("copy", RefinementOp::Ge, 0);
        assert!(refinements_match(&supplied, &required));
    }

    #[test]
    fn v17_match_fails_on_literal_mismatch() {
        // `>= 0` does NOT match `>= 5` (different literal).
        let supplied = clause("v", RefinementOp::Ge, 0);
        let required = clause("v", RefinementOp::Ge, 5);
        assert!(!refinements_match(&supplied, &required));
    }

    #[test]
    fn v17_match_fails_on_op_mismatch() {
        // `>= 0` does NOT match `> 0` (different op, V14 syntactic).
        let supplied = clause("v", RefinementOp::Ge, 0);
        let required = clause("v", RefinementOp::Gt, 0);
        assert!(!refinements_match(&supplied, &required));
    }

    // V21: field name preserved on attachment. We attach via the
    // helper; the returned Vec carries the SOURCE record's field name,
    // not the destination's.

    #[test]
    fn v21_attached_refinement_carries_source_field_name() {
        let mut universe = TypeUniverse::default();
        universe.record_refinements.insert(
            "Index".to_owned(),
            vec![clause("value", RefinementOp::Ge, 0)],
        );

        let attached =
            compute_field_access_refinement(&universe, Some("Index"), "value", &Type::I64);
        let attached = attached.expect("V21: attachment must produce Some for refined i64 field");
        assert_eq!(attached.len(), 1, "expected exactly 1 clause attached");
        assert_eq!(
            attached[0].field, "value",
            "V21: attached clause must carry SOURCE field name (`value`), \
             not destination's field name. Got: {:?}",
            attached[0].field
        );
    }

    #[test]
    fn v18_non_i64_field_returns_none_silently() {
        // V18: non-i64 field returns None (the debug_assert! only fires
        // if a refinement clause leaks for a non-i64 field, which Step
        // 1's V12 parser-level check prevents).
        let universe = TypeUniverse::default();

        // bool field (not i64) → None even if record has refinements.
        let attached =
            compute_field_access_refinement(&universe, Some("Some"), "flag", &Type::Bool);
        assert!(
            attached.is_none(),
            "V18: non-i64 field must attach None; got {:?}",
            attached
        );
    }

    #[test]
    fn v18_unrecognized_record_returns_none() {
        let universe = TypeUniverse::default();
        let attached = compute_field_access_refinement(&universe, Some("Unknown"), "x", &Type::I64);
        assert!(attached.is_none());
    }

    #[test]
    fn v18_no_record_name_returns_none() {
        let universe = TypeUniverse::default();
        let attached = compute_field_access_refinement(&universe, None, "x", &Type::I64);
        assert!(attached.is_none());
    }

    // ── Wall 4 Step 3 V35 + V44: Z3 subsumption unit-test triad ─────
    //
    // V35 pins three subsuming pairs (Holds) and three non-subsuming
    // pairs (Violated with counterexample). At least one of the
    // non-subsuming pairs MUST excise 0 from the valid counterexample
    // range — this is V44/MC-S3-B's footgun catch: a lazy
    // `.unwrap_or(0)` implementation would report `x = 0` and fail
    // the range assertion.
    //
    // V44: counterexample is `Option<i64>`. On fresh evaluation (cache
    // miss), Z3 extracts a model and the counterexample is `Some(_)`.
    // Cache hits within the same test process re-use the cached value;
    // first-call test ordering guarantees a fresh extraction.

    #[cfg(feature = "solver")]
    use crate::z3_capability::{SubsumptionResult, check_refinement_subsumption};

    #[test]
    #[cfg(feature = "solver")]
    fn v35_subsumes_strict_subset() {
        // `>= 5` is a strict subset of `>= 0`; subsumption holds.
        let s = clause("a", RefinementOp::Ge, 5);
        let d = clause("b", RefinementOp::Ge, 0);
        assert!(matches!(
            check_refinement_subsumption(&s, &d),
            SubsumptionResult::Holds
        ));
    }

    #[test]
    #[cfg(feature = "solver")]
    fn v35_subsumes_equivalent_over_i64() {
        // `> -1` and `>= 0` define the same set on i64 → subsumption holds.
        let s = clause("a", RefinementOp::Gt, -1);
        let d = clause("b", RefinementOp::Ge, 0);
        assert!(matches!(
            check_refinement_subsumption(&s, &d),
            SubsumptionResult::Holds
        ));
    }

    #[test]
    #[cfg(feature = "solver")]
    fn v35_eq_subsumes_ge_when_literal_in_range() {
        // `== 5` is a singleton subset of `>= 0`; subsumption holds.
        let s = clause("a", RefinementOp::Eq, 5);
        let d = clause("b", RefinementOp::Ge, 0);
        assert!(matches!(
            check_refinement_subsumption(&s, &d),
            SubsumptionResult::Holds
        ));
    }

    #[test]
    #[cfg(feature = "solver")]
    fn v35_does_not_subsume_wrong_direction() {
        // `>= 0` does NOT subsume `>= 5`; counterexamples are {0..4}.
        // V44: counterexample is Option<i64>; Some on cache miss.
        let s = clause("a", RefinementOp::Ge, 0);
        let d = clause("b", RefinementOp::Ge, 5);
        match check_refinement_subsumption(&s, &d) {
            SubsumptionResult::Violated {
                counterexample: Some(cex),
            } => {
                assert!(
                    (0..5).contains(&cex),
                    "V35: expected counterexample in [0, 4]; got {cex}"
                );
            }
            SubsumptionResult::Violated {
                counterexample: None,
            } => {
                panic!(
                    "V44/V45: counterexample must be Some(_) on fresh \
                     evaluation. Got None — implementation may have \
                     swallowed get_model() or the cache lost the cex."
                );
            }
            other => panic!("expected Violated, got {other:?}"),
        }
    }

    /// V44 footgun catch (MC-S3-B): pin a pair where 0 is NOT a valid
    /// counterexample. The counterexample MUST be in [10, 99], excluding
    /// 0. A lazy `.unwrap_or(0)` implementation would fail here because
    /// 0 doesn't satisfy `x >= 10`.
    #[test]
    #[cfg(feature = "solver")]
    fn v35_counterexample_excludes_zero_when_range_starts_above_zero() {
        // `>= 10` does NOT subsume `>= 100`; counterexamples are {10..99}.
        let s = clause("a", RefinementOp::Ge, 10);
        let d = clause("b", RefinementOp::Ge, 100);
        match check_refinement_subsumption(&s, &d) {
            SubsumptionResult::Violated {
                counterexample: Some(cex),
            } => {
                assert!(
                    (10..100).contains(&cex),
                    "V44/MC-S3-B: expected counterexample in [10, 99] \
                     (NOT 0 — lazy `unwrap_or(0)` would fail here); \
                     got {cex}"
                );
                assert!(
                    cex != 0,
                    "V44/MC-S3-B: counterexample must NOT be 0 for this \
                     pair; lazy unwrap_or(0) implementation detected"
                );
            }
            SubsumptionResult::Violated {
                counterexample: None,
            } => {
                panic!("V44: counterexample must be Some(_) on fresh evaluation");
            }
            other => panic!("expected Violated, got {other:?}"),
        }
    }

    #[test]
    #[cfg(feature = "solver")]
    fn v35_eq_does_not_subsume_outside_point() {
        // `== 5` does NOT subsume `== 10`; only counterexample is 5.
        let s = clause("a", RefinementOp::Eq, 5);
        let d = clause("b", RefinementOp::Eq, 10);
        match check_refinement_subsumption(&s, &d) {
            SubsumptionResult::Violated {
                counterexample: Some(cex),
            } => {
                assert_eq!(
                    cex, 5,
                    "V35: `== 5` non-subsumption of `== 10` must counterexample x=5"
                );
            }
            other => panic!("expected Violated{{Some(5)}}, got {other:?}"),
        }
    }
}

#[cfg(test)]
mod pr_a_record_subst_tests {
    use super::super::*;
    use crate::ast::Literal;
    use crate::span::Span;
    use crate::typed_ast::TypedExprKind;

    fn span() -> Span {
        Span::default()
    }

    /// Build a TypedExpr with the given type, placeholder kind.
    fn typed(ty: Type) -> TypedExpr {
        TypedExpr {
            ty,
            kind: TypedExprKind::Literal(Literal::Int(0)),
            span: span(),
            refinement: None,
        }
    }

    /// N12-PRA: non-generic records bypass the helper entirely.
    #[test]
    fn pra_early_return_when_type_params_empty() {
        let result = build_record_construction_subst(
            &[],
            &[("a".into(), Type::I64)],
            &[("a".into(), typed(Type::I64))],
            None,
        );
        assert!(result.is_ok(), "non-generic records must early-return Ok");
        assert!(
            result.unwrap().is_empty(),
            "subst must be empty for non-generic records"
        );
    }

    /// Happy path: single type-param resolves from a single field.
    #[test]
    fn pra_single_field_infers_t() {
        let result = build_record_construction_subst(
            &["T".into()],
            &[("value".into(), Type::Generic("T".into()))],
            &[("value".into(), typed(Type::I64))],
            None,
        );
        let subst = result.expect("inference should succeed");
        assert_eq!(subst.get("T"), Some(&Type::I64));
    }

    /// N2-PRA: insert-time conflict detection. Field `a` binds T=i64,
    /// field `b` binds T=Str → ONE Conflict fault (N5-PRA: keyed
    /// per param, not per field-pair).
    #[test]
    fn pra_n2_n5_conflict_detected_at_insert_time_keyed_by_param() {
        let result = build_record_construction_subst(
            &["T".into()],
            &[
                ("a".into(), Type::Generic("T".into())),
                ("b".into(), Type::Generic("T".into())),
            ],
            &[
                ("a".into(), typed(Type::I64)),
                ("b".into(), typed(Type::Str)),
            ],
            None,
        );
        let faults = result.expect_err("conflict must surface as fault");
        // N5-PRA: EXACTLY ONE Conflict fault per param.
        let conflicts: Vec<_> = faults
            .iter()
            .filter(|f| matches!(f, RecordSubstFault::Conflict { .. }))
            .collect();
        assert_eq!(conflicts.len(), 1, "exactly one Conflict per param");
        // The Conflict names the param and lists BOTH contributors.
        match &conflicts[0] {
            RecordSubstFault::Conflict { param, bindings } => {
                assert_eq!(param, "T");
                assert_eq!(bindings.len(), 2, "Conflict must list all contributors");
                assert!(bindings.iter().any(|(n, _)| n == "a"));
                assert!(bindings.iter().any(|(n, _)| n == "b"));
            }
            _ => unreachable!(),
        }
    }

    /// N5-PRA: three conflicting fields produce ONE Conflict, not three.
    #[test]
    fn pra_n5_three_conflicting_fields_one_fault() {
        let result = build_record_construction_subst(
            &["T".into()],
            &[
                ("a".into(), Type::Generic("T".into())),
                ("b".into(), Type::Generic("T".into())),
                ("c".into(), Type::Generic("T".into())),
            ],
            &[
                ("a".into(), typed(Type::I64)),
                ("b".into(), typed(Type::Str)),
                ("c".into(), typed(Type::Bool)),
            ],
            None,
        );
        let faults = result.expect_err("conflict must surface");
        let conflicts: Vec<_> = faults
            .iter()
            .filter(|f| matches!(f, RecordSubstFault::Conflict { .. }))
            .collect();
        assert_eq!(
            conflicts.len(),
            1,
            "N5-PRA: T234 fires AT MOST ONCE per param regardless of contributor count"
        );
    }

    /// N3-PRA: annotation-pinned binding short-circuits to
    /// PinnedAnnotationViolated (T071-style), NOT Conflict (T234).
    #[test]
    fn pra_n3_annotation_pinned_routes_to_t071_not_t234() {
        let mut seed = HashMap::new();
        seed.insert("T".to_string(), Type::I64);
        let result = build_record_construction_subst(
            &["T".into()],
            &[("value".into(), Type::Generic("T".into()))],
            &[("value".into(), typed(Type::Str))],
            Some(&seed),
        );
        let faults = result.expect_err("annotation violation must surface");
        // PinnedAnnotationViolated, NOT Conflict.
        assert!(
            faults
                .iter()
                .any(|f| matches!(f, RecordSubstFault::PinnedAnnotationViolated { .. }))
        );
        assert!(
            !faults
                .iter()
                .any(|f| matches!(f, RecordSubstFault::Conflict { .. }))
        );
    }

    /// T233 / Unresolved: type-param doesn't appear in any field type
    /// AND no annotation → Unresolved fault.
    #[test]
    fn pra_unresolved_phantom_t() {
        let result = build_record_construction_subst(
            &["T".into()],
            &[("dummy".into(), Type::I64)],
            &[("dummy".into(), typed(Type::I64))],
            None,
        );
        let faults = result.expect_err("phantom T must surface as Unresolved");
        assert!(faults.iter().any(|f| matches!(
            f,
            RecordSubstFault::Unresolved { param } if param == "T"
        )));
    }

    /// N8-PRA: Multiple faults surface in a single helper call.
    /// Conflict on T AND Unresolved on U.
    #[test]
    fn pra_n8_multiple_faults_surface_together() {
        let result = build_record_construction_subst(
            &["T".into(), "U".into()],
            &[
                ("a".into(), Type::Generic("T".into())),
                ("b".into(), Type::Generic("T".into())),
                // U doesn't appear in any field
                ("c".into(), Type::I64),
            ],
            &[
                ("a".into(), typed(Type::I64)),
                ("b".into(), typed(Type::Str)),
                ("c".into(), typed(Type::I64)),
            ],
            None,
        );
        let faults = result.expect_err("expected faults");
        let has_conflict = faults
            .iter()
            .any(|f| matches!(f, RecordSubstFault::Conflict { param, .. } if param == "T"));
        let has_unresolved = faults
            .iter()
            .any(|f| matches!(f, RecordSubstFault::Unresolved { param } if param == "U"));
        assert!(has_conflict, "T conflict must be reported");
        assert!(has_unresolved, "U unresolved must be reported");
    }

    /// N6-PRA: When T conflicts, the resulting subst (if any) marks T as
    /// Type::Error to prevent cascade. Verify by NOT supplying a fault-
    /// triggering case but instead checking that a multi-field
    /// consistent record produces the right subst.
    #[test]
    fn pra_two_consistent_fields_resolve_t() {
        let result = build_record_construction_subst(
            &["T".into()],
            &[
                ("a".into(), Type::Generic("T".into())),
                ("b".into(), Type::Generic("T".into())),
            ],
            &[
                ("a".into(), typed(Type::I64)),
                ("b".into(), typed(Type::I64)),
            ],
            None,
        );
        let subst = result.expect("consistent fields should succeed");
        assert_eq!(subst.get("T"), Some(&Type::I64));
    }

    /// N10-PRA: helper calls `unify` for each field. Verify by
    /// confirming that nested Type::Named substitution works (which
    /// only works through unify's recursion).
    #[test]
    fn pra_n10_helper_uses_unify_for_nested_named() {
        let result = build_record_construction_subst(
            &["T".into()],
            &[(
                "wrapped".into(),
                Type::Named("Box".into(), vec![Type::Generic("T".into())]),
            )],
            &[(
                "wrapped".into(),
                typed(Type::Named("Box".into(), vec![Type::I64])),
            )],
            None,
        );
        let subst = result.expect("nested unification should succeed");
        assert_eq!(
            subst.get("T"),
            Some(&Type::I64),
            "unify should recurse into Type::Named args"
        );
    }

    /// Annotation seed propagates when no field-value contradicts it.
    #[test]
    fn pra_annotation_seed_propagates() {
        let mut seed = HashMap::new();
        seed.insert("T".to_string(), Type::I64);
        let result = build_record_construction_subst(
            &["T".into()],
            &[("value".into(), Type::Generic("T".into()))],
            &[("value".into(), typed(Type::I64))],
            Some(&seed),
        );
        let subst = result.expect("annotation seed should propagate");
        assert_eq!(subst.get("T"), Some(&Type::I64));
    }

    /// PR AF / N16-AF: the canonical `make_array_len_refinement`
    /// helper returns EXACTLY `[{ field: "@", op: Eq, rhs:
    /// Literal(size), span }]`. Operator drift (Ge/Gt/etc.) or
    /// wrong rhs shape would let `where @ == N` queries silently
    /// fail downstream, so this test pins the canonical shape.
    #[test]
    fn af_n16_array_len_refinement_canonical_shape() {
        use crate::ast::{RefinementOp, RefinementRhs};
        let span = crate::span::Span::with_source(0, 0, crate::span::SourceId::SYNTHETIC);
        let clauses = make_array_len_refinement(3, span).expect("builder must return Some");
        assert_eq!(clauses.len(), 1, "must produce exactly one clause");
        let clause = &clauses[0];
        assert_eq!(clause.field, "@", "field must be the magic `@` symbol");
        assert!(
            matches!(clause.op, RefinementOp::Eq),
            "operator must be Eq, found {:?}",
            clause.op
        );
        match &clause.rhs {
            RefinementRhs::Literal(n) => assert_eq!(*n, 3, "rhs literal must equal size"),
            other => panic!("rhs must be Literal, found {other:?}"),
        }
    }

    /// PR AF / N16-AF: differing sizes produce differing clauses
    /// (each clause carries the size in its rhs literal, so the
    /// builder is a true function of size).
    #[test]
    fn af_n16_array_len_refinement_size_propagates() {
        let span = crate::span::Span::with_source(0, 0, crate::span::SourceId::SYNTHETIC);
        let c3 = make_array_len_refinement(3, span).expect("builder must return Some");
        let c7 = make_array_len_refinement(7, span).expect("builder must return Some");
        assert_ne!(c3, c7, "different sizes must produce different clauses");
        if let crate::ast::RefinementRhs::Literal(n) = c7[0].rhs {
            assert_eq!(n, 7);
        } else {
            panic!("rhs must be Literal");
        }
    }
}

// ── PR-HK0: higher-kinded type resolution (resolve_type_expr_kinded) ───────────
//
// A use of an in-scope higher-kinded binder resolves to `Type::HktVar` (bare `F`)
// or `Type::HktApp` (applied `F<A>`), preserving the type arguments — NOT a bare
// `Type::Generic`, which would silently drop the `<…>`. Gated on the
// `in_scope_hkt` binder set, so a name absent from it keeps the pre-HKT nominal
// resolution.
#[cfg(test)]
mod hkt_resolve_tests {
    use super::super::resolve::resolve_type_expr_kinded;
    use super::super::{Type, TypeUniverse};
    use crate::ast::{Path, TypeExpr};
    use crate::span::{SourceId, Span};
    use std::collections::HashMap;

    fn syn() -> Span {
        Span::with_source(0, 0, SourceId::SYNTHETIC)
    }

    fn named_ty(name: &str, args: Vec<TypeExpr>) -> TypeExpr {
        TypeExpr {
            path: Path {
                segments: vec![name.to_owned()],
                type_args: args,
                span: syn(),
            },
            ref_kind: None,
            deadline: vec![],
            span: syn(),
            fn_type: None,
            array_type: None,
            tuple_type: None,
        }
    }

    #[test]
    fn bare_binder_resolves_to_hktvar() {
        let universe = TypeUniverse::default();
        let ty = named_ty("F", vec![]);
        let resolved =
            resolve_type_expr_kinded(&ty, &universe, &HashMap::new(), &[], &[("F".to_owned(), 1)]);
        assert_eq!(
            resolved,
            Type::HktVar {
                name: "F".to_owned(),
                arity: 1,
            }
        );
    }

    #[test]
    fn applied_binder_resolves_to_hktapp_preserving_args() {
        let universe = TypeUniverse::default();
        let ty = named_ty("F", vec![named_ty("i64", vec![])]);
        let resolved =
            resolve_type_expr_kinded(&ty, &universe, &HashMap::new(), &[], &[("F".to_owned(), 1)]);
        assert_eq!(
            resolved,
            Type::HktApp {
                ctor: "F".to_owned(),
                args: vec![Type::I64],
            }
        );
    }

    #[test]
    fn name_absent_from_binder_set_is_nominal() {
        // Without F in in_scope_hkt the HKT branch is inert — `F<i64>` resolves to
        // the ordinary nominal `Named`, exactly as before HKT.
        let universe = TypeUniverse::default();
        let ty = named_ty("F", vec![named_ty("i64", vec![])]);
        let resolved = resolve_type_expr_kinded(&ty, &universe, &HashMap::new(), &[], &[]);
        assert_eq!(resolved, Type::Named("F".to_owned(), vec![Type::I64]));
    }
}
