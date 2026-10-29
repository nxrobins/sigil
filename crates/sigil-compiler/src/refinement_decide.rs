//! Native refinement decider: the solver-free backend of refinement discharge (the
//! design-by-contract spec's DBC-1, rung 1a). It decides the live refinement fragment
//! exactly, over the mathematical integers, so that its verdicts match the `Int` encoding
//! `z3_capability` sends to Z3: one value against a literal bound (`LiteralFits`), two
//! concrete values under one operator (`CrossField`), and subsumption between two
//! literal-bound clauses (`SubsumptionAny`, `SubsumptionAtConstruction`).
//!
//! Load-bearing constraints. It imports nothing from z3 and is compiled in both
//! configurations (`tests/quarantine_grep.rs` pins the import boundary). Every number is an
//! `i128` or a four-limb u256, and a wide value is never narrowed: no `as i64`, no
//! low-limb read (`tests/z3_guard_fences.rs` pins the source shape, the spec's DC-5). The
//! domain is ℤ, not i64, so `x <= i64::MIN` does not imply `x == i64::MIN` and a witness may
//! lie outside i64 (DC-6). Unwired in rung 1a: the orchestrator calls only Z3 until DBC-1b;
//! the solver lane's `dbc1_native_decider_agrees_with_z3` (in `type_check_v2`) compares the
//! two backends on an exhaustive grid, and the known-answer tests below run in every lane.

use std::cmp::Ordering;

use crate::ast::{RefValue, RefinementClause, RefinementOp, RefinementRhs};

/// The verdict of a native decision. It never times out, so there is no third variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeVerdict {
    /// The predicate holds at the supplied value(s).
    Holds,
    /// The predicate is refuted at the supplied value(s).
    Violated,
}

/// The verdict of a native subsumption decision. A refutation carries a witness `x` that
/// satisfies the supplied clause and not the required one, when the witness fits an i64 (as
/// Z3's model extraction reports it); a witness outside i64, or a wide bound, which is refused
/// without proof exactly as `check_refinement_subsumption` refuses it, reports `None`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeSubsumption {
    /// Every integer the supplied clause admits, the required clause admits.
    Holds,
    /// Some integer the supplied clause admits, the required clause refuses.
    Violated { counterexample: Option<i64> },
}

/// Does `value op bound` hold over ℤ? `LiteralFits`: `value` is the supplied field value and
/// `bound` the clause's literal, which may be wide.
pub fn decide_literal_fits(clause: &RefinementClause, value: RefValue) -> NativeVerdict {
    let value = match value {
        RefValue::Narrow(n) => Integer::narrow(n),
        RefValue::Wide(limbs) => Integer::wide(limbs),
    };
    verdict(satisfies(clause.op, value, literal_bound(clause)))
}

/// Does `lhs op rhs` hold over ℤ? `CrossField`: both values are concrete i64 field values and
/// the clause's operator is applied in its declared operand order, as the Z3 route does; the
/// clause's RHS names the sibling field and is not consulted.
pub fn decide_cross_field(clause: &RefinementClause, lhs: i64, rhs: i64) -> NativeVerdict {
    verdict(satisfies(
        clause.op,
        Integer::narrow(lhs),
        Integer::narrow(rhs),
    ))
}

/// Does every integer `supplied` admits satisfy `required`? Each literal-bound clause denotes
/// a half-line, a point, or ℤ minus a point, so inclusion is a closed case table; a refutation
/// names a witness. A wide bound on either side fails closed with no witness, mirroring the Z3
/// route, which is i64-only.
pub fn decide_subsumption(
    supplied: &RefinementClause,
    required: &RefinementClause,
) -> NativeSubsumption {
    let (Some(supplied), Some(required)) = (Shape::of(supplied), Shape::of(required)) else {
        return NativeSubsumption::Violated {
            counterexample: None,
        };
    };
    match separating_witness(supplied, required) {
        None => NativeSubsumption::Holds,
        Some(witness) => NativeSubsumption::Violated {
            counterexample: i64::try_from(witness).ok(),
        },
    }
}

fn verdict(holds: bool) -> NativeVerdict {
    if holds {
        NativeVerdict::Holds
    } else {
        NativeVerdict::Violated
    }
}

/// `lhs op rhs` over ℤ.
fn satisfies(op: RefinementOp, lhs: Integer, rhs: Integer) -> bool {
    match op {
        RefinementOp::Le => lhs <= rhs,
        RefinementOp::Lt => lhs < rhs,
        RefinementOp::Ge => lhs >= rhs,
        RefinementOp::Gt => lhs > rhs,
        RefinementOp::Eq => lhs == rhs,
        RefinementOp::Ne => lhs != rhs,
    }
}

/// The literal a clause compares against. `Field` and `length()` clauses have their own routes
/// (the cross-field query, and resolution before discharge) and never reach a decider, exactly
/// as `z3_capability::check_refinement` refuses them: reaching here with one is a compiler bug.
fn literal_bound(clause: &RefinementClause) -> Integer {
    match &clause.rhs {
        RefinementRhs::Literal(v) => Integer::narrow(*v),
        RefinementRhs::LiteralWide(limbs) => Integer::wide(*limbs),
        RefinementRhs::Field(_) | RefinementRhs::LengthOf(_) => unreachable!(
            "the native decider decides literal-bound clauses only; Field and LengthOf \
             clauses have their dedicated routes"
        ),
    }
}

/// An integer of the fragment, ordered as a mathematical integer. Every narrow value and bound
/// fits an i128; a wide value that does not (at or above 2^127) compares above every integer
/// that does, and against another such value by its limbs, most significant first. The
/// representation is canonical, so derived equality is integer equality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Integer {
    Small(i128),
    Big([u64; 4]),
}

impl Integer {
    fn narrow(n: i64) -> Self {
        Integer::Small(i128::from(n))
    }

    /// A u256 from its four little-endian limbs (the lexer's representation): the value is the
    /// sum of `limb_k * 2^(64 k)`. Below 2^127 it is an i128, built by widening, never by
    /// narrowing.
    fn wide(limbs: [u64; 4]) -> Self {
        let [low, second, third, top] = limbs;
        if third == 0 && top == 0 && second < 1u64 << 63 {
            Integer::Small((i128::from(second) << 64) | i128::from(low))
        } else {
            Integer::Big(limbs)
        }
    }
}

impl Ord for Integer {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Integer::Small(a), Integer::Small(b)) => a.cmp(b),
            (Integer::Small(_), Integer::Big(_)) => Ordering::Less,
            (Integer::Big(_), Integer::Small(_)) => Ordering::Greater,
            (Integer::Big(a), Integer::Big(b)) => a.iter().rev().cmp(b.iter().rev()),
        }
    }
}

impl PartialOrd for Integer {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// The set of integers a literal-bound clause admits, with inclusive bounds: over ℤ, `x < b`
/// is `x <= b - 1` and `x > b` is `x >= b + 1`, and an i64 bound leaves i128 room for both.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Shape {
    AtMost(i128),
    AtLeast(i128),
    Exactly(i128),
    Except(i128),
}

impl Shape {
    /// `None` for a wide bound: the subsumption route is i64-only on both backends.
    fn of(clause: &RefinementClause) -> Option<Self> {
        let bound = match &clause.rhs {
            RefinementRhs::Literal(v) => i128::from(*v),
            RefinementRhs::LiteralWide(_) => return None,
            RefinementRhs::Field(_) | RefinementRhs::LengthOf(_) => unreachable!(
                "the native decider decides literal-bound clauses only; Field and LengthOf \
                 clauses have their dedicated routes"
            ),
        };
        Some(match clause.op {
            RefinementOp::Le => Shape::AtMost(bound),
            RefinementOp::Lt => Shape::AtMost(bound - 1),
            RefinementOp::Ge => Shape::AtLeast(bound),
            RefinementOp::Gt => Shape::AtLeast(bound + 1),
            RefinementOp::Eq => Shape::Exactly(bound),
            RefinementOp::Ne => Shape::Except(bound),
        })
    }

    fn contains(self, x: i128) -> bool {
        match self {
            Shape::AtMost(b) => x <= b,
            Shape::AtLeast(b) => x >= b,
            Shape::Exactly(b) => x == b,
            Shape::Except(b) => x != b,
        }
    }
}

/// An integer in `supplied` and not in `required`, or `None` when `supplied ⊆ required`. The
/// witness is deterministic: the case table names it. Every arm's witness is checked against
/// both shapes in debug builds and by the known-answer tests.
fn separating_witness(supplied: Shape, required: Shape) -> Option<i128> {
    use Shape::{AtLeast, AtMost, Exactly, Except};
    let witness = match (supplied, required) {
        (AtMost(a), AtMost(b)) => {
            if a <= b {
                return None;
            }
            a
        }
        (AtMost(a), AtLeast(b)) => a.min(b - 1),
        (AtMost(a), Exactly(b)) => {
            if a == b {
                a - 1
            } else {
                a
            }
        }
        (AtMost(a), Except(b)) => {
            if b > a {
                return None;
            }
            b
        }
        (AtLeast(a), AtLeast(b)) => {
            if a >= b {
                return None;
            }
            a
        }
        (AtLeast(a), AtMost(b)) => a.max(b + 1),
        (AtLeast(a), Exactly(b)) => {
            if a == b {
                a + 1
            } else {
                a
            }
        }
        (AtLeast(a), Except(b)) => {
            if b < a {
                return None;
            }
            b
        }
        (Exactly(a), required) => {
            if required.contains(a) {
                return None;
            }
            a
        }
        // ℤ minus a point is unbounded on both sides: never inside a half-line or a point.
        (Except(a), AtMost(b)) => {
            if b + 1 == a {
                b + 2
            } else {
                b + 1
            }
        }
        (Except(a), AtLeast(b)) => {
            if b - 1 == a {
                b - 2
            } else {
                b - 1
            }
        }
        (Except(a), Exactly(b)) => a.max(b) + 1,
        (Except(a), Except(b)) => {
            if a == b {
                return None;
            }
            b
        }
    };
    debug_assert!(
        supplied.contains(witness) && !required.contains(witness),
        "separating witness {witness} is not in {supplied:?} \\ {required:?}"
    );
    Some(witness)
}

#[cfg(test)]
mod tests {
    //! Known answers in every lane (the spec's §8): the i64 boundaries where ℤ and i64 differ
    //! (DC-6), wide values that must never be narrowed (DC-5), the witness contract, and the
    //! closed case table checked against a brute-force sample.

    use super::{
        NativeSubsumption, NativeVerdict, Shape, decide_cross_field, decide_literal_fits,
        decide_subsumption, separating_witness,
    };
    use crate::ast::{RefValue, RefinementClause, RefinementOp, RefinementRhs};
    use crate::span::Span;

    const OPS: [RefinementOp; 6] = [
        RefinementOp::Le,
        RefinementOp::Lt,
        RefinementOp::Ge,
        RefinementOp::Gt,
        RefinementOp::Eq,
        RefinementOp::Ne,
    ];
    /// The spec's §8 literal set: both i64 edges and their neighbours, and small values.
    const BOUNDS: [i64; 9] = [
        i64::MIN,
        i64::MIN + 1,
        -2,
        -1,
        0,
        1,
        2,
        i64::MAX - 1,
        i64::MAX,
    ];
    /// 2^64, 2^255 and 2^256 - 1 as little-endian limbs.
    const TWO_POW_64: [u64; 4] = [0, 1, 0, 0];
    const TWO_POW_255: [u64; 4] = [0, 0, 0, 1 << 63];
    const U256_MAX: [u64; 4] = [u64::MAX; 4];

    fn clause(op: RefinementOp, bound: i64) -> RefinementClause {
        RefinementClause {
            field: "x".to_string(),
            op,
            rhs: RefinementRhs::Literal(bound),
            span: Span::new(0, 0),
        }
    }

    fn wide_clause(op: RefinementOp, limbs: [u64; 4]) -> RefinementClause {
        RefinementClause {
            field: "x".to_string(),
            op,
            rhs: RefinementRhs::LiteralWide(limbs),
            span: Span::new(0, 0),
        }
    }

    /// `x op bound` at `x`, evaluated the plain way over i128, independent of `Shape`.
    fn holds_at(op: RefinementOp, x: i128, bound: i128) -> bool {
        match op {
            RefinementOp::Le => x <= bound,
            RefinementOp::Lt => x < bound,
            RefinementOp::Ge => x >= bound,
            RefinementOp::Gt => x > bound,
            RefinementOp::Eq => x == bound,
            RefinementOp::Ne => x != bound,
        }
    }

    #[test]
    fn the_domain_is_the_integers_not_i64() {
        // DC-6: below i64::MIN there are integers, so `x <= MIN` admits more than `x == MIN`;
        // the witness, MIN - 1, lies outside i64 and is reported as absent, as Z3's would be.
        assert_eq!(
            decide_subsumption(
                &clause(RefinementOp::Le, i64::MIN),
                &clause(RefinementOp::Eq, i64::MIN)
            ),
            NativeSubsumption::Violated {
                counterexample: None
            }
        );
        assert_eq!(
            decide_subsumption(
                &clause(RefinementOp::Ge, i64::MAX),
                &clause(RefinementOp::Eq, i64::MAX)
            ),
            NativeSubsumption::Violated {
                counterexample: None
            }
        );
        // The point is inside the half-line, and `x < MIN + 1` is `x <= MIN` over ℤ.
        assert_eq!(
            decide_subsumption(
                &clause(RefinementOp::Eq, i64::MIN),
                &clause(RefinementOp::Le, i64::MIN)
            ),
            NativeSubsumption::Holds
        );
        assert_eq!(
            decide_subsumption(
                &clause(RefinementOp::Lt, i64::MIN + 1),
                &clause(RefinementOp::Le, i64::MIN)
            ),
            NativeSubsumption::Holds
        );
        assert_eq!(
            decide_subsumption(
                &clause(RefinementOp::Le, i64::MIN),
                &clause(RefinementOp::Lt, i64::MIN + 1)
            ),
            NativeSubsumption::Holds
        );
        assert_eq!(
            decide_subsumption(
                &clause(RefinementOp::Gt, i64::MAX - 1),
                &clause(RefinementOp::Ge, i64::MAX)
            ),
            NativeSubsumption::Holds
        );
        // A witness inside i64 is named: MAX satisfies `x <= MAX` and not `x <= MAX - 1`.
        assert_eq!(
            decide_subsumption(
                &clause(RefinementOp::Le, i64::MAX),
                &clause(RefinementOp::Le, i64::MAX - 1)
            ),
            NativeSubsumption::Violated {
                counterexample: Some(i64::MAX)
            }
        );
        // Literal fits at the edges, where an i64 evaluation would wrap or saturate.
        assert_eq!(
            decide_literal_fits(
                &clause(RefinementOp::Lt, i64::MIN + 1),
                RefValue::Narrow(i64::MIN)
            ),
            NativeVerdict::Holds
        );
        assert_eq!(
            decide_literal_fits(
                &clause(RefinementOp::Gt, i64::MIN),
                RefValue::Narrow(i64::MIN)
            ),
            NativeVerdict::Violated
        );
        assert_eq!(
            decide_literal_fits(
                &clause(RefinementOp::Ge, i64::MAX),
                RefValue::Narrow(i64::MAX)
            ),
            NativeVerdict::Holds
        );
        assert_eq!(
            decide_cross_field(&clause(RefinementOp::Lt, 0), i64::MIN, i64::MAX),
            NativeVerdict::Holds
        );
        assert_eq!(
            decide_cross_field(&clause(RefinementOp::Le, 0), i64::MAX, i64::MIN),
            NativeVerdict::Violated
        );
    }

    #[test]
    fn a_wide_value_is_compared_whole_never_narrowed() {
        // DC-5's truncation witness: narrowed to its low limb, 2^64 would be 0 and `<= 100`
        // would hold.
        assert_eq!(
            decide_literal_fits(&clause(RefinementOp::Le, 100), RefValue::Wide(TWO_POW_64)),
            NativeVerdict::Violated
        );
        assert_eq!(
            decide_literal_fits(
                &clause(RefinementOp::Gt, i64::MAX),
                RefValue::Wide(TWO_POW_64)
            ),
            NativeVerdict::Holds
        );
        // Above 2^127 the value is kept as limbs and still ordered correctly.
        assert_eq!(
            decide_literal_fits(
                &clause(RefinementOp::Gt, i64::MAX),
                RefValue::Wide(TWO_POW_255)
            ),
            NativeVerdict::Holds
        );
        assert_eq!(
            decide_literal_fits(
                &wide_clause(RefinementOp::Gt, TWO_POW_255),
                RefValue::Wide(U256_MAX)
            ),
            NativeVerdict::Holds
        );
        assert_eq!(
            decide_literal_fits(
                &wide_clause(RefinementOp::Lt, TWO_POW_255),
                RefValue::Wide(U256_MAX)
            ),
            NativeVerdict::Violated
        );
        assert_eq!(
            decide_literal_fits(
                &wide_clause(RefinementOp::Eq, TWO_POW_64),
                RefValue::Wide(TWO_POW_64)
            ),
            NativeVerdict::Holds
        );
        assert_eq!(
            decide_literal_fits(
                &wide_clause(RefinementOp::Ne, U256_MAX),
                RefValue::Wide(U256_MAX)
            ),
            NativeVerdict::Violated
        );
        // A negative narrow value sits below every wide bound.
        assert_eq!(
            decide_literal_fits(
                &wide_clause(RefinementOp::Lt, TWO_POW_64),
                RefValue::Narrow(-1)
            ),
            NativeVerdict::Holds
        );
        // Subsumption with a wide bound on either side fails closed, with no witness.
        for (supplied, required) in [
            (
                wide_clause(RefinementOp::Ge, TWO_POW_64),
                clause(RefinementOp::Ge, 0),
            ),
            (
                clause(RefinementOp::Ge, 0),
                wide_clause(RefinementOp::Ge, TWO_POW_64),
            ),
        ] {
            assert_eq!(
                decide_subsumption(&supplied, &required),
                NativeSubsumption::Violated {
                    counterexample: None
                }
            );
        }
    }

    #[test]
    fn every_witness_separates_and_every_holds_is_an_inclusion() {
        // Over every operator pair and the §8 bound set: a refutation's witness lies in the
        // supplied set and outside the required one (evaluated the plain way, not through
        // `Shape`), and an inclusion verdict survives a brute-force sample around every bound.
        let mut refutations = 0;
        let mut inclusions = 0;
        for supplied_op in OPS {
            for supplied_bound in BOUNDS {
                for required_op in OPS {
                    for required_bound in BOUNDS {
                        let supplied = clause(supplied_op, supplied_bound);
                        let required = clause(required_op, required_bound);
                        let verdict = decide_subsumption(&supplied, &required);
                        let (s, r) = (i128::from(supplied_bound), i128::from(required_bound));
                        let sample = BOUNDS
                            .iter()
                            .map(|b| i128::from(*b))
                            .flat_map(|b| [b - 2, b - 1, b, b + 1, b + 2]);
                        match verdict {
                            NativeSubsumption::Holds => {
                                inclusions += 1;
                                for x in sample {
                                    assert!(
                                        !holds_at(supplied_op, x, s) || holds_at(required_op, x, r),
                                        "{supplied:?} ⊆ {required:?} claimed, but x = {x} separates them"
                                    );
                                }
                            }
                            NativeSubsumption::Violated { counterexample } => {
                                refutations += 1;
                                // The shape-level witness exists for every refutation; its i64
                                // image is what the verdict reports.
                                let (Some(ss), Some(rs)) =
                                    (Shape::of(&supplied), Shape::of(&required))
                                else {
                                    panic!("narrow clauses always have a shape");
                                };
                                let witness = separating_witness(ss, rs)
                                    .expect("a refutation names a separating witness");
                                assert!(
                                    holds_at(supplied_op, witness, s)
                                        && !holds_at(required_op, witness, r),
                                    "witness {witness} does not separate {supplied:?} from {required:?}"
                                );
                                assert_eq!(counterexample, i64::try_from(witness).ok());
                            }
                        }
                    }
                }
            }
        }
        // Both outcomes occur in the grid (SC-P4: the loop exercised both arms).
        assert!(
            refutations > 0 && inclusions > 0,
            "{refutations} refutations, {inclusions} inclusions"
        );
    }

    #[test]
    fn anti_stub_a_wrong_witness_fails_the_separation_check() {
        // The witness contract in the test above is what makes a refutation evidence: a value
        // that does not separate the shapes must be caught by the same predicate.
        let (s, r) = (Shape::AtMost(5), Shape::AtMost(3));
        let witness = separating_witness(s, r).expect("5 separates x <= 5 from x <= 3");
        assert!(s.contains(witness) && !r.contains(witness));
        let planted = 2;
        assert!(
            !(s.contains(planted) && !r.contains(planted)),
            "2 is inside both shapes"
        );
    }
}
