//! Z3-backed refinement queries.
//!
//! This module owns the three query shapes used by `type_check_v2`:
//! literal fit, cross-field fit, and predicate subsumption. AIR capability
//! verification is owned separately by `air_capability_v2`.
//!
//! ## SMT theory inventory (load-bearing for soundness)
//!
//! Canonical reference: [`docs/z3-theory-inventory.md`](../../../../docs/z3-theory-inventory.md).
//! It inventories every query family, proves the supported fragments
//! decidable, and defines the update protocol. Every query here is
//! validated by the runtime fragment guard through the cached chokepoint.
//!
//! ## Determinism
//!
//! The solver is constrained by `rlimit` (a deterministic resource budget,
//! conflicts/decisions) rather than wall-clock `timeout`. This preserves
//! reproducible builds: same source + same toolchain → same diagnostics across
//! hardware.

use z3::{
    Config, Context, Params, SatResult, Solver,
    ast::{Ast, Int},
};

/// Z3 resource budget per refinement query.
///
/// The AIR capability prover uses the same per-query value. Raise it only
/// from measured corpus evidence. `rlimit` counts deterministic solver work,
/// not wall-clock time.
pub(crate) const Z3_RLIMIT: u32 = 1_000_000;

/// Construct a `Solver` with a deterministic resource limit applied. The
/// rlimit must be set BEFORE any `solver.check()` call to take effect on
/// that check.
fn make_solver<'ctx>(ctx: &'ctx Context, rlimit: u32) -> Solver<'ctx> {
    let solver = Solver::new(ctx);
    let mut params = Params::new(ctx);
    params.set_u32("rlimit", rlimit);
    solver.set_params(&params);
    solver
}

/// Cached-check wrapper: invoke `solver.check()` via the process-wide
/// Z3 result cache (a hit avoids the Z3 call; a miss runs Z3 through
/// `z3_cache::fresh_check` then stores the verdict). On the first hit
/// per (key, process), the cache re-runs Z3 in a fresh same-context
/// solver and panics on verdict mismatch — see `z3_cache::check_cached`
/// for the soundness rationale.
///
/// Returns a fragment violation when the compiler-built query leaves the
/// supported grammar. Callers treat that as an internal compiler error.
fn check_cached_solver(
    solver: &Solver<'_>,
) -> Result<SatResult, crate::z3_fragment_guard::FragmentViolation> {
    use crate::z3_cache::Verdict;
    Ok(
        match crate::z3_cache::check_cached(solver, crate::z3_cache::fresh_check)? {
            Verdict::Sat => SatResult::Sat,
            Verdict::Unsat => SatResult::Unsat,
            Verdict::Unknown => SatResult::Unknown,
        },
    )
}

// Refinement-predicate satisfiability.

/// Outcome of a refinement-clause check. The discharge layer preserves the
/// distinction between refutation and resource exhaustion in diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RefinementVerdict {
    /// Z3 proved `NOT(predicate(value))` is unsatisfiable → predicate holds.
    Holds,
    /// Z3 found a counterexample, so the predicate is refutable.
    Violated,
    /// Z3 ran out of budget.
    Timeout,
}

/// The single encoder for refinement values. Narrow values use `from_i64`;
/// wide `u256` values become one `ANUM` from canonical decimal text. Building
/// wide values through arithmetic or narrowing them would leave the proven
/// representation contract. Invalid decimal output is a compiler bug.
#[cfg(feature = "solver")]
fn encode_ref_value<'ctx>(ctx: &'ctx Context, v: crate::ast::RefValue) -> Int<'ctx> {
    match v {
        crate::ast::RefValue::Narrow(n) => Int::from_i64(ctx, n),
        crate::ast::RefValue::Wide(limbs) => {
            let decimal = crate::lexer::u256_to_decimal(limbs);
            Int::from_str(ctx, &decimal).unwrap_or_else(|| {
                panic!(
                    "ICE [C005]: u256_to_decimal produced a non-numeral string {decimal:?}; \
                     the digit-only contract is violated (compiler bug, not user error)"
                )
            })
        }
    }
}

/// Discharge a refinement clause against a concrete field value. The query
/// binds `refine__value`, asserts the negated predicate, and uses the cached
/// solver path. The caller must preserve all three verdicts.
pub(crate) fn check_refinement(
    clause: &crate::ast::RefinementClause,
    supplied_value: crate::ast::RefValue,
) -> RefinementVerdict {
    use crate::ast::RefinementOp;

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = make_solver(&ctx, Z3_RLIMIT);

    // The name is disjoint from the other refinement query shapes and from
    // AIR capability variables, keeping canonical cache keys separate.
    let value = Int::new_const(&ctx, "refine__value");
    // Wide values must pass through the canonical non-narrowing encoder.
    let supplied = encode_ref_value(&ctx, supplied_value);
    // Field RHS clauses route to `check_refinement_xfield`; LengthOf clauses
    // are resolved before discharge. This path accepts literal bounds only.
    let rhs = match &clause.rhs {
        crate::ast::RefinementRhs::Literal(v) => Int::from_i64(&ctx, *v),
        crate::ast::RefinementRhs::LiteralWide(limbs) => {
            encode_ref_value(&ctx, crate::ast::RefValue::Wide(*limbs))
        }
        crate::ast::RefinementRhs::Field(_) | crate::ast::RefinementRhs::LengthOf(_) => {
            unreachable!(
                "check_refinement must only be called with a Literal/LiteralWide-RHS \
                 clause; Field and LengthOf clauses require their dedicated routes"
            );
        }
    };

    // Bind the symbolic value to the literal so cache keys differ between
    // supplied-value variants. The canonical SMT then encodes both the
    // predicate and the value under check.
    solver.assert(&value._eq(&supplied));

    // Predicate term: refine__value <op> literal.
    let predicate = match clause.op {
        RefinementOp::Le => value.le(&rhs),
        RefinementOp::Lt => value.lt(&rhs),
        RefinementOp::Ge => value.ge(&rhs),
        RefinementOp::Gt => value.gt(&rhs),
        RefinementOp::Eq => value._eq(&rhs),
        RefinementOp::Ne => value._eq(&rhs).not(),
    };

    // Assert NOT(predicate) and ask Z3: is this satisfiable?
    // Unsat → predicate holds for all bindings consistent with the
    // value-equality assertion (i.e., for this exact literal).
    solver.assert(&predicate.not());

    // The query builder is closed over six comparison operators and literal
    // values, so a fragment violation is a compiler bug.
    match check_cached_solver(&solver).unwrap_or_else(|v| {
        panic!(
            "ICE [C005]: refinement SMT query left the decidable fragment — {v}; \
             see docs/specs/z3-fragment-guard.md (AG-Z3)"
        )
    }) {
        SatResult::Unsat => RefinementVerdict::Holds,
        SatResult::Sat => RefinementVerdict::Violated,
        SatResult::Unknown => RefinementVerdict::Timeout,
    }
}

/// Check a two-value cross-field predicate. `refine__lhs` and
/// `refine__rhs` are bound to concrete values and the declared operator is
/// applied without mirroring or swapping. Their names are distinct from the
/// literal-fit and subsumption query names for cache-key separation.
#[cfg(feature = "solver")]
pub(crate) fn check_refinement_xfield(
    clause: &crate::ast::RefinementClause,
    lhs_value: i64,
    rhs_value: i64,
) -> RefinementVerdict {
    use crate::ast::RefinementOp;

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = make_solver(&ctx, Z3_RLIMIT);

    let lhs = Int::new_const(&ctx, "refine__lhs");
    let rhs = Int::new_const(&ctx, "refine__rhs");
    let lhs_lit = Int::from_i64(&ctx, lhs_value);
    let rhs_lit = Int::from_i64(&ctx, rhs_value);

    // Bind both symbolic variables to their supplied values.
    solver.assert(&lhs._eq(&lhs_lit));
    solver.assert(&rhs._eq(&rhs_lit));

    // Preserve the clause's operand order exactly.
    let predicate = match clause.op {
        RefinementOp::Le => lhs.le(&rhs),
        RefinementOp::Lt => lhs.lt(&rhs),
        RefinementOp::Ge => lhs.ge(&rhs),
        RefinementOp::Gt => lhs.gt(&rhs),
        RefinementOp::Eq => lhs._eq(&rhs),
        RefinementOp::Ne => lhs._eq(&rhs).not(),
    };

    // Assert NOT(predicate). Unsat → predicate holds at these values.
    solver.assert(&predicate.not());

    // theory: QF_LIA (two integer variables; bindings via equality on
    // concrete literals; literal-coefficient comparison). Decidable.
    // Single check_cached_solver site for the cross-field literal-RHS
    // path; cache key isolated from other refinement queries by the
    // distinct variable names.
    //
    // A fragment violation in this closed query builder is a compiler bug.
    match check_cached_solver(&solver).unwrap_or_else(|v| {
        panic!(
            "ICE [C005]: cross-field refinement SMT query left the decidable fragment — {v}; \
             see docs/specs/z3-fragment-guard.md (AG-Z3)"
        )
    }) {
        SatResult::Unsat => RefinementVerdict::Holds,
        SatResult::Sat => RefinementVerdict::Violated,
        SatResult::Unknown => RefinementVerdict::Timeout,
    }
}

/// Result of a refinement-subsumption query. A refutation carries a
/// counterexample when model extraction produced one; callers render the
/// absent case explicitly.
#[cfg(feature = "solver")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SubsumptionResult {
    /// `∀x. supplied(x) → required(x)` — Z3 proved subsumption. The
    /// match path may accept.
    Holds,
    /// Counterexample exists; `x = counterexample` satisfies supplied
    /// but not required. The optional value is cached with the verdict.
    Violated { counterexample: Option<i64> },
    /// rlimit exhausted; subsumption cannot be discharged. Caller
    /// emits T215 with timeout-flavored detail.
    Timeout,
}

/// Z3-backed predicate subsumption.
///
/// Asks Z3: does the supplied clause's predicate IMPLY the destination
/// clause's predicate over i64? Encoded as `∃x. supplied(x) ∧ ¬destination(x)`.
/// Unsat → no counterexample → subsumption holds. Sat → a concrete `x`
/// exists where source holds but destination doesn't → no subsumption.
///
/// Counterexamples are extracted only inside fresh evaluation and cached with
/// the verdict. Cache hits never query a model from an unevaluated solver.
/// The `refine__x` name keeps this query shape cache-key-disjoint.
#[cfg(feature = "solver")]
pub(crate) fn check_refinement_subsumption(
    supplied: &crate::ast::RefinementClause,
    required: &crate::ast::RefinementClause,
) -> SubsumptionResult {
    use crate::ast::RefinementOp;

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = make_solver(&ctx, Z3_RLIMIT);

    // This subsumption path is i64-only. Wide bounds fail closed rather than
    // being narrowed or accepted without proof.
    if matches!(supplied.rhs, crate::ast::RefinementRhs::LiteralWide(_))
        || matches!(required.rhs, crate::ast::RefinementRhs::LiteralWide(_))
    {
        return SubsumptionResult::Violated {
            counterexample: None,
        };
    }

    // Single free variable; the implication is over all i64 bindings of x.
    let x = Int::new_const(&ctx, "refine__x");
    // Obligation collection routes only literal-RHS clauses here.
    let extract_literal = |c: &crate::ast::RefinementClause| -> i64 {
        match &c.rhs {
            crate::ast::RefinementRhs::Literal(v) => *v,
            crate::ast::RefinementRhs::LiteralWide(_) => {
                unreachable!("LiteralWide is rejected before i64 subsumption")
            }
            crate::ast::RefinementRhs::Field(_) | crate::ast::RefinementRhs::LengthOf(_) => {
                unreachable!(
                    "check_refinement_subsumption must only be called with \
                     Literal-RHS clauses; Field and LengthOf clauses require \
                     their dedicated routes"
                );
            }
        }
    };
    let supplied_lit = Int::from_i64(&ctx, extract_literal(supplied));
    let required_lit = Int::from_i64(&ctx, extract_literal(required));

    let supplied_term = match supplied.op {
        RefinementOp::Le => x.le(&supplied_lit),
        RefinementOp::Lt => x.lt(&supplied_lit),
        RefinementOp::Ge => x.ge(&supplied_lit),
        RefinementOp::Gt => x.gt(&supplied_lit),
        RefinementOp::Eq => x._eq(&supplied_lit),
        RefinementOp::Ne => x._eq(&supplied_lit).not(),
    };
    let required_term = match required.op {
        RefinementOp::Le => x.le(&required_lit),
        RefinementOp::Lt => x.lt(&required_lit),
        RefinementOp::Ge => x.ge(&required_lit),
        RefinementOp::Gt => x.gt(&required_lit),
        RefinementOp::Eq => x._eq(&required_lit),
        RefinementOp::Ne => x._eq(&required_lit).not(),
    };

    // ∃x. supplied(x) ∧ ¬required(x). Unsat → ∀x. supplied(x) → required(x).
    solver.assert(&supplied_term);
    solver.assert(&required_term.not());

    // Extract the model inside fresh evaluation, while it is valid. The cache
    // stores the optional counterexample beside the verdict.
    let (verdict, cex) = crate::z3_cache::check_cached_with_model(&solver, |s| {
        // The fresh check routes through z3_cache::fresh_check (the
        // sanctioned walk-then-check); the model is extracted right
        // after, still inside the cache-miss closure.
        let verdict = crate::z3_cache::fresh_check(s)?;
        let cex = if verdict == crate::z3_cache::Verdict::Sat {
            #[allow(clippy::disallowed_methods)]
            let model = s.get_model();
            model
                .and_then(|m| m.eval(&x, true))
                .and_then(|n| n.as_i64())
        } else {
            None
        };
        Ok((verdict, cex))
    })
    // A fragment violation in this closed query builder is a compiler bug.
    .unwrap_or_else(|v| {
        panic!(
            "ICE [C005]: refinement-subsumption SMT query left the decidable fragment — {v}; \
             see docs/specs/z3-fragment-guard.md (AG-Z3)"
        )
    });

    match verdict {
        crate::z3_cache::Verdict::Unsat => SubsumptionResult::Holds,
        crate::z3_cache::Verdict::Sat => SubsumptionResult::Violated {
            counterexample: cex,
        },
        crate::z3_cache::Verdict::Unknown => SubsumptionResult::Timeout,
    }
}

#[cfg(test)]
mod tests {
    use super::{Z3_RLIMIT, check_cached_solver, make_solver};
    use z3::{
        Config, Context, SatResult,
        ast::{Ast, BV},
    };

    /// B2: rlimit machinery actually constrains the solver. A multiplication
    /// equation over 32-bit bitvectors at rlimit=1 must return Unknown with
    /// a resource-limit reason. If this fails, the rlimit param is on the
    /// wrong object or the wrong value type.
    #[test]
    fn make_solver_applies_rlimit() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let solver = make_solver(&ctx, 1);

        // Force a non-trivial query: factor 0xDEADBEEF over 32-bit BV with
        // both factors > 1. Z3 cannot solve this with one conflict budget.
        let x = BV::new_const(&ctx, "x", 32);
        let y = BV::new_const(&ctx, "y", 32);
        solver.assert(&x.bvmul(&y)._eq(&BV::from_u64(&ctx, 0xDEAD_BEEF, 32)));
        solver.assert(&x.bvugt(&BV::from_u64(&ctx, 1, 32)));
        solver.assert(&y.bvugt(&BV::from_u64(&ctx, 1, 32)));

        // Sanctioned carve-out: this test exercises RAW solver rlimit
        // behavior (deliberately out-of-allowlist ops — BMUL/UGT — and a
        // direct check), so it must not route through the fragment guard.
        // See clippy.toml's census note.
        #[allow(clippy::disallowed_methods)]
        let result = solver.check();
        assert_eq!(
            result,
            SatResult::Unknown,
            "rlimit=1 must produce Unknown on a non-trivial query"
        );
        let reason = solver.get_reason_unknown();
        assert!(
            reason.is_some(),
            "Unknown verdict must carry a `reason_unknown` string"
        );
    }

    /// A wide value built via `Int::from_str` must
    /// (a) stay inside the decidable fragment (`check_fragment` Ok: a single ANUM
    /// numeral, no ADD/MUL/UMINUS), so a wide refinement never ICEs [C005], and
    /// (b) carry the correct magnitude. This canary gates the whole U3-b approach
    /// and is permanent: a z3 version bump that re-classified large numerals would
    /// trip it before shipping.
    #[test]
    fn wide_numeral_is_fragment_clean_and_correct() {
        use z3::ast::Int;
        let cfg = Config::new();
        let ctx = Context::new(&cfg);

        // 2^256-1 (max u256), 2^255 (i256 sign bit), 2^128, 2^64 (just past i64).
        const EXTREMES: &[(&str, &str)] = &[
            (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935",
                "2^256-1",
            ),
            (
                "57896044618658097711785492504343953926634992332820282019728792003956564819968",
                "2^255",
            ),
            ("340282366920938463463374607431768211456", "2^128"),
            ("18446744073709551616", "2^64"),
        ];

        // (a) fragment-clean + Holds: value == wide  ⊢  value >= wide.
        for (decimal, label) in EXTREMES {
            let value = Int::new_const(&ctx, "refine__value");
            let wide = Int::from_str(&ctx, decimal)
                .unwrap_or_else(|| panic!("from_str must parse {label}"));
            let solver = make_solver(&ctx, Z3_RLIMIT);
            solver.assert(&value._eq(&wide));
            solver.assert(&value.ge(&wide).not());
            // The sanctioned production path: check_cached_solver runs the fragment
            // guard (Err → left the fragment) AND returns the verdict — so a clean
            // Ok IS the fragment-cleanliness assertion, no raw-solver carve-out.
            let r = check_cached_solver(&solver)
                .unwrap_or_else(|v| panic!("wide numeral {label} left the fragment: {v}"));
            assert_eq!(
                r,
                SatResult::Unsat,
                "{label}: value==wide ⊢ value>=wide must Hold"
            );
        }

        // (b) correctness/Violated: x == (2^64 - 1) does NOT satisfy x >= 2^64
        // (catches a magnitude bug that would make every wide compare vacuously).
        let value = Int::new_const(&ctx, "refine__value");
        let lo = Int::from_str(&ctx, "18446744073709551615").unwrap(); // 2^64 - 1
        let bound = Int::from_str(&ctx, "18446744073709551616").unwrap(); // 2^64
        let solver = make_solver(&ctx, Z3_RLIMIT);
        solver.assert(&value._eq(&lo));
        solver.assert(&value.ge(&bound).not());
        let r = check_cached_solver(&solver).expect("wide numeral left the fragment");
        assert_eq!(
            r,
            SatResult::Sat,
            "(2^64-1) >= 2^64 must be Violated (Sat of the negation)"
        );
    }

    /// Self-test: Z3_RLIMIT is the empirically-tightened value documented at
    /// its declaration. Changing it requires changing the documented basis
    /// AND verifying the v2 prover's `rlimit_has_at_least_2x_headroom`
    /// (air_capability_v2's test module) still passes at the new value's
    /// half — the two rlimit constants are kept equal by
    /// `rlimit_constants_stay_in_sync` there.
    #[test]
    fn z3_rlimit_matches_documented_value() {
        assert_eq!(
            Z3_RLIMIT, 1_000_000,
            "Z3_RLIMIT changed without updating the documented justification — \
             update the doc comment above Z3_RLIMIT with the new measurement basis."
        );
    }
}
