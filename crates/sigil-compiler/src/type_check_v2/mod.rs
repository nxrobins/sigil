//! Refinement obligation pipeline used by production type checking.
//!
//! ## Architecture
//!
//! The orchestrator runs three phases in order:
//!
//! 1. **Pure** — `refinement::collect_refinement_obligations`,
//!    which walks a `TypedProgram` and emits a refinement workload. It
//!    cannot call Z3 (enforced by `tests/quarantine_grep.rs`).
//!
//! 2. **Discharge** — `discharge_refinements`, the only refinement-Z3
//!    entry in this tree, routes verdicts to diagnostics and returns an
//!    opaque completion token.
//!
//! 3. **Assembly** — collector and discharge diagnostics are sorted into
//!    a stable result carrying the completion token.
//!
//! ## Current role
//!
//! `type_check::check_with_warnings` runs this pipeline after structural
//! collection, including over partial typed programs. It is the sole
//! production refinement-discharge path.
//!
//! ## Confinement
//!
//! `refinement.rs`, `capability_tc.rs`, and `obligations.rs` MUST NOT
//! import `z3`, `crate::z3_capability`, or `crate::z3_cache`. THIS file
//! (`mod.rs`) IS the orchestrator and IS allowed to import them. The
//! `tests/quarantine_grep.rs` asserts the boundary.

pub mod obligations;
pub mod refinement;

use crate::diagnostics::Diagnostic;
use crate::name_resolution::ResolvedProgram;
use crate::registries::AuthorityRegistry;
use crate::typed_ast::TypedProgram;

use obligations::{RefinementObligation, RefinementWorkload};

/// Proof token: the refinement workload has been walked and every
/// obligation discharged. **Private constructor.** Only `discharge_refinements`
/// (in THIS file) can mint one — no other module in the crate can
/// construct this value.
///
/// The pass result carries this token so a completed result cannot be
/// assembled without running discharge.
#[derive(Debug)]
#[allow(dead_code)] // opaque seal is carried as proof and intentionally unread
pub struct DischargedRefinements {
    _seal: (),
}

// Capability obligations are owned and discharged by `crate::air_capability_v2`.

/// The sole refinement-discharge entry point.
///
/// **Does NOT re-run type-checking.** Consumes the already-computed
/// `TypedProgram` + `AuthorityRegistry` from `check_collecting` and runs the
/// Pure → Discharge pipeline on top, so it adds no work to sig collection.
/// Called from `type_check::check_with_warnings`, which merges the returned
/// diagnostics into the combined structural+refinement error stream (run over
/// the possibly-partial typed program, so a refinement violation is reported
/// alongside any structural error — see tests/refinement_mixed_error.rs).
pub fn run_obligation_passes(
    program: &ResolvedProgram,
    typed_program: &TypedProgram,
    authority_registry: &AuthorityRegistry,
) -> ShadowResult {
    // Phase 1: pure refinement-obligation collection.
    let _ = authority_registry; // retained in the signature for symmetry; refinement collection doesn't need it
    let (refine_collect_diags, refine_workload) =
        refinement::collect_refinement_obligations(program, typed_program);

    // Phase 2: Discharge (the ONLY refinement-Z3 call site in this tree).
    let (refine_discharge_diags, refine_token) = discharge_refinements(refine_workload);

    // Phase 3: assemble + sort. The orchestrator does no string
    // formatting — each obligation already carries its on_violated /
    // on_timeout diagnostic constructed by the Pure Pipeline.
    let mut diagnostics =
        Vec::with_capacity(refine_collect_diags.len() + refine_discharge_diags.len());
    diagnostics.extend(refine_collect_diags);
    diagnostics.extend(refine_discharge_diags);
    // Sort by (source_id, start, code) for deterministic diagnostics.
    diagnostics.sort_by_key(|d| {
        let span = d.span().unwrap_or_default();
        (span.source.0, span.start, d.code().as_str())
    });

    ShadowResult {
        diagnostics,
        _refinements_discharged: refine_token,
    }
}

/// Test-only access to the pure collector's raw workload and diagnostics.
///
/// Snapshot tests use this to detect dropped or malformed obligations before
/// Z3 runs. Collector diagnostics are included because some construction
/// failures emit directly instead of producing obligations. Capability
/// workloads are exposed separately by `air_capability_v2`.
///
/// This is public only because integration tests are separate crates;
/// production callers should use [`run_obligation_passes`].
pub fn collect_workloads_for_test(
    program: &ResolvedProgram,
    typed_program: &TypedProgram,
) -> (Vec<Diagnostic>, RefinementWorkload) {
    refinement::collect_refinement_obligations(program, typed_program)
}

/// Refinement obligation-pass output. The historical name remains part of the
/// public integration-test surface. `check_with_warnings` merges its diagnostics
/// into the structural stream; the token proves discharge ran.
#[derive(Debug)]
pub struct ShadowResult {
    pub diagnostics: Vec<Diagnostic>,
    pub _refinements_discharged: DischargedRefinements,
}

/// Discharge a refinement workload. **The only refinement-Z3 caller in
/// the type_check tree.** Routes each obligation to the corresponding
/// `z3_capability::check_*` function and pushes the carried diagnostic
/// on `Violated` / `Timeout` verdicts.
///
/// Returns `(diagnostics, token)`. The token cannot be constructed any
/// other way (private `_seal` field).
///
fn discharge_refinements(w: RefinementWorkload) -> (Vec<Diagnostic>, DischargedRefinements) {
    let mut diagnostics = Vec::with_capacity(w.obligations.len());

    for obligation in w.obligations {
        // T215 construction subsumption builds its message AT discharge (the
        // record message embeds the Z3 counterexample, known only after the
        // subsumption query runs), so it routes through a dedicated path
        // rather than the pre-built-diagnostic + 3-way-verdict model.
        if let RefinementObligation::SubsumptionAtConstruction {
            actual,
            expected,
            site,
        } = &obligation
        {
            if let Some(diag) = discharge_subsumption_at_construction(actual, expected, *site) {
                diagnostics.push(diag);
            }
            continue;
        }

        let (on_violated, on_timeout) = match &obligation {
            RefinementObligation::LiteralFits {
                on_violated,
                on_timeout,
                ..
            }
            | RefinementObligation::SubsumptionAny {
                on_violated,
                on_timeout,
                ..
            }
            | RefinementObligation::CrossField {
                on_violated,
                on_timeout,
                ..
            } => (on_violated.clone(), on_timeout.clone()),
            // Handled above via `continue`; never reached here.
            RefinementObligation::SubsumptionAtConstruction { .. } => unreachable!(),
        };

        let verdict = discharge_one_refinement(&obligation);
        match verdict {
            RefinementDischargeVerdict::Holds => {}
            RefinementDischargeVerdict::Violated => diagnostics.push(on_violated),
            RefinementDischargeVerdict::Timeout => diagnostics.push(on_timeout),
        }
    }

    (diagnostics, DischargedRefinements { _seal: () })
}

/// Verdict the orchestrator routes after asking Z3. Distinct from
/// `z3_capability::RefinementVerdict` (which is `pub(crate)` in the Z3
/// module) to keep this file's surface narrow — if we ever swap the
/// backend, only the small match below changes.
///
/// In the no-solver build, the discharge always returns `Holds`, so
/// `Violated` and `Timeout` are unused — silence the warning rather
/// than reshape the enum (the solver build needs all three variants).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(feature = "solver"), allow(dead_code))]
enum RefinementDischargeVerdict {
    Holds,
    Violated,
    Timeout,
}

/// Route a single obligation to the discharge backend.
///
/// **This is the ONLY Z3-touching site in the `type_check_v2` tree;**
/// the CI refinement-attachment lint enforces that boundary.
///
/// Variant routing:
/// - **LiteralFits** → `check_refinement(clause, value)`
/// - **SubsumptionAny** → loop `check_refinement_subsumption(s, expected)`
///   over the supplied clauses; accept on first `Holds`, propagate the
///   FIRST Timeout if all subsequent results are non-Holds.
/// - **CrossField** → `check_refinement_xfield(clause, lhs, rhs)`.
#[cfg(feature = "solver")]
fn discharge_one_refinement(obligation: &RefinementObligation) -> RefinementDischargeVerdict {
    use crate::z3_capability::{self, RefinementVerdict, SubsumptionResult};

    match obligation {
        RefinementObligation::LiteralFits { clause, value, .. } => {
            match z3_capability::check_refinement(clause, *value) {
                RefinementVerdict::Holds => RefinementDischargeVerdict::Holds,
                RefinementVerdict::Violated => RefinementDischargeVerdict::Violated,
                RefinementVerdict::Timeout => RefinementDischargeVerdict::Timeout,
            }
        }
        RefinementObligation::SubsumptionAny {
            actual, expected, ..
        } => {
            // Accept on the first holding clause. Otherwise preserve the first
            // timeout so diagnostics distinguish budget exhaustion from refutation.
            let mut saw_timeout = false;
            for supplied in actual {
                match z3_capability::check_refinement_subsumption(supplied, expected) {
                    SubsumptionResult::Holds => return RefinementDischargeVerdict::Holds,
                    SubsumptionResult::Violated { .. } => {}
                    SubsumptionResult::Timeout => saw_timeout = true,
                }
            }
            if saw_timeout {
                RefinementDischargeVerdict::Timeout
            } else {
                RefinementDischargeVerdict::Violated
            }
        }
        RefinementObligation::CrossField {
            clause,
            lhs_value,
            rhs_value,
            ..
        } => match z3_capability::check_refinement_xfield(clause, *lhs_value, *rhs_value) {
            RefinementVerdict::Holds => RefinementDischargeVerdict::Holds,
            RefinementVerdict::Violated => RefinementDischargeVerdict::Violated,
            RefinementVerdict::Timeout => RefinementDischargeVerdict::Timeout,
        },
        // Routed via the dedicated path in `discharge_refinements` (its
        // message embeds the counterexample), never through this verdict
        // function.
        RefinementObligation::SubsumptionAtConstruction { .. } => {
            unreachable!("SubsumptionAtConstruction is discharged separately")
        }
    }
}

/// No-solver fallback: ordinary obligations are accepted because this build
/// cannot discharge them. Construction subsumption has a separate fail-closed
/// path below.
#[cfg(not(feature = "solver"))]
fn discharge_one_refinement(_obligation: &RefinementObligation) -> RefinementDischargeVerdict {
    RefinementDischargeVerdict::Holds
}

/// Discharge a construction-site subsumption obligation (record T215). The
/// syntactic fast-path was already applied in the collector; here we run the
/// Z3 subsumption loop,
/// capturing the FIRST counterexample and any timeout, then build the
/// counterexample-bearing T215 message. Returns `None` if a supplied clause
/// subsumes (accept), else the T215 diagnostic.
#[cfg(feature = "solver")]
fn discharge_subsumption_at_construction(
    actual: &[crate::ast::RefinementClause],
    expected: &crate::ast::RefinementClause,
    site: crate::span::Span,
) -> Option<Diagnostic> {
    use crate::z3_capability::{SubsumptionResult, check_refinement_subsumption};

    let mut first_violation_cex: Option<Option<i64>> = None;
    let mut had_timeout = false;
    for supplied in actual {
        match check_refinement_subsumption(supplied, expected) {
            SubsumptionResult::Holds => return None, // subsumed → accept
            SubsumptionResult::Violated { counterexample } => {
                if first_violation_cex.is_none() {
                    first_violation_cex = Some(counterexample);
                }
            }
            SubsumptionResult::Timeout => had_timeout = true,
        }
    }
    // No supplied clause subsumes: emit T215 with the most useful detail.
    let detail = match (first_violation_cex, had_timeout) {
        (Some(Some(cex)), _) => format!("Z3 found a counterexample to subsumption: x = {cex}"),
        (Some(None), _) => {
            "Z3 found a counterexample to subsumption; (counterexample unavailable)".to_string()
        }
        (None, true) => {
            "Z3 rlimit exhausted; subsumption cannot be discharged within the per-program budget"
                .to_string()
        }
        (None, false) => {
            "no clause in the supplied refinement subsumes the destination's required predicate"
                .to_string()
        }
    };
    Some(refinement::record_subsumption_t215_diagnostic(
        expected, actual, &detail, site,
    ))
}

/// No-solver fallback. The syntactic fast path already failed in the collector,
/// so construction subsumption remains fail-closed when Z3 is unavailable.
#[cfg(not(feature = "solver"))]
fn discharge_subsumption_at_construction(
    actual: &[crate::ast::RefinementClause],
    expected: &crate::ast::RefinementClause,
    site: crate::span::Span,
) -> Option<Diagnostic> {
    let detail = "no clause in the supplied refinement subsumes the destination's required predicate (Z3 disabled at build time)";
    Some(refinement::record_subsumption_t215_diagnostic(
        expected, actual, detail, site,
    ))
}

#[cfg(all(test, feature = "solver"))]
mod native_decider_agreement {
    //! DBC-1a (the design-by-contract spec's §8): the native decider agrees with Z3 on an
    //! exhaustive grid of the live fragment, every operator against both i64 edges, their
    //! neighbours and small values, with 2^64, 2^255 and 2^256 - 1 as wide values and bounds
    //! where the route admits them. The grid's cardinality is pinned at its measured value.
    //! The walk lives in the orchestrator because this is the one file allowed to call the
    //! `z3_capability::check_refinement*` primitives (the CI lint "v2 is the sole refinement-Z3
    //! caller"); from DBC-1b on, the orchestrator runs both backends on every obligation and
    //! a disagreement is an internal error. SC-P4: the walk takes its oracle as a parameter,
    //! so the anti-stub compares the native decider with a planted wrong verdict against the
    //! unplanted native decider, which shows the walk reports a divergence in each of its
    //! three shapes without spending a second Z3 pass.

    use crate::ast::{RefValue, RefinementClause, RefinementOp, RefinementRhs};
    use crate::refinement_decide::{
        NativeSubsumption, NativeVerdict, decide_cross_field, decide_literal_fits,
        decide_subsumption,
    };
    use crate::span::Span;
    use crate::z3_capability::{
        RefinementVerdict, SubsumptionResult, check_refinement, check_refinement_subsumption,
        check_refinement_xfield,
    };

    const OPS: [RefinementOp; 6] = [
        RefinementOp::Le,
        RefinementOp::Lt,
        RefinementOp::Ge,
        RefinementOp::Gt,
        RefinementOp::Eq,
        RefinementOp::Ne,
    ];
    const NARROW: [i64; 9] = [
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
    const WIDE: [[u64; 4]; 3] = [[0, 1, 0, 0], [0, 0, 0, 1 << 63], [u64::MAX; 4]];
    /// Measured and pinned (§8): 6 operators × 12 values × 12 bounds literal fits, 6 × 9 × 9
    /// cross-field pairs, and (6 × 9)² subsumption pairs over the narrow bounds (a wide bound
    /// is refused by both routes before any decision; `wide_bound_subsumption_is_refused_by_
    /// both_backends` pins that separately).
    const GRID_CELLS: usize = 864 + 486 + 2916;

    fn clause(op: RefinementOp, rhs: RefinementRhs) -> RefinementClause {
        RefinementClause {
            field: "x".to_string(),
            op,
            rhs,
            span: Span::new(0, 0),
        }
    }

    /// `x op bound` at `x`, evaluated the plain way over i128: the check that a reported
    /// counterexample separates the two clauses, independent of both deciders.
    fn holds_at(op: RefinementOp, x: i128, bound: i64) -> bool {
        let bound = i128::from(bound);
        match op {
            RefinementOp::Le => x <= bound,
            RefinementOp::Lt => x < bound,
            RefinementOp::Ge => x >= bound,
            RefinementOp::Gt => x > bound,
            RefinementOp::Eq => x == bound,
            RefinementOp::Ne => x != bound,
        }
    }

    /// The anti-stub's planted disagreement: which cell, if any, has the native verdict
    /// inverted before the comparison.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Planted {
        None,
        LiteralFits(usize),
        CrossField(usize),
        Subsumption(usize),
    }

    fn invert(verdict: NativeVerdict) -> NativeVerdict {
        match verdict {
            NativeVerdict::Holds => NativeVerdict::Violated,
            NativeVerdict::Violated => NativeVerdict::Holds,
        }
    }

    fn agree(native: NativeVerdict, oracle: RefinementVerdict) -> bool {
        matches!(
            (native, oracle),
            (NativeVerdict::Holds, RefinementVerdict::Holds)
                | (NativeVerdict::Violated, RefinementVerdict::Violated)
        )
    }

    /// The native decider in the Z3 route's verdict shapes: the anti-stub's oracle.
    fn native_fits(clause: &RefinementClause, value: RefValue) -> RefinementVerdict {
        match decide_literal_fits(clause, value) {
            NativeVerdict::Holds => RefinementVerdict::Holds,
            NativeVerdict::Violated => RefinementVerdict::Violated,
        }
    }

    fn native_xfield(clause: &RefinementClause, lhs: i64, rhs: i64) -> RefinementVerdict {
        match decide_cross_field(clause, lhs, rhs) {
            NativeVerdict::Holds => RefinementVerdict::Holds,
            NativeVerdict::Violated => RefinementVerdict::Violated,
        }
    }

    fn native_subsumption(
        supplied: &RefinementClause,
        required: &RefinementClause,
    ) -> SubsumptionResult {
        match decide_subsumption(supplied, required) {
            NativeSubsumption::Holds => SubsumptionResult::Holds,
            NativeSubsumption::Violated { counterexample } => {
                SubsumptionResult::Violated { counterexample }
            }
        }
    }

    /// Walks the whole grid, comparing the native decider (with `planted` applied) against the
    /// three oracle functions: the number of cells compared, and every disagreement as a line
    /// naming the cell and both verdicts. An oracle timeout is a disagreement too: the native
    /// decider never times out, and the grid is far inside Z3's rlimit.
    fn disagreements<F, X, S>(
        fits: F,
        xfield: X,
        subsumption: S,
        planted: Planted,
    ) -> (usize, Vec<String>)
    where
        F: Fn(&RefinementClause, RefValue) -> RefinementVerdict,
        X: Fn(&RefinementClause, i64, i64) -> RefinementVerdict,
        S: Fn(&RefinementClause, &RefinementClause) -> SubsumptionResult,
    {
        let mut cells = 0;
        let mut bad = Vec::new();

        let values: Vec<RefValue> = NARROW
            .iter()
            .map(|n| RefValue::Narrow(*n))
            .chain(WIDE.iter().map(|w| RefValue::Wide(*w)))
            .collect();
        let bounds: Vec<RefinementRhs> = NARROW
            .iter()
            .map(|n| RefinementRhs::Literal(*n))
            .chain(WIDE.iter().map(|w| RefinementRhs::LiteralWide(*w)))
            .collect();
        let mut index = 0;
        for op in OPS {
            for value in &values {
                for bound in &bounds {
                    let c = clause(op, bound.clone());
                    let mut native = decide_literal_fits(&c, *value);
                    if planted == Planted::LiteralFits(index) {
                        native = invert(native);
                    }
                    let oracle = fits(&c, *value);
                    if !agree(native, oracle) {
                        bad.push(format!(
                            "LiteralFits {value:?} {op:?} {bound:?}: native {native:?}, oracle {oracle:?}"
                        ));
                    }
                    cells += 1;
                    index += 1;
                }
            }
        }

        let mut index = 0;
        for op in OPS {
            for lhs in NARROW {
                for rhs in NARROW {
                    let c = clause(op, RefinementRhs::Field("y".to_string()));
                    let mut native = decide_cross_field(&c, lhs, rhs);
                    if planted == Planted::CrossField(index) {
                        native = invert(native);
                    }
                    let oracle = xfield(&c, lhs, rhs);
                    if !agree(native, oracle) {
                        bad.push(format!(
                            "CrossField {lhs} {op:?} {rhs}: native {native:?}, oracle {oracle:?}"
                        ));
                    }
                    cells += 1;
                    index += 1;
                }
            }
        }

        let mut index = 0;
        for supplied_op in OPS {
            for supplied_bound in NARROW {
                for required_op in OPS {
                    for required_bound in NARROW {
                        let supplied = clause(supplied_op, RefinementRhs::Literal(supplied_bound));
                        let required = clause(required_op, RefinementRhs::Literal(required_bound));
                        let mut native = decide_subsumption(&supplied, &required);
                        if planted == Planted::Subsumption(index) {
                            native = match native {
                                NativeSubsumption::Holds => NativeSubsumption::Violated {
                                    counterexample: None,
                                },
                                NativeSubsumption::Violated { .. } => NativeSubsumption::Holds,
                            };
                        }
                        let oracle = subsumption(&supplied, &required);
                        let name = format!(
                            "Subsumption (x {supplied_op:?} {supplied_bound}) ⊆ (x {required_op:?} {required_bound})"
                        );
                        match (native, oracle) {
                            (NativeSubsumption::Holds, SubsumptionResult::Holds) => {}
                            (
                                NativeSubsumption::Violated { .. },
                                SubsumptionResult::Violated { counterexample },
                            ) => {
                                // The oracle's witness, when it reports one, must separate the
                                // clauses.
                                if let Some(x) = counterexample
                                    && !(holds_at(supplied_op, i128::from(x), supplied_bound)
                                        && !holds_at(required_op, i128::from(x), required_bound))
                                {
                                    bad.push(format!(
                                        "{name}: oracle witness {x} does not separate"
                                    ));
                                }
                            }
                            (native, oracle) => {
                                bad.push(format!("{name}: native {native:?}, oracle {oracle:?}"));
                            }
                        }
                        cells += 1;
                        index += 1;
                    }
                }
            }
        }

        (cells, bad)
    }

    #[test]
    fn dbc1_native_decider_agrees_with_z3() {
        let (cells, bad) = disagreements(
            check_refinement,
            check_refinement_xfield,
            check_refinement_subsumption,
            Planted::None,
        );
        assert_eq!(
            cells, GRID_CELLS,
            "the grid moved; re-pin its cardinality at the measured value"
        );
        assert!(
            bad.is_empty(),
            "the native decider disagrees with Z3 on {} of {cells} cells:\n{}",
            bad.len(),
            bad.join("\n")
        );
    }

    #[test]
    fn anti_stub_a_planted_wrong_verdict_is_reported_in_each_shape() {
        // Against itself, the native decider agrees everywhere; with one verdict inverted it
        // disagrees in exactly that cell, in each shape the walk compares.
        let (cells, bad) = disagreements(
            native_fits,
            native_xfield,
            native_subsumption,
            Planted::None,
        );
        assert_eq!(cells, GRID_CELLS);
        assert!(bad.is_empty(), "{bad:?}");
        for planted in [
            Planted::LiteralFits(0),
            Planted::CrossField(0),
            Planted::Subsumption(0),
        ] {
            let (_, bad) = disagreements(native_fits, native_xfield, native_subsumption, planted);
            assert_eq!(
                bad.len(),
                1,
                "{planted:?}: exactly the planted cell must disagree, found {bad:?}"
            );
        }
    }

    #[test]
    fn wide_bound_subsumption_is_refused_by_both_backends() {
        let wide = clause(RefinementOp::Ge, RefinementRhs::LiteralWide(WIDE[0]));
        let narrow = clause(RefinementOp::Ge, RefinementRhs::Literal(0));
        for (supplied, required) in [(&wide, &narrow), (&narrow, &wide), (&wide, &wide)] {
            assert_eq!(
                decide_subsumption(supplied, required),
                NativeSubsumption::Violated {
                    counterexample: None
                }
            );
            assert_eq!(
                check_refinement_subsumption(supplied, required),
                SubsumptionResult::Violated {
                    counterexample: None
                }
            );
        }
    }
}
