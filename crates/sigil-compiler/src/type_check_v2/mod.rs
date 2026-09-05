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
