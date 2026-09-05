//! Pure-data obligations for refinement checking.
//!
//! The Pure Pipeline (`refinement.rs`) walks a `TypedProgram` and emits
//! obligations into a `RefinementWorkload`. The orchestrator (`mod.rs`)
//! discharges each obligation through Z3 and routes the verdict to its
//! diagnostic. AIR capability obligations live in `crate::air_capability_v2`.
//!
//! This file MUST NOT import `z3`, the z3 capability module, or the z3
//! cache. `tests/quarantine_grep.rs` enforces that boundary.

use crate::ast::RefinementClause;
use crate::diagnostics::Diagnostic;
use crate::span::Span;

/// A single refinement proof obligation:
///
/// - `LiteralFits` checks one literal against one clause.
/// - `SubsumptionAny` accepts when any supplied clause subsumes the expected
///   clause.
/// - `CrossField` checks two literal fields jointly.
/// - `SubsumptionAtConstruction` retains the discharge-time counterexample
///   needed by T215.
///
/// Each variant carries the diagnostic the orchestrator should emit on a
/// `Violated` or `Timeout` verdict. The Pure Pipeline constructs these
/// diagnostics so the orchestrator does zero string formatting — its job
/// is purely verdict → diagnostic routing.
#[derive(Debug, Clone)]
#[allow(dead_code)] // `site` is evidence-bearing in workload Debug snapshots, not read during discharge
pub enum RefinementObligation {
    /// "Does literal `value` satisfy `clause`?" (`value` is `Narrow` for an
    /// i64-fitting literal and `Wide` for a larger u256 literal.)
    LiteralFits {
        clause: RefinementClause,
        value: crate::ast::RefValue,
        site: Span,
        on_violated: Diagnostic,
        on_timeout: Diagnostic,
    },
    /// "Does ANY of the supplied clauses imply `expected`?" Models the
    /// any-of-N semantics: the orchestrator asks Z3 about each pair and
    /// accepts on the first `Holds`.
    /// Emits `on_violated` only when ALL pairs fail; `on_timeout` if any
    /// query returns Timeout AND no later pair returns Holds.
    ///
    /// The Pure Pipeline pre-filters the syntactic fast-path:
    /// `refinements_match(supplied, expected)` is checked in the
    /// collector — if any supplied syntactically matches, NO obligation
    /// is emitted (no Z3 work). Only the symbolic residue reaches here.
    SubsumptionAny {
        actual: Vec<RefinementClause>,
        expected: RefinementClause,
        site: Span,
        on_violated: Diagnostic,
        on_timeout: Diagnostic,
    },
    /// "Do two literals jointly satisfy a 2-variable cross-field clause?"
    CrossField {
        clause: RefinementClause,
        lhs_value: i64,
        rhs_value: i64,
        site: Span,
        on_violated: Diagnostic,
        on_timeout: Diagnostic,
    },
    /// "Does ANY supplied clause subsume `expected` at a CONSTRUCTION site?"
    /// (record field / variant payload). Like `SubsumptionAny` (the
    /// syntactic fast-path is pre-filtered in the collector), but the
    /// record-construction T215 message embeds the Z3 counterexample, which
    /// is only known at discharge — so this variant carries NO pre-built
    /// diagnostic. The orchestrator runs the subsumption loop, captures the
    /// first counterexample + any timeout, and builds the T215 message
    /// itself (see `discharge_subsumption_at_construction`).
    SubsumptionAtConstruction {
        actual: Vec<RefinementClause>,
        expected: RefinementClause,
        site: Span,
    },
}

#[derive(Debug, Clone, Default)]
pub struct RefinementWorkload {
    pub obligations: Vec<RefinementObligation>,
}
