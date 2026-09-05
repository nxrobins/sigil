//! Pure-data AIR capability obligations.
//!
//! This file must not import any of:
//! - `z3`
//! - `crate::z3_capability`
//! - `crate::z3_cache`
//!
//! Enforced by `crates/sigil-compiler/tests/quarantine_grep.rs`.
//!
//! ## What an obligation is
//!
//! Each `AirCapabilityObligation` describes ONE capability-flow check the
//! discharge phase must prove: "at this sink site, does the value's
//! statically-traced authority mask (`actual_mask`) cover what the sink
//! requires (`required_mask`)?". The Pure collector
//! (`collector::collect_air_capability_obligations`) walks the
//! `AirProgram` and emits one obligation per Call/Spawn/Serialize/Return
//! sink, carrying the pre-built `on_violated` diagnostic so the
//! orchestrator does zero string formatting — its job is purely
//! verdict → diagnostic routing.
//!
//! `actual_mask` is deterministic from static data-flow analysis
//! (`trace_static_authority`). No Z3 context is needed to build an obligation;
//! Z3 runs only during discharge. The `Air` prefix distinguishes these
//! post-lowering authority-mask records from type-check-time concepts.

use crate::air::VarId;
use crate::diagnostics::Diagnostic;

/// A capability sink site — the place a cap value reaches its consumer.
/// Carried in `AirCapabilityObligation` so the orchestrator can route
/// `Violated` verdicts to the right diagnostic code (C001/C002/C003 for
/// Call/Spawn/Serialize/Return).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CapSinkKind {
    Call,
    Spawn,
    Serialize,
    Return,
}

/// One capability-flow obligation: prove `actual_mask` covers
/// `required_mask` for the cap value at `var_id`.
///
/// All fields are pure data. `on_violated` is the diagnostic the
/// orchestrator emits if the discharge phase's Z3 verdict is `Violated`.
#[derive(Debug, Clone)]
pub struct AirCapabilityObligation {
    /// The AIR variable carrying the cap value at the sink site.
    pub var_id: VarId,
    /// Cap type name (e.g. `"Fuel"`), for the C003 authority-set message.
    pub cap_type: String,
    /// Authority bits the sink demands.
    pub required_mask: u32,
    /// Authority bits the value statically carries
    /// (`trace_static_authority` output — Z3-free).
    pub actual_mask: u32,
    /// Which sink kind this is, for verdict → diagnostic-code routing.
    pub kind: CapSinkKind,
    /// Diagnostic to emit if the discharge phase returns `Violated`.
    /// Pre-built by the Pure collector so the orchestrator does zero
    /// string formatting.
    pub on_violated: Diagnostic,
}

/// The full set of capability obligations for one `AirProgram`.
///
/// `obligations` order is deterministic: the collector iterates
/// `AirProgram.functions` → `AirFunction.blocks` → `AirBlock.stmts`
/// (all `Vec`s), so the obligation order is byte-stable across runs.
/// The discharge phase MUST iterate this `Vec` in order (NC6 / CM11 —
/// quarantine contract, anchored in docs/specs/v2-unification-decision.md
/// §5) so cumulative `rlimit_consumed` is deterministic.
#[derive(Debug, Clone, Default)]
pub struct AirCapabilityWorkload {
    pub obligations: Vec<AirCapabilityObligation>,
}
