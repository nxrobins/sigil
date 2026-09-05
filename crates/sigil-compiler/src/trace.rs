//! Phase 5a-1.6 / I21 / AP17: typed trace events for compiler internals.
//!
//! Event surface (today):
//! - `cross_module_dispatch` — every cross-module function-call resolution
//!   decision (Found / Private / CrossRing / Ambiguous / NotFound).
//! - `method_call_reroute` — every parser-MethodCall that gets routed to
//!   cross-module dispatch (or rejected via T156 shadowing).
//! - `use_scope_built` — once per module, after `build_use_scope`.
//! - `cycle_detected` — once per detected `use`-graph cycle.
//!
//! Discipline (enforced by `trace_smoke.rs` test):
//! - Every event has a typed payload (no free-text format strings).
//! - Payloads carry AST node IDs, spans, code identifiers, module
//!   names — NEVER raw source bytes.
//! - The `trace` Cargo feature gates all emission; without the feature,
//!   every emit function is a no-op (the `tracing` macros const-fold).
//!
//! Anti-pattern AP17 makes free-text `tracing::trace!()` calls in the
//! compiler a code-review-reject. Use the typed emit functions here
//! instead.

#![allow(dead_code)] // Some events are wired only when corresponding
// code paths exist; suppress dead-code on stub variants.

use crate::span::Span;

/// Outcome of a cross-module dispatch attempt. Mirrors the
/// `CrossModuleResolution` enum in `type_check.rs` but with no
/// borrowed data — safe to log.
#[derive(Debug, Clone, Copy)]
pub enum DispatchOutcome {
    /// Found a Public callable in the resolved module.
    Found,
    /// Module/symbol exists but the callee is private.
    Private,
    /// Caller and callee are in different rings (R004).
    CrossRing,
    /// Single-segment name found in 2+ `use`'d modules (N008).
    Ambiguous,
    /// No matching module/symbol — falls through to local lookup.
    NotFound,
}

/// One cross-module dispatch decision.
#[derive(Debug, Clone)]
pub struct CrossModuleDispatch<'a> {
    pub caller_module: &'a str,
    pub callee_path: &'a [String],
    pub outcome: DispatchOutcome,
    pub span: Span,
    /// For Ambiguous, list the candidate module names.
    pub candidates: &'a [String],
    /// For Found, the resolved fully-qualified name.
    pub resolved: Option<&'a str>,
}

/// One method-call reroute decision (parser produced MethodCall, but the
/// receiver looked like a module name).
#[derive(Debug, Clone, Copy)]
pub enum RerouteOutcome {
    /// Receiver is a known module name, no shadowing — routed to
    /// cross-module dispatch.
    Routed,
    /// Receiver is shadowed by a local variable; T156 fired.
    ShadowedRejected,
    /// Receiver doesn't look like a module — proceeded as method call.
    NotModule,
}

#[derive(Debug, Clone)]
pub struct MethodCallReroute<'a> {
    pub caller_module: &'a str,
    pub receiver: &'a str,
    pub method: &'a str,
    pub outcome: RerouteOutcome,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct UseScopeBuilt<'a> {
    pub module: &'a str,
    pub alias_count: usize,
}

#[derive(Debug, Clone)]
pub struct CycleDetected<'a> {
    pub path_len: usize,
    pub head: &'a str,
    pub tail: &'a str,
}

// ── Emit functions ────────────────────────────────────────────────────────
//
// Each emit function is gated on the `trace` feature. Without the
// feature, the function body is empty and the `tracing` crate isn't
// linked.

#[cfg(feature = "trace")]
pub fn dispatch(event: &CrossModuleDispatch<'_>) {
    tracing::trace!(
        target: "sigil_compiler::cross_module",
        caller = event.caller_module,
        callee = ?event.callee_path,
        outcome = ?event.outcome,
        candidates = ?event.candidates,
        resolved = ?event.resolved,
        span_start = event.span.start,
        span_end = event.span.end,
        "cross_module_dispatch"
    );
}

#[cfg(not(feature = "trace"))]
pub fn dispatch(_event: &CrossModuleDispatch<'_>) {}

#[cfg(feature = "trace")]
pub fn reroute(event: &MethodCallReroute<'_>) {
    tracing::trace!(
        target: "sigil_compiler::method_call_reroute",
        caller = event.caller_module,
        receiver = event.receiver,
        method = event.method,
        outcome = ?event.outcome,
        span_start = event.span.start,
        span_end = event.span.end,
        "method_call_reroute"
    );
}

#[cfg(not(feature = "trace"))]
pub fn reroute(_event: &MethodCallReroute<'_>) {}

#[cfg(feature = "trace")]
pub fn use_scope_built(event: &UseScopeBuilt<'_>) {
    tracing::trace!(
        target: "sigil_compiler::use_scope",
        module = event.module,
        alias_count = event.alias_count,
        "use_scope_built"
    );
}

#[cfg(not(feature = "trace"))]
pub fn use_scope_built(_event: &UseScopeBuilt<'_>) {}

#[cfg(feature = "trace")]
pub fn cycle(event: &CycleDetected<'_>) {
    tracing::trace!(
        target: "sigil_compiler::cycle",
        path_len = event.path_len,
        head = event.head,
        tail = event.tail,
        "cycle_detected"
    );
}

#[cfg(not(feature = "trace"))]
pub fn cycle(_event: &CycleDetected<'_>) {}
