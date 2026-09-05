//! Pure AIR capability-obligation collector.
//!
//! This file must not contain any of:
//! - `use z3` (any path)
//! - `use crate::z3_capability` (any path)
//! - `use crate::z3_cache` (any path)
//! - the substring `Solver` / `z3::Context` / `DischargeContext`
//!
//! Enforced by `crates/sigil-compiler/tests/quarantine_grep.rs`
//! (`pure_pipeline_files_have_no_z3_imports` + the type-leak scan
//! `air_cap_collector_has_no_z3_type_leak`).
//!
//! ## What this collects
//!
//! One `AirCapabilityObligation` per capability-typed argument at each
//! Call / Spawn / Serialize sink site, plus one per cap-typed Return
//! terminator value. Each obligation carries:
//!
//! * `actual_mask` — the value's statically-traced authority bits
//!   (`trace_static_authority`, Z3-free), and
//! * `required_mask` — `registry.full_mask(cap_type)` (the sink demands
//!   full authority), plus the pre-built C003 `on_violated` diagnostic.
//!
//! Two program-invariant concerns belong to the discharge re-walk rather than
//! these per-sink evidence records:
//!
//! * **Legitimacy probes** (`assert_var_legitimate` → C002): per-variable
//!   Z3 legitimacy-Bool checks at spawn / message sites.
//! * **Global constraint-satisfiability** (the Phase 3 `solver.check()` →
//!   C002): a whole-function consistency check.
//!
//! `trace_static_authority`, `c003_message`, and `format_authority_set` are the
//! Z3-free helpers shared by evidence collection and production discharge.

use std::collections::HashMap;

use super::obligations::{AirCapabilityObligation, AirCapabilityWorkload, CapSinkKind};
use crate::air::{AirFunction, AirProgram, AirStmt, AirTerminator, AirValue, VarId};
use crate::diagnostics::{Diagnostic, codes};
use crate::type_check::AuthorityRegistry;

/// Collect capability obligations from a lowered `AirProgram` + the
/// program's `AuthorityRegistry`.
///
/// Returns `(Vec::new(), workload)` — the collector emits no standalone
/// diagnostics. Every obligation carries its own `on_violated`; the
/// discharge phase decides which actually fire. (The empty
/// diagnostic Vec keeps the `(Vec<Diagnostic>, Workload)` shape uniform
/// with the refinement collector and leaves room for collector-stage
/// diagnostics should a future sink need one.)
pub(super) fn collect_air_capability_obligations(
    program: &AirProgram,
    registry: &AuthorityRegistry,
) -> (Vec<Diagnostic>, AirCapabilityWorkload) {
    let mut workload = AirCapabilityWorkload::default();
    // Deterministic order (NC5 — quarantine contract, anchored in
    // docs/specs/v2-unification-decision.md §5): functions → blocks →
    // stmts, all Vecs.
    for function in &program.functions {
        collect_function_obligations(function, registry, &mut workload);
    }
    (Vec::new(), workload)
}

fn collect_function_obligations(
    function: &AirFunction,
    registry: &AuthorityRegistry,
    workload: &mut AirCapabilityWorkload,
) {
    // Record which statement defines each capability variable's authority.
    // Slot authority bit-vectors remain a discharge concern.
    let auth_sources = build_auth_sources(function);

    // One obligation per capability-typed argument, in block → statement
    // order; the Return
    // terminator's obligation (if any) comes after the block's stmts.
    for block in &function.blocks {
        for stmt in &block.stmts {
            let (cap_args, kind, sink_context): (Vec<VarId>, CapSinkKind, &str) = match stmt {
                AirStmt::Call { args, .. } => (args.clone(), CapSinkKind::Call, "call site"),
                AirStmt::SpawnActor { caps, fuel_cap, .. } => {
                    let mut v = caps.clone();
                    v.push(*fuel_cap);
                    (v, CapSinkKind::Spawn, "spawn argument")
                }
                AirStmt::SerializeMessage { args, .. } => {
                    (args.clone(), CapSinkKind::Serialize, "message argument")
                }
                _ => continue,
            };

            for arg in cap_args {
                emit_sink_obligation(
                    function,
                    registry,
                    &auth_sources,
                    arg,
                    kind,
                    sink_context,
                    workload,
                );
            }
        }

        if let AirTerminator::Return(Some(var)) = &block.terminator {
            emit_sink_obligation(
                function,
                registry,
                &auth_sources,
                *var,
                CapSinkKind::Return,
                "return value",
                workload,
            );
        }
    }
}

/// Emit one obligation for a capability-typed sink argument. Non-capability
/// arguments and zero-authority capability types require no obligation.
#[allow(clippy::too_many_arguments)]
fn emit_sink_obligation(
    function: &AirFunction,
    registry: &AuthorityRegistry,
    auth_sources: &HashMap<VarId, &AirStmt>,
    arg: VarId,
    kind: CapSinkKind,
    sink_context: &str,
    workload: &mut AirCapabilityWorkload,
) {
    // M4: covers Cap|StateCap — a state cap reaching this sink is authority-checked.
    let arg_kind = function.var_kind(arg);
    let Some(cap_type) = arg_kind.cap_type_name() else {
        return;
    };
    let full = registry.full_mask(cap_type);
    if full == 0 {
        // A zero-authority token trivially satisfies the sink.
        return;
    }

    let actual_mask = trace_static_authority(arg, auth_sources, full);
    // Diagnostic identity uses the stable `debug_names` channel with the
    // historical `_{id}` fallback, not `var_label`'s `v{id}` form.
    let var_name = function
        .debug_names
        .get(&arg)
        .cloned()
        .unwrap_or_else(|| format!("_{}", arg.0));
    let on_violated = Diagnostic::error(
        codes::C003,
        c003_message(
            &var_name,
            cap_type,
            sink_context,
            actual_mask,
            full,
            registry,
        ),
        // Def-site span of the offending cap VarId — the C003 obligation
        // is keyed on this VarId, so its def-site is the correct anchor
        // (cf. the discharge re-walk, which threads the same span).
        function.var_span(arg),
    );

    workload.obligations.push(AirCapabilityObligation {
        var_id: arg,
        cap_type: cap_type.to_owned(),
        required_mask: full,
        actual_mask,
        kind,
        on_violated,
    });
}

/// Build the authority-source map: capability variable → the statement that
/// defines its authority. Z3 slot-authority bookkeeping remains in discharge.
/// `SlotTake` is recorded for evidence even though static tracing terminates
/// there.
pub(super) fn build_auth_sources(function: &AirFunction) -> HashMap<VarId, &AirStmt> {
    let mut auth_sources: HashMap<VarId, &AirStmt> = HashMap::new();
    for block in &function.blocks {
        for stmt in &block.stmts {
            match stmt {
                AirStmt::CapRestrict { dst, .. }
                | AirStmt::CapSplit { dst, .. }
                | AirStmt::CapDraw { dst, .. }
                // Capabilities-as-values: `mint` is a legitimate authority
                // SOURCE — it originates the full mask of its cap type (the
                // `_ =>` arm in the authority-assignment + `trace_static_authority`
                // both terminate at `full_mask`). Registered explicitly so the
                // source is legible and a future Assign-aliasing change can't
                // chain a narrower mask THROUGH a mint.
                | AirStmt::CapMint { dst, .. } => {
                    auth_sources.insert(*dst, stmt);
                }
                AirStmt::Assign {
                    dst,
                    val: AirValue::Var(_),
                } if function.var_kind(*dst).is_cap() => {
                    auth_sources.insert(*dst, stmt);
                }
                AirStmt::SlotTake { dst_cap, .. } => {
                    auth_sources.insert(*dst_cap, stmt);
                }
                _ => {}
            }
        }
    }
    auth_sources
}

// ── Z3-free authority helpers ──────────────────────────────────────────────

/// Statically trace the authority mask of a cap variable by walking its
/// source-stmt chain. Returns the smallest mask the variable is
/// guaranteed to have, given only static information. CapRestrict
/// narrows; CapSplit and Assign(Var) preserve; opaque sources (params,
/// LoadField, Call returns, RecordConstruct, SlotTake) terminate the
/// walk at `full_mask`. Loop bound 512 guarantees termination.
pub(super) fn trace_static_authority(
    var: VarId,
    auth_sources: &HashMap<VarId, &AirStmt>,
    full_mask: u32,
) -> u32 {
    let mut current = var;
    let mut mask = full_mask;
    for _ in 0..512 {
        match auth_sources.get(&current) {
            Some(AirStmt::CapRestrict {
                src,
                restriction_mask,
                ..
            }) => {
                mask &= *restriction_mask;
                current = *src;
            }
            Some(AirStmt::CapSplit { src, .. }) | Some(AirStmt::CapDraw { src, .. }) => {
                current = *src;
            }
            Some(AirStmt::Assign {
                val: AirValue::Var(src),
                ..
            }) => {
                current = *src;
            }
            // Capabilities-as-values: a minted cap is an authority ORIGIN —
            // terminate the walk at `full_mask` (it has no narrower `src`).
            Some(AirStmt::CapMint { .. }) => break,
            _ => break,
        }
    }
    mask
}

/// Format a list of authority names as the policy author would read them.
/// Empty vec → "(none)"; one name → "{name}"; many → "{a}, {b}, {c}".
fn format_authority_set(names: &[String]) -> String {
    if names.is_empty() {
        "(none)".to_string()
    } else {
        names.join(", ")
    }
}

/// Build a C003 diagnostic message that names the actual authority set,
/// the required authority set, and the missing authorities. `context` is
/// the noun-phrase describing the sink ("call site", "spawn argument",
/// "return value", "message argument").
pub(super) fn c003_message(
    var_name: &str,
    cap_type: &str,
    context: &str,
    actual_mask: u32,
    required_mask: u32,
    registry: &AuthorityRegistry,
) -> String {
    let actual_names = registry.authority_names(cap_type, actual_mask);
    let required_names = registry.authority_names(cap_type, required_mask);
    let missing_mask = required_mask & !actual_mask;
    let missing_names = registry.authority_names(cap_type, missing_mask);
    format!(
        "`{var_name}` has `{cap_type}` authority {{{}}} but {context} requires {{{}}} (missing: {{{}}})",
        format_authority_set(&actual_names),
        format_authority_set(&required_names),
        format_authority_set(&missing_names),
    )
}
