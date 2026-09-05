//! Production AIR capability verification.
//!
//! ## Architecture
//!
//! Two phases plus a token:
//!
//! 1. **Pure** — `collector::collect_air_capability_obligations` walks an
//!    `AirProgram` + `AuthorityRegistry` and emits an
//!    `AirCapabilityWorkload`. It cannot call Z3; `tests/quarantine_grep.rs`
//!    enforces the import and type boundary.
//!
//! 2. **Discharge** — `discharge_air_capabilities` is the ONLY Z3-touching
//!    function in this tree. It checks legitimacy, authority bit-vectors,
//!    slot meets, individual sinks, and whole-function consistency before
//!    minting the proof token.
//!
//! 3. **Token** — `DischargedAirCapability` has a private `_seal: ()`
//!    constructor. Only `discharge_air_capabilities` can mint one; Rust
//!    privacy is the enforcement — the seal is unconstructible outside
//!    this file.
//!
//! `verify_air_capabilities` is the sole production AIR capability prover.
//! `capability::verify` calls it after structural checks; any diagnostic fails
//! compilation.
//!
//! Why the discharge re-walks the program rather than consuming the
//! collector's workload: static tracing stops at `SlotTake`, while the solver
//! computes the meet of all `SlotPut` authorities. A workload-only verdict
//! would therefore be unsound. The workload remains deterministic evidence;
//! the discharge re-walk is the enforcement authority.

pub mod collector;
pub mod obligations;

use crate::air::AirProgram;
use crate::diagnostics::Diagnostic;
#[cfg(feature = "solver")]
use crate::diagnostics::codes;
use crate::type_check::AuthorityRegistry;

use obligations::AirCapabilityWorkload;

/// Proof token: the AIR capability workload has been walked and every
/// obligation discharged. **Private constructor** (`_seal: ()`). Only
/// `discharge_air_capability_obligations` (in THIS file) can mint one —
/// no other module in the crate can construct this value (CM4 — quarantine
/// contract; docs/specs/v2-unification-decision.md §5 anchors the IDs).
///
/// Production verification mints and retains this token in its result. The
/// private seal prevents callers from manufacturing a discharged state.
#[derive(Debug)]
#[allow(dead_code)] // opaque seal is carried as proof and intentionally unread
pub struct DischargedAirCapability {
    _seal: (),
}

/// Test-seam output for the rlimit-forcing entry below. The historical public
/// name remains stable for integration tests.
#[derive(Debug)]
pub struct ShadowAirResult {
    pub diagnostics: Vec<Diagnostic>,
    pub _discharged: DischargedAirCapability,
}

/// Certificate-bound statistics from the sole-prover discharge.
///
/// * `checked_sites` — incremented at the seven semantic verification points:
///   record construction, spawn, restrict, split/draw, message serialization,
///   sink arguments, and returns.
/// * `z3_rlimit_consumed` — the discharge solver's cumulative tally.
///   It is excluded from certificate byte equality because solver accounting
///   is operational rather than semantic.
pub struct AirCapVerification {
    pub checked_sites: usize,
    pub z3_rlimit_consumed: Option<u64>,
}

/// The production AIR capability prover. Called by `capability::verify` after
/// structural checks pass. Any capability-flow or fragment-guard violation is
/// returned as a compile-failing diagnostic.
///
/// Diagnostics are returned in natural walk order; the prover does not reorder
/// semantic emission.
#[cfg(feature = "solver")]
pub fn verify_air_capabilities(
    program: &AirProgram,
    registry: &AuthorityRegistry,
) -> Result<AirCapVerification, Vec<Diagnostic>> {
    let (diagnostics, checked_sites, z3_rlimit_consumed, _token) =
        discharge_air_capabilities(program, registry);
    if diagnostics.is_empty() {
        Ok(AirCapVerification {
            checked_sites,
            z3_rlimit_consumed,
        })
    } else {
        Err(diagnostics)
    }
}

/// Test-only: run the discharge at a custom Z3 rlimit. Forcing `rlimit=1`
/// provokes Unknown → C004 deterministically — the only practical way to
/// exercise that verdict because corpus programs stay far below the production
/// budget. The arm-coverage test pins that Unknown never passes silently.
///
/// **Visibility:** `pub` (not `pub(crate)`) because the arm-coverage
/// integration test is a separate compilation unit. The `_at_rlimit`
/// suffix marks it test-only; production uses [`verify_air_capabilities`].
#[cfg(feature = "solver")]
pub fn run_air_capability_passes_at_rlimit(
    program: &AirProgram,
    registry: &AuthorityRegistry,
    rlimit: u32,
) -> ShadowAirResult {
    let (mut diagnostics, _sites, _rlimit, token) =
        discharge_air_capabilities_at_rlimit(program, registry, rlimit);
    diagnostics.sort_by_key(|d| {
        let span = d.span().unwrap_or_default();
        (span.source.0, span.start, d.code().as_str())
    });
    ShadowAirResult {
        diagnostics,
        _discharged: token,
    }
}

/// Test-only: run JUST the Pure collector and return the raw workload +
/// its collector-stage diagnostics. Mirrors
/// `type_check_v2::collect_workloads_for_test` but for the AIR-cap
/// pipeline — it needs a lowered `AirProgram`, so callers lower first.
///
/// Used by `sigil-test-utils::pipeline::collect_workloads_or_skip` to
/// feed `tests/workload_snapshots.rs`, pinning the SHAPE of the
/// capability obligations the collector emits (independent of whether
/// the discharge phase ultimately proves or rejects them).
///
/// **Visibility:** `pub` (not `pub(crate)`) because the workload-snapshot
/// integration test is a separate crate compilation unit. The `_for_test`
/// suffix is the contract; production code uses [`verify_air_capabilities`].
pub fn collect_air_capability_workload_for_test(
    program: &AirProgram,
    registry: &AuthorityRegistry,
) -> (Vec<Diagnostic>, AirCapabilityWorkload) {
    collector::collect_air_capability_obligations(program, registry)
}

/// Discharge AIR capability flow over the whole program. **The only
/// Z3-touching function in the `air_capability_v2` tree.**
///
/// Returns `(diagnostics, token)`. The token cannot be constructed any
/// other way (private `_seal` field; CM4 enforces exactly one mint site).
///
/// ## Why this re-walks the program (not the workload)
///
/// The collector's `AirCapabilityWorkload` carries a static `actual_mask`.
/// Static tracing stops at `SlotTake`, while Z3 computes the meet of every
/// `SlotPut` authority. A workload-driven bitwise verdict would miss slot-meet
/// violations, so discharge derives the complete constraint system directly
/// from the AIR program. The workload is observability evidence; the re-walk is
/// the enforcement authority.
///
/// ## Cache bypass
///
/// Calls `solver.check()` directly rather than using the verdict cache. Fresh
/// solves keep this security decision independent of cache state, and the
/// fragment guard runs immediately before every check. Resource accounting is
/// excluded from certificate byte equality and remains below the corpus budget.
#[cfg(feature = "solver")]
fn discharge_air_capabilities(
    program: &AirProgram,
    registry: &AuthorityRegistry,
) -> (Vec<Diagnostic>, usize, Option<u64>, DischargedAirCapability) {
    discharge_air_capabilities_at_rlimit(program, registry, AIR_CAP_Z3_RLIMIT)
}

/// Discharge at a caller-chosen Z3 rlimit. Factored out of
/// `discharge_air_capabilities` so the test-only
/// `run_air_capability_passes_at_rlimit` can force a tiny rlimit and
/// provoke Unknown → C004 deterministically. Production always uses
/// `AIR_CAP_Z3_RLIMIT`.
#[cfg(feature = "solver")]
fn discharge_air_capabilities_at_rlimit(
    program: &AirProgram,
    registry: &AuthorityRegistry,
    rlimit: u32,
) -> (Vec<Diagnostic>, usize, Option<u64>, DischargedAirCapability) {
    discharge_air_capabilities_at_budgets(program, registry, rlimit, AIR_CAP_Z3_PROGRAM_RLIMIT)
}

/// Test seam: force a tiny PER-PROGRAM budget to exercise the C004
/// program-budget rejection deterministically. Production uses the
/// `AIR_CAP_Z3_PROGRAM_RLIMIT` constant via the wrapper above.
#[cfg(feature = "solver")]
fn discharge_air_capabilities_at_budgets(
    program: &AirProgram,
    registry: &AuthorityRegistry,
    rlimit: u32,
    program_rlimit: u64,
) -> (Vec<Diagnostic>, usize, Option<u64>, DischargedAirCapability) {
    use z3::{Config, Context};

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = make_solver(&ctx, rlimit);
    let mut diagnostics = Vec::new();
    // Certificate evidence counts the seven semantic verification points.
    let mut checked_sites = 0usize;

    for function in &program.functions {
        verify_function(
            function,
            &ctx,
            &solver,
            registry,
            &mut diagnostics,
            &mut checked_sites,
        );
    }

    // Reject with C004 when cumulative solver consumption exceeds the
    // per-program policy. Corpus programs remain far below this boundary.
    let consumed = read_rlimit_count(&solver);
    if let Some(consumed) = consumed
        && consumed > program_rlimit
    {
        diagnostics.push(Diagnostic::error(
            codes::C004,
            format!(
                "Z3 program-level rlimit budget exceeded: consumed {consumed} \
                 across all functions (limit: {program_rlimit}). The policy \
                 may have unusually complex cap flow; consider simplifying or \
                 splitting the module."
            ),
            None,
        ));
    }

    (
        diagnostics,
        checked_sites,
        consumed,
        DischargedAirCapability { _seal: () },
    )
}

/// Per-invocation Z3 resource budget.
#[cfg(feature = "solver")]
const AIR_CAP_Z3_RLIMIT: u32 = 1_000_000;

/// Per-program cumulative Z3 resource budget.
#[cfg(feature = "solver")]
const AIR_CAP_Z3_PROGRAM_RLIMIT: u64 = 50_000_000;

/// Construct a solver with a deterministic resource limit.
#[cfg(feature = "solver")]
fn make_solver<'ctx>(ctx: &'ctx z3::Context, rlimit: u32) -> z3::Solver<'ctx> {
    let solver = z3::Solver::new(ctx);
    let mut params = z3::Params::new(ctx);
    params.set_u32("rlimit", rlimit);
    solver.set_params(&params);
    solver
}

/// Check the solver directly after enforcing the supported-fragment guard.
/// The sole prover bypasses the verdict cache by design (NC4/CM7; the
/// quarantine contract IDs are anchored in
/// docs/specs/v2-unification-decision.md §5). The shadow-era test that
/// pinned the bypass retired with the comparison harness, so today the
/// bypass is a stated decision, not a pinned one (V2D-2 there).
#[cfg(feature = "solver")]
fn check_direct(
    solver: &z3::Solver<'_>,
) -> Result<z3::SatResult, crate::z3_fragment_guard::FragmentViolation> {
    let report = crate::z3_fragment_guard::check_fragment(solver)?;
    crate::z3_fragment_guard::record_observations(&report);
    #[allow(clippy::disallowed_methods)] // sanctioned: NC4/CM7 direct check (walk above)
    Ok(solver.check())
}

/// Convert a fragment-guard violation into a conservative compile rejection.
#[cfg(feature = "solver")]
fn c005_diagnostic(
    violation: &crate::z3_fragment_guard::FragmentViolation,
    site: &str,
) -> Diagnostic {
    Diagnostic::error(
        codes::C005,
        format!(
            "internal: SMT query left the decidable fragment at the {site} — {violation}; \
             this is a compiler bug (see docs/specs/z3-fragment-guard.md)"
        ),
        None,
    )
}

/// Read the cumulative `rlimit count` statistic, or `None` when the active Z3
/// version does not expose it.
#[cfg(feature = "solver")]
fn read_rlimit_count(solver: &z3::Solver<'_>) -> Option<u64> {
    use z3::StatisticsValue;
    match solver.get_statistics().value("rlimit count") {
        Some(StatisticsValue::UInt(v)) => Some(v as u64),
        Some(StatisticsValue::Double(v)) if v >= 0.0 => Some(v as u64),
        _ => None,
    }
}

// ── Production Z3 capability verifier ─────────────────────────────────────
//
// The verifier owns legitimacy booleans, authority bit-vector constraints,
// slot meets, per-sink probes, and the final whole-function consistency check.
// Static authority tracing and C003 formatting are shared with the pure
// collector so evidence and enforcement use one vocabulary.

#[cfg(feature = "solver")]
use crate::air::{AirFunction, AirStmt, AirTerminator, AirValue, BlockId, VarId};
#[cfg(feature = "solver")]
use z3::{
    Context, SatResult, Solver,
    ast::{Ast, BV, Bool, Int},
};

#[cfg(feature = "solver")]
fn verify_function<'ctx>(
    function: &AirFunction,
    ctx: &'ctx Context,
    solver: &Solver<'ctx>,
    registry: &AuthorityRegistry,
    diagnostics: &mut Vec<Diagnostic>,
    checked_sites: &mut usize,
) {
    solver.push();

    // Phase 1: legitimacy constraints for all cap-typed variables.
    let mut legitimacy: std::collections::HashMap<(VarId, BlockId, usize), Bool<'ctx>> =
        std::collections::HashMap::new();

    for (var, _) in &function.params {
        if function.var_kind(*var).is_cap() {
            let name = format!("legit_param_{}", var.0);
            let legit = Bool::new_const(ctx, name.as_str());
            solver.assert(&legit);
            legitimacy.insert((*var, BlockId(u32::MAX), 0), legit);
        }
    }

    for block in &function.blocks {
        for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
            match stmt {
                AirStmt::Assign {
                    dst,
                    val: AirValue::RecordConstruct { .. },
                } if function.var_kind(*dst).is_cap() => {
                    *checked_sites += 1;
                    let name = format!("legit_{}_{}_{}", dst.0, block.id.0, stmt_idx);
                    let legit = Bool::new_const(ctx, name.as_str());
                    solver.assert(&legit.not());
                    legitimacy.insert((*dst, block.id, stmt_idx), legit);
                }
                AirStmt::SpawnActor {
                    dst,
                    caps,
                    fuel_cap,
                    ..
                } => {
                    *checked_sites += 1;
                    let name = format!("legit_{}_{}_{}", dst.0, block.id.0, stmt_idx);
                    let legit = Bool::new_const(ctx, name.as_str());
                    solver.assert(&legit);
                    legitimacy.insert((*dst, block.id, stmt_idx), legit);

                    for cap in caps {
                        assert_var_legitimate(
                            function,
                            *cap,
                            &legitimacy,
                            solver,
                            diagnostics,
                            "spawn cap argument",
                        );
                    }
                    assert_var_legitimate(
                        function,
                        *fuel_cap,
                        &legitimacy,
                        solver,
                        diagnostics,
                        "spawn fuel argument",
                    );
                }
                // Capabilities-as-values: `mint <Cap> for <target>` is a
                // SANCTIONED cap source — assert its `dst` legitimate (the
                // SpawnActor precedent above). The authorization is proven at
                // type-check (the `mintable_by` gate + T273, fail-closed BEFORE
                // AIR), so the oracle trusts any mint that reaches it. This arm
                // is MANDATORY (harden E1): without it, a minted cap has no
                // legitimacy entry and `assert_var_legitimate` accepts it by
                // OMISSION (fail-open) — accepting for the wrong reason, and a
                // forgery hole if an ungated mint ever reached AIR. The
                // `every_cap_originating_stmt_is_legitimacy_seeded` test
                // (cap_source_legitimacy_guard.rs) pins every cap-defining
                // stmt into this match.
                AirStmt::CapMint { dst, .. } => {
                    *checked_sites += 1;
                    let name = format!("legit_{}_{}_{}", dst.0, block.id.0, stmt_idx);
                    let legit = Bool::new_const(ctx, name.as_str());
                    solver.assert(&legit);
                    legitimacy.insert((*dst, block.id, stmt_idx), legit);
                }
                AirStmt::CapRestrict { dst, src, .. } => {
                    *checked_sites += 1;
                    let dst_name = format!("legit_{}_{}_{}", dst.0, block.id.0, stmt_idx);
                    let dst_legit = Bool::new_const(ctx, dst_name.as_str());
                    if let Some(src_legit) = find_legitimacy(*src, &legitimacy) {
                        solver.assert(&dst_legit._eq(&src_legit));
                    } else {
                        solver.assert(&dst_legit);
                    }
                    legitimacy.insert((*dst, block.id, stmt_idx), dst_legit);

                    let src_perms = Int::new_const(ctx, format!("perms_{}", src.0).as_str());
                    let dst_perms = Int::new_const(ctx, format!("perms_{}", dst.0).as_str());
                    solver.assert(&dst_perms.le(&src_perms));
                }
                AirStmt::CapSplit { dst, src, amount } | AirStmt::CapDraw { dst, src, amount } => {
                    *checked_sites += 1;
                    let dst_name = format!("legit_{}_{}_{}", dst.0, block.id.0, stmt_idx);
                    let dst_legit = Bool::new_const(ctx, dst_name.as_str());
                    if let Some(src_legit) = find_legitimacy(*src, &legitimacy) {
                        solver.assert(&dst_legit._eq(&src_legit));
                    } else {
                        solver.assert(&dst_legit);
                    }
                    legitimacy.insert((*dst, block.id, stmt_idx), dst_legit);

                    let src_fuel = Int::new_const(ctx, format!("fuel_{}", src.0).as_str());
                    let split_amount =
                        Int::new_const(ctx, format!("split_amount_{}", amount.0).as_str());
                    let dst_fuel = Int::new_const(ctx, format!("fuel_{}", dst.0).as_str());

                    solver.assert(&dst_fuel._eq(&split_amount));
                    solver.assert(&src_fuel.ge(&split_amount));
                    solver.assert(&split_amount.ge(&Int::from_i64(ctx, 0)));
                    solver.assert(&src_fuel.ge(&Int::from_i64(ctx, 0)));
                }
                AirStmt::MessageSend { msg, .. } | AirStmt::MessageAsk { msg, .. }
                    if function.var_kind(*msg).is_cap() =>
                {
                    *checked_sites += 1;
                    assert_var_legitimate(
                        function,
                        *msg,
                        &legitimacy,
                        solver,
                        diagnostics,
                        "message capability",
                    );
                }
                _ => {}
            }
        }
    }

    // Phase 2: authority bitvector constraints.
    let mut auth_sources: std::collections::HashMap<VarId, &AirStmt> =
        std::collections::HashMap::new();
    let mut slot_authority: std::collections::HashMap<VarId, Vec<BV<'ctx>>> =
        std::collections::HashMap::new();
    for block in &function.blocks {
        for stmt in &block.stmts {
            match stmt {
                AirStmt::CapRestrict { dst, .. }
                | AirStmt::CapSplit { dst, .. }
                | AirStmt::CapDraw { dst, .. } => {
                    auth_sources.insert(*dst, stmt);
                }
                AirStmt::Assign {
                    dst,
                    val: AirValue::Var(_),
                } if function.var_kind(*dst).is_cap() => {
                    auth_sources.insert(*dst, stmt);
                }
                AirStmt::SlotPut { slot, cap } => {
                    let cap_auth = BV::new_const(ctx, format!("auth_{}", cap.0), 32);
                    slot_authority.entry(*slot).or_default().push(cap_auth);
                }
                AirStmt::SlotTake { dst_cap, .. } => {
                    auth_sources.insert(*dst_cap, stmt);
                }
                _ => {}
            }
        }
    }

    let auth_var = |var: VarId| -> BV<'ctx> { BV::new_const(ctx, format!("auth_{}", var.0), 32) };

    for (var, _) in function.params.iter().chain(function.locals.iter()) {
        // M4: `cap_type_name` matches both `Cap` and `StateCap` — a state cap must
        // still get an authority BV (full mask by default), or it silently drops
        // out of the Z3 authority system (fail-open) and `.restrict`/`.draw`
        // authority checks on state caps stop firing.
        let var_kind = function.var_kind(*var);
        if let Some(cap_type) = var_kind.cap_type_name() {
            let auth = auth_var(*var);
            if let Some(source_stmt) = auth_sources.get(var) {
                match source_stmt {
                    AirStmt::CapRestrict {
                        src,
                        restriction_mask,
                        ..
                    } => {
                        let src_auth = auth_var(*src);
                        let mask = BV::from_u64(ctx, *restriction_mask as u64, 32);
                        solver.assert(&auth._eq(&src_auth.bvand(&mask)));
                        solver.assert(&auth.bvule(&src_auth));
                    }
                    AirStmt::CapSplit { src, .. } | AirStmt::CapDraw { src, .. } => {
                        let src_auth = auth_var(*src);
                        solver.assert(&auth._eq(&src_auth));
                    }
                    AirStmt::Assign {
                        val: AirValue::Var(src),
                        ..
                    } => {
                        let src_auth = auth_var(*src);
                        solver.assert(&auth._eq(&src_auth));
                    }
                    AirStmt::SlotTake { slot, .. } => {
                        let slot_auth = match slot_authority.get(slot) {
                            Some(puts) if !puts.is_empty() => puts
                                .iter()
                                .cloned()
                                .reduce(|a, b| a.bvand(&b))
                                .expect("non-empty by guard"),
                            _ => BV::from_u64(ctx, 0, 32),
                        };
                        solver.assert(&auth._eq(&slot_auth));
                    }
                    _ => {
                        let full = registry.full_mask(cap_type);
                        solver.assert(&auth._eq(&BV::from_u64(ctx, full as u64, 32)));
                    }
                }
            } else {
                let full = registry.full_mask(cap_type);
                solver.assert(&auth._eq(&BV::from_u64(ctx, full as u64, 32)));
            }
        }
    }

    // Sinks: each cap-typed arg at Call/Spawn/Serialize/Return must have
    // full authority.
    for block in &function.blocks {
        for stmt in &block.stmts {
            let (cap_args, sink_context): (Vec<VarId>, &str) = match stmt {
                AirStmt::Call { args, .. } => (
                    args.iter()
                        .filter(|v| function.var_kind(**v).is_cap())
                        .copied()
                        .collect(),
                    "call site",
                ),
                AirStmt::SpawnActor { caps, fuel_cap, .. } => {
                    let mut v: Vec<VarId> = caps.to_vec();
                    v.push(*fuel_cap);
                    (v, "spawn argument")
                }
                AirStmt::SerializeMessage { args, .. } => (
                    args.iter()
                        .filter(|v| function.var_kind(**v).is_cap())
                        .copied()
                        .collect(),
                    "message argument",
                ),
                _ => (Vec::new(), ""),
            };

            for arg in cap_args {
                // M4: sink authority check applies to state caps too (Cap|StateCap).
                let arg_kind = function.var_kind(arg);
                if let Some(cap_type) = arg_kind.cap_type_name() {
                    *checked_sites += 1;
                    let full = registry.full_mask(cap_type);
                    if full == 0 {
                        continue;
                    }
                    let required = BV::from_u64(ctx, full as u64, 32);
                    let actual = auth_var(arg);

                    solver.push();
                    // theory: QF_BV<32> (bvand on 32-bit authority masks).
                    // See docs/z3-theory-inventory.md §2 site #1.
                    solver.assert(&actual.bvand(&required)._eq(&required).not());
                    match check_direct(solver) {
                        Err(v) => {
                            diagnostics.push(c005_diagnostic(&v, "call-site authority sink"));
                        }
                        Ok(SatResult::Sat) => {
                            let var_name = function
                                .debug_names
                                .get(&arg)
                                .cloned()
                                .unwrap_or_else(|| format!("_{}", arg.0));
                            let actual_mask =
                                collector::trace_static_authority(arg, &auth_sources, full);
                            diagnostics.push(Diagnostic::error(
                                codes::C003,
                                collector::c003_message(
                                    &var_name,
                                    cap_type,
                                    sink_context,
                                    actual_mask,
                                    full,
                                    registry,
                                ),
                                function.var_span(arg),
                            ));
                        }
                        Ok(SatResult::Unsat) => {}
                        Ok(SatResult::Unknown) => {
                            let var_name = function
                                .debug_names
                                .get(&arg)
                                .cloned()
                                .unwrap_or_else(|| format!("_{}", arg.0));
                            diagnostics.push(Diagnostic::error(
                                codes::C004,
                                format!(
                                    "Z3 could not prove sufficient `{cap_type}` authority for `{var_name}` \
                                     at call site in `{}` (reason: {})",
                                    function.name,
                                    solver.get_reason_unknown().unwrap_or_else(|| "unknown".into()),
                                ),
                                function.var_span(arg),
                            ));
                        }
                    }
                    solver.pop(1);
                }
            }
        }

        if let AirTerminator::Return(Some(var)) = &block.terminator
            && let Some(cap_type) = function.var_kind(*var).cap_type_name()
        {
            // M4: `cap_type_name` covers Cap|StateCap so a returned state cap is
            // still authority-checked here (the linear-consume C010 is separate).
            *checked_sites += 1;
            let full = registry.full_mask(cap_type);
            if full > 0 {
                let required = BV::from_u64(ctx, full as u64, 32);
                let actual = auth_var(*var);
                solver.push();
                // theory: QF_BV<32> (return-sink authority check).
                // See docs/z3-theory-inventory.md §2 site #2.
                solver.assert(&actual.bvand(&required)._eq(&required).not());
                match check_direct(solver) {
                    Err(v) => {
                        diagnostics.push(c005_diagnostic(&v, "return-value authority sink"));
                    }
                    Ok(SatResult::Sat) => {
                        let var_name = function
                            .debug_names
                            .get(var)
                            .cloned()
                            .unwrap_or_else(|| format!("_{}", var.0));
                        let actual_mask =
                            collector::trace_static_authority(*var, &auth_sources, full);
                        diagnostics.push(Diagnostic::error(
                            codes::C003,
                            collector::c003_message(
                                &var_name,
                                cap_type,
                                "return value",
                                actual_mask,
                                full,
                                registry,
                            ),
                            function.var_span(*var),
                        ));
                    }
                    Ok(SatResult::Unsat) => {}
                    Ok(SatResult::Unknown) => {
                        let var_name = function
                            .debug_names
                            .get(var)
                            .cloned()
                            .unwrap_or_else(|| format!("_{}", var.0));
                        diagnostics.push(Diagnostic::error(
                            codes::C004,
                            format!(
                                "Z3 could not prove sufficient `{cap_type}` authority for `{var_name}` \
                                 at return in `{}` (reason: {})",
                                function.name,
                                solver.get_reason_unknown().unwrap_or_else(|| "unknown".into()),
                            ),
                            function.var_span(*var),
                        ));
                    }
                }
                solver.pop(1);
            }
        }
    }

    // Phase 3: global constraint-satisfiability check.
    // theory: QF_BV<32> + QF_LIA (mixed, disjoint signatures).
    // See docs/z3-theory-inventory.md §2 site #3.
    match check_direct(solver) {
        Err(v) => {
            diagnostics.push(c005_diagnostic(&v, "constraint-consistency probe"));
        }
        Ok(SatResult::Unsat) => {
            diagnostics.push(Diagnostic::error(
                codes::C002,
                format!(
                    "Z3 capability verifier found unsatisfiable constraints in `{}` — \
                     capability provenance violation detected",
                    function.name
                ),
                // Whole-function verdict: no single offending VarId, so
                // anchor at the function declaration.
                Some(function.def_span),
            ));
        }
        Ok(SatResult::Sat) => {}
        Ok(SatResult::Unknown) => {
            diagnostics.push(Diagnostic::error(
                codes::C004,
                format!(
                    "Z3 capability verifier returned unknown for `{}` (reason: {})",
                    function.name,
                    solver
                        .get_reason_unknown()
                        .unwrap_or_else(|| "unknown".into()),
                ),
                // Whole-function verdict: no single offending VarId, so
                // anchor at the function declaration.
                Some(function.def_span),
            ));
        }
    }

    solver.pop(1);
}

/// Assert a variable is legitimate; emit C002 if Z3 finds it may be
/// illegitimate, or C004 when Z3 returns Unknown.
#[cfg(feature = "solver")]
fn assert_var_legitimate<'ctx>(
    function: &AirFunction,
    var: VarId,
    legitimacy: &std::collections::HashMap<(VarId, BlockId, usize), Bool<'ctx>>,
    solver: &Solver<'ctx>,
    diagnostics: &mut Vec<Diagnostic>,
    context: &str,
) {
    if !function.var_kind(var).is_cap() {
        return;
    }

    if let Some(legit) = find_legitimacy(var, legitimacy) {
        solver.push();
        // theory: propositional Bool (legitimacy probe).
        // See docs/z3-theory-inventory.md §2 site #4.
        solver.assert(&legit.not());
        match check_direct(solver) {
            Err(v) => {
                diagnostics.push(c005_diagnostic(&v, "legitimacy probe"));
            }
            Ok(SatResult::Sat) => {
                diagnostics.push(Diagnostic::error(
                    codes::C002,
                    format!(
                        "Z3 capability verifier: `{}` may be an illegitimate capability \
                         used as {context} in `{}`",
                        function.var_label(var),
                        function.name,
                    ),
                    function.var_span(var),
                ));
            }
            Ok(SatResult::Unsat) => {}
            Ok(SatResult::Unknown) => {
                diagnostics.push(Diagnostic::error(
                    codes::C004,
                    format!(
                        "Z3 could not prove legitimacy of `{}` used as {context} in `{}` (reason: {})",
                        function.var_label(var),
                        function.name,
                        solver.get_reason_unknown().unwrap_or_else(|| "unknown".into()),
                    ),
                    function.var_span(var),
                ));
            }
        }
        solver.pop(1);
    }
}

/// Find a variable's legitimacy constraint using AIR's SSA-like
/// single-assignment property.
#[cfg(feature = "solver")]
fn find_legitimacy<'ctx>(
    var: VarId,
    legitimacy: &std::collections::HashMap<(VarId, BlockId, usize), Bool<'ctx>>,
) -> Option<Bool<'ctx>> {
    if let Some(legit) = legitimacy.get(&(var, BlockId(u32::MAX), 0)) {
        return Some(legit.clone());
    }
    legitimacy
        .iter()
        .filter(|((v, _, _), _)| *v == var)
        .map(|(_, legit)| legit.clone())
        .next()
}

#[cfg(all(test, feature = "solver"))]
mod tests {
    //! Budget and resource-limit behavior for the sole AIR capability prover.

    use super::*;
    use crate::air::{
        AirBlock, AirFunction, AirFunctionKind, AirTerminator, AirType, AirValueKind, BlockId,
        VarId,
    };
    use crate::ast::Ring;
    use crate::diagnostics::codes;

    /// Sanity: the production rlimit is large enough that a trivial program
    /// passes verification cleanly. If this regresses the rlimit needs to be
    /// raised — but raise it from data, not from a hunch.
    #[test]
    fn production_rlimit_accepts_trivial_program() {
        let program = trivial_cap_program();
        let registry = AuthorityRegistry::default();
        let _ = verify_air_capabilities(&program, &registry)
            .expect("trivial cap program must verify cleanly under AIR_CAP_Z3_RLIMIT");
    }

    /// The silent-Unknown closure works end-to-end: under rlimit=1, the
    /// prover MUST NOT return a silent pass — every Unknown hit during a
    /// real check must surface as a C004 diagnostic. Either the program
    /// verifies (Z3 answered fast enough at rlimit=1) or every emitted
    /// diagnostic is C004 — both sound; a silent Ok with internal
    /// Unknowns would be the soundness hole this pins shut.
    #[test]
    fn rlimit_one_is_either_ok_or_c004_never_silent() {
        let program = trivial_cap_program();
        let registry = AuthorityRegistry::default();
        let (diags, _, _, _) = discharge_air_capabilities_at_rlimit(&program, &registry, 1);
        let non_c004: Vec<_> = diags.iter().filter(|d| d.code() != codes::C004).collect();
        assert!(
            non_c004.is_empty(),
            "rlimit=1 path produced non-C004 errors (a silent pass surfaced as something else): {non_c004:?}"
        );
    }

    /// Headroom invariant: the trivial workload must pass under HALF of
    /// the production rlimit, proving at least 2× budget margin over the
    /// observed workload — so noisy queries or future small additions
    /// don't fail spuriously. If this fails after raising fixture
    /// complexity, raise `AIR_CAP_Z3_RLIMIT` (not the divisor) — keep the
    /// 2× headroom invariant intact. NOTE: the sole prover bypasses the
    /// verdict cache, so consumption here is the true uncached cost.
    #[test]
    fn rlimit_has_at_least_2x_headroom() {
        let program = trivial_cap_program();
        let registry = AuthorityRegistry::default();
        let (diags, _, _, _) =
            discharge_air_capabilities_at_rlimit(&program, &registry, AIR_CAP_Z3_RLIMIT / 2);
        assert!(
            diags.is_empty(),
            "trivial cap program must verify under AIR_CAP_Z3_RLIMIT/2 — \
             rlimit has insufficient headroom over observed workload: {diags:?}"
        );
    }

    /// The sync pin `z3_capability.rs`'s `Z3_RLIMIT` doc cites: refinement
    /// queries and cap-flow queries run on the same per-query budget. If
    /// the constants must ever diverge, update both doc comments with the
    /// new relationship in the same commit — an undocumented split would
    /// silently give the two query families different budgets.
    #[test]
    fn rlimit_constants_stay_in_sync() {
        assert_eq!(
            AIR_CAP_Z3_RLIMIT,
            crate::z3_capability::Z3_RLIMIT,
            "AIR_CAP_Z3_RLIMIT diverged from z3_capability::Z3_RLIMIT — \
             update the doc comments on both constants with the new basis"
        );
    }

    /// The `z3_rlimit_consumed` stat is populated (Some, non-zero) for
    /// compiler-produced programs under the production prover. Catches
    /// regressions where the statistics readout silently breaks (e.g. a
    /// Z3 version change drops the "rlimit count" key) — the budget
    /// enforcement would then silently no-op, an escape hatch.
    #[test]
    fn rlimit_consumption_is_measured() {
        let program = trivial_cap_program();
        let registry = AuthorityRegistry::default();
        let stats = verify_air_capabilities(&program, &registry)
            .expect("trivial cap program verifies cleanly");
        assert!(
            stats.z3_rlimit_consumed.is_some(),
            "Z3 statistics 'rlimit count' key is unavailable in this z3 \
             version — the per-program budget check is silently no-op. \
             Investigate and either pin z3 to a compatible version or \
             find the new key name."
        );
        let consumed = stats.z3_rlimit_consumed.unwrap();
        assert!(
            consumed > 0,
            "rlimit consumption reported zero for a non-trivial verify pass — \
             suspect Z3 statistics drift; got {consumed}"
        );
    }

    /// The per-program budget rejects a program whose cumulative SMT cost
    /// exceeds the bound: force a tiny program-budget (1) against a real
    /// program to provoke the rejection deterministically.
    #[test]
    fn per_program_budget_rejects_when_exceeded() {
        let program = trivial_cap_program();
        let registry = AuthorityRegistry::default();
        let (diags, _, _, _) =
            discharge_air_capabilities_at_budgets(&program, &registry, AIR_CAP_Z3_RLIMIT, 1);
        assert!(
            diags.iter().any(|d| d.code() == codes::C004),
            "expected C004 (program-budget exceeded), got: {diags:?}"
        );
        assert!(
            diags
                .iter()
                .any(|d| d.message().contains("program-level rlimit budget exceeded")),
            "expected per-program budget message, got: {diags:?}"
        );
    }

    fn trivial_cap_program() -> AirProgram {
        AirProgram {
            functions: vec![AirFunction {
                name: "sigil::trivial".to_owned(),
                export_name: "sigil__trivial".to_owned(),
                ring: Ring::default(),
                kind: AirFunctionKind::ModuleFunction,
                params: vec![(VarId(0), AirType::Ptr)],
                ret: AirType::Unit,
                locals: Vec::new(),
                value_kinds: [(VarId(0), AirValueKind::Cap("Fuel".to_owned()))]
                    .into_iter()
                    .collect(),
                debug_names: [(VarId(0), "fuel".to_owned())].into_iter().collect(),
                blocks: vec![AirBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: AirTerminator::Return(None),
                }],
                entry_block: BlockId(0),
                def_span: Default::default(),
                debug_spans: Default::default(),
                block_static_multiplicity: Vec::new(),
                security: Default::default(),
            }],
        }
    }
}
