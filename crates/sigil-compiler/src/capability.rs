//! The structural half of the AIR capability gate. Walks every AIR
//! function's blocks and rejects capability shape violations with exact
//! codes: C001 (a `RecordConstruct` assigned into a cap-kinded
//! destination, i.e. a forged capability), R010/R011 (non-cap, non-slot
//! spawn argument / non-cap fuel argument), R012 (attenuation via
//! `CapRestrict`/`CapSplit`/`CapDraw` that is not cap-to-cap), R013
//! (`CapMint` whose destination is not a cap of the minted type).
//!
//! Only after structural success does the sole Z3-backed flow prover run
//! (`air_capability_v2::verify_air_capabilities`, `solver` feature); any
//! diagnostic from either half fails the compile -- fail closed.
//!
//! This file owns the `solver_verified` cert witness (ET-M3): THE single,
//! false-biased assignment site. A solver-off build runs the structural
//! checks only and reports `solver_verified: false` -- the witness must
//! never over-claim, and any future bypass must set it false. The one-site
//! rule is grep-pinned by `tests/z3_guard_fences.rs`
//! (`solver_verified_has_exactly_one_assignment_site`).

use crate::{
    air::{AirFunction, AirProgram, AirStmt, AirValue, AirValueKind},
    diagnostics::{Diagnostic, codes},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CapabilityReport {
    pub verified_functions: usize,
    pub checked_blocks: usize,
    pub checked_sites: usize,
    /// Total Z3 `rlimit count` consumed by the sole prover's discharge
    /// (`air_capability_v2::verify_air_capabilities`) for this program, when
    /// the `solver` feature is enabled and the statistics key is exposed by
    /// the Z3 version in use. `None` when the solver feature is off or the
    /// key is unavailable. Used by step 7's per-program budget invariant:
    /// total consumption must stay below `AIR_CAP_Z3_PROGRAM_RLIMIT`
    /// (air_capability_v2/mod.rs).
    pub z3_rlimit_consumed: Option<u64>,
    /// Z3 cap-query cache: hits during this verification run (axis-2
    /// eighth touch). Process-wide cumulative since cache init; not part
    /// of cert byte-equality (mirrors `z3_rlimit_consumed`'s exclusion in
    /// `diff_certificates`, sigil-cli/src/cert_gate.rs).
    /// 0 when the `solver` feature is off.
    pub z3_cache_hits: u64,
    /// Z3 cap-query cache: misses (fresh Z3 calls) during this run.
    /// Mirrors `z3_cache_hits`. 0 when the `solver` feature is off.
    pub z3_cache_misses: u64,
    /// Whether the Z3-backed verification actually ran for this artifact.
    ///
    /// **Contract (load-bearing):** `true` ONLY IF the `solver` feature is
    /// compiled in AND the Z3-routing verification entry points executed
    /// for this program. A solver-OFF build runs the STRUCTURAL checks
    /// only (C001 forgery, linearity, exclusivity, taint) and leaves the
    /// flow-sensitive Z3 proofs (cap-flow, refinement discharge)
    /// undischarged — so `solver_verified` is `false` and the cert/CLI
    /// say so. Any FUTURE bypass, kill-switch, or partial discharge MUST
    /// set this `false`; the witness must never over-claim.
    ///
    /// UNLIKE `z3_rlimit_consumed` / `z3_cache_*` (which vary per run and
    /// are excluded from cert byte-equality), this field is DETERMINISTIC
    /// per build configuration and is INCLUDED in byte-equality: the same
    /// source built solver-on vs solver-off yields DIFFERENT certs.
    pub solver_verified: bool,
}

pub fn verify(
    program: &AirProgram,
    #[allow(unused_variables)] registry: &crate::type_check::AuthorityRegistry,
) -> Result<CapabilityReport, Vec<Diagnostic>> {
    let checked_blocks = program
        .functions
        .iter()
        .map(|function| function.blocks.len())
        .sum();
    let mut checked_sites = 0usize;
    let mut diagnostics = Vec::new();

    for function in &program.functions {
        checked_sites += verify_function(function, &mut diagnostics);
    }

    // Fast early-out: if structural checks fail, return immediately
    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }

    // Structural success is followed by the sole Z3-backed flow verifier.
    // Any diagnostic propagates as a compile failure.
    //
    // The verifier deliberately bypasses verdict caching, so cache counters are
    // zero. These operational fields are excluded from certificate byte equality.
    #[cfg(feature = "solver")]
    let (z3_rlimit_consumed, z3_cache_hits, z3_cache_misses) =
        match crate::air_capability_v2::verify_air_capabilities(program, registry) {
            Ok(v2) => {
                checked_sites += v2.checked_sites;
                (v2.z3_rlimit_consumed, 0u64, 0u64)
            }
            Err(solver_diagnostics) => {
                return Err(solver_diagnostics);
            }
        };

    // When the solver feature is off, these fields are inert: no Z3
    // calls happen, no cache lookups, no rlimit to report.
    #[cfg(not(feature = "solver"))]
    let (z3_rlimit_consumed, z3_cache_hits, z3_cache_misses): (Option<u64>, u64, u64) =
        (None, 0, 0);

    // ET-M3: THE single, false-biased assignment of the solver-verification
    // witness. `cfg!(feature = "solver")` is the v1 implementation: in this
    // function, "solver compiled in" and "the Z3 prover ran for this
    // artifact" are equivalent (under the feature the v2 prover above runs
    // unconditionally, and we reach here only on its `Ok`). The CONTRACT on
    // `CapabilityReport::solver_verified` — not this `cfg!` — is what future
    // code is held to: any bypass MUST set it false. Grep-pinned to exactly
    // one assignment site by tests/z3_guard_fences.rs.
    let solver_verified = cfg!(feature = "solver");

    Ok(CapabilityReport {
        verified_functions: program.functions.len(),
        checked_blocks,
        checked_sites,
        z3_rlimit_consumed,
        z3_cache_hits,
        z3_cache_misses,
        solver_verified,
    })
}

fn verify_function(function: &AirFunction, diagnostics: &mut Vec<Diagnostic>) -> usize {
    let mut checked_sites = 0usize;

    for block in &function.blocks {
        for stmt in &block.stmts {
            match stmt {
                AirStmt::Assign {
                    dst,
                    val: AirValue::RecordConstruct { .. },
                } => {
                    checked_sites += 1;
                    if function.var_kind(*dst).is_cap() {
                        diagnostics.push(Diagnostic::error(
                            codes::C001,
                            format!(
                                "capability verifier rejected forged capability value `{}` in `{}`",
                                function.var_label(*dst),
                                function.name
                            ),
                            function.var_span(*dst),
                        ));
                    }
                }
                AirStmt::SpawnActor { caps, fuel_cap, .. } => {
                    checked_sites += 1;

                    for cap in caps {
                        let kind = function.var_kind(*cap);
                        // Wall 1 Step 3: accept `Slot<Cap>` spawn args alongside
                        // raw caps. Slots are i32 heap pointers at the wasm
                        // boundary; the actor's init receives them as ordinary
                        // values. The cap-inside-slot tracking is handled by
                        // SlotPut/SlotTake's Z3 source rule.
                        if !kind.is_cap() && !kind.is_slot() {
                            diagnostics.push(Diagnostic::error(
                                codes::R010,
                                format!(
                                    "capability verifier rejected non-cap, non-slot spawn argument `{}` in `{}`",
                                    function.var_label(*cap),
                                    function.name
                                ),
                                None,
                            ));
                        }
                    }

                    if !function.var_kind(*fuel_cap).is_cap() {
                        diagnostics.push(Diagnostic::error(
                            codes::R011,
                            format!(
                                "capability verifier rejected non-cap fuel argument `{}` in `{}`",
                                function.var_label(*fuel_cap),
                                function.name
                            ),
                            None,
                        ));
                    }
                }
                AirStmt::CapRestrict { dst, src, .. }
                | AirStmt::CapSplit { dst, src, .. }
                | AirStmt::CapDraw { dst, src, .. } => {
                    checked_sites += 1;
                    if !function.var_kind(*src).is_cap() || !function.var_kind(*dst).is_cap() {
                        diagnostics.push(Diagnostic::error(
                            codes::R012,
                            format!(
                                "capability verifier expected cap-to-cap attenuation in `{}`",
                                function.name
                            ),
                            None,
                        ));
                    }
                }
                // Capabilities-as-values: assert the mint invariant (R013) —
                // `CapMint`'s `dst` must be a cap of exactly the minted type.
                // Asserting it (rather than accepting by omission) pins that
                // mint produces a real cap; C001 already cannot fire here
                // because `CapMint` is structurally not a `RecordConstruct`.
                AirStmt::CapMint { dst, cap_name, .. } => {
                    checked_sites += 1;
                    let matches = matches!(
                        function.var_kind(*dst),
                        AirValueKind::Cap(ref n) if n == cap_name
                    );
                    if !matches {
                        diagnostics.push(Diagnostic::error(
                            codes::R013,
                            format!(
                                "capability verifier rejected mint of `{}` to non-matching destination `{}` in `{}`",
                                cap_name,
                                function.var_label(*dst),
                                function.name
                            ),
                            function.var_span(*dst),
                        ));
                    }
                }
                _ => {}
            }
        }
    }

    checked_sites
}

#[cfg(test)]
mod tests {
    use super::verify;
    use crate::air::{
        ActorTypeId, AirBlock, AirFunction, AirFunctionKind, AirProgram, AirStmt,
        AirSupervisionStrategy, AirTerminator, AirType, AirValue, AirValueKind, BlockId, VarId,
    };
    use crate::ast::Ring;

    #[test]
    fn rejects_forged_capability_records() {
        let program = AirProgram {
            functions: vec![AirFunction {
                name: "sigil::forgery".to_owned(),
                export_name: "sigil__forgery".to_owned(),
                ring: Ring::default(),
                kind: AirFunctionKind::ModuleFunction,
                params: Vec::new(),
                ret: AirType::Unit,
                locals: vec![(VarId(0), AirType::Ptr)],
                value_kinds: [(VarId(0), AirValueKind::Cap("Fuel".to_owned()))]
                    .into_iter()
                    .collect(),
                debug_names: [(VarId(0), "fuel".to_owned())].into_iter().collect(),
                blocks: vec![AirBlock {
                    id: BlockId(0),
                    stmts: vec![AirStmt::Assign {
                        dst: VarId(0),
                        val: AirValue::RecordConstruct { fields: Vec::new() },
                    }],
                    terminator: AirTerminator::Return(None),
                }],
                entry_block: BlockId(0),
                def_span: Default::default(),
                debug_spans: Default::default(),
                block_static_multiplicity: Vec::new(),
                security: Default::default(),
            }],
        };

        let err = verify(&program, &crate::type_check::AuthorityRegistry::default())
            .expect_err("forged caps should be rejected");
        assert_eq!(
            err[0].message(),
            "capability verifier rejected forged capability value `fuel` in `sigil::forgery`"
        );
    }

    #[test]
    fn rejects_non_cap_spawn_arguments() {
        let program = AirProgram {
            functions: vec![AirFunction {
                name: "sigil::spawn".to_owned(),
                export_name: "sigil__spawn".to_owned(),
                ring: Ring::default(),
                kind: AirFunctionKind::ModuleFunction,
                params: vec![(VarId(0), AirType::Ptr), (VarId(1), AirType::Ptr)],
                ret: AirType::Unit,
                locals: vec![(VarId(2), AirType::Ptr)],
                value_kinds: [
                    (VarId(0), AirValueKind::Copy),
                    (VarId(1), AirValueKind::Cap("Fuel".to_owned())),
                    (VarId(2), AirValueKind::Copy),
                ]
                .into_iter()
                .collect(),
                debug_names: [
                    (VarId(0), "seed".to_owned()),
                    (VarId(1), "fuel".to_owned()),
                    (VarId(2), "child".to_owned()),
                ]
                .into_iter()
                .collect(),
                blocks: vec![AirBlock {
                    id: BlockId(0),
                    stmts: vec![AirStmt::SpawnActor {
                        dst: VarId(2),
                        actor_type: ActorTypeId(1),
                        caps: vec![VarId(0)],
                        fuel_cap: VarId(1),
                        supervision: AirSupervisionStrategy::Stop,
                    }],
                    terminator: AirTerminator::Return(None),
                }],
                entry_block: BlockId(0),
                def_span: Default::default(),
                debug_spans: Default::default(),
                block_static_multiplicity: Vec::new(),
                security: Default::default(),
            }],
        };

        let err = verify(&program, &crate::type_check::AuthorityRegistry::default())
            .expect_err("non-cap spawn args should be rejected");
        assert_eq!(
            err[0].message(),
            "capability verifier rejected non-cap, non-slot spawn argument `seed` in `sigil::spawn`"
        );
    }
}
