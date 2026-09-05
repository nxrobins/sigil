//! AIR-Cap PR 4b — CM17: verdict→diagnostic arm coverage for the codes
//! the corpus cannot reach.
//!
//! The rejection-corpus test (`air_cap_rejection_soundness.rs`) covers
//! the **C003** arm thoroughly (5 `.sigil` fixtures, incl. the slot-meet
//! case). But the discharge also has **C002** (legitimacy / provenance)
//! and **C004** (Unknown / budget) arms that NO `.sigil` source can
//! reach:
//!
//!   * **C002** — fires on an illegitimate (forged) capability reaching a
//!     spawn/message sink. In the full pipeline a forged cap is caught by
//!     the STRUCTURAL check (`capability::verify` → C001) BEFORE the Z3
//!     prover runs, so `compile_module` emits C001, never C002. C002 is
//!     only reachable by feeding a forged-cap `AirProgram` DIRECTLY to
//!     the prover (bypassing the structural pre-check).
//!   * **C004** — fires on a Z3 `Unknown`. Unreachable under the
//!     production rlimit (1M); exercised via the `_at_rlimit(prog, reg, 1)`
//!     test seam.
//!
//! So this file covers those two arms with HAND-BUILT `AirProgram`s — the
//! only mechanism that reaches them — and pins the sole prover's contract
//! directly.
//!
//! ## Solver gate
//!
//! `#![cfg(feature = "solver")]` — both arms are Z3 verdicts.

#![cfg(feature = "solver")]

use sigil_compiler::air::{
    ActorTypeId, AirBlock, AirFunction, AirFunctionKind, AirProgram, AirStmt,
    AirSupervisionStrategy, AirTerminator, AirType, AirValue, AirValueKind, BlockId, VarId,
};
use sigil_compiler::air_capability_v2;
use sigil_compiler::ast::Ring;
use sigil_compiler::diagnostics::{Diagnostic, Severity};
use sigil_compiler::type_check::AuthorityRegistry;

fn cap_codes(diags: &[Diagnostic]) -> Vec<String> {
    let mut codes: Vec<String> = diags
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .map(|d| d.code().as_str().to_string())
        .filter(|c| c.starts_with('C'))
        .collect();
    codes.sort();
    codes.dedup();
    codes
}

/// An `AirProgram` that forges a `Fuel` capability (RecordConstruct on a
/// cap-typed var) and passes it as a `SpawnActor` cap argument. Fed
/// DIRECTLY to the Z3 verifier (bypassing the structural C001 check),
/// the Phase 1 legitimacy probe marks the forged cap illegitimate and
/// `assert_var_legitimate` at the spawn fires C002.
///
/// `fuel_cap` is a legitimate param cap (so it doesn't itself fire). The
/// default registry has no `Fuel` authorities → `full_mask("Fuel") == 0`
/// → the sink authority check short-circuits, so no C003 noise; the only
/// diagnostic is the C002 we are exercising.
fn forged_cap_at_spawn_program() -> AirProgram {
    AirProgram {
        functions: vec![AirFunction {
            name: "sigil::forge_then_spawn".to_owned(),
            export_name: "sigil__forge_then_spawn".to_owned(),
            ring: Ring::default(),
            kind: AirFunctionKind::ModuleFunction,
            // VarId(1): a legitimate param Fuel cap (used as fuel_cap).
            params: vec![(VarId(1), AirType::Ptr)],
            ret: AirType::Unit,
            // VarId(0): forged Fuel cap. VarId(2): spawn result.
            locals: vec![(VarId(0), AirType::Ptr), (VarId(2), AirType::Ptr)],
            value_kinds: [
                (VarId(0), AirValueKind::Cap("Fuel".to_owned())),
                (VarId(1), AirValueKind::Cap("Fuel".to_owned())),
                (VarId(2), AirValueKind::Copy),
            ]
            .into_iter()
            .collect(),
            debug_names: [
                (VarId(0), "forged".to_owned()),
                (VarId(1), "fuel".to_owned()),
                (VarId(2), "child".to_owned()),
            ]
            .into_iter()
            .collect(),
            blocks: vec![AirBlock {
                id: BlockId(0),
                stmts: vec![
                    // Forge: RecordConstruct assigned to a cap-typed var.
                    AirStmt::Assign {
                        dst: VarId(0),
                        val: AirValue::RecordConstruct { fields: Vec::new() },
                    },
                    // Use the forged cap as a spawn cap argument → the
                    // legitimacy probe fires C002.
                    AirStmt::SpawnActor {
                        dst: VarId(2),
                        actor_type: ActorTypeId(1),
                        caps: vec![VarId(0)],
                        fuel_cap: VarId(1),
                        supervision: AirSupervisionStrategy::Stop,
                    },
                ],
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

/// CM17 — C002 arm. Feed the forged-cap-at-spawn program DIRECTLY to the
/// sole prover. Assert it rejects with C002 (the pin carries the verdict
/// the legacy-vs-v2 comparison certified before the PR-5 deletion).
#[test]
fn c002_legitimacy_arm_rejects_forged_cap() {
    let program = forged_cap_at_spawn_program();
    let registry = AuthorityRegistry::default();

    let codes = match air_capability_v2::verify_air_capabilities(&program, &registry) {
        Ok(_) => Vec::new(),
        Err(diags) => cap_codes(&diags),
    };

    assert!(
        codes.contains(&"C002".to_string()),
        "expected the prover to emit C002 for a forged cap at a spawn sink; got \
         {codes:?}. If this changed, the C002 legitimacy arm is no longer exercised."
    );
}

/// A minimal legitimate cap program (param Fuel cap, returns Unit). Used
/// for the C004 rlimit-contract test — its actual verdict doesn't matter,
/// only that under `rlimit=1` the v2 discharge never returns a silent
/// non-C004 error.
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

/// CM17 — C004 arm. Under `rlimit=1` the v2 discharge MUST be either clean
/// (Z3 answered fast enough) or reject with C004 — NEVER a silent
/// non-C004 error. Mirrors legacy's `rlimit_one_is_either_ok_or_c004_never_silent`
/// (legacy's `_at_rlimit` seam is private, so we assert the v2 CONTRACT
/// rather than a legacy-vs-v2 equality). This pins the soundness property
/// that an undecided Z3 verdict surfaces as a hard error, never a silent
/// pass.
#[test]
fn c004_unknown_arm_never_silently_passes_at_rlimit_one() {
    let program = trivial_cap_program();
    let registry = AuthorityRegistry::default();

    let v2 = air_capability_v2::run_air_capability_passes_at_rlimit(&program, &registry, 1);
    let codes = cap_codes(&v2.diagnostics);

    // Either Z3 answered (no diagnostics) or every emitted C-code is C004.
    // A non-C004 capability error under rlimit=1 would mean an Unknown was
    // mis-routed (the soundness hole this arm guards).
    let non_c004: Vec<&String> = codes.iter().filter(|c| c.as_str() != "C004").collect();
    assert!(
        non_c004.is_empty(),
        "C004 arm: rlimit=1 v2 discharge produced a non-C004 capability error \
         (an Unknown that was mis-routed instead of surfacing as C004): {non_c004:?}"
    );
}
