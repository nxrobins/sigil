//! λ-SIGIL M7 — differential cross-check, **C003 solver-lane half** (harden-spec C2).
//!
//! The four C003 fixtures (Call / Spawn / Send / Return sinks) are the `.sigil` counterparts of the
//! λ-SIGIL `lsd_c003_reject` / `lsd_c003_stuck` obligations in `proofs/lean/LambdaSigil/Differential.lean`.
//! Q3 = mirror all four sinks; the check is sink-uniform (`sinkOk req k = req ⊆ k`), so the single
//! wired λ-SIGIL `sink` rule models all four — each fixture below maps to the same obligation pair.
//!
//! C003 is a Z3 (solver) diagnostic, so this file is gated `#![cfg(feature = "solver")]` and runs ONLY
//! in the `solver` CI lane (`cargo test -p sigil-compiler --features solver`); it contributes 0 tests
//! to the workspace `--no-default-features` `rust` lane (harden-spec C2).  It drives
//! parse → resolve → type-check → AIR lowering and runs the sole prover
//! `air_capability_v2::verify_air_capabilities` directly, asserting EXACTLY `{C003}` per sink
//! (mirroring the validated `air_cap_rejection_soundness.rs` pattern).

#![cfg(feature = "solver")]

use std::fs;
use std::path::PathBuf;

use sigil_compiler::diagnostics::{Diagnostic, Severity};
use sigil_compiler::source::SourceFile;
use sigil_compiler::{CompileOptions, air, air_capability_v2, name_resolution, parser, type_check};

/// (shared LSD id, fixture path) — one per C003 surface sink.  All map to the λ-SIGIL `lsd_c003_*`
/// obligations (the sink rule is sink-uniform).
const C003_SINKS: &[(&str, &str)] = &[
    (
        "LSD-C003-call",
        "tests/z3_corpus/01_attenuation_at_call.sigil",
    ),
    (
        "LSD-C003-spawn",
        "tests/z3_corpus/02_attenuation_at_spawn.sigil",
    ),
    (
        "LSD-C003-send",
        "tests/z3_corpus/03_attenuation_at_send.sigil",
    ),
    (
        "LSD-C003-return",
        "tests/z3_corpus/07_attenuation_at_return.sigil",
    ),
];

/// Sorted, deduplicated capability C-codes among error diagnostics.
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

#[test]
fn c003_all_four_sinks_reject() {
    let crate_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (id, rel) in C003_SINKS {
        let path = crate_root.join(rel);
        let src = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{id}: read {path:?}: {e}"));

        let source = SourceFile::new(*rel, &src);
        let (ast, pdiags) = parser::parse(&source);
        assert!(
            !pdiags.iter().any(|d| d.severity() == Severity::Error),
            "{id}: fixture must parse cleanly"
        );
        let resolved = name_resolution::resolve(&ast)
            .unwrap_or_else(|_| panic!("{id}: name resolution failed"));
        let (typed, registry) =
            type_check::check_with_options(&resolved, &CompileOptions::default())
                .unwrap_or_else(|_| panic!("{id}: type-check failed"));
        let air = air::lower(&typed);

        let codes = match air_capability_v2::verify_air_capabilities(&air, &registry) {
            Ok(_) => Vec::new(),
            Err(diags) => cap_codes(&diags),
        };
        assert_eq!(
            codes,
            vec!["C003".to_string()],
            "{id}: expected exactly C003"
        );
    }
}
