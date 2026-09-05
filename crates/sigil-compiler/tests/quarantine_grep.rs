//! Pure-collector I/O confinement gate.
//!
//! Two Pure Pipelines must NEVER import the Z3 backend:
//!
//! * `type_check_v2`: `refinement.rs`,
//!   `obligations.rs`. The orchestrator `type_check_v2/mod.rs` is the
//!   ONLY Z3-touching file.
//! * `air_capability_v2`: `collector.rs`, `obligations.rs`. The orchestrator
//!   `air_capability_v2/mod.rs` is the ONLY Z3-touching file.
//!
//! This test reads each Pure-Pipeline file, strips line comments
//! (everything from `//` to end of line), and asserts none of the
//! remaining code contains the forbidden import substrings. Comments
//! mentioning the forbidden paths in prose (e.g., to document the
//! confinement rule itself) are allowed.
//!
//! `air_capability_v2/collector.rs` carries an ADDITIONAL set of
//! forbidden substrings (NC1 / CM1 — quarantine contract IDs, anchored in
//! docs/specs/v2-unification-decision.md §5): a transitive Z3 leak via a
//! `DischargeContext` / `Solver` / `Context` type parameter would slip
//! past the `use`-based scan, so the collector is also scanned for those
//! type-name substrings in code positions.
//!
//! When this test fails, the message tells you which file imported what.
//! The fix is to move the import to the orchestrator `mod.rs` and have
//! the Pure file return an obligation that the orchestrator dispatches.

use std::fs;

const PURE_FILES: &[&str] = &[
    // Pure refinement collection.
    "src/type_check_v2/refinement.rs",
    "src/type_check_v2/obligations.rs",
    // Pure AIR-capability collection.
    "src/air_capability_v2/collector.rs",
    "src/air_capability_v2/obligations.rs",
];

const FORBIDDEN_IMPORTS: &[&str] = &[
    "use z3",
    "use crate::z3_capability",
    "use crate::z3_cache",
    "crate::z3_capability::",
    "crate::z3_cache::",
];

/// Files subject to the NC1 / CM1 type-level firewall: beyond the
/// `use`-based forbidden-import scan, these must not name any Z3 solver
/// type even transitively (e.g. as a fn parameter type), because such a
/// parameter would let Z3 leak into the Pure collector without an
/// `import` line for the basic scan to catch.
const TYPE_FIREWALL_FILES: &[&str] = &["src/air_capability_v2/collector.rs"];

/// Substrings forbidden in `TYPE_FIREWALL_FILES` code (NC1 / CM1).
/// `Solver` and `Context` cover the z3 solver/context types in any path
/// form; `DischargeContext` is the orchestrator's shared-state struct
/// that owns a Solver — the collector must never accept it.
const FORBIDDEN_TYPE_NAMES: &[&str] = &["Solver", "z3::Context", "DischargeContext"];

/// Strip line comments from a single source line. Treats `//` as the
/// comment start regardless of position. Does NOT understand string
/// literals — a `"//"` substring inside a string is treated as a comment
/// start. Acceptable for this grep gate because the forbidden import
/// substrings are not the kind of thing a programmer would put inside a
/// string literal in the Pure files.
fn strip_line_comment(line: &str) -> &str {
    match line.find("//") {
        Some(idx) => &line[..idx],
        None => line,
    }
}

#[test]
fn pure_pipeline_files_have_no_z3_imports() {
    let crate_root = env!("CARGO_MANIFEST_DIR");
    for file in PURE_FILES {
        let path = format!("{crate_root}/{file}");
        let source =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("failed to read {path}: {e}"));
        for (lineno, line) in source.lines().enumerate() {
            let code = strip_line_comment(line);
            for forbidden in FORBIDDEN_IMPORTS {
                assert!(
                    !code.contains(forbidden),
                    "I/O Quarantine breach in {file}:{}: line contains forbidden substring `{forbidden}` outside of a comment: `{}`. \
                     Move the Z3 interaction to the orchestrator mod.rs and have \
                     this file return a typed obligation for the orchestrator to dispatch.",
                    lineno + 1,
                    code.trim(),
                );
            }
        }
    }
}

/// NC1 / CM1: the AIR-cap collector must not name a Z3 solver type even
/// transitively. A `DischargeContext` / `Solver` / `Context` parameter
/// would let Z3 reach the Pure collector without a `use` line, slipping
/// past `pure_pipeline_files_have_no_z3_imports`. This scan catches the
/// type name in any code position.
#[test]
fn air_cap_collector_has_no_z3_type_leak() {
    let crate_root = env!("CARGO_MANIFEST_DIR");
    for file in TYPE_FIREWALL_FILES {
        let path = format!("{crate_root}/{file}");
        let source =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("failed to read {path}: {e}"));
        for (lineno, line) in source.lines().enumerate() {
            let code = strip_line_comment(line);
            for forbidden in FORBIDDEN_TYPE_NAMES {
                assert!(
                    !code.contains(forbidden),
                    "NC1 type-level Quarantine breach in {file}:{}: code names forbidden Z3 type `{forbidden}`: `{}`. \
                     The Pure collector must take ONLY &AirProgram + &AuthorityRegistry. \
                     Move any solver-state dependency to air_capability_v2/mod.rs (the orchestrator).",
                    lineno + 1,
                    code.trim(),
                );
            }
        }
    }
}
