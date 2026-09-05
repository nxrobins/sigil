//! Harden E1 (capabilities-as-values): structural guard against the fail-open
//! forgery hole.
//!
//! The Z3 cap oracle's `assert_var_legitimate` is a NO-OP when a cap variable
//! has no legitimacy entry (`find_legitimacy` returns `None`) — so a cap source
//! that is NOT seeded in the Phase-1 legitimacy walk is trusted by OMISSION.
//! `mint` adds a new cap source (`AirStmt::CapMint`); if its legitimacy arm were
//! ever dropped, an ungated mint reaching AIR would be silently accepted.
//!
//! This test pins every cap-ORIGINATING `AirStmt` variant into the Phase-1
//! legitimacy region of `air_capability_v2/mod.rs`. Adding a new cap source
//! without a legitimacy arm fails here, loudly, before it can become a hole.

/// The verifier source, embedded at compile time (path relative to this file).
const VERIFIER_SRC: &str = include_str!("../src/air_capability_v2/mod.rs");

/// Cap-originating statements: each produces / originates a cap-typed `dst`
/// whose legitimacy the oracle must establish. Keep in sync with `AirStmt` and
/// `classify_value_kind`.
const CAP_ORIGINATING_STMTS: &[&str] = &[
    "CapRestrict",
    "CapSplit",
    "CapDraw",
    "CapMint",
    "SpawnActor",
];

/// Extract the Phase-1 legitimacy region (`// Phase 1: legitimacy …` up to
/// `// Phase 2: authority …`). Fails if the anchors move, forcing this guard to
/// be re-pinned alongside any refactor of the phase structure.
fn phase_one_region(src: &str) -> &str {
    let start = src
        .find("// Phase 1: legitimacy")
        .expect("Phase 1 anchor missing — re-pin the legitimacy-guard test");
    let end = src
        .find("// Phase 2: authority")
        .expect("Phase 2 anchor missing — re-pin the legitimacy-guard test");
    assert!(start < end, "phase anchors out of order");
    &src[start..end]
}

#[test]
fn every_cap_originating_stmt_is_legitimacy_seeded() {
    let region = phase_one_region(VERIFIER_SRC);
    for stmt in CAP_ORIGINATING_STMTS {
        let needle = format!("AirStmt::{stmt}");
        assert!(
            region.contains(&needle),
            "`AirStmt::{stmt}` is a cap-originating statement but has NO arm in the \
             Phase-1 legitimacy walk of air_capability_v2 — a missing legitimacy arm \
             makes the cap fail-OPEN (trusted by omission), the forgery hole harden E1 \
             forbids. Add a legitimacy arm that asserts (or refutes) its `dst`."
        );
    }
}
