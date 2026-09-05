//! λ-SIGIL M7 — differential cross-check, **Rust half** (rust lane, no solver).
//!
//! Each fixture is the `.sigil` counterpart of a λ-SIGIL obligation in
//! `proofs/lean/LambdaSigil/Differential.lean`; the shared `LSD-…` id ties the two halves.
//! This half asserts that `sigil_check` (via `compile_module`, the full pipeline — so the
//! AIR-level ownership pass that emits O001 actually runs, per harden-spec C1) gives the expected
//! verdict: a reject fixture emits exactly its headline code, an accept sibling emits none.
//!
//! Verdict is read on the **in-scope code surface** {O001,E001,T272,T273} with `assert_eq!`
//! (NOT `contains`), so a wrong-family headline code (e.g. a stray T272 in an O001 fixture) breaks
//! the test (harden-spec C3).  The four C003 sinks are solver-gated and live in
//! `crates/sigil-compiler/tests/lambda_sigil_c003.rs` (harden-spec C2) — absent here by design.
//!
//! **C001 (cap forgery)** is *by construction* on both sides and has no source-level coded fixture:
//! a record-literal coerced to a cap type is rejected by the SIGIL **front end** (parse/type errors),
//! so the AIR-level `capability.rs` C001 backstop is unreachable from surface source (it is exercised
//! by hand-built AIR in `air_cap_arm_coverage.rs`).  λ-SIGIL has no cap-forging `Term` at all.  The
//! `cap_forgery_rejected_by_frontend` test witnesses this correspondence (forgery rejected; legit
//! pass-through carries no capability violation).
//!
//! There is no machine Lean-to-Rust bridge; the correspondence is a reviewed classification of
//! shared and intentionally one-sided ids, checked by `lean_obligation_ids_are_pinned`.

use sigil_compiler::compile_module;

/// The headline ownership/effect/mint codes the coded fixtures range over.  Codes outside this set
/// (parse/resolve artifacts, missing-entry, etc.) are filtered out — the verdict is "does this
/// trigger one of the headline violations?".  C001 is excluded (front-end-rejected; see module doc).
const IN_SCOPE: &[&str] = &["O001", "E001", "T272", "T273"];

/// `sigil_check` verdict on the in-scope code surface: empty = accepted (no headline violation).
fn in_scope_codes(src: &str) -> Vec<String> {
    let mut v: Vec<String> = match compile_module(src) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .filter(|c| IN_SCOPE.contains(&c.as_str()))
            .collect(),
    };
    v.sort();
    v.dedup();
    v
}

struct Fixture {
    /// shared id with the λ-SIGIL obligation in Differential.lean
    id: &'static str,
    /// expected in-scope code set (`&[]` = accept)
    expect: &'static [&'static str],
    src: &'static str,
}

// ── O001: use-after-move (affine ownership) ─────────────────────────────────────────────────
// λ-SIGIL: lsd_o001_reject (cap reused; 2nd var_lin fails).  SIGIL O001 governs all linear values;
// this fixture exercises the typestate-marker sub-case (cf. Differential.lean's C9 scope note that
// the λ-SIGIL obligation models the capability sub-case — both are the same affine discipline).
const O001_REJECT: &str = "\
module tool;
state Grant { Active, Revoked }
record Grant<@S> { id: i64 }
fn delegate() -> Grant<Active> { return Grant { id: 1 }; }
fn revoke(g: Grant<Active>) -> Grant<Revoked> { return Grant { id: 0 }; }
fn access(g: Grant<Active>) -> i64 { return g.id; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let g: Grant<Active> = delegate();
    let r: Grant<Revoked> = revoke(g);
    let x: i64 = access(g);
    return x;
}
";
const O001_ACCEPT: &str = "\
module tool;
state Grant { Active, Revoked }
record Grant<@S> { id: i64 }
fn delegate() -> Grant<Active> { return Grant { id: 1 }; }
fn revoke(g: Grant<Active>) -> Grant<Revoked> { return Grant { id: 0 }; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let g: Grant<Active> = delegate();
    let r: Grant<Revoked> = revoke(g);
    return r.id;
}
";

// ── E001: undeclared effect (callee row ⊄ caller row) ───────────────────────────────────────
// λ-SIGIL: mechanism gap — row synthesis + effect_safety (Differential.lean note).  The accept
// drops `effect NetIO;`, so NetIO is unregistered and the row drops to empty (no leak).
const E001_REJECT: &str = "\
#[ring(outer)]
module m;
effect NetIO;
fn expensive() -> i64 ! { NetIO } { return 0; }
fn boot() -> i64 ! {} { return expensive(); }
";
const E001_ACCEPT: &str = "\
#[ring(outer)]
module m;
fn expensive() -> i64 ! { NetIO } { return 0; }
fn boot() -> i64 ! {} { return expensive(); }
";

// ── T272 / T273: mint policy + authority gate ───────────────────────────────────────────────
// λ-SIGIL: lsd_t273_reject models the &Admin TYPE gate; T272's mintable_by layer is out of model.
// T273 reject: mint a mintable cap WITHOUT the &Admin authority.  T272 reject: mint a cap that is
// not `mintable_by` anything.  Accept (LSD-ACC-mint): mint the mintable cap WITH &Admin in scope.
const T273_REJECT: &str = "\
module sigil;
cap type Admin { mint_file }
cap type FileAccess mintable_by Admin { read, write }
record File { id: i64 }
fn make(f: File) -> FileAccess { return mint FileAccess for f; }
";
const T273_ACCEPT: &str = "\
module sigil;
cap type Admin { mint_file }
cap type FileAccess mintable_by Admin { read, write }
record File { id: i64 }
fn make(f: File, admin: &Admin) -> FileAccess { return mint FileAccess for f; }
";
const T272_REJECT: &str = "\
module sigil;
cap type Admin { mint_file }
cap type FileAccess mintable_by Admin { read, write }
record File { id: i64 }
fn bad(f: File) -> Admin { return mint Admin for f; }
";

const FIXTURES: &[Fixture] = &[
    // rejects
    Fixture {
        id: "LSD-O001",
        expect: &["O001"],
        src: O001_REJECT,
    },
    Fixture {
        id: "LSD-E001",
        expect: &["E001"],
        src: E001_REJECT,
    },
    Fixture {
        id: "LSD-T273",
        expect: &["T273"],
        src: T273_REJECT,
    },
    Fixture {
        id: "LSD-T272",
        expect: &["T272"],
        src: T272_REJECT,
    },
    // accept siblings (1 mutation away — proves each reject is load-bearing, harden-spec C3)
    Fixture {
        id: "LSD-ACC-O001",
        expect: &[],
        src: O001_ACCEPT,
    },
    Fixture {
        id: "LSD-ACC-E001",
        expect: &[],
        src: E001_ACCEPT,
    },
    Fixture {
        id: "LSD-ACC-mint",
        expect: &[],
        src: T273_ACCEPT,
    },
];

/// The coded-fixture id set the rust-lane half covers (C003 ids are solver-lane; C001 is the
/// forgery-rejected witness below). Keep in lockstep with `FIXTURES`; cross-language differences
/// are classified explicitly in `CORRESPONDENCE` below.
const EXPECTED_IDS: &[&str] = &[
    "LSD-O001",
    "LSD-E001",
    "LSD-T273",
    "LSD-T272",
    "LSD-ACC-O001",
    "LSD-ACC-E001",
    "LSD-ACC-mint",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CorrespondenceLocation {
    Shared,
    RustOnly,
    LeanOnly,
}

/// Explicit classification of the measured Rust/Lean ID union. A count-only pin detected that the
/// sets differed but left every difference unexplained. Each row now states whether the ID is
/// literally shared or intentionally belongs to one side, and why.
const CORRESPONDENCE: &[(&str, CorrespondenceLocation, &str)] = &[
    (
        "LSD-O001",
        CorrespondenceLocation::Shared,
        "capability reuse is rejected by Rust ownership and Lean affine typing",
    ),
    (
        "LSD-T273",
        CorrespondenceLocation::Shared,
        "both sides model the mint-authority type gate",
    ),
    (
        "LSD-ACC-mint",
        CorrespondenceLocation::Shared,
        "both sides admit minting with authority",
    ),
    (
        "LSD-E001",
        CorrespondenceLocation::RustOnly,
        "Lean synthesizes effect rows and has no source annotation-mismatch verdict",
    ),
    (
        "LSD-T272",
        CorrespondenceLocation::RustOnly,
        "Lean has no mintable_by policy layer",
    ),
    (
        "LSD-ACC-O001",
        CorrespondenceLocation::RustOnly,
        "Rust accept twin; Lean's analogous single-use witness is LSD-ACC-once",
    ),
    (
        "LSD-ACC-E001",
        CorrespondenceLocation::RustOnly,
        "Rust annotation-check accept twin for the Lean effect-row mechanism gap",
    ),
    (
        "LSD-C003",
        CorrespondenceLocation::LeanOnly,
        "one Lean sink obligation maps to four solver-lane Rust fixtures",
    ),
    (
        "LSD-C003-call",
        CorrespondenceLocation::Shared,
        "Lean table shorthand and the first solver-lane sink fixture",
    ),
    (
        "LSD-C003-spawn",
        CorrespondenceLocation::RustOnly,
        "solver-lane spawn fixture maps to Lean's sink-uniform LSD-C003 obligation",
    ),
    (
        "LSD-C003-send",
        CorrespondenceLocation::RustOnly,
        "solver-lane send fixture maps to Lean's sink-uniform LSD-C003 obligation",
    ),
    (
        "LSD-C003-return",
        CorrespondenceLocation::RustOnly,
        "solver-lane return fixture maps to Lean's sink-uniform LSD-C003 obligation",
    ),
    (
        "LSD-ACC-once",
        CorrespondenceLocation::LeanOnly,
        "Lean's direct affine single-use witness",
    ),
    (
        "LSD-ACC-restr",
        CorrespondenceLocation::LeanOnly,
        "Lean-only observable restrict witness",
    ),
    (
        "LSD-ACC-sink",
        CorrespondenceLocation::LeanOnly,
        "Lean accept witness for the sink rule modeled by solver-lane Rust fixtures",
    ),
    (
        "LSD-ACC-handle",
        CorrespondenceLocation::LeanOnly,
        "Lean effect-handler witness has no same-ID Rust fixture",
    ),
    (
        "LSD-RESTR-removed",
        CorrespondenceLocation::LeanOnly,
        "Lean mutation witness proving restrict is load-bearing",
    ),
];

#[test]
fn differential_verdicts_match() {
    for f in FIXTURES {
        let got = in_scope_codes(f.src);
        let expect: Vec<String> = f.expect.iter().map(|s| s.to_string()).collect();
        assert_eq!(
            got,
            expect,
            "fixture {} ({}): in-scope code set mismatch",
            f.id,
            if f.expect.is_empty() {
                "accept"
            } else {
                "reject"
            }
        );
    }
}

#[test]
fn fixture_ids_match_expected_ids() {
    // A Rust-INTERNAL drift detector: the coded-fixture id set must match the in-repo EXPECTED_IDS
    // list 1:1. RENAMED from `ids_match_lean_obligations` (task #254) — the old name and the ledger
    // claim it backed both said this checked the LEAN obligation ids, but it never read Lean; it
    // only compared two Rust-side lists in this file. The genuine Rust↔Lean comparison is
    // `lean_obligation_ids_are_pinned` below, and it shows the two sets do NOT match.
    let mut ids: Vec<&str> = FIXTURES.iter().map(|f| f.id).collect();
    ids.sort();
    ids.dedup();
    let mut expected: Vec<&str> = EXPECTED_IDS.to_vec();
    expected.sort();
    assert_eq!(
        ids, expected,
        "fixture ids drifted from the in-repo EXPECTED_IDS list"
    );
}

/// Extract every `LSD-…` obligation id from a Lean source: after each `LSD-` take the leading
/// `[A-Za-z0-9-]` run. Mirrors the id syntax used in Differential.lean's correspondence table.
fn extract_lsd_ids(src: &str) -> std::collections::BTreeSet<String> {
    // `match_indices` yields byte offsets at each ASCII "LSD-" (always char boundaries); collecting
    // the following run by CHARS avoids any byte-slicing into the Lean file's unicode (e.g. the `…`
    // in its prose). A manual byte-advance here previously panicked mid-`…`.
    let mut out = std::collections::BTreeSet::new();
    for (i, _) in src.match_indices("LSD-") {
        let after = &src[i + 4..];
        let tail: String = after
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '-')
            .collect();
        // Trim a trailing '-' so `LSD-C003-` (before a '/') does not become a distinct id.
        let tail = tail.trim_end_matches('-');
        if !tail.is_empty() {
            out.insert(format!("LSD-{tail}"));
        }
    }
    out
}

/// Task #254 follow-on: read `Differential.lean` and require every ID in the Rust/Lean union to have
/// an explicit, location-correct correspondence classification. The relation is intentionally not
/// 1:1; the important invariant is that no difference is unexplained.
#[test]
fn lean_obligation_ids_are_pinned() {
    const LEAN_SRC: &str = include_str!("../../../proofs/lean/LambdaSigil/Differential.lean");
    const SOLVER_BRIDGE_SRC: &str = include_str!("../../sigil-compiler/tests/lambda_sigil_c003.rs");
    let lean = extract_lsd_ids(LEAN_SRC);

    // Anti-vacuity (SC-P4): the extractor must actually find the Lean ids, or every assertion below
    // is empty. Prove present-vs-absent before trusting it.
    assert!(
        extract_lsd_ids("no ids here").is_empty(),
        "extractor invented ids from nothing"
    );
    assert!(
        lean.len() >= 8,
        "Lean LSD-id extractor found only {} ids — the correspondence table moved or the extractor \
         broke; every pin below would be vacuous",
        lean.len()
    );

    let solver_rust = extract_lsd_ids(SOLVER_BRIDGE_SRC);
    let expected_solver: std::collections::BTreeSet<String> = [
        "LSD-C003-call",
        "LSD-C003-spawn",
        "LSD-C003-send",
        "LSD-C003-return",
    ]
    .into_iter()
    .map(str::to_string)
    .collect();
    assert_eq!(
        solver_rust, expected_solver,
        "the solver-lane Rust bridge IDs drifted"
    );
    let mut rust: std::collections::BTreeSet<String> =
        EXPECTED_IDS.iter().map(|s| s.to_string()).collect();
    rust.extend(solver_rust);
    let union: std::collections::BTreeSet<String> = rust.union(&lean).cloned().collect();
    let classified: std::collections::BTreeSet<String> = CORRESPONDENCE
        .iter()
        .map(|(id, _, _)| (*id).to_string())
        .collect();
    assert_eq!(
        classified, union,
        "every Rust/Lean differential ID must have exactly one classified correspondence row"
    );
    assert_eq!(
        classified.len(),
        CORRESPONDENCE.len(),
        "correspondence IDs must be unique"
    );

    for (id, location, reason) in CORRESPONDENCE {
        assert!(
            !reason.trim().is_empty(),
            "correspondence row {id} must explain its classification"
        );
        let in_rust = rust.contains(*id);
        let in_lean = lean.contains(*id);
        let actual = match (in_rust, in_lean) {
            (true, true) => CorrespondenceLocation::Shared,
            (true, false) => CorrespondenceLocation::RustOnly,
            (false, true) => CorrespondenceLocation::LeanOnly,
            (false, false) => panic!("classified ID {id} exists on neither side"),
        };
        assert_eq!(
            *location, actual,
            "correspondence row {id} has the wrong side classification"
        );
    }
}

#[test]
fn cap_forgery_rejected_by_frontend() {
    // LSD-C001 / LSD-ACC-C001 — by construction on both sides (no coded fixture; see module doc).
    // λ-SIGIL has no cap-forging Term; SIGIL rejects a record-literal coerced to a cap type at the
    // front end (parse/type), and capability.rs's C001 is an AIR-level backstop unreachable from
    // source.  Witness: forgery is NOT accepted; a legitimate pass-through carries no C-code.
    let forges = [
        "module sigil;\ncap type Fuel { burn, query }\nfn forge() -> Fuel { return Fuel { }; }\n",
        "module sigil;\ncap type Fuel { burn, query }\nrecord Faux { x: i64 }\n\
         fn forge() -> Fuel { let r: Faux = Faux { x: 0 }; return r; }\n",
    ];
    for src in forges {
        assert!(
            compile_module(src).is_err(),
            "cap forgery must be rejected: {src:?}"
        );
    }
    // LSD-ACC-C001: a legitimate capability pass-through triggers no capability (C-code) violation.
    let legit =
        "module sigil;\ncap type Fuel { burn, query }\nfn pass(f: Fuel) -> Fuel { return f; }\n";
    let cap_errs: Vec<String> = match compile_module(legit) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .filter(|c| c.starts_with('C'))
            .collect(),
    };
    assert_eq!(
        cap_errs,
        Vec::<String>::new(),
        "legit cap pass-through must carry no C-code"
    );
}
