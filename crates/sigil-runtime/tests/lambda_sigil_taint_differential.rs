//! λ-SIGIL M-T4 — the **taint** differential, Rust half (rust lane, no solver).
//!
//! Each fixture is the `.sigil` counterpart of a taint obligation in
//! `proofs/lean/LambdaSigil/TaintSafety.lean`; the shared `LSD-…` id ties the two halves.
//! Sibling of `lambda_sigil_differential.rs` (the M7 ownership/effect/mint half) and built in
//! the same shape.
//!
//! WHY THIS FILE EXISTS. `TaintSafety.lean` shipped its correspondence table with an explicit
//! bridge-status note: the taint ids were "**not yet asserted by a Rust-side harness** (no
//! `lambda_sigil_taint_differential.rs` pairs `.sigil` fixtures to these ids yet)". docs/CLAIMS.md
//! §D carried the same gap as an unproven row — *"the taint differential has no Rust half — the
//! Lean side declares its obligation ids and states plainly that nothing on the implementation
//! side consumes them."* A proof that no implementation artifact consumes is a proof about a
//! calculus and nothing else. This is that consumer.
//!
//! Verdict is read on the **in-scope code surface** {T001, O001} with `assert_eq!` (NOT
//! `contains`), so a right-verdict-wrong-reason fixture — an O001 appearing in a T001 row, or a
//! reject landing for an unrelated parse/type reason — breaks the test rather than passing as a
//! coincidence. `compile_module` runs the FULL pipeline on purpose: declassify-cap linearity is
//! enforced in AIR lowering, so an earlier-stage-only check would never see O001 at all.
//!
//! **SCOPE (honest).** This pairs *verdicts*, not *mechanisms*. It asserts that where λ-SIGIL
//! proves an obligation underivable, SIGIL rejects, and where λ-SIGIL exhibits a typing witness,
//! SIGIL accepts. It is NOT a claim that the two systems decide by the same means: the λ-SIGIL
//! taint calculus is first-order (no lam/let/call at all), while SIGIL's pass propagates
//! interprocedurally through signature tables. The Lean scope is sink-safety — the terminal check
//! — and this harness inherits exactly that scope.
//!
//! Unlike the M7 half, whose Rust and Lean id sets are intentionally NOT 1:1 (solver-lane
//! fixtures, Lean-only witnesses), the taint id sets are exactly equal, so
//! `lean_taint_obligation_ids_match_the_rust_half` asserts set EQUALITY rather than a classified
//! union. That is a stronger invariant and it should stay that way: a new Lean taint obligation
//! with no Rust fixture fails this file by name.

use sigil_compiler::compile_module;
use std::collections::BTreeSet;

/// The headline taint codes the fixtures range over. T001 is the taint-downgrade sink violation
/// (the F007 anchor); O001 is affine use-after-move, which is what declassify-cap reuse becomes
/// once the cap's linearity is enforced (the F002 anchor). Codes outside this set — parse,
/// resolve, missing-entry artifacts — are filtered out: the verdict asked of each fixture is
/// "does this trigger one of the headline taint violations?", not "does this compile at all".
const IN_SCOPE: &[&str] = &["T001", "O001"];

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
    /// shared id with the λ-SIGIL obligation in TaintSafety.lean
    id: &'static str,
    /// expected in-scope code set (`&[]` = accept)
    expect: &'static [&'static str],
    src: &'static str,
}

// ── T001 rejects — the three F007 sink violations ───────────────────────────────────────────

/// `LSD-T001-direct` / Lean `lsd_t001_direct_reject`. A `@Secret` value reaching an unannotated
/// (= `@Public`) sink parameter. The Lean twin `lsd_t001_direct_dirty` proves the flow this
/// rejection prevents is a genuine leak (`sec ⋢ pub`), so the reject is not merely conservative.
const T001_DIRECT: &str = "#[ring(outer)] module ext;
fn sink(v: i64) -> i64 { return v; }
fn leak(s: i64 @Secret) -> i64 { return sink(s); }
";

/// `LSD-T001-implicit` / Lean `lsd_t001_implicit_reject`. **Implicit flow**: no secret value is
/// ever passed to the sink — only control depends on the secret. Lean types the branches under
/// `pc ⊔ ℓg` and folds the guard label into the result; SIGIL must likewise taint the assignment
/// through the branch pc, or the secret leaks one bit at a time through an entirely public value.
const T001_IMPLICIT: &str = "#[ring(outer)] module ext;
fn sink(v: i64) -> i64 { return v; }
fn leak(s: i64 @Secret) -> i64 {
    let mut r: i64 = 0;
    if s == 0 { r = 1; } else { r = 2; }
    return sink(r);
}
";

/// `LSD-T001-host` / Lean `lsd_t001_host_reject`. Host/FFI results enter at `@Internal`, and
/// `@Internal ⋢ @Public` — so an unlaundered FFI result cannot reach a public sink either. The
/// lattice has three levels and a guard that only knows about `@Secret` leaves this open.
const T001_HOST: &str = "#[ring(outer)] module ext;
fn sink(v: i64) -> i64 { return v; }
fn ffi_read(p: i64) -> i64 @Internal ! { FFI, Unsafe } { return p; }
fn leak(p: i64) -> i64 ! { FFI, Unsafe } {
    let v: i64 @Internal = ffi_read(p);
    return sink(v);
}
";

/// `LSD-O001-declass` / Lean `lsd_o001_declass_reject` (= `declassify_linear`, F002). Two
/// downgrades cannot share one linear capability. Lean rejects via the consumed `Use` bit; SIGIL
/// rejects via affine ownership in AIR. This is the fixture that requires the full pipeline.
const O001_DECLASS: &str = "module ext;
cap type Declassify {}
fn f(s: i64 @Secret, t: i64 @Secret, d: Declassify) -> i64 @Public {
    let a: i64 @Public = declassify(s, d);
    let b: i64 @Public = declassify(t, d);
    return a + b;
}
";

// ── accept twins — each isolates the ONE thing that made its reject illegal ──────────────────

/// `LSD-ACC-declass` / Lean `lsd_acc_declass` (= `declassify_leak_typed`). The legal
/// `@Secret → @Public` downgrade through one consumed cap. Without this twin, T001-direct's
/// rejection would be consistent with "SIGIL rejects all declassification".
const ACC_DECLASS: &str = "module ext;
cap type Declassify {}
fn f(s: i64 @Secret, d: Declassify) -> i64 @Public {
    let a: i64 @Public = declassify(s, d);
    return a;
}
";

/// `LSD-ACC-once` / Lean `lsd_acc_declass_once` (= `declassify_once`, `[true] ↦ [false]`) and its
/// Lean control `declassify_twice_two_caps`. TWO declassifies with TWO caps is accepted — so
/// O001-declass is rejected for cap REUSE, not for declassifying twice. Linearity is the sole
/// cause, which is the exact claim the Lean control was written to isolate.
const ACC_ONCE: &str = "module ext;
cap type Declassify {}
fn f(s: i64 @Secret, t: i64 @Secret, d: Declassify, e: Declassify) -> i64 @Public {
    let a: i64 @Public = declassify(s, d);
    let b: i64 @Public = declassify(t, e);
    return a + b;
}
";

/// `LSD-ACC-host` / Lean `lsd_acc_host`. An FFI result may reach a sink at its OWN level — so
/// T001-host is rejected for the level MISMATCH, not for touching FFI at all.
const ACC_HOST: &str = "#[ring(outer)] module ext;
fn isink(v: i64 @Internal) -> i64 @Internal { return v; }
fn ffi_read(p: i64) -> i64 @Internal ! { FFI, Unsafe } { return p; }
fn ok(p: i64) -> i64 @Internal ! { FFI, Unsafe } {
    let v: i64 @Internal = ffi_read(p);
    return isink(v);
}
";

/// `LSD-ACC-implicit` / Lean `lsd_acc_implicit`. The SAME branch shape as T001-implicit with a
/// `@Public` guard. This is the load-bearing twin of the corpus: it proves T001-implicit is
/// rejected because the GUARD is secret, not because SIGIL taints every value written under any
/// conditional. Delete this twin and the implicit-flow row degenerates into "branches are
/// rejected", which would be true of a uselessly conservative checker.
const ACC_IMPLICIT: &str = "#[ring(outer)] module ext;
fn sink(v: i64) -> i64 { return v; }
fn ok(p: i64) -> i64 {
    let mut r: i64 = 0;
    if p == 0 { r = 1; } else { r = 2; }
    return sink(r);
}
";

const FIXTURES: &[Fixture] = &[
    Fixture {
        id: "LSD-T001-direct",
        expect: &["T001"],
        src: T001_DIRECT,
    },
    Fixture {
        id: "LSD-T001-implicit",
        expect: &["T001"],
        src: T001_IMPLICIT,
    },
    Fixture {
        id: "LSD-T001-host",
        expect: &["T001"],
        src: T001_HOST,
    },
    Fixture {
        id: "LSD-O001-declass",
        expect: &["O001"],
        src: O001_DECLASS,
    },
    Fixture {
        id: "LSD-ACC-declass",
        expect: &[],
        src: ACC_DECLASS,
    },
    Fixture {
        id: "LSD-ACC-once",
        expect: &[],
        src: ACC_ONCE,
    },
    Fixture {
        id: "LSD-ACC-host",
        expect: &[],
        src: ACC_HOST,
    },
    Fixture {
        id: "LSD-ACC-implicit",
        expect: &[],
        src: ACC_IMPLICIT,
    },
];

/// The in-repo expectation, kept separate from `FIXTURES` so a fixture silently dropped from the
/// corpus fails rather than shrinking the covered set.
const EXPECTED_IDS: &[&str] = &[
    "LSD-ACC-declass",
    "LSD-ACC-host",
    "LSD-ACC-implicit",
    "LSD-ACC-once",
    "LSD-O001-declass",
    "LSD-T001-direct",
    "LSD-T001-host",
    "LSD-T001-implicit",
];

#[test]
fn taint_differential_verdicts_match() {
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

/// SC-P4 anti-stub. `taint_differential_verdicts_match` compares each fixture against its own
/// expectation, which a corpus of all-accepts would satisfy trivially — and an accept is exactly
/// what `in_scope_codes` returns when the compiler silently stops emitting taint codes at all.
/// Pin that the corpus contains BOTH verdicts and that the instrument distinguishes them.
#[test]
fn taint_corpus_carries_both_verdicts() {
    let rejects = FIXTURES.iter().filter(|f| !f.expect.is_empty()).count();
    let accepts = FIXTURES.iter().filter(|f| f.expect.is_empty()).count();
    assert_eq!(rejects, 4, "the corpus lost a reject fixture");
    assert_eq!(accepts, 4, "the corpus lost an accept fixture");

    // Every headline code must be exercised by some reject — a corpus that covers only T001
    // would leave the F002/O001 anchor unbridged while still looking balanced.
    let covered: BTreeSet<&str> = FIXTURES
        .iter()
        .flat_map(|f| f.expect.iter().copied())
        .collect();
    let in_scope: BTreeSet<&str> = IN_SCOPE.iter().copied().collect();
    assert_eq!(
        covered, in_scope,
        "every in-scope taint code must be the headline of some reject fixture"
    );
}

/// Extract every `LSD-…` obligation id from a Lean source: after each `LSD-` take the leading
/// `[A-Za-z0-9-]` run. Mirrors `lambda_sigil_differential.rs`'s extractor, with one addition —
/// TaintSafety.lean's prose refers to id FAMILIES as `LSD-T001-*` and `LSD-ACC-*`. Those globs
/// would otherwise become phantom ids (`LSD-T001`, `LSD-ACC`) that no fixture can ever match, so
/// a run followed by `*` is skipped. Collecting by CHARS avoids byte-slicing into the file's
/// unicode (`…`, `⊑`, `↦`).
fn extract_lsd_ids(src: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for (i, _) in src.match_indices("LSD-") {
        let after = &src[i + 4..];
        let tail: String = after
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '-')
            .collect();
        // A wildcard reference to a family, not an id.
        if after.chars().nth(tail.chars().count()) == Some('*') {
            continue;
        }
        let tail = tail.trim_end_matches('-');
        if !tail.is_empty() {
            out.insert(format!("LSD-{tail}"));
        }
    }
    out
}

/// THE BRIDGE. Reads `TaintSafety.lean` and requires its obligation ids and this file's fixture
/// ids to be the SAME SET. Closes docs/CLAIMS.md §D's "the taint differential has no Rust half".
///
/// Equality, not containment, in both directions on purpose: a new Lean obligation with no Rust
/// fixture is an unbridged proof, and a Rust fixture with no Lean obligation is a test claiming a
/// correspondence that was never proved. Both are the drift this bridge exists to catch.
#[test]
fn lean_taint_obligation_ids_match_the_rust_half() {
    const LEAN_SRC: &str = include_str!("../../../proofs/lean/LambdaSigil/TaintSafety.lean");

    // Anti-vacuity (SC-P4): the extractor must distinguish present from absent, or every
    // assertion below is a comparison of two empty sets.
    assert!(
        extract_lsd_ids("no ids here").is_empty(),
        "extractor invented ids from nothing"
    );
    assert_eq!(
        extract_lsd_ids("see `LSD-T001-direct` and `LSD-ACC-host`."),
        ["LSD-T001-direct", "LSD-ACC-host"]
            .into_iter()
            .map(str::to_string)
            .collect::<BTreeSet<String>>(),
        "extractor must find real ids and stop at the closing backtick"
    );
    assert!(
        extract_lsd_ids("the `LSD-T001-*` family").is_empty(),
        "a wildcard family reference must NOT become a phantom id"
    );

    let lean = extract_lsd_ids(LEAN_SRC);
    let rust: BTreeSet<String> = EXPECTED_IDS.iter().map(|s| s.to_string()).collect();

    // Floor: if the Lean file were moved or its table rewritten, an empty extraction would make
    // the equality below pass only when the Rust side were ALSO empty — which the corpus pins
    // against — but say it directly rather than relying on that interaction.
    assert!(
        lean.len() >= 8,
        "Lean taint-id extractor found only {} ids — the correspondence table moved or the \
         extractor broke",
        lean.len()
    );
    assert_eq!(
        lean, rust,
        "the λ-SIGIL taint obligation ids and this file's fixture ids must be the same set"
    );

    let mut fixture_ids: Vec<&str> = FIXTURES.iter().map(|f| f.id).collect();
    fixture_ids.sort();
    fixture_ids.dedup();
    let mut expected: Vec<&str> = EXPECTED_IDS.to_vec();
    expected.sort();
    assert_eq!(
        fixture_ids, expected,
        "fixture ids drifted from the in-repo EXPECTED_IDS list"
    );
}
