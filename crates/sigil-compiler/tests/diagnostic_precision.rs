//! Axis a10 — **single-error precision** over the labeled reject corpus.
//!
//! SCOPE (read this before extending): this is a PRECISION gate, not a
//! soundness/recall one. For every fixture the compiler is *supposed to reject*,
//! it asserts the rejection is exactly right:
//!   * EXACTLY ONE `Severity::Error` diagnostic whose code equals the declared
//!     expected code (exact equality — never a substring/message match), AND
//!   * ZERO other `Severity::Error` codes (no spurious cascade / report-once),
//!     unless the fixture is in the central [`PRECISION_MULTI_ERROR`] allowlist.
//!
//! It has ZERO recall: a should-error-but-silently-accepted program lives in no
//! `expect-error` fixture and cannot move this metric. Genuine recall needs a
//! separate negative-corpus axis (out of scope).
//!
//! This is the genuinely-new bit over `registry_wired.rs` (which checks code
//! *presence*): the no-spurious-sibling property makes the no-cascade invariants
//! that today live only in code comments — `Type::Error` poison
//! (type_check/expressions.rs), the `place_ok` follow-on suppression and
//! region-depth isolation (type_check/statements.rs) — machine-checked. Deleting
//! one of those guards makes a dedicated `precision_corpus` fixture sprout a
//! spurious sibling and turns this test red.
//!
//! Lanes: the default `cargo test` lane enforces the non-solver corpus
//! (`tests/fixtures` by filename + `tests/cve_corpus` + `tests/precision_corpus`);
//! the solver lane (`#[cfg(feature = "solver")]`) adds the Z3 refinement family in
//! `tests/z3_corpus`. Both lanes are non-empty so neither CI surface is a no-op.

use std::collections::{BTreeMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use sigil_compiler::diagnostics::Severity;
use sigil_compiler::{Diagnostic, compile_named_module};

/// Programmatic sentinel fixtures (`registry_wired::SENTINEL_PROGRAMMATIC`) have
/// no single-error source form and are excluded from precision enforcement.
const SENTINEL_EXCLUDED: &[&str] = &["S004", "S005", "S006"];

/// Central, reviewed allowlist for fixtures that LEGITIMATELY emit Error codes
/// beyond their expected one. A fixture may carry extra Error siblings ONLY if
/// it appears here with a non-empty reason. Each extra code DEBITS a10 (the
/// scoreboard credits `enforced - allowlisted_extras`), so silencing a real
/// spurious-cascade regression by appending to this table *lowers* the metric
/// and is refused by the `--check` ratchet — the opposite of a free escape hatch.
///
/// `(fixture stem, &[extra Error codes beyond the expected one], reason)`
const PRECISION_MULTI_ERROR: &[(&str, &[&str], &str)] = &[
    (
        "R006",
        &["E003"],
        "the #[ring(inner)] #[trusted] module also declares `! { Unsafe }`, so it independently \
         violates E003 (inner-ring modules cannot declare Unsafe/FFI) alongside R006 (trusted \
         requires #[ring(outer)]) — two distinct authority errors on one module.",
    ),
    (
        "T198",
        &["P002"],
        "the malformed `cap type Approval(deadline: bool)` is rejected by BOTH the parser (P002) \
         and the cap-decl validator (T198) — a pre-existing parse/typecheck double-report on one \
         declaration (candidate for a future report-once cleanup).",
    ),
    (
        "10_cve_2018_1002105_k8s",
        &["T095"],
        "passing an i64 where a capability is required at spawn-init trips two adjacent capability \
         checks (T095 and the expected T096); both are genuine for the same smuggle.",
    ),
    (
        "24_multi_param_arity_mismatch",
        &["T201"],
        "a multi-parameter cap arity mismatch reports T201 once per offending parameter (2 here); \
         pre-existing per-parameter reporting, baselined (candidate for a future report-once review).",
    ),
    (
        "48_variant_refinement_positional_fails_parse",
        &["P001"],
        "the positional variant-refinement form deliberately fails to parse (P001) in addition to \
         the T223 it is named for — both are intended for this fixture.",
    ),
    (
        "74_cap_smuggle_nested_option_recursive",
        &["T242"],
        "the recursive nested-Option cap smuggle is flagged at two nesting levels (2x T242); \
         pre-existing per-level reporting, baselined (candidate for a future report-once review).",
    ),
];

// ── core logic (unit-testable: takes diagnostics, no compile) ─────────────

/// Precision violations for one fixture's diagnostics. Empty ⇒ pass.
/// Warnings are structurally excluded (T252 `@ReadOnly` lint rides the `Err`
/// path); the check is count-per-exact-code, so a same-code duplicate is caught
/// too, not just a different-code sibling.
fn precision_violations(
    diags: &[Diagnostic],
    expected: &str,
    allowed_extra: &[&str],
) -> Vec<String> {
    // The fixture's Error-code MULTISET must be EXACTLY {expected: 1} plus the
    // allowlisted extras (which may include `expected` itself to declare a
    // legitimate same-code count). Multiset equality catches a spurious sibling
    // (a different code) AND a same-code cascade (one root re-reported N times).
    let mut actual: BTreeMap<String, usize> = BTreeMap::new();
    for d in diags.iter().filter(|d| d.severity() == Severity::Error) {
        *actual.entry(d.code().as_str().to_string()).or_default() += 1;
    }
    let mut expected_ms: BTreeMap<String, usize> = BTreeMap::new();
    *expected_ms.entry(expected.to_string()).or_default() += 1;
    for c in allowed_extra {
        *expected_ms.entry((*c).to_string()).or_default() += 1;
    }
    if actual == expected_ms {
        Vec::new()
    } else {
        vec![format!(
            "Error-code multiset {actual:?} != expected {expected_ms:?}"
        )]
    }
}

// ── corpus loading ────────────────────────────────────────────────────────

struct Fixture {
    /// Display name (file stem) for diagnostics + allowlist matching.
    name: String,
    source: String,
    /// The single Error code the compiler must emit for this input.
    expected: String,
}

fn tests_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests")
}

fn read_sigil(dir: &Path) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for entry in fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display())) {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|ext| ext == "sigil") {
            let stem = path.file_stem().unwrap().to_string_lossy().to_string();
            let source = fs::read_to_string(&path).unwrap();
            out.push((stem, source));
        }
    }
    out.sort_by(|a, b| a.0.cmp(&b.0));
    out
}

/// `tests/fixtures/<CODE>.sigil` — the expected code IS the filename (covers the
/// hard-required N007/N008/N009/N011/R004/T155/T156 whose first line is a plain
/// `// N007:` comment, not `// expect-error:`). SENTINEL stubs excluded.
fn load_fixtures_by_filename() -> Vec<Fixture> {
    read_sigil(&tests_dir().join("fixtures"))
        .into_iter()
        .filter(|(stem, _)| !SENTINEL_EXCLUDED.contains(&stem.as_str()))
        .map(|(stem, source)| Fixture {
            name: stem.clone(),
            source,
            expected: stem,
        })
        .collect()
}

/// Parse the EXACT expected code from a `// expect-error: <CODE>` line. The code
/// is the first whitespace-delimited token after the prefix — never a substring
/// of the message (E2). Returns `None` for `expect-ok` / `expect-shape` / files
/// with no such annotation (they keep their existing compile-clean contract).
fn parse_expect_error(source: &str) -> Option<String> {
    for line in source.lines() {
        let t = line.trim();
        if let Some(rest) = t.strip_prefix("// expect-error:") {
            return rest.split_whitespace().next().map(str::to_string);
        }
        if t.starts_with("// expect-ok") || t.starts_with("// expect-shape") {
            return None;
        }
        if !t.starts_with("//") && !t.is_empty() {
            return None;
        }
    }
    None
}

/// Load the `expect-error` fixtures from a corpus subdir. Missing dir ⇒ empty
/// (so `precision_corpus` can be added incrementally).
fn load_expect_error_dir(sub: &str) -> Vec<Fixture> {
    let dir = tests_dir().join(sub);
    if !dir.is_dir() {
        return Vec::new();
    }
    read_sigil(&dir)
        .into_iter()
        .filter_map(|(name, source)| {
            parse_expect_error(&source).map(|expected| Fixture {
                name,
                source,
                expected,
            })
        })
        .collect()
}

fn default_lane_fixtures() -> Vec<Fixture> {
    let mut v = load_fixtures_by_filename();
    v.extend(load_expect_error_dir("cve_corpus"));
    v.extend(load_expect_error_dir("precision_corpus"));
    v
}

fn allowed_extra(name: &str) -> &'static [&'static str] {
    PRECISION_MULTI_ERROR
        .iter()
        .find(|(n, _, _)| *n == name)
        .map(|(_, extras, _)| *extras)
        .unwrap_or(&[])
}

/// `None` ⇒ the fixture passes precision; `Some(msg)` ⇒ a one-line failure
/// (with the full Error-code set) for the aggregated report.
fn check_fixture(fx: &Fixture) -> Option<String> {
    let err = match compile_named_module(&fx.name, &fx.source) {
        Err(e) => e,
        Ok(_) => {
            return Some(format!(
                "`{}`: declared expect-error {} but compiled CLEAN (wrong feature lane or recall regression)",
                fx.name, fx.expected
            ));
        }
    };
    let violations = precision_violations(err.diagnostics(), &fx.expected, allowed_extra(&fx.name));
    if violations.is_empty() {
        return None;
    }
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .map(|d| d.code().as_str())
        .collect();
    Some(format!(
        "`{}` (expected {}): {} [errors: {codes:?}]",
        fx.name,
        fx.expected,
        violations.join("; ")
    ))
}

fn run_lane(fxs: &[Fixture], lane: &str) {
    let failures: Vec<String> = fxs.iter().filter_map(check_fixture).collect();
    assert!(
        failures.is_empty(),
        "{} precision failure(s) in the {lane} lane:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

// ── lane tests ────────────────────────────────────────────────────────────

#[test]
fn precision_default_lane() {
    let fxs = default_lane_fixtures();
    assert!(
        fxs.len() >= 20,
        "default lane must be non-empty/meaningful (E3); got {}",
        fxs.len()
    );
    run_lane(&fxs, "default");
}

#[cfg(feature = "solver")]
#[test]
fn precision_solver_lane() {
    let fxs = load_expect_error_dir("z3_corpus");
    assert!(
        fxs.len() >= 20,
        "solver lane must be non-empty; got {}",
        fxs.len()
    );
    run_lane(&fxs, "solver");
}

// ── meta-tests (anti-gaming, anti-rot) ────────────────────────────────────

#[test]
fn allowlist_is_well_formed() {
    // Every allowlist entry must name a real fixture and carry a reason; stale
    // or empty entries fail the build (E4).
    let mut names: HashSet<String> = default_lane_fixtures()
        .into_iter()
        .map(|f| f.name)
        .collect();
    for (stem, _) in read_sigil(&tests_dir().join("z3_corpus")) {
        names.insert(stem);
    }
    for (name, extras, reason) in PRECISION_MULTI_ERROR {
        assert!(
            !reason.trim().is_empty(),
            "allowlist entry `{name}` must have a non-empty reason"
        );
        assert!(
            !extras.is_empty(),
            "allowlist entry `{name}` lists no extra codes — delete it"
        );
        assert!(
            names.contains(*name),
            "allowlist entry `{name}` matches no fixture in any corpus"
        );
    }
}

#[test]
fn precision_uses_exact_matching_and_runs_in_ci() {
    // Grep-guard (E2/E10): this file must never reintroduce the lowercased
    // substring code-matcher, nor opt itself out of CI. Needles are assembled
    // via concat! so this guard does not match its own source.
    let src = fs::read_to_string(tests_dir().join("diagnostic_precision.rs")).unwrap();
    let banned_substr = concat!("to_", "lowercase");
    assert!(
        !src.contains(banned_substr),
        "precision must use EXACT code equality, never a lowercased substring match (E2)"
    );
    let banned_ignore = concat!("#[", "ignore]");
    assert!(
        !src.contains(banned_ignore),
        "the precision test must run in CI — never skip it (E10)"
    );
}

#[test]
fn warnings_and_duplicates_handled() {
    use sigil_compiler::DiagnosticCode;
    let err = |c: &'static str| Diagnostic::error(DiagnosticCode::new(c), "x", None);
    let warn = |c: &'static str| Diagnostic::warning(DiagnosticCode::new(c), "x", None);

    // A warning (T252) alongside the expected error is NOT a spurious sibling (E5).
    assert!(precision_violations(&[err("T046"), warn("T252")], "T046", &[]).is_empty());
    // A different-code Error sibling is caught.
    assert!(!precision_violations(&[err("T046"), err("T044")], "T046", &[]).is_empty());
    // A same-code duplicate is caught (E8 — count-per-code, not set membership).
    assert!(!precision_violations(&[err("T046"), err("T046")], "T046", &[]).is_empty());
    // An allowlisted extra is permitted.
    assert!(precision_violations(&[err("T046"), err("T044")], "T046", &["T044"]).is_empty());
    // The expected code missing entirely is caught.
    assert!(!precision_violations(&[err("T044")], "T046", &[]).is_empty());
}
