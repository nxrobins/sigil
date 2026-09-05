//! Style census — the mechanizable slice of docs/STYLE.md, as ratchets.
//!
//! The style guide exists because this repo was built by many agent sessions
//! and style drifts stratigraphically: each session imitates whatever files
//! land in its context window. Prose guidance alone cannot hold a line that
//! nobody's tests check — the house maxim is that a claim no test enforces is
//! a hope — so every style rule that can be counted is pinned here in the
//! house ratchet idiom: counts may FALL freely (ratchet wins), and fail only
//! on growth past the pinned value. Judgment-call rules (comment altitude,
//! naming, evidence idioms) live in docs/STYLE.md and CLAUDE.md; this file
//! polices only what a machine can police.
//!
//! Four families:
//!
//! 1. **Debt markers are zero.** There are no TODO/FIXME-style markers in
//!    106k lines of src, and that is a convention, not an accident: debt
//!    lives in the ledgers (docs/RESIDUAL_RISKS.md, docs/CLAIMS.md section D,
//!    docs/diagnostic-test-gaps.txt, tests/attack/KNOWN_GAPS.md), where it
//!    carries an owner and a review point instead of rotting in a comment.
//! 2. **Module-doc gaps are an exact-set manifest, pinned empty.** Every
//!    src file opens with a `//!` stating its role; the 26-file
//!    pre-convention backlog enumerated in docs/style-module-doc-gaps.txt
//!    was cleared by the coherency campaign, so ANY file without a module
//!    doc is now a fresh gap absent from the manifest and fails loudly —
//!    write the doc, don't grow the manifest.
//! 3. **Bare-unwrap ceilings per crate.** The strong stratum uses
//!    `.expect("narrated invariant")` or typed errors; bare `.unwrap()` in
//!    src is pinned at its measured count per crate and may only fall.
//!    (Integration tests are exempt: only `src/` is scanned — which
//!    includes inline `#[cfg(test)]` modules, deliberately, since their
//!    failure text is all the context a red CI run gives.)
//! 4. **The `test_` name prefix is extinct.** Test names are assertion
//!    sentences (docs/STYLE.md section 2.1); the compiler attribute already
//!    says it is a test. The last seven prefixed names were renamed in the
//!    registry cleanup and the count is pinned at zero.
//!
//! Every detector carries an anti-stub proving it detects (SC-P4): a census
//! whose detector cannot see the construct when present is evidence of
//! nothing — this repo has caught exactly that failure twice in one day.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

// The `#[test]`-aware name extractor PIN-6 trusts: real test fns only,
// never `fn` text inside a fixture string. Shared via #[path] like every
// census that needs it.
#[path = "support/test_source.rs"]
mod test_source;

const GAP_MANIFEST_REL: &str = "docs/style-module-doc-gaps.txt";

/// Cardinality pin for the gap manifest (SC-P1: measured — 26 at
/// introduction, zero since the backlog cleared). Any growth is a fresh
/// regression and requires a stated reason in the same commit.
const MODULE_DOC_GAP_COUNT: usize = 0;

/// Bare `.unwrap()` ceilings per crate src tree — measured at introduction.
/// Lower a value when you clean a crate up (ratchet win); raising one is an
/// explicit style regression and needs a stated reason in the same commit.
const UNWRAP_CEILINGS: &[(&str, usize)] = &[
    ("sigil-abi", 0),
    ("sigil-cli", 4),
    // The formal-bridge census repair exposed that this pre-existing ceiling
    // had drifted far below the measured tree while the missing-crate check
    // returned first. Pin the audited tree exactly so future growth is blocked.
    ("sigil-compiler", 92),
    ("sigil-corpus", 0),
    ("sigil-formal-bridge", 0),
    ("sigil-frontends", 1),
    ("sigil-mcp", 10),
    ("sigil-registry", 0),
    ("sigil-runtime", 10),
    ("sigil-serve", 0),
    ("sigil-test-utils", 2),
];

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crates/sigil-runtime has a workspace root two levels up")
        .to_path_buf()
}

/// Every `.rs` file under `crates/<crate>/src`, as (crate, workspace-relative
/// forward-slash path) pairs, sorted.
fn src_files() -> Vec<(String, String)> {
    let root = workspace_root();
    let mut out = Vec::new();
    let crates_dir = root.join("crates");
    for entry in fs::read_dir(&crates_dir).expect("crates/ exists") {
        let crate_dir = entry.expect("dir entry").path();
        let src = crate_dir.join("src");
        if !src.is_dir() {
            continue;
        }
        let crate_name = crate_dir
            .file_name()
            .expect("crate dir has a name")
            .to_string_lossy()
            .to_string();
        collect_rs(&src, &root, &crate_name, &mut out);
    }
    out.sort();
    out
}

fn collect_rs(dir: &Path, root: &Path, crate_name: &str, out: &mut Vec<(String, String)>) {
    for entry in fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display())) {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            collect_rs(&path, root, crate_name, out);
        } else if path.extension().is_some_and(|x| x == "rs") {
            let rel = path
                .strip_prefix(root)
                .expect("under root")
                .components()
                .map(|c| c.as_os_str().to_string_lossy())
                .collect::<Vec<_>>()
                .join("/");
            out.push((crate_name.to_string(), rel));
        }
    }
}

// ── Detectors, factored for anti-stubbing ───────────────────────────────

/// Debt-marker detector. Word-ish match on the four marker spellings the
/// original census measured at zero.
fn debt_markers_in(source: &str) -> usize {
    ["TODO", "FIXME", "HACK", "XXX"]
        .iter()
        .map(|m| source.matches(m).count())
        .sum()
}

/// Module-doc detector: any line starting with `//!` at column zero — the
/// same predicate the gap manifest was measured with. Column zero matters:
/// an indented `//!` inside an inline `mod` block documents that module,
/// not the file, and must not satisfy the file-level rule.
fn has_module_doc(source: &str) -> bool {
    source.lines().any(|l| l.starts_with("//!"))
}

/// Bare-unwrap counter: literal `.unwrap()` occurrences.
fn unwrap_count_in(source: &str) -> usize {
    source.matches(".unwrap()").count()
}

// ── Family 1: debt markers ──────────────────────────────────────────────

#[test]
fn style_debt_markers_are_zero_in_src() {
    let root = workspace_root();
    let mut hits = Vec::new();
    for (_, rel) in src_files() {
        let text =
            fs::read_to_string(root.join(&rel)).unwrap_or_else(|e| panic!("reading {rel}: {e}"));
        let n = debt_markers_in(&text);
        if n > 0 {
            hits.push(format!("{rel}: {n} marker(s)"));
        }
    }
    assert!(
        hits.is_empty(),
        "debt markers found in src:\n{}\n\
         The convention is zero: debt goes to a ledger with an owner and a \
         review point (docs/RESIDUAL_RISKS.md for soundness risks, \
         docs/CLAIMS.md section D for unproven claims, \
         tests/attack/KNOWN_GAPS.md for attack-surface gaps), not into a \
         comment that nothing revisits.",
        hits.join("\n"),
    );
}

#[test]
fn style_debt_marker_detector_detects() {
    assert_eq!(debt_markers_in("let x = 1; // fine"), 0);
    let planted = String::from("// T") + "ODO: fix this later";
    assert_eq!(
        debt_markers_in(&planted),
        1,
        "anti-stub: the detector must see a planted marker"
    );
}

// ── Family 2: module-doc gaps as an exact-set manifest ──────────────────

#[test]
fn style_module_doc_gaps_match_the_manifest() {
    let root = workspace_root();
    let manifest_text = fs::read_to_string(root.join(GAP_MANIFEST_REL))
        .unwrap_or_else(|e| panic!("reading {GAP_MANIFEST_REL}: {e}"));
    let manifest: BTreeSet<String> = manifest_text
        .lines()
        .map(|l| l.strip_suffix('\r').unwrap_or(l).trim())
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(str::to_string)
        .collect();
    assert_eq!(
        manifest.len(),
        MODULE_DOC_GAP_COUNT,
        "{GAP_MANIFEST_REL} cardinality moved; update MODULE_DOC_GAP_COUNT in the \
         same commit with a stated reason (shrinking is a ratchet win)"
    );

    let mut actual = BTreeSet::new();
    for (_, rel) in src_files() {
        let text =
            fs::read_to_string(root.join(&rel)).unwrap_or_else(|e| panic!("reading {rel}: {e}"));
        if !has_module_doc(&text) {
            actual.insert(rel);
        }
    }

    let new_gaps: Vec<_> = actual.difference(&manifest).cloned().collect();
    let healed: Vec<_> = manifest.difference(&actual).cloned().collect();
    assert!(
        new_gaps.is_empty(),
        "src file(s) without a leading //! module doc, not in {GAP_MANIFEST_REL}:\n{}\n\
         Write the module doc (role + load-bearing constraints — see docs/STYLE.md) \
         rather than adding to the manifest; the manifest exists only to hold the \
         line while the pre-convention backlog shrinks.",
        new_gaps.join("\n"),
    );
    assert!(
        healed.is_empty(),
        "manifest row(s) whose file now HAS a module doc (or no longer exists) — \
         a ratchet win; remove them from {GAP_MANIFEST_REL} and lower \
         MODULE_DOC_GAP_COUNT in the same commit:\n{}",
        healed.join("\n"),
    );
}

#[test]
fn style_module_doc_detector_detects() {
    assert!(has_module_doc("//! A module doc.\nfn f() {}\n"));
    assert!(
        !has_module_doc("// a plain comment\nfn f() {}\n"),
        "anti-stub: a file without any inner doc line must read as a gap"
    );
    assert!(
        !has_module_doc("mod t {\n    //! inner-module doc\n}\n"),
        "anti-stub: an indented inner-module doc must not satisfy the file-level rule"
    );
}

// ── Family 3: bare-unwrap ceilings ──────────────────────────────────────

#[test]
fn style_bare_unwrap_ceilings_hold() {
    let root = workspace_root();
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for (crate_name, rel) in src_files() {
        let text =
            fs::read_to_string(root.join(&rel)).unwrap_or_else(|e| panic!("reading {rel}: {e}"));
        *counts.entry(crate_name).or_insert(0) += unwrap_count_in(&text);
    }

    let ceilings: BTreeMap<&str, usize> = UNWRAP_CEILINGS.iter().copied().collect();
    // Every crate with src must have a ceiling row: a NEW crate gets a row
    // (ideally 0) rather than escaping the census by omission.
    let missing: Vec<_> = counts
        .keys()
        .filter(|c| !ceilings.contains_key(c.as_str()))
        .cloned()
        .collect();
    assert!(
        missing.is_empty(),
        "crate(s) without an UNWRAP_CEILINGS row: {missing:?} — add a row (new \
         crates should enter at 0)"
    );

    let mut over = Vec::new();
    let mut slack = Vec::new();
    for (crate_name, ceiling) in UNWRAP_CEILINGS {
        let actual = counts.get(*crate_name).copied().unwrap_or(0);
        if actual > *ceiling {
            over.push(format!(
                "{crate_name}: {actual} bare .unwrap() calls in src, ceiling {ceiling}"
            ));
        } else if actual < *ceiling {
            slack.push(format!(
                "{crate_name}: {actual} < ceiling {ceiling} — tighten the pin"
            ));
        }
    }
    assert!(
        over.is_empty(),
        "bare-unwrap ceiling exceeded:\n{}\n\
         The house dialect is .expect(\"narrated invariant\") when the invariant \
         is real, or a typed error when the path is fallible — see docs/STYLE.md. \
         Raising a ceiling requires a stated reason in the same commit.",
        over.join("\n"),
    );
    // Slack is printed, not failed: the pin can be tightened opportunistically,
    // and failing on improvement would punish cleanups made in passing.
    if !slack.is_empty() {
        println!(
            "unwrap ceilings with slack (tighten when convenient):\n{}",
            slack.join("\n")
        );
    }
}

#[test]
fn style_unwrap_counter_counts() {
    assert_eq!(unwrap_count_in("a.unwrap().b.unwrap()"), 2);
    assert_eq!(
        unwrap_count_in("a.unwrap_or_else(|| 0).unwrap_or(1)"),
        0,
        "anti-stub: the counter must not match the _or/_or_else forms"
    );
}

// ── Family 4: the test_ name prefix is extinct ──────────────────────────

/// Every `.rs` file under `crates/<crate>/{src,tests}`, workspace-relative.
/// Family 4 scans both trees: test fns live in integration files AND in
/// inline `#[cfg(test)]` modules under src.
fn src_and_test_files() -> Vec<String> {
    let root = workspace_root();
    let mut out: Vec<(String, String)> = Vec::new();
    let crates_dir = root.join("crates");
    for entry in fs::read_dir(&crates_dir).expect("crates/ exists") {
        let crate_dir = entry.expect("dir entry").path();
        let crate_name = crate_dir
            .file_name()
            .expect("crate dir has a name")
            .to_string_lossy()
            .to_string();
        for sub in ["src", "tests"] {
            let dir = crate_dir.join(sub);
            if dir.is_dir() {
                collect_rs(&dir, &root, &crate_name, &mut out);
            }
        }
    }
    let mut rels: Vec<String> = out.into_iter().map(|(_, rel)| rel).collect();
    rels.sort();
    rels
}

/// Test names are assertion sentences (docs/STYLE.md section 2.1) — the
/// `#[test]` attribute already says it is a test, so a `test_` prefix is
/// dead weight that displaces the claim. Measured to zero by the registry
/// cleanup (which renamed the last seven); pinned so it stays extinct.
/// Uses the `#[test]`-aware extractor, so `fn test_` text inside a fixture
/// string or a non-test helper (`test_fn_names_in` itself) cannot
/// false-positive.
#[test]
fn style_test_prefix_is_extinct() {
    let root = workspace_root();
    let mut offenders = Vec::new();
    for rel in src_and_test_files() {
        let text =
            fs::read_to_string(root.join(&rel)).unwrap_or_else(|e| panic!("reading {rel}: {e}"));
        for name in test_source::test_fn_names_in(&text) {
            if name.starts_with("test_") {
                offenders.push(format!("{rel}: fn {name}"));
            }
        }
    }
    offenders.sort();
    assert!(
        offenders.is_empty(),
        "test fn(s) with a `test_` prefix:\n{}\n\
         Name the test as the assertion sentence it proves \
         (docs/STYLE.md section 2.1) — the attribute already marks it a test.",
        offenders.join("\n"),
    );
}

#[test]
fn style_test_prefix_detector_detects() {
    let planted = "#[test]\nfn test_something() {}\n";
    let names = test_source::test_fn_names_in(planted);
    assert!(
        names.iter().any(|n| n.starts_with("test_")),
        "anti-stub: a planted prefixed test fn must be extracted and flagged"
    );
    let clean = "#[test]\nfn sentence_shaped_name() {}\nfn test_helper_without_attr() {}\n";
    let names = test_source::test_fn_names_in(clean);
    assert!(
        !names.iter().any(|n| n.starts_with("test_")),
        "anti-stub: a non-test helper named test_* must NOT be extracted"
    );
}

// ── The guide itself stays present and cross-referenced ─────────────────

/// The judgment-call rules live in prose, so the least the census can do is
/// pin that the prose exists, is substantial, and is discoverable from the
/// per-session contract. Deleting or stubbing the guide should be as loud
/// as breaking any other pin.
#[test]
fn style_guide_files_exist_and_are_cross_referenced() {
    let root = workspace_root();
    let claude = fs::read_to_string(root.join("CLAUDE.md"))
        .expect("CLAUDE.md exists at the workspace root — it is the per-session style contract");
    let style = fs::read_to_string(root.join("docs/STYLE.md"))
        .expect("docs/STYLE.md exists — the full mined style guide");
    assert!(
        claude.contains("docs/STYLE.md"),
        "CLAUDE.md must point sessions at docs/STYLE.md"
    );
    assert!(
        style.contains("style_census.rs"),
        "docs/STYLE.md must name the census that enforces its mechanizable slice"
    );
    assert!(
        style.len() > 4_000,
        "docs/STYLE.md is suspiciously small ({} bytes) — the guide must carry \
         the mined rules with exemplars, not a stub",
        style.len()
    );
}
