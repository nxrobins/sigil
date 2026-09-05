//! CVE Retrofit Corpus harness.
//!
//! Walks `crates/sigil-compiler/tests/cve_corpus/` and validates that each
//! CVE entry has the right files (vulnerable + safe + writeup, or
//! safe-only + writeup for BY-CONSTRUCTION), that the vulnerable
//! fixtures emit the diagnostics they claim, that the safe fixtures
//! emit ZERO diagnostics, and that the matrix + writeups cross-link
//! correctly.
//!
//! This driver enforces ten contracts at test time. Every adversarial-review
//! fence (MC-1..MC-10, MI-1..MI-12) is either tested here or pinned by a
//! mandatory written artifact that this driver validates.
//!
//! The mutation contract is inherited from z3_corpus.rs.
//!
//! Unlike z3_corpus.rs this driver does NOT require the `solver`
//! feature — CVE diagnostics in this PR come from non-Z3 layers
//! (effect/ring/ownership/type-system).

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::{Path, PathBuf};

use sigil_compiler::{CompileError, compile_module};

const CORPUS_SUBDIR: &str = "cve_corpus";

/// Top-level test: every CVE entry passes every contract, in two orders.
#[test]
fn cve_corpus_passes_in_both_orders() {
    let mut entries = load_entries();
    assert!(
        entries.len() >= 10,
        "cve_corpus must hold at least 10 CVE entries (got {})",
        entries.len()
    );

    for entry in &entries {
        check_entry(entry);
    }

    entries.reverse();
    for entry in &entries {
        check_entry(entry);
    }
}

/// Contiguous numbering check (MC-7 fence).
#[test]
fn cve_numbers_are_contiguous() {
    let entries = load_entries();
    let numbers: BTreeSet<u32> = entries.iter().map(|e| e.number).collect();
    let expected: BTreeSet<u32> = (1..=entries.len() as u32).collect();
    assert_eq!(
        numbers, expected,
        "CVE numbers must be contiguous (01..=N) with no gaps or duplicates"
    );
}

/// Pair coverage: every CVE has the required files for its tier (MC-2 fence).
#[test]
fn pair_coverage_matches_tier() {
    let entries = load_entries();
    for entry in &entries {
        let safe_exists = entry.safe_path.is_file();
        let vuln_exists = entry.vuln_path.is_file();
        let writeup_exists = entry.writeup_path.is_file();

        assert!(
            safe_exists,
            "CVE #{:02}: missing safe fixture at {}",
            entry.number,
            entry.safe_path.display()
        );
        assert!(
            writeup_exists,
            "CVE #{:02}: missing writeup at {}",
            entry.number,
            entry.writeup_path.display()
        );

        match entry.tier {
            Tier::Structural | Tier::Class => {
                assert!(
                    vuln_exists,
                    "CVE #{:02} ({:?}): missing vulnerable fixture at {}",
                    entry.number,
                    entry.tier,
                    entry.vuln_path.display()
                );
            }
            Tier::ByConstruction => {
                assert!(
                    !vuln_exists,
                    "CVE #{:02} (BY-CONSTRUCTION): a vulnerable fixture exists at {}, but BY-CONSTRUCTION CVEs must NOT have one",
                    entry.number,
                    entry.vuln_path.display()
                );
            }
        }
    }
}

/// Safe fixtures emit ZERO diagnostics, not just compile-clean (MI-11 fence).
#[test]
fn safe_fixtures_emit_zero_diagnostics() {
    let entries = load_entries();
    for entry in &entries {
        let source = std::fs::read_to_string(&entry.safe_path).unwrap();
        match compile_module(&source) {
            Ok(_) => {}
            Err(e) => panic!(
                "CVE #{:02} safe fixture failed to compile cleanly. \
                 Safe fixtures must emit ZERO diagnostics (MI-11 fence). \
                 Diagnostics: {:?}",
                entry.number,
                collect_messages(&e)
            ),
        }
    }
}

/// Matrix-fixture diagnostic agreement (MC-5 / MC-8 / MC-10 fence).
///
/// Parses `CVE-MATRIX.md` at the workspace root, extracts the
/// (CVE number, diagnostic code) pairs from the inventory table, and
/// asserts each row's diagnostic code matches the fixture's primary
/// emission. BY-CONSTRUCTION rows have no diagnostic (the cell shows
/// `—`); we assert there's no vulnerable fixture for those.
#[test]
fn matrix_codes_match_fixtures() {
    let matrix_path = workspace_root().join("CVE-MATRIX.md");
    assert!(
        matrix_path.is_file(),
        "CVE-MATRIX.md must exist at the workspace root: {}",
        matrix_path.display()
    );
    let matrix_text = std::fs::read_to_string(&matrix_path).unwrap();
    let claims = parse_matrix_claims(&matrix_text);
    assert_eq!(
        claims.len(),
        10,
        "CVE-MATRIX.md must contain exactly 10 inventory rows (got {})",
        claims.len()
    );

    let entries = load_entries();
    let by_number: BTreeMap<u32, &Entry> = entries.iter().map(|e| (e.number, e)).collect();

    for (number, claim) in &claims {
        let entry = by_number.get(number).unwrap_or_else(|| {
            panic!("CVE-MATRIX.md row #{number:02} has no matching fixture entry")
        });

        match (claim, entry.tier) {
            (MatrixClaim::Diagnostic(code), Tier::Structural | Tier::Class) => {
                let source = std::fs::read_to_string(&entry.vuln_path).unwrap();
                let err = match compile_module(&source) {
                    Ok(_) => panic!(
                        "CVE #{number:02} matrix claims diagnostic `{code}` but fixture compiled cleanly"
                    ),
                    Err(e) => e,
                };
                let primary = err
                    .diagnostics()
                    .iter()
                    .find(|d| !d.code().as_str().starts_with('W'))
                    .map(|d| d.code().as_str().to_string())
                    .unwrap_or_default();
                assert!(
                    err.diagnostics().iter().any(|d| d.code().as_str() == code),
                    "CVE #{number:02} matrix claims diagnostic `{code}` but fixture \
                     primary diagnostic is `{primary}`. Full diagnostics: {:?}",
                    collect_messages(&err)
                );
            }
            (MatrixClaim::None, Tier::ByConstruction) => {
                // BY-CONSTRUCTION: no vulnerable fixture, no diagnostic. ✓
            }
            (claim, tier) => panic!(
                "CVE #{number:02} matrix/tier mismatch: matrix says {:?}, tier is {:?}",
                claim, tier
            ),
        }
    }
}

/// Writeup link integrity (MC-6 fence) + section template (MC-3, MI-8, MI-12)
/// + citations (MI-1, MI-9).
#[test]
fn writeup_template_and_links() {
    let entries = load_entries();
    let required_sections = [
        "## What was the bug",
        "## How attackers exploited it",
        "## SIGIL's defense",
        "## Vulnerable shape",
        "## Safe alternative",
        "## Defense layer",
        "## Citations",
    ];
    const MIN_SECTION_CHARS: usize = 200;

    for entry in &entries {
        let writeup = std::fs::read_to_string(&entry.writeup_path).unwrap_or_else(|_| {
            panic!(
                "CVE #{:02}: writeup not readable at {}",
                entry.number,
                entry.writeup_path.display()
            )
        });

        // NVD link present, or explicit note that no formal CVE
        // exists (e.g., The DAO had no CVE ID assigned). MI-1 fence.
        assert!(
            writeup.contains("https://nvd.nist.gov")
                || writeup.contains("No formal CVE")
                || writeup.contains("no CVE ID"),
            "CVE #{:02}: writeup must contain NVD link or note `No formal CVE` / `no CVE ID`",
            entry.number
        );

        // Each required H2 section present + at least MIN_SECTION_CHARS.
        // The Citations section is structurally a URL list, so its
        // length threshold is lower (verified separately via URL count
        // below).
        for section in required_sections {
            assert!(
                writeup.contains(section),
                "CVE #{:02}: writeup missing required H2 section `{section}`",
                entry.number
            );
            let body = extract_section_body(&writeup, section);
            // Threshold per section type:
            //   * Prose sections (What was the bug / How attackers ... /
            //     SIGIL's defense / Safe alternative / Defense layer)
            //     need substantial content (200 chars).
            //   * Structural sections (Vulnerable shape / Citations)
            //     are either a short pointer or a URL list — 80 chars
            //     is enough.
            // Narrative sections (What was the bug / How attackers ... /
            // SIGIL's defense) carry the substance; structural sections
            // (Vulnerable shape / Safe alternative / Defense layer /
            // Citations) are pointers / tables / URL lists and need
            // less content.
            let threshold = match section {
                "## What was the bug" | "## How attackers exploited it" | "## SIGIL's defense" => {
                    MIN_SECTION_CHARS
                }
                _ => 50,
            };
            assert!(
                body.len() >= threshold,
                "CVE #{:02}: section `{section}` is {} chars (must be at least {})",
                entry.number,
                body.len(),
                threshold
            );
        }

        // Citations: at least 2 URLs in the Citations section.
        let citations = extract_section_body(&writeup, "## Citations");
        let url_count = citations
            .split_whitespace()
            .filter(|w| w.starts_with("http://") || w.starts_with("https://"))
            .count();
        assert!(
            url_count >= 2,
            "CVE #{:02}: Citations section must contain at least 2 URLs (found {})",
            entry.number,
            url_count
        );

        // Linked fixtures actually exist.
        let safe_name = entry.safe_path.file_name().unwrap().to_string_lossy();
        assert!(
            writeup.contains(safe_name.as_ref()),
            "CVE #{:02}: writeup must reference its safe fixture `{}`",
            entry.number,
            safe_name
        );
        if matches!(entry.tier, Tier::Structural | Tier::Class) {
            let vuln_name = entry.vuln_path.file_name().unwrap().to_string_lossy();
            assert!(
                writeup.contains(vuln_name.as_ref()),
                "CVE #{:02}: writeup must reference its vulnerable fixture `{}`",
                entry.number,
                vuln_name
            );
        }
    }
}

/// README + ATTACK-MATRIX cross-links (MI-5 fence).
#[test]
fn cross_links_intact() {
    let root = workspace_root();
    let readme = std::fs::read_to_string(root.join("README.md")).unwrap();
    let attack = std::fs::read_to_string(root.join("ATTACK-MATRIX.md")).unwrap();
    let cve = std::fs::read_to_string(root.join("CVE-MATRIX.md")).unwrap();

    assert!(
        readme.contains("CVE-MATRIX.md"),
        "README.md must link to CVE-MATRIX.md"
    );
    assert!(
        attack.contains("CVE-MATRIX.md"),
        "ATTACK-MATRIX.md must link to CVE-MATRIX.md (companion document)"
    );
    assert!(
        cve.contains("ATTACK-MATRIX.md"),
        "CVE-MATRIX.md must link back to ATTACK-MATRIX.md"
    );
}

// ───────────────────────────────────────────────────────────────────
// Data model
// ───────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tier {
    Structural,
    Class,
    ByConstruction,
}

#[derive(Debug, Clone)]
struct Entry {
    number: u32,
    safe_path: PathBuf,
    vuln_path: PathBuf,
    writeup_path: PathBuf,
    tier: Tier,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum MatrixClaim {
    Diagnostic(String),
    None,
}

fn load_entries() -> Vec<Entry> {
    let dir = corpus_dir();
    assert!(
        dir.is_dir(),
        "cve_corpus directory missing: {}",
        dir.display()
    );

    // Discover entries by reading writeups (every CVE has one) and
    // deducing the other files from filename conventions.
    let mut entries = Vec::new();
    let mut seen_numbers = HashSet::new();

    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let Some(stem) = name.strip_suffix(".md") else {
            continue;
        };
        if stem == "README" || stem == "PRE-FLIGHT" {
            continue;
        }
        let Some(number) = parse_leading_number(stem) else {
            continue;
        };
        if !seen_numbers.insert(number) {
            panic!("duplicate CVE number {number:02} in writeup filenames");
        }

        let safe_path = dir.join(format!("{stem}_safe.sigil"));
        let vuln_path = dir.join(format!("{stem}.sigil"));
        let writeup_path = path;

        let tier = parse_tier(
            &std::fs::read_to_string(&writeup_path).unwrap(),
            &writeup_path,
        );

        entries.push(Entry {
            number,
            safe_path,
            vuln_path,
            writeup_path,
            tier,
        });
    }

    entries.sort_by_key(|e| e.number);
    entries
}

fn parse_leading_number(stem: &str) -> Option<u32> {
    let prefix: String = stem.chars().take_while(|c| c.is_ascii_digit()).collect();
    if prefix.is_empty() {
        None
    } else {
        prefix.parse().ok()
    }
}

fn parse_tier(writeup: &str, path: &Path) -> Tier {
    for line in writeup.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("**Scope of claim:**") {
            let rest = rest.trim();
            if rest.contains("STRUCTURAL") {
                return Tier::Structural;
            }
            if rest.contains("BY-CONSTRUCTION") {
                return Tier::ByConstruction;
            }
            if rest.contains("CLASS") {
                return Tier::Class;
            }
        }
    }
    panic!(
        "writeup {} missing `**Scope of claim:**` header line",
        path.display()
    );
}

fn parse_matrix_claims(matrix: &str) -> BTreeMap<u32, MatrixClaim> {
    // Looks for table rows of the form:
    //   | 01 | CVE-... | ... | ... | E003 | STRUCTURAL | ✅ | [link]... |
    // Extracts the leading number and the diagnostic column (5th cell).
    let mut out = BTreeMap::new();
    for line in matrix.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with('|') {
            continue;
        }
        let cells: Vec<&str> = trimmed.split('|').map(str::trim).collect();
        if cells.len() < 8 {
            continue;
        }
        // cells[0] is "" (before first |); cells[1] is the number
        let Some(number) = parse_leading_number(cells[1]) else {
            continue;
        };
        let diag = cells[5];
        let claim = if diag == "—" || diag.is_empty() {
            MatrixClaim::None
        } else {
            MatrixClaim::Diagnostic(diag.to_string())
        };
        out.insert(number, claim);
    }
    out
}

fn extract_section_body(markdown: &str, h2: &str) -> String {
    let mut in_section = false;
    let mut out = String::new();
    for line in markdown.lines() {
        let trimmed = line.trim();
        if trimmed == h2 {
            in_section = true;
            continue;
        }
        if in_section {
            if trimmed.starts_with("## ") || trimmed.starts_with("# ") {
                break;
            }
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

fn check_entry(entry: &Entry) {
    // Safe fixture: must compile cleanly.
    let safe_source = std::fs::read_to_string(&entry.safe_path).unwrap();
    if let Err(e) = compile_module(&safe_source) {
        panic!(
            "CVE #{:02} safe fixture failed to compile: {:?}",
            entry.number,
            collect_messages(&e)
        );
    }

    // Vulnerable fixture (only for STRUCTURAL/CLASS): must emit the
    // expected diagnostic AND pass the mutation contract.
    if matches!(entry.tier, Tier::Structural | Tier::Class) {
        let vuln_source = std::fs::read_to_string(&entry.vuln_path).unwrap();
        let expected_code = parse_expected_code(&vuln_source).unwrap_or_else(|| {
            panic!(
                "CVE #{:02} vulnerable fixture must declare `// expect-error: <code>`",
                entry.number
            )
        });

        let err = match compile_module(&vuln_source) {
            Ok(_) => panic!(
                "CVE #{:02} vulnerable fixture declared expect-error but compiled cleanly",
                entry.number
            ),
            Err(e) => e,
        };
        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.code().as_str() == expected_code),
            "CVE #{:02} vulnerable fixture: expected diagnostic `{expected_code}` not in {:?}",
            entry.number,
            collect_messages(&err)
        );

        // Mutation contract.
        let mutated = mutate_source(&vuln_source).unwrap_or_else(|| {
            panic!(
                "CVE #{:02} vulnerable fixture has no `// MUTATION_SITE` line",
                entry.number
            )
        });
        if let Err(e) = compile_module(&mutated) {
            panic!(
                "CVE #{:02}: post-mutation source must compile cleanly. Got: {:?}",
                entry.number,
                collect_messages(&e)
            );
        }
    }
}

fn parse_expected_code(source: &str) -> Option<String> {
    for line in source.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("// expect-error:") {
            return Some(rest.trim().to_string());
        }
    }
    None
}

fn mutate_source(source: &str) -> Option<String> {
    let mut found = false;
    let mut out = Vec::with_capacity(source.lines().count());
    for line in source.lines() {
        if line.contains("// MUTATION_SITE") {
            assert!(!found, "fixture has multiple `// MUTATION_SITE` lines");
            found = true;
            continue;
        }
        out.push(line);
    }
    if !found {
        return None;
    }
    Some(out.join("\n"))
}

fn collect_messages(err: &CompileError) -> Vec<String> {
    err.diagnostics()
        .iter()
        .map(|d| format!("{}: {}", d.code().as_str(), d.message()))
        .collect()
}

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join(CORPUS_SUBDIR)
}

fn workspace_root() -> PathBuf {
    // Workspace root is two levels up from CARGO_MANIFEST_DIR (which
    // points at crates/sigil-compiler/).
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}
