//! The test-fixture extractor (standalone `.sigil` fixtures): the negative
//! "secret weapon" plus the positive compile fixtures.
//!
//! Each fixture's disposition is decided by the COMPILER, never the
//! `// expect-error:` header (ET-C2 — the headers are mostly free-text). A
//! fixture from an error directory must compile to an error, and the emitted
//! record's `code` is the first registry code the compiler produces; a positive
//! fixture must compile clean. Mismatches are dropped and counted (ET-C1).
//!
//! Scope: only the NON-solver directories. Capability fixtures
//! (`z3_corpus`/`cve_corpus`) need the Z3 solver to reject; under this crate's
//! `default-features = false` (no solver) build they would compile clean and be
//! mislabeled as positives — so they are deferred to a solver-enabled pass, not
//! laundered into the corpus here.

use std::path::Path;

use super::{ExtractCtx, Extractor, RawRecord, ValidationIntent};
use crate::schema::{
    ByteSpan, Context, Difficulty, Kind, MAX_PROSE_BYTES, Record, SCHEMA_VERSION, Validated,
    ValidationKind,
};

/// `(directory, expect_error)`. Error dirs yield negatives; positive dirs yield
/// positives. The header is a description only.
const FIXTURE_DIRS: &[(&str, bool)] = &[
    ("tests/reject", true),
    ("crates/sigil-compiler/tests/fixtures", true),
    ("tests/compile", false),
    ("tests/runtime", false),
];

pub struct TestFixture;

impl Extractor for TestFixture {
    fn name(&self) -> &'static str {
        "test_fixture"
    }

    fn extract(&self, ctx: &ExtractCtx) -> anyhow::Result<Vec<RawRecord>> {
        let root = &ctx.workspace_root;
        let mut out = Vec::new();
        for (dir, expect_error) in FIXTURE_DIRS {
            for rel in sigil_files(root, dir)? {
                let src = std::fs::read_to_string(root.join(&rel))
                    .map_err(|e| anyhow::anyhow!("reading {rel}: {e}"))?;
                let header = first_comment_line(&src);
                let stem = Path::new(&rel)
                    .file_stem()
                    .and_then(|s| s.to_str())
                    .unwrap_or("fixture")
                    .to_string();
                let intent = truncate(&header, MAX_PROSE_BYTES);

                let record = Record {
                    id: format!("test_fixture:{}", slug(&rel)),
                    // Provisional; the gate flips error fixtures to Rejection.
                    kind: if *expect_error {
                        Kind::Rejection
                    } else {
                        Kind::Implementation
                    },
                    intent: intent.clone(),
                    context: Context::default(),
                    output: src.clone(),
                    reasoning: None,
                    tags: vec!["test-fixture".to_string(), dir_tag(dir).to_string()],
                    difficulty: Difficulty::Easy,
                    pr: None,
                    negative_examples: Vec::new(),
                    source_path: rel.clone(),
                    git_sha: ctx.git_sha.clone(),
                    span: Some(ByteSpan {
                        start: 0,
                        end: src.len(),
                    }),
                    validated: Validated {
                        ok: false,
                        how: ValidationKind::Unvalidated {
                            reason: "pending fixture validation".to_string(),
                        },
                    },
                    extractor: "test_fixture".to_string(),
                    schema_version: SCHEMA_VERSION.to_string(),
                };
                out.push(RawRecord {
                    record,
                    intent: ValidationIntent::Fixture {
                        expect_error: *expect_error,
                    },
                    name_for_compile: stem,
                    // The header is the only prose; intent must be a substring.
                    provenance: header,
                });
            }
        }
        Ok(out)
    }
}

/// The first `//` comment line's text (markers stripped), or empty. The fixture
/// header (`// expect-error: …` or `// CODE: …`) — a description, never trusted
/// for the code.
fn first_comment_line(src: &str) -> String {
    for line in src.lines() {
        let t = line.trim_start();
        if t.starts_with("//") {
            return t.trim_start_matches('/').trim().to_string();
        }
        if !t.is_empty() {
            break;
        }
    }
    String::new()
}

fn dir_tag(dir: &str) -> &'static str {
    match dir {
        "tests/reject" => "reject",
        "crates/sigil-compiler/tests/fixtures" => "diagnostic-fixture",
        "tests/compile" => "compile",
        "tests/runtime" => "runtime",
        _ => "fixture",
    }
}

fn sigil_files(root: &Path, dir: &str) -> anyhow::Result<Vec<String>> {
    let path = root.join(dir);
    let mut files = Vec::new();
    let entries = match std::fs::read_dir(&path) {
        Ok(e) => e,
        // A missing fixture dir is not an error — just no records from it.
        Err(_) => return Ok(files),
    };
    for entry in entries {
        let p = entry?.path();
        if p.extension().and_then(|e| e.to_str()) == Some("sigil")
            && let Some(name) = p.file_name().and_then(|n| n.to_str())
        {
            files.push(format!("{dir}/{name}"));
        }
    }
    files.sort();
    Ok(files)
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() <= max {
        return s.to_string();
    }
    let mut end = max;
    while end > 0 && !s.is_char_boundary(end) {
        end -= 1;
    }
    s[..end].to_string()
}

fn slug(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut prev_dash = false;
    for c in s.chars() {
        if c.is_ascii_alphanumeric() {
            out.push(c.to_ascii_lowercase());
            prev_dash = false;
        } else if !prev_dash {
            out.push('-');
            prev_dash = true;
        }
    }
    out.trim_matches('-').to_string()
}
