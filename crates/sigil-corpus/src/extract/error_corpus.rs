//! The error-corpus extractor: one `rejection` REFERENCE record per registered
//! diagnostic code, drawn from `sigil_compiler::registry::CODES` (the 269-entry
//! catalog). `intent` is the code's title; `reasoning` is the code's
//! documentation prose from `docs/ERROR-CODES.md` (richer than the registry's
//! one-line hint), falling back to the hint when a code has no doc section —
//! both verbatim substrings of their provenance, so grounded by construction
//! (ET-C3).
//!
//! These are `Unvalidated` reference records (counted in their own manifest
//! bucket, never silently dropped). The compiler-VALIDATED negatives for these
//! codes are produced by the `test_fixture` extractor (one per fixture file);
//! re-attaching the same fixtures here would only duplicate `output`.

use sigil_compiler::registry::{CODES, Category, CodeEntry};

use super::{ExtractCtx, Extractor, RawRecord, ValidationIntent};
use std::collections::BTreeMap;

use crate::schema::{
    Context, Difficulty, Kind, MAX_PROSE_BYTES, NegativeExample, Record, SCHEMA_VERSION, Validated,
    ValidationKind,
};

const NO_FIXTURE: &str = "no triggering fixture (reference record)";
const REGISTRY_PATH: &str = "crates/sigil-compiler/src/diagnostics/registry.rs";
const ERROR_CODES_MD: &str = "docs/ERROR-CODES.md";

pub struct ErrorCorpus;

impl Extractor for ErrorCorpus {
    fn name(&self) -> &'static str {
        "error_corpus"
    }

    fn extract(&self, ctx: &ExtractCtx) -> anyhow::Result<Vec<RawRecord>> {
        // The per-code documentation prose from ERROR-CODES.md, joined to each
        // record's `reasoning` (richer than the registry's one-line hint). A
        // missing file just means we fall back to the hint.
        let md =
            std::fs::read_to_string(ctx.workspace_root.join(ERROR_CODES_MD)).unwrap_or_default();
        let prose: BTreeMap<String, String> = parse_error_codes_md(&md);

        // Sort by code so the proposal order is stable regardless of the
        // registry's source order (ET-C5 determinism).
        let mut entries: Vec<&CodeEntry> = CODES.iter().collect();
        entries.sort_by(|a, b| a.code.as_str().cmp(b.code.as_str()));

        let mut out = Vec::with_capacity(entries.len());
        for e in entries {
            let code = e.code.as_str().to_string();
            let title = e.title.to_string();
            let hint = e.default_hint.to_string();
            // reasoning = ERROR-CODES.md prose if present, else the registry
            // hint. provenance carries the FULL text so a truncated reasoning
            // is still a verbatim substring (ET-C3 grounding).
            let doc = prose.get(&code).cloned().unwrap_or_else(|| hint.clone());
            let reasoning_text = truncate(&doc, MAX_PROSE_BYTES);
            let provenance = format!("{title}\n{doc}");

            let record = Record {
                id: format!("error_corpus:{code}"),
                kind: Kind::Rejection,
                intent: title.clone(),
                context: Context::default(),
                output: String::new(),
                reasoning: if reasoning_text.is_empty() {
                    None
                } else {
                    Some(reasoning_text)
                },
                tags: vec![
                    category_tag(e.category).to_string(),
                    "error-reference".to_string(),
                ],
                difficulty: Difficulty::Medium,
                pr: None,
                negative_examples: vec![NegativeExample {
                    code: code.clone(),
                    error: title,
                    explanation: hint,
                }],
                source_path: REGISTRY_PATH.to_string(),
                git_sha: ctx.git_sha.clone(),
                span: None,
                validated: Validated {
                    ok: false,
                    how: ValidationKind::Unvalidated {
                        reason: NO_FIXTURE.to_string(),
                    },
                },
                extractor: "error_corpus".to_string(),
                schema_version: SCHEMA_VERSION.to_string(),
            };

            out.push(RawRecord {
                record,
                intent: ValidationIntent::Reference {
                    reason: NO_FIXTURE.to_string(),
                },
                name_for_compile: String::new(),
                provenance,
            });
        }
        Ok(out)
    }
}

/// Parse `docs/ERROR-CODES.md` into a `code → prose` map. Each `### <CODE> — …`
/// heading starts a section whose body (the lines up to the next heading) is the
/// documentation prose, blank lines dropped and joined with spaces.
fn parse_error_codes_md(md: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let mut current: Option<String> = None;
    let mut buf: Vec<&str> = Vec::new();
    for line in md.lines() {
        if let Some(rest) = line.strip_prefix("### ") {
            if let Some(code) = current.take() {
                out.insert(code, join_prose(&buf));
            }
            buf.clear();
            let code = rest.split_whitespace().next().unwrap_or_default();
            current = if crate::validate::is_registry_code(code) {
                Some(code.to_string())
            } else {
                None
            };
        } else if line.starts_with("## ") || line.starts_with("# ") {
            if let Some(code) = current.take() {
                out.insert(code, join_prose(&buf));
            }
            buf.clear();
        } else if current.is_some() {
            buf.push(line);
        }
    }
    if let Some(code) = current.take() {
        out.insert(code, join_prose(&buf));
    }
    out
}

fn join_prose(lines: &[&str]) -> String {
    lines
        .iter()
        .map(|l| l.trim())
        .filter(|l| !l.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
}

/// Truncate to ≤ `max` bytes at a char boundary; a prefix stays a substring of
/// its provenance (ET-C3).
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

/// TOTAL `Category → tag` map — no `_` arm, so a new `Category` variant fails to
/// compile here (ET-C9 drift-lock).
fn category_tag(c: Category) -> &'static str {
    match c {
        Category::Lexer => "lexer",
        Category::Parser => "parser",
        Category::NameResolution => "name-resolution",
        Category::TypeCheck => "type-check",
        Category::Ownership => "ownership",
        Category::Effect => "effect",
        Category::Ring => "ring",
        Category::Capability => "capability",
        Category::Ffi => "ffi",
        Category::SourceLimit => "source-limit",
        Category::ModuleSet => "module-set",
        Category::Codegen => "codegen",
        Category::Internal => "internal",
    }
}
