//! The inline-program extractor: SIGIL programs embedded as Rust string literals
//! in the test harnesses (`crates/**/tests/*.rs` + a few `src` files).
//!
//! The differential and diagnostic harnesses carry the single largest body of
//! compiler-validated SIGIL in the repo — thousands of `module …;` programs as
//! `"…\n…"` / `r#"…"#` literals, each exercising one language feature or one
//! diagnostic. `source_idiom` mines the `.sigil` SOURCE files and `test_fixture`
//! the standalone `.sigil` FIXTURES, but neither sees these inline programs.
//!
//! Each Rust file is parsed with `syn` (which decodes escapes, raw strings, and
//! line-continuations for us); every string literal that PARSES CLEAN as a SIGIL
//! module with ≥1 item is proposed with `ValidationIntent::Classify` — the
//! compiler verdict alone labels it a positive (compiles clean) or a rejection
//! (reproduces a registry diagnostic). Programs that only PARSE-error (non-SIGIL
//! strings, or intentional syntax fixtures — those live as `.sigil` files already)
//! never enter, so no Rust prose is laundered into the corpus. Distinct programs
//! are deduplicated by content (ET-C5 determinism: sorted files, content-derived
//! ids), so a shape repeated across many tests yields exactly one record.

use std::path::Path;

use sigil_compiler::Severity;
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;
use syn::visit::Visit;

use super::{ExtractCtx, Extractor, RawRecord, ValidationIntent};
use crate::schema::{
    Context, Difficulty, Kind, MAX_OUTPUT_BYTES, Record, SCHEMA_VERSION, Validated, ValidationKind,
};

/// The root scanned (RECURSIVELY) for `.rs` files carrying inline SIGIL — every
/// crate's `src` and `tests`, so a new harness or test file is picked up with no
/// config change. `sigil-corpus` itself is skipped (its own test strings would be
/// self-referential) along with build output.
const SCAN_ROOT: &str = "crates";
/// Directory names pruned from the recursive walk.
const SKIP_DIRS: &[&str] = &["target", "sigil-corpus"];

pub struct InlineProgram;

impl Extractor for InlineProgram {
    fn name(&self) -> &'static str {
        "inline_program"
    }

    fn extract(&self, ctx: &ExtractCtx) -> anyhow::Result<Vec<RawRecord>> {
        let root = &ctx.workspace_root;
        let mut out = Vec::new();
        // Dedup by program content: one record per DISTINCT program, first sorted
        // occurrence wins the id, so the output is insertion-order-independent.
        let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();

        for rel in rust_files(root) {
            {
                let content = match std::fs::read_to_string(root.join(&rel)) {
                    Ok(c) => c,
                    Err(_) => continue,
                };
                let Ok(file) = syn::parse_file(&content) else {
                    // A file `syn` cannot parse contributes no records — its inline
                    // programs are simply not mined (never a silent corruption).
                    continue;
                };
                let mut collector = LitCollector { lits: Vec::new() };
                collector.visit_file(&file);
                for prog in collector.lits {
                    if !looks_like_module(&prog) {
                        continue;
                    }
                    if prog.len() > MAX_OUTPUT_BYTES {
                        continue; // the gate would drop it; skip the compile.
                    }
                    if !parses_clean_as_sigil(&prog) {
                        continue; // non-SIGIL string or a parse-error fixture.
                    }
                    if !seen.insert(prog.clone()) {
                        continue; // duplicate program (already proposed once).
                    }
                    out.push(make_record(&rel, &prog, &ctx.git_sha));
                }
            }
        }
        Ok(out)
    }
}

/// Collects every string-literal VALUE in a Rust file (escapes/raw/continuations
/// already decoded by `syn`).
struct LitCollector {
    lits: Vec<String>,
}

impl<'ast> Visit<'ast> for LitCollector {
    fn visit_lit_str(&mut self, node: &'ast syn::LitStr) {
        self.lits.push(node.value());
    }
}

/// Cheap pre-screen: the literal opens with a `module <name>;` declaration. The
/// authoritative SIGIL check is `parses_clean_as_sigil`; this only avoids
/// compiling thousands of unrelated strings.
fn looks_like_module(s: &str) -> bool {
    let t = s.trim_start();
    let Some(rest) = t.strip_prefix("module ") else {
        return false;
    };
    // A module path (ident, optionally dotted) then `;` within a short window.
    let head: String = rest.chars().take(64).collect();
    let Some(semi) = head.find(';') else {
        return false;
    };
    let path = head[..semi].trim();
    !path.is_empty()
        && path
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.')
}

/// True iff `prog` parses as SIGIL with no error-severity parse diagnostic AND at
/// least one module item — i.e. it is confidently a (syntactically valid) SIGIL
/// program, not a Rust string that merely starts with `module `.
fn parses_clean_as_sigil(prog: &str) -> bool {
    let sf = SourceFile::new("<inline>", prog);
    let (program, diags) = parser::parse(&sf);
    if diags.iter().any(|d| d.severity() == Severity::Error) {
        return false;
    }
    program.modules.iter().any(|m| !m.items.is_empty())
}

fn make_record(rel: &str, prog: &str, git_sha: &str) -> RawRecord {
    let id = format!("inline_program:{:016x}", fnv1a(prog));
    let record = Record {
        id,
        // Provisional: the gate flips type-erroring programs to `Rejection`.
        kind: Kind::Implementation,
        // No grounded prose claim — the program is its own evidence. (A later
        // pass can mine the enclosing test name / doc comment for intent.)
        intent: String::new(),
        context: Context::default(),
        output: prog.to_string(),
        reasoning: None,
        tags: vec!["inline-program".to_string(), file_stem(rel)],
        difficulty: difficulty(prog),
        pr: None,
        negative_examples: Vec::new(),
        source_path: rel.to_string(),
        git_sha: git_sha.to_string(),
        span: None,
        validated: Validated {
            ok: false,
            how: ValidationKind::Unvalidated {
                reason: "pending classify".to_string(),
            },
        },
        extractor: "inline_program".to_string(),
        schema_version: SCHEMA_VERSION.to_string(),
    };
    RawRecord {
        record,
        intent: ValidationIntent::Classify,
        name_for_compile: format!("inline_{:016x}", fnv1a(prog)),
        // intent/reasoning are empty, so grounding is vacuous — no provenance blob
        // is needed (the `output` IS the committed evidence, audited by source_path).
        provenance: String::new(),
    }
}

/// A stable, dependency-free content hash (FNV-1a 64-bit) for the record id — so
/// the same program yields the same id across runs and machines (ET-C5).
fn fnv1a(s: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in s.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

fn file_stem(rel: &str) -> String {
    Path::new(rel)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("inline")
        .to_string()
}

fn difficulty(prog: &str) -> Difficulty {
    match prog.lines().count() {
        0..=8 => Difficulty::Easy,
        9..=30 => Difficulty::Medium,
        _ => Difficulty::Hard,
    }
}

/// Every `.rs` file under `crates/` (recursively), relative to the workspace
/// root, SORTED for determinism. Prunes `target/` and the `sigil-corpus` crate.
fn rust_files(root: &Path) -> Vec<String> {
    let mut files = Vec::new();
    walk(&root.join(SCAN_ROOT), root, &mut files);
    files.sort();
    files
}

/// Depth-first directory walk collecting `.rs` paths (relative to `root`).
fn walk(dir: &Path, root: &Path, out: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let p = entry.path();
        let name = p.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if p.is_dir() {
            if !SKIP_DIRS.contains(&name) && !name.starts_with('.') {
                walk(&p, root, out);
            }
        } else if p.extension().and_then(|e| e.to_str()) == Some("rs")
            && let Ok(rel) = p.strip_prefix(root)
            && let Some(rel_str) = rel.to_str()
        {
            // Normalize to forward slashes so `source_path` is stable across OSes.
            out.push(rel_str.replace('\\', "/"));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_prescreen() {
        assert!(looks_like_module("module m; fn f() -> i64 { return 0; }"));
        assert!(looks_like_module("  module demo;\n  fn f() {}"));
        assert!(looks_like_module("module a.b.c; fn f() {}"));
        assert!(!looks_like_module("module level access control"));
        assert!(!looks_like_module("not a module at all"));
        assert!(!looks_like_module("modulary thing; nope"));
    }

    #[test]
    fn sigil_parse_filter() {
        // Real SIGIL parses clean with an item.
        assert!(parses_clean_as_sigil(
            "module m; fn f() -> i64 { return 0; }"
        ));
        // A type error still PARSES clean (the gate classifies it a negative).
        assert!(parses_clean_as_sigil(
            "module m; fn f() -> i64 { return true; }"
        ));
        // English prose that merely starts with `module ` does NOT parse as SIGIL.
        assert!(!parses_clean_as_sigil("module level access control here"));
        // A bare module with no items contributes nothing.
        assert!(!parses_clean_as_sigil("module m;"));
    }

    #[test]
    fn fnv_is_stable_and_distinct() {
        assert_eq!(fnv1a("module m;"), fnv1a("module m;"));
        assert_ne!(fnv1a("module a;"), fnv1a("module b;"));
    }
}
