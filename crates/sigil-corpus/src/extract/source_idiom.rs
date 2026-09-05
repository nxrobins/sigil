//! The source-idiom extractor: function- and type-level positive examples from
//! the self-hosted compiler (`selfhost/*.sigil`) and the stdlib
//! (`stdlib/sigil/*.sigil`).
//!
//! Each file is parsed for structure (the parser proves every file parses
//! clean), and one record is emitted per top-level `fn`, `impl` method,
//! `record`, and `enum`. The `output` is the exact source slice; `intent`/
//! `reasoning` are mined from the immediately-preceding `///`/`//` doc block
//! (bounded backward scan, ET-C10) and so are grounded by construction (ET-C3).
//!
//! Validation is at the level of a whole compilation UNIT (AG-C1): a stdlib file
//! compiles clean standalone, and the selfhost trio compiles clean only when
//! lexer+parser+typecheck are inlined as one module (the way the differential
//! harness composes them). A record ships iff its unit compiles; otherwise it is
//! dropped and counted (ET-C1/ET-C6).

use std::path::Path;
use std::rc::Rc;

use sigil_compiler::ast::{Item, Module};
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;

use super::{ExtractCtx, Extractor, RawRecord, ValidationIntent};
use crate::schema::{
    Context, Difficulty, Kind, MAX_DOC_SCAN_LINES, MAX_PROSE_BYTES, Record, SCHEMA_VERSION,
    Validated, ValidationKind,
};

/// The selfhost trio, in inline order. Records from these files are witnessed by
/// one inlined compile (`SELFHOST_UNIT`).
const SELFHOST_FILES: &[&str] = &[
    "selfhost/lexer.sigil",
    "selfhost/parser.sigil",
    "selfhost/typecheck.sigil",
];
const SELFHOST_UNIT: &str = "selfhost-trio";
const INTENT_CAP: usize = 280;

pub struct SourceIdiom;

impl Extractor for SourceIdiom {
    fn name(&self) -> &'static str {
        "source_idiom"
    }

    fn extract(&self, ctx: &ExtractCtx) -> anyhow::Result<Vec<RawRecord>> {
        let root = &ctx.workspace_root;
        let mut out = Vec::new();
        let mut seen: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();

        // The selfhost trio: one shared validation unit (the inlined module).
        let trio = Rc::new(inlined_trio(root)?);
        for rel in SELFHOST_FILES {
            let src = read(root, rel)?;
            let unit = ValidationIntent::PositiveUnit {
                unit_key: SELFHOST_UNIT.to_string(),
                unit_src: Rc::clone(&trio),
            };
            file_records(
                rel,
                &src,
                &ctx.git_sha,
                Kind::Implementation,
                "self-hosting",
                &mut seen,
                &mut out,
                &unit,
            );
        }

        // The stdlib: each file is its own validation unit.
        for rel in stdlib_files(root)? {
            let src = read(root, &rel)?;
            let unit = ValidationIntent::PositiveUnit {
                unit_key: format!("stdlib:{rel}"),
                unit_src: Rc::new(src.clone()),
            };
            file_records(
                &rel,
                &src,
                &ctx.git_sha,
                Kind::Idiom,
                "stdlib",
                &mut seen,
                &mut out,
                &unit,
            );
        }

        Ok(out)
    }
}

/// Parse `src` for structure and push one `RawRecord` per fn / impl-method /
/// record / enum, all sharing `unit` as their validation witness.
#[allow(clippy::too_many_arguments)]
fn file_records(
    rel: &str,
    src: &str,
    git_sha: &str,
    kind: Kind,
    domain: &str,
    seen: &mut std::collections::BTreeMap<String, usize>,
    out: &mut Vec<RawRecord>,
    unit: &ValidationIntent,
) {
    let sf = SourceFile::new(rel, src);
    let (program, _diags) = parser::parse(&sf);
    for module in &program.modules {
        let ctx = module_context(module);
        for item in &module.items {
            for (name, span) in item_examples(item) {
                push_record(
                    rel, src, git_sha, kind, domain, module, &ctx, &name, span, seen, out, unit,
                );
            }
        }
    }
}

/// The (name, span) pairs a top-level item contributes. A fn/record/enum is one;
/// an impl block is one per method (name-qualified by the impl type).
fn item_examples(item: &Item) -> Vec<(String, sigil_compiler::span::Span)> {
    match item {
        Item::FnDef(f) => vec![(f.name.clone(), f.span)],
        Item::RecordDef(_) | Item::EnumDef(_) => match item.name() {
            Some(n) => vec![(n.to_string(), item.span())],
            None => Vec::new(),
        },
        Item::ImplDef(im) => im
            .methods
            .iter()
            .map(|m| (format!("{}::{}", im.type_name, m.name), m.span))
            .collect(),
        _ => Vec::new(),
    }
}

#[allow(clippy::too_many_arguments)]
fn push_record(
    rel: &str,
    src: &str,
    git_sha: &str,
    kind: Kind,
    domain: &str,
    module: &Module,
    ctx: &Context,
    name: &str,
    span: sigil_compiler::span::Span,
    seen: &mut std::collections::BTreeMap<String, usize>,
    out: &mut Vec<RawRecord>,
    unit: &ValidationIntent,
) {
    let (start, end) = (span.start, span.end);
    if start >= end || end > src.len() {
        return;
    }
    let output = src[start..end].to_string();

    let doc = harvest_doc(src, start);
    let provenance = doc.clone();
    let intent = truncate(&doc, INTENT_CAP);

    let base = format!("source_idiom:{}:{}", slug(rel), slug(name));
    let ord = seen.entry(base.clone()).or_insert(0);
    let id = if *ord == 0 {
        base.clone()
    } else {
        format!("{base}#{ord}")
    };
    *ord += 1;

    let record = Record {
        id,
        kind,
        intent,
        context: ctx.clone(),
        output: output.clone(),
        reasoning: None,
        tags: vec![domain.to_string(), module.name.clone()],
        difficulty: difficulty(&output),
        pr: None,
        negative_examples: Vec::new(),
        source_path: rel.to_string(),
        git_sha: git_sha.to_string(),
        span: Some(crate::schema::ByteSpan { start, end }),
        validated: Validated {
            ok: false,
            how: ValidationKind::Unvalidated {
                reason: "pending unit validation".to_string(),
            },
        },
        extractor: "source_idiom".to_string(),
        schema_version: SCHEMA_VERSION.to_string(),
    };
    out.push(RawRecord {
        record,
        intent: clone_intent(unit),
        name_for_compile: String::new(),
        provenance,
    });
}

/// `ValidationIntent` is not `Clone` (it carries an `Rc`), so reproduce the unit
/// intent explicitly for each record sharing it.
fn clone_intent(unit: &ValidationIntent) -> ValidationIntent {
    match unit {
        ValidationIntent::PositiveUnit { unit_key, unit_src } => ValidationIntent::PositiveUnit {
            unit_key: unit_key.clone(),
            unit_src: Rc::clone(unit_src),
        },
        // source_idiom only ever uses PositiveUnit.
        _ => ValidationIntent::Reference {
            reason: "unexpected".to_string(),
        },
    }
}

/// Module-level context: `use` imports and the names of declared types.
fn module_context(m: &Module) -> Context {
    let mut imports = Vec::new();
    let mut types = Vec::new();
    for it in &m.items {
        match it {
            Item::UseDecl(u) => imports.push(u.path.display_name()),
            Item::RecordDef(_) | Item::EnumDef(_) | Item::CapTypeDef(_) | Item::TraitDef(_) => {
                if let Some(n) = it.name() {
                    types.push(n.to_string());
                }
            }
            _ => {}
        }
    }
    imports.sort();
    imports.dedup();
    types.sort();
    types.dedup();
    Context {
        imports,
        types_in_scope: types,
        constraints: Vec::new(),
    }
}

/// Bounded backward scan for the doc block immediately above `start` (the byte
/// offset of `pub`/`fn`/`record`/`enum`, which excludes comments — they are
/// lexer trivia). Returns the comment text, markers stripped, space-joined.
fn harvest_doc(src: &str, start: usize) -> String {
    let head = &src[..start];
    let segments: Vec<&str> = head.split('\n').collect();
    let mut collected: Vec<&str> = Vec::new();
    // The last segment is the item line's own indentation — skip it.
    let mut idx = segments.len().saturating_sub(1);
    while idx > 0 {
        idx -= 1;
        let trimmed = segments[idx].trim_start();
        if trimmed.starts_with("//") {
            collected.push(trimmed.trim_start_matches('/').trim_start());
            if collected.len() >= MAX_DOC_SCAN_LINES {
                break;
            }
        } else {
            break;
        }
    }
    collected.reverse();
    collected.join(" ").trim().to_string()
}

fn difficulty(output: &str) -> Difficulty {
    match output.lines().count() {
        0..=8 => Difficulty::Easy,
        9..=30 => Difficulty::Medium,
        _ => Difficulty::Hard,
    }
}

/// Truncate to at most `max` bytes at a char boundary. A prefix of a string is
/// still a substring of its provenance, so grounding (ET-C3) holds.
fn truncate(s: &str, max: usize) -> String {
    let cap = max.min(MAX_PROSE_BYTES);
    if s.len() <= cap {
        return s.to_string();
    }
    let mut end = cap;
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

fn read(root: &Path, rel: &str) -> anyhow::Result<String> {
    std::fs::read_to_string(root.join(rel)).map_err(|e| anyhow::anyhow!("reading {rel}: {e}"))
}

/// `selfhost/*.sigil` inlined into one module (their `module …;` lines stripped),
/// matching how the differential harness composes the trio.
fn inlined_trio(root: &Path) -> anyhow::Result<String> {
    let lex = read(root, "selfhost/lexer.sigil")?;
    let par = read(root, "selfhost/parser.sigil")?;
    let tc = read(root, "selfhost/typecheck.sigil")?;
    Ok(format!(
        "module tool;\n{}\n{}\n{}\n",
        lex.replace("\nmodule lexer;\n", "\n"),
        par.replace("\nmodule parser;\n", "\n"),
        tc.replace("\nmodule typecheck;\n", "\n"),
    ))
}

/// `stdlib/sigil/*.sigil` paths relative to the workspace root, sorted.
fn stdlib_files(root: &Path) -> anyhow::Result<Vec<String>> {
    let dir = root.join("stdlib").join("sigil");
    let mut files = Vec::new();
    for entry in
        std::fs::read_dir(&dir).map_err(|e| anyhow::anyhow!("read_dir {}: {e}", dir.display()))?
    {
        let path = entry?.path();
        if path.extension().and_then(|e| e.to_str()) == Some("sigil")
            && let Some(name) = path.file_name().and_then(|n| n.to_str())
        {
            files.push(format!("stdlib/sigil/{name}"));
        }
    }
    files.sort();
    Ok(files)
}
