//! a5 (resolvability): generate + sync-check the per-code `docs/errors/<CODE>.md`
//! pages from `registry::CODES`, so every diagnostic's `doc_url`
//! (`sigil://errors/<CODE>`) resolves to a real committed page by path
//! convention (`docs/errors/<CODE>.md`).
//!
//! Pages are GENERATED, never hand-edited — the registry is the single source
//! of truth (C1). `diagnostic_doc_pages_match_registry` fails on any content
//! drift, a missing page, or an orphan page (a `.md` with no live code, C2),
//! forcing a deliberate regen:
//!   `SIGIL_REGEN_DOC_PAGES=1 cargo test -p sigil-compiler --test diagnostic_doc_pages`
//!
//! This is distinct from the hand-curated `docs/ERROR-CODES.md` narrative —
//! different role, not regenerated here.

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use sigil_compiler::diagnostics::registry;

fn docs_errors_dir() -> PathBuf {
    // tests run with CWD = crate dir (crates/sigil-compiler); repo root is two up.
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("../../docs/errors");
    p
}

/// One page's exact bytes — registry-derived content ONLY (code, title,
/// category, default_hint, doc_url). Nothing invented, so the sync check is
/// exact and there is nothing to hallucinate.
fn render_page(entry: &registry::CodeEntry) -> String {
    let code = entry.code.as_str();
    format!(
        "# {code} — {title}\n\
         \n\
         - **Category:** {category:?}\n\
         - **doc_url:** `sigil://errors/{code}`\n\
         \n\
         {hint}\n\
         \n\
         ---\n\
         \n\
         _Generated from `crates/sigil-compiler/src/diagnostics/registry.rs` — do not edit by hand.\n\
         Regenerate: `SIGIL_REGEN_DOC_PAGES=1 cargo test -p sigil-compiler --test diagnostic_doc_pages`._\n",
        code = code,
        title = entry.title,
        category = entry.category,
        hint = entry.default_hint,
    )
}

/// The index, grouped by category (deterministic: sorted by category name then
/// code) so the file is stable across runs.
fn render_index() -> String {
    let mut entries: Vec<&registry::CodeEntry> = registry::CODES.iter().collect();
    entries.sort_by(|a, b| {
        format!("{:?}", a.category)
            .cmp(&format!("{:?}", b.category))
            .then_with(|| a.code.as_str().cmp(b.code.as_str()))
    });
    let mut out = String::new();
    out.push_str("# SIGIL diagnostic codes\n\n");
    out.push_str(
        "Generated from `crates/sigil-compiler/src/diagnostics/registry.rs` — do not edit by hand.\n\
         Regenerate: `SIGIL_REGEN_DOC_PAGES=1 cargo test -p sigil-compiler --test diagnostic_doc_pages`.\n\n",
    );
    let mut current_cat = String::new();
    for e in entries {
        let cat = format!("{:?}", e.category);
        if cat != current_cat {
            out.push_str(&format!("## {cat}\n\n"));
            current_cat = cat;
        }
        out.push_str(&format!(
            "- [{code}]({code}.md) — {title}\n",
            code = e.code.as_str(),
            title = e.title
        ));
    }
    out
}

#[test]
fn diagnostic_doc_pages_match_registry() {
    let dir = docs_errors_dir();

    if std::env::var_os("SIGIL_REGEN_DOC_PAGES").is_some() {
        fs::create_dir_all(&dir).expect("create docs/errors dir");
        // Drop stale .md first so a removed code's page can't linger.
        if let Ok(rd) = fs::read_dir(&dir) {
            for ent in rd.flatten() {
                let p = ent.path();
                if p.extension().and_then(|s| s.to_str()) == Some("md") {
                    let _ = fs::remove_file(p);
                }
            }
        }
        for entry in registry::CODES {
            let path = dir.join(format!("{}.md", entry.code.as_str()));
            fs::write(&path, render_page(entry)).expect("write code page");
        }
        fs::write(dir.join("README.md"), render_index()).expect("write index");
        return;
    }

    let mut problems: Vec<String> = Vec::new();
    let mut expected: BTreeSet<String> = BTreeSet::new();

    for entry in registry::CODES {
        let name = format!("{}.md", entry.code.as_str());
        expected.insert(name.clone());
        match fs::read_to_string(dir.join(&name)) {
            Ok(actual) if actual == render_page(entry) => {}
            Ok(_) => problems.push(format!("CONTENT DRIFT {name}")),
            Err(_) => problems.push(format!("MISSING {name}")),
        }
    }

    expected.insert("README.md".to_owned());
    match fs::read_to_string(dir.join("README.md")) {
        Ok(actual) if actual == render_index() => {}
        Ok(_) => problems.push("CONTENT DRIFT README.md".to_owned()),
        Err(_) => problems.push("MISSING README.md".to_owned()),
    }

    // Orphans: a committed .md with no corresponding live code (C2).
    match fs::read_dir(&dir) {
        Ok(rd) => {
            for ent in rd.flatten() {
                let p = ent.path();
                if p.extension().and_then(|s| s.to_str()) == Some("md") {
                    let fname = p
                        .file_name()
                        .unwrap_or_default()
                        .to_string_lossy()
                        .into_owned();
                    if !expected.contains(&fname) {
                        problems.push(format!("ORPHAN {fname}"));
                    }
                }
            }
        }
        Err(e) => problems.push(format!("docs/errors unreadable at {} ({e})", dir.display())),
    }

    problems.sort();
    assert!(
        problems.is_empty(),
        "docs/errors/ is out of sync with registry::CODES:\n  {}\n\n\
         Regenerate with: SIGIL_REGEN_DOC_PAGES=1 cargo test -p sigil-compiler \
         --test diagnostic_doc_pages",
        problems.join("\n  ")
    );
}

#[test]
fn render_page_includes_every_registry_field() {
    // Teeth: the page must carry each field, so an empty/dropped field is caught.
    let e = &registry::CODES[0];
    let page = render_page(e);
    assert!(page.contains(e.code.as_str()), "page missing code");
    assert!(page.contains(e.title), "page missing title");
    assert!(page.contains(e.default_hint), "page missing default_hint");
    assert!(
        page.contains(&format!("sigil://errors/{}", e.code.as_str())),
        "page missing doc_url"
    );
}
