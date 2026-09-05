//! SOL-XFILE PR1/L1 — multi-file PROJECT translation: resolve a Solidity import closure
//! against an IN-MEMORY file-set and feed the union to the existing flattener + pipeline.
//!
//! THE SECURITY KEYSTONE: untrusted `import` strings NEVER drive filesystem reads.
//! The caller (the CLI, from the trusted `--project-root` argument) enumerates and reads
//! the file-set; this module resolves every import as a PURE MAP LOOKUP over `files` —
//! a path that lexically normalizes outside the root simply is not a key, so traversal
//! is UNREACHABLE, not guarded. Resolution is bounded by dumb caps (files / depth /
//! bytes) and gated by an ASCII charset + a per-segment `..`-floor check BEFORE any
//! lookup. Everything downstream (dup-name gate, C3 linearization, merge, the whole
//! check/desugar/emit pipeline) is the SAME code the single-file path runs — see
//! `flatten::flatten_project` (the ENTRY-MAIN RULE) and `mod.rs::run_pipeline`.

use std::collections::BTreeMap;

use crate::codes;
use crate::{EmittedSigil, FrontendDiag};

use super::parser::{ContractKind, ParsedFile};
use super::{check, desugar, flatten, lexer, parser, run_pipeline};

/// Dumb caps on the resolved import CLOSURE (not the enumerated file-set — the CLI may
/// hand us a whole repo; only what the entry transitively imports is loaded/parsed).
/// The worst real OZ token closure is 29 files at import-depth 5.
pub const MAX_PROJECT_FILES: usize = 64;
pub const MAX_IMPORT_DEPTH: u32 = 16;
/// Total source bytes across the closure (the single-file input cap, applied to the sum).
pub const MAX_CLOSURE_BYTES: usize = crate::limits::MAX_INPUT_BYTES;

/// Translate the multi-file Solidity project rooted at `entry` (a root-relative path that
/// must be a key of `files`). `files` maps `/`-separated root-relative paths → contents.
pub fn translate_solidity_project(
    files: &BTreeMap<String, String>,
    entry: &str,
) -> Result<EmittedSigil, Vec<FrontendDiag>> {
    let (program, cap_mode, entry_key) = resolve_project(files, entry).map_err(|d| vec![d])?;
    run_pipeline(program, cap_mode, &entry_key)
}

/// Closure resolution + gates + union + pinned flatten → the `Program` the shared
/// pipeline consumes (plus the entry's cap-mode + key for the emit source name).
fn resolve_project(
    files: &BTreeMap<String, String>,
    entry: &str,
) -> Result<(parser::Program, bool, String), FrontendDiag> {
    // The entry path passes the SAME charset/floor gate as an import (one rule, no seams).
    let entry_key = normalize_path("", entry).ok_or_else(|| {
        FrontendDiag::new(
            codes::FE476_IMPORT_OR_BASE_SOL,
            format!("entry path `{entry}` is not a plain root-relative path"),
            0..0,
        )
    })?;
    if !files.contains_key(&entry_key) {
        return Err(FrontendDiag::new(
            codes::FE476_IMPORT_OR_BASE_SOL,
            format!("entry file `{entry_key}` is not in the project file-set"),
            0..0,
        ));
    }

    // BFS the import closure from the entry. `order` is the deterministic union order
    // (discovery order: entry first, then each file's imports in source order).
    let mut order: Vec<String> = Vec::new();
    let mut parsed_by_key: BTreeMap<String, ParsedFile> = BTreeMap::new();
    let mut queue: Vec<(String, u32)> = vec![(entry_key.clone(), 0)];
    let mut total_bytes: usize = 0;
    while let Some((key, depth)) = queue.pop() {
        if parsed_by_key.contains_key(&key) {
            continue;
        }
        if depth > MAX_IMPORT_DEPTH {
            return Err(FrontendDiag::new(
                codes::FE402_TOO_LARGE_SOL,
                format!("import depth exceeds {MAX_IMPORT_DEPTH} at `{key}`"),
                0..0,
            ));
        }
        if parsed_by_key.len() >= MAX_PROJECT_FILES {
            return Err(FrontendDiag::new(
                codes::FE402_TOO_LARGE_SOL,
                format!("import closure exceeds {MAX_PROJECT_FILES} files"),
                0..0,
            ));
        }
        let src = files.get(&key).expect("closure keys come from `files`");
        total_bytes = total_bytes.saturating_add(src.len());
        if total_bytes > MAX_CLOSURE_BYTES {
            return Err(FrontendDiag::new(
                codes::FE402_TOO_LARGE_SOL,
                format!("import closure exceeds {MAX_CLOSURE_BYTES} bytes"),
                0..0,
            ));
        }
        // A lex/parse reject in ANY closure file rejects the project (fail-closed — the
        // file may declare contracts the union needs). Prefix the FILE KEY so the diag
        // is attributable (spans are per-file byte offsets, not entry offsets).
        let tag_file =
            |d: FrontendDiag| FrontendDiag::new(d.code, format!("[{key}] {}", d.message), d.span);
        let toks = lexer::lex(src).map_err(tag_file)?;
        let parsed = parser::parse(toks, src.len()).map_err(tag_file)?;

        // Resolve this file's imports (pure lexical normalize + map membership — the
        // ONLY resolution rule). Push in REVERSE source order so the Vec-as-stack pops
        // them in source order (deterministic discovery).
        let dir = parent_dir(&key);
        let mut child_keys: Vec<String> = Vec::with_capacity(parsed.imports.len());
        for (raw, span) in &parsed.imports {
            let child = normalize_path(dir, raw).ok_or_else(|| {
                FrontendDiag::new(
                    codes::FE476_IMPORT_OR_BASE_SOL,
                    format!(
                        "import `{raw}` in `{key}` is not a plain in-root relative path \
                         (allowed: `[A-Za-z0-9_./-]`, no absolute paths, no escape past the root)"
                    ),
                    span.clone(),
                )
            })?;
            if !files.contains_key(&child) {
                return Err(FrontendDiag::new(
                    codes::FE476_IMPORT_OR_BASE_SOL,
                    format!(
                        "import `{raw}` in `{key}` does not resolve to a project file (`{child}`)"
                    ),
                    span.clone(),
                ));
            }
            child_keys.push(child);
        }
        for child in child_keys.into_iter().rev() {
            if !parsed_by_key.contains_key(&child) {
                queue.push((child, depth + 1));
            }
        }

        order.push(key.clone());
        parsed_by_key.insert(key, parsed);
    }

    // Per-file pragma gate (EX-4, file granularity): every CODE-BEARING closure file
    // (one declaring a concrete or abstract contract — the kinds whose members reach the
    // merge) must carry a provably->=0.8 pragma; interface/library-only files are exempt
    // (their members are token-group-skipped at parse — zero code contributed), which is
    // what makes OZ's old `>=0.5/0.6` interface pragmas livable. File granularity is
    // deliberately STRICTER than "linearized files only" (a code-bearing closure file
    // that ends up un-linearized is still gated — fail-closed).
    for key in &order {
        let pf = &parsed_by_key[key];
        let code_bearing = pf
            .contracts
            .iter()
            .any(|c| matches!(c.kind, ContractKind::Concrete | ContractKind::Abstract));
        if !code_bearing {
            continue;
        }
        let ok = pf
            .pragma
            .as_ref()
            .is_some_and(|(body, _)| check::pragma_body_is_0_8(body));
        if !ok {
            return Err(FrontendDiag::new(
                codes::FE411_UNCHECKED_OR_PRAGMA,
                format!(
                    "project file `{key}` declares contract code but its `pragma solidity` \
                     is missing or not provably >= 0.8.0 (checked arithmetic)"
                ),
                0..0,
            ));
        }
    }

    // THE ENTRY-MAIN RULE (EX-1): the translated contract is the entry file's EXACTLY-ONE
    // concrete contract — never inferred from union-wide sink analysis (an imported file's
    // unrelated or entry-deriving concrete contract must not flip FE470 or steal main).
    let entry_parsed = &parsed_by_key[&entry_key];
    let mut entry_concrete = entry_parsed
        .contracts
        .iter()
        .filter(|c| c.kind == ContractKind::Concrete);
    let main_name = match (entry_concrete.next(), entry_concrete.next()) {
        (Some(c), None) => c.name.clone(),
        (None, _) => {
            return Err(FrontendDiag::new(
                codes::FE470_AMBIGUOUS_MAIN_SOL,
                format!("entry file `{entry_key}` declares no concrete contract to translate"),
                0..0,
            ));
        }
        (Some(_), Some(second)) => {
            return Err(FrontendDiag::new(
                codes::FE470_AMBIGUOUS_MAIN_SOL,
                format!(
                    "entry file `{entry_key}` declares more than one concrete contract \
                     (`{}` is the second) — the entry must name exactly one",
                    second.name
                ),
                second.span.clone(),
            ));
        }
    };

    // Cap-mode is the ENTRY file's directive (a translation-unit-wide switch belongs to
    // the deployable, not to a library file deep in the closure).
    let cap_mode = desugar::detect_cap_directive(&files[&entry_key]);
    // The Program pragma is the ENTRY file's (every code-bearing file already passed the
    // per-file gate above, so the single check_pragma downstream re-verifies the entry's).
    let pragma = parsed_by_key[&entry_key].pragma.clone();

    // Union in discovery order (deterministic; flatten's dup-name gate rejects any
    // cross-file contract-name collision before anything else happens).
    let mut contracts = Vec::new();
    for key in &order {
        contracts.append(&mut parsed_by_key.get_mut(key).expect("ordered key").contracts);
    }
    let union = ParsedFile {
        pragma,
        contracts,
        imports: Vec::new(),
    };
    let program = flatten::flatten_project(union, &main_name)?;
    Ok((program, cap_mode, entry_key))
}

/// The directory part of a `/`-separated key (`""` for a root-level file).
fn parent_dir(key: &str) -> &str {
    match key.rfind('/') {
        Some(i) => &key[..i],
        None => "",
    }
}

/// PURE lexical path normalization — the resolver's only path rule (EX-2).
/// Joins `raw` onto `base_dir` (a `./`- or `../`-prefixed raw is relative to the
/// importing file's directory; a bare path is root-relative), then walks segments with a
/// floor check. Returns `None` (→ FE476 at the caller) for: an empty path, any char
/// outside `[A-Za-z0-9_./-]` (rejects `\`, drive letters, URLs, NUL, unicode tricks),
/// an absolute path (leading `/`), an empty segment (`//`), or a `..` that would climb
/// past the project root. NO filesystem access, ever.
fn normalize_path(base_dir: &str, raw: &str) -> Option<String> {
    if raw.is_empty()
        || !raw
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '/' | '-'))
    {
        return None;
    }
    if raw.starts_with('/') {
        return None; // absolute — never resolved
    }
    let relative = raw.starts_with("./") || raw.starts_with("../");
    let mut stack: Vec<&str> = if relative && !base_dir.is_empty() {
        base_dir.split('/').collect()
    } else {
        Vec::new()
    };
    for seg in raw.split('/') {
        match seg {
            "" => return None, // `a//b` or a trailing `/`
            "." => {}
            ".." => {
                // A `..` with nothing to pop would climb past the root → None (FE476).
                stack.pop()?;
            }
            s => stack.push(s),
        }
    }
    if stack.is_empty() {
        return None; // normalized to the root itself, not a file
    }
    Some(stack.join("/"))
}

#[cfg(test)]
mod tests {
    use super::normalize_path;

    #[test]
    fn normalize_path_gates() {
        // In-root joins.
        assert_eq!(normalize_path("", "a.sol").as_deref(), Some("a.sol"));
        assert_eq!(
            normalize_path("t/e", "./x.sol").as_deref(),
            Some("t/e/x.sol")
        );
        assert_eq!(
            normalize_path("t/e", "../u/C.sol").as_deref(),
            Some("t/u/C.sol")
        );
        assert_eq!(normalize_path("t", "../a.sol").as_deref(), Some("a.sol"));
        // A bare (non-./) path is ROOT-relative, ignoring the importer's dir.
        assert_eq!(
            normalize_path("t/e", "lib/D.sol").as_deref(),
            Some("lib/D.sol")
        );
        // `.` segments collapse.
        assert_eq!(
            normalize_path("", "./a/./b.sol").as_deref(),
            Some("a/b.sol")
        );
        // Escapes and junk are None (→ FE476).
        assert_eq!(normalize_path("t", "../../a.sol"), None); // past the root
        assert_eq!(normalize_path("", "../a.sol"), None); // past the root from root
        assert_eq!(normalize_path("", "/etc/passwd"), None); // absolute
        assert_eq!(normalize_path("", "a\\b.sol"), None); // backslash
        assert_eq!(normalize_path("", "C:/x.sol"), None); // drive colon
        assert_eq!(normalize_path("", "a//b.sol"), None); // empty segment
        assert_eq!(normalize_path("", ""), None); // empty
        assert_eq!(normalize_path("t", ".."), None); // normalizes to the root
        assert_eq!(normalize_path("", "päth.sol"), None); // non-ASCII
    }
}
