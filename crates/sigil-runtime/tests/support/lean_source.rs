//! The Lean SOURCE-derived theorem census, shared by the public development's contract
//! (`soundness_contract.rs`, over `proofs/lean/LambdaSigil`) and the research overlay's
//! (`research_lean_gate.rs`, over the research overlay's module tree). Each package's
//! committed `axiom-targets.txt` must equal the set this scraper derives from its sources, and
//! each package's gate independently requires that manifest to equal the census Lean's
//! elaborated environment reports — the two derivations fence each other.
//!
//! `allow(dead_code)`: included by `#[path]` into several test binaries under `-D warnings`.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

#[allow(dead_code)]
pub fn lean_theorem_names_in_source(src: &str, label: &str) -> BTreeSet<String> {
    let src = lean_source_code_only(src, label);
    let mut theorems = BTreeSet::new();
    let mut nested_namespaces: Vec<String> = Vec::new();
    for line in src.lines().map(str::trim_start) {
        if let Some(rest) = line.strip_prefix("namespace ") {
            let name = rest.split_whitespace().next().unwrap_or_default();
            let relative = name.strip_prefix("LambdaSigil.").unwrap_or(name);
            if relative != "LambdaSigil" && !relative.is_empty() {
                for component in relative.split('.') {
                    if !component.is_empty()
                        && component
                            .chars()
                            .all(|c| c.is_ascii_alphanumeric() || c == '_')
                    {
                        nested_namespaces.push(component.to_string());
                    }
                }
            }
            continue;
        }
        if let Some(rest) = line.strip_prefix("end ") {
            let name = rest.split_whitespace().next().unwrap_or_default();
            let relative = name.strip_prefix("LambdaSigil.").unwrap_or(name);
            if relative != "LambdaSigil" {
                let components: Vec<_> = relative.split('.').collect();
                if nested_namespaces.len() >= components.len()
                    && nested_namespaces[nested_namespaces.len() - components.len()..]
                        .iter()
                        .map(String::as_str)
                        .eq(components.iter().copied())
                {
                    nested_namespaces.truncate(nested_namespaces.len() - components.len());
                }
            }
            continue;
        }
        // Strip any leading attribute block before looking for `theorem`. Matching the
        // bare prefix alone let `@[simp] theorem foo` escape the census entirely, and a
        // theorem outside the census is outside the axiom gate: the gate only reports on
        // manifest targets and never scans sources for `axiom` declarations.
        //
        // `private theorem` is deliberately still skipped -- Lean mangles private names,
        // so `#print axioms` cannot address them, and their axiom dependencies surface
        // through whichever public theorem uses them.
        let mut declaration = line;
        while let Some(attribute) = declaration.strip_prefix("@[") {
            // Count bracket depth rather than taking the first `]`: an attribute block
            // like `@[simp, foo[bar]] theorem` closes at the OUTER bracket, and stopping
            // at the inner one would leave `] theorem …` and hide the declaration again.
            let mut depth = 1usize;
            let mut end = None;
            for (index, character) in attribute.char_indices() {
                match character {
                    '[' => depth += 1,
                    ']' => {
                        depth -= 1;
                        if depth == 0 {
                            end = Some(index);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let Some(close) = end else { break };
            declaration = attribute[close + 1..].trim_start();
        }
        // `lemma` is Mathlib's alias for `theorem`, and Mathlib is a transitive import of
        // this development, so it elaborates here. Both produce `.thmInfo`, so both must
        // be censused -- matching `theorem` alone left unimported lemmas outside BOTH
        // derivations (the environment census cannot see unimported modules).
        let Some(rest) = declaration
            .strip_prefix("theorem ")
            .or_else(|| declaration.strip_prefix("lemma "))
        else {
            continue;
        };
        let name = rest
            .split(|c: char| c.is_whitespace() || matches!(c, '{' | '(' | ':'))
            .next()
            .unwrap_or_default();
        assert!(!name.is_empty(), "malformed theorem declaration in {label}");
        let qualified = if nested_namespaces.is_empty() {
            name.to_string()
        } else {
            format!("{}.{}", nested_namespaces.join("."), name)
        };
        assert!(
            theorems.insert(qualified.clone()),
            "duplicate Lean theorem declaration {qualified} in {label}"
        );
    }
    theorems
}

#[allow(dead_code)]
pub fn lean_theorem_names(dir: &Path) -> BTreeSet<String> {
    let dir = dir.to_path_buf();
    let mut files: Vec<PathBuf> = Vec::new();
    let mut pending_dirs = vec![dir.clone()];
    while let Some(current) = pending_dirs.pop() {
        for entry in std::fs::read_dir(&current)
            .unwrap_or_else(|err| panic!("cannot read {}: {err}", current.display()))
            .flatten()
        {
            let path = entry.path();
            if path.is_dir() {
                pending_dirs.push(path);
            } else if path.extension().is_some_and(|ext| ext == "lean") {
                files.push(path);
            }
        }
    }
    files.sort();

    let mut theorems = BTreeSet::new();
    for file in files {
        let src = std::fs::read_to_string(&file)
            .unwrap_or_else(|err| panic!("cannot read {}: {err}", file.display()));
        for theorem in lean_theorem_names_in_source(&src, &file.display().to_string()) {
            assert!(
                theorems.insert(theorem.clone()),
                "duplicate Lean theorem declaration {theorem}"
            );
        }
    }
    theorems
}

#[allow(dead_code)]
pub fn lean_source_code_only(src: &str, label: &str) -> String {
    let bytes = src.as_bytes();
    let mut stripped = Vec::with_capacity(bytes.len());
    let mut index = 0usize;
    let mut block_depth = 0usize;
    let mut in_line_comment = false;
    let mut in_string = false;
    let mut escaped = false;

    while index < bytes.len() {
        let byte = bytes[index];
        let next = bytes.get(index + 1).copied();

        if in_line_comment {
            if byte == b'\n' {
                stripped.push(byte);
                in_line_comment = false;
            } else {
                stripped.push(b' ');
            }
            index += 1;
            continue;
        }

        if block_depth > 0 {
            if byte == b'/' && next == Some(b'-') {
                stripped.extend_from_slice(b"  ");
                block_depth += 1;
                index += 2;
            } else if byte == b'-' && next == Some(b'/') {
                stripped.extend_from_slice(b"  ");
                block_depth -= 1;
                index += 2;
            } else {
                // Preserve line boundaries so declarations immediately following a comment
                // retain their original line position; all other comment bytes become space.
                stripped.push(if byte == b'\n' { byte } else { b' ' });
                index += 1;
            }
            continue;
        }

        if in_string {
            stripped.push(if byte == b'\n' { byte } else { b' ' });
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
            index += 1;
            continue;
        }

        if byte == b'-' && next == Some(b'-') {
            stripped.extend_from_slice(b"  ");
            in_line_comment = true;
            index += 2;
        } else if byte == b'/' && next == Some(b'-') {
            stripped.extend_from_slice(b"  ");
            block_depth = 1;
            index += 2;
        } else {
            if byte == b'"' {
                stripped.push(b' ');
                in_string = true;
            } else {
                stripped.push(byte);
            }
            index += 1;
        }
    }

    assert_eq!(
        block_depth, 0,
        "unterminated Lean block comment while scanning {label}"
    );
    assert!(
        !in_string,
        "unterminated Lean string literal while scanning {label}"
    );
    String::from_utf8(stripped)
        .unwrap_or_else(|err| panic!("comment stripping corrupted UTF-8 in {label}: {err}"))
}
