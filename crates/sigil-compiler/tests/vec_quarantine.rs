//! Vec-intrinsic privacy gate (PR B).
//!
//! `vec_load` / `vec_store` are stdlib-private primitives: the ONLY place
//! they may appear in SIGIL source is `stdlib/sigil/vec.sigil`, which wraps
//! them in the bounds-checked `Vec<T>` methods. User code (and every other
//! stdlib module, fixture, example, and corpus program) must reach a vector
//! through those methods, never the raw intrinsics.
//!
//! This is a HYGIENE boundary, not a safety boundary (see vec.sigil's
//! header / PR B anti-goal AG2): the intrinsics self-trap on
//! `index >= bound` regardless of caller, so a stray use is memory-safe,
//! merely off-contract. The gate keeps the surface honest by scanning every
//! `.sigil` file in the repository, stripping `//` line comments, and
//! asserting the two tokens appear in no file but `stdlib/sigil/vec.sigil`.
//!
//! When this fails, either route the new code through `Vec<T>`'s methods, or
//! — if you are deliberately extending the vector primitives — add the new
//! file to `ALLOWED` below with a comment explaining why.

use std::fs;
use std::path::{Path, PathBuf};

/// SIGIL files permitted to name the raw vec intrinsics, relative to the
/// repository root (forward slashes; normalized before compare).
const ALLOWED: &[&str] = &[
    "stdlib/sigil/vec.sigil",
    // B-VEC: the self-hosted W-lane RECOGNIZES the intrinsic names to lower them (the same role
    // the Rust air.rs/intrinsics.rs play) — it never calls them as user code. The string
    // literals live in the intrinsic-dispatch arms (cv_emit_vecintr, ai_call_in_subset,
    // cv_expr_tytok); the self-host completion record owns this boundary.
    "selfhost/air.sigil",
    // B-COMPOSE: the self-hosted tc REGISTERS the intrinsic signatures (the same role the Rust
    // type_check's builtin recognition plays) so cloned Vec method bodies type-check in the
    // composed gate chain — string literals in tc_build_sigs' seed block; it never calls them.
    "selfhost/typecheck.sigil",
];

/// Forbidden intrinsic tokens.
const FORBIDDEN: &[&str] = &["vec_load", "vec_store"];

/// Directories never worth scanning (build output / VCS metadata / Claude worktrees).
// `var/` holds materialized selfhost copies of tracked sources
// (`.gitignore` pins `/var/`); the self-hosted compiler names the
// quarantined tokens in STRING LITERALS there. CI never sees var/,
// but local full-suite runs on machines with selfhost artifacts must
// not fail on it — the compile-time module gates (T257/T25x) remain
// the in-tree enforcement.
//
// `.worktrees/` is the same case one directory up. Agent worktrees used to be
// created only under `.claude/worktrees/`; a checkout now also appears at the
// repo root, and a worktree holds a DIFFERENT commit's sources. Scanning one
// both false-positives (a 2.4 GB checkout's `selfhost/air.sigil` names
// `str_from_raw` in a string literal, failing this gate on a clean tree) and
// false-negatives (it is not the tree under test). Ignored by `.gitignore`
// for the same reason.
const SKIP_DIRS: &[&str] = &[
    "target",
    ".git",
    "node_modules",
    ".claude",
    ".worktrees",
    "var",
];

fn strip_line_comment(line: &str) -> &str {
    match line.find("//") {
        Some(idx) => &line[..idx],
        None => line,
    }
}

/// Collect every `*.sigil` path under `root`, skipping `SKIP_DIRS`.
fn collect_sigil_files(root: &Path, out: &mut Vec<PathBuf>) {
    let entries = match fs::read_dir(root) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if SKIP_DIRS.contains(&name) {
                continue;
            }
            collect_sigil_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("sigil") {
            out.push(path);
        }
    }
}

#[test]
fn vec_intrinsics_appear_only_in_vec_sigil() {
    // crates/sigil-compiler -> repo root is two levels up.
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("repo root is two levels above the crate manifest")
        .to_path_buf();

    let mut files = Vec::new();
    collect_sigil_files(&repo_root, &mut files);
    assert!(
        files.len() >= 50,
        "found only {} .sigil files under {} — the walk is probably mis-rooted",
        files.len(),
        repo_root.display()
    );

    for path in &files {
        let rel = path
            .strip_prefix(&repo_root)
            .unwrap_or(path)
            .to_string_lossy()
            .replace('\\', "/");
        if ALLOWED.contains(&rel.as_str()) {
            continue;
        }
        let source =
            fs::read_to_string(path).unwrap_or_else(|e| panic!("failed to read {rel}: {e}"));
        for (lineno, line) in source.lines().enumerate() {
            let code = strip_line_comment(line);
            for forbidden in FORBIDDEN {
                assert!(
                    !code.contains(forbidden),
                    "Vec-intrinsic privacy breach in {rel}:{}: `{forbidden}` may appear only in \
                     stdlib/sigil/vec.sigil. Use a `Vec<T>` method (push/get/len/...) instead, or \
                     add this file to ALLOWED if you are extending the vector primitives. Line: `{}`",
                    lineno + 1,
                    code.trim(),
                );
            }
        }
    }
}
