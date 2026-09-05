//! Owned-strings `str_from_raw` privacy gate (PR S2 / ET-1).
//!
//! `str_from_raw(ptr, len)` is the stdlib-private keystone of owned-string
//! construction: it forges a `str` fat-pointer from a raw `(data_ptr, len)`
//! pair. The ONLY place it may appear in SIGIL source is
//! `stdlib/sigil/string.sigil`, whose `concat`/`join`/`itoa` builders allocate
//! a buffer, fill it, and wrap it — deriving `len` from the buffer they own.
//!
//! Unlike the `vec_load`/`vec_store` quarantine, this is a SAFETY boundary, not
//! mere hygiene: `vec_store` self-traps on `index >= bound` regardless of
//! caller, but a forged `str` carries a LYING `len` that the `byte_at`/`substr`
//! bounds-checks then trust — an out-of-bounds read. So the privacy is enforced
//! TWICE: this repo-wide grep (a stray token anywhere fails the build) AND a
//! compile-time module gate (T257) that rejects any caller outside module
//! `string` (see `tests/str_from_raw_gate.rs`).
//!
//! When this fails, build owned strings through `concat`/`join`/`itoa`, or — if
//! you are deliberately extending the owned-string primitives — add the new
//! file to `ALLOWED` below with a comment explaining why.

use std::fs;
use std::path::{Path, PathBuf};

/// SIGIL files permitted to name the raw str-forge intrinsic, relative to the
/// repository root (forward slashes; normalized before compare).
const ALLOWED: &[&str] = &[
    "stdlib/sigil/string.sigil",
    // W-STRRAW: the self-hosted W-lane RECOGNIZES the intrinsic name to LOWER it (the same role
    // the Rust air.rs/intrinsics.rs play) — it never calls str_from_raw as user code. The string
    // literals live in the intrinsic-dispatch arms (cv_emit_vecintr, ai_value_in_subset,
    // cv_expr_tytok). Mirrors vec_quarantine's air.sigil allow.
    "selfhost/air.sigil",
    // HB-2 family-1: the self-hosted TYPECHECK shadow recognizes the intrinsic name to TYPE it
    // (the same role the Rust type_check/expressions/intrinsics.rs plays) — the string literal
    // is the sig-table NAME in tc_build_sigs' intrinsic seed, never a call. Same rationale as
    // the air.sigil allow above.
    "selfhost/typecheck.sigil",
];

/// Forbidden intrinsic token.
const FORBIDDEN: &[&str] = &["str_from_raw"];

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
fn str_from_raw_appears_only_in_string_sigil() {
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
                    "str-forge privacy breach in {rel}:{}: `{forbidden}` may appear only in \
                     stdlib/sigil/string.sigil. Build owned strings via `concat`/`join`/`itoa` \
                     instead, or add this file to ALLOWED if you are extending the owned-string \
                     primitives. Line: `{}`",
                    lineno + 1,
                    code.trim(),
                );
            }
        }
    }
}
