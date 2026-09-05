//! Workspace-root discovery and the build's `git_sha` stamp. The root is the
//! parent-of-parent of this crate's manifest dir (`crates/sigil-corpus`), so
//! the extractors resolve `selfhost/`, `stdlib/`, `crates/...` against a single
//! anchor.

use std::path::{Path, PathBuf};
use std::process::Command;

/// The repository root: `<manifest>/../..` where `<manifest>` is
/// `crates/sigil-corpus`. `CARGO_MANIFEST_DIR` is set by cargo at both compile
/// and `cargo run` time; the compile-time value is the fallback.
pub fn workspace_root() -> PathBuf {
    let manifest =
        std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| env!("CARGO_MANIFEST_DIR").into());
    Path::new(&manifest)
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from("."))
}

/// `git rev-parse HEAD` at `root`, or `"unknown"` if git is unavailable. (The
/// `GIT_TIMEOUT_MS` budget from §9 ET-C9 governs the pr_history extractor's
/// git calls in PR-4; `rev-parse` here is instant.)
pub fn git_sha(root: &Path) -> String {
    Command::new("git")
        .current_dir(root)
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "unknown".to_string())
}
