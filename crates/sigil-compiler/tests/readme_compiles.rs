//! Every ` ```sigil ` block in `README.md` must actually compile.
//!
//! The README is the first artifact a reader — human or agent — meets, and
//! under this project's north star agents are PRIMARY readers and writers of
//! SIGIL. A language tour that does not compile is therefore worse than no
//! tour: it teaches constructs the parser rejects, and an agent that learns
//! from it emits code that fails on the first try.
//!
//! The tour historically drifted because it was fenced ` ```rust `, so it
//! was never anything but prose — it accumulated method chaining, `|x|`
//! closure syntax, implicit tail returns, unbraced match arms and top-level
//! `let`, none of which SIGIL accepts.
//!
//! This test compiles what the README claims. Blocks are opted IN by the
//! ` ```sigil ` fence; ` ```rust `, ` ```bash `, ` ```json ` and friends are
//! scaffolding and are left alone.

use sigil_compiler::compile_named_module;
use std::path::PathBuf;

fn repo_root() -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.pop(); // crates/sigil-compiler -> crates
    path.pop(); // crates -> repo root
    path
}

/// Returns `(1-based line of the opening fence, block body)` for every
/// ` ```sigil ` block in `md`.
fn sigil_blocks(md: &str) -> Vec<(usize, String)> {
    let mut blocks = Vec::new();
    let mut lines = md.lines().enumerate();
    while let Some((index, line)) = lines.next() {
        let trimmed = line.trim_start();
        // Match the bare fence and info-string forms (```sigil, ```sigil,no_run)
        // but not a longer language name that merely starts with "sigil".
        let is_sigil_fence = trimmed
            .strip_prefix("```sigil")
            .is_some_and(|rest| rest.is_empty() || rest.starts_with(','));
        if !is_sigil_fence {
            continue;
        }
        let mut body = String::new();
        for (_, inner) in lines.by_ref() {
            if inner.trim_start().starts_with("```") {
                break;
            }
            body.push_str(inner);
            body.push('\n');
        }
        blocks.push((index + 1, body));
    }
    blocks
}

/// Anti-vacuity floor. Without it, re-fencing the tour back to ` ```rust `
/// (or deleting it) would leave this test scanning zero blocks and passing
/// green — asserting nothing while looking like coverage. That is the exact
/// failure mode the tour had for its entire life before this test existed,
/// so the floor is the point, not a formality.
const MIN_README_SIGIL_BLOCKS: usize = 1;

#[test]
fn readme_sigil_blocks_compile() {
    let path = repo_root().join("README.md");
    let markdown = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    let blocks = sigil_blocks(&markdown);
    assert!(
        blocks.len() >= MIN_README_SIGIL_BLOCKS,
        "expected at least {MIN_README_SIGIL_BLOCKS} ```sigil block(s) in README.md, found {}",
        blocks.len()
    );

    for (line, source) in blocks {
        if let Err(err) = compile_named_module(format!("README.md-{line}.sigil"), &source) {
            let codes: Vec<&str> = err
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code().as_str())
                .collect();
            let messages: Vec<String> = err
                .diagnostics()
                .iter()
                .map(|diagnostic| {
                    format!("  {}: {}", diagnostic.code().as_str(), diagnostic.message())
                })
                .collect();
            panic!(
                "README.md ```sigil block opening at line {line} does not compile.\n\
                 codes: {codes:?}\n{}\n--- block ---\n{source}-------------",
                messages.join("\n")
            );
        }
    }
}
