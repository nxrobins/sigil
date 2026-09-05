//! `sigil-corpus` CLI. Thin over the library (`docs/specs/training-corpus.md`).
//!
//!   sigil-corpus build [--out <dir>]   # extract → validate → write JSONL
//!   sigil-corpus stats                 # extract → validate → print counts
//!   sigil-corpus validate              # (PR-5) re-gate an existing out dir

use std::path::PathBuf;

use anyhow::{Context, anyhow, bail};

use sigil_corpus::extract::ExtractCtx;
use sigil_corpus::{build, corpus_paths, emit};

fn main() -> anyhow::Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cmd = args.first().map(String::as_str).unwrap_or("build");
    match cmd {
        "build" => cmd_build(&args[1..]),
        "stats" => cmd_stats(),
        "validate" => cmd_validate(),
        other => Err(anyhow!(
            "unknown command `{other}`; use: build | stats | validate"
        )),
    }
}

fn make_ctx() -> ExtractCtx {
    let root = corpus_paths::workspace_root();
    let git_sha = corpus_paths::git_sha(&root);
    ExtractCtx {
        workspace_root: root,
        git_sha,
        offline: false,
    }
}

fn cmd_build(args: &[String]) -> anyhow::Result<()> {
    let ctx = make_ctx();
    let out = parse_out(args)?.unwrap_or_else(|| ctx.workspace_root.join("corpus").join("out"));
    let result = build(&ctx)?;
    emit::write_corpus(&out, &result)
        .with_context(|| format!("writing corpus to {}", out.display()))?;

    let m = emit::manifest(&result);
    println!(
        "wrote {} records ({} validated, {} unvalidated) to {} — proposed {}, dropped {}",
        m.totals.emitted,
        m.totals.validated,
        m.totals.unvalidated,
        out.display(),
        m.totals.proposed,
        m.totals.dropped,
    );
    Ok(())
}

fn cmd_stats() -> anyhow::Result<()> {
    let ctx = make_ctx();
    let result = build(&ctx)?;
    let m = emit::manifest(&result);
    println!("schema_version {}  git_sha {}", m.schema_version, m.git_sha);
    println!(
        "proposed {}  emitted {}  dropped {}  validated {}  unvalidated {}",
        m.totals.proposed,
        m.totals.emitted,
        m.totals.dropped,
        m.totals.validated,
        m.totals.unvalidated,
    );
    println!("per kind:");
    for (k, n) in &m.per_kind {
        println!("  {k:<16} {n}");
    }
    println!("per extractor:");
    for (e, n) in &m.per_extractor {
        println!("  {e:<16} {n}");
    }
    if !m.drop_buckets.is_empty() {
        println!("drops:");
        for (b, n) in &m.drop_buckets {
            println!("  {b:<24} {n}");
        }
    }
    Ok(())
}

/// Re-run the full extraction + gate and confirm the ledger reconciles. `build`
/// already panics on any §9 invariant breach (ungrounded prose, a secret, a
/// duplicate id, silent loss); this is the auditable green-light.
fn cmd_validate() -> anyhow::Result<()> {
    let ctx = make_ctx();
    let result = build(&ctx)?;
    let m = emit::manifest(&result);
    if m.totals.proposed != m.totals.emitted + m.totals.dropped {
        bail!(
            "reconciliation mismatch: proposed {} != emitted {} + dropped {}",
            m.totals.proposed,
            m.totals.emitted,
            m.totals.dropped,
        );
    }
    println!(
        "OK — {} records ({} validated, {} unvalidated), {} dropped; ledger balanced",
        m.totals.emitted, m.totals.validated, m.totals.unvalidated, m.totals.dropped,
    );
    Ok(())
}

/// `--out <dir>` (optional).
fn parse_out(args: &[String]) -> anyhow::Result<Option<PathBuf>> {
    match args {
        [] => Ok(None),
        [flag, path] if flag == "--out" => Ok(Some(PathBuf::from(path))),
        [flag] if flag == "--out" => Err(anyhow!("--out needs a path")),
        _ => Err(anyhow!("unexpected arguments: {}", args.join(" "))),
    }
}
