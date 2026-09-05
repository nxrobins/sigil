//! Deterministic output writer: per-kind `<kind>.jsonl`, a reconciled
//! `manifest.json`, and `rejects.log`. Records are already id-ordered (the
//! `BTreeMap` in `BuildResult`); serde serializes struct fields in declaration
//! order and `BTreeMap`s in key order, so the bytes are stable across runs
//! (ET-C5).

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use anyhow::Context as _;
use serde::Serialize;

use crate::BuildResult;
use crate::schema::{Kind, SCHEMA_VERSION, ValidationKind};

/// Write the whole corpus to `out_dir`, creating it if needed.
pub fn write_corpus(out_dir: &Path, build: &BuildResult) -> anyhow::Result<()> {
    fs::create_dir_all(out_dir)
        .with_context(|| format!("creating output dir {}", out_dir.display()))?;

    for kind in Kind::ALL {
        let mut buf = String::new();
        for rec in build.records.values().filter(|r| r.kind == kind) {
            buf.push_str(&serde_json::to_string(rec)?);
            buf.push('\n');
        }
        fs::write(out_dir.join(format!("{}.jsonl", kind.as_str())), buf)?;
    }

    let manifest = manifest(build);
    fs::write(
        out_dir.join("manifest.json"),
        serde_json::to_string_pretty(&manifest)? + "\n",
    )?;

    let mut rbuf = String::new();
    for rej in &build.ledger.rejects {
        rbuf.push_str(&serde_json::to_string(&RejectLine {
            id: &rej.id,
            extractor: &rej.extractor,
            reason: &rej.reason,
        })?);
        rbuf.push('\n');
    }
    fs::write(out_dir.join("rejects.log"), rbuf)?;
    Ok(())
}

#[derive(Serialize)]
pub struct Manifest {
    pub schema_version: &'static str,
    pub git_sha: String,
    pub totals: Totals,
    pub per_kind: BTreeMap<String, usize>,
    pub per_extractor: BTreeMap<String, usize>,
    pub drop_buckets: BTreeMap<String, usize>,
}

#[derive(Serialize)]
pub struct Totals {
    pub proposed: usize,
    pub emitted: usize,
    pub dropped: usize,
    pub validated: usize,
    pub unvalidated: usize,
}

/// Build the manifest from a `BuildResult`. No timestamps — the artifact is a
/// pure function of the repo state (ET-C5).
pub fn manifest(build: &BuildResult) -> Manifest {
    let mut per_kind: BTreeMap<String, usize> = BTreeMap::new();
    let mut per_extractor: BTreeMap<String, usize> = BTreeMap::new();
    let mut validated = 0usize;

    for r in build.records.values() {
        *per_kind.entry(r.kind.as_str().to_string()).or_insert(0) += 1;
        *per_extractor.entry(r.extractor.clone()).or_insert(0) += 1;
        if r.validated.ok {
            validated += 1;
        }
    }
    let emitted = build.records.len();
    let git_sha = build
        .records
        .values()
        .next()
        .map(|r| r.git_sha.clone())
        .unwrap_or_else(|| "unknown".to_string());

    // Sanity: a non-`ok` emitted record must be `Unvalidated` (ET-C1 guards the
    // inverse; this keeps the manifest's `unvalidated` count honest).
    debug_assert!(
        build.records.values().all(
            |r| r.validated.ok || matches!(r.validated.how, ValidationKind::Unvalidated { .. })
        )
    );

    Manifest {
        schema_version: SCHEMA_VERSION,
        git_sha,
        totals: Totals {
            proposed: build.proposed,
            emitted,
            dropped: build.ledger.total(),
            validated,
            unvalidated: emitted - validated,
        },
        per_kind,
        per_extractor,
        drop_buckets: build.ledger.buckets.clone(),
    }
}

#[derive(Serialize)]
struct RejectLine<'a> {
    id: &'a str,
    extractor: &'a str,
    reason: &'a str,
}
