//! The pr-history extractor: the self-hosting journey as intent→code pairs.
//! Each merged PR that touched a `.sigil` file contributes the file's
//! post-image, with the PR title as `intent` and the body's first paragraph as
//! `reasoning` (both grounded).
//!
//! Validate-or-drop is load-bearing here (ET-C1): a post-image from an old PR
//! may no longer compile against today's compiler — it is dropped and counted,
//! so only still-valid code ships. Yield is intentionally modest: the squash-
//! merge commit only surfaces the recent self-hosting PRs (older epics merged as
//! true-merge commits, whose diffs are invisible via the merge oid — a declared
//! boundary, the merge-commit-diff + compiler-drift problem of AG-C9, not a
//! defect to pre-solve).

use std::collections::BTreeMap;
use std::process::{Command, Stdio};
use std::rc::Rc;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use serde::Deserialize;

use super::{ExtractCtx, Extractor, RawRecord, ValidationIntent};
use crate::schema::{
    ByteSpan, Context, Difficulty, GH_TIMEOUT_MS, Kind, MAX_OUTPUT_BYTES, MAX_PROSE_BYTES, MAX_PRS,
    Record, SCHEMA_VERSION, Validated, ValidationKind,
};

/// The `owner/repo` slug `gh` is pointed at, derived from the checkout's `origin` remote so the
/// extractor works unchanged in every clone of this history. Fail closed: a remote that is not a
/// GitHub URL is an error, never a guess.
fn repository_slug(root: &std::path::Path) -> anyhow::Result<String> {
    let url = run_capture(root, "git", &["remote", "get-url", "origin"], GH_TIMEOUT_MS)
        .ok_or_else(|| anyhow::anyhow!("cannot read the origin remote of {}", root.display()))?;
    let url = url.trim().trim_end_matches('/');
    let url = url.strip_suffix(".git").unwrap_or(url);
    let tail = url
        .rsplit_once("github.com")
        .map(|(_, tail)| tail.trim_start_matches([':', '/']))
        .ok_or_else(|| anyhow::anyhow!("origin remote is not a GitHub URL: {url}"))?;
    let mut parts = tail.split('/');
    match (parts.next(), parts.next(), parts.next()) {
        (Some(owner), Some(repo), None) if !owner.is_empty() && !repo.is_empty() => {
            Ok(format!("{owner}/{repo}"))
        }
        _ => anyhow::bail!("origin remote does not name owner/repo: {url}"),
    }
}
const SELFHOST: &[&str] = &[
    "selfhost/lexer.sigil",
    "selfhost/parser.sigil",
    "selfhost/typecheck.sigil",
];

#[derive(Deserialize)]
struct PrJson {
    number: u64,
    title: String,
    body: String,
    #[serde(rename = "mergeCommit")]
    merge_commit: Option<MergeCommit>,
}

#[derive(Deserialize)]
struct MergeCommit {
    oid: String,
}

pub struct PrHistory;

impl Extractor for PrHistory {
    fn name(&self) -> &'static str {
        "pr_history"
    }

    fn extract(&self, ctx: &ExtractCtx) -> anyhow::Result<Vec<RawRecord>> {
        if ctx.offline {
            return Ok(Vec::new());
        }
        let root = ctx.workspace_root.clone();
        let json = match run_capture(
            &root,
            "gh",
            &[
                "pr",
                "list",
                "--repo",
                &repository_slug(&root)?,
                "--state",
                "merged",
                "--json",
                "number,title,body,mergeCommit",
                "--limit",
                &MAX_PRS.to_string(),
            ],
            GH_TIMEOUT_MS,
        ) {
            Some(j) => j,
            // gh unavailable / timed out (e.g. a headless run): no PR records,
            // not a build failure.
            None => return Ok(Vec::new()),
        };
        let prs: Vec<PrJson> = serde_json::from_str(&json).unwrap_or_default();

        // Sort by PR number so the proposal order is deterministic (ET-C5).
        let mut prs = prs;
        prs.sort_by_key(|p| p.number);

        let mut out = Vec::new();
        let mut trio_cache: BTreeMap<String, Option<Rc<String>>> = BTreeMap::new();
        for pr in &prs {
            let Some(oid) = pr.merge_commit.as_ref().map(|m| m.oid.as_str()) else {
                continue;
            };
            let changed = changed_sigil_files(&root, oid);
            if changed.is_empty() {
                continue;
            }
            // Intent/reasoning grounded in the PR title + body.
            let title = truncate(&pr.title, MAX_PROSE_BYTES);
            let body_para = first_paragraph(&pr.body);
            let reasoning = if body_para.is_empty() {
                None
            } else {
                Some(truncate(&body_para, MAX_PROSE_BYTES))
            };
            let provenance = format!("{}\n{}", pr.title, pr.body);

            for path in changed {
                let Some(src) = git_show_file(&root, oid, &path) else {
                    continue;
                };
                let is_selfhost = path.starts_with("selfhost/");
                let intent_kind = if is_selfhost {
                    // Validate via the trio AT THIS COMMIT (internally
                    // consistent), memoized per oid.
                    let trio = trio_cache
                        .entry(oid.to_string())
                        .or_insert_with(|| inlined_trio_at(&root, oid).map(Rc::new))
                        .clone();
                    match trio {
                        Some(unit_src) => ValidationIntent::PositiveUnit {
                            unit_key: format!("pr{}-trio:{oid}", pr.number),
                            unit_src,
                        },
                        None => continue, // a sibling missing at this oid
                    }
                } else {
                    ValidationIntent::Positive
                };

                let record = Record {
                    id: format!("pr_history:{}:{}", pr.number, slug(&path)),
                    kind: Kind::Implementation,
                    intent: title.clone(),
                    context: Context::default(),
                    output: src.clone(),
                    reasoning: reasoning.clone(),
                    tags: vec!["pr-history".to_string(), "self-hosting".to_string()],
                    difficulty: Difficulty::Hard,
                    pr: Some(pr.number),
                    negative_examples: Vec::new(),
                    source_path: path.clone(),
                    git_sha: oid.to_string(),
                    span: Some(ByteSpan {
                        start: 0,
                        end: src.len(),
                    }),
                    validated: Validated {
                        ok: false,
                        how: ValidationKind::Unvalidated {
                            reason: "pending pr-history validation".to_string(),
                        },
                    },
                    extractor: "pr_history".to_string(),
                    schema_version: SCHEMA_VERSION.to_string(),
                };
                out.push(RawRecord {
                    record,
                    intent: intent_kind,
                    name_for_compile: path.rsplit('/').next().unwrap_or("m").to_string(),
                    provenance: provenance.clone(),
                });
            }
        }
        Ok(out)
    }
}

/// `.sigil` paths (selfhost/ + stdlib/sigil/) changed by `git show <oid>`.
fn changed_sigil_files(root: &std::path::Path, oid: &str) -> Vec<String> {
    let out = run_capture(
        root,
        "git",
        &["show", oid, "--name-only", "--format="],
        10_000,
    )
    .unwrap_or_default();
    let mut files: Vec<String> = out
        .lines()
        .map(str::trim)
        .filter(|l| {
            (l.starts_with("selfhost/") || l.starts_with("stdlib/sigil/")) && l.ends_with(".sigil")
        })
        .map(str::to_string)
        .collect();
    files.sort();
    files.dedup();
    files
}

fn git_show_file(root: &std::path::Path, oid: &str, path: &str) -> Option<String> {
    let src = run_capture(root, "git", &["show", &format!("{oid}:{path}")], 10_000)?;
    // ET-C7 size cap is enforced later by the gate, but skip the giant ones
    // early to avoid carrying them.
    if src.len() > MAX_OUTPUT_BYTES {
        return None;
    }
    Some(src)
}

/// The selfhost trio inlined AT `oid` (all three files from the same commit),
/// or `None` if any is missing at that commit.
fn inlined_trio_at(root: &std::path::Path, oid: &str) -> Option<String> {
    let lex = run_capture(
        root,
        "git",
        &["show", &format!("{oid}:{}", SELFHOST[0])],
        10_000,
    )?;
    let par = run_capture(
        root,
        "git",
        &["show", &format!("{oid}:{}", SELFHOST[1])],
        10_000,
    )?;
    let tc = run_capture(
        root,
        "git",
        &["show", &format!("{oid}:{}", SELFHOST[2])],
        10_000,
    )?;
    Some(format!(
        "module tool;\n{}\n{}\n{}\n",
        lex.replace("\nmodule lexer;\n", "\n"),
        par.replace("\nmodule parser;\n", "\n"),
        tc.replace("\nmodule typecheck;\n", "\n"),
    ))
}

/// Run a subprocess, capturing stdout, killed at `timeout_ms`. `None` on
/// non-zero exit, spawn failure, or timeout (ET-C9 bound).
fn run_capture(
    root: &std::path::Path,
    cmd: &str,
    args: &[&str],
    timeout_ms: u64,
) -> Option<String> {
    let mut child = Command::new(cmd)
        .args(args)
        .current_dir(root)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    let mut stdout = child.stdout.take()?;
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let mut buf = String::new();
        use std::io::Read;
        let _ = stdout.read_to_string(&mut buf);
        let _ = tx.send(buf);
    });
    // Wait for the process within budget.
    let start = wait_with_timeout(&mut child, Duration::from_millis(timeout_ms));
    if !start {
        let _ = child.kill();
        return None;
    }
    let status = child.wait().ok()?;
    if !status.success() {
        return None;
    }
    rx.recv_timeout(Duration::from_millis(1_000)).ok()
}

/// Poll the child for up to `dur`; returns true if it exited in time.
fn wait_with_timeout(child: &mut std::process::Child, dur: Duration) -> bool {
    let step = Duration::from_millis(25);
    let mut waited = Duration::ZERO;
    loop {
        match child.try_wait() {
            Ok(Some(_)) => return true,
            Ok(None) => {
                if waited >= dur {
                    return false;
                }
                thread::sleep(step);
                waited += step;
            }
            Err(_) => return false,
        }
    }
}

/// The first non-heading paragraph of the body, returned VERBATIM (a substring
/// of the body, so it grounds against `provenance`, ET-C3). Paragraphs split on
/// blank lines; an all-heading paragraph is skipped.
fn first_paragraph(body: &str) -> String {
    for para in body.split("\n\n") {
        let p = para.trim();
        if p.is_empty() || p.lines().all(|l| l.trim_start().starts_with('#')) {
            continue;
        }
        return p.to_string();
    }
    String::new()
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() <= max {
        return s.to_string();
    }
    let mut end = max;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_paragraph_is_a_substring_of_body() {
        // The grounding contract (ET-C3): the chosen paragraph must appear
        // verbatim in the body, so it can be grounded against provenance.
        let body = "## C1 PR-4b — match statements\n\nThe ninth slice typechecks `match`.\nIt binds the scrutinee.\n\n### Gate\ncargo test";
        let para = first_paragraph(body);
        assert_eq!(
            para,
            "The ninth slice typechecks `match`.\nIt binds the scrutinee."
        );
        assert!(
            body.contains(&para),
            "first paragraph must be a verbatim body substring"
        );
    }

    #[test]
    fn first_paragraph_empty_when_only_headings() {
        assert_eq!(first_paragraph("## a\n\n### b"), "");
        assert_eq!(first_paragraph(""), "");
    }
}
