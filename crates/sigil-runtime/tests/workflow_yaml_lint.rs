//! A workflow file that GitHub cannot parse disables CI ENTIRELY — silently.
//!
//! On 2026-08-02 a `run:` step in `ci.yml` ended with
//! `grep -q "test result: ok. 1 passed" ddc.log`. In YAML a *plain* (unquoted)
//! scalar may not contain `": "` — colon-space starts a mapping — so the file
//! stopped parsing at that column. GitHub's response is not a red X on the
//! offending job: the whole workflow is refused, every lane in it never
//! starts, and the pull request simply sits at "waiting for status" forever.
//! Two PRs were blocked this way and it read as a stuck queue, not a failure.
//!
//! The double quotes in that command are invisible to YAML. They are shell
//! syntax sitting *inside* a plain scalar, so they quote nothing as far as the
//! parser is concerned — which is exactly why the mistake is easy to make and
//! hard to see.
//!
//! **This check cannot live in CI.** A CI step that validates the workflow
//! file only runs if the workflow file parses, so the one case it exists to
//! catch is the one case it cannot see. It has to run locally, under
//! `cargo test`, which is why it is here.
//!
//! The rule enforced is the precise YAML one rather than a general parse, so
//! no YAML dependency is needed and the diagnostic names the actual hazard.

use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.pop(); // crates/sigil-runtime -> crates
    path.pop(); // crates -> repo root
    path
}

/// A YAML plain scalar cannot contain `": "`. Block scalars (`|`, `>`) and
/// genuinely quoted scalars (`'…'`, `"…"`) can, so they are exempt.
fn offending_colon_space(value: &str) -> bool {
    let value = value.trim();
    if value.starts_with('|') || value.starts_with('>') {
        return false; // block scalar: colons are safe
    }
    if (value.starts_with('\'') && value.ends_with('\'') && value.len() > 1)
        || (value.starts_with('"') && value.ends_with('"') && value.len() > 1)
    {
        return false; // properly quoted scalar
    }
    value.contains(": ")
}

fn workflow_files(root: &Path) -> Vec<PathBuf> {
    let dir = root.join(".github/workflows");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|err| panic!("cannot read {}: {err}", dir.display()))
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension()
                .is_some_and(|ext| ext == "yml" || ext == "yaml")
        })
        .collect();
    files.sort();
    files
}

fn top_level_job_name(line: &str) -> Option<&str> {
    let rest = line.strip_prefix("  ")?;
    if rest.starts_with(' ') || rest.starts_with('\t') || rest.starts_with('#') {
        return None;
    }
    let name = rest.strip_suffix(':')?;
    (!name.is_empty()
        && name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')))
    .then_some(name)
}

fn job_lines<'a>(workflow: &'a str, wanted: &str) -> Vec<&'a str> {
    let mut found = false;
    let mut lines = Vec::new();
    for line in workflow.lines() {
        if let Some(name) = top_level_job_name(line) {
            if found {
                break;
            }
            found = name == wanted;
        }
        if found {
            lines.push(line);
        }
    }
    assert!(!lines.is_empty(), "workflow lost required job {wanted:?}");
    lines
}

fn active_job_contains(lines: &[&str], fragment: &str) -> bool {
    lines.iter().any(|line| {
        let line = line.trim();
        !line.starts_with('#') && line.contains(fragment)
    })
}

#[test]
fn workflow_plain_scalars_have_no_colon_space() {
    let root = repo_root();
    let files = workflow_files(&root);

    // Anti-vacuity floor: if the workflow directory is renamed or emptied this
    // test would scan nothing and pass, asserting exactly as much as the
    // broken file it exists to catch.
    assert!(
        files.len() >= 2,
        "expected at least 2 workflow files, found {} — has .github/workflows moved?",
        files.len()
    );

    let mut problems = Vec::new();
    for file in &files {
        let text = std::fs::read_to_string(file)
            .unwrap_or_else(|err| panic!("cannot read {}: {err}", file.display()));
        for (index, line) in text.lines().enumerate() {
            // Only `run:` and `if:` take long free-form values in practice, and
            // they are where shell text (and its colons) ends up.
            for key in ["run:", "if:"] {
                let Some(position) = line.find(key) else {
                    continue;
                };
                // Must be the key at this indent, not a substring of a word.
                if !line[..position].chars().all(char::is_whitespace) {
                    continue;
                }
                let value = &line[position + key.len()..];
                if offending_colon_space(value) {
                    problems.push(format!(
                        "{}:{}: plain `{key}` scalar contains \": \" — GitHub will refuse the \
                         whole workflow file\n      {}",
                        file.file_name().unwrap_or_default().to_string_lossy(),
                        index + 1,
                        line.trim()
                    ));
                }
            }
        }
    }

    assert!(
        problems.is_empty(),
        "workflow YAML would fail to parse, which disables every lane in the file \
         without reporting a failing check:\n  {}\n\nFix by removing the colon-space \
         (e.g. a `[[:space:]]` character class in a grep pattern) or by quoting the \
         whole scalar.",
        problems.join("\n  ")
    );
}

/// The lines of the workflow step that contains line `index`: from that step's
/// `- name:` line up to (not including) the next step's `- name:` or the next
/// top-level job. A pin that only asks "is this line somewhere in the file"
/// would be satisfied by an `env:` line sitting in a NEIGHBOURING step, where
/// it arms nothing, so the canary pin scopes both of its lines to one step.
fn step_block<'a>(lines: &[&'a str], index: usize) -> Vec<&'a str> {
    let is_step_start = |line: &str| line.trim_start().starts_with("- name:");
    let start = (0..=index)
        .rev()
        .find(|&i| is_step_start(lines[i]))
        .unwrap_or_else(|| {
            panic!(
                "line {} of the workflow is not inside a `- name:` step",
                index + 1
            )
        });
    let end = (index + 1..lines.len())
        .find(|&i| is_step_start(lines[i]) || top_level_job_name(lines[i]).is_some())
        .unwrap_or(lines.len());
    lines[start..end].to_vec()
}

/// SC-P4 anti-stub for `step_block`: the arming line planted in the NEXT step
/// must not count for the canary step, and the one in the canary step must.
#[test]
fn step_block_scopes_to_one_step() {
    let sample = [
        "  checks:",
        "    steps:",
        "      - name: Formal verifier scaling canary",
        "        env:",
        "          ARMED_HERE: \"1\"",
        "        run: cargo test canary",
        "      - name: The next step",
        "        env:",
        "          PLANTED_ELSEWHERE: \"1\"",
        "        run: cargo test other",
        "  next-job:",
    ];
    let run_at = sample
        .iter()
        .position(|line| line.trim() == "run: cargo test canary")
        .expect("the sample carries the canary run line");
    let block = step_block(&sample, run_at);
    assert_eq!(
        block.first().copied(),
        Some(sample[2]),
        "block starts at its own `- name:`"
    );
    assert!(
        block.iter().any(|line| line.trim() == "ARMED_HERE: \"1\""),
        "the step's own env line is inside its block"
    );
    assert!(
        !block
            .iter()
            .any(|line| line.trim() == "PLANTED_ELSEWHERE: \"1\""),
        "an env line planted in the NEXT step must be outside the block"
    );
    let other_at = sample
        .iter()
        .position(|line| line.trim() == "run: cargo test other")
        .expect("the sample carries the other run line");
    assert_eq!(
        step_block(&sample, other_at).last().copied(),
        Some(sample[9]),
        "the last step's block ends before the next top-level job"
    );
}

#[test]
fn ci_keeps_formal_verifier_scaling_canary() {
    let workflow = repo_root().join(".github/workflows/ci.yml");
    let text = std::fs::read_to_string(&workflow)
        .unwrap_or_else(|err| panic!("cannot read {}: {err}", workflow.display()));
    let command = "run: cargo test -p sigil-corpus --no-default-features --lib \
                   validate::tests::selfhost_trio_completes_within_validation_budget \
                   -- --exact --nocapture";
    // The arming line. The step's `env:` sets `sigil_corpus::schema::SCALING_CANARY_ENV`
    // to exactly `1`, which turns on the five-second `SELFHOST_TRIO_CANARY_MS` assertion
    // inside that test. Without it the step still runs the test, but the test then asserts
    // only the corpus extractor's wider drop bound — a verifier scaling regression would
    // pass this required lane unseen. So the pin covers BOTH lines, in ONE step.
    let arming = "SIGIL_CORPUS_SCALING_CANARY: \"1\"";

    let lines: Vec<&str> = text.lines().collect();
    let run_at = lines
        .iter()
        .position(|line| line.trim() == command)
        .unwrap_or_else(|| {
            panic!(
                "{} must run the linked formal-verifier scaling canary in required CI",
                workflow.display()
            )
        });
    let step = step_block(&lines, run_at);
    assert!(
        step.iter().any(|line| line.trim() == arming),
        "{} runs the formal-verifier scaling canary but its step lost the arming line \
         {arming:?} — unarmed, the test asserts only the extractor's drop bound, so the \
         required lane would stop detecting a verifier scaling regression",
        workflow.display()
    );
}

#[test]
fn ci_uses_the_bounded_observable_workspace_clippy_runner() {
    let root = repo_root();
    let workflow = root.join(".github/workflows/ci.yml");
    let text = std::fs::read_to_string(&workflow)
        .unwrap_or_else(|err| panic!("cannot read {}: {err}", workflow.display()));
    let checks = job_lines(&text, "checks");

    for required in [
        "run: bash scripts/clippy-workspace.sh no-default",
        "run: bash scripts/clippy-workspace.sh json",
    ] {
        assert!(
            checks.iter().any(|line| line.trim() == required),
            "required checks job lost observable Clippy command {required:?}"
        );
    }
    assert!(
        !active_job_contains(
            &checks,
            "cargo clippy --workspace --all-targets --no-default-features"
        ),
        "required checks job bypasses the bounded Clippy runner"
    );

    let runner = root.join("scripts/clippy-workspace.sh");
    let script = std::fs::read_to_string(&runner)
        .unwrap_or_else(|err| panic!("cannot read {}: {err}", runner.display()));
    for required in [
        "CLIPPY_JOB_CAP=8",
        "HEARTBEAT_SECONDS=30",
        "cargo clippy --workspace --all-targets --no-default-features --locked",
        "cargo clippy -p sigil-compiler --all-targets --no-default-features --features json --locked",
        "--jobs \"$jobs\" -- -D warnings",
    ] {
        assert!(
            script.contains(required),
            "{} lost load-bearing Clippy runner fragment {required:?}",
            runner.display()
        );
    }
}

#[test]
fn ci_keeps_production_v9_and_release_enforcement_commands() {
    let root = repo_root();
    let ci_path = root.join(".github/workflows/ci.yml");
    let ci = std::fs::read_to_string(&ci_path)
        .unwrap_or_else(|err| panic!("cannot read {}: {err}", ci_path.display()));

    let test = job_lines(&ci, "test");
    assert!(
        active_job_contains(&test, "cargo test --workspace --no-default-features"),
        "required `test` job must execute the complete solver-off workspace, including the \
         certificate/R819/package/MCP/serve integration suites"
    );

    let checks = job_lines(&ci, "checks");
    for required in [
        "cargo test -p sigil-corpus --no-default-features --lib validate::tests::selfhost_trio_completes_within_validation_budget",
        "cargo test -p sigil-compiler --no-default-features --test formal_rollout_contract",
        "cargo test -p sigil-runtime --no-default-features --test production_lean_composition_profile",
        "cargo test -p sigil-compiler --no-default-features --test formal_security",
        "cargo test -p sigil-compiler --no-default-features --test public_region_probes",
        "cargo test -p sigil-formal-bridge --test v9_production_verifier",
        "cargo test -p sigil-compiler --no-default-features --test compiler_context",
        "cargo test -p sigil-compiler --no-default-features --test host_profile_wasm",
        "cargo test -p sigil-runtime --no-default-features --test host_profile_binding",
        "production_v9_warm_small_fixture_median_stays_below_one_millisecond -- --exact",
    ] {
        assert!(
            active_job_contains(&checks, required),
            "required `checks` job lost production-v9 command fragment {required:?}"
        );
    }

    let hygiene = job_lines(&ci, "hygiene");
    for required in [
        "python tools/validate_release_evidence.py --self-test",
        "python tools/validate_release_evidence.py --template docs/release-evidence/csir-v9-dual-gate.toml",
    ] {
        assert!(
            active_job_contains(&hygiene, required),
            "required `hygiene` job lost release-evidence command {required:?}"
        );
    }
}
