//! Source fences for the Z3 fragment guard. See
//! `docs/specs/z3-fragment-guard.md` section 7.
//!
//! Feature-INDEPENDENT: these are pure source scans, so they run in the
//! default `--no-default-features` CI lanes, even where solver-gated code is
//! not compiled.
//!
//! Comment lines (`//`, `///`, `//!`) are stripped before matching, so
//! prose mentioning the fenced constructs (like this header) never
//! trips a fence.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// Workspace `crates/` root, resolved from this crate's manifest dir.
fn crates_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("sigil-compiler sits inside crates/")
        .to_path_buf()
}

/// Every `.rs` file under `crates/`, recursively.
fn all_rs_files() -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let entries =
            fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir {} failed: {e}", dir.display()));
        for entry in entries {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                // target/ never lives inside crates/<name>/src|tests, but
                // guard against vendored build dirs anyway.
                if path.file_name().is_some_and(|n| n == "target") {
                    continue;
                }
                walk(&path, out);
            } else if path.extension().is_some_and(|e| e == "rs") {
                out.push(path);
            }
        }
    }
    let mut out = Vec::new();
    walk(&crates_root(), &mut out);
    assert!(
        out.len() > 50,
        "suspiciously few .rs files under crates/ — walk broken?"
    );
    out
}

fn is_comment_line(line: &str) -> bool {
    let t = line.trim_start();
    t.starts_with("//") || t.starts_with("///") || t.starts_with("//!")
}

/// Path rendered relative to crates/, with forward slashes, for the
/// pinned-census keys (platform-stable).
fn rel(path: &Path) -> String {
    path.strip_prefix(crates_root())
        .expect("file under crates/")
        .to_string_lossy()
        .replace('\\', "/")
}

/// ET-Z2(a): module-/file-scoped `#![allow(clippy::disallowed_methods)]`
/// is FORBIDDEN workspace-wide — one inner attribute would neuter the
/// entire lint fence for its whole scope (the MC-4 attack).
#[test]
fn no_scoped_allow_of_disallowed_methods() {
    let needle = "#![allow(clippy::disallowed_methods)";
    let mut offenders: Vec<String> = Vec::new();
    for file in all_rs_files() {
        let source = fs::read_to_string(&file)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", file.display()));
        for (idx, line) in source.lines().enumerate() {
            if is_comment_line(line) {
                continue;
            }
            if line.trim_start().starts_with(needle) {
                offenders.push(format!("{}:{}", rel(&file), idx + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "module-/file-scoped #![allow(clippy::disallowed_methods)] is \
         forbidden (ET-Z2) — it would neuter the whole lint fence for its \
         scope. Use an expression-level #[allow] and add it to the census. \
         Found: {offenders:?}"
    );
}

/// ET-Z2(b): the expression-level carve-out census, pinned exactly. A
/// new `#[allow(clippy::disallowed_methods)]` anywhere in the workspace
/// fails this test until it is deliberately added here AND to the
/// clippy.toml census comment.
#[test]
fn carve_out_census_is_exactly_the_pinned_set() {
    let needle = "#[allow(clippy::disallowed_methods)";
    let mut found: BTreeMap<String, usize> = BTreeMap::new();
    for file in all_rs_files() {
        let source = fs::read_to_string(&file)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", file.display()));
        for line in source.lines() {
            if is_comment_line(line) {
                continue;
            }
            if line.trim_start().starts_with(needle) {
                *found.entry(rel(&file)).or_default() += 1;
            }
        }
    }

    // The pinned census (see clippy.toml's chokepoint-fence comment):
    //   z3_cache.rs            — fresh_check + verify_first_hit
    //   z3_capability.rs       — model extraction + the raw
    //                            rlimit self-test
    //   air_capability_v2/mod.rs — check_direct
    //   z3_fragment_guard_canaries.rs — the quantifier canary
    //   sigil-runtime ephemeral.rs — the runtime Cap<Z3> shim (its own
    //                            trust domain)
    let expected: BTreeMap<String, usize> = [
        ("sigil-compiler/src/z3_cache.rs", 2),
        ("sigil-compiler/src/z3_capability.rs", 2),
        ("sigil-compiler/src/air_capability_v2/mod.rs", 1),
        ("sigil-compiler/tests/z3_fragment_guard_canaries.rs", 1),
        ("sigil-runtime/src/ephemeral.rs", 1),
    ]
    .into_iter()
    .map(|(f, n)| (f.to_string(), n))
    .collect();

    assert_eq!(
        found, expected,
        "the #[allow(clippy::disallowed_methods)] carve-out census drifted \
         from the pinned set (ET-Z2). A new carve-out must be deliberate: \
         justify it, add it to clippy.toml's census comment, and update \
         this pin."
    );
}

/// ET-Z1's build-time backstop: in sigil-compiler PRODUCTION code, every
/// raw `.check()` call must have a `check_fragment` call within the 25
/// lines above it in the same file — the walk and the check live
/// together. (Test modules are exempt: the rlimit self-test deliberately
/// exercises a raw check; the sigil-runtime shim is a different trust
/// domain, census-pinned above.)
#[test]
fn every_production_check_is_guard_adjacent() {
    let compiler_src = crates_root().join("sigil-compiler").join("src");
    let mut offenders: Vec<String> = Vec::new();

    for file in all_rs_files() {
        if !file.starts_with(&compiler_src) {
            continue;
        }
        let source = fs::read_to_string(&file)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", file.display()));
        let lines: Vec<&str> = source.lines().collect();
        // Production half only — same split as the z3_corpus fences.
        let test_module_start = lines
            .iter()
            .position(|l| l.trim_start().starts_with("#[cfg(test)]"))
            .unwrap_or(lines.len());

        for (idx, line) in lines.iter().enumerate().take(test_module_start) {
            if is_comment_line(line) {
                continue;
            }
            if !line.contains(".check()") {
                continue;
            }
            let lo = idx.saturating_sub(25);
            let guarded = lines[lo..idx].iter().any(|l| l.contains("check_fragment("));
            if !guarded {
                offenders.push(format!("{}:{} `{}`", rel(&file), idx + 1, line.trim()));
            }
        }
    }

    assert!(
        offenders.is_empty(),
        "production `.check()` call(s) without a `check_fragment` walk in \
         the 25 lines above (ET-Z1 — the walk and the check live in the \
         same function). Route through z3_cache::fresh_check / \
         check_cached* or the v2 check_direct. Found: {offenders:?}"
    );
}

/// ET-Z6: `catch_unwind` is FORBIDDEN in sigil-compiler — a harness that
/// converts the refinement-site ICE into a recoverable non-failure would
/// turn a fired guard into a silent pass.
#[test]
fn no_catch_unwind_in_sigil_compiler() {
    let compiler_src = crates_root().join("sigil-compiler").join("src");
    let mut offenders: Vec<String> = Vec::new();
    for file in all_rs_files() {
        if !file.starts_with(&compiler_src) {
            continue;
        }
        let source = fs::read_to_string(&file)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", file.display()));
        for (idx, line) in source.lines().enumerate() {
            if is_comment_line(line) {
                continue;
            }
            if line.contains("catch_unwind") {
                offenders.push(format!("{}:{}", rel(&file), idx + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "catch_unwind is forbidden in sigil-compiler/src (ET-Z6): the \
         fragment guard's ICE path must stay process-fatal — a swallowed \
         panic is a swallowed soundness firing. Found: {offenders:?}"
    );
}

/// The guard module imports only `z3` and `std`. A `use crate::` would couple
/// the shared guard to one compiler query family.
#[test]
fn fragment_guard_imports_are_isolated() {
    let guard = crates_root()
        .join("sigil-compiler")
        .join("src")
        .join("z3_fragment_guard.rs");
    let source = fs::read_to_string(&guard)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", guard.display()));
    let lines: Vec<&str> = source.lines().collect();
    // The in-module #[cfg(test)] tests may use super::*; only the
    // production half is constrained.
    let test_module_start = lines
        .iter()
        .position(|l| l.trim_start().starts_with("#[cfg(test)]"))
        .unwrap_or(lines.len());

    let mut offenders: Vec<String> = Vec::new();
    for (idx, line) in lines.iter().enumerate().take(test_module_start) {
        if is_comment_line(line) {
            continue;
        }
        let t = line.trim_start();
        if t.starts_with("use crate::") || t.starts_with("use super::") {
            offenders.push(format!("line {}: `{}`", idx + 1, t));
        }
    }
    assert!(
        offenders.is_empty(),
        "z3_fragment_guard.rs must import only `z3` and `std` (ET-Z9) — \
         it is shared by both solver query families. Found: {offenders:?}"
    );
}

/// ET-M3 (the `solver_verified` cert witness): the witness is assigned at
/// exactly ONE site — the capability-verify chokepoint — so a second
/// writer cannot quietly fork the semantics (e.g. a future kill-switch
/// that sets it `true` while skipping the prover). The contract on
/// `CapabilityReport::solver_verified` requires any bypass to set it
/// `false`; pinning the lone assignment makes a violating bypass
/// reviewer-visible at the only place it can legally happen.
#[test]
fn solver_verified_has_exactly_one_assignment_site() {
    let mut sites: Vec<String> = Vec::new();
    for file in all_rs_files() {
        // Skip this scanner file itself: its needle string literal
        // (`"solver_verified ="`) is a substring match but not a real
        // assignment. (The other fences above use `starts_with`, which
        // dodges in-string-literal self-matches; an assignment cannot be
        // anchored that way, so we exclude the scanner explicitly.)
        if file.file_name().is_some_and(|n| n == "z3_guard_fences.rs") {
            continue;
        }
        let source = fs::read_to_string(&file)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", file.display()));
        for line in source.lines() {
            if is_comment_line(line) {
                continue;
            }
            // An ASSIGNMENT: `solver_verified =` but NOT `==` (a
            // comparison, e.g. the cfg-split lock test) and NOT
            // `solver_verified:` (a struct field / construction). The
            // single legal site is the `let solver_verified = ...` at the
            // capability-verify chokepoint.
            if let Some(pos) = line.find("solver_verified =") {
                let after = &line[pos + "solver_verified =".len()..];
                if after.starts_with('=') {
                    continue; // `solver_verified ==` comparison
                }
                sites.push(rel(&file));
            }
        }
    }
    assert_eq!(
        sites,
        vec!["sigil-compiler/src/capability.rs".to_string()],
        "solver_verified must be assigned at exactly ONE site \
         (capability::verify — ET-M3). A second writer can fork the \
         witness semantics; route through the chokepoint. Found: {sites:?}"
    );
}

/// A wide `u256` refinement value or bound must use `Int::from_str` as one
/// arbitrary-precision numeral, never an `i64` truncation. This source fence
/// complements the behavioral witness in `u256_refinements.rs`.
#[test]
fn u256_wide_refinement_value_is_never_narrowed_to_i64() {
    let path = crates_root().join("sigil-compiler/src/z3_capability.rs");
    let source = fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    let code: String = source
        .lines()
        .filter(|l| !is_comment_line(l))
        .map(|l| format!("{l}\n"))
        .collect();

    // The canonical u256→i64 truncation token must never appear in the Z3 layer.
    assert!(
        !code.contains("limbs[0]"),
        "NC-b2: `limbs[0]` (a u256→i64 truncation) must not appear in z3_capability.rs"
    );
    // The single wide chokepoint exists and builds the numeral via from_str.
    // (z3 0.21 spelling: objects are built in the current thread-local
    // context, so the constructor no longer takes one.)
    assert!(
        code.contains("Int::from_str(&decimal)"),
        "NC-b2: the Wide refinement numeral must be built via Int::from_str(u256_to_decimal)"
    );
    // No code line may narrow a Wide value to i64.
    for line in code.lines() {
        if line.contains("RefValue::Wide") {
            assert!(
                !line.contains("from_i64") && !line.contains("as i64"),
                "NC-b2: a RefValue::Wide must never be narrowed to i64 — offending line: {line}"
            );
        }
    }
}

/// DC-5 (the design-by-contract spec): the native decider compares a wide value whole. The
/// fence above, which keeps the Z3 layer from narrowing a `RefValue::Wide`, extends to
/// `refinement_decide.rs`: no `limbs[0]` read, and no `as i64` or `from_i64` on any code line,
/// since every narrow value there widens to i128 and nothing narrows; the one wide-to-i128
/// chokepoint widens limbs and is named here so a rewrite re-pins the fence.
#[test]
fn native_decider_never_narrows_a_wide_value() {
    let path = crates_root().join("sigil-compiler/src/refinement_decide.rs");
    let source = fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    let code: String = source
        .lines()
        .filter(|l| !is_comment_line(l))
        .map(|l| format!("{l}\n"))
        .collect();
    assert!(
        !code.contains("limbs[0]"),
        "DC-5: `limbs[0]` (a u256→i64 truncation) must not appear in refinement_decide.rs"
    );
    for line in code.lines() {
        assert!(
            !line.contains(" as i64") && !line.contains("from_i64"),
            "DC-5: refinement_decide.rs narrows a value to i64 — offending line: {line}"
        );
    }
    assert!(
        code.contains("i128::from(second) << 64"),
        "DC-5: the wide-to-i128 widening chokepoint moved; re-pin the fence"
    );
}

/// Each line of the workflow job `job`, as a bare `key: value` (a list item's `- ` dropped,
/// blank and comment lines skipped): from its two-space-indented key to the next key at that
/// depth or shallower. `None` when the workflow has no such job.
fn workflow_job_keys<'a>(workflow: &'a str, job: &str) -> Option<Vec<&'a str>> {
    let header = format!("  {job}:");
    let mut lines = workflow.lines().skip_while(|line| *line != header);
    lines.next()?;
    Some(
        lines
            .take_while(|line| {
                let indent = line.len() - line.trim_start().len();
                line.trim().is_empty() || line.trim_start().starts_with('#') || indent > 2
            })
            .map(|line| line.trim().trim_start_matches("- "))
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .collect(),
    )
}

/// What this checks about the workflow's `supply-chain` job: its `run:` steps are exactly
/// `cargo install --locked cargo-audit` and then `cargo audit --deny warnings`, so no step in
/// between can rewrite the config or the lockfile; no line of the job adds an `--ignore` or sets
/// `if:`, `continue-on-error:`, `needs:`, `shell:`, `working-directory:` or `defaults:`; and the
/// workflow sets no top-level `defaults:`. Not checked: a `uses:` step, which runs an action that
/// could rewrite either file. Fails closed: a workflow without the job reports that.
fn supply_chain_job_problems(workflow: &str) -> Vec<String> {
    let Some(keys) = workflow_job_keys(workflow, "supply-chain") else {
        return vec!["no `supply-chain` job".to_string()];
    };
    let mut problems = Vec::new();
    let runs: Vec<&str> = keys
        .iter()
        .copied()
        .filter(|key| key.starts_with("run:"))
        .collect();
    if runs
        != [
            "run: cargo install --locked cargo-audit",
            "run: cargo audit --deny warnings",
        ]
    {
        problems.push(format!(
            "the job's steps are not exactly the install and `cargo audit --deny warnings`: {runs:?}"
        ));
    }
    for key in &keys {
        let weakens = [
            "if:",
            "continue-on-error:",
            "needs:",
            "shell:",
            "working-directory:",
            "defaults:",
        ]
        .iter()
        .any(|k| key.starts_with(k));
        if weakens || key.contains("--ignore") {
            problems.push(format!("`{key}` can let an advisory through"));
        }
    }
    if workflow.lines().any(|line| line.starts_with("defaults:")) {
        problems.push("a workflow-level `defaults:` reaches the audit step".to_string());
    }
    problems
}

/// The solver lane still runs the clippy fence: `cargo clippy -p <crate> --all-targets --features
/// solver -- -D warnings` for each crate that depends on z3, the only lane where the z3 paths
/// of its `disallowed-methods` fence resolve. Fails closed: no `solver` job reports that.
fn solver_lane_problems(workflow: &str) -> Vec<String> {
    let Some(keys) = workflow_job_keys(workflow, "solver") else {
        return vec!["no `solver` job".to_string()];
    };
    ["sigil-compiler", "sigil-runtime"]
        .iter()
        .filter(|krate| {
            let lint = format!(
                "run: cargo clippy -p {krate} --all-targets --features solver -- -D warnings"
            );
            !keys.contains(&lint.as_str())
        })
        .map(|krate| format!("the solver lane no longer lints {krate} with z3 compiled"))
        .collect()
}

/// The supply-chain audit runs with no ignore: there is no `.cargo/audit.toml`. The lane's one
/// ignore (RUSTSEC-2026-0295, a use-after-free in z3 0.12.1's `ApplyResult`, residual risk
/// SR-031) ran from 2026-10-03 until the upgrade to z3 0.21.1, where it is fixed. It set the bar
/// an ignore must clear: a fence that keeps the advisory unreachable, an Accepted
/// `docs/RESIDUAL_RISKS.md` row with a tracking issue, and a pin of the config's whole effective
/// content, since `severity_threshold`, `[target]`, `[yanked]` and the database keys can all hide
/// findings. Adding a config is therefore a reviewed change to this test. The job that reads the
/// lockfile and the lane that enforces the clippy fence stay pinned as before. SC-P4: both
/// readers are shown planted inputs.
#[test]
fn supply_chain_audit_has_no_ignore_config() {
    let root = crates_root()
        .parent()
        .expect("crates/ sits in the repository root")
        .to_path_buf();
    assert!(
        !root.join(".cargo/audit.toml").exists(),
        "a cargo-audit config appeared: an ignore needs a fence that keeps the advisory \
         unreachable, an Accepted docs/RESIDUAL_RISKS.md row with a tracking issue, and this test \
         pinning the config's whole effective content, in the same commit"
    );
    let ci = fs::read_to_string(root.join(".github/workflows/ci.yml"))
        .unwrap_or_else(|e| panic!("failed to read .github/workflows/ci.yml: {e}"));
    assert_eq!(
        supply_chain_job_problems(&ci),
        Vec::<String>::new(),
        "the supply-chain job's steps or keys changed in a way this pin reads as weakening it"
    );
    assert_eq!(
        solver_lane_problems(&ci),
        Vec::<String>::new(),
        "the lane that enforces the clippy fence stopped running it"
    );

    let job = |body: &str| format!("jobs:\n  supply-chain:\n    steps:\n{body}\n  test:\n");
    let install = "      - run: cargo install --locked cargo-audit";
    let audit_step = "      - run: cargo audit --deny warnings";
    let gating = format!("{install}\n{audit_step}");
    assert!(supply_chain_job_problems(&job(&gating)).is_empty());
    for weakened in [
        format!("{install}\n      - run: cargo audit --deny warnings --ignore RUSTSEC-2099-0001"),
        format!("{gating}\n        continue-on-error: true"),
        format!("    if: false\n{gating}"),
        format!("    needs: [skipped]\n{gating}"),
        format!("    defaults:\n      run:\n        shell: sh\n{gating}"),
        format!("{install}\n{audit_step}\n        working-directory: elsewhere"),
        format!("{install}\n      - run: rm .cargo/audit.toml\n{audit_step}"),
        format!("{install}\n      - run: cargo audit"),
    ] {
        assert!(
            !supply_chain_job_problems(&job(&weakened)).is_empty(),
            "missed a weakened audit job: {weakened}"
        );
    }
    assert!(!supply_chain_job_problems("jobs:\n  test:\n").is_empty());
    assert!(
        !supply_chain_job_problems(&format!(
            "defaults:\n  run:\n    shell: sh\n{}",
            job(&gating)
        ))
        .is_empty()
    );
    let solver = |crates: &[&str]| {
        let steps: String = crates
            .iter()
            .map(|krate| {
                format!("      - run: cargo clippy -p {krate} --all-targets --features solver -- -D warnings\n")
            })
            .collect();
        format!("jobs:\n  solver:\n    steps:\n{steps}  test:\n")
    };
    assert!(solver_lane_problems(&solver(&["sigil-compiler", "sigil-runtime"])).is_empty());
    assert_eq!(solver_lane_problems(&solver(&["sigil-compiler"])).len(), 1);
    assert!(!solver_lane_problems("jobs:\n  test:\n").is_empty());
}

/// This file, relative to `crates/`: the one file the scans below exempt, because it names what
/// they look for. Exempted by exact path, so a namesake elsewhere is still scanned.
const FENCE_TEST: &str = "sigil-compiler/tests/z3_guard_fences.rs";

/// Is `needle`, found at byte `at` of `text`, a whole word: no identifier character on either
/// side?
fn is_word_at(text: &str, at: usize, needle: &str) -> bool {
    let boundary = |c: Option<char>| c.is_none_or(|c| !(c.is_ascii_alphanumeric() || c == '_'));
    boundary(text[..at].chars().next_back()) && boundary(text[at + needle.len()..].chars().next())
}

fn names_word(text: &str, word: &str) -> bool {
    text.match_indices(word)
        .any(|(at, _)| is_word_at(text, at, word))
}

/// Does a code line name something only a lowering or a redirect of the fence lints would use?
/// That is `disallowed_types` (clippy.toml has had no entry for it since the z3 0.21.1 upgrade,
/// and no carve-out of it may exist), its pre-rename name
/// `disallowed_type` (clippy still maps it once `renamed_and_removed_lints` is allowed), the
/// pre-rename `disallowed_method`, and `CLIPPY_CONF_DIR` (a build script can set it with
/// `cargo:rustc-env`). Any mention counts, so a multi-line attribute cannot split a name from its
/// `allow(`. The census-pinned `disallowed_methods` carve-outs do not match, since the old names
/// need a word boundary after them. The `style` and `all` groups are checked as attributes, by
/// `attribute_silences_a_fence`, where a strengthening `deny` can be told apart.
fn names_a_fence_silencer(line: &str) -> bool {
    [
        "clippy::disallowed_types",
        "clippy::disallowed_type",
        "clippy::disallowed_method",
        "CLIPPY_CONF_DIR",
    ]
    .iter()
    .any(|name| names_word(line, name))
}

/// Every attribute that opens a code line (`#[` or `#![` after indentation), paired with its
/// 1-based line. Its text runs to the matching `]`, joined across lines, with whitespace, `//`
/// comments and string contents removed (a `reason = "..."` keeps only its quotes), so a bracket
/// or a lint name in a comment or a string can neither end nor fake the attribute. Not seen: an
/// attribute that does not open its line, a second attribute on the same line, and one a macro
/// expands to. rustfmt, which the `checks` lane enforces, puts item and statement attributes on
/// lines of their own.
fn line_attributes(source: &str) -> Vec<(usize, String)> {
    let lines: Vec<&str> = source.lines().collect();
    let mut attributes = Vec::new();
    let mut index = 0;
    while index < lines.len() {
        let opening = lines[index].trim_start();
        if is_comment_line(lines[index])
            || !(opening.starts_with("#[") || opening.starts_with("#!["))
        {
            index += 1;
            continue;
        }
        let first = index;
        let (mut text, mut depth, mut in_string, mut escaped) = (String::new(), 0, false, false);
        'attribute: while index < lines.len() {
            let part = if index == first {
                opening
            } else {
                lines[index]
            };
            let mut chars = part.chars().peekable();
            while let Some(c) = chars.next() {
                if in_string {
                    if escaped {
                        escaped = false;
                    } else if c == '\\' {
                        escaped = true;
                    } else if c == '"' {
                        in_string = false;
                        text.push(c);
                    }
                    continue;
                }
                match c {
                    '/' if chars.peek() == Some(&'/') => break,
                    '"' => {
                        in_string = true;
                        text.push(c);
                    }
                    '[' => {
                        depth += 1;
                        text.push(c);
                    }
                    ']' => {
                        depth -= 1;
                        text.push(c);
                        if depth == 0 {
                            break 'attribute;
                        }
                    }
                    c if c.is_whitespace() => {}
                    c => text.push(c),
                }
            }
            index += 1;
        }
        attributes.push((first + 1, text));
        index += 1;
    }
    attributes
}

/// Does an attribute, as `line_attributes` renders it, lower a fence lint some way the line scan
/// and the carve-out census miss?
/// - `warnings` in an `allow`, `expect` or `warn`. An `allow` or `expect` silences every
///   warn-level lint, clippy's included, and a `warn` sets the group back to warn, which beats the
///   command line's `-D warnings` inside its scope.
/// - The `style` or `all` group in an `allow` or `expect`: both groups hold `disallowed_types`
///   and `disallowed_methods`.
/// - `disallowed_methods` in any form but the census's plain `#[allow(clippy::disallowed_methods)]`.
///   An `expect`, a `cfg_attr`, or a second lint in the list is a carve-out the census never
///   counts.
fn attribute_silences_a_fence(attribute: &str) -> bool {
    let quiets = attribute.contains("allow(") || attribute.contains("expect(");
    let warns = quiets || attribute.contains("warn(");
    (warns && names_word(attribute, "warnings"))
        || (quiets
            && (names_word(attribute, "clippy::style") || names_word(attribute, "clippy::all")))
        || (attribute.contains("clippy::disallowed_methods")
            && attribute != "#[allow(clippy::disallowed_methods)]")
}

/// Does a command lower lint levels with `-A`, `--allow` (bare, `=value`, or `-Alint`) or
/// `--cap-lints`? Only the first command in the line counts, up to a `|`, `;` or `&`, so
/// `| grep -A3` is not the command's flag, and `--allow-dirty` is not `--allow`.
fn lowers_lints(command: &str) -> bool {
    let first = command.split(['|', ';', '&']).next().unwrap_or_default();
    first
        .split(|c: char| c.is_whitespace() || matches!(c, '"' | '\'' | '=' | ',' | '[' | ']'))
        .any(|token| {
            token == "-A"
                || token == "--allow"
                || token == "--cap-lints"
                || (token.starts_with("-A") && token.len() > 2)
        })
}

/// Config outside the source that could switch a fence lint off for a whole crate or build:
/// - a second clippy config anywhere under `crates/`, or a root `.clippy.toml` (clippy reads the
///   one nearest each crate's manifest);
/// - a `lints` table in the root or a member manifest, as a header, dotted keys or an inline
///   table. Any such table counts, strengthening ones included, until this check reads levels;
/// - `CLIPPY_CONF_DIR`, a clippy lint name, or a lint-lowering flag in a `.cargo/config`;
/// - in a workflow, `CLIPPY_CONF_DIR`, or a lint-lowering flag on a `RUSTFLAGS` or `cargo clippy`
///   line.
///
/// Not seen: a composite action or a script that a workflow runs, `RUSTFLAGS` set through a YAML
/// block scalar or another variable, and anything outside the repository.
fn lint_config_problems(root: &Path) -> Vec<String> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let entries =
            fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir {} failed: {e}", dir.display()));
        for entry in entries {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                if path.file_name().is_some_and(|n| n != "target") {
                    walk(&path, out);
                }
            } else {
                out.push(path);
            }
        }
    }
    let read = |path: &Path| {
        fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()))
    };
    let mut problems = Vec::new();
    let mut under_crates = Vec::new();
    walk(&root.join("crates"), &mut under_crates);
    let mut configs: Vec<PathBuf> = under_crates
        .into_iter()
        .filter(|p| {
            p.file_name()
                .is_some_and(|n| n == "clippy.toml" || n == ".clippy.toml")
        })
        .collect();
    configs.push(root.join(".clippy.toml"));
    for config in configs.into_iter().filter(|p| p.exists()) {
        problems.push(format!("a second clippy config: {}", config.display()));
    }
    let mut manifests = vec![root.join("Cargo.toml")];
    for entry in fs::read_dir(root.join("crates")).expect("crates/ is readable") {
        let manifest = entry.expect("dir entry").path().join("Cargo.toml");
        if manifest.is_file() {
            manifests.push(manifest);
        }
    }
    let lints_table = |line: &str| {
        let line = line.trim_start();
        [
            "[lints",
            "[workspace.lints",
            "lints.",
            "lints =",
            "lints=",
            "workspace.lints",
        ]
        .iter()
        .any(|start| line.starts_with(start))
    };
    for manifest in &manifests {
        if read(manifest).lines().any(lints_table) {
            problems.push(format!("a lints table in {}", manifest.display()));
        }
    }
    for config in [".cargo/config", ".cargo/config.toml"] {
        let path = root.join(config);
        if !path.exists() {
            continue;
        }
        for line in read(&path).lines() {
            if names_word(line, "CLIPPY_CONF_DIR")
                || line.contains("clippy::")
                || lowers_lints(line)
            {
                problems.push(format!("lint config in {config}: `{}`", line.trim()));
            }
        }
    }
    let workflows = root.join(".github/workflows");
    for entry in fs::read_dir(&workflows).expect(".github/workflows is readable") {
        let path = entry.expect("dir entry").path();
        if path.extension().is_none_or(|e| e != "yml") {
            continue;
        }
        for (index, line) in read(&path).lines().enumerate() {
            let code = line.trim_start();
            if code.starts_with('#') {
                continue;
            }
            let flags = ["RUSTFLAGS", "cargo clippy"].iter().any(|keyword| {
                code.find(keyword)
                    .is_some_and(|at| lowers_lints(&code[at..]))
            });
            if names_word(code, "CLIPPY_CONF_DIR") || flags {
                problems.push(format!("{}:{}: `{code}`", path.display(), index + 1));
            }
        }
    }
    problems
}

/// Every route these detectors know for switching a z3 fence lint off is closed in the tree:
/// - the names `names_a_fence_silencer` lists, anywhere in code. clippy's own diagnostic
///   suggests the first: "to override `-D warnings` add `#[allow(clippy::disallowed_types)]`";
/// - the attributes `attribute_silences_a_fence` lists;
/// - the config routes `lint_config_problems` lists.
///
/// Each detector states what it cannot see, and none of them is a proof that no other route
/// exists. The lint they guard is `disallowed_methods`, the fragment guard's fence
/// (`docs/specs/z3-fragment-guard.md` section 7), whose carve-outs the census above pins.
/// SC-P4: each detector is shown planted inputs.
#[test]
fn nothing_can_silence_the_z3_fences() {
    let mut sites = Vec::new();
    for file in all_rs_files() {
        if rel(&file) == FENCE_TEST {
            continue;
        }
        let source = fs::read_to_string(&file)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", file.display()));
        for (index, line) in source.lines().enumerate() {
            if !is_comment_line(line) && names_a_fence_silencer(line) {
                sites.push(format!("{}:{}", rel(&file), index + 1));
            }
        }
        for (line, attribute) in line_attributes(&source) {
            if attribute_silences_a_fence(&attribute) {
                sites.push(format!("{}:{line}: {attribute}", rel(&file)));
            }
        }
    }
    assert!(
        sites.is_empty(),
        "these lines can silence a z3 clippy fence: {sites:?}"
    );
    let root = crates_root()
        .parent()
        .expect("crates/ sits in the repository root")
        .to_path_buf();
    assert_eq!(
        lint_config_problems(&root),
        Vec::<String>::new(),
        "lint config can switch a z3 clippy fence off"
    );

    for planted in [
        "#[allow(clippy::disallowed_types)]",
        "#[allow(renamed_and_removed_lints, clippy::disallowed_type)]",
        "#[expect(clippy::disallowed_method)]",
        "    clippy::disallowed_types,",
        "println!(\"cargo:rustc-env=CLIPPY_CONF_DIR=elsewhere\");",
    ] {
        assert!(names_a_fence_silencer(planted), "missed: {planted}");
    }
    for clean in [
        "#[allow(clippy::too_many_arguments)]",
        "#[allow(clippy::disallowed_methods)]",
        "#![deny(clippy::all)]",
        "let style = clippy_all;",
    ] {
        assert!(!names_a_fence_silencer(clean), "false hit: {clean}");
    }
    let planted_source = "#![allow(warnings)]\n\
                          #[expect(\n    unused,\n    warnings,\n    reason = \"a ] in a reason\"\n)]\n\
                          fn f() {}\n\
                          #[cfg_attr(test, allow(clippy::disallowed_methods))]\n\
                          #[expect(clippy::disallowed_methods)]\n\
                          #[allow(dead_code, clippy::disallowed_methods)]\n\
                          #![warn(warnings)]\n\
                          #![allow(clippy::style)]\n\
                          #[allow(\n    unused, // a ] in a comment\n    clippy::all\n)]\n\
                          #[cfg_attr(feature = \"solver\", allow(clippy::style))]\n";
    let found: Vec<usize> = line_attributes(planted_source)
        .into_iter()
        .filter(|(_, attribute)| attribute_silences_a_fence(attribute))
        .map(|(line, _)| line)
        .collect();
    assert_eq!(
        found,
        [1, 2, 8, 9, 10, 11, 12, 13, 17],
        "the attribute scan missed a planted silencer"
    );
    let clean_source = "#[allow(clippy::disallowed_methods)] // census-pinned\n\
                        #[deny(warnings)]\n\
                        #![deny(clippy::all)]\n\
                        #![warn(clippy::all)]\n\
                        #[doc = \"see [this]\"]\n\
                        #[allow(unused, reason = \"silences warnings from codegen\")]\n\
                        let s = \"#[allow(warnings)]\";\n";
    let found: Vec<(usize, String)> = line_attributes(clean_source)
        .into_iter()
        .filter(|(_, attribute)| attribute_silences_a_fence(attribute))
        .collect();
    assert!(found.is_empty(), "false hits: {found:?}");

    // A planted miniature repository carries every config route at once, and a clean twin none.
    let plant = |files: &[(&str, &str)]| {
        let dir = tempfile::tempdir().expect("a scratch directory");
        for (path, text) in files {
            let path = dir.path().join(path);
            fs::create_dir_all(path.parent().expect("a parent")).expect("create the parent");
            fs::write(&path, text).expect("write the planted file");
        }
        dir
    };
    let clean_tree = [
        ("Cargo.toml", "[workspace]\nmembers = [\"crates/x\"]\n"),
        ("crates/x/Cargo.toml", "[package]\nname = \"x\"\n"),
        ("crates/y/Cargo.toml", "[package]\nname = \"y\"\n"),
        (
            ".github/workflows/ci.yml",
            "env:\n  RUSTFLAGS: -L z3/bin\nsteps:\n  \
             - run: cargo clippy --fix --allow-dirty -- -D warnings -D clippy::unwrap_used \
             2>&1 | grep -A3 error\n",
        ),
    ];
    let clean = plant(&clean_tree);
    assert_eq!(lint_config_problems(clean.path()), Vec::<String>::new());
    let mut weakened_tree = clean_tree.to_vec();
    weakened_tree.extend([
        (
            "crates/x/Cargo.toml",
            "[package]\nname = \"x\"\n\n[lints.clippy]\ndisallowed_types = \"allow\"\n",
        ),
        (
            "crates/y/Cargo.toml",
            "[package]\nname = \"y\"\nlints.clippy.disallowed_types = \"allow\"\n",
        ),
        ("crates/x/clippy.toml", ""),
        (
            ".cargo/config.toml",
            "[env]\nCLIPPY_CONF_DIR = \"elsewhere\"\n",
        ),
        (
            ".github/workflows/lint.yml",
            "env:\n  CLIPPY_CONF_DIR: elsewhere\n  RUSTFLAGS: --cap-lints=warn\nsteps:\n  \
             - run: cargo clippy -- -A clippy::style\n",
        ),
    ]);
    let weakened = plant(&weakened_tree);
    let problems = lint_config_problems(weakened.path());
    for (route, expected) in [
        ("a second clippy config", 1),
        ("a lints table in", 2),
        ("lint config in .cargo/config.toml", 1),
        ("CLIPPY_CONF_DIR: elsewhere", 1),
        ("RUSTFLAGS: --cap-lints=warn", 1),
        ("cargo clippy -- -A clippy::style", 1),
    ] {
        assert_eq!(
            problems.iter().filter(|p| p.contains(route)).count(),
            expected,
            "planted route `{route}` in {problems:?}"
        );
    }
    assert_eq!(
        problems.len(),
        7,
        "one problem per planted route: {problems:?}"
    );
}
