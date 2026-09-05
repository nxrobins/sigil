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
    assert!(
        code.contains("Int::from_str(ctx, &decimal)"),
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
