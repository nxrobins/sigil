//! Z3 corpus harness — adversarial proof-layer test surface.
//!
//! Walks `crates/sigil-compiler/tests/z3_corpus/` and validates that each
//! fixture behaves according to its declared expectation. Three contracts are
//! supported:
//!
//! * `// expect-error: <substring>` — compilation MUST fail; one of the
//!   diagnostic messages must contain the substring (case-insensitive). Such
//!   fixtures must also have a `// MUTATION_SITE` line; after deleting that
//!   line the program must compile cleanly. The mutation check is what makes
//!   the corpus test the *attack* rather than incidental properties of the
//!   source — without it, a fixture that "rejects for the wrong reason"
//!   would slip through.
//!
//! * `// expect-shape: <probe-name>` — compilation MUST succeed. The named
//!   probe is run against the resulting AIR program. AIR-shape probes are
//!   what makes the AIR-coverage closure (handle/region body lowering)
//!   load-bearing: without an explicit assertion that specific AirStmt nodes
//!   are present, a future regression silently re-introducing the drop bug
//!   would still pass a "compiles cleanly" test.
//!
//! * `// expect-ok` — compilation MUST succeed; no further assertions. Used
//!   for negative controls.
//!
//! All fixtures are loaded sorted by filename and re-loaded in reverse order
//! to verify order-independence (no shared state between fixtures).

#![cfg(feature = "solver")]

use std::path::{Path, PathBuf};

use sigil_compiler::air::{AirProgram, AirStmt};
use sigil_compiler::{CompileError, compile_module};

const CORPUS_SUBDIR: &str = "z3_corpus";

/// Top-level test: every fixture passes its declared contract, in two orders.
#[test]
fn z3_corpus_passes_in_both_orders() {
    let mut fixtures = load_fixtures();
    assert!(
        fixtures.len() >= 6,
        "z3_corpus must hold at least 6 fixtures (got {})",
        fixtures.len()
    );

    let forward: Vec<String> = fixtures.iter().map(|f| f.name.clone()).collect();
    for fixture in &fixtures {
        run_fixture(fixture);
    }

    fixtures.reverse();
    let reverse: Vec<String> = fixtures.iter().map(|f| f.name.clone()).collect();
    assert_ne!(
        forward, reverse,
        "fixture order should differ on reverse run"
    );
    for fixture in &fixtures {
        run_fixture(fixture);
    }
}

#[derive(Debug, Clone)]
struct Fixture {
    name: String,
    source: String,
    expectation: Expectation,
}

#[derive(Debug, Clone)]
enum Expectation {
    /// Compilation must fail; one diagnostic message contains the substring
    /// (case-insensitive). Mutation contract: there must be a single line
    /// containing `// MUTATION_SITE`; after deletion the program must
    /// compile cleanly.
    Error { substring: String },
    /// Compilation must succeed; the named probe is then run against the AIR.
    Shape { probe: String },
    /// Compilation must succeed. No further assertions.
    Ok,
}

fn load_fixtures() -> Vec<Fixture> {
    let dir = corpus_dir();
    assert!(
        dir.is_dir(),
        "z3_corpus directory missing: {}",
        dir.display()
    );

    let mut fixtures = Vec::new();
    for entry in std::fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().is_some_and(|ext| ext == "sigil") {
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            let source = std::fs::read_to_string(&path).unwrap();
            let expectation = parse_expectation(&source).unwrap_or_else(|| {
                panic!("fixture `{name}` lacks a recognized // expect-* annotation")
            });
            fixtures.push(Fixture {
                name,
                source,
                expectation,
            });
        }
    }
    fixtures.sort_by(|a, b| a.name.cmp(&b.name));
    fixtures
}

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join(CORPUS_SUBDIR)
}

fn parse_expectation(source: &str) -> Option<Expectation> {
    for line in source.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("// expect-error:") {
            return Some(Expectation::Error {
                substring: rest.trim().to_string(),
            });
        }
        if let Some(rest) = trimmed.strip_prefix("// expect-shape:") {
            return Some(Expectation::Shape {
                probe: rest.trim().to_string(),
            });
        }
        if trimmed.starts_with("// expect-ok") {
            return Some(Expectation::Ok);
        }
        if !trimmed.starts_with("//") && !trimmed.is_empty() {
            return None;
        }
    }
    None
}

fn run_fixture(fixture: &Fixture) {
    match &fixture.expectation {
        Expectation::Error { substring } => {
            let err = match compile_module(&fixture.source) {
                Err(e) => e,
                Ok(_) => panic!(
                    "fixture `{}` declared `expect-error: {substring}` but compiled cleanly",
                    fixture.name
                ),
            };
            let needle = substring.to_lowercase();
            let matched = err.diagnostics().iter().any(|d| {
                d.code().to_string().to_lowercase().contains(&needle)
                    || d.message().to_lowercase().contains(&needle)
            });
            assert!(
                matched,
                "fixture `{}`: no diagnostic matched `{substring}` in code or message. \
                 Diagnostics: {:?}",
                fixture.name,
                collect_messages(&err)
            );

            // Production budgets must decide every corpus query. A C004 means
            // either the measured budget is no longer sufficient or the query
            // family needs a new decidability and complexity audit.
            let c004_count = err
                .diagnostics()
                .iter()
                .filter(|d| d.code().as_str() == "C004")
                .count();
            assert_eq!(
                c004_count, 0,
                "fixture `{}`: production rlimit produced {} C004 diagnostic(s). \
                 Either the rlimit is too tight (measure and raise) or a new \
                 query is outside the decidable fragment (see docs/z3-theory-inventory.md).",
                fixture.name, c004_count
            );

            // Mutation contract: delete the MUTATION_SITE line and recompile.
            let mutated = mutate_source(&fixture.source).unwrap_or_else(|| {
                panic!(
                    "fixture `{}` is `expect-error` but has no `// MUTATION_SITE` line",
                    fixture.name
                )
            });
            assert_ne!(
                mutated, fixture.source,
                "fixture `{}`: mutation produced identical source",
                fixture.name
            );
            match compile_module(&mutated) {
                Ok(_) => {}
                Err(e) => panic!(
                    "fixture `{}`: post-mutation source must compile cleanly. Got: {:?}",
                    fixture.name,
                    collect_messages(&e),
                ),
            }
        }
        Expectation::Shape { probe } => {
            let compilation = compile_module(&fixture.source).unwrap_or_else(|e| {
                panic!(
                    "fixture `{}` declared `expect-shape: {probe}` but failed to compile: {:?}",
                    fixture.name,
                    collect_messages(&e),
                )
            });
            run_shape_probe(probe, &fixture.name, &compilation.air);
        }
        Expectation::Ok => {
            let _ = compile_module(&fixture.source).unwrap_or_else(|e| {
                panic!(
                    "fixture `{}` declared `expect-ok` but failed to compile: {:?}",
                    fixture.name,
                    collect_messages(&e),
                )
            });
        }
    }
}

fn collect_messages(err: &CompileError) -> Vec<String> {
    err.diagnostics()
        .iter()
        .map(|d| d.message().to_string())
        .collect()
}

/// Delete the line containing `// MUTATION_SITE` (exactly one expected).
/// Returns `None` if no such line exists.
fn mutate_source(source: &str) -> Option<String> {
    let mut found = false;
    let mut out = Vec::with_capacity(source.lines().count());
    for line in source.lines() {
        if line.contains("// MUTATION_SITE") {
            assert!(!found, "fixture has multiple `// MUTATION_SITE` lines");
            found = true;
            continue;
        }
        out.push(line);
    }
    if !found {
        return None;
    }
    Some(out.join("\n"))
}

fn run_shape_probe(probe: &str, fixture_name: &str, air: &AirProgram) {
    match probe {
        "handle_inner_assign" | "region_inner_assign" => {
            let dummy = air
                .functions
                .iter()
                .find(|f| f.name.contains("dummy"))
                .unwrap_or_else(|| panic!("fixture `{fixture_name}`: no `dummy` function in AIR"));
            let assigns: usize = dummy
                .blocks
                .iter()
                .flat_map(|b| &b.stmts)
                .filter(|s| matches!(s, AirStmt::Assign { .. }))
                .count();
            // Both let bindings inside the scoped body must survive AIR
            // lowering as assignments.
            assert!(
                assigns >= 2,
                "probe `{probe}` on `{fixture_name}`: expected ≥2 AirStmt::Assign \
                 inside `dummy` body (proves let bindings inside scoped body \
                 were lowered, not silently dropped); found {assigns}."
            );

            // Region-specific: also assert RegionBegin/RegionEnd bookend.
            if probe == "region_inner_assign" {
                let has_begin = dummy
                    .blocks
                    .iter()
                    .flat_map(|b| &b.stmts)
                    .any(|s| matches!(s, AirStmt::RegionBegin { .. }));
                let has_end = dummy
                    .blocks
                    .iter()
                    .flat_map(|b| &b.stmts)
                    .any(|s| matches!(s, AirStmt::RegionEnd { .. }));
                assert!(
                    has_begin && has_end,
                    "probe `{probe}` on `{fixture_name}`: expected RegionBegin/RegionEnd \
                     bookend stmts in AIR"
                );
            }
        }
        other => panic!("unknown shape probe `{other}` in fixture `{fixture_name}`"),
    }
}

/// Require every production AIR capability dispatch to identify its theory
/// within the preceding three lines. Test-only solver calls are outside the
/// production inventory.
#[test]
fn every_solver_check_has_theory_comment() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("air_capability_v2")
        .join("mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));

    // Split into production / test halves at the `#[cfg(...test...)]`
    // module line. Only production sites must carry a `// theory:`
    // comment.
    let test_module_start = source
        .lines()
        .position(|l| l.trim_start().starts_with("#[cfg(all(test,"))
        .unwrap_or(source.lines().count());

    let lines: Vec<&str> = source.lines().collect();
    let mut missing: Vec<(usize, String)> = Vec::new();

    for (idx, line) in lines.iter().enumerate().take(test_module_start) {
        // Only real call sites — skip comment lines that mention
        // `check_direct` in prose, and the wrapper's DEFINITION line.
        let trimmed = line.trim_start();
        if trimmed.starts_with("//") || trimmed.starts_with("///") {
            continue;
        }
        if trimmed.starts_with("fn check_direct") {
            continue;
        }
        if !line.contains("check_direct(solver)") {
            continue;
        }
        // Look within the 3 lines IMMEDIATELY above for `// theory:`.
        let lo = idx.saturating_sub(3);
        let has_theory = lines[lo..idx]
            .iter()
            .any(|l| l.trim_start().starts_with("// theory:"));
        if !has_theory {
            missing.push((idx + 1, line.trim().to_string()));
        }
    }

    assert!(
        missing.is_empty(),
        "air_capability_v2/mod.rs has {} production `check_direct(solver)` \
         dispatch site(s) without a `// theory:` comment in the 3 lines \
         above. Each new dispatch site must add a `// theory:` annotation \
         and a row in docs/z3-theory-inventory.md §2. Missing: {:?}",
        missing.len(),
        missing
    );
}

/// Drive the complete corpus and require observed operations and sorts to
/// equal the hand-maintained inventory. The allowlist may contain only the
/// observed set plus structural Bool constants. Canary binaries do not record
/// observations, so they cannot pollute this process-wide accumulator.
#[test]
fn observed_fragment_matches_the_inventory_manifest() {
    use std::collections::BTreeSet;

    sigil_compiler::z3_fragment_guard::reset_observations_for_test();
    for fixture in load_fixtures() {
        // Failing fixtures still run their Z3 queries before (or while)
        // producing diagnostics — compile both kinds, ignore outcomes.
        let _ = compile_module(&fixture.source);
    }

    let (decls, sorts) = sigil_compiler::z3_fragment_guard::observed_snapshot();
    let expected_decls: BTreeSet<String> = [
        "ANUM",
        "BAND",
        "BNUM",
        "EQ",
        "GE",
        "GT",
        "LE",
        "LT",
        "NOT",
        "ULEQ",
        "UNINTERPRETED",
    ]
    .iter()
    .map(|s| (*s).to_string())
    .collect();
    let expected_sorts: BTreeSet<String> = ["BV", "Bool", "Int"]
        .iter()
        .map(|s| (*s).to_string())
        .collect();

    assert_eq!(
        decls, expected_decls,
        "observed DeclKinds drifted from the inventory pin (ET-Z4): a \
         missing op needs a corpus fixture (never a subset assertion); an \
         extra op means the inventory doc + allowlist must be amended \
         DOC-FIRST"
    );
    assert_eq!(
        sorts, expected_sorts,
        "observed SortKinds drifted from the inventory pin (ET-Z4)"
    );

    // Allowlist exactness: TRUE/FALSE are the ONLY allowed-but-unobserved
    // entries (structural Bool constants Z3 may surface; rejecting the
    // constant `true` would be absurd). Anything else allowed-but-unused
    // is bloat — shrink the allowlist or add the exercising fixture.
    let mut with_consts = expected_decls.clone();
    with_consts.insert("TRUE".to_string());
    with_consts.insert("FALSE".to_string());
    assert_eq!(
        sigil_compiler::z3_fragment_guard::allowed_decl_kind_names(),
        with_consts,
        "the guard's allowlist drifted from observed ∪ {{TRUE, FALSE}}"
    );
}

/// Lock the four production AIR capability dispatch sites documented in the
/// theory inventory. A deliberate new site must update both authorities.
#[test]
fn production_solver_check_count_matches_inventory() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("air_capability_v2")
        .join("mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    let test_module_start = source
        .lines()
        .position(|l| l.trim_start().starts_with("#[cfg(all(test,"))
        .unwrap_or(source.lines().count());
    let count: usize = source
        .lines()
        .take(test_module_start)
        .filter(|l| {
            // Real dispatch sites only — skip comments + the
            // `fn check_direct` definition line itself.
            let trimmed = l.trim_start();
            if trimmed.starts_with("//") || trimmed.starts_with("///") {
                return false;
            }
            if trimmed.starts_with("fn check_direct") {
                return false;
            }
            l.contains("check_direct(solver)")
        })
        .count();
    const INVENTORY_DOCUMENTED_COUNT: usize = 4;
    assert_eq!(
        count, INVENTORY_DOCUMENTED_COUNT,
        "air_capability_v2/mod.rs has {count} production dispatch sites; \
         docs/z3-theory-inventory.md §2 documents {INVENTORY_DOCUMENTED_COUNT}. \
         Either revert the new site or update the inventory AND this constant."
    );
}
