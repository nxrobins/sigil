//! Integration test harness for the SIGIL compiler spec-grade test corpus.
//!
//! Walks `tests/compile/`, `tests/reject/`, `tests/runtime/`, and `tests/attack/`
//! directories and validates that each program behaves as expected.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use sigil_compiler::CompileError;
use sigil_compiler::compile_module;
use sigil_runtime::RuntimeHost;

const WORKSPACE_ROOT: &str = env!("CARGO_MANIFEST_DIR");

fn workspace_tests_dir() -> std::path::PathBuf {
    Path::new(WORKSPACE_ROOT)
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests")
}

fn read_test_files(subdir: &str) -> Vec<(String, String)> {
    let dir = workspace_tests_dir().join(subdir);
    if !dir.exists() {
        return Vec::new();
    }
    let mut files: Vec<(String, String)> = Vec::new();
    for entry in fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().is_some_and(|ext| ext == "sigil") {
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            let source = fs::read_to_string(&path).unwrap();
            files.push((name, source));
        }
    }
    files.sort_by(|a, b| a.0.cmp(&b.0));
    files
}

/// What a fixture's header comment claims should happen to it.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Expect {
    /// `// expect-error: T044, T088` — the EXACT set of diagnostic codes the
    /// compiler must emit for this fixture.
    Codes(BTreeSet<String>),
    /// `// expect-runtime: FuelExhausted` — the fixture compiles, and the
    /// named outcome must happen when it runs.
    Runtime(String),
}

/// Parse the fixture header.
///
/// `expect-error` carries diagnostic CODES, not prose. That is the whole point
/// of the format: codes are compared against [`Diagnostic::code`], a structured
/// field, so the comparison cannot be satisfied by the fixture's own text.
///
/// The previous format carried a prose fragment matched against
/// `format!("{errors:?}")`. Because [`CompileError`] holds the `SourceMap` and
/// `SourceFile` is `{ name: String, text: String }` — both deriving `Debug` —
/// that blob contained the entire fixture source, INCLUDING the expect-comment
/// being searched for. Every `expect-error` assertion in `tests/reject/` and
/// `tests/attack/` was therefore satisfied by the comment it was checking, and
/// passed whenever the fixture failed to compile for any reason at all. Two
/// fixtures were already mis-annotated when this was found.
/// `expect_comment_cannot_satisfy_itself` pins the fix.
fn extract_expectation(source: &str) -> Option<Expect> {
    for line in source.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("// expect-error:") {
            return Some(Expect::Codes(parse_code_list(rest)));
        }
        if let Some(rest) = trimmed.strip_prefix("// expect-runtime:") {
            return Some(Expect::Runtime(rest.trim().to_string()));
        }
        // Stop searching after non-comment lines
        if !trimmed.starts_with("//") && !trimmed.is_empty() {
            break;
        }
    }
    None
}

/// Split `T044, T088` into a code set, rejecting anything that isn't shaped
/// like a diagnostic code. Without this check a leftover prose annotation
/// would parse as a one-element set and fail with a confusing set-mismatch
/// instead of naming the real problem.
///
/// The example codes here are deliberately ones already carrying direct test
/// references. `diagnostic_security_surface_is_censused` counts code tokens
/// found anywhere in a `crates/**/tests/` file — comments and string literals
/// included — so naming a gap-manifest code in illustrative prose would move
/// the direct-test-reference pin without any test actually exercising it.
fn parse_code_list(rest: &str) -> BTreeSet<String> {
    rest.split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(|s| {
            assert!(
                is_code_shaped(s),
                "`expect-error:` takes diagnostic codes (e.g. `T044, T088`), not prose; got `{s}`"
            );
            s.to_string()
        })
        .collect()
}

/// One to three uppercase letters followed by three digits: `O001`, `T278`, `P011`.
fn is_code_shaped(s: &str) -> bool {
    let letters = s.chars().take_while(char::is_ascii_uppercase).count();
    (1..=3).contains(&letters)
        && s.len() == letters + 3
        && s[letters..].chars().all(|c| c.is_ascii_digit())
}

/// The set of codes a compilation actually emitted.
fn emitted_codes(errors: &CompileError) -> BTreeSet<String> {
    errors
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect()
}

/// Assert the emitted code set equals the fixture's declared set.
///
/// Exact-set rather than "contains": a fixture that grows a spurious extra
/// diagnostic, or silently loses the one it exists to pin, must both fail.
/// The message prints the actual set so re-pinning is a copy-paste.
fn assert_expected_codes(
    kind: &str,
    name: &str,
    expected: &BTreeSet<String>,
    errors: &CompileError,
) {
    let actual = emitted_codes(errors);
    assert_eq!(
        actual,
        *expected,
        "{kind} test `{name}`: emitted diagnostic codes do not match its `expect-error:` header.\n  \
         expected: {}\n  actual:   {}\n  \
         If the new behaviour is correct, update the header to `// expect-error: {}`.\n  \
         First message: {}",
        format_codes(expected),
        format_codes(&actual),
        format_codes(&actual),
        errors
            .diagnostics()
            .first()
            .map(|d| d.message())
            .unwrap_or("<none>"),
    );
}

fn format_codes(codes: &BTreeSet<String>) -> String {
    if codes.is_empty() {
        "<none>".to_string()
    } else {
        codes.iter().cloned().collect::<Vec<_>>().join(", ")
    }
}

/// Corpus deletion floors — measured at the fixture-corpora upgrade (SC-P1:
/// pin the measured value). A corpus may GROW freely; shrinking below the
/// floor requires lowering the pin with a stated reason in the same commit.
/// A bare `!is_empty()` let all but one fixture vanish silently.
const COMPILE_CORPUS_FLOOR: usize = 15;
const REJECT_CORPUS_FLOOR: usize = 11;
const ATTACK_CORPUS_FLOOR: usize = 13;
const RUNTIME_CORPUS_FLOOR: usize = 3;

fn assert_corpus_floor(kind: &str, len: usize, floor: usize) {
    assert!(
        len >= floor,
        "{kind} corpus has {len} fixtures, below its deletion floor {floor}; if the          corpus genuinely shrank, lower the floor with a stated reason in the same commit"
    );
}

#[test]
fn compile_success_tests() {
    let files = read_test_files("compile");
    assert_corpus_floor("compile", files.len(), COMPILE_CORPUS_FLOOR);

    for (name, source) in &files {
        let result = compile_module(source);
        assert!(
            result.is_ok(),
            "compile test `{name}` should succeed but got error: {:?}",
            result.err()
        );
    }
}

#[test]
fn reject_tests() {
    let files = read_test_files("reject");
    assert_corpus_floor("reject", files.len(), REJECT_CORPUS_FLOOR);

    for (name, source) in &files {
        let result = compile_module(source);
        assert!(
            result.is_err(),
            "reject test `{name}` should fail compilation but succeeded"
        );

        // Every reject fixture must SAY what it rejects. Previously the
        // annotation was optional, so a fixture with no header asserted only
        // "something went wrong" — indistinguishable from a typo in the fixture.
        let expected = match extract_expectation(source) {
            Some(Expect::Codes(codes)) => codes,
            Some(Expect::Runtime(r)) => panic!(
                "reject test `{name}` carries `// expect-runtime: {r}`, but a reject fixture is \
                 rejected at COMPILE time — annotate it with `// expect-error: <CODE>` instead"
            ),
            None => panic!(
                "reject test `{name}` has no `// expect-error: <CODE>` header; every reject \
                 fixture must name the diagnostic codes it exists to pin"
            ),
        };
        assert_expected_codes("reject", name, &expected, &result.unwrap_err());
        assert_mutant_compiles_clean("reject", name, source);
    }
}

#[test]
fn runtime_tests() {
    let files = read_test_files("runtime");
    assert_corpus_floor("runtime", files.len(), RUNTIME_CORPUS_FLOOR);

    for (name, source) in &files {
        let expect = match extract_expectation(source) {
            Some(Expect::Runtime(r)) => r,
            Some(Expect::Codes(codes)) => {
                // A fixture in `runtime/` that is rejected at compile time is
                // still a legitimate pin — assert its codes and move on.
                let errors = compile_module(source)
                    .expect_err("runtime fixture declares `expect-error:` but compiled cleanly");
                assert_expected_codes("runtime", name, &codes, &errors);
                continue;
            }
            None => panic!(
                "runtime test `{name}` has no `// expect-runtime:` or `// expect-error:` header"
            ),
        };
        let compilation = match compile_module(source) {
            Ok(c) => c,
            Err(e) => panic!("runtime test `{name}` failed to compile: {e:?}"),
        };

        let mut host = RuntimeHost::new(compilation.runtime_module.fuel_budget);
        let boot_result = host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner);

        if expect.to_lowercase() == "fuelexhausted" {
            // Either bootstrap or message drain should produce FuelExhausted
            match boot_result {
                Err(e) if format!("{e}").contains("fuel") => continue,
                Ok(_) => {
                    let drain_result = host.drain_messages(100);
                    match drain_result {
                        Err(e) if format!("{e}").contains("fuel") => continue,
                        Err(e) => {
                            panic!("runtime test `{name}` expected FuelExhausted but got: {e}")
                        }
                        Ok(_) => panic!(
                            "runtime test `{name}` expected FuelExhausted but the drain \
                             completed cleanly"
                        ),
                    }
                }
                Err(e) => panic!("runtime test `{name}` expected FuelExhausted but got: {e}"),
            }
        } else {
            // Should succeed
            boot_result.unwrap_or_else(|e| panic!("runtime test `{name}` bootstrap failed: {e}"));

            // STATED GAP — the drain result is deliberately discarded, and this
            // is the one assertion in this file that is still weaker than it
            // looks. Asserting it fails today:
            //
            //     runtime test `message_delivery.sigil` drain failed:
            //     handler `Start` expected 4 payload byte(s), found 0
            //
            // That fixture is the tree's only source-level `ask` end-to-end
            // case, and it has been failing silently since it was written —
            // the discard is why nobody saw it. The fix is a runtime/bootstrap
            // payload-framing change, not a harness change, so it is out of
            // scope here rather than papered over. Tighten this line to
            // `.unwrap_or_else(...)` in the same commit that fixes the framing.
            let _ = host.drain_messages(100);
        }
    }
}

#[test]
fn attack_corpus_tests() {
    let files = read_test_files("attack");
    assert_corpus_floor("attack", files.len(), ATTACK_CORPUS_FLOOR);

    for (name, source) in &files {
        let expectation = extract_expectation(source).unwrap_or_else(|| {
            panic!("attack test `{name}` has no `// expect-error:` or `// expect-runtime:` header")
        });

        // First try compilation — some attacks are caught at compile time.
        let compilation = match compile_module(source) {
            Err(errors) => {
                match &expectation {
                    Expect::Codes(codes) => {
                        assert_expected_codes("attack", name, codes, &errors);
                        assert_mutant_compiles_clean("attack", name, source);
                    }
                    Expect::Runtime(r) => panic!(
                        "attack test `{name}` declares `// expect-runtime: {r}`, but it is \
                         rejected at COMPILE time with {}. The attack is blocked — earlier than \
                         the fixture claims — so re-annotate it `// expect-error: {}`. Note that \
                         doing so means this fixture no longer exercises the runtime path it was \
                         written for.",
                        format_codes(&emitted_codes(&errors)),
                        format_codes(&emitted_codes(&errors)),
                    ),
                }
                continue; // Rejected at compile time — attack blocked
            }
            Ok(c) => c,
        };

        let Expect::Runtime(expect) = &expectation else {
            panic!(
                "attack test `{name}` declares `// expect-error: {}`, but it COMPILED CLEANLY. \
                 Either the checker that used to reject it has regressed, or the fixture needs a \
                 `// expect-runtime:` header.",
                match &expectation {
                    Expect::Codes(c) => format_codes(c),
                    Expect::Runtime(r) => r.clone(),
                }
            )
        };

        // If it compiled, try running — runtime should catch the attack
        let mut host = RuntimeHost::new(compilation.runtime_module.fuel_budget);
        let boot_result = host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner);

        if expect.to_lowercase() == "fuelexhausted" {
            match boot_result {
                Err(e) if format!("{e}").contains("fuel") => continue,
                Ok(_) => {
                    let e = host.drain_messages(100).err().unwrap_or_else(|| {
                        panic!(
                            "attack test `{name}` expected FuelExhausted but the drain \
                             completed cleanly"
                        )
                    });
                    assert!(
                        format!("{e}").contains("fuel"),
                        "attack test `{name}` expected FuelExhausted but got: {e}"
                    );
                }
                Err(e) => panic!(
                    "attack test `{name}` expected FuelExhausted but got unexpected error: {e}"
                ),
            }
        } else if expect.to_lowercase().contains("trap") {
            // Expect Wasm trap (OOB, unreachable, TrapIf, etc.)
            match boot_result {
                Err(_) => continue, // Trap during bootstrap — attack mitigated
                Ok(_) => {
                    let drain_result = host.drain_messages(100);
                    assert!(
                        drain_result.is_err(),
                        "attack test `{name}` expected Wasm trap but execution succeeded"
                    );
                }
            }
        } else if expect.to_lowercase() == "ok" {
            // Expect runtime to survive (e.g., supervisor restart absorbs the crash)
            boot_result.unwrap_or_else(|e| {
                panic!("attack test `{name}` expected ok but bootstrap failed: {e}")
            });
            let _ = host.drain_messages(100); // May have errors from child actors, but host survives
        } else {
            panic!(
                "attack test `{name}` declares `// expect-runtime: {expect}`, which is not a \
                 recognised outcome (expected one of: FuelExhausted, Trap, ok)"
            );
        }
    }
}

/// Delete the line carrying `// MUTATION_SITE` (exactly one allowed).
/// Returns `None` when no line carries the marker. Mirrors the z3_corpus
/// mutation contract byte-for-byte in semantics: the marker rides the
/// offending line, so deleting that ONE line must legalize the program.
fn mutate_source(source: &str) -> Option<String> {
    let mut found = false;
    let mut out = Vec::with_capacity(source.lines().count());
    for line in source.lines() {
        if line.contains("// MUTATION_SITE") {
            assert!(
                !found,
                "fixture has multiple `// MUTATION_SITE` lines — exactly one \
                 line may carry the marker, or the deletion twin is ambiguous"
            );
            found = true;
            continue;
        }
        out.push(line);
    }
    if found { Some(out.join("\n")) } else { None }
}

/// The mutation gate (docs/STYLE.md section 4.2, mirroring z3_corpus): an
/// expect-error fixture proves it rejects for the DECLARED attack — not for
/// incidental breakage — by compiling CLEAN once its marked attack line is
/// deleted. The mutant doubles as the accept twin (section 4.6): the
/// minimally-different legal program, one line away from the reject, so the
/// corpus exercises both verdict classes on every run. Before this gate the
/// corpus had no such proof, and two fixtures were in fact rejecting for
/// reasons other than the ones they named.
fn assert_mutant_compiles_clean(kind: &str, name: &str, source: &str) {
    let mutated = mutate_source(source).unwrap_or_else(|| {
        panic!(
            "{kind} test `{name}` is expect-error but has no `// MUTATION_SITE` line; \
             mark the single attack line whose deletion legalizes the program"
        )
    });
    if let Err(e) = compile_module(&mutated) {
        panic!(
            "{kind} test `{name}`: deleting the MUTATION_SITE line must yield a CLEAN \
             compile (the accept twin), but the mutant still rejects with [{}]. The \
             fixture is rejecting for something other than its marked attack line — \
             restructure it so the marked line is the only illegal construct.",
            format_codes(&emitted_codes(&e)),
        );
    }
}

/// Anti-stub for the mutation machinery: prove the deleter deletes, refuses
/// ambiguity, and reports absence.
#[test]
fn mutation_site_deleter_deletes_exactly_one_marked_line() {
    assert_eq!(mutate_source("a\nb\n"), None, "no marker must report None");
    let mutated = mutate_source("keep\nbad line // MUTATION_SITE\nkeep2\n")
        .expect("a marked source must mutate");
    assert_eq!(
        mutated, "keep\nkeep2",
        "the marked line must be deleted whole"
    );
    let ambiguous =
        std::panic::catch_unwind(|| mutate_source("x // MUTATION_SITE\ny // MUTATION_SITE\n"));
    assert!(
        ambiguous.is_err(),
        "two markers must be refused, not silently resolved"
    );
}

/// The reject+attack corpora's code-coverage pin: the union of every
/// `expect-error` header must equal the committed manifest
/// `tests/expected-reject-codes.txt` exactly. Deleting a fixture that was
/// the last witness for a code shrinks the union and fails here; a new code
/// entering the corpus is a visible manifest diff. The manifest lives at the
/// repo root rather than as constants in this file because the diagnostic
/// census counts code-shaped tokens in every crates/**/tests file — comments
/// and strings included — and seventeen literals here would move its pins.
#[test]
fn reject_and_attack_corpora_cover_the_pinned_code_set() {
    let manifest_path = workspace_tests_dir().join("expected-reject-codes.txt");
    let manifest_text = std::fs::read_to_string(&manifest_path)
        .expect("tests/expected-reject-codes.txt exists — the corpus code-coverage pin");
    let pinned: BTreeSet<String> = manifest_text
        .lines()
        .map(|l| l.strip_suffix('\r').unwrap_or(l).trim())
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(str::to_string)
        .collect();

    let mut covered = BTreeSet::new();
    for (_, source) in read_test_files("reject")
        .iter()
        .chain(read_test_files("attack").iter())
    {
        if let Some(Expect::Codes(codes)) = extract_expectation(source) {
            covered.extend(codes);
        }
    }

    let lost: Vec<_> = pinned.difference(&covered).cloned().collect();
    let unpinned: Vec<_> = covered.difference(&pinned).cloned().collect();
    assert!(
        lost.is_empty() && unpinned.is_empty(),
        "corpus code coverage drifted from tests/expected-reject-codes.txt.\n  \
         pinned but no longer covered: [{}]\n  covered but not pinned: [{}]\n\
         Update the manifest in the same commit, with the row diff as review content.",
        lost.join(", "),
        unpinned.join(", "),
    );
}

/// SC-P4 anti-stub for the fixture comparator: prove that a WRONG expectation
/// is actually rejected.
///
/// This is the test the corpus needed and did not have. The historical
/// comparator matched the expect-comment against `format!("{errors:?}")`; that
/// blob embeds the `SourceMap`, hence the fixture source, hence the comment
/// itself — so the assertion passed for any compile failure whatsoever. The two
/// halves below pin both directions: the code-set comparison rejects a wrong
/// expectation, and the old text-blob predicate would have accepted it.
#[test]
fn expect_comment_cannot_satisfy_itself() {
    // T999 is not a real code, so no compilation can legitimately emit it.
    let source = "// expect-error: T999\nmodule m;\npub fn f() -> i64 { return nope(); }\n";

    let Some(Expect::Codes(expected)) = extract_expectation(source) else {
        panic!("header must parse as a code set");
    };
    assert_eq!(
        expected,
        BTreeSet::from(["T999".to_string()]),
        "the header parser must read the code out of the comment"
    );

    let errors = compile_module(source).expect_err("probe source must fail to compile");
    let actual = emitted_codes(&errors);

    // (1) The live comparator must NOT be satisfied by the comment.
    assert_ne!(
        actual, expected,
        "the code-set comparison accepted a fixture whose header names a code the compiler \
         never emitted — the comparator has lost its teeth"
    );
    assert!(
        !actual.is_empty(),
        "probe source should have produced at least one diagnostic"
    );

    // (2) The regression this guards against: the old predicate DOES pass here,
    // because the fixture's own text — including `T999` — is inside the Debug
    // blob. If this assertion ever fails, `CompileError`'s Debug has stopped
    // embedding source text; that is an improvement, and this half can be
    // retired, but the half above must stay.
    assert!(
        format!("{errors:?}").contains("T999"),
        "expected the Debug blob to still embed the fixture source (the reason text matching \
         was unsound); if it no longer does, retire this half of the anti-stub"
    );
}

/// The header parser must reject a leftover prose annotation loudly rather than
/// treating it as a one-element code set.
#[test]
fn prose_expectations_are_rejected_by_the_parser() {
    assert!(is_code_shaped("O001"));
    assert!(is_code_shaped("T278"));
    assert!(is_code_shaped("FE410"));
    assert!(!is_code_shaped("non-exhaustive match"));
    assert!(!is_code_shaped("T27"));
    assert!(!is_code_shaped("t278"));

    let err = std::panic::catch_unwind(|| {
        extract_expectation("// expect-error: cannot borrow primitive type\nmodule m;\n")
    });
    assert!(
        err.is_err(),
        "a prose `expect-error:` header must panic with a format error, not parse silently"
    );
}

/// Step 14 acceptance test: the multi-party 3-of-3 approval fixture from
/// the z3_corpus must not only compile, it must EXECUTE end-to-end. The
/// runtime accepts `spawn::<Action>(alice, bob, carol)` with 3 caps
/// mapped to a 3-param init: the last arg becomes `fuel_cap`, earlier
/// args are user caps. If this test regresses, the multi-party encoding
/// claim from step 14's commit is overstated and needs design rework.
#[test]
fn z3_corpus_multi_party_approval_runs_end_to_end() {
    let path = Path::new(WORKSPACE_ROOT)
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("crates/sigil-compiler/tests/z3_corpus/10_multi_party_approval.sigil");
    let source = fs::read_to_string(&path).expect("fixture file exists");
    let compilation = compile_module(&source).expect("fixture compiles cleanly");
    let mut host = RuntimeHost::new(compilation.runtime_module.fuel_budget);
    host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
        .expect("fixture bootstraps cleanly — spawn signature matches runtime convention");
    host.drain_messages(100)
        .expect("fixture executes cleanly — Main spawns Action with all three approvals");
}
