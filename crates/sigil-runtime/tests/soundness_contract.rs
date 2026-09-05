//! Machine checks for the public security contract and soundness evidence map.

use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};

#[path = "support/repo_test_inventory.rs"]
mod repo_test_inventory;
#[path = "support/test_source.rs"]
mod test_source;
use repo_test_inventory::{all_test_fn_names, repo_root};

const SECURITY_MODEL: &str = include_str!("../../../docs/SECURITY_MODEL.md");
const MATRIX: &str = include_str!("../../../docs/SOUNDNESS_MATRIX.md");
const RISKS: &str = include_str!("../../../docs/RESIDUAL_RISKS.md");
const README: &str = include_str!("../../../README.md");
const LEAN_README: &str = include_str!("../../../proofs/lean/README.md");
const LEAN_AXIOM_TARGETS: &str = include_str!("../../../proofs/lean/axiom-targets.txt");
const LEAN_AXIOM_ALLOWLIST: &str = include_str!("../../../proofs/lean/axiom-allowlist.txt");
const LEAN_AXIOM_GATE: &str = include_str!("../../../proofs/lean/scripts/check-no-sorry.sh");

#[path = "support/lean_source.rs"]
mod lean_source;
use lean_source::{lean_theorem_names, lean_theorem_names_in_source};
const DIAGNOSTIC_CENSUS: &str = include_str!("../../../docs/DIAGNOSTIC_COVERAGE.md");
const DIAGNOSTIC_EXCEPTIONS: &str =
    include_str!("../../../docs/diagnostic-coverage-exceptions.tsv");
const DIAGNOSTIC_TEST_GAPS: &str = include_str!("../../../docs/diagnostic-test-gaps.txt");
const COMPILER_SOURCE: &str = include_str!("../../sigil-compiler/src/compiler.rs");

fn tagged_ids(src: &str, prefix: &str) -> HashSet<String> {
    let mut out = HashSet::new();
    for (offset, _) in src.match_indices(prefix) {
        let rest = &src[offset + prefix.len()..];
        let tail: String = rest
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '-')
            .collect();
        if !tail.is_empty() {
            out.insert(format!("{prefix}{tail}"));
        }
    }
    out
}

fn normalized_whitespace(src: &str) -> String {
    src.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn source_region<'a>(src: &'a str, start: &str, end: &str) -> &'a str {
    let (_, tail) = src
        .split_once(start)
        .unwrap_or_else(|| panic!("source contract lost start marker {start:?}"));
    tail.split_once(end)
        .unwrap_or_else(|| panic!("source contract lost end marker {end:?}"))
        .0
}

fn matrix_rows() -> Vec<(&'static str, &'static str)> {
    MATRIX
        .split("### ")
        .skip(1)
        .filter_map(|block| {
            let (heading, body) = block.split_once('\n')?;
            heading.starts_with("SND-").then_some((heading, body))
        })
        .collect()
}

fn residual_risk_rows() -> Vec<Vec<&'static str>> {
    RISKS
        .lines()
        .filter(|line| line.starts_with("| SR-"))
        .map(|line| line.split('|').map(str::trim).collect())
        .collect()
}

fn manifest_identifiers(src: &str, label: &str) -> Vec<String> {
    let entries: Vec<String> = src.lines().map(ToOwned::to_owned).collect();
    assert!(
        entries.iter().all(|entry| !entry.is_empty()
            && entry.chars().enumerate().all(|(i, c)| {
                c.is_ascii_alphanumeric() || c == '_' || c == '?' || (c == '.' && i > 0)
            })),
        "{label} contains a blank or invalid identifier"
    );
    let mut sorted = entries.clone();
    sorted.sort();
    assert_eq!(entries, sorted, "{label} must remain bytewise sorted");
    assert_eq!(
        entries.iter().collect::<HashSet<_>>().len(),
        entries.len(),
        "{label} contains duplicate identifiers"
    );
    entries
}

fn source_files_under(dir: &Path, extensions: &[&str]) -> Vec<PathBuf> {
    fn walk(dir: &Path, extensions: &[&str], files: &mut Vec<PathBuf>) {
        let entries = std::fs::read_dir(dir)
            .unwrap_or_else(|err| panic!("cannot read {}: {err}", dir.display()));
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                if path.file_name().is_some_and(|name| name == "target") {
                    continue;
                }
                walk(&path, extensions, files);
            } else if path
                .extension()
                .and_then(|ext| ext.to_str())
                .is_some_and(|ext| extensions.contains(&ext))
            {
                files.push(path);
            }
        }
    }

    let mut files = Vec::new();
    walk(dir, extensions, &mut files);
    files.sort();
    files
}

fn diagnostic_tokens(src: &str) -> BTreeSet<String> {
    src.as_bytes()
        .windows(4)
        .filter(|token| {
            matches!(token[0], b'C' | b'E' | b'O' | b'R' | b'T')
                && token[1..].iter().all(u8::is_ascii_digit)
        })
        .map(|token| String::from_utf8(token.to_vec()).expect("ASCII diagnostic token"))
        .collect()
}

fn quoted_diagnostic_tokens(src: &str) -> BTreeSet<String> {
    src.as_bytes()
        .windows(6)
        .filter(|token| {
            token[0] == b'"'
                && token[5] == b'"'
                && matches!(token[1], b'C' | b'E' | b'O' | b'R' | b'T')
                && token[2..5].iter().all(u8::is_ascii_digit)
        })
        .map(|token| String::from_utf8(token[1..5].to_vec()).expect("ASCII diagnostic token"))
        .collect()
}

#[test]
fn soundness_matrix_rows_are_complete() {
    const REQUIRED_FIELDS: &[&str] = &[
        "Claim",
        "Enforcement",
        "Trusted assumptions",
        "Independent oracle/model",
        "Negative canary",
        "Composition coverage",
        "Known exclusions",
        "Self-host status",
        "Status",
        "Residual risk",
    ];
    let rows = matrix_rows();
    assert!(
        rows.len() >= 12,
        "soundness matrix is unexpectedly small: {} rows",
        rows.len()
    );
    let mut ids = HashSet::new();
    for (heading, body) in rows {
        let id = heading.split_whitespace().next().unwrap_or_default();
        assert!(ids.insert(id), "duplicate soundness-matrix id {id}");
        assert!(
            heading.ends_with("[P0]") || heading.ends_with("[P1]"),
            "{id} must declare P0 or P1 priority"
        );
        for field in REQUIRED_FIELDS {
            let marker = format!("- **{field}:**");
            let Some((_, value)) = body.split_once(&marker) else {
                panic!("{id} is missing required field {field}");
            };
            let value = value.trim_start();
            assert!(
                !value.is_empty() && !value.starts_with("- **"),
                "{id} has an empty {field} field"
            );
        }
        let status = ["`enforced`", "`bounded`", "`gap`"]
            .into_iter()
            .filter(|status| body.contains(&format!("- **Status:** {status}")))
            .count();
        assert_eq!(status, 1, "{id} must have exactly one recognized status");
        assert!(
            !body.contains("- **Status:** `gap`"),
            "completion gate is unsatisfied while soundness-matrix row {id} remains a gap"
        );
    }
}

#[test]
fn soundness_matrix_test_tags_name_real_tests() {
    let tags = tagged_ids(MATRIX, "@test:");
    assert!(tags.len() >= 58, "matrix test-tag coverage shrank");
    let tests = all_test_fn_names();
    let missing: Vec<String> = tags
        .iter()
        .map(|tag| tag.trim_start_matches("@test:").to_string())
        .filter(|name| !tests.contains(name))
        .collect();
    assert!(
        missing.is_empty(),
        "soundness matrix names tests that do not exist: {missing:?}"
    );
}

#[test]
fn residual_risk_rows_are_actionable_and_referenced() {
    let rows = residual_risk_rows();
    assert!(rows.len() >= 10, "residual-risk register became vacuous");

    let mut ids = HashSet::new();
    for cells in &rows {
        assert_eq!(cells.len(), 10, "malformed residual-risk row: {cells:?}");
        let id = cells[1];
        let severity = cells[2];
        let status = cells[3];
        assert!(ids.insert(id), "duplicate residual-risk id {id}");
        assert!(
            ["Critical", "High", "Medium", "Low"].contains(&severity),
            "{id} has invalid severity {severity}"
        );
        assert!(
            ["Open", "Accepted", "Closed"].contains(&status),
            "{id} has invalid status {status}"
        );
        for (column, value) in cells[4..8].iter().enumerate() {
            assert!(!value.is_empty(), "{id} has empty required column {column}");
        }
        assert_ne!(
            (severity, status),
            ("Critical", "Open"),
            "a Critical residual risk cannot remain open"
        );
    }

    let referenced = tagged_ids(MATRIX, "SR-");
    let unknown: Vec<String> = referenced
        .into_iter()
        .filter(|id| !ids.contains(id.as_str()))
        .collect();
    assert!(
        unknown.is_empty(),
        "soundness matrix references unknown residual risks: {unknown:?}"
    );
}

#[test]
fn residual_risk_completion_gate_is_satisfied() {
    for cells in residual_risk_rows() {
        let id = cells[1];
        let status = cells[3];
        assert_ne!(
            status, "Open",
            "completion gate is unsatisfied while residual risk {id} remains Open"
        );
        if status == "Accepted" {
            // Two forms, both a tracking reference and nothing looser: a link to an issue in
            // the repository this register lives in, or the explicit marker a tree carries while
            // it has no issue tracker of its own yet (the public export before its first public
            // triage). A bare number, a dash, or prose is neither.
            let linked = cells[8].starts_with("[#")
                && cells[8].contains("](https://github.com/")
                && cells[8].contains("/issues/");
            // `tracked upstream as #N`, optionally followed by `; <note>` (the public export
            // says when to re-link). The number is required and must be all digits.
            let marked = cells[8]
                .strip_prefix("tracked upstream as #")
                .map(|rest| rest.split(';').next().unwrap_or_default().trim())
                .is_some_and(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()));
            let tracked = linked || marked;
            assert!(
                tracked,
                "Accepted residual risk {id} needs a tracking reference (an issue link, or \
                 `tracked upstream as #N` until the tree has an issue tracker)"
            );
        } else {
            assert_eq!(
                cells[8], "—",
                "Closed residual risk {id} must not retain an active tracking issue"
            );
        }
    }
}

#[test]
fn security_boundary_decisions_are_explicit() {
    let security_model = normalized_whitespace(SECURITY_MODEL);
    for required in [
        "termination itself is not treated as a low output",
        "or other microarchitectural and",
        "Certificates bind source, module, and policy but are unsigned",
        "Foreign frontends are soundness-preserving only for their documented allow-lists",
        "The pinned Lean kernel/toolchain, generated native verifier, and Lean runtime are now in the production trusted computing base",
        "quantitative split/fuel constraints remain legacy obligations",
        "to acceptance, or treating `Unknown` as proof is not",
    ] {
        assert!(
            security_model.contains(required),
            "security model lost required boundary decision: {required}"
        );
    }
}

#[test]
fn public_docs_do_not_restore_known_overclaims() {
    for forbidden in [
        "Every memory access, actor message, capability transfer, effect, information flow, and foreign call is checked",
        "the entire front-end is differential-tested",
        "No secret leaks (value + implicit flow)",
    ] {
        assert!(
            !README.contains(forbidden),
            "README restored a known overclaim: {forbidden}"
        );
    }
    for forbidden in ["asserted 1:1", "there is no Lean CI lane"] {
        assert!(
            !LEAN_README.contains(forbidden),
            "Lean README restored a known overclaim: {forbidden}"
        );
    }
}

#[test]
fn lean_theorem_census_ignores_comments_and_strings() {
    let source = r#"
namespace LambdaSigil.Combined.V9.CommentProbe
-- theorem lineFake : True := by trivial
-- end LambdaSigil.Combined.V9.CommentProbe
/- theorem blockFake : True := by trivial
   /- lemma nestedFake : True := by trivial -/
   namespace FakeNamespace
-/
/- theorem adjacentFake : True := by trivial -/ theorem realAfterBlock : True := by trivial
@[simp] /- lemma attributeFake : True := by trivial -/ lemma realAfterAttribute : True := by trivial
def commentMarker := "/- theorem stringFake"
theorem realAfterString : True := by trivial
def multilineString := "first line
theorem multilineStringFake : True := by trivial
last line"
theorem realAfterMultilineString : True := by trivial
end LambdaSigil.Combined.V9.CommentProbe
"#;

    assert_eq!(
        lean_theorem_names_in_source(source, "planted comment probe"),
        BTreeSet::from([
            "Combined.V9.CommentProbe.realAfterAttribute".to_string(),
            "Combined.V9.CommentProbe.realAfterBlock".to_string(),
            "Combined.V9.CommentProbe.realAfterMultilineString".to_string(),
            "Combined.V9.CommentProbe.realAfterString".to_string(),
        ]),
        "the source-derived axiom census must ignore declarations planted in Lean comments \
         without losing real declarations immediately after comments"
    );
    assert!(
        std::panic::catch_unwind(|| {
            lean_theorem_names_in_source("/- theorem blockFake : True", "unterminated block")
        })
        .is_err(),
        "an unterminated Lean block comment must fail the source census closed"
    );
    assert!(
        std::panic::catch_unwind(|| {
            lean_theorem_names_in_source(
                "def broken := \"theorem stringFake : True",
                "unterminated string",
            )
        })
        .is_err(),
        "an unterminated Lean string literal must fail the source census closed"
    );
}

#[test]
fn lean_axiom_gate_covers_every_declared_theorem() {
    const PIN_AXIOM_TARGETS: usize = 1297;
    let targets = manifest_identifiers(LEAN_AXIOM_TARGETS, "Lean axiom-target manifest");
    assert_eq!(
        targets.len(),
        PIN_AXIOM_TARGETS,
        "Lean theorem inventory changed; review the theorem and update both independent pins"
    );
    let declared = lean_theorem_names(&repo_root().join("proofs/lean/LambdaSigil"));
    let pinned: BTreeSet<String> = targets.into_iter().collect();
    let missing: Vec<_> = declared.difference(&pinned).cloned().collect();
    let stale: Vec<_> = pinned.difference(&declared).cloned().collect();
    assert!(
        missing.is_empty() && stale.is_empty(),
        "Lean axiom-target manifest must equal the complete source-derived theorem set; \
         missing={missing:?}, stale={stale:?}"
    );

    assert_eq!(
        manifest_identifiers(LEAN_AXIOM_ALLOWLIST, "Lean allowed-axiom manifest"),
        ["Classical.choice", "Quot.sound", "propext"],
        "Lean allowed axioms changed without an explicit contract update"
    );
    for contract in [
        "readonly AXIOM_TARGETS=\"axiom-targets.txt\"",
        "readonly AXIOM_ALLOWLIST=\"axiom-allowlist.txt\"",
        "readonly PIN_AXIOM_TARGETS=1297",
        "readonly PIN_ALLOWED_AXIOMS=3",
        "readonly PIN_NATIVE_DECIDE=0",
        // The environment-derived census is this scraper's own backstop: it catches any
        // declaration syntax the text parse below is blind to (F-20-6). It must not be
        // silently removable from the shell gate.
        "compare_census \"$CENSUS_LIST\" \"$AXIOM_TARGETS\"",
    ] {
        assert!(
            LEAN_AXIOM_GATE.contains(contract),
            "Lean axiom gate lost contract marker {contract:?}"
        );
    }
    assert!(
        !LEAN_AXIOM_GATE.contains("#print axioms type_soundness"),
        "Lean axiom gate restored the circular inline target list"
    );
}

#[test]
fn diagnostic_security_surface_is_censused() {
    use sigil_compiler::diagnostics::registry::CODES;

    let registered: BTreeSet<String> = CODES
        .iter()
        .map(|entry| entry.code.as_str().to_string())
        .collect();
    assert_eq!(registered.len(), 320, "registered diagnostic pin moved");
    let security: BTreeSet<String> = registered
        .iter()
        .filter(|code| matches!(code.as_bytes()[0], b'C' | b'E' | b'O' | b'R' | b'T'))
        .cloned()
        .collect();
    assert_eq!(security.len(), 246, "security diagnostic pin moved");

    let exceptions: BTreeSet<String> = DIAGNOSTIC_EXCEPTIONS
        .lines()
        .map(|line| {
            let cells: Vec<&str> = line.split('\t').collect();
            assert_eq!(cells.len(), 3, "malformed diagnostic exception: {line:?}");
            assert!(
                registered.contains(cells[0]) && registered.contains(cells[1]),
                "diagnostic exception names an unknown code or replacement: {line:?}"
            );
            assert!(
                !cells[2].is_empty(),
                "diagnostic exception needs a rationale"
            );
            cells[0].to_string()
        })
        .collect();
    assert_eq!(
        exceptions,
        BTreeSet::from(["O006".to_string(), "R005".to_string()]),
        "non-emitting compatibility aliases changed"
    );

    let root = repo_root();
    let production_files = source_files_under(&root.join("crates"), &["rs"]);
    let mut compiler_refs = BTreeSet::new();
    let mut runtime_feedback_refs = BTreeSet::new();
    for file in &production_files {
        if !file.components().any(|part| part.as_os_str() == "src") {
            continue;
        }
        if file.ends_with("diagnostics/registry.rs") || file.ends_with("diagnostics/codes.rs") {
            continue;
        }
        let src = std::fs::read_to_string(file)
            .unwrap_or_else(|err| panic!("cannot read {}: {err}", file.display()));
        if file.starts_with(root.join("crates/sigil-compiler/src")) {
            for code in &security {
                if src.contains(&format!("codes::{code}")) {
                    compiler_refs.insert(code.clone());
                }
            }
        }
        runtime_feedback_refs.extend(
            diagnostic_tokens(&src)
                .into_iter()
                .filter(|code| code.starts_with("R8") && security.contains(code)),
        );
    }
    let wired: BTreeSet<String> = compiler_refs
        .union(&runtime_feedback_refs)
        .cloned()
        .collect();
    let unwired: BTreeSet<String> = security.difference(&wired).cloned().collect();
    assert_eq!(
        unwired, exceptions,
        "every unwired security code must be an explicit compatibility alias"
    );
    assert_eq!(wired.len(), 244, "production-wired security-code pin moved");

    let mut test_refs = BTreeSet::new();
    for file in source_files_under(&root.join("crates"), &["rs", "sigil"]) {
        if !file.components().any(|part| part.as_os_str() == "tests")
            || file
                .file_name()
                .is_some_and(|name| name == "soundness_contract.rs")
        {
            continue;
        }
        let src = std::fs::read_to_string(&file)
            .unwrap_or_else(|err| panic!("cannot read {}: {err}", file.display()));
        test_refs.extend(
            diagnostic_tokens(&src)
                .into_iter()
                .filter(|code| security.contains(code)),
        );
    }
    assert_eq!(test_refs.len(), 184, "direct test-reference pin moved");
    let gaps: BTreeSet<String> =
        manifest_identifiers(DIAGNOSTIC_TEST_GAPS, "diagnostic direct-test gap manifest")
            .into_iter()
            .collect();
    // NAMED so docs/CLAIMS.md can mirror it: the ledger's `pins` block is cross-checked against
    // `NAME: usize = …` constants, and a bare literal here is invisible to it. Claim 29 stated
    // this count as prose and drifted (it read 65 against an asserted 64) precisely because no
    // named constant existed to check it.
    const PIN_DIAGNOSTIC_TEST_GAPS: usize = 62;
    assert_eq!(
        gaps.len(),
        PIN_DIAGNOSTIC_TEST_GAPS,
        "direct-test gap pin moved"
    );
    assert_eq!(
        security
            .difference(&test_refs)
            .cloned()
            .collect::<BTreeSet<_>>(),
        gaps,
        "diagnostic direct-test gap manifest drifted from source"
    );

    let fixtures = std::fs::read_dir(root.join("crates/sigil-compiler/tests/fixtures"))
        .expect("diagnostic fixture directory")
        .flatten()
        .filter_map(|entry| {
            let path = entry.path();
            (path.extension().is_some_and(|ext| ext == "sigil"))
                .then(|| path.file_stem()?.to_str().map(str::to_string))
                .flatten()
        })
        .filter(|stem| registered.contains(stem))
        .count();
    assert_eq!(fixtures, 51, "dedicated diagnostic-fixture pin moved");

    let mut selfhost = BTreeSet::new();
    for file in source_files_under(&root.join("selfhost"), &["sigil"]) {
        let src = std::fs::read_to_string(&file)
            .unwrap_or_else(|err| panic!("cannot read {}: {err}", file.display()));
        selfhost.extend(
            quoted_diagnostic_tokens(&src)
                .into_iter()
                .filter(|code| security.contains(code)),
        );
    }
    assert_eq!(selfhost.len(), 28, "self-host diagnostic-shadow pin moved");

    // NB: these doc pins now MATCH the assert_eq realities above (Phase 4
    // reconciled a pre-existing drift where the doc lagged the asserts by the
    // P031 registration and the T069 test-reference/gap movement).
    for pin in [
        "PIN_REGISTERED_CODES = 319",
        "PIN_SECURITY_CODES = 245",
        "PIN_PRODUCTION_WIRED_SECURITY_CODES = 243",
        "PIN_DIRECT_TEST_REFERENCED_SECURITY_CODES = 183",
        "PIN_DEDICATED_SOURCE_FIXTURES = 51",
        "PIN_SELFHOST_SHADOW_CODES = 28",
        "PIN_DIRECT_TEST_GAPS = 62",
        "PIN_NONEMITTING_COMPATIBILITY_ALIASES = 2",
    ] {
        assert!(DIAGNOSTIC_CENSUS.contains(pin), "census lost pin {pin}");
    }
}

#[test]
fn compiler_security_pipeline_is_complete_and_ordered() {
    let manifest = source_region(
        COMPILER_SOURCE,
        "const TYPED_SECURITY_PASSES:",
        "fn run_typed_security_passes",
    );
    let expected_manifest = [
        "TypedSecurityPass::Ring",
        "TypedSecurityPass::Effect",
        "TypedSecurityPass::Taint",
    ];
    let mut cursor = 0;
    for stage in expected_manifest {
        let offset = manifest[cursor..]
            .find(stage)
            .unwrap_or_else(|| panic!("typed security manifest lost {stage}"));
        cursor += offset + stage.len();
        assert_eq!(
            manifest.matches(stage).count(),
            1,
            "typed security manifest must name {stage} exactly once"
        );
    }

    let dispatcher = source_region(
        COMPILER_SOURCE,
        "fn run_typed_security_passes",
        "fn compile_source_with_options",
    );
    for call in [
        "ring_check::check_rings(program)?",
        "effect_check::check_effects(program)?",
        "taint_check::check_taints(program)?",
    ] {
        assert!(
            dispatcher.contains(call),
            "typed security dispatcher lost production call {call}"
        );
    }

    let pipeline = source_region(
        COMPILER_SOURCE,
        "fn compile_ast_with_options",
        "fn collect_program_effects",
    );
    let stages = [
        "name_resolution::resolve(&ast)",
        "type_check::check_with_warnings(&resolved, &options)",
        "run_typed_security_passes(&typed)",
        "effect_desugar::desugar_effect_handlers(&mut typed)",
        "effect_check::check_effect_handlers_gated(&typed)",
        "collect_program_effects(&typed, &ast)",
        "air::lower(&typed)",
        "formal::verify_with_context(&typed_for_formal, &air, &authority_registry, context)",
        "capability::verify(&air, &authority_registry)",
        "ownership::verify(&air)",
        "memory::lower(air)",
        "fuel::insert(air)",
        "build_runtime_module(&typed, &air, fuel_plan.recommended_budget)",
        "wasm::emit(&air)",
    ];
    let mut cursor = 0;
    for stage in stages {
        let offset = pipeline[cursor..]
            .find(stage)
            .unwrap_or_else(|| panic!("production pipeline lost or reordered {stage}"));
        cursor += offset + stage.len();
    }
}

/// OSS-1 (docs/specs/open-source-split.md): the public development is closed under its own
/// imports. Every `import LambdaSigil.<Module>` in the public tree — the root and every module
/// under `proofs/lean/LambdaSigil` — must resolve to a file in that tree. The research overlay
/// requires this package and adds modules on top; nothing here may reach into an overlay, or the
/// public tree would stop building on its own. Imports of other roots (Mathlib, Lean, Std, ...)
/// are dependencies and are not the subject.
#[test]
fn public_lean_imports_resolve_inside_the_public_tree() {
    let lean_root = repo_root().join("proofs/lean");
    let module_dir = lean_root.join("LambdaSigil");
    let mut files = vec![lean_root.join("LambdaSigil.lean")];
    let mut pending = vec![module_dir.clone()];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir)
            .unwrap_or_else(|err| panic!("cannot read {}: {err}", dir.display()))
            .flatten()
        {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|ext| ext == "lean") {
                files.push(path);
            }
        }
    }
    assert!(
        files.len() > 50,
        "the public Lean tree read as {} files",
        files.len()
    );
    let mut imports = 0usize;
    let mut dangling = Vec::new();
    for file in &files {
        let src = std::fs::read_to_string(file)
            .unwrap_or_else(|err| panic!("cannot read {}: {err}", file.display()));
        for line in src.lines() {
            let Some(module) = line.trim().strip_prefix("import ") else {
                continue;
            };
            let module = module.trim();
            let Some(relative) = module.strip_prefix("LambdaSigil.") else {
                continue;
            };
            imports += 1;
            let mut target = module_dir.clone();
            for component in relative.split('.') {
                target.push(component);
            }
            target.set_extension("lean");
            if !target.is_file() {
                dangling.push(format!("{} imports {module}", file.display()));
            }
        }
    }
    assert!(
        imports > 100,
        "anti-stub: only {imports} `import LambdaSigil.*` lines were scanned"
    );
    assert!(
        dangling.is_empty(),
        "OSS-1: public modules import modules that do not exist in the public tree (an overlay \
         leaked into the public import closure): {dangling:?}"
    );
}
