//! Current-state contracts for completed quarantine migrations.

use std::fs;
use std::path::{Path, PathBuf};

fn crate_path(relative: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(relative)
}

fn assert_absent(relative: &str, stale_phrases: &[&str]) {
    let source = fs::read_to_string(crate_path(relative))
        .unwrap_or_else(|error| panic!("failed to read {relative}: {error}"));
    for phrase in stale_phrases {
        assert!(
            !source.contains(phrase),
            "{relative} still describes completed work as `{phrase}`"
        );
    }
}

fn read_module_family(root_file: &str, modules_dir: &str) -> String {
    let mut paths = vec![crate_path(root_file)];
    paths.extend(
        fs::read_dir(crate_path(modules_dir))
            .unwrap_or_else(|error| panic!("failed to read {modules_dir}: {error}"))
            .map(|entry| entry.expect("read module entry").path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "rs")),
    );
    paths.sort();
    paths
        .iter()
        .map(|path| fs::read_to_string(path).expect("read module source"))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn completed_migration_journals_are_retired() {
    for relative in [
        "../../docs/air-capability-quarantine.md",
        "../../docs/refinement-quarantine-t215-gap.md",
        "../../docs/diagnostics-axes-loop.md",
        "../../docs/maintenance-audit-2026-05-26.md",
        "../../docs/sigil-roadmap-alignment.md",
    ] {
        assert!(
            !crate_path(relative).exists(),
            "completed migration journal remains tracked: {relative}"
        );
    }

    let retired_specs = [
        "agg-0-phase0.md",
        "agg2b-2-design.md",
        "agg2b-4-sweep-findings.md",
        "agg2b-phase0.md",
        "ms-s2.md",
        "ms-s3-fences.md",
        "mutable-state-epic.md",
        "persistent-collection-heap.md",
        "preserve-the-milestone.md",
        "rtc-alloc-size-fence.md",
        "rtc-silent-noop-class.md",
        "sh-fuel.md",
        "sh-mem-report.md",
        "sh-nr-0.md",
        "sh-nr-1.md",
        "sh-nr-2.md",
        "sh-parse-mm.md",
        "sh-ring.md",
        "sh-effect.md",
        "sh-taint.md",
        "stage3-0.md",
        "stage3-a.md",
        "stage3-b.md",
        "stage3-phase0.md",
    ];
    let retired_prefixes = [
        "sh-boot-",
        "sh-cap-",
        "sh-mono-",
        "sh-own-",
        "sh-self-",
        "sh-surface-",
        "sh-w-",
    ];
    for entry in fs::read_dir(crate_path("../../docs/specs")).expect("read docs/specs") {
        let name = entry
            .expect("read spec entry")
            .file_name()
            .to_string_lossy()
            .into_owned();
        assert!(
            !retired_specs.contains(&name.as_str())
                && !retired_prefixes
                    .iter()
                    .any(|prefix| name.starts_with(prefix)),
            "completed slice journal remains tracked: docs/specs/{name}"
        );
    }
}

#[test]
fn refinement_modules_describe_live_collectors() {
    assert_absent(
        "src/type_check_v2/mod.rs",
        &[
            "collectors are stubs",
            "Future PRs implement the collectors",
            "planned PR 3 signature change",
            "PR 3 will change",
            "type-check shadow",
            "Legacy and v2 coexist",
            "When PR 1.5",
            "PR 1.6 wires",
            "ships in PR 1.7",
            "PR 3 of the Quarantine",
            "legacy refinement-check call sites",
            "Future PR adds",
        ],
    );
    assert_absent(
        "src/type_check_v2/refinement.rs",
        &["legacy walker", "Future PR", "left UNCOVERED"],
    );
}

#[test]
fn air_capability_modules_describe_the_production_prover() {
    assert_absent(
        "src/air_capability_v2/obligations.rs",
        &["collector emits nothing yet", "PR 2 scaffolding"],
    );
    assert_absent(
        "src/air_capability_v2/mod.rs",
        &[
            "Inert in PR 2",
            "A future PR may make",
            "legacy prover",
            "shadow pipeline",
            "docs/air-capability-quarantine.md",
        ],
    );
}

#[test]
fn large_dispatchers_are_partitioned_into_named_phases() {
    let expressions = read_module_family(
        "src/type_check/expressions.rs",
        "src/type_check/expressions",
    );
    for helper in [
        "infer_unresolved_call_expr",
        "finish_resolved_call_expr",
        "try_reroute_method_call_expr",
        "try_infer_builtin_method_expr",
        "infer_user_method_expr",
    ] {
        assert!(
            expressions.contains(&format!("fn {helper}")),
            "call dispatch is missing the `{helper}` phase"
        );
    }

    let solidity = fs::read_to_string(crate_path("../sigil-frontends/src/solidity/check.rs"))
        .expect("read Solidity checker");
    for helper in [
        "check_assign_stmt",
        "check_index_assign_stmt",
        "check_map_transfer_stmt",
        "check_if_stmt",
    ] {
        assert!(
            solidity.contains(&format!("fn {helper}")),
            "Solidity statement checking is missing `{helper}`"
        );
    }
}
