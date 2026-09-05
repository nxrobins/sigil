//! T215 ownership and reachability contracts for the production refinement path.

use std::fs;
use std::path::{Path, PathBuf};

fn crate_path(relative: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(relative)
}

fn strip_line_comment(line: &str) -> &str {
    line.split_once("//").map_or(line, |(code, _comment)| code)
}

fn count_in_rs_tree(directory: &Path, needle: &str) -> usize {
    let mut total = 0;
    let mut pending = vec![directory.to_path_buf()];
    while let Some(path) = pending.pop() {
        let entries = fs::read_dir(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        for entry in entries {
            let path = entry.expect("read directory entry").path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().and_then(|extension| extension.to_str()) == Some("rs") {
                let source = fs::read_to_string(&path)
                    .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
                total += source
                    .lines()
                    .map(strip_line_comment)
                    .map(|line| line.matches(needle).count())
                    .sum::<usize>();
            }
        }
    }
    total
}

#[test]
fn t215_remains_v2_owned() {
    // T215 must remain owned by the sole discharge path and reachable through
    // the pinned mismatch fixtures below.
    let emission_sites = count_in_rs_tree(&crate_path("src/type_check_v2"), "codes::T215");
    assert!(
        emission_sites > 0,
        "v2 lost every T215 emission site; this would reopen a covered rejection gap"
    );
}

#[test]
fn t215_reachability_remains_pinned() {
    for fixture in [
        "tests/z3_corpus/31_refinement_mismatch.sigil",
        "tests/z3_corpus/36_refinement_semantic_non_subset.sigil",
    ] {
        let source = fs::read_to_string(crate_path(fixture))
            .unwrap_or_else(|error| panic!("failed to read {fixture}: {error}"));
        assert!(
            source.contains("expect-error: T215"),
            "{fixture} no longer proves T215 is reachable"
        );
    }
}
