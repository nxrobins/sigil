use std::collections::HashSet;
use std::path::{Path, PathBuf};

pub fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("sigil-runtime must be under crates/")
        .to_path_buf()
}

pub fn all_test_fn_names() -> HashSet<String> {
    all_fn_names(crate::test_source::test_fn_names_in)
}

/// Every `#[ignore]`d test in the workspace — the subset that exists by name but never runs.
///
/// `allow(dead_code)`: shared `#[path]` support module, used only by `claims_ledger`; CI builds
/// every test binary with `-D warnings`.
#[allow(dead_code)]
pub fn all_ignored_test_fn_names() -> HashSet<String> {
    all_fn_names(crate::test_source::ignored_test_fn_names_in)
}

fn all_fn_names(extract: fn(&str) -> HashSet<String>) -> HashSet<String> {
    fn walk(dir: &Path, names: &mut HashSet<String>, extract: fn(&str) -> HashSet<String>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                if path.file_name().is_some_and(|name| name == "target") {
                    continue;
                }
                walk(&path, names, extract);
            } else if path.extension().is_some_and(|ext| ext == "rs")
                && let Ok(src) = std::fs::read_to_string(path)
            {
                names.extend(extract(&src));
            }
        }
    }

    let mut names = HashSet::new();
    walk(&repo_root().join("crates"), &mut names, extract);
    names
}
