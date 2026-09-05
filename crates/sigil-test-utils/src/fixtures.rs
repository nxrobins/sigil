//! Fixture-corpus loaders.
//!
//! Bridges the test-fixture directories in `crates/sigil-compiler/tests/`
//! to test code. The well-known corpora:
//!
//! * `tests/cve_corpus/` — CVE reproductions (e.g.,
//!   `01_cve_2021_44228_log4shell.sigil`, with companion `.md` files
//!   that document the original CVE).
//! * `tests/z3_corpus/` — refinement-checker fixtures
//!   (`01_attenuation_at_call.sigil` and friends).
//! * `tests/fixtures/` — diagnostic-code reproductions named after
//!   the code they exercise (`E003.sigil`, `N007.sigil`, ...).
//!
//! ## Usage pattern
//!
//! ```rust,ignore
//! use std::path::Path;
//! use sigil_test_utils::fixtures;
//!
//! let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/cve_corpus");
//! for fixture in fixtures::each_sigil_file(&dir) {
//!     let src = std::fs::read_to_string(&fixture.path).unwrap();
//!     // ... assert on `src` ...
//! }
//! ```
//!
//! Companion `.md` documentation files are ignored by
//! [`each_sigil_file`] (only `.sigil` extensions match), so the test
//! sees a clean list of source-only fixtures.

use std::fs;
use std::path::{Path, PathBuf};

/// One fixture file discovered by [`each_sigil_file`].
///
/// `name` is the stem-form (no `.sigil` extension), suitable for use
/// as a snapshot name. `path` is the absolute path on disk for
/// reading the source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fixture {
    /// File stem (e.g., `"01_cve_2021_44228_log4shell"`). Stable
    /// across machines; suitable as an `insta` snapshot name.
    pub name: String,
    /// Absolute path to the `.sigil` source file. Read with
    /// `std::fs::read_to_string(&fixture.path)`.
    pub path: PathBuf,
}

/// Walk `dir` and return every `.sigil` file as a [`Fixture`], sorted
/// by name. Sorting is deterministic so snapshot tests don't depend on
/// the filesystem's directory-iteration order (which varies across
/// OSes — Windows alphabetical, Linux usually-but-not-always inode).
///
/// Non-`.sigil` files (e.g., `.md` companions) are silently skipped.
///
/// Panics if `dir` does not exist or is not a directory — tests should
/// fail loud if a corpus path goes stale.
pub fn each_sigil_file(dir: &Path) -> Vec<Fixture> {
    let entries = fs::read_dir(dir).unwrap_or_else(|e| {
        panic!(
            "fixtures::each_sigil_file: cannot read directory {}: {e}",
            dir.display()
        )
    });
    let mut fixtures: Vec<Fixture> = entries
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) != Some("sigil") {
                return None;
            }
            let name = path.file_stem()?.to_string_lossy().into_owned();
            Some(Fixture { name, path })
        })
        .collect();
    fixtures.sort_by(|a, b| a.name.cmp(&b.name));
    fixtures
}

/// Convenience: read a single fixture's source by name from a given
/// corpus directory. Panics if the file is missing or unreadable.
///
/// ```rust,ignore
/// let src = fixtures::load_by_name(&cve_dir, "01_cve_2021_44228_log4shell");
/// ```
pub fn load_by_name(dir: &Path, name: &str) -> String {
    let path = dir.join(format!("{name}.sigil"));
    fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "fixtures::load_by_name: cannot read {}: {e}",
            path.display()
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;
    use std::path::PathBuf;

    /// The sigil-compiler crate's tests directory, relative to this
    /// crate's manifest dir. Used only by tests inside sigil-test-utils
    /// itself to smoke-test the loader against the real corpus.
    ///
    /// In real use, consumers pass their own
    /// `env!("CARGO_MANIFEST_DIR")`-rooted paths.
    fn sigil_compiler_tests_dir() -> PathBuf {
        // sigil-test-utils/Cargo.toml → ../sigil-compiler/tests
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join("sigil-compiler")
            .join("tests")
    }

    #[test]
    fn each_sigil_file_finds_cve_corpus_entries() {
        let dir = sigil_compiler_tests_dir().join("cve_corpus");
        let fixtures = each_sigil_file(&dir);
        assert!(
            !fixtures.is_empty(),
            "cve_corpus should contain at least one .sigil file"
        );
        // Spot-check one known-stable fixture name.
        assert!(
            fixtures.iter().any(|f| f.name.contains("log4shell")),
            "expected a log4shell fixture in cve_corpus"
        );
    }

    #[test]
    fn each_sigil_file_is_sorted() {
        let dir = sigil_compiler_tests_dir().join("cve_corpus");
        let fixtures = each_sigil_file(&dir);
        for window in fixtures.windows(2) {
            assert!(
                window[0].name <= window[1].name,
                "fixtures should be sorted by name; saw {} before {}",
                window[0].name,
                window[1].name,
            );
        }
    }

    #[test]
    fn each_sigil_file_skips_markdown_companions() {
        let dir = sigil_compiler_tests_dir().join("cve_corpus");
        let fixtures = each_sigil_file(&dir);
        for f in &fixtures {
            assert_eq!(
                f.path.extension().and_then(|s| s.to_str()),
                Some("sigil"),
                "expected .sigil extension, got {:?}",
                f.path
            );
        }
    }

    #[test]
    #[should_panic(expected = "cannot read directory")]
    fn each_sigil_file_panics_on_missing_dir() {
        each_sigil_file(Path::new("/__does_not_exist__/cve_corpus"));
    }
}
