//! Determinism lock-in test.
//!
//! For every `.sigil` fixture in `tests/fixtures/`, `tests/cve_corpus/`,
//! and `tests/z3_corpus/`, compile it twice and assert that both
//! compiled artifacts are byte-equal:
//!   - `wasm_inner`
//!   - `wasm_outer`
//!
//! Why: agent-driven workflows want to use the compiled-Wasm SHA as a
//! memoization key. That only works if compilation is hash-stable —
//! identical input → byte-identical output. Common sources of
//! nondeterminism in a Rust compiler: `HashMap`/`HashSet` iteration
//! order leaking into emitted bytecode; system clock; thread-pool
//! scheduling; random IDs. This test fixes the invariant at the API
//! boundary; any future drift fails the test immediately.
//!
//! What this test does NOT prove:
//!   - Cross-platform stability (the test runs on whatever host the
//!     suite is invoked on; cross-platform determinism would need a
//!     separate harness running on each target).
//!   - Cross-version stability (sigil-compiler version bumps are
//!     allowed to change output; this test only asserts run-over-run
//!     stability within a single binary).
//!   - Z3 timing determinism — only Z3 OUTPUT for a given query, not
//!     the wall-clock to discharge it.
//!
//! Iteration over collections inside the test uses `BTreeSet` so the
//! per-fixture failure list is deterministic regardless of HashMap
//! iteration order in the broader compiler.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use sigil_compiler::compile_named_module;

const CORPORA: &[&str] = &["fixtures", "cve_corpus", "z3_corpus"];

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn collect_sigil_files(dir: &Path) -> Vec<PathBuf> {
    let mut out: BTreeSet<PathBuf> = BTreeSet::new();
    if !dir.is_dir() {
        return Vec::new();
    }
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return Vec::new(),
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) == Some("sigil") {
            out.insert(path);
        }
    }
    out.into_iter().collect()
}

#[derive(Debug)]
struct Mismatch {
    fixture: PathBuf,
    detail: String,
}

/// Compile a fixture twice and compare the two Wasm artefacts byte-by-
/// byte. Returns `Some(Mismatch)` on drift; `None` on a clean compare.
/// Fixtures whose compiles fail (expect-error programs) are silently
/// skipped — there's nothing to compare. Fixtures where the two
/// compiles disagree on success/failure are themselves a determinism
/// bug and are reported.
fn check_fixture(path: &Path) -> Option<Mismatch> {
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            return Some(Mismatch {
                fixture: path.to_path_buf(),
                detail: format!("read error: {e}"),
            });
        }
    };
    let name = path
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("?")
        .to_string();

    let first = compile_named_module(name.clone(), source.clone());
    let second = compile_named_module(name.clone(), source.clone());

    match (first, second) {
        (Ok(a), Ok(b)) => {
            if a.wasm_inner != b.wasm_inner {
                return Some(Mismatch {
                    fixture: path.to_path_buf(),
                    detail: format!(
                        "wasm_inner differs across runs: first={} bytes, second={} bytes, \
                         first_sha={:x} second_sha={:x}",
                        a.wasm_inner.len(),
                        b.wasm_inner.len(),
                        simple_fnv(&a.wasm_inner),
                        simple_fnv(&b.wasm_inner),
                    ),
                });
            }
            let outer_a = a.wasm_outer.as_deref().unwrap_or(&[]);
            let outer_b = b.wasm_outer.as_deref().unwrap_or(&[]);
            if outer_a != outer_b {
                return Some(Mismatch {
                    fixture: path.to_path_buf(),
                    detail: format!(
                        "wasm_outer differs across runs: first={} bytes, second={} bytes",
                        outer_a.len(),
                        outer_b.len(),
                    ),
                });
            }
            None
        }
        (Err(_), Err(_)) => {
            // expect-error fixture; both runs errored. We do not
            // currently compare error payloads because diagnostic
            // ordering may legitimately vary across runs. Skip.
            None
        }
        (Ok(_), Err(_)) | (Err(_), Ok(_)) => Some(Mismatch {
            fixture: path.to_path_buf(),
            detail: "first and second compiles disagreed on success/failure".to_string(),
        }),
    }
}

/// Hash-equivalent debug formatter. Not cryptographic — just enough
/// to print a stable identifier of a byte slice in test output. FNV-
/// 1a 64-bit.
fn simple_fnv(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100_0000_01b3);
    }
    h
}

#[test]
fn compilation_is_byte_stable_across_runs() {
    let mut mismatches: Vec<Mismatch> = Vec::new();
    let mut total = 0usize;

    for corpus in CORPORA {
        let dir = manifest_dir().join("tests").join(corpus);
        for fixture in collect_sigil_files(&dir) {
            total += 1;
            if let Some(m) = check_fixture(&fixture) {
                mismatches.push(m);
            }
        }
    }

    if !mismatches.is_empty() {
        let mut msg = format!(
            "Determinism lock failed: {} of {} fixtures produced different bytes across two compiles.\n",
            mismatches.len(),
            total,
        );
        for m in &mismatches {
            msg.push_str(&format!("  - {}: {}\n", m.fixture.display(), m.detail));
        }
        panic!("{msg}");
    }
}
