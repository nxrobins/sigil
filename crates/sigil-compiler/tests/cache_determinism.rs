// The cache only exists when the `solver` feature is on. Under
// `--no-default-features` CI, this test compiles to an empty crate.
// (The check is vacuous without the cache to test.)
#![cfg(feature = "solver")]

//! Cache-soundness cross-check (axis-2 eighth touch, commit 5 of 6).
//!
//! For every fixture in `tests/fixtures/`, `tests/cve_corpus/`, and
//! `tests/z3_corpus/`, compile twice — once with `SIGIL_Z3_CACHE=off`
//! and once with the cache ON — and assert both compiles produce
//! byte-identical `wasm_inner` and `wasm_outer`. The cache must NEVER
//! cause a wasm-level difference; if it does, it's a soundness bug
//! that compromises the verification certificate.
//!
//! Why this is distinct from `determinism_lock.rs`: that test runs
//! two compiles with the SAME cache state; this one varies the cache
//! state to specifically exercise the cache code path.
//!
//! ┌─────────────────────────────────────────────────────────────────┐
//! │ DO NOT add additional `#[test] fn` to this file.                │
//! │ The single-test invariant means env-var mutations don't need    │
//! │ cross-test coordination beyond TEST_LOCK. A second `#[test] fn` │
//! │ would race on env vars unless ALL tests in this file take       │
//! │ TEST_LOCK. See plan-file round-2 ledger → UP-7.                 │
//! └─────────────────────────────────────────────────────────────────┘

use std::collections::{BTreeSet, HashSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use sigil_compiler::DiagnosticCode;
use sigil_compiler::compile_named_module;
use sigil_compiler::z3_cache::{reset_for_test_with_env_reread, stats_snapshot};

/// The determinism test exercises all three corpora — including
/// cve_corpus, which is mostly expect-error fixtures: those exercise
/// the (Err, Err) match arm, which still asserts that the diagnostic
/// code set doesn't drift between cache-off and cache-on. The bench
/// excludes cve_corpus because it's not a perf measurement; see
/// plan-file round-2 ledger MI-5.
const CORPORA: &[&str] = &["fixtures", "cve_corpus", "z3_corpus"];

/// Serializes env-var mutations across tests in this binary. The
/// single-test-fn invariant (see top doc) means only one taker today;
/// future tests added to this file MUST also acquire this lock.
static TEST_LOCK: Mutex<()> = Mutex::new(());

/// RAII guard: snapshot an env var on construction, restore on Drop.
/// Drop is infallible — restore errors are swallowed to avoid
/// double-panicking from a destructor. See round-2 ledger MC-5.
struct EnvGuard {
    key: &'static str,
    prev: Option<String>,
}

impl EnvGuard {
    fn set(key: &'static str, value: &str) -> Self {
        let prev = env::var(key).ok();
        // SAFETY: tests holding TEST_LOCK serialize env-var mutations;
        // no concurrent reader within this binary. Other integration-
        // test binaries don't run concurrently with this one.
        unsafe { env::set_var(key, value) };
        Self { key, prev }
    }

    fn unset(key: &'static str) -> Self {
        let prev = env::var(key).ok();
        unsafe { env::remove_var(key) };
        Self { key, prev }
    }
}

impl Drop for EnvGuard {
    fn drop(&mut self) {
        // Infallible by construction. If restore fails, the env is
        // already in a weird state; double-panicking from Drop would
        // hide the original failure.
        match self.prev.take() {
            Some(v) => unsafe { env::set_var(self.key, v) },
            None => unsafe { env::remove_var(self.key) },
        }
    }
}

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

/// Compile one fixture under both cache states; compare wasm.
/// Returns `Some(Mismatch)` on drift; `None` on a clean compare or
/// an expect-error fixture whose diagnostic codes match across modes.
///
/// Per round-2 UP-1, tempdir creation failure is fail-loud
/// (`.expect()`), not a silent skip. Per round-2 UP-2, `(Err, Err)`
/// requires matching diagnostic-code sets — different codes are a
/// soundness drift, not an expected-error skip.
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

    // Each fixture gets a fresh tempdir for L2 isolation. Fail-loud:
    // tempdir creation failure is an environment problem, not a
    // fixture-clean result. Round-2 UP-1.
    let tempdir = tempfile::tempdir().expect("test infrastructure: tempdir creation failed");
    // Outer-scope guard — both passes inherit SIGIL_Z3_CACHE_DIR.
    // Round-2 MI-2 / MI-7.
    let _cache_dir_guard = EnvGuard::set(
        "SIGIL_Z3_CACHE_DIR",
        tempdir.path().to_string_lossy().as_ref(),
    );

    // Pass 1: cache OFF.
    let off_result = {
        let _off_guard = EnvGuard::set("SIGIL_Z3_CACHE", "off");
        reset_for_test_with_env_reread();
        compile_named_module(name.clone(), source.clone())
    }; // _off_guard dropped here — SIGIL_Z3_CACHE restored.

    // Pass 2: cache ON (env var unset → default behavior).
    let on_result = {
        let _on_guard = EnvGuard::unset("SIGIL_Z3_CACHE");
        reset_for_test_with_env_reread();
        compile_named_module(name.clone(), source.clone())
    };

    // Explicit match arms; no `_ => None` collapse. Round-2 MC-4.
    match (off_result, on_result) {
        (Ok(a), Ok(b)) => {
            if a.wasm_inner != b.wasm_inner {
                return Some(Mismatch {
                    fixture: path.to_path_buf(),
                    detail: format!(
                        "wasm_inner differs between cache-off and cache-on: \
                         off={} bytes, on={} bytes",
                        a.wasm_inner.len(),
                        b.wasm_inner.len(),
                    ),
                });
            }
            let outer_a = a.wasm_outer.as_deref().unwrap_or(&[]);
            let outer_b = b.wasm_outer.as_deref().unwrap_or(&[]);
            if outer_a != outer_b {
                return Some(Mismatch {
                    fixture: path.to_path_buf(),
                    detail: format!(
                        "wasm_outer differs between cache-off and cache-on: \
                         off={} bytes, on={} bytes",
                        outer_a.len(),
                        outer_b.len(),
                    ),
                });
            }
            None
        }
        (Err(off_err), Err(on_err)) => {
            // Round-2 UP-2: same diagnostic code set ⇒ benign
            // expected error. Different codes ⇒ cache changed WHICH
            // error fires.
            let off_codes: HashSet<DiagnosticCode> =
                off_err.diagnostics().iter().map(|d| d.code()).collect();
            let on_codes: HashSet<DiagnosticCode> =
                on_err.diagnostics().iter().map(|d| d.code()).collect();
            if off_codes != on_codes {
                let off_sorted: BTreeSet<&str> = off_codes.iter().map(|c| c.as_str()).collect();
                let on_sorted: BTreeSet<&str> = on_codes.iter().map(|c| c.as_str()).collect();
                Some(Mismatch {
                    fixture: path.to_path_buf(),
                    detail: format!(
                        "cache-off and cache-on errored with different diagnostic codes: \
                         off={off_sorted:?}, on={on_sorted:?}",
                    ),
                })
            } else {
                None
            }
        }
        (Ok(_), Err(_)) => Some(Mismatch {
            fixture: path.to_path_buf(),
            detail: "cache-off compiled OK but cache-on errored — cache poisoned compile success"
                .to_string(),
        }),
        (Err(_), Ok(_)) => Some(Mismatch {
            fixture: path.to_path_buf(),
            detail:
                "cache-off errored but cache-on compiled OK — cache mode changed compile outcome"
                    .to_string(),
        }),
    }
}

#[test]
fn cache_does_not_affect_wasm_output() {
    let _lock = TEST_LOCK.lock().unwrap();

    // Snapshot cache stats BEFORE the run so we can assert the cache
    // was actually exercised across the corpus. Round-2 MC-9 / MI-1.
    let (hits_before, misses_before) = stats_snapshot();

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

    // Cache-was-exercised assertion: if no cap queries ran, the
    // "soundness check" is vacuous. Round-2 MC-9 / MI-1.
    let (hits_after, misses_after) = stats_snapshot();
    let cache_activity = (hits_after - hits_before) + (misses_after - misses_before);
    assert!(
        cache_activity > 0,
        "cache soundness test was vacuous — no fixture exercised the \
         cache path (hits+misses delta = 0). Add at least one cap-typed \
         fixture to the corpora, or remove this test."
    );

    if !mismatches.is_empty() {
        let mut msg = format!(
            "Cache soundness check failed: {} of {} fixtures produced \
             different wasm under cache-off vs cache-on.\n",
            mismatches.len(),
            total,
        );
        for m in &mismatches {
            msg.push_str(&format!("  - {}: {}\n", m.fixture.display(), m.detail));
        }
        panic!("{msg}");
    }
}
