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
//!
//! The SHP-P0 tests at the bottom lock one known leak the corpus double-compile could not
//! see: a closure's capture order is its `__env` layout. They pin that layout at both ends
//! (the construct's stores and the lifted body's loads, as exact offsets) and compile the
//! multi-capture fixture sixteen times.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use sigil_compiler::air::{AirFunctionKind, AirStmt, VarId};
use sigil_compiler::compile_named_module;
use sigil_compiler::typed_ast::TypedFunctionKind;

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

// ── SHP-P0: closure capture order ───────────────────────────────────────────
//
// No fixture the corpora above compile holds a closure that captures anything (the one
// capturing closure in them sits in an expect-error fixture, which never reaches codegen),
// so they could not see the one known leak of `HashSet` order into bytes: a closure's
// captures came from a randomly seeded `HashSet`, and that order IS the `__env` layout. A
// closure with two or more captures compiled to a different module on every run. The
// fixture below captures three locals whose first-use order is not their name order.

const MULTI_CAPTURE: &str = include_str!("../../../tests/compile/closure_multi_capture.sigil");
const MULTI_CAPTURE_NAMES: [&str; 3] = ["alpha", "mid", "zeta"];

/// Index of the first artefact that differs from the first one, or `None` when all
/// agree (an empty or single-element list trivially agrees).
fn first_mismatch(artefacts: &[Vec<u8>]) -> Option<usize> {
    let first = artefacts.first()?;
    artefacts.iter().position(|a| a != first)
}

/// The anti-stub for the repeated-compile test below: the comparator must flag a
/// planted difference, or its silence proves nothing.
#[test]
fn first_mismatch_flags_a_planted_difference() {
    let same = vec![1u8, 2, 3];
    let mut planted = same.clone();
    planted[1] ^= 0x01;
    assert_eq!(
        first_mismatch(&[same.clone(), same.clone(), planted]),
        Some(2)
    );
    assert_eq!(first_mismatch(&[same.clone(), same.clone(), same]), None);
    assert_eq!(first_mismatch(&[]), None);
}

/// The layout itself, read three ways: the lifted closure's typed captures, the offsets its
/// AIR prologue loads them from (`__env` is param 0; captures start after the 4-byte table
/// index), and the offsets the enclosing function's closure construct stores them at. The
/// loads and the stores must both be exactly the name-ordered slots, in statement order: a
/// construct that stored in one order while the body loaded in another would be a miscompile
/// that byte stability alone cannot see.
#[test]
fn closure_captures_are_laid_out_in_name_order() {
    let compilation = compile_named_module("closure_multi_capture.sigil", MULTI_CAPTURE)
        .expect("the multi-capture fixture compiles");

    let closures: Vec<_> = compilation
        .typed
        .modules
        .iter()
        .flat_map(|m| m.functions.iter())
        .filter(|f| matches!(f.kind, TypedFunctionKind::Closure))
        .collect();
    assert_eq!(closures.len(), 1, "the fixture lifts exactly one closure");
    let typed_order: Vec<&str> = closures[0]
        .captures
        .iter()
        .map(|c| c.name.as_str())
        .collect();
    assert_eq!(
        typed_order, MULTI_CAPTURE_NAMES,
        "typed captures out of name order"
    );

    let lifted = compilation
        .air
        .functions
        .iter()
        .find(|f| matches!(f.kind, AirFunctionKind::Closure))
        .expect("the lifted closure reaches AIR");
    let loads: Vec<(u32, String)> = lifted
        .blocks
        .iter()
        .flat_map(|b| b.stmts.iter())
        .filter_map(|s| match s {
            AirStmt::LoadField {
                dst,
                base_ptr: VarId(0),
                offset,
                ..
            } => lifted.debug_names.get(dst).map(|n| (*offset, n.clone())),
            _ => None,
        })
        .filter(|(_, name)| MULTI_CAPTURE_NAMES.contains(&name.as_str()))
        .collect();
    // Three i64 captures after the 4-byte table index.
    let expected: Vec<(u32, String)> = [(4, "alpha"), (12, "mid"), (20, "zeta")]
        .iter()
        .map(|(offset, name)| (*offset, name.to_string()))
        .collect();
    assert_eq!(
        loads, expected,
        "the lifted body's prologue loads are not the name-ordered slots"
    );

    let stores: Vec<(u32, String)> = compilation
        .air
        .functions
        .iter()
        .filter(|f| !matches!(f.kind, AirFunctionKind::Closure))
        .flat_map(|f| {
            f.blocks
                .iter()
                .flat_map(|b| b.stmts.iter())
                .filter_map(move |s| match s {
                    AirStmt::StoreField { offset, val, .. } => {
                        f.debug_names.get(val).map(|n| (*offset, n.clone()))
                    }
                    _ => None,
                })
        })
        .filter(|(_, name)| MULTI_CAPTURE_NAMES.contains(&name.as_str()))
        .collect();
    assert_eq!(
        stores, expected,
        "the closure construct does not store the captures into the slots the body loads"
    );
}

/// Sixteen compiles of the multi-capture fixture in one process. Each compile hashed
/// its free variables with a fresh `RandomState`, so before the fix sixteen identical
/// modules over three captures was vanishingly unlikely; now it is the only outcome.
#[test]
fn closure_capture_bytes_are_stable_across_compiles() {
    let modules: Vec<Vec<u8>> = (0..16)
        .map(|_| {
            compile_named_module("closure_multi_capture.sigil", MULTI_CAPTURE)
                .expect("the multi-capture fixture compiles")
                .wasm_inner
        })
        .collect();
    assert_eq!(
        first_mismatch(&modules),
        None,
        "closure capture layout changed between compiles of the same source"
    );
}
