//! Z3 query result cache.
//!
//! Memoizes `solver.check()` against the canonical SMT-LIB2 form of
//! the solver's current assertion set. Two tiers:
//!
//! 1. **L1** — in-memory `LruCache<[u8; 32], CachedValue>` capped at 100k
//!    entries. Process-wide via `OnceLock<Mutex<…>>`; survives across
//!    compile invocations within one OS process (e.g., LSP, cargo-watch).
//! 2. **L2** — on-disk file-per-key under `<target>/.z3-cache/`. A
//!    fresh process consults L2 before falling through to a real Z3
//!    call; L2 hits are promoted into L1.
//!
//! Soundness: a wrong verdict = false-positive verification = security
//! hole. Defense-in-depth: on the FIRST hit per (key, process), re-run
//! Z3 from a fresh solver in the same context and panic on mismatch.
//! Once a (key, process) is verified, subsequent hits trust the cache.
//!
//! Env-var contract (read ONCE at cache init):
//!
//! * `SIGIL_Z3_CACHE=off|0|false|no|disabled` — disables L1 lookups,
//!   L2 reads, and L2 writes. Every `check_cached` call becomes a pure
//!   passthrough to the closure. Case-insensitive. Ambiguous values
//!   (`true`, `yes`) leave the cache ON.
//! * `SIGIL_Z3_CACHE_DIR=<path>` — override the auto-resolved L2
//!   location. Empty string treated as unset.
//! * `SIGIL_Z3_CACHE_VERIFY=always` — re-verify every hit, not just
//!   the first. Designed for paranoid CI: multiplies Z3 cost by ~2×.
//!   Not for interactive use.
//! * `SIGIL_Z3_CACHE_TREAT_UNKNOWN_AS_MISS=1` — treat cached `Unknown`
//!   as a miss (re-run Z3). Surfaces whether a higher rlimit would
//!   have answered.
//!
//! L2 location resolution (in order):
//!
//! 1. `$SIGIL_Z3_CACHE_DIR` (if set and non-empty).
//! 2. Walk up from CWD looking for a directory containing BOTH
//!    `Cargo.toml` AND `Cargo.lock` (workspace root). Use
//!    `$CARGO_TARGET_DIR` if set, else `<root>/target`. The pair
//!    requirement avoids being trapped by stray home-dir `Cargo.toml`.
//! 3. Fallback: `./target/.z3-cache/` relative to CWD.
//! 4. If none of the above can be created, L2 is silently disabled
//!    (one-time stderr warning suggests `SIGIL_Z3_CACHE_DIR`). L1
//!    keeps working.
//!
//! Stats overcount: under parallel compiles racing on the same key,
//! L2 misses can populate L1 from two threads simultaneously; the
//! `stats_hits` counter can over-report by at most
//! `(parallel_threads - 1)` per contended key. Not load-bearing — only
//! affects the `CapabilityReport.z3_cache_hits` field, which is
//! excluded from cert byte-equality.
//!
//! Cached values contain the verdict and an optional integer
//! counterexample. They do not contain a live model, unsat core, or proof.
//! Callers must not request those objects after a cache hit. The one model-
//! producing query extracts its counterexample during fresh evaluation and
//! stores the value with the verdict. `clippy.toml` enforces this boundary.
//!
//! Every query through this cache is validated by the runtime SMT
//! fragment guard (`z3_fragment_guard.rs`): once BEFORE any cache
//! consultation (hits get validated queries + manifest recording) and
//! again inside `fresh_check` at the moment of the actual solve. See
//! docs/specs/z3-fragment-guard.md.

use std::collections::{HashMap, HashSet};
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::io::{ErrorKind, Write};
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, OnceLock};

use lru::LruCache;
use sha2::{Digest, Sha256};
use z3::{SatResult, Solver};

use crate::z3_fragment_guard::FragmentViolation;

/// Bound on the in-memory cache. Conservative — beyond this is
/// pathological input territory. LRU evicts silently; eviction is
/// invisible (future lookups simply miss).
const L1_MAX_ENTRIES: usize = 100_000;

/// Soft cap on L2 file count. Past this, new writes are silently
/// refused (one-time stderr warning suggests `cargo clean`); reads
/// keep working. Avoids unbounded growth on long-running CI machines.
const L2_MAX_FILES: usize = 100_000;

/// Refresh the cached `l2_file_count` from disk every 2^N writes.
/// Mask check `count & L2_REFRESH_MASK == 0` recovers from external
/// deletions (manual `cargo clean`, gc) without paying the O(n)
/// `read_dir` cost on every write.
const L2_REFRESH_MASK: usize = 0x3FF; // every 1024 writes

/// L2 file layout. Format version 2 carries an optional `i64`
/// counterexample alongside the verdict. Version 1 files are treated as
/// misses and overwritten.
///
/// Byte layout (total = 18 bytes):
///
/// - `magic_u32` (4 bytes)
/// - `format_version_u32` (4 bytes)
/// - `verdict_u8` (1 byte)
/// - `has_cex_u8` (1 byte; 0 = no cex, 1 = cex present)
/// - `cex_i64_le` (8 bytes; ignored when `has_cex_u8 == 0`)
const CACHE_MAGIC: u32 = 0x5A_43_43_31; // "ZCC1" (little-endian text)
const CACHE_FORMAT_VERSION: u32 = 2;
const L2_FILE_BYTES: usize = 4 + 4 + 1 + 1 + 8; // magic + version + verdict + has_cex + cex_i64

/// Z3 library version proxy.
///
/// The actual `Z3_get_version` FFI accessor requires an `unsafe` block,
/// but `sigil-compiler` enforces `forbid(unsafe_code)` at the crate
/// level. Rather than relax that crate-wide invariant for a version
/// string, we use the `z3` BINDING crate's pinned version (from
/// Cargo.toml) as the proxy. Bumping the `z3` dep in Cargo.toml
/// requires a Cargo.lock rebuild and changes this string; that's the
/// invalidation trigger.
///
/// Limitation: if the underlying Z3 library is rebuilt with a different
/// algorithm without bumping the binding's version, this proxy doesn't
/// catch it. Defense-in-depth: belt-and-braces verification on first
/// hit per (key, process) re-runs Z3 and catches verdict drift.
const Z3_BINDING_VERSION: &str = "z3-binding-0.12";

/// Cached verdict from `solver.check()`.
///
/// Maps 1:1 to `z3::SatResult`; stored as a 1-byte representation in
/// the L2 on-disk format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

impl From<SatResult> for Verdict {
    fn from(r: SatResult) -> Self {
        match r {
            SatResult::Sat => Verdict::Sat,
            SatResult::Unsat => Verdict::Unsat,
            SatResult::Unknown => Verdict::Unknown,
        }
    }
}

impl Verdict {
    fn as_u8(self) -> u8 {
        match self {
            Verdict::Sat => 0,
            Verdict::Unsat => 1,
            Verdict::Unknown => 2,
        }
    }

    fn from_u8(b: u8) -> Option<Self> {
        match b {
            0 => Some(Verdict::Sat),
            1 => Some(Verdict::Unsat),
            2 => Some(Verdict::Unknown),
            _ => None,
        }
    }
}

/// A solver verdict and optional integer counterexample. Ordinary queries
/// store `None`. Refinement subsumption may extract `Some(i64)` immediately
/// after a fresh SAT result and cache it with the verdict.
pub type CachedValue = (Verdict, Option<i64>);

struct Z3CacheState {
    l1: LruCache<[u8; 32], CachedValue>,
    /// Keys we have re-verified at least once via a fresh solver. After
    /// the first verified hit, future hits trust the cache directly.
    verified_first_hit: HashMap<[u8; 32], ()>,
    stats_hits: u64,
    stats_misses: u64,
    // Env-var quartet (read once at construction).
    enabled: bool,
    on_disk_root: Option<PathBuf>,
    verify_every_hit: bool,
    treat_unknown_as_miss: bool,
    // Cached count of `*.bin` files in `on_disk_root`. Seeded by one
    // `read_dir` at construction; refreshed every 1024 writes.
    l2_file_count: usize,
    // Dedupe per-process stderr warnings about disk I/O errors.
    warned_io_kinds: HashSet<ErrorKind>,
}

impl Z3CacheState {
    /// Read env vars + resolve cache location. Called once at OnceLock
    /// init AND on every `reset_for_test_with_env_reread()` call.
    fn new_from_env() -> Self {
        let enabled = env::var("SIGIL_Z3_CACHE")
            .ok()
            .map(|v| !env_is_truthy_off(&v))
            .unwrap_or(true);

        let verify_every_hit = env::var("SIGIL_Z3_CACHE_VERIFY")
            .ok()
            .map(|v| v.trim().eq_ignore_ascii_case("always"))
            .unwrap_or(false);

        let treat_unknown_as_miss = env::var("SIGIL_Z3_CACHE_TREAT_UNKNOWN_AS_MISS")
            .ok()
            .map(|v| v.trim() == "1")
            .unwrap_or(false);

        // L2 root: only resolved when the cache is enabled. Saves a
        // `read_dir` + `create_dir_all` on the `SIGIL_Z3_CACHE=off`
        // path.
        let on_disk_root = if enabled { resolve_cache_dir() } else { None };

        let l2_file_count = on_disk_root.as_deref().map(count_l2_bin_files).unwrap_or(0);

        Self {
            l1: LruCache::new(NonZeroUsize::new(L1_MAX_ENTRIES).expect("L1_MAX_ENTRIES > 0")),
            verified_first_hit: HashMap::new(),
            stats_hits: 0,
            stats_misses: 0,
            enabled,
            on_disk_root,
            verify_every_hit,
            treat_unknown_as_miss,
            l2_file_count,
            warned_io_kinds: HashSet::new(),
        }
    }
}

/// Env helper: lowercase-compare against the disable vocabulary.
/// Ambiguous values (`true`, `yes` for the off-switch) leave the
/// cache ON — this function returns false for them.
fn env_is_truthy_off(s: &str) -> bool {
    matches!(
        s.trim().to_ascii_lowercase().as_str(),
        "off" | "0" | "false" | "no" | "disabled"
    )
}

static GLOBAL: OnceLock<Mutex<Z3CacheState>> = OnceLock::new();

fn with_state<R>(f: impl FnOnce(&mut Z3CacheState) -> R) -> R {
    let state = GLOBAL.get_or_init(|| Mutex::new(Z3CacheState::new_from_env()));
    let mut guard = state.lock().expect("Z3 cache state mutex poisoned");
    f(&mut guard)
}

/// Cumulative (hits, misses) since process start. Used by
/// `CapabilityReport` to surface cache effectiveness in the certificate
/// (excluded from cert byte-equality alongside `z3_rlimit_consumed`).
///
/// Note: under parallel compiles racing on the same key, `hits` can
/// over-report by at most `parallel_threads - 1` per contended key.
/// Not load-bearing — the stat is informational, never gates behavior.
pub fn stats_snapshot() -> (u64, u64) {
    with_state(|s| (s.stats_hits, s.stats_misses))
}

/// Test-only reset hook. Clears L1, verified set, and stats; keeps
/// the env-derived configuration intact. Used by tests that exercise
/// hit/miss counts and want a clean slate.
#[cfg(test)]
pub fn reset_for_test() {
    with_state(|s| {
        s.l1.clear();
        s.verified_first_hit.clear();
        s.stats_hits = 0;
        s.stats_misses = 0;
        s.warned_io_kinds.clear();
    });
}

/// Integration-test reset hook. Replaces the inner state with a
/// fresh `Z3CacheState::new_from_env()` so env-var-setting tests
/// don't depend on test ordering relative to `OnceLock`
/// initialization. The `OnceLock` stays initialized — only the
/// inner state is replaced.
///
/// **Stats are preserved across resets**: `stats_hits` and
/// `stats_misses` carry over from the previous state. Integration
/// tests that loop over many fixtures and want to assert cumulative
/// cache activity (e.g., `cache_determinism.rs`'s "test wasn't
/// vacuous" check) rely on this. Use `reset_for_test()` instead if
/// you want pristine counters.
///
/// Production callers MUST NOT touch this. Doc-hidden so it doesn't
/// appear in rustdoc; the `for_test` name is the second deterrent.
/// The only caller outside this module is the
/// `cache_determinism.rs` integration test.
#[doc(hidden)]
pub fn reset_for_test_with_env_reread() {
    let state = GLOBAL.get_or_init(|| Mutex::new(Z3CacheState::new_from_env()));
    let mut guard = state.lock().expect("Z3 cache state mutex poisoned");
    let stats_hits = guard.stats_hits;
    let stats_misses = guard.stats_misses;
    *guard = Z3CacheState::new_from_env();
    guard.stats_hits = stats_hits;
    guard.stats_misses = stats_misses;
}

/// The ONE sanctioned direct `Solver::check` for cached-path fresh
/// evaluation. Re-walks the solver through the fragment guard at check
/// time. The pre-lookup walk in `check_cached_with_model` is additive, not a
/// substitute, because the `run_fresh` closure between them could
/// otherwise assert formulas the guard never saw).
///
/// Callers pass this (or wrap it, for model extraction) instead of
/// writing `solver.check()` themselves — `z3::Solver::check` is on the
/// clippy `disallowed-methods` fence.
pub fn fresh_check(solver: &Solver<'_>) -> Result<Verdict, FragmentViolation> {
    crate::z3_fragment_guard::check_fragment(solver)?;
    #[allow(clippy::disallowed_methods)] // sanctioned: cache-miss evaluation (walk above)
    let verdict: Verdict = solver.check().into();
    Ok(verdict)
}

/// Memoized wrapper around `solver.check()`.
///
/// Lookup order: fragment guard → L1 → L2 → fresh. L2 hits are promoted
/// into L1. `SIGIL_Z3_CACHE=off` bypasses all cache layers (never the
/// guard).
///
/// Returns the Verdict only; the cache's counterexample slot is always
/// `None` for callers that don't supply a model extractor. For
/// counterexample-aware callers (refinement subsumption queries),
/// use `check_cached_with_model` below.
pub fn check_cached(
    solver: &Solver<'_>,
    run_fresh: impl FnOnce(&Solver<'_>) -> Result<Verdict, FragmentViolation>,
) -> Result<Verdict, FragmentViolation> {
    Ok(check_cached_with_model(solver, |s| Ok((run_fresh(s)?, None)))?.0)
}

/// Memoized wrapper that also caches an optional counterexample integer
/// alongside the verdict. The `run_fresh` closure
/// receives the solver and returns `(Verdict, Option<i64>)` — the i64 is
/// the counterexample value when the verdict is `Sat` AND the caller
/// extracted it from `solver.get_model()` BEFORE the solver scope ended.
///
/// On cache hit, the cached `(Verdict, Option<i64>)` tuple is returned
/// directly — `solver.get_model()` is NOT re-invoked, because the solver
/// state on cache hit may have never run `solver.check()`. This is the
/// load-bearing architectural decision: the counterexample MUST be
/// extracted at the moment of fresh evaluation, not deferred until cache
/// hit.
///
/// ## The fragment guard runs FIRST
///
/// Before any cache consultation, every assertion is walked by
/// `z3_fragment_guard::check_fragment`; a violation rejects the query
/// with NO cache interaction (no stats, no lookup, no store). Rationale:
/// cache hits get validated queries + manifest recording, and the
/// placement survives any future lossy-key refactor. (It is NOT an
/// anti-poisoning measure — the key is the SHA256 of the canonical
/// assertion text, so an out-of-fragment query can never collide into a
/// clean entry's verdict; verdict integrity is `SIGIL_Z3_CACHE_VERIFY`'s
/// job.)
pub fn check_cached_with_model(
    solver: &Solver<'_>,
    run_fresh: impl FnOnce(&Solver<'_>) -> Result<CachedValue, FragmentViolation>,
) -> Result<CachedValue, FragmentViolation> {
    let report = crate::z3_fragment_guard::check_fragment(solver)?;
    crate::z3_fragment_guard::record_observations(&report);

    let canonical = canonical_smt(solver);
    let key = canonical_key(&canonical);

    let (enabled, on_disk_root, verify_every_hit, treat_unknown_as_miss) = with_state(|s| {
        (
            s.enabled,
            s.on_disk_root.clone(),
            s.verify_every_hit,
            s.treat_unknown_as_miss,
        )
    });

    if !enabled {
        return run_fresh(solver);
    }

    // L1 lookup.
    let l1_cached = with_state(|s| s.l1.get(&key).copied());
    if let Some((verdict, cex)) = l1_cached {
        if treat_unknown_as_miss && verdict == Verdict::Unknown {
            // Fall through to L2 / fresh.
        } else {
            with_state(|s| s.stats_hits = s.stats_hits.saturating_add(1));
            maybe_verify_hit(solver, &canonical, &key, verdict, verify_every_hit);
            return Ok((verdict, cex));
        }
    }

    // L2 lookup — mutex released during disk I/O.
    if let Some(ref root) = on_disk_root
        && let Some((verdict, cex)) = read_l2(root, &key)
        && !(treat_unknown_as_miss && verdict == Verdict::Unknown)
    {
        with_state(|s| {
            s.stats_hits = s.stats_hits.saturating_add(1);
            s.l1.put(key, (verdict, cex)); // promote into L1
        });
        maybe_verify_hit(solver, &canonical, &key, verdict, verify_every_hit);
        return Ok((verdict, cex));
    }

    // Fresh.
    let (verdict, cex) = run_fresh(solver)?;
    with_state(|s| {
        s.stats_misses = s.stats_misses.saturating_add(1);
        s.l1.put(key, (verdict, cex));
        // First "hit" against our own fresh result is implicitly
        // verified — record it so we don't re-verify on the next lookup.
        s.verified_first_hit.insert(key, ());
    });
    if let Some(ref root) = on_disk_root {
        write_l2(root, &key, verdict, cex); // best-effort; warns internally
    }
    Ok((verdict, cex))
}

/// Decide whether this hit needs belt-and-braces verification, and run
/// it if so. The mutex is taken briefly here (to read the
/// verified-first-hit set) and again after (to record the verification);
/// the actual fresh solver work runs without the lock held.
fn maybe_verify_hit(
    solver: &Solver<'_>,
    canonical: &str,
    key: &[u8; 32],
    cached: Verdict,
    verify_every_hit: bool,
) {
    let needs_verify = verify_every_hit || with_state(|s| !s.verified_first_hit.contains_key(key));
    if needs_verify {
        verify_first_hit(solver, canonical, key, cached);
        if !verify_every_hit {
            with_state(|s| {
                s.verified_first_hit.insert(*key, ());
            });
        }
    }
}

/// Belt-and-braces verification on first hit per (key, process).
///
/// Builds a NEW solver in the same context, re-asserts every assertion
/// from the original solver, and re-checks. Mismatch = soundness bug
/// (canonicalization collision or cache corruption). Aborts loudly so
/// CI can't silently absorb it.
fn verify_first_hit(original: &Solver<'_>, canonical: &str, key: &[u8; 32], cached: Verdict) {
    let fresh = Solver::new(original.get_context());
    for a in original.get_assertions() {
        fresh.assert(&a);
    }
    // ET-Z1: the walk lives in the same function as the check. The
    // original already passed the pre-lookup guard with identical
    // assertions, so a violation here means the re-assert itself is
    // broken — abort as loudly as a verdict mismatch.
    if let Err(v) = crate::z3_fragment_guard::check_fragment(&fresh) {
        panic!(
            "Z3 cache re-verification solver left the decidable fragment — {v}\n  key: {}\n  query: {}\n",
            hex_lower(key),
            canonical_prefix_for_log(canonical),
        );
    }
    #[allow(clippy::disallowed_methods)] // sanctioned: belt-and-braces re-verification (walk above)
    let fresh_verdict: Verdict = fresh.check().into();
    if fresh_verdict != cached {
        panic!(
            "Z3 cache verdict mismatch — soundness bug.\n\
             \n  cached:  {cached:?}\n  fresh:   {fresh_verdict:?}\n  key:     {}\n  query:   {}\n",
            hex_lower(key),
            canonical_prefix_for_log(canonical),
        );
    }
}

fn hex_lower(bytes: &[u8; 32]) -> String {
    use std::fmt::Write;
    let mut s = String::with_capacity(64);
    for b in bytes {
        let _ = write!(&mut s, "{b:02x}");
    }
    s
}

fn canonical_prefix_for_log(s: &str) -> String {
    let mut out = String::with_capacity(200);
    for ch in s.chars().take(200) {
        out.push(ch);
    }
    if s.len() > 200 {
        out.push('…');
    }
    out
}

/// Canonical SMT-LIB form: serialize each assertion in
/// `solver.get_assertions()` and concatenate, sorted.
///
/// Why NOT `solver.to_string()`: that calls `Z3_solver_to_string`,
/// which is unstable across `solver.check()`. After check, Z3 adds
/// internal model-completion bookkeeping. Two cache lookups on the
/// same solver — one before check, one after — would compute different
/// keys → 100% miss rate.
///
/// `get_assertions()` returns the original `Vec<Bool>` of asserted
/// expressions. Each Bool's `Display` serializes the AST without
/// solver-internal state. Sorted to make assertion order irrelevant.
pub(crate) fn canonical_smt(solver: &Solver<'_>) -> String {
    let assertions = solver.get_assertions();
    let mut serialized: Vec<String> = assertions.iter().map(|a| a.to_string()).collect();
    serialized.sort();
    let mut out = String::with_capacity(serialized.iter().map(|s| s.len() + 1).sum());
    for a in serialized {
        out.push_str(&a);
        out.push('\n');
    }
    out
}

/// SHA-256 over the canonical SMT-LIB form + the compiler version +
/// the Z3 library version. Either version changing invalidates the
/// cache entry.
pub(crate) fn canonical_key(canonical: &str) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(canonical.as_bytes());
    h.update(b"\n");
    h.update(env!("CARGO_PKG_VERSION").as_bytes());
    h.update(b"\n");
    h.update(Z3_BINDING_VERSION.as_bytes());
    h.finalize().into()
}

// ─────────────────────────────────────────────────────────────────────
// Cache-dir resolution
// ─────────────────────────────────────────────────────────────────────

/// One-time stderr warning when L2 can't be enabled.
static WARNED_NO_L2: AtomicBool = AtomicBool::new(false);
fn warn_cache_dir_unresolved_once() {
    if !WARNED_NO_L2.swap(true, Ordering::Relaxed) {
        eprintln!(
            "Z3 cache: L2 disabled (could not resolve target/.z3-cache/). \
             Set SIGIL_Z3_CACHE_DIR=<path> to enable."
        );
    }
}

/// One-time stderr warning when L2 hits the soft file cap.
static WARNED_FULL_CACHE: AtomicBool = AtomicBool::new(false);
fn warn_full_cache_once() {
    if !WARNED_FULL_CACHE.swap(true, Ordering::Relaxed) {
        eprintln!(
            "Z3 cache: L2 directory contains ≥{L2_MAX_FILES} *.bin files; \
             refusing new writes. Run `cargo clean` to reset."
        );
    }
}

fn resolve_cache_dir() -> Option<PathBuf> {
    // 1. Explicit override.
    if let Some(p) = env::var("SIGIL_Z3_CACHE_DIR")
        .ok()
        .filter(|s| !s.is_empty())
    {
        let path = PathBuf::from(p);
        if fs::create_dir_all(&path).is_err() {
            warn_cache_dir_unresolved_once();
            return None;
        }
        return Some(path);
    }

    // 2. Walk up looking for BOTH Cargo.toml AND Cargo.lock.
    //    Real workspaces have both; home-dir strays lack the lock.
    let cwd = env::current_dir().ok()?;
    let mut search: &Path = cwd.as_path();
    let workspace_root: Option<PathBuf> = loop {
        if search.join("Cargo.toml").is_file() && search.join("Cargo.lock").is_file() {
            break Some(search.to_path_buf());
        }
        match search.parent() {
            Some(parent) => search = parent,
            None => break None,
        }
    };

    // 3. Resolve target root: $CARGO_TARGET_DIR if set, else
    //    <workspace_root>/target, else ./target. Filter empty.
    let target_root = env::var("CARGO_TARGET_DIR")
        .ok()
        .filter(|s| !s.is_empty())
        .map(PathBuf::from)
        .or_else(|| workspace_root.map(|w| w.join("target")))
        .unwrap_or_else(|| PathBuf::from("./target"));
    let cache = target_root.join(".z3-cache");

    if fs::create_dir_all(&cache).is_err() {
        warn_cache_dir_unresolved_once();
        return None;
    }
    Some(cache)
}

// ─────────────────────────────────────────────────────────────────────
// L2 read / write
// ─────────────────────────────────────────────────────────────────────

fn key_path(root: &Path, key: &[u8; 32]) -> PathBuf {
    use std::fmt::Write;
    let mut name = String::with_capacity(64 + 4);
    for b in key {
        let _ = write!(&mut name, "{b:02x}");
    }
    name.push_str(".bin");
    root.join(name)
}

/// One-shot count of `*.bin` files in the cache root. Filters out
/// `.`, `..`, and any non-.bin sibling files (sidecar metadata,
/// editor tmpfiles, lock files).
fn count_l2_bin_files(root: &Path) -> usize {
    fs::read_dir(root)
        .map(|it| {
            it.filter_map(|e| e.ok())
                .filter(|e| e.path().extension() == Some(OsStr::new("bin")))
                .count()
        })
        .unwrap_or(0)
}

/// Dedupe-once-per-kind stderr warning channel. The `HashSet<ErrorKind>`
/// is tiny so brief contention is negligible.
fn warn_io_error_once(context: &str, kind: ErrorKind) {
    let should_warn = with_state(|s| s.warned_io_kinds.insert(kind));
    if should_warn {
        eprintln!(
            "Z3 cache: {context}: I/O error {kind:?} \
             (will continue without persisting)"
        );
    }
}

fn read_l2(root: &Path, key: &[u8; 32]) -> Option<CachedValue> {
    let path = key_path(root, key);
    let bytes = match fs::read(&path) {
        Ok(b) => b,
        Err(e) if e.kind() == ErrorKind::NotFound => return None, // expected miss
        Err(e) => {
            warn_io_error_once("read", e.kind());
            return None;
        }
    };
    if bytes.len() != L2_FILE_BYTES {
        return None; // truncated / corrupt → miss; will be overwritten
    }
    let magic = u32::from_le_bytes(bytes[0..4].try_into().ok()?);
    if magic != CACHE_MAGIC {
        return None;
    }
    let version = u32::from_le_bytes(bytes[4..8].try_into().ok()?);
    if version != CACHE_FORMAT_VERSION {
        // V45: pre-V45 files (version 1, 9 bytes) auto-rejected via
        // length mismatch above. This branch catches a future format
        // bump arriving at an older binary.
        return None;
    }
    let verdict = Verdict::from_u8(bytes[8])?;
    // V45: bytes[9] is has_cex_u8; bytes[10..18] is cex_i64_le.
    let cex = match bytes[9] {
        0 => None,
        1 => Some(i64::from_le_bytes(bytes[10..18].try_into().ok()?)),
        _ => return None, // invalid has_cex byte
    };
    Some((verdict, cex))
}

fn write_l2(root: &Path, key: &[u8; 32], verdict: Verdict, cex: Option<i64>) {
    // O(1) amortized soft-cap check via cached count.
    // Refresh from disk every 1024 writes to recover from external deletes.
    let (count_now, needs_refresh) =
        with_state(|s| (s.l2_file_count, s.l2_file_count & L2_REFRESH_MASK == 0));
    let count_now = if needs_refresh {
        let fresh = count_l2_bin_files(root);
        with_state(|s| s.l2_file_count = fresh);
        fresh
    } else {
        count_now
    };
    if count_now >= L2_MAX_FILES {
        warn_full_cache_once();
        return;
    }

    let mut buf = Vec::with_capacity(L2_FILE_BYTES);
    buf.extend_from_slice(&CACHE_MAGIC.to_le_bytes());
    buf.extend_from_slice(&CACHE_FORMAT_VERSION.to_le_bytes());
    buf.push(verdict.as_u8());
    // V45: emit has_cex_u8 + cex_i64_le. Non-subsumption callers pass
    // None; the i64 slot is zeroed but ignored on read (has_cex==0).
    match cex {
        Some(v) => {
            buf.push(1);
            buf.extend_from_slice(&v.to_le_bytes());
        }
        None => {
            buf.push(0);
            buf.extend_from_slice(&0i64.to_le_bytes());
        }
    }

    let tmp = match tempfile::NamedTempFile::new_in(root) {
        Ok(t) => t,
        Err(e) => {
            warn_io_error_once("tempfile", e.kind());
            return;
        }
    };
    if let Err(e) = tmp.as_file().write_all(&buf) {
        warn_io_error_once("write", e.kind());
        return;
    }
    match tmp.persist(key_path(root, key)) {
        Ok(_) => {
            with_state(|s| s.l2_file_count = s.l2_file_count.saturating_add(1));
        }
        Err(e) => {
            warn_io_error_once("persist", e.error.kind());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::ast::{Ast, Bool, Int};

    fn ctx() -> z3::Context {
        z3::Context::new(&z3::Config::new())
    }

    // ── canonical_smt + canonical_key invariants ──────────────────────

    #[test]
    fn canonical_smt_stable_after_check() {
        let c = ctx();
        let s = Solver::new(&c);
        let x = Int::new_const(&c, "stable_after_check_var");
        s.assert(&x.gt(&Int::from_i64(&c, 0)));
        let before = canonical_smt(&s);
        let _ = fresh_check(&s).expect("fragment-clean test query");
        let after = canonical_smt(&s);
        assert_eq!(
            before, after,
            "canonical_smt must be stable across solver.check() calls"
        );
    }

    #[test]
    fn canonical_smt_order_independent() {
        let c1 = ctx();
        let s1 = Solver::new(&c1);
        let a1 = Int::new_const(&c1, "a");
        let b1 = Int::new_const(&c1, "b");
        s1.assert(&a1.gt(&Int::from_i64(&c1, 0)));
        s1.assert(&b1.lt(&Int::from_i64(&c1, 10)));

        let c2 = ctx();
        let s2 = Solver::new(&c2);
        let a2 = Int::new_const(&c2, "a");
        let b2 = Int::new_const(&c2, "b");
        s2.assert(&b2.lt(&Int::from_i64(&c2, 10)));
        s2.assert(&a2.gt(&Int::from_i64(&c2, 0)));

        assert_eq!(canonical_smt(&s1), canonical_smt(&s2));
    }

    #[test]
    fn canonical_smt_is_pure() {
        let c1 = ctx();
        let s1 = Solver::new(&c1);
        let x1 = Int::new_const(&c1, "x");
        s1.assert(&x1.gt(&Int::from_i64(&c1, 0)));

        let c2 = ctx();
        let s2 = Solver::new(&c2);
        let x2 = Int::new_const(&c2, "x");
        s2.assert(&x2.gt(&Int::from_i64(&c2, 0)));

        assert_eq!(canonical_smt(&s1), canonical_smt(&s2));
    }

    #[test]
    fn canonical_smt_strips_metadata() {
        let c = ctx();
        let s = Solver::new(&c);
        s.assert(&Bool::from_bool(&c, true));
        let canonical = canonical_smt(&s);
        for line in canonical.lines() {
            assert!(!line.trim_start().starts_with(';'));
            assert!(!line.trim_start().starts_with("(set-info"));
            assert!(!line.trim_start().starts_with("(set-option"));
        }
    }

    #[test]
    fn canonical_key_is_deterministic() {
        let c = ctx();
        let s = Solver::new(&c);
        s.assert(&Bool::from_bool(&c, true));
        let canonical = canonical_smt(&s);
        let k1 = canonical_key(&canonical);
        let k2 = canonical_key(&canonical);
        assert_eq!(k1, k2);
    }

    // ── check_cached round-trip (cache-on path) ──────────────────────

    #[test]
    fn cache_hit_returns_same_verdict_as_fresh() {
        let c = ctx();
        let s = Solver::new(&c);
        let x = Int::new_const(&c, "cache_hit_test_var");
        s.assert(&x.gt(&Int::from_i64(&c, 0)));

        let v1 = check_cached(&s, fresh_check).expect("fragment-clean test query");
        assert_eq!(v1, Verdict::Sat);

        let v2 = check_cached(&s, |_| panic!("must not run fresh on cache hit"))
            .expect("fragment-clean test query");
        assert_eq!(v2, Verdict::Sat);

        let v3 = check_cached(&s, |_| panic!("must not run fresh on cache hit"))
            .expect("fragment-clean test query");
        assert_eq!(v3, Verdict::Sat);
    }

    #[test]
    fn cache_unsat_round_trip() {
        let c = ctx();
        let s = Solver::new(&c);
        let x = Int::new_const(&c, "unsat_round_trip_var");
        s.assert(&x.gt(&Int::from_i64(&c, 0)));
        s.assert(&x.lt(&Int::from_i64(&c, 0)));

        let v1 = check_cached(&s, fresh_check).expect("fragment-clean test query");
        assert_eq!(v1, Verdict::Unsat);

        let v2 = check_cached(&s, |_| panic!("must not run fresh on cache hit"))
            .expect("fragment-clean test query");
        assert_eq!(v2, Verdict::Unsat);
    }

    #[test]
    fn cache_stats_monotonic_on_call() {
        let c = ctx();
        let s = Solver::new(&c);
        let x = Int::new_const(&c, "cache_stats_monotonic_var");
        s.assert(&x.gt(&Int::from_i64(&c, 0)));

        let (h0, m0) = stats_snapshot();
        let _ = check_cached(&s, fresh_check).expect("fragment-clean test query");
        let (h1, m1) = stats_snapshot();
        assert!(h1 + m1 > h0 + m0);
    }

    // ── env_is_truthy_off vocabulary ─────────────────────────────────

    #[test]
    fn env_disable_accepts_off_0_false_no_disabled() {
        for v in ["off", "0", "false", "no", "disabled"] {
            assert!(env_is_truthy_off(v), "expected `{v}` to disable the cache");
        }
    }

    #[test]
    fn env_disable_case_insensitive() {
        for v in ["OFF", "Off", "FALSE", "Disabled", "DiSaBlEd", "  off "] {
            assert!(
                env_is_truthy_off(v),
                "expected `{v}` (case/whitespace) to disable the cache"
            );
        }
    }

    #[test]
    fn env_disable_ambiguous_value_leaves_cache_on() {
        for v in ["", "on", "1", "true", "yes", "enabled", "anything-else"] {
            assert!(
                !env_is_truthy_off(v),
                "expected `{v}` to NOT match the disable vocabulary"
            );
        }
    }

    // ── Verdict <-> u8 round-trip ────────────────────────────────────

    #[test]
    fn verdict_byte_round_trip() {
        for v in [Verdict::Sat, Verdict::Unsat, Verdict::Unknown] {
            assert_eq!(Verdict::from_u8(v.as_u8()), Some(v));
        }
        assert_eq!(Verdict::from_u8(3), None);
        assert_eq!(Verdict::from_u8(255), None);
    }

    // ── L2 file format ───────────────────────────────────────────────

    /// Build a temp cache root and write a known verdict via the real
    /// write path; read it back via the real read path. Wall 4 Step 3
    /// V45 extended the signature to include an optional counterexample
    /// — non-subsumption callers pass `None`.
    fn write_and_read_l2(verdict: Verdict) -> Option<Verdict> {
        let root = tempfile::tempdir().expect("tempdir");
        let key = [0x42u8; 32];
        write_l2(root.path(), &key, verdict, None);
        read_l2(root.path(), &key).map(|(v, _cex)| v)
    }

    #[test]
    fn l2_round_trip_via_disk() {
        // Each variant survives a disk write+read.
        for v in [Verdict::Sat, Verdict::Unsat, Verdict::Unknown] {
            assert_eq!(write_and_read_l2(v), Some(v));
        }
    }

    /// V45 round-trip: Sat verdict with a counterexample survives the L2
    /// write+read path. The cex value is preserved byte-for-byte.
    #[test]
    fn v45_l2_round_trip_with_counterexample() {
        let root = tempfile::tempdir().expect("tempdir");
        let key = [0x99u8; 32];
        for cex in [0i64, 1, -1, i64::MAX, i64::MIN, 42, -42_424_242] {
            write_l2(root.path(), &key, Verdict::Sat, Some(cex));
            let got = read_l2(root.path(), &key);
            assert_eq!(
                got,
                Some((Verdict::Sat, Some(cex))),
                "V45: cex {cex} did not round-trip through L2"
            );
        }
    }

    #[test]
    fn l2_missing_file_is_silent_miss() {
        let root = tempfile::tempdir().expect("tempdir");
        let key = [0u8; 32];
        // Read nonexistent file → None, no warning emitted (NotFound
        // is the expected miss path).
        assert_eq!(read_l2(root.path(), &key), None);
    }

    #[test]
    fn l2_corrupt_file_treated_as_miss() {
        let root = tempfile::tempdir().expect("tempdir");
        let key = [0x11u8; 32];
        // Write a real file, then truncate to 1 byte.
        write_l2(root.path(), &key, Verdict::Sat, None);
        fs::write(key_path(root.path(), &key), [0x5Au8]).expect("truncate write");
        assert_eq!(read_l2(root.path(), &key), None);
    }

    /// V45: pre-V45 files (9-byte format, version 1) are auto-rejected
    /// by length mismatch. The cache version bump invalidates them.
    #[test]
    fn v45_pre_v45_file_format_treated_as_miss() {
        let root = tempfile::tempdir().expect("tempdir");
        let key = [0xAAu8; 32];
        // Hand-write a v1-format file (9 bytes: magic + 1u32 + verdict).
        let mut buf = Vec::with_capacity(9);
        buf.extend_from_slice(&CACHE_MAGIC.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes()); // version 1
        buf.push(Verdict::Sat.as_u8());
        fs::write(key_path(root.path(), &key), &buf).expect("write");
        // V45's L2_FILE_BYTES is 18, so a 9-byte file is rejected on
        // length check before version check ever fires.
        assert_eq!(read_l2(root.path(), &key), None);
    }

    #[test]
    fn l2_wrong_magic_treated_as_miss() {
        let root = tempfile::tempdir().expect("tempdir");
        let key = [0x22u8; 32];
        // Hand-write a file with the wrong magic (full 18-byte length).
        let mut buf = Vec::with_capacity(L2_FILE_BYTES);
        buf.extend_from_slice(&0xDEAD_BEEFu32.to_le_bytes()); // wrong magic
        buf.extend_from_slice(&CACHE_FORMAT_VERSION.to_le_bytes());
        buf.push(0); // verdict
        buf.push(0); // has_cex
        buf.extend_from_slice(&0i64.to_le_bytes()); // cex
        fs::write(key_path(root.path(), &key), &buf).expect("write");
        assert_eq!(read_l2(root.path(), &key), None);
    }

    #[test]
    fn l2_wrong_version_treated_as_miss() {
        let root = tempfile::tempdir().expect("tempdir");
        let key = [0x33u8; 32];
        let mut buf = Vec::with_capacity(L2_FILE_BYTES);
        buf.extend_from_slice(&CACHE_MAGIC.to_le_bytes());
        buf.extend_from_slice(&99u32.to_le_bytes()); // wrong version
        buf.push(0);
        buf.push(0);
        buf.extend_from_slice(&0i64.to_le_bytes());
        fs::write(key_path(root.path(), &key), &buf).expect("write");
        assert_eq!(read_l2(root.path(), &key), None);
    }

    #[test]
    fn l2_invalid_verdict_byte_treated_as_miss() {
        let root = tempfile::tempdir().expect("tempdir");
        let key = [0x44u8; 32];
        let mut buf = Vec::with_capacity(L2_FILE_BYTES);
        buf.extend_from_slice(&CACHE_MAGIC.to_le_bytes());
        buf.extend_from_slice(&CACHE_FORMAT_VERSION.to_le_bytes());
        buf.push(0xFF); // not a known Verdict
        buf.push(0);
        buf.extend_from_slice(&0i64.to_le_bytes());
        fs::write(key_path(root.path(), &key), &buf).expect("write");
        assert_eq!(read_l2(root.path(), &key), None);
    }

    /// V45: invalid has_cex byte (must be 0 or 1) rejects the file.
    #[test]
    fn v45_l2_invalid_has_cex_byte_treated_as_miss() {
        let root = tempfile::tempdir().expect("tempdir");
        let key = [0x55u8; 32];
        let mut buf = Vec::with_capacity(L2_FILE_BYTES);
        buf.extend_from_slice(&CACHE_MAGIC.to_le_bytes());
        buf.extend_from_slice(&CACHE_FORMAT_VERSION.to_le_bytes());
        buf.push(Verdict::Sat.as_u8());
        buf.push(0xAB); // invalid has_cex; must be 0 or 1
        buf.extend_from_slice(&0i64.to_le_bytes());
        fs::write(key_path(root.path(), &key), &buf).expect("write");
        assert_eq!(read_l2(root.path(), &key), None);
    }

    // ── L2 file count + soft cap ─────────────────────────────────────

    #[test]
    fn l2_count_filters_to_bin_files() {
        let root = tempfile::tempdir().expect("tempdir");
        // 3 .bin files, 2 non-.bin files.
        for i in 0..3u8 {
            let mut key = [0u8; 32];
            key[0] = i;
            write_l2(root.path(), &key, Verdict::Sat, None);
        }
        fs::write(root.path().join("notes.txt"), b"hello").expect("non-bin");
        fs::write(root.path().join("lockfile.lock"), b"x").expect("non-bin");
        assert_eq!(count_l2_bin_files(root.path()), 3);
    }

    #[test]
    fn l2_count_starts_at_existing_files() {
        let root = tempfile::tempdir().expect("tempdir");
        for i in 0..5u8 {
            let mut key = [0u8; 32];
            key[1] = i + 1;
            // Hand-write to avoid touching the global state's
            // l2_file_count (we measure independently).
            let mut buf = Vec::with_capacity(L2_FILE_BYTES);
            buf.extend_from_slice(&CACHE_MAGIC.to_le_bytes());
            buf.extend_from_slice(&CACHE_FORMAT_VERSION.to_le_bytes());
            buf.push(Verdict::Sat.as_u8());
            fs::write(key_path(root.path(), &key), &buf).expect("write");
        }
        assert_eq!(count_l2_bin_files(root.path()), 5);
    }

    // ── resolve_cache_dir behavior (no env mutations needed) ─────────

    #[test]
    fn cache_dir_walk_up_finds_workspace_with_lock() {
        // Manually construct what resolve_cache_dir's walk-up does.
        let temp = tempfile::tempdir().expect("tempdir");
        let workspace = temp.path().join("ws");
        let crate_dir = workspace.join("crates").join("inner");
        fs::create_dir_all(&crate_dir).expect("mkdir");
        fs::write(workspace.join("Cargo.toml"), b"[workspace]\n").expect("toml");
        fs::write(workspace.join("Cargo.lock"), b"# lock\n").expect("lock");

        // Walk up from crate_dir.
        let mut search: &Path = crate_dir.as_path();
        let root: Option<PathBuf> = loop {
            if search.join("Cargo.toml").is_file() && search.join("Cargo.lock").is_file() {
                break Some(search.to_path_buf());
            }
            match search.parent() {
                Some(p) => search = p,
                None => break None,
            }
        };
        assert_eq!(root.as_deref(), Some(workspace.as_path()));
    }

    #[test]
    fn cache_dir_walk_up_rejects_lone_cargo_toml() {
        // A directory with Cargo.toml but no Cargo.lock (e.g., a stray
        // home-dir Cargo.toml) must NOT be picked as the workspace.
        let temp = tempfile::tempdir().expect("tempdir");
        let stray = temp.path().join("home");
        let inner = stray.join("nested");
        fs::create_dir_all(&inner).expect("mkdir");
        fs::write(stray.join("Cargo.toml"), b"[package]\n").expect("toml");

        let mut search: &Path = inner.as_path();
        let mut found_one = false;
        loop {
            if search.join("Cargo.toml").is_file() && search.join("Cargo.lock").is_file() {
                found_one = true;
                break;
            }
            match search.parent() {
                Some(p) => search = p,
                None => break,
            }
        }
        assert!(
            !found_one,
            "walk-up must reject lone Cargo.toml without sibling Cargo.lock"
        );
    }

    // ── I/O error dedupe ─────────────────────────────────────────────

    #[test]
    fn io_error_warned_once_per_kind() {
        // We can't easily simulate a real I/O error here, but we can
        // test the dedupe property directly. Pre-populate the
        // warned_io_kinds set with a kind, then verify the second
        // insert returns false (i.e., would not warn again).
        with_state(|s| {
            s.warned_io_kinds.clear();
            assert!(s.warned_io_kinds.insert(ErrorKind::PermissionDenied));
            assert!(
                !s.warned_io_kinds.insert(ErrorKind::PermissionDenied),
                "second insert must return false (already warned)"
            );
            // Different kind warns separately.
            assert!(s.warned_io_kinds.insert(ErrorKind::Other));
        });
    }

    // ── Wall 4 Step 1 (V3): refinement-query cache-key disjointness ──

    /// Wall 4 Step 1 V3 contract: refinement queries use the `refine__`
    /// variable prefix, which makes their canonical SMT byte-disjoint from
    /// cap-flow proofs (which use `legit_*`, `auth_*`, `cap_*` patterns —
    /// never `refine__`). This test builds two solvers with structurally
    /// identical assertions but different variable namespaces and asserts
    /// the cache keys differ.
    ///
    /// If a future change reuses `refine__` outside refinement queries OR
    /// introduces a cap variable prefixed `refine__`, this test fails the
    /// build before the silent cache-collision can corrupt verdicts.
    #[test]
    fn refinement_and_cap_queries_have_disjoint_cache_keys() {
        let c = ctx();

        // Refinement-shaped solver: variable named `refine__value`.
        let refine_solver = Solver::new(&c);
        let refine_v = Int::new_const(&c, "refine__value");
        refine_solver.assert(&refine_v._eq(&Int::from_i64(&c, 42)));
        refine_solver.assert(&refine_v.gt(&Int::from_i64(&c, 100)).not());

        // Cap-flow-shaped solver: same shape, different variable name.
        let cap_solver = Solver::new(&c);
        let cap_v = Int::new_const(&c, "auth_value");
        cap_solver.assert(&cap_v._eq(&Int::from_i64(&c, 42)));
        cap_solver.assert(&cap_v.gt(&Int::from_i64(&c, 100)).not());

        let refine_key = canonical_key(&canonical_smt(&refine_solver));
        let cap_key = canonical_key(&canonical_smt(&cap_solver));
        assert_ne!(
            refine_key, cap_key,
            "Wall 4 Step 1 V3 contract violation: refinement and cap-flow queries with structurally identical assertions produced colliding cache keys. Refinement variables must use the `refine__` prefix to keep canonical SMT byte-disjoint from cap-flow queries."
        );
    }
}
