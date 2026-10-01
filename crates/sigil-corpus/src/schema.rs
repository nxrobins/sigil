//! The JSONL training record (`docs/specs/training-corpus.md` §2) plus the
//! §9 dumb physical bounds as named `const`s. Serde field order is the
//! serialization order, and every collection is an ordered `Vec`/`BTreeMap`,
//! so a record serializes byte-identically across runs (ET-C5).

use serde::{Deserialize, Serialize};

/// Bumped whenever the record shape changes; pinned into every record.
pub const SCHEMA_VERSION: &str = "1";

// ── §9 Constraints & Fallbacks: the dumb physical bounds ──────────────────────
/// The EXTRACTOR's per-compile drop bound (ET-C1): a compile that has not
/// answered within this many milliseconds drops its record(s), counted as
/// `VALIDATE_TIMEOUT` (ET-C6) — never emitted unvalidated. Its job is to bound a
/// HUNG compile, which is minutes, not to detect a slow one; the slow-compile
/// detector is `SELFHOST_TRIO_CANARY_MS`, measured in isolation.
///
/// Why thirty seconds and not the canary's five: the three selfhost files share
/// ONE memoized compile (`selfhost-trio`, the slowest unit by an order of
/// magnitude — 2.4 s alone and 3.0 s under three concurrent full builds on a
/// developer machine, 2026-09-30, where the next-slowest unit is 315 ms), so a
/// single timeout drops EVERY selfhost idiom and the corpus stops being
/// deterministic (ET-C5: 3962 vs 4140 records on PR #765, where the same trio
/// passed the five-second bound twice in the isolated `checks` step and failed
/// it only inside the parallel workspace `test` lane). Load contention, not a
/// scaling regression — and a drop bound that flips on contention is a
/// nondeterminism generator. Six times the failed bound leaves the hung-compile
/// case (minutes) still caught; every drop stays counted.
///
/// Note the bound is on the WAIT: the abandoned worker thread is not cancelled
/// and runs to completion in the background (`validate::compile_within_budget`).
pub const VALIDATE_BUDGET_MS: u64 = 30_000;
/// The linked Lean verifier's SCALING-CANARY bound: the selfhost trio must
/// compile within this many milliseconds when measured IN ISOLATION. This fixed
/// five-second bound caught two accidental O(n²) verifier scans, so it stays
/// tight and deliberately separate from `VALIDATE_BUDGET_MS`: widening the
/// extractor's drop bound cannot disguise a verifier regression, and the canary
/// cannot be loosened by the lane it happens to run in. Asserted by
/// `validate::tests::selfhost_trio_completes_within_validation_budget` only when
/// `SCALING_CANARY_ENV` is `1` — the `Formal verifier scaling canary` step in
/// `ci.yml` sets it and runs that test alone; the parallel workspace lane, which
/// does not set it, still asserts the extractor bound.
pub const SELFHOST_TRIO_CANARY_MS: u64 = 5_000;
/// Arms the tight `SELFHOST_TRIO_CANARY_MS` assertion when set to exactly `1`.
/// Absent = the extractor bound only (a contended lane must not fail on timing
/// it cannot control); any OTHER value panics (fail closed — a typo in the CI
/// `env:` block must not silently disarm the canary).
pub const SCALING_CANARY_ENV: &str = "SIGIL_CORPUS_SCALING_CANARY";
/// Stack reserved for the compiler worker that enforces the validation budget.
pub const VALIDATE_STACK_BYTES: usize = 32 * 1024 * 1024;
/// Max bytes of any `intent`/`reasoning` field (ET-C3).
pub const MAX_PROSE_BYTES: usize = 2_048;
/// Max bytes of a record's `output` — bigger than the biggest single `.sigil`
/// function, smaller than a whole pathological file (ET-C7).
pub const MAX_OUTPUT_BYTES: usize = 131_072;
/// Runaway backstop, ~50× the expected volume (ET-C8).
pub const MAX_RECORDS: usize = 100_000;
/// Max PRs enumerated by the pr_history extractor (ET-C9; used from PR-4).
pub const MAX_PRS: usize = 1_000;
/// External-tool budgets (ET-C9; used from PR-4).
pub const GH_TIMEOUT_MS: u64 = 30_000;
pub const GIT_TIMEOUT_MS: u64 = 10_000;
/// Max lines the backward doc-comment scan reads above a definition (ET-C10;
/// used from PR-1).
pub const MAX_DOC_SCAN_LINES: usize = 40;

/// One training example.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Record {
    /// Stable, provenance-derived id (deterministic, never insertion-order).
    pub id: String,
    pub kind: Kind,
    pub intent: String,
    pub context: Context,
    pub output: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reasoning: Option<String>,
    pub tags: Vec<String>,
    pub difficulty: Difficulty,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pr: Option<u64>,
    pub negative_examples: Vec<NegativeExample>,
    // ── provenance / audit ──
    pub source_path: String,
    pub git_sha: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<ByteSpan>,
    pub validated: Validated,
    pub extractor: String,
    pub schema_version: String,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum Kind {
    Implementation,
    Design,
    Rejection,
    Refactor,
    Idiom,
    Fix,
    Review,
}

impl Kind {
    /// All kinds, in a fixed order — drives the per-kind output files. TOTAL:
    /// adding a `Kind` variant without listing it here is caught by the
    /// `kind_all_is_total` test (ET-C9 drift-lock).
    pub const ALL: [Kind; 7] = [
        Kind::Implementation,
        Kind::Design,
        Kind::Rejection,
        Kind::Refactor,
        Kind::Idiom,
        Kind::Fix,
        Kind::Review,
    ];

    pub fn as_str(self) -> &'static str {
        match self {
            Kind::Implementation => "implementation",
            Kind::Design => "design",
            Kind::Rejection => "rejection",
            Kind::Refactor => "refactor",
            Kind::Idiom => "idiom",
            Kind::Fix => "fix",
            Kind::Review => "review",
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Difficulty {
    Easy,
    Medium,
    Hard,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct Context {
    pub imports: Vec<String>,
    pub types_in_scope: Vec<String>,
    pub constraints: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct NegativeExample {
    pub code: String,
    pub error: String,
    pub explanation: String,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub struct ByteSpan {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Validated {
    pub ok: bool,
    pub how: ValidationKind,
}

/// How a record was (or was not) validated. `ParsedTypechecked` and
/// `ReproducedCode` records carry a compiler verdict and MUST have `ok == true`
/// to be emitted (ET-C1); `Unvalidated` records (reference docs) are emitted
/// with `ok == false` and counted in a separate manifest bucket.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "how", rename_all = "snake_case")]
pub enum ValidationKind {
    ParsedTypechecked,
    ReproducedCode { code: String },
    Unvalidated { reason: String },
}
