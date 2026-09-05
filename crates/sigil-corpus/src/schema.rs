//! The JSONL training record (`docs/specs/training-corpus.md` §2) plus the
//! §9 dumb physical bounds as named `const`s. Serde field order is the
//! serialization order, and every collection is an ordered `Vec`/`BTreeMap`,
//! so a record serializes byte-identically across runs (ET-C5).

use serde::{Deserialize, Serialize};

/// Bumped whenever the record shape changes; pinned into every record.
pub const SCHEMA_VERSION: &str = "1";

// ── §9 Constraints & Fallbacks: the dumb physical bounds ──────────────────────
/// Per-record compile budget; a slower compile drops the record (ET-C1).
pub const VALIDATE_BUDGET_MS: u64 = 5_000;
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
