//! Extractor interface. Each extractor is a pure structure pass that reads
//! committed inputs and proposes `RawRecord`s; the gate (`crate::certify`)
//! certifies them into emitted `Record`s or counted drops.

use std::path::PathBuf;
use std::rc::Rc;

use crate::schema::Record;

pub mod error_corpus;
pub mod inline_program;
pub mod pr_history;
pub mod source_idiom;
pub mod test_fixture;

/// Shared inputs every extractor resolves against.
pub struct ExtractCtx {
    pub workspace_root: PathBuf,
    pub git_sha: String,
    /// When true, extractors that shell out to the network (`pr_history` →
    /// `gh`) skip — keeps deterministic tests fast and network-free.
    pub offline: bool,
}

/// How the gate must validate a candidate.
pub enum ValidationIntent {
    /// Must compile clean through the real compiler (the record's own `output`
    /// is the compilable module — used by self-contained fixtures).
    Positive,
    /// Must reproduce this diagnostic code.
    Negative { code: String },
    /// Validated at the level of a whole compilation UNIT shared by many records
    /// (a stdlib file, or the inlined selfhost trio): the unit must compile
    /// clean, and the gate memoizes the verdict by `unit_key` so the unit is
    /// compiled once. Used for function-level source idioms, which never compile
    /// in isolation (AG-C1).
    PositiveUnit {
        unit_key: String,
        unit_src: Rc<String>,
    },
    /// A standalone fixture whose disposition is decided by the compiler. If
    /// `expect_error`, it must compile to an error and the record becomes a
    /// `rejection` carrying the FIRST registry code the compiler emits (ET-C2 —
    /// the header is never trusted); a fixture that compiles clean is dropped
    /// (drift / solver-skipped). If `!expect_error`, it must compile clean and
    /// becomes a positive; otherwise it is dropped.
    Fixture { expect_error: bool },
    /// A program whose disposition is decided ENTIRELY by the compiler, with no
    /// expect-error header to honour (inline test programs mined from the Rust
    /// harnesses). The extractor has already proven it parses clean as SIGIL, so
    /// the gate keeps BOTH dispositions: compiles clean → a positive
    /// (`Implementation`); reproduces a registry diagnostic → a `Rejection`
    /// carrying the first such code; a no-registry-code / timeout outcome → a
    /// counted drop (never a guessed label).
    Classify,
    /// A reference record (e.g. an error-code doc) with no compilable body;
    /// emitted `Unvalidated`, counted in its own manifest bucket.
    Reference { reason: String },
}

/// A proposed record plus everything the gate needs to certify it.
pub struct RawRecord {
    pub record: Record,
    pub intent: ValidationIntent,
    /// Module name passed to the compiler when validating (`Positive`/`Negative`).
    pub name_for_compile: String,
    /// The committed source blob every non-empty `intent`/`reasoning` field must
    /// be a verbatim substring of (ET-C3 grounding).
    pub provenance: String,
}

pub trait Extractor {
    fn name(&self) -> &'static str;
    fn extract(&self, ctx: &ExtractCtx) -> anyhow::Result<Vec<RawRecord>>;
}
