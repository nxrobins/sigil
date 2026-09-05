//! Source-file text storage and the `SourceMap` resolving each `SourceId` to
//! its file for multi-file diagnostics. Owns the UTF-8 ingest boundary:
//! `SourceFile::from_bytes` validates ONCE, rejecting invalid bytes with the
//! typed `Utf8IngestError` (reserved code L010, pinned in
//! `tests/diagnostic_messages.rs`) so corrupted text never reaches the lexer.
//! Synthetic-id lookups return `None`; offset helpers clamp, never panic.

use crate::span::{SourceId, Span};

/// Wall 5 Step 1 follow-up: a collection of source files indexed by
/// [`SourceId`]. The renderer consults the SourceMap to resolve every
/// [`Span`]'s `source` field back to a [`SourceFile`] so multi-file
/// diagnostics render against the correct file's text.
///
/// A SourceMap of length `N` covers ids `0..N`. [`SourceId::SYNTHETIC`]
/// (`u32::MAX`) is reserved for compiler-generated spans and is NEVER
/// a valid index — lookups for it return `None` and the renderer emits
/// a `<compiler-generated>` fallback.
///
/// `SourceMap` is intentionally a thin wrapper around `Vec<SourceFile>`
/// so callers can construct one cheaply from any iterator of files.
#[derive(Debug, Clone, Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    /// Construct an empty SourceMap.
    pub fn new() -> Self {
        Self { files: Vec::new() }
    }

    /// Construct a SourceMap from a vector of files. Each file's
    /// position in the vector becomes its [`SourceId`].
    pub fn from_files(files: Vec<SourceFile>) -> Self {
        debug_assert!(
            files.len() < u32::MAX as usize,
            "SourceMap cannot hold more than u32::MAX - 1 files (the top index is reserved for SourceId::SYNTHETIC)"
        );
        Self { files }
    }

    /// Append a file and return its assigned [`SourceId`]. Used by the
    /// multi-file driver as it walks the input list.
    pub fn push(&mut self, file: SourceFile) -> SourceId {
        let id = SourceId(self.files.len() as u32);
        self.files.push(file);
        id
    }

    /// Resolve a [`SourceId`] to a borrowed [`SourceFile`]. Returns
    /// `None` for [`SourceId::SYNTHETIC`] or for any id outside this
    /// map's range.
    pub fn get(&self, id: SourceId) -> Option<&SourceFile> {
        if id.is_synthetic() {
            return None;
        }
        self.files.get(id.0 as usize)
    }

    /// Number of files in the map.
    pub fn len(&self) -> usize {
        self.files.len()
    }

    /// True iff the map is empty.
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    /// Iterate over `(SourceId, &SourceFile)` pairs in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = (SourceId, &SourceFile)> + '_ {
        self.files
            .iter()
            .enumerate()
            .map(|(i, f)| (SourceId(i as u32), f))
    }

    /// Iterate over the underlying files only.
    pub fn files(&self) -> &[SourceFile] {
        &self.files
    }
}

impl From<SourceFile> for SourceMap {
    /// Construct a single-file SourceMap. Convenience for legacy
    /// single-file callers.
    fn from(file: SourceFile) -> Self {
        Self::from_files(vec![file])
    }
}

impl From<Vec<SourceFile>> for SourceMap {
    fn from(files: Vec<SourceFile>) -> Self {
        Self::from_files(files)
    }
}

/// PR S1 / N30-S1: error returned by [`SourceFile::from_bytes`] when the
/// supplied bytes are not valid UTF-8. SIGIL `str` is a refinement-typed
/// view over UTF-8-validated bytes; the type-system promise is that
/// any `str` value satisfies `utf8_valid(self)`. To preserve that
/// invariant the ingest boundary REJECTS invalid UTF-8 immediately
/// rather than carrying corrupted bytes into the lexer.
///
/// `byte_offset` is the offset of the first invalid byte (the number
/// of bytes that successfully decoded as UTF-8 before the failure).
/// Callers translate this error into a file-qualified L010 diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Utf8IngestError {
    pub source_name: String,
    pub byte_offset: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceFile {
    name: String,
    text: String,
}

impl SourceFile {
    pub fn new(name: impl Into<String>, text: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            text: text.into(),
        }
    }

    /// PR S1 / N30-S1: construct a [`SourceFile`] from raw bytes,
    /// validating UTF-8 at the ingress boundary. This is the canonical
    /// entry point for the multi-file driver and the CLI when reading
    /// a source file from disk — `fs::read(path)` produces `Vec<u8>`
    /// which feeds directly into this constructor.
    ///
    /// SIGIL `str` is a refinement-typed view over UTF-8-validated bytes;
    /// the validation runs ONCE at file ingest. Invalid UTF-8 returns
    /// [`Utf8IngestError`] carrying the byte offset of the first invalid
    /// sequence. Callers translate the error into a file-qualified L010
    /// diagnostic.
    ///
    /// Per N30-S1, multi-file ingest validates EACH input file before
    /// any parse begins; one bad file aborts the entire compile.
    pub fn from_bytes(name: impl Into<String>, bytes: Vec<u8>) -> Result<Self, Utf8IngestError> {
        let name = name.into();
        match String::from_utf8(bytes) {
            Ok(text) => Ok(Self { name, text }),
            Err(e) => Err(Utf8IngestError {
                source_name: name,
                byte_offset: e.utf8_error().valid_up_to(),
            }),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn line_col(&self, offset: usize) -> (usize, usize) {
        let clamped = self.char_boundary_at_or_before(offset);
        let mut line = 1;
        let mut col = 1;

        for ch in self.text[..clamped].chars() {
            if ch == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }

        (line, col)
    }

    pub fn line_text(&self, line: usize) -> &str {
        self.text.lines().nth(line.saturating_sub(1)).unwrap_or("")
    }

    pub fn span_text(&self, span: Span) -> &str {
        let start = self.char_boundary_at_or_before(span.start);
        let end = self.char_boundary_at_or_before(span.end).max(start);
        &self.text[start..end]
    }

    fn char_boundary_at_or_before(&self, offset: usize) -> usize {
        let mut clamped = offset.min(self.text.len());
        while !self.text.is_char_boundary(clamped) {
            clamped -= 1;
        }
        clamped
    }
}
