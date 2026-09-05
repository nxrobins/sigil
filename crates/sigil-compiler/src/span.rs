//! Byte-offset source spans and the `SourceId` file attribution they carry.
//! Owned invariants: `Span` stays `Copy` (the AST stores it by value in
//! thousands of nodes), and `SourceId::SYNTHETIC` marks compiler-generated
//! spans -- never a valid `SourceMap` index. No diagnostics originate here;
//! `join` debug-asserts that both spans share a file (synthetic exempt).

/// Newtype wrapper around a 32-bit source-file identifier.
///
/// Wall 5 Step 1 follow-up: every [`Span`] carries a `SourceId` so the
/// renderer can look up the right source file when multiple files
/// participate in a compilation (the multi-file driver merges
/// `Program.modules` from N files, and individual spans must still
/// remember which file's text they index into).
///
/// `SourceId` is a `u32` newtype so [`Span`] stays `Copy` — the AST
/// stores `Span` by value in thousands of nodes, and losing `Copy`
/// would force a Clone-cascade through every match arm that takes a
/// span by value. The trade-off is that callers must consult a
/// [`SourceMap`] to resolve the id back to a [`crate::source::SourceFile`].
///
/// [`SourceId::SYNTHETIC`] is the sentinel for compiler-generated spans
/// (test fixtures, synthesized AST nodes, default-constructed spans).
/// The renderer treats it as "no file in the SourceMap" and emits a
/// `<compiler-generated>` label instead of source-line text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceId(pub u32);

impl SourceId {
    /// Sentinel for compiler-generated spans with no associated source
    /// file. Reserved at the top of the `u32` space so legitimate
    /// source ids start at 0 and grow upward (a `SourceMap` of length
    /// `N` covers ids `0..N`; `u32::MAX` is unreachable in practice).
    pub const SYNTHETIC: SourceId = SourceId(u32::MAX);

    /// True iff this is the [`Self::SYNTHETIC`] sentinel — i.e., the
    /// span has no associated source file. Renderers branch on this
    /// to emit a fallback label.
    pub const fn is_synthetic(self) -> bool {
        self.0 == u32::MAX
    }
}

impl Default for SourceId {
    /// The default `SourceId` is [`Self::SYNTHETIC`]. Combined with
    /// `Span::default()`'s `(0, 0)` byte range, the default span is
    /// "no location, no file" — the right answer for synthesized AST
    /// nodes and test fixtures that don't correspond to user-written
    /// source.
    fn default() -> Self {
        Self::SYNTHETIC
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    /// Wall 5 Step 1 follow-up: identifier of the source file this
    /// span indexes into. [`SourceId::SYNTHETIC`] for spans that have
    /// no associated source (compiler-generated nodes, test fixtures).
    /// The renderer looks this up in a [`crate::source::SourceMap`] to
    /// produce file-precise diagnostics in multi-file mode.
    pub source: SourceId,
}

impl Span {
    /// Construct a span from byte offsets. Source defaults to
    /// [`SourceId::SYNTHETIC`] — use [`Self::with_source`] when a real
    /// file context is available (the lexer + parser do this for every
    /// token they emit).
    pub const fn new(start: usize, end: usize) -> Self {
        Self {
            start,
            end,
            source: SourceId::SYNTHETIC,
        }
    }

    /// Construct a span with an explicit source-file identifier. Used
    /// by the lexer and parser to attribute every token's span to its
    /// originating file in multi-file compilations.
    pub const fn with_source(start: usize, end: usize, source: SourceId) -> Self {
        Self { start, end, source }
    }

    /// Combine two spans into one covering both. The resulting span's
    /// source is taken from `self` (the left operand).
    ///
    /// In debug builds, `join` asserts that both spans share a source
    /// — joining cross-file spans is a logic bug today because every
    /// existing call site joins spans within a single parse stream.
    /// Synthetic spans are excluded from the assertion so test
    /// fixtures and synthesized nodes can still be joined freely.
    pub fn join(self, other: Span) -> Self {
        debug_assert!(
            self.source == other.source
                || self.source.is_synthetic()
                || other.source.is_synthetic(),
            "Span::join across distinct source files: self={:?}, other={:?}",
            self.source,
            other.source,
        );
        // Pick the non-synthetic source if exactly one side has one;
        // otherwise default to self's. Matches the existing
        // "lhs-source-wins" convention but upgrades synthesized spans
        // when joined against real ones.
        let source = if self.source.is_synthetic() {
            other.source
        } else {
            self.source
        };
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
            source,
        }
    }

    pub const fn len(self) -> usize {
        self.end.saturating_sub(self.start)
    }

    pub const fn is_empty(self) -> bool {
        self.start >= self.end
    }
}
