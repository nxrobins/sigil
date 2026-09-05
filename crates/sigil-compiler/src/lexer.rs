//! The SIGIL lexer -- the single-pass byte scanner (`lex_with_id`) turning a
//! UTF-8-validated `SourceFile` into the parser's token stream, with every
//! span funneled through one helper so `SourceId` attribution is never
//! silently dropped.
//!
//! This file is the differential ORACLE for the self-hosted lexer:
//! `selfhost/lexer.sigil` must match it token-for-token, value-for-value, and
//! diagnostic-for-diagnostic (`docs/specs/lexer-in-sigil.md`, proven by
//! `crates/sigil-runtime/tests/lexer_differential.rs`); a token or diagnostic
//! change here breaks that differential until the selfhost side moves in
//! lock-step. Two more owned contracts: the keyword arms of `lex_identifier`
//! and their reverse map `TokenKind::keyword_text` (the basis of the parser's
//! P026 reserved-keyword recovery) are pinned together by the in-file
//! `keyword_text_round_trips` test, and `f"..."` lexes to a token SEQUENCE
//! whose chunks and holes strictly alternate (ET-E3) -- the exact shape
//! `parse_fstring_expr` assumes.
//!
//! Failure discipline: every fault is a typed diagnostic -- L001 (integer or
//! hex literal malformed or exceeding u256), L002 (bad float), L003
//! (unterminated string, f-string, or hole), L004 (unexpected character) --
//! and lexing always continues to EOF, returning the full
//! `(tokens, diagnostics)` pair. The few expects narrate by-construction
//! UTF-8/ASCII invariants.

use crate::{
    diagnostics::{Diagnostic, codes},
    source::SourceFile,
    span::{SourceId, Span},
};

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    Actor,
    Ask,
    Cap,
    Const,
    Distinct,
    Else,
    Entry,
    Effect,
    Enum,
    Extern,
    Fn,
    Handle,
    For,
    Grant,
    Record,
    Region,
    Ring,
    If,
    Impl,
    In,
    Init,
    Let,
    Match,
    Break,
    Continue,
    Module,
    Mut,
    On,
    Pub,
    Return,
    Send,
    Spawn,
    State,
    Supervision,
    Trait,
    Type,
    Use,
    While,
    Declassify,
    DeclassifyCt,
    With,
    BoolLit(bool),
    IntLit(i64),
    /// A wide integer literal `> i64::MAX` (u256 PR-U2), as 4 little-endian u64
    /// limbs. Emitted when `parse::<i64>()` / `from_str_radix` overflows but the
    /// value still fits 256 bits; `>= 2^256` is L001.
    IntLit256([u64; 4]),
    FloatLit(f64),
    StrLit(String),
    Ident(String),
    Bang,
    Plus,
    PlusEq,
    Minus,
    MinusEq,
    Star,
    StarEq,
    Slash,
    SlashEq,
    Percent,
    PercentEq,
    Eq,
    EqEq,
    BangEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    LtLt,
    LtLtEq,
    GtGt,
    GtGtEq,
    Ampersand,
    AmpersandEq,
    AndAnd,
    Arrow,
    FatArrow,
    Question,
    Dot,
    DotDot,
    DotDotEq,
    Comma,
    Colon,
    Semicolon,
    ColonColon,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Pipe,
    PipeEq,
    OrOr,
    Hash,
    At,
    // PR-E3: string interpolation `f"…{e}…"`. A single `f"…"` lexeme emits a TOKEN
    // SEQUENCE: `FStrBegin` (the `f"`), then alternating `FStrChunk(decoded literal
    // run)` and a hole `FStrHoleStart` (`{`) … normal expression tokens …
    // `FStrHoleEnd` (`}`), ending with `FStrEnd` (the closing `"`). A literal run is
    // ALWAYS emitted (possibly empty) so chunks/holes strictly alternate (ET-E3).
    FStrBegin,
    FStrChunk(String),
    FStrHoleStart,
    FStrHoleEnd,
    FStrEnd,
    Eof,
}

impl TokenKind {
    /// Reverse of the keyword table in [`Lexer::lex_identifier`]: for a
    /// reserved-keyword token this returns the exact source word it was
    /// lexed from; for every non-keyword token (identifiers, literals,
    /// punctuation, EOF) it returns `None`.
    ///
    /// The parser uses this to recognise a reserved keyword sitting where a
    /// name is required (`fn handle(...)`, a parameter named `spawn`, a
    /// `let on = …`) and emit a precise `P026` diagnostic with faithful
    /// recovery, instead of resynchronizing into a degenerate, truncated
    /// parse that silently type-checks clean. Keep this in lock-step with
    /// the keyword arms of [`Lexer::lex_identifier`]; the
    /// `keyword_text_round_trips` test pins them together.
    pub fn keyword_text(&self) -> Option<&'static str> {
        Some(match self {
            TokenKind::Actor => "actor",
            TokenKind::Ask => "ask",
            TokenKind::Cap => "cap",
            TokenKind::Const => "const",
            TokenKind::Distinct => "distinct",
            TokenKind::Else => "else",
            TokenKind::Entry => "entry",
            TokenKind::Effect => "effect",
            TokenKind::Enum => "enum",
            TokenKind::Extern => "extern",
            TokenKind::Fn => "fn",
            TokenKind::Handle => "handle",
            TokenKind::For => "for",
            TokenKind::Grant => "grant",
            TokenKind::Record => "record",
            TokenKind::Region => "region",
            TokenKind::Ring => "ring",
            TokenKind::If => "if",
            TokenKind::Impl => "impl",
            TokenKind::In => "in",
            TokenKind::Init => "init",
            TokenKind::Let => "let",
            TokenKind::Match => "match",
            TokenKind::Break => "break",
            TokenKind::Continue => "continue",
            TokenKind::Module => "module",
            TokenKind::Mut => "mut",
            TokenKind::On => "on",
            TokenKind::Pub => "pub",
            TokenKind::Return => "return",
            TokenKind::Send => "send",
            TokenKind::Spawn => "spawn",
            TokenKind::State => "state",
            TokenKind::Supervision => "supervision",
            TokenKind::Trait => "trait",
            TokenKind::Type => "type",
            TokenKind::Use => "use",
            TokenKind::While => "while",
            TokenKind::Declassify => "declassify",
            TokenKind::DeclassifyCt => "declassify_ct",
            TokenKind::With => "with",
            _ => return None,
        })
    }
}

/// Legacy single-file entry point. Spans produced via this path
/// attribute to [`SourceId::SYNTHETIC`] (no SourceMap context). Used
/// by tests and callers that don't have a SourceMap yet. Production
/// callers should use [`lex_with_id`] so spans carry real attribution.
pub fn lex(source: &SourceFile) -> (Vec<Token>, Vec<Diagnostic>) {
    Lexer::new(source, SourceId::SYNTHETIC).lex()
}

/// Wall 5 Step 1 follow-up: lex with an explicit [`SourceId`]. Every
/// token's `span.source` field will carry this id so multi-file
/// diagnostics resolve to the right file via [`crate::source::SourceMap`].
pub fn lex_with_id(source: &SourceFile, source_id: SourceId) -> (Vec<Token>, Vec<Diagnostic>) {
    Lexer::new(source, source_id).lex()
}

struct Lexer<'a> {
    source: &'a SourceFile,
    source_id: SourceId,
    bytes: &'a [u8],
    cursor: usize,
    tokens: Vec<Token>,
    diagnostics: Vec<Diagnostic>,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a SourceFile, source_id: SourceId) -> Self {
        Self {
            source,
            source_id,
            bytes: source.text().as_bytes(),
            cursor: 0,
            tokens: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    /// Construct a span attributing to this lexer's source file. The
    /// single helper that every span-producing site in the lexer
    /// funnels through, so the source attribution can never be
    /// accidentally dropped.
    #[inline]
    fn span(&self, start: usize, end: usize) -> Span {
        Span::with_source(start, end, self.source_id)
    }

    fn lex(mut self) -> (Vec<Token>, Vec<Diagnostic>) {
        while self.peek().is_some() {
            self.lex_one_token();
        }
        let eof_span = self.span(self.cursor, self.cursor);
        self.push(TokenKind::Eof, eof_span);
        (self.tokens, self.diagnostics)
    }

    /// Lex exactly ONE token (or skip one whitespace/comment run) at the cursor.
    /// Extracted from `lex` so `lex_fstring` can reuse it for interpolation-hole
    /// contents (it drives this until the hole's closing `}`).
    fn lex_one_token(&mut self) {
        let byte = match self.peek() {
            Some(b) => b,
            None => return,
        };
        {
            match byte {
                b' ' | b'\r' | b'\n' | b'\t' => {
                    self.cursor += 1;
                }
                b'/' if self.peek_next() == Some(b'/') => self.skip_line_comment(),
                b'0'..=b'9' => self.lex_int(),
                b'"' => self.lex_string(),
                // PR-E3: `f"…"` is an interpolated string (the `f` must be
                // IMMEDIATELY before `"`; `f "x"` stays ident+string). Must precede
                // the identifier arm, which also matches `b'f'`.
                b'f' if self.peek_next() == Some(b'"') => self.lex_fstring(),
                b'a'..=b'z' | b'A'..=b'Z' | b'_' => self.lex_identifier(),
                b'(' => self.single(TokenKind::LParen),
                b')' => self.single(TokenKind::RParen),
                b'{' => self.single(TokenKind::LBrace),
                b'}' => self.single(TokenKind::RBrace),
                b'[' => self.single(TokenKind::LBracket),
                b']' => self.single(TokenKind::RBracket),
                b';' => self.single(TokenKind::Semicolon),
                b',' => self.single(TokenKind::Comma),
                b'.' => {
                    if self.peek_next() == Some(b'.')
                        && self.bytes.get(self.cursor + 2) == Some(&b'=')
                    {
                        let start = self.cursor;
                        self.cursor += 3;
                        self.push(TokenKind::DotDotEq, self.span(start, self.cursor));
                    } else if self.peek_next() == Some(b'.') {
                        // PR AF: `..` (DotDot) range operator for slice syntax
                        // `&arr[lo..hi]`. N9-AF: no existing fixture uses
                        // bare `..` in code today (only inside comments,
                        // which the lexer strips), so introducing this
                        // token is non-breaking.
                        let start = self.cursor;
                        self.cursor += 2;
                        self.push(TokenKind::DotDot, self.span(start, self.cursor));
                    } else {
                        self.single(TokenKind::Dot);
                    }
                }
                b'?' => self.single(TokenKind::Question),
                b'+' => self.double_or_single(b'=', TokenKind::PlusEq, TokenKind::Plus),
                b'*' => self.double_or_single(b'=', TokenKind::StarEq, TokenKind::Star),
                b'/' => self.double_or_single(b'=', TokenKind::SlashEq, TokenKind::Slash),
                b'%' => self.double_or_single(b'=', TokenKind::PercentEq, TokenKind::Percent),
                b'|' if self.peek_next() == Some(b'|') => self.double(TokenKind::OrOr),
                b'|' => self.double_or_single(b'=', TokenKind::PipeEq, TokenKind::Pipe),
                b'&' if self.peek_next() == Some(b'&') => self.double(TokenKind::AndAnd),
                b'&' => self.double_or_single(b'=', TokenKind::AmpersandEq, TokenKind::Ampersand),
                b'!' if self.cursor + 1 >= self.source.text().len()
                    || self.source.text().as_bytes()[self.cursor + 1] != b'=' =>
                {
                    self.single(TokenKind::Bang)
                }
                b'#' => self.single(TokenKind::Hash),
                b'@' => self.single(TokenKind::At),
                b':' => self.double_or_single(b':', TokenKind::ColonColon, TokenKind::Colon),
                b'-' => {
                    if self.peek_next() == Some(b'>') {
                        self.double(TokenKind::Arrow);
                    } else if self.peek_next() == Some(b'=') {
                        self.double(TokenKind::MinusEq);
                    } else {
                        self.single(TokenKind::Minus);
                    }
                }
                b'=' => {
                    if self.peek_next() == Some(b'=') {
                        self.double(TokenKind::EqEq);
                    } else if self.peek_next() == Some(b'>') {
                        self.double(TokenKind::FatArrow);
                    } else {
                        self.single(TokenKind::Eq);
                    }
                }
                b'!' => {
                    if self.peek_next() == Some(b'=') {
                        self.double(TokenKind::BangEq);
                    } else {
                        self.unexpected_char();
                    }
                }
                b'<' => {
                    if self.peek_next() == Some(b'=') {
                        self.double(TokenKind::LtEq);
                    } else if self.peek_next() == Some(b'<') {
                        if self.bytes.get(self.cursor + 2) == Some(&b'=') {
                            let start = self.cursor;
                            self.cursor += 3;
                            self.push(TokenKind::LtLtEq, self.span(start, self.cursor));
                        } else {
                            self.double(TokenKind::LtLt);
                        }
                    } else {
                        self.single(TokenKind::Lt);
                    }
                }
                b'>' => {
                    if self.peek_next() == Some(b'=') {
                        self.double(TokenKind::GtEq);
                    } else if self.peek_next() == Some(b'>') {
                        if self.bytes.get(self.cursor + 2) == Some(&b'=') {
                            let start = self.cursor;
                            self.cursor += 3;
                            self.push(TokenKind::GtGtEq, self.span(start, self.cursor));
                        } else {
                            self.double(TokenKind::GtGt);
                        }
                    } else {
                        self.single(TokenKind::Gt);
                    }
                }
                _ => self.unexpected_char(),
            }
        }
    }

    fn skip_line_comment(&mut self) {
        self.cursor += 2;
        while let Some(byte) = self.peek() {
            self.cursor += 1;
            if byte == b'\n' {
                break;
            }
        }
    }

    fn lex_int(&mut self) {
        let start = self.cursor;
        let first = self.bytes.get(start).copied();
        self.cursor += 1;

        // Hex literal: `0x...` or `0X...` followed by at least one hex digit.
        // Lands as a plain `IntLit` token — the AST and downstream layers
        // never see the textual radix.
        if first == Some(b'0') && matches!(self.peek(), Some(b'x') | Some(b'X')) {
            self.cursor += 1; // consume 'x' / 'X'
            let hex_start = self.cursor;
            while matches!(
                self.peek(),
                Some(b'0'..=b'9') | Some(b'a'..=b'f') | Some(b'A'..=b'F')
            ) {
                self.cursor += 1;
            }
            let span = self.span(start, self.cursor);
            if self.cursor == hex_start {
                self.diagnostics.push(Diagnostic::error(
                    codes::L001,
                    "hex literal must have at least one hex digit after `0x`",
                    Some(span),
                ));
                return;
            }
            let hex_text = self.source.span_text(self.span(hex_start, self.cursor));
            match i64::from_str_radix(hex_text, 16) {
                Ok(value) => self.push(TokenKind::IntLit(value), span),
                // u256 PR-U2-b: a hex literal `> i64::MAX` (addresses, hashes)
                // becomes a wide IntLit256 when it fits 256 bits; `>= 2^256` is L001.
                Err(_) => match parse_u256_hex(hex_text) {
                    Some(limbs) => self.push(TokenKind::IntLit256(limbs), span),
                    None => self.diagnostics.push(Diagnostic::error(
                        codes::L001,
                        "hex literal out of range (exceeds u256 / 2^256)",
                        Some(span),
                    )),
                },
            }
            return;
        }

        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.cursor += 1;
        }

        // Check for float literal (contains '.')
        if matches!(self.peek(), Some(b'.'))
            && matches!(
                self.source.text().as_bytes().get(self.cursor + 1),
                Some(b'0'..=b'9')
            )
        {
            self.cursor += 1; // consume '.'
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.cursor += 1;
            }
            let span = self.span(start, self.cursor);
            let text = self.source.span_text(span);
            match text.parse::<f64>() {
                Ok(value) => self.push(TokenKind::FloatLit(value), span),
                Err(_) => self.diagnostics.push(Diagnostic::error(
                    codes::L002,
                    "invalid float literal",
                    Some(span),
                )),
            }
            return;
        }

        let span = self.span(start, self.cursor);
        let text = self.source.span_text(span);
        match text.parse::<i64>() {
            Ok(value) => self.push(TokenKind::IntLit(value), span),
            // u256 PR-U2: a decimal literal `> i64::MAX` becomes a wide IntLit256
            // when it still fits 256 bits; `>= 2^256` is rejected (L001).
            Err(_) => match parse_u256_decimal(text) {
                Some(limbs) => self.push(TokenKind::IntLit256(limbs), span),
                None => self.diagnostics.push(Diagnostic::error(
                    codes::L001,
                    "integer literal out of range (exceeds u256 / 2^256)",
                    Some(span),
                )),
            },
        }
    }

    fn lex_string(&mut self) {
        let start = self.cursor;
        self.cursor += 1;
        // PR S1 / N9-S1 + N15-S1: collect raw source bytes into a
        // `Vec<u8>` to preserve UTF-8 sequences verbatim. The legacy
        // `value.push(other as char)` pattern was a mojibake bug: a
        // source byte `b` in 0x80..=0xFF was reinterpreted as Unicode
        // codepoint U+0080..=U+00FF and re-encoded as a 2-byte UTF-8
        // sequence in the resulting Rust `String`, doubling the byte
        // count and producing incorrect static-data content. Pushing
        // raw bytes preserves the source's UTF-8 sequences.
        let mut value: Vec<u8> = Vec::new();

        while let Some(byte) = self.peek() {
            match byte {
                b'"' => {
                    self.cursor += 1;
                    let span = self.span(start, self.cursor);
                    // SAFETY: bytes pushed into `value` are either
                    // (a) a sub-sequence of `self.bytes` which
                    // originated from `source.text().as_bytes()` (a
                    // valid UTF-8 `&str`), or (b) ASCII escape
                    // replacements (`"`, `\`, `\n`, `\t`) which are
                    // single-byte UTF-8 by definition. Therefore the
                    // result is valid UTF-8 by construction.
                    let value_str = String::from_utf8(value)
                        .expect("string literal bytes are valid UTF-8 by construction");
                    self.push(TokenKind::StrLit(value_str), span);
                    return;
                }
                b'\\' => {
                    self.cursor += 1;
                    match self.peek() {
                        Some(b'"') => value.push(b'"'),
                        Some(b'\\') => value.push(b'\\'),
                        Some(b'n') => value.push(b'\n'),
                        Some(b't') => value.push(b'\t'),
                        Some(other) => value.push(other),
                        None => break,
                    }
                    self.cursor += 1;
                }
                other => {
                    value.push(other);
                    self.cursor += 1;
                }
            }
        }

        self.diagnostics.push(Diagnostic::error(
            codes::L003,
            "unterminated string literal",
            Some(self.span(start, self.cursor)),
        ));
    }

    /// PR-E3: lex an interpolated string `f"…{e}…"` into a token SEQUENCE
    /// (`FStrBegin`, alternating `FStrChunk` / `FStrHoleStart`-tokens-`FStrHoleEnd`,
    /// `FStrEnd`). A literal run is ALWAYS flushed, even empty, so chunks and holes
    /// strictly alternate (ET-E3). `{{`/`}}` and `\{`/`\}` un-escape to literal
    /// braces; a lone `}` in literal text is a literal `}`. Hole contents are lexed
    /// by `lex_one_token` up to the first `}` (no nested braces / no string literals
    /// in a hole — AG-E7/E10). Cursor ends past the closing `"` (ET-E2); an EOF
    /// before the closing `"` or a hole's `}` is an L003 (ET-E8), never a panic.
    fn lex_fstring(&mut self) {
        let begin_start = self.cursor;
        self.cursor += 2; // consume `f"`
        self.push(TokenKind::FStrBegin, self.span(begin_start, self.cursor));
        loop {
            // Scan one literal chunk (decoded), stopping at `{`, `"`, or EOF.
            let chunk_start = self.cursor;
            let mut value: Vec<u8> = Vec::new();
            let mut at_hole = false;
            loop {
                match self.peek() {
                    None => {
                        let text = String::from_utf8(value)
                            .expect("f-string chunk bytes are valid UTF-8 by construction");
                        self.push(
                            TokenKind::FStrChunk(text),
                            self.span(chunk_start, self.cursor),
                        );
                        self.diagnostics.push(Diagnostic::error(
                            codes::L003,
                            "unterminated f-string literal",
                            Some(self.span(begin_start, self.cursor)),
                        ));
                        return;
                    }
                    Some(b'"') => break,
                    Some(b'{') => {
                        if self.peek_next() == Some(b'{') {
                            value.push(b'{');
                            self.cursor += 2;
                        } else {
                            at_hole = true;
                            break;
                        }
                    }
                    Some(b'}') => {
                        if self.peek_next() == Some(b'}') {
                            value.push(b'}');
                            self.cursor += 2;
                        } else {
                            value.push(b'}');
                            self.cursor += 1;
                        }
                    }
                    Some(b'\\') => {
                        self.cursor += 1;
                        match self.peek() {
                            Some(b'"') => value.push(b'"'),
                            Some(b'\\') => value.push(b'\\'),
                            Some(b'n') => value.push(b'\n'),
                            Some(b't') => value.push(b'\t'),
                            Some(b'{') => value.push(b'{'),
                            Some(b'}') => value.push(b'}'),
                            Some(other) => value.push(other),
                            None => break,
                        }
                        self.cursor += 1;
                    }
                    Some(other) => {
                        value.push(other);
                        self.cursor += 1;
                    }
                }
            }
            let text = String::from_utf8(value)
                .expect("f-string chunk bytes are valid UTF-8 by construction");
            self.push(
                TokenKind::FStrChunk(text),
                self.span(chunk_start, self.cursor),
            );
            if at_hole {
                let hole_start = self.cursor;
                self.cursor += 1; // consume `{`
                self.push(TokenKind::FStrHoleStart, self.span(hole_start, self.cursor));
                loop {
                    match self.peek() {
                        None => {
                            self.diagnostics.push(Diagnostic::error(
                                codes::L003,
                                "unterminated interpolation hole",
                                Some(self.span(hole_start, self.cursor)),
                            ));
                            return;
                        }
                        Some(b'}') => {
                            let hole_end = self.cursor;
                            self.cursor += 1; // consume `}`
                            self.push(TokenKind::FStrHoleEnd, self.span(hole_end, self.cursor));
                            break;
                        }
                        Some(_) => self.lex_one_token(),
                    }
                }
                // loop back to scan the next literal chunk
            } else {
                // at the closing `"`
                let end_start = self.cursor;
                self.cursor += 1; // consume `"`
                self.push(TokenKind::FStrEnd, self.span(end_start, self.cursor));
                return;
            }
        }
    }

    fn lex_identifier(&mut self) {
        let start = self.cursor;
        self.cursor += 1;

        while matches!(
            self.peek(),
            Some(b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_')
        ) {
            self.cursor += 1;
        }

        let span = self.span(start, self.cursor);
        let text = self.source.span_text(span);
        let kind = match text {
            "actor" => TokenKind::Actor,
            "ask" => TokenKind::Ask,
            "cap" => TokenKind::Cap,
            "const" => TokenKind::Const,
            "declassify" => TokenKind::Declassify,
            "declassify_ct" => TokenKind::DeclassifyCt,
            "distinct" => TokenKind::Distinct,
            "else" => TokenKind::Else,
            "effect" => TokenKind::Effect,
            "entry" => TokenKind::Entry,
            "enum" => TokenKind::Enum,
            "extern" => TokenKind::Extern,
            "handle" => TokenKind::Handle,
            "false" => TokenKind::BoolLit(false),
            "fn" => TokenKind::Fn,
            "for" => TokenKind::For,
            "if" => TokenKind::If,
            "impl" => TokenKind::Impl,
            "in" => TokenKind::In,
            "init" => TokenKind::Init,
            "let" => TokenKind::Let,
            "match" => TokenKind::Match,
            "module" => TokenKind::Module,
            "mut" => TokenKind::Mut,
            "on" => TokenKind::On,
            "break" => TokenKind::Break,
            "continue" => TokenKind::Continue,
            "pub" => TokenKind::Pub,
            "grant" => TokenKind::Grant,
            "ring" => TokenKind::Ring,
            "record" => TokenKind::Record,
            "region" => TokenKind::Region,
            "return" => TokenKind::Return,
            "send" => TokenKind::Send,
            "spawn" => TokenKind::Spawn,
            "state" => TokenKind::State,
            "supervision" => TokenKind::Supervision,
            "trait" => TokenKind::Trait,
            "true" => TokenKind::BoolLit(true),
            "type" => TokenKind::Type,
            "use" => TokenKind::Use,
            "while" => TokenKind::While,
            "with" => TokenKind::With,
            _ => TokenKind::Ident(text.to_owned()),
        };
        self.push(kind, span);
    }

    fn single(&mut self, kind: TokenKind) {
        let start = self.cursor;
        self.cursor += 1;
        self.push(kind, self.span(start, self.cursor));
    }

    fn double(&mut self, kind: TokenKind) {
        let start = self.cursor;
        self.cursor += 2;
        self.push(kind, self.span(start, self.cursor));
    }

    fn double_or_single(&mut self, expected: u8, doubled: TokenKind, single: TokenKind) {
        if self.peek_next() == Some(expected) {
            self.double(doubled);
        } else {
            self.single(single);
        }
    }

    fn unexpected_char(&mut self) {
        let start = self.cursor;
        self.cursor += 1;
        let snippet = self.source.span_text(self.span(start, self.cursor));
        self.diagnostics.push(Diagnostic::error(
            codes::L004,
            format!("unexpected character `{}`", snippet),
            Some(self.span(start, self.cursor)),
        ));
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.cursor).copied()
    }

    fn peek_next(&self) -> Option<u8> {
        self.bytes.get(self.cursor + 1).copied()
    }

    fn push(&mut self, kind: TokenKind, span: Span) {
        self.tokens.push(Token { kind, span });
    }
}

/// Parse a plain decimal digit string into a u256 as 4 little-endian u64 limbs
/// (u256 PR-U2). Returns `None` if the value is `>= 2^256`. `text` is already a
/// validated run of ASCII digits (the lexer only calls this on `parse::<i64>()`
/// overflow, so it is non-empty and digit-only). Uses native u128 for the
/// per-limb `*10 + carry` so there is no dependency on the in-language u256.
fn parse_u256_decimal(text: &str) -> Option<[u64; 4]> {
    let mut limbs: [u64; 4] = [0; 4];
    for byte in text.bytes() {
        debug_assert!(byte.is_ascii_digit(), "lexer only passes digit runs");
        let mut carry: u128 = (byte - b'0') as u128;
        for limb in limbs.iter_mut() {
            let v: u128 = (*limb as u128) * 10 + carry;
            *limb = v as u64;
            carry = v >> 64;
        }
        if carry != 0 {
            return None; // overflowed 256 bits
        }
    }
    Some(limbs)
}

/// Parse a hex digit string (no `0x` prefix) into a u256 as 4 little-endian u64
/// limbs (u256 PR-U2-b). Returns `None` if the value is `>= 2^256` or a byte is
/// not a hex digit. `text` is non-empty (the lexer guarantees `>= 1` hex digit).
/// Leading zeros are accepted (overflow is decided by the running carry, not the
/// digit count) so a zero-padded 256-bit address/hash parses cleanly.
fn parse_u256_hex(text: &str) -> Option<[u64; 4]> {
    let mut limbs: [u64; 4] = [0; 4];
    for byte in text.bytes() {
        let digit = match byte {
            b'0'..=b'9' => (byte - b'0') as u64,
            b'a'..=b'f' => (byte - b'a' + 10) as u64,
            b'A'..=b'F' => (byte - b'A' + 10) as u64,
            _ => return None,
        };
        // limbs = (limbs << 4) + digit
        let mut carry: u128 = digit as u128;
        for limb in limbs.iter_mut() {
            let v: u128 = ((*limb as u128) << 4) + carry;
            *limb = v as u64;
            carry = v >> 64;
        }
        if carry != 0 {
            return None; // overflowed 256 bits
        }
    }
    Some(limbs)
}

/// Render a u256 (4 little-endian u64 limbs) as its canonical base-10 decimal
/// string (u256 PR-U3-b). The forward inverse of `parse_u256_decimal`: standard
/// multi-limb long division by 10, MSB→LSB per step, collecting remainders. Total
/// and canonical — non-empty, digit-only, no leading zeros, `[0;4] → "0"`. The
/// SINGLE source of wide-value→decimal for BOTH the Z3 numeral (`Int::from_str`)
/// and refinement diagnostics; pinned by an external known-answer table (not just
/// the `parse_u256_decimal` round-trip, which cannot validate the upper two limbs
/// and would cancel a mirrored bug). See docs/specs/u256-refinements-soundness.md.
pub(crate) fn u256_to_decimal(limbs: [u64; 4]) -> String {
    if limbs == [0; 4] {
        return "0".to_string();
    }
    let mut digits: Vec<u8> = Vec::with_capacity(78);
    let mut v = limbs;
    while v != [0; 4] {
        let mut rem: u128 = 0;
        // Divide the 256-bit value by 10, processing the most-significant limb
        // first so the remainder carries down into the next limb.
        for i in (0..4).rev() {
            let cur: u128 = (rem << 64) | (v[i] as u128);
            v[i] = (cur / 10) as u64;
            rem = cur % 10;
        }
        digits.push(b'0' + rem as u8);
    }
    digits.reverse();
    // SAFETY-equivalent: every pushed byte is `b'0'..=b'9'`.
    String::from_utf8(digits).expect("u256_to_decimal emits only ASCII digits")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// PR-U3-b NC-b1: `u256_to_decimal` pinned against an EXTERNAL hand-computed
    /// known-answer table (independent of `parse_u256_decimal`), so a marshalling
    /// bug that would cancel in the round-trip cannot hide — including the upper
    /// two limbs, which the round-trip + a u128 cross-check cannot validate.
    #[test]
    fn u256_to_decimal_known_answers() {
        let cases: &[([u64; 4], &str)] = &[
            ([0, 0, 0, 0], "0"),
            ([1, 0, 0, 0], "1"),
            ([9223372036854775808, 0, 0, 0], "9223372036854775808"), // i64::MAX + 1 = 2^63
            ([0, 1, 0, 0], "18446744073709551616"),                  // 2^64
            ([5, 1, 0, 0], "18446744073709551621"),                  // 2^64 + 5 (mixed low/high)
            ([0, 0, 1, 0], "340282366920938463463374607431768211456"), // 2^128
            (
                [0, 0, 0, 1],
                "6277101735386680763835789423207666416102355444464034512896",
            ), // 2^192
            (
                [u64::MAX, u64::MAX, u64::MAX, u64::MAX],
                "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            ), // 2^256 - 1
        ];
        for (limbs, expected) in cases {
            assert_eq!(
                &u256_to_decimal(*limbs),
                expected,
                "u256_to_decimal({limbs:?}) mismatch"
            );
        }
    }

    /// Belt (NOT the sole pin): `u256_to_decimal` is a left-inverse of
    /// `parse_u256_decimal` over the limb domain.
    #[test]
    fn u256_to_decimal_round_trips_through_parser() {
        let limb_sets: &[[u64; 4]] = &[
            [0, 0, 0, 0],
            [1, 0, 0, 0],
            [0, 1, 0, 0],
            [0, 0, 1, 0],
            [0, 0, 0, 1],
            [12345, 67890, 13579, 24680],
            [u64::MAX, u64::MAX, u64::MAX, u64::MAX],
        ];
        for limbs in limb_sets {
            let decimal = u256_to_decimal(*limbs);
            assert_eq!(
                parse_u256_decimal(&decimal),
                Some(*limbs),
                "round-trip failed for {limbs:?} (decimal {decimal})"
            );
        }
    }

    /// Every keyword the lexer recognises must round-trip through
    /// [`TokenKind::keyword_text`]: lexing the source word yields a token
    /// whose `keyword_text()` returns that exact word. This pins the reverse
    /// map in lock-step with the keyword arms of [`Lexer::lex_identifier`] —
    /// a keyword added to the lexer but forgotten in `keyword_text` would
    /// silently re-open the reserved-keyword-as-identifier bug (P026 would
    /// not fire for it), and this test fails loudly instead.
    #[test]
    fn keyword_text_round_trips() {
        // The authoritative list of word-shaped keywords (mirrors the match
        // arms in `lex_identifier`; `true`/`false` lex to `BoolLit`, not a
        // keyword token, so they are intentionally excluded).
        const KEYWORDS: &[&str] = &[
            "actor",
            "ask",
            "cap",
            "const",
            "distinct",
            "else",
            "entry",
            "effect",
            "enum",
            "extern",
            "fn",
            "handle",
            "for",
            "grant",
            "record",
            "region",
            "ring",
            "if",
            "impl",
            "in",
            "init",
            "let",
            "match",
            "break",
            "continue",
            "module",
            "mut",
            "on",
            "pub",
            "return",
            "send",
            "spawn",
            "state",
            "supervision",
            "trait",
            "type",
            "use",
            "while",
            "declassify",
            "declassify_ct",
            "with",
        ];

        for &kw in KEYWORDS {
            let source = SourceFile::new("<kw>", kw);
            let (tokens, diags) = lex(&source);
            assert!(diags.is_empty(), "`{kw}` produced lexer diagnostics");
            // tokens = [keyword, Eof]
            assert_eq!(
                tokens[0].kind.keyword_text(),
                Some(kw),
                "`{kw}` lexed to {:?}, which keyword_text() does not map back to `{kw}`",
                tokens[0].kind,
            );
        }
    }

    /// Non-keyword tokens (identifiers, literals, punctuation) report no
    /// keyword text, so the parser never mistakes a real name for a keyword.
    #[test]
    fn non_keywords_have_no_keyword_text() {
        let source = SourceFile::new("<id>", "handler reply 42 + ;");
        let (tokens, _diags) = lex(&source);
        for token in &tokens {
            assert_eq!(
                token.kind.keyword_text(),
                None,
                "{:?} unexpectedly reported keyword text",
                token.kind,
            );
        }
    }
}
