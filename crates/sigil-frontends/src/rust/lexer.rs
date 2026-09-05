//! Hand-written lexer for the RS0 Rust subset. Total over all input (SC-8/SC-9):
//! every byte either advances cleanly or produces a single `FrontendDiag` — never
//! a panic, never partial output. All bounds are dumb and checked before work.
//!
//! Rust keywords (`fn`, `pub`, `return`, `i64`, `bool`, `true`, `false`, …) are
//! lexed as `Ident` and interpreted positionally by the parser (mirrors the TS
//! frontend). The lexer reads only ASCII `[A-Za-z0-9_]` for identifiers; a
//! non-ASCII byte at token position is a fail-closed `FE620` (UTF-8 in comments is
//! consumed byte-wise, which is safe — `*/`, `\n` never collide with a UTF-8
//! continuation byte).

use std::ops::Range;

use crate::FrontendDiag;
use crate::codes;
use crate::limits;

#[derive(Debug, Clone, PartialEq)]
pub enum TokKind {
    /// An identifier or word-keyword. Always a legal SIGIL identifier charset by
    /// construction — the lexer only reads ASCII `[A-Za-z0-9_]`.
    Ident(String),
    /// A plain decimal integer literal within i64 range.
    Int(i64),
    /// A `#[ … ]` attribute, carrying the inner text (RS1: `sigil::cap( … )`),
    /// parsed separately so `::`/`[`/`]` stay out of the general token set.
    Attr(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    ColonColon, // ::  (enum-variant paths; RS3b enums)
    Semi,
    Arrow,    // ->
    FatArrow, // =>  (match arms; RS3b)
    Plus,
    Minus,
    Star,
    Dot,    // .  (field access; RS3 structs)
    Eq,     // =  (assignment; reserved for a later RS0 increment)
    EqEq,   // ==
    BangEq, // !=
    Bang,   // !
    Lt,     // <
    LtEq,   // <=
    Gt,     // >
    GtEq,   // >=
}

#[derive(Debug, Clone)]
pub struct Tok {
    pub kind: TokKind,
    pub span: Range<usize>,
}

struct Lexer<'a> {
    src: &'a [u8],
    pos: usize,
}

/// Tokenize the whole input. Whitespace and all comment forms (`//`, `///`,
/// `//!`, `/* */`) are skipped. Fails fast on the first illegal byte / number /
/// identifier; on success returns the token stream (no EOF sentinel).
pub fn lex(src: &str) -> Result<Vec<Tok>, FrontendDiag> {
    // SC-8 / FE602: size cap checked before any work.
    if src.len() > limits::MAX_INPUT_BYTES {
        return Err(FrontendDiag::new(
            codes::FE602_TOO_LARGE_RS,
            format!(
                "input is {} bytes; the limit is {} bytes",
                src.len(),
                limits::MAX_INPUT_BYTES
            ),
            0..src.len(),
        ));
    }
    let mut lx = Lexer {
        src: src.as_bytes(),
        pos: 0,
    };
    let mut out = Vec::new();
    loop {
        lx.skip_trivia()?;
        if lx.pos >= lx.src.len() {
            break;
        }
        let start = lx.pos;
        let b = lx.src[lx.pos];
        let tok = match b {
            b'(' => lx.single(TokKind::LParen),
            b')' => lx.single(TokKind::RParen),
            b'{' => lx.single(TokKind::LBrace),
            b'}' => lx.single(TokKind::RBrace),
            b',' => lx.single(TokKind::Comma),
            b':' => match lx.peek_at(1) {
                // `::` is an enum-variant path (`Name::Variant`; RS3b). Other path
                // uses (`std::mem`, `a::b::c`) are gated by the parser, which only
                // accepts `::` between two bare identifiers in ctor/pattern position.
                Some(b':') => lx.two(TokKind::ColonColon),
                _ => lx.single(TokKind::Colon),
            },
            b';' => lx.single(TokKind::Semi),
            b'+' => lx.single(TokKind::Plus),
            b'*' => lx.single(TokKind::Star),
            b'-' => match lx.peek_at(1) {
                Some(b'>') => lx.two(TokKind::Arrow),
                _ => lx.single(TokKind::Minus),
            },
            b'=' => match lx.peek_at(1) {
                Some(b'=') => lx.two(TokKind::EqEq),
                Some(b'>') => lx.two(TokKind::FatArrow), // => (match arm; RS3b)
                _ => lx.single(TokKind::Eq),
            },
            b'!' => match lx.peek_at(1) {
                Some(b'=') => lx.two(TokKind::BangEq),
                _ => lx.single(TokKind::Bang),
            },
            b'<' => match lx.peek_at(1) {
                Some(b'=') => lx.two(TokKind::LtEq),
                Some(b'<') => {
                    return Err(FrontendDiag::new(
                        codes::FE611_BAD_OPERATOR_RS,
                        "shift operator `<<` is not supported in RS0",
                        start..start + 2,
                    ));
                }
                _ => lx.single(TokKind::Lt),
            },
            b'>' => match lx.peek_at(1) {
                Some(b'=') => lx.two(TokKind::GtEq),
                Some(b'>') => {
                    return Err(FrontendDiag::new(
                        codes::FE611_BAD_OPERATOR_RS,
                        "shift operator `>>` is not supported in RS0",
                        start..start + 2,
                    ));
                }
                _ => lx.single(TokKind::Gt),
            },
            // References/borrows and logical `&&`/`||` are out-of-subset in RS0
            // (value-semantics only; `&&`/`||` desugaring arrives later).
            b'&' => {
                return Err(FrontendDiag::new(
                    codes::FE601_UNSUPPORTED_RS,
                    "references/borrows and `&&` are not supported in RS0 (value semantics only)",
                    start..start + 1,
                ));
            }
            b'|' => {
                return Err(FrontendDiag::new(
                    codes::FE601_UNSUPPORTED_RS,
                    "closures and `||` are not supported in RS0",
                    start..start + 1,
                ));
            }
            // `/` reaching here is division (comment forms are consumed in trivia).
            b'/' | b'%' => {
                return Err(FrontendDiag::new(
                    codes::FE611_BAD_OPERATOR_RS,
                    format!(
                        "operator `{}` is not supported in RS0 (`/` `%` excluded — divergent int semantics)",
                        b as char
                    ),
                    start..start + 1,
                ));
            }
            b'^' | b'~' => {
                return Err(FrontendDiag::new(
                    codes::FE611_BAD_OPERATOR_RS,
                    format!("bitwise operator `{}` is not supported in RS0", b as char),
                    start..start + 1,
                ));
            }
            b'.' => lx.single(TokKind::Dot),
            b'#' => lx.lex_attr()?,
            b'?' => {
                return Err(FrontendDiag::new(
                    codes::FE601_UNSUPPORTED_RS,
                    "the `?` operator is not supported in RS0",
                    start..start + 1,
                ));
            }
            b'0'..=b'9' => lx.lex_number()?,
            b'A'..=b'Z' | b'a'..=b'z' | b'_' => lx.lex_ident()?,
            b if b >= 0x80 => {
                // A non-ASCII byte at token position: Rust permits Unicode XID
                // identifiers, but SIGIL's identifier charset is ASCII, so this is
                // a fail-closed FE620. Span the whole UTF-8 char so we never split
                // a code point (SC-9).
                let end = lx.utf8_char_end(start);
                return Err(FrontendDiag::new(
                    codes::FE620_BAD_IDENTIFIER_RS,
                    "non-ASCII identifiers are not supported in RS0 (identifier charset is ASCII)",
                    start..end,
                ));
            }
            _ => {
                return Err(FrontendDiag::new(
                    codes::FE601_UNSUPPORTED_RS,
                    format!("unexpected byte 0x{b:02x}"),
                    start..start + 1,
                ));
            }
        };
        out.push(tok);
    }
    Ok(out)
}

impl Lexer<'_> {
    fn peek_at(&self, off: usize) -> Option<u8> {
        self.src.get(self.pos + off).copied()
    }

    fn two(&mut self, kind: TokKind) -> Tok {
        let start = self.pos;
        self.pos += 2;
        Tok {
            kind,
            span: start..self.pos,
        }
    }

    fn single(&mut self, kind: TokKind) -> Tok {
        let start = self.pos;
        self.pos += 1;
        Tok {
            kind,
            span: start..self.pos,
        }
    }

    /// Byte index just past the UTF-8 character starting at `start` (total: falls
    /// back to `start + 1` for a stray continuation byte, never past the end).
    fn utf8_char_end(&self, start: usize) -> usize {
        let b = self.src[start];
        let len = if b >= 0xF0 {
            4
        } else if b >= 0xE0 {
            3
        } else if b >= 0xC0 {
            2
        } else {
            1
        };
        (start + len).min(self.src.len())
    }

    /// Lex a `#[ … ]` attribute into an `Attr` token carrying the inner text.
    /// Bracket depth is tracked iteratively (no recursion → no stack overflow;
    /// the scan is bounded by the already-size-capped input). `[`/`]` are ASCII,
    /// so slicing the inner text never splits a UTF-8 code point.
    fn lex_attr(&mut self) -> Result<Tok, FrontendDiag> {
        let start = self.pos; // at `#`
        self.pos += 1; // consume `#`
        if self.src.get(self.pos) != Some(&b'[') {
            return Err(FrontendDiag::new(
                codes::FE601_UNSUPPORTED_RS,
                "expected `[` after `#` (RS1 supports `#[sigil::cap( … )]` attributes)",
                start..self.pos,
            ));
        }
        self.pos += 1; // consume `[`
        let inner_start = self.pos;
        let mut depth: u32 = 1;
        while self.pos < self.src.len() {
            match self.src[self.pos] {
                b'[' => depth += 1,
                b']' => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
            self.pos += 1;
        }
        if depth != 0 {
            return Err(FrontendDiag::new(
                codes::FE601_UNSUPPORTED_RS,
                "unterminated attribute (missing `]`)",
                start..self.src.len(),
            ));
        }
        let inner = std::str::from_utf8(&self.src[inner_start..self.pos])
            .map_err(|_| {
                FrontendDiag::new(
                    codes::FE601_UNSUPPORTED_RS,
                    "attribute contains invalid UTF-8",
                    start..self.pos,
                )
            })?
            .to_owned();
        self.pos += 1; // consume `]`
        Ok(Tok {
            kind: TokKind::Attr(inner),
            span: start..self.pos,
        })
    }

    /// Skip whitespace, `//` line comments (incl. `///` / `//!`), and `/* */`
    /// block comments. Comment bodies are scanned byte-wise, which is UTF-8-safe.
    fn skip_trivia(&mut self) -> Result<(), FrontendDiag> {
        loop {
            match self.src.get(self.pos).copied() {
                Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n') => self.pos += 1,
                Some(b'/') if self.peek_at(1) == Some(b'/') => {
                    self.pos += 2;
                    while let Some(c) = self.src.get(self.pos).copied() {
                        if c == b'\n' {
                            break;
                        }
                        self.pos += 1;
                    }
                }
                Some(b'/') if self.peek_at(1) == Some(b'*') => {
                    self.skip_block_comment()?;
                }
                _ => break,
            }
        }
        Ok(())
    }

    fn skip_block_comment(&mut self) -> Result<(), FrontendDiag> {
        let start = self.pos;
        self.pos += 2; // consume /*
        loop {
            match self.src.get(self.pos).copied() {
                None => {
                    return Err(FrontendDiag::new(
                        codes::FE601_UNSUPPORTED_RS,
                        "unterminated block comment",
                        start..self.src.len(),
                    ));
                }
                Some(b'*') if self.peek_at(1) == Some(b'/') => {
                    self.pos += 2;
                    return Ok(());
                }
                _ => self.pos += 1,
            }
        }
    }

    fn lex_number(&mut self) -> Result<Tok, FrontendDiag> {
        let start = self.pos;
        while let Some(b'0'..=b'9') = self.src.get(self.pos).copied() {
            self.pos += 1;
        }
        let digits = &self.src[start..self.pos];
        // Reject any non-plain-decimal continuation: `.`/alpha/`_` (float, hex/bin/
        // oct radix, a type suffix like `5i32`, or `_` separators) → FE612.
        if let Some(c) = self.src.get(self.pos).copied()
            && (c == b'.' || c == b'_' || c.is_ascii_alphabetic())
        {
            while let Some(c) = self.src.get(self.pos).copied() {
                if c.is_ascii_alphanumeric() || c == b'.' || c == b'_' {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            return Err(FrontendDiag::new(
                codes::FE612_BAD_NUMBER_RS,
                "only plain decimal integer literals are supported (no float/hex/octal/binary/suffix/`_` separators)",
                start..self.pos,
            ));
        }
        // Reject a non-canonical leading zero (`007`) so emitted literals stay
        // canonical and deterministic.
        if digits.len() > 1 && digits[0] == b'0' {
            return Err(FrontendDiag::new(
                codes::FE612_BAD_NUMBER_RS,
                "integer literals may not have a leading zero",
                start..self.pos,
            ));
        }
        let text = std::str::from_utf8(digits).expect("ascii digits");
        match text.parse::<i64>() {
            Ok(v) => Ok(Tok {
                kind: TokKind::Int(v),
                span: start..self.pos,
            }),
            Err(_) => Err(FrontendDiag::new(
                codes::FE612_BAD_NUMBER_RS,
                format!("integer literal `{text}` is out of i64 range"),
                start..self.pos,
            )),
        }
    }

    fn lex_ident(&mut self) -> Result<Tok, FrontendDiag> {
        let start = self.pos;
        while let Some(b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_') =
            self.src.get(self.pos).copied()
        {
            self.pos += 1;
        }
        let len = self.pos - start;
        if len > limits::MAX_IDENT_BYTES {
            return Err(FrontendDiag::new(
                codes::FE620_BAD_IDENTIFIER_RS,
                format!(
                    "identifier is {} bytes; the limit is {} bytes",
                    len,
                    limits::MAX_IDENT_BYTES
                ),
                start..self.pos,
            ));
        }
        let text = std::str::from_utf8(&self.src[start..self.pos])
            .expect("ascii identifier")
            .to_owned();
        Ok(Tok {
            kind: TokKind::Ident(text),
            span: start..self.pos,
        })
    }
}
