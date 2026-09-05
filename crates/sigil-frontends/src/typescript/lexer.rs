//! Hand-written lexer for the FE0 TypeScript policy subset. Total over all
//! input (threat T12): every byte either advances cleanly or produces a single
//! `FrontendDiag` — never a panic, never partial output. All bounds are dumb
//! and checked before work.

use std::ops::Range;

use crate::FrontendDiag;
use crate::codes;
use crate::limits;

#[derive(Debug, Clone, PartialEq)]
pub enum TokKind {
    /// An identifier or word-keyword (`function`/`return`/`number` are matched
    /// in the parser by string). Always legal SIGIL identifier charset by
    /// construction — the lexer only reads ASCII `[A-Za-z0-9_]`.
    Ident(String),
    /// A plain decimal integer literal within i64 range.
    Int(i64),
    /// The inner text of a `/** ... */` doc comment (carries policy tags).
    JsDoc(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Semi,
    Arrow, // =>
    Plus,
    Minus,
    Star,
    // FE2 additions:
    Dot,      // .
    Eq,       // =  (assignment)
    EqEq,     // ==
    BangEq,   // !=
    Bang,     // !
    Lt,       // <
    LtEq,     // <=
    Gt,       // >
    GtEq,     // >=
    AmpAmp,   // &&
    PipePipe, // ||
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

/// Tokenize the whole input, emitting `JsDoc` tokens for `/** ... */` doc
/// comments (other comments and whitespace are skipped). Fails fast on the
/// first illegal byte/number/identifier; on success returns the token stream
/// (no EOF sentinel).
pub fn lex(src: &str) -> Result<Vec<Tok>, FrontendDiag> {
    // Threat T12 / FE002: size cap checked before any work.
    if src.len() > limits::MAX_INPUT_BYTES {
        return Err(FrontendDiag::new(
            codes::FE002_TOO_LARGE,
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
        lx.skip_trivia(src, &mut out)?;
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
            b':' => lx.single(TokKind::Colon),
            b';' => lx.single(TokKind::Semi),
            b'+' => lx.single(TokKind::Plus),
            b'-' => lx.single(TokKind::Minus),
            b'*' => {
                // Reject `**` (exponent, threat T16) explicitly.
                if lx.peek_at(1) == Some(b'*') {
                    return Err(FrontendDiag::new(
                        codes::FE031_BAD_OPERATOR,
                        "operator `**` (exponent) is not supported",
                        start..start + 2,
                    ));
                }
                lx.single(TokKind::Star)
            }
            b'=' => match (lx.peek_at(1), lx.peek_at(2)) {
                (Some(b'>'), _) => lx.two(TokKind::Arrow),
                (Some(b'='), Some(b'=')) => {
                    return Err(FrontendDiag::new(
                        codes::FE320_UNSUPPORTED_TS,
                        "strict equality `===` is not supported (use `==`)",
                        start..start + 3,
                    ));
                }
                (Some(b'='), _) => lx.two(TokKind::EqEq),
                _ => lx.single(TokKind::Eq),
            },
            b'!' => match (lx.peek_at(1), lx.peek_at(2)) {
                (Some(b'='), Some(b'=')) => {
                    return Err(FrontendDiag::new(
                        codes::FE320_UNSUPPORTED_TS,
                        "strict inequality `!==` is not supported (use `!=`)",
                        start..start + 3,
                    ));
                }
                (Some(b'='), _) => lx.two(TokKind::BangEq),
                _ => lx.single(TokKind::Bang),
            },
            b'<' => match lx.peek_at(1) {
                Some(b'=') => lx.two(TokKind::LtEq),
                Some(b'<') => {
                    return Err(FrontendDiag::new(
                        codes::FE031_BAD_OPERATOR,
                        "operator `<<` (shift) is not supported",
                        start..start + 2,
                    ));
                }
                _ => lx.single(TokKind::Lt),
            },
            b'>' => match lx.peek_at(1) {
                Some(b'=') => lx.two(TokKind::GtEq),
                Some(b'>') => {
                    return Err(FrontendDiag::new(
                        codes::FE031_BAD_OPERATOR,
                        "shift operators are not supported",
                        start..start + 2,
                    ));
                }
                _ => lx.single(TokKind::Gt),
            },
            b'&' => match lx.peek_at(1) {
                Some(b'&') => lx.two(TokKind::AmpAmp),
                _ => {
                    return Err(FrontendDiag::new(
                        codes::FE031_BAD_OPERATOR,
                        "bitwise `&` is not supported",
                        start..start + 1,
                    ));
                }
            },
            b'|' => match lx.peek_at(1) {
                Some(b'|') => lx.two(TokKind::PipePipe),
                _ => {
                    return Err(FrontendDiag::new(
                        codes::FE031_BAD_OPERATOR,
                        "bitwise `|` is not supported",
                        start..start + 1,
                    ));
                }
            },
            b'.' => lx.single(TokKind::Dot),
            b'?' => {
                return Err(FrontendDiag::new(
                    codes::FE320_UNSUPPORTED_TS,
                    "`?` (optional field / ternary / nullish) is not supported in FE2",
                    start..start + 1,
                ));
            }
            b'0'..=b'9' => lx.lex_number()?,
            b'A'..=b'Z' | b'a'..=b'z' | b'_' => lx.lex_ident()?,
            // `/` division, `%` modulo, `^` xor, `~` bitnot — excluded (FE2 keeps
            // integer-division/float divergence out, like FE0).
            b'/' | b'%' | b'^' | b'~' => {
                return Err(FrontendDiag::new(
                    codes::FE031_BAD_OPERATOR,
                    format!(
                        "operator `{}` is not supported (FE2 excludes / % and bitwise)",
                        b as char
                    ),
                    start..start + 1,
                ));
            }
            _ => {
                return Err(FrontendDiag::new(
                    codes::FE001_UNSUPPORTED,
                    format!("unexpected byte 0x{b:02x} (FE2 accepts ASCII only)"),
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

    /// Skip whitespace, `//` line comments, and `/* */` block comments. A
    /// `/** ... */` doc comment is emitted as a `JsDoc` token into `out`.
    fn skip_trivia(&mut self, src: &str, out: &mut Vec<Tok>) -> Result<(), FrontendDiag> {
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
                    let start = self.pos;
                    // Doc comment iff `/**` but not the empty `/**/`.
                    let is_doc = self.peek_at(2) == Some(b'*') && self.peek_at(3) != Some(b'/');
                    self.skip_block_comment()?;
                    if is_doc {
                        let inner = &src[start + 3..self.pos - 2];
                        out.push(Tok {
                            kind: TokKind::JsDoc(inner.to_owned()),
                            span: start..self.pos,
                        });
                    }
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
                        codes::FE001_UNSUPPORTED,
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
        // Reject any non-plain-decimal continuation: `.`/alpha/`_` (hex, float,
        // BigInt `n`, separators — threat T9).
        if let Some(c) = self.src.get(self.pos).copied()
            && (c == b'.' || c == b'_' || c.is_ascii_alphabetic())
        {
            let bad_start = start;
            while let Some(c) = self.src.get(self.pos).copied() {
                if c.is_ascii_alphanumeric() || c == b'.' || c == b'_' {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            return Err(FrontendDiag::new(
                codes::FE030_BAD_NUMBER,
                "only plain decimal integer literals are supported (no float/hex/octal/binary/BigInt/separators)",
                bad_start..self.pos,
            ));
        }
        // Reject non-canonical leading zero (`007`).
        if digits.len() > 1 && digits[0] == b'0' {
            return Err(FrontendDiag::new(
                codes::FE030_BAD_NUMBER,
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
                codes::FE030_BAD_NUMBER,
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
                codes::FE020_BAD_IDENTIFIER,
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
