//! Hand-rolled Solidity lexer for the SOL0 subset. Total (never panics, never
//! hangs): on any byte it cannot classify it returns a single `FrontendDiag`.
//! Mirrors the TypeScript frontend's lexer discipline (size cap first, ASCII
//! only, comments skipped). Type names (`uint256`, `address`, …) are lexed as
//! `Ident`; the allow-list reject (NC-S2/NC-S5) lives in the parser/checker so
//! the diagnostic can name the offending type precisely.

use crate::FrontendDiag;
use crate::codes;
use crate::limits::MAX_INPUT_BYTES;
use std::ops::Range;

#[derive(Debug, Clone, PartialEq)]
pub enum TokKind {
    // declaration keywords
    Contract,
    Function,
    Returns,
    Return,
    Require,
    Assert,
    Revert,
    If,
    Else,
    Unchecked,
    /// An inline `assembly { … }` (YUL) block — the lexer skips the WHOLE balanced block (so
    /// its YUL bytes never surface as a generic "unexpected byte"); the parser rejects it
    /// precisely (FE478). A separate low-level sub-language we do not translate.
    Assembly,
    // visibility / mutability / data-location markers
    Public,
    Private,
    Internal,
    External,
    View,
    Pure,
    Memory,
    Storage,
    Calldata,
    // literals
    True,
    False,
    Num(String),   // decimal or 0x-hex, raw text (range-checked in lex_number)
    Ident(String), // identifiers AND type names (uint256/address/…)
    /// A string literal. SOL0 keeps NO contents — the only place a string is legal
    /// is a `require(cond, "reason")` reason, which is dropped (NC AG-S4). Anywhere
    /// else, the parser fail-closes (a string is not an expression form).
    Str(String), // raw literal text between the quotes (SOL-XFILE: consumed only by the import-path capture)
    /// The raw text of a `pragma … ;` directive (between `pragma` and `;`,
    /// trimmed) — version validation (NC-S3, >= 0.8.0) happens in the checker.
    Pragma(String),
    // punctuation
    LParen,
    RParen,
    LBrace,
    RBrace,
    /// `[` / `]` — mapping index `m[k]` (SOL1).
    LBracket,
    RBracket,
    Semi,
    Comma,
    Dot,
    /// `=>` — the mapping arrow `mapping(K => V)` (SOL1).
    FatArrow,
    // operators
    Plus,
    Minus,
    Star,
    /// `**` — Solidity exponentiation. SOL-TOKEN constant-folds a literal `base ** exp`; a
    /// non-constant `**` is rejected (FE482). Tokenized here so it never lexes as two `Star`s.
    Pow,
    Slash,
    Percent,
    Assign,
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    PercentEq,
    EqEq,
    BangEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    Bang,
    AmpAmp,
    PipePipe,
    /// Bitwise / shift / ternary operator bytes — tokenized so the lexer never dies on them;
    /// the parser rejects them precisely (bitwise/shift → FE479, ternary → FE480). The `=`
    /// compounds (`&=`/`<<=`/…) lex as the base op + `Assign`, hitting the same reject.
    Amp,
    Pipe,
    Caret,
    Tilde,
    Shl,
    Shr,
    Question,
    Colon,
    Eof,
}

#[derive(Debug, Clone)]
pub struct Tok {
    pub kind: TokKind,
    pub span: Range<usize>,
}

struct Lexer<'a> {
    b: &'a [u8],
    src: &'a str,
    i: usize,
    out: Vec<Tok>,
}

/// Tokenize `src`. Fail-closed + total.
pub fn lex(src: &str) -> Result<Vec<Tok>, FrontendDiag> {
    if src.len() > MAX_INPUT_BYTES {
        return Err(FrontendDiag::new(
            codes::FE402_TOO_LARGE_SOL,
            format!("source exceeds {MAX_INPUT_BYTES} bytes"),
            0..src.len(),
        ));
    }
    let mut lx = Lexer {
        b: src.as_bytes(),
        src,
        i: 0,
        out: Vec::new(),
    };
    lx.run()?;
    let end = src.len();
    lx.out.push(Tok {
        kind: TokKind::Eof,
        span: end..end,
    });
    Ok(lx.out)
}

/// Whether a decimal digit string is `< 2^256` (the u256 ceiling). Compares against
/// `2^256 - 1` by length, then lexicographically at the boundary length (valid since
/// both are equal-length pure-digit strings). Input is all-ASCII digits by construction.
/// `pub(super)` so `parser::fold_pow_decimal` can range-check a constant-folded `**` result.
pub(super) fn u256_decimal_in_range(digits: &str) -> bool {
    /// `2^256 - 1`, the largest u256 (78 decimal digits).
    const MAX: &str =
        "115792089237316195423570985008687907853269984665640564039457584007913129639935";
    let t = digits.trim_start_matches('0');
    let t = if t.is_empty() { "0" } else { t };
    t.len() < MAX.len() || (t.len() == MAX.len() && t <= MAX)
}

/// `mantissa` (pure ASCII digits) × 10^`scale` as a decimal-integer string, or `None` if the
/// value is not a non-negative integer (a negative `scale` that would drop a non-zero digit —
/// e.g. `0.5`). Used to expand Solidity scientific / fractional literals (`1e18`, `2.5e3`) to a
/// plain integer. Padding is capped (u256 max is 78 digits; the caller range-rejects an oversize
/// result) so a huge exponent cannot trigger a pathological allocation.
fn expand_pow10(mantissa: &str, scale: i64) -> Option<String> {
    let m = mantissa.trim_start_matches('0');
    let m = if m.is_empty() { "0" } else { m };
    if m == "0" {
        return Some("0".to_string());
    }
    match scale.cmp(&0) {
        std::cmp::Ordering::Equal => Some(m.to_string()),
        std::cmp::Ordering::Greater => {
            let pad = scale.min(100) as usize; // >78 is unconditionally out of range
            let mut s = String::with_capacity(m.len() + pad);
            s.push_str(m);
            s.extend(std::iter::repeat_n('0', pad));
            Some(s)
        }
        std::cmp::Ordering::Less => {
            let drop = (-scale) as usize;
            // Integral only if the dropped trailing digits are all zero.
            if drop < m.len() && m.as_bytes()[m.len() - drop..].iter().all(|b| *b == b'0') {
                Some(m[..m.len() - drop].to_string())
            } else {
                None
            }
        }
    }
}

impl<'a> Lexer<'a> {
    fn run(&mut self) -> Result<(), FrontendDiag> {
        while self.i < self.b.len() {
            let c = self.b[self.i];
            match c {
                b' ' | b'\t' | b'\r' | b'\n' => self.i += 1,
                b'/' if self.peek(1) == Some(b'/') => self.skip_line_comment(),
                b'/' if self.peek(1) == Some(b'*') => self.skip_block_comment()?,
                b'0'..=b'9' => self.lex_number()?,
                // Solidity strings may be double- OR single-quoted (identical semantics);
                // contents are discarded either way (SOL only uses a string as a dropped
                // `require` reason). Pass the opening quote so the matching close is correct.
                b'"' | b'\'' => self.lex_string(c)?,
                b'(' => self.punct(TokKind::LParen),
                b')' => self.punct(TokKind::RParen),
                b'{' => self.punct(TokKind::LBrace),
                b'}' => self.punct(TokKind::RBrace),
                b'[' => self.punct(TokKind::LBracket),
                b']' => self.punct(TokKind::RBracket),
                b';' => self.punct(TokKind::Semi),
                b',' => self.punct(TokKind::Comma),
                b'.' => self.punct(TokKind::Dot),
                b'+' => self.op2(b'=', TokKind::PlusEq, TokKind::Plus),
                b'-' => self.op2(b'=', TokKind::MinusEq, TokKind::Minus),
                // `**` (exponentiation) before `*=`/`*`; Solidity has no `**=`.
                b'*' if self.peek(1) == Some(b'*') => self.punct2(TokKind::Pow),
                b'*' => self.op2(b'=', TokKind::StarEq, TokKind::Star),
                b'/' => self.op2(b'=', TokKind::SlashEq, TokKind::Slash),
                b'%' => self.op2(b'=', TokKind::PercentEq, TokKind::Percent),
                // `=` is three-way: `==` (EqEq), `=>` (FatArrow, mapping arrow), `=` (Assign).
                b'=' if self.peek(1) == Some(b'=') => self.punct2(TokKind::EqEq),
                b'=' if self.peek(1) == Some(b'>') => self.punct2(TokKind::FatArrow),
                b'=' => self.punct(TokKind::Assign),
                b'!' => self.op2(b'=', TokKind::BangEq, TokKind::Bang),
                // `<<`/`>>` shifts before the `<=`/`>=`/`<`/`>` comparisons.
                b'<' if self.peek(1) == Some(b'<') => self.punct2(TokKind::Shl),
                b'<' => self.op2(b'=', TokKind::LtEq, TokKind::Lt),
                b'>' if self.peek(1) == Some(b'>') => self.punct2(TokKind::Shr),
                b'>' => self.op2(b'=', TokKind::GtEq, TokKind::Gt),
                b'&' if self.peek(1) == Some(b'&') => self.punct2(TokKind::AmpAmp),
                b'&' => self.punct(TokKind::Amp),
                b'|' if self.peek(1) == Some(b'|') => self.punct2(TokKind::PipePipe),
                b'|' => self.punct(TokKind::Pipe),
                b'^' => self.punct(TokKind::Caret),
                b'~' => self.punct(TokKind::Tilde),
                b'?' => self.punct(TokKind::Question),
                b':' => self.punct(TokKind::Colon),
                _ if c == b'_' || c.is_ascii_alphabetic() => self.lex_ident_or_keyword()?,
                _ => {
                    return Err(FrontendDiag::new(
                        codes::FE401_UNSUPPORTED_SOL,
                        format!("unexpected byte {:?}", c as char),
                        self.i..self.i + 1,
                    ));
                }
            }
        }
        Ok(())
    }

    fn peek(&self, k: usize) -> Option<u8> {
        self.b.get(self.i + k).copied()
    }

    fn punct(&mut self, kind: TokKind) {
        self.out.push(Tok {
            kind,
            span: self.i..self.i + 1,
        });
        self.i += 1;
    }

    fn punct2(&mut self, kind: TokKind) {
        self.out.push(Tok {
            kind,
            span: self.i..self.i + 2,
        });
        self.i += 2;
    }

    /// A one-or-two-char operator: if the next byte is `second`, emit `two`
    /// (2 bytes), else `one` (1 byte).
    fn op2(&mut self, second: u8, two: TokKind, one: TokKind) {
        if self.peek(1) == Some(second) {
            self.punct2(two);
        } else {
            self.punct(one);
        }
    }

    fn skip_line_comment(&mut self) {
        while self.i < self.b.len() && self.b[self.i] != b'\n' {
            self.i += 1;
        }
    }

    fn skip_block_comment(&mut self) -> Result<(), FrontendDiag> {
        let start = self.i;
        self.i += 2; // consume /*
        while self.i + 1 < self.b.len() {
            if self.b[self.i] == b'*' && self.b[self.i + 1] == b'/' {
                self.i += 2;
                return Ok(());
            }
            self.i += 1;
        }
        Err(FrontendDiag::new(
            codes::FE401_UNSUPPORTED_SOL,
            "unterminated block comment",
            start..self.b.len(),
        ))
    }

    /// Skip whitespace + line/block comments (no token emitted). Used to peek from an
    /// `assembly` keyword to its `{ … }` block.
    fn skip_trivia(&mut self) {
        while self.i < self.b.len() {
            let c = self.b[self.i];
            if matches!(c, b' ' | b'\t' | b'\r' | b'\n') {
                self.i += 1;
            } else if c == b'/' && self.peek(1) == Some(b'/') {
                self.skip_line_comment();
            } else if c == b'/' && self.peek(1) == Some(b'*') {
                if self.skip_block_comment().is_err() {
                    return;
                }
            } else {
                return;
            }
        }
    }

    /// Skip a balanced `open`/`close` group starting at `self.i` (which IS `open`), honoring
    /// string + comment contents so a brace/paren inside `"…"`/`'…'`/`/*…*/` does not miscount.
    /// Used to skip an inline-assembly block (and its optional `("flags")` list) wholesale, so
    /// the YUL bytes inside (`:=`, `->`, …) never reach the byte dispatch.
    fn skip_balanced(&mut self, open: u8, close: u8) -> Result<(), FrontendDiag> {
        let start = self.i;
        let mut depth = 0u32;
        while self.i < self.b.len() {
            let c = self.b[self.i];
            if c == b'/' && self.peek(1) == Some(b'/') {
                self.skip_line_comment();
            } else if c == b'/' && self.peek(1) == Some(b'*') {
                self.skip_block_comment()?;
            } else if c == b'"' || c == b'\'' {
                self.skip_quoted(c)?;
            } else if c == open {
                depth += 1;
                self.i += 1;
            } else if c == close {
                depth -= 1;
                self.i += 1;
                if depth == 0 {
                    return Ok(());
                }
            } else {
                self.i += 1;
            }
        }
        Err(FrontendDiag::new(
            codes::FE478_INLINE_ASSEMBLY_SOL,
            "unterminated inline `assembly` block",
            start..self.b.len(),
        ))
    }

    /// Skip a `"…"`/`'…'` string (delimited by `quote`) WITHOUT emitting a token — for skipping
    /// over a string inside an assembly block. Honors `\`-escapes; unterminated → Err.
    fn skip_quoted(&mut self, quote: u8) -> Result<(), FrontendDiag> {
        let start = self.i;
        self.i += 1;
        while self.i < self.b.len() {
            let c = self.b[self.i];
            if c == b'\\' {
                self.i += 2;
            } else if c == quote {
                self.i += 1;
                return Ok(());
            } else {
                self.i += 1;
            }
        }
        Err(FrontendDiag::new(
            codes::FE401_UNSUPPORTED_SOL,
            "unterminated string literal",
            start..self.b.len(),
        ))
    }

    fn lex_number(&mut self) -> Result<(), FrontendDiag> {
        let start = self.i;
        let oob = |s: &Self, st: usize| {
            FrontendDiag::new(
                codes::FE430_BAD_NUMBER_SOL,
                "numeric literal exceeds the u256 range [0, 2^256)",
                st..s.i,
            )
        };
        let text: String = if self.b[self.i] == b'0'
            && matches!(self.peek(1), Some(b'x') | Some(b'X'))
        {
            // Hex `0x…`, with optional `_` digit separators.
            self.i += 2;
            let hs = self.i;
            while self.i < self.b.len()
                && (self.b[self.i].is_ascii_hexdigit() || self.b[self.i] == b'_')
            {
                self.i += 1;
            }
            let hex: String = self.src[hs..self.i].chars().filter(|c| *c != '_').collect();
            if hex.is_empty() {
                return Err(FrontendDiag::new(
                    codes::FE430_BAD_NUMBER_SOL,
                    "hex literal `0x` has no digits",
                    start..self.i,
                ));
            }
            if hex.trim_start_matches('0').len() > 64 {
                return Err(oob(self, start)); // 64 hex digits = 256 bits
            }
            format!("0x{hex}")
        } else {
            // Decimal `<digits>[.<digits>]?[ (e|E) [+]? <digits> ]?`, with `_` separators among
            // the digits. Solidity literals are exact rationals; SOL needs a non-negative
            // INTEGER, so a non-integral form (`0.5`, `2.55e1`) → FE430. `1e18` / `1_000_000` /
            // `2.5e3` (=2500) expand to a plain integer.
            while self.i < self.b.len()
                && (self.b[self.i].is_ascii_digit() || self.b[self.i] == b'_')
            {
                self.i += 1;
            }
            let mut frac_len: i64 = 0;
            if self.peek(0) == Some(b'.') {
                self.i += 1;
                let fs = self.i;
                while self.i < self.b.len()
                    && (self.b[self.i].is_ascii_digit() || self.b[self.i] == b'_')
                {
                    self.i += 1;
                }
                frac_len = self.src[fs..self.i]
                    .bytes()
                    .filter(u8::is_ascii_digit)
                    .count() as i64;
            }
            let mut exp: i64 = 0;
            if matches!(self.peek(0), Some(b'e') | Some(b'E')) {
                self.i += 1;
                if self.peek(0) == Some(b'+') {
                    self.i += 1;
                }
                let es = self.i;
                while self.i < self.b.len() && self.b[self.i].is_ascii_digit() {
                    self.i += 1;
                }
                if self.i == es {
                    return Err(FrontendDiag::new(
                        codes::FE430_BAD_NUMBER_SOL,
                        "scientific-notation exponent has no digits",
                        start..self.i,
                    ));
                }
                exp = self.src[es..self.i].parse::<i64>().unwrap_or(i64::MAX);
            }
            // mantissa = every digit in the int+frac part (`_` and `.` stripped).
            let mantissa: String = self.src[start..self.i]
                .bytes()
                .take_while(|b| *b != b'e' && *b != b'E')
                .filter(u8::is_ascii_digit)
                .map(char::from)
                .collect();
            match expand_pow10(&mantissa, exp - frac_len) {
                Some(t) if u256_decimal_in_range(&t) => t,
                Some(_) => return Err(oob(self, start)),
                None => {
                    return Err(FrontendDiag::new(
                        codes::FE430_BAD_NUMBER_SOL,
                        "numeric literal is not a non-negative integer (a fractional value is unsupported)",
                        start..self.i,
                    ));
                }
            }
        };
        self.out.push(Tok {
            kind: TokKind::Num(text),
            span: start..self.i,
        });
        Ok(())
    }

    /// Scan a `"…"` or `'…'` string literal (delimited by `quote`). Total: handles
    /// `\`-escapes (the escaped byte is skipped, never interpreted) and reports an
    /// unterminated string as FE401. SOL-XFILE: the RAW contents (between the quotes,
    /// escapes uninterpreted, lossy on a non-UTF-8 boundary) are now CARRIED — the only
    /// consumer is `parse_import`'s path capture, which gates the text to an ASCII
    /// charset downstream (so a lossy/escaped literal fails closed there); every other
    /// string use (a dropped `require` reason / SafeMath message) still ignores it.
    fn lex_string(&mut self, quote: u8) -> Result<(), FrontendDiag> {
        let start = self.i;
        self.i += 1; // opening quote
        while self.i < self.b.len() {
            let c = self.b[self.i];
            if c == b'\\' {
                self.i += 2; // skip the escape AND the escaped byte
            } else if c == quote {
                let text = String::from_utf8_lossy(&self.b[start + 1..self.i]).into_owned();
                self.i += 1; // closing quote
                self.out.push(Tok {
                    kind: TokKind::Str(text),
                    span: start..self.i,
                });
                return Ok(());
            } else {
                self.i += 1;
            }
        }
        Err(FrontendDiag::new(
            codes::FE401_UNSUPPORTED_SOL,
            "unterminated string literal",
            start..self.b.len(),
        ))
    }

    fn lex_ident_or_keyword(&mut self) -> Result<(), FrontendDiag> {
        let start = self.i;
        while self.i < self.b.len()
            && (self.b[self.i] == b'_' || self.b[self.i].is_ascii_alphanumeric())
        {
            self.i += 1;
        }
        let word = &self.src[start..self.i];
        if word == "pragma" {
            return self.lex_pragma(start);
        }
        // Inline `assembly [("flags")] { … }` — skip the whole balanced block (its YUL bytes,
        // `:=`/`->`/…, must never reach the byte dispatch as a generic "unexpected byte"); emit
        // one `Assembly` marker the parser rejects (FE478). A bare identifier `assembly` (NOT
        // followed by a block) stays an `Ident`.
        if word == "assembly" {
            let after_kw = self.i;
            self.skip_trivia();
            let mut is_block = self.peek(0) == Some(b'{');
            // The flags form `assembly ("memory-safe") { … }` — only a `(…)` whose first
            // non-trivia byte is a STRING is the flags list. A `(…)` that is a parameter list
            // (`function assembly() { … }`) means `assembly` is an ordinary identifier, NOT a
            // YUL block — so we must NOT skip that function's body as assembly.
            if !is_block && self.peek(0) == Some(b'(') {
                let save = self.i;
                self.i += 1;
                self.skip_trivia();
                let is_flags = matches!(self.peek(0), Some(b'"') | Some(b'\''));
                self.i = save;
                if is_flags {
                    self.skip_balanced(b'(', b')')?;
                    self.skip_trivia();
                    is_block = self.peek(0) == Some(b'{');
                }
            }
            if is_block {
                self.skip_balanced(b'{', b'}')?;
                self.out.push(Tok {
                    kind: TokKind::Assembly,
                    span: start..self.i,
                });
                return Ok(());
            }
            self.i = after_kw; // not a block — fall through to `Ident("assembly")`
        }
        let word = &self.src[start..self.i];
        let kind = match word {
            "contract" => TokKind::Contract,
            "function" => TokKind::Function,
            "returns" => TokKind::Returns,
            "return" => TokKind::Return,
            "require" => TokKind::Require,
            "assert" => TokKind::Assert,
            "revert" => TokKind::Revert,
            "if" => TokKind::If,
            "else" => TokKind::Else,
            "unchecked" => TokKind::Unchecked,
            "public" => TokKind::Public,
            "private" => TokKind::Private,
            "internal" => TokKind::Internal,
            "external" => TokKind::External,
            "view" => TokKind::View,
            "pure" => TokKind::Pure,
            "memory" => TokKind::Memory,
            "storage" => TokKind::Storage,
            "calldata" => TokKind::Calldata,
            "true" => TokKind::True,
            "false" => TokKind::False,
            _ => TokKind::Ident(word.to_string()),
        };
        self.out.push(Tok {
            kind,
            span: start..self.i,
        });
        Ok(())
    }

    /// Capture a `pragma … ;` directive's body (everything after `pragma`, up to
    /// but excluding `;`), trimmed. The version-range check (NC-S3) is in the
    /// checker. `start` is the byte offset of the `pragma` keyword.
    fn lex_pragma(&mut self, start: usize) -> Result<(), FrontendDiag> {
        let body_start = self.i;
        while self.i < self.b.len() && self.b[self.i] != b';' {
            self.i += 1;
        }
        if self.i >= self.b.len() {
            return Err(FrontendDiag::new(
                codes::FE411_UNCHECKED_OR_PRAGMA,
                "unterminated pragma directive (missing `;`)",
                start..self.b.len(),
            ));
        }
        let body = self.src[body_start..self.i].trim().to_string();
        let end = self.i + 1; // include the `;`
        self.out.push(Tok {
            kind: TokKind::Pragma(body),
            span: start..end,
        });
        self.i = end;
        Ok(())
    }
}
