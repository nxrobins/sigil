//! Recursive-descent parser for the FE0 TypeScript policy subset. Totality
//! (threat T12) is guaranteed by an FE0-OWNED depth counter checked *before*
//! each descent — the Rust oracle parser has no such cap, so we must not lean
//! on it. Grammar:
//!
//! ```text
//! program  := function*
//! function := jsdoc? "function" ident "(" params? ")" ":" "number" block
//! params   := param ("," param)*
//! param    := ident ":" "number"
//! block    := "{" "return" expr ";" "}"
//! expr     := term (("+" | "-") term)*
//! term     := factor ("*" factor)*
//! factor   := int | ident | ident "(" args? ")" | "(" expr ")"
//! args     := expr ("," expr)*
//! ```
//!
//! JSDoc policy annotations (in a `/** ... */` immediately preceding a
//! function): `@cap Name(deadline=<int>)`. `@effects` is recognized but deferred
//! (needs the outer ring, which cannot own caps — see the spec) → FE001. Any
//! other `@tag` → FE010 (fail-closed, threat T1).

use std::ops::Range;

use crate::FrontendDiag;
use crate::codes;
use crate::limits;

use super::lexer::{Tok, TokKind};

#[derive(Debug, Clone)]
pub struct TsProgram {
    pub interfaces: Vec<TsInterface>,
    pub functions: Vec<TsFunction>,
}

/// A type annotation: `number` → i64, `boolean` → bool, anything else is a
/// named record (resolved in `check.rs`).
#[derive(Debug, Clone)]
pub struct TsTypeAnn {
    pub name: String,
    pub span: Range<usize>,
}

/// `interface Name { f: T; ... }` → a SIGIL `record`.
#[derive(Debug, Clone)]
pub struct TsInterface {
    pub name: String,
    pub name_span: Range<usize>,
    pub fields: Vec<TsField>,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub struct TsField {
    pub name: String,
    pub name_span: Range<usize>,
    pub ty: TsTypeAnn,
}

#[derive(Debug, Clone)]
pub struct TsFunction {
    pub name: String,
    pub name_span: Range<usize>,
    pub params: Vec<TsParam>,
    pub ret: TsTypeAnn,
    pub caps: Vec<TsCap>,
    /// `None` = no `@effects` tag; `Some(v)` = the tag was present (v may be
    /// empty). Its presence (even empty) selects effect-mode (FE1 / F8).
    pub effects: Option<Vec<TsEffect>>,
    pub body: Vec<TsStmt>,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub struct TsParam {
    pub name: String,
    pub ty: TsTypeAnn,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub enum TsStmt {
    /// `decl_let` = declared with `let` (mutable intent) vs `const`.
    Let {
        name: String,
        name_span: Range<usize>,
        decl_let: bool,
        ann: Option<TsTypeAnn>,
        value: TsExpr,
        span: Range<usize>,
    },
    Assign {
        name: String,
        name_span: Range<usize>,
        value: TsExpr,
        span: Range<usize>,
    },
    Return {
        value: Option<TsExpr>,
        span: Range<usize>,
    },
    If {
        cond: TsExpr,
        then_body: Vec<TsStmt>,
        else_body: Vec<TsStmt>,
        span: Range<usize>,
    },
    While {
        cond: TsExpr,
        body: Vec<TsStmt>,
        span: Range<usize>,
    },
    ExprStmt(TsExpr, Range<usize>),
}

/// A capability requirement parsed from `@cap Name(deadline=<int>)`.
#[derive(Debug, Clone)]
pub struct TsCap {
    pub name: String,
    pub deadline: i64,
    pub span: Range<usize>,
}

/// An effect requirement parsed from `@effects A, B` (FE1).
#[derive(Debug, Clone)]
pub struct TsEffect {
    pub name: String,
    pub span: Range<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone)]
pub enum TsExpr {
    Int(i64, Range<usize>),
    Bool(bool, Range<usize>),
    Var(String, Range<usize>),
    /// `receiver.field` — (receiver, field-name, full span).
    Field(Box<TsExpr>, String, Range<usize>),
    Call(String, Vec<TsExpr>, Range<usize>),
    /// `{ f: v, ... }` — anonymous object literal; its record type is resolved
    /// from the expected type at the construction site (H13).
    Object(Vec<(String, Range<usize>, TsExpr)>, Range<usize>),
    Unary(UnOp, Box<TsExpr>, Range<usize>),
    Bin(BinOp, Box<TsExpr>, Box<TsExpr>, Range<usize>),
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
    depth: u32,
    end: usize,
}

pub fn parse(toks: Vec<Tok>, src_len: usize) -> Result<TsProgram, FrontendDiag> {
    let mut p = Parser {
        toks,
        pos: 0,
        depth: 0,
        end: src_len,
    };
    let mut interfaces = Vec::new();
    let mut functions = Vec::new();
    let mut decls = 0usize;
    while !p.at_end() {
        decls += 1;
        if decls > limits::MAX_FUNCTIONS {
            return Err(FrontendDiag::new(
                codes::FE002_TOO_LARGE,
                format!(
                    "more than {} declarations in one file",
                    limits::MAX_FUNCTIONS
                ),
                p.cur_span(),
            ));
        }
        // An interface carries no leading JSDoc in FE2; a function may.
        if matches!(p.peek(), Some(TokKind::Ident(s)) if s == "interface") {
            interfaces.push(p.parse_interface()?);
        } else {
            functions.push(p.parse_function()?);
        }
    }
    Ok(TsProgram {
        interfaces,
        functions,
    })
}

impl Parser {
    fn at_end(&self) -> bool {
        self.pos >= self.toks.len()
    }

    fn cur_span(&self) -> Range<usize> {
        match self.toks.get(self.pos) {
            Some(t) => t.span.clone(),
            None => self.end..self.end,
        }
    }

    fn peek(&self) -> Option<&TokKind> {
        self.toks.get(self.pos).map(|t| &t.kind)
    }

    fn peek2(&self) -> Option<&TokKind> {
        self.toks.get(self.pos + 1).map(|t| &t.kind)
    }

    fn advance(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn err(&self, code: &'static str, msg: impl Into<String>) -> FrontendDiag {
        FrontendDiag::new(code, msg, self.cur_span())
    }

    /// Recursion/AST-depth guard (threat T12), threaded through EVERY recursive
    /// descent (`parse_stmt`, `parse_unary`) AND every flat operator/postfix loop
    /// (the precedence chain + `.field` postfix, which `enter` once per accumulated
    /// node). A flat chain like `a+a+…` / `a.f.f…` parses in a LOOP at constant
    /// recursion depth but builds an N-deep AST that would otherwise overflow the
    /// native stack in the downstream desugar/check/emit walkers, the FE500 re-parse,
    /// and the recursive `Drop` — so its depth is charged here and rejected (FE002)
    /// before the tree is ever built. `leave` is skipped on the error path: the parse
    /// unwinds on the first error, so the stale counter is never observed.
    fn enter(&mut self) -> Result<(), FrontendDiag> {
        self.depth += 1;
        if self.depth > limits::MAX_DEPTH {
            return Err(self.err(
                codes::FE002_TOO_LARGE,
                format!("nesting exceeds depth {}", limits::MAX_DEPTH),
            ));
        }
        Ok(())
    }

    fn leave(&mut self) {
        self.depth -= 1;
    }

    /// Consume an exact punctuation token or fail (FE001).
    fn expect(&mut self, kind: &TokKind, what: &str) -> Result<Tok, FrontendDiag> {
        match self.peek() {
            Some(k) if k == kind => Ok(self.advance().expect("peeked")),
            _ => Err(self.err(codes::FE001_UNSUPPORTED, format!("expected {what}"))),
        }
    }

    /// Consume a specific word-keyword (`function`/`return`/`number`).
    fn expect_word(&mut self, word: &str) -> Result<Tok, FrontendDiag> {
        match self.peek() {
            Some(TokKind::Ident(s)) if s == word => Ok(self.advance().expect("peeked")),
            _ => Err(self.err(codes::FE001_UNSUPPORTED, format!("expected `{word}`"))),
        }
    }

    /// Consume an identifier that will be EMITTED into SIGIL, rejecting
    /// reserved keywords and the synthetic `__fe_` prefix (threats T7/T8).
    fn expect_emittable_ident(
        &mut self,
        role: &str,
    ) -> Result<(String, Range<usize>), FrontendDiag> {
        let span = self.cur_span();
        let name = match self.peek() {
            Some(TokKind::Ident(s)) => s.clone(),
            _ => return Err(self.err(codes::FE001_UNSUPPORTED, format!("expected {role}"))),
        };
        check_emittable(&name, &span, role)?;
        self.advance();
        Ok((name, span))
    }

    /// A type annotation token: `number`/`boolean`/<RecordName>. Generic args
    /// (`Foo<T>`) and other forms are fail-closed rejected (H20).
    fn parse_type_ann(&mut self, role: &str) -> Result<TsTypeAnn, FrontendDiag> {
        let span = self.cur_span();
        let name = match self.peek() {
            Some(TokKind::Ident(s)) => s.clone(),
            _ => return Err(self.err(codes::FE001_UNSUPPORTED, format!("expected {role}"))),
        };
        self.advance();
        if self.peek() == Some(&TokKind::Lt) {
            return Err(self.err(
                codes::FE320_UNSUPPORTED_TS,
                "generic type arguments are not supported in FE2",
            ));
        }
        Ok(TsTypeAnn { name, span })
    }

    fn parse_interface(&mut self) -> Result<TsInterface, FrontendDiag> {
        let start = self.cur_span().start;
        self.expect_word("interface")?;
        let (name, name_span) = self.expect_emittable_ident("an interface name")?;
        if matches!(self.peek(), Some(TokKind::Ident(s)) if s == "extends") {
            return Err(self.err(
                codes::FE320_UNSUPPORTED_TS,
                "`interface extends` is not supported in FE2",
            ));
        }
        if self.peek() == Some(&TokKind::Lt) {
            return Err(self.err(
                codes::FE320_UNSUPPORTED_TS,
                "generic interfaces are not supported in FE2",
            ));
        }
        self.expect(&TokKind::LBrace, "`{`")?;
        let mut fields = Vec::new();
        while self.peek() != Some(&TokKind::RBrace) {
            if self.at_end() {
                return Err(self.err(codes::FE001_UNSUPPORTED, "unterminated interface"));
            }
            let (fname, fspan) = self.expect_emittable_ident("a field name")?;
            if self.peek() == Some(&TokKind::LParen) {
                return Err(self.err(
                    codes::FE320_UNSUPPORTED_TS,
                    "interface methods are not supported in FE2",
                ));
            }
            self.expect(&TokKind::Colon, "`:` after field name")?;
            let ty = self.parse_type_ann("a field type")?;
            fields.push(TsField {
                name: fname,
                name_span: fspan,
                ty,
            });
            if matches!(self.peek(), Some(TokKind::Semi) | Some(TokKind::Comma)) {
                self.advance();
            }
        }
        let end = self.expect(&TokKind::RBrace, "`}`")?.span.end;
        Ok(TsInterface {
            name,
            name_span,
            fields,
            span: start..end,
        })
    }

    fn parse_function(&mut self) -> Result<TsFunction, FrontendDiag> {
        let start = self.cur_span().start;

        // Optional leading JSDoc carrying policy annotations.
        let mut caps = Vec::new();
        let mut effects: Option<Vec<TsEffect>> = None;
        if let Some(TokKind::JsDoc(text)) = self.peek() {
            let text = text.clone();
            let doc_span = self.cur_span();
            self.advance();
            let (c, e) = parse_jsdoc_annotations(&text, doc_span.start + 3)?;
            caps = c;
            effects = e;
        }

        self.expect_word("function")?;
        let (name, name_span) = self.expect_emittable_ident("a function name")?;

        self.expect(&TokKind::LParen, "`(`")?;
        let mut params = Vec::new();
        if self.peek() != Some(&TokKind::RParen) {
            loop {
                let (pname, pspan) = self.expect_emittable_ident("a parameter name")?;
                self.expect(&TokKind::Colon, "`:` after parameter name")?;
                let ty = self.parse_type_ann("a parameter type")?;
                params.push(TsParam {
                    name: pname,
                    ty,
                    span: pspan,
                });
                if self.peek() == Some(&TokKind::Comma) {
                    self.advance();
                    continue;
                }
                break;
            }
        }
        self.expect(&TokKind::RParen, "`)`")?;
        self.expect(&TokKind::Colon, "`:` before return type")?;
        let ret = self.parse_type_ann("a return type")?;

        let (body, end) = self.parse_block()?;

        Ok(TsFunction {
            name,
            name_span,
            params,
            ret,
            caps,
            effects,
            body,
            span: start..end,
        })
    }

    /// `{ stmt* }` — returns the statements and the byte offset just past `}`.
    fn parse_block(&mut self) -> Result<(Vec<TsStmt>, usize), FrontendDiag> {
        self.expect(&TokKind::LBrace, "`{`")?;
        let mut stmts = Vec::new();
        while self.peek() != Some(&TokKind::RBrace) {
            if self.at_end() {
                return Err(self.err(codes::FE001_UNSUPPORTED, "unterminated block"));
            }
            stmts.push(self.parse_stmt()?);
        }
        let end = self.expect(&TokKind::RBrace, "`}`")?.span.end;
        Ok((stmts, end))
    }

    // Statement-nesting depth guard (threat T12): nested `if`/`while` bodies and
    // `else if` chains recurse through here (via `parse_block` and the `else if`
    // tail), so `enter`/`leave` bounds that recursion against the same `depth`
    // budget as expressions. Without it, deep statement nesting overflowed the
    // native stack in the parser and every downstream walker.
    fn parse_stmt(&mut self) -> Result<TsStmt, FrontendDiag> {
        self.enter()?;
        let result = self.parse_stmt_inner();
        if result.is_ok() {
            self.leave();
        }
        result
    }

    fn parse_stmt_inner(&mut self) -> Result<TsStmt, FrontendDiag> {
        let start = self.cur_span().start;
        match self.peek() {
            Some(TokKind::Ident(s)) if s == "let" || s == "const" => {
                let decl_let = s == "let";
                self.advance();
                let (name, name_span) = self.expect_emittable_ident("a variable name")?;
                let ann = if self.peek() == Some(&TokKind::Colon) {
                    self.advance();
                    Some(self.parse_type_ann("a type")?)
                } else {
                    None
                };
                self.expect(&TokKind::Eq, "`=` in a let/const binding")?;
                let value = self.parse_expr()?;
                let end = self.expect(&TokKind::Semi, "`;`")?.span.end;
                Ok(TsStmt::Let {
                    name,
                    name_span,
                    decl_let,
                    ann,
                    value,
                    span: start..end,
                })
            }
            Some(TokKind::Ident(s)) if s == "return" => {
                self.advance();
                if self.peek() == Some(&TokKind::Semi) {
                    let end = self.expect(&TokKind::Semi, "`;`")?.span.end;
                    Ok(TsStmt::Return {
                        value: None,
                        span: start..end,
                    })
                } else {
                    let value = self.parse_expr()?;
                    let end = self.expect(&TokKind::Semi, "`;`")?.span.end;
                    Ok(TsStmt::Return {
                        value: Some(value),
                        span: start..end,
                    })
                }
            }
            Some(TokKind::Ident(s)) if s == "if" => {
                self.advance();
                self.expect(&TokKind::LParen, "`(` after `if`")?;
                let cond = self.parse_expr()?;
                self.expect(&TokKind::RParen, "`)`")?;
                let (then_body, mut end) = self.parse_block()?;
                let else_body = if matches!(self.peek(), Some(TokKind::Ident(s)) if s == "else") {
                    self.advance();
                    if matches!(self.peek(), Some(TokKind::Ident(s)) if s == "if") {
                        let nested = self.parse_stmt()?;
                        end = stmt_span(&nested).end;
                        vec![nested]
                    } else {
                        let (eb, e) = self.parse_block()?;
                        end = e;
                        eb
                    }
                } else {
                    Vec::new()
                };
                Ok(TsStmt::If {
                    cond,
                    then_body,
                    else_body,
                    span: start..end,
                })
            }
            Some(TokKind::Ident(s)) if s == "while" => {
                self.advance();
                self.expect(&TokKind::LParen, "`(` after `while`")?;
                let cond = self.parse_expr()?;
                self.expect(&TokKind::RParen, "`)`")?;
                let (body, end) = self.parse_block()?;
                Ok(TsStmt::While {
                    cond,
                    body,
                    span: start..end,
                })
            }
            // Assignment: `ident = expr;` (an `==` is an expression statement).
            Some(TokKind::Ident(_)) if matches!(self.peek2(), Some(TokKind::Eq)) => {
                let (name, name_span) = self.expect_emittable_ident("a variable name")?;
                self.expect(&TokKind::Eq, "`=`")?;
                let value = self.parse_expr()?;
                let end = self.expect(&TokKind::Semi, "`;`")?.span.end;
                Ok(TsStmt::Assign {
                    name,
                    name_span,
                    value,
                    span: start..end,
                })
            }
            _ => {
                let e = self.parse_expr()?;
                let end = self
                    .expect(&TokKind::Semi, "`;` after an expression statement")?
                    .span
                    .end;
                Ok(TsStmt::ExprStmt(e, start..end))
            }
        }
    }

    // Expression precedence (low → high): || , && , == != , < <= > >= , + - ,
    // * , unary (! -) , postfix (.field / call) , primary.
    fn parse_expr(&mut self) -> Result<TsExpr, FrontendDiag> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<TsExpr, FrontendDiag> {
        let mut lhs = self.parse_and()?;
        let mut chained = 0u32;
        while self.peek() == Some(&TokKind::PipePipe) {
            self.advance();
            self.enter()?;
            chained += 1;
            let rhs = self.parse_and()?;
            let span = expr_span(&lhs).start..expr_span(&rhs).end;
            lhs = TsExpr::Bin(BinOp::Or, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    fn parse_and(&mut self) -> Result<TsExpr, FrontendDiag> {
        let mut lhs = self.parse_equality()?;
        let mut chained = 0u32;
        while self.peek() == Some(&TokKind::AmpAmp) {
            self.advance();
            self.enter()?;
            chained += 1;
            let rhs = self.parse_equality()?;
            let span = expr_span(&lhs).start..expr_span(&rhs).end;
            lhs = TsExpr::Bin(BinOp::And, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    fn parse_equality(&mut self) -> Result<TsExpr, FrontendDiag> {
        let mut lhs = self.parse_relational()?;
        let mut chained = 0u32;
        while let Some(op) = match self.peek() {
            Some(TokKind::EqEq) => Some(BinOp::Eq),
            Some(TokKind::BangEq) => Some(BinOp::Ne),
            _ => None,
        } {
            self.advance();
            self.enter()?;
            chained += 1;
            let rhs = self.parse_relational()?;
            let span = expr_span(&lhs).start..expr_span(&rhs).end;
            lhs = TsExpr::Bin(op, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    fn parse_relational(&mut self) -> Result<TsExpr, FrontendDiag> {
        let mut lhs = self.parse_additive()?;
        let mut chained = 0u32;
        while let Some(op) = match self.peek() {
            Some(TokKind::Lt) => Some(BinOp::Lt),
            Some(TokKind::LtEq) => Some(BinOp::Le),
            Some(TokKind::Gt) => Some(BinOp::Gt),
            Some(TokKind::GtEq) => Some(BinOp::Ge),
            _ => None,
        } {
            self.advance();
            self.enter()?;
            chained += 1;
            let rhs = self.parse_additive()?;
            let span = expr_span(&lhs).start..expr_span(&rhs).end;
            lhs = TsExpr::Bin(op, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    fn parse_additive(&mut self) -> Result<TsExpr, FrontendDiag> {
        let mut lhs = self.parse_mul()?;
        let mut chained = 0u32;
        while let Some(op) = match self.peek() {
            Some(TokKind::Plus) => Some(BinOp::Add),
            Some(TokKind::Minus) => Some(BinOp::Sub),
            _ => None,
        } {
            self.advance();
            self.enter()?;
            chained += 1;
            let rhs = self.parse_mul()?;
            let span = expr_span(&lhs).start..expr_span(&rhs).end;
            lhs = TsExpr::Bin(op, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    fn parse_mul(&mut self) -> Result<TsExpr, FrontendDiag> {
        let mut lhs = self.parse_unary()?;
        let mut chained = 0u32;
        while self.peek() == Some(&TokKind::Star) {
            self.advance();
            self.enter()?;
            chained += 1;
            let rhs = self.parse_unary()?;
            let span = expr_span(&lhs).start..expr_span(&rhs).end;
            lhs = TsExpr::Bin(BinOp::Mul, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    // Every expression passes through parse_unary, and every expression recursion
    // (parens, call args, object values, unary chains) re-enters it, so the shared
    // `enter`/`leave` depth guard bounds it (threat T12). Statement nesting and flat
    // operator/postfix chains are charged separately (see `parse_stmt` and the
    // precedence loops), all against the same `depth` budget.
    fn parse_unary(&mut self) -> Result<TsExpr, FrontendDiag> {
        self.enter()?;
        let result = self.parse_unary_inner();
        if result.is_ok() {
            self.leave();
        }
        result
    }

    fn parse_unary_inner(&mut self) -> Result<TsExpr, FrontendDiag> {
        let opspan = self.cur_span();
        match self.peek() {
            Some(TokKind::Bang) => {
                self.advance();
                let e = self.parse_unary()?;
                let span = opspan.start..expr_span(&e).end;
                Ok(TsExpr::Unary(UnOp::Not, Box::new(e), span))
            }
            Some(TokKind::Minus) => {
                self.advance();
                let e = self.parse_unary()?;
                let span = opspan.start..expr_span(&e).end;
                Ok(TsExpr::Unary(UnOp::Neg, Box::new(e), span))
            }
            _ => self.parse_postfix(),
        }
    }

    // postfix := primary ( "." field )*
    fn parse_postfix(&mut self) -> Result<TsExpr, FrontendDiag> {
        let mut e = self.parse_primary()?;
        let mut chained = 0u32;
        while self.peek() == Some(&TokKind::Dot) {
            self.advance();
            self.enter()?;
            chained += 1;
            let (field, fspan) = self.expect_emittable_ident("a field name")?;
            let span = expr_span(&e).start..fspan.end;
            e = TsExpr::Field(Box::new(e), field, span);
        }
        self.depth -= chained;
        Ok(e)
    }

    fn parse_primary(&mut self) -> Result<TsExpr, FrontendDiag> {
        let span = self.cur_span();
        match self.peek() {
            Some(TokKind::Int(v)) => {
                let v = *v;
                self.advance();
                Ok(TsExpr::Int(v, span))
            }
            Some(TokKind::Ident(s)) if s == "true" => {
                self.advance();
                Ok(TsExpr::Bool(true, span))
            }
            Some(TokKind::Ident(s)) if s == "false" => {
                self.advance();
                Ok(TsExpr::Bool(false, span))
            }
            Some(TokKind::Ident(_)) => {
                let (name, nspan) = self.expect_emittable_ident("an identifier")?;
                if self.peek() == Some(&TokKind::LParen) {
                    self.advance();
                    let mut args = Vec::new();
                    if self.peek() != Some(&TokKind::RParen) {
                        loop {
                            args.push(self.parse_expr()?);
                            if self.peek() == Some(&TokKind::Comma) {
                                self.advance();
                                continue;
                            }
                            break;
                        }
                    }
                    let end = self.expect(&TokKind::RParen, "`)`")?.span.end;
                    Ok(TsExpr::Call(name, args, nspan.start..end))
                } else {
                    Ok(TsExpr::Var(name, nspan))
                }
            }
            Some(TokKind::LParen) => {
                self.advance();
                let inner = self.parse_expr()?;
                self.expect(&TokKind::RParen, "`)`")?;
                Ok(inner)
            }
            // Object literal `{ f: v, ... }` (its record type is resolved from
            // the construction site's expected type in check.rs).
            Some(TokKind::LBrace) => {
                self.advance();
                let mut fields: Vec<(String, Range<usize>, TsExpr)> = Vec::new();
                if self.peek() != Some(&TokKind::RBrace) {
                    loop {
                        let (fname, fspan) = self.expect_emittable_ident("a field name")?;
                        self.expect(&TokKind::Colon, "`:` after field name")?;
                        let v = self.parse_expr()?;
                        fields.push((fname, fspan, v));
                        if self.peek() == Some(&TokKind::Comma) {
                            self.advance();
                            continue;
                        }
                        break;
                    }
                }
                let end = self.expect(&TokKind::RBrace, "`}`")?.span.end;
                Ok(TsExpr::Object(fields, span.start..end))
            }
            _ => Err(self.err(codes::FE001_UNSUPPORTED, "expected an expression")),
        }
    }
}

pub fn expr_span(e: &TsExpr) -> Range<usize> {
    match e {
        TsExpr::Int(_, s)
        | TsExpr::Bool(_, s)
        | TsExpr::Var(_, s)
        | TsExpr::Field(_, _, s)
        | TsExpr::Call(_, _, s)
        | TsExpr::Object(_, s)
        | TsExpr::Unary(_, _, s)
        | TsExpr::Bin(_, _, _, s) => s.clone(),
    }
}

pub fn stmt_span(s: &TsStmt) -> Range<usize> {
    match s {
        TsStmt::Let { span, .. }
        | TsStmt::Assign { span, .. }
        | TsStmt::Return { span, .. }
        | TsStmt::If { span, .. }
        | TsStmt::While { span, .. } => span.clone(),
        TsStmt::ExprStmt(_, s) => s.clone(),
    }
}

/// Reject an identifier that would be emitted into SIGIL if it is a reserved
/// keyword (FE021) or uses the synthetic `__fe_` prefix (FE021). The lexer
/// already guarantees the charset (FE020).
fn check_emittable(name: &str, span: &Range<usize>, role: &str) -> Result<(), FrontendDiag> {
    if name.starts_with(limits::SYNTH_PREFIX) {
        return Err(FrontendDiag::new(
            codes::FE021_RESERVED_NAME,
            format!(
                "{role} `{name}` uses the reserved `{}` prefix",
                limits::SYNTH_PREFIX
            ),
            span.clone(),
        ));
    }
    if crate::is_sigil_keyword(name) {
        return Err(FrontendDiag::new(
            codes::FE021_RESERVED_NAME,
            format!("{role} `{name}` is a reserved SIGIL keyword"),
            span.clone(),
        ));
    }
    Ok(())
}

/// Parse `@cap Name(deadline=<int>)` and `@effects A, B` tags out of a JSDoc
/// body. `base` is the byte offset of the doc-comment inner text in the original
/// source (for spans). Returns the caps plus the effects (`None` if no
/// `@effects` tag appeared; `Some` — possibly empty — if it did, which selects
/// effect-mode). Any other `@tag` → FE010 (fail-closed, T1).
fn parse_jsdoc_annotations(
    inner: &str,
    base: usize,
) -> Result<(Vec<TsCap>, Option<Vec<TsEffect>>), FrontendDiag> {
    let bytes = inner.as_bytes();
    let mut caps = Vec::new();
    let mut effects: Option<Vec<TsEffect>> = None;
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != b'@' {
            i += 1;
            continue;
        }
        let at = i;
        i += 1;
        // Read the tag word.
        let tag_start = i;
        while i < bytes.len() && bytes[i].is_ascii_alphabetic() {
            i += 1;
        }
        let tag = &inner[tag_start..i];
        let tag_span = base + at..base + i;
        match tag {
            "cap" => {
                let (cap, next) = parse_cap_tag(inner, i, base)?;
                caps.push(cap);
                i = next;
            }
            "effects" => {
                let (mut names, next) = parse_effects_tag(inner, i, base)?;
                // Multiple `@effects` tags merge; presence (even empty) → Some.
                effects.get_or_insert_with(Vec::new).append(&mut names);
                i = next;
            }
            "" => {
                return Err(FrontendDiag::new(
                    codes::FE010_UNKNOWN_ANNOTATION,
                    "bare `@` is not a recognized policy annotation",
                    tag_span,
                ));
            }
            other => {
                return Err(FrontendDiag::new(
                    codes::FE010_UNKNOWN_ANNOTATION,
                    format!(
                        "unrecognized policy annotation `@{other}` (FE0/FE1 recognize `@cap` and `@effects`)"
                    ),
                    tag_span,
                ));
            }
        }
    }
    Ok((caps, effects))
}

/// Parse the remainder of `@effects` starting after the tag: ` A, B, C` on one
/// line. Each name is an emittable identifier that is not a compiler-reserved
/// effect (FE213). Returns the effects and the byte index just past the list.
fn parse_effects_tag(
    inner: &str,
    start: usize,
    base: usize,
) -> Result<(Vec<TsEffect>, usize), FrontendDiag> {
    let b = inner.as_bytes();
    let mut i = start;
    // Spaces / tabs / `*` separate; a newline ends the single-line list.
    let skip_inline_ws = |i: &mut usize| {
        while *i < b.len() && (b[*i] == b' ' || b[*i] == b'\t' || b[*i] == b'*') {
            *i += 1;
        }
    };
    let mut effects = Vec::new();
    let mut expecting_name = false; // set after a comma
    loop {
        skip_inline_ws(&mut i);
        if i >= b.len() || b[i] == b'\n' || b[i] == b'@' {
            if expecting_name {
                return Err(FrontendDiag::new(
                    codes::FE010_UNKNOWN_ANNOTATION,
                    "trailing comma in `@effects` list",
                    base + i..base + i,
                ));
            }
            break;
        }
        if !(b[i].is_ascii_alphabetic() || b[i] == b'_') {
            return Err(FrontendDiag::new(
                codes::FE010_UNKNOWN_ANNOTATION,
                "malformed `@effects` list (expected an effect name)",
                base + i..base + i,
            ));
        }
        let nstart = i;
        while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
            i += 1;
        }
        let name = inner[nstart..i].to_owned();
        let span = base + nstart..base + i;
        if name.len() > limits::MAX_IDENT_BYTES {
            return Err(FrontendDiag::new(
                codes::FE020_BAD_IDENTIFIER,
                format!("effect name exceeds {} bytes", limits::MAX_IDENT_BYTES),
                span,
            ));
        }
        check_emittable(&name, &span, "effect name")?;
        if limits::RESERVED_EFFECTS.contains(&name.as_str()) {
            return Err(FrontendDiag::new(
                codes::FE213_RESERVED_EFFECT,
                format!("effect name `{name}` is reserved by the compiler"),
                span,
            ));
        }
        effects.push(TsEffect { name, span });
        skip_inline_ws(&mut i);
        if i < b.len() && b[i] == b',' {
            i += 1;
            expecting_name = true;
            continue;
        }
        break;
    }
    Ok((effects, i))
}

/// Parse the remainder of `@cap` starting after the tag: ` Name(deadline=<int>)`.
/// Returns the cap and the byte index in `inner` just past `)`.
fn parse_cap_tag(inner: &str, start: usize, base: usize) -> Result<(TsCap, usize), FrontendDiag> {
    let b = inner.as_bytes();
    let mut i = start;
    let skip_ws = |i: &mut usize| {
        while *i < b.len() && (b[*i] == b' ' || b[*i] == b'\t' || b[*i] == b'*') {
            *i += 1;
        }
    };
    skip_ws(&mut i);

    // Capability name (an emittable identifier).
    let name_start = i;
    if i >= b.len() || !(b[i].is_ascii_alphabetic() || b[i] == b'_') {
        return Err(FrontendDiag::new(
            codes::FE010_UNKNOWN_ANNOTATION,
            "`@cap` must be followed by a capability name, e.g. `@cap Net(deadline=2030)`",
            base + start..base + i.max(start),
        ));
    }
    while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
        i += 1;
    }
    let name = inner[name_start..i].to_owned();
    let name_span = base + name_start..base + i;
    if name.len() > limits::MAX_IDENT_BYTES {
        return Err(FrontendDiag::new(
            codes::FE020_BAD_IDENTIFIER,
            format!("capability name exceeds {} bytes", limits::MAX_IDENT_BYTES),
            name_span,
        ));
    }
    check_emittable(&name, &name_span, "capability name")?;

    skip_ws(&mut i);
    if i >= b.len() || b[i] != b'(' {
        return Err(FrontendDiag::new(
            codes::FE010_UNKNOWN_ANNOTATION,
            "`@cap` requires `(deadline=<int>)`",
            name_span,
        ));
    }
    i += 1;
    skip_ws(&mut i);
    // Expect literal `deadline`.
    let kw_start = i;
    while i < b.len() && b[i].is_ascii_alphabetic() {
        i += 1;
    }
    if &inner[kw_start..i] != "deadline" {
        return Err(FrontendDiag::new(
            codes::FE010_UNKNOWN_ANNOTATION,
            "`@cap` parameter must be `deadline=<int>`",
            base + kw_start..base + i,
        ));
    }
    skip_ws(&mut i);
    if i >= b.len() || b[i] != b'=' {
        return Err(FrontendDiag::new(
            codes::FE010_UNKNOWN_ANNOTATION,
            "expected `=` after `deadline`",
            base + i..base + i,
        ));
    }
    i += 1;
    skip_ws(&mut i);
    // A negative deadline cannot be emitted as a SIGIL parametric-cap literal:
    // the SIGIL lexer tokenizes `-1` as Minus + IntLit(1), which the cap-usage
    // parser rejects (T198), and an i64::MIN magnitude overflows the lexer's
    // literal parse (L001). Reject the leading `-` up front with a clean policy
    // code rather than emitting text that would only fail the FE500 self-check.
    let num_start = i;
    if i < b.len() && b[i] == b'-' {
        return Err(FrontendDiag::new(
            codes::FE030_BAD_NUMBER,
            "capability deadline must be a non-negative integer",
            base + i..base + i + 1,
        ));
    }
    let digits_start = i;
    while i < b.len() && b[i].is_ascii_digit() {
        i += 1;
    }
    if digits_start == i {
        return Err(FrontendDiag::new(
            codes::FE030_BAD_NUMBER,
            "expected an integer deadline",
            base + num_start..base + i,
        ));
    }
    // Reject non-plain-decimal continuation (threat T9).
    if i < b.len() && (b[i] == b'.' || b[i] == b'_' || b[i].is_ascii_alphabetic()) {
        return Err(FrontendDiag::new(
            codes::FE030_BAD_NUMBER,
            "deadline must be a plain decimal integer",
            base + num_start..base + i,
        ));
    }
    // Reject a leading zero (`0123`), matching the lexer's literal rule so the
    // annotation path can't silently accept what an expression literal rejects
    // (threat T9 — review gap). The digit run excludes the optional minus.
    if i - digits_start > 1 && b[digits_start] == b'0' {
        return Err(FrontendDiag::new(
            codes::FE030_BAD_NUMBER,
            "deadline may not have a leading zero",
            base + num_start..base + i,
        ));
    }
    let deadline: i64 = inner[num_start..i].parse().map_err(|_| {
        FrontendDiag::new(
            codes::FE030_BAD_NUMBER,
            "deadline is out of i64 range",
            base + num_start..base + i,
        )
    })?;
    skip_ws(&mut i);
    if i >= b.len() || b[i] != b')' {
        return Err(FrontendDiag::new(
            codes::FE010_UNKNOWN_ANNOTATION,
            "expected `)` to close `@cap`",
            base + i..base + i,
        ));
    }
    i += 1;
    Ok((
        TsCap {
            name,
            deadline,
            span: name_span,
        },
        i,
    ))
}
