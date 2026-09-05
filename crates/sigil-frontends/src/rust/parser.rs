//! Recursive-descent parser for the RS0–RS3 Rust subset. Totality (SC-8) is
//! guaranteed by an RS0-OWNED depth counter checked *before* each descent — both
//! expression recursion (`parse_unary`) and block/statement nesting
//! (`parse_block`) increment the SAME counter, so total structural depth is
//! bounded 1:1 (no native-stack overflow). Rust keywords are lexed as `Ident` and
//! matched here by string.
//!
//! Grammar (RS0–RS3c — locals, control flow, structs, enums + `match` + payloads):
//!
//! ```text
//! program    := item*
//! item       := function | struct | enum
//! function   := attr* "pub"? "fn" ident "(" params? ")" "->" type block
//! struct     := "pub"? "struct" ident "{" field ("," field)* ","? "}"   (RS3a)
//! enum       := "pub"? "enum" ident "{" variant ("," variant)* ","? "}" (RS3b/c)
//! variant    := ident ("(" type ("," type)* ","? ")")?     (tuple payload; RS3c)
//! type       := "i64" | "bool" | ident   (a declared struct/enum name)
//! block      := "{" stmt* tail? "}"
//! stmt       := "let" "mut"? ident (":" type)? "=" expr ";"
//!             | ident "=" expr ";"                         (assignment)
//!             | "return" expr ";"
//!             | "if" expr block ("else" (block | if))?
//!             | "while" expr block
//!             | "match" expr "{" arm ("," arm)* ","? "}"   (RS3b, statement)
//! arm        := pattern "=>" expr                          (RS3b, bare-expr only)
//! pattern    := "_" | int | "-" int | "true" | "false"
//!             | ident "::" ident ("(" ident ("," ident)* ")")?   (bindings; RS3c)
//! tail       := expr                                       (block value; no ";")
//! expr       := equality
//! equality   := comparison (("==" | "!=") comparison)*
//! comparison := term (("<" | "<=" | ">" | ">=") term)*
//! term       := factor (("+" | "-") factor)*
//! factor     := unary ("*" unary)*
//! unary      := ("!" | "-") unary | postfix
//! postfix    := primary ("." ident)*                       (field access; RS3a)
//! primary    := int | "true" | "false" | ident | ident "(" args? ")"
//!             | ident "::" ident ("(" args? ")")?          (enum ctor; RS3b/c)
//!             | ident "{" (ident ":" expr ",")* "}"        (struct literal; RS3a)
//!             | "(" expr ")"
//! args       := expr ("," expr)* ","?
//! ```

use std::ops::Range;

use crate::FrontendDiag;
use crate::codes;
use crate::limits;

use super::lexer::{Tok, TokKind};

#[derive(Debug, Clone)]
pub struct RsProgram {
    pub functions: Vec<RsFunction>,
    /// `struct Name { … }` declarations → SIGIL `record`s (RS3a).
    pub structs: Vec<RsStruct>,
    /// `enum Name { A, B, … }` declarations → SIGIL `enum`s (RS3b; dataless).
    pub enums: Vec<RsEnum>,
}

/// A type annotation — RS0 admits only `i64` and `bool` (else FE610).
#[derive(Debug, Clone)]
pub struct RsType {
    pub name: String,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub struct RsParam {
    pub name: String,
    pub name_span: Range<usize>,
    pub ty: RsType,
}

/// A `struct Name { f: T, … }` → a SIGIL `record` (RS3). Named-field structs
/// only; tuple/unit/empty/generic structs are rejected (FE641). An optional
/// `#[sigil::invariant(<clause>)]` (RS4b) becomes a record `where` clause.
#[derive(Debug, Clone)]
pub struct RsStruct {
    pub name: String,
    pub name_span: Range<usize>,
    pub fields: Vec<RsField>,
    /// `#[sigil::invariant(<field> <op> <rhs>)]` (RS4b): a construction-enforced
    /// record refinement (literal or cross-field RHS), or `None`.
    pub invariant: Option<RsInvariant>,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub struct RsField {
    pub name: String,
    pub name_span: Range<usize>,
    pub ty: RsType,
}

/// An `enum Name { A, B(T), … }` → a SIGIL `enum` (RS3b/RS3c). Variants may carry
/// positional tuple payloads (`A(T1, …, Tn)`; RS3c) or be dataless. A generic enum,
/// a named struct-variant (`A { x: T }`), or an empty enum is rejected (FE650).
#[derive(Debug, Clone)]
pub struct RsEnum {
    pub name: String,
    pub name_span: Range<usize>,
    pub variants: Vec<RsVariant>,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub struct RsVariant {
    pub name: String,
    pub name_span: Range<usize>,
    /// Positional payload field types (`A(i64, bool)` → `[i64, bool]`); empty for a
    /// dataless variant (RS3c).
    pub payloads: Vec<RsType>,
}

/// A capability requirement from `#[sigil::cap(Name, deadline = <int>)]` (RS1).
#[derive(Debug, Clone)]
pub struct RsCap {
    pub name: String,
    pub deadline: i64,
    pub span: Range<usize>,
}

/// An effect from `#[sigil::effects(A, B)]` (RS2).
#[derive(Debug, Clone)]
pub struct RsEffect {
    pub name: String,
    pub span: Range<usize>,
}

/// A comparison operator in a refinement predicate (RS4a). Emits 1:1 to SIGIL.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefineOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl RefineOp {
    pub fn as_str(self) -> &'static str {
        match self {
            RefineOp::Lt => "<",
            RefineOp::Le => "<=",
            RefineOp::Gt => ">",
            RefineOp::Ge => ">=",
            RefineOp::Eq => "==",
            RefineOp::Ne => "!=",
        }
    }
}

/// A `#[sigil::requires(<param> <op> <lit>)]` refinement precondition (RS4a) →
/// a SIGIL param-`where` clause. Exactly one clause; `rhs` is a non-negative i64
/// literal (SR-1). The param membership is checked at type-check (FE661).
#[derive(Debug, Clone)]
pub struct RsRequire {
    pub param: String,
    pub op: RefineOp,
    pub rhs: i64,
    pub span: Range<usize>,
}

/// The right-hand side of a struct-invariant clause (RS4b): a non-negative i64
/// literal, or another field of the same struct (cross-field, e.g. `lo <= hi`).
#[derive(Debug, Clone)]
pub enum RsInvRhs {
    Literal(i64),
    Field(String),
}

/// A `#[sigil::invariant(<field> <op> <rhs>)]` record refinement (RS4b) → a SIGIL
/// record `where` clause, enforced at construction. One clause; the field(s) are
/// validated at type-check (FE660/FE661).
#[derive(Debug, Clone)]
pub struct RsInvariant {
    pub field: String,
    pub op: RefineOp,
    pub rhs: RsInvRhs,
    pub span: Range<usize>,
}

/// An information-flow taint level (RS5a). `@SecretCT` (constant-time) is deferred
/// (AG-T1) → an unrepresentable variant here; the parser rejects it at FE670.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaintLevel {
    Public,
    Internal,
    Secret,
}

impl TaintLevel {
    /// The exact SIGIL `@Label` name (case-sensitive — SIGIL's parser is; SR-T8).
    pub fn as_str(self) -> &'static str {
        match self {
            TaintLevel::Public => "Public",
            TaintLevel::Internal => "Internal",
            TaintLevel::Secret => "Secret",
        }
    }
}

/// A `#[sigil::taint]` target: the return, or a named parameter (RS5a).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RsTaintSel {
    Ret,
    Param(String),
}

/// A `#[sigil::taint(<target> = <Level>, …)]` annotation (RS5a) → SIGIL `@Label`
/// qualifiers on the emitted signature. One attribute per function; targets are
/// validated (param membership + scalar type) at type-check (FE670/FE671).
#[derive(Debug, Clone)]
pub struct RsTaint {
    pub targets: Vec<(RsTaintSel, TaintLevel, Range<usize>)>,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub struct RsFunction {
    pub name: String,
    pub name_span: Range<usize>,
    pub is_pub: bool,
    /// `#[sigil::cap(Name, deadline = D)]` capabilities the function requires
    /// (RS1); each is threaded (moved) into a terminal consumer at emit.
    pub caps: Vec<RsCap>,
    /// `#[sigil::effects(A, B)]` (RS2): `None` = no effects attribute (cap-mode /
    /// RS0); `Some(v)` = present (v may be empty), selecting effect-mode (outer
    /// ring). Its presence — even empty — chooses effect-mode for the whole file.
    pub effects: Option<Vec<RsEffect>>,
    /// `#[sigil::requires(<param> <op> <lit>)]` (RS4a): one param-precondition
    /// clause, or `None`. Emitted as a SIGIL `where` clause; Z3 discharges it.
    pub requires: Option<RsRequire>,
    /// `#[sigil::taint(<target> = <Level>, …)]` (RS5a): information-flow `@Label`
    /// qualifiers on params/return, or `None`. `taint_check` (always-on) enforces.
    pub taints: Option<RsTaint>,
    /// RS5b: the number of `declassify(...)` calls in the body — one synthetic
    /// `Declassify` cap parameter per call (SR-B4). Each `RsExpr::Declassify` carries
    /// its own index `0..n_declassify`.
    pub n_declassify: usize,
    pub params: Vec<RsParam>,
    pub ret: RsType,
    pub body: RsBlock,
    pub span: Range<usize>,
}

/// A `{ … }` block: zero or more statements and an optional trailing value
/// expression (Rust's block value). For the function body the tail is the return
/// value; for an `if`/`while` body a tail is rejected (FE690).
#[derive(Debug, Clone)]
pub struct RsBlock {
    pub stmts: Vec<RsStmt>,
    pub tail: Option<RsExpr>,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub enum RsStmt {
    Let {
        name: String,
        name_span: Range<usize>,
        is_mut: bool,
        /// Optional explicit type annotation (`let x: i64 = …`); absent → the
        /// binding's type is inferred from the initializer (as SIGIL does).
        ann: Option<RsType>,
        value: RsExpr,
        span: Range<usize>,
    },
    Assign {
        name: String,
        name_span: Range<usize>,
        value: RsExpr,
        span: Range<usize>,
    },
    Return {
        value: Option<RsExpr>,
        span: Range<usize>,
    },
    If {
        cond: RsExpr,
        then_block: RsBlock,
        else_block: Option<RsBlock>,
        span: Range<usize>,
    },
    While {
        cond: RsExpr,
        body: RsBlock,
        span: Range<usize>,
    },
    /// `match scrut { pat => expr, … }` (RS3b). A statement (SIGIL match is a
    /// statement); each arm's value lowers to `pat => { return <value>; }`. Only
    /// bare-expression arms are supported — a block-bodied arm is FE652.
    Match {
        scrutinee: RsExpr,
        arms: Vec<RsMatchArm>,
        span: Range<usize>,
    },
}

/// One `match` arm: `pattern => value` (RS3b). The value is a bare expression
/// lowered to `{ return <value>; }` at emit — so every arm returns, and a match
/// contributes to the return-path iff it is exhaustive.
#[derive(Debug, Clone)]
pub struct RsMatchArm {
    pub pattern: RsPattern,
    pub value: RsExpr,
    pub span: Range<usize>,
}

/// A `match` arm pattern (RS3b/RS3c). Guards / ranges / bare-identifier bindings
/// are FE652.
#[derive(Debug, Clone)]
pub enum RsPattern {
    /// `Name::Variant` or `Name::Variant(b1, …, bn)` — an enum-variant pattern; the
    /// bindings (RS3c) capture the variant's positional payloads into the arm scope.
    Variant {
        enum_name: String,
        variant: String,
        bindings: Vec<(String, Range<usize>)>,
        span: Range<usize>,
    },
    Int(i64, Range<usize>),
    Bool(bool, Range<usize>),
    /// `_` — the catch-all.
    Wildcard(Range<usize>),
}

impl RsPattern {
    pub fn span(&self) -> Range<usize> {
        match self {
            RsPattern::Variant { span, .. }
            | RsPattern::Int(_, span)
            | RsPattern::Bool(_, span)
            | RsPattern::Wildcard(span) => span.clone(),
        }
    }
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone)]
pub enum RsExpr {
    Int(i64, Range<usize>),
    Bool(bool, Range<usize>),
    Var(String, Range<usize>),
    Call(String, Vec<RsExpr>, Range<usize>),
    Unary(UnOp, Box<RsExpr>, Range<usize>),
    Bin(BinOp, Box<RsExpr>, Box<RsExpr>, Range<usize>),
    /// `Name { f: e, … }` (RS3): struct name + (field, value, field-span) pairs.
    StructLit(String, Vec<(String, RsExpr, Range<usize>)>, Range<usize>),
    /// `e.f` field access (RS3).
    Field(Box<RsExpr>, String, Range<usize>),
    /// `Name::Variant` or `Name::Variant(e1, …, en)` — enum construction (RS3b/c):
    /// enum name, variant, and positional payload arguments (empty if dataless).
    EnumCtor(String, String, Vec<RsExpr>, Range<usize>),
    /// `declassify(value)` — the RS5b information-flow escape hatch. Recognized at
    /// parse from a `Call("declassify", [value])` (arity 1, SR-B1). The `usize` is a
    /// per-function cap index `0..n` (assigned at parse); the linear `Cap<Declassify>`
    /// is NOT in the Rust surface — the emitter synthesizes a fresh one per call
    /// (AG-B6). Lowers to SIGIL `declassify(value, __fe_declassify_cap_<idx>)`.
    Declassify(Box<RsExpr>, usize, Range<usize>),
}

/// The stored span of an expression node (total over all variants).
pub fn expr_span(e: &RsExpr) -> Range<usize> {
    match e {
        RsExpr::Int(_, s)
        | RsExpr::Bool(_, s)
        | RsExpr::Var(_, s)
        | RsExpr::Call(_, _, s)
        | RsExpr::Unary(_, _, s)
        | RsExpr::Bin(_, _, _, s)
        | RsExpr::StructLit(_, _, s)
        | RsExpr::Field(_, _, s)
        | RsExpr::EnumCtor(_, _, _, s)
        | RsExpr::Declassify(_, _, s) => s.clone(),
    }
}

/// The stored span of a statement node.
pub fn stmt_span(s: &RsStmt) -> Range<usize> {
    match s {
        RsStmt::Let { span, .. }
        | RsStmt::Assign { span, .. }
        | RsStmt::Return { span, .. }
        | RsStmt::If { span, .. }
        | RsStmt::While { span, .. }
        | RsStmt::Match { span, .. } => span.clone(),
    }
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
    depth: u32,
    end: usize,
    /// Suppress `Name { … }` struct-literal parsing (RS3). Set while parsing an
    /// `if`/`while` condition, where `{` opens the body block — Rust's
    /// no-struct-literal-in-condition rule; lifted inside `( … )` / call args /
    /// field values.
    no_struct_lit: bool,
    /// RS5b: a per-function counter assigning each `declassify(...)` a stable cap
    /// index `0..n`. Reset at the top of `parse_function`; the final value becomes
    /// the function's `n_declassify` (the number of synthetic `Declassify` caps the
    /// emitter provisions — one per call, SR-B4). Keeps `emit_expr` stateless.
    declassify_idx: usize,
}

pub fn parse(toks: Vec<Tok>, src_len: usize) -> Result<RsProgram, FrontendDiag> {
    let mut p = Parser {
        toks,
        pos: 0,
        depth: 0,
        end: src_len,
        no_struct_lit: false,
        declassify_idx: 0,
    };
    let mut functions = Vec::new();
    let mut structs = Vec::new();
    let mut enums = Vec::new();
    while p.pos < p.toks.len() {
        if functions.len() + structs.len() + enums.len() >= limits::MAX_FUNCTIONS {
            return Err(FrontendDiag::new(
                codes::FE602_TOO_LARGE_RS,
                format!(
                    "more than {} top-level items in one file",
                    limits::MAX_FUNCTIONS
                ),
                p.cur_span(),
            ));
        }
        // Leading attributes are collected here (RS4b), so they may precede a
        // `struct` (an invariant) as well as a `fn`. Each item parser interprets
        // only the attrs valid on it and rejects the rest.
        let attrs = p.collect_attrs()?;
        if p.at_struct_item() {
            structs.push(p.parse_struct(attrs)?);
        } else if p.at_enum_item() {
            enums.push(p.parse_enum(attrs)?);
        } else {
            functions.push(p.parse_function(attrs)?);
        }
    }
    if functions.is_empty() {
        return Err(FrontendDiag::new(
            codes::FE601_UNSUPPORTED_RS,
            "no functions found (RS0 accepts a file of top-level `fn` declarations)",
            0..src_len,
        ));
    }
    Ok(RsProgram {
        functions,
        structs,
        enums,
    })
}

impl Parser {
    fn cur_span(&self) -> Range<usize> {
        self.toks
            .get(self.pos)
            .map(|t| t.span.clone())
            .unwrap_or(self.end..self.end)
    }

    fn at(&self, want: &TokKind) -> bool {
        self.toks
            .get(self.pos)
            .map(|t| &t.kind == want)
            .unwrap_or(false)
    }

    fn at_struct_item(&self) -> bool {
        // A struct item is `struct …` or `pub struct …`. An attribute (which only
        // precedes a function in RS1/RS2) takes the function path.
        let idx = if self.ident_is("pub") {
            self.pos + 1
        } else {
            self.pos
        };
        matches!(self.toks.get(idx), Some(Tok { kind: TokKind::Ident(n), .. }) if n == "struct")
    }

    fn at_enum_item(&self) -> bool {
        // An enum item is `enum …` or `pub enum …` (attributes take the fn path).
        let idx = if self.ident_is("pub") {
            self.pos + 1
        } else {
            self.pos
        };
        matches!(self.toks.get(idx), Some(Tok { kind: TokKind::Ident(n), .. }) if n == "enum")
    }

    fn ident_is(&self, s: &str) -> bool {
        matches!(self.toks.get(self.pos), Some(Tok { kind: TokKind::Ident(n), .. }) if n == s)
    }

    fn eat_keyword(&mut self, kw: &str) -> bool {
        if self.ident_is(kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, want: &TokKind, msg: &str) -> Result<Range<usize>, FrontendDiag> {
        match self.toks.get(self.pos) {
            Some(t) if &t.kind == want => {
                let s = t.span.clone();
                self.pos += 1;
                Ok(s)
            }
            _ => Err(FrontendDiag::new(
                codes::FE601_UNSUPPORTED_RS,
                msg.to_string(),
                self.cur_span(),
            )),
        }
    }

    fn expect_name(&mut self, what: &str) -> Result<(String, Range<usize>), FrontendDiag> {
        match self.toks.get(self.pos) {
            Some(Tok {
                kind: TokKind::Ident(n),
                span,
            }) => {
                let r = (n.clone(), span.clone());
                self.pos += 1;
                Ok(r)
            }
            _ => Err(FrontendDiag::new(
                codes::FE601_UNSUPPORTED_RS,
                format!("expected {what}"),
                self.cur_span(),
            )),
        }
    }

    /// Consume the run of leading `#[ … ]` attributes at the cursor and parse each
    /// (RS4b: collected here, before item dispatch, so an attribute may precede a
    /// `struct` as well as a `fn`). The item parser interprets only its own attrs.
    fn collect_attrs(&mut self) -> Result<Vec<(ParsedAttr, Range<usize>)>, FrontendDiag> {
        let mut out = Vec::new();
        // Clone the whole `TokKind` so the borrow of `self.toks` ends before `pos`
        // moves (a `while let` binding `&inner` would hold it).
        while let Some(TokKind::Attr(inner)) = self.toks.get(self.pos).map(|t| t.kind.clone()) {
            let span = self.cur_span();
            self.pos += 1;
            out.push((parse_attr(&inner, span.clone())?, span));
        }
        Ok(out)
    }

    fn parse_function(
        &mut self,
        attrs: Vec<(ParsedAttr, Range<usize>)>,
    ) -> Result<RsFunction, FrontendDiag> {
        let start = attrs
            .first()
            .map(|(_, s)| s.start)
            .unwrap_or_else(|| self.cur_span().start);
        // `#[sigil::cap]` (RS1), `#[sigil::effects]` (RS2), `#[sigil::requires]`
        // (RS4a), `#[sigil::taint]` (RS5a). `#[sigil::invariant]` is struct-only.
        let mut caps = Vec::new();
        let mut effects: Option<Vec<RsEffect>> = None;
        let mut requires: Option<RsRequire> = None;
        let mut taints: Option<RsTaint> = None;
        for (attr, span) in attrs {
            match attr {
                ParsedAttr::Cap(c) => caps.push(c),
                ParsedAttr::Effects(es) => effects.get_or_insert_with(Vec::new).extend(es),
                ParsedAttr::Require(r) => {
                    // Exactly one `#[sigil::requires]` per function in RS4a (AG-2).
                    if requires.is_some() {
                        return Err(FrontendDiag::new(
                            codes::FE660_BAD_REFINEMENT_RS,
                            "more than one `#[sigil::requires]` on a function is deferred (RS4a \
                             admits a single clause)",
                            span,
                        ));
                    }
                    requires = Some(r);
                }
                ParsedAttr::Taint(t) => {
                    // Exactly one `#[sigil::taint]` per function (SR-T3).
                    if taints.is_some() {
                        return Err(FrontendDiag::new(
                            codes::FE670_BAD_TAINT_RS,
                            "more than one `#[sigil::taint]` on a function is deferred (RS5a \
                             admits a single attribute; combine targets in one)",
                            span,
                        ));
                    }
                    taints = Some(t);
                }
                ParsedAttr::Invariant(_) => {
                    return Err(FrontendDiag::new(
                        codes::FE660_BAD_REFINEMENT_RS,
                        "`#[sigil::invariant]` is only valid on a `struct`, not a function",
                        span,
                    ));
                }
            }
        }
        let is_pub = self.eat_keyword("pub");
        if !self.eat_keyword("fn") {
            return Err(FrontendDiag::new(
                codes::FE601_UNSUPPORTED_RS,
                "expected `fn` (RS0 accepts only top-level function declarations; \
                 `struct`/`enum`/`impl`/`trait`/`use`/`mod`/`const`/macros are out-of-subset)",
                self.cur_span(),
            ));
        }
        let (name, name_span) = self.expect_name("a function name")?;
        self.expect(&TokKind::LParen, "expected `(` after the function name")?;
        let params = self.parse_params()?;
        self.expect(&TokKind::RParen, "expected `)` to close the parameter list")?;
        self.expect(
            &TokKind::Arrow,
            "RS0 requires an explicit `-> i64` or `-> bool` return type (unit functions arrive later)",
        )?;
        let ret = self.parse_type()?;
        // RS5b: reset the per-function declassify counter, then parse the body; the
        // final value is this function's synthetic-cap count (SR-B4).
        self.declassify_idx = 0;
        let body = self.parse_block()?;
        let n_declassify = self.declassify_idx;
        let end = body.span.end;
        Ok(RsFunction {
            name,
            name_span,
            is_pub,
            caps,
            effects,
            requires,
            taints,
            n_declassify,
            params,
            ret,
            body,
            span: start..end,
        })
    }

    fn parse_struct(
        &mut self,
        attrs: Vec<(ParsedAttr, Range<usize>)>,
    ) -> Result<RsStruct, FrontendDiag> {
        let start = attrs
            .first()
            .map(|(_, s)| s.start)
            .unwrap_or_else(|| self.cur_span().start);
        // A struct admits only `#[sigil::invariant]` (RS4b); cap/effects/requires
        // are function-only → fail-closed here.
        let mut invariant: Option<RsInvariant> = None;
        for (attr, span) in attrs {
            match attr {
                ParsedAttr::Invariant(inv) => {
                    if invariant.is_some() {
                        return Err(FrontendDiag::new(
                            codes::FE660_BAD_REFINEMENT_RS,
                            "more than one `#[sigil::invariant]` on a struct is deferred (RS4b \
                             admits a single clause)",
                            span,
                        ));
                    }
                    invariant = Some(inv);
                }
                ParsedAttr::Taint(_) => {
                    return Err(FrontendDiag::new(
                        codes::FE670_BAD_TAINT_RS,
                        "`#[sigil::taint]` is only valid on a function, not a `struct` (per-field \
                         record taint is deferred, AG-T5)",
                        span,
                    ));
                }
                _ => {
                    return Err(FrontendDiag::new(
                        codes::FE660_BAD_REFINEMENT_RS,
                        "only `#[sigil::invariant]` is valid on a `struct` (cap/effects/requires \
                         are function-only)",
                        span,
                    ));
                }
            }
        }
        // Visibility is ignored — SIGIL `record`s are ring-agnostic (no `pub`).
        self.eat_keyword("pub");
        self.eat_keyword("struct"); // guaranteed by `at_struct_item`
        let (name, name_span) = self.expect_name("a struct name")?;
        // Reject unsupported shapes up front (FE641): generics, tuple/unit structs.
        if self.at(&TokKind::Lt) {
            return Err(FrontendDiag::new(
                codes::FE641_BAD_STRUCT_SHAPE_RS,
                "generic structs are not supported in RS0",
                name_span,
            ));
        }
        if self.at(&TokKind::LParen) {
            return Err(FrontendDiag::new(
                codes::FE641_BAD_STRUCT_SHAPE_RS,
                "tuple structs (`struct P(…)`) are not supported in RS0 (use named fields)",
                name_span,
            ));
        }
        if self.at(&TokKind::Semi) {
            return Err(FrontendDiag::new(
                codes::FE641_BAD_STRUCT_SHAPE_RS,
                "unit structs (`struct U;`) are not supported in RS0",
                name_span,
            ));
        }
        self.expect(&TokKind::LBrace, "expected `{` to open the struct fields")?;
        if self.at(&TokKind::RBrace) {
            return Err(FrontendDiag::new(
                codes::FE641_BAD_STRUCT_SHAPE_RS,
                "empty structs (`struct E {}`) are not supported in RS0",
                self.cur_span(),
            ));
        }
        let mut fields = Vec::new();
        loop {
            let (fname, fname_span) = self.expect_name("a field name")?;
            self.expect(&TokKind::Colon, "expected `:` after the field name")?;
            let ty = self.parse_type()?;
            fields.push(RsField {
                name: fname,
                name_span: fname_span,
                ty,
            });
            if self.at(&TokKind::Comma) {
                self.pos += 1;
                if self.at(&TokKind::RBrace) {
                    break; // trailing comma
                }
                continue;
            }
            break;
        }
        let close = self.expect(&TokKind::RBrace, "expected `}` to close the struct")?;
        Ok(RsStruct {
            name,
            name_span,
            fields,
            invariant,
            span: start..close.end,
        })
    }

    /// `enum Name { A, B, … }` — dataless (C-like) variants only. A generic enum,
    /// a payload variant (`A(i64)`), a struct-variant (`A { … }`), or an empty
    /// enum is rejected (FE650).
    fn parse_enum(
        &mut self,
        attrs: Vec<(ParsedAttr, Range<usize>)>,
    ) -> Result<RsEnum, FrontendDiag> {
        // Attributes on an enum are deferred (no invariant/cap/effects on enums yet).
        if let Some((attr, span)) = attrs.into_iter().next() {
            let (code, msg) = match attr {
                ParsedAttr::Taint(_) => (
                    codes::FE670_BAD_TAINT_RS,
                    "`#[sigil::taint]` is only valid on a function, not an `enum`",
                ),
                _ => (
                    codes::FE660_BAD_REFINEMENT_RS,
                    "attributes on an `enum` are not supported (`#[sigil::invariant]` is struct-only)",
                ),
            };
            return Err(FrontendDiag::new(code, msg, span));
        }
        let start = self.cur_span().start;
        self.eat_keyword("pub"); // visibility ignored (SIGIL enums are ring-agnostic)
        self.eat_keyword("enum"); // guaranteed by `at_enum_item`
        let (name, name_span) = self.expect_name("an enum name")?;
        if self.at(&TokKind::Lt) {
            return Err(FrontendDiag::new(
                codes::FE650_BAD_ENUM_SHAPE_RS,
                "generic enums are not supported in RS3b",
                name_span,
            ));
        }
        self.expect(&TokKind::LBrace, "expected `{` to open the enum variants")?;
        if self.at(&TokKind::RBrace) {
            return Err(FrontendDiag::new(
                codes::FE650_BAD_ENUM_SHAPE_RS,
                "empty enums (`enum E {}`) are not supported in RS3b",
                self.cur_span(),
            ));
        }
        let mut variants = Vec::new();
        loop {
            let (vname, vname_span) = self.expect_name("a variant name")?;
            // A positional tuple payload `A(T1, …, Tn)` (RS3c); a named struct-variant
            // `A { … }` is a different shape, still deferred (FE650).
            let mut payloads = Vec::new();
            if self.at(&TokKind::LParen) {
                self.pos += 1; // consume `(`
                if self.at(&TokKind::RParen) {
                    return Err(FrontendDiag::new(
                        codes::FE650_BAD_ENUM_SHAPE_RS,
                        format!(
                            "empty payload `{vname}()` is not supported (use `{vname}` for a dataless variant)"
                        ),
                        vname_span,
                    ));
                }
                loop {
                    payloads.push(self.parse_type()?);
                    if self.at(&TokKind::Comma) {
                        self.pos += 1;
                        if self.at(&TokKind::RParen) {
                            break; // trailing comma
                        }
                        continue;
                    }
                    break;
                }
                self.expect(
                    &TokKind::RParen,
                    "expected `)` to close the variant payload",
                )?;
            } else if self.at(&TokKind::LBrace) {
                return Err(FrontendDiag::new(
                    codes::FE650_BAD_ENUM_SHAPE_RS,
                    format!(
                        "named struct-variant `{vname} {{ … }}` is not supported in RS3c (use a tuple variant `{vname}(…)`)"
                    ),
                    vname_span,
                ));
            }
            variants.push(RsVariant {
                name: vname,
                name_span: vname_span,
                payloads,
            });
            if self.at(&TokKind::Comma) {
                self.pos += 1;
                if self.at(&TokKind::RBrace) {
                    break; // trailing comma
                }
                continue;
            }
            break;
        }
        let close = self.expect(&TokKind::RBrace, "expected `}` to close the enum")?;
        Ok(RsEnum {
            name,
            name_span,
            variants,
            span: start..close.end,
        })
    }

    fn parse_params(&mut self) -> Result<Vec<RsParam>, FrontendDiag> {
        let mut params = Vec::new();
        if self.at(&TokKind::RParen) {
            return Ok(params);
        }
        loop {
            if self.ident_is("mut") {
                return Err(FrontendDiag::new(
                    codes::FE601_UNSUPPORTED_RS,
                    "`mut` parameters are deferred in RS0",
                    self.cur_span(),
                ));
            }
            let (name, name_span) = self.expect_name("a parameter name")?;
            self.expect(&TokKind::Colon, "expected `:` after the parameter name")?;
            let ty = self.parse_type()?;
            params.push(RsParam {
                name,
                name_span,
                ty,
            });
            if self.at(&TokKind::Comma) {
                self.pos += 1;
                if self.at(&TokKind::RParen) {
                    break; // trailing comma
                }
                continue;
            }
            break;
        }
        Ok(params)
    }

    fn parse_type(&mut self) -> Result<RsType, FrontendDiag> {
        let span = self.cur_span();
        match self.toks.get(self.pos).map(|t| &t.kind) {
            Some(TokKind::Ident(n)) => {
                let name = n.clone();
                self.pos += 1;
                // A generic type application `Name<…>` is deferred (RS0 has no
                // generics). The named type is otherwise `i64`/`bool`/a struct
                // name — the checker validates it is declared (else FE610).
                if self.at(&TokKind::Lt) {
                    return Err(FrontendDiag::new(
                        codes::FE601_UNSUPPORTED_RS,
                        format!("generic type application `{name}<…>` is not supported in RS0"),
                        span,
                    ));
                }
                Ok(RsType { name, span })
            }
            _ => Err(FrontendDiag::new(
                codes::FE610_UNSUPPORTED_TYPE_RS,
                "expected a type annotation (`i64`, `bool`, or a struct name)",
                span,
            )),
        }
    }

    /// `{ stmt* tail? }`. Increments the shared depth counter (SC-8) so nested
    /// blocks (`if`/`while` bodies) cannot overflow the native stack.
    fn parse_block(&mut self) -> Result<RsBlock, FrontendDiag> {
        self.depth += 1;
        if self.depth > limits::MAX_DEPTH {
            return Err(FrontendDiag::new(
                codes::FE602_TOO_LARGE_RS,
                format!("block nesting exceeds depth {}", limits::MAX_DEPTH),
                self.cur_span(),
            ));
        }
        let open = self.expect(&TokKind::LBrace, "expected `{` to open a block")?;
        let mut stmts = Vec::new();
        let mut tail = None;

        while !self.at(&TokKind::RBrace) {
            if self.pos >= self.toks.len() {
                return Err(FrontendDiag::new(
                    codes::FE601_UNSUPPORTED_RS,
                    "unexpected end of input inside a block (missing `}`)",
                    self.cur_span(),
                ));
            }
            let head = match self.toks.get(self.pos).map(|t| &t.kind) {
                Some(TokKind::Ident(n)) => Some(n.clone()),
                _ => None,
            };
            match head.as_deref() {
                Some("let") => stmts.push(self.parse_let()?),
                Some("return") => stmts.push(self.parse_return()?),
                Some("if") => stmts.push(self.parse_if()?),
                Some("while") => stmts.push(self.parse_while()?),
                Some("match") => stmts.push(self.parse_match()?),
                Some("for") | Some("loop") | Some("break") | Some("continue") | Some("unsafe") => {
                    return Err(FrontendDiag::new(
                        codes::FE601_UNSUPPORTED_RS,
                        format!(
                            "`{}` is not supported in RS0 (control-flow beyond `if`/`while`/`match` is deferred)",
                            head.as_deref().unwrap()
                        ),
                        self.cur_span(),
                    ));
                }
                _ => {
                    // Assignment `ident = expr;` (a single `=`, not `==`), else a
                    // trailing value expression.
                    let is_assign = matches!(
                        self.toks.get(self.pos).map(|t| &t.kind),
                        Some(TokKind::Ident(_))
                    ) && matches!(
                        self.toks.get(self.pos + 1).map(|t| &t.kind),
                        Some(TokKind::Eq)
                    );
                    if is_assign {
                        stmts.push(self.parse_assign()?);
                    } else {
                        let e = self.parse_expr()?;
                        if self.at(&TokKind::Semi) {
                            return Err(FrontendDiag::new(
                                codes::FE601_UNSUPPORTED_RS,
                                "a bare expression statement has no effect in RS0 (use `let`, an \
                                 assignment, `return`, or a trailing tail expression)",
                                self.cur_span(),
                            ));
                        }
                        if !self.at(&TokKind::RBrace) {
                            return Err(FrontendDiag::new(
                                codes::FE601_UNSUPPORTED_RS,
                                "expected `;` or `}` after an expression",
                                self.cur_span(),
                            ));
                        }
                        tail = Some(e);
                        break;
                    }
                }
            }
        }

        let close = self.expect(&TokKind::RBrace, "expected `}` to close the block")?;
        self.depth -= 1;
        Ok(RsBlock {
            stmts,
            tail,
            span: open.start..close.end,
        })
    }

    fn parse_let(&mut self) -> Result<RsStmt, FrontendDiag> {
        let start = self.cur_span().start;
        self.eat_keyword("let");
        let is_mut = self.eat_keyword("mut");
        let (name, name_span) = self.expect_name("a variable name after `let`")?;
        // Optional explicit type annotation; absent → inferred from the value
        // (SIGIL infers a `let` type from its initializer too).
        let ann = if self.at(&TokKind::Colon) {
            self.pos += 1;
            Some(self.parse_type()?)
        } else {
            None
        };
        self.expect(&TokKind::Eq, "expected `=` in the `let` binding")?;
        let value = self.parse_expr()?;
        let semi = self.expect(&TokKind::Semi, "expected `;` after the `let` binding")?;
        Ok(RsStmt::Let {
            name,
            name_span,
            is_mut,
            ann,
            value,
            span: start..semi.end,
        })
    }

    fn parse_assign(&mut self) -> Result<RsStmt, FrontendDiag> {
        let (name, name_span) = self.expect_name("a variable name")?;
        self.expect(&TokKind::Eq, "expected `=` in the assignment")?;
        let value = self.parse_expr()?;
        let semi = self.expect(&TokKind::Semi, "expected `;` after the assignment")?;
        let span = name_span.start..semi.end;
        Ok(RsStmt::Assign {
            name,
            name_span,
            value,
            span,
        })
    }

    fn parse_return(&mut self) -> Result<RsStmt, FrontendDiag> {
        let start = self.cur_span().start;
        self.eat_keyword("return");
        let value = self.parse_expr()?;
        let semi = self.expect(&TokKind::Semi, "expected `;` after `return <expr>`")?;
        Ok(RsStmt::Return {
            value: Some(value),
            span: start..semi.end,
        })
    }

    fn parse_if(&mut self) -> Result<RsStmt, FrontendDiag> {
        let start = self.cur_span().start;
        self.eat_keyword("if");
        let cond = self.parse_cond()?;
        let then_block = self.parse_block()?;
        let (else_block, end) = if self.eat_keyword("else") {
            if self.ident_is("if") {
                // `else if` → the nested `if` wrapped in a synthetic one-statement
                // block, so it emits as SIGIL's nested `else { if … }`.
                let nested = self.parse_if()?;
                let nspan = stmt_span(&nested);
                let end = nspan.end;
                (
                    Some(RsBlock {
                        stmts: vec![nested],
                        tail: None,
                        span: nspan,
                    }),
                    end,
                )
            } else {
                let b = self.parse_block()?;
                let end = b.span.end;
                (Some(b), end)
            }
        } else {
            (None, then_block.span.end)
        };
        Ok(RsStmt::If {
            cond,
            then_block,
            else_block,
            span: start..end,
        })
    }

    fn parse_while(&mut self) -> Result<RsStmt, FrontendDiag> {
        let start = self.cur_span().start;
        self.eat_keyword("while");
        let cond = self.parse_cond()?;
        let body = self.parse_block()?;
        let end = body.span.end;
        Ok(RsStmt::While {
            cond,
            body,
            span: start..end,
        })
    }

    /// `match scrut { pat => expr, … }` — a statement. The scrutinee is parsed with
    /// struct literals suppressed (the `{` opens the match body, not a construction).
    /// Each arm is a bare-expression value; a block-bodied arm (`=> { … }`) and a
    /// guard (`pat if … =>`) are deferred (FE652). Arms are flat (no recursion into
    /// `parse_block`), so a match adds no block-nesting depth.
    fn parse_match(&mut self) -> Result<RsStmt, FrontendDiag> {
        let start = self.cur_span().start;
        self.eat_keyword("match");
        let scrutinee = self.parse_cond()?;
        self.expect(&TokKind::LBrace, "expected `{` to open the match body")?;
        let mut arms = Vec::new();
        while !self.at(&TokKind::RBrace) {
            if self.pos >= self.toks.len() {
                return Err(FrontendDiag::new(
                    codes::FE601_UNSUPPORTED_RS,
                    "unexpected end of input inside a match (missing `}`)",
                    self.cur_span(),
                ));
            }
            let pattern = self.parse_pattern()?;
            // A guard `pat if <expr> => …` is deferred (FE652).
            if self.ident_is("if") {
                return Err(FrontendDiag::new(
                    codes::FE652_BAD_MATCH_ARM_RS,
                    "match guards (`pat if …`) are not supported in RS3b",
                    self.cur_span(),
                ));
            }
            if !self.at(&TokKind::FatArrow) {
                return Err(FrontendDiag::new(
                    codes::FE652_BAD_MATCH_ARM_RS,
                    "expected `=>` after a match pattern (ranges / or-patterns / bindings are deferred)",
                    self.cur_span(),
                ));
            }
            self.pos += 1; // consume `=>`
            // A block-bodied arm (`=> { … }`) is deferred — only `=> <expr>` (RS3b).
            if self.at(&TokKind::LBrace) {
                return Err(FrontendDiag::new(
                    codes::FE652_BAD_MATCH_ARM_RS,
                    "block-bodied match arms (`=> { … }`) are deferred in RS3b (use `pat => <expr>`)",
                    self.cur_span(),
                ));
            }
            let value = self.parse_expr_delimited()?;
            let span = pattern.span().start..expr_span(&value).end;
            arms.push(RsMatchArm {
                pattern,
                value,
                span,
            });
            if self.at(&TokKind::Comma) {
                self.pos += 1;
                if self.at(&TokKind::RBrace) {
                    break; // trailing comma
                }
                continue;
            }
            break; // no comma → this must be the last arm
        }
        let close = self.expect(&TokKind::RBrace, "expected `}` to close the match")?;
        Ok(RsStmt::Match {
            scrutinee,
            arms,
            span: start..close.end,
        })
    }

    /// A match-arm pattern (RS3b): `_`, an integer / `-`integer literal, `true` /
    /// `false`, or a dataless enum-variant `Name::Variant`. A bare identifier
    /// binding, a payload binding (`Name::V(x)`), or any other form is FE652.
    fn parse_pattern(&mut self) -> Result<RsPattern, FrontendDiag> {
        let span = self.cur_span();
        match self.toks.get(self.pos).map(|t| t.kind.clone()) {
            Some(TokKind::Ident(n)) => match n.as_str() {
                "_" => {
                    self.pos += 1;
                    Ok(RsPattern::Wildcard(span))
                }
                "true" => {
                    self.pos += 1;
                    Ok(RsPattern::Bool(true, span))
                }
                "false" => {
                    self.pos += 1;
                    Ok(RsPattern::Bool(false, span))
                }
                _ => {
                    self.pos += 1;
                    // `Name::Variant` or `Name::Variant(b1, …, bn)` — an enum-variant
                    // pattern (RS3c binds the positional payloads). A bare ident (no
                    // `::`) is a binding pattern, still deferred (FE652).
                    if !self.at(&TokKind::ColonColon) {
                        return Err(FrontendDiag::new(
                            codes::FE652_BAD_MATCH_ARM_RS,
                            format!(
                                "bare identifier pattern `{n}` (a binding) is deferred (use `_` or a `Name::Variant`)"
                            ),
                            span,
                        ));
                    }
                    self.pos += 1; // consume `::`
                    let (variant, vspan) = self.expect_name("a variant name after `::`")?;
                    let mut end = vspan.end;
                    let mut bindings = Vec::new();
                    if self.at(&TokKind::LParen) {
                        self.pos += 1; // consume `(`
                        if self.at(&TokKind::RParen) {
                            return Err(FrontendDiag::new(
                                codes::FE652_BAD_MATCH_ARM_RS,
                                format!(
                                    "empty payload binding `{n}::{variant}()` (use `{n}::{variant}` for a dataless variant)"
                                ),
                                vspan,
                            ));
                        }
                        loop {
                            let (b, bspan) = self.expect_name("a payload binding name")?;
                            bindings.push((b, bspan));
                            if self.at(&TokKind::Comma) {
                                self.pos += 1;
                                if self.at(&TokKind::RParen) {
                                    break; // trailing comma
                                }
                                continue;
                            }
                            break;
                        }
                        let rp = self.expect(
                            &TokKind::RParen,
                            "expected `)` to close the payload bindings",
                        )?;
                        end = rp.end;
                    }
                    Ok(RsPattern::Variant {
                        enum_name: n,
                        variant,
                        bindings,
                        span: span.start..end,
                    })
                }
            },
            Some(TokKind::Int(v)) => {
                self.pos += 1;
                Ok(RsPattern::Int(v, span))
            }
            Some(TokKind::Minus) => {
                self.pos += 1;
                match self.toks.get(self.pos).map(|t| t.kind.clone()) {
                    Some(TokKind::Int(v)) => {
                        let end = self.cur_span().end;
                        self.pos += 1;
                        Ok(RsPattern::Int(-v, span.start..end))
                    }
                    _ => Err(FrontendDiag::new(
                        codes::FE652_BAD_MATCH_ARM_RS,
                        "expected an integer literal after `-` in a pattern",
                        self.cur_span(),
                    )),
                }
            }
            _ => Err(FrontendDiag::new(
                codes::FE652_BAD_MATCH_ARM_RS,
                "unsupported match pattern (allowed: `_`, an integer / `bool` literal, or `Name::Variant(bindings…)`)",
                span,
            )),
        }
    }

    fn parse_expr(&mut self) -> Result<RsExpr, FrontendDiag> {
        self.parse_equality()
    }

    /// Parse a condition (`if`/`while`) with struct literals suppressed — `Name {`
    /// opens the body block, not a struct construction (Rust's rule; keeps
    /// `if flag { … }` parsing as a bare bool condition).
    fn parse_cond(&mut self) -> Result<RsExpr, FrontendDiag> {
        let saved = self.no_struct_lit;
        self.no_struct_lit = true;
        let c = self.parse_expr();
        self.no_struct_lit = saved;
        c
    }

    /// Parse a sub-expression where struct literals are always allowed (inside
    /// `( … )`, a call argument, or a struct-literal value) — the condition
    /// restriction is lifted.
    fn parse_expr_delimited(&mut self) -> Result<RsExpr, FrontendDiag> {
        let saved = self.no_struct_lit;
        self.no_struct_lit = false;
        let e = self.parse_expr();
        self.no_struct_lit = saved;
        e
    }

    fn parse_equality(&mut self) -> Result<RsExpr, FrontendDiag> {
        let mut left = self.parse_comparison()?;
        loop {
            let op = match self.toks.get(self.pos).map(|t| &t.kind) {
                Some(TokKind::EqEq) => BinOp::Eq,
                Some(TokKind::BangEq) => BinOp::Ne,
                _ => break,
            };
            self.pos += 1;
            let right = self.parse_comparison()?;
            let span = expr_span(&left).start..expr_span(&right).end;
            left = RsExpr::Bin(op, Box::new(left), Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_comparison(&mut self) -> Result<RsExpr, FrontendDiag> {
        let mut left = self.parse_term()?;
        loop {
            let op = match self.toks.get(self.pos).map(|t| &t.kind) {
                Some(TokKind::Lt) => BinOp::Lt,
                Some(TokKind::LtEq) => BinOp::Le,
                Some(TokKind::Gt) => BinOp::Gt,
                Some(TokKind::GtEq) => BinOp::Ge,
                _ => break,
            };
            self.pos += 1;
            let right = self.parse_term()?;
            let span = expr_span(&left).start..expr_span(&right).end;
            left = RsExpr::Bin(op, Box::new(left), Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_term(&mut self) -> Result<RsExpr, FrontendDiag> {
        let mut left = self.parse_factor()?;
        loop {
            let op = match self.toks.get(self.pos).map(|t| &t.kind) {
                Some(TokKind::Plus) => BinOp::Add,
                Some(TokKind::Minus) => BinOp::Sub,
                _ => break,
            };
            self.pos += 1;
            let right = self.parse_factor()?;
            let span = expr_span(&left).start..expr_span(&right).end;
            left = RsExpr::Bin(op, Box::new(left), Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_factor(&mut self) -> Result<RsExpr, FrontendDiag> {
        let mut left = self.parse_unary()?;
        while let Some(TokKind::Star) = self.toks.get(self.pos).map(|t| &t.kind) {
            self.pos += 1;
            let right = self.parse_unary()?;
            let span = expr_span(&left).start..expr_span(&right).end;
            left = RsExpr::Bin(BinOp::Mul, Box::new(left), Box::new(right), span);
        }
        Ok(left)
    }

    // The RS0-OWNED expression depth guard (shares `depth` with `parse_block`).
    fn parse_unary(&mut self) -> Result<RsExpr, FrontendDiag> {
        self.depth += 1;
        if self.depth > limits::MAX_DEPTH {
            return Err(FrontendDiag::new(
                codes::FE602_TOO_LARGE_RS,
                format!("expression nesting exceeds depth {}", limits::MAX_DEPTH),
                self.cur_span(),
            ));
        }
        let result = self.parse_unary_inner();
        if result.is_ok() {
            self.depth -= 1;
        }
        result
    }

    fn parse_unary_inner(&mut self) -> Result<RsExpr, FrontendDiag> {
        let start = self.cur_span().start;
        match self.toks.get(self.pos).map(|t| &t.kind) {
            Some(TokKind::Bang) => {
                self.pos += 1;
                let inner = self.parse_unary()?;
                let span = start..expr_span(&inner).end;
                Ok(RsExpr::Unary(UnOp::Not, Box::new(inner), span))
            }
            Some(TokKind::Minus) => {
                self.pos += 1;
                let inner = self.parse_unary()?;
                let span = start..expr_span(&inner).end;
                Ok(RsExpr::Unary(UnOp::Neg, Box::new(inner), span))
            }
            _ => self.parse_postfix(),
        }
    }

    /// Postfix field access `e.f` (RS3). Chained (`a.b.c`) via a bounded loop —
    /// the chain length is capped at `MAX_DEPTH` so a long chain cannot build an
    /// AST that overflows the checker/emitter recursion (SC-8). A method call
    /// (`e.f()`) or tuple index (`e.0`) is rejected (FE642).
    fn parse_postfix(&mut self) -> Result<RsExpr, FrontendDiag> {
        let mut e = self.parse_primary()?;
        let mut chain: u32 = 0;
        while self.at(&TokKind::Dot) {
            chain += 1;
            if chain > limits::MAX_DEPTH {
                return Err(FrontendDiag::new(
                    codes::FE602_TOO_LARGE_RS,
                    format!("field-access chain exceeds depth {}", limits::MAX_DEPTH),
                    self.cur_span(),
                ));
            }
            self.pos += 1; // consume `.`
            match self.toks.get(self.pos).map(|t| t.kind.clone()) {
                Some(TokKind::Ident(f)) => {
                    let fspan = self.cur_span();
                    self.pos += 1;
                    if self.at(&TokKind::LParen) {
                        return Err(FrontendDiag::new(
                            codes::FE642_BAD_FIELD_ACCESS_RS,
                            format!("method calls (`e.{f}()`) are not supported in RS0"),
                            fspan,
                        ));
                    }
                    let start = expr_span(&e).start;
                    e = RsExpr::Field(Box::new(e), f, start..fspan.end);
                }
                _ => {
                    return Err(FrontendDiag::new(
                        codes::FE642_BAD_FIELD_ACCESS_RS,
                        "expected a field name after `.` (tuple indices `.0` are deferred)",
                        self.cur_span(),
                    ));
                }
            }
        }
        Ok(e)
    }

    fn parse_primary(&mut self) -> Result<RsExpr, FrontendDiag> {
        let span = self.cur_span();
        match self.toks.get(self.pos).map(|t| t.kind.clone()) {
            Some(TokKind::Int(v)) => {
                self.pos += 1;
                Ok(RsExpr::Int(v, span))
            }
            Some(TokKind::Ident(n)) => match n.as_str() {
                // `if`/`match`/`loop`/`while`/`for` in value position → the
                // if/block-as-expression case, deferred in RS0 (FE690).
                "if" | "match" | "loop" | "while" | "for" => Err(FrontendDiag::new(
                    codes::FE690_EXPR_POSITION_RS,
                    format!(
                        "`{n}` in value/expression position is deferred in RS0 (if/block-as-expression)"
                    ),
                    span,
                )),
                "true" => {
                    self.pos += 1;
                    Ok(RsExpr::Bool(true, span))
                }
                "false" => {
                    self.pos += 1;
                    Ok(RsExpr::Bool(false, span))
                }
                _ => {
                    self.pos += 1;
                    if self.at(&TokKind::ColonColon) {
                        // `Name::Variant` or `Name::Variant(e1, …)` — enum construction
                        // (RS3b/c). A deeper path (`a::b::c`) is out-of-subset (FE601).
                        self.pos += 1; // consume `::`
                        let (variant, vspan) = self.expect_name("a variant name after `::`")?;
                        let mut end = vspan.end;
                        let mut args = Vec::new();
                        if self.at(&TokKind::LParen) {
                            self.pos += 1; // consume `(`
                            args = self.parse_call_args()?;
                            let rp = self.expect(
                                &TokKind::RParen,
                                "expected `)` to close the variant payload arguments",
                            )?;
                            end = rp.end;
                        }
                        if self.at(&TokKind::ColonColon) {
                            return Err(FrontendDiag::new(
                                codes::FE601_UNSUPPORTED_RS,
                                "multi-segment paths (`a::b::c`) are not supported",
                                self.cur_span(),
                            ));
                        }
                        Ok(RsExpr::EnumCtor(n, variant, args, span.start..end))
                    } else if self.at(&TokKind::LParen) {
                        self.pos += 1;
                        let args = self.parse_call_args()?;
                        let rp = self
                            .expect(&TokKind::RParen, "expected `)` to close the call arguments")?;
                        let call_span = span.start..rp.end;
                        // RS5b: `declassify(value)` is a recognized escape hatch, NOT a
                        // user-function call — arity exactly 1 (SR-B1); the linear
                        // `Cap<Declassify>` is emitter-synthesized. `declassify_ct` (the
                        // @SecretCT declassifier) is deferred to RS5c (AG-B1/SR-B3).
                        if n == "declassify" {
                            if args.len() != 1 {
                                return Err(FrontendDiag::new(
                                    codes::FE672_BAD_DECLASSIFY_RS,
                                    format!(
                                        "`declassify` takes exactly one argument (the value to declassify); found {}",
                                        args.len()
                                    ),
                                    call_span,
                                ));
                            }
                            let arg = args.into_iter().next().expect("arity checked == 1");
                            // Assign a stable per-function cap index (SR-B4); the
                            // emitter provisions `__fe_declassify_cap_<idx>`.
                            let idx = self.declassify_idx;
                            self.declassify_idx += 1;
                            Ok(RsExpr::Declassify(Box::new(arg), idx, call_span))
                        } else if n == "declassify_ct" {
                            Err(FrontendDiag::new(
                                codes::FE672_BAD_DECLASSIFY_RS,
                                "`declassify_ct` (the @SecretCT constant-time declassifier) is not supported yet (RS5c); use `declassify` for non-CT data",
                                call_span,
                            ))
                        } else {
                            Ok(RsExpr::Call(n, args, call_span))
                        }
                    } else if self.at(&TokKind::LBrace) && !self.no_struct_lit {
                        // `Name { … }` struct construction (RS3), unless suppressed
                        // in a condition (where `{` opens the body block).
                        self.parse_struct_lit(n, span.start)
                    } else {
                        Ok(RsExpr::Var(n, span))
                    }
                }
            },
            Some(TokKind::LBrace) => Err(FrontendDiag::new(
                codes::FE690_EXPR_POSITION_RS,
                "a block `{ … }` in value/expression position is deferred in RS0",
                span,
            )),
            Some(TokKind::LParen) => {
                self.pos += 1;
                let inner = self.parse_expr_delimited()?;
                self.expect(&TokKind::RParen, "expected `)`")?;
                Ok(inner)
            }
            _ => Err(FrontendDiag::new(
                codes::FE601_UNSUPPORTED_RS,
                "expected an expression (integer, `true`/`false`, identifier, call, struct \
                 construction, or `( … )`)",
                span,
            )),
        }
    }

    /// `Name { f: e, … }` — the struct name already consumed; parses the `{ … }`.
    /// Field shorthand (`{ x }`) and functional update (`{ ..base }`) are deferred.
    fn parse_struct_lit(&mut self, name: String, start: usize) -> Result<RsExpr, FrontendDiag> {
        self.pos += 1; // consume `{`
        let mut fields = Vec::new();
        if !self.at(&TokKind::RBrace) {
            loop {
                let (fname, fspan) = self.expect_name("a struct field name")?;
                self.expect(
                    &TokKind::Colon,
                    "expected `:` in a struct field (field shorthand `{ x }` is deferred in RS0)",
                )?;
                let value = self.parse_expr_delimited()?;
                fields.push((fname, value, fspan));
                if self.at(&TokKind::Comma) {
                    self.pos += 1;
                    if self.at(&TokKind::RBrace) {
                        break; // trailing comma
                    }
                    continue;
                }
                break;
            }
        }
        let close = self.expect(&TokKind::RBrace, "expected `}` to close the struct literal")?;
        Ok(RsExpr::StructLit(name, fields, start..close.end))
    }

    fn parse_call_args(&mut self) -> Result<Vec<RsExpr>, FrontendDiag> {
        let mut args = Vec::new();
        if self.at(&TokKind::RParen) {
            return Ok(args);
        }
        loop {
            let a = self.parse_expr_delimited()?;
            args.push(a);
            if self.at(&TokKind::Comma) {
                self.pos += 1;
                if self.at(&TokKind::RParen) {
                    break; // trailing comma
                }
                continue;
            }
            break;
        }
        Ok(args)
    }
}

// ── RS1 attribute parsing: `#[sigil::cap(Name, deadline = <int>)]` ───────────
// The inner text is parsed here (not by the main lexer), keeping `::`/`[`/`]` out
// of the general token set. Anything that is not exactly a well-formed
// `sigil::cap( … )` is a fail-closed reject (FE010) — a security translator must
// never silently ignore a policy annotation it does not understand.

#[derive(Debug)]
enum MiniTok {
    Ident(String),
    Int(i64),
    ColonColon,
    LParen,
    RParen,
    Comma,
    Eq,
    // Refinement predicate operators (RS4a).
    Lt,
    Le,
    Gt,
    Ge,
    EqEq,
    Ne,
    /// A `-` (RS4a): only ever an error signal here — a negative cap deadline
    /// (FE612) or a negative refinement bound (FE660), rejected by each arm.
    Minus,
}

fn mini_lex(inner: &str, span: &Range<usize>) -> Result<Vec<MiniTok>, FrontendDiag> {
    let b = inner.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < b.len() {
        match b[i] {
            b' ' | b'\t' | b'\r' | b'\n' => i += 1,
            b':' => {
                if b.get(i + 1) == Some(&b':') {
                    out.push(MiniTok::ColonColon);
                    i += 2;
                } else {
                    return Err(attr_err(span, "a lone `:` in the attribute"));
                }
            }
            b'(' => {
                out.push(MiniTok::LParen);
                i += 1;
            }
            b')' => {
                out.push(MiniTok::RParen);
                i += 1;
            }
            b',' => {
                out.push(MiniTok::Comma);
                i += 1;
            }
            b'=' => {
                if b.get(i + 1) == Some(&b'=') {
                    out.push(MiniTok::EqEq);
                    i += 2;
                } else {
                    out.push(MiniTok::Eq);
                    i += 1;
                }
            }
            b'<' => {
                if b.get(i + 1) == Some(&b'=') {
                    out.push(MiniTok::Le);
                    i += 2;
                } else {
                    out.push(MiniTok::Lt);
                    i += 1;
                }
            }
            b'>' => {
                if b.get(i + 1) == Some(&b'=') {
                    out.push(MiniTok::Ge);
                    i += 2;
                } else {
                    out.push(MiniTok::Gt);
                    i += 1;
                }
            }
            b'!' => {
                if b.get(i + 1) == Some(&b'=') {
                    out.push(MiniTok::Ne);
                    i += 2;
                } else {
                    return Err(attr_err(span, "a lone `!` in the attribute"));
                }
            }
            b'-' => {
                out.push(MiniTok::Minus);
                i += 1;
            }
            b'0'..=b'9' => {
                let start = i;
                while i < b.len() && b[i].is_ascii_digit() {
                    i += 1;
                }
                let text = std::str::from_utf8(&b[start..i]).expect("ascii digits");
                match text.parse::<i64>() {
                    Ok(v) => out.push(MiniTok::Int(v)),
                    Err(_) => {
                        return Err(FrontendDiag::new(
                            codes::FE612_BAD_NUMBER_RS,
                            "a `#[sigil::cap]` deadline is out of i64 range",
                            span.clone(),
                        ));
                    }
                }
            }
            b'A'..=b'Z' | b'a'..=b'z' | b'_' => {
                let start = i;
                while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                    i += 1;
                }
                let text = std::str::from_utf8(&b[start..i])
                    .expect("ascii ident")
                    .to_owned();
                out.push(MiniTok::Ident(text));
            }
            _ => return Err(attr_err(span, "an unrecognized character in the attribute")),
        }
    }
    Ok(out)
}

fn attr_err(span: &Range<usize>, what: &str) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE010_UNKNOWN_ANNOTATION,
        format!(
            "unrecognized attribute (supported: `#[sigil::cap(Name, deadline = <int>)]`, \
             `#[sigil::effects(A, …)]`, `#[sigil::requires(<param> <cmp> <int>)]`, \
             `#[sigil::invariant(<clause>)]`, `#[sigil::taint(<target> = <Level>)]`): {what}"
        ),
        span.clone(),
    )
}

enum ParsedAttr {
    Cap(RsCap),
    Effects(Vec<RsEffect>),
    Require(RsRequire),
    Invariant(RsInvariant),
    Taint(RsTaint),
}

fn parse_attr(inner: &str, span: Range<usize>) -> Result<ParsedAttr, FrontendDiag> {
    let toks = mini_lex(inner, &span)?;
    let mut it = toks.into_iter();
    // `sigil :: <cap|effects> ( … )`
    match it.next() {
        Some(MiniTok::Ident(s)) if s == "sigil" => {}
        _ => return Err(attr_err(&span, "expected `sigil`")),
    }
    match it.next() {
        Some(MiniTok::ColonColon) => {}
        _ => return Err(attr_err(&span, "expected `::`")),
    }
    let kind = match it.next() {
        Some(MiniTok::Ident(s)) => s,
        _ => return Err(attr_err(&span, "expected `cap` or `effects`")),
    };
    match it.next() {
        Some(MiniTok::LParen) => {}
        _ => return Err(attr_err(&span, "expected `(`")),
    }
    match kind.as_str() {
        "cap" => {
            // `<Name> , deadline = <int> )`
            let name = match it.next() {
                Some(MiniTok::Ident(s)) => s,
                _ => return Err(attr_err(&span, "expected a capability name")),
            };
            match it.next() {
                Some(MiniTok::Comma) => {}
                _ => return Err(attr_err(&span, "expected `,`")),
            }
            match it.next() {
                Some(MiniTok::Ident(s)) if s == "deadline" => {}
                _ => return Err(attr_err(&span, "expected `deadline`")),
            }
            match it.next() {
                Some(MiniTok::Eq) => {}
                _ => return Err(attr_err(&span, "expected `=`")),
            }
            let deadline = match it.next() {
                Some(MiniTok::Int(d)) => d,
                // A `-` now lexes as `Minus` (RS4a); the cap deadline stays
                // non-negative, so re-emit the FE612 the lexer used to raise.
                Some(MiniTok::Minus) => {
                    return Err(FrontendDiag::new(
                        codes::FE612_BAD_NUMBER_RS,
                        "a `#[sigil::cap]` deadline must be a non-negative integer",
                        span.clone(),
                    ));
                }
                _ => return Err(attr_err(&span, "expected an integer deadline")),
            };
            match it.next() {
                Some(MiniTok::RParen) => {}
                _ => return Err(attr_err(&span, "expected `)`")),
            }
            if it.next().is_some() {
                return Err(attr_err(&span, "trailing tokens after `)`"));
            }
            Ok(ParsedAttr::Cap(RsCap {
                name,
                deadline,
                span,
            }))
        }
        "effects" => {
            // `A , B , … )` or `)` (empty still selects effect-mode).
            let mut names = Vec::new();
            loop {
                match it.next() {
                    Some(MiniTok::RParen) => break,
                    Some(MiniTok::Ident(s)) => {
                        names.push(RsEffect {
                            name: s,
                            span: span.clone(),
                        });
                        match it.next() {
                            Some(MiniTok::Comma) => continue,
                            Some(MiniTok::RParen) => break,
                            _ => return Err(attr_err(&span, "expected `,` or `)`")),
                        }
                    }
                    _ => return Err(attr_err(&span, "expected an effect name or `)`")),
                }
            }
            if it.next().is_some() {
                return Err(attr_err(&span, "trailing tokens after `)`"));
            }
            Ok(ParsedAttr::Effects(names))
        }
        "requires" => {
            // `<param> <op> <int> )` — exactly one clause (SR-1). The LHS must be a
            // plain identifier (a literal LHS like `1 == 1` is FE660, SR-2); the RHS
            // must be a non-negative i64 literal (a `-` / another param → FE660,
            // AG-1). Parameter membership of the LHS is checked at type-check (FE661).
            let bad = |what: &str| {
                FrontendDiag::new(
                    codes::FE660_BAD_REFINEMENT_RS,
                    format!(
                        "malformed `#[sigil::requires]` predicate ({what}); RS4a admits exactly \
                         `<param> <cmp> <non-negative int>` with `<cmp>` in `< <= > >= == !=`"
                    ),
                    span.clone(),
                )
            };
            let param = match it.next() {
                Some(MiniTok::Ident(s)) => s,
                _ => return Err(bad("the left side must be a parameter name")),
            };
            let op = match it.next() {
                Some(MiniTok::Lt) => RefineOp::Lt,
                Some(MiniTok::Le) => RefineOp::Le,
                Some(MiniTok::Gt) => RefineOp::Gt,
                Some(MiniTok::Ge) => RefineOp::Ge,
                Some(MiniTok::EqEq) => RefineOp::Eq,
                Some(MiniTok::Ne) => RefineOp::Ne,
                _ => return Err(bad("expected a comparison operator")),
            };
            let rhs = match it.next() {
                Some(MiniTok::Int(v)) => v,
                Some(MiniTok::Minus) => {
                    return Err(bad(
                        "a negative bound is deferred (RS4a: non-negative literal RHS)",
                    ));
                }
                Some(MiniTok::Ident(_)) => {
                    return Err(bad(
                        "a parameter right-hand side (`x < y`) is deferred to RS4b",
                    ));
                }
                _ => return Err(bad("the right side must be a non-negative integer literal")),
            };
            match it.next() {
                Some(MiniTok::RParen) => {}
                // Anything before `)` (a second clause, `&&`, arithmetic) is
                // out-of-fragment (AG-2).
                _ => return Err(bad("expected `)` after a single clause")),
            }
            if it.next().is_some() {
                return Err(bad("trailing tokens after `)`"));
            }
            Ok(ParsedAttr::Require(RsRequire {
                param,
                op,
                rhs,
                span,
            }))
        }
        "invariant" => {
            // `<field> <op> <rhs> )` — one clause (RS4b). `<rhs>` is a non-negative
            // i64 literal OR another field (cross-field, e.g. `lo <= hi`). Field
            // membership + i64-ness + self-reference are checked at type-check.
            let bad = |what: &str| {
                FrontendDiag::new(
                    codes::FE660_BAD_REFINEMENT_RS,
                    format!(
                        "malformed `#[sigil::invariant]` clause ({what}); RS4b admits exactly \
                         `<field> <cmp> <field | non-negative int>` with `<cmp>` in `< <= > >= == !=`"
                    ),
                    span.clone(),
                )
            };
            let field = match it.next() {
                Some(MiniTok::Ident(s)) => s,
                _ => return Err(bad("the left side must be a field name")),
            };
            let op = match it.next() {
                Some(MiniTok::Lt) => RefineOp::Lt,
                Some(MiniTok::Le) => RefineOp::Le,
                Some(MiniTok::Gt) => RefineOp::Gt,
                Some(MiniTok::Ge) => RefineOp::Ge,
                Some(MiniTok::EqEq) => RefineOp::Eq,
                Some(MiniTok::Ne) => RefineOp::Ne,
                _ => return Err(bad("expected a comparison operator")),
            };
            let rhs = match it.next() {
                Some(MiniTok::Int(v)) => RsInvRhs::Literal(v),
                Some(MiniTok::Ident(f)) => RsInvRhs::Field(f),
                Some(MiniTok::Minus) => {
                    return Err(bad(
                        "a negative bound is deferred (RS4b: non-negative literal RHS)",
                    ));
                }
                _ => {
                    return Err(bad(
                        "the right side must be a field or a non-negative integer",
                    ));
                }
            };
            match it.next() {
                Some(MiniTok::RParen) => {}
                _ => return Err(bad("expected `)` after a single clause")),
            }
            if it.next().is_some() {
                return Err(bad("trailing tokens after `)`"));
            }
            Ok(ParsedAttr::Invariant(RsInvariant {
                field,
                op,
                rhs,
                span,
            }))
        }
        "taint" => {
            // `<target> = <Level> (, <target> = <Level>)* )` — RS5a (SR-T1). `<target>`
            // is `ret` or a param name; `<Level>` ∈ {Public, Internal, Secret}.
            // `SecretCT` is deferred; a duplicate target is FE670 (never last-wins).
            let bad = |what: &str| {
                FrontendDiag::new(
                    codes::FE670_BAD_TAINT_RS,
                    format!(
                        "malformed `#[sigil::taint]` ({what}); RS5a admits `<param|ret> = <Level>` \
                         clauses with `<Level>` in `Public | Internal | Secret`"
                    ),
                    span.clone(),
                )
            };
            let mut targets: Vec<(RsTaintSel, TaintLevel, Range<usize>)> = Vec::new();
            let mut seen: Vec<String> = Vec::new();
            loop {
                let tname = match it.next() {
                    Some(MiniTok::Ident(s)) => s,
                    Some(MiniTok::RParen) if targets.is_empty() => {
                        return Err(bad("empty attribute; name at least one target"));
                    }
                    _ => return Err(bad("expected a target (`ret` or a parameter name)")),
                };
                match it.next() {
                    Some(MiniTok::Eq) => {}
                    _ => return Err(bad("expected `=` after the target")),
                }
                let level = match it.next() {
                    Some(MiniTok::Ident(s)) => match s.as_str() {
                        "Public" => TaintLevel::Public,
                        "Internal" => TaintLevel::Internal,
                        "Secret" => TaintLevel::Secret,
                        "SecretCT" => {
                            return Err(FrontendDiag::new(
                                codes::FE670_BAD_TAINT_RS,
                                "the `SecretCT` (constant-time) level is deferred in RS5a (AG-T1)",
                                span.clone(),
                            ));
                        }
                        other => return Err(bad(&format!("unknown level `{other}`"))),
                    },
                    _ => return Err(bad("expected a level after `=`")),
                };
                // SR-T3: a target may be set at most once — never merge/last-wins.
                if seen.contains(&tname) {
                    return Err(bad(&format!("target `{tname}` is set more than once")));
                }
                seen.push(tname.clone());
                let sel = if tname == "ret" {
                    RsTaintSel::Ret
                } else {
                    RsTaintSel::Param(tname)
                };
                targets.push((sel, level, span.clone()));
                match it.next() {
                    Some(MiniTok::Comma) => continue,
                    Some(MiniTok::RParen) => break,
                    _ => return Err(bad("expected `,` or `)` after a clause")),
                }
            }
            if it.next().is_some() {
                return Err(bad("trailing tokens after `)`"));
            }
            Ok(ParsedAttr::Taint(RsTaint { targets, span }))
        }
        _ => Err(attr_err(
            &span,
            "expected `cap`, `effects`, `requires`, `invariant`, or `taint`",
        )),
    }
}
