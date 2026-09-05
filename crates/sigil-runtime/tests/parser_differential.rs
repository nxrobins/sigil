//! Parser PR-1 — the differential-parser harness foundation (see
//! `docs/specs/parser-in-sigil.md`).
//!
//! The SIGIL lexer + SIGIL parser are inlined into ONE tool, so
//! `parser_parse(lex(src))` composes in-SIGIL across a single forge boundary;
//! the tool ships a canonical PRE-ORDER serialization of its `Arena<PNode>` AST
//! (`kind,start,end,value,flags,child_count;…|pool`) via `as_output`. The host
//! flattens the Rust `parse_with_id` oracle's `Program` in the SAME pre-order
//! with the SAME per-kind child order (ET-P3's schema) and compares
//! node-for-node — kind, span, value, flags, child_count, and the decoded name
//! text (ET-P2).
//!
//! ET-P9 drift-locks: `item_kind_of` / `stmt_kind_of` / `expr_kind_of` /
//! `op_code_of` are TOTAL matches with NO `_` arm — a new Rust AST variant
//! won't compile until mapped. Kinds the PR-1 slice doesn't parse yet map to
//! UNHANDLED, which the SIGIL parser never emits, so any corpus node of that
//! kind is caught as a divergence (the lexer harness's proven pattern).

use sigil_compiler::ast::{
    ArrayElem, BinaryOp, Block, Expr, Item, Literal, MatchArm, Module, Pattern, Stmt, TaintLabel,
    TypeExpr, Visibility,
};
use sigil_compiler::compile_tool;
use sigil_compiler::parser::parse_with_id;
use sigil_compiler::source::SourceFile;
use sigil_compiler::span::SourceId;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// The SIGIL lexer + parser sources, inlined into one tool (their `module …;`
/// lines stripped). Every parser symbol is `parser_`/`P_`/`PNode`-prefixed, so
/// the merged namespace is collision-free by construction.
const LEXER: &str = include_str!("../../../selfhost/lexer.sigil");
const PARSER: &str = include_str!("../../../selfhost/parser.sigil");

const FUEL: u64 = 300_000_000;

fn parser_tool(body: &str) -> String {
    let lexer_defs = LEXER.replace("\nmodule lexer;\n", "\n");
    let parser_defs = PARSER.replace("\nmodule parser;\n", "\n");
    format!(
        "module tool;\n{lexer_defs}\n{parser_defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// The standard differential body: src → lex → parse → encode → as_output.
fn differential_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = parser_encode(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

/// The differential tool's wasm, compiled ONCE (the body is fixed; only the
/// input source varies).
fn parser_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        compile_tool(&parser_tool(differential_body()))
            .expect("parser tool should compile")
            .wasm
    })
}

// ── node kinds (the contract with selfhost/parser.sigil's P_K_* consts) ──────

const K_MODULE: i64 = 1;
const K_FN: i64 = 2;
const K_TYPE: i64 = 3;
const K_BLOCK: i64 = 4;
const K_RETURN: i64 = 10;
const K_LET: i64 = 11;
const K_LET_TUPLE: i64 = 12;
const K_ASSIGN: i64 = 13;
const K_EXPR_STMT: i64 = 14;
const K_IF: i64 = 15;
const K_WHILE: i64 = 16;
const K_FOR_IN: i64 = 17;
const K_BREAK: i64 = 18;
const K_CONTINUE: i64 = 19;
const K_MATCH: i64 = 20;
const K_MATCH_ARM: i64 = 21;
const K_PAT_LIT: i64 = 22;
const K_PAT_LIT_STR: i64 = 23;
const K_PAT_RANGE: i64 = 24;
const K_PAT_WILDCARD: i64 = 25;
const K_PAT_BINDING: i64 = 26;
const K_PAT_ENUM: i64 = 27;
const K_PAT_ARRAY: i64 = 28;
const K_BINARY: i64 = 30;
const K_LIT_INT: i64 = 31;
const K_PATH: i64 = 32;
const K_LIT_BOOL: i64 = 33;
const K_LIT_FLOAT: i64 = 34;
const K_LIT_STR: i64 = 35;
const K_BORROW: i64 = 36;
const K_CALL: i64 = 37;
const K_METHOD: i64 = 38;
const K_TRY: i64 = 39;
const K_INDEX: i64 = 40;
const K_SLICE: i64 = 41;
const K_RESULT_CTOR: i64 = 42;
const K_ARRAY: i64 = 43;
const K_TUPLE: i64 = 44;
const K_RECORD_CONSTRUCT: i64 = 45;
const K_TYPE_FN: i64 = 46;
const K_TYPE_ARRAY: i64 = 47;
const K_TYPE_TUPLE: i64 = 48;
const K_PARAM: i64 = 49;
const K_CLOSURE: i64 = 50;
const K_USE: i64 = 51;
const K_CONST: i64 = 52;
const K_RECORD_DEF: i64 = 53;
const K_FIELD: i64 = 54;
const K_TYPE_PARAM: i64 = 55;
const K_ENUM_DEF: i64 = 56;
const K_ENUM_VARIANT: i64 = 57;
const K_ENUM_FIELD: i64 = 58;
const K_IMPL: i64 = 59;
const K_TRAIT: i64 = 60;
const K_TRAIT_SIG: i64 = 61;
const K_EXTERN_FN: i64 = 62;
const K_EFFECT_DECL: i64 = 63;
const K_SEND: i64 = 64;
const K_ASK: i64 = 65;
const K_SPAWN: i64 = 66;
const K_CAP_RESTRICT: i64 = 67;
const K_CAP_RESTRICT_DEADLINE: i64 = 68;
const K_CAP_SPLIT: i64 = 69;
const K_CAP_DRAW: i64 = 70;
const K_GRANT: i64 = 71;
const K_HANDLE: i64 = 72;
const K_DECLASSIFY: i64 = 73;
const K_DECLASSIFY_CT: i64 = 74;
const K_REGION: i64 = 75;
const K_ACTOR: i64 = 76;
const K_ACTOR_INIT: i64 = 77;
const K_HANDLER: i64 = 78;
const K_CAP_TYPE: i64 = 79;
const K_REFINEMENT: i64 = 80;
/// PR-E3: an `Expr::FString` node. Must match `selfhost/parser.sigil`'s
/// `P_K_FSTRING` once the self-hosted parser mirror lands; no f-string fixture
/// exercises it yet (the corpus has none), so it is currently inert.
const K_FSTRING: i64 = 81;
/// PR-E4: a `type Name = TypeExpr;` alias item. Must match `selfhost/parser.sigil`'s
/// `P_K_TYPE_ALIAS`. `value` = name length, `flags` = public bit, one child = the body
/// type (flattened via the shared type grammar), `text` = the alias name.
const K_TYPE_ALIAS: i64 = 82;
/// SH-PARSE-MM: the multi-module wrapper root; must match `P_K_PROGRAM`. Emitted
/// only for a >1-module source. NOT in `kind_has_text` (its `text` is `""`).
const K_PROGRAM: i64 = 83;
/// Capabilities-as-values (R1): a `mint <Cap> [(<deadline>…)] for <target>`
/// expression — matches `selfhost/parser.sigil`'s `P_K_MINT`. text = the
/// cap-type name, value = its length, flags = the deadline-param count, one
/// child = the target expression. LIVE: the corpus exercises it (`m1`/`m2`/`m3`).
const K_MINT: i64 = 84;
/// Typestate (Epic 1, R3): a `[pub] state Name { S1, S2, … }` protocol decl —
/// matches `selfhost/parser.sigil`'s `P_K_STATE_DEF`. text = `name;S1;S2;…`,
/// value = its length, flags = public bit, a leaf (markers ride `text`).
const K_STATE_DEF: i64 = 85;
/// Effect Handlers (EH0): the clause form `handle <e> { Op(x) => .. }` — a leaf
/// spanning `handle`..`}` (its scrutinee/clauses are consumed but not emitted in
/// this slice). Matches `selfhost/parser.sigil`'s `P_K_CLAUSE_HANDLE`.
const K_CLAUSE_HANDLE: i64 = 86;
/// Effect Handlers (EH0): `perform <Effect>.<op>(args)` — a leaf; text =
/// `effect;op`, value = its length (args consumed but not emitted in this
/// slice). Matches `selfhost/parser.sigil`'s `P_K_PERFORM`.
const K_PERFORM: i64 = 87;
/// RANGE-FOR (RF-M4): `for v in a..b { … }`. text = the loop var (POOLED —
/// full text parity with `P_K_FOR_RANGE = 88` in parser.sigil, like K_FOR_IN);
/// children = [start, end, body]. First exercised by the stdlib corpus when
/// bounded_map's probe loops moved to the capped-scan `for i in 0..64` shape
/// (the loop-aware-budget arc).
const K_FOR_RANGE: i64 = 88;
const K_ERR: i64 = 900;
/// AST kinds this slice doesn't parse yet (the SIGIL parser never emits
/// this, so a corpus node of an unhandled kind is caught as a divergence).
const UNHANDLED: i64 = 901;

/// Does this kind carry text through the pool? The name-bearing kinds (incl.
/// a Call's callee path, a MethodCall's method name, and a RecordConstruct's
/// `type;field1;field2;…`) plus K_LIT_STR (whose text is the DECODED string
/// value, ET-3). Mirrors `parser_kind_has_text`.
fn kind_has_text(k: i64) -> bool {
    matches!(
        k,
        K_MODULE
            | K_FN
            | K_TYPE_FN
            | K_TYPE
            | K_PATH
            | K_LIT_STR
            | K_CALL
            | K_METHOD
            | K_RECORD_CONSTRUCT
            | K_LET
            | K_LET_TUPLE
            | K_FOR_IN
            | K_FOR_RANGE
            | K_PAT_LIT_STR
            | K_PAT_BINDING
            | K_PAT_ENUM
            | K_PAT_ARRAY
            | K_PARAM
            | K_USE
            | K_CONST
            | K_RECORD_DEF
            | K_FIELD
            | K_TYPE_PARAM
            | K_ENUM_DEF
            | K_ENUM_VARIANT
            | K_ENUM_FIELD
            | K_IMPL
            | K_TRAIT
            | K_TRAIT_SIG
            | K_EXTERN_FN
            | K_EFFECT_DECL
            | K_SEND
            | K_ASK
            | K_CAP_RESTRICT
            | K_CAP_RESTRICT_DEADLINE
            | K_CAP_SPLIT
            | K_CAP_DRAW
            | K_HANDLE
            | K_REGION
            | K_ACTOR
            | K_HANDLER
            | K_CAP_TYPE
            | K_REFINEMENT
            | K_TYPE_ALIAS
            | K_MINT
            | K_STATE_DEF
            | K_PERFORM
    )
}

// ── the TOTAL kind maps (ET-P9 — no `_` arm anywhere) ────────────────────────

// NOTE: every `Item` variant is now handled, so its ET-P9 drift-lock lives
// directly in `flatten_item` — a TOTAL match with NO `_` arm.

// NOTE: every `Stmt` and `Pattern` variant is now handled, so their ET-P9
// drift-locks live directly in `flatten_stmt` / `flatten_pattern` — both are
// TOTAL matches with NO `_` arm (a new Rust variant fails to compile there).

/// Taint label → its i64 code (1-4; absence is 0). TOTAL, no `_` (ET-P9).
fn taint_code_of(t: &TaintLabel) -> i64 {
    match t {
        TaintLabel::Public => 1,
        TaintLabel::Internal => 2,
        TaintLabel::Secret => 3,
        TaintLabel::SecretCT => 4,
    }
}

/// `@Flow` — taint polymorphism. Not a `TaintLabel` (it denotes "any of them"),
/// so it has no `taint_code_of` arm; it rides the same encoded field as the
/// concrete labels, one past `SecretCT`. Must match `parser_taint` and the
/// param-annotation loop in `selfhost/parser.sigil`.
const FLOW_TAINT_CODE: i64 = 5;

fn expr_kind_of(expr: &Expr) -> i64 {
    match expr {
        Expr::Binary(_) => K_BINARY,
        Expr::Literal(l) => match &l.literal {
            Literal::Int(_) => K_LIT_INT,
            // u256 PR-U2: wide literal is an int-literal kind. Never exercised —
            // the self-hosted parser doesn't lex wide literals (PR-U4 deferred).
            Literal::Int256(_) => K_LIT_INT,
            Literal::Bool(_) => K_LIT_BOOL,
            Literal::Float(_) => K_LIT_FLOAT,
            Literal::Str(_) => K_LIT_STR,
        },
        Expr::Path(_) => K_PATH,
        Expr::Borrow(_) => K_BORROW,
        Expr::Call(_) => K_CALL,
        Expr::MethodCall(_) => K_METHOD,
        Expr::Try(_) => K_TRY,
        Expr::Index(_) => K_INDEX,
        Expr::Slice(_) => K_SLICE,
        Expr::ResultCtor(_) => K_RESULT_CTOR,
        Expr::ArrayLit(_) => K_ARRAY,
        Expr::Tuple(_) => K_TUPLE,
        Expr::RecordConstruct(_) => K_RECORD_CONSTRUCT,
        Expr::Closure(_) => K_CLOSURE,
        Expr::Send(_) => K_SEND,
        Expr::Ask(_) => K_ASK,
        Expr::Spawn(_) => K_SPAWN,
        Expr::CapRestrict(_) => K_CAP_RESTRICT,
        Expr::CapRestrictDeadline(_) => K_CAP_RESTRICT_DEADLINE,
        Expr::CapSplit(_) => K_CAP_SPLIT,
        Expr::CapDraw(_) => K_CAP_DRAW,
        Expr::Mint(_) => K_MINT,
        Expr::Grant(_) => K_GRANT,
        Expr::Handle(_) => K_HANDLE,
        Expr::Declassify(_) => K_DECLASSIFY,
        Expr::DeclassifyCt(_) => K_DECLASSIFY_CT,
        Expr::Region(_) => K_REGION,
        // PR-E3: f-string node (`Expr::FString`). The SIGIL parser will emit the
        // matching `P_K_FSTRING` once the self-hosted mirror lands.
        Expr::FString(_) => K_FSTRING,
        // NEVER parser-produced (built during type-check, like FieldAccess) —
        // no corpus can cover them; the SIGIL parser never emits them either.
        Expr::EnumConstruct(_) | Expr::FieldAccess(_) => UNHANDLED,
        // Effect Handlers (EH0b): `perform`/clause-`handle` are mirrored as
        // leaves (Perform has an explicit flatten arm; ClauseHandle uses the
        // flatten catch-all). `resume` lives only inside a clause body, which a
        // clause-handle leaf consumes without emitting — so it is never
        // flattened and maps to UNHANDLED.
        Expr::Perform(_) => K_PERFORM,
        Expr::ClauseHandle(_) => K_CLAUSE_HANDLE,
        Expr::Resume(_) => UNHANDLED,
    }
}

/// One refinement clause → a leaf node: text = the LHS (a field name, or `@`
/// for a return refinement); flags = op-code + literal*8. Field / length-of
/// RHS forms are a later slice.
fn flatten_refinement(c: &sigil_compiler::ast::RefinementClause, out: &mut Vec<FlatNode>) {
    use sigil_compiler::ast::{RefinementOp, RefinementRhs};
    let op = match c.op {
        RefinementOp::Le => 1,
        RefinementOp::Lt => 2,
        RefinementOp::Ge => 3,
        RefinementOp::Gt => 4,
        RefinementOp::Eq => 5,
        RefinementOp::Ne => 6,
    };
    let lit = match &c.rhs {
        RefinementRhs::Literal(v) => *v,
        // u256 PR-U3-b2: a wide (LiteralWide) refinement bound is not in the
        // self-host differential corpus (PR-U4 deferred) — treat as unhandled,
        // like Field/LengthOf.
        RefinementRhs::Field(_) | RefinementRhs::LengthOf(_) | RefinementRhs::LiteralWide(_) => {
            out.push(FlatNode {
                kind: UNHANDLED,
                start: c.span.start as i64,
                end: c.span.end as i64,
                value: 0,
                flags: 0,
                child_count: 0,
                text: None,
            });
            return;
        }
    };
    out.push(FlatNode {
        kind: K_REFINEMENT,
        start: c.span.start as i64,
        end: c.span.end as i64,
        value: c.field.len() as i64,
        flags: op + lit * 8,
        child_count: 0,
        text: Some(c.field.clone()),
    });
}

/// Binary operator → its i64 code. Reuses the LEXER's operator token tags
/// (T_PLUS=19 etc.) — "the lexer's value conventions where they overlap". TOTAL.
fn op_code_of(op: &BinaryOp) -> i64 {
    match op {
        BinaryOp::Add => 19,
        BinaryOp::Sub => 20,
        BinaryOp::Mul => 21,
        BinaryOp::Div => 22,
        BinaryOp::Mod => 23,
        BinaryOp::Lt => 25,
        BinaryOp::Gt => 26,
        BinaryOp::BitAnd => 27,
        BinaryOp::BitOr => 28,
        BinaryOp::LogicalAnd => 125,
        BinaryOp::LogicalOr => 126,
        BinaryOp::Eq => 105,
        BinaryOp::NotEq => 107,
        BinaryOp::LtEq => 108,
        BinaryOp::GtEq => 109,
        BinaryOp::Shl => 110,
        BinaryOp::Shr => 112,
    }
}

// ── the oracle flattener (the SAME canonical pre-order as parser_emit) ───────

/// One flattened node — the compared tuple (ET-P2): kind, span, value, flags,
/// child_count, and the name text for name-bearing kinds.
#[derive(Debug, Clone, PartialEq)]
struct FlatNode {
    kind: i64,
    start: i64,
    end: i64,
    value: i64,
    flags: i64,
    child_count: i64,
    text: Option<String>,
}

fn flatten_module(m: &Module, out: &mut Vec<FlatNode>) {
    use sigil_compiler::ast::Ring;
    // flags = ring-outer + trusted*2 + pub*4; the attributes never extend the span.
    let flags = i64::from(matches!(m.ring, Ring::Outer))
        + 2 * i64::from(m.trusted)
        + 4 * i64::from(matches!(m.visibility, Visibility::Public));
    out.push(FlatNode {
        kind: K_MODULE,
        start: m.span.start as i64,
        end: m.span.end as i64,
        value: m.name.len() as i64,
        flags,
        child_count: m.items.len() as i64,
        text: Some(m.name.clone()),
    });
    for item in &m.items {
        flatten_item(item, out);
    }
}

/// SH-PARSE-MM: flatten a whole `Program`. ONE module → the bare K_MODULE root
/// (byte-identical to before — ET-PMM-1); >1 → a K_PROGRAM wrapper (start = first
/// module start, end = last module end) followed by each module in source order.
/// Mirrors `selfhost/parser.sigil`'s `parser_parse`.
fn flatten_program(modules: &[Module], out: &mut Vec<FlatNode>) {
    if modules.len() == 1 {
        flatten_module(&modules[0], out);
        return;
    }
    let first = &modules[0];
    let last = &modules[modules.len() - 1];
    out.push(FlatNode {
        kind: K_PROGRAM,
        start: first.span.start as i64,
        end: last.span.end as i64,
        value: 0,
        flags: 0,
        child_count: modules.len() as i64,
        text: None,
    });
    for m in modules {
        flatten_module(m, out);
    }
}

/// A const's literal value rendered into the pool text: `name;<rendering>`.
/// Float consts are a later slice (None → the caller flattens UNHANDLED).
fn render_const_literal(l: &Literal) -> Option<(String, i64)> {
    match l {
        Literal::Int(v) => Some((v.to_string(), 0)),
        Literal::Bool(b) => Some((if *b { "true" } else { "false" }.to_string(), 1)),
        Literal::Str(s) => Some((s.clone(), 2)),
        Literal::Float(_) => None,
        // u256 PR-U2: wide const literals are not in the self-host differential
        // corpus (PR-U4 deferred) — treat as unhandled, like Float.
        Literal::Int256(_) => None,
    }
}

fn flatten_type_param(tp: &sigil_compiler::ast::TypeParam, out: &mut Vec<FlatNode>) {
    use sigil_compiler::ast::ParamKind;
    // text = `name` or `name;bound1;…`; the span covers the NAME only.
    let mut text = tp.name.clone();
    for b in &tp.bounds {
        text.push(';');
        text.push_str(b);
    }
    // R2: the parameter KIND rides `flags` (was hardcoded 0 — so `<S>` vs `<@S>`
    // vs `<F: * -> *>` were indistinguishable in the flattened stream, a latent
    // under-modeling predating the HKT/typestate epics). 0 = Star (an ordinary
    // value generic `T` / `T: Bound`); 1 = State (`<@S>`, typestate); 1+arity =
    // Constructor (`<F: * -> *>` is arity 1 → 2, `<M: * -> * -> *>` → 3). The
    // self-hosted `parser.sigil` type-param emit MUST compute the same code.
    let flags = match tp.kind {
        ParamKind::Star => 0,
        ParamKind::State => 1,
        ParamKind::Constructor { arity } => 1 + arity as i64,
    };
    out.push(FlatNode {
        kind: K_TYPE_PARAM,
        start: tp.span.start as i64,
        end: tp.span.end as i64,
        value: text.len() as i64,
        flags,
        child_count: 0,
        text: Some(text),
    });
}

fn flatten_fn(f: &sigil_compiler::ast::FnDef, out: &mut Vec<FlatNode>) {
    // Region outlives (`where region(a): region(b)`) is a later slice.
    let not_yet = !f.region_outlives.is_empty();
    if not_yet {
        out.push(FlatNode {
            kind: UNHANDLED,
            start: f.span.start as i64,
            end: f.span.end as i64,
            value: 0,
            flags: 0,
            child_count: 0,
            text: None,
        });
        return;
    }
    // text = name + the effect suffix: None → bare; Some(effs) → `;!` then
    // `;eff` each (the `!` marker keeps no-row and empty-row distinct).
    let mut text = f.name.clone();
    if let Some(effs) = &f.effects {
        text.push_str(";!");
        for e in effs {
            text.push(';');
            text.push_str(e);
        }
    }
    // The canonical FN child order:
    // [type-param…, param…, return-type?, param-ref…, ret-ref?, body].
    let child_count = f.type_params.len() as i64
        + f.params.len() as i64
        + i64::from(f.return_type.is_some())
        + f.param_refinements.len() as i64
        + i64::from(f.return_refinement.is_some())
        + 1;
    // flags = the pub bit + the return-taint code in bits 1-3. `@Flow` (taint
    // polymorphism) is code 5: it is mutually exclusive with `ret_taint`, and
    // the self-host parser encodes it in the same field, so it must appear here
    // or the two disagree on every `@Flow` signature.
    let ret_taint_code = if f.ret_flow {
        FLOW_TAINT_CODE
    } else {
        f.ret_taint.as_ref().map_or(0, taint_code_of)
    };
    let flags = i64::from(matches!(f.visibility, Visibility::Public)) + ret_taint_code * 2;
    out.push(FlatNode {
        kind: K_FN,
        start: f.span.start as i64,
        end: f.span.end as i64,
        value: text.len() as i64,
        flags,
        child_count,
        text: Some(text),
    });
    for tp in &f.type_params {
        flatten_type_param(tp, out);
    }
    for p in &f.params {
        flatten_param(p, out);
    }
    if let Some(rt) = &f.return_type {
        flatten_type(rt, out);
    }
    for c in &f.param_refinements {
        flatten_refinement(c, out);
    }
    if let Some(rr) = &f.return_refinement {
        flatten_refinement(rr, out);
    }
    flatten_block(&f.body, out);
}

fn flatten_item(item: &Item, out: &mut Vec<FlatNode>) {
    match item {
        Item::FnDef(f) => flatten_fn(f, out),
        Item::UseDecl(u) => {
            let name = u.path.segments.join("::");
            out.push(FlatNode {
                kind: K_USE,
                start: u.span.start as i64,
                end: u.span.end as i64,
                value: name.len() as i64,
                flags: i64::from(matches!(u.visibility, Visibility::Public)),
                child_count: 0,
                text: Some(name),
            });
        }
        Item::ConstDef(c) => {
            let Some((rendering, littype)) = render_const_literal(&c.value) else {
                out.push(FlatNode {
                    kind: UNHANDLED,
                    start: c.span.start as i64,
                    end: c.span.end as i64,
                    value: 0,
                    flags: 0,
                    child_count: 0,
                    text: None,
                });
                return;
            };
            let mut text = c.name.clone();
            text.push(';');
            text.push_str(&rendering);
            out.push(FlatNode {
                kind: K_CONST,
                start: c.span.start as i64,
                end: c.span.end as i64,
                value: text.len() as i64,
                flags: i64::from(matches!(c.visibility, Visibility::Public)) + littype * 2,
                child_count: 1,
                text: Some(text),
            });
            flatten_type(&c.ty, out);
        }
        // PR-E4: `type Name = Body;` — name on `text`, public bit on `flags`, the body
        // type as the single child (shared type grammar). The self-hosted P_K_TYPE_ALIAS
        // node must match node-for-node.
        Item::TypeAlias(a) => {
            out.push(FlatNode {
                kind: K_TYPE_ALIAS,
                start: a.span.start as i64,
                end: a.span.end as i64,
                value: a.name.len() as i64,
                flags: i64::from(matches!(a.visibility, Visibility::Public)),
                child_count: 1,
                text: Some(a.name.clone()),
            });
            flatten_type(&a.body, out);
        }
        Item::RecordDef(r) => {
            // Refinement clauses are children, but a record-level `where`
            // sits OUTSIDE the record's span (the oracle closes the span at
            // `}` before the clause parses — the ET-P6 exemption).
            out.push(FlatNode {
                kind: K_RECORD_DEF,
                start: r.span.start as i64,
                end: r.span.end as i64,
                value: r.name.len() as i64,
                flags: i64::from(matches!(r.visibility, Visibility::Public)),
                child_count: r.type_params.len() as i64
                    + r.fields.len() as i64
                    + r.refinements.len() as i64,
                text: Some(r.name.clone()),
            });
            for tp in &r.type_params {
                flatten_type_param(tp, out);
            }
            for fld in &r.fields {
                out.push(FlatNode {
                    kind: K_FIELD,
                    start: fld.span.start as i64,
                    end: fld.span.end as i64,
                    value: fld.name.len() as i64,
                    flags: 0,
                    child_count: 1,
                    text: Some(fld.name.clone()),
                });
                flatten_type(&fld.ty, out);
            }
            for c in &r.refinements {
                flatten_refinement(c, out);
            }
        }
        Item::EnumDef(e) => {
            out.push(FlatNode {
                kind: K_ENUM_DEF,
                start: e.span.start as i64,
                end: e.span.end as i64,
                value: e.name.len() as i64,
                flags: i64::from(matches!(e.visibility, Visibility::Public)),
                child_count: e.type_params.len() as i64 + e.variants.len() as i64,
                text: Some(e.name.clone()),
            });
            for tp in &e.type_params {
                flatten_type_param(tp, out);
            }
            for v in &e.variants {
                out.push(FlatNode {
                    kind: K_ENUM_VARIANT,
                    start: v.span.start as i64,
                    end: v.span.end as i64,
                    value: v.name.len() as i64,
                    flags: 0,
                    child_count: v.fields.len() as i64 + v.refinements.len() as i64,
                    text: Some(v.name.clone()),
                });
                for vf in &v.fields {
                    let fname = vf.name.clone().unwrap_or_default();
                    out.push(FlatNode {
                        kind: K_ENUM_FIELD,
                        start: vf.span.start as i64,
                        end: vf.span.end as i64,
                        value: fname.len() as i64,
                        flags: 0,
                        child_count: 1,
                        text: Some(fname),
                    });
                    flatten_type(&vf.ty, out);
                }
                for c in &v.refinements {
                    flatten_refinement(c, out);
                }
            }
        }
        Item::ImplDef(i) => {
            // text = `trait;type` (the trait EMPTY for an inherent impl).
            let mut text = i.trait_name.clone().unwrap_or_default();
            text.push(';');
            text.push_str(&i.type_name);
            out.push(FlatNode {
                kind: K_IMPL,
                start: i.span.start as i64,
                end: i.span.end as i64,
                value: text.len() as i64,
                flags: 0,
                child_count: i.type_params.len() as i64 + i.methods.len() as i64,
                text: Some(text),
            });
            for tp in &i.type_params {
                flatten_type_param(tp, out);
            }
            for m in &i.methods {
                flatten_fn(m, out);
            }
        }
        Item::TraitDef(t) => {
            out.push(FlatNode {
                kind: K_TRAIT,
                start: t.span.start as i64,
                end: t.span.end as i64,
                value: t.name.len() as i64,
                flags: i64::from(matches!(t.visibility, Visibility::Public)),
                child_count: t.methods.len() as i64,
                text: Some(t.name.clone()),
            });
            for sig in &t.methods {
                out.push(FlatNode {
                    kind: K_TRAIT_SIG,
                    start: sig.span.start as i64,
                    end: sig.span.end as i64,
                    value: sig.name.len() as i64,
                    flags: 0,
                    child_count: sig.params.len() as i64 + i64::from(sig.return_type.is_some()),
                    text: Some(sig.name.clone()),
                });
                for p in &sig.params {
                    flatten_param(p, out);
                }
                if let Some(rt) = &sig.return_type {
                    flatten_type(rt, out);
                }
            }
        }
        Item::ExternFnDecl(x) => {
            // text = `abi;name(;eff)*` — the extern row is a PLAIN Vec;
            // flags = the return-taint code (externs have no pub bit).
            let mut text = x.abi.clone();
            text.push(';');
            text.push_str(&x.name);
            for e in &x.effects {
                text.push(';');
                text.push_str(e);
            }
            out.push(FlatNode {
                kind: K_EXTERN_FN,
                start: x.span.start as i64,
                end: x.span.end as i64,
                value: text.len() as i64,
                flags: x.ret_taint.as_ref().map_or(0, taint_code_of),
                child_count: x.params.len() as i64 + i64::from(x.return_type.is_some()),
                text: Some(text),
            });
            for p in &x.params {
                flatten_param(p, out);
            }
            if let Some(rt) = &x.return_type {
                flatten_type(rt, out);
            }
        }
        // Effect Handlers (EH0b): `effect Name { fn op(..) -> Ty; .. }`. A LEAF —
        // text = `Name(;op)*` (the operation NAMES ride the text, joined `;`,
        // like StateDef's markers); a bare `effect Name;` is just `Name` (no
        // suffix), so existing fixtures are unchanged. span = `effect`..name-end
        // (the operations do not extend the decl span — parity with the oracle).
        Item::EffectDecl(e) => {
            let mut text = e.name.clone();
            for op in &e.ops {
                text.push(';');
                text.push_str(&op.name);
            }
            out.push(FlatNode {
                kind: K_EFFECT_DECL,
                start: e.span.start as i64,
                end: e.span.end as i64,
                value: text.len() as i64,
                flags: 0,
                child_count: 0,
                text: Some(text),
            });
        }
        // Typestate (Epic 1, R3): `[pub] state Name { S1, S2, … }`. text =
        // `Name;S1;S2;…` (protocol name + its closed marker set, joined `;` —
        // idents are `;`-free); value = text.len(); flags = the public bit; a
        // leaf (markers ride `text`); span = (pub|state)..`}`. The self-hosted
        // `parser.sigil` P_K_STATE_DEF node MUST emit this same shape.
        Item::StateDef(s) => {
            let mut text = s.name.clone();
            for m in &s.states {
                text.push(';');
                text.push_str(m);
            }
            out.push(FlatNode {
                kind: K_STATE_DEF,
                start: s.span.start as i64,
                end: s.span.end as i64,
                value: text.len() as i64,
                flags: i64::from(matches!(s.visibility, Visibility::Public)),
                child_count: 0,
                text: Some(text),
            });
        }
        Item::ActorDef(a) => {
            // Children commit in SLOT order regardless of source order (the
            // oracle stores state/init/handlers in three fields):
            // [state-field…, init?, handler…]. flags = pub + entry*2.
            out.push(FlatNode {
                kind: K_ACTOR,
                start: a.span.start as i64,
                end: a.span.end as i64,
                value: a.name.len() as i64,
                flags: i64::from(matches!(a.visibility, Visibility::Public))
                    + 2 * i64::from(a.is_entry),
                child_count: a.state_fields.len() as i64
                    + i64::from(a.init.is_some())
                    + a.handlers.len() as i64,
                text: Some(a.name.clone()),
            });
            for fld in &a.state_fields {
                out.push(FlatNode {
                    kind: K_FIELD,
                    start: fld.span.start as i64,
                    end: fld.span.end as i64,
                    value: fld.name.len() as i64,
                    flags: 0,
                    child_count: 1,
                    text: Some(fld.name.clone()),
                });
                flatten_type(&fld.ty, out);
            }
            if let Some(init) = &a.init {
                out.push(FlatNode {
                    kind: K_ACTOR_INIT,
                    start: init.span.start as i64,
                    end: init.span.end as i64,
                    value: 0,
                    flags: 0,
                    child_count: init.params.len() as i64 + 1,
                    text: None,
                });
                for p in &init.params {
                    flatten_param(p, out);
                }
                flatten_block(&init.body, out);
            }
            for h in &a.handlers {
                out.push(FlatNode {
                    kind: K_HANDLER,
                    start: h.span.start as i64,
                    end: h.span.end as i64,
                    value: h.message_name.len() as i64,
                    flags: 0,
                    child_count: h.params.len() as i64 + i64::from(h.return_type.is_some()) + 1,
                    text: Some(h.message_name.clone()),
                });
                for p in &h.params {
                    flatten_param(p, out);
                }
                if let Some(rt) = &h.return_type {
                    flatten_type(rt, out);
                }
                flatten_block(&h.body, out);
            }
        }
        Item::CapTypeDef(c) => {
            // text = `name;auth,auth;param,param` — comma-joined sublists in
            // two `;`-separated slots. A leaf.
            let mut text = c.name.clone();
            text.push(';');
            text.push_str(&c.authorities.join(","));
            text.push(';');
            text.push_str(
                &c.params
                    .iter()
                    .map(|p| p.name.as_str())
                    .collect::<Vec<_>>()
                    .join(","),
            );
            out.push(FlatNode {
                kind: K_CAP_TYPE,
                start: c.span.start as i64,
                end: c.span.end as i64,
                value: text.len() as i64,
                flags: i64::from(matches!(c.visibility, Visibility::Public)),
                child_count: 0,
                text: Some(text),
            });
        }
    }
}

fn flatten_type(t: &TypeExpr, out: &mut Vec<FlatNode>) {
    let start = t.span.start as i64;
    let end = t.span.end as i64;
    if let Some(tt) = &t.tuple_type {
        out.push(FlatNode {
            kind: K_TYPE_TUPLE,
            start,
            end,
            value: 0,
            flags: 0,
            child_count: tt.len() as i64,
            text: None,
        });
        for e in tt {
            flatten_type(e, out);
        }
        return;
    }
    if let Some(at) = &t.array_type {
        out.push(FlatNode {
            kind: K_TYPE_ARRAY,
            start,
            end,
            value: i64::from(at.size),
            flags: 0,
            child_count: 1,
            text: None,
        });
        flatten_type(&at.elem, out);
        return;
    }
    if let Some(ft) = &t.fn_type {
        // text = the latent-row suffix in parser_effect_suffix's convention:
        // None -> "" (no row); Some(effs) -> ";!" then ";eff" each. The ";!"
        // marker alone is the EXPLICIT-EMPTY row, keeping None vs Some([])
        // distinct exactly as the K_FN name suffix does. value = text length.
        let mut text = String::new();
        if let Some(effs) = &ft.effects {
            text.push_str(";!");
            for e in effs {
                text.push(';');
                text.push_str(e);
            }
        }
        out.push(FlatNode {
            kind: K_TYPE_FN,
            start,
            end,
            value: text.len() as i64,
            flags: 0,
            child_count: ft.params.len() as i64 + 1,
            text: Some(text),
        });
        for p in &ft.params {
            flatten_type(p, out);
        }
        flatten_type(&ft.return_type, out);
        return;
    }
    // nominal: the ref is a FLAG on the node (the oracle hoists the inner's
    // path into the ref'd TypeExpr — no wrapper node): 0 plain / 1 `&` /
    // 2 `&mut` / 3 `&[slice]` (the slice form drops a `mut`, like the
    // oracle). Generic args are the children.
    use sigil_compiler::ast::RefKind;
    let flags = match &t.ref_kind {
        None => 0,
        Some(RefKind::Ref(false)) => 1,
        Some(RefKind::Ref(true)) => 2,
        Some(RefKind::Slice) => 3,
    };
    let mut name = t.path.segments.join("::");
    // parametric-cap USAGE values (`Approval(2030)`) append `;<value>` each.
    for d in &t.deadline {
        name.push(';');
        name.push_str(&d.to_string());
    }
    out.push(FlatNode {
        kind: K_TYPE,
        start,
        end,
        value: name.len() as i64,
        flags,
        child_count: t.path.type_args.len() as i64,
        text: Some(name),
    });
    for a in &t.path.type_args {
        flatten_type(a, out);
    }
}

fn flatten_param(p: &sigil_compiler::ast::Param, out: &mut Vec<FlatNode>) {
    use sigil_compiler::ast::Mutability;
    // text = the name, or `name;region` for an `@in r` param; flags =
    // mut-code (0/1/2) + taint*4 + has-region*32; span = name..type (the
    // oracle's param_span excludes the annotations).
    let mcode = match p.mutability {
        Mutability::Default => 0,
        Mutability::ReadOnly => 1,
        Mutability::Mut => 2,
    };
    // `@Flow` rides the taint field as code 5 (see FLOW_TAINT_CODE); it is
    // mutually exclusive with a concrete label, so the two never collide.
    let taint = if p.flow {
        FLOW_TAINT_CODE
    } else {
        p.taint.as_ref().map_or(0, taint_code_of)
    };
    let mut text = p.name.clone();
    if let Some(r) = &p.region {
        text.push(';');
        text.push_str(r);
    }
    out.push(FlatNode {
        kind: K_PARAM,
        start: p.span.start as i64,
        end: p.span.end as i64,
        value: text.len() as i64,
        flags: mcode + taint * 4 + i64::from(p.region.is_some()) * 32,
        child_count: 1,
        text: Some(text),
    });
    flatten_type(&p.ty, out);
}

fn flatten_block(b: &Block, out: &mut Vec<FlatNode>) {
    out.push(FlatNode {
        kind: K_BLOCK,
        start: b.span.start as i64,
        end: b.span.end as i64,
        value: 0,
        flags: 0,
        child_count: b.statements.len() as i64,
        text: None,
    });
    for s in &b.statements {
        flatten_stmt(s, out);
    }
}

fn flatten_stmt(s: &Stmt, out: &mut Vec<FlatNode>) {
    match s {
        Stmt::Return(r) => {
            out.push(FlatNode {
                kind: K_RETURN,
                start: r.span.start as i64,
                end: r.span.end as i64,
                value: 0,
                flags: 0,
                child_count: i64::from(r.value.is_some()),
                text: None,
            });
            if let Some(v) = &r.value {
                flatten_expr(v, out);
            }
        }
        Stmt::Let(l) => {
            // text = the name; flags = mut-bit | taint<<1; children [ty?, value].
            let taint = l.taint.as_ref().map_or(0, taint_code_of);
            out.push(FlatNode {
                kind: K_LET,
                start: l.span.start as i64,
                end: l.span.end as i64,
                value: l.name.len() as i64,
                flags: i64::from(l.mutable) + taint * 2,
                child_count: i64::from(l.ty.is_some()) + 1,
                text: Some(l.name.clone()),
            });
            if let Some(ty) = &l.ty {
                flatten_type(ty, out);
            }
            flatten_expr(&l.value, out);
        }
        Stmt::LetTuple(lt) => {
            // text = names joined `;`; flags = the per-binding mut bitmask.
            let names = lt
                .bindings
                .iter()
                .map(|(n, _)| n.as_str())
                .collect::<Vec<_>>()
                .join(";");
            let flags: i64 = lt
                .bindings
                .iter()
                .enumerate()
                .map(|(i, (_, m))| i64::from(*m) << i)
                .sum();
            out.push(FlatNode {
                kind: K_LET_TUPLE,
                start: lt.span.start as i64,
                end: lt.span.end as i64,
                value: names.len() as i64,
                flags,
                child_count: i64::from(lt.ty.is_some()) + 1,
                text: Some(names),
            });
            if let Some(ty) = &lt.ty {
                flatten_type(ty, out);
            }
            flatten_expr(&lt.value, out);
        }
        Stmt::Assign(a) => {
            // value = the kept compound-op code (field/index places), 0 when
            // plain — a LOCAL compound was already desugared at parse time.
            out.push(FlatNode {
                kind: K_ASSIGN,
                start: a.span.start as i64,
                end: a.span.end as i64,
                value: a.op.as_ref().map_or(0, op_code_of),
                flags: 0,
                child_count: 2,
                text: None,
            });
            flatten_expr(&a.target, out);
            flatten_expr(&a.value, out);
        }
        Stmt::Expr(e) => {
            out.push(FlatNode {
                kind: K_EXPR_STMT,
                start: e.span.start as i64,
                end: e.span.end as i64,
                value: 0,
                flags: 0,
                child_count: 1,
                text: None,
            });
            flatten_expr(&e.expr, out);
        }
        Stmt::If(i) => {
            // the else branch is REQUIRED (the oracle's P016): three children.
            out.push(FlatNode {
                kind: K_IF,
                start: i.span.start as i64,
                end: i.span.end as i64,
                value: 0,
                flags: 0,
                child_count: 3,
                text: None,
            });
            flatten_expr(&i.condition, out);
            flatten_block(&i.then_branch, out);
            flatten_block(&i.else_branch, out);
        }
        Stmt::While(w) => {
            out.push(FlatNode {
                kind: K_WHILE,
                start: w.span.start as i64,
                end: w.span.end as i64,
                value: 0,
                flags: 0,
                child_count: 2,
                text: None,
            });
            flatten_expr(&w.condition, out);
            flatten_block(&w.body, out);
        }
        Stmt::ForIn(f) => {
            out.push(FlatNode {
                kind: K_FOR_IN,
                start: f.span.start as i64,
                end: f.span.end as i64,
                value: f.var.len() as i64,
                flags: 0,
                child_count: 2,
                text: Some(f.var.clone()),
            });
            flatten_expr(&f.iterable, out);
            flatten_block(&f.body, out);
        }
        Stmt::ForRange(f) => {
            out.push(FlatNode {
                kind: K_FOR_RANGE,
                start: f.span.start as i64,
                end: f.span.end as i64,
                value: f.var.len() as i64,
                flags: 0,
                child_count: 3,
                text: Some(f.var.clone()),
            });
            flatten_expr(&f.start, out);
            flatten_expr(&f.end, out);
            flatten_block(&f.body, out);
        }
        Stmt::Break(span) => out.push(FlatNode {
            kind: K_BREAK,
            start: span.start as i64,
            end: span.end as i64,
            value: 0,
            flags: 0,
            child_count: 0,
            text: None,
        }),
        Stmt::Continue(span) => out.push(FlatNode {
            kind: K_CONTINUE,
            start: span.start as i64,
            end: span.end as i64,
            value: 0,
            flags: 0,
            child_count: 0,
            text: None,
        }),
        Stmt::Match(m) => {
            out.push(FlatNode {
                kind: K_MATCH,
                start: m.span.start as i64,
                end: m.span.end as i64,
                value: 0,
                flags: 0,
                child_count: 1 + m.arms.len() as i64,
                text: None,
            });
            flatten_expr(&m.scrutinee, out);
            for arm in &m.arms {
                flatten_match_arm(arm, out);
            }
        }
    }
}

fn flatten_match_arm(arm: &MatchArm, out: &mut Vec<FlatNode>) {
    // children [pattern, guard?, body]; flags bit0 = has-guard.
    out.push(FlatNode {
        kind: K_MATCH_ARM,
        start: arm.span.start as i64,
        end: arm.span.end as i64,
        value: 0,
        flags: i64::from(arm.guard.is_some()),
        child_count: 2 + i64::from(arm.guard.is_some()),
        text: None,
    });
    flatten_pattern(&arm.pattern, out);
    if let Some(g) = &arm.guard {
        flatten_expr(g, out);
    }
    flatten_block(&arm.body, out);
}

fn flatten_pattern(p: &Pattern, out: &mut Vec<FlatNode>) {
    let span = p.span();
    let (kind, value, flags, text) = match p {
        Pattern::Literal(l) => match &l.literal {
            Literal::Int(v) => (K_PAT_LIT, *v, 0, None),
            Literal::Bool(b) => (K_PAT_LIT, i64::from(*b), 1, None),
            Literal::Str(s) => (K_PAT_LIT_STR, s.len() as i64, 0, Some(s.clone())),
            Literal::Float(_) => (UNHANDLED, 0, 0, None),
            // u256 PR-U2: wide-int match patterns are rejected by the compiler
            // and absent from the self-host corpus — unhandled.
            Literal::Int256(_) => (UNHANDLED, 0, 0, None),
        },
        Pattern::Range(r) => match (&r.lo, &r.hi) {
            // int bounds only (the shape real code uses): value = lo, flags = hi.
            (Literal::Int(lo), Literal::Int(hi)) => (K_PAT_RANGE, *lo, *hi, None),
            _ => (UNHANDLED, 0, 0, None),
        },
        Pattern::Wildcard(_) => (K_PAT_WILDCARD, 0, 0, None),
        Pattern::Binding(b) => (K_PAT_BINDING, b.name.len() as i64, 0, Some(b.name.clone())),
        Pattern::EnumVariant(ev) => {
            // `type;variant;binding…` — the type name is EMPTY for the bare
            // form (`Some(x)` → `;Some;x`), mirroring the inferred type_name.
            let mut t = ev.type_name.clone();
            t.push(';');
            t.push_str(&ev.variant);
            for b in &ev.bindings {
                t.push(';');
                t.push_str(b);
            }
            (K_PAT_ENUM, t.len() as i64, 0, Some(t))
        }
        // Array pattern `[a, _, ..rest]` (Phase 5). value = fixed-element count;
        // flags = rest kind (0 none / 1 anon `..` / 2 named `..name`); text =
        // `;`-joined element words (a binding's name, or `_` for a wildcard)
        // followed by the rest name iff named. The self-hosted parser emits the
        // byte-identical encoding.
        Pattern::Array(ap) => {
            let mut words: Vec<String> = ap
                .elements
                .iter()
                .map(|el| match el {
                    ArrayElem::Bind(name, _) => name.clone(),
                    ArrayElem::Wild(_) => "_".to_owned(),
                })
                .collect();
            let rest_kind = match &ap.rest {
                None => 0,
                Some(r) => match &r.name {
                    None => 1,
                    Some(n) => {
                        words.push(n.clone());
                        2
                    }
                },
            };
            // Kind 28 carries text (see `kind_has_text`), so `value` is the text
            // BYTE LENGTH (the harness slices `value` bytes from the pool), and the
            // empty word-list (`[]` / `[..]`) is `Some("")`. `flags` distinguishes
            // `[]` (0) from `[..]` (1); the element count is implicit in the text.
            let joined = words.join(";");
            (K_PAT_ARRAY, joined.len() as i64, rest_kind, Some(joined))
        }
    };
    out.push(FlatNode {
        kind,
        start: span.start as i64,
        end: span.end as i64,
        value,
        flags,
        child_count: 0,
        text,
    });
}

fn flatten_expr(e: &Expr, out: &mut Vec<FlatNode>) {
    match e {
        Expr::Binary(b) => {
            out.push(FlatNode {
                kind: K_BINARY,
                start: b.span.start as i64,
                end: b.span.end as i64,
                value: op_code_of(&b.op),
                flags: 0,
                child_count: 2,
                text: None,
            });
            flatten_expr(&b.lhs, out);
            flatten_expr(&b.rhs, out);
        }
        Expr::Literal(l) => {
            // Int carries its i64; Bool 1/0; Float is span-only (value 0 —
            // AG-P4 inherits AG-L3); Str carries the DECODED text (ET-3).
            let (kind, value, text) = match &l.literal {
                Literal::Int(v) => (K_LIT_INT, *v, None),
                Literal::Bool(b) => (K_LIT_BOOL, i64::from(*b), None),
                Literal::Float(_) => (K_LIT_FLOAT, 0, None),
                Literal::Str(s) => (K_LIT_STR, s.len() as i64, Some(s.clone())),
                // u256 PR-U2: wide literals aren't in the self-host corpus (PR-U4).
                Literal::Int256(_) => (UNHANDLED, 0, None),
            };
            out.push(FlatNode {
                kind,
                start: l.span.start as i64,
                end: l.span.end as i64,
                value,
                flags: 0,
                child_count: 0,
                text,
            });
        }
        Expr::Borrow(b) => {
            out.push(FlatNode {
                kind: K_BORROW,
                start: b.span.start as i64,
                end: b.span.end as i64,
                value: 0,
                flags: i64::from(b.mutable),
                child_count: 1,
                text: None,
            });
            flatten_expr(&b.inner, out);
        }
        Expr::Call(c) => {
            // Turbofish type-args are a later slice (PR-4 types).
            if c.callee.type_args.is_empty() {
                let name = c.callee.segments.join("::");
                out.push(FlatNode {
                    kind: K_CALL,
                    start: c.span.start as i64,
                    end: c.span.end as i64,
                    value: name.len() as i64,
                    flags: 0,
                    child_count: c.args.len() as i64,
                    text: Some(name),
                });
                for a in &c.args {
                    flatten_expr(a, out);
                }
            } else {
                out.push(FlatNode {
                    kind: UNHANDLED,
                    start: c.span.start as i64,
                    end: c.span.end as i64,
                    value: 0,
                    flags: 0,
                    child_count: 0,
                    text: None,
                });
            }
        }
        Expr::MethodCall(m) => {
            out.push(FlatNode {
                kind: K_METHOD,
                start: m.span.start as i64,
                end: m.span.end as i64,
                value: m.method.len() as i64,
                flags: 0,
                child_count: 1 + m.args.len() as i64,
                text: Some(m.method.clone()),
            });
            flatten_expr(&m.receiver, out);
            for a in &m.args {
                flatten_expr(a, out);
            }
        }
        Expr::Try(t) => {
            out.push(FlatNode {
                kind: K_TRY,
                start: t.span.start as i64,
                end: t.span.end as i64,
                value: 0,
                flags: 0,
                child_count: 1,
                text: None,
            });
            flatten_expr(&t.value, out);
        }
        Expr::Index(i) => {
            out.push(FlatNode {
                kind: K_INDEX,
                start: i.span.start as i64,
                end: i.span.end as i64,
                value: 0,
                flags: 0,
                child_count: 2,
                text: None,
            });
            flatten_expr(&i.array, out);
            flatten_expr(&i.index, out);
        }
        Expr::Slice(s) => {
            // flags bit0 = has-start, bit1 = has-end; children [array, start?, end?].
            let flags = i64::from(s.start.is_some()) + 2 * i64::from(s.end.is_some());
            let child_count = 1 + i64::from(s.start.is_some()) + i64::from(s.end.is_some());
            out.push(FlatNode {
                kind: K_SLICE,
                start: s.span.start as i64,
                end: s.span.end as i64,
                value: 0,
                flags,
                child_count,
                text: None,
            });
            flatten_expr(&s.array, out);
            if let Some(lo) = &s.start {
                flatten_expr(lo, out);
            }
            if let Some(hi) = &s.end {
                flatten_expr(hi, out);
            }
        }
        Expr::ResultCtor(r) => {
            out.push(FlatNode {
                kind: K_RESULT_CTOR,
                start: r.span.start as i64,
                end: r.span.end as i64,
                value: 0,
                flags: i64::from(r.is_ok),
                child_count: 1,
                text: None,
            });
            flatten_expr(&r.value, out);
        }
        Expr::Send(s) => {
            // text = the target path (joined `::`); child = [message].
            let name = s.target.segments.join("::");
            out.push(FlatNode {
                kind: K_SEND,
                start: s.span.start as i64,
                end: s.span.end as i64,
                value: name.len() as i64,
                flags: 0,
                child_count: 1,
                text: Some(name),
            });
            flatten_expr(&s.message, out);
        }
        Expr::Ask(a) => {
            // children [message, timeout]; the label and bare forms are the
            // same AST.
            let name = a.target.segments.join("::");
            out.push(FlatNode {
                kind: K_ASK,
                start: a.span.start as i64,
                end: a.span.end as i64,
                value: name.len() as i64,
                flags: 0,
                child_count: 2,
                text: Some(name),
            });
            flatten_expr(&a.message, out);
            flatten_expr(&a.timeout, out);
        }
        Expr::Spawn(sp) => {
            use sigil_compiler::ast::SupervisionExpr;
            // children [actor-type, arg…, restart-expr?];
            // flags = 0 none / 1 Stop / 2 Restart.
            let (sflags, restart) = match &sp.supervision {
                None => (0, None),
                Some(SupervisionExpr::Stop) => (1, None),
                Some(SupervisionExpr::Restart { max_restarts }) => (2, Some(max_restarts)),
            };
            out.push(FlatNode {
                kind: K_SPAWN,
                start: sp.span.start as i64,
                end: sp.span.end as i64,
                value: 0,
                flags: sflags,
                child_count: 1 + sp.args.len() as i64 + i64::from(restart.is_some()),
                text: None,
            });
            flatten_type(&sp.actor, out);
            for arg in &sp.args {
                flatten_expr(arg, out);
            }
            if let Some(r) = restart {
                flatten_expr(r, out);
            }
        }
        Expr::CapRestrict(cr) => {
            // text = `cap-path;restriction`; a leaf.
            let mut name = cr.cap.segments.join("::");
            name.push(';');
            name.push_str(&cr.restriction);
            out.push(FlatNode {
                kind: K_CAP_RESTRICT,
                start: cr.span.start as i64,
                end: cr.span.end as i64,
                value: name.len() as i64,
                flags: 0,
                child_count: 0,
                text: Some(name),
            });
        }
        Expr::CapRestrictDeadline(cd) => {
            // text = the cap path; flags = the raw i64 deadline; a leaf.
            let name = cd.cap.segments.join("::");
            out.push(FlatNode {
                kind: K_CAP_RESTRICT_DEADLINE,
                start: cd.span.start as i64,
                end: cd.span.end as i64,
                value: name.len() as i64,
                flags: cd.deadline,
                child_count: 0,
                text: Some(name),
            });
        }
        Expr::CapSplit(cs) => {
            let name = cs.cap.segments.join("::");
            out.push(FlatNode {
                kind: K_CAP_SPLIT,
                start: cs.span.start as i64,
                end: cs.span.end as i64,
                value: name.len() as i64,
                flags: 0,
                child_count: 1,
                text: Some(name),
            });
            flatten_expr(&cs.amount, out);
        }
        Expr::CapDraw(cd) => {
            let name = cd.cap.segments.join("::");
            out.push(FlatNode {
                kind: K_CAP_DRAW,
                start: cd.span.start as i64,
                end: cd.span.end as i64,
                value: name.len() as i64,
                flags: 0,
                child_count: 1,
                text: Some(name),
            });
            flatten_expr(&cd.amount, out);
        }
        Expr::Grant(g) => {
            out.push(FlatNode {
                kind: K_GRANT,
                start: g.span.start as i64,
                end: g.span.end as i64,
                value: 0,
                flags: 0,
                child_count: 2,
                text: None,
            });
            flatten_expr(&g.cap, out);
            flatten_expr(&g.body, out);
        }
        Expr::Handle(h) => {
            // text = the handled effect names joined `;`; child = [body].
            let name = h.effects.join(";");
            out.push(FlatNode {
                kind: K_HANDLE,
                start: h.span.start as i64,
                end: h.span.end as i64,
                value: name.len() as i64,
                flags: 0,
                child_count: 1,
                text: Some(name),
            });
            flatten_block(&h.body, out);
        }
        Expr::Declassify(d) => {
            // children [value, cap]; flags = the optional target taint code
            // (the `@Label` sits OUTSIDE the span).
            out.push(FlatNode {
                kind: K_DECLASSIFY,
                start: d.span.start as i64,
                end: d.span.end as i64,
                value: 0,
                flags: d.target.as_ref().map_or(0, taint_code_of),
                child_count: 2,
                text: None,
            });
            flatten_expr(&d.value, out);
            flatten_expr(&d.cap, out);
        }
        Expr::DeclassifyCt(dc) => {
            out.push(FlatNode {
                kind: K_DECLASSIFY_CT,
                start: dc.span.start as i64,
                end: dc.span.end as i64,
                value: 0,
                flags: 0,
                child_count: 2,
                text: None,
            });
            flatten_expr(&dc.value, out);
            flatten_expr(&dc.cap, out);
        }
        Expr::Region(rg) => {
            // text = the region name; children [limit, body].
            out.push(FlatNode {
                kind: K_REGION,
                start: rg.span.start as i64,
                end: rg.span.end as i64,
                value: rg.name.len() as i64,
                flags: 0,
                child_count: 2,
                text: Some(rg.name.clone()),
            });
            flatten_expr(&rg.limit, out);
            flatten_block(&rg.body, out);
        }
        Expr::Closure(c) => {
            // [param…, return-type?, body] — the FN child-order subset.
            let child_count = c.params.len() as i64 + i64::from(c.return_type.is_some()) + 1;
            out.push(FlatNode {
                kind: K_CLOSURE,
                start: c.span.start as i64,
                end: c.span.end as i64,
                value: 0,
                flags: 0,
                child_count,
                text: None,
            });
            for p in &c.params {
                flatten_param(p, out);
            }
            if let Some(rt) = &c.return_type {
                flatten_type(rt, out);
            }
            flatten_block(&c.body, out);
        }
        Expr::ArrayLit(a) => {
            // The repeat form `[elem; N]` already expanded at parse time into
            // N cloned elements, so this arm covers both spellings.
            out.push(FlatNode {
                kind: K_ARRAY,
                start: a.span.start as i64,
                end: a.span.end as i64,
                value: 0,
                flags: 0,
                child_count: a.elements.len() as i64,
                text: None,
            });
            for e in &a.elements {
                flatten_expr(e, out);
            }
        }
        Expr::Tuple(t) => {
            out.push(FlatNode {
                kind: K_TUPLE,
                start: t.span.start as i64,
                end: t.span.end as i64,
                value: 0,
                flags: 0,
                child_count: t.elements.len() as i64,
                text: None,
            });
            for e in &t.elements {
                flatten_expr(e, out);
            }
        }
        Expr::RecordConstruct(r) => {
            // text = `type;field1;field2;…` (idents are ASCII without `;`);
            // the children are the field values in source order.
            let mut name = r.type_name.clone();
            for (f, _) in &r.fields {
                name.push(';');
                name.push_str(f);
            }
            out.push(FlatNode {
                kind: K_RECORD_CONSTRUCT,
                start: r.span.start as i64,
                end: r.span.end as i64,
                value: name.len() as i64,
                flags: 0,
                child_count: r.fields.len() as i64,
                text: Some(name),
            });
            for (_, v) in &r.fields {
                flatten_expr(v, out);
            }
        }
        Expr::Path(p) => {
            // Turbofish type-args are a later slice (PR-4 types).
            if p.path.type_args.is_empty() {
                let name = p.path.segments.join("::");
                out.push(FlatNode {
                    kind: K_PATH,
                    start: p.span.start as i64,
                    end: p.span.end as i64,
                    value: name.len() as i64,
                    flags: 0,
                    child_count: 0,
                    text: Some(name),
                });
            } else {
                out.push(FlatNode {
                    kind: UNHANDLED,
                    start: p.span.start as i64,
                    end: p.span.end as i64,
                    value: 0,
                    flags: 0,
                    child_count: 0,
                    text: None,
                });
            }
        }
        // PR-E3: f-string. child_count = parts.len() (ET-E3 strict alternation:
        // every literal run — incl. empty — is a `Literal` part). A literal chunk
        // is a K_LIT_STR child carrying its own span + decoded text (mirrors a
        // string-literal node); a hole recurses as its underlying expression. The
        // self-hosted `parser.sigil` P_K_FSTRING node MUST emit this same shape.
        Expr::FString(fs) => {
            use sigil_compiler::ast::FStringPart;
            out.push(FlatNode {
                kind: K_FSTRING,
                start: fs.span.start as i64,
                end: fs.span.end as i64,
                value: fs.parts.len() as i64,
                flags: 0,
                child_count: fs.parts.len() as i64,
                text: None,
            });
            for part in &fs.parts {
                match part {
                    FStringPart::Literal(s, sp) => out.push(FlatNode {
                        kind: K_LIT_STR,
                        start: sp.start as i64,
                        end: sp.end as i64,
                        value: s.len() as i64,
                        flags: 0,
                        child_count: 0,
                        text: Some(s.clone()),
                    }),
                    FStringPart::Hole(e) => flatten_expr(e, out),
                }
            }
        }
        // Capabilities-as-values (R1): `mint <CapType> [(<deadline>,…)] for
        // <target>`. text = the cap-type name; value = its byte-length; flags =
        // the deadline-param COUNT (the literal values are a type-check concern,
        // not parse structure); one child = the target expression. The
        // self-hosted `parser.sigil` P_K_MINT node MUST emit this same shape.
        Expr::Mint(m) => {
            out.push(FlatNode {
                kind: K_MINT,
                start: m.span.start as i64,
                end: m.span.end as i64,
                value: m.cap_name.len() as i64,
                flags: m.params.len() as i64,
                child_count: 1,
                text: Some(m.cap_name.clone()),
            });
            flatten_expr(&m.target, out);
        }
        // Effect Handlers (EH0b): `perform <Effect>.<op>(args)`. A LEAF — text =
        // `effect;op`, value = its byte-length; args are consumed but not emitted
        // in this slice. `selfhost/parser.sigil`'s P_K_PERFORM emits this shape.
        Expr::Perform(p) => {
            let text = format!("{};{}", p.effect, p.op);
            out.push(FlatNode {
                kind: K_PERFORM,
                start: p.span.start as i64,
                end: p.span.end as i64,
                value: text.len() as i64,
                flags: 0,
                child_count: 0,
                text: Some(text),
            });
        }
        other => out.push(FlatNode {
            kind: expr_kind_of(other),
            start: other.span().start as i64,
            end: other.span().end as i64,
            value: 0,
            flags: 0,
            child_count: 0,
            text: None,
        }),
    }
}

// ── decoding the SIGIL side ──────────────────────────────────────────────────

/// Run the SIGIL lexer+parser on `source` and decode its pre-order node stream.
/// Decoded node streams, cached per source. Several tests walk the SAME
/// corpus (the differential, ET-P6 nesting, ET-P8 determinism); without the
/// cache each pass re-executes the big merged wasm tool per fixture, which
/// pushed CI past its job timeout. Correctness is unchanged: ET-P8 still
/// performs a genuinely FRESH second execution (`sigil_nodes_fresh`) and
/// compares it against the cached first run.
fn sigil_nodes(source: &str) -> Vec<FlatNode> {
    use std::collections::HashMap;
    use std::sync::Mutex;
    static CACHE: Mutex<Option<HashMap<String, Vec<FlatNode>>>> = Mutex::new(None);
    let mut guard = CACHE.lock().expect("cache lock");
    let map = guard.get_or_insert_with(HashMap::new);
    if let Some(hit) = map.get(source) {
        return hit.clone();
    }
    let nodes = sigil_nodes_fresh(source);
    map.insert(source.to_string(), nodes.clone());
    nodes
}

/// An UNCACHED execution — the determinism test's second run.
fn sigil_nodes_fresh(source: &str) -> Vec<FlatNode> {
    let out = execute_ephemeral(parser_wasm(), source.as_bytes(), FUEL, &IoGrants::none())
        .expect("parser tool should execute")
        .output;
    let enc = String::from_utf8(out).expect("encoding is utf8");
    let (records, pool) = enc
        .split_once('|')
        .expect("encoding carries a records|pool separator");
    let pool = pool.as_bytes();
    let mut cursor = 0usize;
    let mut nodes = Vec::new();
    for rec in records.split(';').filter(|s| !s.is_empty()) {
        let mut it = rec.split(',').map(|x| x.parse::<i64>().expect("int field"));
        let kind = it.next().expect("kind");
        let start = it.next().expect("start");
        let end = it.next().expect("end");
        let value = it.next().expect("value");
        let flags = it.next().expect("flags");
        let child_count = it.next().expect("child_count");
        let text = if kind_has_text(kind) {
            let len = usize::try_from(value).expect("non-negative text length");
            let bytes = &pool[cursor..cursor + len];
            cursor += len;
            Some(String::from_utf8(bytes.to_vec()).expect("name text is utf8"))
        } else {
            None
        };
        nodes.push(FlatNode {
            kind,
            start,
            end,
            value,
            flags,
            child_count,
            text,
        });
    }
    nodes
}

// ── the differential ─────────────────────────────────────────────────────────

/// ET-P2: compare the SIGIL pre-order node stream against the flattened
/// oracle, localizing the first divergence with the offending source lexeme.
fn assert_parses_like_oracle(source: &str) {
    check_parse(source, source);
}

/// The differential core. `label` (a filename for the stdlib corpus, the
/// source itself for the hand corpus) keeps failure messages readable;
/// mismatches print the oracle lexeme so a divergence is locatable.
fn check_parse(source: &str, label: &str) {
    let sigil = sigil_nodes(source);
    let sf = SourceFile::new("diff.sigil", source.to_string());
    let (program, diags) = parse_with_id(&sf, SourceId::SYNTHETIC);
    // ERRORS-ONLY: the parser now has warning-tier diagnostics (P031, the
    // fn-type-row declaration-binding advisory). A warning is not a parse
    // failure, and the decl-binding corpus row exists precisely to pin node
    // parity on that shape — so gating on `diags.is_empty()` would make the
    // fixture unaddable rather than checked.
    let errors: Vec<_> = diags
        .iter()
        .filter(|d| d.severity() == sigil_compiler::diagnostics::Severity::Error)
        .collect();
    assert!(
        errors.is_empty(),
        "oracle parse errored on {label}: {errors:?}"
    );
    // flatten_program handles both: single-module → bare K_MODULE root (byte-identical,
    // ET-PMM-1); multi-module → a K_PROGRAM wrapper. The single-module corpus is
    // unchanged because every fixture/stdlib file has exactly one `module` decl.
    let mut oracle = Vec::new();
    flatten_program(&program.modules, &mut oracle);
    let common = sigil.len().min(oracle.len());
    for idx in 0..common {
        let (s, r) = (&sigil[idx], &oracle[idx]);
        let lexeme = source
            .get(r.start as usize..r.end as usize)
            .unwrap_or("<span oob>");
        assert_eq!(
            s, r,
            "node {idx} differs on {label} (oracle lexeme {lexeme:?}):\n sigil={s:#?}\n oracle={r:#?}"
        );
    }
    assert_eq!(
        sigil.len(),
        oracle.len(),
        "node COUNT differs on {label}: sigil={} oracle={} (first {common} nodes agree)",
        sigil.len(),
        oracle.len()
    );
}

/// SH-PARSE-MM: a source with >=2 `module` decls parses to a P_K_PROGRAM wrapper root
/// (children = module nodes in source order) at node-for-node parity with the oracle
/// `Program{modules}`. The single-module corpus (every other test + the stdlib corpus)
/// stays byte-identical (a bare K_MODULE root) — that's the no-regression proof.
#[test]
fn differential_multi_module_program() {
    let fixtures: &[&str] = &[
        "module a;\nfn x() -> i64 { return 1; }\nmodule b;\nfn y() -> i64 { return 2; }\n",
        "module a;\nfn x() -> i64 { return 1; }\nmodule b;\nfn y() -> i64 { return 2; }\nmodule c;\nfn z() -> i64 { return 3; }\n",
        "module a;\nrecord P { x: i64 }\nmodule b;\nenum E { A, B }\n",
        // empty leading module: a's item loop stops immediately at `module b`.
        "module a;\nmodule b;\nfn y() -> i64 { return 0; }\n",
        // differing item counts per module.
        "module a;\nfn p() -> i64 { return 1; }\nfn q() -> i64 { return 2; }\nmodule b;\nfn r() -> i64 { return 3; }\n",
        // AG-R11 (SH-PARSE-MM gap): a NON-FIRST module carrying a module
        // attribute. Before the item-loop fix, `a`'s item loop stopped only on
        // `module`/EOF, so it fed the next module's leading `#`/`pub` run to
        // parser_item — which bailed token-by-token (spurious P_K_ERR children)
        // and parsed the 2nd module with flags=0, dropping its ring/trusted/pub
        // bits. The oracle's `at_module_start` (`module` | `pub`-then-`module` |
        // `#`) ends `a`'s items at the boundary, so the 2nd module keeps its
        // flags. The exact program from the bug report (cap type + cap param),
        // `#[ring(outer)]` → flags=1:
        "module util;\nfn z() -> i64 { return 0; }\n#[ring(outer)] module m;\ncap type Fuel { burn }\nfn f(c: Fuel) -> i64 { return 0; }\n",
        // bare `pub module` as the non-first module (flags=4) — the
        // `pub`-then-`module` arm of the boundary check.
        "module util;\nfn z() -> i64 { return 0; }\npub module m;\nfn f() -> i64 { return 1; }\n",
        // `#[trusted]` on the non-first module (flags=2). The oracle's
        // `parse_ring_annotation` greedily consumes `#[` before testing for the
        // `ring` keyword and never backtracks, so it accepts `#[trusted]` ONLY
        // when a `#[ring(...)]` attribute precedes it — spell `ring(inner)`
        // explicitly (inner is the default ring, so the only flag set is trusted).
        "module util;\nfn z() -> i64 { return 0; }\n#[ring(inner)] #[trusted] module m;\nfn f() -> i64 { return 1; }\n",
        // all three at once on the non-first module: `#[ring(outer)] #[trusted]
        // pub module` → flags = 1 + 2 + 4 = 7.
        "module util;\nfn z() -> i64 { return 0; }\n#[ring(outer)] #[trusted] pub module m;\nfn f() -> i64 { return 1; }\n",
        // attributed FIRST + attributed MIDDLE + plain LAST: the boundary fires
        // mid-stream, not only between the first two modules.
        "#[ring(outer)] module a;\nfn p() -> i64 { return 1; }\n#[ring(inner)] #[trusted] module b;\nfn q() -> i64 { return 2; }\nmodule c;\nfn r() -> i64 { return 3; }\n",
    ];
    for (i, src_ref) in fixtures.iter().enumerate() {
        let src = *src_ref;
        let sigil = sigil_nodes(src);
        let sf = SourceFile::new("diff.sigil", src.to_string());
        let (program, diags) = parse_with_id(&sf, SourceId::SYNTHETIC);
        assert!(
            diags.is_empty(),
            "multi-module #{i} oracle parse errored: {diags:?}"
        );
        assert!(
            program.modules.len() >= 2,
            "multi-module #{i} expected >=2 modules, got {}",
            program.modules.len()
        );
        let mut oracle = Vec::new();
        flatten_program(&program.modules, &mut oracle);
        let common = sigil.len().min(oracle.len());
        for idx in 0..common {
            assert_eq!(
                &sigil[idx], &oracle[idx],
                "multi-module #{i} node {idx} differs:\n sigil={:#?}\n oracle={:#?}",
                sigil[idx], oracle[idx]
            );
        }
        assert_eq!(
            sigil.len(),
            oracle.len(),
            "multi-module #{i} node COUNT differs: sigil={} oracle={}",
            sigil.len(),
            oracle.len()
        );
    }
    // NON-STUB (ET-PMM-7): distinct fixtures produce distinct streams.
    assert_ne!(
        sigil_nodes(fixtures[0]),
        sigil_nodes(fixtures[2]),
        "stub: distinct multi-module fixtures produced identical streams"
    );
}

/// The expression-slice corpus — header modules, fn items (pub-ness, optional
/// return type), return statements, and the FULL precedence climb: equality /
/// comparison / bitor / bitand / shift / additive / multiplicative, prefix
/// borrow + unary minus (fold AND desugar) + `!` (desugar), all four literal
/// forms, idents, and paren grouping (no node).
fn corpus() -> Vec<&'static str> {
    vec![
        "module t;\n",
        // PR-E1: optional `else` — a bare `if` (no else) must parse node-for-node
        // identically on both sides (Rust synthesizes an empty else Block; the
        // self-hosted parser synthesizes a matching zero-width empty else block).
        "module t;\nfn f() -> i64 { let mut x = 0; if x < 1 { x = 1; } return x; }\n",
        // and the else-bearing twin still parses identically.
        "module t;\nfn g() -> i64 { let mut x = 0; if x < 1 { x = 1; } else { x = 2; } return x; }\n",
        "module t;\nfn f() -> i64 { return 1; }\n",
        "module t;\npub fn g() -> i64 { return 42 + 7; }\n",
        "module t;\nfn h() -> i64 { return abc; }\n",
        "module t;\nfn k() -> i64 { return 1 + 2 - 3; }\n",
        "module t;\nfn p() -> i64 { return (1 + 2) - x; }\n",
        "module t;\nfn v() { return; }\n",
        "module t;\nfn a() -> i64 { return 1; }\npub fn b() -> i64 { return 2; }\n",
        "module t;\n// a comment\nfn c() -> i64 { return zz + 9; }\n",
        "module long_module_name;\nfn deep() -> i64 { return ((1)) + (2 - (3)); }\n",
        // the full precedence band: | over & over << over + over *
        "module t;\nfn band() -> i64 { return 1 | 2 & 3 << 4 + 5 * 6; }\n",
        "module t;\nfn mq() -> i64 { return 7 * 3 / 2 % 4; }\n",
        "module t;\nfn sh() -> i64 { return 1 << 3 >> 2; }\n",
        // equality over comparison; chained comparisons
        "module t;\nfn cmp() -> bool { return 1 + 2 * 3 == 7; }\n",
        "module t;\nfn ord() -> bool { return a < b == c > d; }\n",
        "module t;\nfn le() -> bool { return x <= y; }\n",
        "module t;\nfn ge() -> bool { return p >= q != r < s; }\n",
        // parens reshaping precedence (still no node)
        "module t;\nfn par() -> i64 { return (1 | 2) & (3 + 4) * 5; }\n",
        // prefix borrow vs infix bitand (positional disambiguation)
        "module t;\nfn bor() -> i64 { return &arr; }\n",
        "module t;\nfn borm() -> i64 { return &mut buf; }\n",
        "module t;\nfn mix() -> i64 { return a & &x; }\n",
        "module t;\nfn nest() -> i64 { return & &mut z; }\n",
        // unary minus: the literal FOLD (direct, through parens, doubled) and
        // the `0 - inner` DESUGAR (non-literal operand)
        "module t;\nfn m1() -> i64 { return -5; }\n",
        "module t;\nfn m2() -> i64 { return -(5); }\n",
        "module t;\nfn m3() -> i64 { return --7; }\n",
        "module t;\nfn m4() -> i64 { return -x; }\n",
        "module t;\nfn m5() -> i64 { return 1 - -2; }\n",
        "module t;\nfn m6() -> i64 { return -(a + 1); }\n",
        // unary `!`: the `inner == false` desugar (single and doubled)
        "module t;\nfn n1() -> bool { return !flag; }\n",
        "module t;\nfn n2() -> bool { return !!flag; }\n",
        "module t;\nfn n3() -> bool { return !(a == b); }\n",
        // bool / float / str literals (str DECODED value incl. escapes and
        // record-delimiter bytes — the pool is length-walked)
        "module t;\nfn t1() -> bool { return true; }\n",
        "module t;\nfn t2() -> bool { return false == true; }\n",
        "module t;\nfn fl() -> f64 { return 3.14; }\n",
        "module t;\nfn s1() -> str { return \"hello\"; }\n",
        "module t;\nfn s2() -> str { return \"a\\nb\\t\\\"q\\\"\"; }\n",
        "module t;\nfn s3() -> str { return \"a,b;c|d\"; }\n",
        "module t;\nfn s4() -> str { return \"héllo 日本\"; }\n",
        // calls: zero/one/many args, nested, trailing comma, in the ladder
        "module t;\nfn c1() -> i64 { return f(); }\n",
        "module t;\nfn c2() -> i64 { return f(1); }\n",
        "module t;\nfn c3() -> i64 { return g(1, x, 2 + 3); }\n",
        "module t;\nfn c4() -> i64 { return f(g(1), h(2, 3)); }\n",
        "module t;\nfn c5() -> i64 { return f(1, 2,); }\n",
        "module t;\nfn c6() -> i64 { return f(1) + g(2) * h(3); }\n",
        // multi-segment paths: bare (a 2/3-segment Path node) and as callees
        "module t;\nfn p1() -> i64 { return a.b; }\n",
        "module t;\nfn p2() -> i64 { return a.b.c; }\n",
        "module t;\nfn p3() -> i64 { return abi::pack; }\n",
        "module t;\nfn p4() -> i64 { return abi::pack(p, l); }\n",
        // method calls: the last segment splits off; the receiver Path keeps
        // the FULL path span (the oracle's quirk)
        "module t;\nfn m1() -> i64 { return v.len(); }\n",
        "module t;\nfn m2() -> i64 { return v.push(item); }\n",
        "module t;\nfn m3() -> i64 { return a.b.find(needle, 0); }\n",
        // result ctors: single-segment Ok/Err with exactly one argument
        "module t;\nfn r1() -> i64 { return Ok(5); }\n",
        "module t;\nfn r2() -> i64 { return Err(code + 1); }\n",
        // try `?`: postfix, chained, over calls and methods
        "module t;\nfn q1() -> i64 { return f()?; }\n",
        "module t;\nfn q2() -> i64 { return v.pop()? + 1; }\n",
        "module t;\nfn q3() -> i64 { return f()??; }\n",
        // index + slice: closed, open-start, open-end, full-open, expr bounds
        "module t;\nfn i1() -> i64 { return arr[0]; }\n",
        "module t;\nfn i2() -> i64 { return arr[i + 1]; }\n",
        "module t;\nfn i3() -> i64 { return arr[f(0)][1]; }\n",
        "module t;\nfn sl1() -> i64 { return &arr[1..3]; }\n",
        "module t;\nfn sl2() -> i64 { return &arr[..3]; }\n",
        "module t;\nfn sl3() -> i64 { return &arr[1..]; }\n",
        "module t;\nfn sl4() -> i64 { return &arr[..]; }\n",
        "module t;\nfn sl5() -> i64 { return &arr[lo..hi + 1]; }\n",
        // postfix mixing: index-then-try, try-into-binary, borrow over method
        "module t;\nfn x1() -> i64 { return arr[0]? + v.len(); }\n",
        "module t;\nfn x2() -> i64 { return &mut v.iter(); }\n",
        // array literals: empty, singleton, many, trailing comma, nested, exprs
        "module t;\nfn a1() -> i64 { return []; }\n",
        "module t;\nfn a2() -> i64 { return [1]; }\n",
        "module t;\nfn a3() -> i64 { return [1, 2, 3]; }\n",
        "module t;\nfn a4() -> i64 { return [1, x + 2, f(3),]; }\n",
        "module t;\nfn a5() -> i64 { return [[1, 2], [3, 4]]; }\n",
        // the repeat form: parse-time expansion to N clones; folded-negative
        // and string elements; indexable like any array
        "module t;\nfn rp1() -> i64 { return [0; 4]; }\n",
        "module t;\nfn rp2() -> i64 { return [-5; 3]; }\n",
        "module t;\nfn rp3() -> i64 { return [true; 2]; }\n",
        "module t;\nfn rp4() -> str { return [\"ab\"; 2]; }\n",
        "module t;\nfn rp5() -> i64 { return [0; 1]; }\n",
        "module t;\nfn rp6() -> i64 { return [7; 2][0]; }\n",
        // tuple literals: pairs, triples, nested, exprs, trailing comma —
        // and `(e)` stays grouping (no node)
        "module t;\nfn tu1() -> i64 { return (1, 2); }\n",
        "module t;\nfn tu2() -> i64 { return (a, b + 1, f(2)); }\n",
        "module t;\nfn tu3() -> i64 { return ((1, 2), (3, 4)); }\n",
        "module t;\nfn tu4() -> i64 { return (1, 2,); }\n",
        "module t;\nfn tu5() -> i64 { return ((((1)))); }\n",
        // record construction: single/many fields, trailing comma, nested,
        // multi-segment type paths, exprs as values
        "module t;\nfn rc1() -> i64 { return Point { x: 1 }; }\n",
        "module t;\nfn rc2() -> i64 { return Point { x: 1, y: 2 }; }\n",
        "module t;\nfn rc3() -> i64 { return Tok { kind: k + 1, start: f(0), end: 3, }; }\n",
        "module t;\nfn rc4() -> i64 { return Outer { inner: Inner { v: 1 }, n: 2 }; }\n",
        "module t;\nfn rc5() -> i64 { return geo::Point { x: 1, y: 2 }; }\n",
        "module t;\nfn rc6() -> i64 { return Wrap { items: [1, 2], pair: (3, 4) }; }\n",
        // let: plain, mut, annotated, annotated+mut, taint (with + without ty),
        // complex values, multi-statement blocks
        "module t;\nfn l1() -> i64 { let x = 1; return x; }\n",
        "module t;\nfn l2() -> i64 { let mut s = 0; return s; }\n",
        "module t;\nfn l3() -> i64 { let x: i64 = 5; return x; }\n",
        "module t;\nfn l4() -> bool { let mut y: bool = true; return y; }\n",
        "module t;\nfn l5() -> i64 { let s @Secret = f(); return s; }\n",
        "module t;\nfn l6() -> i64 { let k: i64 @Public = 1; return k; }\n",
        "module t;\nfn l7() -> i64 { let v = f(1) + arr[0]; let w = v * 2; return w; }\n",
        "module t;\nfn l8() -> str { let nm: str = \"x\"; return nm; }\n",
        // let-tuple: pairs, per-binding mut, from a call
        "module t;\nfn lt1() -> i64 { let (a, b) = (1, 2); return a + b; }\n",
        "module t;\nfn lt2() -> i64 { let (mut a, b, mut c) = t3(); return a; }\n",
        // assignment: locals, field places (2-segment paths), index places
        "module t;\nfn s1() -> i64 { let mut x = 0; x = 5; return x; }\n",
        "module t;\nfn s2() -> i64 { p.x = 3; return 0; }\n",
        "module t;\nfn s3() -> i64 { arr[0] = 9; m[k] = v; return 0; }\n",
        "module t;\nfn s4() -> i64 { v = f(x) + 1; return v; }\n",
        // compound assignment: LOCAL (the parse-time desugar — target cloned,
        // the Binary spans the whole statement) vs FIELD/INDEX (op kept)
        "module t;\nfn k1() -> i64 { let mut x = 0; x += 1; return x; }\n",
        "module t;\nfn k2() -> i64 { let mut n = 8; n *= 2; n -= 3; return n; }\n",
        "module t;\nfn k3() -> i64 { flags |= mask; bits &= m2; return flags; }\n",
        "module t;\nfn k4() -> i64 { n <<= 1; n >>= 2; q /= 3; r %= 4; return n; }\n",
        "module t;\nfn k5() -> i64 { arr[0] += 5; arr[i] <<= 1; return arr[0]; }\n",
        "module t;\nfn k6() -> i64 { p.x -= 2; return p.x; }\n",
        // expression statements: calls, method calls, a bare expr
        "module t;\nfn e1() -> i64 { f(1); v.push(3); 1 + 2; return 0; }\n",
        // if/else (else REQUIRED), nested, empty blocks, complex conditions
        "module t;\nfn if1() -> i64 { if x { return 1; } else { return 0; } }\n",
        "module t;\nfn if2() -> i64 { if a == b { } else { } return 0; }\n",
        "module t;\nfn if3() -> i64 { if a { if b { } else { } } else { c(); } return 0; }\n",
        // while + break/continue
        "module t;\nfn w1() -> i64 { let mut i = 0; while i < n { i += 1; } return i; }\n",
        "module t;\nfn w2() -> i64 { while true { if done { break; } else { continue; } } return 0; }\n",
        // for-in
        "module t;\nfn fo1() -> i64 { let mut s = 0; for x in v.iter() { s += x; } return s; }\n",
        "module t;\nfn fo2() -> i64 { for i in range(0, 9) { f(i); } return 0; }\n",
        // match: literal arms + wildcard, every separator style (comma, semi,
        // none, trailing), empty match
        "module t;\nfn m1() -> i64 { match v { 1 => { return 1; }, 2 => { return 2; }, _ => { return 0; } } }\n",
        "module t;\nfn m2() -> i64 { match v { 1 => { f(); }, 2 => { g(); }, _ => { h(); }, } return 0; }\n",
        "module t;\nfn m3() -> i64 { match v { 1 => { }; 2 => { }; _ => { } } return 0; }\n",
        "module t;\nfn m4() -> i64 { match x { } return 0; }\n",
        // enum patterns: bare variants (Some/None-as-binding!), `_` bindings,
        // qualified Type::Variant with and without payloads
        "module t;\nfn m5() -> i64 { match o { Some(v) => { return v; }, None => { return 0; } } }\n",
        "module t;\nfn m6() -> i64 { match p { Pair(a, b) => { return a + b; }, Some(_) => { return 1; }, _ => { return 0; } } }\n",
        "module t;\nfn m7() -> i64 { match r { Result::Ok(v) => { use_it(v); }, Result::Err(e) => { log(e); } } return 0; }\n",
        "module t;\nfn m8() -> i64 { match c { Color::Red => { return 1; }, Color::Blue => { return 2; }, _ => { return 0; } } }\n",
        // ranges (incl. negative bounds), bool + string literal patterns
        "module t;\nfn m9() -> i64 { match n { 0..=9 => { return 1; }, -5..=5 => { return 2; }, 10 => { return 3; }, _ => { return 0; } } }\n",
        "module t;\nfn m10() -> i64 { match n { -7 => { return 1; }, _ => { return 0; } } }\n",
        "module t;\nfn m11() -> bool { match b { true => { return false; }, false => { return true; } } }\n",
        "module t;\nfn m12() -> i64 { match s { \"add\" => { return 1; }, \"sub;x\" => { return 2; }, _ => { return 0; } } }\n",
        // PR P5: array/slice destructuring patterns — `[]`, fixed `[a, b]`, a
        // wildcard element `[a, _]`, named rest `[a, ..rest]`, anonymous rest
        // `[a, ..]`, rest-only `[..rest]` / `[..]`. Both parsers must emit the
        // byte-identical `P_K_PAT_ARRAY` encoding (value=elem count, flags=rest
        // kind, text=`;`-joined element words then the rest name iff named).
        "module t;\nfn ap1() -> i64 { match arr { [] => { return 0; }, [a] => { return a; }, [a, b] => { return a + b; }, [a, ..rest] => { return a; } } }\n",
        "module t;\nfn ap2() -> i64 { match s { [first, _, ..tail] => { return first; }, [..] => { return 0; } } }\n",
        "module t;\nfn ap3() -> i64 { match s { [..whole] => { return 0; } } }\n",
        // guards
        "module t;\nfn m13() -> i64 { match n { x if x > 0 => { return x; }, _ => { return 0; } } }\n",
        "module t;\nfn m14() -> i64 { match o { Some(v) if v != 0 => { return v; }, _ => { return 0; } } }\n",
        // PR-E2: `if let` / `while let` desugar to `match` (Stmt::Match) — both
        // parsers must produce the IDENTICAL node tree (synthetic wildcard /
        // `true` / `break` placed at matching offsets). if-let with else, no-else
        // (synth empty `_` arm), qualified + bare + binding + literal patterns,
        // nested, while-let (synth `true`/`break`), while-let with non-breaking arm.
        "module t;\nfn il1() -> i64 { if let Some(v) = o { return v; } else { return 0; } }\n",
        "module t;\nfn il2() -> i64 { let mut n = 0; if let Some(v) = o { n = v; } return n; }\n",
        "module t;\nfn il3() -> i64 { if let Opt::Some(v) = o { return v; } else { return 0; } }\n",
        "module t;\nfn il4() -> i64 { if let Pair(a, b) = p { return a + b; } return 0; }\n",
        "module t;\nfn il5() -> i64 { if let 1 = n { return 1; } else { return 0; } }\n",
        "module t;\nfn il6() -> i64 { if let Some(v) = o { if let Some(w) = q { return v + w; } } return 0; }\n",
        "module t;\nfn wl1() -> i64 { let mut s = 0; while let Some(v) = it.next() { s += v; } return s; }\n",
        "module t;\nfn wl2() -> i64 { while let Opt::Some(v) = it.next() { use_it(v); } return 0; }\n",
        // fn params: one/many, annotations (taint, @Mut/@ReadOnly, @in r),
        // generic + nested-generic types (note the `> >` nested close)
        "module t;\nfn p1(a: i64) -> i64 { return a; }\n",
        "module t;\nfn p2(a: i64, b: str, c: bool) -> i64 { return a; }\n",
        "module t;\nfn p3(v: Vec<i64>) -> i64 { return v.len(); }\n",
        "module t;\nfn p4(m: Map<str, Vec<i64> >) -> i64 { return m.len(); }\n",
        "module t;\nfn p5(s: str @Secret, n: i64 @Public) -> i64 { return n; }\n",
        "module t;\nfn p6(v: Vec<i64> @Mut, w: Vec<i64> @ReadOnly) -> i64 { return 0; }\n",
        "module t;\nfn p7(r: Region, v: Vec<i64> @in r) -> i64 { return 0; }\n",
        "module t;\nfn p8(s: str @Secret @Mut) -> i64 { return 0; }\n",
        // type shapes: refs (& / &mut / &[T]), arrays, tuples, fn types,
        // multi-segment paths, grouping `(T)` ≡ T
        "module t;\nfn t1(x: &i64) -> i64 { return 0; }\n",
        "module t;\nfn t2(x: &mut Vec<i64>) -> i64 { return 0; }\n",
        "module t;\nfn t3(x: &[i64]) -> i64 { return 0; }\n",
        "module t;\nfn t4(x: [i64; 8]) -> i64 { return 0; }\n",
        "module t;\nfn t5(x: (i64, str)) -> (i64, bool) { return (1, true); }\n",
        "module t;\nfn t6(f: Fn(i64) -> i64) -> i64 { return f(1); }\n",
        "module t;\nfn t7(f: Fn(i64, str) -> bool, g: Fn() -> i64) -> i64 { return 0; }\n",
        // fn-type latent effect rows (Phase 3b): param position, the
        // explicit-empty row (the None-vs-Some([]) ";!" marker), generic-arg
        // position, the paren'd return position (row binds to the TYPE), the
        // decl-binding shape (row binds to the DECLARATION; the oracle emits a
        // P031 WARNING, which the errors-only assert tolerates), and a
        // multi-name row.
        "module t;\nfn r1(f: Fn(i64) -> i64 ! { Alloc }) -> i64 { return f(1); }\n",
        "module t;\nfn r2(f: Fn() -> i64 ! { }) -> i64 { return 0; }\n",
        "module t;\nfn r3(v: Vec<Fn(i64) -> i64 ! { Alloc }>) -> i64 { return 0; }\n",
        "module t;\nfn r4() -> (Fn(i64) -> i64 ! { FsIO }) { return r4(); }\n",
        "module t;\nfn r5() -> Fn(i64) -> i64 ! { Alloc } { return r5(); }\n",
        "module t;\nfn r6(f: Fn(i64, str) -> bool ! { NetIO, Alloc }) -> i64 { return 0; }\n",
        "module t;\nfn t8(x: geo::Point) -> i64 { return 0; }\n",
        "module t;\nfn t9(x: (i64)) -> i64 { return 0; }\n",
        "module t;\nfn t10() -> [bool; 4] { return [true; 4]; }\n",
        "module t;\nfn t11() -> i64 { let g: Vec<(i64, str)> = Vec::new(); return g.len(); }\n",
        // closures: bare, with params, with return type, assigned + invoked
        "module t;\nfn c1() -> i64 { let f = fn() { return; }; return 0; }\n",
        "module t;\nfn c2() -> i64 { let f = fn(x: i64) -> i64 { return x + 1; }; return f(2); }\n",
        "module t;\nfn c3() -> i64 { let g = fn(a: i64, b: i64) -> i64 { return a * b; }; return 0; }\n",
        // use / const items
        "module t;\nuse sigil::vec;\nfn f() -> i64 { return 0; }\n",
        "module t;\npub use a::b::c;\n",
        "module t;\nconst T_EOF: i64 = 0;\nconst T_MAX: i64 = 900;\n",
        "module t;\npub const NAME: str = \"lex;er\";\nconst ON: bool = true;\n",
        // records: plain, pub, generic, multi-field with comma + semi seps
        "module t;\nrecord Point { x: i64, y: i64 }\n",
        "module t;\npub record Token { kind: i64, start: i64, end: i64, value: i64, text: str }\n",
        "module t;\nrecord Vec2<T> { buf: i64, count: i64 }\n",
        "module t;\nrecord Pair<A, B> { fst: A; snd: B }\n",
        // enums: unit variants, positional + named payloads, generic
        "module t;\npub enum Option2<T> { Some(T), None }\n",
        "module t;\nenum E { A, B(i64, str), C(x: i64, y: i64) }\n",
        "module t;\npub enum Result2<T, E> { Ok(T), Err(E) }\n",
        // impls: inherent, generic, trait-for; the method-visibility quirk
        // (a bare `fn` in an impl is STILL Public, span starting at `fn`)
        "module t;\nimpl Point { pub fn norm(self: Point) -> i64 { return self.x; } }\n",
        "module t;\nimpl Vec2<T> { pub fn len(self: Vec2<T> @ReadOnly) -> i64 { return self.count; } fn grow(self: Vec2<T> @Mut) -> i64 ! { Alloc } { return 0; } }\n",
        "module t;\nimpl Hash for i64 { fn hash(self: i64) -> i64 { return self; } }\n",
        // traits: signature-only methods, Self types, pub-in-body ignored
        "module t;\npub trait Hash { fn hash(self: Self) -> i64; }\n",
        "module t;\ntrait Eq2 { fn eq(self: Self, other: Self) -> bool; pub fn ne(self: Self, other: Self) -> bool; }\n",
        // extern fns: with and without effect rows
        "module t;\nextern \"C\" fn fs_read(ptr: i64, len: i64) -> i64 ! { FsIO, Alloc, FFI, Unsafe };\n",
        "module t;\nextern \"C\" fn noop();\n",
        // effect declarations: semi form and braced form (span ends at the NAME)
        "module t;\neffect FsIO;\neffect Z3Solve { }\n",
        // fn generics + bounds + effect rows (incl. the empty row `! { }`)
        "module t;\nfn keyed<K: Hash + Eq, V>(k: K) -> i64 { return 0; }\n",
        "module t;\npub fn mapv<U>(v: Vec<U>) -> Vec<U> ! { Alloc } { return v; }\n",
        "module t;\nfn pure2() -> i64 ! { } { return 1; }\n",
        // return-taint on fns and externs (flags bits): the FFI-module shape
        "module t;\npub fn sha(p: i32, l: i32) -> i64 @Internal ! { Alloc, FFI, Unsafe } { return ffi_call(p, l); }\n",
        "module t;\nfn leak() -> str @Secret { return s; }\n",
        "module t;\nextern \"C\" fn crypto_sha256(ptr: i32, len: i32) -> i64 @Internal ! { Alloc, FFI, Unsafe };\n",
        // module attributes + visibility (flags; attrs never extend the span)
        "#[ring(outer)] #[trusted]\nmodule tool;\nextern \"C\" fn f() -> i64 ! { FFI };\n",
        "#[ring(inner)]\nmodule quiet;\nfn g() -> i64 { return 0; }\n",
        "pub module exported;\nfn h() -> i64 { return 0; }\n",
        // actor-op call forms: send/ask (label + bare timeout), cap ops
        "module t;\nfn s1() -> i64 { counter.send(Inc(1)); return 0; }\n",
        "module t;\nfn s2() -> i64 { let r = svc.ask(Get(k), timeout: 100); return 0; }\n",
        "module t;\nfn s3() -> i64 { let r = svc.ask(Q(1), limit + 5); return 0; }\n",
        "module t;\nfn c1() -> i64 { let d = c.restrict(Read); return 0; }\n",
        "module t;\nfn c2() -> i64 { let d = io.caps.restrict_deadline(2030); return 0; }\n",
        "module t;\nfn c3() -> i64 { let (a, b) = budget.split(50); return 0; }\n",
        "module t;\nfn c4() -> i64 { let d = pool.draw(n + 1); return 0; }\n",
        // grant / handle / declassify / declassify_ct / region
        "module t;\nfn g1() -> i64 { return grant(fs_cap, read_all()); }\n",
        "module t;\nfn h1() -> i64 { handle FsIO, Alloc { do_io(); }; return 0; }\n",
        "module t;\nfn d1() -> i64 { let p = declassify(secret, dc_cap); return p; }\n",
        "module t;\nfn d2() -> i64 { let p = declassify(s, c) @Public; return p; }\n",
        "module t;\nfn d3() -> i64 { let p = declassify_ct(ct_val, ct_cap); return p; }\n",
        "module t;\nfn r1() -> i64 { region scratch(4096) { let v = build(); }; return 0; }\n",
        // capabilities-as-values: `mint <Cap> [(<deadline>…)] for <target>` (R1).
        // non-parametric, single + multi deadline param (the `flags` count), and
        // `mint` as an ORDINARY identifier (fn name / call / let binding / bare
        // value) — the CONTEXTUAL keyword must fire ONLY on the two-ident
        // `mint <Cap>` shape, never on `mint(…)`/a bare `mint` (the ERC20 golden).
        "module t;\nfn m1(r: i64) -> i64 { let c = mint FileAccess for r; return 0; }\n",
        "module t;\nfn m2(r: i64) -> i64 { let c = mint Approval(2030) for r; return 0; }\n",
        "module t;\nfn m3(r: i64) -> i64 { let c = mint Quota(10, 60) for r; return 0; }\n",
        "module t;\nfn mint(x: i64) -> i64 { return x; }\nfn mu() -> i64 { let a = mint(7); let mint = 5; return a + mint; }\n",
        // typestate (Epic 1, R3): a `state Name { … }` protocol decl (pub +
        // empty-marker-set variants), and the state-kinded binder `<@S>`
        // (flags=1) — distinct in the flattened stream from an ordinary `<T>`
        // generic (flags=0, the R2 kind encoding); a mixed `<T, @S>` list pins it.
        "module t;\nstate File { Open, Closed }\n",
        "module t;\npub state Conn { Idle, Active, Closed }\n",
        "module t;\nstate Unit { }\n",
        "module t;\nfn fd<@S>(f: File<S>) -> i64 { return 0; }\n",
        "module t;\nfn dup<T, @S>(x: T) -> i64 { return 0; }\n",
        // HKT (R4): higher-kinded kind annotations `<F: * -> *>` (arity 1 →
        // flags 2), `<M: * -> * -> *>` (arity 2 → flags 3), and the kind-then-
        // bound form `<F: * -> * + Functor>` (text gains `;Functor`); plus a
        // real use site `count<F: * -> *, A>(xs: F<A>)`. `*`/`->` already
        // tokenize, so NO lexer change.
        "module t;\nfn k1<F: * -> *>() -> i64 { return 0; }\n",
        "module t;\nfn k2<M: * -> * -> *>() -> i64 { return 0; }\n",
        "module t;\nfn k3<F: * -> * + Functor>() -> i64 { return 0; }\n",
        "module t;\nfn count<F: * -> *, A>(xs: F<A>) -> i64 { return 0; }\n",
        // spawn: bare, args, supervision Stop / Restart
        "module t;\nfn sp1() -> i64 { let a = spawn<Worker>(); return 0; }\n",
        "module t;\nfn sp2() -> i64 { let a = spawn::<Worker>(1, cfg); return 0; }\n",
        "module t;\nfn sp3() -> i64 { let a = spawn<W>(x, supervision: Stop); return 0; }\n",
        "module t;\nfn sp4() -> i64 { let a = spawn<W>(supervision: Restart(3)); return 0; }\n",
        // actors: state/init/handlers (incl. semi-bodied handler), entry form
        "module t;\nactor Counter {\n    state { count: i64 }\n    init(start: i64) { count = start; }\n    on Inc(by: i64) { count += by; }\n    on Get() -> i64 { return count; }\n}\n",
        "module t;\npub entry actor Main {\n    init() ;\n    on Tick() ;\n}\n",
        // cap types: bare, authorities, parametric, semi form
        "module t;\ncap type FsRead { read, stat }\n",
        "module t;\npub cap type Approval(deadline_ms: i64) { consume }\n",
        "module t;\ncap type Marker;\n",
        // parametric-cap usage in type position
        "module t;\nfn a1(c: Approval(2030)) -> i64 { return 0; }\n",
        "module t;\nfn a2(c: Quota(10, 60)) -> i64 { return 0; }\n",
        // refinement where-clauses: record (OUTSIDE the span), variant,
        // fn param-where + return-where
        "module t;\nrecord Pos { x: i64, y: i64 } where x >= 0\n",
        "module t;\nenum Cmd { Move(dx: i64) where dx != 0, Stop2() }\n",
        "module t;\nfn pw(n: i64) where n > 0 -> i64 { return n; }\n",
        "module t;\nfn rw() -> i64 where @ >= -5 { return 0; }\n",
        // a stdlib-shaped composite: const + record + impl + generic methods
        "module mini;\n\nconst CAP: i64 = 8;\n\nrecord Slot<T> { item: T, used: bool }\n\nimpl Slot<T> {\n    pub fn take(self: Slot<T> @Mut) -> T {\n        self.used = false;\n        return self.item;\n    }\n}\n\npub fn fresh<T>(item: T) -> Slot<T> ! { Alloc } {\n    return Slot { item: item, used: true };\n}\n",
        // a realistic composite: the shapes hand-written SIGIL actually uses
        "module t;\nfn real() -> i64 {\n    let mut acc = 0;\n    let mut i = 0;\n    while i < src.len() {\n        let b = src.byte_at(i);\n        if b == 47 {\n            acc += 1;\n        } else {\n            match b {\n                10 => { lines += 1; },\n                _ => { }\n            }\n        }\n        i = i + 1;\n    }\n    return acc;\n}\n",
        // PR-E3: f-strings parse to a P_K_FSTRING node — value + child_count = the
        // part count; children are a P_K_LIT_STR per chunk (ET-E3 strict alternation:
        // every literal run, incl. empty, is a chunk) and the parsed expression per
        // hole. Node-for-node parity with the Rust Expr::FString flatten.
        "module t;\nfn f() -> str { return f\"hello\"; }\n", // no holes (1 chunk)
        "module t;\nfn f() -> str { return f\"\"; }\n",      // empty (1 empty chunk)
        "module t;\nfn f() -> str { let s = \"x\"; return f\"a{s}b\"; }\n", // chunks + ident hole
        "module t;\nfn f() -> str { let s = \"x\"; return f\"{s}\"; }\n", // hole only
        "module t;\nfn f() -> str { let a = \"x\"; let b = \"y\"; return f\"{a}{b}\"; }\n", // adjacent
        "module t;\nfn f() -> str { let n = 1; return f\"sum={n + 2}\"; }\n", // arith hole
        "module t;\nfn f() -> str { return f\"{g(1)}\"; }\n",                 // call hole
        "module t;\nfn f() -> str { return f\"p={Foo::bar}\"; }\n",           // path hole
        "module t;\nfn f() -> str { return f\"{{lit}}\"; }\n", // escaped braces (1 chunk)
        // PR-E4: type aliases parse to a P_K_TYPE_ALIAS node — name on `text`, pub bit
        // on `flags`, the body type as the single child (shared type grammar). Node-for-
        // node parity with the Rust Item::TypeAlias flatten.
        "module t;\ntype NodeId = i64;\n",         // scalar alias
        "module t;\npub type Id = u64;\n",         // pub bit
        "module t;\ntype A = B;\ntype B = i64;\n", // alias-to-alias chain (parse)
        "module t;\ntype Pair = (i64, str);\n",    // tuple body
        "module t;\ntype Buf = [i64; 8];\n",       // array body
        "module t;\nrecord R { x: i64 }\ntype RR = &R;\n", // ref body
        "module t;\ntype Ints = Vec<i64>;\n",      // generic-Named body
        // an alias used in a fn signature (param + return type position)
        "module t;\ntype NodeId = i64;\nfn f(n: NodeId) -> NodeId { return n; }\n",
    ]
}

#[test]
fn differential_minimal_corpus() {
    for src in corpus() {
        assert_parses_like_oracle(src);
    }
}

/// Adversarial parse-parity sweep for the R1–R4 mirror (capabilities-as-values
/// `mint`, typestate `state`/`<@S>`, HKT `<F: * -> *>`): the edge combinations
/// the flat corpus does not hit. Each must parse node-for-node identically to
/// the oracle. Angles: the kind annotations on RECORDS/ENUMS/IMPLS (not just
/// fns — all four route through the one `parser_type_params`), mixed kind lists
/// (Constructor + State + bounded Star), kind-then-multi-bound, nested/rich
/// `mint` targets and `mint` as an ordinary value, and — the key regression —
/// the actor `state { … }` block coexisting with a top-level `state` decl.
#[test]
fn differential_caps_typestate_hkt_adversarial() {
    let cases: &[&str] = &[
        // mint: a nested `mint` target, a method-call target, three deadline
        // params (flags=3), and a bare `mint` value (NOT a mint expr — the
        // peek after `mint` is `;`/`=`, never an ident).
        "module t;\nfn mn(r: i64) -> i64 { let c = mint Outer for mint Inner for r; return 0; }\n",
        "module t;\nfn mt(r: i64) -> i64 { let c = mint Cap for compute(r); return 0; }\n",
        "module t;\nfn mp(r: i64) -> i64 { let c = mint Q(1, 2, 3) for r; return 0; }\n",
        "module t;\nfn mb2(r: i64) -> i64 { let mint = r; return mint; }\n",
        // typestate: a single-marker decl; a state binder `<@S>` on a RECORD and
        // an ENUM (flags=1, the carrier-type pattern).
        "module t;\nstate S { A }\n",
        "module t;\nrecord File<@S> { fd: i64 }\n",
        "module t;\nenum Conn2<@S> { Open2, Closed2 }\n",
        // REGRESSION: a top-level `state P { … }` decl MUST NOT hijack the
        // named-less actor `state { … }` block (parsed inside the actor) — both
        // present in one module.
        "module t;\nstate P { Idle }\nactor C {\n    state { count: i64 }\n    init() { count = 0; }\n    on Inc() { count += 1; }\n}\n",
        // MUTABLE-STATE S1: an actor `state {}` block with a `mut` field + a plain
        // field. The oracle captures `mut` in `Field.mutability`; the selfhost
        // parser consumes it to the SAME P_K_FIELD shape (inert marker). Parses to
        // an identical tree both sides — pins that the state-only `mut` keyword
        // does not perturb the shadow.
        "module t;\nactor Cnt {\n    state { mut count: i64, tag: i64 }\n    init() { count = 0; tag = 1; }\n    on Get() -> i64 { return count + tag; }\n}\n",
        // HKT kinds on a RECORD and an ENUM; a mixed list (Constructor + State +
        // bounded Star → flags 2/1/0); a kind followed by multiple bounds.
        "module t;\nrecord Wrap<F: * -> *> { n: i64 }\n",
        "module t;\nenum Choice<F: * -> *> { L, R }\n",
        "module t;\nfn mix<F: * -> *, @S, T: Hash>() -> i64 { return 0; }\n",
        "module t;\nfn mbnd<F: * -> * + A + B>() -> i64 { return 0; }\n",
        // an impl whose type-params (after the type name) carry a state binder.
        "module t;\nrecord D<@S> { v: i64 }\nimpl D<@S> { fn z() -> i64 { return 0; } }\n",
    ];
    for src in cases {
        assert_parses_like_oracle(src);
    }
}

/// Effect Handlers (EH0b, constraint C-NOVAC): the new `perform` / clause-form
/// `handle` / operation-bearing `effect` surface MUST parse node-for-node
/// identically on both sides — a non-vacuous parity check that the self-hosted
/// `parser.sigil` mirror actually recognizes the grammar. Also pins C-PATHSEP:
/// the legacy bare `handle E { stmts }` is NOT mis-routed to the clause path.
#[test]
fn differential_effect_handlers() {
    let cases: &[&str] = &[
        // operation-bearing effect (op NAMES ride the decl text); + a perform.
        "module t;\neffect Reader { fn get() -> i64; }\nfn g() -> i64 { let x = perform Reader.get(); return x; }\n",
        // an op with a param and a `-> never` (abortive) return; an abortive perform.
        "module t;\neffect Fail { fn raise(msg: str) -> never; }\nfn h(n: i64) -> i64 { perform Fail.raise(n); return n; }\n",
        // bare marker effect is unchanged (no op suffix in the text).
        "module t;\neffect Audit;\n",
        // clause-form handle: a call scrutinee, an abortive clause body.
        "module t;\neffect Reader { fn get() -> i64; }\nfn provider() -> i64 { return 1; }\nfn f() -> i64 { return handle provider() { Reader.get() => 7 }; }\n",
        // clause-form handle with `resume` in the clause body (the leaf consumes
        // it without emitting — so `resume` need not be mirrored in this slice).
        "module t;\neffect Reader { fn get() -> i64; }\nfn provider() -> i64 { return 1; }\nfn f2() -> i64 { return handle provider() { Reader.get() => resume 42 }; }\n",
        // C-PATHSEP REGRESSION: a bare `handle E { stmts }` (no `=>`) must route
        // to the legacy bare form (K_HANDLE), NOT the clause path.
        "module t;\neffect Audit;\nfn b() -> i64 { handle Audit { let z = 1; }; return 2; }\n",
    ];
    for src in cases {
        assert_parses_like_oracle(src);
    }
}

/// The stdlib differential corpus — the parser epic's "done" line. Every real
/// `stdlib/sigil/*.sigil` file MUST parse node-for-node identically to the
/// oracle — kinds, spans, values, flags, child counts, and every name/effect/
/// taint encoding. Real files exercise the whole grammar at production scale.
#[test]
fn differential_stdlib_corpus() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/sigil");
    let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read stdlib dir {}: {e}", dir.display()))
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "sigil"))
        .collect();
    files.sort();
    assert!(
        files.len() >= 10,
        "expected the full stdlib (>=10 files), found {} under {}",
        files.len(),
        dir.display()
    );
    for path in &files {
        let src = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let name = path.file_name().expect("file name").to_string_lossy();
        check_parse(&src, &name);
    }
}

#[test]
fn et_p6_spans_nest_within_parents() {
    // ET-P6 (oracle-INDEPENDENT): walk the pre-order stream with an explicit
    // stack of (remaining_children, span); every node's span must sit inside
    // its parent's.
    for src in corpus() {
        let nodes = sigil_nodes(src);
        assert!(!nodes.is_empty(), "at least the root on {src:?}");
        let mut stack: Vec<(i64, i64, i64)> = Vec::new(); // (remaining, start, end)
        for (idx, n) in nodes.iter().enumerate() {
            if let Some((_, ps, pe)) = stack.last() {
                // K_REFINEMENT is the one documented containment exemption:
                // a record-level `where` clause sits OUTSIDE the record's
                // span (the oracle closes the span at `}` before the clause
                // parses).
                if n.kind != K_REFINEMENT {
                    assert!(
                        *ps <= n.start && n.end <= *pe,
                        "node {idx} span [{},{}) escapes parent [{ps},{pe}) on {src:?}",
                        n.start,
                        n.end
                    );
                }
            }
            if let Some(top) = stack.last_mut() {
                top.0 -= 1;
            }
            if n.child_count > 0 {
                stack.push((n.child_count, n.start, n.end));
            }
            while matches!(stack.last(), Some((0, _, _))) {
                stack.pop();
            }
        }
        assert!(
            stack.is_empty(),
            "pre-order child counts must consume exactly on {src:?}"
        );
    }
}

#[test]
fn et_p8_parse_is_deterministic() {
    // The cached first run vs a genuinely FRESH second execution. SAMPLED
    // (every 3rd hand fixture) for CI budget — each fresh run re-executes the
    // big merged wasm tool, and full-corpus determinism ran unsampled for the
    // epic's whole development arc. The stdlib corpus test covers the real
    // files; the sample keeps a live cross-section of every grammar area.
    for (i, src) in corpus().into_iter().enumerate() {
        if i % 3 != 0 {
            continue;
        }
        assert_eq!(
            sigil_nodes(src),
            sigil_nodes_fresh(src),
            "non-deterministic on {src:?}"
        );
    }
}

/// ET-P1 — the coverage manifest: every parser-PRODUCIBLE node kind must
/// appear ≥1× across the corpus (hand fixtures + the whole stdlib), otherwise
/// "passes the corpus" is hollow for the missing kind. The non-producible
/// kinds are documented exclusions: the oracle parser never constructs
/// EnumConstruct/FieldAccess (type-check builds them — they have no tags),
/// and K_ERR appears only on malformed input (the error corpus covers it).
#[test]
fn et_p1_corpus_covers_every_kind() {
    let mut seen = std::collections::HashSet::new();
    for src in corpus() {
        for n in sigil_nodes(src) {
            seen.insert(n.kind);
        }
    }
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/sigil");
    for entry in std::fs::read_dir(&dir).expect("stdlib dir") {
        let path = entry.expect("entry").path();
        if path.extension().is_some_and(|x| x == "sigil") {
            let src = std::fs::read_to_string(&path).expect("read");
            for n in sigil_nodes(&src) {
                seen.insert(n.kind);
            }
        }
    }
    let mut expected: Vec<i64> = vec![K_MODULE, K_FN, K_TYPE, K_BLOCK];
    expected.extend(10..=27); // statements + patterns
    expected.extend(30..=50); // expressions + type overlays + params/closures
    expected.extend(51..=63); // items
    expected.extend(64..=80); // the exotica
    let missing: Vec<i64> = expected
        .iter()
        .copied()
        .filter(|k| !seen.contains(k))
        .collect();
    assert!(
        missing.is_empty(),
        "corpus does not cover node kinds: {missing:?}"
    );
}

/// The parser-error corpus — error PRESENCE + FIRST-POSITION parity on
/// malformed input: the oracle reports diagnostics ⟺ the SIGIL stream
/// contains K_ERR nodes, and the FIRST error's span matches the FIRST
/// diagnostic's span (both point at the offending token). Coarse P-CODE
/// parity is deferred — the SIGIL parser's uniform `parser_bail` carries no
/// per-site code today (the oracle has ~24 codes across ~100 sites); see the
/// spec's AG-P3 amendment.
#[test]
fn differential_parser_errors() {
    // POSITION-parity fixtures: the error fires at a dispatch-level expect,
    // so the SIGIL bail node SURVIVES as the production's result and its span
    // is the offending token — matching the oracle's first diagnostic.
    let position_cases: Vec<&str> = vec![
        "module t; fn f( -> i64 { return 0; }",
        "module t; fn f() -> i64 { let = 5; return 0; }",
        "module t; record R { x i64 }",
        "module t; enum E { 5 }",
        "module t; wat",
        "module t; fn f() -> i64 { match v { 1 => { } 2 => { } } return 0; }",
    ];
    // PRESENCE-only fixtures: the error fires deep inside an expression whose
    // partial subtree the bailing production DISCARDS (an orphan, absent from
    // the pre-order stream) — only a later cascade bail survives, so the
    // positions legitimately differ (AG-P3's recovery-internals exemption).
    let presence_cases: Vec<&str> = vec![
        "module t; fn f() -> i64 { return 1 + ; }",
        "module t; fn f() -> i64 { x = ( ; return 0; }",
    ];
    for src in position_cases {
        let sigil = sigil_nodes(src);
        // The EARLIEST surviving error by POSITION (cascade bails come later).
        let first_err = sigil
            .iter()
            .filter(|n| n.kind == K_ERR)
            .min_by_key(|n| n.start);
        let sf = SourceFile::new("err.sigil", src.to_string());
        let (_program, diags) = parse_with_id(&sf, SourceId::SYNTHETIC);
        assert!(
            !diags.is_empty(),
            "expected the oracle to report parser diagnostics on {src:?}"
        );
        let err = first_err.unwrap_or_else(|| {
            panic!("oracle errored but the SIGIL stream has no K_ERR on {src:?}")
        });
        let dspan = diags[0].span().expect("a parser diagnostic carries a span");
        assert_eq!(
            (err.start as usize, err.end as usize),
            (dspan.start, dspan.end),
            "FIRST error position differs on {src:?}: sigil=[{},{}) oracle={:?} ({})",
            err.start,
            err.end,
            dspan,
            diags[0].message()
        );
    }
    for src in presence_cases {
        let sigil = sigil_nodes(src);
        let has_err = sigil.iter().any(|n| n.kind == K_ERR);
        let sf = SourceFile::new("err.sigil", src.to_string());
        let (_program, diags) = parse_with_id(&sf, SourceId::SYNTHETIC);
        assert!(
            !diags.is_empty() && has_err,
            "error PRESENCE must agree on {src:?}: oracle={} sigil={}",
            !diags.is_empty(),
            has_err
        );
    }
}

#[test]
fn et_p8_never_traps_on_adversarial_input() {
    // ET-P8: malformed input yields a stream (with K_ERR nodes), never a trap,
    // and the parse always terminates (ET-P5's Eof discipline).
    let inputs: Vec<&str> = vec![
        "",
        "module",
        "module t",
        "module t;",
        "module t; fn",
        "module t; fn f(",
        "module t; fn f() {",
        "module t; fn f() -> { return 1; }",
        "module t; fn f() -> i64 { return 1 + ; }",
        "module t; fn f() -> i64 { return (1; }",
        "module t; @ $ ~ fn",
        "fn orphan() { return; }",
        "module t; fn f() -> i64 { return 1 }",
        "module t; pub pub fn f() {}",
        // structured-primary malformed shapes (PR-2c paths)
        "module t; fn f() -> i64 { return [1, ; }",
        "module t; fn f() -> i64 { return (1,); }",
        "module t; fn f() -> i64 { return (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13); }",
        "module t; fn f() -> i64 { return [0; x]; }",
        "module t; fn f() -> i64 { return [f(); 2]; }",
        "module t; fn f() -> i64 { return [0; 99999]; }",
        "module t; fn f() -> i64 { return Name {; }",
        "module t; fn f() -> i64 { return Name { x 1 }; }",
        "module t; fn f() -> i64 { return Name { x: }; }",
        // data-statement malformed shapes (PR-3a paths)
        "module t; fn f() -> i64 { let; }",
        "module t; fn f() -> i64 { let x 5; }",
        "module t; fn f() -> i64 { let x = ; }",
        "module t; fn f() -> i64 { let x: = 1; }",
        "module t; fn f() -> i64 { let s @Wrong = 1; }",
        "module t; fn f() -> i64 { let (a) = t; }",
        "module t; fn f() -> i64 { let (a, = t; }",
        "module t; fn f() -> i64 { x = ; }",
        "module t; fn f() -> i64 { x += ; }",
        "module t; fn f() -> i64 { 1 + 2 }",
        // control-flow malformed shapes (PR-3b paths)
        "module t; fn f() -> i64 { if x { } }",
        "module t; fn f() -> i64 { if x { } else }",
        "module t; fn f() -> i64 { while { } }",
        "module t; fn f() -> i64 { for x v { } }",
        "module t; fn f() -> i64 { for in v { } }",
        "module t; fn f() -> i64 { break }",
        "module t; fn f() -> i64 { match x { 1 => } }",
        "module t; fn f() -> i64 { match x { => { } } }",
        "module t; fn f() -> i64 { match x { 1..= => { } } }",
        "module t; fn f() -> i64 { match x { Foo:: => { } } }",
        "module t; fn f() -> i64 { match x { Some( => { } } }",
        "module t; fn f() -> i64 { match x",
        // type/param/closure malformed shapes (PR-4a paths)
        "module t; fn f(x) -> i64 { return 0; }",
        "module t; fn f(x:) -> i64 { return 0; }",
        "module t; fn f(x: Vec<) -> i64 { return 0; }",
        "module t; fn f(x: Vec<i64) -> i64 { return 0; }",
        "module t; fn f(x: Vec<Vec<i64>>) -> i64 { return 0; }",
        "module t; fn f(x: [i64; ]) -> i64 { return 0; }",
        "module t; fn f(x: [i64; n]) -> i64 { return 0; }",
        "module t; fn f(x: [i64; 99999]) -> i64 { return 0; }",
        "module t; fn f(x: &) -> i64 { return 0; }",
        "module t; fn f(x: (i64,)) -> i64 { return 0; }",
        "module t; fn f(x: Fn(i64) i64) -> i64 { return 0; }",
        // fn-type row: `!` not followed by `{` (malformed row in a bounded
        // position) — both sides must report an error, not silently accept.
        "module t; fn f(g: Fn(i64) -> i64 ! Alloc) -> i64 { return 0; }",
        "module t; fn f(s: str @Wrong) -> i64 { return 0; }",
        "module t; fn f() -> i64 { let g = fn(x { return; }; return 0; }",
        // item malformed shapes (PR-4b paths)
        "module t; record R {",
        "module t; record R { x }",
        "module t; record R { x: }",
        "module t; enum E { A(",
        "module t; enum E { A(x:) }",
        "module t; impl X",
        "module t; impl X for { }",
        "module t; trait T { fn f() }",
        "module t; extern fn f();",
        "module t; extern \"C\" f();",
        "module t; const C = 1;",
        "module t; const C: i64 = -1;",
        "module t; use ;",
        "module t; fn f<T(x: i64) -> i64 { return 0; }",
        "module t; fn f() -> i64 ! Alloc { return 0; }",
        "#[ring(weird)] module t;",
        "#[wat] module t;",
        "# module t;",
        // exotica malformed shapes (PR-5b paths)
        "module t; fn f() -> i64 { a.send(; }",
        "module t; fn f() -> i64 { a.ask(m); }",
        "module t; fn f() -> i64 { c.restrict(5); }",
        "module t; fn f() -> i64 { c.restrict_deadline(x); }",
        "module t; fn f() -> i64 { let a = spawn<W>(supervision: Wat); }",
        "module t; fn f() -> i64 { grant(c); }",
        "module t; fn f() -> i64 { handle 5 { }; }",
        "module t; fn f() -> i64 { region (4096) { }; }",
        "module t; actor A { wat }",
        "module t; actor A { state { x } }",
        "module t; cap type;",
        "module t; cap type Q(d: str);",
        "module t; record R { x: i64 } where",
        "module t; record R { x: i64 } where y > 0",
        "module t; fn f(n: i64) where n ?? 0 -> i64 { return n; }",
    ];
    for src in inputs {
        let nodes = sigil_nodes(src); // panics if the tool traps / mis-returns
        assert!(!nodes.is_empty(), "must emit at least one node on {src:?}");
    }
}

#[test]
fn et_p4_no_orphan_nodes_on_clean_corpus() {
    // ET-P4 reachability: on the clean corpus, every allocated node is
    // reachable from the root — arena len == pre-order emit count. The tool
    // returns the gap (+1000) as a negative sentinel.
    let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
        \x20   let src: str = opt.unwrap_or(\"\");\n\
        \x20   let toks: Vec<Token> = lex(src);\n\
        \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
        \x20   let mut kids: Vec<i64> = Vec::new();\n\
        \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
        \x20   let mut recs: Vec<str> = Vec::new();\n\
        \x20   let mut pool: Vec<str> = Vec::new();\n\
        \x20   let emitted: i64 = parser_emit(nodes, kids, root, recs, pool);\n\
        \x20   return 0 - (nodes.len() - emitted + 1000);";
    let compiled = compile_tool(&parser_tool(body)).expect("reachability tool should compile");
    for src in corpus() {
        match execute_ephemeral(&compiled.wasm, src.as_bytes(), FUEL, &IoGrants::none()) {
            Err(ToolError::Trapped { message }) => {
                let p = "tool returned error (";
                let s = message
                    .find(p)
                    .unwrap_or_else(|| panic!("unexpected trap on {src:?}: {message}"))
                    + p.len();
                let e = message[s..].find(')').expect("malformed trap");
                let gap: i64 = message[s..s + e].parse().expect("parse sentinel");
                assert_eq!(
                    gap,
                    1000,
                    "orphan nodes on {src:?}: allocated-reachable gap = {}",
                    gap - 1000
                );
            }
            other => panic!("expected the sentinel return on {src:?}, got {other:?}"),
        }
    }
}

#[test]
fn et_p9_kind_tags_are_unique() {
    // The compile-time lock is the no-`_` matches above; this pins the tag
    // VALUES against accidental duplication.
    let tags = [
        K_MODULE, K_FN, K_TYPE, K_BLOCK, K_RETURN, K_BINARY, K_LIT_INT, K_PATH, K_ERR, UNHANDLED,
    ];
    let unique: std::collections::HashSet<i64> = tags.iter().copied().collect();
    assert_eq!(unique.len(), tags.len(), "node-kind tags must be unique");
}
