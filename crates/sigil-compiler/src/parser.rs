//! The SIGIL parser -- hand-written recursive descent from the lexer's token
//! stream to the surface `Program` AST. `parse_with_id` is the production
//! entry point (it lexes internally, so every span carries real `SourceId`
//! attribution); `parse` is the legacy single-file path with synthetic spans.
//!
//! This file is the differential ORACLE for the self-hosted parser:
//! `selfhost/parser.sigil` must match it node-for-node -- kinds, spans,
//! values, flags, child counts -- per `docs/specs/parser-in-sigil.md`, proven
//! by `crates/sigil-runtime/tests/parser_differential.rs`. A grammar or
//! recovery change here redefines "correct" for that stage and breaks the
//! differential until the selfhost side moves in lock-step.
//!
//! Failure discipline: the parser recovers instead of aborting -- every
//! fault lands as a typed diagnostic beside a best-effort `Program`. Grammar
//! faults are P-codes (from P001 expected-token to the P031 effect-row
//! binding warning); form checks fire parse-time T-codes, among them T198
//! (parametric-cap form), T223 (mixed variant payloads), and T228/T229/T230
//! (impl-block type-param checks); nesting past `MAX_EXPR_DEPTH` (128) --
//! expression, block, or type -- raises a single S007 and fast-forwards to
//! EOF rather than overflowing the stack (pinned by
//! `tests/parser_depth_cap.rs` and `parser_depth_properties.rs`). Recovery
//! stays FAITHFUL, never degenerate: a reserved keyword in a name position
//! gets a precise P026 plus a poison name the lexer can never produce, so a
//! recovered parse cannot silently type-check clean
//! (`tests/reserved_keyword_ident.rs`).

use crate::{
    ast::{
        ActorDef, ArrayElem, ArrayLitExpr, ArrayPattern, ArrayTypeExpr, AskExpr, AssignStmt,
        BinaryExpr, BinaryOp, BindingPattern, Block, BorrowExpr, CallExpr, CapDrawExpr,
        CapRestrictDeadlineExpr, CapRestrictExpr, CapSplitExpr, CapTypeDef, CapTypeParam,
        ClauseHandleExpr, ClosureExpr, ConstDef, DeclassifyCtExpr, DeclassifyExpr, EffectDecl,
        EffectOp, EnumDef, EnumVariant, EnumVariantField, EnumVariantPattern, Expr, ExprStmt,
        ExternFnDecl, Field, FieldAccessExpr, FnDef, FnTypeExpr, ForInStmt, ForRangeStmt,
        GrantExpr, HandleClause, HandleExpr, Handler, IfStmt, ImplDef, IndexExpr, InitBlock, Item,
        LetStmt, LetTupleStmt, Literal, LiteralExpr, LiteralPattern, MAX_KIND_ARITY,
        MAX_TUPLE_ARITY, MatchArm, MatchStmt, MethodCallExpr, MintExpr, MintPolicy, Module,
        Mutability, Param, ParamKind, Path, PathExpr, Pattern, PerformExpr, Program, RangePattern,
        RecordConstructExpr, RecordDef, RefKind, RefinementClause, RefinementOp, RegionExpr,
        RestBind, ResultCtorExpr, ResumeExpr, ReturnStmt, Ring, SendExpr, SliceExpr, SpawnExpr,
        StateDef, Stmt, SupervisionExpr, TaintLabel, TraitDef, TraitMethodSig, TryExpr, TupleExpr,
        TypeAliasDef, TypeExpr, TypeParam, UseDecl, Visibility, WhileStmt,
    },
    diagnostics::{Diagnostic, SuggestedEdit, codes},
    lexer::{Token, TokenKind, lex_with_id},
    source::SourceFile,
    span::{SourceId, Span},
};

/// Poison-name prefix used when [`Parser::expect_ident`] recovers from a
/// reserved keyword sitting in an identifier position. It contains characters
/// (`<`, space) that the lexer can never produce inside a real identifier, so
/// the recovered name can never collide with a source identifier — references
/// to it fail name resolution, keeping the overall outcome a clean rejection
/// rather than a degenerate parse that silently type-checks.
const RESERVED_KEYWORD_POISON_PREFIX: &str = "<reserved keyword> ";

/// Legacy single-file entry point. Spans produced via this path
/// attribute to [`SourceId::SYNTHETIC`]. Used by tests that don't
/// have a SourceMap yet. Production callers should use
/// [`parse_with_id`].
pub fn parse(source: &SourceFile) -> (Program, Vec<Diagnostic>) {
    parse_with_id(source, SourceId::SYNTHETIC)
}

/// Wall 5 Step 1 follow-up: parse with an explicit [`SourceId`]. Every
/// span produced by the lexer and parser will carry this id so
/// multi-file diagnostics resolve to the right file via
/// [`crate::source::SourceMap`].
pub fn parse_with_id(source: &SourceFile, source_id: SourceId) -> (Program, Vec<Diagnostic>) {
    let (tokens, diagnostics) = lex_with_id(source, source_id);
    Parser::new(tokens, diagnostics, source_id).parse_program()
}

/// Wall 4 Step 6 commit #2: enum-variant payload form tracker.
/// Per N4-S6 / N12-S6, a variant's payload list is either ALL-named
/// (`V(x: i64, y: i64)`) or ALL-positional (`V(i64, i64)`); mixed is
/// rejected at parse time with T223. The parser commits to a form at
/// the first field and re-validates each subsequent field against the
/// locked form.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PayloadForm {
    /// All payload fields carry `name: Some(_)`. Required for
    /// variant `where` clauses (per N4-S6 / T223 sub-case 1).
    Named,
    /// All payload fields carry `name: None`. Refinements on
    /// positional variants are rejected (per N4-S6 / T223).
    Positional,
}

/// Map a compound-assignment token (`+=`, `-=`, `<<=`, etc.) to the
/// underlying `BinaryOp`. Returns `None` for any non-compound token —
/// including plain `Eq`, which the caller handles separately.
/// SIGIL Complete v0 / Phase 6 (N5-V0): T228 shadow check shared
/// between `parse_impl_block` (parse time) and the type-checker's
/// `collect_function_sigs` (defensive). Returns the list of method
/// type_params that shadow an impl-block-level type_param, paired
/// with the method's span (used as the diagnostic site since FnDef
/// doesn't carry per-type_param spans).
///
/// Empty Vec is the happy path (no shadow). Non-empty list → emit one
/// T228 per shadowed name; routing exclusivity from T229 is preserved
/// because T229 fires on the impl-block's type_params before this
/// helper is called.
pub(crate) fn enforce_no_method_impl_shadow(
    impl_type_params: &[String],
    method: &FnDef,
) -> Vec<(String, Span)> {
    if impl_type_params.is_empty() || method.type_params.is_empty() {
        return Vec::new();
    }
    let impl_set: std::collections::BTreeSet<&str> =
        impl_type_params.iter().map(|s| s.as_str()).collect();
    method
        .type_params
        .iter()
        .filter(|p| impl_set.contains(p.name.as_str()))
        .map(|p| (p.name.clone(), method.span))
        .collect()
}

/// SIGIL Complete v0 / Phase 6 (N6-V0): T230 receiver-mirror check.
/// A method declared inside `impl TypeName<T, E> { ... }` MUST have
/// its `self` parameter typed as exactly `TypeName<T, E>` in the
/// same declaration order. Args swapped (`self: Result<E, T>`) or
/// substituted (`self: Result<i64, E>`) silently mis-bind
/// substitutions at dispatch time.
///
/// Returns `Some(Diagnostic)` if the mirror check fails for this
/// method's first parameter; `None` if the structure matches OR if
/// the method has no `self` parameter (free-function-style methods
/// inside impl blocks — uncommon today but grammatically allowed).
pub(crate) fn check_self_param_mirrors_impl_type_params(
    impl_type_name: &str,
    impl_type_params: &[String],
    method: &FnDef,
) -> Option<Diagnostic> {
    // Locate the `self` parameter (first param named "self"). If the
    // method has no `self` param, T230 doesn't apply.
    let self_param = method.params.iter().find(|p| p.name == "self")?;

    // Self-param's named-type segments and type_args.
    let path = &self_param.ty.path;
    let last_segment = path.segments.last()?;

    // Type name must match the impl block's type name.
    if last_segment != impl_type_name {
        return Some(Diagnostic::error(
            codes::T230,
            format!(
                "method `{}`'s `self` parameter is typed as `{}` but the enclosing `impl {}<...>` block declares the type name as `{}` — every method's `self`-type must match its impl block's type name",
                method.name, last_segment, impl_type_name, impl_type_name,
            ),
            Some(self_param.ty.span),
        ));
    }

    // Arity of the self-param's type-args must match impl's
    // type_params count.
    if path.type_args.len() != impl_type_params.len() {
        let expected_list = impl_type_params
            .iter()
            .map(|n| n.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        return Some(Diagnostic::error(
            codes::T230,
            format!(
                "method `{}`'s `self` parameter is typed as `{}<...>` with {} type argument(s), but the enclosing `impl {}<{}>` block declares {} type parameter(s) — the `self`-type must mirror the impl block exactly",
                method.name,
                last_segment,
                path.type_args.len(),
                impl_type_name,
                expected_list,
                impl_type_params.len(),
            ),
            Some(self_param.ty.span),
        ));
    }

    // Structural mirror: each type-arg's path segment must be a bare
    // single-segment ident equal to the corresponding impl type_param.
    for (i, expected_name) in impl_type_params.iter().enumerate() {
        let arg = &path.type_args[i];
        let mirrored = arg.path.segments.len() == 1
            && arg.path.segments[0] == *expected_name
            && arg.path.type_args.is_empty()
            && arg.ref_kind.is_none();
        if !mirrored {
            let actual = arg.path.display_name();
            return Some(Diagnostic::error(
                codes::T230,
                format!(
                    "method `{}`'s `self` parameter has type argument #{} as `{}` but the enclosing `impl {}<{}>` block declares position #{} as `{}` — `self`-type-args must mirror the impl block's type parameters in declaration order (per N6-V0)",
                    method.name,
                    i + 1,
                    actual,
                    impl_type_name,
                    impl_type_params.join(", "),
                    i + 1,
                    expected_name,
                ),
                Some(arg.span),
            ));
        }
    }

    None
}

fn compound_assign_op(kind: &TokenKind) -> Option<BinaryOp> {
    match kind {
        TokenKind::PlusEq => Some(BinaryOp::Add),
        TokenKind::MinusEq => Some(BinaryOp::Sub),
        TokenKind::StarEq => Some(BinaryOp::Mul),
        TokenKind::SlashEq => Some(BinaryOp::Div),
        TokenKind::PercentEq => Some(BinaryOp::Mod),
        TokenKind::LtLtEq => Some(BinaryOp::Shl),
        TokenKind::GtGtEq => Some(BinaryOp::Shr),
        TokenKind::AmpersandEq => Some(BinaryOp::BitAnd),
        TokenKind::PipeEq => Some(BinaryOp::BitOr),
        _ => None,
    }
}

/// Regions (DEF-2b): true iff this `TypeExpr` is the bare built-in `Region` type — the
/// only valid `@in r` target (a `Region` value, not `&Region` / `[Region]` / `Region<T>`).
fn type_expr_is_region(ty: &TypeExpr) -> bool {
    ty.ref_kind.is_none()
        && ty.fn_type.is_none()
        && ty.array_type.is_none()
        && ty.path.type_args.is_empty()
        && ty.path.segments.len() == 1
        && ty.path.segments[0] == "Region"
}

/// Which `where`-clause position a refinement combinator turned up in.
/// Selects the T214 fix template: the "collapse to the strongest single
/// bound" route is shared, but the "carry the second clause somewhere
/// else" route differs by site — a record can be split into records, a
/// parameter has to be wrapped in one, and so on.
#[derive(Clone, Copy)]
enum RefinementSite {
    Record,
    Variant,
    Param,
    Return,
}

impl RefinementSite {
    /// The T214 message for this position. Every arm must name the
    /// deferred combinator feature AND offer a copyable fix, per the
    /// axis-4 message bar pinned in `tests/diagnostic_messages.rs`.
    fn compound_predicate_message(self) -> &'static str {
        match self {
            Self::Record => {
                "compound refinement predicate rejected: SIGIL admits a single `where <field> <op> <literal>` clause per record (Wall 4 Step 1 grammar). The combinator operators `&&` / `||` are deferred to a future step (combinator support). To fix: (a) collapse the constraint into the strongest single bound — e.g., `where x > 0 && x < 10` → `where x > 0` if upper bound is enforced elsewhere; OR (b) split into two separate records each with one clause and join via a wrapping struct; OR (c) move secondary constraints into runtime asserts."
            }
            Self::Variant => {
                "compound refinement predicate rejected: SIGIL admits a single `where <field> <op> <rhs>` clause per enum variant (N19-S6 grammar). The combinator operators `&&` / `||` are deferred to a future step (combinator support). To fix: (a) collapse the constraint into the strongest single bound — e.g., `where n > 0 && n < 10` → `where n > 0` if the upper bound is enforced elsewhere; OR (b) give the payload its own `record` type and carry the second clause as that record's refinement; OR (c) move secondary constraints into runtime asserts at construction."
            }
            Self::Param => {
                "compound refinement predicate rejected: SIGIL admits a single `where <param> <op> <literal>` clause per parameter position (Wall 4 Step 7 grammar, N7-S7). The combinator operators `&&` / `||` are deferred to a future step (combinator support). To fix: (a) collapse the constraint into the strongest single bound — e.g., `where x > 0 && x < 10` → `where x > 0` if the upper bound is enforced elsewhere; OR (b) wrap the parameter in a `record` whose own refinement carries the second clause; OR (c) check secondary constraints with a runtime assert in the function body."
            }
            Self::Return => {
                "compound refinement predicate rejected: SIGIL admits a single `where @ <op> <literal>` clause per return position (Wall 4 Step 7 grammar, N4-S7). The combinator operators `&&` / `||` are deferred to a future step (combinator support). To fix: (a) collapse the constraint into the strongest single bound — e.g., `where @ > 0 && @ < 10` → `where @ > 0` if the upper bound is enforced elsewhere; OR (b) return a `record` whose own refinement carries the second clause; OR (c) check secondary constraints with a runtime assert before returning."
            }
        }
    }
}

struct Parser {
    tokens: Vec<Token>,
    cursor: usize,
    diagnostics: Vec<Diagnostic>,
    /// Wall 5 Step 1 follow-up: source-file identifier for spans the
    /// parser synthesizes itself (e.g., the "expected `module`"
    /// pseudo-span pointing at offset 0 of an empty file). Token spans
    /// already carry the right id from the lexer; this field covers
    /// the parser's own synthesized cases.
    source_id: SourceId,
    /// Effect Handlers (EH0): nesting depth of handler-clause bodies currently
    /// being parsed. `resume <expr>` is recognized contextually ONLY when this
    /// is > 0, so `resume` stays a plain identifier everywhere outside a clause.
    clause_depth: usize,
    /// Fn-type effect rows (roadmap Phase 3): when set, a `Fn(..) -> U` TYPE
    /// expression does NOT consume a trailing `! { … }` row. Set for the span of
    /// a function DECLARATION's return-type parse, where the trailing row is the
    /// DECLARATION's (status quo preserved — `fn f() -> Fn(i64) -> i64 ! { A }`
    /// keeps meaning "f's row is {A}"); cleared inside any grouping that makes
    /// the row unambiguous again (parens/tuples, Fn parameter lists, generic
    /// args, array element types), so `-> (Fn(i64) -> i64 ! { A })` opts the row
    /// into the TYPE. P031 (warning) fires at the suppressed site so the binding
    /// choice is never silent. The parser differential cannot adjudicate this
    /// binding (both sides would change meaning together) — the semantic pin is
    /// `fn_type_effect_rows.rs`' binding tests, not the differential.
    suppress_fn_type_row: bool,
    /// Expression recursion depth, incremented on every `parse_prefix_expr`
    /// entry (the choke point every expression parse flows through). Bounds
    /// the recursive descent so pathologically nested input — deep
    /// `((((…))))` grouping or `----…` unary chains, both far under the 5 MB
    /// source cap — raises S007 instead of overflowing the stack and aborting
    /// the process (finding P1).
    expr_depth: usize,
    /// Latched once S007 has fired, so the single diagnostic is emitted exactly
    /// once and the over-deep subtree unwinds without re-descending or spamming
    /// the diagnostic list.
    depth_exceeded: bool,
    /// Whether the most recent `parse_path_from_first` consumed any `::`
    /// separator (segment join or turbofish). Read IMMEDIATELY after that
    /// call by `parse_ident_led_expr` to stamp `MethodCallExpr::colon_spelled`;
    /// reset at the start of every path parse.
    last_path_colon_spelled: bool,
}

/// Maximum expression nesting depth before the parser bails with S007.
/// Set to Rust's own default `recursion_limit` (128): comfortably above any
/// hand-written or generated expression, and safely below the stack-overflow
/// threshold on the smallest (debug) build's main-thread stack.
const MAX_EXPR_DEPTH: usize = 128;

impl Parser {
    fn new(tokens: Vec<Token>, diagnostics: Vec<Diagnostic>, source_id: SourceId) -> Self {
        Self {
            tokens,
            cursor: 0,
            diagnostics,
            source_id,
            clause_depth: 0,
            suppress_fn_type_row: false,
            expr_depth: 0,
            depth_exceeded: false,
            last_path_colon_spelled: false,
        }
    }

    fn parse_program(mut self) -> (Program, Vec<Diagnostic>) {
        let mut modules = Vec::new();

        while !self.is_eof() {
            if self.at_module_start() {
                if let Some(module) = self.parse_module() {
                    modules.push(module);
                }
            } else {
                self.diagnostics.push(Diagnostic::error(
                    codes::P002,
                    "expected `module` declaration",
                    Some(self.current().span),
                ));
                self.synchronize_program();
            }
        }

        if modules.is_empty() && self.diagnostics.is_empty() {
            self.diagnostics.push(Diagnostic::error(
                codes::P002,
                "expected `module` declaration",
                Some(Span::with_source(0, 0, self.source_id)),
            ));
        }

        (Program { modules }, self.diagnostics)
    }

    fn parse_ring_annotation(&mut self) -> Ring {
        // Check for #[ring(inner)] or #[ring(outer)]
        if !self.at_hash() {
            return Ring::Inner; // default: secure by construction
        }
        self.advance(); // consume #
        if !self.at_lbracket() {
            return Ring::Inner;
        }
        self.advance(); // consume [
        if !matches!(self.current().kind, TokenKind::Ring) {
            return Ring::Inner;
        }
        self.advance(); // consume 'ring'
        if !self.at_lparen() {
            return Ring::Inner;
        }
        self.advance(); // consume (
        let ring = if let Some((name, _)) = self.expect_ident("expected 'inner' or 'outer'") {
            match name.as_str() {
                "inner" => Ring::Inner,
                "outer" => Ring::Outer,
                other => {
                    self.diagnostics.push(Diagnostic::error(
                        codes::P003,
                        format!("unknown ring `{other}`, expected `inner` or `outer`"),
                        Some(self.previous_span()),
                    ));
                    Ring::Inner
                }
            }
        } else {
            Ring::Inner
        };
        if self.at_rparen() {
            self.advance();
        }
        if self.at_rbracket() {
            self.advance();
        }
        ring
    }

    fn parse_module(&mut self) -> Option<Module> {
        let mut ring = Ring::Inner;
        let mut trusted = false;

        // Parse attributes: #[ring(inner/outer)] and #[trusted]
        while self.at_hash() {
            let parsed_ring = self.parse_ring_annotation();
            if parsed_ring != Ring::Inner {
                ring = parsed_ring;
            }
            // Check for #[trusted]
            if self.at_hash() {
                let saved = self.cursor;
                self.advance(); // #
                if self.at_lbracket() {
                    self.advance(); // [
                    if let TokenKind::Ident(ref name) = self.current().kind.clone()
                        && name == "trusted"
                    {
                        self.advance();
                        if self.at_rbracket() {
                            self.advance();
                        }
                        trusted = true;
                        continue;
                    }
                }
                self.cursor = saved; // backtrack if not #[trusted]
                break;
            } else {
                break;
            }
        }
        let (visibility, start) = self.parse_visibility();
        let module_start = self.expect_module()?;
        let start = start.unwrap_or(module_start);
        let (name, name_span) = self.expect_ident("expected module name after `module`")?;

        let (items, end) = if self.at_semicolon() {
            let header_end = self.advance().span;
            let (items, last_item_span) = self.parse_items_until_module_or_eof();
            (items, last_item_span.unwrap_or(header_end))
        } else if self.at_lbrace() {
            let open = self.advance().span;
            let (items, last_item_span) = self.parse_items_until_rbrace();
            let close = if self.at_rbrace() {
                self.advance().span
            } else {
                self.diagnostics.push(Diagnostic::error(
                    codes::P004,
                    "expected `}` to close module body",
                    Some(self.current().span),
                ));
                last_item_span.unwrap_or(open)
            };
            (items, close)
        } else {
            self.diagnostics.push(Diagnostic::error(
                codes::P005,
                "expected `;` or `{` after module name",
                Some(self.current().span),
            ));
            return Some(Module {
                name,
                ring,
                trusted,
                visibility,
                items: Vec::new(),
                span: start.join(name_span),
            });
        };

        Some(Module {
            name,
            ring,
            trusted,
            visibility,
            items,
            span: start.join(end),
        })
    }

    fn parse_items_until_module_or_eof(&mut self) -> (Vec<Item>, Option<Span>) {
        let mut items = Vec::new();
        let mut last_span = None;

        while !self.is_eof() && !self.at_module_start() {
            if self.at_rbrace() {
                break;
            }

            let before = self.cursor;
            match self.parse_item() {
                Some(item) => {
                    last_span = Some(item.span());
                    items.push(item);
                }
                None => {
                    if !self.synchronize_item_made_progress() && self.cursor == before {
                        // Top level: there is no enclosing parser to hand this
                        // token to, and stopping would silently truncate the
                        // file. Step over it and keep reporting — but only when
                        // the whole iteration consumed nothing. If `parse_item`
                        // consumed tokens before failing and recovery parked on
                        // the next item start, the next iteration parses that
                        // item; advancing here instead would discard a valid
                        // item start and cascade (`P002`/`P006` after a `T223`
                        // enum rejection — the diagnostic_precision solver lane).
                        self.advance();
                    }
                }
            }
        }

        (items, last_span)
    }

    fn parse_items_until_rbrace(&mut self) -> (Vec<Item>, Option<Span>) {
        let mut items = Vec::new();
        let mut last_span = None;

        while !self.is_eof() && !self.at_rbrace() {
            let before = self.cursor;
            match self.parse_item() {
                Some(item) => {
                    last_span = Some(item.span());
                    items.push(item);
                }
                None => {
                    if !self.synchronize_item_made_progress() && self.cursor == before {
                        // Top level: there is no enclosing parser to hand this
                        // token to, and stopping would silently truncate the
                        // file. Step over it and keep reporting — but only when
                        // the whole iteration consumed nothing. If `parse_item`
                        // consumed tokens before failing and recovery parked on
                        // the next item start, the next iteration parses that
                        // item; advancing here instead would discard a valid
                        // item start and cascade (`P002`/`P006` after a `T223`
                        // enum rejection — the diagnostic_precision solver lane).
                        self.advance();
                    }
                }
            }
        }

        (items, last_span)
    }

    fn parse_item(&mut self) -> Option<Item> {
        let (visibility, vis_span) = self.parse_visibility();

        if self.at_use() {
            return self.parse_use(visibility, vis_span).map(Item::UseDecl);
        }

        if self.at_const() {
            return self.parse_const(visibility, vis_span).map(Item::ConstDef);
        }

        if self.at_fn() {
            return self.parse_fn(visibility, vis_span).map(Item::FnDef);
        }

        if self.at_actor_start() {
            return self.parse_actor(visibility, vis_span).map(Item::ActorDef);
        }

        if self.at_cap() {
            return self
                .parse_cap_type(visibility, vis_span)
                .map(Item::CapTypeDef);
        }

        if self.at_record() {
            return self.parse_record(visibility, vis_span).map(Item::RecordDef);
        }

        if self.at_enum() {
            return self.parse_enum(visibility, vis_span).map(Item::EnumDef);
        }

        // Typestate (Epic 1): a TOP-LEVEL `state Name { … }` is a protocol decl.
        // (The actor `state { fields }` block is named-less and parsed inside
        // `parse_actor`, so there is no ambiguity at the item level.)
        if self.at_state() {
            return self
                .parse_state_def(visibility, vis_span)
                .map(Item::StateDef);
        }

        if self.at_extern() {
            return self.parse_extern_fn_decl().map(Item::ExternFnDecl);
        }

        if self.at_effect() {
            return self.parse_effect_decl().map(Item::EffectDecl);
        }

        if self.at_impl() {
            return self
                .parse_impl_block(visibility, vis_span)
                .map(Item::ImplDef);
        }

        if self.at_trait() {
            return self.parse_trait(visibility, vis_span).map(Item::TraitDef);
        }

        // PR-E4: a bare `type` (not `cap type`, which `at_cap` claimed above) opens a
        // type alias `type Name = TypeExpr;`.
        if self.at_type() {
            return self
                .parse_type_alias(visibility, vis_span)
                .map(Item::TypeAlias);
        }

        self.diagnostics.push(Diagnostic::error(
            codes::P006,
            "expected item declaration",
            Some(self.current().span),
        ));
        None
    }

    /// PR-E4: `type Name = TypeExpr;`. The `=` and `;` are required; the body is any
    /// type expression (resolved — incl. transitively through other aliases — at
    /// type-resolution). `cap type …` is handled earlier via `at_cap`.
    fn parse_type_alias(
        &mut self,
        visibility: Visibility,
        vis_span: Option<Span>,
    ) -> Option<TypeAliasDef> {
        let start = vis_span.unwrap_or(self.current().span);
        self.advance(); // consume `type`
        let (name, _name_span) = self.expect_ident("expected type alias name")?;
        self.expect_eq("expected `=` in type alias")?;
        let body = self.parse_type_expr("expected a type after `=` in a type alias")?;
        let end = self.expect_semicolon("expected `;` after type alias")?;
        Some(TypeAliasDef {
            visibility,
            name,
            body,
            span: start.join(end),
        })
    }

    fn parse_use(&mut self, visibility: Visibility, vis_span: Option<Span>) -> Option<UseDecl> {
        let start = vis_span.unwrap_or(self.current().span);
        self.advance();
        let path = self.parse_path("expected path after `use`")?;
        let end = self.expect_semicolon("expected `;` after use declaration")?;

        Some(UseDecl {
            visibility,
            path,
            span: start.join(end),
        })
    }

    fn parse_const(&mut self, visibility: Visibility, vis_span: Option<Span>) -> Option<ConstDef> {
        let start = vis_span.unwrap_or(self.current().span);
        self.advance();
        let (name, name_span) = self.expect_ident("expected constant name after `const`")?;
        self.expect_colon("expected `:` after constant name")?;
        let ty = self.parse_type_expr("expected type after `:`")?;
        self.expect_eq("expected `=` in constant declaration")?;
        let value = self.parse_literal()?;
        let end = self.expect_semicolon("expected `;` after constant declaration")?;

        Some(ConstDef {
            visibility,
            name,
            ty,
            value,
            span: start.join(name_span).join(end),
        })
    }

    fn parse_fn(&mut self, visibility: Visibility, vis_span: Option<Span>) -> Option<FnDef> {
        let start = vis_span.unwrap_or(self.current().span);
        self.advance();
        let (name, _) = self.expect_ident("expected function name after `fn`")?;
        let type_params = self.parse_type_params();
        let params = self.parse_params_allowing_flow()?;

        // Regions (DEF-2b, PR-5): a `where region(a): region(b)` outlives clause shares the
        // param-where position. Parse it first — it consumes only a `where region …`, so a
        // refinement-where (`where x > 0`) still falls through to the refinement parser.
        let region_outlives = self.parse_optional_region_outlives_where(&params);

        // Wall 4 Step 7: param-where clause between `)` and `->`. Per
        // N5-S7 literal-RHS only; per N7-S7 single clause; per N3-S7
        // LHS must reference a declared param name.
        let mut param_refinements = if region_outlives.is_empty() {
            self.parse_optional_param_refinement_where(&params)
        } else {
            Vec::new()
        };

        let return_type = if self.at_arrow() {
            self.advance();
            // Declaration-return position: a trailing `! { … }` after a
            // Fn-shaped return type is the DECLARATION's row (status quo), not
            // the type's — suppress type-row parsing for exactly this parse.
            // Restore BEFORE the `?` so an error path cannot leak the flag.
            self.suppress_fn_type_row = true;
            let parsed = self.parse_type_expr("expected return type after `->`");
            self.suppress_fn_type_row = false;
            Some(parsed?)
        } else {
            None
        };
        let (ret_taint, mut ret_flow) = self.parse_taint_annotation_allowing_flow();
        // `-> T @Flow` means "the result's label is whatever flowed in". With no
        // `@Flow` parameter nothing flows in, so the annotation names no label
        // at all — reject rather than silently resolving it to @Public.
        if ret_flow && !params.iter().any(|p| p.flow) {
            self.diagnostics.push(Diagnostic::error(
                codes::P021,
                format!(
                    "`fn {name}` returns `@Flow` but has no `@Flow` parameter; the return label \
                     has nothing to follow"
                ),
                Some(self.current().span),
            ));
            ret_flow = false;
        }

        // Wall 4 Step 7: return-where clause after the return type. Per
        // N4-S7 LHS is the magic `@` token; per N5-S7 literal-RHS only.
        // Per N34-S7 / MI-S7-15: `where @ ...` with no return type fires
        // T226 from inside the helper.
        let mut return_refinement =
            self.parse_optional_return_refinement_where(return_type.is_some());

        let effects = self.parse_effect_row();

        // Wall 4 Step 7 / N23-S7: T226 emit-and-clear coupled. If the
        // function is generic AND has any refinement, fire T226 and
        // clear BOTH slots in the same code path. Per MC-S7-L (A1-S6
        // inheritance), the registry hint covers generic + closure +
        // no-return sub-cases at a generic level.
        if !type_params.is_empty() && (!param_refinements.is_empty() || return_refinement.is_some())
        {
            self.diagnostics.push(Diagnostic::error(
                codes::T226,
                format!(
                    "function `{name}` is generic (declares type parameters) and carries refinement clauses; Wall 4 Step 7 explicitly defers refinement on generic functions (Option B sidecar does not propagate through monomorphization, anti-goal MC-S7-C). Either drop the type parameters or move the refined logic to a non-generic function."
                ),
                Some(start),
            ));
            param_refinements.clear();
            return_refinement = None;
        }

        let body = self.parse_body("expected function body")?;

        Some(FnDef {
            visibility,
            name,
            type_params,
            params,
            return_type,
            ret_taint,
            ret_flow,
            effects,
            span: start.join(body.span),
            body,
            param_refinements,
            return_refinement,
            // Regions (DEF-2b, PR-5): the `where region(a): region(b)` outlives pairs.
            region_outlives,
        })
    }

    fn parse_extern_fn_decl(&mut self) -> Option<ExternFnDecl> {
        let start = self.advance().span; // consume 'extern'

        // Expect ABI string literal, e.g. "C"
        let abi = match &self.current().kind {
            TokenKind::StrLit(s) => {
                let s = s.clone();
                self.advance();
                s
            }
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::P007,
                    "expected ABI string (e.g. \"C\") after `extern`",
                    Some(self.current().span),
                ));
                return None;
            }
        };

        // Expect `fn`
        if !self.at_fn() {
            self.diagnostics.push(Diagnostic::error(
                codes::P008,
                "expected `fn` after extern ABI",
                Some(self.current().span),
            ));
            return None;
        }
        self.advance();

        let (name, _) = self.expect_ident("expected function name after `fn`")?;
        let params = self.parse_params()?;
        let return_type = if self.at_arrow() {
            self.advance();
            // Extern declarations also carry a trailing row (`! { FFI, Unsafe }`),
            // so the same declaration-binding suppression applies here.
            self.suppress_fn_type_row = true;
            let parsed = self.parse_type_expr("expected return type after `->`");
            self.suppress_fn_type_row = false;
            Some(parsed?)
        } else {
            None
        };
        let ret_taint = self.parse_taint_annotation();
        let effect_row = self.parse_effect_row();
        let effects = effect_row.unwrap_or_default();
        let end = self.expect_semicolon("expected `;` after extern fn declaration")?;

        Some(ExternFnDecl {
            abi,
            name,
            params,
            return_type,
            ret_taint,
            effects,
            span: start.join(end),
        })
    }

    /// PR-3a (trait Wall): a `trait Name { fn m(self: Self, …) -> Ty; … }`
    /// declaration — the contract a `T: Name` bound is checked against. v1 has
    /// no trait-level type params and no super-traits (heuristic 7).
    fn parse_trait(&mut self, visibility: Visibility, vis_span: Option<Span>) -> Option<TraitDef> {
        let start = vis_span.unwrap_or(self.current().span);
        self.advance(); // consume `trait`
        let (name, _) = self.expect_ident("expected trait name after `trait`")?;
        self.expect_lbrace("expected `{` after trait name")?;
        let mut methods = Vec::new();
        while !self.is_eof() && !self.at_rbrace() {
            // `pub` is implicit on a trait method; accept and ignore it.
            if self.at_pub() {
                self.advance();
            }
            if !self.at_fn() {
                self.diagnostics.push(Diagnostic::error(
                    codes::P012,
                    "expected a method signature (`fn name(...) -> Ty;`) inside the trait body",
                    Some(self.current().span),
                ));
                return None;
            }
            let sig = self.parse_trait_method_sig()?;
            methods.push(sig);
        }
        let end = self.expect_rbrace("expected `}` to close the trait body")?;
        Some(TraitDef {
            visibility,
            name,
            methods,
            super_traits: vec![],
            span: start.join(end),
        })
    }

    /// A trait method SIGNATURE: `fn name(params) -> Ty;` — no body, and (CM-T3)
    /// no effect row or refinement (trait methods are pure, fixed-shape). `self`
    /// and any `Self` types are kept verbatim; resolution to the implementing
    /// type happens at satisfaction-check time (PR-3b).
    fn parse_trait_method_sig(&mut self) -> Option<TraitMethodSig> {
        let start = self.current().span; // at `fn`
        self.advance(); // consume `fn`
        let (name, _) = self.expect_ident("expected method name after `fn`")?;
        // HK2: optional method-level type parameters `<A, B>` (e.g. `Functor`'s
        // `fn fmap<A, B>(self: Self<A>, …) -> Self<B>`). Reuses the same parser as
        // free-fn/record type params (incl. the `<F: * -> *>` kind fork, though a
        // trait method's own params are ordinary value types).
        let type_params = self.parse_type_params();
        let params = self.parse_params()?;
        let return_type = if self.at_arrow() {
            self.advance();
            Some(self.parse_type_expr("expected return type after `->`")?)
        } else {
            None
        };
        let end = self.expect_semicolon(
            "expected `;` after a trait method signature (trait methods are signatures only — no body)",
        )?;
        Some(TraitMethodSig {
            name,
            type_params,
            params,
            return_type,
            span: start.join(end),
        })
    }

    fn parse_actor(&mut self, visibility: Visibility, vis_span: Option<Span>) -> Option<ActorDef> {
        let start = vis_span.unwrap_or(self.current().span);
        let is_entry = if self.at_entry() {
            self.advance();
            true
        } else {
            false
        };

        self.expect_actor()?;
        let (name, _) = self.expect_ident("expected actor name after `actor`")?;
        self.expect_lbrace("expected `{` after actor name")?;

        let mut state_fields = Vec::new();
        let mut state_block_span: Option<Span> = None;
        let mut init = None;
        let mut handlers = Vec::new();
        let mut end = self.previous_span();

        while !self.is_eof() && !self.at_rbrace() {
            if self.at_state() {
                let (fields, span) = self.parse_state_block()?;
                if let Some(previous) = state_block_span {
                    self.diagnostics.push(Diagnostic::error(
                        codes::P009,
                        format!("duplicate `state` block in actor `{name}`"),
                        Some(previous.join(span)),
                    ));
                } else {
                    state_fields = fields;
                    state_block_span = Some(span);
                }
                end = span;
            } else if self.at_init() {
                let init_block = self.parse_init_block()?;
                end = init_block.span;
                if let Some(previous) = init.as_ref().map(|existing: &InitBlock| existing.span) {
                    self.diagnostics.push(Diagnostic::error(
                        codes::P010,
                        format!("duplicate `init` block in actor `{name}`"),
                        Some(previous.join(init_block.span)),
                    ));
                } else {
                    init = Some(init_block);
                }
            } else if self.at_on() {
                let handler = self.parse_handler()?;
                end = handler.span;
                handlers.push(handler);
            } else {
                self.diagnostics.push(Diagnostic::error(
                    codes::P011,
                    "expected `state`, `init`, or `on` inside actor body",
                    Some(self.current().span),
                ));
                if self.at_item_start() || self.at_module_start() {
                    // A misplaced but well-formed item (`fn`, a nested `actor`,
                    // ...). Consume it so the body continues and the actor's own
                    // `}` still matches: one diagnostic at the offending keyword
                    // beats a cascade from an actor the parser thinks never
                    // closed. `parse_item` is also what guarantees progress here
                    // — `synchronize_item` never consumes an item start, which
                    // is precisely how this loop used to spin forever.
                    let before = self.cursor;
                    let _ = self.parse_item();
                    if self.cursor == before {
                        self.advance();
                    }
                } else if !self.synchronize_item_made_progress() {
                    self.advance();
                }
            }
        }

        let close = self.expect_rbrace("expected `}` to close actor body")?;
        end = end.join(close);

        Some(ActorDef {
            visibility,
            name,
            is_entry,
            state_fields,
            init,
            handlers,
            span: start.join(end),
        })
    }

    fn parse_cap_type(
        &mut self,
        visibility: Visibility,
        vis_span: Option<Span>,
    ) -> Option<CapTypeDef> {
        let start = vis_span.unwrap_or(self.current().span);
        self.advance();
        self.expect_type("expected `type` after `cap`")?;
        let (name, name_span) = self.expect_ident("expected capability type name")?;

        // Wall 2 → Wall 3: parametric cap declaration. After the cap
        // name, an optional `(<p1>: i64, <p2>: i64, ...)` introduces a
        // comma-separated parameter list. Every parameter must be `i64`.
        // Empty parens, leading/trailing/double commas, and non-`i64`
        // types at any position all fire T198.
        let params = if self.at_lparen() {
            let paren_span = self.advance().span;
            if self.at_rparen() {
                let end = self.advance().span;
                self.diagnostics.push(Diagnostic::error(
                    codes::T198,
                    "parametric capability type requires at least one parameter declaration; use `cap type <Name> {}` for the non-parametric form or `cap type <Name>(<p1>: i64, <p2>: i64, ...) {}` to declare parameters",
                    Some(paren_span.join(end)),
                ));
                return None;
            }
            // MC-7 fence: leading comma invalid.
            if self.at_comma() {
                let comma_span = self.current().span;
                self.diagnostics.push(Diagnostic::error(
                    codes::T198,
                    "parametric capability type parameter list cannot start with `,`; remove the leading comma",
                    Some(comma_span),
                ));
                return None;
            }
            let mut collected: Vec<CapTypeParam> = Vec::new();
            loop {
                let (param_name, p_name_span) =
                    self.expect_ident("expected parameter name (e.g., `deadline_ms`)")?;
                self.expect_colon("expected `:` after capability parameter name")?;
                let ty_tok = self.current().clone();
                // INV-21 fence: every position must be `i64`. Lazy
                // implementations might only check position 0; we
                // enforce per-position here.
                let is_i64_ident = matches!(&ty_tok.kind, TokenKind::Ident(s) if s == "i64");
                if !is_i64_ident {
                    self.diagnostics.push(Diagnostic::error(
                        codes::T198,
                        format!(
                            "parametric capability type parameter `{param_name}` must be of type `i64`; Stage 1 of the deadline-typed cap rollout supports only `i64`-typed parameters at every position"
                        ),
                        Some(ty_tok.span),
                    ));
                    return None;
                }
                self.cursor += 1;
                collected.push(CapTypeParam {
                    name: param_name,
                    span: p_name_span.join(ty_tok.span),
                });
                if self.at_comma() {
                    let comma_span = self.current().span;
                    self.advance();
                    // MC-7 fence: trailing comma + double comma invalid.
                    if self.at_rparen() {
                        self.diagnostics.push(Diagnostic::error(
                            codes::T198,
                            "parametric capability type parameter list cannot end with a trailing `,`; remove the trailing comma",
                            Some(comma_span),
                        ));
                        return None;
                    }
                    if self.at_comma() {
                        self.diagnostics.push(Diagnostic::error(
                            codes::T198,
                            "parametric capability type parameter list cannot contain double `,`; each parameter is separated by a single comma",
                            Some(self.current().span),
                        ));
                        return None;
                    }
                    continue;
                }
                break;
            }
            self.expect_rparen("expected `)` after parameter list")?;
            collected
        } else {
            Vec::new()
        };

        // Capabilities-as-values: optional `mintable_by <Authority>[::<bit>]`
        // minting policy. `mintable_by` is a contextual keyword (not a lexer
        // token), placed after the optional params and before `{`/`;`. Absent
        // ⇒ `None` ⇒ the cap type is not mintable (fail-closed; T272 at any
        // `mint` site).
        let mintable_by = if matches!(self.current().kind, TokenKind::Ident(ref s) if s == "mintable_by")
        {
            let mb_start = self.advance().span;
            let (authority_cap, auth_span) =
                self.expect_ident("expected authority capability name after `mintable_by`")?;
            let (authority_name, end_span) = if self.at_colon_colon() {
                self.advance();
                let (bit, bit_span) =
                    self.expect_ident("expected authority name after `::` in `mintable_by`")?;
                (Some(bit), bit_span)
            } else {
                (None, auth_span)
            };
            Some(MintPolicy {
                authority_cap,
                authority_name,
                span: mb_start.join(end_span),
            })
        } else {
            None
        };

        if self.at_semicolon() {
            let end = self.advance().span;
            return Some(CapTypeDef {
                visibility,
                name,
                authorities: Vec::new(),
                params,
                mintable_by,
                span: start.join(name_span).join(end),
            });
        }

        self.expect_lbrace("expected `{` or `;` after capability type name")?;

        // Parse comma-separated authority names: { consume, split, query }
        let mut authorities = Vec::new();
        while !self.is_eof() && !self.at_rbrace() {
            if let Some((auth_name, _)) = self.expect_ident("expected authority name") {
                authorities.push(auth_name);
            }
            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }

        let close = self.expect_rbrace("expected `}` to close capability type")?;

        Some(CapTypeDef {
            visibility,
            name,
            authorities,
            params,
            mintable_by,
            span: start.join(close),
        })
    }

    fn parse_record(
        &mut self,
        visibility: Visibility,
        vis_span: Option<Span>,
    ) -> Option<RecordDef> {
        let start = vis_span.unwrap_or(self.current().span);
        self.advance(); // consume 'record'
        let (name, _name_span) = self.expect_ident("expected record name")?;
        let type_params = self.parse_type_params();
        self.expect_lbrace("expected `{` after record name")?;
        let (fields, _last_field_span) = self.parse_fields_until_rbrace(false)?;
        let close = self.expect_rbrace("expected `}` to close record definition")?;

        // Wall 4 Step 1: optional `where` clause refinement. Per V8, the
        // token `where` is recognized as a reserved keyword exclusively in
        // the immediately-post-`}` position of a record declaration; the
        // lexer treats it as a plain identifier everywhere else. Per V16,
        // Step 1 ships single-clause refinements only — SIGIL's lexer
        // doesn't tokenize `&&` / `||` anyway, so this scope cut is forced.
        let refinements = self.parse_optional_refinement_where(&fields);

        Some(RecordDef {
            visibility,
            name,
            type_params,
            fields,
            refinements,
            span: start.join(close),
        })
    }

    /// Wall 4 Step 1: parse the optional `where <field> <relop> <int-literal>`
    /// clause immediately following a record declaration's closing `}`. Returns
    /// an empty Vec when no `where` token is present.
    ///
    /// Validation per the Constraints & Fallbacks matrix:
    /// - **V2**: LHS identifier must appear in the declared field list.
    ///   Field-type-is-i64 is enforced later in `type_check.rs` (T212).
    /// - **V6 (T213)**: integer literal must lie in i32 range
    ///   `[-2_147_483_648, 2_147_483_647]`.
    /// - **V8**: `where` is keyword only in this position.
    /// - **V13 (T214)**: at most one clause per record in Step 1 (the
    ///   forced V16 scope cut).
    fn parse_optional_refinement_where(&mut self, fields: &[Field]) -> Vec<RefinementClause> {
        // V8: positional check. The token after `}` must be the Ident "where"
        // for this to be a refinement clause; otherwise return immediately and
        // leave the token stream to the next item.
        let is_where = matches!(self.current().kind, TokenKind::Ident(ref s) if s == "where");
        if !is_where {
            return Vec::new();
        }
        let where_span = self.current().span;
        self.advance(); // consume `where`

        // Parse exactly one clause: Ident RelOp IntLiteral.
        let (field_name, field_span) =
            match self.expect_ident("expected field name on left of refinement comparison") {
                Some(p) => p,
                None => return Vec::new(),
            };

        // V2: field-in-list (syntactic). Reject early with P_REF style error
        // (reuses existing parser-error idiom; type-check stage emits T212 for
        // the non-i64 case).
        if !fields.iter().any(|f| f.name == field_name) {
            self.diagnostics.push(Diagnostic::error(
                codes::T210,
                format!(
                    "refinement predicate references `{field_name}` which is not a declared field of this record"
                ),
                Some(field_span),
            ));
            self.recover_to_item_boundary();
            return Vec::new();
        }

        // Parse the comparison operator (one token, possibly compound).
        let op_tok = self.current().clone();
        let op = match op_tok.kind {
            TokenKind::LtEq => RefinementOp::Le,
            TokenKind::Lt => RefinementOp::Lt,
            TokenKind::GtEq => RefinementOp::Ge,
            TokenKind::Gt => RefinementOp::Gt,
            TokenKind::EqEq => RefinementOp::Eq,
            TokenKind::BangEq => RefinementOp::Ne,
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::T210,
                    "expected comparison operator (`<=`, `<`, `>=`, `>`, `==`, `!=`) in refinement predicate",
                    Some(op_tok.span),
                ));
                self.recover_to_item_boundary();
                return Vec::new();
            }
        };
        self.advance(); // consume the operator

        // RHS: Wall 4 Steps 4+5 commit #2 extends this from
        // integer-literal-only to a 2-way fork. Step 4's `Field` RHS
        // arrives in commit #3.
        //
        //   - `Ident . length ( )` → RefinementRhs::LengthOf(Ident)  (Step 5)
        //   - `[-] IntLit`         → RefinementRhs::Literal(signed)  (Steps 1+3)
        //
        // Step 5 (LengthOf) only appears when the next token is an
        // Ident; we peek past the Ident for `.` `length` `(` `)` to
        // disambiguate from Step 4's bare-Ident (`Field`). Until Step
        // 4's commit, bare-Ident RHS that isn't followed by `.length()`
        // is a parser error.
        let rhs_start = self.current().clone();
        if matches!(rhs_start.kind, TokenKind::Ident(_)) && self.peek_is_length_method() {
            // Step 5 LengthOf path.
            let ident_name = match &rhs_start.kind {
                TokenKind::Ident(s) => s.clone(),
                _ => unreachable!("guard checks Ident"),
            };
            self.advance(); // consume Ident
            // Consume `.length()` — peek_is_length_method already validated.
            self.advance(); // consume `.`
            self.advance(); // consume `length`
            self.advance(); // consume `(`
            let close_paren = self.current().clone();
            self.advance(); // consume `)`

            if self.reject_refinement_combinator(RefinementSite::Record) {
                return Vec::new();
            }
            let clause_span = where_span.join(close_paren.span);
            return vec![RefinementClause {
                field: field_name,
                op,
                rhs: crate::ast::RefinementRhs::LengthOf(ident_name),
                span: clause_span,
            }];
        }

        // Wall 4 Step 4: `<Ident>` (bare identifier, not followed by
        // `.length()`) at refinement-RHS position is the cross-field
        // `Field(name)` variant. V70 + V58 are enforced HERE at parse
        // time:
        //   V58 (T218): `field == field` (same name on both sides) is
        //   vacuous and rejected.
        //   V70: the parser produces `RefinementRhs::Field(ident_name)`;
        //   the type-check phase validates the ident resolves to a
        //   declared field of the enclosing record (T120 fires
        //   otherwise via the existing field-lookup path).
        //
        // Same-field validation against the LHS happens immediately;
        // resolve-to-declared-field validation happens in type_check
        // when the record's universe entry is populated.
        if let TokenKind::Ident(rhs_ident) = &rhs_start.kind {
            let rhs_name = rhs_ident.clone();
            if rhs_name == field_name {
                // V58 (T218): same-name vacuous self-reference.
                self.diagnostics.push(Diagnostic::error(
                    codes::T218,
                    format!(
                        "cross-field refinement self-references field `{field_name}` on both sides; the predicate is vacuous. Use distinct fields, a literal RHS, or drop the clause."
                    ),
                    Some(rhs_start.span),
                ));
                self.recover_to_item_boundary();
                return Vec::new();
            }
            self.advance(); // consume the bare Ident
            if self.reject_refinement_combinator(RefinementSite::Record) {
                return Vec::new();
            }
            let clause_span = where_span.join(rhs_start.span);
            return vec![RefinementClause {
                field: field_name,
                op,
                rhs: crate::ast::RefinementRhs::Field(rhs_name),
                span: clause_span,
            }];
        }

        // Step 1+3 Literal path. Accept optional unary minus for
        // negative literals since the lexer tokenizes `-1` as `Minus`
        // followed by `IntLit(1)`.
        let negate = matches!(self.current().kind, TokenKind::Minus);
        if negate {
            self.advance();
        }
        let lit_tok = self.current().clone();
        // PR-U3-b2: a WIDE (> i64::MAX) literal RHS becomes a `LiteralWide` bound
        // (RECORD site only — param/return/variant stay i64-only below). No i32
        // clamp: the wide path encodes via `Int::from_str` (exact at any
        // magnitude). The type-checker admits it ONLY on a `u256` field. A negative
        // wide bound is nonsensical for the unsigned u256 it targets → reject.
        if let TokenKind::IntLit256(limbs) = lit_tok.kind {
            self.advance(); // consume the wide literal
            if negate {
                self.diagnostics.push(Diagnostic::error(
                    codes::T213,
                    "a wide (> i64) refinement bound cannot be negative; u256 refinement bounds are non-negative",
                    Some(lit_tok.span),
                ));
                self.recover_to_item_boundary();
                return Vec::new();
            }
            if self.reject_refinement_combinator(RefinementSite::Record) {
                return Vec::new();
            }
            let clause_span = where_span.join(lit_tok.span);
            return vec![RefinementClause {
                field: field_name,
                op,
                rhs: crate::ast::RefinementRhs::LiteralWide(limbs),
                span: clause_span,
            }];
        }
        let magnitude = match lit_tok.kind {
            TokenKind::IntLit(v) => v,
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::T210,
                    "refinement RHS must be an integer literal, a sibling field name, or `<ident>.length()`",
                    Some(lit_tok.span),
                ));
                self.recover_to_item_boundary();
                return Vec::new();
            }
        };
        self.advance(); // consume literal

        // V6 (T213): magnitude must fit i32 ABS range.
        let signed: i64 = if negate { -magnitude } else { magnitude };
        const I32_MIN_I64: i64 = i32::MIN as i64;
        const I32_MAX_I64: i64 = i32::MAX as i64;
        if !(I32_MIN_I64..=I32_MAX_I64).contains(&signed) {
            self.diagnostics.push(Diagnostic::error(
                codes::T213,
                format!(
                    "refinement RHS literal `{signed}` is outside i32 range [-2147483648, 2147483647]; Wall 4 Step 1 uses QF_LIA encoding that is sound only within i32 limits"
                ),
                Some(lit_tok.span),
            ));
            self.recover_to_item_boundary();
            return Vec::new();
        }

        // V13 (T214): the forced V16 scope-cut means at most ONE clause
        // per record in Step 1, so a trailing combinator starts a second
        // predicate we don't admit.
        if self.reject_refinement_combinator(RefinementSite::Record) {
            return Vec::new();
        }

        let clause_span = where_span.join(lit_tok.span);
        vec![RefinementClause {
            field: field_name,
            op,
            rhs: crate::ast::RefinementRhs::Literal(signed),
            span: clause_span,
        }]
    }

    /// Wall 4 Step 6 commit #2: peek whether the current token is the
    /// Ident `where`. Used by `parse_enum` after a variant's payload
    /// to decide whether to enter the variant-refinement parser.
    /// V8-equivalent for enums: `where` is a reserved-keyword position
    /// only here (immediately after `)` or after the variant name when
    /// the variant has no payload — though zero-payload + where is
    /// itself a T223 error per N20-S6).
    fn variant_has_where_clause(&self) -> bool {
        matches!(self.current().kind, TokenKind::Ident(ref s) if s == "where")
    }

    /// Wall 4 Step 6 commit #2: parse a variant's optional refinement
    /// `where` clause. Parallel to `parse_optional_refinement_where`
    /// for records, but operates on `EnumVariantField` (named-payload
    /// fields) and emits T221 instead of T120 for unresolved field
    /// references (N19-S6: cross-variant references are not in scope).
    ///
    /// Pre-conditions: caller has verified (a) the variant has a
    /// `where` token at the current position, (b) `fields` is non-
    /// empty, (c) all `fields` have `name: Some(_)` (the all-named
    /// pre-condition of N4-S6 / T223 sub-case 1).
    ///
    /// Reuses the same RHS-shape grammar as records: integer literal,
    /// sibling-Ident, or `<Ident>.length()`. Per A1-S6 the registry
    /// hint is shared across T223 sub-cases.
    fn parse_optional_variant_refinement_where(
        &mut self,
        variant_name: &str,
        fields: &[EnumVariantField],
    ) -> Vec<RefinementClause> {
        let where_span = self.current().span;
        self.advance(); // consume `where`

        let (field_name, field_span) =
            match self.expect_ident("expected field name on left of variant refinement") {
                Some(p) => p,
                None => return Vec::new(),
            };

        // N19-S6: LHS field must be a NAMED payload field of this
        // variant. Cross-variant references → T221.
        let lhs_in_variant = fields
            .iter()
            .any(|f| f.name.as_deref() == Some(field_name.as_str()));
        if !lhs_in_variant {
            self.diagnostics.push(Diagnostic::error(
                codes::T221,
                format!(
                    "variant `{variant_name}` refinement references `{field_name}` which is not a named payload field of this variant; per N19-S6 variant refinement clauses scope to their own payload only"
                ),
                Some(field_span),
            ));
            self.recover_to_item_boundary();
            return Vec::new();
        }

        // Operator (mirrors record helper).
        let op_tok = self.current().clone();
        let op = match op_tok.kind {
            TokenKind::LtEq => RefinementOp::Le,
            TokenKind::Lt => RefinementOp::Lt,
            TokenKind::GtEq => RefinementOp::Ge,
            TokenKind::Gt => RefinementOp::Gt,
            TokenKind::EqEq => RefinementOp::Eq,
            TokenKind::BangEq => RefinementOp::Ne,
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::T220,
                    "expected comparison operator (`<=`, `<`, `>=`, `>`, `==`, `!=`) in variant refinement predicate",
                    Some(op_tok.span),
                ));
                self.recover_to_item_boundary();
                return Vec::new();
            }
        };
        self.advance(); // consume operator

        // RHS: 3-way fork mirroring the record helper.
        let rhs_start = self.current().clone();
        if matches!(rhs_start.kind, TokenKind::Ident(_)) && self.peek_is_length_method() {
            // LengthOf path.
            let ident_name = match &rhs_start.kind {
                TokenKind::Ident(s) => s.clone(),
                _ => unreachable!("guard checks Ident"),
            };
            self.advance(); // consume Ident
            self.advance(); // consume `.`
            self.advance(); // consume `length`
            self.advance(); // consume `(`
            let close_paren = self.current().clone();
            self.advance(); // consume `)`
            if self.reject_refinement_combinator(RefinementSite::Variant) {
                return Vec::new();
            }
            let clause_span = where_span.join(close_paren.span);
            return vec![RefinementClause {
                field: field_name,
                op,
                rhs: crate::ast::RefinementRhs::LengthOf(ident_name),
                span: clause_span,
            }];
        }

        // Bare-Ident → cross-field (Field RHS). N19-S6: the RHS field
        // must also be a payload field of THIS variant.
        if let TokenKind::Ident(rhs_ident) = &rhs_start.kind {
            let rhs_name = rhs_ident.clone();
            // V58 / N4-S6: same-name vacuous self-reference.
            if rhs_name == field_name {
                self.diagnostics.push(Diagnostic::error(
                    codes::T218,
                    format!(
                        "variant `{variant_name}` cross-field refinement self-references payload field `{field_name}` on both sides; the predicate is vacuous"
                    ),
                    Some(rhs_start.span),
                ));
                self.recover_to_item_boundary();
                return Vec::new();
            }
            // N19-S6: RHS field must be in THIS variant's payload.
            let rhs_in_variant = fields
                .iter()
                .any(|f| f.name.as_deref() == Some(rhs_name.as_str()));
            if !rhs_in_variant {
                self.diagnostics.push(Diagnostic::error(
                    codes::T221,
                    format!(
                        "variant `{variant_name}` cross-field refinement RHS `{rhs_name}` is not a named payload field of this variant; per N19-S6 references scope to the variant's own payload"
                    ),
                    Some(rhs_start.span),
                ));
                self.recover_to_item_boundary();
                return Vec::new();
            }
            self.advance(); // consume the bare Ident
            if self.reject_refinement_combinator(RefinementSite::Variant) {
                return Vec::new();
            }
            let clause_span = where_span.join(rhs_start.span);
            return vec![RefinementClause {
                field: field_name,
                op,
                rhs: crate::ast::RefinementRhs::Field(rhs_name),
                span: clause_span,
            }];
        }

        // Literal path with optional unary minus, mirroring records.
        let negate = matches!(self.current().kind, TokenKind::Minus);
        if negate {
            self.advance();
        }
        let lit_tok = self.current().clone();
        let magnitude = match lit_tok.kind {
            TokenKind::IntLit(v) => v,
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::T220,
                    "variant refinement RHS must be an integer literal, a sibling field name, or `<ident>.length()`",
                    Some(lit_tok.span),
                ));
                self.recover_to_item_boundary();
                return Vec::new();
            }
        };
        self.advance(); // consume literal
        let signed: i64 = if negate { -magnitude } else { magnitude };
        const I32_MIN_I64: i64 = i32::MIN as i64;
        const I32_MAX_I64: i64 = i32::MAX as i64;
        if !(I32_MIN_I64..=I32_MAX_I64).contains(&signed) {
            self.diagnostics.push(Diagnostic::error(
                codes::T213,
                format!(
                    "variant refinement RHS literal `{signed}` is outside i32 range [-2147483648, 2147483647]; Wall 4 uses QF_LIA encoding that is sound only within i32 limits"
                ),
                Some(lit_tok.span),
            ));
            self.recover_to_item_boundary();
            return Vec::new();
        }

        // N19-S6: one clause per variant, so a trailing combinator starts
        // a second predicate we don't admit.
        if self.reject_refinement_combinator(RefinementSite::Variant) {
            return Vec::new();
        }

        let clause_span = where_span.join(lit_tok.span);
        vec![RefinementClause {
            field: field_name,
            op,
            rhs: crate::ast::RefinementRhs::Literal(signed),
            span: clause_span,
        }]
    }

    /// Wall 4 Step 5 commit #2: peek `[Ident] . length ( )` shape from
    /// the current token forward, without consuming anything. The current
    /// token MUST be `Ident` (caller-checked). Returns true if the next
    /// four tokens are `.`, `length`, `(`, `)` in that order; false
    /// otherwise.
    ///
    /// Wall 4 Step 7 commit #1: parse the optional `where <param_name>
    /// RELOP literal` clause between the params close-paren and the
    /// return-type arrow. Parallel to `parse_optional_refinement_where`
    /// (records) and `parse_optional_variant_refinement_where`
    /// (variants).
    ///
    /// Per N3-S7: LHS Ident MUST match a declared param name of this
    /// `FnDef`. Per N5-S7: RHS is `RefinementRhs::Literal(i64)` ONLY —
    /// Field-RHS and LengthOf-RHS deferred to a future step. Per N7-S7
    /// / V16: single clause per where (multi-where at the same
    /// position fires T214 at the second `where`, per N37-S7).
    fn parse_optional_param_refinement_where(&mut self, params: &[Param]) -> Vec<RefinementClause> {
        let is_where = matches!(self.current().kind, TokenKind::Ident(ref s) if s == "where");
        if !is_where {
            return Vec::new();
        }
        let where_span = self.current().span;

        // Wall 4 Step 7 / NF-S7 follow-up: detect `where @ ...` at the
        // PARAM-where position. This means the user wrote
        // `fn f() where @ > 0` with no return type — the `@` is a
        // misplaced return-refinement reference (no return type means
        // no return value to reference). Fire T226 immediately per
        // N34-S7 rather than falling through to `expect_ident` which
        // would produce a confusing P-prefixed parse error.
        let next_is_at = self
            .tokens
            .get(self.cursor + 1)
            .map(|t| matches!(t.kind, TokenKind::At))
            .unwrap_or(false);
        if next_is_at {
            self.advance(); // consume `where`
            let at_span = self.current().span;
            self.advance(); // consume `@`
            self.diagnostics.push(Diagnostic::error(
                codes::T226,
                "function declares `where @ ...` return refinement but has no return type; the magic `@` requires an `i64` return type (per N6-S7). Add `-> i64` between the params and the return-where, or drop the return-refinement clause.",
                Some(where_span.join(at_span)),
            ));
            self.recover_to_item_boundary();
            return Vec::new();
        }

        self.advance(); // consume `where`

        let (field_name, field_span) =
            match self.expect_ident("expected param name on left of function refinement") {
                Some(p) => p,
                None => return Vec::new(),
            };

        // N3-S7: LHS Ident must match a declared param name.
        if !params.iter().any(|p| p.name == field_name) {
            self.diagnostics.push(Diagnostic::error(
                codes::T224,
                format!(
                    "function refinement references param `{field_name}` which is not a declared parameter of this function"
                ),
                Some(field_span),
            ));
            self.recover_to_item_boundary();
            return Vec::new();
        }

        // Operator parse — identical to record helper.
        let op_tok = self.current().clone();
        let op = match op_tok.kind {
            TokenKind::LtEq => RefinementOp::Le,
            TokenKind::Lt => RefinementOp::Lt,
            TokenKind::GtEq => RefinementOp::Ge,
            TokenKind::Gt => RefinementOp::Gt,
            TokenKind::EqEq => RefinementOp::Eq,
            TokenKind::BangEq => RefinementOp::Ne,
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::T224,
                    "expected comparison operator (`<=`, `<`, `>=`, `>`, `==`, `!=`) in function param refinement predicate",
                    Some(op_tok.span),
                ));
                self.recover_to_item_boundary();
                return Vec::new();
            }
        };
        self.advance(); // consume operator

        // RHS: literal-only per N5-S7. Optional unary minus.
        let negate = matches!(self.current().kind, TokenKind::Minus);
        if negate {
            self.advance();
        }
        let lit_tok = self.current().clone();
        let magnitude = match lit_tok.kind {
            TokenKind::IntLit(v) => v,
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::T224,
                    "function param refinement RHS must be an integer literal (Wall 4 Step 7 admits literal RHS only; Field / LengthOf RHS deferred per N5-S7)",
                    Some(lit_tok.span),
                ));
                self.recover_to_item_boundary();
                return Vec::new();
            }
        };
        self.advance(); // consume literal
        let signed: i64 = if negate { -magnitude } else { magnitude };
        const I32_MIN_I64: i64 = i32::MIN as i64;
        const I32_MAX_I64: i64 = i32::MAX as i64;
        if !(I32_MIN_I64..=I32_MAX_I64).contains(&signed) {
            self.diagnostics.push(Diagnostic::error(
                codes::T213,
                format!(
                    "function param refinement RHS literal `{signed}` is outside i32 range [-2147483648, 2147483647]; Wall 4 uses QF_LIA encoding sound only within i32 limits"
                ),
                Some(lit_tok.span),
            ));
            self.recover_to_item_boundary();
            return Vec::new();
        }

        // N7-S7: a trailing combinator starts a second predicate, which
        // this position doesn't admit either.
        if self.reject_refinement_combinator(RefinementSite::Param) {
            return Vec::new();
        }

        // N37-S7: AT MOST ONE `where` keyword per position. A second
        // immediately-following `where` fires T214.
        if matches!(self.current().kind, TokenKind::Ident(ref s) if s == "where") {
            self.diagnostics.push(Diagnostic::error(
                codes::T214,
                "Wall 4 Step 7 admits at most one `where` clause per syntactic position; combinators / multi-clause deferred per N7-S7",
                Some(self.current().span),
            ));
            self.recover_to_item_boundary();
            return Vec::new();
        }

        let clause_span = where_span.join(lit_tok.span);
        vec![RefinementClause {
            field: field_name,
            op,
            rhs: crate::ast::RefinementRhs::Literal(signed),
            span: clause_span,
        }]
    }

    /// Regions (DEF-2b, PR-5): parse `region ( IDENT )` as one side of a
    /// `where region(a): region(b)` outlives clause. Returns the region-parameter name and
    /// its span; `None` (with a P025) on a malformed operand.
    fn parse_region_outlives_operand(&mut self) -> Option<(String, Span)> {
        if !matches!(self.current().kind, TokenKind::Region) {
            self.diagnostics.push(Diagnostic::error(
                codes::P025,
                "expected `region(<name>)` in a `where region(a): region(b)` outlives clause",
                Some(self.current().span),
            ));
            return None;
        }
        self.advance(); // consume `region`
        if !matches!(self.current().kind, TokenKind::LParen) {
            self.diagnostics.push(Diagnostic::error(
                codes::P025,
                "expected `(` after `region` in a `where region(...)` outlives clause",
                Some(self.current().span),
            ));
            return None;
        }
        self.advance(); // consume `(`
        let (name, span) =
            self.expect_ident("expected a `Region` parameter name inside `region(...)`")?;
        if !matches!(self.current().kind, TokenKind::RParen) {
            self.diagnostics.push(Diagnostic::error(
                codes::P025,
                "expected `)` to close `region(...)` in a `where` outlives clause",
                Some(self.current().span),
            ));
            return None;
        }
        self.advance(); // consume `)`
        Some((name, span))
    }

    /// Regions (DEF-2b, LD-4 / PR-5): parse an optional `where region(a): region(b)[, …]`
    /// clause at the param-where position. Returns the `(a, b)` name pairs — `a` OUTLIVES
    /// `b` — or empty WITHOUT consuming when the `where` is absent or is a refinement-where
    /// (the token after `where` is not the `region` keyword), so the refinement parser still
    /// owns those. Both names must be `Region` parameters of this function (P025). DIRECT-
    /// PAIR-ONLY: a self/cyclic edge is stored verbatim and is inert (AG-2b-9).
    fn parse_optional_region_outlives_where(&mut self, params: &[Param]) -> Vec<(String, String)> {
        let is_where = matches!(self.current().kind, TokenKind::Ident(ref s) if s == "where");
        if !is_where {
            return Vec::new();
        }
        let next_is_region = self
            .tokens
            .get(self.cursor + 1)
            .map(|t| matches!(t.kind, TokenKind::Region))
            .unwrap_or(false);
        if !next_is_region {
            return Vec::new();
        }
        self.advance(); // consume `where`

        let mut pairs: Vec<(String, String)> = Vec::new();
        loop {
            let Some((a, a_span)) = self.parse_region_outlives_operand() else {
                self.recover_to_item_boundary();
                return pairs;
            };
            if !matches!(self.current().kind, TokenKind::Colon) {
                self.diagnostics.push(Diagnostic::error(
                    codes::P025,
                    "expected `:` between the two regions of `where region(a): region(b)`",
                    Some(self.current().span),
                ));
                self.recover_to_item_boundary();
                return pairs;
            }
            self.advance(); // consume `:`
            let Some((b, b_span)) = self.parse_region_outlives_operand() else {
                self.recover_to_item_boundary();
                return pairs;
            };
            // Both names must be `Region` parameters of this function (NC-2b-2).
            for (name, span) in [(&a, a_span), (&b, b_span)] {
                if !params
                    .iter()
                    .any(|p| p.name == *name && type_expr_is_region(&p.ty))
                {
                    self.diagnostics.push(Diagnostic::error(
                        codes::P025,
                        format!(
                            "`where region({name})`: `{name}` must be a `Region` parameter of this function"
                        ),
                        Some(span),
                    ));
                }
            }
            pairs.push((a, b));
            if matches!(self.current().kind, TokenKind::Comma) {
                self.advance(); // consume `,`
                continue;
            }
            break;
        }
        pairs
    }

    /// Wall 4 Step 7 commit #1: parse the optional `where @ RELOP literal`
    /// clause AFTER the return type. The magic `@` token references the
    /// function's return value (N4-S7). Per N34-S7 / MI-S7-15: if
    /// `has_return_type` is `false`, fire T226 because `@` has no
    /// referent.
    fn parse_optional_return_refinement_where(
        &mut self,
        has_return_type: bool,
    ) -> Option<RefinementClause> {
        let is_where = matches!(self.current().kind, TokenKind::Ident(ref s) if s == "where");
        if !is_where {
            return None;
        }
        let where_span = self.current().span;

        // Peek for `@` immediately after `where`. If the next token
        // isn't `@`, this isn't a return-refinement; back out without
        // consuming `where` so any subsequent parser pass can see it.
        // (Defensive: in practice no other production puts `where`
        // after the return type in the current grammar.)
        let next_is_at = self
            .tokens
            .get(self.cursor + 1)
            .map(|t| matches!(t.kind, TokenKind::At))
            .unwrap_or(false);
        if !next_is_at {
            self.diagnostics.push(Diagnostic::error(
                codes::T225,
                "return-refinement `where` must be followed by the magic `@` token referencing the return value (per N4-S7)",
                Some(self.current().span),
            ));
            self.recover_to_item_boundary();
            return None;
        }

        self.advance(); // consume `where`
        let at_span = self.current().span;
        self.advance(); // consume `@`

        // N34-S7: `where @ ...` without a return type → T226.
        if !has_return_type {
            self.diagnostics.push(Diagnostic::error(
                codes::T226,
                "function declares `where @ ...` return refinement but has no return type; the magic `@` requires an `i64` return type (per N6-S7). Add `-> i64` between the params and the return-where, or drop the return-refinement clause.",
                Some(where_span.join(at_span)),
            ));
            self.recover_to_item_boundary();
            return None;
        }

        // Operator parse.
        let op_tok = self.current().clone();
        let op = match op_tok.kind {
            TokenKind::LtEq => RefinementOp::Le,
            TokenKind::Lt => RefinementOp::Lt,
            TokenKind::GtEq => RefinementOp::Ge,
            TokenKind::Gt => RefinementOp::Gt,
            TokenKind::EqEq => RefinementOp::Eq,
            TokenKind::BangEq => RefinementOp::Ne,
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::T225,
                    "expected comparison operator (`<=`, `<`, `>=`, `>`, `==`, `!=`) after `@` in return refinement",
                    Some(op_tok.span),
                ));
                self.recover_to_item_boundary();
                return None;
            }
        };
        self.advance();

        // RHS: literal-only per N5-S7.
        let negate = matches!(self.current().kind, TokenKind::Minus);
        if negate {
            self.advance();
        }
        let lit_tok = self.current().clone();
        let magnitude = match lit_tok.kind {
            TokenKind::IntLit(v) => v,
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::T225,
                    "return refinement RHS must be an integer literal (Wall 4 Step 7 admits literal RHS only per N5-S7)",
                    Some(lit_tok.span),
                ));
                self.recover_to_item_boundary();
                return None;
            }
        };
        self.advance();
        let signed: i64 = if negate { -magnitude } else { magnitude };
        const I32_MIN_I64: i64 = i32::MIN as i64;
        const I32_MAX_I64: i64 = i32::MAX as i64;
        if !(I32_MIN_I64..=I32_MAX_I64).contains(&signed) {
            self.diagnostics.push(Diagnostic::error(
                codes::T213,
                format!(
                    "return refinement RHS literal `{signed}` is outside i32 range; Wall 4 uses QF_LIA encoding sound only within i32 limits"
                ),
                Some(lit_tok.span),
            ));
            self.recover_to_item_boundary();
            return None;
        }

        // N4-S7: a trailing combinator starts a second predicate, which
        // the return position doesn't admit either.
        if self.reject_refinement_combinator(RefinementSite::Return) {
            return None;
        }

        // N37-S7: AT MOST ONE `where` per position.
        if matches!(self.current().kind, TokenKind::Ident(ref s) if s == "where") {
            self.diagnostics.push(Diagnostic::error(
                codes::T214,
                "Wall 4 Step 7 admits at most one `where` clause per syntactic position",
                Some(self.current().span),
            ));
            self.recover_to_item_boundary();
            return None;
        }

        let clause_span = where_span.join(lit_tok.span);
        Some(RefinementClause {
            // N4-S7: sentinel for the return value.
            field: "@".to_string(),
            op,
            rhs: crate::ast::RefinementRhs::Literal(signed),
            span: clause_span,
        })
    }

    /// V69: `.length()` is a refinement-RHS-only form. The parser doesn't
    /// promote it to a general method call anywhere else (A11 inherits).
    fn peek_is_length_method(&self) -> bool {
        let offset = self.cursor + 1;
        if offset + 3 >= self.tokens.len() {
            return false;
        }
        let dot = &self.tokens[offset].kind;
        let length = &self.tokens[offset + 1].kind;
        let open = &self.tokens[offset + 2].kind;
        let close = &self.tokens[offset + 3].kind;
        matches!(dot, TokenKind::Dot)
            && matches!(length, TokenKind::Ident(s) if s == "length")
            && matches!(open, TokenKind::LParen)
            && matches!(close, TokenKind::RParen)
    }

    /// V13 (T214): called once a refinement clause is syntactically
    /// complete. A combinator in trailing position starts a SECOND
    /// predicate, which the Wall 4 grammar defers. Emits T214 at the
    /// combinator, recovers to the next item, and returns `true` so the
    /// caller bails with no clauses.
    ///
    /// Matches both the two-token spelling (`AndAnd` / `OrOr`) and the
    /// single-char one (`Ampersand` / `Pipe`). The single-char pair was
    /// all this guard checked while the lexer still split `&&` into two
    /// `Ampersand`s; once `&&` / `||` became dedicated tokens, matching
    /// only the old pair silently let every compound predicate fall
    /// through to a generic P006 at the item boundary.
    fn reject_refinement_combinator(&mut self, site: RefinementSite) -> bool {
        if !matches!(
            self.current().kind,
            TokenKind::AndAnd | TokenKind::OrOr | TokenKind::Ampersand | TokenKind::Pipe
        ) {
            return false;
        }
        self.diagnostics.push(Diagnostic::error(
            codes::T214,
            site.compound_predicate_message(),
            Some(self.current().span),
        ));
        self.recover_to_item_boundary();
        true
    }

    /// Coarse error recovery used after a refinement-clause parse fails:
    /// skip forward until we see something that looks like the start of the
    /// next top-level item, so the rest of the module can still be parsed.
    fn recover_to_item_boundary(&mut self) {
        while !self.is_eof() {
            let k = &self.current().kind;
            if matches!(
                k,
                TokenKind::Semicolon
                    | TokenKind::Record
                    | TokenKind::Enum
                    | TokenKind::Fn
                    | TokenKind::Actor
                    | TokenKind::Module
                    | TokenKind::Pub
                    | TokenKind::Effect
                    | TokenKind::Cap
                    | TokenKind::Use
                    | TokenKind::Const
            ) {
                if matches!(k, TokenKind::Semicolon) {
                    self.advance();
                }
                return;
            }
            self.advance();
        }
    }

    fn parse_enum(&mut self, visibility: Visibility, vis_span: Option<Span>) -> Option<EnumDef> {
        let start = vis_span.unwrap_or(self.current().span);
        self.advance(); // consume 'enum'
        let (name, _name_span) = self.expect_ident("expected enum name")?;
        let type_params = self.parse_type_params();
        self.expect_lbrace("expected `{` after enum name")?;

        let mut variants = Vec::new();
        while !self.is_eof() && !self.at_rbrace() {
            let variant_start = self.current().span;
            let (variant_name, _) = self.expect_ident("expected variant name")?;

            // Wall 4 Step 6 commit #2: payload parsing now admits both
            // positional (`V(i64)`) and named (`V(x: i64)`) shapes, but
            // a single variant must be ALL-named OR ALL-positional
            // (N4-S6 / N12-S6 — mixed fires T223). The 2-token
            // lookahead `Ident` + `Colon` (N17-S6) is the
            // disambiguator at each field position.
            let (fields, payload_form) = if self.at_lparen() {
                self.advance(); // consume '('
                let mut variant_fields: Vec<EnumVariantField> = Vec::new();
                // None until the first field commits to a form.
                let mut form: Option<PayloadForm> = None;
                let mut shape_error_emitted = false;
                while !self.is_eof() && !self.at_rparen() {
                    let field_start = self.current().span;
                    // N17-S6: 2-token peek. If the current token is
                    // Ident AND the next is Colon, parse as named.
                    let next_is_colon = self.cursor + 1 < self.tokens.len()
                        && matches!(self.tokens[self.cursor + 1].kind, TokenKind::Colon);
                    let is_named_field =
                        matches!(self.current().kind, TokenKind::Ident(_)) && next_is_colon;

                    // N12-S6: state-tracking across the payload list.
                    let this_form = if is_named_field {
                        PayloadForm::Named
                    } else {
                        PayloadForm::Positional
                    };
                    match form {
                        None => form = Some(this_form),
                        Some(prev) if prev == this_form => {}
                        Some(_) => {
                            // Mid-payload mismatch — T223 sub-case 2.
                            if !shape_error_emitted {
                                self.diagnostics.push(Diagnostic::error(
                                    codes::T223,
                                    format!(
                                        "variant `{variant_name}` mixes named and positional payload fields; pick all-named (`V(x: i64, y: i64)`) or all-positional (`V(i64, i64)`)"
                                    ),
                                    Some(field_start),
                                ));
                                shape_error_emitted = true;
                            }
                        }
                    }

                    let (field_name, field_name_span) = if is_named_field {
                        let (n, span) = self.expect_ident("expected named payload field")?;
                        self.expect_colon("expected `:` after named payload field")?;
                        (Some(n), Some(span))
                    } else {
                        (None, None)
                    };

                    // N5-S6: no-duplicate field names within a named
                    // variant. Sub-case 3 of T223.
                    if let Some(ref nm) = field_name
                        && variant_fields
                            .iter()
                            .any(|f| f.name.as_deref() == Some(nm.as_str()))
                    {
                        self.diagnostics.push(Diagnostic::error(
                            codes::T223,
                            format!(
                                "variant `{variant_name}` declares duplicate payload field name `{nm}`; rename one"
                            ),
                            field_name_span,
                        ));
                        shape_error_emitted = true;
                    }

                    let ty = self.parse_type_expr("expected variant field type")?;
                    let field_end = self.tokens[self.cursor.saturating_sub(1)].span;
                    variant_fields.push(EnumVariantField {
                        name: field_name,
                        ty,
                        span: field_start.join(field_end),
                    });
                    if self.at_comma() {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect_rparen("expected `)` after variant fields")?;
                let resolved_form = form.unwrap_or(PayloadForm::Positional);
                (variant_fields, resolved_form)
            } else {
                (Vec::new(), PayloadForm::Positional)
            };

            // Wall 4 Step 6: after the payload close, look for an
            // optional `where` clause on this variant. Three pre-
            // conditions per the constraint matrix:
            //
            //   (1) N20-S6 / T223 sub-case 4: zero-payload variants
            //       CANNOT carry refinements ("no fields to refine").
            //   (2) N4-S6 / T223 sub-case 1: positional-only variants
            //       with refinements are rejected.
            //   (3) The named-payload variant proceeds to the variant-
            //       refinement clause parser (parallel to the record
            //       helper but operating on `EnumVariantField`).
            let refinements = if self.variant_has_where_clause() {
                let where_span = self.current().span;
                if fields.is_empty() {
                    // (1) zero-payload + where → T223
                    self.diagnostics.push(Diagnostic::error(
                        codes::T223,
                        format!(
                            "variant `{variant_name}` has no payload fields, so cannot carry a refinement `where` clause"
                        ),
                        Some(where_span),
                    ));
                    self.recover_to_item_boundary();
                    Vec::new()
                } else if payload_form == PayloadForm::Positional {
                    // (2) positional + where → T223
                    self.diagnostics.push(Diagnostic::error(
                        codes::T223,
                        format!(
                            "variant `{variant_name}` has positional-only payload; refinement `where` clauses require all-named payload fields (rewrite as `V(x: i64) where x > 0`)"
                        ),
                        Some(where_span),
                    ));
                    self.recover_to_item_boundary();
                    Vec::new()
                } else {
                    // (3) named + where → parse variant refinements.
                    self.parse_optional_variant_refinement_where(&variant_name, &fields)
                }
            } else {
                Vec::new()
            };

            let variant_end = self.tokens[self.cursor.saturating_sub(1)].span;
            variants.push(EnumVariant {
                name: variant_name,
                fields,
                refinements,
                span: variant_start.join(variant_end),
            });

            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }

        let close = self.expect_rbrace("expected `}` to close enum definition")?;
        Some(EnumDef {
            visibility,
            name,
            type_params,
            variants,
            span: start.join(close),
        })
    }

    fn parse_impl_block(
        &mut self,
        _visibility: Visibility,
        vis_span: Option<Span>,
    ) -> Option<ImplDef> {
        let start = vis_span.unwrap_or(self.current().span);
        self.advance(); // consume 'impl'
        let (first_name, first_span) =
            self.expect_ident("expected a type or trait name after `impl`")?;

        // PR-5 (trait Wall): `impl Trait for Type { ... }` is an EXPLICIT trait
        // impl — the methods attach to `Type` exactly as an inherent
        // `impl Type { ... }`; the trait name is recorded for the orphan /
        // coherence checks (T249 / T250). No `for` ⇒ `trait_name = None`.
        let (trait_name, type_name, type_name_span) = if self.at_for() {
            self.advance(); // consume `for`
            let (ty, ty_span) = self.expect_ident("expected the implementing type after `for`")?;
            (Some(first_name), ty, ty_span)
        } else {
            (None, first_name, first_span)
        };

        // SIGIL Complete v0 / Phase 6 supremum path: optionally consume
        // impl-block-level type parameters `<T, E, ...>`. Per N10-V0,
        // declaration order is preserved by `parse_type_params`'s
        // `Vec::push` (no sort/dedup). Empty Vec → non-generic impl
        // block, backward-compatible with all existing `impl Foo { ... }`.
        let type_params = self.parse_type_params();
        // PR-1: name-only view for the `&[String]` shadow/mirror helpers below.
        let type_param_names: Vec<String> = crate::ast::type_param_names(&type_params);

        // N4-V0: T229 — duplicate type parameter names in the impl block.
        // BTreeSet equality check; if the dedup'd set size differs from
        // the Vec size, at least one name is duplicated. Per N4-V0 the
        // duplicate fires T229 before the impl block is added to the
        // AST so downstream substitution never sees the malformed shape.
        if !type_params.is_empty() {
            let mut seen: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
            let mut duplicates: Vec<&str> = Vec::new();
            for p in &type_params {
                let name = p.name.as_str();
                if !seen.insert(name) && !duplicates.contains(&name) {
                    duplicates.push(name);
                }
            }
            if !duplicates.is_empty() {
                let dup_list = duplicates
                    .iter()
                    .map(|n| format!("`{n}`"))
                    .collect::<Vec<_>>()
                    .join(", ");
                self.diagnostics.push(Diagnostic::error(
                    codes::T229,
                    format!(
                        "impl block on `{type_name}` declares duplicate type parameter name(s): {dup_list} — every type parameter must be unique within the impl block"
                    ),
                    Some(type_name_span),
                ));
            }
        }

        self.expect_lbrace("expected `{` after impl type name")?;

        let mut methods = Vec::new();
        while !self.is_eof() && !self.at_rbrace() {
            // Optionally consume `pub` modifier before `fn`. SIGIL Complete
            // v0 / Phase 6: stdlib combinators (`pub fn map<U>(...)`) need
            // this. Pre-v0 the parser didn't accept `pub` inside impl
            // blocks because no real `.sigil` file ever exercised them.
            let method_visibility = if self.at_pub() {
                self.advance();
                Visibility::Public
            } else {
                Visibility::Public // impl methods default to public per MC-v0-Q
            };
            if self.at_fn() {
                if let Some(method) = self.parse_fn(method_visibility, None) {
                    // N5-V0: T228 — method-level type-param shadows
                    // impl-block-level type-param. The check runs at
                    // parse time AND in `collect_function_sigs`
                    // (defensive). Both routes call the shared helper.
                    let shadows = enforce_no_method_impl_shadow(&type_param_names, &method);
                    for (shadowed, span) in shadows {
                        self.diagnostics.push(Diagnostic::error(
                            codes::T228,
                            format!(
                                "method `{}` declares type parameter `{shadowed}` which shadows impl block `{type_name}`'s type parameter — rename the method-level parameter (e.g., `<U>`) or drop the redeclaration (the impl's `{shadowed}` is already in scope)",
                                method.name
                            ),
                            Some(span),
                        ));
                    }

                    // N6-V0: T230 — method's `self`-param type-arg
                    // structure must mirror impl's type_params in
                    // declaration order. Skip for non-generic impl
                    // blocks (no binders to mismatch).
                    if !type_params.is_empty()
                        && let Some(diag) = check_self_param_mirrors_impl_type_params(
                            &type_name,
                            &type_param_names,
                            &method,
                        )
                    {
                        self.diagnostics.push(diag);
                    }

                    methods.push(method);
                }
            } else {
                self.diagnostics.push(Diagnostic::error(
                    codes::P012,
                    "expected `fn` inside impl block",
                    Some(self.current().span),
                ));
                self.advance();
            }
        }

        let close = self.expect_rbrace("expected `}` to close impl block")?;
        Some(ImplDef {
            type_name,
            trait_name,
            type_params,
            methods,
            span: start.join(close),
        })
    }

    fn parse_state_block(&mut self) -> Option<(Vec<Field>, Span)> {
        let start = self.advance().span;
        self.expect_lbrace("expected `{` after `state`")?;
        let (fields, last_field_span) = self.parse_fields_until_rbrace(true)?;
        let close = self.expect_rbrace("expected `}` to close state block")?;
        Some((fields, last_field_span.unwrap_or(start).join(close)))
    }

    /// Typestate (Epic 1): a top-level `state Name { A, B }` protocol declaration —
    /// the closed state-marker set for the carrier record `Name<@S>`. Distinct from
    /// the actor `state { fields }` block (no name; `parse_state_block`); the leading
    /// protocol name disambiguates the two forms.
    fn parse_state_def(
        &mut self,
        visibility: Visibility,
        vis_span: Option<Span>,
    ) -> Option<StateDef> {
        let start = vis_span.unwrap_or(self.current().span);
        self.advance(); // consume `state`
        let (name, _) = self.expect_ident("expected protocol name after `state`")?;
        self.expect_lbrace("expected `{` after the state protocol name")?;
        let mut states = vec![];
        while !self.is_eof() && !self.at_rbrace() {
            let Some((marker, _)) = self.expect_ident("expected a state-marker name") else {
                break;
            };
            states.push(marker);
            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }
        let close = self.expect_rbrace("expected `}` to close the state protocol")?;
        Some(StateDef {
            visibility,
            name,
            states,
            span: start.join(close),
        })
    }

    fn parse_init_block(&mut self) -> Option<InitBlock> {
        let start = self.advance().span;
        let params = self.parse_params()?;
        let body = self.parse_body("expected init body")?;

        Some(InitBlock {
            params,
            span: start.join(body.span),
            body,
        })
    }

    fn parse_handler(&mut self) -> Option<Handler> {
        let start = self.advance().span;
        let (message_name, _) = self.expect_ident("expected handler message name after `on`")?;
        let params = self.parse_params()?;
        let return_type = if self.at_arrow() {
            self.advance();
            Some(self.parse_type_expr("expected return type after `->`")?)
        } else {
            None
        };
        let body = self.parse_body("expected handler body")?;

        Some(Handler {
            message_name,
            params,
            return_type,
            span: start.join(body.span),
            body,
        })
    }

    /// Parameter list for a position where `@Flow` is NOT admissible — every
    /// caller except an `fn` item (externs, traits, actor handlers/inits,
    /// effect operations, closures). Taint polymorphism is checked by
    /// re-verifying the callee's BODY per label, so it can only be offered
    /// where a body exists and is checked here.
    fn parse_params(&mut self) -> Option<Vec<Param>> {
        self.parse_params_inner(false)
    }

    /// Parameter list for an `fn` item, where `@Flow` is admissible.
    fn parse_params_allowing_flow(&mut self) -> Option<Vec<Param>> {
        self.parse_params_inner(true)
    }

    fn parse_params_inner(&mut self, allow_flow: bool) -> Option<Vec<Param>> {
        self.expect_lparen("expected `(`")?;
        let mut params = Vec::new();

        while !self.is_eof() && !self.at_rparen() {
            let (name, name_span) = self.expect_ident("expected parameter name")?;
            self.expect_colon("expected `:` after parameter name")?;
            let ty = self.parse_type_expr("expected parameter type after `:`")?;
            let (taint, mutability, region, mut flow) = self.parse_param_annotations();
            if flow && !allow_flow {
                self.diagnostics.push(Diagnostic::error(
                    codes::P021,
                    "`@Flow` is only valid on the parameters and return type of an `fn` item \
                     (not on externs, traits, actor handlers, effect operations, or closures)"
                        .to_string(),
                    Some(name_span),
                ));
                flow = false;
            }
            let param_span = name_span.join(ty.span);
            params.push(Param {
                name,
                ty,
                taint,
                mutability,
                region,
                flow,
                span: param_span,
            });

            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }

        self.expect_rparen("expected `)` after parameter list")?;
        // Regions (DEF-2b, NC-2b-2 / R8): every `@in r` must name a `Region` PARAMETER of
        // this function (forward references are fine — the full list is now built). `@in`
        // on a missing name or a non-`Region` param is P024 — the slot the AG-R2 lift maps
        // to must be a real region.
        for p in &params {
            if let Some(r) = &p.region
                && !params
                    .iter()
                    .any(|q| q.name == *r && type_expr_is_region(&q.ty))
            {
                self.diagnostics.push(Diagnostic::error(
                    codes::P024,
                    format!("`@in {r}`: `{r}` must be a `Region` parameter of this function"),
                    Some(p.span),
                ));
            }
        }
        Some(params)
    }

    /// Parse `name: Type` fields up to the closing `}`. `allow_mut` gates the
    /// MUTABLE-STATE S1 leading `mut` marker: an actor `state {}` block accepts
    /// `mut n: T` (captured as `Mutability::Mut`), but the SAME grammar also
    /// serves records — where a leading `mut` is rejected with P030 (a state-only
    /// keyword must not leak into records).
    fn parse_fields_until_rbrace(&mut self, allow_mut: bool) -> Option<(Vec<Field>, Option<Span>)> {
        let mut fields = Vec::new();
        let mut last_span = None;

        while !self.is_eof() && !self.at_rbrace() {
            // S1: an optional leading `mut`. Consumed in either context (so the
            // field name still parses for recovery), but only KEPT for state
            // fields; a record `mut` is rejected loudly (P030).
            let mutability = if matches!(self.current().kind, TokenKind::Mut) {
                let mut_span = self.current().span;
                self.advance(); // consume `mut`
                if allow_mut {
                    Mutability::Mut
                } else {
                    self.diagnostics.push(Diagnostic::error(
                        codes::P030,
                        "`mut` is only allowed on actor `state` fields, not record fields",
                        Some(mut_span),
                    ));
                    Mutability::Default
                }
            } else {
                Mutability::Default
            };
            let (name, name_span) = self.expect_ident("expected field name")?;
            self.expect_colon("expected `:` after field name")?;
            let ty = self.parse_type_expr("expected field type after `:`")?;
            let field_span = name_span.join(ty.span);

            fields.push(Field {
                name,
                ty,
                span: field_span,
                mutability,
            });
            last_span = Some(field_span);

            if self.at_comma() || self.at_semicolon() {
                self.advance();
            } else if !self.at_rbrace() {
                self.diagnostics.push(Diagnostic::error(
                    codes::P013,
                    "expected `,`, `;`, or `}` after field declaration",
                    Some(self.current().span),
                ));
                if !self.synchronize_item_made_progress() {
                    break;
                }
            }
        }

        Some((fields, last_span))
    }

    fn parse_type_params(&mut self) -> Vec<TypeParam> {
        if !self.at_lt() {
            return vec![];
        }
        self.advance(); // consume <
        let mut params = vec![];
        while !self.is_eof() && !self.at_gt() {
            // Typestate (Epic 1): a leading `@` marks a STATE-kinded binder `<@S>` —
            // a phantom protocol-state index. Token-disjoint from `*` (HKT) and from
            // a bare ident (ordinary generic).
            let state_kinded = matches!(self.current().kind, TokenKind::At);
            if state_kinded {
                self.advance(); // consume `@`
            }
            if let Some((name, span)) = self.expect_ident("expected type parameter name") {
                // PR-2 (trait epic): an optional `: Bound + Bound + …` trait-bound
                // list. Bounds are collected by NAME only — unknown-trait and
                // satisfaction checks run at type-check, where the trait registry
                // exists (T248 / T245). An empty list is the unbounded common
                // case. `at_colon` is the single `:` (turbofish `::` is separate).
                let mut bounds = vec![];
                let mut kind = if state_kinded {
                    ParamKind::State
                } else {
                    ParamKind::Star
                };
                if state_kinded && self.at_colon() {
                    // A state binder `@S` admits no `:` bound or kind annotation (P028).
                    self.diagnostics.push(Diagnostic::error(
                        codes::P028,
                        "a state-kinded type parameter `@S` takes no `:` bound or kind annotation",
                        Some(self.current().span),
                    ));
                    self.advance(); // consume the stray `:` for recovery
                    self.parse_bound_list(&mut bounds);
                    bounds.clear(); // a state binder carries no bounds
                } else if self.at_colon() {
                    self.advance(); // consume `:`
                    // HKT (EX-5): fork on the post-`:` token. A `*` begins a KIND
                    // annotation (`<F: * -> *>`) — the two grammars are token-
                    // disjoint (`*` is never a trait-bound name). Otherwise it is
                    // the ordinary trait-bound list (`<T: Hash + Eq>`). After a
                    // kind, an optional `+ Bound …` may still follow
                    // (`<F: * -> * + Functor>`).
                    if self.at_star() {
                        if let Some(arity) = self.parse_kind() {
                            kind = ParamKind::Constructor { arity };
                        }
                        if self.at_plus() {
                            self.advance(); // `+` after the kind → bound list
                            self.parse_bound_list(&mut bounds);
                        }
                    } else {
                        // Exits cleanly when `expect_ident` fails (a diagnostic is
                        // already emitted — no spin); the inner `break` stops a
                        // well-formed list at the first non-`+`.
                        self.parse_bound_list(&mut bounds);
                    }
                }
                params.push(TypeParam {
                    name,
                    bounds,
                    kind,
                    span,
                });
            }
            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }
        if self.at_gt() {
            self.advance();
        }
        params
    }

    /// Parse a `Bound + Bound + …` trait-bound list, appending names to `bounds`.
    /// Exits cleanly when `expect_ident` fails (a diagnostic is already emitted —
    /// no spin); the inner `break` stops a well-formed list at the first non-`+`.
    fn parse_bound_list(&mut self, bounds: &mut Vec<String>) {
        while let Some((bound_name, _)) =
            self.expect_ident("expected trait name in type-parameter bound")
        {
            bounds.push(bound_name);
            if self.at_plus() {
                self.advance(); // `+` → expect another bound
            } else {
                break;
            }
        }
    }

    /// HKT (EX-5): parse a higher-kinded annotation `* (-> *)*` after the `:` of a
    /// type-parameter binder and return its arity (the arrow count). The grammar is
    /// fail-closed: it MUST begin with `*`, every `->` MUST be followed by `*`, and
    /// the arity MUST lie in `[1, MAX_KIND_ARITY]` — a bare `*` (arity 0) is not
    /// higher-kinded. On any violation it emits P027 and returns `None`; the caller
    /// leaves the parameter `Star`-kinded and recovers.
    fn parse_kind(&mut self) -> Option<usize> {
        debug_assert!(self.at_star(), "parse_kind entered without a leading `*`");
        let start = self.current().span;
        self.advance(); // consume the leading `*`
        let mut arity = 0usize;
        let mut end = start;
        while self.at_arrow() {
            self.advance(); // consume `->`
            if !self.at_star() {
                self.diagnostics.push(Diagnostic::error(
                    codes::P027,
                    "expected `*` after `->` in a higher-kinded type-parameter kind",
                    Some(self.current().span),
                ));
                return None;
            }
            end = self.current().span;
            self.advance(); // consume `*`
            arity += 1;
        }
        let span = start.join(end);
        if arity == 0 {
            self.diagnostics.push(Diagnostic::error(
                codes::P027,
                "`*` alone is not higher-kinded; a higher-kinded parameter needs a kind like `* -> *`",
                Some(span),
            ));
            return None;
        }
        if arity > MAX_KIND_ARITY {
            self.diagnostics.push(Diagnostic::error(
                codes::P027,
                "higher-kinded arity exceeds the maximum of 2 (e.g. `* -> * -> *`)",
                Some(span),
            ));
            return None;
        }
        Some(arity)
    }

    /// Depth-guarding wrapper: `Fn(...)` types, tuple/grouping `( … )` types,
    /// generic type arguments, and array types all recurse through here with no
    /// other guard, so a deep `let x: (((( … ))))` would otherwise overflow the
    /// stack during type parsing. See `enter_nesting`.
    fn parse_type_expr(&mut self, message: &'static str) -> Option<TypeExpr> {
        if !self.enter_nesting() {
            return None;
        }
        let result = self.parse_type_expr_inner(message);
        self.exit_nesting();
        result
    }

    /// Parse a nested type in a DELIMITER-BOUNDED position — inside `( … )`,
    /// `[ … ]`, `< … >`, or a parameter list. A trailing `! { … }` there is
    /// unambiguous (the closing delimiter bounds it), so declaration-return row
    /// suppression is lifted for the duration and restored after. Positions that
    /// remain TRAILING (a Fn type's own return slot, a `&T` target) do NOT use
    /// this — they inherit the ambient flag.
    fn parse_bounded_type_expr(&mut self, message: &'static str) -> Option<TypeExpr> {
        let saved = self.suppress_fn_type_row;
        self.suppress_fn_type_row = false;
        let out = self.parse_type_expr(message);
        self.suppress_fn_type_row = saved;
        out
    }

    fn parse_type_expr_inner(&mut self, message: &'static str) -> Option<TypeExpr> {
        // PR B / N29-PRB: function-type syntax `Fn(T1, T2, ...) -> U`.
        // Must check BEFORE the path-based parse below (which would
        // otherwise interpret `Fn(...)` as a parametric-cap usage and
        // fire T198 expecting i64 literals).
        //
        // Distinguished by:
        //   - current token is `Ident("Fn")`
        //   - next token is `LParen`
        //
        // Closure expression `Expr::Closure` keeps its own parsing
        // path via `TokenKind::Fn` (lowercase `fn`); this is the
        // capital-Fn TYPE-expression path. The two are disambiguated
        // by the lexer producing `TokenKind::Fn` for `fn` and a
        // regular `Ident("Fn")` for `Fn`.
        if matches!(&self.current().kind, TokenKind::Ident(s) if s == "Fn")
            && matches!(self.peek().kind, TokenKind::LParen)
        {
            let fn_start = self.current().span;
            self.advance(); // consume `Fn`
            self.advance(); // consume `(`
            let mut params: Vec<TypeExpr> = Vec::new();
            while !self.is_eof() && !self.at_rparen() {
                // Bounded by `)` — declaration-return row suppression lifted.
                let param = self.parse_bounded_type_expr("expected Fn parameter type")?;
                params.push(param);
                if self.at_comma() {
                    self.advance();
                } else {
                    break;
                }
            }
            let _params_close = self.expect_rparen("expected `)` after Fn parameter list")?;
            if !self.at_arrow() {
                self.diagnostics.push(Diagnostic::error(
                    codes::P002,
                    "expected `->` after Fn parameter list".to_string(),
                    Some(self.current().span),
                ));
                return None;
            }
            self.advance(); // consume `->`
            // The Fn RETURN position stays under the ambient suppression: in
            // `-> Fn(i64) -> Fn(i64) -> i64 ! { A } { body }` the row is still
            // TRAILING, so it must still bind to the declaration.
            let return_type = self.parse_type_expr("expected Fn return type after `->`")?;
            // Latent-row suffix (roadmap Phase 3): `Fn(T) -> U ! { E }`. In
            // declaration-return position (suppress_fn_type_row) the trailing
            // row is the DECLARATION's — leave it unconsumed and say so (P031),
            // because a silent binding choice here is the one failure mode the
            // parser differential structurally cannot catch.
            let effects = if self.suppress_fn_type_row {
                if self.at_bang() {
                    self.diagnostics.push(Diagnostic::warning(
                        codes::P031,
                        "this `! { … }` binds to the DECLARATION's effect row, not to the \
                         returned `Fn` type; parenthesize the Fn type — \
                         `-> (Fn(…) -> … ! { … })` — to attach the row to the type"
                            .to_string(),
                        Some(self.current().span),
                    ));
                }
                None
            } else {
                self.parse_effect_row()
            };
            let end_span = if effects.is_some() {
                self.previous_span()
            } else {
                return_type.span
            };
            let span = fn_start.join(end_span);
            return Some(TypeExpr {
                // Synthetic path for diagnostic rendering only; ignored
                // when fn_type.is_some().
                path: Path {
                    segments: vec!["Fn".to_string()],
                    type_args: Vec::new(),
                    span: fn_start,
                },
                ref_kind: None,
                deadline: Vec::new(),
                span,
                fn_type: Some(Box::new(FnTypeExpr {
                    params,
                    return_type,
                    effects,
                    span,
                })),
                array_type: None,
                tuple_type: None,
            });
        }

        // Tuple type `(A, B, …)`. A no-comma `(T)` is plain grouping (we return
        // the inner type); `(A,)` (1-tuple) and `()` are rejected (AG-4); arity is
        // capped at MAX_TUPLE_ARITY (ET-2). Before this branch, `(` in type
        // position was always a syntax error, so this is a pure addition. (A
        // parametric cap like `Approval(2030)` starts with an `Ident`, not `(`,
        // so it never reaches here — it goes through the path parse below.)
        if self.at_lparen() {
            let start = self.advance().span; // consume (
            let mut elems: Vec<TypeExpr> = Vec::new();
            let mut saw_comma = false;
            while !self.is_eof() && !self.at_rparen() {
                elems.push(self.parse_bounded_type_expr("expected a type inside `( … )`")?);
                if self.at_comma() {
                    saw_comma = true;
                    self.advance();
                } else {
                    break;
                }
            }
            let end = self.expect_rparen("expected `)` to close a tuple or parenthesized type")?;
            let span = start.join(end);
            // No comma + exactly one element → grouping `(T)` ≡ T.
            if !saw_comma && elems.len() == 1 {
                return elems.into_iter().next();
            }
            if elems.len() < 2 {
                self.diagnostics.push(Diagnostic::error(
                    codes::T261,
                    "a tuple type needs at least two elements; `(T,)` and `()` are not tuple types"
                        .to_string(),
                    Some(span),
                ));
                return None;
            }
            if elems.len() > MAX_TUPLE_ARITY {
                self.diagnostics.push(Diagnostic::error(
                    codes::T261,
                    format!(
                        "tuple type has {} elements; the maximum is {MAX_TUPLE_ARITY}",
                        elems.len()
                    ),
                    Some(span),
                ));
                return None;
            }
            return Some(TypeExpr {
                // Synthetic path for diagnostic rendering only; ignored when
                // tuple_type.is_some() (display_name renders the elements).
                path: Path {
                    segments: vec!["(...)".to_string()],
                    type_args: Vec::new(),
                    span: start,
                },
                ref_kind: None,
                deadline: Vec::new(),
                span,
                fn_type: None,
                array_type: None,
                tuple_type: Some(elems),
            });
        }

        // Check for & prefix (reference or slice type)
        if self.at_ampersand() {
            let start = self.advance().span; // consume &
            let mutable = if self.at_mut() {
                self.advance();
                true
            } else {
                false
            };
            // Check for &[T] (slice)
            if self.at_lbracket() {
                self.advance(); // consume [
                let inner = self.parse_bounded_type_expr("expected element type in slice")?;
                let end = self.expect_rbracket("expected `]` after slice element type")?;
                // Phase 4 sweep: PRESERVE the element's full structure. This
                // used to hardcode `fn_type/array_type/tuple_type: None`, so
                // `&[Fn(i64) -> i64 ! { E }]` silently degraded to a slice of
                // the NOMINAL type `Fn` — the element's params, return, and
                // effect row (typos and row variables included) vanished from
                // the AST before any validator could see them. Structured
                // slice elements are still REJECTED (T281 at resolution), but
                // now loudly, from a faithful AST.
                return Some(TypeExpr {
                    path: inner.path,
                    ref_kind: Some(RefKind::Slice),
                    deadline: inner.deadline,
                    span: start.join(end),
                    fn_type: inner.fn_type,
                    array_type: inner.array_type,
                    tuple_type: inner.tuple_type,
                });
            }
            // &T or &mut T
            let inner = self.parse_type_expr("expected type after `&`")?;
            // Phase 4 sweep: PRESERVE the target's full structure — the twin
            // of the slice branch above (same silent dropper, caught by the
            // row-position shape census). `&Fn(..)` is still rejected (T281),
            // but from a faithful AST instead of degrading to a reference to
            // the NOMINAL type `Fn`.
            return Some(TypeExpr {
                path: inner.path,
                ref_kind: Some(RefKind::Ref(mutable)),
                deadline: inner.deadline,
                span: start.join(inner.span),
                fn_type: inner.fn_type,
                array_type: inner.array_type,
                tuple_type: inner.tuple_type,
            });
        }

        // PR P16 / N3-P16: array-type syntax `[T; N]`. Routes via the
        // new `array_type: Option<Box<ArrayTypeExpr>>` field. The
        // grammar is strict: `LBracket TypeExpr Semicolon IntLit
        // RBracket` with the IntLit in `0..=65535`. Any deviation
        // fires T239 at parse time.
        //
        // This branch sits BEFORE `parse_path` because `[` is not a
        // path-start token; the existing parser would syntax-error
        // on it. Pre-PR-P16, `[` at type position was always a syntax
        // error (no fixture exercises it), so this is a pure ADDITION.
        if self.at_lbracket() {
            let lbracket_span = self.advance().span; // consume `[`
            let elem = self.parse_bounded_type_expr("expected element type in array")?;

            // Expect `;` separator.
            if !self.at_semicolon() {
                let tok = self.current().clone();
                self.diagnostics.push(Diagnostic::error(
                    codes::T239,
                    "expected `;` between array element type and size in `[T; N]` (e.g. `[i64; 64]`)",
                    Some(tok.span),
                ));
                return None;
            }
            self.advance(); // consume `;`

            // Expect IntLit (positive, <= 65535).
            let size_tok = self.current().clone();
            let size: u32 = match size_tok.kind {
                TokenKind::IntLit(v) if (0..=65535).contains(&v) => {
                    self.advance();
                    v as u32
                }
                TokenKind::IntLit(v) => {
                    self.diagnostics.push(Diagnostic::error(
                        codes::T239,
                        format!(
                            "array size `{v}` is out of range; `[T; N]` admits only integer literals in 0..=65535 (inclusive). For larger arrays use a heap-allocated growable collection with `! {{ Alloc }}` effect."
                        ),
                        Some(size_tok.span),
                    ));
                    return None;
                }
                _ => {
                    self.diagnostics.push(Diagnostic::error(
                        codes::T239,
                        "expected integer literal as array size in `[T; N]` (e.g. `[i64; 64]`); SIGIL does not admit const-expression sizes or named constants in size position",
                        Some(size_tok.span),
                    ));
                    return None;
                }
            };

            let rbracket = self.expect_rbracket("expected `]` after array size")?;
            let span = lbracket_span.join(rbracket);
            return Some(TypeExpr {
                // Synthetic path for diagnostic rendering only; ignored
                // when array_type.is_some().
                path: Path {
                    segments: vec![format!("[T; {size}]")],
                    type_args: Vec::new(),
                    span,
                },
                ref_kind: None,
                deadline: Vec::new(),
                span,
                fn_type: None,
                array_type: Some(Box::new(ArrayTypeExpr { elem, size, span })),
                tuple_type: None,
            });
        }

        let mut path = self.parse_path(message)?;
        let mut span = path.span;

        // In type context, parse <T, U> eagerly (no :: required)
        if self.at_lt() {
            let start = self.advance().span;
            while !self.is_eof() && !self.at_gt() {
                let arg = self.parse_bounded_type_expr("expected type argument")?;
                span = span.join(arg.span);
                path.type_args.push(arg);

                if self.at_comma() {
                    self.advance();
                } else {
                    break;
                }
            }

            let end = self.expect_gt("expected `>` to close type arguments")?;
            span = span.join(start).join(end);
        }

        // Parametric cap usage (Wall 2 → Wall 3): a `(<v1>, <v2>, ...)`
        // suffix after the type name. Each value is an `i64` literal,
        // comma-separated. Arity vs the declaration is validated in
        // `validate_lowered_type` (T196/T197/T201). Leading, trailing,
        // and double commas fire T198 at parse time.
        let deadline: Vec<i64> = if self.at_lparen() {
            self.advance(); // consume `(`
            // Empty parens at usage are still parser-rejected (T198).
            if self.at_rparen() {
                let end = self.current().span;
                self.diagnostics.push(Diagnostic::error(
                    codes::T198,
                    "parametric capability usage `<Name>(...)` requires at least one `i64` literal; either supply values or drop the parentheses",
                    Some(end),
                ));
                return None;
            }
            // MC-7 fence: leading comma invalid.
            if self.at_comma() {
                let comma_span = self.current().span;
                self.diagnostics.push(Diagnostic::error(
                    codes::T198,
                    "parametric capability value list cannot start with `,`; remove the leading comma",
                    Some(comma_span),
                ));
                return None;
            }
            let mut values = Vec::new();
            loop {
                let tok = self.current().clone();
                let value = match tok.kind {
                    TokenKind::IntLit(v) => {
                        self.cursor += 1;
                        v
                    }
                    _ => {
                        self.diagnostics.push(Diagnostic::error(
                            codes::T198,
                            "expected `i64` literal inside `(...)` after capability type name",
                            Some(tok.span),
                        ));
                        return None;
                    }
                };
                values.push(value);
                span = span.join(tok.span);
                if self.at_comma() {
                    let comma_span = self.current().span;
                    self.advance();
                    // MC-7 fence: trailing comma + double comma invalid.
                    if self.at_rparen() {
                        self.diagnostics.push(Diagnostic::error(
                            codes::T198,
                            "parametric capability value list cannot end with a trailing `,`; remove the trailing comma",
                            Some(comma_span),
                        ));
                        return None;
                    }
                    if self.at_comma() {
                        self.diagnostics.push(Diagnostic::error(
                            codes::T198,
                            "parametric capability value list cannot contain double `,`; each value is separated by a single comma",
                            Some(self.current().span),
                        ));
                        return None;
                    }
                    continue;
                }
                break;
            }
            let end = self.expect_rparen("expected `)` after parametric capability value list")?;
            span = span.join(end);
            values
        } else {
            Vec::new()
        };

        Some(TypeExpr {
            path,
            ref_kind: None,
            deadline,
            span,
            fn_type: None,
            array_type: None,
            tuple_type: None,
        })
    }

    fn parse_path(&mut self, message: &'static str) -> Option<Path> {
        let (segment, start) = self.expect_ident(message)?;
        self.parse_path_from_first(segment, start)
    }

    fn parse_path_from_first(&mut self, segment: String, start: Span) -> Option<Path> {
        // Spelling record: reset per path-parse; set when any `::` separator
        // (segment join or turbofish) is consumed. CONTRACT: consumers must
        // read `self.last_path_colon_spelled` IMMEDIATELY after this call
        // returns (before any nested parse), as the next path-parse resets it.
        self.last_path_colon_spelled = false;
        let mut segments = vec![segment];
        let mut type_args = vec![];
        let mut span = start;

        loop {
            if self.at_colon_colon() {
                self.last_path_colon_spelled = true;
                // Turbofish: :: followed by < means generic args, not a path segment
                if matches!(self.peek().kind, TokenKind::Lt) {
                    self.advance(); // consume ::
                    self.advance(); // consume <
                    while !self.is_eof() && !self.at_gt() {
                        if let Some(arg) = self.parse_bounded_type_expr("expected type argument") {
                            span = span.join(arg.span);
                            type_args.push(arg);
                        }
                        if self.at_comma() {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    if self.at_gt() {
                        span = span.join(self.advance().span);
                    }
                    break;
                }
                self.advance();
                let (segment, part_span) = self.expect_ident("expected path segment")?;
                segments.push(segment);
                span = span.join(part_span);
            } else if self.at_dot() {
                self.advance();
                let (segment, part_span) =
                    self.expect_path_member_segment("expected path segment")?;
                segments.push(segment);
                span = span.join(part_span);
            } else {
                break;
            }
        }

        Some(Path {
            segments,
            type_args,
            span,
        })
    }

    fn parse_literal(&mut self) -> Option<Literal> {
        let token = self.current().clone();
        match token.kind {
            TokenKind::BoolLit(value) => {
                self.cursor += 1;
                Some(Literal::Bool(value))
            }
            TokenKind::IntLit(value) => {
                self.cursor += 1;
                Some(Literal::Int(value))
            }
            // u256 PR-U2: a wide integer literal (> i64::MAX, <= 2^256-1).
            TokenKind::IntLit256(limbs) => {
                self.cursor += 1;
                Some(Literal::Int256(limbs))
            }
            TokenKind::FloatLit(value) => {
                self.cursor += 1;
                Some(Literal::Float(value))
            }
            TokenKind::StrLit(value) => {
                self.cursor += 1;
                Some(Literal::Str(value))
            }
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::P014,
                    "expected literal value",
                    Some(token.span),
                ));
                None
            }
        }
    }

    fn parse_body(&mut self, message: &'static str) -> Option<Block> {
        if self.at_semicolon() {
            let span = self.advance().span;
            return Some(Block {
                statements: Vec::new(),
                span,
            });
        }

        self.parse_braced_block(message)
    }

    fn parse_statement(&mut self) -> Option<Stmt> {
        if self.at_let() {
            // `let (` / `let mut (` → tuple destructuring; otherwise a normal
            // single-name `let`.
            if self.is_let_tuple() {
                return self.parse_let_tuple_statement().map(Stmt::LetTuple);
            }
            return self.parse_let_statement().map(Stmt::Let);
        }

        if self.at_if() {
            // PR-E2: `if let PATTERN = E { … }` desugars to a `match` (Stmt::Match);
            // a plain `if` keeps its IfStmt shape.
            if matches!(self.peek().kind, TokenKind::Let) {
                return self.parse_if_let_statement();
            }
            return self.parse_if_statement().map(Stmt::If);
        }

        if self.at_match() {
            return self.parse_match_statement().map(Stmt::Match);
        }

        if self.at_while() {
            // PR-E2: `while let PATTERN = E { … }` desugars to
            // `while true { match … }` (Stmt::While); a plain `while` is unchanged.
            if matches!(self.peek().kind, TokenKind::Let) {
                return self.parse_while_let_statement();
            }
            return self.parse_while_statement().map(Stmt::While);
        }

        if self.at_for() {
            return self.parse_for_in_statement();
        }

        if self.at_return() {
            return self.parse_return_statement().map(Stmt::Return);
        }

        if matches!(self.current().kind, TokenKind::Break) {
            let start = self.advance().span;
            let end = self.expect_semicolon("expected `;` after `break`")?;
            return Some(Stmt::Break(start.join(end)));
        }

        if matches!(self.current().kind, TokenKind::Continue) {
            let start = self.advance().span;
            let end = self.expect_semicolon("expected `;` after `continue`")?;
            return Some(Stmt::Continue(start.join(end)));
        }

        // Expression statement OR assignment. Parse the leading expression,
        // then decide: a trailing `=` / `op=` makes it an assignment whose LHS
        // is that (place) expression; otherwise it is an expression statement.
        if self.at_expr_start() {
            let start = self.current().span;
            let lhs = self.parse_expr()?;
            let op = if matches!(self.current().kind, TokenKind::Eq) {
                self.advance();
                None
            } else if let Some(binop) = compound_assign_op(&self.current().kind) {
                self.advance();
                Some(binop)
            } else {
                let end = self.expect_semicolon("expected `;` after expression statement")?;
                return Some(Stmt::Expr(ExprStmt {
                    span: start.join(end),
                    expr: lhs,
                }));
            };
            let value = self.parse_expr()?;
            let end = self.expect_semicolon("expected `;` after assignment")?;
            // Local compound `x op= rhs` desugars to `x = x op rhs` (byte-
            // identical with today, NC5). A FIELD/INDEX compound keeps `op`
            // and is lowered as load-op-store at AIR (NC2 — no place clone, so
            // the subscript is not double-evaluated).
            let is_local = matches!(&lhs, Expr::Path(p) if p.path.segments.len() == 1);
            let (op_final, value_final) = match (op, is_local) {
                (Some(binop), true) => {
                    let desugared = Expr::Binary(BinaryExpr {
                        lhs: Box::new(lhs.clone()),
                        op: binop,
                        rhs: Box::new(value),
                        span: start.join(end),
                    });
                    (None, desugared)
                }
                (other, _) => (other, value),
            };
            return Some(Stmt::Assign(AssignStmt {
                target: lhs,
                op: op_final,
                value: value_final,
                span: start.join(end),
            }));
        }

        self.diagnostics.push(Diagnostic::error(
            codes::P015,
            "expected statement (`let`, assignment, expression, `if`, `match`, `while`, or `return`)",
            Some(self.current().span),
        ));
        None
    }

    fn parse_let_statement(&mut self) -> Option<LetStmt> {
        let start = self.advance().span;
        let mutable = if self.at_mut() {
            self.advance();
            true
        } else {
            false
        };

        let (name, name_span) = self.expect_ident("expected local name after `let`")?;
        let ty = if self.at_colon() {
            self.advance();
            Some(self.parse_type_expr("expected type after `:`")?)
        } else {
            None
        };
        let taint = self.parse_taint_annotation();
        self.expect_eq("expected `=` in let statement")?;
        let value = self.parse_expr()?;
        let end = self.expect_semicolon("expected `;` after let statement")?;

        Some(LetStmt {
            name,
            mutable,
            ty,
            taint,
            value,
            span: start.join(name_span).join(end),
        })
    }

    /// `let (` opens a tuple destructuring rather than a normal single-name
    /// `let`. The `(` immediately after `let` is the discriminator (`let (` was
    /// always a syntax error before, so this is a pure addition). Per-binding
    /// `mut` lives INSIDE the parens (`let (mut a, b) = …`), so `let mut …`
    /// stays the normal single-name path.
    fn is_let_tuple(&self) -> bool {
        matches!(self.nth_kind(1), Some(TokenKind::LParen))
    }

    /// Parse `let (a, mut b, …) [: (A, B, …)] = value;` — a tuple destructuring
    /// with per-binding `mut`. Type-check desugars it into a hidden temp +
    /// per-element field loads (ET-3: the value is bound once). Bindings are
    /// flat — nested patterns are an Anti-Goal (AG-2). Arity is
    /// `2..=MAX_TUPLE_ARITY` (T261 otherwise).
    fn parse_let_tuple_statement(&mut self) -> Option<LetTupleStmt> {
        let start = self.advance().span; // consume `let`
        let lparen = self.advance().span; // consume `(` (guaranteed by is_let_tuple)
        let mut bindings: Vec<(String, bool)> = Vec::new();
        while !self.is_eof() && !self.at_rparen() {
            let is_mut = if self.at_mut() {
                self.advance();
                true
            } else {
                false
            };
            let (name, _name_span) =
                self.expect_ident("expected a binding name in `let (a, b) = …`")?;
            bindings.push((name, is_mut));
            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }
        let rparen = self.expect_rparen("expected `)` after tuple binding names")?;
        let pat_span = lparen.join(rparen);
        if bindings.len() < 2 {
            self.diagnostics.push(Diagnostic::error(
                codes::T261,
                "a tuple destructuring binds at least two names, e.g. `let (a, b) = …`; for a single binding use `let x = …`"
                    .to_string(),
                Some(pat_span),
            ));
            return None;
        }
        if bindings.len() > MAX_TUPLE_ARITY {
            self.diagnostics.push(Diagnostic::error(
                codes::T261,
                format!(
                    "tuple destructuring binds {} names; the maximum is {MAX_TUPLE_ARITY}",
                    bindings.len()
                ),
                Some(pat_span),
            ));
            return None;
        }
        let ty = if self.at_colon() {
            self.advance();
            Some(self.parse_type_expr("expected type after `:`")?)
        } else {
            None
        };
        self.expect_eq("expected `=` in tuple `let` statement")?;
        let value = self.parse_expr()?;
        let end = self.expect_semicolon("expected `;` after let statement")?;
        Some(LetTupleStmt {
            bindings,
            ty,
            value,
            span: start.join(end),
        })
    }

    fn parse_return_statement(&mut self) -> Option<ReturnStmt> {
        let start = self.advance().span;
        let value = if self.at_semicolon() {
            None
        } else {
            Some(self.parse_expr()?)
        };
        let end = self.expect_semicolon("expected `;` after return statement")?;

        Some(ReturnStmt {
            value,
            span: start.join(end),
        })
    }

    fn parse_if_statement(&mut self) -> Option<IfStmt> {
        let start = self.advance().span;
        let condition = self.parse_expr()?;
        let then_branch = self.parse_braced_block("expected `{` after `if` condition")?;

        // PR-E1: `else` is OPTIONAL. When absent, synthesize an EMPTY `else` block (a
        // zero-width span at the end of the then-branch) so `IfStmt.else_branch` stays a
        // (possibly empty) `Block` — no AST churn (AG-E5). An empty else is correctly
        // non-returning for the T050 both-branches-return check and emits no instructions
        // in AIR/wasm; the parser-differential flattener still sees three children.
        let else_branch = if self.at_else() {
            self.advance();
            if self.at_if() {
                // `else if C { … }` desugars to `else { if C { … } }`. No new
                // AST node (AG-E5) and the three-child shape the
                // parser-differential flattener expects is preserved; the
                // nested `if` keeps its own real span, so every node still
                // lands at a source offset.
                //
                // Depth-guarded exactly like `parse_braced_block`, because
                // this recursion does NOT pass through a block: an unguarded
                // `else if` chain would recurse once per link and overflow the
                // native stack. That is the same O(N)-recursion parser DoS
                // already closed for if/while/match, and `else if` is the most
                // natural way to write a long chain — so it gets the guard
                // rather than inheriting the hole.
                if !self.enter_nesting() {
                    return None;
                }
                let nested = self.parse_if_statement();
                self.exit_nesting();
                let nested = nested?;
                let span = nested.span;
                Block {
                    statements: vec![Stmt::If(nested)],
                    span,
                }
            } else {
                self.parse_braced_block("expected `{` after `else`")?
            }
        } else {
            Block {
                statements: Vec::new(),
                span: Span::with_source(
                    then_branch.span.end,
                    then_branch.span.end,
                    then_branch.span.source,
                ),
            }
        };
        let span = start.join(else_branch.span);

        Some(IfStmt {
            condition,
            then_branch,
            else_branch,
            span,
        })
    }

    fn parse_while_statement(&mut self) -> Option<WhileStmt> {
        let start = self.advance().span;
        let condition = self.parse_expr()?;
        let body = self.parse_braced_block("expected `{` after `while` condition")?;

        Some(WhileStmt {
            condition,
            span: start.join(body.span),
            body,
        })
    }

    /// PR-E2: `if let PATTERN = E { T } else { F }` desugars to
    /// `match E { PATTERN => { T }, _ => { F } }` — a `Stmt::Match`, reusing the
    /// existing pattern + match machinery (no new AST node, AG-E5). `else` is
    /// OPTIONAL (the missing arm becomes an empty `F` block, per PR-E1). The
    /// synthetic wildcard pattern is a zero-width span at the start of the (real
    /// or synthesized) else block, so the Rust and self-hosted desugars place
    /// every node at identical offsets — node-for-node parser-differential parity.
    fn parse_if_let_statement(&mut self) -> Option<Stmt> {
        let start = self.advance().span; // `if`
        self.advance(); // `let`
        let pattern = self.parse_pattern()?;
        let pat_span = pattern.span();
        self.expect_eq("expected `=` in `if let`")?;
        let scrutinee = self.parse_expr()?;
        let then_branch = self.parse_braced_block("expected `{` after `if let` pattern")?;
        let then_span = then_branch.span;
        let else_branch = if self.at_else() {
            self.advance();
            self.parse_braced_block("expected `{` after `else`")?
        } else {
            Block {
                statements: Vec::new(),
                span: Span::with_source(then_span.end, then_span.end, then_span.source),
            }
        };
        let else_span = else_branch.span;
        let wild_span = Span::with_source(else_span.start, else_span.start, else_span.source);
        let arms = vec![
            MatchArm {
                span: pat_span.join(then_span),
                pattern,
                guard: None,
                body: then_branch,
            },
            MatchArm {
                span: wild_span.join(else_span),
                pattern: Pattern::Wildcard(wild_span),
                guard: None,
                body: else_branch,
            },
        ];
        Some(Stmt::Match(MatchStmt {
            scrutinee,
            arms,
            span: start.join(else_span),
        }))
    }

    /// PR-E2: `while let PATTERN = E { B }` desugars to
    /// `while true { match E { PATTERN => { B }, _ => { break; } } }` — a
    /// `Stmt::While` whose body is a single `match`. The loop re-evaluates `E`
    /// each iteration; the `_` arm `break`s when the pattern stops matching (the
    /// standard while-let lowering). The synthetic `true` condition is zero-width
    /// at the `while` keyword; the wildcard / `break` / break-block are zero-width
    /// at the end of `B`; so the self-hosted desugar matches node-for-node.
    fn parse_while_let_statement(&mut self) -> Option<Stmt> {
        let start = self.advance().span; // `while`
        self.advance(); // `let`
        let pattern = self.parse_pattern()?;
        let pat_span = pattern.span();
        self.expect_eq("expected `=` in `while let`")?;
        let scrutinee = self.parse_expr()?;
        let body = self.parse_braced_block("expected `{` after `while let` pattern")?;
        let body_span = body.span;
        let cond_span = Span::with_source(start.start, start.start, start.source);
        let end_span = Span::with_source(body_span.end, body_span.end, body_span.source);
        let break_block = Block {
            statements: vec![Stmt::Break(end_span)],
            span: end_span,
        };
        // The synthetic match/inner-block span starts at the PATTERN (which in
        // `while let P = E` precedes the scrutinee), so arm1 (pattern..body) nests
        // within the match — ET-P6 span-containment holds.
        let match_span = Span::with_source(pat_span.start, body_span.end, body_span.source);
        let arms = vec![
            MatchArm {
                span: pat_span.join(body_span),
                pattern,
                guard: None,
                body,
            },
            MatchArm {
                span: end_span,
                pattern: Pattern::Wildcard(end_span),
                guard: None,
                body: break_block,
            },
        ];
        let inner = Block {
            statements: vec![Stmt::Match(MatchStmt {
                scrutinee,
                arms,
                span: match_span,
            })],
            span: match_span,
        };
        let condition = Expr::Literal(LiteralExpr {
            literal: Literal::Bool(true),
            span: cond_span,
        });
        Some(Stmt::While(WhileStmt {
            condition,
            span: start.join(body_span),
            body: inner,
        }))
    }

    /// `for v in <expr> { … }` (element/iterator loop) or
    /// `for v in <expr>..<expr> { … }` (the exclusive range loop). The range form
    /// is recognized HERE, in for-header position only — `..` is not an expression
    /// operator anywhere else (parse_expr's postfix loop stops at `DotDot`, which is
    /// what makes `a..b` cleanly split into two expressions). `..=` rejects (P029):
    /// one canonical loop shape, no off-by-one variant for the bounds machinery or
    /// the SH-AIR shadow to mis-derive.
    fn parse_for_in_statement(&mut self) -> Option<Stmt> {
        let start = self.advance().span; // consume 'for'
        let (var, _) = self.expect_ident("expected loop variable after `for`")?;

        if !matches!(self.current().kind, TokenKind::In) {
            self.diagnostics.push(Diagnostic::error(
                codes::P017,
                "expected `in` after loop variable",
                Some(self.current().span),
            ));
            return None;
        }
        self.advance(); // consume 'in'

        let iterable = self.parse_expr()?;

        if matches!(self.current().kind, TokenKind::DotDotEq) {
            self.diagnostics.push(Diagnostic::error(
                codes::P029,
                "inclusive range `..=` is not supported in a `for` header — use an exclusive end (`for v in a..b`)",
                Some(self.current().span),
            ));
            // Faithful recovery (the P026 discipline): consume the REST of the
            // range-for shape (`..= end { body }`) so the statement is swallowed
            // whole and no cascade diagnostics fire on its residue — the P029
            // fixture must emit EXACTLY {P029} (diagnostic_precision).
            self.advance(); // consume '..='
            let _end = self.parse_expr();
            let _body = self.parse_braced_block("expected `{` after `for ... in` range");
            return None;
        }

        if self.at_dot_dot() {
            self.advance(); // consume '..'
            let end = self.parse_expr()?;
            let body =
                self.parse_braced_block("expected `{` after `for ... in start..end` range")?;
            return Some(Stmt::ForRange(ForRangeStmt {
                var,
                start: iterable,
                end,
                span: start.join(body.span),
                body,
            }));
        }

        let body = self.parse_braced_block("expected `{` after `for ... in` expression")?;

        Some(Stmt::ForIn(ForInStmt {
            var,
            iterable,
            span: start.join(body.span),
            body,
        }))
    }

    fn parse_match_statement(&mut self) -> Option<MatchStmt> {
        let start = self.advance().span;
        let scrutinee = self.parse_expr()?;
        self.expect_lbrace("expected `{` after `match` scrutinee")?;

        let mut arms = Vec::new();
        let mut end = self.previous_span();

        while !self.is_eof() && !self.at_rbrace() {
            let pattern = self.parse_pattern()?;

            // Optional guard: `if expr`
            let guard = if self.at_if() {
                self.advance(); // consume `if`
                Some(self.parse_expr()?)
            } else {
                None
            };

            self.expect_fat_arrow("expected `=>` after match pattern")?;
            let body = self.parse_braced_block("expected `{` to start match arm body")?;
            let arm_span = pattern.span().join(body.span);
            end = arm_span;
            arms.push(MatchArm {
                pattern,
                guard,
                body,
                span: arm_span,
            });

            if self.at_comma() || self.at_semicolon() {
                self.advance();
            } else if !self.at_rbrace() {
                self.diagnostics.push(Diagnostic::error(
                    codes::P018,
                    "expected `,`, `;`, or `}` after match arm",
                    Some(self.current().span),
                ));
                self.synchronize_block_statement();
            }
        }

        let close = self.expect_rbrace("expected `}` to close match statement")?;

        Some(MatchStmt {
            scrutinee,
            arms,
            span: start.join(end).join(close),
        })
    }

    fn parse_pattern(&mut self) -> Option<Pattern> {
        let token = self.current().clone();
        // Negative integer literal as a pattern: `-5` and `-5..=5` etc.
        // Recognized at parse_pattern (not parse_literal) because the
        // unary-minus desugar in parse_prefix_expr produces a Binary
        // expression, which isn't a valid pattern shape.
        let is_neg_int = matches!(token.kind, TokenKind::Minus)
            && matches!(self.peek().kind, TokenKind::IntLit(_));
        match &token.kind {
            TokenKind::BoolLit(_) | TokenKind::IntLit(_) | TokenKind::StrLit(_) => {
                let lo_literal = self.parse_literal()?;
                let lo_span = token.span;

                if matches!(self.current().kind, TokenKind::DotDotEq) {
                    self.advance(); // consume ..=
                    let (hi_literal, hi_span) = self.parse_pattern_literal()?;
                    return Some(Pattern::Range(RangePattern {
                        lo: lo_literal,
                        hi: hi_literal,
                        span: lo_span.join(hi_span),
                    }));
                }

                Some(Pattern::Literal(LiteralPattern {
                    literal: lo_literal,
                    span: lo_span,
                }))
            }
            _ if is_neg_int => {
                let (lo_literal, lo_span) = self.parse_pattern_literal()?;

                if matches!(self.current().kind, TokenKind::DotDotEq) {
                    self.advance(); // consume ..=
                    let (hi_literal, hi_span) = self.parse_pattern_literal()?;
                    return Some(Pattern::Range(RangePattern {
                        lo: lo_literal,
                        hi: hi_literal,
                        span: lo_span.join(hi_span),
                    }));
                }

                Some(Pattern::Literal(LiteralPattern {
                    literal: lo_literal,
                    span: lo_span,
                }))
            }
            TokenKind::Ident(name) if name == "_" => {
                self.cursor += 1;
                Some(Pattern::Wildcard(token.span))
            }
            TokenKind::Ident(name) => {
                let name = name.clone();
                let start = self.advance().span;

                // Check for :: (enum variant pattern: TypeName::Variant or Variant(bindings))
                if self.at_colon_colon() {
                    self.advance(); // consume ::
                    let (variant, variant_span) =
                        self.expect_ident("expected variant name after `::`")?;
                    let span = start.join(variant_span);

                    // Optional payload bindings: Variant(x, y)
                    let mut bindings = Vec::new();
                    if self.at_lparen() {
                        self.advance(); // consume (
                        while !self.is_eof() && !self.at_rparen() {
                            let (binding, _) =
                                self.expect_ident("expected binding name in pattern")?;
                            bindings.push(binding);
                            if self.at_comma() {
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        let end =
                            self.expect_rparen("expected `)` after variant pattern bindings")?;
                        return Some(Pattern::EnumVariant(EnumVariantPattern {
                            type_name: name,
                            variant,
                            bindings,
                            span: start.join(end),
                        }));
                    }

                    Some(Pattern::EnumVariant(EnumVariantPattern {
                        type_name: name,
                        variant,
                        bindings,
                        span,
                    }))
                } else if self.at_lparen() {
                    // Bare variant with payload: Some(x) — type_name is inferred
                    self.advance(); // consume (
                    let mut bindings = Vec::new();
                    while !self.is_eof() && !self.at_rparen() {
                        let binding_token = self.current().clone();
                        if matches!(binding_token.kind, TokenKind::Ident(ref n) if n == "_") {
                            bindings.push("_".to_owned());
                            self.advance();
                        } else {
                            let (binding, _) =
                                self.expect_ident("expected binding name in pattern")?;
                            bindings.push(binding);
                        }
                        if self.at_comma() {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    let end = self.expect_rparen("expected `)` after variant pattern bindings")?;
                    Some(Pattern::EnumVariant(EnumVariantPattern {
                        type_name: String::new(), // inferred from scrutinee type
                        variant: name,
                        bindings,
                        span: start.join(end),
                    }))
                } else {
                    // Plain binding pattern: x
                    Some(Pattern::Binding(BindingPattern { name, span: start }))
                }
            }
            // Array/slice destructuring pattern: `[]`, `[a]`, `[a, b, ..rest]`.
            // Phase 5. Elements are bindings or `_` (AG-P5-1); the optional
            // `..rest`/`..` is the LAST element (AG-P5-2), at most one.
            TokenKind::LBracket => {
                let start = self.advance().span; // consume '['
                let mut elements: Vec<ArrayElem> = Vec::new();
                let mut rest: Option<RestBind> = None;
                while !self.is_eof() && !self.at_rbracket() {
                    if self.at_dot_dot() {
                        let rest_span = self.advance().span; // consume '..'
                        // Optional binding name: `..rest`; `..` / `.._` are anonymous.
                        let name = match &self.current().kind {
                            TokenKind::Ident(n) if n == "_" => {
                                self.advance();
                                None
                            }
                            TokenKind::Ident(n) => {
                                let n = n.clone();
                                self.advance();
                                Some(n)
                            }
                            _ => None,
                        };
                        if rest.is_some() {
                            self.diagnostics.push(Diagnostic::error(
                                codes::P019,
                                "array pattern may contain at most one `..` rest element",
                                Some(rest_span),
                            ));
                            return None;
                        }
                        rest = Some(RestBind {
                            name,
                            span: rest_span,
                        });
                    } else {
                        // A fixed element. Suffix elements after `..rest` are
                        // unsupported (AG-P5-2): a fixed element with `rest` set
                        // is a rest-not-last error.
                        if rest.is_some() {
                            self.diagnostics.push(Diagnostic::error(
                                codes::P019,
                                "`..` rest must be the last element of an array pattern",
                                Some(self.current().span),
                            ));
                            return None;
                        }
                        let el_tok = self.current().clone();
                        match &el_tok.kind {
                            TokenKind::Ident(n) if n == "_" => {
                                self.advance();
                                elements.push(ArrayElem::Wild(el_tok.span));
                            }
                            TokenKind::Ident(n) => {
                                let n = n.clone();
                                self.advance();
                                elements.push(ArrayElem::Bind(n, el_tok.span));
                            }
                            _ => {
                                self.diagnostics.push(Diagnostic::error(
                                    codes::P019,
                                    "array pattern elements must be bindings or `_` (nested patterns are not supported)",
                                    Some(el_tok.span),
                                ));
                                return None;
                            }
                        }
                    }
                    if self.at_comma() {
                        self.advance();
                    } else {
                        break;
                    }
                }
                let end = self.expect_rbracket("expected `]` to close array pattern")?;
                Some(Pattern::Array(ArrayPattern {
                    elements,
                    rest,
                    span: start.join(end),
                }))
            }
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::P019,
                    "expected pattern (literal, `_`, binding, or enum variant)",
                    Some(token.span),
                ));
                None
            }
        }
    }

    // Shared helper used by `parse_pattern` for both the standalone-literal
    // and range-bounds cases. Accepts a positive IntLit / BoolLit / StrLit,
    // or `-IntLit` (negative integer literal — needed for ranges like
    // `-5..=5` and standalone negative-int patterns).
    fn parse_pattern_literal(&mut self) -> Option<(Literal, Span)> {
        let token = self.current().clone();
        if matches!(token.kind, TokenKind::Minus)
            && matches!(self.peek().kind, TokenKind::IntLit(_))
        {
            let minus_span = self.advance().span;
            let int_token = self.current().clone();
            let TokenKind::IntLit(n) = int_token.kind else {
                return None;
            };
            self.advance();
            return Some((Literal::Int(-n), minus_span.join(int_token.span)));
        }
        match token.kind {
            TokenKind::BoolLit(_) | TokenKind::IntLit(_) | TokenKind::StrLit(_) => {
                let literal = self.parse_literal()?;
                Some((literal, token.span))
            }
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::P019,
                    "expected literal pattern",
                    Some(token.span),
                ));
                None
            }
        }
    }

    fn parse_expr(&mut self) -> Option<Expr> {
        self.parse_logical_or_expr()
    }

    fn parse_logical_or_expr(&mut self) -> Option<Expr> {
        let mut expr = self.parse_logical_and_expr()?;
        while self.at_or_or() {
            self.advance();
            let rhs = self.parse_logical_and_expr()?;
            let span = expr.span().join(rhs.span());
            expr = Expr::Binary(BinaryExpr {
                lhs: Box::new(expr),
                op: BinaryOp::LogicalOr,
                rhs: Box::new(rhs),
                span,
            });
        }
        Some(expr)
    }

    fn parse_logical_and_expr(&mut self) -> Option<Expr> {
        let mut expr = self.parse_equality_expr()?;
        while self.at_and_and() {
            self.advance();
            let rhs = self.parse_equality_expr()?;
            let span = expr.span().join(rhs.span());
            expr = Expr::Binary(BinaryExpr {
                lhs: Box::new(expr),
                op: BinaryOp::LogicalAnd,
                rhs: Box::new(rhs),
                span,
            });
        }
        Some(expr)
    }

    fn parse_equality_expr(&mut self) -> Option<Expr> {
        let mut expr = self.parse_comparison_expr()?;

        while self.at_eq_eq() || self.at_bang_eq() {
            let op = if self.at_eq_eq() {
                self.advance();
                BinaryOp::Eq
            } else {
                self.advance();
                BinaryOp::NotEq
            };
            let rhs = self.parse_comparison_expr()?;
            let span = expr.span().join(rhs.span());
            expr = Expr::Binary(BinaryExpr {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
                span,
            });
        }

        Some(expr)
    }

    fn parse_comparison_expr(&mut self) -> Option<Expr> {
        let mut expr = self.parse_bit_or_expr()?;

        while self.at_lt() || self.at_lt_eq() || self.at_gt() || self.at_gt_eq() {
            let op = if self.at_lt() {
                self.advance();
                BinaryOp::Lt
            } else if self.at_lt_eq() {
                self.advance();
                BinaryOp::LtEq
            } else if self.at_gt() {
                self.advance();
                BinaryOp::Gt
            } else {
                self.advance();
                BinaryOp::GtEq
            };
            let rhs = self.parse_bit_or_expr()?;
            let span = expr.span().join(rhs.span());
            expr = Expr::Binary(BinaryExpr {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
                span,
            });
        }

        Some(expr)
    }

    // Bit-or sits between comparison and bit-and, mirroring Rust/C
    // precedence. Sigil has no logical operators, so the bitwise
    // hierarchy lives in this band: `a | b & c << d + e * f`.
    fn parse_bit_or_expr(&mut self) -> Option<Expr> {
        let mut expr = self.parse_bit_and_expr()?;

        while self.at_pipe() {
            self.advance();
            let rhs = self.parse_bit_and_expr()?;
            let span = expr.span().join(rhs.span());
            expr = Expr::Binary(BinaryExpr {
                lhs: Box::new(expr),
                op: BinaryOp::BitOr,
                rhs: Box::new(rhs),
                span,
            });
        }

        Some(expr)
    }

    // Bit-and. The `&` token is shared with the borrow prefix; the
    // disambiguation is positional — `parse_prefix_expr` only consumes
    // `&` at the START of an expression, so infix `&` after a parsed
    // operand always reaches this loop.
    fn parse_bit_and_expr(&mut self) -> Option<Expr> {
        let mut expr = self.parse_shift_expr()?;

        while self.at_ampersand() {
            self.advance();
            let rhs = self.parse_shift_expr()?;
            let span = expr.span().join(rhs.span());
            expr = Expr::Binary(BinaryExpr {
                lhs: Box::new(expr),
                op: BinaryOp::BitAnd,
                rhs: Box::new(rhs),
                span,
            });
        }

        Some(expr)
    }

    fn parse_shift_expr(&mut self) -> Option<Expr> {
        let mut expr = self.parse_additive_expr()?;

        while self.at_lt_lt() || self.at_gt_gt() {
            let op = if self.at_lt_lt() {
                self.advance();
                BinaryOp::Shl
            } else {
                self.advance();
                BinaryOp::Shr
            };
            let rhs = self.parse_additive_expr()?;
            let span = expr.span().join(rhs.span());
            expr = Expr::Binary(BinaryExpr {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
                span,
            });
        }

        Some(expr)
    }

    fn parse_additive_expr(&mut self) -> Option<Expr> {
        let mut expr = self.parse_multiplicative_expr()?;

        while self.at_plus() || self.at_minus() {
            let op = if self.at_plus() {
                self.advance();
                BinaryOp::Add
            } else {
                self.advance();
                BinaryOp::Sub
            };
            let rhs = self.parse_multiplicative_expr()?;
            let span = expr.span().join(rhs.span());
            expr = Expr::Binary(BinaryExpr {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
                span,
            });
        }

        Some(expr)
    }

    fn parse_multiplicative_expr(&mut self) -> Option<Expr> {
        let mut expr = self.parse_prefix_expr()?;

        while self.at_star() || self.at_slash() || self.at_percent() {
            let op = if self.at_star() {
                self.advance();
                BinaryOp::Mul
            } else if self.at_slash() {
                self.advance();
                BinaryOp::Div
            } else {
                self.advance();
                BinaryOp::Mod
            };
            let rhs = self.parse_prefix_expr()?;
            let span = expr.span().join(rhs.span());
            expr = Expr::Binary(BinaryExpr {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
                span,
            });
        }

        Some(expr)
    }

    /// Enter one level of recursive descent — an expression, a statement block,
    /// or a type expression — and bound the total nesting depth. Returns `false`
    /// when `MAX_EXPR_DEPTH` is exceeded so the caller bails instead of
    /// overflowing the stack and aborting the process (finding P1). Every `true`
    /// result MUST be paired with a later `exit_nesting`.
    ///
    /// On the FIRST time the cap is crossed it emits a single S007 and then
    /// fast-forwards the cursor to EOF. That abort is deliberate and
    /// load-bearing: statement recovery (`synchronize_block_statement`) breaks
    /// on a nesting-start token WITHOUT consuming it, so simply returning `None`
    /// from a block/type guard would let the outer loop re-descend into the same
    /// over-deep input forever. Jumping to EOF makes every `while !is_eof()`
    /// loop terminate, so the parse unwinds cleanly with one diagnostic.
    fn enter_nesting(&mut self) -> bool {
        self.expr_depth += 1;
        if self.expr_depth > MAX_EXPR_DEPTH {
            if !self.depth_exceeded {
                self.depth_exceeded = true;
                let span = self.current().span;
                self.diagnostics.push(Diagnostic::error(
                    codes::S007,
                    format!(
                        "nesting too deep (an expression, block, or type exceeds \
                         MAX_EXPR_DEPTH = {MAX_EXPR_DEPTH}); refactor deeply nested \
                         constructs into intermediate `let` bindings"
                    ),
                    Some(span),
                ));
                // Abort the parse: skip to the EOF token so recovery loops
                // terminate rather than re-descend into the pathological input.
                self.cursor = self.tokens.len().saturating_sub(1);
            }
            self.expr_depth -= 1;
            return false;
        }
        true
    }

    fn exit_nesting(&mut self) {
        self.expr_depth = self.expr_depth.saturating_sub(1);
    }

    /// Depth-guarding wrapper around `parse_prefix_expr_inner`. Every expression
    /// parse — grouping, unary/borrow prefix chains, binary RHS, call/array/
    /// block sub-expressions — descends through here (see `enter_nesting`).
    fn parse_prefix_expr(&mut self) -> Option<Expr> {
        if !self.enter_nesting() {
            return None;
        }
        let result = self.parse_prefix_expr_inner();
        self.exit_nesting();
        result
    }

    fn parse_prefix_expr_inner(&mut self) -> Option<Expr> {
        if self.at_ampersand() {
            let start = self.advance().span; // consume &
            let mutable = if self.at_mut() {
                self.advance();
                true
            } else {
                false
            };
            let inner = self.parse_prefix_expr()?;
            let span = start.join(inner.span());
            return Some(Expr::Borrow(BorrowExpr {
                inner: Box::new(inner),
                mutable,
                span,
            }));
        }
        if self.at_minus() {
            // Unary minus. For integer literals, parse-time-fold to
            // `Literal::Int(-n)` so PIL's `infer_literal_type` sees the
            // signed value directly and produces `Type::IntLit(-n)`
            // with sign reflected (N15-PIL). Without the fold, PIL
            // would unify `IntLit(0) - IntLit(n)` against the target
            // and silently accept (the resulting wasm underflows).
            //
            // For non-literal operands, fall back to the `0 - inner`
            // desugar — the existing semantics. `--x` becomes
            // `0 - (0 - x)` via recursion through `parse_prefix_expr`.
            let start = self.advance().span; // consume -
            let inner = self.parse_prefix_expr()?;
            let span = start.join(inner.span());
            if let Expr::Literal(LiteralExpr {
                literal: Literal::Int(n),
                span: lit_span,
            }) = &inner
            {
                return Some(Expr::Literal(LiteralExpr {
                    literal: Literal::Int(-*n),
                    span: start.join(*lit_span),
                }));
            }
            return Some(Expr::Binary(BinaryExpr {
                lhs: Box::new(Expr::Literal(LiteralExpr {
                    literal: Literal::Int(0),
                    span: start,
                })),
                op: BinaryOp::Sub,
                rhs: Box::new(inner),
                span,
            }));
        }
        if self.at_bang() {
            // Unary `!` (boolean NOT) desugars to `inner == false` at parse
            // time. No new AST node — the existing equality check enforces
            // the operand is bool (T055 fires on non-bool with a clear
            // "operator `==` requires comparable operands" message).
            // Double negation `!!x` parses as `(x == false) == false`,
            // which evaluates back to the original boolean.
            let start = self.advance().span; // consume !
            let inner = self.parse_prefix_expr()?;
            let span = start.join(inner.span());
            return Some(Expr::Binary(BinaryExpr {
                lhs: Box::new(inner),
                op: BinaryOp::Eq,
                rhs: Box::new(Expr::Literal(LiteralExpr {
                    literal: Literal::Bool(false),
                    span: start,
                })),
                span,
            }));
        }
        self.parse_postfix_expr()
    }

    fn parse_postfix_expr(&mut self) -> Option<Expr> {
        let mut expr = self.parse_primary_expr()?;

        loop {
            if self.at_question() {
                let end = self.advance().span;
                let span = expr.span().join(end);
                expr = Expr::Try(TryExpr {
                    value: Box::new(expr),
                    span,
                });
            } else if self.at_lbracket() {
                // PR AF: `[expr]` is `Expr::Index`; `[lo..hi]` and its
                // open-range relatives (`[..hi]`, `[lo..]`, `[..]`)
                // are `Expr::Slice`. Disambiguate by peeking after
                // the `[` for an immediate `..`, or after the first
                // expression for a `..`. Type-check (commit #4)
                // enforces N18-AF: the slice form is only admitted
                // when the immediate syntactic parent is `Expr::Borrow`.
                let start = expr.span();
                self.advance(); // consume '['
                if self.at_dot_dot() {
                    // `[..hi]` or `[..]` — open start
                    self.advance(); // consume '..'
                    let end_expr = if self.at_rbracket() {
                        None
                    } else {
                        Some(Box::new(self.parse_expr()?))
                    };
                    let end = self.expect_rbracket("expected `]` to close slice operator")?;
                    expr = Expr::Slice(SliceExpr {
                        array: Box::new(expr),
                        start: None,
                        end: end_expr,
                        span: start.join(end),
                    });
                } else {
                    // Parse the first expression; it's either the
                    // single index, the slice's start, or the
                    // start of a slice with implicit end.
                    let first = self.parse_expr()?;
                    if self.at_dot_dot() {
                        self.advance(); // consume '..'
                        let end_expr = if self.at_rbracket() {
                            None
                        } else {
                            Some(Box::new(self.parse_expr()?))
                        };
                        let end = self.expect_rbracket("expected `]` to close slice operator")?;
                        expr = Expr::Slice(SliceExpr {
                            array: Box::new(expr),
                            start: Some(Box::new(first)),
                            end: end_expr,
                            span: start.join(end),
                        });
                    } else {
                        let end = self.expect_rbracket(
                            "expected `]` after array index (or `..` for a slice)",
                        )?;
                        expr = Expr::Index(IndexExpr {
                            array: Box::new(expr),
                            index: Box::new(first),
                            span: start.join(end),
                        });
                    }
                }
            } else if self.at_dot() && matches!(self.peek().kind, TokenKind::Ident(_)) {
                // Method call / field access on an ARBITRARY receiver.
                //
                // `MethodCallExpr.receiver` and `FieldAccessExpr.object` have
                // always been `Box<Expr>`; the restriction lived here. Method
                // calls are recognised EARLIER, while parsing a path, so the
                // receiver could only ever be a `Path` and `f(x).g()` had no
                // way to parse. That arm still runs first and still consumes
                // `a.b.c(..)` wholesale, so this one only sees a `.` trailing
                // a non-path primary — a call, an index, a parenthesised
                // expression — which is exactly the gap.
                //
                // Guarded on an `Ident` follower so `.0` tuple indexing (not
                // implemented) keeps falling through to the existing error
                // path rather than being mis-parsed as a field named `0`.
                self.advance(); // consume '.'
                // Scoped so the `&self` borrow from `advance` ends here and
                // the `at_lparen` / `parse_expr` calls below can borrow again.
                let (name, name_span) = {
                    let token = self.advance();
                    let TokenKind::Ident(text) = token.kind.clone() else {
                        unreachable!("guarded by the Ident lookahead above")
                    };
                    (text, token.span)
                };

                if self.at_lparen() {
                    self.advance(); // consume '('
                    let mut args = Vec::new();
                    while !self.is_eof() && !self.at_rparen() {
                        args.push(self.parse_expr()?);
                        if self.at_comma() {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    let end = self.expect_rparen("expected `)` after method arguments")?;
                    let span = expr.span().join(end);
                    expr = Expr::MethodCall(MethodCallExpr {
                        receiver: Box::new(expr),
                        method: name,
                        args,
                        // A `.`-spelled receiver by construction: `::` cannot
                        // reach this arm, so T156's fail-closed `::` handling
                        // is unaffected.
                        colon_spelled: false,
                        span,
                    });
                } else {
                    let span = expr.span().join(name_span);
                    expr = Expr::FieldAccess(FieldAccessExpr {
                        object: Box::new(expr),
                        field: name,
                        span,
                    });
                }
            } else {
                break;
            }
        }

        Some(expr)
    }

    /// PR-E3: assemble an `Expr::FString` from the lexer's f-string token sequence
    /// `FStrBegin (FStrChunk (FStrHoleStart expr FStrHoleEnd)?)* FStrEnd`. The lexer
    /// guarantees this shape (an unterminated f-string/hole is an L003 there), so
    /// `parse_expr` cleanly stops at the non-expression `FStrHoleEnd` (ET-E9) and the
    /// `FStrHoleEnd`/catch-all checks are safety nets.
    fn parse_fstring_expr(&mut self) -> Option<Expr> {
        let start = self.advance().span; // consume FStrBegin
        let mut parts: Vec<crate::ast::FStringPart> = Vec::new();
        // The lexer guarantees the sequence is `…FStrEnd`, so `end` is assigned
        // exactly once (at FStrEnd) on the only path that reaches the span join.
        let end;
        loop {
            match self.current().kind.clone() {
                TokenKind::FStrChunk(text) => {
                    let sp = self.advance().span;
                    parts.push(crate::ast::FStringPart::Literal(text, sp));
                }
                TokenKind::FStrHoleStart => {
                    self.advance(); // consume the hole-open `{`
                    let hole = self.parse_expr()?;
                    let close = self.current().span;
                    if matches!(self.current().kind, TokenKind::FStrHoleEnd) {
                        self.advance();
                    } else {
                        self.diagnostics.push(Diagnostic::error(
                            codes::P018,
                            "expected `}` to close the interpolation hole",
                            Some(close),
                        ));
                        return None;
                    }
                    parts.push(crate::ast::FStringPart::Hole(Box::new(hole)));
                }
                TokenKind::FStrEnd => {
                    end = self.advance().span;
                    break;
                }
                _ => {
                    self.diagnostics.push(Diagnostic::error(
                        codes::P018,
                        "malformed f-string",
                        Some(self.current().span),
                    ));
                    return None;
                }
            }
        }
        Some(Expr::FString(crate::ast::FStringExpr {
            parts,
            span: start.join(end),
        }))
    }

    fn parse_array_literal(&mut self) -> Option<Expr> {
        let start = self.advance().span; // consume '['

        // Empty array `[]`.
        if self.at_rbracket() {
            let end = self.advance().span;
            return Some(Expr::ArrayLit(ArrayLitExpr {
                elements: Vec::new(),
                span: start.join(end),
            }));
        }

        let first = self.parse_expr()?;

        // Array-repeat form `[elem; N]`. Mirrors the type-position `[T; N]`
        // grammar exactly: a strict `IntLit` count in 0..=65535 (T239 on any
        // deviation). It desugars HERE, at parse time, into an `N`-element
        // `ArrayLit`, so there is no new AST node and no new type-check / AIR
        // path — downstream sees an ordinary array literal. The repeated
        // element MUST be a literal so that cloning it `N` times is identical
        // to evaluating it once; a side-effecting element (e.g. `[f(); 8]`) is
        // rejected rather than silently evaluated `N` times. Before this branch,
        // `[e; n]` was always a syntax error (the comma loop below would `break`
        // and `expect_rbracket` would fail on the `;`), so this is a pure
        // ADDITION that leaves every existing array literal byte-identical.
        if self.at_semicolon() {
            self.advance(); // consume ';'
            let count_tok = self.current().clone();
            let count: usize = match count_tok.kind {
                TokenKind::IntLit(v) if (0..=65535).contains(&v) => {
                    self.advance();
                    v as usize
                }
                TokenKind::IntLit(v) => {
                    self.diagnostics.push(Diagnostic::error(
                        codes::T239,
                        format!(
                            "array-repeat count `{v}` is out of range; `[elem; N]` admits only integer literals in 0..=65535 (inclusive)."
                        ),
                        Some(count_tok.span),
                    ));
                    return None;
                }
                _ => {
                    self.diagnostics.push(Diagnostic::error(
                        codes::T239,
                        "expected an integer literal as the count in an array-repeat `[elem; N]` (e.g. `[0; 64]`); SIGIL does not admit const-expression or named-constant counts",
                        Some(count_tok.span),
                    ));
                    return None;
                }
            };
            if !matches!(first, Expr::Literal(_)) {
                self.diagnostics.push(Diagnostic::error(
                    codes::P001,
                    "the repeated element in an array-repeat `[elem; N]` must be a literal (e.g. `[0; 8]`), so it can be expanded without re-evaluating a side-effecting expression",
                    Some(first.span()),
                ));
                return None;
            }
            let end = self.expect_rbracket("expected `]` to close array-repeat literal")?;
            let elements = vec![first; count];
            return Some(Expr::ArrayLit(ArrayLitExpr {
                elements,
                span: start.join(end),
            }));
        }

        // Comma-separated form `[a, b, c]` (optionally trailing comma).
        let mut elements = vec![first];
        if self.at_comma() {
            self.advance();
            while !self.is_eof() && !self.at_rbracket() {
                elements.push(self.parse_expr()?);
                if self.at_comma() {
                    self.advance();
                } else {
                    break;
                }
            }
        }

        let end = self.expect_rbracket("expected `]` to close array literal")?;
        Some(Expr::ArrayLit(ArrayLitExpr {
            elements,
            span: start.join(end),
        }))
    }

    fn parse_primary_expr(&mut self) -> Option<Expr> {
        let token = self.current().clone();

        match token.kind {
            TokenKind::BoolLit(_)
            | TokenKind::IntLit(_)
            | TokenKind::IntLit256(_)
            | TokenKind::StrLit(_) => {
                let literal = self.parse_literal()?;
                Some(Expr::Literal(LiteralExpr {
                    literal,
                    span: token.span,
                }))
            }
            TokenKind::FloatLit(_) => {
                let literal = self.parse_literal()?;
                Some(Expr::Literal(LiteralExpr {
                    literal,
                    span: token.span,
                }))
            }
            TokenKind::FStrBegin => self.parse_fstring_expr(),
            // Capabilities-as-values: `mint` is a CONTEXTUAL keyword. It leads a
            // `mint <CapType> for <target>` expression ONLY when immediately
            // followed by another identifier (the cap-type name) — a shape that
            // never occurs in a normal expression. Everywhere else (`fn mint`,
            // `mint(...)`, `.mint()`, a bare `mint` value) it stays a plain
            // identifier, so `mint` is NOT a reserved word (an ERC20 `function
            // mint` translates and compiles fine).
            TokenKind::Ident(ref name)
                if name == "mint" && matches!(self.peek().kind, TokenKind::Ident(_)) =>
            {
                self.parse_mint_expr()
            }
            // Effect Handlers (EH0): `perform <Effect>.<op>(args)`. Contextual on
            // the unambiguous `perform <Ident> .` shape (`<ident> <ident>` is not
            // a valid expression, so this never overlaps real code) — mirrors the
            // `mint` trick above so `perform` stays a plain identifier elsewhere.
            TokenKind::Ident(ref name)
                if name == "perform"
                    && matches!(self.peek().kind, TokenKind::Ident(_))
                    && matches!(self.nth_kind(2), Some(TokenKind::Dot)) =>
            {
                self.parse_perform_expr()
            }
            // Effect Handlers (EH0): `resume <expr>`, recognized ONLY inside a
            // handler-clause body (`clause_depth > 0`); a plain identifier otherwise.
            TokenKind::Ident(ref name) if name == "resume" && self.clause_depth > 0 => {
                self.parse_resume_expr()
            }
            TokenKind::Ident(_) => self.parse_ident_led_expr(),
            TokenKind::Spawn => self.parse_spawn_expr(),
            TokenKind::LBracket => self.parse_array_literal(),
            TokenKind::Fn => self.parse_closure_expr(),
            TokenKind::Grant => self.parse_grant_expr(),
            TokenKind::Handle => self.parse_handle_expr(),
            TokenKind::Declassify => self.parse_declassify_expr(),
            TokenKind::DeclassifyCt => self.parse_declassify_ct_expr(),
            TokenKind::Region => self.parse_region_expr(),
            TokenKind::LParen => {
                // `(` opens either a parenthesized expression (grouping) or a
                // tuple literal. The COMMA is the sole discriminator (ET-8):
                // `(e)` → grouping (byte-identical to the pre-tuple behavior —
                // the AST carries no Paren node, just the inner Expr); `(a, b, …)`
                // → a tuple. `(a,)` (1-tuple) is rejected (AG-4); arity is capped
                // at MAX_TUPLE_ARITY (ET-2). A trailing comma in a ≥2 tuple
                // (`(a, b,)`) is accepted.
                let start = self.advance().span; // consume (
                let first = self.parse_expr()?;
                if self.at_comma() {
                    let mut elements = vec![first];
                    self.advance(); // consume the first comma
                    while !self.is_eof() && !self.at_rparen() {
                        elements.push(self.parse_expr()?);
                        if self.at_comma() {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    let end = self.expect_rparen("expected `)` to close tuple literal")?;
                    let span = start.join(end);
                    if elements.len() < 2 {
                        self.diagnostics.push(Diagnostic::error(
                            codes::T261,
                            "a tuple needs at least two elements; `(a,)` is not a 1-tuple — a single parenthesized value `(a)` is just that value"
                                .to_string(),
                            Some(span),
                        ));
                        return None;
                    }
                    if elements.len() > MAX_TUPLE_ARITY {
                        self.diagnostics.push(Diagnostic::error(
                            codes::T261,
                            format!(
                                "tuple literal has {} elements; the maximum is {MAX_TUPLE_ARITY}",
                                elements.len()
                            ),
                            Some(span),
                        ));
                        return None;
                    }
                    Some(Expr::Tuple(TupleExpr { elements, span }))
                } else {
                    self.expect_rparen("expected `)` to close parenthesized expression")?;
                    Some(first)
                }
            }
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::P020,
                    "expected expression",
                    Some(token.span),
                ));
                None
            }
        }
    }

    fn parse_handle_expr(&mut self) -> Option<Expr> {
        // Effect Handlers (EH0, C-PATHSEP): the clause form
        // `handle <expr> { Op(x) => .. }` is a DISTINCT node from the legacy bare
        // row-widening `handle E (, E)* { stmts }`. Disambiguate by lookahead so
        // the legacy form stays byte-identical.
        if self.at_clause_handle() {
            return self.parse_clause_handle_expr();
        }
        let start = self.advance().span; // consume 'handle'
        let mut effects = Vec::new();
        // Parse effect names until {
        while !self.is_eof() && !self.at_lbrace() {
            if let Some((name, _)) = self.expect_ident("expected effect name in handle") {
                effects.push(name);
            }
            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }
        let body = self.parse_braced_block("expected `{` for handle body")?;
        let span = start.join(body.span);
        Some(Expr::Handle(HandleExpr {
            effects,
            body,
            span,
        }))
    }

    /// Effect Handlers (EH0): lookahead from a `handle` token deciding clause-form
    /// vs bare-form. The bare form is exactly `Ident (, Ident)* {` whose body has
    /// no top-level `=>`. Anything else — a non-ident header, or a body with a
    /// depth-1 `=>` — is the clause form. Token-bounded, side-effect-free.
    fn at_clause_handle(&self) -> bool {
        // Offset 0 == `handle`; the header begins at offset 1.
        let mut i = 1;
        loop {
            match self.nth_kind(i) {
                Some(TokenKind::Ident(_)) => match self.nth_kind(i + 1) {
                    Some(TokenKind::Comma) => i += 2,
                    Some(TokenKind::LBrace) => {
                        // Bare-shaped header `Ident (, Ident)* {` — decide by body.
                        return self.body_has_top_level_fat_arrow(i + 1);
                    }
                    // `Ident` followed by `.`/`(`/etc. => a scrutinee expression.
                    _ => return true,
                },
                // A non-ident header (`(`, literal, …) => a scrutinee expression.
                _ => return true,
            }
        }
    }

    /// Scan the braced body beginning at token offset `brace_off` (a `{`),
    /// tracking `(){}[]` depth, and return true if a `=>` appears at the body's
    /// own depth (depth 1). A nested `match`/closure pushes deeper, so its arrows
    /// never trip this. Bounded by the token count.
    fn body_has_top_level_fat_arrow(&self, brace_off: usize) -> bool {
        let mut depth = 0i32;
        let mut i = brace_off;
        loop {
            match self.nth_kind(i) {
                None => return false,
                Some(TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket) => depth += 1,
                Some(TokenKind::RBrace | TokenKind::RParen | TokenKind::RBracket) => {
                    depth -= 1;
                    if depth == 0 {
                        return false; // closed the body with no top-level `=>`
                    }
                }
                Some(TokenKind::FatArrow) if depth == 1 => return true,
                _ => {}
            }
            i += 1;
        }
    }

    /// Effect Handlers (EH0): `handle <scrutinee> { Op(x) => body, .. }`. Mirrors
    /// `parse_match_statement`'s scrutinee/`{`/arm structure.
    fn parse_clause_handle_expr(&mut self) -> Option<Expr> {
        let start = self.advance().span; // consume `handle`
        let scrutinee = self.parse_expr()?;
        self.expect_lbrace("expected `{` after `handle` scrutinee")?;
        let mut clauses = Vec::new();
        while !self.is_eof() && !self.at_rbrace() {
            clauses.push(self.parse_handle_clause()?);
            if self.at_comma() || self.at_semicolon() {
                self.advance();
            } else if !self.at_rbrace() {
                self.diagnostics.push(Diagnostic::error(
                    codes::P018,
                    "expected `,`, `;`, or `}` after a handle clause",
                    Some(self.current().span),
                ));
                self.synchronize_block_statement();
            }
        }
        let close = self.expect_rbrace("expected `}` to close handle")?;
        Some(Expr::ClauseHandle(ClauseHandleExpr {
            scrutinee: Box::new(scrutinee),
            clauses,
            span: start.join(close),
        }))
    }

    /// Effect Handlers (EH0): one clause `Effect.op(binders) => body`. Binders are
    /// plain names; the body is a braced block OR a single expression (wrapped as
    /// a one-statement block). `resume` is enabled inside the body via
    /// `clause_depth`.
    fn parse_handle_clause(&mut self) -> Option<HandleClause> {
        let (effect, effect_span) = self.expect_ident("expected effect name in handle clause")?;
        self.expect_dot("expected `.` after effect name in handle clause")?;
        let (op, _) = self.expect_ident("expected operation name after `Effect.`")?;
        self.expect_lparen("expected `(` after operation name in handle clause")?;
        let mut binders = Vec::new();
        while !self.is_eof() && !self.at_rparen() {
            let (b, _) = self.expect_ident("expected a binder name in handle clause")?;
            binders.push(b);
            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }
        self.expect_rparen("expected `)` after handle clause binders")?;
        self.expect_fat_arrow("expected `=>` after handle clause pattern")?;
        self.clause_depth += 1;
        let body = if self.at_lbrace() {
            self.parse_braced_block("expected `{` to start a handle clause body")?
        } else {
            let expr = self.parse_expr()?;
            let span = expr.span();
            Block {
                statements: vec![Stmt::Expr(ExprStmt { expr, span })],
                span,
            }
        };
        self.clause_depth = self.clause_depth.saturating_sub(1);
        let span = effect_span.join(body.span);
        Some(HandleClause {
            effect,
            op,
            binders,
            body,
            span,
        })
    }

    /// Effect Handlers (EH0): `perform <Effect>.<op>(args)`.
    fn parse_perform_expr(&mut self) -> Option<Expr> {
        let start = self.advance().span; // consume `perform`
        let (effect, effect_span) = self.expect_ident("expected effect name after `perform`")?;
        self.expect_dot("expected `.` after effect name in `perform`")?;
        let (op, _) = self.expect_ident("expected operation name after `perform Effect.`")?;
        self.expect_lparen("expected `(` after `perform Effect.op`")?;
        let mut args = Vec::new();
        while !self.is_eof() && !self.at_rparen() {
            args.push(self.parse_expr()?);
            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }
        let end = self.expect_rparen("expected `)` to close `perform` arguments")?;
        Some(Expr::Perform(PerformExpr {
            effect,
            effect_span,
            op,
            args,
            span: start.join(end),
        }))
    }

    /// Effect Handlers (EH0): `resume <expr>` (only reached inside a clause body).
    fn parse_resume_expr(&mut self) -> Option<Expr> {
        let start = self.advance().span; // consume `resume`
        let value = self.parse_expr()?;
        let span = start.join(value.span());
        Some(Expr::Resume(ResumeExpr {
            value: Box::new(value),
            span,
        }))
    }

    /// Effect Handlers (EH0): consume a `.` or emit P001.
    fn expect_dot(&mut self, message: &'static str) -> Option<Span> {
        if self.at_dot() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting(".", message, at);
            None
        }
    }

    fn parse_effect_row(&mut self) -> Option<Vec<String>> {
        if !self.at_bang() {
            return None;
        }
        self.advance(); // consume !
        self.expect_lbrace("expected `{` after `!` in effect row")?;
        let mut effects = Vec::new();
        while !self.is_eof() && !self.at_rbrace() {
            if let Some((name, _)) = self.expect_ident("expected effect name") {
                effects.push(name);
            }
            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }
        if self.at_rbrace() {
            self.advance();
        }
        Some(effects)
    }

    fn at_bang(&self) -> bool {
        matches!(self.current().kind, TokenKind::Bang)
    }

    fn parse_effect_decl(&mut self) -> Option<EffectDecl> {
        let start = self.advance().span; // consume 'effect'
        let (name, end_span) = self.expect_ident("expected effect name")?;
        let mut ops = Vec::new();
        // `effect Name;` (bare marker) OR
        // `effect Name { fn op(params) -> Ty; .. }` (operation-bearing, EH0).
        if self.at_semicolon() {
            self.advance();
        } else if self.at_lbrace() {
            self.advance(); // consume `{`
            while !self.is_eof() && !self.at_rbrace() {
                if !self.at_fn() {
                    self.diagnostics.push(Diagnostic::error(
                        codes::P012,
                        "expected an effect operation signature (`fn name(...) -> Ty;`) inside the effect body",
                        Some(self.current().span),
                    ));
                    return None;
                }
                ops.push(self.parse_effect_op()?);
            }
            self.expect_rbrace("expected `}` to close effect declaration");
        }
        // Span ends at the effect NAME — byte-identical with the legacy form and
        // the self-hosted `parser.sigil` mirror (the operation list does not
        // extend the decl span). See parser_differential parity.
        Some(EffectDecl {
            name,
            ops,
            span: start.join(end_span),
        })
    }

    /// Effect Handlers (EH0): one operation signature inside an `effect` body —
    /// `fn name(params) -> Ty;` (no body, no type params, no effect row),
    /// modelled on [`Self::parse_trait_method_sig`]. The return type is the
    /// resumed-value type; `-> never` marks an abortive-only operation.
    fn parse_effect_op(&mut self) -> Option<EffectOp> {
        let start = self.current().span; // at `fn`
        self.advance(); // consume `fn`
        let (name, _) = self.expect_ident("expected operation name after `fn`")?;
        let params = self.parse_params()?;
        let return_type = if self.at_arrow() {
            self.advance();
            Some(self.parse_type_expr("expected return type after `->`")?)
        } else {
            None
        };
        let end = self.expect_semicolon(
            "expected `;` after an effect operation signature (operations are signatures only — no body)",
        )?;
        Some(EffectOp {
            name,
            params,
            return_type,
            span: start.join(end),
        })
    }

    fn parse_grant_expr(&mut self) -> Option<Expr> {
        let start = self.advance().span; // consume 'grant'
        self.expect_lparen("expected `(` after `grant`")?;
        let cap = self.parse_expr()?;
        self.expect_comma("expected `,` between grant cap and body")?;
        let body = self.parse_expr()?; // should be a closure
        let end = self.expect_rparen("expected `)` after grant body")?;
        Some(Expr::Grant(GrantExpr {
            cap: Box::new(cap),
            body: Box::new(body),
            span: start.join(end),
        }))
    }

    fn parse_taint_annotation(&mut self) -> Option<TaintLabel> {
        self.parse_taint_annotation_inner(false).0
    }

    /// Taint annotation in a position where `@Flow` (taint polymorphism) is
    /// also admissible — currently only an `fn` item's return. Returns
    /// `(concrete_label, saw_flow)`; at most one can be set.
    fn parse_taint_annotation_allowing_flow(&mut self) -> (Option<TaintLabel>, bool) {
        self.parse_taint_annotation_inner(true)
    }

    fn parse_taint_annotation_inner(&mut self, allow_flow: bool) -> (Option<TaintLabel>, bool) {
        if self.current().kind != TokenKind::At {
            return (None, false);
        }
        self.advance(); // consume @
        let Some((name, name_span)) = self.expect_ident("expected taint label after `@`") else {
            return (None, false);
        };
        match name.as_str() {
            "Public" => (Some(TaintLabel::Public), false),
            "Internal" => (Some(TaintLabel::Internal), false),
            "Secret" => (Some(TaintLabel::Secret), false),
            "SecretCT" => (Some(TaintLabel::SecretCT), false),
            "Flow" if allow_flow => (None, true),
            "Flow" => {
                self.diagnostics.push(Diagnostic::error(
                    codes::P021,
                    "`@Flow` is only valid on the parameters and return type of an `fn` item \
                     (not on externs, traits, actor handlers, effect operations, closures, \
                     or `let` bindings)"
                        .to_string(),
                    Some(name_span),
                ));
                (None, false)
            }
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::P021,
                    format!(
                        "unknown taint label '@{name}', expected Public/Internal/Secret/SecretCT"
                    ),
                    Some(self.current().span),
                ));
                (None, false)
            }
        }
    }

    /// Parse the optional `@`-annotations after a parameter's type. Two
    /// ORTHOGONAL axes may appear, in any order and combination (H7): a taint
    /// label (`@Public`/`@Internal`/`@Secret`/`@SecretCT`) and a mutability
    /// marker (`@ReadOnly`/`@Mut`). At most one of each; `@ReadOnly @Mut` on the
    /// same param is a contradiction (H3) and is rejected. Each iteration
    /// consumes `@` then the ident and classifies by name — no lookahead — so a
    /// mutability marker is never mis-routed as an unknown taint label.
    fn parse_param_annotations(
        &mut self,
    ) -> (Option<TaintLabel>, Mutability, Option<String>, bool) {
        let mut taint: Option<TaintLabel> = None;
        let mut mutability = Mutability::Default;
        let mut region: Option<String> = None;
        let mut flow = false;
        while self.current().kind == TokenKind::At {
            self.advance(); // consume @
            // Regions (DEF-2b, LD-4): `@in r` — the region annotation. `in` is the keyword
            // token (not an ident), so it is matched before `expect_ident`. The following
            // ident is the `Region` parameter name (validated in `parse_params`).
            if self.current().kind == TokenKind::In {
                self.advance(); // consume `in`
                if let Some((region_name, _)) =
                    self.expect_ident("expected a `Region` parameter name after `@in`")
                {
                    region = Some(region_name);
                }
                continue;
            }
            let (name, name_span) = match self.expect_ident("expected annotation after `@`") {
                Some(pair) => pair,
                None => break,
            };
            match name.as_str() {
                "Public" => taint = Some(TaintLabel::Public),
                "Internal" => taint = Some(TaintLabel::Internal),
                "Secret" => taint = Some(TaintLabel::Secret),
                "SecretCT" => taint = Some(TaintLabel::SecretCT),
                // Taint polymorphism. Admissibility for this parameter position
                // is decided by `parse_params` (only `fn` items allow it); here
                // we only record that it was written.
                "Flow" => flow = true,
                "ReadOnly" => {
                    if mutability == Mutability::Mut {
                        self.diagnostics.push(Diagnostic::error(
                            codes::P021,
                            "a parameter cannot be both `@ReadOnly` and `@Mut`".to_string(),
                            Some(name_span),
                        ));
                    }
                    mutability = Mutability::ReadOnly;
                }
                "Mut" => {
                    if mutability == Mutability::ReadOnly {
                        self.diagnostics.push(Diagnostic::error(
                            codes::P021,
                            "a parameter cannot be both `@ReadOnly` and `@Mut`".to_string(),
                            Some(name_span),
                        ));
                    }
                    mutability = Mutability::Mut;
                }
                _ => {
                    self.diagnostics.push(Diagnostic::error(
                        codes::P021,
                        format!(
                            "unknown annotation '@{name}', expected a taint label \
                             (Public/Internal/Secret/SecretCT/Flow) or a mutability marker \
                             (ReadOnly/Mut)"
                        ),
                        Some(name_span),
                    ));
                }
            }
        }
        // A parameter carries ONE label contract. `@Flow` says "any label, and
        // the result follows"; a concrete label says "exactly this". Together
        // they contradict.
        if flow && taint.is_some() {
            self.diagnostics.push(Diagnostic::error(
                codes::P021,
                "a parameter cannot be both `@Flow` and a concrete taint label".to_string(),
                Some(self.current().span),
            ));
            flow = false;
        }
        (taint, mutability, region, flow)
    }

    fn parse_declassify_expr(&mut self) -> Option<Expr> {
        let start = self.advance().span; // consume 'declassify'
        self.expect_lparen("expected `(` after `declassify`")?;
        let value = self.parse_expr()?;
        self.expect_comma("expected `,` between value and capability")?;
        let cap = self.parse_expr()?;
        let end = self.expect_rparen("expected `)` after declassify arguments")?;
        let target = self.parse_taint_annotation(); // optional @Label after )
        Some(Expr::Declassify(DeclassifyExpr {
            value: Box::new(value),
            cap: Box::new(cap),
            target,
            span: start.join(end),
        }))
    }

    /// Parses `declassify_ct(value, cap)` — lowers `@SecretCT → @Secret`.
    /// The capability is `Cap<DeclassifyCT>`. See spec §3.4.1.
    fn parse_declassify_ct_expr(&mut self) -> Option<Expr> {
        let start = self.advance().span; // consume 'declassify_ct'
        self.expect_lparen("expected `(` after `declassify_ct`")?;
        let value = self.parse_expr()?;
        self.expect_comma("expected `,` between value and capability")?;
        let cap = self.parse_expr()?;
        let end = self.expect_rparen("expected `)` after declassify_ct arguments")?;
        Some(Expr::DeclassifyCt(DeclassifyCtExpr {
            value: Box::new(value),
            cap: Box::new(cap),
            span: start.join(end),
        }))
    }

    fn parse_region_expr(&mut self) -> Option<Expr> {
        let start = self.advance().span; // consume 'region'
        let (name, _) = self.expect_ident("expected region name")?;
        self.expect_lparen("expected `(` after region name")?;
        let limit = self.parse_expr()?;
        self.expect_rparen("expected `)` after region limit")?;
        let body = self.parse_braced_block("expected `{` for region body")?;
        let span = start.join(body.span);
        Some(Expr::Region(RegionExpr {
            name,
            limit: Box::new(limit),
            body,
            span,
        }))
    }

    /// `mint <CapType>[(d0, d1, …)] for <target>` — the capabilities-as-values
    /// constructor. `mint` leads a primary expression, so the `for` here is a
    /// delimiter, never a `for`-in loop (those only start a statement).
    fn parse_mint_expr(&mut self) -> Option<Expr> {
        let start = self.advance().span; // consume `mint`
        let (cap_name, cap_name_span) =
            self.expect_ident("expected capability type name after `mint`")?;

        // Optional positional deadline literals: `mint Approval(2030) for t`.
        // Mirrors the positional `i64` deadline params a parametric cap
        // carries; arity / staleness are validated at type-check.
        let params = if self.at_lparen() {
            self.advance();
            let mut collected = Vec::new();
            loop {
                let tok = self.current().clone();
                match tok.kind {
                    TokenKind::IntLit(v) => {
                        self.cursor += 1;
                        collected.push(v);
                    }
                    _ => {
                        self.p001_expecting(
                            "<deadline>",
                            "expected an `i64` deadline literal in a parametric `mint`",
                            tok.span,
                        );
                        return None;
                    }
                }
                if self.at_comma() {
                    self.advance();
                    continue;
                }
                break;
            }
            self.expect_rparen("expected `)` after `mint` deadline parameters")?;
            collected
        } else {
            Vec::new()
        };

        if !self.at_for() {
            let at = self.current().span;
            self.p001_expecting(
                "for",
                "expected `for <target>` after the capability type in a `mint` expression",
                at,
            );
            return None;
        }
        self.advance(); // consume `for`

        let target = self.parse_expr()?;
        let span = start.join(target.span());
        Some(Expr::Mint(MintExpr {
            cap_name,
            cap_name_span,
            params,
            target: Box::new(target),
            span,
        }))
    }

    fn parse_closure_expr(&mut self) -> Option<Expr> {
        let start = self.advance().span; // consume 'fn'
        let params = self.parse_params()?; // parse_params consumes ( ... )
        let return_type = if self.at_arrow() {
            self.advance();
            Some(self.parse_type_expr("expected return type after `->`")?)
        } else {
            None
        };
        let body = self.parse_braced_block("expected `{` for closure body")?;
        let span = start.join(body.span);
        Some(Expr::Closure(ClosureExpr {
            params,
            return_type,
            body,
            span,
        }))
    }

    fn parse_ident_led_expr(&mut self) -> Option<Expr> {
        let (segment, start) = self.expect_ident("expected expression")?;
        let path = self.parse_path_from_first(segment, start)?;
        // Capture the spelling BEFORE any nested parse can reset it.
        let colon_spelled = self.last_path_colon_spelled;

        if self.at_lparen() {
            return self.parse_call_expr(path, colon_spelled);
        }

        // Record construction: TypeName { field: value, ... }
        // Disambiguate from block: peek past { to see if ident: follows
        if self.at_lbrace() && self.peek_is_record_literal() {
            return self.parse_record_literal(path);
        }

        let span = path.span;
        Some(Expr::Path(PathExpr { path, span }))
    }

    fn peek_is_record_literal(&self) -> bool {
        // Check if { is followed by ident : (field assignment pattern)
        let base = self.cursor + 1; // skip past {
        if base + 1 >= self.tokens.len() {
            return false;
        }
        matches!(self.tokens[base].kind, TokenKind::Ident(_))
            && matches!(self.tokens[base + 1].kind, TokenKind::Colon)
    }

    fn parse_record_literal(&mut self, type_path: Path) -> Option<Expr> {
        let start = type_path.span;
        let type_name = type_path.display_name();
        self.advance(); // consume {
        let mut fields = Vec::new();

        while !self.is_eof() && !self.at_rbrace() {
            let (field_name, _) = self.expect_ident("expected field name")?;
            self.expect_colon("expected `:` after field name")?;
            let value = self.parse_expr()?;
            fields.push((field_name, value));

            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }

        let end = self.expect_rbrace("expected `}` to close record literal")?;
        Some(Expr::RecordConstruct(RecordConstructExpr {
            type_name,
            fields,
            span: start.join(end),
        }))
    }

    fn parse_call_expr(&mut self, callee: Path, colon_spelled: bool) -> Option<Expr> {
        if let Some(actor_op) = self.try_parse_actor_op_expr(&callee, colon_spelled)? {
            return Some(actor_op);
        }

        if let Some(result_ctor) = self.try_parse_result_ctor(&callee)? {
            return Some(result_ctor);
        }

        let start = callee.span;
        self.expect_lparen("expected `(` after callable path")?;
        let mut args = Vec::new();

        while !self.is_eof() && !self.at_rparen() {
            args.push(self.parse_expr()?);

            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }

        let end = self.expect_rparen("expected `)` after call arguments")?;
        Some(Expr::Call(CallExpr {
            callee,
            args,
            span: start.join(end),
        }))
    }

    fn try_parse_result_ctor(&mut self, callee: &Path) -> Option<Option<Expr>> {
        match callee.segments.as_slice() {
            [name] if name == "Ok" || name == "Err" => self
                .parse_result_ctor_expr(name == "Ok", callee.span)
                .map(Some),
            _ => Some(None),
        }
    }

    fn parse_result_ctor_expr(&mut self, is_ok: bool, start: Span) -> Option<Expr> {
        self.expect_lparen("expected `(` after result constructor")?;
        let value = self.parse_expr()?;
        let end = self.expect_rparen("expected `)` after result constructor")?;

        Some(Expr::ResultCtor(ResultCtorExpr {
            is_ok,
            value: Box::new(value),
            span: start.join(end),
        }))
    }

    fn try_parse_actor_op_expr(
        &mut self,
        callee: &Path,
        colon_spelled: bool,
    ) -> Option<Option<Expr>> {
        let Some(method_name) = callee.segments.last().map(String::as_str) else {
            return Some(None);
        };

        let target_segments = &callee.segments[..callee.segments.len().saturating_sub(1)];
        if target_segments.is_empty() {
            return Some(None);
        }

        let target = Path {
            segments: target_segments.to_vec(),
            type_args: vec![],
            span: callee.span,
        };

        match method_name {
            "send" => self.parse_send_expr(target).map(Some),
            "ask" => self.parse_ask_expr(target).map(Some),
            "restrict" => self.parse_restrict_expr(target).map(Some),
            "restrict_deadline" => self.parse_restrict_deadline_expr(target).map(Some),
            "split" => self.parse_split_expr(target).map(Some),
            "draw" => self.parse_draw_expr(target).map(Some),
            _ if self.at_lparen() => {
                // Only treat as method call if `(` follows — otherwise it's field access
                self.parse_method_call_expr(target, method_name, colon_spelled)
                    .map(Some)
            }
            _ => Some(None), // Fall through to field access handling
        }
    }

    fn parse_send_expr(&mut self, target: Path) -> Option<Expr> {
        let start = target.span;
        self.expect_lparen("expected `(` after `send`")?;
        let message = self.parse_expr()?;
        let end = self.expect_rparen("expected `)` after `send` payload")?;

        Some(Expr::Send(SendExpr {
            target,
            message: Box::new(message),
            span: start.join(end),
        }))
    }

    fn parse_ask_expr(&mut self, target: Path) -> Option<Expr> {
        let start = target.span;
        self.expect_lparen("expected `(` after `ask`")?;
        let message = self.parse_expr()?;
        self.expect_comma("expected `,` after `ask` payload")?;

        let timeout = if self.at_timeout_label() {
            self.advance();
            self.expect_colon("expected `:` after `timeout`")?;
            self.parse_expr()?
        } else {
            self.parse_expr()?
        };

        let end = self.expect_rparen("expected `)` after `ask` arguments")?;
        Some(Expr::Ask(AskExpr {
            target,
            message: Box::new(message),
            timeout: Box::new(timeout),
            span: start.join(end),
        }))
    }

    fn parse_restrict_expr(&mut self, target: Path) -> Option<Expr> {
        let start = target.span;
        self.expect_lparen("expected `(` after `restrict`")?;
        let (restriction, _) = self.expect_ident("expected authority name in `.restrict()`")?;
        let end = self.expect_rparen("expected `)` after restriction argument")?;
        Some(Expr::CapRestrict(CapRestrictExpr {
            cap: target,
            restriction,
            span: start.join(end),
        }))
    }

    fn parse_restrict_deadline_expr(&mut self, target: Path) -> Option<Expr> {
        let start = target.span;
        self.expect_lparen("expected `(` after `restrict_deadline`")?;
        let tok = self.current().clone();
        let deadline = match tok.kind {
            TokenKind::IntLit(v) => {
                self.cursor += 1;
                v
            }
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    codes::T200,
                    "expected an `i64` literal deadline in `.restrict_deadline(<i64>)`; Stage 2 supports only a compile-time integer literal here",
                    Some(tok.span),
                ));
                return None;
            }
        };
        let end = self.expect_rparen("expected `)` after deadline argument")?;
        Some(Expr::CapRestrictDeadline(CapRestrictDeadlineExpr {
            cap: target,
            deadline,
            span: start.join(end),
        }))
    }

    fn parse_split_expr(&mut self, target: Path) -> Option<Expr> {
        let start = target.span;
        self.expect_lparen("expected `(` after `split`")?;
        let amount = self.parse_expr()?;
        let end = self.expect_rparen("expected `)` after split amount")?;
        Some(Expr::CapSplit(CapSplitExpr {
            cap: target,
            amount: Box::new(amount),
            span: start.join(end),
        }))
    }

    fn parse_draw_expr(&mut self, target: Path) -> Option<Expr> {
        let start = target.span;
        self.expect_lparen("expected `(` after `draw`")?;
        let amount = self.parse_expr()?;
        let end = self.expect_rparen("expected `)` after draw amount")?;
        Some(Expr::CapDraw(CapDrawExpr {
            cap: target,
            amount: Box::new(amount),
            span: start.join(end),
        }))
    }

    fn parse_method_call_expr(
        &mut self,
        target: Path,
        method_name: &str,
        colon_spelled: bool,
    ) -> Option<Expr> {
        let start = target.span;
        self.expect_lparen("expected `(` after method name")?;

        let mut args = Vec::new();
        while !self.is_eof() && !self.at_rparen() {
            args.push(self.parse_expr()?);
            if self.at_comma() {
                self.advance();
            } else {
                break;
            }
        }

        let end = self.expect_rparen("expected `)` after method arguments")?;
        Some(Expr::MethodCall(MethodCallExpr {
            receiver: Box::new(Expr::Path(PathExpr {
                path: target,
                span: start,
            })),
            method: method_name.to_owned(),
            args,
            colon_spelled,
            span: start.join(end),
        }))
    }

    fn parse_spawn_expr(&mut self) -> Option<Expr> {
        let start = self.advance().span;
        if self.at_colon_colon() {
            self.advance();
        }
        let generic_start = self.expect_lt("expected `<` after `spawn`")?;
        let actor = self.parse_type_expr("expected actor type after `spawn::<`")?;
        let generic_end = self.expect_gt("expected `>` after spawned actor type")?;
        self.expect_lparen("expected `(` after spawned actor type")?;
        let mut args = Vec::new();

        while !self.is_eof() && !self.at_rparen() {
            // Check for supervision: keyword argument before parsing as positional arg
            if self.at_supervision_label() {
                break;
            }
            args.push(self.parse_expr()?);

            if self.at_comma() {
                // Peek ahead — if next token is supervision keyword, break without consuming
                if matches!(self.peek().kind, TokenKind::Supervision) {
                    self.advance(); // consume comma
                    break;
                }
                self.advance();
            } else {
                break;
            }
        }

        // Parse optional supervision: keyword argument
        let supervision = if self.at_supervision_label() {
            self.advance(); // consume 'supervision'
            self.expect_colon("expected `:` after `supervision`")?;
            Some(self.parse_supervision_expr()?)
        } else {
            None
        };

        let end = self.expect_rparen("expected `)` after spawn arguments")?;
        Some(Expr::Spawn(SpawnExpr {
            actor,
            args,
            supervision,
            span: start.join(generic_start).join(generic_end).join(end),
        }))
    }

    fn parse_supervision_expr(&mut self) -> Option<SupervisionExpr> {
        if matches!(self.current().kind, TokenKind::Ident(ref name) if name == "Stop") {
            self.advance();
            return Some(SupervisionExpr::Stop);
        }
        if matches!(self.current().kind, TokenKind::Ident(ref name) if name == "Restart") {
            self.advance();
            self.expect_lparen("expected `(` after `Restart`")?;
            let max_restarts = self.parse_expr()?;
            self.expect_rparen("expected `)` after max_restarts")?;
            return Some(SupervisionExpr::Restart {
                max_restarts: Box::new(max_restarts),
            });
        }
        self.diagnostics.push(Diagnostic::error(
            codes::P022,
            "expected `Stop` or `Restart(n)` after `supervision:`",
            Some(self.current().span),
        ));
        None
    }

    fn at_supervision_label(&self) -> bool {
        matches!(self.current().kind, TokenKind::Supervision)
    }

    /// Depth-guarding wrapper: every block body — `if`/`else`/`while`/`for`/
    /// `match`-arm/`handle`/`region`/closure — flows through here, so bounding
    /// it bounds all statement-block nesting (a deep `if a { if b { … } }` chain
    /// recurses block → statement → if → block without touching the expression
    /// guard). See `enter_nesting`.
    fn parse_braced_block(&mut self, message: &'static str) -> Option<Block> {
        if !self.enter_nesting() {
            return None;
        }
        let result = self.parse_braced_block_inner(message);
        self.exit_nesting();
        result
    }

    fn parse_braced_block_inner(&mut self, message: &'static str) -> Option<Block> {
        if !self.at_lbrace() {
            self.diagnostics.push(Diagnostic::error(
                codes::P001,
                message,
                Some(self.current().span),
            ));
            return None;
        }

        let start = self.advance().span;
        let mut statements = Vec::new();
        let mut last_span = start;

        while !self.is_eof() && !self.at_rbrace() {
            match self.parse_statement() {
                Some(statement) => {
                    last_span = statement.span();
                    statements.push(statement);
                }
                None => self.synchronize_block_statement(),
            }
        }

        let end = self.expect_rbrace("unterminated block body")?;
        Some(Block {
            statements,
            span: start.join(last_span).join(end),
        })
    }

    fn parse_visibility(&mut self) -> (Visibility, Option<Span>) {
        if self.at_pub() {
            let span = self.advance().span;
            (Visibility::Public, Some(span))
        } else {
            (Visibility::Private, None)
        }
    }

    fn expect_module(&mut self) -> Option<Span> {
        if self.at_module() {
            Some(self.advance().span)
        } else {
            self.diagnostics.push(Diagnostic::error(
                codes::P002,
                "expected `module` declaration",
                Some(self.current().span),
            ));
            None
        }
    }

    fn expect_actor(&mut self) -> Option<Span> {
        if self.at_actor() {
            Some(self.advance().span)
        } else {
            self.diagnostics.push(Diagnostic::error(
                codes::P023,
                "expected `actor`",
                Some(self.current().span),
            ));
            None
        }
    }

    fn expect_type(&mut self, message: &'static str) -> Option<Span> {
        if self.at_type() {
            Some(self.advance().span)
        } else {
            self.diagnostics.push(Diagnostic::error(
                codes::P001,
                message,
                Some(self.current().span),
            ));
            None
        }
    }

    fn expect_ident(&mut self, message: &'static str) -> Option<(String, Span)> {
        let token = self.current().clone();
        match token.kind {
            TokenKind::Ident(name) => {
                self.cursor += 1;
                Some((name, token.span))
            }
            ref kind if kind.keyword_text().is_some() => {
                // A reserved keyword (`handle`, `spawn`, `on`, …) sits where a
                // name is required. Report it precisely (P026) and recover
                // FAITHFULLY: consume the keyword and hand back a poison name so
                // the surrounding item (and everything after it) still parses,
                // instead of resynchronizing into a degenerate, truncated module
                // that would silently type-check clean and mask real errors. The
                // poison name cannot collide with any source identifier, so
                // downstream name resolution rejects references to it — the
                // overall outcome stays a consistent rejection.
                let keyword = kind.keyword_text().unwrap();
                self.diagnostics.push(Diagnostic::error(
                    codes::P026,
                    format!("`{keyword}` is a reserved keyword and cannot be used as a name here"),
                    Some(token.span),
                ));
                self.cursor += 1;
                Some((
                    format!("{RESERVED_KEYWORD_POISON_PREFIX}{keyword}"),
                    token.span,
                ))
            }
            _ => {
                self.diagnostics
                    .push(Diagnostic::error(codes::P001, message, Some(token.span)));
                None
            }
        }
    }

    fn expect_path_member_segment(&mut self, message: &'static str) -> Option<(String, Span)> {
        let token = self.current().clone();
        match token.kind {
            TokenKind::Ident(name) => {
                self.cursor += 1;
                Some((name, token.span))
            }
            TokenKind::Send => {
                self.cursor += 1;
                Some(("send".to_owned(), token.span))
            }
            TokenKind::Ask => {
                self.cursor += 1;
                Some(("ask".to_owned(), token.span))
            }
            _ => {
                self.diagnostics
                    .push(Diagnostic::error(codes::P001, message, Some(token.span)));
                None
            }
        }
    }

    fn expect_lparen(&mut self, message: &'static str) -> Option<Span> {
        if self.at_lparen() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting("(", message, at);
            None
        }
    }

    fn expect_rparen(&mut self, message: &'static str) -> Option<Span> {
        if self.at_rparen() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting(")", message, at);
            None
        }
    }

    fn expect_rbracket(&mut self, message: &'static str) -> Option<Span> {
        if self.at_rbracket() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting("]", message, at);
            None
        }
    }

    fn expect_lbrace(&mut self, message: &'static str) -> Option<Span> {
        if self.at_lbrace() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting("{", message, at);
            None
        }
    }

    fn expect_rbrace(&mut self, message: &'static str) -> Option<Span> {
        if self.at_rbrace() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting("}", message, at);
            None
        }
    }

    fn expect_colon(&mut self, message: &'static str) -> Option<Span> {
        if self.at_colon() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting(":", message, at);
            None
        }
    }

    fn expect_eq(&mut self, message: &'static str) -> Option<Span> {
        if self.at_eq() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting("=", message, at);
            None
        }
    }

    fn expect_fat_arrow(&mut self, message: &'static str) -> Option<Span> {
        if self.at_fat_arrow() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting("=>", message, at);
            None
        }
    }

    fn expect_semicolon(&mut self, message: &'static str) -> Option<Span> {
        if self.at_semicolon() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting(";", message, at);
            None
        }
    }

    fn expect_comma(&mut self, message: &'static str) -> Option<Span> {
        if self.at_comma() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting(",", message, at);
            None
        }
    }

    fn expect_gt(&mut self, message: &'static str) -> Option<Span> {
        if self.at_gt() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting(">", message, at);
            None
        }
    }

    fn expect_lt(&mut self, message: &'static str) -> Option<Span> {
        if self.at_lt() {
            Some(self.advance().span)
        } else {
            let at = self.current().span;
            self.p001_expecting("<", message, at);
            None
        }
    }

    /// Push a P001 with a machine-applicable INSERT edit for a determinate
    /// expected token. Callable ONLY with a literal token string — the
    /// class-expecting helpers (`expect_ident`/`expect_type`/
    /// `expect_path_member_segment`) have no literal to pass, so a
    /// low-confidence edit physically cannot be attached (constraint E1).
    fn p001_expecting(&mut self, expected: &'static str, message: &'static str, at: Span) {
        self.diagnostics.push(
            Diagnostic::error(codes::P001, message, Some(at)).with_suggested_edits(vec![
                SuggestedEdit {
                    start: at.start,
                    end: at.start,
                    replacement: expected.to_owned(),
                },
            ]),
        );
    }

    fn synchronize_program(&mut self) {
        while !self.is_eof() {
            if self.at_module_start() {
                break;
            }
            self.cursor += 1;
        }
    }

    /// Item-level recovery, reporting whether the caller's loop can make progress.
    ///
    /// `synchronize_item` deliberately breaks WITHOUT consuming when it reaches a
    /// `}`, an item start, or a module start, so the caller can parse that token
    /// itself. Every caller that loops on `!is_eof() && !at_rbrace()` must
    /// therefore check that recovery actually moved, or the loop re-tests an
    /// unchanged cursor and spins forever — pushing a heap-allocated `Diagnostic`
    /// every iteration, so it is unbounded memory growth as well as a hang.
    ///
    /// That is not hypothetical. `at_item_start()` includes `at_fn()`, so a `fn`
    /// item inside an `actor` body reached exactly this state: `check` never
    /// returned on a ~150-byte program. Reproduced 2026-08-04 (nested `actor`) and
    /// 2026-08-06 (`fn` in `actor`), live since 2026-05-06, registered as SR-016.
    /// This is the same class `enter_nesting` documents for statement recovery.
    ///
    /// Returns `true` when the loop may safely continue: recovery consumed
    /// something, or the loop's own exit condition (EOF or `}`) now holds.
    /// Returns `false` when the cursor is parked on an item/module start that
    /// recovery will never consume — the caller MUST then either leave its block
    /// or force the cursor forward, because iterating again cannot progress.
    #[must_use]
    fn synchronize_item_made_progress(&mut self) -> bool {
        let before = self.cursor;
        self.synchronize_item();
        self.cursor != before || self.is_eof() || self.at_rbrace()
    }

    fn synchronize_item(&mut self) {
        while !self.is_eof() {
            if self.at_semicolon() {
                self.cursor += 1;
                break;
            }

            if self.at_rbrace() || self.at_item_start() || self.at_module_start() {
                break;
            }

            self.cursor += 1;
        }
    }

    fn synchronize_block_statement(&mut self) {
        while !self.is_eof() {
            if self.at_semicolon() {
                self.cursor += 1;
                break;
            }

            if self.at_rbrace()
                || self.at_let()
                || self.at_expr_start()
                || self.at_if()
                || self.at_match()
                || self.at_while()
                || self.at_return()
            {
                break;
            }

            self.cursor += 1;
        }
    }

    fn current(&self) -> &Token {
        &self.tokens[self.cursor]
    }

    fn peek(&self) -> &Token {
        &self.tokens[(self.cursor + 1).min(self.tokens.len() - 1)]
    }

    fn previous_span(&self) -> Span {
        let index = self.cursor.saturating_sub(1);
        self.tokens[index].span
    }

    fn advance(&mut self) -> &Token {
        let token = &self.tokens[self.cursor];
        self.cursor += 1;
        token
    }

    fn at_item_start(&self) -> bool {
        self.at_use()
            || self.at_const()
            || self.at_fn()
            || self.at_actor_start()
            || self.at_cap()
            || (self.at_pub() && self.next_is_item_keyword())
    }

    fn at_module_start(&self) -> bool {
        self.at_module() || (self.at_pub() && self.peek_is_module()) || self.at_hash()
    }

    fn at_effect(&self) -> bool {
        matches!(self.current().kind, TokenKind::Effect)
    }

    fn at_hash(&self) -> bool {
        matches!(self.current().kind, TokenKind::Hash)
    }

    fn peek_is_module(&self) -> bool {
        matches!(self.nth_kind(1), Some(TokenKind::Module))
    }

    fn next_is_item_keyword(&self) -> bool {
        matches!(
            self.nth_kind(1),
            Some(TokenKind::Use)
                | Some(TokenKind::Const)
                | Some(TokenKind::Fn)
                | Some(TokenKind::Actor)
                | Some(TokenKind::Entry)
                | Some(TokenKind::Cap)
        )
    }

    fn nth_kind(&self, offset: usize) -> Option<&TokenKind> {
        self.tokens
            .get(self.cursor + offset)
            .map(|token| &token.kind)
    }

    fn at_actor_start(&self) -> bool {
        self.at_actor() || (self.at_entry() && matches!(self.nth_kind(1), Some(TokenKind::Actor)))
    }

    fn at_actor(&self) -> bool {
        matches!(self.current().kind, TokenKind::Actor)
    }

    fn at_arrow(&self) -> bool {
        matches!(self.current().kind, TokenKind::Arrow)
    }

    fn at_cap(&self) -> bool {
        matches!(self.current().kind, TokenKind::Cap)
    }

    fn at_bang_eq(&self) -> bool {
        matches!(self.current().kind, TokenKind::BangEq)
    }

    fn at_colon(&self) -> bool {
        matches!(self.current().kind, TokenKind::Colon)
    }

    fn at_colon_colon(&self) -> bool {
        matches!(self.current().kind, TokenKind::ColonColon)
    }

    fn at_comma(&self) -> bool {
        matches!(self.current().kind, TokenKind::Comma)
    }

    fn at_const(&self) -> bool {
        matches!(self.current().kind, TokenKind::Const)
    }

    fn at_dot(&self) -> bool {
        matches!(self.current().kind, TokenKind::Dot)
    }

    /// PR AF: predicate for `..` (the range operator) used in slice
    /// syntax `&arr[lo..hi]`. Distinct from `at_dot_dot_eq()` (the
    /// `..=` inclusive-range token).
    fn at_dot_dot(&self) -> bool {
        matches!(self.current().kind, TokenKind::DotDot)
    }

    fn at_enum(&self) -> bool {
        matches!(self.current().kind, TokenKind::Enum)
    }

    fn at_extern(&self) -> bool {
        matches!(self.current().kind, TokenKind::Extern)
    }

    fn at_for(&self) -> bool {
        matches!(self.current().kind, TokenKind::For)
    }

    fn at_entry(&self) -> bool {
        matches!(self.current().kind, TokenKind::Entry)
    }

    fn at_else(&self) -> bool {
        matches!(self.current().kind, TokenKind::Else)
    }

    fn at_expr_start(&self) -> bool {
        matches!(
            self.current().kind,
            TokenKind::Ident(_)
                | TokenKind::BoolLit(_)
                | TokenKind::IntLit(_)
                | TokenKind::IntLit256(_)
                | TokenKind::FloatLit(_)
                | TokenKind::StrLit(_)
                | TokenKind::FStrBegin
                | TokenKind::Spawn
                | TokenKind::LBracket
                | TokenKind::Fn
                | TokenKind::Ampersand
                | TokenKind::Grant
                | TokenKind::Handle
                | TokenKind::Declassify
                | TokenKind::Region
        )
    }

    fn at_timeout_label(&self) -> bool {
        matches!(self.current().kind, TokenKind::Ident(ref name) if name == "timeout")
    }

    fn at_eq_eq(&self) -> bool {
        matches!(self.current().kind, TokenKind::EqEq)
    }

    fn at_eq(&self) -> bool {
        matches!(self.current().kind, TokenKind::Eq)
    }

    fn at_fat_arrow(&self) -> bool {
        matches!(self.current().kind, TokenKind::FatArrow)
    }

    fn at_eof(&self) -> bool {
        matches!(self.current().kind, TokenKind::Eof)
    }

    fn at_fn(&self) -> bool {
        matches!(self.current().kind, TokenKind::Fn)
    }

    fn at_gt(&self) -> bool {
        matches!(self.current().kind, TokenKind::Gt)
    }

    fn at_gt_eq(&self) -> bool {
        matches!(self.current().kind, TokenKind::GtEq)
    }

    fn at_gt_gt(&self) -> bool {
        matches!(self.current().kind, TokenKind::GtGt)
    }

    fn at_if(&self) -> bool {
        matches!(self.current().kind, TokenKind::If)
    }

    fn at_impl(&self) -> bool {
        matches!(self.current().kind, TokenKind::Impl)
    }

    fn at_init(&self) -> bool {
        matches!(self.current().kind, TokenKind::Init)
    }

    fn at_lbrace(&self) -> bool {
        matches!(self.current().kind, TokenKind::LBrace)
    }

    fn at_lbracket(&self) -> bool {
        matches!(self.current().kind, TokenKind::LBracket)
    }

    fn at_lparen(&self) -> bool {
        matches!(self.current().kind, TokenKind::LParen)
    }

    fn at_lt(&self) -> bool {
        matches!(self.current().kind, TokenKind::Lt)
    }

    fn at_lt_eq(&self) -> bool {
        matches!(self.current().kind, TokenKind::LtEq)
    }

    fn at_lt_lt(&self) -> bool {
        matches!(self.current().kind, TokenKind::LtLt)
    }

    fn at_let(&self) -> bool {
        matches!(self.current().kind, TokenKind::Let)
    }

    fn at_minus(&self) -> bool {
        matches!(self.current().kind, TokenKind::Minus)
    }

    fn at_module(&self) -> bool {
        matches!(self.current().kind, TokenKind::Module)
    }

    fn at_match(&self) -> bool {
        matches!(self.current().kind, TokenKind::Match)
    }

    fn at_plus(&self) -> bool {
        matches!(self.current().kind, TokenKind::Plus)
    }

    fn at_star(&self) -> bool {
        matches!(self.current().kind, TokenKind::Star)
    }

    fn at_slash(&self) -> bool {
        matches!(self.current().kind, TokenKind::Slash)
    }

    fn at_percent(&self) -> bool {
        matches!(self.current().kind, TokenKind::Percent)
    }

    fn at_ampersand(&self) -> bool {
        matches!(self.current().kind, TokenKind::Ampersand)
    }

    fn at_and_and(&self) -> bool {
        matches!(self.current().kind, TokenKind::AndAnd)
    }

    fn at_pipe(&self) -> bool {
        matches!(self.current().kind, TokenKind::Pipe)
    }

    fn at_or_or(&self) -> bool {
        matches!(self.current().kind, TokenKind::OrOr)
    }

    fn at_on(&self) -> bool {
        matches!(self.current().kind, TokenKind::On)
    }

    fn at_pub(&self) -> bool {
        matches!(self.current().kind, TokenKind::Pub)
    }

    fn at_question(&self) -> bool {
        matches!(self.current().kind, TokenKind::Question)
    }

    fn at_record(&self) -> bool {
        matches!(self.current().kind, TokenKind::Record)
    }

    fn at_rbrace(&self) -> bool {
        matches!(self.current().kind, TokenKind::RBrace)
    }

    fn at_trait(&self) -> bool {
        matches!(self.current().kind, TokenKind::Trait)
    }

    fn at_rbracket(&self) -> bool {
        matches!(self.current().kind, TokenKind::RBracket)
    }

    fn at_rparen(&self) -> bool {
        matches!(self.current().kind, TokenKind::RParen)
    }

    fn at_semicolon(&self) -> bool {
        matches!(self.current().kind, TokenKind::Semicolon)
    }

    fn at_mut(&self) -> bool {
        matches!(self.current().kind, TokenKind::Mut)
    }

    fn at_return(&self) -> bool {
        matches!(self.current().kind, TokenKind::Return)
    }

    fn at_state(&self) -> bool {
        matches!(self.current().kind, TokenKind::State)
    }

    fn at_type(&self) -> bool {
        matches!(self.current().kind, TokenKind::Type)
    }

    fn at_use(&self) -> bool {
        matches!(self.current().kind, TokenKind::Use)
    }

    fn at_while(&self) -> bool {
        matches!(self.current().kind, TokenKind::While)
    }

    fn is_eof(&self) -> bool {
        self.at_eof()
    }
}
