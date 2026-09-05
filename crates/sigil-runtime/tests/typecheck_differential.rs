//! Differential test for the SIGIL type-checker (`selfhost/typecheck.sigil`),
//! PR-4c: binary int-literal pinning.
//!
//! Mirrors `parser_differential.rs`: lexer + parser + typecheck inline into one
//! SIGIL tool (`lex -> parse -> typecheck -> encode`), executed per fixture, and
//! the emitted span-keyed type stream (one record per function return type + one
//! per typed expression — the Option-A differential) is compared against the
//! Rust oracle (`type_check::check_with_options`). Each record is
//! `start,end,tag,name` — `name` is the record name for Named types (tag 9),
//! empty for scalars. PR-3b/3c/3d added field access, record construction, and
//! enums. PR-4a/4b added if/while/assign control flow and `match`. PR-4c fixes
//! BINARY INT-LITERAL PINNING: when one operand of a comparison or arithmetic op
//! is a bare integer literal and the other is concrete-typed, the literal is
//! pinned to that concrete int type (e.g. `v < 0` with `v: i32` types `0` as i32),
//! matching the oracle's IntLit unification. Enum-variant payload bindings
//! (`Opt::Some(x)`) and malformed-corpus T-code parity (ET-T3) land in later PRs.
//!
//! Oracle note: the differential runs the POST-IntLit-pass entry
//! (`check_with_options`), NOT `check_collecting` — the latter leaves integer
//! literals as `Type::IntLit(_)` (pre-post-pass), which would put a surviving
//! IntLit in the type stream (ET-T4 forbids that). PR-0's return-type slice is
//! itself post-pass-agnostic (return types are explicit annotations), but the
//! entry is fixed now so the epic's type stream is concrete from the start.

use sigil_compiler::CompileOptions;
use sigil_compiler::air::mangle_type;
use sigil_compiler::ast::{Item, Program};
use sigil_compiler::compile_tool;
use sigil_compiler::diagnostics::{Diagnostic, Severity};
use sigil_compiler::source::SourceFile;
use sigil_compiler::type_check::{Type, TypedExpr, TypedExprKind, TypedStmt};
use sigil_compiler::{name_resolution, parser, type_check};
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// The crystallized core-owned T-code set (the monomorphic slice of the 138 total
/// codes; ET-T1's `MIN_COVERED` floor). The diagnostic differential compares only
/// these codes — out-of-core codes (generics/traits/refinement/cap/region) are not
/// the monomorphic checker's responsibility. PR-5a emits the expected-known
/// mismatch subset {T041,T045,T049,T050,T051}; PR-5b..5d grow the SIGIL side to the
/// rest. The oracle side filters to this full set from the start, so a fixture that
/// trips an unimplemented core code fails parity loudly rather than silently.
const CORE_CODES: &[&str] = &[
    "T041", "T044", "T045", "T046", "T049", "T050", "T051", "T054", "T055", "T060", "T062", "T070",
    "T071", "T087", "T088", "T120",
    "T190", // PR-6a: monomorphic trait declaration-time coherence.
    "T248", "T249",
    "T250", // PR-6b: call-site bound satisfaction (built-in table + structural derive).
    "T245", "T246",
    "T150", // PR-G1a: generic free fn — return type-param could not be inferred.
    "T233", // PR-G2a-ii: generic-record construction — type-param unbound by fields.
    "T234", // PR-G2a-iii: generic-record construction — conflicting field inferences.
    "T236", // PR-G2b-iii: ambiguous bare enum variant (name in ≥2 in-scope enums).
    "T262", // PR-E3a: f-string interpolation hole is not `str` (no Display yet).
];

const LEXER: &str = include_str!("../../../selfhost/lexer.sigil");
const PARSER: &str = include_str!("../../../selfhost/parser.sigil");
const TYPECHECK: &str = include_str!("../../../selfhost/typecheck.sigil");

const FUEL: u64 = 300_000_000;

/// Lexer + parser + typecheck inlined into one tool (their `module …;` lines
/// stripped). Every typecheck symbol is `tc_`/`TC_`-prefixed, every parser
/// symbol `parser_`/`P_`/`PNode`-prefixed, so the merged namespace is
/// collision-free by construction.
fn tc_tool(body: &str) -> String {
    let lexer_defs = LEXER.replace("\nmodule lexer;\n", "\n");
    let parser_defs = PARSER.replace("\nmodule parser;\n", "\n");
    let tc_defs = TYPECHECK.replace("\nmodule typecheck;\n", "\n");
    format!(
        "module tool;\n{lexer_defs}\n{parser_defs}\n{tc_defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// The type-check differential body: src -> lex -> parse -> typecheck -> encode.
fn tc_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = tc_encode(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

/// The tool's wasm, compiled ONCE (the body is fixed; only the input varies).
fn tc_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        compile_tool(&tc_tool(tc_body()))
            .expect("typecheck tool should compile")
            .wasm
    })
}

/// The TOTAL `Type` -> tag map (ET-T6 drift-lock: no `_` arm — a new `Type`
/// variant fails to compile until mapped here). The SIGIL `TC_T_*` constants are
/// the twin; PR-0 only exercises the scalar + Unit tags.
fn type_tag(ty: &Type) -> i64 {
    match ty {
        Type::Unit => 0,
        Type::Bool => 1,
        Type::I32 => 2,
        Type::U32 => 3,
        Type::I64 => 4,
        Type::U64 => 5,
        Type::F64 => 6,
        Type::Str => 7,
        Type::Generic(_) => 8,
        Type::Named(_, _) => 9,
        Type::Cap(_, _) => 10,
        Type::ActorRef(_) => 11,
        Type::Array { .. } => 12,
        Type::Fn(_, _, _, _) => 13,
        Type::Ref(_, _) => 14,
        Type::Slice(_) => 15,
        Type::Ptr(_) => 16,
        Type::MutPtr(_) => 17,
        Type::Region => 18,
        Type::Tuple(_) => 19,
        Type::IntLit(_) => 20,
        Type::Error => 21,
        // u256/i256 (PR-U0/U1): tagged here only so this drift-locked map
        // compiles. The self-hosted typechecker twin does not know these types
        // yet (PR-U4, deferred), so no u256 fixture appears in the differential
        // corpus — these arms are never exercised at runtime until then.
        Type::U256 => 22,
        Type::I256 => 23,
        // HKT (higher-kinded types). Tagged here only so this drift-locked map
        // compiles; the self-hosted typechecker twin does not know these types
        // (self-hosted HKT parity is a deferred follow-on epic, AG-HK-S7), so no
        // HKT fixture appears in the differential corpus — these arms are never
        // exercised at runtime until then. `HktVar`/`HktApp`/`TypeCtor` are also
        // check-time-only and erase to `Type::Named` before AIR, so they never
        // reach an emitted typed-node stream regardless.
        Type::HktVar { .. } => 24,
        Type::HktApp { .. } => 25,
        Type::TypeCtor(_) => 26,
        // Typestate (Epic 1). Tagged here only so this drift-locked map compiles;
        // the self-hosted twin does not know state markers (self-hosted parity is
        // deferred, AG-TS-3), and `StateMarker` is check-time-only and erased by
        // `strip_state_args` before AIR, so it never reaches an emitted typed-node
        // stream — this arm is never exercised at runtime until then.
        Type::StateMarker(_) => 27,
        // Effect Handlers (EH3). Tagged here only so this drift-locked map
        // compiles; the self-hosted twin does not model effects/operations, and
        // `Never` is the abortive bottom — gated before AIR and confined to
        // operation return types — so it never reaches an emitted typed-node
        // stream. This arm is never exercised at runtime.
        Type::Never => 28,
    }
}

/// The record's 4th field (PR-5e): a recursive type-DETAIL string. Subsumes the
/// former `type_name` (which returned the bare Named name + "" for everything
/// else). Scalars emit
/// "" (unchanged — back-compatible with the whole pre-composite corpus); a Named
/// emits its bare name (== `type_name`); a COMPOSITE (Array/Tuple/Ref/Slice) emits
/// the compiler's `mangle_type` byte-for-byte, which the SIGIL `tc_tmangle` twin
/// must reproduce exactly. This is the only behavioural change vs `type_name`, and
/// it fires ONLY on composite tags — so ET-D4 holds (a 0-byte no-op until a
/// composite appears). The total `type_tag` (ET-T6) is untouched.
fn type_detail(ty: &Type) -> String {
    match ty {
        Type::Named(n, _) => n.clone(),
        Type::Array { .. } | Type::Tuple(_) | Type::Ref(..) | Type::Slice(_) => mangle_type(ty),
        // PR-C1: a cap-typed value's detail is the oracle's `render_type(Type::Cap)` —
        // the bare cap name when non-parametric (the C1 corpus), else positional
        // `Name(v0, v1, …)`. The self-hosted side emits the same via the bind's `detail`
        // (the bare name); deadline-bearing caps are deferred to C4 (out-of-core).
        Type::Cap(name, params) if params.is_empty() => name.clone(),
        Type::Cap(name, params) => {
            let vals = params
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!("{name}({vals})")
        }
        _ => String::new(),
    }
}

/// PR-G0 (ET-G2): the source spans of GENERIC functions (FnDefs with type-params).
/// A monomorphized instance in `module.functions` REUSES its generic source span
/// (`expressions.rs:1319`), so a function whose span is in this set is an instance,
/// not a concrete source fn — STRUCTURAL and instantiation-count-INDEPENDENT (a
/// generic instantiated exactly once still has a span equal to its generic def, even
/// without a span-collision). The oracle never emits the generic source itself
/// (`mod.rs:683`), so on the all-monomorphic pre-generics corpus this set is empty
/// and the filter is a no-op. PR-G3b joins generic-impl-method spans (below).
fn generic_source_spans(prog: &Program) -> std::collections::HashSet<(usize, usize)> {
    let mut spans = std::collections::HashSet::new();
    for item in prog.modules.iter().flat_map(|m| &m.items) {
        match item {
            Item::FnDef(f) if !f.type_params.is_empty() => {
                spans.insert((f.span.start, f.span.end));
            }
            // PR-G3b (ET-G2): every method of a GENERIC-TARGET impl (impl Box<T>) is a
            // generic source def — the oracle emits one monomorphized instance per
            // concrete type (Box__get__i64), each REUSING the method's source span. So
            // every function sharing a generic-impl-method span is an instance, filtered
            // here, exactly as for a generic free fn. A non-generic impl (impl P) has
            // empty `type_params` → its methods are NOT filtered (they emit once, at
            // parity — PR-G3a). A method-level `<U>` (T235) is OUT (oracle ICE).
            Item::ImplDef(impl_def) if !impl_def.type_params.is_empty() => {
                for method in &impl_def.methods {
                    spans.insert((method.span.start, method.span.end));
                }
            }
            _ => {}
        }
    }
    spans
}

/// Oracle: parse -> resolve -> type-check, then emit the same span-keyed records
/// the SIGIL side does — one per function return type + one per typed expression.
/// PR-G0: monomorphized generic INSTANCES are FILTERED (Option A, ET-G2) so both
/// sides compare only the concrete (non-generic) source slice; the generic
/// diagnostics still surface in `oracle_codes` (a separate channel).
fn oracle_records(src: &str) -> String {
    let source = SourceFile::new("<tc-diff>", src);
    let (ast, _diags) = parser::parse(&source);
    let resolved = name_resolution::resolve(&ast).expect("name resolution");
    let (typed, _registry) =
        type_check::check_with_options(&resolved, &CompileOptions::default()).expect("type-check");
    let gspans = generic_source_spans(&ast);
    let mut out: Vec<String> = Vec::new();
    for module in &typed.modules {
        for f in &module.functions {
            if gspans.contains(&(f.span.start, f.span.end)) {
                continue; // a monomorphized instance — filtered (ET-G2)
            }
            out.push(format!(
                "{},{},{},{};",
                f.span.start,
                f.span.end,
                type_tag(&f.ret),
                type_detail(&f.ret)
            ));
            for stmt in &f.body.statements {
                walk_stmt(stmt, &mut out);
            }
        }
    }
    out.join("")
}

/// Walk a typed statement, emitting a record for each value expression it
/// carries. PR-4b handles `return`, `let`, expression statements, simple
/// assignments (place + value), the `if`/`while` control-flow statements, and
/// `match` (scrutinee + each arm's guard + each arm body's statements — patterns
/// are not `TypedExpr` so they carry no record); `break`/`continue` carry no
/// expression. Any other statement kind fail-fasts (ET-T6 — never a silent skip)
/// until its PR adds an arm.
fn walk_stmt(stmt: &TypedStmt, out: &mut Vec<String>) {
    match stmt {
        TypedStmt::Return(r) => {
            if let Some(e) = &r.value {
                walk_expr(e, out);
            }
        }
        TypedStmt::Let(l) => walk_expr(&l.value, out),
        TypedStmt::Expr(es) => walk_expr(&es.expr, out),
        TypedStmt::Assign(a) => {
            walk_expr(&a.place, out);
            walk_expr(&a.value, out);
        }
        TypedStmt::If(i) => {
            walk_expr(&i.condition, out);
            for s in &i.then_branch.statements {
                walk_stmt(s, out);
            }
            for s in &i.else_branch.statements {
                walk_stmt(s, out);
            }
        }
        TypedStmt::While(w) => {
            walk_expr(&w.condition, out);
            for s in &w.body.statements {
                walk_stmt(s, out);
            }
        }
        TypedStmt::Match(m) => {
            walk_expr(&m.scrutinee, out);
            for arm in &m.arms {
                if let Some(g) = &arm.guard {
                    walk_expr(g, out);
                }
                for s in &arm.body.statements {
                    walk_stmt(s, out);
                }
            }
        }
        TypedStmt::Break(_) => {}
        TypedStmt::Continue(_) => {}
        other => panic!("PR-4b oracle walker: unhandled TypedStmt: {other:?}"),
    }
}

/// Emit `start,end,tag,name;` for a typed expression, then recurse into its
/// sub-expressions. PR-3d handles literals + variable refs (leaves, incl.
/// record-/enum-typed values), binary operators, calls, field access (recurse the
/// receiver, which shares the access span), record construction (recurse each
/// field-init value), and enum variant construction (recurse each payload value);
/// other expr kinds fail-fast.
fn walk_expr(e: &TypedExpr, out: &mut Vec<String>) {
    out.push(format!(
        "{},{},{},{};",
        e.span.start,
        e.span.end,
        type_tag(&e.ty),
        type_detail(&e.ty)
    ));
    match &e.kind {
        TypedExprKind::Literal(_) => {}
        TypedExprKind::Local(_) => {}
        TypedExprKind::Binary(b) => {
            walk_expr(&b.lhs, out);
            walk_expr(&b.rhs, out);
        }
        TypedExprKind::Call(c) => {
            for arg in &c.args {
                walk_expr(arg, out);
            }
        }
        TypedExprKind::FieldAccess(fa) => walk_expr(&fa.object, out),
        // PR-5e: a borrow `&x` / `&mut x` emits its own Ref/Slice record (above),
        // then recurses into the borrowed operand (which emits the operand's
        // record) — the SIGIL P_K_BORROW arm mirrors this two-record shape.
        TypedExprKind::Borrow(b) => walk_expr(&b.inner, out),
        // PR-5f: an array literal recurses each element; an index recurses the
        // Array-typed receiver then the index expression. A tuple literal desugars
        // to RecordConstruct, so it is covered by that arm below.
        TypedExprKind::ArrayLit(a) => {
            for el in &a.elements {
                walk_expr(el, out);
            }
        }
        TypedExprKind::Index(ix) => {
            walk_expr(&ix.array, out);
            walk_expr(&ix.index, out);
        }
        TypedExprKind::RecordConstruct(rc) => {
            for (_name, value) in &rc.fields {
                walk_expr(value, out);
            }
        }
        TypedExprKind::EnumConstruct(ec) => {
            for field in &ec.fields {
                walk_expr(field, out);
            }
        }
        // PR-E3 (Option 2b): an f-string emits its OWN `str` record (above), then
        // recurses each hole expression — a literal chunk carries no record. The
        // self-hosted `typecheck.sigil` FString arm mirrors this exact shape (no
        // concat-chain lowering at type-check; that happens at the pre-AIR pass,
        // which the differential never runs).
        TypedExprKind::FString(fs) => {
            use sigil_compiler::typed_ast::TypedFStringPart;
            for part in &fs.parts {
                if let TypedFStringPart::Hole(h) = part {
                    walk_expr(h, out);
                }
            }
        }
        other => panic!("PR-4b oracle walker: unhandled TypedExprKind: {other:?}"),
    }
}

/// Run the SIGIL tool and return the records section (before the `|`).
fn sigil_records(src: &str) -> String {
    let result = execute_ephemeral(tc_wasm(), src.as_bytes(), FUEL, &IoGrants::none())
        .expect("typecheck tool executes");
    let text = String::from_utf8(result.output).expect("tool output is UTF-8");
    let (recs, _pool) = text.split_once('|').expect("output has a | separator");
    recs.to_string()
}

/// Split a record stream into individual `start,end,tag,namelen` records and
/// sort: the differential compares the SET of span-keyed type records, so each
/// side may emit in its own traversal order.
fn sorted_recs(records: &str) -> Vec<String> {
    let mut v: Vec<String> = records
        .split(';')
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .collect();
    v.sort();
    v
}

/// Codes the differential compares WITH their byte span (a8 parity). The oracle
/// emits `code,start,end;` for these and the self-host emits the same via
/// `tc_push_diag_with_span`; all other core codes stay bare `code;`. Adding a
/// code here REQUIRES wiring its self-host emit site to carry the span, or the
/// arity mismatch fails the differential loudly (never silently).
const ADOPTED_SPAN_CODES: &[&str] = &["T120", "T062", "T070", "T190", "T060", "T236"];

/// The core-owned, Error-severity diagnostic codes in a diagnostic list, as
/// `Txxx;` entries — or `Txxx,start,end;` for codes in `ADOPTED_SPAN_CODES`
/// (PR-5a, ET-T3 exact-code parity; a8 adds span parity for adopted codes).
/// Warnings and out-of-core codes are dropped — the monomorphic checker is
/// judged only on the codes it owns.
fn collect_core_codes(diags: &[Diagnostic]) -> Vec<String> {
    diags
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .filter(|d| CORE_CODES.contains(&d.code().as_str()))
        .map(|d| {
            let c = d.code().as_str();
            match (ADOPTED_SPAN_CODES.contains(&c), d.span()) {
                (true, Some(s)) => format!("{c},{},{};", s.start, s.end),
                _ => format!("{c};"),
            }
        })
        .collect()
}

/// The oracle's core-owned diagnostic stream for `src`. Runs `check_collecting`
/// (which yields diagnostics even on a rejected program); a name-resolution
/// rejection is mapped first. A parse error means the fixture is out of scope for
/// type-code parity (the corpus is parse-clean) → empty.
fn oracle_codes(src: &str) -> String {
    let source = SourceFile::new("<tc-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    if pdiags.iter().any(|d| d.severity() == Severity::Error) {
        return String::new();
    }
    let codes = match name_resolution::resolve(&ast) {
        Err(rdiags) => collect_core_codes(&rdiags),
        Ok(resolved) => {
            let (_typed, _reg, diags) =
                type_check::check_collecting(&resolved, &CompileOptions::default());
            collect_core_codes(&diags)
        }
    };
    codes.join("")
}

/// The SIGIL checker's diagnostic section: the THIRD `|`-delimited field of the
/// tool output (`records|pool|diags`).
fn sigil_codes(src: &str) -> String {
    let result = execute_ephemeral(tc_wasm(), src.as_bytes(), FUEL, &IoGrants::none())
        .expect("typecheck tool executes");
    let text = String::from_utf8(result.output).expect("tool output is UTF-8");
    let mut parts = text.splitn(3, '|');
    let _recs = parts.next().unwrap_or("");
    let _pool = parts.next().unwrap_or("");
    parts.next().unwrap_or("").to_string()
}

/// Split a diagnostic stream into individual `Txxx` codes and sort — the
/// differential compares the SET of core-owned codes (ET-T3).
fn sorted_codes(stream: &str) -> Vec<String> {
    let mut v: Vec<String> = stream
        .split(';')
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .collect();
    v.sort();
    v
}

/// a8 teeth: the span-bearing comparison must distinguish a 1-byte span
/// difference and must not let a `code,start,end` entry collapse to a bare
/// `code` — proves the differential actually verifies adopted-code spans, not
/// just the code. (E1 from the ritual.)
#[test]
fn a8_span_parity_has_teeth() {
    assert_ne!(
        sorted_codes("T120,10,20;"),
        sorted_codes("T120,10,21;"),
        "span comparison must distinguish a 1-byte difference"
    );
    assert_ne!(
        sorted_codes("T120,10,20;"),
        sorted_codes("T120;"),
        "a span-bearing entry must not compare equal to the bare code"
    );
}

#[test]
fn pr_c0_cap_decl_is_inert_no_op() {
    // PR-C0 (caps-in-typecheck): the self-hosted typechecker now runs a cap-declaration
    // pre-pass (`tc_build_caps` over P_K_CAP_TYPE → a flat `TcCap` table) and reserves the
    // Cap type tag (TC_T_CAP=10) plus the cap logical-code band (TC_CAP_BASE). C0 emits NO
    // cap records yet (that is PR-C1), so a program that DECLARES caps must still produce a
    // record stream AND a core-code stream BYTE-IDENTICAL to the oracle: a `cap type` decl
    // is not a typed value, and the table is built-but-not-consulted (ET-CAP-5).
    //
    // This is the NON-STUB proof. The existing corpus (every other test below) has ZERO
    // `cap type` decls, so it only proves C0 is inert when the table is EMPTY. These
    // fixtures drive the pre-pass over cap-bearing input — the table is non-empty (incl. a
    // parametric cap, exercising `tc_build_caps`' arity counter) — and prove it does not
    // perturb the type stream. A regression (a stray cap record, or the decl derailing the
    // parse of the following fn) fails the records/codes diff loudly.
    let caps: &[&str] = &[
        // a non-parametric cap with one authority, declared but unused.
        "module m;\ncap type Fuel { Spend }\npub fn f(x: i64) -> i64 { return x; }\n",
        // a PARAMETRIC cap — exercises the arity counter (pnames=2) — still emits no record.
        "module m;\ncap type Approval(year: i64, month: i64) { Sign }\npub fn h(x: i64) -> i64 { return x; }\n",
        // multiple cap decls interleaved with a record + a body that reads a field, so the
        // source-order table build runs alongside the (unchanged) record/field typing.
        "module m;\ncap type A { X }\ncap type B(d: i64) { Y }\nrecord P { v: i64 }\npub fn k(p: P) -> i64 { return p.v; }\n",
        // a cap with many authorities — the table stores only the name + arity, so the
        // authority list is irrelevant to C0; still no record.
        "module m;\ncap type Big { A, B, C, D, E, F }\npub fn f(x: i64) -> i64 { return x; }\n",
        // a 3-param parametric cap (arity counter past 2).
        "module m;\ncap type T3(a: i64, b: i64, c: i64) { Z }\npub fn f(x: i64) -> i64 { return x; }\n",
        // a cap interleaved among an enum, a free fn, and an impl method — proves the
        // pre-pass walk and the emit-loop skip both ignore P_K_CAP_TYPE amid other items.
        "module m;\nenum E { A, B }\ncap type C1 { Go }\nrecord R { n: i64 }\nimpl R { fn get(self: R) -> i64 { return self.n; } }\npub fn f(r: R) -> i64 { return r.get(); }\n",
    ];
    for src in caps {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-C0: a cap decl must not perturb the record stream on {src:?}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-C0: a cap decl must not perturb the core-code stream on {src:?}"
        );
    }
}

#[test]
fn pr_c1_cap_value_records_match_oracle() {
    // PR-C1 (caps-in-typecheck, the minimal SH-RING unblock): a cap-typed param/return
    // emits a tag-10 record whose detail is the bare cap name — the oracle's
    // `render_type(Type::Cap)` for the non-parametric case. The self-hosted side binds a
    // cap param with `tag=TC_T_CAP, detail=<name>` and emits via `tc_push_rec_detail`; the
    // cap-return type emits its own tag-10 record. Both must match the oracle, and NO core
    // code fires (caps are out-of-core for the type checks — ET-CAP-8). Non-parametric
    // caps only; the deadline-bearing form pulls in C4's codes (deferred, out-of-core).
    let caps: &[&str] = &[
        // a cap param returned: TWO tag-10 records — the return type AND the `c` var-ref.
        "module m;\ncap type Fuel { Spend }\npub fn f(c: Fuel) -> Fuel { return c; }\n",
        // a different cap, proving the rendered name is not hardcoded.
        "module m;\ncap type Net { Send }\npub fn h(n: Net) -> Net { return n; }\n",
        // a cap declared alongside a record + a normal fn — the cap typing must not
        // perturb the ordinary record/scalar stream (the cap `c` is used exactly once).
        "module m;\ncap type Fuel { Spend }\nrecord P { v: i64 }\npub fn k(c: Fuel, p: P) -> Fuel { return c; }\n",
        // a cap-typed LET: `c2` binds as a cap (tag 10 + name detail) and its later use
        // emits `10,<name>`; the cap annotation is a valid type (no false T046).
        "module m;\ncap type Fuel { Spend }\npub fn f(c: Fuel) -> Fuel { let c2: Fuel = c; return c2; }\n",
    ];
    for src in caps {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-C1: cap-value record stream must match the oracle on {src:?}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-C1: cap-value core-code stream must match the oracle on {src:?}"
        );
    }
}

#[test]
fn pr_c1_cap_deferred_shapes_no_false_code() {
    // C1 covers cap let/param/return. Caps in CALL positions remain OUT-OF-CORE (the sig's
    // return type is not cap-aware): the call-result RECORD may diverge (the self-host
    // fail-softs to TC_UNHANDLED where the oracle has a `Type::Cap`), but the self-host MUST
    // NEVER emit a false core code — `sigil_codes ⊆ oracle_codes`. Soundness floor for the
    // deferred surface: `tc_check_assign` gates T071 on BOTH operands being concrete, and a
    // cap value/arg emits TC_UNHANDLED (non-concrete), so no cap shape manufactures a code.
    let deferred: &[&str] = &[
        // a cap passed as a call ARG + a cap call RESULT (the sig's return type is not
        // cap-aware in C1) — the call-result record is out-of-core, but no false code.
        "module m;\ncap type Fuel { Spend }\nfn id(c: Fuel) -> Fuel { return c; }\npub fn caller(c: Fuel) -> Fuel { return id(c); }\n",
    ];
    for src in deferred {
        let s = sorted_codes(&sigil_codes(src));
        let o = sorted_codes(&oracle_codes(src));
        for code in &s {
            assert!(
                o.contains(code),
                "PR-C1: self-host emitted a false core code {code:?} on a deferred cap shape {src:?} (oracle codes: {o:?})"
            );
        }
    }
}

#[test]
fn pr_match_field_scrutinee_match_oracle() {
    // A `match` / `if let` whose scrutinee is a NON-LOCAL expression (a record-field
    // access `b.opt`, or a call result `mk()`) must bind the matched variant payload
    // to its real type — fixing the prior false T060 (the payload was left unbound
    // because the field-access type-checked to TC_UNHANDLED, not the enum). The
    // build-time field-table now resolves a record/enum-typed field to its code, so
    // `b.opt : Opt` and the payload binds. Records + core-codes parity (NON-generic).
    let pos: &[&str] = &[
        // field-access scrutinee, i64 payload read (the AG-E6 repro).
        "module m;\nenum Opt { Some(i64), None }\nrecord Box { opt: Opt }\npub fn f(b: Box) -> i64 { match b.opt { Opt::Some(x) => { return x; }, Opt::None => { } } return 0; }\n",
        // if-let over a field-access scrutinee (PR-E2 desugar + this fix → AG-E6 closed).
        "module m;\nenum Opt { Some(i64), None }\nrecord Box { opt: Opt }\npub fn f(b: Box) -> i64 { if let Opt::Some(x) = b.opt { return x; } return 0; }\n",
        // str payload through a field-access scrutinee (the second concrete).
        "module m;\nenum Wr { W(str), E }\nrecord Box { w: Wr }\npub fn f(b: Box) -> str { match b.w { Wr::W(s) => { return s; }, Wr::E => { } } return \"\"; }\n",
        // call-result scrutinee (non-generic) — already worked; a regression guard.
        "module m;\nenum Opt { Some(i64), None }\nfn mk() -> Opt { return Opt::None; }\npub fn f() -> i64 { match mk() { Opt::Some(x) => { return x; }, Opt::None => { } } return 0; }\n",
        // impl-method-result scrutinee returning an enum.
        "module m;\nenum Opt { Some(i64), None }\nrecord Box { n: i64 }\nimpl Box { fn get(self: Box) -> Opt { return Opt::Some(self.n); } }\npub fn f(b: Box) -> i64 { match b.get() { Opt::Some(x) => { return x; }, Opt::None => { } } return 0; }\n",
    ];
    for src in pos {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "non-local-scrutinee record stream must match the oracle on {src:?}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "non-local-scrutinee core-code stream must match the oracle on {src:?}"
        );
    }

    // GENERIC-enum field / call-result scrutinee: the BASE enum resolves (so the
    // payload binds — NO false T060), but the concrete type-arg is not yet threaded
    // through a field access / call result, so the payload tag fail-softs to
    // TC_UNHANDLED where the oracle substitutes the concrete (AG-G19 follow-on:
    // "generic-Named value-flow"). The RECORDS therefore diverge (corpus-excluded),
    // but the CORE CODES must still match exactly — SIGIL emits no false positive.
    let neg_records_ok_codes: &[&str] = &[
        "module m;\nenum Opt<T> { Some(T), None }\nrecord Box { opt: Opt<i64> }\npub fn f(b: Box) -> i64 { match b.opt { Opt::Some(x) => { return x; }, Opt::None => { } } return 0; }\n",
        "module m;\nenum Opt<T> { Some(T), None }\nfn nx() -> Opt<i64> { return Opt::None; }\npub fn f() -> i64 { match nx() { Opt::Some(x) => { return x; }, Opt::None => { } } return 0; }\n",
    ];
    for src in neg_records_ok_codes {
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "generic non-local scrutinee must fail-soft (no false code) on {src:?}"
        );
    }

    // KNOWN REMAINING (separate follow-on, NOT this fix): a MULTI-LEVEL field access
    // scrutinee (`o.inner.opt`) still false-T060s — the self-hosted field-access typing
    // resolves only `local.field` (one level), not `(expr).field`, so the intermediate
    // `o.inner` is not recursively typed and `o.inner.opt` fail-softs to TC_UNHANDLED.
    // This is a PRE-EXISTING one-level-field-access limitation (not regressed here);
    // recursive field-access typing is a separate type-checker PR. Corpus-excluded.
}

#[test]
fn pr1a_return_expression_types_match_oracle() {
    // Five scalar return types, each `return <literal>`. `ru` returns an integer
    // literal in a u32 context: the oracle does NOT re-type the literal to u32 —
    // the return is a compatibility check, and the IntLit post-pass defaults the
    // unpinned literal to i64. So the SIGIL side must type that `5` as i64 too; a
    // naive "literal takes the return type" diverges here (this fixture is the
    // guard). Context-pinning to a non-i64 type comes via annotations in PR-1c.
    // `u` (no `->`) contributes only a Unit function record.
    let src = "module demo;\n\
               pub fn ri() -> i64 {\n    return 0;\n}\n\
               pub fn ru() -> u32 {\n    return 5;\n}\n\
               pub fn rb() -> bool {\n    return true;\n}\n\
               pub fn rs() -> str {\n    return \"hi\";\n}\n\
               pub fn rf() -> f64 {\n    return 1.5;\n}\n\
               pub fn u() {\n}\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL per-expression + per-function type stream must match the oracle"
    );
}

#[test]
fn pr1b_binary_operators_match_oracle() {
    // Arithmetic (Add, Mul) => operand type; comparison (Lt, Eq) => Bool; nested
    // `1 + 2 * 3` exercises precedence + recursion; `!true` desugars at parse
    // time to `true == false` (a Binary Eq over bool literals), so the SIGIL side
    // types it through the same binary path — no unary node exists.
    let src = "module demo;\n\
               pub fn add() -> i64 {\n    return 1 + 2;\n}\n\
               pub fn cmp() -> bool {\n    return 1 < 2;\n}\n\
               pub fn nest() -> i64 {\n    return 1 + 2 * 3;\n}\n\
               pub fn neq() -> bool {\n    return 1 == 2;\n}\n\
               pub fn nott() -> bool {\n    return !true;\n}\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL binary-operator type stream must match the oracle"
    );
}

#[test]
fn pr_e2_if_let_while_let_match_oracle() {
    // PR-E2 (ergonomics): `if let PATTERN = E { T } else { F }` desugars to
    // `match E { PATTERN => { T }, _ => { F } }`, and `while let PATTERN = E { B }`
    // to `while true { match E { PATTERN => { B }, _ => { break; } } }`. Because
    // BOTH parsers (Rust oracle + self-hosted) perform the SAME desugar, the typed
    // record stream + core-code stream must agree — proving the synthetic
    // wildcard / `true` / `break` / wrapping blocks carry no divergent type record
    // and the payload binding scopes + substitutes identically to a hand-written
    // `match`. The payload is read at two concretes (i64 and str) per arm shape.
    // The accept corpus broadened by the adversarial pass (5 lenses, 73 fixtures;
    // 69 parity-clean). LOCAL / param / literal scrutinees only — see AG-E6 below.
    let pos: &[&str] = &[
        // if-let with else, qualified variant, i64 payload read.
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { if let Opt::Some(x) = o { return x; } else { return 0; } }\n",
        // if-let with else, str payload (the second concrete).
        "module m;\nenum Box { Wrap(str), Empty }\npub fn f(o: Box) -> str { if let Box::Wrap(x) = o { return x; } else { return \"\"; } }\n",
        // if-let, NO else (synthesized empty `_` arm).
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { let mut n: i64 = 0; if let Opt::Some(x) = o { n = x; } return n; }\n",
        // bare-variant if-let (Some is unique to the single enum — no T236).
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { if let Some(x) = o { return x; } else { return 0; } }\n",
        // nested if-let — the inner bind scopes to the inner then-block only.
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt, q: Opt) -> i64 { if let Opt::Some(x) = o { if let Opt::Some(y) = q { return x + y; } } return 0; }\n",
        // while-let, i64 payload accumulate (synthetic `true` + break-on-mismatch).
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { let mut n: i64 = 0; while let Opt::Some(x) = o { n = n + x; } return n; }\n",
        // while-let, str payload.
        "module m;\nenum Box { Wrap(str), Empty }\npub fn f(o: Box) -> str { let mut s: str = \"\"; while let Box::Wrap(x) = o { s = x; } return s; }\n",
        // multi-payload variant: BOTH bindings (i64, str) scope to arm1.
        "module m;\nenum Two { Pair(i64, str), Nil }\npub fn f(t: Two) -> i64 { if let Two::Pair(a, b) = t { let s: str = b; return a; } else { return 0; } }\n",
        // payload-FREE variant pattern (binds nothing; the synth `_` covers Some).
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { if let Opt::None = o { return 1; } else { return 0; } }\n",
        // bool-literal pattern (bool scrutinee; the synth `_` catches false).
        "module m;\nenum E { A }\npub fn f(b: bool) -> i64 { if let true = b { return 1; } else { return 0; } }\n",
        // range pattern over i64, NO else.
        "module m;\nenum E { A }\npub fn f(n: i64) -> i64 { let mut c: i64 = 0; if let 1..=5 = n { c = 1; } return c; }\n",
        // string-literal pattern (param scrutinee), NO else.
        "module m;\nenum E { A }\npub fn f(s: str) -> i64 { let mut hit: i64 = 0; if let \"go\" = s { hit = 1; } return hit; }\n",
        // if-let chained via else (the else block is itself an if-let).
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt, p: Opt) -> i64 { if let Opt::Some(x) = o { return x; } else { if let Opt::Some(y) = p { return y; } else { return 0; } } }\n",
        // 3-deep nested if-let; a payload read at every level.
        "module m;\nenum Opt { Some(i64), None }\npub fn f(a: Opt, b: Opt, c: Opt) -> i64 { if let Opt::Some(x) = a { if let Opt::Some(y) = b { if let Opt::Some(z) = c { return x + y + z; } else { return x + y; } } else { return x; } } else { return 0; } }\n",
        // while-let, payload-FREE variant pattern.
        "module m;\nenum Tok { Plus, End }\npub fn f(t: Tok) -> i64 { let mut n: i64 = 0; while let Tok::Plus = t { n = n + 1; } return n; }\n",
        // while-let with a USER break inside an if/else, alongside the synth break.
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { let mut n: i64 = 0; while let Opt::Some(x) = o { n = n + x; if n > 10 { break; } else { } } return n; }\n",
        // while-let nested inside a plain while (inner break targets inner loop).
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { let mut n: i64 = 0; while n < 3 { while let Opt::Some(x) = o { n = n + x; } n = n + 1; } return n; }\n",
        // back-to-back if-lets (each no-else; bindings scope to their own arms).
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt, q: Opt) -> i64 { let mut n: i64 = 0; if let Opt::Some(x) = o { n = x; } if let Opt::Some(y) = q { n = n + y; } return n; }\n",
        // if-let in TAIL position of BOTH real match arms.
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt, p: Opt) -> i64 { match o { Opt::Some(x) => { if let Opt::Some(y) = p { return x + y; } else { return x; } }, Opt::None => { if let Opt::Some(z) = p { return z; } else { return 0; } } } }\n",
        // pattern / `=` / scrutinee / braces / else split across newlines.
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 {\n  if let Opt::Some(x)\n      =\n      o\n  {\n      return x;\n  }\n  else\n  {\n      return 0;\n  }\n}\n",
    ];
    for src in pos {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-E2 if-let/while-let record stream must match the oracle on {src:?}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-E2 if-let/while-let core-code stream must match the oracle on {src:?}"
        );
    }

    // Negatives: a type error reached THROUGH the desugared arm must fire the SAME
    // core code on both sides. Compared codes-only (a reject may perturb non-core
    // records / panic `oracle_records`). Codes confirmed identical (probe): payload
    // misuse -> T041, str-return -> T049, str-arith -> T054, missing-return -> T044,
    // scope-leak (payload not leaking past the arm) -> T060 — for if-let AND while-let.
    let neg: &[&str] = &[
        // payload bound i64, assigned to a str let inside the then-arm -> T041.
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { if let Opt::Some(x) = o { let y: str = x; return 0; } else { return 0; } }\n",
        // str payload returned where the fn returns i64 -> T049.
        "module m;\nenum Box { Wrap(str), Empty }\npub fn f(o: Box) -> i64 { if let Box::Wrap(x) = o { return x; } else { return 0; } }\n",
        // str payload in arithmetic -> T054.
        "module m;\nenum Box { Wrap(str), Empty }\npub fn f(o: Box) -> i64 { if let Box::Wrap(x) = o { return x + 1; } else { return 0; } }\n",
        // no-else if-let in value position: the synth empty `_` arm falls through -> T044.
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { if let Opt::Some(x) = o { return x; } }\n",
        // else-block returns str where the fn returns i64 -> T049 (the `_` arm is typed).
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { if let Opt::Some(x) = o { return x; } else { return \"no\"; } }\n",
        // payload x does NOT leak past the if-let -> T060 (undefined `x` after the arm).
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { if let Opt::Some(x) = o { return x; } return x; }\n",
        // while-let payload bound str, assigned to an i64 let in the loop body -> T041.
        "module m;\nenum Box { Wrap(str), Empty }\npub fn f(o: Box) -> i64 { while let Box::Wrap(s) = o { let n: i64 = s; } return 0; }\n",
        // while-let payload does NOT leak past the loop -> T060.
        "module m;\nenum Opt { Some(i64), None }\npub fn f(o: Opt) -> i64 { let mut n: i64 = 0; while let Opt::Some(x) = o { n = x; } return x; }\n",
    ];
    for src in neg {
        let sc = sorted_codes(&sigil_codes(src));
        assert_eq!(
            sc,
            sorted_codes(&oracle_codes(src)),
            "PR-E2 if-let reject must match the oracle's core codes on {src:?}"
        );
        assert!(
            !sc.is_empty(),
            "PR-E2 neg fixture must actually be rejected on {src:?}"
        );
    }

    // AG-E6 (adversarial pass) — RESOLVED for NON-GENERIC non-local scrutinees: the
    // build-time field-table now resolves a record/enum-typed field to its code, so a
    // field-access scrutinee (`b.opt : Opt`) and a non-generic call result bind the
    // matched payload — covered by `pr_match_field_scrutinee_match_oracle` (records +
    // codes parity, match AND if-let forms). REMAINING (AG-G19 follow-on): a GENERIC
    // non-local scrutinee (`b.opt: Opt<i64>`, `next() -> Opt<i64>`) resolves the BASE
    // enum (no false T060) but the concrete type-arg is not threaded through the field
    // access / call result, so the payload fail-softs to TC_UNHANDLED (records diverge,
    // codes still match — no false positive). Those generic forms stay corpus-excluded.
}

#[test]
fn pr_e3a_fstring_match_oracle() {
    // PR-E3a (Option 2b): an f-string `f"…{e}…"` TYPES as `str` and checks each hole.
    // BOTH type-checkers do this with NO stdlib linked (the concat-chain lowering is a
    // Rust-only pre-AIR pass the differential never runs), so the typed record stream +
    // core-code stream must agree: the FString node emits ONE `str` record at its span,
    // each hole emits its own record(s), and literal chunks emit none. Holes are `str`
    // only in PR-E3a (i64/bool auto-convert is PR-E3b); a known non-`str` hole → T262.
    let pos: &[&str] = &[
        // no holes — one (possibly empty) chunk, FString is `str`.
        "module m;\nfn f() -> str { return f\"hello\"; }\n",
        "module m;\nfn f() -> str { return f\"\"; }\n",
        // leading + trailing chunks around a str-var hole.
        "module m;\nfn f(s: str) -> str { return f\"a{s}b\"; }\n",
        // hole only (empty chunks both sides).
        "module m;\nfn f(s: str) -> str { return f\"{s}\"; }\n",
        // adjacent str holes (empty middle chunk).
        "module m;\nfn f(a: str, b: str) -> str { return f\"{a}{b}\"; }\n",
        // trailing literal text after the hole.
        "module m;\nfn f(s: str) -> str { return f\"id={s}!\"; }\n",
        // three str holes interleaved with text.
        "module m;\nfn f(a: str, b: str, c: str) -> str { return f\"{a}-{b}-{c}\"; }\n",
        // a str-typed FIELD-ACCESS hole (the hole is an expression, not just an ident).
        "module m;\nrecord R { name: str }\nfn f(r: R) -> str { return f\"hi {r.name}!\"; }\n",
        // assigned to a str let (not just returned) — value-position FString is `str`.
        "module m;\nfn f(s: str) -> str { let g: str = f\"<{s}>\"; return g; }\n",
        // escaped braces decode to a literal chunk (no hole) — still clean `str`.
        "module m;\nfn f() -> str { return f\"{{lit}}\"; }\n",
        // (adversarial pass) parenthesized str hole — the hole is a full expression.
        "module m;\nfn f(s: str) -> str { return f\"{(s)}\"; }\n",
        // (adversarial pass) internal whitespace in the hole.
        "module m;\nfn f(a: str, b: str) -> str { return f\"{  a  }{  b  }\"; }\n",
        // (adversarial pass) escaped \\n / \\t in chunks around a str hole.
        "module m;\nfn f(s: str) -> str { return f\"a\\nb{s}c\\td\"; }\n",
        // (adversarial pass) multi-byte UTF-8 immediately adjacent to the hole braces.
        "module m;\nfn f(s: str) -> str { return f\"café{s}日本\"; }\n",
        // PR-E3b: i64 + bool holes are now ACCEPTED (auto-convert via str_itoa /
        // str_of_bool at the pre-AIR pass) — the f-string types `str`, the hole keeps
        // its own i64/bool record, NO T262, at SIGIL/oracle parity.
        "module m;\nfn f(n: i64) -> str { return f\"x={n}\"; }\n",
        "module m;\nfn f(b: bool) -> str { return f\"{b}\"; }\n",
        "module m;\nfn f(n: i64, m: i64) -> str { return f\"{n}-{m}\"; }\n",
        "module m;\nfn f(s: str, n: i64, b: bool) -> str { return f\"{s}:{n}:{b}\"; }\n",
    ];
    for src in pos {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-E3a f-string record stream must match the oracle on {src:?}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-E3a f-string core-code stream must match the oracle on {src:?}"
        );
    }

    // Negatives: a hole whose type is NOT str/i64/bool is not stringifiable → T262 at
    // the f-string, on BOTH sides. (PR-E3b widened the accept set to i64/bool; f64 and
    // composites stay rejected.) Compared codes-only (the reject still type-checks the
    // holes, so records mostly agree, but follow the E2 pattern).
    let neg: &[&str] = &[
        // f64 param hole → T262 (no float Display).
        "module m;\nfn f(x: f64) -> str { return f\"{x}\"; }\n",
        // TWO f64 holes → two T262 (multiplicity parity).
        "module m;\nfn f(x: f64, y: f64) -> str { return f\"{x}-{y}\"; }\n",
        // mixed: a str hole (clean) + an f64 hole (T262) — only the f64 fires.
        "module m;\nfn f(s: str, x: f64) -> str { return f\"{s}={x}\"; }\n",
        // a record-typed hole → T262 (no Display for records).
        "module m;\nrecord P { v: i64 }\nfn f(p: P) -> str { return f\"{p}\"; }\n",
        // PR-E3b accepts i64 ONLY (str_itoa takes i64); other int widths stay T262 at
        // parity — the auto-convert is deliberately i64/bool/str, not all scalars.
        "module m;\nfn f(n: i32) -> str { return f\"{n}\"; }\n",
        "module m;\nfn f(n: u32) -> str { return f\"{n}\"; }\n",
    ];
    for src in neg {
        let sc = sorted_codes(&sigil_codes(src));
        assert_eq!(
            sc,
            sorted_codes(&oracle_codes(src)),
            "PR-E3a f-string reject must match the oracle's core codes on {src:?}"
        );
        assert!(
            sc.contains(&"T262".to_string()),
            "PR-E3a neg fixture must actually fire T262 on {src:?}"
        );
    }

    // (Adversarial pass) Error-suppression parity: a hole that ITSELF reports a type
    // error (e.g. an ill-typed comparison) is typed `Error` by the oracle, which then
    // does NOT pile on T262 — and the SIGIL checker mirrors this (it skips T262 when
    // the hole sub-expression already pushed a diagnostic). The only core code is the
    // hole's own (here T055), NEVER an extra T262. Pins the no-double-report fix.
    let err_holes: &[&str] =
        &["module m;\nfn f(a: i64, b: i64, c: i64) -> str { return f\"{a < b == c}\"; }\n"];
    for src in err_holes {
        let sc = sorted_codes(&sigil_codes(src));
        assert_eq!(
            sc,
            sorted_codes(&oracle_codes(src)),
            "PR-E3a errored-hole codes must match the oracle (no extra T262) on {src:?}"
        );
        assert!(
            !sc.contains(&"T262".to_string()),
            "PR-E3a errored hole must NOT also fire T262 (oracle suppresses it) on {src:?}"
        );
    }
}

#[test]
fn pr1c_let_bindings_and_annotations_match_oracle() {
    // ET-T2 dual target: the SAME literal `5` types U32 under a u32 annotation
    // (`la`) but I64 under an i64 annotation (`lb`) and with no annotation
    // (`lc`) — a "default-everything-to-i64" checker diverges on `la`. `ld`
    // propagates the u32 expectation through arithmetic to both operands; `le`
    // shows a comparison's operands stay i64 while its result is Bool. The let
    // variables are unused (variable USE needs the symbol table — PR-2.x).
    let src = "module demo;\n\
               pub fn f() -> i64 {\n\
               let la: u32 = 5;\n\
               let lb: i64 = 5;\n\
               let lc = 5;\n\
               let ld: u32 = 1 + 2;\n\
               let le: bool = 1 < 2;\n\
               let lg: bool = true;\n\
               return 0;\n\
               }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL let-binding type stream must match the oracle"
    );
}

#[test]
fn pr2a_variable_references_match_oracle() {
    // Variable references resolve through the per-function symbol table:
    // `ref_basic`/`ref_u32` return a bound variable (the ref takes the binding's
    // type, u32 included — not a default); `ref_as_rhs` uses a variable as a let
    // RHS; `var_arith`/`var_cmp` combine two same-typed variables (no
    // literal/variable unification — that is deferred); `shadow` rebinds a name
    // in the same scope (most-recent wins).
    let src = "module demo;\n\
               pub fn ref_basic() -> i64 { let x: i64 = 5; return x; }\n\
               pub fn ref_u32() -> u32 { let x: u32 = 5; return x; }\n\
               pub fn ref_as_rhs() -> i64 { let x: i64 = 5; let y: i64 = x; return y; }\n\
               pub fn var_arith() -> i64 { let a: i64 = 2; let b: i64 = 3; return a + b; }\n\
               pub fn var_cmp() -> bool { let a: i64 = 1; let b: i64 = 2; return a < b; }\n\
               pub fn shadow() -> i64 { let x: i64 = 1; let x: i64 = 2; return x; }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL variable-reference type stream must match the oracle"
    );
}

#[test]
fn pr2b_function_parameters_match_oracle() {
    // Parameters seed the body's symbol table: refs to params type by the param
    // type (u32 params stay u32, not the i64 default); `withlocal` mixes a param
    // and a local; `shadowparam` shadows a param with a local `let` (most-recent
    // wins); params appear in arithmetic and comparison. No calls yet (PR-2c).
    let src = "module demo;\n\
               pub fn add(a: i64, b: i64) -> i64 { return a + b; }\n\
               pub fn addu(a: u32, b: u32) -> u32 { return a + b; }\n\
               pub fn pick(a: i64, b: i64) -> i64 { return a; }\n\
               pub fn cmp(a: i64, b: i64) -> bool { return a < b; }\n\
               pub fn ident(s: str) -> str { return s; }\n\
               pub fn withlocal(a: i64) -> i64 { let b: i64 = a; return a + b; }\n\
               pub fn shadowparam(a: i64) -> i64 { let a: i64 = 5; return a; }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL function-parameter type stream must match the oracle"
    );
}

#[test]
fn pr2c_function_calls_match_oracle() {
    // A call types as the callee's return type; an argument literal is pinned by
    // the parameter type (`idu(5)` with a u32 param => the 5 is U32, not the i64
    // default); args may be variables; calls nest (`add(id(1), 2)`); a forward
    // reference (`fwd` calls `later` defined after it) resolves via the pre-pass
    // signature table.
    let src = "module demo;\n\
               fn id(x: i64) -> i64 { return x; }\n\
               fn idu(x: u32) -> u32 { return x; }\n\
               fn add(a: i64, b: i64) -> i64 { return a + b; }\n\
               pub fn call_lit() -> i64 { return id(5); }\n\
               pub fn call_u32() -> u32 { return idu(5); }\n\
               pub fn call_var() -> i64 { let y: i64 = 3; return id(y); }\n\
               pub fn call_two() -> i64 { return add(1, 2); }\n\
               pub fn call_nest() -> i64 { return add(id(1), 2); }\n\
               pub fn fwd() -> i64 { return later(7); }\n\
               fn later(x: i64) -> i64 { return x; }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL function-call type stream must match the oracle"
    );
}

/// Adversarial fixtures from the pr2c-adversarial-calls workflow — self/mutual
/// recursion, forward-ref chains, six-param positional arg pinning, the
/// function-vs-local namespace collision, calls in every expression position.
/// Each that the oracle ACCEPTS must match the SIGIL stream; oracle-rejected
/// fixtures (out of the PR-2c call scope) are logged and skipped.
#[test]
fn pr2c_adversarial_fixtures_match_oracle() {
    let fixtures: &[&str] = &[
        "module demo; fn loopi(x: i64) -> i64 { return loopi(x); }",
        "module demo; fn r(n: u32) -> u32 { let y: u32 = r(5); return y; }",
        "module demo; fn ping(a: i64) -> i64 { return pong(a); } fn pong(b: i64) -> i64 { return ping(b); }",
        "module demo; pub fn caller() -> u32 { return callee(9); } fn callee(x: u32) -> u32 { return x; }",
        "module demo; fn f(x: i64) -> i64 { return g(x); } fn g(x: i64) -> i64 { return h(x); } fn h(x: i64) -> i64 { return leaf(x); } fn leaf(x: i64) -> i64 { return x; }",
        "module demo; fn ev(n: u32) -> bool { return od(n); } fn od(n: u32) -> bool { let r: u32 = sub1(n); return ev(r); } fn sub1(x: u32) -> u32 { return x; }",
        "module demo; fn tb(p: bool) -> bool { return p; } fn ts(p: str) -> str { return p; } fn tf(p: f64) -> f64 { return p; } fn ti32(p: i32) -> i32 { return p; } fn tu64(p: u64) -> u64 { return p; } fn tu32(p: u32) -> u32 { return p; } fn ti64(p: i64) -> i64 { return p; } pub fn cb() -> bool { return tb(true); } pub fn cs() -> str { return ts(\"hi\"); } pub fn cf() -> f64 { return tf(1.5); } pub fn ci32() -> i32 { return ti32(7); } pub fn cu64() -> u64 { return tu64(9); } pub fn cu32() -> u32 { return tu32(5); } pub fn ci64() -> i64 { return ti64(3); }",
        "module demo; fn mix(a: u32, b: i32, c: bool, d: str, e: f64, f: u64) -> u64 { return f; } pub fn call_mix() -> u64 { return mix(5, 7, true, \"x\", 1.5, 9); }",
        "module demo; fn wu(p: u32) -> u32 { return p; } fn wi(p: i64) -> i64 { return p; } pub fn f() -> i64 { let a: u32 = wu(5); let b: i64 = wi(5); return b; }",
        "module demo; fn innr(x: i32) -> i32 { return x; } fn outr(a: i32, b: u32) -> i32 { return a; } pub fn f() -> i32 { return outr(innr(100), 200); }",
        "module demo; fn three(a: f64, b: str, c: bool) -> bool { return c; } pub fn f() -> bool { return three(2.5, \"yo\", false); }",
        "module demo; fn pi32(p: i32) -> i32 { return p; } fn pu32(p: u32) -> u32 { return p; } fn pu64(p: u64) -> u64 { return p; } fn pi64(p: i64) -> i64 { return p; } pub fn f() -> i64 { let a: i32 = pi32(2147483647); let b: u32 = pu32(4294967295); let c: u64 = pu64(0); let d: i64 = pi64(9000000000); return d; }",
        "module demo; fn gu(p: u32) -> u32 { return p; } fn gi(p: i64) -> i64 { return p; } pub fn f() -> u32 { let x: i64 = gi(42); let y: u32 = gu(8); return y; }",
        "module demo; pub fn f() -> u32 { let y: u32 = idu(5); return y; } fn idu(x: u32) -> u32 { return x; }",
        "module demo; fn mk() -> u32 { return 7; } pub fn f() -> u32 { let a: u32 = mk(); let mk: u32 = a; return mk; }",
        "module demo; fn one() -> u32 { return 1; } fn two() -> u32 { return 2; } pub fn f() -> u32 { return one() + two(); }",
        "module demo; fn lo() -> u32 { return 1; } fn hi() -> u32 { return 2; } pub fn f() -> bool { return lo() < hi(); }",
        "module demo; fn idu(x: u32) -> u32 { return x; } fn addu(a: u32, b: u32) -> u32 { return a + b; } pub fn f() -> u32 { return addu(idu(1), idu(2)); }",
        "module demo; fn idu(x: u32) -> u32 { return x; } pub fn f(p: u32) -> u32 { return idu(p); }",
        "module demo; fn idu(x: u32) -> u32 { return x; } pub fn f() -> u32 { let a: u32 = 3; let b: u32 = 4; return idu(a + b); }",
        "module demo; fn times2(x: i64) -> i64 { return x + x; } fn times3(x: i64) -> i64 { return x + x + x; } pub fn pick() -> i64 { return times2(5); } pub fn altcall() -> i64 { return times3(7); }",
        "module demo; fn id(x: i64) -> i64 { return x; } pub fn letcall() -> i64 { let y: i64 = id(5); return y; }",
        "module demo; fn split(a: u32, b: i64) -> bool { return a < b; } pub fn mixargs() -> bool { return split(7, 100); }",
        "module demo; fn double(x: i64) -> i64 { return x + x; } pub fn arithcall() -> i64 { return double(3) + 5; }",
        "module demo; fn self_ref(x: i64) -> i64 { return self_ref(x); } pub fn f() -> i64 { return self_ref(5); }",
        "module demo; fn first(x: i64) -> i64 { return second(x); } fn second(x: i64) -> i64 { return x; } pub fn fwd_chain() -> i64 { return first(7); }",
        "module demo; fn id(x: i64) -> i64 { return x; } fn add(a: i64, b: i64) -> i64 { return a + b; } pub fn triplenest() -> i64 { return add(id(add(1, 2)), id(3)); }",
        "module demo; fn mix(a: u32, b: i64) -> i64 { return b; } pub fn litvar() -> i64 { let x: i64 = 100; return mix(5, x); }",
    ];
    let mut mismatches: Vec<String> = Vec::new();
    let mut rejects: Vec<usize> = Vec::new();
    for (i, src) in fixtures.iter().enumerate() {
        match oracle_graceful(src) {
            None => rejects.push(i),
            Some(orc) => {
                let sig = sigil_records(src);
                if sorted_recs(&sig) != sorted_recs(&orc) {
                    mismatches.push(format!(
                        "[{i}] {src}\n    sigil:  {:?}\n    oracle: {:?}",
                        sorted_recs(&sig),
                        sorted_recs(&orc)
                    ));
                }
            }
        }
    }
    if !rejects.is_empty() {
        eprintln!(
            "pr2c adversarial: {} oracle-rejected (out of call scope): {rejects:?}",
            rejects.len()
        );
    }
    assert!(
        mismatches.is_empty(),
        "adversarial call fixtures diverged from the oracle:\n{}",
        mismatches.join("\n")
    );
}

#[test]
fn pr3a_record_types_match_oracle() {
    // Record types: a record-typed value emits as Named (tag 9) + the record NAME
    // (Point vs Line distinguished — ET-T4). A record param is `@ReadOnly` and
    // cannot be returned (T253), so it is exercised by being PASSED as a call
    // argument — the arg reference types as Named(record). `use2` passes two
    // distinct record types. Field access + construction land in PR-3b/PR-3c.
    let src = "module demo;\n\
               record Point { x: i64, y: i64 }\n\
               record Line { a: i64, b: i64 }\n\
               record Tri { a: i64, b: i64, c: i64 }\n\
               fn consume(p: Point) -> i64 { return 0; }\n\
               fn consume2(a: Point, b: Line) -> i64 { return 0; }\n\
               fn mixc(n: i64, p: Point) -> i64 { return n; }\n\
               fn takeTri(t: Tri) -> i64 { return 0; }\n\
               pub fn use1(p: Point) -> i64 { return consume(p); }\n\
               pub fn use2(p: Point, q: Line) -> i64 { return consume2(p, q); }\n\
               pub fn use3(p: Point) -> i64 { return mixc(5, p); }\n\
               pub fn use4(t: Tri) -> i64 { return takeTri(t); }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL record-type stream must match the oracle"
    );
}

#[test]
fn pr3b_field_access_match_oracle() {
    // Field access `p.x` (parsed as a dotted K_PATH "p::x"): the receiver and the
    // access share the SAME span — the receiver types as Named(record), the
    // access as the field's type. Reads i64/u32/bool/str/f64 fields; a field in
    // arithmetic + comparison; two records with distinct field types.
    let src = "module demo;\n\
               record Point { x: i64, y: u32 }\n\
               record Flags { flag: bool, label: str, ratio: f64 }\n\
               pub fn gx(p: Point) -> i64 { return p.x; }\n\
               pub fn gy(p: Point) -> u32 { return p.y; }\n\
               pub fn gflag(f: Flags) -> bool { return f.flag; }\n\
               pub fn glabel(f: Flags) -> str { return f.label; }\n\
               pub fn gratio(f: Flags) -> f64 { return f.ratio; }\n\
               pub fn sumx(p: Point, q: Point) -> i64 { return p.x + q.x; }\n\
               pub fn cmpx(p: Point, q: Point) -> bool { return p.x < q.x; }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL field-access type stream must match the oracle"
    );
}

#[test]
fn pr3c_record_construction_match_oracle() {
    // Record construction `Name { f: v, … }`: the construction emits Named(record)
    // at its span; each field-init value is typed with the field's declared type
    // as expected — so a literal pins to the field's type (`y: 2` in a `y: u32`
    // field types `2` as u32, NOT i64). Returned fresh (no T253), let-bound,
    // built from params, out-of-source-order fields, and every scalar field type.
    let src = "module demo;\n\
               record Point { x: i64, y: u32 }\n\
               record Bag { a: i64, b: f64, c: bool, d: str }\n\
               pub fn make(k: i64) -> Point { return Point { x: k, y: 2 }; }\n\
               pub fn lit() -> Point { return Point { x: 1, y: 7 }; }\n\
               pub fn reorder() -> Point { return Point { y: 9, x: 4 }; }\n\
               pub fn bag() -> Bag { return Bag { a: 5, b: 2.5, c: true, d: \"hi\" }; }\n\
               pub fn viaLet() -> i64 { let p: Point = Point { x: 3, y: 1 }; return p.x; }\n\
               pub fn fieldof() -> u32 { let p: Point = Point { x: 0, y: 8 }; return p.y; }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL record-construction type stream must match the oracle"
    );
}

#[test]
fn pr3d_enums_match_oracle() {
    // Enums: an enum type is Named(enum) (same tag-9 encoding as records). A
    // variant construction types as Named(enum) at its span — a UNIT variant
    // (`Color::Red`, a dotted K_PATH) emits one record; a PAYLOAD variant
    // (`Opt::Some(5)`, a K_METHOD on `Enum::Variant`) emits Named(enum) + each
    // payload arg typed WITHOUT expectation (so a u32-payload literal stays i64,
    // unlike a record field-init). Fresh constructions are returned (T253 only
    // bites a returned enum PARAM, so params are consumed as call args instead).
    let src = "module demo;\n\
               enum Color { Red, Green, Blue }\n\
               enum Opt { None, Some(i64) }\n\
               enum Box1 { E, V(u32) }\n\
               enum Sh { Dot, Pair(i64, i64) }\n\
               fn useColor(c: Color) -> i64 { return 0; }\n\
               pub fn pick() -> Color { return Color::Red; }\n\
               pub fn pick2() -> Color { return Color::Blue; }\n\
               pub fn none() -> Opt { return Opt::None; }\n\
               pub fn wrap(n: i64) -> Opt { return Opt::Some(n); }\n\
               pub fn wlit() -> Opt { return Opt::Some(5); }\n\
               pub fn boxu() -> Box1 { return Box1::V(7); }\n\
               pub fn pair() -> Sh { return Sh::Pair(1, 2); }\n\
               pub fn consume() -> i64 { return useColor(Color::Green); }\n\
               pub fn viaLet() -> i64 { let c: Color = Color::Red; return useColor(c); }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL enum/variant type stream must match the oracle"
    );
}

#[test]
fn pr4a_control_flow_match_oracle() {
    // Control flow: `if`/`while` are statements (no value). The CONDITION is a
    // bool expr; the branch/body statements recurse. SIGIL `if` always carries an
    // else block (synthesised empty when absent). A simple assignment emits a
    // record for the place AND the value (the RHS is NOT pinned to the place type
    // — `y = 5` with `y: u32` types `5` as i64). Expression statements type their
    // expr; break/continue carry none. Covers nested if, while loops, assignment
    // from literal/var/arith, and break/continue.
    let src = "module demo;\n\
               fn side(n: i64) -> i64 { return n; }\n\
               pub fn cmp(x: i64) -> i64 { if x < 5 { return 1; } else { return 2; } }\n\
               pub fn nested(p: bool, q: bool) -> i64 { if p { if q { return 1; } else { return 2; } } else { return 3; } }\n\
               pub fn sumloop(n: i64) -> i64 { let mut i: i64 = 0; let mut s: i64 = 0; while i < n { s = s + i; i = i + 1; } return s; }\n\
               pub fn assignu() -> u32 { let mut y: u32 = 0; y = 5; return y; }\n\
               pub fn assignexpr(a: u32, b: u32) -> u32 { let mut y: u32 = 0; y = a + b; return y; }\n\
               pub fn exprstmt() -> i64 { side(7); return 0; }\n\
               pub fn loopbc(n: i64) -> i64 { let mut i: i64 = 0; while i < n { if i < 3 { i = i + 1; continue; } else {} if i > 8 { break; } else {} i = i + 1; } return i; }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL control-flow type stream must match the oracle"
    );
}

#[test]
fn pr4d_enum_payload_match_oracle() {
    // Enum-variant payload patterns bind each payload name to the variant's
    // payload type by position: `Opt::Some(x)` => x : the payload type, used in
    // the arm body or guard. Covers the qualified and bare (`Val(v)`) forms,
    // multiple payloads, a payload binding inside a guard, and several scalar
    // payload types (u32/i64/u64/i32/bool). The enum is resolved from the
    // scrutinee, so the bare form (whose pattern text omits the enum) resolves.
    let src = "module demo;\n\
               enum Opt { Some(u32), None }\n\
               enum Pair { Two(i32, u64), Nil }\n\
               enum Sig { Val(i64), Off }\n\
               enum Flag { B(bool), I(i32) }\n\
               pub fn fa(o: Opt) -> u32 { match o { Opt::Some(x) => { return x; }, Opt::None => { return 0; } } }\n\
               pub fn fb(p: Pair) -> u64 { match p { Pair::Two(a, b) => { return b; }, Pair::Nil => { return 0; } } }\n\
               pub fn fc(s: Sig) -> i64 { match s { Val(v) => { return v; }, Sig::Off => { return 0; } } }\n\
               pub fn fd(o: Opt) -> u32 { match o { Opt::Some(x) if x > 3 => { return x; }, _ => { return 0; } } }\n\
               pub fn fe(g: Flag) -> bool { match g { Flag::B(x) => { return x; }, Flag::I(n) => { return n > 0; } } }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL enum-payload-binding type stream must match the oracle"
    );
}

#[test]
fn pr4d_adversarial_fixtures_match_oracle() {
    let fixtures: &[&str] = &[
        "module demo; enum Tri { Three(i32, u32, i64), Nil } pub fn f(t: Tri) -> u32 { match t { Tri::Three(a, b, c) => { return b; }, Tri::Nil => { return 0; } } }",
        "module demo; enum Quad { Four(i64, bool, u32, str), Empty } pub fn f(q: Quad) -> u32 { match q { Quad::Four(a, b, c, d) => { return c + 1; }, Quad::Empty => { return 0; } } }",
        "module demo; enum Box { Has(u32), Empty } pub fn f(x: u32, b: Box) -> u32 { match b { Box::Has(x) => { return x; }, Box::Empty => { return x; } } }",
        "module demo; enum Opt { Some(i64), None } pub fn f(o: Opt) -> i64 { match o { Opt::Some(x) => { if x > 0 { return x; } else { return 0; } }, Opt::None => { return 0; } } }",
        "module demo; enum Cnt { N(u32), Z } pub fn f(c: Cnt) -> u32 { match c { Cnt::N(x) => { let mut s: u32 = x; while s > 0 { s = s - 1; } return s; }, Cnt::Z => { return 0; } } }",
        "module demo; enum A { Av(i32), An } enum B { Bv(str), Bn } pub fn fa(a: A) -> i32 { match a { A::Av(x) => { return x; }, A::An => { return 0; } } } pub fn fb(b: B) -> str { match b { B::Bv(s) => { return s; }, B::Bn => { return \"\"; } } }",
        "module demo; enum E { V(u64), W(i64), U } pub fn g1(e: E) -> u64 { match e { E::V(x) => { return x; }, E::W(y) => { return 0; }, E::U => { return 0; } } } pub fn g2(e: E) -> i64 { match e { E::W(y) => { return y; }, _ => { return 0; } } }",
        "module demo; enum Opt { Some(i64), None } fn dbl(n: i64) -> i64 { return n + n; } pub fn f(o: Opt) -> i64 { match o { Opt::Some(x) => { return dbl(x); }, Opt::None => { return 0; } } }",
        "module demo; enum M { P(u32), Q, R(i64) } pub fn f(m: M) -> i64 { match m { M::P(x) => { return 0; }, M::R(y) => { return y; }, _ => { return 0; } } }",
        "module demo; enum Outer { O(i64), X } enum Inner { I(i64), Y } pub fn f(o: Outer, i: Inner) -> i64 { match o { Outer::O(a) => { match i { Inner::I(b) => { return a + b; }, Inner::Y => { return a; } } }, Outer::X => { return 0; } } }",
        "module demo; enum Opt { Some(u32), None } pub fn add_five(o: Opt) -> u32 { match o { Opt::Some(x) => { return x + 5; }, Opt::None => { return 0; } } }",
        "module demo; enum Sig { Val(i32), Nil } pub fn clamp(s: Sig) -> i32 { match s { Sig::Val(x) => { if x < 10 { return x; } else { return 10; } }, Sig::Nil => { return 0; } } }",
        "module demo; enum Pair { Two(i64, u32), Zero } pub fn first(p: Pair) -> i64 { match p { Pair::Two(a, b) => { return a + 1; }, Pair::Zero => { return 0; } } }",
        "module demo; enum Flag { On(bool), Off } pub fn current(x: Flag) -> bool { match x { Flag::On(b) => { return b; }, Flag::Off => { return false; } } }",
        "module demo; enum Reading { Temp(f64), Missing } pub fn hot(r: Reading) -> bool { match r { Reading::Temp(d) => { return d > 3.5; }, Reading::Missing => { return false; } } }",
        "module demo; enum Msg { Text(str), Empty } pub fn is_hi(m: Msg) -> bool { match m { Msg::Text(s) => { return s == \"hi\"; }, Msg::Empty => { return false; } } }",
        "module demo; enum Opt { Some(i32), None } pub fn bump(o: Opt) -> i32 { match o { Opt::Some(x) if x > 3 => { return x + 1; }, Opt::Some(x) => { return x; }, Opt::None => { return 0; } } }",
        "module demo; enum Box { Val(u64), Empty } pub fn grow(b: Box) -> u64 { match b { Box::Val(x) => { let mut acc: u64 = x; acc = acc * 2 + 3; return acc; }, Box::Empty => { return 0; } } }",
        "module demo; fn weight(s: str) -> u64 { return 7; } enum Label { Name(str), Blank } pub fn score(l: Label) -> u64 { match l { Label::Name(s) => { return weight(s); }, Label::Blank => { return 0; } } }",
        "module demo; enum Count { Up(u32), Down(u32), Stop } pub fn run(c: Count) -> u32 { match c { Count::Up(x) => { let mut i: u32 = 0; while i < x { i = i + 1; } return i; }, other => { return 0; } } }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-4d adversarial fixture #{i} type stream must match the oracle:\n{src}"
        );
    }
}

#[test]
fn pr4b_match_match_oracle() {
    // `match` is a statement (no value): it emits no record itself — only the
    // scrutinee, each arm's guard, and each arm body's statements do. Arms are
    // comma-separated block bodies (juxtaposed arms are a parse error). Covers
    // integer/string/bool literal patterns, wildcard, a binding pattern (binds to
    // the scrutinee type, used in the body), a guard (binding in scope for the
    // guard + body), and enum UNIT-variant patterns. Enum payload-binding patterns
    // (`Opt::Some(x)`) are out of scope (PR-4c).
    let src = "module demo;\n\
               enum Color { Red, Green, Blue }\n\
               pub fn mi(x: i64) -> i64 { match x { 0 => { return 10; }, 1 => { return 20; }, _ => { return 30; } } }\n\
               pub fn mbind(x: i64) -> i64 { match x { n => { return n; } } }\n\
               pub fn mguard(x: i64) -> i64 { match x { n if n > 5 => { return n; }, _ => { return 0; } } }\n\
               pub fn menum(c: Color) -> i64 { match c { Color::Red => { return 1; }, Color::Green => { return 2; }, Color::Blue => { return 3; } } }\n\
               pub fn mstr(s: str) -> i64 { match s { \"a\" => { return 1; }, _ => { return 0; } } }\n\
               pub fn mnest(x: i64, y: i64) -> i64 { match x { 0 => { if y < 3 { return 1; } else { return 2; } }, _ => { return y + x; } } }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL match type stream must match the oracle"
    );
}

#[test]
fn pr4c_int_literal_pinning_match_oracle() {
    // Binary int-literal pinning: when exactly one operand of a comparison or
    // arithmetic op is a bare integer literal and the other is a concrete-typed
    // value, the oracle pins the literal to that concrete int type. So `v < 0`
    // with `v: i32` types the `0` as i32 (not the i64 default), and `y + 5` with
    // `y: u32` types the `5` as u32 — in either operand position, and in
    // return/comparison position where no outer expectation flows in. Pure
    // literal-vs-literal comparisons stay i64.
    let src = "module demo;\n\
               pub fn sign(n: i32) -> i32 { match n { 0 => { return 0; }, v if v < 0 => { return 0; }, _ => { return 1; } } }\n\
               pub fn ucmp(u: u32) -> bool { return u < 5; }\n\
               pub fn ucmprev(u: u32) -> bool { return 5 < u; }\n\
               pub fn uadd(y: u32) -> u32 { return y + 5; }\n\
               pub fn uaddrev(y: u32) -> u32 { return 5 + y; }\n\
               pub fn i32cmp(a: i32, b: i32) -> bool { return a < 9; }\n\
               pub fn u64mix(w: u64) -> u64 { return w * 3 + 1; }\n\
               pub fn bothlit() -> bool { return 3 < 5; }\n\
               pub fn i64lit(x: i64) -> i64 { return x + 7; }\n";
    assert_eq!(
        sorted_recs(&sigil_records(src)),
        sorted_recs(&oracle_records(src)),
        "SIGIL int-literal-pinning type stream must match the oracle"
    );
}

#[test]
fn pr1a_is_deterministic() {
    let src = "module demo;\npub fn f() -> i64 {\n    return 7;\n}\n";
    assert_eq!(
        sigil_records(src),
        sigil_records(src),
        "tool output must be deterministic across runs"
    );
}

/// Oracle, but returns None instead of panicking when the program is rejected
/// (name-resolution or type-check error) — for vetting candidate fixtures.
fn oracle_graceful(src: &str) -> Option<String> {
    let source = SourceFile::new("<fuzz>", src);
    let (ast, _pd) = parser::parse(&source);
    let resolved = name_resolution::resolve(&ast).ok()?;
    let (typed, _registry) =
        type_check::check_with_options(&resolved, &CompileOptions::default()).ok()?;
    let mut out: Vec<String> = Vec::new();
    for module in &typed.modules {
        for f in &module.functions {
            out.push(format!(
                "{},{},{},{};",
                f.span.start,
                f.span.end,
                type_tag(&f.ret),
                type_detail(&f.ret)
            ));
            for stmt in &f.body.statements {
                walk_stmt(stmt, &mut out);
            }
        }
    }
    Some(out.join(""))
}

/// Adversarial fixtures generated by the pr2a-adversarial-fixtures workflow —
/// symbol-table + variable-reference edge cases (type-changing shadows,
/// mid-scope refs to earlier bindings, self-referential shadows, every scalar as
/// a variable, ref chains, nested var arithmetic). Each must type-check in the
/// oracle AND match the SIGIL stream.
#[test]
fn pr2a_adversarial_fixtures_match_oracle() {
    let fixtures: &[&str] = &[
        "module demo; pub fn f() -> u32 { let x: u32 = 1; let x: u32 = 2; return x; }",
        "module demo; pub fn f() -> bool { let x: i64 = 1; let x: bool = true; return x; }",
        "module demo; pub fn f() -> f64 { let x: str = \"a\"; let y: str = x; let x: f64 = 1.5; return x; }",
        "module demo; pub fn f() -> str { let p: i64 = 7; let p: bool = false; let p: str = \"z\"; return p; }",
        "module demo; pub fn f() -> bool { let a: i64 = 1; let b: bool = true; let c: i64 = 2; let d: bool = b; return d; }",
        "module demo; pub fn f() -> bool { let x: i64 = 5; let x: bool = x < 9; return x; }",
        "module demo; pub fn use_bool() -> bool { let a: bool = true; let b: bool = a; let c: bool = false; return b == c; }",
        "module demo; pub fn use_str() -> bool { let s: str = \"hi\"; let t: str = s; let u: str = \"yo\"; return t != u; }",
        "module demo; pub fn use_f64() -> bool { let x: f64 = 1.5; let y: f64 = x; let z: f64 = 2.5; return y < z; }",
        "module demo; pub fn use_i32() -> bool { let a: i32 = 1; let b: i32 = a; let c: i32 = 2; return b <= c; }",
        "module demo; pub fn use_u64() -> bool { let a: u64 = 10; let b: u64 = a; let c: u64 = 20; return b > c; }",
        "module demo; pub fn use_u32() -> bool { let a: u32 = 7; let b: u32 = a; let c: u32 = 8; return b == c; }",
        "module demo; pub fn uchain() -> u32 { let a: u32 = 7; let b: u32 = a; let c: u32 = b; let d: u32 = c; return d; }",
        "module demo; pub fn vadd() -> u64 { let a: u64 = 10; let b: u64 = 20; return a + b; }",
        "module demo; pub fn vnest() -> u32 { let a: u32 = 1; let b: u32 = 2; let c: u32 = 3; let d: u32 = 4; return a + b + c + d; }",
        "module demo; pub fn vcmp() -> bool { let a: u32 = 4; let b: u32 = 9; return a < b; }",
        "module demo; pub fn vnot() -> bool { let flag: bool = true; return !flag; }",
        "module demo; pub fn vchaincmp() -> bool { let a: i64 = 1; let b: i64 = a; let c: i64 = b; return b == c; }",
        "module demo; pub fn nested_var_refs() -> i64 { let x: i64 = 5; return x + x * x; }",
        "module demo; pub fn var_type_match_annotation() -> u32 { let x: u32 = 10; let y: u32 = x; return y; }",
        "module demo; pub fn comparison_operand_order() -> bool { let a: i64 = 3; let b: i64 = 7; let r1: bool = a < b; let r2: bool = b < a; return r1; }",
        "module demo; pub fn all_scalar_types_vars() -> f64 { let ib: bool = true; let ii: i32 = 42; let uu: u32 = 50; let il: i64 = 100; let ul: u64 = 200; let fl: f64 = 3.14; return fl; }",
        "module demo; pub fn var_chain_through_lets() -> i64 { let x: i64 = 10; let y: i64 = x; let z: i64 = y; return z; }",
        "module demo; pub fn shadow_with_type_change() -> i64 { let x: i64 = 1; let x: u32 = 5; return 100; }",
        "module demo; pub fn three_var_arithmetic() -> i64 { let a: i64 = 2; let b: i64 = 3; let c: i64 = 5; return a + b + c; }",
        "module demo; pub fn multi_type_arithmetic() -> i64 { let x: i32 = 10; let y: i32 = 20; let z: i64 = 5; let sum1: i32 = x + y; let sum2: i64 = z + z; return sum2; }",
    ];
    let mut mismatches: Vec<String> = Vec::new();
    let mut rejects: Vec<usize> = Vec::new();
    for (i, src) in fixtures.iter().enumerate() {
        match oracle_graceful(src) {
            None => rejects.push(i),
            Some(orc) => {
                let sig = sigil_records(src);
                if sorted_recs(&sig) != sorted_recs(&orc) {
                    mismatches.push(format!(
                        "[{i}] {src}\n    sigil:  {:?}\n    oracle: {:?}",
                        sorted_recs(&sig),
                        sorted_recs(&orc)
                    ));
                }
            }
        }
    }
    assert!(
        rejects.is_empty(),
        "fixtures rejected by the oracle (out of scope): {rejects:?}"
    );
    assert!(
        mismatches.is_empty(),
        "adversarial fixtures diverged from the oracle:\n{}",
        mismatches.join("\n")
    );
}

/// Adversarial fixtures generated by the pr3b-adversarial-fixtures workflow —
/// record-field-access edge cases: every scalar field type read + returned;
/// fields in arithmetic/comparison (field+field, i64/f64 field+literal, repeated
/// reuse, nested polynomials); a field access bound to a let or passed as a call
/// argument; record-param aliasing via a same-type let then accessed; multiple
/// records sharing a field NAME with different types; single- and wide-field
/// records; record + scalar params mixed. Each must type-check in the oracle AND
/// match the SIGIL stream (all 51 vetted in-scope + matching at authoring time).
#[test]
fn pr3b_adversarial_fixtures_match_oracle() {
    let fixtures: &[&str] = &[
        "module demo;\nrecord All { flag: bool, small: i32, uns: u32, big: i64, ubig: u64, frac: f64, name: str }\npub fn gb(v: All) -> bool { return v.flag; }\npub fn gi(v: All) -> i32 { return v.small; }\npub fn gu(v: All) -> u32 { return v.uns; }\npub fn gl(v: All) -> i64 { return v.big; }\npub fn gul(v: All) -> u64 { return v.ubig; }\npub fn gf(v: All) -> f64 { return v.frac; }\npub fn gs(v: All) -> str { return v.name; }\n",
        "module demo;\nrecord Hept { a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64 }\npub fn first(h: Hept) -> i64 { return h.a; }\npub fn mid(h: Hept) -> i64 { return h.d; }\npub fn last(h: Hept) -> i64 { return h.g; }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\npub fn f(p: Point) -> i64 { let q: Point = p; return q.x; }\n",
        "module demo;\nrecord P { x: i64, y: i64 }\npub fn g(p: P) -> i64 { let q: P = p; return p.x + q.y; }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\nfn consume(v: i64) -> i64 { return v; }\npub fn g(p: Point) -> i64 { return consume(p.x); }\n",
        "module demo;\nrecord P { x: i64, y: i64 }\nrecord Q { u: i64, t: i64 }\nfn id(z: i64) -> i64 { return z; }\npub fn g(p: P, q: Q) -> i64 { return id(p.x) + id(q.t); }\n",
        "module demo;\nrecord P { x: u32, y: u32 }\npub fn g(p: P) -> u32 { let k: u32 = p.y; return p.x + k; }\n",
        "module demo;\nrecord P { x: i32, y: i32 }\npub fn cmp(p: P, q: P) -> bool { return p.x < q.x; }\npub fn sumlast(p: P, q: P) -> i32 { return p.y + q.y; }\n",
        "module demo;\nrecord R { ratio: f64, scale: f64 }\npub fn g(r: R) -> f64 { return r.ratio + 2.5; }\n",
        "module demo;\nrecord S { a: bool, b: bool, s: str, t: str }\npub fn beq(v: S) -> bool { return v.a == v.b; }\npub fn seq(v: S) -> bool { return v.s == v.t; }\n",
        "module demo; record P { x: i64, y: i64 } pub fn f(p: P) -> i64 { return p.x + p.x * p.x; }",
        "module demo; record P { x: i64, y: i64 } pub fn f(p: P, q: P) -> i64 { return p.x + q.x + p.y + q.y; }",
        "module demo; record P { x: i64, y: i64 } pub fn f(p: P, q: P) -> i64 { return p.x * q.y + q.x * p.y; }",
        "module demo; record P { x: i64, y: i64 } pub fn f(p: P, q: P) -> bool { return p.x == q.x; }",
        "module demo; record P { a: u32, b: u32 } pub fn f(p: P, q: P) -> u32 { return p.a + q.a + p.b; }",
        "module demo; record P { a: u32, b: u32 } pub fn f(p: P, q: P) -> bool { return p.a < q.b; }",
        "module demo; record P { x: i64, y: i64 } pub fn f(p: P) -> i64 { return p.x + 5; }",
        "module demo; record P { r: f64, s: f64 } pub fn f(p: P) -> f64 { return p.r + 2.5 * p.s; }",
        "module demo; record P { x: i64, y: i64 } fn consume(v: i64) -> i64 { return v; } pub fn f(p: P, q: P) -> i64 { return consume(p.x + q.y); }",
        "module demo; record P { x: i64, y: i64 } pub fn f(p: P) -> i64 { let v: i64 = p.x; return v + p.y * v; }",
        "module demo;\nrecord Point { x: i64, y: i64 }\npub fn f(p: Point) -> i64 { let a: i64 = p.x; let b: i64 = a; let c: i64 = b; return c; }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\nfn consume(v: i64) -> i64 { return v; }\npub fn f(p: Point) -> i64 { return consume(p.x); }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\npub fn f(p: Point, q: Point) -> i64 { return p.x + q.y; }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\npub fn f(p: Point) -> i64 { let q: Point = p; let r: Point = q; return r.y; }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\npub fn f(p: Point) -> i64 { let q: Point = p; return q.x + p.y; }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\nrecord Line { a: i64, b: i64 }\nfn combine(m: i64, n: i64) -> i64 { return m + n; }\npub fn f(p: Point, l: Line) -> i64 { return combine(p.x, l.a); }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\nrecord Line { a: i64, b: i64 }\npub fn f(p: Point, l: Line) -> i64 { let q: Point = p; let m: Line = l; return q.x + m.b; }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\nfn id(v: i64) -> i64 { return v; }\nfn add(a: i64, b: i64) -> i64 { return a + b; }\npub fn f(p: Point, q: Point) -> i64 { return add(id(p.x), q.y); }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\nfn dbl(v: i64) -> i64 { return v + v; }\npub fn f(p: Point) -> i64 { let q: Point = p; let s: i64 = dbl(q.x); return s + p.y; }\n",
        "module demo;\nrecord Vec2 { ux: u32, uy: u32 }\npub fn f(p: Vec2) -> u32 { let k: u32 = p.uy; return p.ux + k; }\n",
        "module demo;\nrecord Meas { ratio: f64, scale: f64 }\npub fn f(m: Meas) -> bool { let r: f64 = m.ratio; return r < m.scale; }\n",
        "module demo;\nrecord Flags { active: bool, label: str }\npub fn f(g: Flags, h: Flags) -> bool { let s: bool = g.active == h.active; return s; }\n",
        "module demo;\nrecord Big { ii: i64, uu: u32, ff: f64, bb: bool, ss: str }\npub fn f(z: Big) -> f64 { let a: i64 = z.ii; let b: u32 = z.uu; let c: f64 = z.ff; let d: bool = z.bb; let e: str = z.ss; return c; }\n",
        "module demo;\nrecord Pos { lo: i64, hi: i64 }\npub fn f(pt: Pos) -> bool { let lhs: i64 = pt.lo; let rhs: i64 = pt.hi; return lhs < rhs; }\n",
        "module demo;\nrecord Single { only: i64 }\npub fn f(p: Single) -> i64 { return p.only; }\n",
        "module demo;\nrecord Wide { a: i64, b: i64, c: i64, d: i64, e: i64, g: i64, h: i64, last: i64 }\npub fn f(p: Wide) -> i64 { return p.last; }\n",
        "module demo;\nrecord Ai { x: i64, y: i64 }\nrecord Bu { x: u32, y: u32 }\npub fn gi(p: Ai) -> i64 { return p.x; }\npub fn gu(q: Bu) -> u32 { return q.x; }\n",
        "module demo;\nrecord Pos { px: i64, py: i64 }\nrecord Vel { vx: i64, vy: i64 }\nfn add2(m: i64, n: i64) -> i64 { return m + n; }\npub fn step(p: Pos, v: Vel) -> i64 { return add2(p.px, v.vx); }\n",
        "module demo;\nrecord Pt { x: i64, y: i64 }\npub fn quad(p: Pt) -> i64 { return p.x + p.x + p.x + p.x; }\n",
        "module demo;\nrecord Box1 { w: i64, h: i64 }\npub fn area_plus(b: Box1, k: i64) -> i64 { return b.w * b.h + k; }\n",
        "module demo;\nrecord Node1 { val: i64, tag: i64 }\npub fn viaAlias(p: Node1) -> i64 { let q: Node1 = p; return q.val; }\n",
        "module demo;\nrecord Meter { lo: u32, hi: u32 }\npub fn within(m: Meter) -> bool { let a: u32 = m.lo; return a < m.hi; }\n",
        "module demo;\nrecord Cell { v: u32 }\nfn idu(x: u32) -> u32 { return x; }\npub fn passit(c: Cell) -> u32 { return idu(c.v); }\n",
        "module demo;\nrecord Sample { amp: f64, freq: f64 }\nrecord Named1 { name: str }\npub fn scale(s: Sample) -> f64 { return s.amp + s.freq; }\npub fn isFoo(n: Named1) -> bool { return n.name == n.name; }\n",
        "module demo;\nrecord Vec2 { x: i64, y: i64 }\npub fn dot(a: Vec2, b: Vec2) -> i64 { let c: Vec2 = a; return c.x * b.x + c.y * b.y; }\n",
        "module demo;\nrecord Toggle { active: bool, locked: bool }\npub fn both(t: Toggle) -> bool { let a: bool = t.active; return a == t.locked; }\n",
        "module demo;\nrecord Score { pts: i64 }\npub fn bump(s: Score) -> i64 { return s.pts + 10; }\npub fn over(s: Score) -> bool { return s.pts > 100; }\n",
        "module demo;\nrecord Counter { n: u32 }\npub fn twice(c: Counter) -> u32 { let bump: u32 = c.n; return c.n + bump; }\n",
        "module demo;\nrecord R1 { a: i64 }\nrecord R2 { b: i64 }\nrecord R3 { c: i64 }\nfn sum3(x: i64, y: i64, z: i64) -> i64 { return x + y + z; }\npub fn combine(p: R1, q: R2, r: R3) -> i64 { return sum3(p.a, q.b, r.c); }\n",
        "module demo;\nrecord One { v: i64 }\npub fn poly(p: One) -> i64 { return p.v + p.v * p.v + p.v * p.v * p.v; }\n",
        "module demo;\nrecord User1 { id: str, age: i64 }\nrecord Acct { id: str, bal: i64 }\npub fn same(u: User1, a: Acct) -> bool { return u.id == a.id; }\n",
    ];
    let mut mismatches: Vec<String> = Vec::new();
    let mut rejects: Vec<usize> = Vec::new();
    for (i, src) in fixtures.iter().enumerate() {
        match oracle_graceful(src) {
            None => rejects.push(i),
            Some(orc) => {
                let sig = sigil_records(src);
                if sorted_recs(&sig) != sorted_recs(&orc) {
                    mismatches.push(format!(
                        "[{i}] {src}\n    sigil:  {:?}\n    oracle: {:?}",
                        sorted_recs(&sig),
                        sorted_recs(&orc)
                    ));
                }
            }
        }
    }
    assert!(
        rejects.is_empty(),
        "fixtures rejected by the oracle (out of scope): {rejects:?}"
    );
    assert!(
        mismatches.is_empty(),
        "adversarial fixtures diverged from the oracle:\n{}",
        mismatches.join("\n")
    );
}

/// Adversarial fixtures generated by the pr3c-adversarial-fixtures workflow —
/// record-construction edge cases: every scalar field type pinned from a literal,
/// out-of-declaration-order fields, field-init values that are params / field
/// accesses / arithmetic (field-type-pinned literals) / call results, the
/// construction returned fresh / let-bound / passed as a call argument, building a
/// record from another record's fields, single- and wide-field records, and two
/// records sharing a field name. Each must type-check in the oracle AND match the
/// SIGIL stream (all 47 vetted in-scope + matching at authoring time).
#[test]
fn pr3c_adversarial_fixtures_match_oracle() {
    let fixtures: &[&str] = &[
        "module demo;\nrecord Bag { i: i64, u: u32, n: i32, w: u64, f: f64, b: bool, s: str }\npub fn make() -> Bag { return Bag { i: 1, u: 2, n: 3, w: 4, f: 2.5, b: true, s: \"hi\" }; }\n",
        "module demo;\nrecord Bag { i: i64, u: u32, n: i32, w: u64, f: f64, b: bool, s: str }\npub fn make() -> Bag { return Bag { s: \"yo\", b: false, f: 1.5, w: 9, n: 7, u: 5, i: 3 }; }\n",
        "module demo;\nrecord Quad { a: u32, b: u32, c: u32, d: u32 }\npub fn make() -> Quad { return Quad { c: 3, a: 1, d: 4, b: 2 }; }\n",
        "module demo;\nrecord Point { x: i64, y: u32 }\npub fn at(yy: u32, xx: i64) -> Point { return Point { x: xx, y: yy }; }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\npub fn flip(p: Point) -> Point { return Point { x: p.y, y: p.x }; }\n",
        "module demo;\nrecord Stat { total: i64, over: bool }\npub fn mk(a: i64, b: i64) -> Stat { return Stat { total: a + b, over: a > b }; }\n",
        "module demo;\nrecord Wrap { v: i64, k: u32 }\nfn dbl(x: i64) -> i64 { return x + x; }\npub fn f(n: i64) -> i64 { let w: Wrap = Wrap { v: dbl(n), k: 5 }; return w.v; }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\nfn consume(p: Point) -> i64 { return 0; }\npub fn f() -> i64 { return consume(Point { x: 1, y: 2 }); }\n",
        "module demo;\nrecord Vals { p: f64, q: f64 }\npub fn f() -> Vals { let a: f64 = 1.5; let b: f64 = 2.5; return Vals { p: a, q: b }; }\n",
        "module demo;\nrecord Pt { x: i64, y: i64 }\nrecord Lab { name: str, ok: bool }\npub fn g() -> bool { let p: Pt = Pt { x: 1, y: 2 }; return p.x < 5; }\npub fn h() -> Lab { return Lab { name: \"k\", ok: true }; }\n",
        "module demo;\nrecord Mix { small: i32, huge: u64 }\npub fn f() -> u64 { let m: Mix = Mix { huge: 9, small: 7 }; return m.huge; }\n",
        "module demo;\nrecord Acc { sum: i64 }\nrecord In1 { base: i64, step: i64 }\npub fn run(i: In1) -> Acc { return Acc { sum: i.base + i.step * 2 }; }\n",
        "module demo; record Point { x: i64, y: i64 } record Line { a: i64, b: i64 } pub fn f(p: Point) -> Line { return Line { a: p.x, b: p.y }; }",
        "module demo; record Point { x: i64, y: u32 } pub fn f() -> u32 { let p: Point = Point { x: 1, y: 2 }; return p.y; }",
        "module demo; record Point { x: i64, y: i64 } fn consume(p: Point) -> i64 { return 0; } pub fn f() -> i64 { return consume(Point { x: 1, y: 2 }); }",
        "module demo; record Point { x: i64, y: u32 } fn id(v: i64) -> i64 { return v; } pub fn f() -> Point { return Point { y: 3, x: id(5) }; }",
        "module demo; record Pt { x: i64, y: i64 } record Box1 { w: i64, h: i64 } pub fn f(p: Pt) -> Box1 { return Box1 { w: p.x + 1, h: p.y * 2 }; }",
        "module demo; record Bag { a: i32, b: u32, c: i64, d: u64, e: f64, f: bool, g: str } pub fn f() -> Bag { return Bag { a: 1, b: 2, c: 3, d: 4, e: 2.5, f: true, g: \"hi\" }; }",
        "module demo; record Flag { hot: bool, n: i64 } pub fn f(k: i64) -> Flag { return Flag { hot: k < 10, n: k }; }",
        "module demo; record P { x: u32, y: u32 } pub fn f(src: P) -> u32 { let q: P = P { x: src.y, y: src.x }; return q.x; }",
        "module demo; record Rec { a: i64, b: u64 } fn take(r: Rec) -> i64 { return 0; } pub fn f(n: i64) -> i64 { return take(Rec { a: n, b: 9 }); }",
        "module demo; record Q { p: i32, q: i32 } fn mk(x: i32) -> i32 { return x; } fn add(a: i32, b: i32) -> i32 { return a + b; } pub fn f() -> Q { return Q { q: add(mk(1), 2), p: mk(7) }; }",
        "module demo; record Point { x: i64, y: u32 } pub fn f() -> Point { let k: i64 = 3; return Point { x: k, y: 8 }; }",
        "module demo; record P { x: i64, y: i64 } record S { lo: i64, hi: i64 } pub fn f(p: P) -> i64 { let s: S = S { lo: p.x, hi: p.x + p.y }; return s.hi; }",
        "module demo; record Counts { a: u32, b: i32, c: u64 } pub fn mk(p: u32, q: i32, r: u64) -> Counts { return Counts { a: p + 1, b: q + 2, c: r + 3 }; }",
        "module demo; record Vecf { r: f64, s: f64 } pub fn mk(p: Vecf) -> Vecf { return Vecf { r: p.r + 2.5, s: 1.0 }; }",
        "module demo; record Flags { lt: bool, eq: bool } pub fn mk(a: i64, b: i64, p: u32, q: u32) -> Flags { return Flags { lt: a < b, eq: p == q }; }",
        "module demo; record Acc { total: i64, count: i64 } pub fn mk(a: i64, b: i64, c: i64) -> Acc { return Acc { total: a + b * c - a, count: 0 }; }",
        "module demo; fn dbl(x: i64) -> i64 { return x + x; } record Box1 { w: i64, h: i64 } pub fn mk(p: i64) -> Box1 { return Box1 { w: dbl(p), h: p * 2 }; }",
        "module demo; record Vec2 { ux: u32, uy: u32 } pub fn mk(p: Vec2) -> Vec2 { return Vec2 { uy: p.uy + 2, ux: p.ux * 3 }; }",
        "module demo; record Pt { x: i64, y: i64 } fn consume(p: Pt) -> i64 { return 0; } pub fn run(a: i64, b: i64) -> i64 { return consume(Pt { x: a + b, y: a - b }); }",
        "module demo; record P { x: i64, y: i64 } pub fn f(a: i64, b: i64) -> i64 { let p: P = P { x: a + 1, y: b * 2 }; return p.x + p.y; }",
        "module demo; record Poly { v: i64, k: i64 } pub fn mk(p: i64) -> Poly { return Poly { v: p + p * p + p * p * p, k: 7 }; }",
        "module demo; record Big { flag: bool, name: str, frac: f64, small: i32, ubig: u64, big: i64 } pub fn mk(a: i64, b: i64, x: i32, y: u64, r: f64) -> Big { return Big { flag: a < b, name: \"hi\", frac: r + 0.5, small: x + 1, ubig: y * 2, big: a + b }; }",
        "module demo; record Src { v: u32, w: u32 } record Dst { out: u32, dbl: u32 } pub fn mk(s: Src) -> Dst { return Dst { out: s.v + 10, dbl: s.w + s.v }; }",
        "module demo; record Stat { sum: i64, sq: i64 } pub fn mk(a: i64, b: i64) -> Stat { let s: i64 = a + b; return Stat { sum: s, sq: s * s }; }",
        "module demo;\nrecord Single { only: i64 }\npub fn mk() -> Single { return Single { only: 42 }; }\n",
        "module demo;\nrecord All { flag: bool, small: i32, uns: u32, big: i64, ubig: u64, frac: f64, name: str }\npub fn mk() -> All { return All { flag: true, small: 1, uns: 2, big: 3, ubig: 4, frac: 2.5, name: \"hi\" }; }\n",
        "module demo;\nrecord Ai { v: i64 }\nrecord Bu { v: u32 }\npub fn mi() -> Ai { return Ai { v: 7 }; }\npub fn mu() -> Bu { return Bu { v: 7 }; }\n",
        "module demo;\nrecord Point { x: i64, y: u32 }\npub fn a() -> Point { return Point { x: 1, y: 2 }; }\npub fn b() -> Point { return Point { y: 9, x: 4 }; }\npub fn c(k: i64) -> Point { return Point { x: k, y: 3 }; }\n",
        "module demo;\nrecord In1 { src: i64 }\nrecord Out1 { a: i64, b: i64, c: u32 }\npub fn build(p: In1, k: i64, m: u32) -> Out1 { return Out1 { a: p.src, b: k, c: m }; }\n",
        "module demo;\nrecord Point { x: i64, y: i64 }\nfn consume(p: Point) -> i64 { return 0; }\npub fn f() -> i64 { return consume(Point { x: 1, y: 2 }); }\n",
        "module demo;\nrecord Stat { sum: i64, gt: bool }\npub fn f(a: i64, b: i64) -> Stat { return Stat { sum: a + b, gt: a > b }; }\n",
        "module demo;\nrecord Rgb { r: u32, g: u32, b: u32 }\npub fn green() -> u32 { let c: Rgb = Rgb { g: 255, b: 0, r: 0 }; return c.g; }\n",
        "module demo;\nrecord Src2 { px: i64, py: i64 }\nrecord Dst2 { qx: i64, qy: i64 }\npub fn copyit(s: Src2) -> Dst2 { return Dst2 { qx: s.px, qy: s.py }; }\n",
        "module demo;\nrecord Mix { n: i64, f: f64, ok: bool, tag: str }\nfn gen() -> i64 { return 5; }\npub fn build() -> Mix { return Mix { n: gen(), f: 1.5, ok: false, tag: \"z\" }; }\n",
        "module demo;\nrecord Nums { i: i32, u: u32, l: i64, b: u64 }\npub fn f() -> Nums { return Nums { i: 1, u: 2, l: 3, b: 4 }; }\n",
    ];
    let mut mismatches: Vec<String> = Vec::new();
    let mut rejects: Vec<usize> = Vec::new();
    for (i, src) in fixtures.iter().enumerate() {
        match oracle_graceful(src) {
            None => rejects.push(i),
            Some(orc) => {
                let sig = sigil_records(src);
                if sorted_recs(&sig) != sorted_recs(&orc) {
                    mismatches.push(format!(
                        "[{i}] {src}\n    sigil:  {:?}\n    oracle: {:?}",
                        sorted_recs(&sig),
                        sorted_recs(&orc)
                    ));
                }
            }
        }
    }
    assert!(
        rejects.is_empty(),
        "fixtures rejected by the oracle (out of scope): {rejects:?}"
    );
    assert!(
        mismatches.is_empty(),
        "adversarial fixtures diverged from the oracle:\n{}",
        mismatches.join("\n")
    );
}

/// Adversarial fixtures generated by the pr3d-adversarial-fixtures workflow —
/// enum + variant-construction edge cases: unit and payload variants; payloads of
/// every scalar type (int-literal payloads stay i64 even in u32/i32/u64 variants);
/// multi-field variants; payload from a param / field access / arithmetic / call
/// result; a variant returned fresh, let-bound, or passed as a call argument; an
/// enum param consumed (never returned — T253); enums mixed with records; two
/// enums sharing a variant name; single- and many-variant enums. Each must
/// type-check in the oracle AND match the SIGIL stream (all 52 vetted in-scope +
/// matching at authoring time).
#[test]
fn pr3d_adversarial_fixtures_match_oracle() {
    let fixtures: &[&str] = &[
        "module demo; enum Light { Red, Yellow, Green, Off, Broken } pub fn r() -> Light { return Light::Red; } pub fn y() -> Light { return Light::Yellow; } pub fn g() -> Light { return Light::Green; } pub fn o() -> Light { return Light::Off; } pub fn b() -> Light { return Light::Broken; }",
        "module demo; enum Cell { B, Ci(i64), Cu(u32), Cn(i32), Cw(u64), Cf(f64), Cb(bool), Cs(str) } pub fn k() -> Cell { return Cell::B; } pub fn a() -> Cell { return Cell::Ci(1); } pub fn b() -> Cell { return Cell::Cu(2); } pub fn c() -> Cell { return Cell::Cn(3); } pub fn d() -> Cell { return Cell::Cw(4); } pub fn e() -> Cell { return Cell::Cf(2.5); } pub fn g() -> Cell { return Cell::Cb(true); } pub fn h() -> Cell { return Cell::Cs(\"hi\"); }",
        "module demo; enum Shape { Dot, Pair(i64, i64), Trip(i64, i64, i64), Tagged(str, bool) } pub fn d() -> Shape { return Shape::Dot; } pub fn p() -> Shape { return Shape::Pair(1, 2); } pub fn t() -> Shape { return Shape::Trip(1, 2, 3); } pub fn g() -> Shape { return Shape::Tagged(\"x\", false); }",
        "module demo; enum A { One, Two(i64) } enum B { Lo, Hi(str) } fn useA(c: A) -> i64 { return 0; } fn useB(c: B) -> i64 { return 0; } pub fn mkA() -> A { return A::Two(7); } pub fn mkB() -> B { return B::Hi(\"yo\"); } pub fn consumeA(c: A) -> i64 { return useA(c); } pub fn consumeB(c: B) -> i64 { return useB(c); }",
        "module demo; enum N { Z, Val(i64) } pub fn fromParam(k: i64) -> N { return N::Val(k); } pub fn fromLet() -> N { let m: i64 = 9; return N::Val(m); } pub fn fromArith(a: i64, b: i64) -> N { return N::Val(a + b * 2); }",
        "module demo; record P { x: i64, y: u32 } enum Wrap { Empty, Hold(i64) } fn gen() -> i64 { return 5; } pub fn fromField(p: P) -> Wrap { return Wrap::Hold(p.x); } pub fn fromCall() -> Wrap { return Wrap::Hold(gen()); }",
        "module demo; enum Color { Red, Green, Blue } enum Opt { None, Some(i64) } fn takeColor(c: Color) -> i64 { return 0; } fn takeOpt(o: Opt) -> i64 { return 0; } pub fn c1() -> i64 { return takeColor(Color::Green); } pub fn c2() -> i64 { return takeOpt(Opt::Some(42)); } pub fn c3() -> i64 { return takeOpt(Opt::None); }",
        "module demo; enum Box3 { Eu(u32), En(i32), Ew(u64), Ef(f64), Eb(bool), Es(str) } pub fn pu() -> Box3 { return Box3::Eu(7); } pub fn pn() -> Box3 { return Box3::En(8); } pub fn pw() -> Box3 { return Box3::Ew(9); } pub fn pf() -> Box3 { return Box3::Ef(1.5); } pub fn pb() -> Box3 { return Box3::Eb(false); } pub fn ps() -> Box3 { return Box3::Es(\"z\"); }",
        "module demo; record Q { a: i64, b: u32 } enum Event { Idle, Tick(i64), Mov(i64, i64), Label(str), Ratio(f64), Flag(bool), Combo(i64, str, bool) } fn src() -> i64 { return 3; } pub fn e1() -> Event { return Event::Idle; } pub fn e2(k: i64) -> Event { return Event::Tick(k); } pub fn e3(q: Q) -> Event { return Event::Mov(q.a, q.a + 1); } pub fn e4() -> Event { return Event::Label(\"go\"); } pub fn e5() -> Event { return Event::Ratio(2.5); } pub fn e6() -> Event { return Event::Flag(true); } pub fn e7() -> Event { return Event::Combo(src(), \"c\", false); }",
        "module demo; enum Pay { Zero, One(u32), Two(u32, i32), Many(u32, i32, u64, f64) } pub fn z() -> Pay { return Pay::Zero; } pub fn o() -> Pay { return Pay::One(1); } pub fn t() -> Pay { return Pay::Two(2, 3); } pub fn m() -> Pay { return Pay::Many(4, 5, 6, 2.5); }",
        "module demo; enum Opt1 { None, Some(i64) } enum Opt2 { None, Got(str) } pub fn f() -> Opt1 { return Opt1::None; } pub fn g() -> Opt2 { return Opt2::None; } pub fn h() -> Opt1 { return Opt1::Some(5); } pub fn k() -> Opt2 { return Opt2::Got(\"x\"); }",
        "module demo; enum Reg { Empty, Hold(u32) } pub fn fromU32(p: u32) -> Reg { return Reg::Hold(p); } pub fn fromLet() -> Reg { let v: u32 = 8; return Reg::Hold(v); } pub fn fromLit() -> Reg { return Reg::Hold(255); }",
        "module demo;\nenum Color { Red, Green, Blue }\nfn useColor(c: Color) -> i64 { return 0; }\npub fn direct() -> i64 { return useColor(Color::Green); }\npub fn vialet() -> i64 { let c: Color = Color::Blue; return useColor(c); }\npub fn fresh() -> Color { return Color::Red; }\n",
        "module demo;\nenum Tag { A, B }\nfn sink(t: Tag) -> i64 { return 0; }\npub fn consume(t: Tag) -> i64 { return sink(t); }\n",
        "module demo;\nenum Kind { One, Two }\nfn sink(k: Kind) -> i64 { return 0; }\npub fn relabel(k: Kind) -> Kind { let n: i64 = sink(k); return Kind::Two; }\n",
        "module demo;\nenum Opt { None, Some(i64) }\npub fn fromParam(n: i64) -> Opt { return Opt::Some(n); }\npub fn fromLet() -> Opt { let v: i64 = 9; return Opt::Some(v); }\npub fn fromArith(a: i64, b: i64) -> Opt { return Opt::Some(a + b); }\n",
        "module demo;\nrecord Pt { x: i64, y: u32 }\nenum Wrap { W(i64) }\npub fn ofx(p: Pt) -> Wrap { return Wrap::W(p.x); }\n",
        "module demo;\nenum Box1 { V(i64) }\nfn mk(n: i64) -> i64 { return n + 1; }\npub fn build(n: i64) -> Box1 { return Box1::V(mk(n)); }\n",
        "module demo;\nenum Sh { Dot, Pair(i64, i64), Tri(i64, i64, i64) }\npub fn pair(a: i64) -> Sh { return Sh::Pair(a, 5); }\npub fn tri(a: i64, b: i64) -> Sh { return Sh::Tri(1, a, a + b); }\n",
        "module demo;\nenum Mix { U(u32), I(i32), W(u64) }\npub fn pu() -> Mix { return Mix::U(7); }\npub fn pi() -> Mix { return Mix::I(8); }\npub fn pw() -> Mix { return Mix::W(9); }\n",
        "module demo;\nenum Color { Red, Green }\nfn takeC(c: Color) -> i64 { return 0; }\npub fn f() -> i64 { return takeC(Color::Red); }\npub fn g() -> i64 { return takeC(Color::Green); }\n",
        "module demo;\nenum Opt { None, Some(i64) }\nfn takeO(o: Opt) -> i64 { return 0; }\npub fn f(n: i64) -> i64 { return takeO(Opt::Some(n)); }\npub fn g() -> i64 { return takeO(Opt::Some(3)); }\npub fn h() -> i64 { return takeO(Opt::None); }\n",
        "module demo;\nenum Msg { Text(str), Flag(bool), Ratio(f64) }\npub fn t() -> Msg { return Msg::Text(\"hi\"); }\npub fn b() -> Msg { return Msg::Flag(true); }\npub fn r() -> Msg { return Msg::Ratio(2.5); }\n",
        "module demo;\nenum Opt { None, Some(i64) }\nfn use1(o: Opt) -> i64 { return 0; }\npub fn vlu() -> i64 { let o: Opt = Opt::None; return use1(o); }\npub fn vlp() -> i64 { let o: Opt = Opt::Some(4); return use1(o); }\n",
        "module demo;\nenum Color { Red }\nenum Shape { Dot }\nfn two(c: Color, s: Shape) -> i64 { return 0; }\npub fn f() -> i64 { return two(Color::Red, Shape::Dot); }\n",
        "module demo;\nenum St { Lo, Hi }\nfn rank(s: St) -> i64 { return 0; }\nfn pick(n: i64) -> i64 { return n; }\npub fn step(s: St) -> St { let r: i64 = rank(s); let p: i64 = pick(r); return St::Hi; }\n",
        "module demo;\nrecord Q { a: i64, b: i64 }\nenum Acc { Sum(i64) }\nfn drain(x: Acc) -> i64 { return 0; }\npub fn f(q: Q, k: i64) -> i64 { let acc: Acc = Acc::Sum(q.a + q.b * k); return drain(acc); }\n",
        "module demo;\nenum Opt { None, Some(i64) }\npub fn wrap(n: i64) -> Opt { return Opt::Some(n); }\npub fn inc(n: i64) -> Opt { return Opt::Some(n + 1); }\npub fn pair(a: i64, b: i64) -> Opt { return Opt::Some(a * b - a); }\n",
        "module demo;\nrecord Pt { x: i64, y: u32 }\nenum Tag { Z, X(i64), Y(u32) }\npub fn tx(p: Pt) -> Tag { return Tag::X(p.x); }\npub fn ty(p: Pt) -> Tag { return Tag::Y(p.y); }\n",
        "module demo;\nenum Box1 { E, V(i64) }\nfn gen() -> i64 { return 5; }\npub fn mk() -> Box1 { return Box1::V(gen()); }\npub fn mk2() -> Box1 { return Box1::V(later(3)); }\nfn later(x: i64) -> i64 { return x + 1; }\n",
        "module demo;\nrecord Pt { x: i64, y: i64 }\nenum Sh { Dot, Pair(i64, i64), Tri(i64, i64, i64) }\npub fn diag(p: Pt) -> Sh { return Sh::Pair(p.x, p.y); }\npub fn shift(p: Pt, d: i64) -> Sh { return Sh::Tri(p.x + d, p.y - d, d); }\n",
        "module demo;\nenum Box1 { E, U(u32), I(i32), W(u64) }\npub fn pu() -> Box1 { return Box1::U(7); }\npub fn pi() -> Box1 { return Box1::I(7); }\npub fn pw() -> Box1 { return Box1::W(7); }\n",
        "module demo;\nenum Msg { Empty, Text(str), Flag(bool), Tagged(str, bool), Meas(f64, i64) }\npub fn t() -> Msg { return Msg::Text(\"hi\"); }\npub fn f() -> Msg { return Msg::Flag(true); }\npub fn tg() -> Msg { return Msg::Tagged(\"on\", false); }\npub fn m(r: f64) -> Msg { return Msg::Meas(r + 1.5, 3); }\n",
        "module demo;\nenum Color { Red, Green, Blue }\nfn useColor(c: Color) -> i64 { return 0; }\npub fn viaLet() -> i64 { let c: Color = Color::Green; return useColor(c); }\npub fn direct() -> i64 { return useColor(Color::Blue); }\n",
        "module demo;\nenum Light { Off, On }\nfn read(l: Light) -> i64 { return 0; }\npub fn consume(l: Light) -> i64 { return read(l); }\npub fn fresh() -> Light { return Light::On; }\n",
        "module demo;\nenum N { Zero, Pos(i64), Neg(i64) }\npub fn p(a: i64, b: i64) -> N { let s: i64 = a + b; return N::Pos(s); }\npub fn n(a: i64) -> N { let d: i64 = a * 2; return N::Neg(d); }\npub fn z() -> N { return N::Zero; }\n",
        "module demo;\nenum Opt { None, Some(i64) }\nfn take(o: Opt) -> i64 { return 0; }\npub fn f(n: i64) -> i64 { return take(Opt::Some(n + n * n)); }\npub fn g() -> i64 { return take(Opt::None); }\n",
        "module demo;\nrecord Cfg { lvl: u32, base: i64 }\nenum A { A0, A1(u32) }\nenum B { B0, B1(i64) }\npub fn mka(c: Cfg) -> A { return A::A1(c.lvl); }\npub fn mkb(c: Cfg) -> B { return B::B1(c.base + 10); }\n",
        "module demo;\nenum Res { Ok(i64), Err(str) }\npub fn ok(n: i64) -> Res { return Res::Ok(n); }\npub fn err() -> Res { return Res::Err(\"bad\"); }\n",
        "module demo;\nrecord Pt { x: i64, y: i64 }\nenum Sh { Dot, Pair(i64, i64) }\nfn dbl(v: i64) -> i64 { return v + v; }\npub fn f(p: Pt) -> Sh { return Sh::Pair(dbl(p.x), p.y); }\n",
        "module demo; enum Solo { Only } pub fn f() -> Solo { return Solo::Only; }",
        "module demo; enum Dir { N, S, E, W, Up, Down } pub fn a() -> Dir { return Dir::N; } pub fn b() -> Dir { return Dir::Down; } pub fn c() -> Dir { return Dir::E; } pub fn d() -> Dir { return Dir::W; } pub fn e() -> Dir { return Dir::Up; } pub fn g() -> Dir { return Dir::S; }",
        "module demo; enum Color { Red, Green, Blue } enum Light { Red, Amber } pub fn a() -> Color { return Color::Red; } pub fn b() -> Light { return Light::Red; }",
        "module demo; enum Opt1 { None, Some(i64) } enum Opt2 { None, Got(str) } pub fn f() -> Opt1 { return Opt1::None; } pub fn g() -> Opt2 { return Opt2::None; }",
        "module demo; record Box1 { w: i64, h: i64 } enum Box2 { Empty, Full(i64) } pub fn r() -> Box1 { return Box1 { w: 1, h: 2 }; } pub fn e() -> Box2 { return Box2::Full(9); }",
        "module demo; enum E { A(i64) } record E2 { A: i64 } pub fn f() -> E { return E::A(3); } pub fn g() -> E2 { return E2 { A: 3 }; }",
        "module demo; enum Sig { Off, On(bool) } pub fn a() -> Sig { return Sig::Off; } pub fn b() -> Sig { return Sig::On(true); }",
        "module demo; enum Cell { B, Ci(i32), Cu(u32), Cl(i64), Cw(u64), Cf(f64), Cb(bool), Cs(str) } pub fn a() -> Cell { return Cell::Ci(1); } pub fn b() -> Cell { return Cell::Cu(2); } pub fn c() -> Cell { return Cell::Cl(3); } pub fn d() -> Cell { return Cell::Cw(4); } pub fn e() -> Cell { return Cell::Cf(2.5); } pub fn g() -> Cell { return Cell::Cb(true); } pub fn h() -> Cell { return Cell::Cs(\"hi\"); } pub fn k() -> Cell { return Cell::B; }",
        "module demo; enum Tag { T(str, bool, f64) } pub fn f() -> Tag { return Tag::T(\"x\", true, 1.5); }",
        "module demo; record Pt { x: i64, y: i64 } enum Wrap { V(i64) } pub fn f(p: Pt) -> Wrap { return Wrap::V(p.x + p.y); }",
        "module demo; enum Opt { None, Some(i64) } fn useOpt(o: Opt) -> i64 { return 0; } pub fn pass(n: i64) -> i64 { return useOpt(Opt::Some(n + 1)); } pub fn passlet() -> i64 { let o: Opt = Opt::Some(5); return useOpt(o); }",
        "module demo; enum Tri { Dot, Pair(i64, i64), Trip(i64, i64, i64) } fn mk() -> i64 { return 7; } pub fn a() -> Tri { return Tri::Dot; } pub fn b() -> Tri { return Tri::Pair(1, mk()); } pub fn c(n: i64) -> Tri { return Tri::Trip(n, n + 1, n * 2); }",
    ];
    let mut mismatches: Vec<String> = Vec::new();
    let mut rejects: Vec<usize> = Vec::new();
    for (i, src) in fixtures.iter().enumerate() {
        match oracle_graceful(src) {
            None => rejects.push(i),
            Some(orc) => {
                let sig = sigil_records(src);
                if sorted_recs(&sig) != sorted_recs(&orc) {
                    mismatches.push(format!(
                        "[{i}] {src}\n    sigil:  {:?}\n    oracle: {:?}",
                        sorted_recs(&sig),
                        sorted_recs(&orc)
                    ));
                }
            }
        }
    }
    assert!(
        rejects.is_empty(),
        "fixtures rejected by the oracle (out of scope): {rejects:?}"
    );
    assert!(
        mismatches.is_empty(),
        "adversarial fixtures diverged from the oracle:\n{}",
        mismatches.join("\n")
    );
}

/// Adversarial fixtures generated by the pr4a-adversarial-fixtures workflow —
/// control-flow edge cases: AND/OR via nested ifs, deeply nested if/else,
/// comparisons of every scalar kind as conditions, counter/accumulator/two-phase
/// while loops, nested loops, break/continue (guarded, nested), assignment from
/// literal/var/arith/field-access/call-result, expression-statement calls, and
/// control flow that builds + returns a record or enum. Each must type-check in
/// the oracle AND match the SIGIL stream (43 vetted in-scope + matching; one
/// generated fixture using `while x == false {` was dropped — that hits the
/// struct-literal-in-condition parse ambiguity, a parser-layer concern).
#[test]
fn pr4a_adversarial_fixtures_match_oracle() {
    let fixtures: &[&str] = &[
        "module demo;\npub fn andp(p: bool, q: bool) -> i64 { if p { if q { return 1; } else { return 2; } } else { return 3; } }\n",
        "module demo;\npub fn orp(a: bool, b: bool) -> i64 { if a { return 1; } else { if b { return 1; } else { return 0; } } }\n",
        "module demo;\npub fn cmps(i: i64, i2: i64, u: u32, u2: u32, n: i32, n2: i32, w: u64, w2: u64, f: f64, f2: f64) -> i64 { let mut r: i64 = 0; if i < i2 { r = 1; } else {} if u > u2 { r = 2; } else {} if n <= n2 { r = 3; } else {} if w >= w2 { r = 4; } else {} if f == f2 { r = 5; } else {} if i != i2 { r = 6; } else {} return r; }\n",
        "module demo;\npub fn deep(a: i64) -> i64 { let mut r: i64 = 0; if a < 10 { if a < 8 { if a < 6 { if a < 4 { r = 1; } else { r = 2; } } else { r = 3; } } else { r = 4; } } else { r = 5; } return r; }\n",
        "module demo;\npub fn pickmax(x: i64, y: i64) -> i64 { let mut m: i64 = 0; if x < y { m = y; } else { m = x; } return m; }\n",
        "module demo;\npub fn scan(n: i64) -> i64 { let mut i: i64 = 0; let mut acc: i64 = 0; while i < n { if i < 3 { i = i + 1; continue; } else {} if i > 12 { break; } else {} acc = acc + i; i = i + 1; } return acc; }\n",
        "module demo;\npub fn until(n: i64) -> i64 { let mut go: bool = true; let mut i: i64 = 0; while go { i = i + 1; if i >= n { go = false; } else {} } return i; }\n",
        "module demo;\npub fn ugate(p: bool) -> u32 { let mut y: u32 = 0; if p { y = 5; } else { y = 9; } return y; }\n",
        "module demo;\nfn side(n: i64) -> i64 { return n; }\npub fn run(flag: bool, n: i64) -> i64 { if flag { side(1); } else { side(2); } let mut i: i64 = 0; while i < n { side(i); i = i + 1; } return 0; }\n",
        "module demo;\npub fn beq(a: bool, b: bool) -> bool { let mut r: bool = false; if a == b { r = true; } else {} if a != b { r = false; } else {} return r; }\n",
        "module demo;\npub fn fpick(a: f64, b: f64) -> f64 { let mut m: f64 = 0.0; if a < b { m = b + 1.0; } else { m = a; } return m; }\n",
        "module demo;\npub fn grid(rows: i64, cols: i64) -> i64 { let mut total: i64 = 0; let mut r: i64 = 0; if rows > 0 { while r < rows { let mut c: i64 = 0; while c < cols { if c > 100 { break; } else {} total = total + 1; c = c + 1; } r = r + 1; } } else {} return total; }\n",
        "module demo;\nrecord P { lo: i32, hi: i32 }\nfn clamp(v: i32) -> i32 { return v; }\npub fn norm(p: P) -> i32 { let mut out: i32 = 0; if p.lo < p.hi { out = clamp(p.hi); } else { out = p.lo; } return out; }\n",
        "module demo;\npub fn twoways(b: bool, n: i64) -> i64 { if b { let mut i: i64 = 0; while i < n { i = i + 1; } return i; } else { let mut j: i64 = n; while j > 0 { j = j + 1; if j > 50 { break; } else {} } return j; } }\n",
        "module demo;\n\npub fn count_up(n: i64) -> i64 {\n    let mut i: i64 = 0;\n    let mut cnt: i64 = 0;\n    while i < n {\n        cnt = cnt + 1;\n        i = i + 1;\n    }\n    return cnt;\n}\n",
        "module demo;\n\npub fn sum_and_prod(n: i64) -> i64 {\n    let mut i: i64 = 1;\n    let mut acc: i64 = 0;\n    let mut prod: i64 = 1;\n    while i <= n {\n        acc = acc + i;\n        prod = prod * i;\n        i = i + 1;\n    }\n    return acc + prod;\n}\n",
        "module demo;\n\npub fn partition_balance(n: i64) -> i64 {\n    let mut i: i64 = 0;\n    let mut lo: i64 = 0;\n    let mut hi: i64 = 0;\n    while i < n {\n        if i < 5 {\n            lo = lo + i;\n        } else {\n            hi = hi + i;\n        }\n        i = i + 1;\n    }\n    return hi - lo;\n}\n",
        "module demo;\n\npub fn two_phase(n: i64) -> i64 {\n    let mut acc: i64 = 0;\n    let mut i: i64 = 0;\n    while i < n {\n        acc = acc + i;\n        i = i + 1;\n    }\n    let mut j: i64 = 0;\n    while j < n {\n        acc = acc - 1;\n        j = j + 1;\n    }\n    return acc;\n}\n",
        "module demo;\n\npub fn in_band(n: i64, lo: i64, hi: i64) -> i64 {\n    let mut i: i64 = 0;\n    let mut hits: i64 = 0;\n    while i < n {\n        if i > lo {\n            if i < hi {\n                hits = hits + 1;\n            } else {\n            }\n        } else {\n        }\n        i = i + 1;\n    }\n    return hits;\n}\n",
        "module demo;\n\npub fn skip_and_stop(n: i64) -> i64 {\n    let mut i: i64 = 0;\n    let mut acc: i64 = 0;\n    while i < n {\n        i = i + 1;\n        if i == 3 {\n            continue;\n        } else {\n        }\n        if i == 8 {\n            break;\n        } else {\n        }\n        acc = acc + i;\n    }\n    return acc;\n}\n",
        "module demo;\n\npub fn grid_sum(rows: i64, cols: i64) -> i64 {\n    let mut r: i64 = 0;\n    let mut acc: i64 = 0;\n    while r < rows {\n        let mut c: i64 = 0;\n        while c < cols {\n            acc = acc + r * cols + c;\n            c = c + 1;\n        }\n        r = r + 1;\n    }\n    return acc;\n}\n",
        "module demo;\n\nrecord Span { lo: i64, hi: i64 }\n\npub fn span_walk(s: Span) -> i64 {\n    let mut i: i64 = s.lo;\n    let mut acc: i64 = 0;\n    while i < s.hi {\n        acc = acc + i;\n        i = i + 1;\n    }\n    return acc;\n}\n",
        "module demo;\n\nfn weight(k: i64) -> i64 {\n    if k > 0 {\n        return k * 2;\n    } else {\n        return 1;\n    }\n}\n\npub fn weighted(n: i64) -> i64 {\n    let mut i: i64 = 0;\n    let mut acc: i64 = 0;\n    while i < n {\n        let w: i64 = weight(i - 2);\n        acc = acc + w;\n        i = i + 1;\n    }\n    return acc;\n}\n",
        "module demo; pub fn f() -> u32 { let mut a: i64 = 0; let mut b: u32 = 0; let mut c: i32 = 0; let mut d: u64 = 0; let mut e: f64 = 0.0; let mut g: bool = false; let mut h: str = \"\"; a = 7; b = 9; c = 3; d = 11; e = 2.5; g = true; h = \"x\"; return b; }",
        "module demo; pub fn f() -> i64 { let mut acc: i64 = 0; let k: i64 = 4; acc = 1; acc = k; acc = acc + k; acc = acc * 2; return acc; }",
        "module demo; record P { x: i64, y: u32 } pub fn f(p: P) -> i64 { let mut v: i64 = 0; v = p.x; let mut w: u32 = 0; w = p.y; return v; }",
        "module demo; fn gen() -> i64 { return 5; } fn side(n: i64) -> i64 { return n; } pub fn f() -> i64 { let mut v: i64 = 0; side(3); v = gen(); side(v); return v; }",
        "module demo; pub fn f(n: i64) -> i64 { let mut a: i64 = 0; let mut b: i64 = 1; let mut i: i64 = 0; while i < n { let t: i64 = a + b; a = b; b = t; i = i + 1; } return a; }",
        "module demo; pub fn f(c: bool) -> u32 { let mut r: u32 = 0; if c { r = 1; } else { r = 2; } return r; }",
        "module demo; pub fn f() -> f64 { let mut x: f64 = 1.5; let mut y: f64 = 0.0; y = x; x = y + 2.5; y = x * x; return y; }",
        "module demo; fn log(n: i64) -> i64 { return n; } pub fn f(a: bool, b: bool) -> i64 { let mut r: i64 = 0; if a { if b { r = 1; log(r); } else { r = 2; } } else { r = 3; } return r; }",
        "module demo; pub fn f(n: i64) -> i64 { let mut s: i64 = 0; let mut i: i64 = 0; while i < n { i = i + 1; if i < 2 { continue; } else {} if i > 9 { break; } else {} s = s + i; } return s; }",
        "module demo; pub fn f(p: str) -> str { let mut m: str = \"a\"; m = \"b\"; m = p; let mut flag: bool = false; let r: bool = 3 < 5; flag = r; return m; }",
        "module demo;\nrecord Pt { row: i64, col: i64 }\npub fn scan(grid: Pt, w: i64, h: i64) -> i64 {\n    let mut r: i64 = 0;\n    let mut found: i64 = 0;\n    while r < h {\n        let mut c: i64 = 0;\n        while c < w {\n            if c == grid.col {\n                found = r;\n                break;\n            } else {}\n            c = c + 1;\n        }\n        r = r + 1;\n    }\n    return found;\n}\n",
        "module demo;\npub fn collatz(start: i64) -> i64 {\n    let mut n: i64 = start;\n    let mut steps: i64 = 0;\n    while n > 1 {\n        let half: i64 = n - n;\n        if n > 100 {\n            n = n - 1;\n            continue;\n        } else {}\n        n = n - 1;\n        steps = steps + 1;\n    }\n    return steps;\n}\n",
        "module demo;\nrecord Range1 { lo: i64, hi: i64 }\npub fn clampmk(x: i64, r: Range1) -> Range1 {\n    let mut v: i64 = x;\n    if v < r.lo {\n        v = r.lo;\n    } else {\n        if v > r.hi {\n            v = r.hi;\n        } else {}\n    }\n    return Range1 { lo: v, hi: r.hi };\n}\n",
        "module demo;\nenum Status { Idle, Active(i64), Done }\npub fn classify(n: i64, limit: i64) -> Status {\n    let mut acc: i64 = 0;\n    let mut i: i64 = 0;\n    while i < n {\n        acc = acc + i;\n        if acc > limit {\n            break;\n        } else {}\n        i = i + 1;\n    }\n    if acc == 0 {\n        return Status::Idle;\n    } else {\n        if acc > limit {\n            return Status::Active(acc);\n        } else {\n            return Status::Done;\n        }\n    }\n}\n",
        "module demo;\nrecord Cursor { pos: i64, max: i64 }\npub fn advance(c: Cursor) -> i64 {\n    let mut p: i64 = c.pos;\n    while p < c.max {\n        if p == c.max {\n            break;\n        } else {}\n        p = p + 1;\n    }\n    return p;\n}\n",
        "module demo;\nfn record_hit(k: i64) -> i64 { return k; }\npub fn mixed(n: i64, threshold: i64) -> i64 {\n    let mut total: i64 = 0;\n    let mut i: i64 = 0;\n    if n < 0 {\n        return 0;\n    } else {}\n    while i < n {\n        total = total + i;\n        record_hit(total);\n        if total > threshold {\n            break;\n        } else {}\n        i = i + 1;\n    }\n    return total;\n}\n",
        "module demo;\npub fn andlike(a: i64, b: i64, lo: i64, hi: i64) -> i64 {\n    let mut hits: i64 = 0;\n    let mut i: i64 = a;\n    while i < b {\n        if i > lo {\n            if i < hi {\n                hits = hits + 1;\n            } else {\n                break;\n            }\n        } else {}\n        i = i + 1;\n    }\n    return hits;\n}\n",
        "module demo;\npub fn evens(n: i64) -> i64 {\n    let mut i: i64 = 0;\n    let mut cnt: i64 = 0;\n    while i < n {\n        let m: i64 = i - i;\n        i = i + 1;\n        if m == 0 {\n            if i > 5 {\n                break;\n            } else {}\n            continue;\n        } else {}\n        cnt = cnt + 1;\n    }\n    return cnt;\n}\n",
        "module demo;\npub fn grid_walk(w: i64, h: i64, target: i64) -> i64 {\n    let mut y: i64 = 0;\n    let mut steps: i64 = 0;\n    while y < h {\n        let mut x: i64 = 0;\n        while x < w {\n            steps = steps + 1;\n            if steps == target {\n                break;\n            } else {}\n            x = x + 1;\n        }\n        if steps == target {\n            break;\n        } else {}\n        y = y + 1;\n    }\n    return steps;\n}\n",
        "module demo;\nrecord Acc1 { sum: i64, n: i64 }\nfn step(v: i64) -> i64 { return v + 1; }\npub fn fold(bound: i64) -> Acc1 {\n    let mut s: i64 = 0;\n    let mut k: i64 = 0;\n    while k < bound {\n        s = s + step(k);\n        k = k + 1;\n    }\n    return Acc1 { sum: s, n: k };\n}\n",
    ];
    let mut mismatches: Vec<String> = Vec::new();
    let mut rejects: Vec<usize> = Vec::new();
    for (i, src) in fixtures.iter().enumerate() {
        match oracle_graceful(src) {
            None => rejects.push(i),
            Some(orc) => {
                let sig = sigil_records(src);
                if sorted_recs(&sig) != sorted_recs(&orc) {
                    mismatches.push(format!(
                        "[{i}] {src}\n    sigil:  {:?}\n    oracle: {:?}",
                        sorted_recs(&sig),
                        sorted_recs(&orc)
                    ));
                }
            }
        }
    }
    assert!(
        rejects.is_empty(),
        "fixtures rejected by the oracle (out of scope): {rejects:?}"
    );
    assert!(
        mismatches.is_empty(),
        "adversarial fixtures diverged from the oracle:\n{}",
        mismatches.join("\n")
    );
}

/// Adversarial fixtures generated by the pr4b-adversarial-fixtures workflow —
/// match edge cases: integer/string literal patterns + wildcard, binding patterns
/// (used in the body, in a guard, on non-i64 scrutinees), multiple guarded arms,
/// enum unit-variant matches (2- and 6-variant, exhaustive or `_`-terminated),
/// matching a record field, matches inside while loops (with break/continue),
/// nested matches, and arms that assign a mut local returned after the match. Each
/// must type-check in the oracle AND match the SIGIL stream (46 vetted in-scope +
/// matching; one generated fixture comparing an `i32` binding to a bare `0`
/// literal was dropped — the oracle pins that literal to i32 while the SIGIL
/// comparison arm defaults it to i64, a pre-existing binary int-literal-pinning
/// gap orthogonal to match, to be fixed before PR-5).
#[test]
fn pr4b_adversarial_fixtures_match_oracle() {
    let fixtures: &[&str] = &[
        "module demo;\npub fn classify(n: i64) -> i64 { match n { 0 => { let z: i64 = 100; return z; }, 1 => { let a: i64 = 2; let b: i64 = 3; return a * b + n; }, 2 => { return n + n; }, _ => { let r: i64 = n - 1; return r; } } }\n",
        "module demo;\npub fn route(s: str) -> i64 { match s { \"a\" => { let x: i64 = 1; return x + 1; }, \"b\" => { let y: i64 = 10; let z: i64 = 20; return y + z; }, _ => { return 0; } } }\n",
        "module demo;\npub fn fi(n: u32) -> u32 { match n { 0 => { return 0; }, 7 => { let k: u32 = n + 1; return k; }, _ => { return n; } } }\npub fn fs(s: str) -> i64 { match s { \"x\" => { return 1; }, \"y\" => { return 2; }, _ => { return 3; } } }\n",
        "module demo;\npub fn bind(n: i64) -> i64 { match n { 0 => { return 0; }, m => { let d: i64 = m * 2; return d + m; } } }\n",
        "module demo;\npub fn graded(n: i64) -> i64 { match n { v if v < 0 => { return 0; }, v if v < 10 => { let t: i64 = v + 1; return t; }, v if v < 100 => { return v * 2; }, _ => { return 999; } } }\n",
        "module demo;\npub fn grid(x: i64, y: i64) -> i64 { match x { 0 => { match y { 0 => { return 1; }, _ => { return 2; } } }, _ => { let s: i64 = x + y; return s; } } }\n",
        "module demo;\nenum Color { Red, Green, Blue }\npub fn rank(c: Color) -> i64 { match c { Color::Red => { let r: i64 = 1; return r; }, Color::Green => { return 2; }, Color::Blue => { return 3; } } }\npub fn step(n: i64) -> i64 { match n { 0 => { return 0; }, 1 => { return 10; }, _ => { return n - 1; } } }\n",
        "module demo;\nenum Tag { A, B, C, D }\npub fn weigh(t: Tag, base: i64) -> i64 { match t { Tag::A => { return base; }, Tag::B => { let w: i64 = base + 5; return w; }, _ => { let w: i64 = base * 2; return w; } } }\n",
        "module demo;\npub fn churn(n: i64) -> i64 { match n { 0 => { return 0; }, k => { let mut i: i64 = 0; let mut acc: i64 = 0; while i < k { acc = acc + i; i = i + 1; } if acc > 100 { return 100; } else { return acc; } } } }\n",
        "module demo; pub fn f(x: i64) -> i64 { match x { n => { return n + 1; } } }",
        "module demo; pub fn f(x: i64) -> i64 { match x { n if n > 10 => { return n; }, _ => { return 0; } } }",
        "module demo; pub fn f(x: i64) -> i64 { match x { n if n > 100 => { return 3; }, n if n > 10 => { return 2; }, n if n > 0 => { return 1; }, m => { return m; } } }",
        "module demo; pub fn f(x: i64) -> i64 { match x { n if n + 1 > 5 => { return n + 2; }, _ => { return 0; } } }",
        "module demo; pub fn f(x: u32, lim: u32) -> u32 { match x { n if n > lim => { return n; }, m => { return m; } } }",
        "module demo; pub fn f(x: i32, hi: i32) -> i32 { match x { n if n < hi => { return hi; }, m => { return m; } } }",
        "module demo; pub fn f(x: i64) -> i64 { match x { 0 => { return 100; }, 1 => { return 200; }, n => { return n; } } }",
        "module demo; pub fn f(x: i64, lo: i64) -> i64 { match x { n if n > lo => { return n; }, _ => { return lo; } } }",
        "module demo; pub fn f(x: i64, y: i64) -> i64 { match x { n if n > 0 => { match y { m if m > n => { return m; }, _ => { return n; } } }, _ => { return 0; } } }",
        "module demo; pub fn f(s: str) -> str { match s { \"a\" => { return \"x\"; }, n => { return n; } } }",
        "module demo; pub fn f(x: u64, base: u64) -> u64 { match x { n if n > base => { return n; }, m => { return base; } } }",
        "module demo; pub fn f(x: i32, lo: i32, hi: i32) -> i32 { match x { n if n > hi => { return n; }, k if k < lo => { return lo; }, m => { return m; } } }",
        "module demo; pub fn f(x: i64) -> i64 { match x { n if n > 0 => { let mut i: i64 = 0; let mut s: i64 = 0; while i < n { s = s + i; i = i + 1; } return s; }, _ => { return 0; } } }",
        "module demo; pub fn f(s: str) -> i64 { match s { n if n == \"hi\" => { return 1; }, _ => { return 0; } } }",
        "module demo; pub fn f(x: i64) -> i64 { match x { n if n > 0 => { if n > 100 { return 1; } else { return n; } }, _ => { return 0; } } }",
        "module demo; enum Bit { Off, On } pub fn val(b: Bit) -> i64 { match b { Bit::Off => { return 0; }, Bit::On => { return 1; } } }",
        "module demo; enum Dir { N, S, E, W, Up, Down } pub fn code(d: Dir) -> i64 { match d { Dir::N => { return 10; }, Dir::S => { return 20; }, Dir::E => { return 30; }, Dir::W => { return 40; }, Dir::Up => { return 50; }, Dir::Down => { return 60; } } }",
        "module demo; enum Light { Red, Yellow, Green, Off, Broken } pub fn go(l: Light) -> i64 { match l { Light::Red => { return 1; }, Light::Yellow => { return 2; }, _ => { return 0; } } }",
        "module demo; enum Color { Red, Green, Blue } enum Mood { Calm, Wild } pub fn ci(c: Color) -> i64 { match c { Color::Red => { return 1; }, Color::Green => { return 2; }, Color::Blue => { return 3; } } } pub fn mi(m: Mood) -> i64 { match m { Mood::Calm => { return 100; }, Mood::Wild => { return 200; } } }",
        "module demo; record Item { tag: i64, n: i64 } pub fn classify(p: Item) -> i64 { match p.tag { 0 => { return 100; }, 1 => { return 200; }, _ => { return p.n; } } }",
        "module demo; enum Op { Add, Sub, Mul } pub fn apply(o: Op, a: i64, b: i64) -> i64 { match o { Op::Add => { return a + b; }, Op::Sub => { return a - b; }, Op::Mul => { return a * b; } } }",
        "module demo; enum Tag { P, Q } pub fn nest(t: Tag, n: i64) -> i64 { match t { Tag::P => { match n { 0 => { return 100; }, _ => { return 101; } } }, Tag::Q => { return 200; } } }",
        "module demo; enum Step { One, Two, Three } pub fn run(s: Step, base: i64) -> i64 { match s { Step::One => { let r: i64 = base + 1; return r; }, Step::Two => { let r: i64 = base * 2; return r; }, Step::Three => { let r: i64 = base - 3; return r; } } }",
        "module demo; enum Solo { Only } pub fn f(s: Solo) -> i64 { match s { Solo::Only => { return 42; } } }",
        "module demo; enum Level { Lo, Hi } pub fn lvl(x: Level, a: u32, b: u32) -> u32 { match x { Level::Lo => { return a; }, Level::Hi => { return a + b; } } }",
        "module demo; enum Cmd { Go, Stop } pub fn drive(c: Cmd, n: i64) -> i64 { let mut i: i64 = 0; let mut acc: i64 = 0; while i < n { match c { Cmd::Go => { acc = acc + 1; }, Cmd::Stop => { acc = acc - 1; } } i = i + 1; } return acc; }",
        "module demo; enum Color { Red, Green, Blue } fn rank(c: Color) -> i64 { return 0; } pub fn f(c: Color, hot: bool) -> i64 { match c { v if hot => { return rank(v); }, _ => { return 9; } } }",
        "module demo;\npub fn drain(n: i64) -> i64 {\n    let mut acc: i64 = 0;\n    let mut i: i64 = 0;\n    while i < n {\n        match i {\n            0 => { acc = acc + 100; },\n            1 => { acc = acc + 10; },\n            k => { acc = acc + k; }\n        }\n        i = i + 1;\n    }\n    return acc;\n}\n",
        "module demo;\npub fn route(x: i64, y: i64) -> i64 {\n    match x {\n        0 => {\n            match y {\n                0 => { return 1; },\n                _ => { return 2; }\n            }\n        },\n        n => {\n            match y {\n                0 => { return n; },\n                m => { return n + m; }\n            }\n        }\n    }\n}\n",
        "module demo;\npub fn scan(n: i64) -> i64 {\n    let mut i: i64 = 0;\n    let mut acc: i64 = 0;\n    while i < n {\n        match i {\n            3 => {\n                i = i + 1;\n                continue;\n            },\n            k => {\n                if k > 20 {\n                    break;\n                } else {}\n                acc = acc + k;\n            }\n        }\n        i = i + 1;\n    }\n    return acc;\n}\n",
        "module demo;\npub fn fold(x: i64) -> i64 {\n    match x {\n        n => {\n            let mut i: i64 = 0;\n            let mut s: i64 = 0;\n            while i < n {\n                s = s + i;\n                i = i + 1;\n            }\n            return s;\n        }\n    }\n}\n",
        "module demo;\npub fn band(x: i64) -> i64 {\n    match x {\n        n if n < 0 => { return 0; },\n        n if n < 10 => {\n            if n > 5 {\n                return n + 100;\n            } else {\n                return n;\n            }\n        },\n        n if n < 100 => { return n * 2; },\n        _ => { return 999; }\n    }\n}\n",
        "module demo;\nenum Color { Red, Green, Blue }\npub fn weight(c: Color) -> i64 {\n    let mut w: i64 = 0;\n    match c {\n        Color::Red => { w = 1; },\n        Color::Green => { w = 2; },\n        Color::Blue => { w = 3; }\n    }\n    return w;\n}\n",
        "module demo;\npub fn tally(x: i64) -> i64 {\n    let mut out: i64 = 0;\n    match x {\n        0 => { out = 10; },\n        1 => {\n            if out < 5 {\n                out = 20;\n            } else {\n                out = 25;\n            }\n        },\n        n => { out = n + 1; }\n    }\n    return out;\n}\n",
        "module demo;\npub fn deep(flag: bool, n: i64) -> i64 {\n    let mut acc: i64 = 0;\n    if flag {\n        let mut i: i64 = 0;\n        while i < n {\n            match i {\n                0 => {\n                    if n > 3 {\n                        acc = acc + 5;\n                    } else {\n                        acc = acc + 1;\n                    }\n                },\n                k => { acc = acc + k; }\n            }\n            i = i + 1;\n        }\n    } else {\n        acc = n;\n    }\n    return acc;\n}\n",
        "module demo;\npub fn dispatch(s: str, n: i64) -> i64 {\n    match s {\n        \"add\" => {\n            match n {\n                0 => { return 100; },\n                _ => { return n + 1; }\n            }\n        },\n        \"sub\" => {\n            match n {\n                0 => { return 0; },\n                m => { return m - 1; }\n            }\n        },\n        _ => { return n; }\n    }\n}\n",
        "module demo;\npub fn churn(x: i64) -> i64 {\n    match x {\n        seed if seed > 0 => {\n            let mut acc: i64 = 0;\n            let mut i: i64 = 0;\n            while i < seed {\n                match i {\n                    0 => { acc = acc + 1; },\n                    j => {\n                        if j > 50 {\n                            break;\n                        } else {\n                            acc = acc + j;\n                        }\n                    }\n                }\n                i = i + 1;\n            }\n            return acc;\n        },\n        _ => { return 0; }\n    }\n}\n",
    ];
    let mut mismatches: Vec<String> = Vec::new();
    let mut rejects: Vec<usize> = Vec::new();
    for (i, src) in fixtures.iter().enumerate() {
        match oracle_graceful(src) {
            None => rejects.push(i),
            Some(orc) => {
                let sig = sigil_records(src);
                if sorted_recs(&sig) != sorted_recs(&orc) {
                    mismatches.push(format!(
                        "[{i}] {src}\n    sigil:  {:?}\n    oracle: {:?}",
                        sorted_recs(&sig),
                        sorted_recs(&orc)
                    ));
                }
            }
        }
    }
    assert!(
        rejects.is_empty(),
        "fixtures rejected by the oracle (out of scope): {rejects:?}"
    );
    assert!(
        mismatches.is_empty(),
        "adversarial fixtures diverged from the oracle:\n{}",
        mismatches.join("\n")
    );
}

/// Adversarial fixtures generated by the pr4c-adversarial-fixtures workflow —
/// binary int-literal-pinning edge cases: non-i64 (u32/i32/u64) values compared to
/// or combined with bare integer literals in either operand position, across
/// return / if- / while-conditions / match guards / non-i64-annotated lets /
/// record field-inits / enum payloads / call arguments; nested all-literal
/// subtrees that must inherit a concrete sibling's type (`a + 1 - 2 * 3`); deep
/// mixed nesting; and i64 / f64 / both-literal controls that stay i64. Each must
/// type-check in the oracle AND match the SIGIL stream (31 vetted in-scope +
/// matching; one fixture using `cap` — a reserved keyword — as a field name was
/// dropped).
#[test]
fn pr4c_adversarial_fixtures_match_oracle() {
    let fixtures: &[&str] = &[
        "module demo;\n\n// Comparison in RETURN position, literal on RIGHT and LEFT of u32 values.\npub fn cmp_ret(u: u32, v: u32) -> bool {\n    if u < 5 {\n        return 5 < v;\n    } else {\n    }\n    return u >= 10;\n}\n",
        "module demo;\n\n// Equality / inequality on i32, literal in BOTH operand positions, in returns.\npub fn eq_i32(a: i32, b: i32) -> bool {\n    if a == 7 {\n        return 7 != b;\n    } else {\n    }\n    if 0 == a {\n        return b == 0;\n    } else {\n    }\n    return a != 99;\n}\n",
        "module demo;\n\n// u64 comparisons driving an IF condition, literal on each side; both branches return.\npub fn if_cond_u64(n: u64) -> bool {\n    if n > 100 {\n        return true;\n    } else {\n        if 3 <= n {\n            return false;\n        } else {\n            return n == 0;\n        }\n    }\n}\n",
        "module demo;\n\n// WHILE condition comparing a mutable u32 to a literal (literal on right), then a\n// final return that compares a literal on the LEFT to the same u32.\npub fn loop_u32(lim: u32) -> bool {\n    let mut w: u32 = 0;\n    while w < lim {\n        w = w + 1;\n    }\n    return 0 < w;\n}\n",
        "module demo;\n\n// match-arm GUARDS comparing the bound u32 scrutinee to literals, literal on both\n// sides across arms; exhaustive integer match ends with `_`.\npub fn guard_u32(u: u32) -> i32 {\n    match u {\n        n if n < 4 => { return 1; },\n        n if 8 == n => { return 2; },\n        n if 16 <= n => { return 3; },\n        _ => { return 0; },\n    }\n}\n",
        "module demo;\n\nfn count() -> u32 { return 3; }\n\n// Comparison of a FUNCTION-CALL result (u32 return) to a literal, both positions,\n// in an if-condition and the final return.\npub fn call_cmp() -> bool {\n    if count() < 5 {\n        return 7 > count();\n    } else {\n    }\n    return count() != 0;\n}\n",
        "module demo;\n\n// Mixed ordering + equality on a u64 across several if-conditions, literal\n// alternating sides; every path returns a bool.\npub fn ord_mix_u64(s: u64) -> bool {\n    if 2 < s {\n        if s <= 50 {\n            return s != 9;\n        } else {\n            return 50 >= s;\n        }\n    } else {\n        return s == 1;\n    }\n}\n",
        "module demo;\n\n// A `let` with a NON-i64 annotation seeds a u32 local; later it is compared to\n// literals (both positions) in a while-condition, an if-condition, and the return.\npub fn let_then_cmp(hi: u32) -> bool {\n    let lo: u32 = 1;\n    let mut q: u32 = lo;\n    while q < hi {\n        if 3 == q {\n            q = q + 2;\n        } else {\n            q = q + 1;\n        }\n    }\n    return q >= 4;\n}\n",
        "module demo;\n\nrecord Pt { x: i32, y: i32 }\n\n// Field comparisons of an i32 record reached through a parameter, literal on each\n// side, nested across a while-condition guard, an if, and the return.\npub fn pt_scan(p: Pt) -> bool {\n    let mut a: i32 = p.x;\n    while a < 20 {\n        if 0 == a {\n            a = a + 5;\n        } else {\n            a = a + 1;\n        }\n    }\n    if p.y != 0 {\n        return a > 10;\n    } else {\n        return 7 <= a;\n    }\n}\n",
        "module demo;\n\nfn pick(b: bool) -> u32 {\n    if b {\n        return 2;\n    } else {\n        return 4;\n    }\n}\n\n// Comparisons of BOTH a u32 parameter and a u32 call-result to bare literals\n// (literal on both sides) gated through a match guard and the return.\npub fn dual_u32(u: u32, flag: bool) -> bool {\n    match u {\n        n if pick(flag) < 3 => { return 9 > n; },\n        n if n == 6 => { return pick(flag) != 0; },\n        _ => { return 5 <= u; },\n    }\n}\n",
        "module demo;\npub fn uadd(y: u32) -> u32 { return y + 5; }\npub fn uaddrev(y: u32) -> u32 { return 5 + y; }\npub fn umul(y: u32) -> u32 { return y * 4; }\npub fn umulrev(y: u32) -> u32 { return 6 * y; }\npub fn usub(y: u32) -> u32 { return y - 2; }\n",
        "module demo;\npub fn ichain(a: i32) -> i32 { return a + 1 - 2 * 3; }\npub fn uchain(y: u32) -> u32 { return y * 2 + 3 - 1; }\npub fn wchain(w: u64) -> u64 { return 10 + w - 4 * 2; }\n",
        "module demo;\npub fn deep(y: u32) -> u32 { return y + 1 * 2 - 3 + 4 * 5; }\npub fn deepi(a: i32) -> i32 { return 9 - a * 2 + 7 - 1; }\n",
        "module demo;\npub fn letu(y: u32) -> u32 { let s: u32 = y + 5; return s; }\npub fn leti(a: i32) -> i32 { let q: i32 = 3 + a; return q; }\npub fn letw(w: u64) -> u64 { let acc: u64 = w * 2 - 1; return acc; }\npub fn letmul(y: u32) -> u32 { let p: u32 = 7 * y; return p; }\n",
        "module demo;\nrecord Vec2 { ux: u32, uy: u32 }\npub fn build(p: Vec2) -> Vec2 { return Vec2 { ux: p.ux + 1, uy: 2 * p.uy }; }\npub fn fromparam(y: u32) -> Vec2 { return Vec2 { ux: y - 1, uy: y * 3 + 2 }; }\n",
        "module demo;\nenum Tag { Unit, Pay(u32) }\npub fn wrap(y: u32) -> Tag { return Tag::Pay(y * 3); }\npub fn wrap2(y: u32) -> Tag { return Tag::Pay(y + 4 - 1); }\npub fn wrev(y: u32) -> Tag { return Tag::Pay(8 + y); }\n",
        "module demo;\nfn idu(x: u32) -> u32 { return x; }\nfn addu(a: u32, b: u32) -> u32 { return a + b; }\npub fn callarg(y: u32) -> u32 { return idu(y + 5); }\npub fn calltwo(y: u32) -> u32 { return addu(y * 2, 3 + y); }\npub fn nest(y: u32) -> u32 { return idu(idu(y - 1) * 4); }\n",
        "module demo;\npub fn cond(y: u32) -> u32 { let mut acc: u32 = 0; if y + 1 < 9 { acc = y; } else { acc = y * 2; } return acc; }\npub fn loopcond(w: u64) -> u64 { let mut n: u64 = w; while n - 1 > 3 { n = n - 1; } return n; }\n",
        "module demo;\npub fn guard(n: i32) -> i32 { match n { 0 => { return 0; }, v if v * 2 < 10 => { return v; }, _ => { return 1; } } }\npub fn guardu(u: u32) -> u32 { match u { 0 => { return 0; }, v if v + 3 > 5 => { return v; }, _ => { return 1; } } }\n",
        "module demo;\npub fn i32lit(a: i32) -> i32 { return a + 100; }\npub fn u32lit(y: u32) -> u32 { return 200 * y; }\npub fn u64lit(w: u64) -> u64 { return w - 9000000000; }\npub fn i32big(a: i32) -> i32 { return a * 2147483647; }\n",
        "module demo;\npub fn mixed(y: u32) -> bool { return y + 2 < y * 3; }\npub fn mixedi(a: i32) -> bool { return a - 1 == a + 1; }\npub fn poly(y: u32) -> u32 { let mut t: u32 = y; t = t + 1; t = t * 2; t = t - 3; return t + 4; }\n",
        "module demo;\n\npub fn count_up(lim: u32) -> u32 {\n  let mut y: u32 = 0;\n  while y < lim {\n    y = y + 1;\n  }\n  return y + 2;\n}\n",
        "module demo;\n\npub fn classify(u: u32) -> i64 {\n  match u {\n    0 => { return 100; },\n    _ => {\n      if u < 10 {\n        return 1;\n      } else {\n        return 7;\n      }\n    },\n  }\n}\n",
        "module demo;\n\npub fn step(n: i32) -> i32 {\n  let mut a: i32 = n;\n  while a > 0 {\n    a = a - 3;\n  }\n  return a + 5 - 1;\n}\n",
        "module demo;\n\npub fn guarded(v: u64) -> u64 {\n  match v {\n    1 => { return v + 9; },\n    _ => { return v * 2 + 4; },\n  }\n}\n",
        "module demo;\n\npub fn pass_lit(u: u32) -> u32 {\n  return u + 1;\n}\n\npub fn caller() -> u32 {\n  let w: u32 = 8;\n  return pass_lit(w) + 3;\n}\n",
        "module demo;\n\npub fn controls(u: u32, x: i64, f: f64) -> bool {\n  let p: bool = 3 < 5;\n  let q: i64 = 2 + 2;\n  let g: f64 = f + 2.5;\n  let h: i64 = x + 7;\n  if u < 4 {\n    return p;\n  } else {\n    if q > 1 {\n      return g > 0.0;\n    } else {\n      return h > 0;\n    }\n  }\n}\n",
        "module demo;\n\npub fn nested(u: u32, v: u64, b: i32) -> u32 {\n  let s: u32 = u + 2 * 3 - 1;\n  let mut acc: u32 = 0;\n  while acc < s {\n    if acc > 10 {\n      acc = acc + 5;\n    } else {\n      acc = acc + 1;\n    }\n  }\n  return acc + 7;\n}\n",
        "module demo;\n\nrecord Box { w: u32, h: i32 }\n\npub fn make() -> u32 {\n  let b: Box = Box { w: 4 + 1, h: 9 - 2 };\n  return b.w + 3;\n}\n",
        "module demo;\n\nenum Sig { Off, On(u32) }\n\npub fn build(u: u32) -> Sig {\n  if u < 5 {\n    return Sig::On(u + 1);\n  } else {\n    return Sig::On(u * 2 + 3);\n  }\n}\n",
        "module demo;\n\npub fn deep(u: u32, v: u64, a: i32, x: i64, f: f64) -> u32 {\n  let mut y: u32 = 0;\n  while y < u {\n    if v > 100 {\n      y = y + 2;\n    } else {\n      if a < 3 {\n        y = y + 1;\n      } else {\n        let ctl: i64 = x + 7;\n        let fctl: f64 = f + 2.5;\n        if ctl > 0 {\n          y = y + ((u + 4) * 1 - 3);\n        } else {\n          if fctl > 1.0 {\n            y = y + 5;\n          } else {\n            y = y + 6;\n          }\n        }\n      }\n    }\n  }\n  return y + 9 - 2;\n}\n",
    ];
    let mut mismatches: Vec<String> = Vec::new();
    let mut rejects: Vec<usize> = Vec::new();
    for (i, src) in fixtures.iter().enumerate() {
        match oracle_graceful(src) {
            None => rejects.push(i),
            Some(orc) => {
                let sig = sigil_records(src);
                if sorted_recs(&sig) != sorted_recs(&orc) {
                    mismatches.push(format!(
                        "[{i}] {src}\n    sigil:  {:?}\n    oracle: {:?}",
                        sorted_recs(&sig),
                        sorted_recs(&orc)
                    ));
                }
            }
        }
    }
    assert!(
        rejects.is_empty(),
        "fixtures rejected by the oracle (out of scope): {rejects:?}"
    );
    assert!(
        mismatches.is_empty(),
        "adversarial fixtures diverged from the oracle:\n{}",
        mismatches.join("\n")
    );
}

// ── PR-5a: the diagnostics differential (exact T-code parity, ET-T3) ──────────

#[test]
fn pr5a_mismatch_codes_match_oracle() {
    // Each fixture is a monomorphic program the oracle REJECTS with exactly the
    // PR-5a expected-known-mismatch codes — a let-annotation mismatch (T041), an
    // assignment mismatch (T045), a return-type mismatch (T049, incl. inside a
    // match arm body), or a non-bool if/while condition (T050/T051). The SIGIL
    // checker must emit the IDENTICAL core-owned code set (zero false-accept).
    let fixtures: &[&str] = &[
        // T041 — let-binding type mismatch (scalar annotation).
        "module m; fn f() -> i64 { let x: bool = 5; return 0; }",
        "module m; fn f() -> i64 { let x: i64 = true; return 0; }",
        "module m; fn f() -> i64 { let s: str = 5; return 0; }",
        "module m; fn f(a: i32) -> i64 { let b: i64 = a; return 0; }",
        // T045 — assignment type mismatch.
        "module m; fn f() -> i64 { let mut x: i64 = 0; x = true; return x; }",
        "module m; fn f(a: i32) -> i64 { let mut x: i32 = a; x = true; return 0; }",
        // T049 — return-type mismatch.
        "module m; fn f() -> bool { return 5; }",
        "module m; fn f() -> i64 { return true; }",
        "module m; fn f() -> i64 { return \"hi\"; }",
        "module m; fn f(a: i32) -> i64 { return a; }",
        // T049 inside a match arm body (exhaustive via wildcard, so no T087).
        "module m; fn f(n: i64) -> i64 { match n { 0 => { return true; }, _ => { return 0; } } }",
        // T050 / T051 — non-bool condition.
        "module m; fn f() -> i64 { if 5 { return 1; } else { return 0; } }",
        "module m; fn f() -> i64 { while 5 { return 1; } return 0; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5a fixture #{i} expected an oracle rejection but got none:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5a fixture #{i} T-code parity:\n{src}"
        );
    }
}

#[test]
fn pr5a_wellformed_programs_emit_no_codes() {
    // Zero false-POSITIVE: known-good monomorphic programs exercising every PR-5a
    // detection site (let pin, return, assign, if/while condition, match arms,
    // literal-pinned assignment) must yield NO core-owned diagnostics on EITHER
    // side — the SIGIL checker must not reject what the oracle accepts.
    let fixtures: &[&str] = &[
        "module m; fn f() -> u32 { let x: u32 = 5; return x; }",
        "module m; fn f() -> i64 { let x: i64 = 5; return x; }",
        "module m; fn f(a: i32) -> i32 { let b: i32 = a; return b; }",
        "module m; fn f() -> bool { return true; }",
        "module m; fn f(b: bool) -> i64 { if b { return 1; } else { return 0; } }",
        "module m; fn f(n: i64) -> i64 { let mut s: i64 = n; while s > 0 { s = s - 1; } return s; }",
        "module m; fn f() -> i64 { let mut x: u32 = 0; x = 5; return 0; }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { return 1; }, _ => { return n; } } }",
        "module m; fn f(a: i64, b: i64) -> bool { return a < b; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5a positive #{i} was unexpectedly rejected by the oracle:\n{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5a positive #{i} produced a spurious SIGIL diagnostic:\n{src}"
        );
    }
}

#[test]
fn pr5a_adversarial_neg_codes_match_oracle() {
    // Workflow-generated, oracle-vetted rejections spanning every PR-5a code with
    // maximal type-pair diversity: f64/str/bool let mismatches, no-int-widening
    // (i32->u32, i64->u64), bool/f64/record/enum non-bool conditions, return
    // mismatches nested in if/while/match bodies, record-field-place assignment
    // (p.x = bool), shadow-then-mismatch, and `return 5` into an enum return type.
    let fixtures: &[&str] = &[
        "module m; fn f() -> i64 { let x: bool = 5; return 0; }",
        "module m; fn f() -> i64 { let x: f64 = true; return 0; }",
        "module m; fn f() -> i64 { let x: str = 1.5; return 0; }",
        "module m; fn f(a: i32) -> i64 { let b: u32 = a; return 0; }",
        "module m; fn f(p: i64) -> i64 { let mut x: i64 = p; x = true; return 0; }",
        "module m; fn f() -> i64 { let mut x: bool = true; x = 1.5; return 0; }",
        "module m; fn f(a: i32) -> i64 { let mut x: i64 = 0; x = a; return 0; }",
        "module m; fn f() -> i64 { let x: i64 = 0; let mut x: u32 = 0; x = true; return 0; }",
        "module m; fn f() -> bool { return 5; }",
        "module m; fn f(a: i64) -> u64 { return a; }",
        "module m; fn f(b: bool) -> i64 { if b { return true; } else { return 0; } }",
        "module m; fn f(b: bool) -> str { while b { return 5; } return \"y\"; }",
        "module m; fn f(n: i64) -> u32 { match n { 0 => { return true; }, _ => { return 5; } } }",
        "module m; fn f() -> i64 { if 1.5 { return 1; } else { return 0; } }",
        "module m; fn f(n: i64) -> i64 { while n { return 1; } return 0; }",
        "module m; record P { x: i64 } fn f(p: P) -> i64 { if p { return 1; } else { return 0; } }",
        "module m; enum E { A, B } fn f(e: E) -> i64 { while e { return 1; } return 0; }",
        "module m; fn f() -> i64 { let x: f64 = 5; return 0; }",
        "module m; fn f() -> i64 { let x: bool = 0; return 0; }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { let mut i: i64 = 0; while i < n { if i > 5 { return true; } else { i = i + 1; } } return 0; }, _ => { return n; } } }",
        "module m; record P { x: i64, y: i64 } fn f() -> i64 { let mut p: P = P { x: 1, y: 2 }; p.x = true; return p.x; }",
        "module m; enum E { A(i64), B } fn mk() -> E { return 5; }",
        "module m; fn f() -> i64 { let x: i64 = 3; let x: i32 = 10; return x; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5a adversarial neg #{i} expected an oracle rejection but got none:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5a adversarial neg #{i} T-code parity:\n{src}"
        );
    }
}

#[test]
fn pr5a_adversarial_pos_emit_no_codes() {
    // Workflow-generated, oracle-vetted well-typed programs placed right at the
    // assignability boundary — literal pinning to every machine int via
    // let/return/assign, all-literal arithmetic, same-type variable flow, f64
    // (`f64 = 5.0` accepted where `f64 = 5` is not), valid bool conditions,
    // call/field/record/enum returns at the exact declared type, deeply nested
    // control flow, record-field-place assignment, and shadow-then-rebind. The
    // SIGIL checker must emit NO spurious diagnostic on any of them.
    let fixtures: &[&str] = &[
        "module m;\npub fn ai() -> i32 { let x: i32 = 5; return x; }\npub fn bu() -> u32 { let x: u32 = 5; return x; }\npub fn cl() -> i64 { let x: i64 = 5; return x; }\npub fn du() -> u64 { let x: u64 = 5; return x; }\n",
        "module m;\npub fn ri() -> i32 { return 5; }\npub fn ru() -> u32 { return 5; }\npub fn rl() -> i64 { return 5; }\npub fn rlu() -> u64 { return 5; }\n",
        "module m;\npub fn fi() -> i32 { let mut y: i32 = 0; y = 7; return y; }\npub fn fu() -> u32 { let mut y: u32 = 0; y = 7; return y; }\npub fn fl() -> i64 { let mut y: i64 = 0; y = 7; return y; }\npub fn flu() -> u64 { let mut y: u64 = 0; y = 7; return y; }\n",
        "module m;\npub fn ai() -> i32 { let x: i32 = 5 + 3; return x; }\npub fn au() -> u32 { let x: u32 = 2 * 3 - 1; return x; }\npub fn al() -> i64 { let x: i64 = 4 + 5 * 6; return x; }\npub fn alu() -> u64 { let x: u64 = 10 - 2 + 1; return x; }\n",
        "module m;\npub fn ri() -> i32 { return 5 + 3; }\npub fn ru() -> u32 { return 2 * 3; }\npub fn rl() -> i64 { return 4 + 5 * 6; }\npub fn rlu() -> u64 { return 10 - 2 + 1; }\n",
        "module m;\npub fn fi() -> i32 { let mut y: i32 = 0; y = 5 + 3; return y; }\npub fn fu() -> u32 { let mut y: u32 = 1; y = 2 * 3; return y; }\npub fn fl() -> i64 { let mut y: i64 = 0; y = 4 + 5 * 6; return y; }\npub fn flu() -> u64 { let mut y: u64 = 0; y = 10 - 2 + 1; return y; }\n",
        "module m;\npub fn vi(a: i32) -> i32 { let b: i32 = a; return b; }\npub fn vu(a: u32) -> u32 { let mut b: u32 = 0; b = a; return b; }\npub fn vl(a: i64) -> i64 { return a; }\npub fn vs(s: str) -> str { let t: str = s; return t; }\npub fn vb(p: bool) -> bool { let q: bool = p; return q; }\n",
        "module m;\npub fn d() -> f64 { let d: f64 = 1.5; return d; }\npub fn idf(p: f64) -> f64 { return p; }\npub fn viaf(p: f64) -> f64 { let q: f64 = p; let mut r: f64 = 0.0; r = q; return r; }\n",
        "module m;\npub fn cond_param(b: bool) -> i64 { if b { return 1; } else { return 0; } }\npub fn cond_cmp(x: i64, y: i64) -> i64 { if x < y { return 1; } else { return 0; } }\npub fn cond_eq(x: i64) -> i64 { if x == 0 { return 1; } else { return 0; } }\n",
        "module m;\npub fn wcmp(n: i64) -> i64 { let mut i: i64 = 0; while i < n { i = i + 1; } return i; }\npub fn wparam(go: bool) -> i64 { let mut k: i64 = 0; while go { k = k + 1; return k; } return k; }\npub fn weq(n: u32) -> u32 { let mut i: u32 = 0; while i == 0 { i = i + 1; } return i; }\n",
        "module m;\nfn helper(x: i64) -> i64 { return x + 1; }\nfn helperu(x: u32) -> u32 { return x; }\npub fn cl() -> i64 { return helper(5); }\npub fn cu() -> u32 { let v: u32 = helperu(7); return v; }\n",
        "module m;\nrecord Point { x: i64, y: u32 }\npub fn gx(p: Point) -> i64 { return p.x; }\npub fn gy(p: Point) -> u32 { let v: u32 = p.y; return v; }\npub fn setx(p: Point) -> i64 { let mut a: i64 = 0; a = p.x; return a; }\n",
        "module m;\nrecord Point { x: i64, y: u32 }\npub fn make(k: i64) -> Point { return Point { x: k, y: 2 }; }\npub fn lit() -> Point { return Point { x: 1, y: 7 }; }\npub fn viaLet() -> Point { let p: Point = Point { x: 3, y: 4 }; return p; }\n",
        "module m;\nenum Color { Red, Green, Blue }\nenum Opt { None, Some(i64) }\npub fn pick() -> Color { return Color::Red; }\npub fn wrap(n: i64) -> Opt { return Opt::Some(n); }\npub fn wlit() -> Opt { return Opt::Some(5); }\npub fn viaLet() -> Opt { let o: Opt = Opt::None; return o; }\n",
        "module m;\nrecord Acc { total: i64, count: u32 }\nfn bump(v: i64) -> i64 { return v + 1; }\npub fn run(n: i64, go: bool) -> i64 {\n    let mut a: Acc = Acc { total: 0, count: 0 };\n    let mut sum: i64 = 0;\n    if go {\n        sum = 10;\n    } else {\n        sum = bump(5);\n    }\n    let mut i: i64 = 0;\n    while i < n {\n        sum = sum + a.total;\n        i = i + 1;\n    }\n    match n {\n        0 => { return sum; },\n        _ => { return sum + 1; }\n    }\n}\n",
        "module m; fn f() -> i64 { let x: f64 = 5.0; return 0; }",
        "module m; fn f() -> i64 { let x: u32 = 0; return 0; }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { let mut i: i64 = 0; while i < n { if i > 5 { return i; } else { i = i + 1; } } return 0; }, _ => { return n; } } }",
        "module m; record P { x: i64, y: i64 } fn f() -> i64 { let mut p: P = P { x: 1, y: 2 }; p.x = 7; return p.x; }",
        "module m; record P { x: i64, y: i64 } fn mk() -> P { return P { x: 1, y: 2 }; }",
        "module m; enum E { A(i64), B } fn mk() -> E { return A(5); }",
        "module m; fn f() -> i64 { let x: i32 = 3; let x: i64 = 10; return x; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5a adversarial pos #{i} was unexpectedly rejected by the oracle:\n{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5a adversarial pos #{i} produced a spurious SIGIL diagnostic:\n{src}"
        );
    }
}

// ── PR-5b: binop-operand / name-resolution / annotation diagnostics ──────────

#[test]
fn pr5b_codes_match_oracle() {
    // Monomorphic programs the oracle REJECTS with exactly the PR-5b codes:
    // T054 (arithmetic/ordering needs a matching numeric type), T055 (equality
    // needs a matching type), T046 (non-scalar let annotation mismatch / unknown
    // type), T060 (undefined local, incl. a bad `E::C` variant), T062 (undefined
    // function). The SIGIL checker must emit the identical core-owned code set.
    let fixtures: &[&str] = &[
        // T054 — arithmetic / ordering operand mismatch.
        "module m; fn f(a: i64, b: bool) -> i64 { return a + b; }",
        "module m; fn f(a: i32, b: i64) -> i64 { return a + b; }",
        "module m; fn f(a: str, b: str) -> str { return a + b; }",
        "module m; fn f(a: bool, b: bool) -> bool { return a + b; }",
        "module m; fn f(a: i64, b: bool) -> bool { return a < b; }",
        "module m; fn f(a: str, b: str) -> bool { return a < b; }",
        // T055 — equality operand mismatch.
        "module m; fn f(a: i64, b: bool) -> bool { return a == b; }",
        "module m; fn f(a: i32, b: i64) -> bool { return a == b; }",
        "module m; fn f(a: str, b: i64) -> bool { return a == b; }",
        // T046 — non-scalar / unknown let annotation.
        "module m; record Pair { a: i64, b: i64 } fn f() -> i64 { let p: Pair = 7; return 0; }",
        "module m; fn f() -> i64 { let x: Bogus = 5; return 0; }",
        "module m; enum Opt { None, Some(i64) } fn f() -> i64 { let o: Opt = 5; return 0; }",
        // T060 — undefined local (and a bad enum variant).
        "module m; fn f() -> i64 { return q; }",
        "module m; fn f() -> i64 { let x: i64 = y; return x; }",
        "module m; enum E { A, B } fn f() -> E { return E::C; }",
        // T062 — undefined function.
        "module m; fn f() -> i64 { return h(); }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5b fixture #{i} expected an oracle rejection but got none:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5b fixture #{i} T-code parity:\n{src}"
        );
    }
}

#[test]
fn pr5b_wellformed_emit_no_codes() {
    // Zero false-positive at the PR-5b boundaries: valid same-numeric arithmetic
    // and ordering, valid same-type equality (incl. bool/str), matching
    // record/enum annotations, a defined function call, and an UNqualified enum
    // variant construction. None may produce a core-owned diagnostic.
    let fixtures: &[&str] = &[
        "module m; fn f(a: i64, b: i64) -> i64 { return a + b; }",
        "module m; fn f(a: f64, b: f64) -> f64 { return a + b; }",
        "module m; fn f(a: u32, b: u32) -> u32 { return a * b; }",
        "module m; fn f(a: i64, b: i64) -> bool { return a < b; }",
        "module m; fn f(a: str, b: str) -> bool { return a == b; }",
        "module m; fn f(a: bool, b: bool) -> bool { return a == b; }",
        "module m; fn f(a: f64, b: f64) -> bool { return a != b; }",
        "module m; record Pair { a: i64, b: i64 } fn f() -> i64 { let p: Pair = Pair { a: 1, b: 2 }; return 0; }",
        "module m; enum Opt { None, Some(i64) } fn f() -> i64 { let o: Opt = Opt::None; return 0; }",
        "module m; record Pair { a: i64, b: i64 } fn mk() -> Pair { return Pair { a: 1, b: 2 }; }",
        "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(5); }",
        "module m; enum E { A(i64), B } fn mk() -> E { return A(5); }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5b positive #{i} was unexpectedly rejected by the oracle:\n{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5b positive #{i} produced a spurious SIGIL diagnostic:\n{src}"
        );
    }
}

#[test]
fn pr5b_adversarial_neg_codes_match_oracle() {
    // Workflow-generated, oracle-vetted rejections (49, zero drops) spanning the
    // PR-5b families with maximal diversity: every numeric-mismatch arithmetic /
    // ordering pair (T054) and equality pair (T055), undefined locals deep in
    // if/while/match bodies and as call args (T060), bad `E::Bogus` variants,
    // undefined functions (T062), record/enum/unknown annotation mismatches
    // (T046), and several MULTI-error programs whose full code SET must match.
    let fixtures: &[&str] = &[
        "module m; fn f(a: i64, b: bool) -> i64 { return a + b; }",
        "module m; fn f(a: i32, b: i64) -> i64 { return a - b; }",
        "module m; fn f(a: u32, b: i64) -> u32 { return a * b; }",
        "module m; fn f(a: str, b: i64) -> str { return a + b; }",
        "module m; fn f(a: str, b: str) -> str { return a + b; }",
        "module m; fn f(a: bool, b: bool) -> bool { return a + b; }",
        "module m; fn f(a: f64, b: i64) -> f64 { return a / b; }",
        "module m; fn f(a: i64, b: i64, c: i32) -> i64 { let r: i64 = a % c; return r; }",
        "module m; fn f(a: i64, b: bool) -> bool { return a < b; }",
        "module m; fn f(a: str, b: str) -> bool { return a < b; }",
        "module m; fn f(a: f64, b: i64) -> bool { return a > b; }",
        "module m; fn f(a: i32, b: i64) -> i64 { if a <= b { return 1; } else { return 0; } }",
        "module m; fn f(a: u32, b: i64) -> i64 { while a >= b { return 1; } return 0; }",
        "module m; fn f(a: i32, b: i64, c: i64) -> bool { return (a + b) < c; }",
        "module m; fn f(a: i64, b: bool) -> bool { return a == b; }",
        "module m; fn f(a: i32, b: i64) -> bool { return a != b; }",
        "module m; fn f(a: str, b: bool) -> bool { return a == b; }",
        "module m; fn f(a: f64, b: i64) -> bool { return a != b; }",
        "module m; fn f(a: i64, b: bool) -> i64 { if a == b { return 1; } else { return 0; } }",
        "module m; fn f() -> i64 { return q; }",
        "module m; fn f() -> i64 { let x: i64 = y; return x; }",
        "module m; fn f() -> i64 { let mut x: i64 = 0; x = z; return x; }",
        "module m; fn f(a: i64) -> i64 { return a + bogus; }",
        "module m; fn f() -> i64 { if cond { return 1; } else { return 0; } }",
        "module m; fn f() -> i64 { let mut i: i64 = 0; while limit { i = i + 1; } return i; }",
        "module m; fn f() { match scrut { 0 => { }, _ => { } } }",
        "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(undef); }",
        "module m; fn g(x: i64) -> i64 { return x; } fn f(n: i64) -> i64 { let mut i: i64 = 0; while i < n { i = g(phantom); } return i; }",
        "module m; enum E { A, B } fn f() -> E { return E::Bogus; }",
        "module m; fn f(n: i64) -> i64 { let mut acc: i64 = 0; match n { 0 => { let mut i: i64 = 0; while i < n { acc = acc + extra; i = i + 1; } return acc; }, _ => { return acc; } } }",
        "module m; fn f() -> i64 { return h(); }",
        "module m; fn f() -> i64 { return compute(1); }",
        "module m; fn f(b: bool) -> i64 { if b { doThing(); return 1; } else { return 0; } }",
        "module m; fn f() -> bool { return a < b; }",
        "module m; record Pair { a: i64, b: i64 } fn f() -> i64 { let p: Pair = 7; return 0; }",
        "module m; record Pair { a: i64, b: i64 } fn f() -> i64 { let p: Pair = true; return 0; }",
        "module m; record Pair { a: i64, b: i64 } fn f() -> i64 { let p: Pair = \"s\"; return 0; }",
        "module m; enum Opt { None, Some(i64) } fn f() -> i64 { let o: Opt = 5; return 0; }",
        "module m; enum Opt { None, Some(i64) } fn f() -> i64 { let o: Opt = false; return 0; }",
        "module m; record Pair { a: i64, b: i64 } enum E { A, B } fn f() -> i64 { let p: Pair = E::A; return 0; }",
        "module m; record Pair { a: i64, b: i64 } enum Opt { None, Some(i64) } fn f() -> i64 { let o: Opt = Pair { a: 1, b: 2 }; return 0; }",
        "module m; fn f() -> i64 { let x: Bogus = 5; return 0; }",
        "module m; fn f() -> i64 { let y: Widget = true; return 0; }",
        "module m; record Pair { a: i64, b: i64 } fn f(s: str, n: i64) -> i64 { let p: Pair = 7; let z: i64 = s + n; return q; }",
        "module m; fn f(n: i64, b: bool) -> i64 { let x: Bogus = 5; if n == b { return 1; } else { return h(); } }",
        "module m; record Pair { a: i64 } record Trio { x: i64, y: i64, z: i64 } fn f() -> i64 { let p: Pair = Trio { x: 1, y: 2, z: 3 }; return 0; }",
        "module m; fn f() -> i64 { let x: Bogus = 1; if 1.5 { return 1; } else { return 0; } }",
        "module m; record Pair { a: i64 } enum Opt { None, Some(i64) } fn f() -> i64 { let p: Pair = Opt::Some(5); return 0; }",
        "module m; record Pair { a: i64 } fn f(s: str) -> i64 { let mut x: i64 = 0; let p: Pair = 9; x = s; while s { return 1; } return 0; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5b adversarial neg #{i} expected an oracle rejection but got none:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5b adversarial neg #{i} T-code parity:
{src}"
        );
    }
}

#[test]
fn pr5b_adversarial_pos_emit_no_codes() {
    // Workflow-generated, oracle-vetted well-typed programs (33) at the PR-5b
    // boundaries: matching-numeric arithmetic/ordering for every numeric type,
    // same-type equality (bool/str/f64), literal pinning that must NOT trip
    // (`a + 1`, `v < 0`, `x == 0`, all-literal arithmetic), matching record/enum
    // annotations, qualified + UNqualified variant construction, valid calls,
    // field access, and shadowing. None may emit a core-owned diagnostic.
    let fixtures: &[&str] = &[
        "module m; fn f(a: i32, b: i32) -> i32 { return a + b; }",
        "module m; fn f(a: u32, b: u32) -> u32 { return a - b; }",
        "module m; fn f(a: i64, b: i64) -> i64 { return a * b; }",
        "module m; fn f(a: u64, b: u64) -> u64 { return a % b; }",
        "module m; fn f(a: f64, b: f64) -> f64 { return a / b; }",
        "module m; fn f(a: u64, b: u64) -> bool { return a >= b; }",
        "module m; fn f(a: f64, b: f64) -> bool { return a <= b; }",
        "module m; fn f(a: bool, b: bool) -> bool { return a == b; }",
        "module m; fn f(a: str, b: str) -> bool { return a != b; }",
        "module m; fn f(a: f64, b: f64) -> bool { return a == b; }",
        "module m; fn f(a: u32) -> u32 { return a + 1; }",
        "module m; fn f(v: i32) -> bool { return v < 0; }",
        "module m; fn f(x: i64) -> bool { return x == 0; }",
        "module m; fn f() -> i64 { return 5 + 3; }",
        "module m; fn f() -> u32 { return 2 * 3; }",
        "module m; fn f(a: i64, b: i64, c: i64) -> bool { return (a + b) < c; }",
        "module m; fn f(a: i64, b: i64) -> i64 { let s: i64 = a + b; return s; }",
        "module m; record Point { x: i64, y: i64 } fn f(p: Point) -> i64 { return p.x; }",
        "module m; enum Color { Red, Green, Blue } fn f() -> Color { return Color::Red; }",
        "module m; enum E { A(i64), B } fn f() -> E { return A(5); }",
        "module m; fn g(x: i64) -> i64 { return x + 1; } fn f() -> i64 { return g(7); }",
        "module m; fn f() -> i64 { let x: i64 = 1; let x: i64 = x; return x; }",
        "module m; record Pair { a: i64, b: i64 } fn f() -> i64 { let p: Pair = Pair { a: 1, b: 2 }; return p.a; }",
        "module m; enum Opt { None, Some(i64) } fn f() -> i64 { let o: Opt = Opt::None; return 0; }",
        "module m; enum Opt { None, Some(i64) } fn f() -> i64 { let o: Opt = Opt::Some(5); return 0; }",
        "module m; record Pair { a: i64, b: i64 } fn f() -> i64 { let p = Pair { a: 1, b: 2 }; return p.a; }",
        "module m; enum Opt { None, Some(i64) } fn f() -> i64 { let o = Opt::None; return 0; }",
        "module m; fn f() -> i64 { let x: u32 = 7; return 0; }",
        "module m; fn f(a: u32) -> u32 { let s: u32 = a + 1; return s; }",
        "module m; fn f(v: i32) -> bool { if v < 0 { return true; } else { return false; } }",
        "module m; fn f(x: i64) -> i64 { if x == 0 { return 1; } else { return 0; } }",
        "module m; enum E { A(i64), B } fn f() -> i64 { let e: E = A(5); return 0; }",
        "module m; enum Msg { Text(str), Empty } fn f() -> i64 { let m: Msg = Msg::Text(\"hi\"); return 0; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5b adversarial pos #{i} was unexpectedly rejected by the oracle:
{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5b adversarial pos #{i} produced a spurious SIGIL diagnostic:
{src}"
        );
    }
}

// ── PR-5c: call arity / arg-type / unknown-field diagnostics ─────────────────

#[test]
fn pr5c_codes_match_oracle() {
    // Monomorphic programs the oracle REJECTS with exactly the PR-5c codes: T070
    // (call argument-count mismatch, either direction), T071 (an argument not
    // assignable to its parameter — a bare literal pins, so only a real mismatch
    // trips), T120 (access of a field the record does not declare). One fixture
    // has BOTH a wrong arity and a wrong arg type → {T070, T071}.
    let fixtures: &[&str] = &[
        "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(); }",
        "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(1, 2); }",
        "module m; fn h(a: i64, b: u32) -> i64 { return a; } fn f() -> i64 { return h(1); }",
        "module m; fn h(a: i64, b: u32) -> i64 { return a; } fn f() -> i64 { return h(1, 2, 3); }",
        "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(true); }",
        "module m; fn g(x: i64) -> i64 { return x; } fn f(p: i32) -> i64 { return g(p); }",
        "module m; fn g(x: i64) -> i64 { return x; } fn f(s: str) -> i64 { return g(s); }",
        "module m; fn h(a: i64, b: u32) -> i64 { return a; } fn f(a: i64) -> i64 { return h(a, true); }",
        "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(true, false); }",
        "module m; record Pair { a: i64, b: i64 } fn f(p: Pair) -> i64 { return p.z; }",
        "module m; record Pair { a: i64 } fn f(p: Pair) -> i64 { return p.a + p.q; }",
        "module m; record Pair { a: i64 } fn f(p: Pair) -> i64 { let mut x: i64 = 0; x = p.z; return x; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5c fixture #{i} expected an oracle rejection but got none:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5c fixture #{i} T-code parity:\n{src}"
        );
    }
}

#[test]
fn pr5c_wellformed_emit_no_codes() {
    // Zero false-positive at the PR-5c boundaries: exact-arity calls with literal
    // args that pin to the parameter type, a multi-argument call, and access of a
    // declared field. None may produce a core-owned diagnostic.
    let fixtures: &[&str] = &[
        "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(5); }",
        "module m; fn h(a: i64, b: u32) -> i64 { return a; } fn f(a: i64) -> i64 { return h(a, 7); }",
        "module m; fn add(a: i64, b: i64) -> i64 { return a + b; } fn f() -> i64 { return add(2, 3); }",
        "module m; record Pair { a: i64, b: i64 } fn f(p: Pair) -> i64 { return p.a; }",
        "module m; record Pt { x: i64, y: u32 } fn f(p: Pt) -> u32 { return p.y; }",
        "module m; fn g(x: i64) -> i64 { return x; } fn f(v: i64) -> i64 { return g(v); }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5c positive #{i} was unexpectedly rejected by the oracle:\n{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5c positive #{i} produced a spurious SIGIL diagnostic:\n{src}"
        );
    }
}

#[test]
fn pr5c_adversarial_neg_codes_match_oracle() {
    // Workflow-generated, oracle-vetted rejections (34, zero drops): arity
    // mismatches (T070) at every declared arity in return/let/if/binop positions;
    // arg-type mismatches (T071) for every scalar param type, one per mismatched
    // in-range arg (so `g(p, 2, q)` -> {T071, T071}); unknown-field access (T120)
    // in many positions; and MULTI-error programs whose full code SET must match
    // ({T070,T120}, {T060,T120}, {T046,T120}, {T060,T070,T120}, {T070,T071}).
    let fixtures: &[&str] = &[
        "module m;\nfn z() -> i64 { return 9; }\nfn boot() -> i64 { return z(5); }\n",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn boot() -> i64 { let v: i64 = g(); return v; }\n",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn boot() -> i64 { return g(1, 2); }\n",
        "module m;\nfn add(a: i64, b: i64) -> i64 { return a + b; }\nfn boot() -> i64 { return add(3) + 1; }\n",
        "module m;\nfn add(a: i64, b: i64) -> i64 { return a + b; }\nfn boot() -> i64 { let s: i64 = add(1, 2, 3); return s; }\n",
        "module m;\nfn tri(a: i64, b: i64, c: i64) -> i64 { return a + b + c; }\nfn boot() -> i64 { return tri(1, 2); }\n",
        "module m;\nfn flag(a: i64) -> bool { return a < 10; }\nfn boot() -> i64 { if flag() { return 1; } else { return 0; } }\n",
        "module m;\nfn ready() -> bool { return true; }\nfn boot() -> i64 { if ready(7) { return 1; } else { return 0; } }\n",
        "module m;\nfn mk(a: str, b: bool, c: f64) -> i64 { return 0; }\nfn boot() -> i64 { return mk(\"x\", true); }\n",
        "module m;\nfn pick(a: f64, b: str) -> i64 { return 0; }\nfn boot() -> i64 { return pick(1.5, \"a\", 3) + 2; }\n",
        "module m;\nfn g(x: i64) -> i64 { return x; }\nfn f(s: str) -> i64 { return g(s); }\n",
        "module m;\nfn g(x: u32) -> u32 { return x; }\nfn f(b: bool) -> u32 { return g(b); }\n",
        "module m;\nfn g(x: f64) -> f64 { return x; }\nfn f(a: i64) -> f64 { return g(a); }\n",
        "module m;\nfn g(x: i32) -> i32 { return x; }\nfn f(a: i64) -> i32 { return g(a); }\n",
        "module m;\nfn g(x: u64) -> u64 { return x; }\nfn f(d: f64) -> u64 { return g(d); }\n",
        "module m;\nfn h(a: i64, b: u32) -> i64 { return a; }\nfn f(b: bool) -> i64 { return h(1, b); }\n",
        "module m;\nfn g(a: i64, b: u32, c: str) -> i64 { return a; }\nfn f(p: bool, q: i64) -> i64 { return g(p, 2, q); }\n",
        "module m;\nrecord Pair { a: i64, b: i64 }\nfn g(p: Pair) -> i64 { return p.a; }\nfn f() -> i64 { return g(5); }\n",
        "module m;\nfn g(x: i64) -> i64 { return x; }\nfn f(s: str) -> i64 { return g(s, 2); }\n",
        "module m; record Pair { a: i64, b: i64 } fn f(p: Pair) -> i64 { return p.z; }",
        "module m; record Pair { a: i64, b: i64 } fn f(p: Pair) -> i64 { let x: i64 = p.q; return x; }",
        "module m; record Pair { a: i64, b: i64 } fn f(p: Pair) -> i64 { return p.a + p.q; }",
        "module m; record Pair { a: i64, b: i64 } fn f(p: Pair) -> i64 { let mut x: i64 = 0; x = p.z; return x; }",
        "module m; record Flag { active: bool, n: i64 } fn f(p: Flag) -> i64 { if p.bogus { return 1; } else { return 0; } }",
        "module m; record Pair { a: i64 } fn g(x: i64) -> i64 { return x; } fn f(p: Pair) -> i64 { return g(p.q); }",
        "module m; record Pair { a: i64, b: i64 } fn f() -> i64 { let p: Pair = Pair { a: 1, b: 2 }; return p.z; }",
        "module m; record Pair { a: i64, b: i64 } fn f(p: Pair) -> bool { return p.a == p.k; }",
        "module m; record Pair { a: i64 } fn g(x: i64) -> i64 { return x; } fn f(p: Pair) -> i64 { return g() + p.z; }",
        "module m; record Pair { a: i64 } fn f(p: Pair) -> i64 { return p.z + missing; }",
        "module m; record Pair { a: i64 } fn f(p: Pair) -> i64 { let q: Bogus = 5; return p.z; }",
        "module m; record Pair { a: i64 } fn g(x: i64) -> i64 { return x; } fn f(p: Pair) -> i64 { let mut x: i64 = g(1, 2); x = p.z; return undef; }",
        "module m; record Pair { a: i64 } fn g(x: i64) -> i64 { return x; } fn f(p: Pair, s: str) -> i64 { return g(s) + p.z; }",
        "module m; record Pair { a: i64 } fn g(x: i64) -> i64 { return x; } fn f(p: Pair) -> i64 { return g(p) + p.z; }",
        "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(true, false); }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5c adversarial neg #{i} expected an oracle rejection but got none:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5c adversarial neg #{i} T-code parity:
{src}"
        );
    }
}

#[test]
fn pr5c_adversarial_pos_emit_no_codes() {
    // Workflow-generated, oracle-vetted well-typed programs (14): exact-arity
    // calls across every arity with literal-pinned and correctly-typed variable
    // args, calls nested as arguments, calls in if-condition / binop positions,
    // and access of every declared field of multi-field records. None may emit a
    // core-owned diagnostic.
    let fixtures: &[&str] = &[
        "module m;\nfn z() -> i64 { return 0; }\nfn one(a: i64) -> i64 { return a; }\nfn two(a: i64, b: u32) -> i64 { return a; }\nfn three(a: str, b: bool, c: f64) -> i64 { return 0; }\nfn boot() -> i64 { let w: i64 = z(); let x: i64 = one(5); let y: i64 = two(7, 9); let q: i64 = three(\"hi\", true, 1.5); return w + x + y + q; }\n",
        "module m;\nfn id(x: i64) -> i64 { return x; }\nfn add(a: i64, b: i64) -> i64 { return a + b; }\nfn boot() -> i64 { return add(id(1), add(2, 3)); }\n",
        "module m;\nfn gte(a: i64, b: i64) -> bool { return a < b; }\nfn dbl(x: i64) -> i64 { return x + x; }\nfn boot() -> i64 { if gte(1, 2) { return dbl(4) + 1; } else { return 0; } }\n",
        "module m;\nfn pack(a: u32, b: f64, c: bool) -> u64 { return 0; }\nfn boot() -> u64 { return pack(5, 2.5, false); }\n",
        "module m;\nfn g(x: i64) -> i64 { return x; }\nfn f() -> i64 { return g(5); }\n",
        "module m;\nfn h(a: i64, b: u32) -> i64 { return a; }\nfn f(a: i64) -> i64 { return h(a, 7); }\n",
        "module m;\nfn g(x: f64) -> f64 { return x; }\nfn f() -> f64 { return g(1.5); }\n",
        "module m;\nfn g(x: str) -> str { return x; }\nfn f() -> str { return g(\"hi\"); }\n",
        "module m;\nfn g(a: i64, b: u32, c: str, d: bool) -> i64 { return a; }\nfn f(c: str) -> i64 { return g(5, 7, c, true); }\n",
        "module m; record R { a: i64, b: u32, c: bool, d: str, e: f64 } fn fa(p: R) -> i64 { return p.a; } fn fb(p: R) -> u32 { return p.b; } fn fc(p: R) -> bool { return p.c; } fn fd(p: R) -> str { return p.d; } fn fe(p: R) -> f64 { return p.e; }",
        "module m; record Pt { x: i64, y: i64 } fn f(p: Pt) -> i64 { return p.x + p.y; }",
        "module m; record Pt { x: i64, y: i64 } fn f(p: Pt) -> bool { return p.x < p.y; }",
        "module m; record Pair { a: i64, b: i64 } fn f() -> i64 { let p = Pair { a: 1, b: 2 }; return p.a; }",
        "module m; record Pair { a: i64, b: i64 } fn f() -> i64 { let p: Pair = Pair { a: 1, b: 2 }; return p.b; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5c adversarial pos #{i} was unexpectedly rejected by the oracle:
{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5c adversarial pos #{i} produced a spurious SIGIL diagnostic:
{src}"
        );
    }
}

// ── PR-5d: pattern diagnostics — T087 / T088 / T044 / T190 ───────────────────

#[test]
fn pr5d_codes_match_oracle() {
    // Monomorphic programs the oracle REJECTS with exactly the PR-5d codes: T190
    // (range lo>hi), T087 (non-exhaustive ENUM match), T088 (non-exhaustive
    // non-enum match — bool missing an arm, integers without a wildcard), T044
    // (a non-unit fn that does not return on every path). A non-exhaustive match
    // in a non-unit fn co-fires {T044, T087} / {T044, T088}.
    let fixtures: &[&str] = &[
        "module m; fn f(n: i64) -> i64 { match n { 5..=1 => { return 1; }, _ => { return 0; } } }",
        "module m; fn f(n: i64) -> i64 { match n { -1..=-5 => { return 1; }, _ => { return 0; } } }",
        "module m; enum E { A, B } fn f(e: E) -> i64 { match e { E::A => { return 1; } } }",
        "module m; enum E { A, B } fn f(e: E) { match e { E::A => { } } }",
        "module m; fn f(b: bool) -> i64 { match b { true => { return 1; } } }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { return 1; }, 1 => { return 2; } } }",
        "module m; fn f(b: bool) -> i64 { if b { } else { } }",
        "module m; fn f(n: i64) -> i64 { while n > 0 { return 1; } }",
        "module m; enum E { A, B } fn f(e: E) -> i64 { match e { E::A => { return 1; }, E::B => { } } }",
        "module m; fn f() -> i64 { let x: i64 = 5; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5d fixture #{i} expected an oracle rejection but got none:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5d fixture #{i} T-code parity:\n{src}"
        );
    }
}

#[test]
fn pr5d_wellformed_emit_no_codes() {
    // Zero false-positive: exhaustive matches (enum all-covered, enum+wildcard,
    // bool both-arms, integer+wildcard), valid ranges (lo<hi, lo==hi), all-paths-
    // return fns (if-both, while+trailing-return, match-all-return), and unit fns
    // that need no return. None may produce a core-owned diagnostic.
    let fixtures: &[&str] = &[
        "module m; enum E { A, B } fn f(e: E) -> i64 { match e { E::A => { return 1; }, E::B => { return 2; } } }",
        "module m; enum E { A, B, C } fn f(e: E) -> i64 { match e { E::A => { return 1; }, _ => { return 0; } } }",
        "module m; fn f(b: bool) -> i64 { match b { true => { return 1; }, false => { return 0; } } }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { return 1; }, _ => { return 0; } } }",
        "module m; fn f(b: bool) -> i64 { if b { return 1; } else { return 0; } }",
        "module m; fn f(n: i64) -> i64 { while n > 0 { return 1; } return 0; }",
        "module m; fn f(n: i64) -> i64 { match n { 1..=5 => { return 1; }, _ => { return 0; } } }",
        "module m; fn f(n: i64) -> i64 { match n { 3..=3 => { return 1; }, _ => { return 0; } } }",
        "module m; fn f() { let x: i64 = 5; }",
        "module m; fn f(n: i64) -> i64 { let mut s: i64 = 0; while n > 0 { s = s + 1; } return s; }",
        "module m; fn f(n: i64) -> i64 { if n > 0 { return 1; } else { } return 0; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5d positive #{i} was unexpectedly rejected by the oracle:\n{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5d positive #{i} produced a spurious SIGIL diagnostic:\n{src}"
        );
    }
}

#[test]
fn pr5d_adversarial_neg_codes_match_oracle() {
    // Workflow-generated, oracle-vetted rejections (36, zero drops): non-exhaustive
    // enum matches (T087) at 2/3/4-variant arities in unit and non-unit fns,
    // guarded-arm-doesn't-cover cases, payload-variant enums; non-exhaustive
    // non-enum matches (T088 — bool missing an arm, integer literal/range-only);
    // missing-return (T044) across fall-off / if-one-branch / while-only /
    // exhaustive-arm-no-return shapes; range lo>hi (T190); and MULTI-error programs
    // whose full code SET matches ({T044,T087}, {T044,T088}, {T044,T088,T190},
    // {T044,T049,T087}, {T044,T060,T087}, {T050,T190}, {T087,T190}).
    let fixtures: &[&str] = &[
        "module m; enum E { A, B } fn f(e: E) { match e { E::A => { } } }",
        "module m; enum E { A, B } fn f(e: E) -> i64 { match e { E::A => { return 1; } } }",
        "module m; enum Color { Red, Green, Blue } fn f(c: Color) { match c { Color::Red => { } } }",
        "module m; enum Color { Red, Green, Blue } fn f(c: Color) -> i64 { match c { Color::Red => { return 1; } } }",
        "module m; enum Dir { N, S, E, W } fn f(d: Dir) -> i64 { match d { Dir::N => { return 1; } } }",
        "module m; enum E { A, B, C } fn f(e: E, k: i64) -> i64 { match e { E::A => { return 1; }, E::B => { return 2; }, E::C if k > 0 => { return 3; } } }",
        "module m; enum E { A, B } fn f(e: E, k: i64) { match e { E::A => { }, E::B if k > 0 => { } } }",
        "module m; fn f(b: bool) -> i64 { match b { true => { return 1; } } }",
        "module m; fn f(b: bool) { match b { false => { } } }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { return 1; }, 1 => { return 2; }, 2 => { return 3; } } }",
        "module m; fn f(n: i64) -> i64 { match n { 0..=9 => { return 1; }, 10..=19 => { return 2; } } }",
        "module m; fn f(n: i64) { match n { 1..=5 => { } } }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { return 1; }, 1..=5 => { return 2; }, 6 => { return 3; } } }",
        "module m; fn f(n: u32) -> u32 { match n { 0 => { return 0; }, 1 => { return 1; } } }",
        "module m; enum St { On(i64), Off } fn f(s: St) -> i64 { match s { St::On(v) => { return v; } } }",
        "module m;\nfn f() -> i64 {\n    let x: i64 = 5;\n}\n",
        "module m;\nfn f() -> i64 {\n    let mut x: i64 = 5;\n    x = 7;\n}\n",
        "module m;\nfn g() -> i64 {\n    return 0;\n}\nfn f() -> i64 {\n    g();\n}\n",
        "module m;\nfn f(b: bool) -> i64 {\n    if b {\n        return 1;\n    } else {\n    }\n}\n",
        "module m;\nfn f(b: bool) -> i64 {\n    if b {\n        let x: i64 = 1;\n    } else {\n        let y: i64 = 2;\n    }\n}\n",
        "module m;\nfn f(b: bool) -> i64 {\n    while b {\n        return 1;\n    }\n}\n",
        "module m;\nfn f(n: i64) -> i64 {\n    match n {\n        0 => { return 1; },\n        _ => { let x: i64 = 2; },\n    }\n}\n",
        "module m;\nfn f(b: bool) -> i64 {\n    if b {\n        return 1;\n    } else {\n        while b {\n            return 2;\n        }\n    }\n}\n",
        "module m;\nenum E { A, B }\nfn f(e: E) -> i64 {\n    match e {\n        E::A => { return 1; },\n    }\n}\n",
        "module m;\nfn f(b: bool) -> i64 {\n    match b {\n        true => { return 1; },\n    }\n}\n",
        "module m;\nfn f(b: i64) -> i64 {\n    match b {\n        9..=2 => { return 1; },\n        _ => { return 0; },\n    }\n}\n",
        "module m;\nfn f(b: i64) -> i64 {\n    match b {\n        -1..=-9 => { return 1; },\n        _ => { return 0; },\n    }\n}\n",
        "module m;\nfn f(b: i64) -> i64 {\n    match b {\n        5..=-5 => { return 1; },\n        _ => { return 0; },\n    }\n}\n",
        "module m;\nfn f(b: i64) -> i64 {\n    match b {\n        100000..=42 => { return 1; },\n        _ => { return 0; },\n    }\n}\n",
        "module m;\nfn f(b: i64) -> i64 {\n    match b {\n        20..=10 => { return 1; },\n        0 => { return 2; },\n        _ => { return 3; },\n    }\n}\n",
        "module m;\nfn f(b: i64) -> i64 {\n    match b {\n        5..=1 => { return 1; },\n        0 => { return 2; },\n    }\n}\n",
        "module m;\nfn f(b: i64) -> i64 {\n    let mut r: i64 = 0;\n    match b {\n        7..=3 => { return 1; },\n        _ => { r = 9; },\n    }\n}\n",
        "module m;\nenum Color { Red, Green, Blue }\nfn f(c: Color) -> i64 {\n    match c {\n        Color::Red => { return true; },\n        Color::Green => { return 2; },\n    }\n}\n",
        "module m;\nenum Dir { North, South, East }\nfn f(d: Dir) -> i64 {\n    match d {\n        Dir::North => { return missing; },\n        Dir::South => { return 2; },\n    }\n}\n",
        "module m;\nfn f(b: i64, x: i64) -> i64 {\n    match b {\n        5..=1 => { return 1; },\n        _ => {},\n    }\n    if x { return 1; } else { return 2; }\n}\n",
        "module m;\nenum Color { Red, Green, Blue }\nfn f(b: i64, c: Color) {\n    match b {\n        5..=1 => {},\n        _ => {},\n    }\n    match c {\n        Color::Red => {},\n        Color::Green => {},\n    }\n}\n",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5d adversarial neg #{i} expected an oracle rejection but got none:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5d adversarial neg #{i} T-code parity:
{src}"
        );
    }
}

#[test]
fn pr5d_adversarial_pos_emit_no_codes() {
    // Workflow-generated, oracle-vetted well-typed programs (17): exhaustive enum
    // matches (all variants / unguarded wildcard / unguarded bare-binding), bool
    // both-arms, integer + wildcard, nested exhaustive matches, all-paths-return
    // shapes (if-both, while+trailing-return, first-stmt-guaranteed), valid ranges
    // (lo<hi, lo==hi), and unit fns that need no return. None may emit a code.
    let fixtures: &[&str] = &[
        "module m; enum E { A, B, C } fn f(e: E) -> i64 { match e { E::A => { return 1; }, E::B => { return 2; }, E::C => { return 3; } } }",
        "module m; enum E { A, B, C } fn f(e: E) -> i64 { match e { E::A => { return 1; }, _ => { return 0; } } }",
        "module m; enum E { A, B, C } fn f(e: E) -> i64 { match e { E::A => { return 1; }, other => { return 0; } } }",
        "module m; fn f(b: bool) -> i64 { match b { true => { return 1; }, false => { return 0; } } }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { return 1; }, _ => { return 0; } } }",
        "module m; enum Outer { O, X } enum Inner { I, Y } fn f(o: Outer, i: Inner) -> i64 { match o { Outer::O => { match i { Inner::I => { return 1; }, Inner::Y => { return 2; } } }, Outer::X => { return 0; } } }",
        "module m;\nfn f(b: bool) -> i64 {\n    if b {\n        return 1;\n    } else {\n        return 2;\n    }\n}\n",
        "module m;\nfn f(b: bool) -> i64 {\n    if b {\n        return 1;\n    } else {\n    }\n    return 2;\n}\n",
        "module m;\nfn f(b: bool) -> i64 {\n    while b {\n        return 1;\n    }\n    return 2;\n}\n",
        "module m;\nfn f(n: i64) -> i64 {\n    match n {\n        0 => { return 1; },\n        _ => { return 2; },\n    }\n}\n",
        "module m;\nfn f(b: bool, c: bool) -> i64 {\n    if b {\n        if c {\n            return 1;\n        } else {\n            return 2;\n        }\n    } else {\n        return 3;\n    }\n}\n",
        "module m;\nfn f(n: i64) {\n    let x: i64 = n;\n}\n",
        "module m;\nfn f(b: bool) -> i64 {\n    if b {\n        return 1;\n    } else {\n        return 2;\n    }\n    let dead: i64 = 99;\n}\n",
        "module m;\nfn f(b: i64) -> i64 {\n    match b {\n        0..=9 => { return 1; },\n        _ => { return 0; },\n    }\n}\n",
        "module m;\nfn f(b: i64) -> i64 {\n    match b {\n        0..=0 => { return 1; },\n        _ => { return 0; },\n    }\n}\n",
        "module m;\nfn f(b: i64) -> i64 {\n    match b {\n        -5..=5 => { return 1; },\n        _ => { return 0; },\n    }\n}\n",
        "module m;\nfn f(b: i64) -> i64 {\n    match b {\n        0..=9 => { return 1; },\n        10..=19 => { return 2; },\n        20..=29 => { return 3; },\n        _ => { return 0; },\n    }\n}\n",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5d adversarial pos #{i} was unexpectedly rejected by the oracle:
{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5d adversarial pos #{i} produced a spurious SIGIL diagnostic:
{src}"
        );
    }
}

// ===========================================================================
// PR-5e: composite types I — the type_detail upgrade + Ref (tag 14) + Tuple
// (tag 19). A composite-typed node now emits the oracle's `mangle_type` byte
// string as the record's 4th field (e.g. `$tuple2__i64_u32`, `ref_Point`); the
// SIGIL `tc_tmangle` twin must reproduce it. Array (12) / Slice (15) / Index /
// composite literals are PR-5f (Slice's array-borrow decay needs element
// extraction; Array nodes appear only via literals). Composite type CHECKING
// (T049 on a tuple mismatch, &scalar's T133) stays out-of-core for these slices.
// ===========================================================================

#[test]
fn pr5e_composite_types_match_oracle() {
    // The composite record stream must match the oracle BYTE-FOR-BYTE in the 4th
    // field: a tuple param + tuple return (the `t`-ref + the fn-ret record both
    // carry `$tuple2__i64_u32`), a `&p` borrow of a record param (`ref_Point`,
    // tag 14, recursing into the `p` operand which keeps its own Named record),
    // and a `&mut q` borrow of a mutable record local (`ref_mut_Point`).
    let fixtures: &[&str] = &[
        // Tuple param threaded straight through to a tuple return.
        "module m; fn f(t: (i64, u32)) -> (i64, u32) { return t; }",
        // Tuple of three, distinct element types.
        "module m; fn f(t: (i64, u32, bool)) -> (i64, u32, bool) { return t; }",
        // `&p` shared borrow of a record param, passed to a `&Point` callee.
        "module m; record Point { x: i64 } fn g(r: &Point) -> i64 { return 0; } fn f(p: Point) -> i64 { return g(&p); }",
        // `&mut q` exclusive borrow of a mutable record local.
        "module m; record Point { x: i64 } fn g(r: &mut Point) -> i64 { return 0; } fn f(p: Point) -> i64 { let mut q: Point = p; return g(&mut q); }",
        // A `&P` let-bound shared borrow (the borrow rides a let value).
        "module m; record P { x: i64 } fn f(p: P) -> i64 { let r: &P = &p; return 0; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-5e composite #{i}: SIGIL composite type stream must match the oracle:
{src}"
        );
        // A well-typed composite program emits no diagnostics on either side.
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5e composite #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-5e composite #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

#[test]
fn pr5e_type_detail_known_answers() {
    // ET-D4: `type_detail` (the only oracle twin this slice swaps in) has a pinned
    // known-answer table — a scalar emits "" (the 0-byte no-op that keeps the whole
    // pre-composite corpus byte-identical), a Named emits its bare name, and each
    // composite shape emits its `mangle_type` string. A drift here would silently
    // change every record's 4th field.
    let cases: &[(Type, &str)] = &[
        (Type::I64, ""),
        (Type::U32, ""),
        (Type::Bool, ""),
        (Type::Str, ""),
        (Type::Unit, ""),
        (Type::Named("Point".into(), vec![]), "Point"),
        (
            Type::Array {
                elem: Box::new(Type::I64),
                size: 3,
            },
            "Array__i64$3",
        ),
        (Type::Tuple(vec![Type::I64, Type::U32]), "$tuple2__i64$u32"),
        (
            Type::Ref(Box::new(Type::Named("Point".into(), vec![])), false),
            "ref_Point",
        ),
        (
            Type::Ref(Box::new(Type::Named("Point".into(), vec![])), true),
            "ref_mut_Point",
        ),
        (Type::Slice(Box::new(Type::I64)), "slice__i64"),
    ];
    for (ty, want) in cases {
        assert_eq!(
            &type_detail(ty),
            want,
            "type_detail known-answer drift for {ty:?}"
        );
        // The composite detail is exactly mangle_type (the SIGIL tc_tmangle twin).
        if !want.is_empty() && !matches!(ty, Type::Named(..)) {
            assert_eq!(&type_detail(ty), &mangle_type(ty));
        }
    }
}

#[test]
fn pr5e_mangle_injective() {
    // ET-D2: the type-detail encoder is INJECTIVE over a generated cross-product of
    // composite constructors (not a baked table) — two DISTINCT types may never
    // share a detail string, else two unrelated nodes could collide on one record.
    // Distinct leaves × {Array(0,1,2,255), Ref, RefMut, Slice, Tuple(2,3)} × one
    // level of nesting. A duplicate TYPE is fine; a duplicate DETAIL across
    // different types is the collision we forbid.
    use std::collections::HashMap;
    let leaves = [
        Type::I32,
        Type::U32,
        Type::I64,
        Type::U64,
        Type::F64,
        Type::Bool,
        Type::Str,
        Type::Unit,
        Type::Named("Point".into(), vec![]),
        Type::Named("Pixel".into(), vec![]),
    ];
    let mut constructed: Vec<Type> = Vec::new();
    for l in &leaves {
        constructed.push(l.clone());
        for sz in [0u32, 1, 2, 255] {
            constructed.push(Type::Array {
                elem: Box::new(l.clone()),
                size: sz,
            });
        }
        constructed.push(Type::Ref(Box::new(l.clone()), false));
        constructed.push(Type::Ref(Box::new(l.clone()), true));
        constructed.push(Type::Slice(Box::new(l.clone())));
    }
    // One level of nesting: every ordered leaf pair as a tuple, an array-of-tuple,
    // and a ref-of-array — exercises the recursive element mangle.
    for a in &leaves {
        for b in &leaves {
            constructed.push(Type::Tuple(vec![a.clone(), b.clone()]));
            constructed.push(Type::Array {
                elem: Box::new(Type::Tuple(vec![a.clone(), b.clone()])),
                size: 3,
            });
            constructed.push(Type::Ref(
                Box::new(Type::Array {
                    elem: Box::new(a.clone()),
                    size: 2,
                }),
                false,
            ));
        }
    }
    let mut seen: HashMap<String, String> = HashMap::new();
    for ty in &constructed {
        let detail = mangle_type(ty);
        let repr = format!("{ty:?}");
        if let Some(prev) = seen.get(&detail) {
            assert_eq!(
                prev, &repr,
                "ENCODING_COLLISION: {prev} and {repr} both mangle to {detail}"
            );
        } else {
            seen.insert(detail, repr);
        }
    }
    assert!(
        seen.len() >= 100,
        "ET-D2 enumeration too small ({} distinct details)",
        seen.len()
    );
}

#[test]
fn pr5e_adversarial_pos_match_oracle() {
    // Workflow-generated, oracle-vetted well-typed COMPOSITE programs (24): tuples
    // of arity 2/3/4 with scalar AND record elements (incl. names that collide
    // lexically with the mangle separators `ref_mut` / `i64` / `__`), shared and
    // exclusive record borrows in call-arg / let-value / nested-call / both-if-arms
    // positions, and multiple distinct composites in one program. Each must emit a
    // type-record stream byte-identical to the oracle and produce no diagnostic.
    let fixtures: &[&str] = &[
        "module m; record Point{x:i64} fn f(t:(Point,i64))->(Point,i64){return t;}",
        "module m; record A{x:i64} record B{y:u32} record C{z:bool} fn f(t:(A,B,C))->(A,B,C){return t;}",
        "module m; record P{x:i64} fn h(r:&P)->i64{return 0;} fn g(n:i64)->i64{return n;} fn f(p:P)->i64{return g(h(&p));}",
        "module m; record P{x:i64} fn use1(r:&P)->i64{return 0;} fn f(p:P)->i64{let r:&P=&p; return use1(&p);}",
        "module m; record P{x:i64} fn g(r:&mut P)->i64{return 0;} fn f(p:P)->i64{let mut q:P=p; return g(&mut q);}",
        "module m; record P{x:i64} fn tup(t:(i64,P))->(i64,P){return t;} fn sh(r:&P)->i64{return 0;} fn mt(r:&mut P)->i64{return 0;} fn f(p:P)->i64{let mut q:P=p; return sh(&p)+mt(&mut q);}",
        "module m; record ref_mut{x:i64} fn g(r:&ref_mut)->i64{return 0;} fn f(p:ref_mut)->i64{return g(&p);}",
        "module m; record i64x{a:i64} fn f(t:(i64x,u64))->(i64x,u64){return t;}",
        "module m; fn two(t:(i64,u32))->(i64,u32){return t;} fn three(t:(i64,u32,f64))->(i64,u32,f64){return t;} fn f(a:(i64,u32),b:(i64,u32,f64))->i64{return 0;}",
        "module m; record P{x:i64} fn g(r:&P)->i64{return 0;} fn f(p:P,c:bool)->i64{if c {return g(&p);} else {return g(&p);}}",
        "module m; record P{x:i64} fn f(t:(i64,u32),r:&P)->i64{return 0;}",
        "module m; record P{x:i64} fn h(r:&mut P)->i64{return 0;} fn g(n:i64)->i64{return n;} fn f(p:P)->i64{let mut q:P=p; return g(h(&mut q));}",
        "module m; fn f(t:(f64,u64,i32))->(f64,u64,i32){return t;}",
        "module m; record A_B{x:i64} fn f(t:(A_B,i64))->(A_B,i64){return t;}",
        "module m; record P{x:i64} record Q{y:u32} fn g(a:&P,b:&mut Q)->i64{return 0;} fn f(p:P,r:Q)->i64{let mut q:Q=r; return g(&p,&mut q);}",
        "module m; fn f(t: (i64, u32), a: i64, b: i64) -> i64 { return a + b; }",
        "module m; record P { x: i64 } fn f(p: P) -> i64 { let r: &P = &p; return p.x; }",
        "module m; record Point { x: i64 } fn f(t: (Point, i64)) -> (Point, i64) { return t; }",
        "module m; record P { x: i64 } fn g(r: &mut P) -> i64 { return 0; } fn f(p: P) -> i64 { let mut q: P = p; return g(&mut q); }",
        "module m; fn f(t: (i64, u32, bool, str)) -> (i64, u32, bool, str) { return t; }",
        "module m; record A { x: i64 } record B { y: u32 } fn f(t: (A, B)) -> (A, B) { return t; }",
        "module m; record P { x: i64 } fn g(r: &P) -> i64 { return 0; } fn h(r: &mut P) -> i64 { return 0; } fn f(p: P) -> i64 { let mut q: P = p; return g(&q); }",
        "module m; record P { x: i64 } fn g(r: &P) -> i64 { return 0; } fn f(p: P) -> i64 { let r: &P = &p; return g(&p); }",
        "module m; fn f(t: (i64, u32), c: bool) -> (i64, u32) { if c { return t; } else { return t; } }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-5e adversarial pos #{i}: composite type stream must match the oracle:
{src}"
        );
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5e adversarial pos #{i} was unexpectedly rejected by the oracle:
{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5e adversarial pos #{i} produced a spurious SIGIL diagnostic:
{src}"
        );
    }
}

#[test]
fn pr5e_adversarial_neg_codes_match_oracle() {
    // Workflow-generated, oracle-vetted ill-typed programs (32) that trip a CORE
    // T-code in the PRESENCE of a composite (a tuple param/return or a record
    // borrow let): every core diagnostic the checker owns — T041/T044/T045/T049/
    // T050/T051/T054/T055/T060/T062/T070/T071/T087/T088/T120/T190 — must still fire
    // at exact-code parity even when a tuple or `&record` is in scope. The composite
    // never perturbs the diagnostic. (Drops: composite call-return typing, tuple
    // literals, array->slice borrows, composite-return T044, ref-param T071, and
    // &scalar/T133 are out of PR-5e scope — see PR-5f.)
    let fixtures: &[&str] = &[
        "module m; fn f(t: (i64, u32)) -> (i64, u32) { return nope; }",
        "module m; record P { x: i64 } fn f(p: P) -> i64 { let r: &P = &p; return missing(); }",
        "module m; fn f(t: (i64, u32)) -> bool { return 5; }",
        "module m; fn f(t: (i64, u32)) -> i64 { if 5 { return 1; } else { return 0; } }",
        "module m; record P { x: i64 } fn f(p: P) -> i64 { let r: &P = &p; while 7 { return 1; } return 0; }",
        "module m; fn g(t: (i64, u32)) -> i64 { return 0; } fn f(t: (i64, u32)) -> i64 { return g(); }",
        "module m; fn h(x: i64) -> i64 { return x; } fn f(t: (i64, u32)) -> i64 { return h(true); }",
        "module m; fn f(t: (i64, u32), a: i64, b: u32) -> i64 { return a + b; }",
        "module m; record P { x: i64 } fn f(p: P, a: i64, b: bool) -> bool { let r: &P = &p; return a == b; }",
        "module m; fn f(t: (i64, u32)) -> i64 { let x: bool = 5; return 0; }",
        "module m; fn f(t: (i64, u32)) -> i64 { let mut x: i64 = 0; x = true; return x; }",
        "module m; record P { x: i64 } fn f(p: P) -> i64 { let r: &P = &p; return p.y; }",
        "module m; record P { x: i64 } fn f(p: P) -> i64 { let mut q: P = p; let r: &mut P = &mut q; return q.z; }",
        "module m; fn f(b: bool, t: (i64, u32)) -> i64 { if b { return 1; } else { let z: i64 = 0; } }",
        "module m; record P { x: i64 } fn f(p: P) -> i64 { let r: &P = &p; let z: i64 = p.x; }",
        "module m; enum E { A, B } record P { x: i64 } fn f(e: E, p: P) -> i64 { let r: &P = &p; match e { E::A => { return 1; } } }",
        "module m; fn f(b: bool, t: (i64, u32)) -> i64 { match b { true => { return 1; } } }",
        "module m; fn f(n: i64, t: (i64, u32)) -> i64 { match n { 5..=1 => { return 1; }, _ => { return 0; } } }",
        "module m; record P { x: i64 } fn g(r: &P) -> i64 { return 0; } fn f(p: P) -> i64 { let mut q: P = p; return g(&p, &q); }",
        "module m; record P { x: i64 } fn g(r: &P) -> i64 { return 0; } fn f(p: P) -> i64 { return g(&p, &p); }",
        "module m; fn f(t: (i64, u32), n: i64) -> i64 { if n { return 0; } else { return 1; } }",
        "module m; record P { x: i64 } fn f(p: P, n: i64) -> i64 { let r: &P = &p; while n { return 0; } return 1; }",
        "module m; record P { x: i64, y: u32 } fn f(p: P) -> i64 { let r: &P = &p; return p.x + p.y; }",
        "module m; record P { x: i64, y: u32 } fn f(p: P) -> bool { let r: &P = &p; return p.x == p.y; }",
        "module m; fn f(t: (i64, u32)) -> i64 { let z: bool = 5; return 0; }",
        "module m; record P { x: i64 } fn f(p: P) -> i64 { let r: &P = &p; return true; }",
        "module m; record P { x: i64 } fn f(p: P) -> i64 { let r: &P = &p; return p.z; }",
        "module m; fn f(t: (i64, u32)) -> i64 { let mut a: i64 = 0; a = true; return a; }",
        "module m; fn f(t: (i64, u32), n: i64) -> i64 { match n { 5..=1 => { return 0; }, _ => { return 1; } } }",
        "module m; record P { x: i64 } fn f(c: bool, p: P) -> i64 { let r: &P = &p; if c { return 0; } else { } }",
        "module m; fn f(t: (i64, u32), n: i64) -> i64 { match n { 0 => { return 0; } } }",
        "module m; record P { x: i64 } enum E { A, B } fn f(p: P, e: E) -> i64 { let r: &P = &p; match e { E::A => { return 0; } } }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5e adversarial neg #{i} has no core oracle code (mislabeled):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5e adversarial neg #{i}: SIGIL diagnostic codes must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-5f: composite types II — array literals (Array, tag 12), tuple literals
// (Tuple, tag 19, via the RecordConstruct desugar), and indexing `a[i]`. This
// lands the last MIN_COVERED Type tag (Array 12). Element types are inferred
// INDEPENDENTLY (an int-literal element defaults i64, NOT the annotation's
// element type) — the literal carries its OWN type, like the oracle. Composite
// call-return typing, slice borrows, and composite-element arrays remain out of
// scope (a follow-on).
// ===========================================================================

#[test]
fn pr5f_composite_literals_match_oracle() {
    // Each fixture's per-node stream (the array/tuple literal's `Array__…` /
    // `$tuple…` detail, its element records, and an index's element-typed result)
    // must match the oracle byte-for-byte.
    let fixtures: &[&str] = &[
        // Array literal, i64 elements -> Array__i64_3 (ret + literal both).
        "module m; fn f() -> [i64; 3] { return [1, 2, 3]; }",
        // The literal RESOLVES to the [u32;3] return type's element (array-stride
        // fix, return position): both the ret record AND the literal are u32 ->
        // Array__u32_3. (A returned TUPLE still types elements independently —
        // see the (u32,u32) case below; only arrays thread the element type.)
        "module m; fn f() -> [u32; 3] { return [1, 2, 3]; }",
        // Bool elements.
        "module m; fn f() -> [bool; 2] { return [true, false]; }",
        // Array-repeat `[v; N]` expands to N element nodes -> Array__i64_4.
        "module m; fn f() -> [i64; 4] { return [0; 4]; }",
        // Array literal as a let value (the value record + 3 element records).
        "module m; fn f() -> i64 { let a: [i64; 2] = [5, 6]; return 0; }",
        // Tuple literal (desugars to RecordConstruct) -> $tuple2__i64_bool.
        "module m; fn f() -> (i64, bool) { return (1, true); }",
        // Tuple literal stays $tuple2__i64_i64 under a (u32,u32) return.
        "module m; fn f() -> (u32, u32) { return (1, 2); }",
        // Indexing an array param -> the element type (i64); receiver is tag 12.
        "module m; fn f(a: [i64; 3]) -> i64 { return a[1]; }",
        // Indexing a u32 array -> u32 element; the index expr is i64.
        "module m; fn f(a: [u32; 3]) -> u32 { return a[0]; }",
        // Indexing a let-bound array literal.
        "module m; fn f() -> i64 { let a: [i64; 3] = [7, 8, 9]; return a[2]; }",
        // Index result feeding an arithmetic op (element type flows on).
        "module m; fn f(a: [i64; 3]) -> i64 { return a[0] + a[1]; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-5f composite-literal #{i}: SIGIL stream must match the oracle:
{src}"
        );
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5f composite-literal #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-5f composite-literal #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

#[test]
fn pr5f_adversarial_pos_match_oracle() {
    // Workflow-generated, oracle-vetted well-typed COMPOSITE-LITERAL/INDEX programs
    // (36): array literals of every scalar element + records (Array__P_2), the
    // [v; N] repeat form across sizes, tuple literals arity 2/3/4 mixing scalar +
    // record elements, array indexing feeding comparison / arithmetic / return
    // / loop bodies, and narrow-int array literals RETURNED by value (incl. across
    // if-branches — the array-stride fix resolves their elements to the return
    // type's T on both sides). Each must emit a type stream byte-identical to the oracle.
    let fixtures: &[&str] = &[
        "module m; fn f() -> i32 { let a: [i32; 3] = [10, 20, 30]; return a[0]; }",
        "module m; fn f() -> [u64; 2] { return [100, 200]; }",
        "module m; fn f() -> [f64; 3] { return [1.5, 2.5, 3.5]; }",
        "module m; fn f() -> [str; 2] { return [\"a\", \"b\"]; }",
        "module m; record P { x: i64 } fn f(p: P, q: P) -> i64 { let a: [P; 2] = [p, q]; return 0; }",
        "module m; fn f() -> [bool; 5] { return [true; 5]; }",
        "module m; fn f() -> [u32; 1] { return [9; 1]; }",
        "module m; fn f() -> [f64; 3] { return [2.5; 3]; }",
        "module m; fn f() -> [i64; 6] { return [0; 6]; }",
        "module m; fn f() -> (i64, bool, str) { return (7, true, \"z\"); }",
        "module m; fn f() -> (i32, u64, f64, bool) { return (1, 2, 3.5, false); }",
        "module m; record P { x: i64 } fn f(p: P) -> (P, i64) { return (p, 5); }",
        "module m; record A { x: i64 } record B { y: u32 } fn f(a: A, b: B) -> (A, B, i64) { return (a, b, 9); }",
        "module m; fn f(a: [i64; 3]) -> bool { return a[0] < a[1]; }",
        "module m; fn f(a: [i64; 4]) -> i64 { return a[0] + a[1] + a[2]; }",
        "module m; fn f(a: [u32; 3]) -> u32 { return a[0] + a[2]; }",
        "module m; fn f() -> u64 { let a: [u64; 3] = [1, 2, 3]; return a[1]; }",
        "module m; record P { x: i64 } fn f(a: [P; 2]) -> i64 { return 0; }",
        "module m; record P { x: i64 } record Q { y: u32 } fn f(p: P, q: Q) -> (P, Q, i64, bool) { return (p, q, 5, true); }",
        "module m; record P { x: i64 } fn f() -> [P; 2] { let p: P = P { x: 1 }; let q: P = P { x: 2 }; return [p, q]; }",
        "module m; fn f() -> i64 { let a: [i64; 5] = [0; 5]; return a[4]; }",
        "module m; fn f(a: [i64; 3]) -> bool { return a[0] < a[2]; }",
        "module m; fn f(a: [bool; 3]) -> bool { return a[2]; }",
        "module m; fn f(a: [str; 2]) -> str { return a[0]; }",
        "module m; fn f(a: [u32; 4]) -> bool { return a[0] < a[1]; }",
        "module m; fn f(a: [i64; 3]) -> i64 { let mut s: i64 = 0; let mut i: i64 = 0; while i < 3 { s = s + a[i]; i = i + 1; } return s; }",
        "module m; record P { x: i64 } fn f() -> [P; 2] { return [P { x: 1 }, P { x: 2 }]; }",
        "module m; fn f() -> (i64, bool, i64, bool) { return (1, true, 3, false); }",
        "module m; fn f(p: i64, q: i64, r: i64) -> (i64, i64, i64) { return (p, q, r); }",
        "module m; fn f() -> (i64, u32) { let t: (i64, u32) = (1, 2); return t; }",
        "module m; fn f(a: [u32; 3]) -> u32 { return a[0] + a[1]; }",
        "module m; fn f() -> [i64; 2] { let a: [i64; 2] = [3, 4]; return a; }",
        "module m; fn f() -> i64 { let a: [bool; 2] = [true, false]; if a[0] { return 1; } else { return 0; } }",
        "module m; fn f(a: [i64; 3]) -> i64 { return a[2]; }",
        // Array-stride fix, return position: a narrow-int array literal returned
        // by value resolves its elements to the return type's T (Array__i32_3).
        "module m; fn f() -> [i32; 3] { return [10, 20, 30]; }",
        // Returns across BOTH if-branches: each `return [..]` resolves to u32.
        "module m; fn f(c: bool) -> [u32; 2] { if c { return [1, 2]; } else { return [3, 4]; } }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-5f adversarial pos #{i}: composite stream must match the oracle:
{src}"
        );
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5f adversarial pos #{i} was unexpectedly rejected by the oracle:
{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5f adversarial pos #{i} produced a spurious SIGIL diagnostic:
{src}"
        );
    }
}

#[test]
fn pr5f_adversarial_neg_codes_match_oracle() {
    // Workflow-generated, oracle-vetted ill-typed programs (21) that trip a CORE
    // T-code in the PRESENCE of an array/tuple literal or an array index — every
    // core diagnostic must still fire at exact-code parity. (Drops, out of PR-5f
    // scope: composite-VALUE checking — T041/T045/T049/T044 against a composite
    // literal/return — plus empty arrays, composite call-return, borrow-index,
    // un-annotated composite lets, and nested/composite-element arrays.)
    let fixtures: &[&str] = &[
        "module m; fn f() -> i64 { let t: (i64, bool) = (1, true); return undefined_thing; }",
        "module m; fn f(a: [i64; 3]) -> i64 { return a[k]; }",
        "module m; fn f(b: bool) -> i64 { let a: [i64; 2] = [1, 2]; if b { return a[0]; } else { } }",
        "module m; fn f() -> i64 { let a: [i64; 2] = [1, 2]; let z: bool = a[0]; return 0; }",
        "module m; fn f() -> i64 { let a: [i64; 2] = [1, 2]; if a[0] { return 1; } else { return 0; } }",
        "module m; fn f(a: [i64; 2]) -> i64 { while a[0] { return 1; } return 0; }",
        "module m; fn f(a: [i64; 3]) -> i64 { return a[0] + true; }",
        "module m; fn f() -> bool { let a: [i64; 2] = [3, 4]; return a[0] == \"x\"; }",
        "module m; fn f(a: [u32; 3]) -> u32 { return a[0] + a[1] + miss(); }",
        "module m; fn g(x: i64) -> i64 { return x; } fn f(a: [i64; 3]) -> i64 { return g(a[0], a[1]); }",
        "module m; fn g(x: u32) -> u32 { return x; } fn f(a: [i64; 2]) -> u32 { return g(a[0]); }",
        "module m; enum E { A, B } fn f(e: E, a: [i64; 2]) -> i64 { match e { E::A => { return a[0]; } } }",
        "module m; fn f(b: bool, a: [i64; 2]) -> i64 { match b { true => { return a[0]; } } }",
        "module m; record P { x: i64 } fn f(p: P) -> i64 { let a: [i64; 2] = [1, 2]; return p.bogus; }",
        "module m; fn f(a: [i64; 3], n: i64) -> i64 { match n { 5..=1 => { return a[0]; }, _ => { return 0; } } }",
        "module m; fn f(a: [u32; 3]) -> u32 { return nope; }",
        "module m; fn f(a: [i64; 3]) -> bool { return a[0] == true; }",
        "module m; fn f() -> i64 { let a: [i64; 2] = [1, 2]; return undefn(a[0]); }",
        "module m; fn f(a: [i64; 3]) -> i64 { if a[0] { return 1; } else { return 0; } }",
        "module m; fn f(a: [i64; 3], n: i64) -> i64 { while n { return a[0]; } return a[1]; }",
        "module m; fn f(a: [i64; 3]) -> i64 { let mut x: i64 = 0; x = true; return a[0]; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5f adversarial neg #{i} has no core oracle code (mislabeled):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5f adversarial neg #{i}: SIGIL diagnostic codes must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-5g: block-scope resolution parity (ET-T5). SIGIL's symbol table now unwinds
// a nested if/while/match-arm block's bindings on exit (tc_scope_unwind), so a
// name resolves to the SAME declaration the oracle's scoped resolver picks. The
// canaries below previously diverged (an inner shadow leaked past its block,
// causing a spurious T049); they now match the oracle byte-for-byte. ET-T5 is
// satisfied BY CONSTRUCTION — resolution is correct, so a separate binding-id
// channel would be tautological (ET-D7) and is not built.
// ===========================================================================

#[test]
fn pr5g_block_scope_resolution_match_oracle() {
    let fixtures: &[&str] = &[
        // Canary A: a u32 inner shadow must NOT leak — `return x` is the outer i64.
        "module m; fn f(c: bool) -> i64 { let x: i64 = 1; if c { let x: u32 = 2; let y: u32 = x; } else { } return x; }",
        // Canary B: same-type inner shadow (type-invisible leak) — outer x.
        "module m; fn f(c: bool) -> i64 { let x: i64 = 1; if c { let x: i64 = 2; let y: i64 = x; } else { } return x; }",
        // Canary C: a while-body inner shadow must not leak.
        "module m; fn f(c: bool) -> i64 { let x: i64 = 1; while c { let x: u32 = 9; let y: u32 = x; } return x; }",
        // A match-arm binding must not leak past the match.
        "module m; fn f(n: i64) -> i64 { let x: i64 = 1; match n { 0 => { let x: u32 = 2; let y: u32 = x; }, _ => { } } return x; }",
        // Sibling isolation: a then-branch binding is not visible in the else.
        "module m; fn f(c: bool) -> i64 { if c { let y: i64 = 5; return y; } else { let y: u32 = 6; let z: u32 = y; return 0; } }",
        // A legitimate SAME-scope shadow still resolves to the most-recent decl.
        "module m; fn f() -> u32 { let x: i64 = 1; let x: u32 = 2; return x; }",
        // The inner binding IS visible within its own block.
        "module m; fn f(c: bool) -> i64 { if c { let y: i64 = 5; return y; } else { return 0; } }",
        // Nested blocks: each level unwinds independently.
        "module m; fn f(c: bool, d: bool) -> i64 { let x: i64 = 1; if c { if d { let x: u32 = 9; let y: u32 = x; } else { } } else { } return x; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-5g block-scope #{i}: SIGIL resolution must match the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-5g block-scope #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

#[test]
fn pr5g_adversarial_pos_match_oracle() {
    // Workflow-generated, oracle-vetted well-typed SHADOWING programs (22):
    // different-type inner shadows across if/else/while/match (a post-block use
    // must take the OUTER type), parameter shadows, deeply-nested shadows
    // (match-in-while-in-if), legal same-scope re-shadows (most-recent wins), and
    // enum-payload arm bindings (arm-local). Each must resolve identically to the
    // oracle — a residual scope leak would mistype a post-block use.
    let fixtures: &[&str] = &[
        "module m; fn f(c: bool) -> i64 { let x: i64 = 1; if c { } else { let x: bool = true; let y: bool = x; } return x; }",
        "module m; fn f(c: bool) -> i64 { let x: i64 = 1; while c { let x: str = \"a\"; let y: str = x; } return x; }",
        "module m; fn f(n: i64) -> i64 { let x: i64 = 1; match n { 0 => { let x: f64 = 1.5; let y: f64 = x; }, _ => { } } return x; }",
        "module m; fn f(p: i64, c: bool) -> i64 { if c { let p: u32 = 9; let y: u32 = p; } else { } return p; }",
        "module m; fn f(p: str, c: bool) -> str { while c { let p: u32 = 3; let y: u32 = p; } return p; }",
        "module m; fn f(c: bool, d: bool) -> i64 { let x: i64 = 1; if c { if d { let x: u32 = 9; let y: u32 = x; } else { } let z: i64 = x; } else { } return x; }",
        "module m; fn f(c: bool, d: bool) -> i64 { let x: i64 = 1; if c { while d { let x: bool = true; let y: bool = x; } } else { } return x; }",
        "module m; fn f(c: bool, n: i64) -> i64 { let x: i64 = 1; while c { match n { 0 => { let x: f64 = 2.5; let y: f64 = x; }, _ => { } } } return x; }",
        "module m; fn f() -> u32 { let x: i64 = 1; let x: u32 = 2; let y: u32 = x; return y; }",
        "module m; fn f() -> bool { let x: i64 = 1; let x: u32 = 2; let x: bool = true; return x; }",
        "module m; enum E { S(u32), N } fn f(e: E) -> i64 { let x: i64 = 1; match e { E::S(x) => { let y: u32 = x; }, E::N => { } } return x; }",
        "module m; fn f(c: bool, o: bool, n: i64) -> i64 { let x: i64 = 1; if c { while o { match n { 0 => { let x: u32 = 7; let y: u32 = x; }, _ => { } } } } else { } return x; }",
        "module m; fn f(c: bool, d: bool) -> i64 { let x: i64 = 1; if c { if d { let x: u32 = 9; let y: u32 = x; } else { } } else { } return x; }",
        "module m; fn f(p: i64, c: bool) -> i64 { if c { let p: u32 = 7; let y: u32 = p; } else { } return p; }",
        "module m; fn f(c: bool) -> u32 { let x: i64 = 1; let x: u32 = 2; return x; }",
        "module m; fn f(c: bool) -> i64 { let x: i64 = 1; if c { let x: u32 = 2; let y: u32 = x; } else { let x: bool = true; let z: bool = x; } return x; }",
        "module m; fn f(c: bool, d: bool) -> i64 { let x: i64 = 1; if c { if d { let x: u32 = 9; } else { let x: bool = true; let y: bool = x; } } else { } return x; }",
        "module m; fn f(n: i64) -> i64 { let x: i64 = 7; match n { 0 => { let x: u32 = 2; let y: u32 = x; }, 1 => { let x: bool = false; let z: bool = x; }, _ => { } } return x; }",
        "module m; fn f(o: bool) -> i64 { let v: i64 = 3; while o { let v: f64 = 1.5; let w: f64 = v; } return v; }",
        "module m; enum E { S(u32), N } fn f(o: bool, e: E) -> i64 { let x: i64 = 1; while o { match e { E::S(x) => { let y: u32 = x; }, E::N => { } } } return x; }",
        "module m; enum E { A(u32), B(bool) } fn f(e: E) -> i64 { match e { E::A(v) => { let a: u32 = v; return 0; }, E::B(v) => { let b: bool = v; if b { return 1; } else { return 2; } } } }",
        "module m; fn f(p: i64, n: i64) -> i64 { match n { 0 => { let p: u32 = 9; let q: u32 = p; }, _ => { } } return p; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-5g adversarial pos #{i}: resolution must match the oracle:
{src}"
        );
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5g adversarial pos #{i} was unexpectedly rejected by the oracle:
{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5g adversarial pos #{i} produced a spurious SIGIL diagnostic:
{src}"
        );
    }
}

#[test]
fn pr5g_adversarial_neg_codes_match_oracle() {
    // Workflow-generated, oracle-vetted ill-typed shadowing programs (24): a
    // block-local binding referenced after its block / in a sibling branch / arm
    // (T060), and mistypes (T041/T049/T054/T055/T071/T050/T087/T088) that ONLY
    // surface when resolution correctly binds a post-block use to the OUTER
    // declaration — proving the scope unwind is correct, not just silent. Each
    // must reproduce the oracle's exact core codes.
    let fixtures: &[&str] = &[
        "module m; fn f(c: bool) -> i64 { if c { let y: i64 = 5; return y; } else { let z: i64 = y; return z; } }",
        "module m; fn f(c: bool) -> i64 { let x: i64 = 1; if c { let x: bool = true; } else { } let y: bool = x; return 0; }",
        "module m; fn f(c: bool) -> u32 { let x: u32 = 1; if c { let x: i64 = 9; } else { } return x < 0; }",
        "module m; enum E { S(i64), N } fn f(e: E) -> i64 { match e { E::S(v) => { return v; }, E::N => { return v; } } }",
        "module m; fn f(c: bool) -> i64 { let s: str = \"hi\"; while c { let s: i64 = 3; } return s + 1; }",
        "module m; fn f(c: bool) -> i64 { if c { let y: u32 = 5; } else { } return y; }",
        "module m; fn f(c: bool) -> i64 { while c { let w: i64 = 3; } return w; }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { let y: u32 = 7; }, _ => { } } return y; }",
        "module m; fn f(c: bool) -> i64 { if c { let y: i64 = 5; return y; } else { let z: i64 = y; return 0; } }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { let a: i64 = 1; }, _ => { let b: i64 = a; } } return 0; }",
        "module m; fn f(c: bool) -> i64 { if c { let x: str = \"hi\"; } else { let y: i64 = x; } return x; }",
        "module m; fn f(c: bool) -> i64 { let x: i64 = 1; if c { let x: u32 = 2; } else { } return x + true; }",
        "module m; fn g(p: u32) -> u32 { return p; } fn f(c: bool) -> i64 { let x: i64 = 1; if c { let x: u32 = 2; } else { } return g(x); }",
        "module m; fn f(n: i64) -> u32 { let r: u32 = 1; match n { 0 => { let r: i64 = 5; let q: i64 = r; }, _ => { } } return r < 0; }",
        "module m; fn f(c: bool) -> i64 { let x: i64 = 1; if c { let y: u32 = x; let z: bool = y; } else { } return x; }",
        "module m; enum E { A(u32), B } fn f(e: E) -> i64 { let v: i64 = 1; match e { E::A(v) => { let q: bool = v; }, E::B => { } } return v; }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { let a: i64 = 1; return a; }, _ => { return a; } } }",
        "module m; fn f(c: bool) -> bool { if c { let y: i64 = 5; let z: i64 = y; return true; } else { let w: bool = y; return w; } }",
        "module m; fn f(o: bool) -> i64 { while o { let q: i64 = 3; } return q; }",
        "module m; fn f(n: i64, k: i64) -> i64 { match n { 0 => { match k { 1 => { let w: i64 = 5; }, _ => { } } return w; }, _ => { return 0; } } }",
        "module m; enum E { S(i64), N } fn f(e: E) -> i64 { match e { E::S(x) => { return x; }, E::N if x > 0 => { return 1; }, _ => { return 0; } } }",
        "module m; fn f(n: i64) -> i64 { match n { 0 => { let x: i64 = 3; if x { return 1; } else { return 2; } }, _ => { return 0; } } }",
        "module m; fn f(c: bool) -> i64 { if c { let y: i64 = 2; while y { return 0; } return 0; } else { return 0; } }",
        "module m; enum E { A, B } fn f(c: bool, e: E) -> i64 { if c { match e { E::A => { return 1; } } } else { return 0; } }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5g adversarial neg #{i} has no core oracle code (mislabeled):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5g adversarial neg #{i}: SIGIL diagnostic codes must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-5h: the Epic-1 DONE-LINE gate. Crystallizes the ET-D8 MIN_COVERED floor
// (every core T-code + every core Type tag has a fixture proving parity), plus
// the ET-T4 property suite (no surviving IntLit / Error in a clean stream),
// ET-T1 real-fixture admission (the independently-authored `.sigil` compiler
// fixtures pass the SIGIL differential — anti-self-certification), and an ET-T3
// reject-for-the-right-reason mutation round-trip.
// ===========================================================================

/// ET-D8: the pinned, falsifiable done-line floor. IntLit (20) / Error (21) are
/// excluded by construction — a clean post-IntLit-pass stream carries neither.
const MIN_COVERED_TAGS: &[i64] = &[0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 14, 19];

/// One NEGATIVE fixture per core T-code — the manifest is RED if a code has no
/// covering fixture, or the fixture no longer reproduces it at SIGIL/oracle parity.
const CODE_MANIFEST: &[(&str, &str)] = &[
    (
        "T041",
        "module m; fn f() -> i64 { let x: bool = 5; return 0; }",
    ),
    ("T044", "module m; fn f() -> i64 { let x: i64 = 0; }"),
    (
        "T045",
        "module m; fn f() -> i64 { let mut x: i64 = 0; x = true; return x; }",
    ),
    (
        "T046",
        "module m; record P { x: i64 } record Q { y: i64 } fn f(p: P) -> i64 { let q: Q = p; return 0; }",
    ),
    ("T049", "module m; fn f() -> i64 { return true; }"),
    (
        "T050",
        "module m; fn f(b: i64) -> i64 { if b { return 1; } else { return 0; } }",
    ),
    (
        "T051",
        "module m; fn f(b: i64) -> i64 { while b { return 1; } return 0; }",
    ),
    (
        "T054",
        "module m; fn f(a: i64, b: u32) -> i64 { return a + b; }",
    ),
    (
        "T055",
        "module m; fn f(a: i64, b: bool) -> bool { return a == b; }",
    ),
    ("T060", "module m; fn f() -> i64 { return nope; }"),
    ("T062", "module m; fn f() -> i64 { return missing(); }"),
    (
        "T070",
        "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(); }",
    ),
    (
        "T071",
        "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(true); }",
    ),
    (
        "T087",
        "module m; enum E { A, B } fn f(e: E) -> i64 { match e { E::A => { return 1; } } }",
    ),
    (
        "T088",
        "module m; fn f(b: bool) -> i64 { match b { true => { return 1; } } }",
    ),
    (
        "T120",
        "module m; record P { x: i64 } fn f(p: P) -> i64 { return p.y; }",
    ),
    (
        "T190",
        "module m; fn f(n: i64) -> i64 { match n { 5..=1 => { return 1; }, _ => { return 0; } } }",
    ),
    // PR-6a — declaration-time trait coherence (ET-TR0 MIN_COVERED floor):
    (
        "T248",
        "module m; record P { x: i64 } impl Bogus for P { fn bogus(self: P) -> i64 { return self.x; } }",
    ),
    (
        "T249",
        "module m; trait Hash { fn hash(self: Self) -> i64; } impl Hash for i64 { fn hash(self: i64) -> i64 { return self; } }",
    ),
    (
        "T250",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } }",
    ),
    // PR-6b — call-site bound satisfaction (ET-TR0 MIN_COVERED floor):
    (
        "T245",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record NoH { v: i64 } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: NoH = NoH { v: 1 }; return keyed(n); }",
    ),
    (
        "T246",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record Bad { v: i64 } impl Bad { fn hash(self: Bad) -> bool { return true; } } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let b: Bad = Bad { v: 1 }; return keyed(b); }",
    ),
    // PR-G1a — a generic free fn whose return bare-IS a type-param, called with no
    // binding arg and no annotation: the type-param cannot be inferred (ET-G3b). The
    // generic body is never instantiated, so its `T`-vs-i64 return is NOT checked
    // (AG-G9, the body-code asymmetry) — T150 is the sole core code.
    (
        "T150",
        "module m; fn make<T>() -> T { let d: i64 = 0; return d; } fn f() -> i64 { let x = make(); return 0; }",
    ),
    // PR-G2a-ii — an un-annotated generic-record construct whose type-param is bound by NO
    // field (a phantom `Holder<T>` with only a concrete field) cannot be inferred → T233.
    (
        "T233",
        "module m; record Holder<T> { tag: i64 } fn f() -> i64 { let h = Holder { tag: 0 }; return h.tag; }",
    ),
    // PR-G2a-iii — an un-annotated construct binding ONE type-param to conflicting concretes
    // (field `a` → i64 via the int-lit's default, field `b` → str) → T234. The int literal
    // cannot flex to str, so the two bindings disagree.
    (
        "T234",
        "module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p = Pair { a: 5, b: \"x\" }; return 0; }",
    ),
    // PR-G2b-iii — a BARE variant `Some` declared by TWO in-scope enums, constructed with no
    // disambiguating annotation/qualifier → ambiguous → T236.
    (
        "T236",
        "module m; enum A<T> { Some(T), None } enum B<T> { Some(T), None } fn f() -> i64 { let v = Some(5); return 0; }",
    ),
    // PR-E3a/b — an f-string hole whose type is not str/i64/bool (here an f64 param) is
    // not stringifiable → T262 at the f-string, on both sides. (i64/bool are ACCEPTED
    // as of PR-E3b — auto-converted — so an f64 hole is the canonical T262 trigger.)
    (
        "T262",
        "module m; fn f(x: f64) -> str { return f\"v={x}\"; }",
    ),
];

/// One POSITIVE fixture per core Type tag — each clean program's stream carries
/// that tag, at SIGIL/oracle parity.
const TAG_MANIFEST: &[(i64, &str)] = &[
    (0, "module m; fn f() { }"),
    (1, "module m; fn f() -> bool { return true; }"),
    (2, "module m; fn f() -> i32 { let x: i32 = 0; return x; }"),
    (3, "module m; fn f() -> u32 { let x: u32 = 0; return x; }"),
    (4, "module m; fn f() -> i64 { return 0; }"),
    (5, "module m; fn f() -> u64 { let x: u64 = 0; return x; }"),
    (6, "module m; fn f() -> f64 { return 1.5; }"),
    (7, "module m; fn f() -> str { return \"hi\"; }"),
    (
        9,
        "module m; record P { x: i64 } fn f(p: P) -> i64 { return p.x; }",
    ),
    (12, "module m; fn f() -> [i64; 3] { return [1, 2, 3]; }"),
    (
        14,
        "module m; record P { x: i64 } fn g(r: &P) -> i64 { return 0; } fn f(p: P) -> i64 { return g(&p); }",
    ),
    (
        19,
        "module m; fn f(t: (i64, u32)) -> (i64, u32) { return t; }",
    ),
];

/// Does any record in the stream carry `tag` in its 3rd (tag) field?
fn stream_has_tag(records: &str, tag: i64) -> bool {
    let want = tag.to_string();
    records.split(';').filter(|s| !s.is_empty()).any(|r| {
        let fields: Vec<&str> = r.split(',').collect();
        fields.len() >= 3 && fields[2] == want
    })
}

#[test]
fn pr5h_corpus_coverage_min_covered() {
    // Every core code is covered by a fixture that reproduces it at parity.
    for code in CORE_CODES {
        let entry = CODE_MANIFEST.iter().find(|(c, _)| c == code);
        let (_, src) =
            entry.unwrap_or_else(|| panic!("MIN_COVERED: no manifest fixture for code {code}"));
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            oc.iter().any(|c| c.split(',').next() == Some(*code)),
            "MIN_COVERED: fixture for {code} no longer reproduces it (oracle={oc:?}):\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "MIN_COVERED: SIGIL code parity failed for {code}:\n{src}"
        );
    }
    // Every core Type tag is emitted by a clean fixture, at record parity.
    for tag in MIN_COVERED_TAGS {
        let entry = TAG_MANIFEST.iter().find(|(t, _)| t == tag);
        let (_, src) =
            entry.unwrap_or_else(|| panic!("MIN_COVERED: no manifest fixture for tag {tag}"));
        let sr = sigil_records(src);
        assert!(
            stream_has_tag(&sr, *tag),
            "MIN_COVERED: fixture for tag {tag} does not emit it:\n{src}\n{sr}"
        );
        assert_eq!(
            sorted_recs(&sr),
            sorted_recs(&oracle_records(src)),
            "MIN_COVERED: SIGIL record parity failed for tag {tag}:\n{src}"
        );
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "MIN_COVERED: tag {tag} fixture is not a positive:\n{src}"
        );
    }
}

#[test]
fn pr5h_no_intlit_no_error_in_clean_stream() {
    // ET-T4: a clean (oracle-accepted) program's SIGIL stream must carry neither a
    // surviving IntLit (tag 20 — the post-pass defaults every unpinned literal) nor
    // an Error (tag 21). Checked over every positive manifest fixture.
    for (_, src) in TAG_MANIFEST {
        let sr = sigil_records(src);
        assert!(
            !stream_has_tag(&sr, 20),
            "SURVIVING_INTLIT (tag 20) in a clean stream:\n{src}\n{sr}"
        );
        assert!(
            !stream_has_tag(&sr, 21),
            "SPURIOUS_ERROR (tag 21) in a clean stream:\n{src}\n{sr}"
        );
    }
}

#[test]
fn pr5h_real_sigil_fixtures_match_oracle() {
    // ET-T1 (anti-self-certification): the independently-authored standalone
    // `.sigil` compiler fixtures — written for the Rust compiler's own tests, not
    // for this differential — reproduce their core code at SIGIL/oracle parity.
    let fixtures: &[(&str, &str)] = &[
        (
            "T046",
            include_str!("../../sigil-compiler/tests/fixtures/T046.sigil"),
        ),
        (
            "T190",
            include_str!("../../sigil-compiler/tests/fixtures/T190.sigil"),
        ),
    ];
    for (code, src) in fixtures {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            oc.iter().any(|c| c.split(',').next() == Some(*code)),
            "ET-T1: real fixture {code}.sigil does not reproduce {code} as a core code (oracle={oc:?})"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "ET-T1: SIGIL parity failed on real fixture {code}.sigil"
        );
    }
}

#[test]
fn pr5h_reject_for_the_right_reason_roundtrip() {
    // ET-T3: each malformed program rejects with exactly its declared core code,
    // AND the MINIMAL fix (the mutation site repaired) type-checks clean on both
    // sides — proving the rejection is for the RIGHT reason, not incidental.
    let pairs: &[(&str, &str, &str)] = &[
        (
            "T049",
            "module m; fn f() -> i64 { return true; }",
            "module m; fn f() -> i64 { return 0; }",
        ),
        (
            "T060",
            "module m; fn f() -> i64 { return nope; }",
            "module m; fn f() -> i64 { let nope: i64 = 0; return nope; }",
        ),
        (
            "T071",
            "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(true); }",
            "module m; fn g(x: i64) -> i64 { return x; } fn f() -> i64 { return g(0); }",
        ),
        (
            "T087",
            "module m; enum E { A, B } fn f(e: E) -> i64 { match e { E::A => { return 1; } } }",
            "module m; enum E { A, B } fn f(e: E) -> i64 { match e { E::A => { return 1; }, E::B => { return 2; } } }",
        ),
        (
            "T120",
            "module m; record P { x: i64 } fn f(p: P) -> i64 { return p.y; }",
            "module m; record P { x: i64 } fn f(p: P) -> i64 { return p.x; }",
        ),
    ];
    for (code, broken, fixed) in pairs {
        let bc = sorted_codes(&oracle_codes(broken));
        assert!(
            bc.iter().any(|c| c.split(',').next() == Some(*code)),
            "ET-T3: broken fixture for {code} does not reject with it (oracle={bc:?}):\n{broken}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(broken)),
            bc,
            "ET-T3: SIGIL parity on broken {code}"
        );
        assert!(
            sorted_codes(&oracle_codes(fixed)).is_empty(),
            "ET-T3: MUTATION_SITE not minimal — repaired program still rejected by oracle:\n{fixed}"
        );
        assert!(
            sorted_codes(&sigil_codes(fixed)).is_empty(),
            "ET-T3: repaired program produced a spurious SIGIL diagnostic:\n{fixed}"
        );
    }
}

// ===========================================================================
// PR-5i: composite-VALUE checking (T049/T041/T045/T044). A composite value in a
// scalar context (or vice-versa) now rejects at oracle parity (detail-presence
// XOR, gated on the non-composite side being concrete — ET-V1). Composite-vs-
// composite is deferred (AG-V1). An errored value suppresses the mismatch.
// ===========================================================================

#[test]
fn pr5i_composite_value_checks() {
    let fixtures: &[&str] = &[
        // composite-vs-SCALAR mismatch → a core code, SIGIL == oracle:
        "module m; fn f() -> i64 { return [1, 2, 3]; }",
        "module m; fn f() -> i64 { return (1, 2); }",
        "module m; fn f() -> i64 { let x: bool = (1, 2); return 0; }",
        "module m; fn f() -> i64 { let a: [i64; 3] = 0; return 0; }",
        "module m; fn f() -> i64 { let mut x: i64 = 0; x = (1, 2); return x; }",
        "module m; fn f(c: bool) -> (i64, u32) { if c { return (1, 2); } else { } }",
        // ET-V1 canaries — composite-vs-composite, oracle ACCEPTS → SIGIL stays silent:
        "module m; fn f() -> (u32, u32) { return (1, 2); }",
        "module m; fn f() -> (i64, u32) { let t: (i64, u32) = (1, 2); return t; }",
        "module m; fn f() -> i64 { let a: [i64; 2] = [5, 6]; return 0; }",
        // error-cascade: an undefined value emits ONLY T060 (no spurious T049):
        "module m; fn f(t: (i64, u32)) -> (i64, u32) { return nope; }",
        // valid composite passthrough stays clean:
        "module m; fn f(t: (i64, u32)) -> (i64, u32) { return t; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-5i composite-value #{i}: SIGIL codes must match the oracle:
{src}"
        );
    }
    // ET-V1 hard canary (FALSE_REJECT_CANARY): a valid composite-literal return,
    // whose literal mangles i64 against a u32 return, must NEVER be rejected.
    let canary = "module m; fn f() -> (u32, u32) { return (1, 2); }";
    assert!(
        sorted_codes(&sigil_codes(canary)).is_empty(),
        "FALSE_REJECT_CANARY: SIGIL rejected a valid composite literal return"
    );
}

#[test]
fn pr5i_adversarial_pos_match_oracle() {
    // Workflow-generated, oracle-vetted COMPOSITE positives (9) the checker must NOT
    // over-reject: IntLit-flex composite-vs-composite (`(u32,u32)=(1,2)`,
    // `[u32;N]=[..]`, mixed, repeat form, arity-4), same-type tuple/array/record-tuple
    // passthrough, and index-decayed-scalar flow. Each stays clean at oracle parity.
    let fixtures: &[&str] = &[
        "module m; fn f() -> i64 { let a: [u32; 3] = [1, 2, 3]; return 0; }",
        "module m; record P { x: i64 } fn f(t: (P, i64)) -> (P, i64) { return t; }",
        "module m; fn f(c: bool) -> (u32, u32) { if c { return (1, 2); } else { return (3, 4); } }",
        "module m; fn f() -> i64 { let t: (i64, u32) = (1, 2); return 0; }",
        "module m; fn f() -> i64 { let a: [u32; 4] = [0; 4]; return 0; }",
        "module m; fn f() -> i64 { let a: [i64; 2] = [5, 6]; let b: i64 = a[0]; return b; }",
        "module m; fn f(c: bool) -> (i64, u32) { if c { return (1, 2); } else { return (3, 4); } }",
        "module m; fn f(a: [u32; 3]) -> u32 { let s: u32 = a[0] + a[1]; return s; }",
        "module m; fn f() -> (u32, u32, u32, u32) { return (1, 2, 3, 4); }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-5i adversarial pos #{i}: SIGIL stream must match the oracle:
{src}"
        );
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5i adversarial pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5i adversarial pos #{i} produced a spurious SIGIL diagnostic (FALSE_REJECT):
{src}"
        );
    }
}

#[test]
fn pr5i_adversarial_neg_codes_match_oracle() {
    // Workflow-generated, oracle-vetted composite-VALUE mismatches (26): a composite
    // value in a scalar context (or vice-versa) tripping T049/T041/T045/T044 — across
    // tuples and arrays of every element type, combined with other core codes, with
    // records/enums in scope, and the ERROR-CASCADE (an undefined value emits ONLY its
    // own code, never an extra composite mismatch). Each at exact code parity.
    // (Drops, out of PR-5i scope: composite-vs-composite mismatch (tuple arity / array
    // size — AG-V1), ref-param T071 (PR-5j), array-by-value-return (non-core move).)
    let fixtures: &[&str] = &[
        "module m; fn f() -> bool { return (1, 2); }",
        "module m; fn f() -> i64 { return (\"a\", true); }",
        "module m; fn f() -> i64 { let b: bool = [1.5, 2.5]; return 0; }",
        "module m; fn f() -> i64 { let t: (i64, u32) = 5; return 0; }",
        "module m; fn f() -> i64 { let mut a: [i64; 2] = 0; return 0; }",
        "module m; fn f() -> i64 { let mut s: str = \"x\"; s = (1, 2); return 0; }",
        "module m; fn f() -> i64 { let mut x: i64 = 0; x = [9, 8]; return x; }",
        "module m; fn f() -> [i64; 3] { let x: i64 = 0; }",
        "module m; fn f(b: bool) -> (i64, u32) { if b { return (1, 2); } else { } }",
        "module m; fn f(b: bool) -> [i64; 2] { while b { return [1, 2]; } }",
        "module m; fn f(n: i64) -> i64 { if n { return [1, 2]; } else { return 0; } }",
        "module m; fn f() -> u32 { return [1, 2, 3]; } fn g() -> i64 { return nope; }",
        "module m; fn f() -> bool { let s: str = (1, 2); return (3, 4); }",
        "module m; enum E { A, B } fn f() -> i64 { let e: E = E::A; let z: bool = (1, 2); return 0; }",
        "module m; fn f() -> i64 { let a: [u32; 3] = bogus; return 0; }",
        "module m; fn f() -> (i64, u32) { return nope; }",
        "module m; fn f() -> u32 { return [1, 2, 3]; }",
        "module m; enum E { A, B } fn f() -> i64 { let e: E = E::A; return (1, 2); }",
        "module m; record P { x: i64 } fn f() -> i64 { let p: P = P { x: 1 }; let a: [i64; 2] = [1, 2]; return a; }",
        "module m; fn f() -> i64 { let x: f64 = [1, 2]; return 0; }",
        "module m; fn f() -> i64 { let mut s: [i64; 2] = [0, 0]; s = 7; return 0; }",
        "module m; fn f(c: bool) -> [i64; 2] { if c { return [1, 2]; } else { } }",
        "module m; record P { x: i64 } fn f() -> P { return [1, 2]; }",
        "module m; fn f() -> i64 { let x: i64 = (1, 2); return zzz; }",
        "module m; enum E { A, B } fn f(c: bool) -> E { if c { return E::A; } else { return [1, 2]; } }",
        "module m; record P { x: i64 } enum E { A } fn f() -> i64 { let e: E = E::A; return (1, 2); }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5i adversarial neg #{i} has no core oracle code (mislabeled):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5i adversarial neg #{i}: SIGIL diagnostic codes must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-5j: composite call-return typing + ref-param T071. A composite-returning
// call emits the composite call-node record (so the 5i value checks + later refs
// see the real type); a composite (e.g. &P) param vs a non-composite arg trips
// T071 (XOR). ET-J2: a record-returning call stays tag 9 (not 901). Composite-vs-
// composite (ref-mutability, tuple-arity arg) deferred (AG-J1).
// ===========================================================================

#[test]
fn pr5j_composite_call_and_refparam() {
    // POSITIVES — oracle accepts; SIGIL stream + codes must match byte-for-byte.
    let pos: &[&str] = &[
        // composite call-return used at the SAME composite type (the call node is
        // emitted as the tuple, matching the oracle):
        "module m; fn mk() -> (i64, u32) { return (1, 2); } fn f() -> i64 { let t: (i64, u32) = mk(); return 0; }",
        "module m; fn mk() -> (i64, u32) { return (1, 2); } fn f() -> (i64, u32) { return mk(); }",
        "module m; fn mk() -> [i64; 3] { return [1, 2, 3]; } fn f() -> i64 { let a: [i64; 3] = mk(); return 0; }",
        // ET-J2 canary: a RECORD-returning call must emit tag 9 + name, NOT tag 901.
        "module m; record P { x: i64 } fn mk() -> P { return P { x: 1 }; } fn f() -> i64 { let p: P = mk(); return p.x; }",
        // ref arg matches ref param — clean (composite-vs-composite, deferred):
        "module m; record P { x: i64 } fn g(r: &P) -> i64 { return 0; } fn f(p: P) -> i64 { return g(&p); }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-5j pos #{i}: SIGIL stream must match the oracle:
{src}"
        );
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5j pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-5j pos #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
    // NEGATIVES — composite call-result in a scalar context (5i check fires via the
    // now-composite call record) + ref-param T071, at exact code parity.
    let neg: &[&str] = &[
        "module m; fn mk() -> (i64, u32) { return (1, 2); } fn f() -> i64 { let x: i64 = mk(); return x; }",
        "module m; record P { x: i64 } fn g(r: &P) -> i64 { return 0; } fn f() -> i64 { return g(5); }",
        "module m; record P { x: i64 } fn g(r: &P) -> i64 { return 0; } fn f(p: P) -> i64 { return g(p); }",
    ];
    for (i, src) in neg.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5j neg #{i} has no core oracle code:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5j neg #{i}: SIGIL codes must match the oracle:
{src}"
        );
    }
}

#[test]
fn pr5j_adversarial_pos_match_oracle() {
    // Workflow-generated, oracle-vetted COMPOSITE-CALL / REF-PARAM positives (18) the
    // checker must NOT over-reject: composite call-return used at the SAME composite
    // type (tuple/array/record) in lets/returns/chained-args, recursive composite-
    // returning calls, matching ref / mut-ref args (composite-vs-composite, no T071),
    // multi-arg ref-vs-ref, and the AG-J1 ref-mutability mismatch (silent on BOTH
    // oracle and SIGIL). Each stays clean at exact record + diagnostic parity.
    let fixtures: &[&str] = &[
        "module m; fn mk() -> (i64, u32) { return (1, 2); } fn f() -> (i64, u32) { let t: (i64, u32) = mk(); return t; }",
        "module m; fn mk() -> (i64, bool, str) { return (1, true, \"a\"); } fn f() -> (i64, bool, str) { return mk(); }",
        "module m; fn mk() -> [i64; 4] { return [1, 2, 3, 4]; } fn f() -> [i64; 4] { let a: [i64; 4] = mk(); return a; }",
        "module m; record P { x: i64 } fn mk() -> P { return P { x: 7 }; } fn f() -> i64 { let p: P = mk(); return p.x; }",
        "module m; record P { x: i64 } fn g(r: &mut P) -> i64 { return 0; } fn f(p: P) -> i64 { let mut q: P = p; return g(&mut q); }",
        "module m; fn mk() -> (i64, u32) { return (1, 2); } fn sink(t: (i64, u32)) -> i64 { return 0; } fn f() -> i64 { return sink(mk()); }",
        "module m; fn mk() -> [i64; 2] { return [1, 2]; } fn sink(a: [i64; 2]) -> i64 { return 0; } fn f() -> i64 { return sink(mk()); }",
        "module m; record P { x: i64 } fn g(a: &P, b: &P) -> i64 { return 0; } fn f(p: P) -> i64 { return g(&p, &p); }",
        "module m; record P { x: i64 } fn g(r: &mut P) -> i64 { return 0; } fn f(p: P) -> i64 { return g(&p); }",
        "module m; record P { x: i64 } fn g(r: &P, n: i64) -> i64 { return 0; } fn f(p: P) -> i64 { return g(&p, 5); }",
        "module m; record P{x:i64} fn mk()->P{return P{x:1};} fn f()->P{let p:P=mk(); return p;}",
        "module m; record P{x:i64} fn mk()->P{return P{x:1};} fn use1(p:P)->i64{return 0;} fn f()->i64{return use1(mk());}",
        "module m; fn mk()->(i64,u32){return mk();} fn f()->(i64,u32){return mk();}",
        "module m; fn mk()->[i64;3]{return mk();} fn f()->[i64;3]{return mk();}",
        "module m; fn a()->(i64,u32){return a();} fn b()->(i64,u32){return a();} fn c()->(i64,u32){let t:(i64,u32)=b(); return t;}",
        "module m; fn mk()->(i64,u32){return mk();} fn relay()->(i64,u32){let t:(i64,u32)=mk(); return t;} fn f()->(i64,u32){let u:(i64,u32)=relay(); return u;}",
        "module m; fn mk()->(i64,u32){return mk();} fn use1(t:(i64,u32))->i64{return 0;} fn f()->i64{return use1(mk());}",
        "module m; record P{x:i64} fn g(r:&P)->i64{return 0;} fn f(p:P)->i64{let mut q:P=p; return g(&mut q);}",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-5j adversarial pos #{i}: SIGIL stream must match the oracle:
{src}"
        );
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-5j adversarial pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-5j adversarial pos #{i} produced a spurious SIGIL diagnostic (FALSE_REJECT):
{src}"
        );
    }
}

#[test]
fn pr5j_adversarial_neg_codes_match_oracle() {
    // Workflow-generated, oracle-vetted composite-CALL / REF-PARAM mismatches (21): a
    // composite call result in a scalar let/return/assign (T041/T049/T045 via the now-
    // composite call record), and a composite param (&P / &mut P / tuple / array) vs a
    // non-composite arg (scalar literal, bool, str, record VALUE) tripping T071 — incl.
    // the second-slot/in-range index path, T070+T071 / T049+T071 / T041+T071 co-fire,
    // and a composite-returning call fed into a SCALAR param. Each at exact code parity.
    // (Drops, out of PR-5j scope: composite-in-binop / -condition (AG-J2), composite-vs-
    // composite wrong-arity arg (AG-V1) — all bounded false-ACCEPTs, never false-rejects.)
    let fixtures: &[&str] = &[
        "module m; fn mk() -> (i64, u32) { return (1, 2); } fn f() -> i64 { return mk(); }",
        "module m; fn mk() -> (i64, u32) { return (1, 2); } fn f() -> i64 { let mut x: i64 = 0; x = mk(); return x; }",
        "module m; fn mk() -> [i64; 3] { return [1, 2, 3]; } fn f() -> bool { return mk(); }",
        "module m; fn mk() -> (i64, u32) { return (1, 2); } fn f() -> str { let s: str = mk(); return s; }",
        "module m; fn g(t: (i64, u32)) -> i64 { return 0; } fn f() -> i64 { return g(9); }",
        "module m; fn g(a: [i64; 2]) -> i64 { return 0; } fn f() -> i64 { return g(7); }",
        "module m; record P { x: i64 } fn g(r: &mut P) -> i64 { return 0; } fn f(p: P) -> i64 { return g(p); }",
        "module m; record P { x: i64 } fn g(r: &mut P) -> i64 { return 0; } fn f() -> i64 { return g(7); }",
        "module m; record P { x: i64 } fn g(r: &P) -> i64 { return 0; } fn f() -> i64 { return g(true); }",
        "module m; fn g(t: (i64, bool)) -> i64 { return 0; } fn f() -> i64 { return g(\"hi\"); }",
        "module m; fn g(a: [i64; 3]) -> i64 { return 0; } fn f() -> i64 { return g(2); }",
        "module m; record P { x: i64 } fn g(a: &P, b: &P) -> i64 { return 0; } fn f(p: P) -> i64 { return g(&p, 5); }",
        "module m; record P { x: i64 } fn g(r: &P) -> i64 { return 0; } fn f() -> i64 { return g(5, 6); }",
        "module m; fn g(t: (i64, u32)) -> i64 { return 0; } fn f() -> str { return g(4); }",
        "module m; record P { x: i64 } fn g(r: &P) -> i64 { return 0; } fn f() -> i64 { let b: bool = g(5); return 0; }",
        "module m; fn mk()->(i64,u32){return mk();} fn f()->i64{let x:i64=mk(); return 0;}",
        "module m; fn mk()->(i64,u32){return mk();} fn f()->i64{let mut x:i64=0; x=mk(); return x;}",
        "module m; record P{x:i64} fn g(r:&mut P)->i64{return 0;} fn f(p:P)->i64{let mut q:P=p; return g(q);}",
        "module m; fn g(t:(i64,u32))->i64{return 0;} fn f()->i64{return g(5);}",
        "module m; fn g(a:[i64;3])->i64{return 0;} fn f()->i64{return g(5);}",
        "module m; fn mk()->(i64,u32){return mk();} fn use1(n:i64)->i64{return 0;} fn f()->i64{return use1(mk());}",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-5j adversarial neg #{i} has no core oracle code (mislabeled):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-5j adversarial neg #{i}: SIGIL diagnostic codes must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-6a: monomorphic trait declaration-time coherence. trait/trait-sig nodes are
// record-free (no TypedFunction); a non-generic impl's methods ARE walked as
// functions (record parity, ET-TR9). validate-impls mirrors validators.rs:92 —
// T248 (trait not in scope, decided FIRST — ET-TR5) / T249 (orphan: impl for a
// non-local type) / T250 (duplicate (trait,type) pair). Call-site bound
// satisfaction (T245/T246) is PR-6b.
// ===========================================================================

#[test]
fn pr6a_decl_coherence() {
    // POSITIVES — oracle accepts; SIGIL record stream + codes must match. These are
    // the accept-twins (ET-TR0) of the T248/T249/T250 rejects: a clean explicit impl
    // of a DECLARED trait for a LOCAL record, plus an inherent impl, both with a
    // NON-TRIVIAL self body (ET-TR9 — exercises `self`-as-binding + impl-body records),
    // and signature-only trait declarations (record-free).
    let pos: &[&str] = &[
        // signature-only traits add NO records (record-free, ET-TR9) — the stream is
        // exactly `f`'s, on both sides. (A function-LESS module is out of scope: the
        // oracle synthesizes a ModuleInit record the corpus never exercises — every
        // fixture, pre-traits too, carries ≥1 function.)
        "module m; trait Marker { } fn f() -> i64 { return 0; }",
        "module m; trait Both { fn hash(self: Self) -> i64; fn eq(self: Self, other: Self) -> bool; } fn f() -> i64 { return 0; }",
        // inherent impl, non-trivial self body — the impl method is walked as a fn.
        "module m; record Point { x: i64, y: i64 } impl Point { fn hash(self: Point) -> i64 { return self.x * 31 + self.y; } }",
        // explicit impl of a declared trait for a local record (accept-twin of T248/T249/T250).
        "module m; trait Hash { fn hash(self: Self) -> i64; } record Point { x: i64, y: i64 } impl Hash for Point { fn hash(self: Point) -> i64 { return self.x * 31 + self.y; } }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-6a pos #{i}: SIGIL record stream must match the oracle:
{src}"
        );
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-6a pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-6a pos #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
    // NEGATIVES — declaration-time coherence rejects, at exact code parity.
    let neg: &[&str] = &[
        // T249 orphan: explicit impl of a declared trait for a primitive.
        "module m; trait Hash { fn hash(self: Self) -> i64; } impl Hash for i64 { fn hash(self: i64) -> i64 { return self; } }",
        // T250 dup: same (trait,type) pair twice.
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } }",
        // T248: impl of an undeclared trait.
        "module m; record P { x: i64 } impl Bogus for P { fn bogus(self: P) -> i64 { return self.x; } }",
        // ET-TR5 precedence canary: both orphan AND undeclared trait → T248 wins.
        "module m; impl Bogus for i64 { fn bogus(self: i64) -> i64 { return self; } }",
    ];
    for (i, src) in neg.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-6a neg #{i} has no core oracle code (mislabeled):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-6a neg #{i}: SIGIL codes must match the oracle:
{src}"
        );
    }
}

#[test]
fn pr6a_adversarial_pos_match_oracle() {
    // Workflow-generated, oracle-vetted CLEAN trait/impl positives (27): explicit impls
    // of declared traits for local records/enums (incl. multi-method traits, str/f64/bool
    // returns, record-returning bodies, multi-field arithmetic, free-fn calls from impl
    // bodies), inherent impls, and the NON-dup boundaries that must NOT trip T250 — two
    // DIFFERENT traits on one type, one trait on two types, an inherent+explicit mix, a 2x2
    // matrix. Each stays clean at exact record + diagnostic parity (impl-method bodies walked
    // as functions, ET-TR9).
    let fixtures: &[&str] = &[
        "module m; trait Scale { fn s(self: Self) -> f64; } record R { v: f64 } impl Scale for R { fn s(self: R) -> f64 { return self.v; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } enum E { A, B } impl Hash for E { fn hash(self: E) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Eq for P { fn eq(self: P, other: P) -> bool { return true; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record A { x: i64 } record B { y: i64 } impl Hash for A { fn hash(self: A) -> i64 { return self.x; } } impl Hash for B { fn hash(self: B) -> i64 { return self.y; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl P { fn raw(self: P) -> i64 { return self.x; } } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } }",
        "module m; trait Both { fn hash(self: Self) -> i64; fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl Both for P { fn hash(self: P) -> i64 { return self.x; } fn eq(self: P, other: P) -> bool { return true; } }",
        "module m; trait Show { fn show(self: Self) -> str; } record P { x: i64 } impl Show for P { fn show(self: P) -> str { return \"p\"; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { a: i64, b: i64, c: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.a + self.b + self.c; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Eq for P { fn eq(self: P, other: P) -> bool { return self.x < other.x; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } record Q { y: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Hash for Q { fn hash(self: Q) -> i64 { return self.y; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64, y: i64 } impl P { fn sum(self: P) -> i64 { return self.x + self.y; } } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } record Q { y: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Eq for P { fn eq(self: P, other: P) -> bool { return true; } } impl Hash for Q { fn hash(self: Q) -> i64 { return self.y; } } impl Eq for Q { fn eq(self: Q, other: Q) -> bool { return false; } }",
        "module m; trait Ord { fn cmp(self: Self, other: Self) -> i64; fn key(self: Self) -> i64; } record P { x: i64, y: i64 } impl Ord for P { fn cmp(self: P, other: P) -> i64 { return self.x; } fn key(self: P) -> i64 { return self.y; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } enum E { A, B(i64) } impl Hash for E { fn hash(self: E) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } record Q { y: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl P { fn dbl(self: P) -> i64 { return self.x + self.x; } } impl Hash for Q { fn hash(self: Q) -> i64 { return self.y; } }",
        "module m; record Point { x: i64, y: i64 } impl Point { fn norm(self: Point) -> i64 { return self.x * self.x + self.y * self.y; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { a: i64, b: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.a * 31 + self.b; } }",
        "module m; record R { x: i64, y: i64 } impl R { fn sum(self: R) -> i64 { return self.x + self.y; } fn diff(self: R) -> i64 { return self.x - self.y; } }",
        "module m; record V { n: i64 } fn dbl(k: i64) -> i64 { return k * 2; } impl V { fn big(self: V) -> i64 { return dbl(self.n); } }",
        "module m; record Acct { bal: i64 } impl Acct { fn solvent(self: Acct) -> bool { return self.bal > 0; } }",
        "module m; record Tag { id: i64 } impl Tag { fn label(self: Tag) -> str { return \"tag\"; } }",
        "module m; record Vec2 { x: i64, y: i64 } impl Vec2 { fn flip(self: Vec2) -> Vec2 { return Vec2 { x: self.y, y: self.x }; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Eq for P { fn eq(self: P, other: P) -> bool { return self.x == other.x; } }",
        "module m; enum Color { Red, Green, Blue } impl Color { fn code(self: Color) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } enum Dir { N, S } impl Hash for Dir { fn hash(self: Dir) -> i64 { return 1; } }",
        "module m; trait Marker { fn m(self: Self) -> i64; } fn f() -> i64 { return 7; } record P { x: i64 } impl Marker for P { fn m(self: P) -> i64 { return self.x; } }",
        "module m; record Pt { x: f64, y: f64 } impl Pt { fn sx(self: Pt) -> f64 { return self.x + self.y; } }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-6a adversarial pos #{i}: SIGIL record stream must match the oracle:
{src}"
        );
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-6a adversarial pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert!(
            sorted_codes(&sigil_codes(src)).is_empty(),
            "PR-6a adversarial pos #{i} produced a spurious SIGIL diagnostic (FALSE_REJECT):
{src}"
        );
    }
}

#[test]
fn pr6a_adversarial_neg_codes_match_oracle() {
    // Workflow-generated, oracle-vetted declaration-time coherence rejects (30): T249
    // orphan on every primitive (i32/u32/u64/f64/bool/str) and on foreign/unknown type names;
    // T248 undeclared-trait (incl. a case-sensitivity boundary `impl hash` vs trait `Hash`);
    // T250 duplicate (trait,type) — twice, three times (multiplicity preserved as a multiset),
    // buried among distinct impls, on records AND enums, with differing bodies; the ET-TR5
    // PRECEDENCE canaries (undeclared-trait-AND-orphan → T248; a repeated orphan/undeclared
    // pair emits the per-impl code TWICE, never T250 — the orphan/scope gate precedes the
    // seen-set); and a mixed {T249,T250} multi-diagnostic. Each at exact code (multiset) parity.
    let fixtures: &[&str] = &[
        "module m; trait Hash { fn hash(self: Self) -> i64; } impl Hash for u32 { fn hash(self: u32) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } impl Hash for u64 { fn hash(self: u64) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } impl Hash for i32 { fn hash(self: i32) -> i64 { return 0; } }",
        "module m; trait Scale { fn s(self: Self) -> f64; } impl Scale for f64 { fn s(self: f64) -> f64 { return self; } }",
        "module m; trait Pred { fn p(self: Self) -> bool; } impl Pred for bool { fn p(self: bool) -> bool { return true; } }",
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } impl Eq for str { fn eq(self: str, other: str) -> bool { return true; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } impl Hash for Widget { fn hash(self: Widget) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl hash for P { fn hash(self: P) -> i64 { return self.x; } }",
        "module m; impl Bogus for Widget { fn bogus(self: Widget) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64, y: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Hash for P { fn hash(self: P) -> i64 { return self.y; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } enum E { A } impl Hash for E { fn hash(self: E) -> i64 { return 0; } } impl Hash for E { fn hash(self: E) -> i64 { return 1; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } record Q { y: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Eq for Q { fn eq(self: Q, other: Q) -> bool { return true; } } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } record Q { y: i64 } record R { z: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Hash for Q { fn hash(self: Q) -> i64 { return self.y; } } impl Hash for R { fn hash(self: R) -> i64 { return self.z; } } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } enum E { A, B } impl Hash for E { fn hash(self: E) -> i64 { return 0; } } impl Hash for E { fn hash(self: E) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } impl Hash for str { fn hash(self: str) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } impl Hash for bool { fn hash(self: bool) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } impl Hash for f64 { fn hash(self: f64) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } impl Hash for Ghost { fn hash(self: Ghost) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } impl Hash for i64 { fn hash(self: i64) -> i64 { return self; } } impl Eq for str { fn eq(self: str, other: str) -> bool { return true; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } impl Hash for i64 { fn hash(self: i64) -> i64 { return self; } } impl Hash for i64 { fn hash(self: i64) -> i64 { return self; } }",
        "module m; record P { x: i64 } impl Bogus for P { fn bogus(self: P) -> i64 { return self.x; } } impl Bogus for P { fn bogus(self: P) -> i64 { return self.x; } }",
        "module m; trait Bogus { fn b(self: Self) -> i64; } record P { x: i64 } impl Bogus for i64 { fn b(self: i64) -> i64 { return self; } }",
        "module m; record P { x: i64 } impl Bogus for i64 { fn b(self: i64) -> i64 { return self; } }",
        "module m; fn f() -> i64 { return 0; } trait Hash { fn hash(self: Self) -> i64; } impl Hash for Foreign { fn hash(self: Foreign) -> i64 { return 0; } }",
        "module m; fn f() -> i64 { return 0; } impl Bogus for Foreign { fn bogus(self: Foreign) -> i64 { return 0; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } enum E { A, B } impl Hash for E { fn hash(self: E) -> i64 { return 0; } } impl Hash for E { fn hash(self: E) -> i64 { return 1; } }",
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl Eq for P { fn eq(self: P, other: P) -> bool { return true; } } impl Eq for P { fn eq(self: P, other: P) -> bool { return false; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl Hash for i64 { fn hash(self: i64) -> i64 { return self; } } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl Hash for P { fn hash(self: P) -> i64 { return 1; } } impl Hash for P { fn hash(self: P) -> i64 { return 2; } } impl Hash for P { fn hash(self: P) -> i64 { return 3; } }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-6a adversarial neg #{i} has no core oracle code (mislabeled):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-6a adversarial neg #{i}: SIGIL diagnostic codes must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-6b: call-site bound satisfaction (the built-in table + structural derive).
// At a concrete generic call, each bounded type-param's arg is checked against its
// bounds → T245 (no impl) / T246 (signature mismatch) / T248 (unknown trait).
// CODES-ONLY parity: every fixture has a generic fn, whose monomorphized instances
// the oracle may emit as extra records (AG-T4, deferred) — so records are not
// compared here, only the core-owned diagnostic SET.
// ===========================================================================

#[test]
fn pr6b_bound_satisfaction() {
    // POSITIVES — oracle accepts; SIGIL must emit NO trait code (the accept-twins of
    // the negatives below). Built-in i64/str/bool satisfy Hash; a record with the
    // method satisfies structurally; composed Hash+Eq; an unbounded generic accepts
    // anything; an UNINSTANTIATED bad bound is not checked (AG-T4).
    let pos: &[&str] = &[
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; return keyed(n); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let s: str = \"hi\"; return keyed(s); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let b: bool = true; return keyed(b); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl P { fn hash(self: P) -> i64 { return self.x; } } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl P { fn hash(self: P) -> i64 { return self.x; } fn eq(self: P, other: P) -> bool { return true; } } fn keyed<T: Hash + Eq>(x: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; record Any { v: i64 } fn idy<T>(x: T) -> i64 { return 0; } fn f() -> i64 { let a: Any = Any { v: 1 }; return idy(a); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record NoH { v: i64 } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { return 0; }",
    ];
    for (i, src) in pos.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            oc.is_empty(),
            "PR-6b pos #{i} unexpectedly rejected by the oracle ({oc:?}):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-6b pos #{i}: SIGIL emitted a spurious trait code (FALSE_REJECT):
{src}"
        );
    }
    // NEGATIVES — bound not satisfied, at exact code parity. T245 (no impl: record
    // missing the method; a non-{i64,str,bool} scalar f64; a bare int literal which the
    // oracle leaves unpinned — ET-TR18), T246 (signature mismatch: wrong return / wrong
    // arity), T248 (undeclared trait in the bound).
    let neg: &[&str] = &[
        "module m; trait Hash { fn hash(self: Self) -> i64; } record NoH { v: i64 } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: NoH = NoH { v: 1 }; return keyed(n); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record Bad { v: i64 } impl Bad { fn hash(self: Bad) -> bool { return true; } } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let b: Bad = Bad { v: 1 }; return keyed(b); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record Bad { v: i64 } impl Bad { fn hash(self: Bad, salt: i64) -> i64 { return self.v + salt; } } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let b: Bad = Bad { v: 1 }; return keyed(b); }",
        "module m; fn keyed<T: Bogus>(x: T) -> i64 { return 0; } fn f() -> i64 { let s: i64 = 5; return keyed(s); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let d: f64 = 1.5; return keyed(d); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { return keyed(5); }",
    ];
    for (i, src) in neg.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-6b neg #{i} has no core oracle code (mislabeled):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-6b neg #{i}: SIGIL codes must match the oracle:
{src}"
        );
    }
}

#[test]
fn pr6b_adversarial_pos_emit_no_codes() {
    // Workflow-generated, oracle-vetted CLEAN bound satisfactions (24): built-in
    // i64/str/bool under Hash AND Eq; bool/str literal args; a USER-redefined `Hash` that
    // an i64/str still satisfies via the NAME-keyed built-in table (ET-TR11); structural
    // records (inherent + explicit impls); composed Hash+Eq; unbounded generics;
    // uninstantiated bad bounds (AG-T4). Each emits NO trait code (codes-only; AG-T4
    // monomorph records). (The former nested-`Ref<T>` bound arg moved to
    // `pr_g1a_uninferrable_return_type_param_fires_t150` — PR-G1a made T150 core, and the
    // oracle cannot infer T through `Ref<T>`, so that fixture is now a T150 parity case.)
    let fixtures: &[&str] = &[
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } fn keyed<T: Eq>(x: T) -> i64 { return 0; } fn f() -> i64 { let s: str = \"x\"; return keyed(s); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let r: i64 = keyed(true); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let r: i64 = keyed(\"x\"); return 0; }",
        "module m; trait Hash { fn hh(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; return keyed(n); }",
        "module m; trait Hash { fn digest(self: Self) -> u64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let s: str = \"x\"; return keyed(s); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } fn keyed<K: Hash + Eq>(x: K) -> i64 { return 0; } fn f() -> i64 { let s: str = \"x\"; return keyed(s); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record R { v: i64 } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl P { fn hash(self: P) -> i64 { return self.x; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; let r: i64 = keyed(p); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(a: i64, x: T) -> i64 { return 0; } fn f() -> i64 { let s: str = \"x\"; return keyed(7, s); }",
        "module m; record R { v: i64 } fn idy<T>(x: T) -> i64 { return 0; } fn f() -> i64 { let a: R = R { v: 1 }; return idy(a); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl P { fn hash(self: P) -> i64 { return self.x; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl Hash for P { fn hash(self: P) -> i64 { return self.x; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait HE { fn eq(self: Self, other: Self) -> bool; fn hash(self: Self) -> i64; } record P { x: i64 } impl P { fn eq(self: P, other: P) -> bool { return true; } fn hash(self: P) -> i64 { return self.x; } } fn keyed<T: HE>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl P { fn hash(self: P) -> i64 { return self.x; } fn eq(self: P, other: P) -> bool { return true; } } fn keyed<K: Hash + Eq>(k: K) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } enum E { A, B } impl E { fn hash(self: E) -> i64 { return 0; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let e: E = E::A; return keyed(e); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { return keyed(true); }",
        "module m; trait Hash { fn weird(self: Self) -> str; } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; return keyed(n); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> bool { return keyed(true) == 0; }",
        "module m; trait Hash { fn poke(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; return keyed(n); }",
        "module m; trait Both { fn hash(self: Self) -> i64; fn eq(self: Self, other: Self) -> bool; } record C { x: i64 } impl C { fn hash(self: C) -> i64 { return self.x; } fn eq(self: C, other: C) -> bool { return true; } } fn keyed<T: Both>(x: T) -> i64 { return 0; } fn f() -> i64 { let c: C = C { x: 1 }; return keyed(c); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn dup<T: Hash>(a: T, b: T) -> i64 { return 0; } fn f() -> bool { let x: i64 = 1; let y: i64 = 2; return dup(x, y) == 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record NoHash { v: i64 } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } enum E { Va, Vb } impl E { fn hash(self: E) -> i64 { return 7; } } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let e: E = E::Va; return keyed(e); }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            oc.is_empty(),
            "PR-6b adversarial pos #{i} unexpectedly rejected by the oracle ({oc:?}):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-6b adversarial pos #{i}: SIGIL emitted a spurious trait code (FALSE_REJECT):
{src}"
        );
    }
}

#[test]
fn pr6b_adversarial_neg_codes_match_oracle() {
    // Workflow-generated, oracle-vetted bound-satisfaction rejects (63): T245
    // (NoImpl) on every non-{i64,str,bool} scalar (f64/u32/u64/i32), the bare-int-literal
    // quirk keyed(5)/keyed(1.5), a primitive under a USER trait, and a record missing a
    // method; T246 (SignatureMismatch) on wrong-return / wrong-arity (too many AND too
    // few) / wrong-param / wrong-self; T248 (undeclared bound); composed bounds where one
    // fails (incl. both-fail → T245 twice as a multiset); the multi-PARAM type-param
    // (`pair<T>(a: T, b: T)`) yielding ONE code; and the SORTED-ORDER missing-vs-wrong-sig
    // edge (ET-TR8). Each at exact code (multiset) parity.
    let fixtures: &[&str] = &[
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let d: f64 = 1.5; let r: i64 = keyed(d); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let u: u32 = 5; let r: i64 = keyed(u); return 0; }",
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } fn keyed<T: Eq>(x: T) -> i64 { return 0; } fn f() -> i64 { let u: u64 = 5; let r: i64 = keyed(u); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let v: i32 = 5; let r: i64 = keyed(v); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let r: i64 = keyed(5); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let r: i64 = keyed(1.5); return 0; }",
        "module m; trait MyTr { fn foo(self: Self) -> i64; } fn keyed<T: MyTr>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; let r: i64 = keyed(n); return 0; }",
        "module m; trait Ord { fn cmp(self: Self, other: Self) -> i64; } fn keyed<T: Ord>(x: T) -> i64 { return 0; } fn f() -> i64 { let s: str = \"x\"; let r: i64 = keyed(s); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } fn keyed<K: Hash + Eq>(x: K) -> i64 { return 0; } fn f() -> i64 { let d: f64 = 1.5; let r: i64 = keyed(d); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Cmp { fn cmp(self: Self, other: Self) -> i64; } fn keyed<K: Hash + Cmp>(x: K) -> i64 { return 0; } fn f() -> i64 { let s: str = \"x\"; let r: i64 = keyed(s); return 0; }",
        "module m; fn keyed<T: Bogus>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; return keyed(n); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record N { v: i64 } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let n: N = N { v: 1 }; let r: i64 = keyed(n); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record B { v: i64 } impl B { fn hash(self: B) -> bool { return true; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let b: B = B { v: 1 }; let r: i64 = keyed(b); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record B { v: i64 } impl B { fn hash(self: B, salt: i64) -> i64 { return self.v; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let b: B = B { v: 1 }; let r: i64 = keyed(b); return 0; }",
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } record B { v: i64 } impl B { fn eq(self: B) -> bool { return true; } } fn keyed<T: Eq>(k: T) -> i64 { return 0; } fn f() -> i64 { let b: B = B { v: 1 }; let r: i64 = keyed(b); return 0; }",
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } record B { v: i64 } impl B { fn eq(self: B, other: i64) -> bool { return true; } } fn keyed<T: Eq>(k: T) -> i64 { return 0; } fn f() -> i64 { let b: B = B { v: 1 }; let r: i64 = keyed(b); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record B { v: i64 } impl B { fn hash(self: i32) -> i64 { return 0; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let b: B = B { v: 1 }; let r: i64 = keyed(b); return 0; }",
        "module m; trait Both { fn hash(self: Self) -> i64; fn eq(self: Self, other: Self) -> bool; } record B { v: i64 } impl B { fn hash(self: B) -> bool { return true; } } fn keyed<T: Both>(k: T) -> i64 { return 0; } fn f() -> i64 { let b: B = B { v: 1 }; let r: i64 = keyed(b); return 0; }",
        "module m; trait Both { fn eq(self: Self, other: Self) -> bool; fn hash(self: Self) -> i64; } record B { v: i64 } impl B { fn eq(self: B, other: B) -> bool { return true; } fn hash(self: B) -> bool { return true; } } fn keyed<T: Both>(k: T) -> i64 { return 0; } fn f() -> i64 { let b: B = B { v: 1 }; let r: i64 = keyed(b); return 0; }",
        "module m; trait Both { fn eq(self: Self, other: Self) -> bool; fn hash(self: Self) -> i64; } record B { v: i64 } impl B { fn hash(self: B) -> i64 { return self.v; } } fn keyed<T: Both>(k: T) -> i64 { return 0; } fn f() -> i64 { let b: B = B { v: 1 }; let r: i64 = keyed(b); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } record B { v: i64 } impl B { fn hash(self: B) -> i64 { return self.v; } } fn keyed<K: Hash + Eq>(x: K) -> i64 { return 0; } fn f() -> i64 { let b: B = B { v: 1 }; let r: i64 = keyed(b); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(a: i64, x: T) -> i64 { return 0; } fn f() -> i64 { let d: f64 = 1.5; let r: i64 = keyed(7, d); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn pair<T: Hash>(a: T, b: T) -> i64 { return 0; } fn f() -> i64 { let x: u32 = 1; let y: u32 = 2; let r: i64 = pair(x, y); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn two<A: Hash, B: Hash>(a: A, b: B) -> i64 { return 0; } fn f() -> i64 { let s: str = \"x\"; let d: f64 = 1.5; let r: i64 = two(s, d); return 0; }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl P { fn hash(self: P) -> bool { return true; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl P { fn hash(self: P) -> i32 { return 0; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl P { fn hash(self: P, salt: i64) -> i64 { return self.x; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl P { fn eq(self: P) -> bool { return true; } } fn keyed<T: Eq>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl P { fn eq(self: P, other: i64) -> bool { return true; } } fn keyed<T: Eq>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } record Q { y: i64 } impl P { fn hash(self: Q) -> i64 { return self.y; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } impl P { fn hashish(self: P) -> i64 { return self.x; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait HE { fn hash(self: Self) -> i64; fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl P { fn hash(self: P) -> bool { return true; } } fn keyed<T: HE>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait HE { fn hash(self: Self) -> i64; fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl P { fn eq(self: P, other: P) -> bool { return true; } fn hash(self: P) -> bool { return true; } } fn keyed<T: HE>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl P { fn hash(self: P) -> i64 { return self.x; } } fn keyed<K: Hash + Eq>(k: K) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } record P { x: i64 } impl P { fn eq(self: P, other: P) -> i64 { return self.x; } } fn keyed<T: Eq>(k: T) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } enum E { A, B } impl E { fn hash(self: E) -> bool { return true; } } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let e: E = E::A; return keyed(e); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } enum E { A, B } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let e: E = E::A; return keyed(e); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record P { x: i64 } fn keyed<A, B: Hash>(a: A, b: B) -> i64 { return 0; } fn f() -> i64 { let p: P = P { x: 1 }; return keyed(7, p); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { return keyed(5); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let n: f64 = 1.5; return keyed(n); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(k: T) -> i64 { return 0; } fn f() -> i64 { let n: i32 = 5; return keyed(n); }",
        "module m; trait MyTr { fn m(self: Self) -> i64; } fn keyed<T: MyTr>(k: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; return keyed(n); }",
        "module m; fn keyed<T: Bogus>(k: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; return keyed(n); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { return keyed(1.5); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let z: i32 = 5; return keyed(z); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let z: u64 = 9; return keyed(z); }",
        "module m; trait MyTr { fn frob(self: Self) -> i64; } fn keyed<T: MyTr>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; return keyed(n); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record Q { x: i64 } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let q: Q = Q { x: 1 }; return keyed(q); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record R { x: i64 } impl R { fn hash(self: R) -> bool { return true; } } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let r: R = R { x: 1 }; return keyed(r); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record S { x: i64 } impl S { fn hash(self: S, salt: i64) -> i64 { return self.x + salt; } } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let s: S = S { x: 1 }; return keyed(s); }",
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } record U { x: i64 } impl U { fn eq(self: U) -> bool { return true; } } fn keyed<T: Eq>(x: T) -> i64 { return 0; } fn f() -> i64 { let u: U = U { x: 1 }; return keyed(u); }",
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } record V { x: i64 } impl V { fn eq(self: V, other: i32) -> bool { return true; } } fn keyed<T: Eq>(x: T) -> i64 { return 0; } fn f() -> i64 { let v: V = V { x: 1 }; return keyed(v); }",
        "module m; trait Eq { fn eq(self: Self, other: Self) -> bool; } record W { x: i64 } impl W { fn eq(self: i64, other: W) -> bool { return true; } } fn keyed<T: Eq>(x: T) -> i64 { return 0; } fn f() -> i64 { let w: W = W { x: 1 }; return keyed(w); }",
        "module m; trait Both { fn hash(self: Self) -> i64; fn eq(self: Self, other: Self) -> bool; } record A { x: i64 } impl A { fn hash(self: A, salt: i64) -> i64 { return self.x + salt; } } fn keyed<T: Both>(x: T) -> i64 { return 0; } fn f() -> i64 { let a: A = A { x: 1 }; return keyed(a); }",
        "module m; trait Both { fn hash(self: Self) -> i64; fn eq(self: Self, other: Self) -> bool; } record B { x: i64 } impl B { fn eq(self: B, other: B) -> bool { return true; } } fn keyed<T: Both>(x: T) -> i64 { return 0; } fn f() -> i64 { let b: B = B { x: 1 }; return keyed(b); }",
        "module m; trait Both { fn hash(self: Self) -> i64; fn eq(self: Self, other: Self) -> bool; } record A { x: i64 } impl A { fn eq(self: A, other: A) -> bool { return true; } fn hash(self: A) -> bool { return true; } } fn keyed<T: Both>(x: T) -> i64 { return 0; } fn f() -> i64 { let a: A = A { x: 1 }; return keyed(a); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } trait Eq { fn eq(self: Self, other: Self) -> bool; } record D { x: i64 } impl D { fn hash(self: D) -> i64 { return self.x; } } fn keyed<K: Hash + Eq>(x: K) -> i64 { return 0; } fn f() -> i64 { let d: D = D { x: 1 }; return keyed(d); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn pair<A, B: Hash>(a: A, b: B) -> i64 { return 0; } fn f() -> i64 { let s: str = \"k\"; let z: f64 = 1.5; return pair(s, z); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn mix<T: Hash>(a: T, b: i64) -> i64 { return 0; } fn f() -> i64 { let z: f64 = 1.5; return mix(z, 7); }",
        "module m; trait Bogus { fn b(self: Self) -> i64; } fn keyed<T: Bogus>(x: T) -> i64 { return 0; } fn f() -> i64 { let s: str = \"k\"; return keyed(s); }",
        "module m; fn keyed<T: Bogus>(x: T) -> i64 { return 0; } fn f() -> i64 { let s: str = \"k\"; return keyed(s); }",
        "module m; trait Hash { fn hash(self: Self) -> i64; } record G<T> { v: T } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let g: G<i64> = G { v: 1 }; return keyed(g); }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-6b adversarial neg #{i} has no core oracle code (mislabeled):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-6b adversarial neg #{i}: SIGIL diagnostic codes must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-G0: the Option-A generics foundation. A generic source fn/record emits NOTHING
// on either side — the oracle's monomorphized INSTANCES are filtered by span (ET-G2),
// and the SIGIL side skips a generic-source body (ET-G2b). Type::Generic (tag 8) is
// never emitted (ET-G4). Inference/substitution + the generic diagnostics are PR-G1+.
// ===========================================================================

#[test]
fn pr_g0_generic_recognition() {
    // A defined-but-uninstantiated generic + a concrete fn: only the concrete fn's
    // records appear, on both sides (generic source skipped). Record + code parity.
    let pos: &[&str] = &[
        "module m; fn id<T>(x: T) -> T { return x; } fn boot() -> i64 { return 0; }",
        "module m; fn pair<A, B>(a: A, b: B) -> A { return a; } fn boot() -> i64 { return 0; }",
        "module m; record Box<T> { v: T } fn boot() -> i64 { return 0; }",
        "module m; fn id<T>(x: T) -> T { return x; } fn dbl(n: i64) -> i64 { return n + n; } fn boot() -> i64 { return dbl(2); }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G0 pos #{i}: SIGIL record stream must match the oracle (generic source skipped):
{src}"
        );
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-G0 pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G0 pos #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

#[test]
fn pr_g0_instance_filter_is_noop_on_monomorphic() {
    // ET-G2: the instance filter fires only when generic_source_spans is non-empty.
    // Every all-monomorphic fixture has NO generic FnDef → the set is empty → the
    // filter is provably a no-op (the prior 67 tests are unaffected).
    for (_, src) in TAG_MANIFEST {
        let source = SourceFile::new("<noop>", *src);
        let (ast, _d) = parser::parse(&source);
        assert!(
            generic_source_spans(&ast).is_empty(),
            "PR-G0 no-op: a monomorphic fixture unexpectedly has a generic FnDef:
{src}"
        );
    }
}

#[test]
fn pr_g0_zero_generic_tag_in_stream() {
    // ET-G4: Type::Generic (tag 8) is NEVER emitted — generic bodies are skipped, and
    // (later) type-params are substituted before emit.
    let fx: &[&str] = &[
        "module m; fn id<T>(x: T) -> T { return x; } fn boot() -> i64 { return 0; }",
        "module m; record Box<T> { v: T } fn boot() -> i64 { return 0; }",
        "module m; fn pair<A, B>(a: A, b: B) -> A { return a; } fn boot() -> i64 { return 0; }",
    ];
    for src in fx {
        assert!(
            !stream_has_tag(&sigil_records(src), 8),
            "SURVIVING_GENERIC (tag 8) in the SIGIL stream:
{src}"
        );
    }
    for (_, src) in TAG_MANIFEST {
        assert!(
            !stream_has_tag(&sigil_records(src), 8),
            "tag 8 in monomorphic stream:
{src}"
        );
    }
}

// ===========================================================================
// PR-G1a: generic FREE functions. A generic call whose return bare-IS a type-param
// substitutes the call-node record from the CONCRETE arg that binds it (ET-G3b); the
// generic source body stays skipped (PR-G0). The substituted use-site type flows into
// the surrounding concrete code (ET-G1, the #1 threat — a checker that ignores generics
// would pass vacuously since both sides skip the body). T150 fires when a return-only
// type-param has no binding arg and no annotation (codes path only — such a program is
// ill-typed, so `check_with_options` panics and it is never a records fixture).
// ===========================================================================

#[test]
fn pr_g1a_concrete_arg_binding_records() {
    // ET-G1 + ET-G5: each generic def is consumed at a CONCRETE type and the result
    // flows into non-skipped concrete code (`let x: i64 = id(n); return x;`). The
    // call-node record must carry the SUBSTITUTED concrete tag, at oracle parity. The
    // dual-concrete fixture (id at i64 AND str) proves the SAME source substitutes two
    // ways. All bindings are CONCRETE-ARG-derived (variables) — never a bare literal
    // (AG-G12). idy<T>(x:T)->i64 covers the concrete-return shape (rettp == -1).
    let pos: &[&str] = &[
        // id<T>(x:T)->T bound by a concrete variable arg.
        "module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: i64 = 5; let x: i64 = id(n); return x; }",
        // ET-G5 dual-concrete: one source → i64 AND str.
        "module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: i64 = 5; let a: i64 = id(n); let s: str = \"hi\"; let b: str = id(s); return a; }",
        // bool binding.
        "module m; fn id<T>(x: T) -> T { return x; } fn f() -> bool { let b: bool = true; let x: bool = id(b); return x; }",
        // id2<T>(a:T,b:T)->T — first-arg binding (multi-occurrence type-param).
        "module m; fn id2<T>(a: T, b: T) -> T { return a; } fn f() -> i64 { let n: i64 = 5; let m: i64 = 6; let x: i64 = id2(n, m); return x; }",
        // concrete-return generic (rettp == -1): the call records the literal return.
        "module m; fn idy<T>(x: T) -> i64 { return 0; } fn f() -> i64 { let s: str = \"hi\"; let x: i64 = idy(s); return x; }",
        // generic call as a bare expr-stmt — arg-derived, no annotation needed.
        "module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: i64 = 5; id(n); return 0; }",
        // nested: the generic result feeds a concrete call's arg position.
        "module m; fn id<T>(x: T) -> T { return x; } fn add(a: i64, b: i64) -> i64 { return a + b; } fn f() -> i64 { let n: i64 = 5; let m: i64 = 6; let x: i64 = add(id(n), id(m)); return x; }",
        // the generic result returned directly (concrete-var binding).
        "module m; fn id<T>(x: T) -> T { return x; } fn f() -> str { let s: str = \"hi\"; return id(s); }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-G1a pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G1a pos #{i}: SIGIL substituted use-site stream must match the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G1a pos #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

#[test]
fn pr_g1a_uninferrable_return_type_param_fires_t150() {
    // ET-G3b: a return-only type-param with no binding arg and no annotation cannot be
    // inferred → T150 on BOTH sides. The generic body's `T`-vs-i64 return is NOT a code
    // (AG-G9: the body is never instantiated). Codes path only — T150 makes the program
    // ill-typed, so this is never a records fixture.
    let neg: &[&str] = &[
        "module m; fn make<T>() -> T { let d: i64 = 0; return d; } fn f() -> i64 { let x = make(); return 0; }",
        // a SECOND, type-param-laden variant: the binding arg is of the WRONG type-param
        // (the return param is return-only), so still no inference path.
        "module m; fn pick<A, B>(a: A) -> B { let d: i64 = 0; return d; } fn f() -> i64 { let n: i64 = 5; let x = pick(n); return 0; }",
        // ET-G6 / AG-G6: a type-param reachable ONLY through a composite param (`Ref<T>`)
        // — the oracle does not unify through the wrapper, so T is uninferrable → T150.
        // (Relocated from pr6b_adversarial_pos_emit_no_codes when T150 became core.)
        "module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: Ref<T>) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; return keyed(&n); }",
    ];
    for (i, src) in neg.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            oc.iter().any(|c| c == "T150"),
            "PR-G1a neg #{i}: oracle no longer emits T150 (got {oc:?}):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G1a neg #{i}: SIGIL must reproduce the oracle's T150 code set:
{src}"
        );
    }
}

// ===========================================================================
// PR-G1a adversarial corpus (workflow-generated, oracle-vetted): the COMPLETE
// ET-G3b call-site inference. 54 survivors fold here; 4 fixtures are EXCLUDED as
// declared anti-goals, each a genuine v1 boundary (the differential pins parity
// only on the in-scope slice):
//   * AG-G12 — a bare-int-LITERAL binding the return type-param in a non-let,
//     non-i64 context (`return snd(0, 9)` into a u32 fn): the oracle keeps the
//     literal IntLit (records i64), SIGIL pins the let/return-expected type.
//   * AG-G6  — a type-param reachable ONLY through an ARRAY param
//     (`idarr<T>(x: [T; 2])`): the oracle unifies T through the array, SIGIL does
//     not do nested inference (fires T150). The Ref<T> twin DOES match (both T150).
//   * AG-G13 — a COMPOSITE arg (tuple) binding a bare type-param (`id(t)`): the
//     oracle records the substituted Tuple, SIGIL records the sentinel (composite-
//     detail substitution is a follow-on).
// ===========================================================================

/// POS: each fixture types CLEANLY on the oracle; the SIGIL substituted use-site
/// record stream AND diagnostics must match at parity. Covers: generic arity is NOT
/// checked (surplus args tolerated); the return type-param bound from a concrete arg,
/// a let-annotation, or the return position (ET-G3b first-arg-ELSE-expected);
/// concrete-arg-preferred-over-literal; multi-type-param return selection; the
/// substituted type flowing into binops / if-conditions / record fields / nested
/// generic calls; and declared-but-uncalled generics staying clean.
#[test]
fn pr_g1a_adversarial_pos_match_oracle() {
    let fixtures: &[&str] = &[
        r#"module m; fn id2<T>(a: T, b: T) -> T { return a; } fn f() -> i64 { let n: u32 = 7; let x: u32 = id2(5, n); return 0; }"#,
        r#"module m; fn id2<T>(a: T, b: T) -> T { return a; } fn f() -> u32 { let n: u32 = 7; return id2(5, n) + n; }"#,
        r#"module m; fn id2<T>(a: T, b: T) -> T { return a; } fn f() -> i64 { let x: u32 = id2(5, 6); return 0; }"#,
        r#"module m; fn snd<T>(a: i64, b: T) -> T { return b; } fn f() -> i64 { let x: u32 = snd(0, 9); return 0; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let x: u32 = id(); return 0; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { return id(); }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: u32 = 5; let s: str = "z"; let x: u32 = id(n, s); return 0; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: u32 = 5; let x: u32 = id(n); return 0; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> f64 { let n: f64 = 1.5; let x: f64 = id(n); return x; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: i64 = 5; let a: i64 = id(n); let u: u32 = 7; let b: u32 = id(u); let s: str = "z"; let c: str = id(s); return a; }"#,
        r#"module m; fn snd<T>(a: i64, b: T) -> T { return b; } fn f() -> i64 { let s: str = "x"; let r: str = snd(0, s); return 0; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: u32 = 5; let m: u32 = 6; let x: u32 = id(id(n)); return 0; }"#,
        r#"module m; fn make<T>() -> T { let d: i64 = 0; return d; } fn f() -> i64 { let x: i64 = make(); return x; }"#,
        r#"module m; fn make<T>() -> T { let d: i64 = 0; return d; } fn f() -> i64 { return make(); }"#,
        r#"module m; fn pick<A, B>(a: A) -> B { let d: i64 = 0; return d; } fn f() -> i64 { let n: i64 = 5; let x: i64 = pick(n); return x; }"#,
        r#"module m; fn mix<A, B>(a: A) -> B { let d: i64 = 0; return d; } fn f() -> i64 { let n: i64 = 5; return mix(n); }"#,
        r#"module m; fn make<T>() -> T { let d: i64 = 0; return d; } fn f() -> i64 { let n: i64 = 5; let x: i64 = make() + n; return x; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: u32 = 5; let m: u32 = 6; let x: u32 = id(n, m); return 0; }"#,
        r#"module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; return keyed(n, n); }"#,
        r#"module m; fn idy<T>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; let x: i64 = idy(n, n); return x; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let x: i64 = id(); return x; }"#,
        r#"module m; fn dup<T>(a: T, b: [T; 2]) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; let a: [i64; 2] = [1, 2]; let x: i64 = dup(n, a); return x; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn add(a: i64, b: i64) -> i64 { return a + b; } fn f() -> i64 { let n: i64 = 5; let m: i64 = 6; let x: i64 = add(id(n), id(m)); return x; }"#,
        r#"module m; fn make<T>() -> T { let d: i64 = 0; return d; } fn g<T>(x: T) -> T { return x; } fn f() -> i64 { return 0; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: i64 = 5; let x: i64 = id(n, n); return x; }"#,
        r#"module m; fn id2<T>(a: T, b: T) -> T { return a; } fn f() -> i64 { let n: i64 = 5; let x: i64 = id2(n, n, n); return x; }"#,
        r#"module m; fn idy<T>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; let x: i64 = idy(n, n); return x; }"#,
        r#"module m; fn idy<T>(x: T) -> i64 { let x: i64 = idy(); return x; } fn boot() -> i64 { return 0; }"#,
        r#"module m; fn id<T>(x: T) -> u32 { return 0; } fn g<T>(x: T) -> T { return x; } fn f() -> u32 { let x: u32 = g(5); return x; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let x: i64 = id(5); return x; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn idc(x: i64) -> i64 { return x; } fn f() -> i64 { let n: i64 = 5; let a: i64 = id(n); let b: i64 = idc(n); return a + b; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: i64 = 5; let x: i64 = id(id(n)); return x; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: i64 = 5; let x: i64 = id(n) + 1; return x; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let b: bool = true; if id(b) { return 1; } else { return 0; } }"#,
        r#"module m; fn id2<T>(a: T, b: T) -> T { return a; } fn f() -> i64 { let n: i64 = 5; let s: str = "x"; let x: i64 = id2(n, s); return x; }"#,
        r#"module m; fn pr<A, B>(a: A, b: B) -> B { return b; } fn f() -> str { let n: i64 = 5; let s: str = "x"; let r: str = pr(n, s); return r; }"#,
        r#"module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> T { return x; } fn f() -> str { let s: str = "hi"; let r: str = keyed(s); return r; }"#,
        // Substituted type (str, from a concrete-str arg) flows into a record field
        // whose declared type MATCHES (str) — a true clean positive on both sides. The
        // field type intentionally agrees with the substituted value: a MISMATCHED
        // field (`x: i64`) is now a correct oracle T071 (record-field value-type check)
        // while SIGIL fail-softs, so that divergent variant lives in the AG-G19
        // value-flow guard `pr_g2b_i_callresult_value_flow_no_false_positive` instead.
        r#"module m; record P { x: str } fn id<T>(x: T) -> T { return x; } fn f() -> P { let s: str = "hi"; return P { x: id(s) }; }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-G1a adversarial pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G1a adversarial pos #{i}: SIGIL substituted stream must match the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G1a adversarial pos #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

/// NEG: each fixture emits at least one core code on the oracle; the SIGIL code SET
/// must match (multiset parity). Covers: the let-annotation binding the variable so
/// `return x` does NOT cascade a spurious T049; the substituted type driving
/// T041/T054/T055; per-param T150 for return-only / bounded / Ref-nested uninferrable
/// type-params; T245 through a generic return; and the non-generic 2-on-1 T070 control.
#[test]
fn pr_g1a_adversarial_neg_codes_match_oracle() {
    let fixtures: &[&str] = &[
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: u32 = 5; let x: i64 = id(n); return x; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: str = "a"; let x: i64 = id(n); return x; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: u32 = 5; let m: i64 = 6; let r: i64 = id(n) + m; return 0; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> bool { let n: u32 = 5; let m: i64 = 6; return id(n) == m; }"#,
        r#"module m; fn idy<T>(x: T) -> i64 { return 0; } fn f() -> i64 { let n: bool = true; let x: u32 = idy(n); return 0; }"#,
        r#"module m; fn two<A, B>(a: A) -> B { let d: i64 = 0; return d; } fn f() -> i64 { let n: i64 = 5; let x = two(n); return 0; }"#,
        r#"module m; trait Hash { fn hash(self: Self) -> i64; } fn two<A, B: Hash>(a: A) -> A { return a; } fn f() -> i64 { let n: i64 = 5; let x: i64 = two(n); return x; }"#,
        r#"module m; fn make<T>() -> T { let d: i64 = 0; return d; } fn f() -> i64 { make(); return 0; }"#,
        r#"module m; fn make2<A, B>() -> A { let d: i64 = 0; return d; } fn f() -> i64 { let x = make2(); return 0; }"#,
        r#"module m; fn idref<T>(x: Ref<T>) -> i64 { return 0; } fn f() -> i64 { let n: i64 = 5; let r: i64 = idref(&n); return r; }"#,
        r#"module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> T { return x; } fn f() -> i64 { let d: f64 = 1.5; let r: f64 = keyed(d); return 0; }"#,
        r#"module m; fn idc(x: i64) -> i64 { return x; } fn f() -> i64 { let n: i64 = 5; let x: i64 = idc(n, n); return x; }"#,
        r#"module m; trait Hash { fn hash(self: Self) -> i64; } fn keyed<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let d: f64 = 1.5; return keyed(d, d); }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: i64 = 5; let x: str = id(n, n); return 0; }"#,
        r#"module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let n: i64 = 5; let x: bool = id(n); return 0; }"#,
        r#"module m; trait Hash { fn hash(self: Self) -> i64; } fn idy<T: Hash>(x: T) -> i64 { return 0; } fn f() -> i64 { let d: f64 = 1.5; let r: i64 = idy(d); return r; }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-G1a adversarial neg #{i}: oracle emits no core code (reclassify as pos):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G1a adversarial neg #{i}: SIGIL code set must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-G2a: generic RECORDS. A generic-record local carries its concrete type-args
// (`let b: Box<i64>`), so a field access whose declared type is a type-param SUBSTITUTES
// to the concrete arg — `b.v` types i64 — the distinctive signal (ET-G10). The construct
// records Named (arg-blind, G0c) and field-init values type against the field's slot.
// T233/T234 (un-annotated / conflicting construction) land in PR-G2a-ii.
// ===========================================================================

#[test]
fn pr_g2a_generic_record_field_substitution() {
    // POS: annotated generic-record locals. The field-access record must carry the
    // SUBSTITUTED concrete type at oracle parity (Box<i64>.v→i64, Box<str>.v→str,
    // Map<i64,str>.k→i64 / .v→str), and a phantom-generic concrete field (Holder.tag)
    // stays i64. Records + codes parity.
    let pos: &[&str] = &[
        "module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; return b.v; }",
        "module m; record Box<T> { v: T } fn f() -> str { let b: Box<str> = Box { v: \"hi\" }; return b.v; }",
        "module m; record Holder<T> { tag: i64 } fn f() -> i64 { let h: Holder<i64> = Holder { tag: 0 }; return h.tag; }",
        "module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p: Pair<i64> = Pair { a: 5, b: 6 }; return p.a; }",
        "module m; record Map<K, V> { k: K, v: V } fn f() -> i64 { let mp: Map<i64, str> = Map { k: 1, v: \"x\" }; return mp.k; }",
        "module m; record Map<K, V> { k: K, v: V } fn f() -> str { let mp: Map<i64, str> = Map { k: 1, v: \"x\" }; return mp.v; }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-G2a pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G2a pos #{i}: SIGIL substituted field-access stream must match the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G2a pos #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

#[test]
fn pr_g2a_substituted_field_participates_in_checks() {
    // NEG: the substituted generic-field type feeds assignment checking — reading
    // Box<i64>.v (i64) into a str binding is a genuine T041 on both sides. Confirms the
    // substitution is not cosmetic: a wrong concrete would mis-match here.
    let src = "module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; let x: str = b.v; return 0; }";
    let oc = sorted_codes(&oracle_codes(src));
    assert!(
        oc.iter().any(|c| c == "T041"),
        "PR-G2a neg: oracle no longer emits T041 (got {oc:?}):
{src}"
    );
    assert_eq!(
        sorted_codes(&sigil_codes(src)),
        oc,
        "PR-G2a neg: SIGIL code set must match the oracle:
{src}"
    );
}

// ===========================================================================
// PR-G2a adversarial corpus (workflow-generated, oracle-vetted). Folds 21 POS + 5 NEG
// survivors. 13 fixtures EXCLUDED as declared boundaries:
//   * Construct-time field-init TYPE CHECK (T071 on `let b: Box<str> = Box { v: 5 }`):
//     the oracle's exact T071 count comes from the inference-vs-annotation conflict, which
//     needs the construction-inference machinery deferred to PR-G2a-ii. PR-G2a-i PINS the
//     field-init to its substituted slot (records parity) but does not yet CHECK it.
//   * Un-annotated generic-record field read (`let b = Box { v: 5 }; b.v`): the type-arg
//     comes from construction inference (PR-G2a-ii), so SIGIL carries no targs and records
//     the field as the sentinel.
//   * A CONCRETE record-typed field on a generic record (`record Box<T> { v: T, w: Inner }`,
//     chained `b.w.n`): record-typed-field resolution is a pre-existing limitation
//     orthogonal to generics (tc_build_recs types only scalar/type-param fields).
// ===========================================================================

/// POS: annotated generic-record locals. The construct's type-param field-inits are PINNED
/// to their substituted slot (`Box<u32> = Box { v: 5 }` types the init `5` as u32), and a
/// field READ substitutes to the concrete arg (`b.v` → u32) — records + codes parity. Sweeps
/// every machine-int / bool / str type-arg, multi-param (Map / Tri), shared type-param
/// (Pair), two generic records side by side, and the read flowing into binops / conditions.
#[test]
fn pr_g2a_adversarial_pos_match_oracle() {
    let fixtures: &[&str] = &[
        r#"module m; record Box<T> { v: T } fn f() -> u32 { let b: Box<u32> = Box { v: 5 }; return b.v; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> i32 { let b: Box<i32> = Box { v: 5 }; return b.v; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> u64 { let b: Box<u64> = Box { v: 5 }; return b.v; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; return b.v; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> str { let b: Box<str> = Box { v: "hi" }; return b.v; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> bool { let b: Box<bool> = Box { v: true }; return b.v; }"#,
        r#"module m; record Map<K, V> { k: K, v: V } fn f() -> u32 { let mp: Map<u32, str> = Map { k: 1, v: "x" }; return mp.k; }"#,
        r#"module m; record Map<K, V> { k: K, v: V } fn f() -> u32 { let mp: Map<i64, u32> = Map { k: 1, v: 2 }; return mp.v; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> u32 { let p: Pair<u32> = Pair { a: 5, b: 6 }; return p.a; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> u32 { let b: Box<u32> = Box { v: 5 }; let x: u32 = b.v; return x; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> u32 { let p: Pair<u32> = Pair { a: 1, b: 2 }; return p.a; }"#,
        r#"module m; record Map<K, V> { k: K, v: V } fn f() -> u32 { let mp: Map<u32, str> = Map { k: 7, v: "x" }; return mp.k; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> u32 { let b: Box<u32> = Box { v: 5 }; let c: u32 = b.v; return c; }"#,
        r#"module m; record Holder<T> { tag: i64 } fn f() -> i64 { let h: Holder<u32> = Holder { tag: 5 }; return h.tag; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> u32 { let b: Box<u32> = Box { v: 1 }; let x: u32 = b.v; return x; }"#,
        r#"module m; record Map<K, V> { k: K, v: V } fn f() -> u64 { let mp: Map<u32, u64> = Map { k: 1, v: 2 }; return mp.v; }"#,
        r#"module m; record Tri<A, B, C> { a: A, b: B, c: C } fn f() -> u32 { let t: Tri<str, u32, bool> = Tri { a: "x", b: 5, c: true }; return t.b; }"#,
        r#"module m; record Box<T> { v: T } record Cell<U> { c: U } fn f() -> u32 { let c: Cell<u32> = Cell { c: 9 }; let b: Box<i64> = Box { v: 5 }; return c.c; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> u32 { let b: Box<u32> = Box { v: 5 }; return b.v + b.v; }"#,
        r#"module m; record P { x: i64 } record Box<T> { v: T } fn f(p: P) -> i64 { let b: Box<i64> = Box { v: 5 }; return p.x + b.v; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<bool> = Box { v: true }; if b.v { return 1; } else { return 0; } }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-G2a adversarial pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G2a adversarial pos #{i}: SIGIL field-init pin + field-read substitution must match the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G2a adversarial pos #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

/// NEG: the substituted field READ participates in checks at parity — reading an i64-slot
/// field into a str let (T041) / str return (T049) / str call-arg (T071), comparing a
/// str-slot field against an int (T055), and an unknown field (T120). Code-set parity.
#[test]
fn pr_g2a_adversarial_neg_codes_match_oracle() {
    let fixtures: &[&str] = &[
        r#"module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; let x: str = b.v; return 0; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> str { let b: Box<i64> = Box { v: 5 }; return b.v; }"#,
        r#"module m; record Box<T> { v: T } fn g(x: str) -> i64 { return 0; } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; let r: i64 = g(b.v); return r; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; let x: i64 = b.w; return x; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> bool { let b: Box<str> = Box { v: "a" }; return b.v == 1; }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-G2a adversarial neg #{i}: oracle emits no core code (reclassify as pos):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G2a adversarial neg #{i}: SIGIL code set must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-G2a-ii: generic-record CONSTRUCTION INFERENCE. An UN-ANNOTATED generic-record local
// infers its type-args from the field values, so a later field read substitutes; a
// type-param bound by NO field cannot be inferred → T233. (T234 conflict + the construct-
// time field-init T071 check carry the IntLit-flex modelling and are PR-G2a-iii.)
// ===========================================================================

#[test]
fn pr_g2a_ii_unannotated_record_inference() {
    // POS: `let b = Box { v: <lit> }` (no annotation) infers T from the field value, so
    // `b.v` substitutes to that concrete — records + codes parity across i64/str/bool, and
    // a field bound from a concrete variable.
    let pos: &[&str] = &[
        "module m; record Box<T> { v: T } fn f() -> i64 { let b = Box { v: 5 }; return b.v; }",
        "module m; record Box<T> { v: T } fn f() -> str { let b = Box { v: \"hi\" }; return b.v; }",
        "module m; record Box<T> { v: T } fn f() -> bool { let b = Box { v: true }; return b.v; }",
        "module m; record Box<T> { v: T } fn f() -> u32 { let n: u32 = 7; let b = Box { v: n }; return b.v; }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-G2a-ii pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G2a-ii pos #{i}: SIGIL un-annotated inference stream must match the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G2a-ii pos #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

#[test]
fn pr_g2a_ii_t233_and_inferred_read_codes() {
    // NEG: a phantom type-param (bound by no field) un-annotated → T233; and an inferred
    // un-annotated read participates in checks (`let b = Box { v: 5 }; let x: str = b.v;`
    // → T041 because the inferred i64 read mismatches the str let). Code-set parity.
    let neg: &[(&str, &str)] = &[
        (
            "T233",
            "module m; record Holder<T> { tag: i64 } fn f() -> i64 { let h = Holder { tag: 0 }; return h.tag; }",
        ),
        (
            "T041",
            "module m; record Box<T> { v: T } fn f() -> i64 { let b = Box { v: 5 }; let x: str = b.v; return 0; }",
        ),
    ];
    for (code, src) in neg {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            oc.iter().any(|c| c == code),
            "PR-G2a-ii neg: oracle no longer emits {code} (got {oc:?}):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G2a-ii neg: SIGIL code set must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-G2a-ii adversarial corpus (workflow-generated, oracle-vetted). Folds 9 POS +
// 7 NEG survivors. The excluded fixtures are declared boundaries, all IntLit-flex or
// deferred-inference, none a silent gap:
//   * IntLit-flex through a generic-record field (`let b = Box { v: 5 }; let x: u32 = b.v`):
//     the oracle keeps the boxed int literal POLYMORPHIC so the read pins to its context;
//     SIGIL freezes the un-annotated int-literal field to i64, so a NON-i64-context read
//     diverges (AG-G12, the IntLit-flex boundary — concrete-field bindings DO win, so
//     `Pair { a: 5, b: u32var }` is at parity).
//   * A field value that is a CALL / nested CONSTRUCT / composite (tuple/array) variable:
//     the lightweight inference handles only literals + bare variables, so it leaves the
//     type-param unbound (a spurious T233) — a declared lightweight-inference limit.
//   * T234 (conflicting CONCRETE field inferences) and the construct-time field-init T071
//     check: PR-G2a-iii (they carry the IntLit-flex conflict modelling).
// ===========================================================================

/// POS: un-annotated generic-record inference where the type-arg is a DEFINITE concrete —
/// a str/bool field, a concrete-variable field, a concrete-beats-int-lit mixed binding
/// (`Pair { a: 5, b: u }` → u32), a mixed concrete+type-param record, an inferred Box
/// beside an annotated Box, dual-int-lit defaulting to i64, and a non-generic regression.
#[test]
fn pr_g2a_ii_adversarial_pos_match_oracle() {
    let fixtures: &[&str] = &[
        r#"module m; record Box<T> { v: T } fn f() -> u32 { let n: u32 = 7; let b = Box { v: n }; return b.v; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> u32 { let u: u32 = 7; let p = Pair { a: 5, b: u }; let x: u32 = p.a; return x; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> u32 { let u: u32 = 1; let p = Pair { b: 5, a: u }; return p.a; }"#,
        r#"module m; record H<T> { tag: i64 } fn f() -> i64 { let h: H<i64> = H { tag: 0 }; return h.tag; }"#,
        r#"module m; record M<T> { tag: i64, v: T } fn f() -> i64 { let m = M { tag: 1, v: 7 }; return m.v + m.tag; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> i64 { let a = Box { v: 5 }; let c: Box<i64> = Box { v: 9 }; return a.v + c.v; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> u32 { let u: u32 = 1; let p = Pair { a: u, b: u }; return p.a; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p = Pair { a: 5, b: 6 }; return p.a + p.b; }"#,
        r#"module m; record P { a: i64, b: i64 } fn f() -> i64 { let p = P { a: 1, b: 2 }; return p.a; }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-G2a-ii adversarial pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G2a-ii adversarial pos #{i}: SIGIL inference stream must match the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G2a-ii adversarial pos #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

/// NEG: T233 per unbound type-param (one- and two-phantom records, keyed on WHICH param),
/// an int-lit-into-str field (T041), and the inferred read participating in checks
/// (T049 return / T071 call-arg). Code-set parity.
#[test]
fn pr_g2a_ii_adversarial_neg_codes_match_oracle() {
    let fixtures: &[&str] = &[
        r#"module m; record Box<T> { v: T } fn f() -> i64 { let b = Box { v: 5 }; let x: str = b.v; return 0; }"#,
        r#"module m; record Holder<T> { tag: i64 } fn f() -> i64 { let h = Holder { tag: 0 }; return h.tag; }"#,
        r#"module m; record H<T, U> { tag: i64 } fn f() -> i64 { let h = H { tag: 0 }; return h.tag; }"#,
        r#"module m; record P<A, B> { x: i64 } fn f() -> i64 { let p = P { x: 0 }; return p.x; }"#,
        r#"module m; record H<T, U> { v: U } fn f() -> i64 { let h = H { v: 5 }; return h.v; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> str { let b = Box { v: 5 }; return b.v; }"#,
        r#"module m; record Box<T> { v: T } fn g(x: str) -> i64 { return 0; } fn f() -> i64 { let b = Box { v: 5 }; let r: i64 = g(b.v); return r; }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-G2a-ii adversarial neg #{i}: oracle emits no core code (reclassify as pos):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G2a-ii adversarial neg #{i}: SIGIL code set must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-G2a-iii: generic-record construction REJECTS — the IntLit-flex conflict pieces.
// T234 (un-annotated, conflicting field inferences) + the construct-time field-init T071
// (annotated, the dual int-lit-into-non-int + inferred-vs-slot check, count 1-3).
// ===========================================================================

#[test]
fn pr_g2a_iii_construct_field_t071_and_t234() {
    // NEG (code-set parity, incl. multiset count). The annotated construct-mismatch T071
    // count is a DUAL check: an int-lit into a non-int slot fires twice (the literal AND
    // the i64-vs-slot mismatch), a concrete mismatch once. T234 fires once per type-param
    // bound to conflicting concretes (an int-lit cannot flex to a non-int sibling).
    let neg: &[(&str, usize)] = &[
        // construct-time field-init T071 (annotated):
        (
            "module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<str> = Box { v: 5 }; return 0; }",
            2, // int-lit `5` into str slot: literal + i64-vs-str
        ),
        (
            "module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = Box { v: \"x\" }; return 0; }",
            1, // concrete str into i64 slot: one mismatch
        ),
        (
            "module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<bool> = Box { v: 5 }; return 0; }",
            2, // int-lit `5` into bool slot: literal + i64-vs-bool
        ),
        (
            "module m; record Map<K, V> { k: K, v: V } fn f() -> i64 { let mp: Map<i64, str> = Map { k: \"bad\", v: 9 }; return 0; }",
            3, // k: str-vs-i64 (1); v: int-lit `9` into str (2) → 3 total
        ),
        // T234 (un-annotated conflict):
        (
            "module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p = Pair { a: 5, b: \"x\" }; return 0; }",
            1, // int-lit defaults i64, conflicts with str → one T234
        ),
        (
            "module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p = Pair { a: \"x\", b: true }; return 0; }",
            1, // str vs bool → one T234
        ),
    ];
    for (src, n) in neg {
        let oc = sorted_codes(&oracle_codes(src));
        assert_eq!(
            oc.len(),
            *n,
            "PR-G2a-iii: expected {n} core codes from the oracle, got {oc:?}:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G2a-iii: SIGIL code multiset must match the oracle:
{src}"
        );
    }
    // POS (must NOT fire): int-lit flexes to an int concrete / sibling int-lit, and a clean
    // annotated construct stays clean.
    let pos: &[&str] = &[
        "module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let n: u32 = 7; let p = Pair { a: 5, b: n }; return 0; }",
        "module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p = Pair { a: 5, b: 6 }; return p.a; }",
        "module m; record Box<T> { v: T } fn f() -> u32 { let b: Box<u32> = Box { v: 5 }; return b.v; }",
    ];
    for src in pos {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-G2a-iii pos: oracle unexpectedly rejected:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G2a-iii pos: SIGIL must stay clean at parity:
{src}"
        );
    }
}

// ===========================================================================
// PR-G2a-iii adversarial corpus (workflow-generated, oracle-vetted). Folds 8 POS + 30
// NEG survivors. The NEG set heavily anchors the diagnostic COUNT (a multiset): the
// construct-time T071 DUAL check (int-lit-into-non-int slot fires twice, a concrete
// mismatch once; multi-param totals 1-6), T234 once per conflicting type-param, and the
// CASCADE SUPPRESSION (a conflicted construct emits ONLY T234/T233, no downstream T049/T041
// — the conflicting slot resolves to the error sentinel). 7 fixtures EXCLUDED as AG-G12:
// the IntLit-flex READ of a mixed int-lit + concrete record (`Pair { a: 5, b: u }; return
// p.a` in an i64 fn) — concrete-first infers T=u32 so the read is u32, but the oracle keeps
// the int-lit-originated field polymorphic and flexes it to the i64 read context.
// ===========================================================================

/// POS: clean constructions at parity — int-lit flexing into an annotated machine-int slot,
/// dual-int-lit defaulting to i64, concrete-beats-int-lit read in the MATCHING context,
/// distinct-per-param records (no false T234), and the shipped read/write/inference paths.
#[test]
fn pr_g2a_iii_adversarial_pos_match_oracle() {
    let fixtures: &[&str] = &[
        r#"module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<u32> = Box { v: 5 }; return 0; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p = Pair { a: 5, b: 6 }; return p.a; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let u: u32 = 1; let p = Pair { a: u, b: 5 }; return 0; }"#,
        r#"module m; record Trip<A, B, C> { a: A, b: B, c: C } fn f() -> i64 { let t = Trip { a: 1, b: "x", c: true }; return 0; }"#,
        r#"module m; record Box<T> { v: T } fn g() -> i64 { return 7; } fn f() -> i64 { let b = Box { v: g() }; return 0; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> u32 { let b: Box<u32> = Box { v: 5 }; return b.v; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let u: u32 = 7; let p = Pair { a: 5, b: u }; return 0; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> str { let b = Box { v: "hi" }; return b.v; }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-G2a-iii adversarial pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G2a-iii adversarial pos #{i}: SIGIL stream must match the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G2a-iii adversarial pos #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

/// NEG: construct-time field-init T071 (the dual-count check, single + multi-param), T234
/// (per-conflicting-type-param, incl. int-lit-vs-non-int and two-distinct-concretes), the
/// annotated-conflict-is-T071-not-T234 disjointness, and cascade suppression (a conflicted
/// or phantom construct emits ONLY its T234/T233, no spurious downstream code). MULTISET
/// (count) parity.
#[test]
fn pr_g2a_iii_adversarial_neg_codes_match_oracle() {
    let fixtures: &[&str] = &[
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let x: f64 = 1.0; let p = Pair { a: x, b: 7 }; return p.a; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let s: str = "a"; let bb: bool = true; let p = Pair { a: s, b: bb }; return p.a; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let bb: bool = true; let p = Pair { a: bb, b: 7 }; return p.b; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let s: str = "a"; let p = Pair { a: s, b: 7 }; let y: i64 = p.a; return y; }"#,
        r#"module m; record Trip3<T> { a: T, b: T, c: T } fn f() -> i64 { let s: str = "a"; let p = Trip3 { a: s, b: 7, c: 8 }; return p.a; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p = Pair { a: "x", b: true }; return p.a; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> f64 { let x: f64 = 1.0; let p = Pair { a: x, b: 7 }; return p.a; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<str> = Box { v: 5 }; return 0; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<f64> = Box { v: 5 }; return 0; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = Box { v: "x" }; return 0; }"#,
        r#"module m; record Trip<A, B, C> { a: A, b: B, c: C } fn f() -> i64 { let t: Trip<str, bool, f64> = Trip { a: 1, b: 2, c: 3 }; return 0; }"#,
        r#"module m; record Map<K, V> { k: K, v: V } fn f() -> i64 { let mp: Map<i64, str> = Map { k: "bad", v: 9 }; return 0; }"#,
        r#"module m; record Inner { x: i64 } record Box<T> { v: T } fn f() -> i64 { let b: Box<Inner> = Box { v: 5 }; return 0; }"#,
        r#"module m; record Map<K, V> { k: K, v: V } fn f() -> i64 { let mp: Map<str, bool> = Map { k: 5, v: 9 }; return 0; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let u: u32 = 7; let p = Pair { a: u, b: 5 }; return p.a; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let s: str = "x"; let bb: bool = true; let p = Pair { a: s, b: bb }; return 0; }"#,
        r#"module m; record Two<K,V> { a: K, b: K, c: V, d: V } fn f() -> i64 { let s: str = "x"; let bb: bool = true; let g: f64 = 1.5; let n: u32 = 2; let p = Two { a: s, b: bb, c: g, d: n }; return 0; }"#,
        r#"module m; record Trip<T> { a: T, b: T, c: T } fn f() -> i64 { let s: str = "x"; let bb: bool = true; let g: f64 = 1.5; let p = Trip { a: s, b: bb, c: g }; return 0; }"#,
        r#"module m; record Trip<T> { a: T, b: T, c: T } fn f() -> i64 { let s: str = "x"; let t: str = "y"; let bb: bool = true; let p = Trip { a: s, b: t, c: bb }; return 0; }"#,
        r#"module m; record Trip<T> { a: T, b: T, c: T } fn f() -> i64 { let s: str = "x"; let p = Trip { a: 5, b: s, c: 6 }; return 0; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let g: f64 = 1.5; let p = Pair { a: 5, b: g }; return 0; }"#,
        r#"module m; record Map<K,V> { k: K, v: V } fn f() -> i64 { let m2: Map<i64,str> = Map { k: "bad", v: 9 }; return 0; }"#,
        r#"module m; record Two<T, U> { a: T, b: T } fn f() -> i64 { let p = Two { a: 5, b: "x" } ; return 0; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p: Pair<i64> = Pair { a: 5, b: "x" }; return 0; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p = Pair { a: "x", b: true }; return 0; }"#,
        r#"module m; record Two<T, U> { a: T, b: T } fn f() -> i64 { let p = Two { a: 5, b: "x" }; return 0; }"#,
        r#"module m; record Trio<T> { a: T, b: T, c: T } fn f() -> i64 { let p = Trio { a: 5, b: "x", c: true }; return 0; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let s: str = "x"; let bv: bool = true; let p = Pair { a: s, b: bv }; return 0; }"#,
        r#"module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p = Pair { a: 5, b: 1.5 }; return 0; }"#,
        r#"module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<bool> = Box { v: 5 }; return 0; }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-G2a-iii adversarial neg #{i}: oracle emits no core code (reclassify as pos):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G2a-iii adversarial neg #{i}: SIGIL code multiset must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-G3a: NON-generic method-call typing — the prerequisite the SIGIL checker lacked
// (tc_emit_method returned TC_UNHANDLED for real method calls). A `recv.method(args)` whose
// receiver is a record local types as the impl method's return; the receiver records as
// Named(Record). Generic impl methods (return-type substitution + instance filtering) are
// PR-G3b.
// ===========================================================================

#[test]
fn pr_g3a_nongeneric_method_calls() {
    // POS: record method calls type as the method return, at full record-stream parity
    // (incl. the impl-method body the oracle emits as `Type__method`).
    let pos: &[&str] = &[
        "module m; record P { x: i64 } impl P { fn get(self: P) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.get(); }",
        "module m; record P { x: i64 } impl P { fn lbl(self: P) -> str { return \"hi\"; } } fn f() -> str { let p: P = P { x: 5 }; return p.lbl(); }",
        "module m; record P { x: i64 } impl P { fn ok(self: P) -> bool { return true; } } fn f() -> bool { let p: P = P { x: 5 }; let b: bool = p.ok(); return b; }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-G3a pos #{i} unexpectedly rejected by the oracle:\n{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G3a pos #{i}: SIGIL method-call stream must match the oracle:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G3a pos #{i}: SIGIL diagnostics must match the oracle:\n{src}"
        );
    }
    // NEG: the method-return type participates in checks — an i64 method result into a str
    // let is a genuine T041 on both sides.
    let src = "module m; record P { x: i64 } impl P { fn get(self: P) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; let s: str = p.get(); return 0; }";
    let oc = sorted_codes(&oracle_codes(src));
    assert!(
        oc.iter().any(|c| c == "T041"),
        "PR-G3a neg: oracle no longer emits T041 (got {oc:?}):\n{src}"
    );
    assert_eq!(
        sorted_codes(&sigil_codes(src)),
        oc,
        "PR-G3a neg: SIGIL code set must match:\n{src}"
    );
}

// ===========================================================================
// PR-G3a adversarial corpus (workflow-generated, oracle-vetted). Folds 27 POS + 16 NEG
// survivors. The arg-pin + per-slot T071 check (mirroring free calls) brought the arg
// fixtures to parity. EXCLUDED as documented boundaries: a method-call receiver that is a
// FIELD ACCESS / chained call (`p.q.get()`, `mk().get()` — receiver not a simple local;
// SIGIL records the sentinel), and a NEGATIVE int-literal into an unsigned param
// (`p.add(-1)` into u32 — an out-of-range VALUE check the type-tag checker doesn't do).
// Generic impl methods are PR-G3b.
// ===========================================================================

/// POS: non-generic method calls — return parity across scalars + record returns, the
/// receiver record, multi-method records, same-named methods on distinct records, trait-impl
/// methods, fn-param receivers, and ARG PINNING (a literal arg narrows to its method param's
/// machine-int type; multi-arg and mixed positions).
#[test]
fn pr_g3a_adversarial_pos_match_oracle() {
    let fixtures: &[&str] = &[
        r#"module m; record P { x: i64 } impl P { fn get(self: P) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.get(); }"#,
        r#"module m; record Q { y: i64 } record P { x: i64 } impl P { fn mk(self: P) -> Q { return Q { y: 1 }; } } fn f() -> i64 { let p: P = P { x: 5 }; let q: Q = p.mk(); return q.y; }"#,
        r#"module m; record P { x: i64 } record Q { y: str } impl P { fn get(self: P) -> i64 { return self.x; } } impl Q { fn get(self: Q) -> str { return self.y; } } fn f() -> str { let p: P = P { x: 1 }; let q: Q = Q { y: "h" }; let n: i64 = p.get(); return q.get(); }"#,
        r#"module m; record P { x: i64 } impl P { fn get(self: P) -> i64 { return self.x; } } fn g(p: P) -> i64 { return p.get(); } fn f() -> i64 { let q: P = P { x: 5 }; return g(q); }"#,
        r#"module m; record P { x: i64 } impl P { fn add(self: P, n: u32) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.add(3); }"#,
        r#"module m; record P { x: i64 } impl P { fn add(self: P, n: i32) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.add(9); }"#,
        r#"module m; record P { x: i64 } impl P { fn add(self: P, n: u64) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.add(8); }"#,
        r#"module m; record P { x: i64 } impl P { fn at(self: P, i: u32, j: u32) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.at(1, 2); }"#,
        r#"module m; record P { x: i64 } impl P { fn comb(self: P, a: i64, b: u32) -> i64 { return a; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.comb(1, 2); }"#,
        r#"module m; record P { x: i64 } impl P { fn echo(self: P, n: u32) -> u32 { return n; } } fn f() -> u32 { let p: P = P { x: 5 }; return p.echo(7); }"#,
        r#"module m; record P { x: i64 } impl P { fn add(self: P, n: u32) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.add(2 + 3); }"#,
        r#"module m; record P { x: i64 } impl P { fn get(self: P) -> i64 { return self.x; } fn add(self: P, n: u32) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; let a: i64 = p.get(); return p.add(4); }"#,
        r#"module m; record P { x: i64 } impl P { fn tag(self: P, n: u32) -> str { return "a"; } } fn f() -> str { let p: P = P { x: 5 }; return p.tag(2); }"#,
        r#"module m; trait Add2 { fn add2(self: Self, n: u32) -> i64; } record P { x: i64 } impl Add2 for P { fn add2(self: P, n: u32) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.add2(3); }"#,
        r#"module m; trait Show { fn show(self: Self) -> i64; } record P { x: i64 } impl P { fn bump(self: P, n: u32) -> i64 { return self.x; } } impl Show for P { fn show(self: P) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; let s: i64 = p.show(); return p.bump(6); }"#,
        r#"module m; record P { x: i64 } impl P { fn c(self: P, a: u32, b: i64, d: u32) -> i64 { return b; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.c(1, 2, 3); }"#,
        r#"module m; record P { x: i64 } impl P { fn add(self: P, k: u32) -> u32 { return k; } } fn f() -> u32 { let p: P = P { x: 5 }; return p.add(3); }"#,
        r#"module m; record P { x: i64 } impl P { fn add(self: P, k: i32) -> i32 { return k; } } fn f() -> i32 { let p: P = P { x: 5 }; return p.add(7); }"#,
        r#"module m; record P { x: i64 } impl P { fn add(self: P, k: u64) -> u64 { return k; } } fn f() -> u64 { let p: P = P { x: 5 }; return p.add(9); }"#,
        r#"module m; record P { x: i64 } impl P { fn s(self: P, a: i32, b: i32) -> i32 { return a; } } fn f() -> i32 { let p: P = P { x: 5 }; return p.s(1, 2); }"#,
        r#"module m; record P { x: i64 } impl P { fn s(self: P, a: i32, b: i64) -> i64 { return b; } } fn f() -> i64 { let p: P = P { x: 5 }; let y: i64 = 9; return p.s(1, y); }"#,
        r#"module m; record P { x: i64 } impl P { fn add(self: P, k: i32) -> i32 { return k; } } fn f() -> i32 { let p: P = P { x: 5 }; let r: i32 = p.add(4); return r; }"#,
        r#"module m; record P { x: i64 } impl P { fn add(self: P, k: i32) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.add(8); }"#,
        r#"module m; record P { x: i64 } impl P { fn lbl(self: P, k: i32) -> str { return "hi"; } } fn f() -> str { let p: P = P { x: 5 }; return p.lbl(2); }"#,
        r#"module m; record P { x: i64 } impl P { fn get(self: P) -> i64 { return self.x; } } fn g(n: i64) -> i64 { return n; } fn f() -> i64 { let p: P = P { x: 5 }; let a: i64 = g(p.x); let b: i64 = p.get(); return a; }"#,
        r#"module m; record A { x: i64 } record B { y: i64 } impl A { fn v(self: A) -> i64 { return self.x; } } impl B { fn v(self: B) -> str { return "hi"; } } fn f() -> str { let a: A = A { x: 1 }; let b: B = B { y: 2 }; let n: i64 = a.v(); return b.v(); }"#,
        r#"module m; record P { x: i64 } impl P { fn get(self: P) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; p.get(); return 0; }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert!(
            sorted_codes(&oracle_codes(src)).is_empty(),
            "PR-G3a adversarial pos #{i} unexpectedly rejected by the oracle:
{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G3a adversarial pos #{i}: SIGIL method-call stream must match the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G3a adversarial pos #{i}: SIGIL diagnostics must match the oracle:
{src}"
        );
    }
}

/// NEG: per-slot method-arg T071 (int-lit into a str/bool/f64/record param, single + multi,
/// inherent + trait-impl), and the method RESULT participating in checks (T041 let / T049
/// return / T054 binop / T050 if-cond / T051 while-cond). MULTISET (count) parity.
#[test]
fn pr_g3a_adversarial_neg_codes_match_oracle() {
    let fixtures: &[&str] = &[
        r#"module m; record P { x: i64 } impl P { fn lbl(self: P, s: str) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.lbl(3); }"#,
        r#"module m; record P { x: i64 } impl P { fn d(self: P, v: f64) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.d(3); }"#,
        r#"module m; record P { x: i64 } impl P { fn pick(self: P, b: bool) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.pick(3); }"#,
        r#"module m; record Q { y: i64 } record P { x: i64 } impl P { fn take(self: P, q: Q) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.take(3); }"#,
        r#"module m; record P { x: i64 } impl P { fn mk(self: P, s: str, b: bool) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.mk(1, 2); }"#,
        r#"module m; record P { x: i64 } impl P { fn mk(self: P, a: i64, s: str) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.mk(1, 2); }"#,
        r#"module m; trait Tag { fn tag(self: Self, s: str) -> i64; } record P { x: i64 } impl Tag for P { fn tag(self: P, s: str) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.tag(9); }"#,
        r#"module m; record P { x: i64 } impl P { fn a(self: P) -> i64 { return self.x; } fn pick(self: P, b: bool) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.a() + p.pick(0); }"#,
        r#"module m; record P { x: i64 } impl P { fn lbl(self: P) -> str { return "hi"; } } fn f() -> i64 { let p: P = P { x: 5 }; let n: i64 = p.lbl(); return 0; }"#,
        r#"module m; record P { x: i64 } impl P { fn get(self: P) -> i64 { return self.x; } } fn f() -> str { let p: P = P { x: 5 }; return p.get(); }"#,
        r#"module m; record P { x: i64 } impl P { fn ok(self: P) -> bool { return true; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.ok() + 1; }"#,
        r#"module m; record P { x: i64 } impl P { fn get(self: P) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; if p.get() { return 1; } else { return 0; } }"#,
        r#"module m; record P { x: i64 } impl P { fn get(self: P) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; while p.get() { return 1; } return 0; }"#,
        r#"module m; record P { x: i64 } impl P { fn s(self: P, n: str) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.s(5); }"#,
        r#"module m; record P { x: i64 } impl P { fn b(self: P, n: bool) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.b(5); }"#,
        r#"module m; trait Tag { fn tag(self: Self, n: str) -> i64; } record P { x: i64 } impl Tag for P { fn tag(self: P, n: str) -> i64 { return self.x; } } fn f() -> i64 { let p: P = P { x: 5 }; return p.tag(7); }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-G3a adversarial neg #{i}: oracle emits no core code (reclassify as pos):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G3a adversarial neg #{i}: SIGIL code multiset must match the oracle:
{src}"
        );
    }
}

/// PR-G3b: generic-impl methods. A method of `impl Box<T>` returning a bare
/// type-param (`-> T`) is typed at the CALL site by substituting the receiver's
/// concrete type-arg (indexed by the impl-position, which aligns with the
/// record's slot) — `b.get()` on a `Box<i64>` local is i64, on a `Box<str>` is
/// str (ET-G3b at the method level). The method BODY emits nothing on either side
/// (the oracle emits monomorphized instances reusing the source span; gspans now
/// filters them — ET-G2b). Both the resolved-type record stream AND the (empty)
/// core-code stream must match the oracle.
#[test]
fn pr_g3b_generic_impl_methods_match_oracle() {
    let fixtures: &[&str] = &[
        // M1: `-> T` substituted to i64 at the call; concrete consumer `return b.get();`.
        r#"module m; record Box<T> { v: T } impl Box<T> { fn get(self: Box<T>) -> T { return self.v; } } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; return b.get(); }"#,
        // M2: same generic impl instantiated at str — dual provenance (ET-G5).
        r#"module m; record Box<T> { v: T } impl Box<T> { fn get(self: Box<T>) -> T { return self.v; } } fn f() -> i64 { let b: Box<str> = Box { v: "hi" }; let n: str = b.get(); return 0; }"#,
        // M6: a CONCRETE-return method (`-> i64`) on a generic impl — body still filtered,
        // call typed by the stored concrete return (rettp < 0, no substitution).
        r#"module m; record Box<T> { v: T } impl Box<T> { fn size(self: Box<T>) -> i64 { return 1; } } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; return b.size(); }"#,
        // M-rename: the impl renames the type-param (impl Box<U>) — rettp matches against
        // the IMPL's names (U → pos 0), still indexes the receiver's positional targs.
        r#"module m; record Box<T> { v: T } impl Box<U> { fn get(self: Box<U>) -> U { return self.v; } } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; return b.get(); }"#,
        // M-bool: a third concrete instantiation, result consumed in a bool context.
        r#"module m; record Box<T> { v: T } impl Box<T> { fn get(self: Box<T>) -> T { return self.v; } } fn f() -> bool { let b: Box<bool> = Box { v: true }; return b.get(); }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G3b #{i}: SIGIL generic-impl-method record stream must match the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G3b #{i}: SIGIL core-code stream must match the oracle:
{src}"
        );
    }
}

/// PR-G3b adversarial POS (oracle accepts → records + codes compared). Survivors of
/// the 3-agent hunt, by class:
///  - param-receiver: a generic-record-typed fn PARAM (`fn f(b: Box<i64>)`) used as a
///    method receiver now binds as its record with concrete targs (tc_seed_params),
///    so `b.get()` substitutes and the receiver Named record is emitted. Multi-param
///    (Pair/Triple) substitutes the 2nd/3rd slot; the result also flows through a free
///    call (ET-G1 concrete consumer).
///  - non-int-literal method-arg into a NON-machine-int param: the oracle's method-arg
///    check never flags a str/bool/non-literal-local passed to a `bool`/`str`/composite
///    param (`b.ok("hi")` str→bool, `b.s(k)` i64→str) — only the FREE-call path is strict
///    for those directions. SIGIL matches (record-equal, code-empty). NOTE: the symmetric
///    MACHINE-INT param direction (`b.add(true)` bool→i64, `b.add("no")` str→i64) is NO
///    LONGER silent — it was a soundness hole (clean compile → invalid wasm) that both
///    compilers now reject with T071; those fixtures moved to the NEG test below.
#[test]
fn pr_g3b_adversarial_pos_match_oracle() {
    let fixtures: &[&str] = &[
        // param-receiver — concrete return.
        r#"module m; record Box<T> { v: T } impl Box<T> { fn size(self: Box<T>) -> i64 { return 1; } } fn f(b: Box<i64>) -> i64 { return b.size(); }"#,
        // param-receiver — `-> T` substituted (i64 / str).
        r#"module m; record Box<T> { v: T } impl Box<T> { fn get(self: Box<T>) -> T { return self.v; } } fn f(b: Box<i64>) -> i64 { return b.get(); }"#,
        r#"module m; record Box<T> { v: T } impl Box<T> { fn get(self: Box<T>) -> T { return self.v; } } fn f(b: Box<str>) -> i64 { let n: str = b.get(); return 0; }"#,
        // param-receiver — 2nd / 3rd type-param substitution.
        r#"module m; record Pair<A,B> { x: A, y: B } impl Pair<A,B> { fn snd(self: Pair<A,B>) -> B { return self.y; } } fn f(p: Pair<i64,str>) -> str { return p.snd(); }"#,
        r#"module m; record Triple<A,B,C> { x: A, y: B, z: C } impl Triple<A,B,C> { fn third(self: Triple<A,B,C>) -> C { return self.z; } } fn f(t: Triple<i64,str,bool>) -> bool { return t.third(); }"#,
        // param-receiver — result flows through a free call (ET-G1 consumer).
        r#"module m; record Box<T> { v: T } impl Box<T> { fn get(self: Box<T>) -> T { return self.v; } } fn g(b: Box<i64>) -> i64 { return b.get(); } fn f() -> i64 { let q: Box<i64> = Box { v: 5 }; return g(q); }"#,
        r#"module m; record Box<T> { v: T } impl Box<T> { fn get(self: Box<T>) -> T { return self.v; } } fn g(b: Box<str>) -> str { return b.get(); } fn f() -> str { let q: Box<str> = Box { v: "h" }; return g(q); }"#,
        // non-int-literal method-arg into a NON-machine-int param — oracle silent (only
        // free calls are strict for these directions), SIGIL must not over-fire. The
        // machine-int param direction (`b.add(true)`/`b.add("no")`) is NOW strict and
        // lives in the NEG test.
        r#"module m; record Box<T> { v: T } impl Box<T> { fn ok(self: Box<T>, x: bool) -> i64 { return 0; } } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; return b.ok("hi"); }"#,
        r#"module m; record Box<T> { v: T } impl Box<T> { fn s(self: Box<T>, x: str) -> i64 { return 0; } } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; let k: i64 = 3; return b.s(k); }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G3b adversarial pos #{i}: record stream must match the oracle:
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G3b adversarial pos #{i}: core-code stream must match the oracle:
{src}"
        );
    }
}

/// PR-G3b adversarial NEG (oracle rejects → codes compared). Two reject classes:
///  - type-param method param (`fn set(self: Box<T>, x: T)`): substitutes its expected type
///    from the receiver's targs at the call (tc_build_sigs parmtp + tc_emit_method), so an
///    int-literal arg whose default (i64) mismatches the substituted concrete type fires
///    T071 — matching the oracle's monomorphized-param check. 1st and 2nd type-param positions.
///  - machine-int param + NON-int-literal incompatible arg (`b.add(true)` bool→i64,
///    `p.add(true)` on a non-generic record, `b.add("no")` str→i64): the soundness fix.
///    Previously the method-arg check was int-literal-only so these typed CLEAN and emitted
///    INVALID wasm; both compilers now reject at the arg span (the free-call path always did).
#[test]
fn pr_g3b_adversarial_neg_codes_match_oracle() {
    let fixtures: &[&str] = &[
        r#"module m; record Box<T> { v: T } impl Box<T> { fn set(self: Box<T>, x: T) -> i64 { return 1; } } fn f() -> i64 { let b: Box<str> = Box { v: "x" }; return b.set(5); }"#,
        r#"module m; record Box<T> { v: T } impl Box<T> { fn set(self: Box<T>, x: T) -> i64 { return 1; } } fn f() -> i64 { let b: Box<bool> = Box { v: true }; return b.set(5); }"#,
        r#"module m; record Pair<A,B> { x: A, y: B } impl Pair<A,B> { fn pick(self: Pair<A,B>, k: B) -> B { return k; } } fn f() -> str { let p: Pair<i64,str> = Pair { x: 1, y: "h" }; return p.pick(5); }"#,
        r#"module m; record Pair<A,B> { x: A, y: B } impl Pair<A,B> { fn pick(self: Pair<A,B>, k: B) -> B { return k; } } fn f() -> i64 { let p: Pair<i64,str> = Pair { x: 1, y: "h" }; let s: str = p.pick(5); return 0; }"#,
        r#"module m; record Pair<A,B> { x: A, y: B } impl Pair<A,B> { fn setb(self: Pair<A,B>, y: B) -> i64 { return 1; } } fn f() -> i64 { let p: Pair<i64,str> = Pair { x: 5, y: "h" }; return p.setb(99); }"#,
        // Machine-int param + non-int-literal incompatible arg — the soundness fix (was a
        // clean-compile → invalid-wasm hole; now T071 at the arg in BOTH compilers).
        r#"module m; record Box<T> { v: T } impl Box<T> { fn add(self: Box<T>, x: i64) -> i64 { return 0; } } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; return b.add(true); }"#,
        r#"module m; record P { y: i64 } impl P { fn add(self: P, x: i64) -> i64 { return 0; } } fn f() -> i64 { let p: P = P { y: 5 }; return p.add(true); }"#,
        r#"module m; record Box<T> { v: T } impl Box<T> { fn add(self: Box<T>, x: i64) -> i64 { return x; } } fn f() -> i64 { let b: Box<str> = Box { v: "x" }; return b.add("no"); }"#,
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-G3b adversarial neg #{i}: oracle emits no core code (reclassify as pos):
{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G3b adversarial neg #{i}: SIGIL code multiset must match the oracle:
{src}"
        );
    }
}

// ===========================================================================
// PR-G4: the generics DONE-LINE gate + nested-generic construction + the
// AG-G9 body-code-asymmetry corpus-admission property. Seals the epic: the
// in-scope kinds (generic free fns, generic records, generic-impl methods) at
// call/construct-site inference parity; nested-generic RETURN inference is the
// explicitly-deferred AG-G6 boundary (ET-G6 fail-soft -> TC_UNHANDLED).
// ===========================================================================

/// The oracle's core-code diagnostics WITH spans (code, start, end) — used by the
/// AG-G9 body-asymmetry gate to prove every in-corpus reject fires at a CONCRETE
/// call/construct site, never inside a (record-filtered) generic body.
fn oracle_core_code_spans(src: &str) -> Vec<(String, usize, usize)> {
    let source = SourceFile::new("<tc-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    if pdiags.iter().any(|d| d.severity() == Severity::Error) {
        return Vec::new();
    }
    match name_resolution::resolve(&ast) {
        Err(_) => Vec::new(),
        Ok(resolved) => {
            let (_t, _r, diags) =
                type_check::check_collecting(&resolved, &CompileOptions::default());
            diags
                .iter()
                .filter(|d| d.severity() == Severity::Error)
                .filter(|d| CORE_CODES.contains(&d.code().as_str()))
                .filter_map(|d| {
                    d.span()
                        .map(|s| (d.code().as_str().to_string(), s.start, s.end))
                })
                .collect()
        }
    }
}

/// The generics done-line corpus: representative ACCEPT + REJECT fixtures across
/// every in-scope kind. `true` = accept (records + codes compared); `false` =
/// reject (oracle emits a core code; codes compared).
const GENERICS_CORPUS: &[(bool, &str)] = &[
    // generic free fn — concrete-arg inference + consumer.
    (
        true,
        "module m; fn id<T>(x: T) -> T { return x; } fn f() -> i64 { let x: i64 = id(5); return x + 1; }",
    ),
    // generic free fn — could-not-infer (T150).
    (
        false,
        "module m; fn make<T>() -> T { let d: i64 = 0; return d; } fn f() -> i64 { let x = make(); return 0; }",
    ),
    // generic record — annotated construct + field read.
    (
        true,
        "module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; return b.v; }",
    ),
    // generic record — un-annotated, type-param unbound by fields (T233).
    (
        false,
        "module m; record Holder<T> { tag: i64 } fn f() -> i64 { let h = Holder { tag: 0 }; return h.tag; }",
    ),
    // generic record — conflicting concrete field inferences (T234).
    (
        false,
        "module m; record Pair<T> { a: T, b: T } fn f() -> i64 { let p = Pair { a: 5, b: \"x\" }; return 0; }",
    ),
    // generic-impl method — `-> T` substituted at the call.
    (
        true,
        "module m; record Box<T> { v: T } impl Box<T> { fn get(self: Box<T>) -> T { return self.v; } } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; return b.get(); }",
    ),
    // generic-impl method — param receiver (a generic-record fn param).
    (
        true,
        "module m; record Box<T> { v: T } impl Box<T> { fn size(self: Box<T>) -> i64 { return 1; } } fn f(b: Box<i64>) -> i64 { return b.size(); }",
    ),
    // generic-impl method — type-param param rejects a mismatched int-literal (T071).
    (
        false,
        "module m; record Box<T> { v: T } impl Box<T> { fn set(self: Box<T>, x: T) -> i64 { return 1; } } fn f() -> i64 { let b: Box<str> = Box { v: \"x\" }; return b.set(5); }",
    ),
    // nested-generic CONSTRUCTION — a generic record whose field is another generic record.
    (
        true,
        "module m; record Box<T> { v: T } record Holder<T> { b: Box<T> } fn f() -> i64 { let h: Holder<i64> = Holder { b: Box { v: 5 } }; return 0; }",
    ),
];

/// PR-G4 / ET-G4: NO Type::Generic (tag 8) ever survives into an emitted SIGIL
/// record, across the full generics feature corpus — type-params are substituted
/// (or their generic source body skipped) before any emit.
#[test]
fn pr_g4_zero_generic_tag_full_corpus() {
    for (_, src) in GENERICS_CORPUS {
        assert!(
            !stream_has_tag(&sigil_records(src), 8),
            "PR-G4: surviving Type::Generic (tag 8) in the SIGIL stream:\n{src}"
        );
    }
}

/// PR-G4 / ET-G0 + AG-G9: the body-code-asymmetry corpus-admission gate. The SIGIL
/// side skips generic bodies (records + codes); the oracle's `check_collecting`
/// still surfaces a CALLED generic body's diagnostics. So an admitted generics
/// fixture's every oracle core-code span MUST lie inside a CONCRETE (non-generic)
/// function — never within a generic-source span — else the SIGIL body-skip would
/// silently lose a code. Mechanizes AG-G9 (generic bodies stay CLEAN in-corpus).
#[test]
fn pr_g4_body_code_asymmetry_admission() {
    for (_, src) in GENERICS_CORPUS {
        let source = SourceFile::new("<adm>", *src);
        let (ast, _d) = parser::parse(&source);
        let gspans = generic_source_spans(&ast);
        for (code, start, end) in oracle_core_code_spans(src) {
            let inside = gspans.iter().any(|(gs, ge)| start >= *gs && end <= *ge);
            assert!(
                !inside,
                "PR-G4 AG-G9: oracle code {code} fires INSIDE a generic body span ({start},{end}) \
                 — the SIGIL body-skip would lose it; this fixture is out-of-corpus:\n{src}"
            );
        }
    }
}

/// PR-G4: the done-line differential — every generics-corpus fixture at parity
/// (accept: records + codes; reject: codes, oracle-nonempty). The single gate that
/// proves the in-scope generic surface is sound end-to-end.
#[test]
fn pr_g4_done_line_corpus_parity() {
    for (i, (accept, src)) in GENERICS_CORPUS.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        if *accept {
            assert!(
                oc.is_empty(),
                "PR-G4 done-line #{i}: accept fixture unexpectedly rejected (oracle={oc:?}):\n{src}"
            );
            assert_eq!(
                sorted_recs(&sigil_records(src)),
                sorted_recs(&oracle_records(src)),
                "PR-G4 done-line #{i}: record stream must match the oracle:\n{src}"
            );
        } else {
            assert!(
                !oc.is_empty(),
                "PR-G4 done-line #{i}: reject fixture emits no core code:\n{src}"
            );
        }
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G4 done-line #{i}: SIGIL code stream must match the oracle:\n{src}"
        );
    }
}

/// PR-G4: nested-generic CONSTRUCTION is at parity (a generic record whose field is
/// another generic record / a Vec<T> / Option<T> field), and the AG-G6 nested-RETURN
/// boundary does NOT cascade a stray code. The nested-return CALL itself stays
/// TC_UNHANDLED on the SIGIL side (records diverge → out of the record corpus), but
/// the let binds from its authoritative generic-record annotation, so a downstream
/// field read resolves and no spurious T060 is emitted (codes at parity).
#[test]
fn pr_g4_nested_generics_match_oracle() {
    let pos: &[&str] = &[
        "module m; record Box<T> { v: T } record Holder<T> { b: Box<T> } fn f() -> i64 { let h: Holder<i64> = Holder { b: Box { v: 5 } }; return 0; }",
        "module m; record Bag<T> { items: Vec<T> } fn f() -> i64 { return 0; }",
        "module m; record Maybe<T> { slot: Option<T> } fn f() -> i64 { return 0; }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G4 nested pos #{i}: record stream must match the oracle:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G4 nested pos #{i}: code stream must match the oracle:\n{src}"
        );
    }
    let nested_return = "module m; record Box<T> { v: T } fn mk<T>(x: T) -> Box<T> { return Box { v: x }; } fn f() -> i64 { let b: Box<i64> = mk(5); return b.v; }";
    assert_eq!(
        sorted_codes(&sigil_codes(nested_return)),
        sorted_codes(&oracle_codes(nested_return)),
        "PR-G4 AG-G6: nested-return must not cascade a stray code:\n{nested_return}"
    );
}

/// PR-G4: a GENERIC-NAMED-annotated let (`let b: Box<i64> = …`, `let o: Opt<i64> = …`)
/// now checks the value against the annotation, closing a pre-existing false-ACCEPT
/// class the adversarial pass surfaced. tc_annot_tag returns TC_NO_EXPECT for a
/// type-arg-bearing annotation, so the value escaped the T041/T046 dispatch; SIGIL now
/// mirrors the oracle's resolve_annotated_let_type + type_compatible — an unknown base
/// name → T046, a value that is not the same Named (or the same Named at different
/// type-args, for a copied local) → T041. NEG fixtures, codes compared.
#[test]
fn pr_g4_generic_let_value_check_match_oracle() {
    let fixtures: &[&str] = &[
        // value is a DIFFERENT record / generic record.
        "module m; record Box<T> { v: T } record Other { n: i64 } fn f() -> i64 { let b: Box<i64> = Other { n: 5 }; return 1; }",
        "module m; record Box<T> { v: T } record Pair<A> { a: A } fn f() -> i64 { let b: Box<i64> = Pair { a: 5 }; return 1; }",
        "module m; record Box<T> { v: T } record Sack { s: str } fn f() -> i64 { let b: Box<str> = Sack { s: \"hi\" }; return 1; }",
        // value is a SCALAR (literal or local).
        "module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = 7; return 1; }",
        "module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = true; return 1; }",
        "module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = \"hi\"; return 1; }",
        "module m; record Box<T> { v: T } fn f() -> i64 { let n: i64 = 5; let b: Box<i64> = n; return 1; }",
        // value is an ENUM; or the annotation is a generic ENUM.
        "module m; record Box<T> { v: T } enum E { A, B } fn f() -> i64 { let b: Box<i64> = E::A; return 0; }",
        "module m; record Box<T> { v: T } enum Opt<T> { Some(T), None } fn f() -> i64 { let b: Opt<i64> = 5; return 1; }",
        // same record, DIFFERENT type-args (a copied local) → T041.
        "module m; record Box<T> { v: T } fn f() -> i64 { let a: Box<str> = Box { v: \"x\" }; let b: Box<i64> = a; let x: i64 = b.v; return x; }",
        // mis-bind that ALSO mis-types a downstream field read — must still reject (T041).
        "module m; record Box<T> { v: T } record Other { n: i64 } fn f() -> i64 { let b: Box<i64> = Other { n: 5 }; let x: i64 = b.v; return x; }",
        // annotation names a NONEXISTENT type → T046.
        "module m; fn f() -> i64 { let b: Box<i64> = 5; return 1; }",
        "module m; record Box<T> { v: T } fn f() -> i64 { let nope: Nope<i64> = Box { v: 5 }; return 0; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert!(
            !oc.is_empty(),
            "PR-G4 generic-let-check #{i}: oracle emits no core code (reclassify):\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G4 generic-let-check #{i}: SIGIL code multiset must match the oracle:\n{src}"
        );
    }
}

/// PR-G4: the generic-let value check does NOT over-fire on legitimately-clean
/// generic-record lets (a well-typed construct, a shadow re-let to a different
/// generic record, a deep clean nested construct) — records + codes at parity.
#[test]
fn pr_g4_generic_let_value_check_clean() {
    let fixtures: &[&str] = &[
        "module m; record Box<T> { v: T } fn f() -> i64 { let b: Box<i64> = Box { v: 5 }; let x: i64 = b.v; return x; }",
        "module m; record Box<T> { v: T } record Cell<U> { c: U } fn f() -> u32 { let b: Box<i64> = Box { v: 5 }; let b: Cell<u32> = Cell { c: 7 }; return b.c; }",
        "module m; record Inner<T> { x: T } record Mid<T> { i: Inner<T> } record Outer<T> { m: Mid<T> } fn f() -> i64 { let o: Outer<i64> = Outer { m: Mid { i: Inner { x: 5 } } }; return 0; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G4 generic-let-clean #{i}: SIGIL must stay clean like the oracle:\n{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G4 generic-let-clean #{i}: record stream must match the oracle:\n{src}"
        );
    }
}

/// PR-G2b-i (Gap A): a function returning a generic-Named type at CONCRETE args
/// (`-> Opt<i64>`, `-> Box<str>`) now emits a `9,basename` return record (args
/// dropped, matching the oracle's `type_detail`) instead of TC_UNHANDLED. The
/// `sig.ret` change propagates to call sites — the result flows into a concrete
/// consumer at parity. ET-G15: a generic-SOURCE fn's `-> Box<T>` (type-param arg)
/// keeps TC_UNHANDLED, so the AG-G6 nested-return boundary is unchanged.
#[test]
fn pr_g2b_i_generic_named_return_records_match_oracle() {
    // POS — records + codes parity.
    let pos: &[&str] = &[
        "module m; enum Opt<T> { Some(T), None } fn mk() -> Opt<i64> { return Opt::Some(5); } fn f() -> i64 { return 0; }",
        "module m; record Box<T> { v: T } fn mk2() -> Box<i64> { return Box { v: 5 }; } fn f() -> i64 { return 0; }",
        "module m; record Box<T> { v: T } fn mk3() -> Box<str> { return Box { v: \"x\" }; } fn f() -> i64 { return 0; }",
        // concrete consumer: the returned Box<i64> flows into a let + field read (ET-G1).
        "module m; record Box<T> { v: T } fn mk2() -> Box<i64> { return Box { v: 5 }; } fn f() -> i64 { let b: Box<i64> = mk2(); return b.v; }",
        // enum consumer: the returned Opt<i64> binds a local (payload read is PR-G2b-ii).
        "module m; enum Opt<T> { Some(T), None } fn mk() -> Opt<i64> { return Opt::Some(5); } fn f() -> i64 { let o: Opt<i64> = mk(); return 0; }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G2b-i #{i}: generic-Named return record stream must match the oracle:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G2b-i #{i}: core-code stream must match the oracle:\n{src}"
        );
    }
    // ET-G15 / AG-G6 guard: a generic-SOURCE fn returning `-> Box<T>` keeps the nested
    // call out-of-core (901) — codes clean both sides (records diverge on the nested
    // call by design, so only codes are compared here).
    let nested_source = "module m; record Box<T> { v: T } fn mk<T>(x: T) -> Box<T> { return Box { v: x }; } fn f() -> i64 { let b: Box<i64> = mk(5); return b.v; }";
    assert_eq!(
        sorted_codes(&sigil_codes(nested_source)),
        sorted_codes(&oracle_codes(nested_source)),
        "PR-G2b-i ET-G15: a generic-source nested return must stay code-clean (AG-G6):\n{nested_source}"
    );
}

/// PR-G2b-i / AG-G19: a generic-Named VALUE-FLOW boundary. A generic-Named call
/// result (or cross-fn-passed value) carries no type-args, so a targ-sensitive
/// downstream use diverges from the oracle — BUT only ever as a fail-soft MISS
/// (SIGIL emits a strict SUBSET of the oracle's codes), NEVER a false-positive.
/// This guard pins ET-G19: `sigil_codes ⊆ oracle_codes` for every value-flow
/// fixture. (Full parity for these is the deferred "generic-Named value-flow"
/// follow-on; the corpus admits generic-Named returns only as the bare return
/// record or with an annotated-MATCHING-let consumer.)
#[test]
fn pr_g2b_i_callresult_value_flow_no_false_positive() {
    let fixtures: &[&str] = &[
        // un-annotated let + field read — oracle clean, SIGIL clean (fail-soft 901 record).
        "module m; record Box<T> { v: T } fn mk() -> Box<i64> { return Box { v: 5 }; } fn f() -> i64 { let b = mk(); return b.v; }",
        // mismatched-annotation let — oracle T041, SIGIL silent (miss, no false-positive).
        "module m; record Box<T> { v: T } fn mk() -> Box<i64> { return Box { v: 5 }; } fn f() -> i64 { let b: Box<str> = mk(); return 0; }",
        // generic-Named arg vs param — oracle T071, SIGIL silent.
        "module m; record Box<T> { v: T } fn mk() -> Box<i64> { return Box { v: 5 }; } fn g(x: Box<str>) -> i64 { return 0; } fn f() -> i64 { return g(mk()); }",
        // generic-Named return vs sig — oracle T049, SIGIL silent.
        "module m; record Box<T> { v: T } fn mk() -> Box<i64> { return Box { v: 5 }; } fn g() -> Box<str> { return mk(); } fn f() -> i64 { return 0; }",
        // cross-fn local arg vs param (pre-existing) — oracle T071, SIGIL silent.
        "module m; record Box<T> { v: T } fn g(x: Box<i64>) -> i64 { return 0; } fn f() -> i64 { let a: Box<str> = Box { v: \"x\" }; return g(a); }",
        // generic-CALL result into a record FIELD whose declared type mismatches the
        // substituted value — `id(s): str` into `x: i64`. The oracle's record-field
        // value-type check fires T071; SIGIL records the substituted str but does not
        // yet check the field value against the field type (the record-field half of
        // the deferred value-flow follow-on), so it stays silent. Subset holds.
        "module m; record P { x: i64 } fn id<T>(x: T) -> T { return x; } fn f() -> P { let s: str = \"hi\"; return P { x: id(s) }; }",
    ];
    for (i, src) in fixtures.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        let sc = sorted_codes(&sigil_codes(src));
        for code in &sc {
            assert!(
                oc.contains(code),
                "PR-G2b-i AG-G19 #{i}: SIGIL emitted a FALSE-POSITIVE code {code} not in the oracle {oc:?}:\n{src}"
            );
        }
    }
}

/// PR-G2b-ii (Gap C): a generic-enum match-arm payload binding is substituted from
/// the SCRUTINEE's concrete type-args. `match o { Opt::Some(x) => … }` on an
/// `o: Opt<i64>` binds `x: i64` (was TC_UNHANDLED). The scrutinee's targs come from
/// its annotation or its (generic-record/enum) parameter type; the new `TcRec.vptp`
/// (per-flat-payload type-param index, pushed in lockstep with `vptags` — ET-G16)
/// drives the substitution. ET-G17: an unresolved targ keeps the declared tag (never
/// tag 8). A NON-local scrutinee (`match mk()`) is fail-soft (AG-G17).
#[test]
fn pr_g2b_ii_match_payload_substitution_match_oracle() {
    // POS — records + codes parity.
    let pos: &[&str] = &[
        // local scrutinee, payload read at i64 / str (dual provenance).
        "module m; enum Opt<T> { Some(T), None } fn f() -> i64 { let o: Opt<i64> = Opt::Some(5); match o { Opt::Some(x) => { return x; }, Opt::None => { return 0; } } }",
        "module m; enum Opt<T> { Some(T), None } fn f() -> str { let o: Opt<str> = Opt::Some(\"x\"); match o { Opt::Some(x) => { return x; }, Opt::None => { return \"\"; } } }",
        // param-receiver scrutinee carries targs (PR-G3b generic-param binding).
        "module m; enum Opt<T> { Some(T), None } fn f(o: Opt<i64>) -> i64 { match o { Opt::Some(x) => { return x; }, Opt::None => { return 0; } } }",
        // bool concretization.
        "module m; enum Opt<T> { Some(T), None } fn f() -> bool { let o: Opt<bool> = Opt::Some(true); match o { Opt::Some(x) => { return x; }, Opt::None => { return false; } } }",
        // non-generic enum — must stay unchanged (regression guard).
        "module m; enum E { A(i64), B } fn f() -> i64 { let e: E = E::A(5); match e { E::A(x) => { return x; }, E::B => { return 0; } } }",
        // a generic enum with TWO payload-bearing variants binding the same type-param
        // (exercises the vptp/vptags lockstep indexing across variants — ET-G16).
        "module m; enum Two<T> { L(T), R(T) } fn f() -> i64 { let t: Two<i64> = Two::L(5); match t { Two::L(x) => { return x; }, Two::R(y) => { return y; } } }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G2b-ii #{i}: match-payload record stream must match the oracle:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G2b-ii #{i}: core-code stream must match the oracle:\n{src}"
        );
    }
    // AG-G17 guard: a NON-local scrutinee (call result) carries no targs → the payload
    // binding fail-softs to TC_UNHANDLED (the record diverges, by design), but SIGIL
    // emits no false-positive code (codes clean both sides).
    let nonlocal = "module m; enum Opt<T> { Some(T), None } fn mk() -> Opt<i64> { return Opt::Some(5); } fn f() -> i64 { match mk() { Opt::Some(x) => { return x; }, Opt::None => { return 0; } } }";
    assert_eq!(
        sorted_codes(&sigil_codes(nonlocal)),
        sorted_codes(&oracle_codes(nonlocal)),
        "PR-G2b-ii AG-G17: a non-local match scrutinee must stay code-clean (fail-soft):\n{nonlocal}"
    );
}

/// PR-G2b-iii (Gap B): a generic-ENUM construct under a matching enum annotation
/// (`let o: Opt<i64> = Opt::Some("x")`) now fires T041 when a type-param payload's
/// value mismatches the substituted slot — mirroring the oracle's let-level T041
/// (ET-G18: T041, not T071). Handles both the qualified P_K_METHOD form
/// (`Opt::Some`) and the bare P_K_CALL form (`Some`); an int-literal payload flexes
/// (AG-G12).
#[test]
fn pr_g2b_iii_enum_construct_payload_t041_match_oracle() {
    // NEG — payload mismatch → T041 (codes compared).
    let neg: &[&str] = &[
        "module m; enum Opt<T> { Some(T), None } fn f() -> i64 { let o: Opt<i64> = Opt::Some(\"x\"); return 0; }",
        "module m; enum Opt<T> { Some(T), None } fn f() -> i64 { let o: Opt<str> = Opt::Some(5); return 0; }",
        "module m; enum Opt<T> { Some(T), None } fn f() -> i64 { let o: Opt<bool> = Opt::Some(5); return 0; }",
        // bare construct under annotation.
        "module m; enum Opt<T> { Some(T), None } fn f() -> i64 { let o: Opt<i64> = Some(\"x\"); return 0; }",
        // multi-type-param Either — mismatch on the 1st (A) and 2nd (B) slot.
        "module m; enum Either<A,B> { L(A), R(B) } fn f() -> i64 { let e: Either<i64,str> = Either::L(\"x\"); return 0; }",
        "module m; enum Either<A,B> { L(A), R(B) } fn f() -> i64 { let e: Either<i64,str> = Either::R(5); return 0; }",
        // multi-payload variant: a concrete payload + a mismatched type-param payload.
        "module m; enum E<T> { M(i64, T), N } fn f() -> i64 { let e: E<i64> = E::M(1, \"x\"); return 0; }",
        // payload is a non-literal local that mismatches.
        "module m; enum Opt<T> { Some(T), None } fn f() -> i64 { let s: str = \"h\"; let o: Opt<i64> = Opt::Some(s); return 0; }",
    ];
    for (i, src) in neg.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert_eq!(
            oc,
            vec!["T041".to_string()],
            "PR-G2b-iii Gap B neg #{i}: oracle should be exactly [T041]:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G2b-iii Gap B neg #{i}: SIGIL must match:\n{src}"
        );
    }
    // POS — clean construct + AG-G12 int-lit-flex (records + codes parity).
    let pos: &[&str] = &[
        "module m; enum Opt<T> { Some(T), None } fn f() -> i64 { let o: Opt<i64> = Opt::Some(5); return 0; }",
        "module m; enum Opt<T> { Some(T), None } fn f() -> i64 { let o: Opt<u32> = Opt::Some(5); return 0; }",
        "module m; enum Opt<T> { Some(T), None } fn f() -> str { let o: Opt<str> = Opt::Some(\"h\"); return \"\"; }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G2b-iii Gap B pos #{i} codes:\n{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G2b-iii Gap B pos #{i} records:\n{src}"
        );
    }
}

/// PR-G2b-iii (Gap D, T236): a BARE variant whose name lives in ≥2 in-scope enums,
/// constructed with no disambiguating annotation/qualifier, is ambiguous → T236.
/// An annotation (`let v: A<i64> = Some(5)`) or a qualifier (`A::Some(5)`) suppresses
/// it; a variant unique to one enum never fires it (AG-G18: single-module).
#[test]
fn pr_g2b_iii_t236_ambiguous_bare_variant_match_oracle() {
    // NEG — ambiguous → T236.
    let neg: &[&str] = &[
        "module m; enum A<T> { Some(T), None } enum B<T> { Some(T), None } fn f() -> i64 { let v = Some(5); return 0; }",
        "module m; enum A { S(i64), N } enum B { S(str), N } fn f() -> i64 { let v = S(5); return 0; }",
        // three enums sharing the variant.
        "module m; enum A<T> { Some(T), N } enum B<T> { Some(T), N } enum C<T> { Some(T), N } fn f() -> i64 { let v = Some(5); return 0; }",
        // variant in 2 enums, one generic + one non-generic.
        "module m; enum A<T> { Some(T), N } enum B { Some(i64), N } fn f() -> i64 { let v = Some(5); return 0; }",
    ];
    for (i, src) in neg.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert_eq!(
            oc.len(),
            1,
            "PR-G2b-iii Gap D neg #{i}: oracle should be exactly one code:\n{src}"
        );
        assert_eq!(
            oc[0].split(',').next(),
            Some("T236"),
            "PR-G2b-iii Gap D neg #{i}: oracle code should be T236 (span-agnostic):\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-G2b-iii Gap D neg #{i}: SIGIL must match:\n{src}"
        );
    }
    // POS — disambiguated / unique (records + codes parity).
    let pos: &[&str] = &[
        // unique variant — no T236.
        "module m; enum Opt<T> { Some(T), None } fn f() -> i64 { let v = Some(5); return 0; }",
        // suppressed by annotation.
        "module m; enum A<T> { Some(T), None } enum B<T> { Some(T), None } fn f() -> i64 { let v: A<i64> = Some(5); return 0; }",
        // suppressed by qualifier.
        "module m; enum A<T> { Some(T), None } enum B<T> { Some(T), None } fn f() -> i64 { let v = A::Some(5); return 0; }",
        // suppressed by a NON-generic enum annotation — the bare variant must construct the
        // annotated enum B (not the first enum A with the variant), else a spurious T046.
        "module m; enum A<T> { Some(T), N } enum B { Some(i64), N } fn f() -> i64 { let v: B = Some(5); return 0; }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-G2b-iii Gap D pos #{i} codes:\n{src}"
        );
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-G2b-iii Gap D pos #{i} records:\n{src}"
        );
    }
}

/// PR-E1: optional `else` — a bare `if` (no else branch) type-checks identically on
/// both sides. The Rust parser + the self-hosted parser both synthesize an empty
/// else block, so the per-node type record stream + codes match the oracle. Covers
/// a plain statement-if and an if whose then-branch returns (the else is empty →
/// the fn must still return after, exercising the T044/guaranteed-return path).
#[test]
fn pr_e1_optional_else_match_oracle() {
    // POS — records + codes parity.
    let pos: &[&str] = &[
        "module m; fn f(b: i64) -> i64 { let mut x: i64 = 0; if b == 1 { x = 1; } return x; }",
        "module m; fn f(b: i64) -> i64 { if b == 1 { return 1; } return 0; }",
        // the else-bearing twin — unchanged behavior.
        "module m; fn f(b: i64) -> i64 { let mut x: i64 = 0; if b == 1 { x = 1; } else { x = 2; } return x; }",
        // nested no-else ifs.
        "module m; fn f(a: i64, b: i64) -> i64 { let mut x: i64 = 0; if a == 1 { if b == 1 { x = 1; } } return x; }",
        // no-else if inside a while + an empty then-branch.
        "module m; fn f(n: i64) -> i64 { let mut x: i64 = 0; let mut i: i64 = 0; while i < n { if i == 3 { x = i; } i = i + 1; } return x; }",
        "module m; fn f(b: i64) -> i64 { if b == 1 { } return 0; }",
    ];
    for (i, src) in pos.iter().enumerate() {
        assert_eq!(
            sorted_recs(&sigil_records(src)),
            sorted_recs(&oracle_records(src)),
            "PR-E1 pos #{i}: optional-else record stream must match the oracle:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            sorted_codes(&oracle_codes(src)),
            "PR-E1 pos #{i}: core-code stream must match the oracle:\n{src}"
        );
    }
    // NEG — the empty else is correctly NON-returning: a no-else `if` whose then-branch
    // returns, with nothing after, falls through → T044 (missing return) on both sides.
    let neg: &[&str] = &["module m; fn f(b: i64) -> i64 { if b == 1 { return 1; } }"];
    for (i, src) in neg.iter().enumerate() {
        let oc = sorted_codes(&oracle_codes(src));
        assert_eq!(
            oc,
            vec!["T044".to_string()],
            "PR-E1 neg #{i}: oracle should be [T044]:\n{src}"
        );
        assert_eq!(
            sorted_codes(&sigil_codes(src)),
            oc,
            "PR-E1 neg #{i}: SIGIL must match:\n{src}"
        );
    }
}

// ── HB-2 tc-shadow coverage: intrinsic signatures (T062 restoration, family 1) ──────────────
//
// The certified artifact's stdlib tail calls `store8`/`str_from_raw` from NON-generic fns; the
// shadow had sigs only for the vec-backing trio (alloc/vec_load/vec_store — the B-COMPOSE seed
// in tc_build_sigs), so every such call T062'd and the code had to be gate-filtered. These
// fixtures pin the parity that lets T062 return to the enforced set: the oracle ACCEPTS these
// programs outright (validity asserted on the FULL diagnostic stream, not just core codes — a
// fixture rejected on a non-core code would otherwise pass "" == "" vacuously), and the shadow
// must agree.
#[test]
fn intrinsic_calls_type_on_both_sides() {
    let cases = [
        (
            "alloc + store8 + load8 (globally callable)",
            "#[ring(outer)] module ext;\nfn f() -> i64 ! { Alloc } {\n    let buf: i64 = alloc(8);\n    store8(buf, 65);\n    let b: i64 = load8(buf);\n    return b;\n}\n",
        ),
        (
            "str_from_raw (stdlib-private to module `string` — the fixture uses that module)",
            "#[ring(outer)] module string;\nfn g() -> str ! { Alloc } {\n    let buf: i64 = alloc(1);\n    store8(buf, 65);\n    let s: str = str_from_raw(buf, 1);\n    return s;\n}\n",
        ),
    ];
    for (label, src) in cases {
        // Fixture validity: the ORACLE accepts with zero Error diags of ANY code.
        let source = SourceFile::new("<intrinsic-fixture>", src);
        let (ast, pdiags) = parser::parse(&source);
        assert!(
            !pdiags.iter().any(|d| d.severity() == Severity::Error),
            "{label}: fixture must parse"
        );
        let resolved = name_resolution::resolve(&ast).expect("fixture must resolve");
        let (_typed, _reg, diags) =
            type_check::check_collecting(&resolved, &CompileOptions::default());
        let errs: Vec<String> = diags
            .iter()
            .filter(|d| d.severity() == Severity::Error)
            .map(|d| d.code().as_str().to_string())
            .collect();
        assert!(
            errs.is_empty(),
            "{label}: the oracle must fully accept the fixture, got {errs:?}:\n{src}"
        );
        // Parity: the shadow agrees — no T062, no anything.
        let s = sigil_codes(src);
        assert_eq!(
            s, "",
            "{label}: shadow must accept like the oracle:\n{src}\n{s}"
        );
    }
}

// ── HB-2 tc-shadow coverage: bare unit-variant VALUES (T060 restoration, family 2) ──────────
//
// The certified artifact's option/strings modules use bare `None` in value position; the shadow
// treated any unbound bare name as an undefined local (T060). The oracle resolves a bare
// variant declared by exactly one in-scope enum; locals shadow variants. Fixture validity is
// asserted on the FULL oracle diagnostic stream (as in the intrinsic fixtures above).
#[test]
fn bare_unit_variant_value_types_on_both_sides() {
    let cases = [
        (
            "unique bare variant value",
            "module m;\nenum Color { Red, Green }\nfn f() -> Color {\n    return Red;\n}\n",
        ),
        (
            "local shadows the variant name",
            "module m;\nenum Color { Red, Green }\nfn f() -> i64 {\n    let Red: i64 = 3;\n    return Red;\n}\n",
        ),
    ];
    for (label, src) in cases {
        let source = SourceFile::new("<bare-variant-fixture>", src);
        let (ast, pdiags) = parser::parse(&source);
        assert!(
            !pdiags.iter().any(|d| d.severity() == Severity::Error),
            "{label}: fixture must parse"
        );
        let resolved = name_resolution::resolve(&ast).expect("fixture must resolve");
        let (_typed, _reg, diags) =
            type_check::check_collecting(&resolved, &CompileOptions::default());
        let errs: Vec<String> = diags
            .iter()
            .filter(|d| d.severity() == Severity::Error)
            .map(|d| d.code().as_str().to_string())
            .collect();
        assert!(
            errs.is_empty(),
            "{label}: the oracle must fully accept the fixture, got {errs:?}:\n{src}"
        );
        let s = sigil_codes(src);
        assert_eq!(
            s, "",
            "{label}: shadow must accept like the oracle:\n{src}\n{s}"
        );
    }
}
