//! Deterministic SIGIL emitter for the RS0–RS3 Rust subset. Runs on a program
//! the sound checker (`check::check`) has already accepted, so emission is total
//! and never produces ill-typed SIGIL. Every binary is fully parenthesized; SIGIL
//! requires an `else` on every `if` statement, so an absent `else` emits an empty
//! block. RS3a emits `record`s (construction re-ordered to declaration order); RS3b
//! emits `enum`s, `Name::Variant` construction, and `match` (each bare-expression
//! arm lowered to a braced `{ return <value>; }`); RS3c emits variant payload types,
//! `Name::Variant(args)` construction, and `Name::Variant(x, y)` payload bindings.
//! After building the text a parse self-check (FE500) confirms well-formedness.
//!
//! **The cap-XOR-effect mode split.** Capabilities are inner-ring and effects are
//! outer-ring, and the two cannot mix in one module, so a file is one mode or the
//! other (mixed → FE201):
//!
//! - **cap-mode (RS1, inner ring, no ring attr).** A `#[sigil::cap(Name, deadline
//!   = D)]` becomes a `cap type Name(deadline_ms: i64) {}`, a terminal consumer
//!   `fn __fe_consume_i(c: Name(D)) -> i64 { return 0; }`, a synthetic `__fe_cap_i:
//!   Name(D)` parameter, and a body-top `let __fe_used_i = __fe_consume_j(__fe_cap_i);`
//!   that MOVES the cap (non-decorative; FE011 guards it). Enforced by
//!   `capability::verify` — a stale cap → **T199**.
//! - **effect-mode (RS2, `#[ring(outer)]`).** A `#[sigil::effects(A, B)]` becomes a
//!   sorted row `! { A, B }` on the function (and every function gets a row — an
//!   absent attribute emits `! { }`). Each distinct effect name is co-emitted as an
//!   `effect Name;` decl (the fail-open spine F5: an effect with no decl is
//!   silently unenforced, so co-emission is load-bearing; FE210 backstops it).
//!   Enforced by `effect_check` — a leaked effect → **E001**.
//!
//! The output alphabet is fixed (SC-1): no ambient host operation is constructible.

use std::collections::{BTreeSet, HashMap};

use crate::codes;
use crate::{EmittedSigil, FrontendDiag, SourceMap, parse_emitted_sigil, sanitize_module_name};

use super::parser::{
    BinOp, RsBlock, RsExpr, RsFunction, RsInvRhs, RsPattern, RsProgram, RsStmt, RsTaintSel, UnOp,
};

/// The ` @Label` taint suffix for a targeted parameter, or empty (RS5a, SR-T7 — a
/// non-targeted param emits no suffix). `as_str` is case-exact (SR-T8).
fn param_taint(f: &RsFunction, name: &str) -> String {
    f.taints
        .as_ref()
        .and_then(|t| {
            t.targets
                .iter()
                .find(|(sel, _, _)| matches!(sel, RsTaintSel::Param(n) if n == name))
        })
        .map(|(_, lvl, _)| format!(" @{}", lvl.as_str()))
        .unwrap_or_default()
}

/// The ` @Label` taint suffix for the return type, or empty (RS5a, SR-T7).
fn ret_taint(f: &RsFunction) -> String {
    f.taints
        .as_ref()
        .and_then(|t| {
            t.targets
                .iter()
                .find(|(sel, _, _)| matches!(sel, RsTaintSel::Ret))
        })
        .map(|(_, lvl, _)| format!(" @{}", lvl.as_str()))
        .unwrap_or_default()
}

pub fn emit(program: &RsProgram, source_name: &str) -> Result<EmittedSigil, FrontendDiag> {
    let has_cap = program.functions.iter().any(|f| !f.caps.is_empty());
    let has_effect = program.functions.iter().any(|f| f.effects.is_some());

    // FE201 backstop (the checker rejects this first): cap + effect are exclusive.
    if has_cap && has_effect {
        let span = program
            .functions
            .iter()
            .find(|f| f.effects.is_some())
            .map(|f| f.span.clone())
            .unwrap_or(0..0);
        return Err(FrontendDiag::new(
            codes::FE201_MIXED_MODE,
            "internal: a file mixes `#[sigil::cap]` and `#[sigil::effects]`",
            span,
        ));
    }

    let module = sanitize_module_name(source_name, "rust_module");
    let mut out = String::new();
    if has_effect {
        out.push_str("#[ring(outer)]\n");
    }
    out.push_str(&format!("module {module};\n"));

    // Records (RS3a, ring-agnostic): one per struct, fields in declaration order.
    // An `#[sigil::invariant]` (RS4b) becomes a record `where` clause after the body,
    // enforced at construction by SIGIL's Z3.
    for s in &program.structs {
        let fields: Vec<String> = s
            .fields
            .iter()
            .map(|f| format!("{}: {}", f.name, f.ty.name))
            .collect();
        let where_clause = match &s.invariant {
            Some(inv) => {
                let rhs = match &inv.rhs {
                    RsInvRhs::Literal(v) => v.to_string(),
                    RsInvRhs::Field(f) => f.clone(),
                };
                format!(" where {} {} {}", inv.field, inv.op.as_str(), rhs)
            }
            None => String::new(),
        };
        out.push_str(&format!(
            "record {} {{ {} }}{}\n",
            s.name,
            fields.join(", "),
            where_clause
        ));
    }
    // Enums (RS3b/RS3c, ring-agnostic): one per enum, variants in decl order, each
    // with its positional payload types (`A(i64, bool)`). Construction/patterns are
    // always qualified `Name::Variant`, so a variant name never collides with
    // ambient stdlib variants (Some/None; the T236 case).
    for e in &program.enums {
        let variants: Vec<String> = e
            .variants
            .iter()
            .map(|v| {
                if v.payloads.is_empty() {
                    v.name.clone()
                } else {
                    let tys: Vec<&str> = v.payloads.iter().map(|t| t.name.as_str()).collect();
                    format!("{}({})", v.name, tys.join(", "))
                }
            })
            .collect();
        out.push_str(&format!("enum {} {{ {} }}\n", e.name, variants.join(", ")));
    }
    // Struct field-order map (name → decl-order field names) so construction is
    // emitted in the compiler-required declaration order (a construction stored
    // out of decl order is a known miscompile — see the record-offset invariant).
    let structs: HashMap<&str, Vec<&str>> = program
        .structs
        .iter()
        .map(|s| {
            (
                s.name.as_str(),
                s.fields.iter().map(|f| f.name.as_str()).collect(),
            )
        })
        .collect();

    if has_effect {
        emit_effect_mode(program, &structs, &mut out)?;
    } else {
        emit_cap_mode(program, &structs, &mut out)?;
    }

    // Self-check: emitted SIGIL MUST parse cleanly (FE500). A failure is an
    // emitter bug, never a policy reject. Runs on depth-bounded output.
    parse_emitted_sigil(&module, &out, codes::FE500_INTERNAL_MALFORMED)?;

    let emitted_len = out.len();
    Ok(EmittedSigil {
        source_name: format!("{module}.sigil"),
        text: out,
        map: SourceMap {
            entries: Vec::new(),
            emitted_len,
        },
    })
}

// ── cap-mode (RS1, inner ring) ──────────────────────────────────────────────

fn emit_cap_mode(
    program: &RsProgram,
    structs: &HashMap<&str, Vec<&str>>,
    out: &mut String,
) -> Result<(), FrontendDiag> {
    // Distinct cap names + (name, deadline) pairs, sorted for deterministic
    // emission. Empty for a no-cap (pure RS0) program.
    let mut cap_names: BTreeSet<&str> = BTreeSet::new();
    let mut cap_pairs: BTreeSet<(&str, i64)> = BTreeSet::new();
    for f in &program.functions {
        for c in &f.caps {
            cap_names.insert(c.name.as_str());
            cap_pairs.insert((c.name.as_str(), c.deadline));
        }
    }
    let cap_pairs: Vec<(&str, i64)> = cap_pairs.into_iter().collect();

    for name in &cap_names {
        out.push_str(&format!("cap type {name}(deadline_ms: i64) {{}}\n"));
    }
    // RS5b: the empty `Declassify` cap type, emitted once if any function uses the
    // `declassify(...)` escape hatch. Each call consumes a fresh linear instance —
    // `ownership::verify` (always-on) rejects a reuse with O001.
    if program.functions.iter().any(|f| f.n_declassify > 0) {
        out.push_str("cap type Declassify {}\n");
    }
    for (i, (name, deadline)) in cap_pairs.iter().enumerate() {
        out.push_str(&format!(
            "fn __fe_consume_{i}(c: {name}({deadline})) -> i64 {{ return 0; }}\n"
        ));
    }
    let pair_idx = |name: &str, deadline: i64| -> usize {
        cap_pairs
            .iter()
            .position(|&(n, d)| n == name && d == deadline)
            .expect("pair inserted")
    };

    for f in &program.functions {
        let vis = if f.is_pub { "pub " } else { "" };
        // RS5a: `#[sigil::taint]` → a SIGIL `@Label` on the targeted param/return; a
        // non-targeted one gets NO suffix (SR-T7, byte-identity). Taint is
        // mode-exclusive with caps (AG-T7), so there is no synthetic-param interaction.
        let mut params: Vec<String> = f
            .params
            .iter()
            .map(|p| format!("{}: {}{}", p.name, p.ty.name, param_taint(f, &p.name)))
            .collect();
        // Synthetic cap parameters, appended after the real params.
        for (i, c) in f.caps.iter().enumerate() {
            params.push(format!("__fe_cap_{i}: {}({})", c.name, c.deadline));
        }
        // RS5b: one synthetic linear `Declassify` cap per declassify call (SR-B4),
        // after the real + RS1 synthetic params. `RsExpr::Declassify` carries the
        // matching `k`, so the emit is a bijection (n caps declared, each used once).
        for k in 0..f.n_declassify {
            params.push(format!("__fe_declassify_cap_{k}: Declassify"));
        }

        // RS4a: a `#[sigil::requires]` becomes a SIGIL param-`where` clause between
        // `)` and `->` (Wall 4 Step 7). Z3 discharges it at every call site (T224 on
        // an unprovable one). The LHS param name is checker-validated (FE661).
        let where_clause = match &f.requires {
            Some(r) => format!(" where {} {} {}", r.param, r.op.as_str(), r.rhs),
            None => String::new(),
        };

        let mut body = String::new();
        body.push_str(&format!(
            "{vis}fn {}({}){} -> {}{} {{\n",
            f.name,
            params.join(", "),
            where_clause,
            f.ret.name,
            ret_taint(f)
        ));
        // Cap threading: move each cap into its terminal consumer at the top of
        // the body so it is never decorative (FE011).
        for (i, c) in f.caps.iter().enumerate() {
            let idx = pair_idx(&c.name, c.deadline);
            body.push_str(&format!(
                "  let __fe_used_{i} = __fe_consume_{idx}(__fe_cap_{i});\n"
            ));
        }
        emit_block_body(&f.body, structs, &mut body, 1);
        body.push_str("}\n");

        // FE011 guard: each cap param is threaded (moved) into a consumer. The
        // compiler does NOT flag an unused cap param, so the translator must.
        for i in 0..f.caps.len() {
            if !body.contains(&format!("__fe_cap_{i})")) {
                return Err(FrontendDiag::new(
                    codes::FE011_DECORATIVE_CAP,
                    "internal: emitted cap parameter was not threaded into the body",
                    f.span.clone(),
                ));
            }
        }
        // SR-B4: each synthetic `Declassify` cap is threaded (moved) into exactly its
        // own declassify call — bijective. An unused Declassify cap is silently
        // accepted by the compiler (the FE011 rationale), so the emitter asserts it.
        for k in 0..f.n_declassify {
            if !body.contains(&format!("__fe_declassify_cap_{k})")) {
                return Err(FrontendDiag::new(
                    codes::FE011_DECORATIVE_CAP,
                    "internal: emitted Declassify cap was not threaded into a declassify call",
                    f.span.clone(),
                ));
            }
        }
        out.push_str(&body);
    }
    Ok(())
}

// ── effect-mode (RS2, outer ring) ───────────────────────────────────────────

fn emit_effect_mode(
    program: &RsProgram,
    structs: &HashMap<&str, Vec<&str>>,
    out: &mut String,
) -> Result<(), FrontendDiag> {
    // Co-emit an `effect Name;` decl for every distinct effect name across every
    // row (sorted → deterministic). This is the fail-open spine (F5): a row name
    // with no decl is silently unenforced by the compiler.
    let mut effect_decls: BTreeSet<&str> = BTreeSet::new();
    for f in &program.functions {
        if let Some(es) = &f.effects {
            for e in es {
                effect_decls.insert(e.name.as_str());
            }
        }
    }
    for name in &effect_decls {
        out.push_str(&format!("effect {name};\n"));
    }

    for f in &program.functions {
        let vis = if f.is_pub { "pub " } else { "" };
        let params: Vec<String> = f
            .params
            .iter()
            .map(|p| format!("{}: {}", p.name, p.ty.name))
            .collect();
        // Every function gets an explicit row; an absent attribute → `! { }`.
        let names: BTreeSet<&str> = f
            .effects
            .as_ref()
            .map(|v| v.iter().map(|e| e.name.as_str()).collect())
            .unwrap_or_default();
        let row = if names.is_empty() {
            " ! { }".to_string()
        } else {
            format!(
                " ! {{ {} }}",
                names.iter().copied().collect::<Vec<_>>().join(", ")
            )
        };
        out.push_str(&format!(
            "{vis}fn {}({}) -> {}{row} {{\n",
            f.name,
            params.join(", "),
            f.ret.name
        ));
        emit_block_body(&f.body, structs, out, 1);
        out.push_str("}\n");
    }

    // FE210 backstop (the fail-open spine): every emitted row name has a decl.
    // Guaranteed by construction (decls = the union of all row names), but a
    // missing pairing would be silently unenforced, so we assert it.
    for f in &program.functions {
        if let Some(es) = &f.effects {
            for e in es {
                if !effect_decls.contains(e.name.as_str()) {
                    return Err(FrontendDiag::new(
                        codes::FE210_EFFECT_UNDECLARED,
                        format!(
                            "internal: effect `{}` has no co-emitted declaration",
                            e.name
                        ),
                        e.span.clone(),
                    ));
                }
            }
        }
    }
    Ok(())
}

// ── shared body/expression emission ─────────────────────────────────────────

/// Emit a block's statements at `indent`, then — for the function body — its tail
/// as a `return`. SIGIL has no tail-expression returns (T044), so a Rust tail
/// lowers to `return <tail>;`.
fn emit_block_body(
    block: &RsBlock,
    structs: &HashMap<&str, Vec<&str>>,
    out: &mut String,
    indent: usize,
) {
    for s in &block.stmts {
        emit_stmt(s, structs, out, indent);
    }
    if let Some(tail) = &block.tail {
        let pad = "  ".repeat(indent);
        out.push_str(&format!("{pad}return {};\n", emit_expr(tail, structs)));
    }
}

fn emit_stmt(s: &RsStmt, structs: &HashMap<&str, Vec<&str>>, out: &mut String, indent: usize) {
    let pad = "  ".repeat(indent);
    match s {
        RsStmt::Let {
            name,
            is_mut,
            value,
            ..
        } => {
            let kw = if *is_mut { "let mut" } else { "let" };
            out.push_str(&format!(
                "{pad}{kw} {name} = {};\n",
                emit_expr(value, structs)
            ));
        }
        RsStmt::Assign { name, value, .. } => {
            out.push_str(&format!("{pad}{name} = {};\n", emit_expr(value, structs)));
        }
        RsStmt::Return { value, .. } => match value {
            Some(e) => out.push_str(&format!("{pad}return {};\n", emit_expr(e, structs))),
            None => out.push_str(&format!("{pad}return;\n")),
        },
        RsStmt::If {
            cond,
            then_block,
            else_block,
            ..
        } => {
            // SIGIL requires an `else` on every `if` statement, so we always emit
            // one (an empty block when the Rust had none).
            out.push_str(&format!("{pad}if {} {{\n", emit_expr(cond, structs)));
            emit_block_body(then_block, structs, out, indent + 1);
            out.push_str(&format!("{pad}}} else {{\n"));
            if let Some(eb) = else_block {
                emit_block_body(eb, structs, out, indent + 1);
            }
            out.push_str(&format!("{pad}}}\n"));
        }
        RsStmt::While { cond, body, .. } => {
            out.push_str(&format!("{pad}while {} {{\n", emit_expr(cond, structs)));
            emit_block_body(body, structs, out, indent + 1);
            out.push_str(&format!("{pad}}}\n"));
        }
        RsStmt::Match {
            scrutinee, arms, ..
        } => {
            // Each arm's value lowers to a SIGIL braced block `{ return <value>; }`
            // (SIGIL match arms are blocks, not bare expressions). Arms are
            // comma-separated with no trailing comma on the last.
            out.push_str(&format!(
                "{pad}match {} {{\n",
                emit_expr(scrutinee, structs)
            ));
            let inner = "  ".repeat(indent + 1);
            for (i, arm) in arms.iter().enumerate() {
                let sep = if i + 1 == arms.len() { "" } else { "," };
                out.push_str(&format!(
                    "{inner}{} => {{ return {}; }}{sep}\n",
                    emit_pattern(&arm.pattern),
                    emit_expr(&arm.value, structs)
                ));
            }
            out.push_str(&format!("{pad}}}\n"));
        }
    }
}

/// Emit a match-arm pattern (RS3b/RS3c). Enum-variant patterns stay qualified
/// (`Name::Variant` or `Name::Variant(x, y)`) — the same form SIGIL uses.
fn emit_pattern(p: &RsPattern) -> String {
    match p {
        RsPattern::Variant {
            enum_name,
            variant,
            bindings,
            ..
        } => {
            if bindings.is_empty() {
                format!("{enum_name}::{variant}")
            } else {
                let names: Vec<&str> = bindings.iter().map(|(n, _)| n.as_str()).collect();
                format!("{enum_name}::{variant}({})", names.join(", "))
            }
        }
        RsPattern::Int(v, _) => v.to_string(),
        RsPattern::Bool(b, _) => if *b { "true" } else { "false" }.to_string(),
        RsPattern::Wildcard(_) => "_".to_string(),
    }
}

fn emit_expr(e: &RsExpr, structs: &HashMap<&str, Vec<&str>>) -> String {
    match e {
        RsExpr::Int(v, _) => v.to_string(),
        RsExpr::Bool(b, _) => if *b { "true" } else { "false" }.to_string(),
        RsExpr::Var(n, _) => n.clone(),
        RsExpr::Call(n, args, _) => {
            let parts: Vec<String> = args.iter().map(|a| emit_expr(a, structs)).collect();
            format!("{n}({})", parts.join(", "))
        }
        RsExpr::Unary(UnOp::Not, x, _) => format!("!({})", emit_expr(x, structs)),
        RsExpr::Unary(UnOp::Neg, x, _) => format!("-({})", emit_expr(x, structs)),
        RsExpr::Bin(op, l, r, _) => {
            format!(
                "({} {} {})",
                emit_expr(l, structs),
                binop_str(*op),
                emit_expr(r, structs)
            )
        }
        RsExpr::StructLit(name, fields, _) => {
            // Emit fields in DECLARATION order — the compiler stores record fields
            // at declaration offsets, so an out-of-order construction miscompiles.
            let order = structs.get(name.as_str()).expect("struct is registered");
            let parts: Vec<String> = order
                .iter()
                .map(|&df| {
                    let (_, val, _) = fields
                        .iter()
                        .find(|(fname, _, _)| fname.as_str() == df)
                        .expect("checker verified all declared fields are present");
                    format!("{df}: {}", emit_expr(val, structs))
                })
                .collect();
            format!("{name} {{ {} }}", parts.join(", "))
        }
        RsExpr::Field(recv, f, _) => format!("{}.{f}", emit_expr(recv, structs)),
        RsExpr::EnumCtor(enum_name, variant, args, _) => {
            if args.is_empty() {
                format!("{enum_name}::{variant}")
            } else {
                let parts: Vec<String> = args.iter().map(|a| emit_expr(a, structs)).collect();
                format!("{enum_name}::{variant}({})", parts.join(", "))
            }
        }
        RsExpr::Declassify(inner, k, _) => {
            // RS5b: lower to SIGIL's `declassify(value, cap)` keyword expression,
            // injecting the synthetic linear cap this call was assigned (SR-B4).
            format!(
                "declassify({}, __fe_declassify_cap_{k})",
                emit_expr(inner, structs)
            )
        }
    }
}

fn binop_str(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
    }
}
