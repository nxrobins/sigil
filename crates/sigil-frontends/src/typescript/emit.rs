//! Deterministic SIGIL emitter for the FE2 TypeScript subset. Runs the sound
//! type+scope checker first (`check::check_program`), then emits well-typed
//! SIGIL — records, control-flow bodies, booleans/comparisons — in cap-mode
//! (inner ring) or effect-mode (outer ring). Order is fixed: check → emit, on a
//! tree the parser produced (M3). `&&`/`||` desugaring is the FE2c slice.
//!
//! All ordering is deterministic (BTreeSet for caps/effects; record + field
//! emission in declaration order, M6). Construction names come from the
//! checker's `object_types` (H13). After building the text, a parse self-check
//! (FE500) confirms well-formedness.

use std::collections::BTreeSet;
use std::collections::HashMap;

use crate::codes;
use crate::{EmittedSigil, FrontendDiag, SourceMap, parse_emitted_sigil, sanitize_module_name};

use super::check::{self, Checked};
use super::parser::{BinOp, TsExpr, TsFunction, TsInterface, TsProgram, TsStmt, UnOp};

/// Map a TS type-annotation name to its SIGIL type.
fn sigil_ty(name: &str) -> String {
    match name {
        "number" => "i64".to_string(),
        "boolean" => "bool".to_string(),
        other => other.to_string(),
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
        BinOp::And | BinOp::Or => unreachable!("&&/|| are desugared before emission"),
    }
}

struct EmitCtx<'a> {
    checked: &'a Checked,
    records: HashMap<&'a str, &'a TsInterface>,
}

pub fn emit(program: &TsProgram, source_name: &str) -> Result<EmittedSigil, FrontendDiag> {
    // F1 (FE1 spine): whole-file mode pre-pass before any emission.
    let has_cap = program.functions.iter().any(|f| !f.caps.is_empty());
    let has_effect = program.functions.iter().any(|f| f.effects.is_some());
    if has_cap && has_effect {
        let span = program
            .functions
            .iter()
            .find(|f| f.effects.is_some())
            .map(|f| f.span.clone())
            .unwrap_or(0..0);
        return Err(FrontendDiag::new(
            codes::FE201_MIXED_MODE,
            "a file may not mix @cap and @effects (mode is per-file homogeneous; mixed-mode is deferred)",
            span,
        ));
    }

    // The sound type+scope checker (H2/M1 spine): proves well-typedness and
    // resolves object-literal record types BEFORE any emission.
    let checked = check::check_program(program)?;

    // F7/FE211: emitted top-level names (fns + records + cap-types|effects) unique.
    check_toplevel_name_uniqueness(program, has_effect)?;

    let records: HashMap<&str, &TsInterface> = program
        .interfaces
        .iter()
        .map(|it| (it.name.as_str(), it))
        .collect();
    let ctx = EmitCtx {
        checked: &checked,
        records,
    };

    let module = sanitize_module_name(source_name, "policy");
    let mut out = String::new();
    if has_effect {
        out.push_str("#[ring(outer)]\n");
    }
    out.push_str(&format!("module {module};\n"));

    // Record declarations (both modes; records are ring-agnostic). Source order
    // is deterministic; fields in declaration order (M6).
    for it in &program.interfaces {
        let fields: Vec<String> = it
            .fields
            .iter()
            .map(|f| format!("{}: {}", f.name, sigil_ty(&f.ty.name)))
            .collect();
        out.push_str(&format!("record {} {{ {} }}\n", it.name, fields.join(", ")));
    }

    // Distinct caps/effects (sorted → deterministic).
    let mut effect_decls: BTreeSet<&str> = BTreeSet::new();
    let mut cap_names: BTreeSet<&str> = BTreeSet::new();
    let mut cap_pairs: BTreeSet<(&str, i64)> = BTreeSet::new();
    for f in &program.functions {
        if let Some(effs) = &f.effects {
            for e in effs {
                effect_decls.insert(e.name.as_str());
            }
        }
        for c in &f.caps {
            cap_names.insert(c.name.as_str());
            cap_pairs.insert((c.name.as_str(), c.deadline));
        }
    }
    let cap_pairs: Vec<(&str, i64)> = cap_pairs.into_iter().collect();
    let pair_idx = |name: &str, deadline: i64| -> usize {
        cap_pairs
            .iter()
            .position(|&(n, d)| n == name && d == deadline)
            .expect("pair inserted")
    };

    if has_effect {
        for name in &effect_decls {
            out.push_str(&format!("effect {name};\n"));
        }
    } else {
        for name in &cap_names {
            out.push_str(&format!("cap type {name}(deadline_ms: i64) {{}}\n"));
        }
        for (i, (name, deadline)) in cap_pairs.iter().enumerate() {
            out.push_str(&format!(
                "fn __fe_consume_{i}(c: {name}({deadline})) -> i64 {{ return 0; }}\n"
            ));
        }
    }

    // Functions.
    for f in &program.functions {
        let ftext = emit_function(f, &ctx, has_effect, &pair_idx)?;
        out.push_str(&ftext);
    }

    // F5/FE210 (effect-mode): every row name has a co-emitted decl.
    if has_effect {
        for f in &program.functions {
            if let Some(effs) = &f.effects {
                for e in effs {
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
    }

    // Self-check: emitted SIGIL MUST parse cleanly (T10/FE500).
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

fn emit_function(
    f: &TsFunction,
    ctx: &EmitCtx,
    has_effect: bool,
    pair_idx: &impl Fn(&str, i64) -> usize,
) -> Result<String, FrontendDiag> {
    let mut sig: Vec<String> = f
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, sigil_ty(&p.ty.name)))
        .collect();
    for (i, c) in f.caps.iter().enumerate() {
        sig.push(format!("__fe_cap_{i}: {}({})", c.name, c.deadline));
    }
    let ret = sigil_ty(&f.ret.name);

    let row = if has_effect {
        let names: BTreeSet<&str> = f
            .effects
            .as_ref()
            .map(|v| v.iter().map(|e| e.name.as_str()).collect())
            .unwrap_or_default();
        if names.is_empty() {
            " ! { }".to_string()
        } else {
            format!(
                " ! {{ {} }}",
                names.iter().copied().collect::<Vec<_>>().join(", ")
            )
        }
    } else {
        String::new()
    };

    let mut body = String::new();
    body.push_str(&format!(
        "pub fn {}({}) -> {ret}{row} {{\n",
        f.name,
        sig.join(", ")
    ));
    // Cap threading (cap-mode): move each cap into its terminal consumer at the
    // top of the body so it is never decorative (T2/FE011), regardless of the
    // control-flow that follows.
    for (i, c) in f.caps.iter().enumerate() {
        let idx = pair_idx(&c.name, c.deadline);
        body.push_str(&format!(
            "  let __fe_used_{i} = __fe_consume_{idx}(__fe_cap_{i});\n"
        ));
    }
    for s in &f.body {
        emit_stmt(s, ctx, &mut body, 1);
    }
    body.push_str("}\n");

    // T2/FE011 guard: each cap param is threaded (moved) into a consumer.
    for i in 0..f.caps.len() {
        if !body.contains(&format!("__fe_cap_{i})")) {
            return Err(FrontendDiag::new(
                codes::FE011_DECORATIVE_CAP,
                "internal: emitted cap parameter was not threaded into the body",
                f.span.clone(),
            ));
        }
    }
    Ok(body)
}

fn emit_stmt(s: &TsStmt, ctx: &EmitCtx, out: &mut String, indent: usize) {
    let pad = "  ".repeat(indent);
    match s {
        TsStmt::Let {
            name,
            decl_let,
            value,
            ..
        } => {
            let kw = if *decl_let { "let mut" } else { "let" };
            out.push_str(&format!("{pad}{kw} {name} = {};\n", emit_expr(value, ctx)));
        }
        TsStmt::Assign { name, value, .. } => {
            out.push_str(&format!("{pad}{name} = {};\n", emit_expr(value, ctx)));
        }
        TsStmt::Return { value, .. } => match value {
            Some(e) => out.push_str(&format!("{pad}return {};\n", emit_expr(e, ctx))),
            None => out.push_str(&format!("{pad}return;\n")),
        },
        TsStmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            // SIGIL requires an `else` on every `if` statement, so we always
            // emit one (an empty block when the TS had no else).
            out.push_str(&format!("{pad}if {} {{\n", emit_expr(cond, ctx)));
            for st in then_body {
                emit_stmt(st, ctx, out, indent + 1);
            }
            out.push_str(&format!("{pad}}} else {{\n"));
            for st in else_body {
                emit_stmt(st, ctx, out, indent + 1);
            }
            out.push_str(&format!("{pad}}}\n"));
        }
        TsStmt::While { cond, body, .. } => {
            out.push_str(&format!("{pad}while {} {{\n", emit_expr(cond, ctx)));
            for st in body {
                emit_stmt(st, ctx, out, indent + 1);
            }
            out.push_str(&format!("{pad}}}\n"));
        }
        TsStmt::ExprStmt(e, _) => {
            out.push_str(&format!("{pad}{};\n", emit_expr(e, ctx)));
        }
    }
}

fn emit_expr(e: &TsExpr, ctx: &EmitCtx) -> String {
    match e {
        TsExpr::Int(v, _) => v.to_string(),
        TsExpr::Bool(b, _) => if *b { "true" } else { "false" }.to_string(),
        TsExpr::Var(n, _) => n.clone(),
        TsExpr::Field(r, f, _) => format!("{}.{f}", emit_expr(r, ctx)),
        TsExpr::Call(n, args, _) => {
            let parts: Vec<String> = args.iter().map(|a| emit_expr(a, ctx)).collect();
            format!("{n}({})", parts.join(", "))
        }
        TsExpr::Unary(UnOp::Not, x, _) => format!("!({})", emit_expr(x, ctx)),
        TsExpr::Unary(UnOp::Neg, x, _) => format!("-({})", emit_expr(x, ctx)),
        TsExpr::Bin(op, l, r, _) => {
            format!(
                "({} {} {})",
                emit_expr(l, ctx),
                binop_str(*op),
                emit_expr(r, ctx)
            )
        }
        TsExpr::Object(fields, span) => {
            let rec = ctx
                .checked
                .object_types
                .get(&(span.start, span.end))
                .expect("checker resolved this object literal's record type");
            let it = ctx.records.get(rec.as_str()).expect("record exists");
            // Provided values by field name for O(1) lookup (the checker verified the
            // provided set equals the declared set exactly), then emit in record
            // DECLARATION order (M6 canonical) — independent of object-literal order.
            let provided: HashMap<&str, &TsExpr> = fields
                .iter()
                .map(|(fname, _, val)| (fname.as_str(), val))
                .collect();
            let parts: Vec<String> = it
                .fields
                .iter()
                .map(|df| {
                    let val = provided
                        .get(df.name.as_str())
                        .expect("checker verified all fields present");
                    format!("{}: {}", df.name, emit_expr(val, ctx))
                })
                .collect();
            format!("{rec} {{ {} }}", parts.join(", "))
        }
    }
}

/// F7/FE211: every emitted top-level name (functions + records + cap-types or
/// effects) must be unique. A collision is N002 at name-resolution, invisible to
/// the FE500 parse self-check. Applies in both modes.
fn check_toplevel_name_uniqueness(
    program: &TsProgram,
    has_effect: bool,
) -> Result<(), FrontendDiag> {
    let mut seen: HashMap<String, &'static str> = HashMap::new();
    let mut check = |name: &str,
                     kind: &'static str,
                     span: &std::ops::Range<usize>|
     -> Result<(), FrontendDiag> {
        if let Some(prev) = seen.insert(name.to_string(), kind) {
            return Err(FrontendDiag::new(
                codes::FE211_NAME_COLLISION,
                format!("{kind} `{name}` collides with a {prev} of the same name"),
                span.clone(),
            ));
        }
        Ok(())
    };
    for it in &program.interfaces {
        check(&it.name, "record", &it.name_span)?;
    }
    for f in &program.functions {
        check(&f.name, "function", &f.name_span)?;
    }
    let kind = if has_effect { "effect" } else { "cap type" };
    let mut named: std::collections::HashSet<&str> = std::collections::HashSet::new();
    for f in &program.functions {
        if has_effect {
            if let Some(effs) = &f.effects {
                for e in effs {
                    if named.insert(e.name.as_str()) {
                        check(&e.name, kind, &e.span)?;
                    }
                }
            }
        } else {
            for c in &f.caps {
                if named.insert(c.name.as_str()) {
                    check(&c.name, kind, &c.span)?;
                }
            }
        }
    }
    Ok(())
}
