//! The FE2 type + scope checker — the spine (H2/M1). It assigns every node a
//! resolved type matching what the SIGIL compiler would assign and rejects any
//! in-subset TS type/scope/return error with an `FE3xx` code BEFORE emission,
//! so emitted SIGIL is well-typed by construction (no T-code masquerade). It
//! also resolves each object literal's expected record type (H13) into
//! `object_types`, which the emitter reads to name the construction.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use crate::FrontendDiag;
use crate::codes;

use super::parser::{
    BinOp, TsExpr, TsFunction, TsInterface, TsProgram, TsStmt, TsTypeAnn, UnOp, expr_span,
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum FeTy {
    I64,
    Bool,
    Record(String),
}

impl FeTy {
    fn show(&self) -> String {
        match self {
            FeTy::I64 => "number".to_string(),
            FeTy::Bool => "boolean".to_string(),
            FeTy::Record(r) => r.clone(),
        }
    }
}

/// Output of a successful check: the record type chosen for each object literal,
/// keyed by the literal's `(start, end)` byte span.
pub struct Checked {
    pub object_types: HashMap<(usize, usize), String>,
}

struct Ctx<'a> {
    records: HashMap<&'a str, &'a TsInterface>,
    /// name → (param types, return type, is-cap-bearing)
    fns: HashMap<&'a str, (Vec<FeTy>, FeTy, bool)>,
    object_types: HashMap<(usize, usize), String>,
}

/// One lexical scope block: name → (type, assignable). `assignable` is true for
/// TS `let` (we emit `let mut`), false for `const` and parameters.
type Block = HashMap<String, (FeTy, bool)>;

/// Type names the SIGIL compiler resolves to a built-in BEFORE consulting user
/// records (`resolve_type_expr`: unit/bool/i32/u32/i64/u64/f64/str/Region), plus
/// the `Slot` reserved name (T193). An `interface` or type annotation using one
/// of these would emit a `record`/annotation the oracle silently shadows with
/// the primitive — yielding an ill-typed emission (e.g. field access → T122) or
/// a silent record↔primitive type divergence. These are the Ident-classed names;
/// keyword-classed ones (`region`, `actor`, …) are already rejected by FE021 in
/// the parser. `ActorRef` only resolves to a built-in *with* type args, which
/// FE2 rejects (generics → FE320), so a bare `ActorRef` is a legitimate record.
const RESERVED_SIGIL_TYPES: &[&str] = &[
    "unit", "bool", "i32", "u32", "i64", "u64", "f64", "str", "Region", "Slot",
];

fn is_reserved_sigil_type(name: &str) -> bool {
    RESERVED_SIGIL_TYPES.contains(&name)
}

pub fn check_program(p: &TsProgram) -> Result<Checked, FrontendDiag> {
    // 1. Record registry (interfaces), with duplicate + field validation.
    let mut records: HashMap<&str, &TsInterface> = HashMap::new();
    for it in &p.interfaces {
        if is_reserved_sigil_type(&it.name) {
            return Err(FrontendDiag::new(
                codes::FE021_RESERVED_NAME,
                format!(
                    "interface name `{}` is a reserved SIGIL type name (the compiler would resolve it to the built-in, silently shadowing your record)",
                    it.name
                ),
                it.name_span.clone(),
            ));
        }
        if records.insert(it.name.as_str(), it).is_some() {
            return Err(FrontendDiag::new(
                codes::FE301_ILL_TYPED,
                format!("duplicate interface `{}`", it.name),
                it.name_span.clone(),
            ));
        }
    }
    for it in &p.interfaces {
        let mut seen: HashSet<&str> = HashSet::new();
        for f in &it.fields {
            if !seen.insert(f.name.as_str()) {
                return Err(FrontendDiag::new(
                    codes::FE301_ILL_TYPED,
                    format!("duplicate field `{}` in interface `{}`", f.name, it.name),
                    f.name_span.clone(),
                ));
            }
            resolve_ty(&f.ty, &records)?;
        }
    }

    // 2. Function signature registry.
    let mut fns: HashMap<&str, (Vec<FeTy>, FeTy, bool)> = HashMap::new();
    for f in &p.functions {
        if fns.contains_key(f.name.as_str()) {
            return Err(FrontendDiag::new(
                codes::FE301_ILL_TYPED,
                format!("duplicate function `{}`", f.name),
                f.name_span.clone(),
            ));
        }
        let mut params = Vec::with_capacity(f.params.len());
        for pp in &f.params {
            params.push(resolve_ty(&pp.ty, &records)?);
        }
        let ret = resolve_ty(&f.ret, &records)?;
        fns.insert(f.name.as_str(), (params, ret, !f.caps.is_empty()));
    }

    let mut ctx = Ctx {
        records,
        fns,
        object_types: HashMap::new(),
    };
    for f in &p.functions {
        ctx.check_function(f)?;
    }
    Ok(Checked {
        object_types: ctx.object_types,
    })
}

fn resolve_ty(
    ann: &TsTypeAnn,
    records: &HashMap<&str, &TsInterface>,
) -> Result<FeTy, FrontendDiag> {
    match ann.name.as_str() {
        "number" => Ok(FeTy::I64),
        "boolean" => Ok(FeTy::Bool),
        other => {
            if is_reserved_sigil_type(other) {
                // Defense-in-depth: an interface named this is already rejected
                // at registration, so this fires for a bare annotation like
                // `p: i64` (TS should write `number`) that would otherwise read
                // as an "unknown type".
                Err(FrontendDiag::new(
                    codes::FE320_UNSUPPORTED_TS,
                    format!(
                        "`{other}` is a reserved SIGIL type name; use `number`/`boolean` or rename"
                    ),
                    ann.span.clone(),
                ))
            } else if records.contains_key(other) {
                Ok(FeTy::Record(other.to_string()))
            } else {
                Err(FrontendDiag::new(
                    codes::FE320_UNSUPPORTED_TS,
                    format!(
                        "unknown type `{other}` (FE2 supports number, boolean, and declared interfaces)"
                    ),
                    ann.span.clone(),
                ))
            }
        }
    }
}

impl Ctx<'_> {
    fn check_function(&mut self, f: &TsFunction) -> Result<(), FrontendDiag> {
        let ret = resolve_ty(&f.ret, &self.records)?;
        let mut scope: Vec<Block> = Vec::new();
        let mut params: Block = HashMap::new();
        for pp in &f.params {
            let ty = resolve_ty(&pp.ty, &self.records)?;
            params.insert(pp.name.clone(), (ty, false));
        }
        scope.push(params);
        let guaranteed = self.check_block(&f.body, &mut scope, &ret)?;
        // Every FE2 function has a non-unit return type, so all paths must return.
        if !guaranteed {
            return Err(FrontendDiag::new(
                codes::FE306_NON_EXHAUSTIVE_RETURN,
                format!(
                    "function `{}` may finish without returning a {}",
                    f.name,
                    ret.show()
                ),
                f.name_span.clone(),
            ));
        }
        Ok(())
    }

    /// Returns whether the block is guaranteed to return on every path.
    fn check_block(
        &mut self,
        stmts: &[TsStmt],
        scope: &mut Vec<Block>,
        ret: &FeTy,
    ) -> Result<bool, FrontendDiag> {
        scope.push(HashMap::new());
        let mut guaranteed = false;
        for s in stmts {
            guaranteed |= self.check_stmt(s, scope, ret)?;
        }
        scope.pop();
        Ok(guaranteed)
    }

    fn check_stmt(
        &mut self,
        s: &TsStmt,
        scope: &mut Vec<Block>,
        ret: &FeTy,
    ) -> Result<bool, FrontendDiag> {
        match s {
            TsStmt::Let {
                name,
                name_span,
                decl_let,
                ann,
                value,
                ..
            } => {
                let expected = match ann {
                    Some(a) => Some(resolve_ty(a, &self.records)?),
                    None => None,
                };
                let vty = self.check_expr(value, expected.as_ref(), scope)?;
                let declared = expected.unwrap_or(vty);
                let top = scope.last_mut().expect("a scope block");
                if top.contains_key(name) {
                    return Err(FrontendDiag::new(
                        codes::FE308_UNRESOLVED_REFERENCE,
                        format!("`{name}` is already declared in this block"),
                        name_span.clone(),
                    ));
                }
                top.insert(name.clone(), (declared, *decl_let));
                Ok(false)
            }
            TsStmt::Assign {
                name,
                name_span,
                value,
                ..
            } => {
                let (ty, assignable) = self.lookup(scope, name).ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE308_UNRESOLVED_REFERENCE,
                        format!("assignment to undeclared variable `{name}`"),
                        name_span.clone(),
                    )
                })?;
                if !assignable {
                    return Err(FrontendDiag::new(
                        codes::FE307_ILLEGAL_REASSIGNMENT,
                        format!("cannot reassign `{name}` (declared `const`, or a parameter)"),
                        name_span.clone(),
                    ));
                }
                self.check_expr(value, Some(&ty), scope)?;
                Ok(false)
            }
            TsStmt::Return { value, span } => {
                match value {
                    Some(v) => {
                        self.check_expr(v, Some(ret), scope)?;
                    }
                    None => {
                        return Err(FrontendDiag::new(
                            codes::FE306_NON_EXHAUSTIVE_RETURN,
                            format!(
                                "`return;` with no value in a function returning {}",
                                ret.show()
                            ),
                            span.clone(),
                        ));
                    }
                }
                Ok(true)
            }
            TsStmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.check_condition(cond, scope)?;
                let g_then = self.check_block(then_body, scope, ret)?;
                if else_body.is_empty() {
                    // No else → cannot guarantee return.
                    self.check_block(else_body, scope, ret)?;
                    Ok(false)
                } else {
                    let g_else = self.check_block(else_body, scope, ret)?;
                    Ok(g_then && g_else)
                }
            }
            TsStmt::While { cond, body, .. } => {
                self.check_condition(cond, scope)?;
                // A `while` body may not execute, so it never guarantees return.
                self.check_block(body, scope, ret)?;
                Ok(false)
            }
            TsStmt::ExprStmt(e, _) => {
                self.check_expr(e, None, scope)?;
                Ok(false)
            }
        }
    }

    fn check_condition(
        &mut self,
        cond: &TsExpr,
        scope: &mut Vec<Block>,
    ) -> Result<(), FrontendDiag> {
        let ty = self.check_expr(cond, None, scope)?;
        if ty != FeTy::Bool {
            return Err(FrontendDiag::new(
                codes::FE303_TRUTHY_CONDITION,
                format!(
                    "condition must be boolean, found {} (FE2 has no truthiness)",
                    ty.show()
                ),
                expr_span(cond),
            ));
        }
        Ok(())
    }

    fn lookup(&self, scope: &[Block], name: &str) -> Option<(FeTy, bool)> {
        for blk in scope.iter().rev() {
            if let Some(v) = blk.get(name) {
                return Some(v.clone());
            }
        }
        None
    }

    fn check_expr(
        &mut self,
        e: &TsExpr,
        expected: Option<&FeTy>,
        scope: &mut Vec<Block>,
    ) -> Result<FeTy, FrontendDiag> {
        // Object literals are typed top-down from the expected record type.
        if let TsExpr::Object(fields, span) = e {
            let rec = match expected {
                Some(FeTy::Record(r)) => r.clone(),
                _ => {
                    return Err(FrontendDiag::new(
                        codes::FE304_UNTYPED_OBJECT_LITERAL,
                        "object literal has no inferable record type here (annotate the binding/return, or use it where a record is expected)",
                        span.clone(),
                    ));
                }
            };
            let it = *self
                .records
                .get(rec.as_str())
                .expect("expected record exists");
            // Field-type map for O(1) per-field lookup (interface fields are unique —
            // duplicates were rejected at registration in `check_program`). The
            // deterministic declaration order for the missing-field scan comes from
            // `it.fields` itself, so no ordered copy is needed.
            let mut declared: HashMap<&str, FeTy> = HashMap::new();
            for f in &it.fields {
                declared.insert(f.name.as_str(), resolve_ty(&f.ty, &self.records)?);
            }
            let mut provided: HashSet<&str> = HashSet::new();
            for (fname, fspan, fval) in fields {
                if !provided.insert(fname.as_str()) {
                    return Err(FrontendDiag::new(
                        codes::FE305_UNKNOWN_FIELD,
                        format!("field `{fname}` supplied more than once for `{rec}`"),
                        fspan.clone(),
                    ));
                }
                let Some(fty) = declared.get(fname.as_str()) else {
                    return Err(FrontendDiag::new(
                        codes::FE305_UNKNOWN_FIELD,
                        format!("`{rec}` has no field `{fname}`"),
                        fspan.clone(),
                    ));
                };
                self.check_expr(fval, Some(fty), scope)?;
            }
            for f in &it.fields {
                if !provided.contains(f.name.as_str()) {
                    return Err(FrontendDiag::new(
                        codes::FE302_MISSING_FIELD,
                        format!("record `{rec}` construction is missing field `{}`", f.name),
                        span.clone(),
                    ));
                }
            }
            self.object_types
                .insert((span.start, span.end), rec.clone());
            return Ok(FeTy::Record(rec));
        }

        let ty = self.infer_expr(e, scope)?;
        if let Some(exp) = expected
            && &ty != exp
        {
            // A record↔record name mismatch is the nominal-vs-structural case.
            let code = match (exp, &ty) {
                (FeTy::Record(_), FeTy::Record(_)) => codes::FE310_STRUCTURAL_MISMATCH,
                _ => codes::FE301_ILL_TYPED,
            };
            return Err(FrontendDiag::new(
                code,
                format!("expected {}, found {}", exp.show(), ty.show()),
                expr_span(e),
            ));
        }
        Ok(ty)
    }

    fn infer_expr(&mut self, e: &TsExpr, scope: &mut Vec<Block>) -> Result<FeTy, FrontendDiag> {
        match e {
            TsExpr::Int(_, _) => Ok(FeTy::I64),
            TsExpr::Bool(_, _) => Ok(FeTy::Bool),
            TsExpr::Object(_, span) => Err(FrontendDiag::new(
                codes::FE304_UNTYPED_OBJECT_LITERAL,
                "object literal has no inferable record type here",
                span.clone(),
            )),
            TsExpr::Var(name, span) => self.lookup(scope, name).map(|(t, _)| t).ok_or_else(|| {
                FrontendDiag::new(
                    codes::FE308_UNRESOLVED_REFERENCE,
                    format!("unknown identifier `{name}`"),
                    span.clone(),
                )
            }),
            TsExpr::Unary(UnOp::Not, x, span) => {
                let tx = self.check_expr(x, None, scope)?;
                if tx != FeTy::Bool {
                    return Err(FrontendDiag::new(
                        codes::FE309_NON_BOOL_NEGATION,
                        format!("`!` requires a boolean operand, found {}", tx.show()),
                        span.clone(),
                    ));
                }
                Ok(FeTy::Bool)
            }
            TsExpr::Unary(UnOp::Neg, x, span) => {
                let tx = self.check_expr(x, None, scope)?;
                if tx != FeTy::I64 {
                    return Err(FrontendDiag::new(
                        codes::FE301_ILL_TYPED,
                        format!("unary `-` requires a number operand, found {}", tx.show()),
                        span.clone(),
                    ));
                }
                Ok(FeTy::I64)
            }
            TsExpr::Bin(op, l, r, span) => self.infer_bin(*op, l, r, span, scope),
            TsExpr::Field(recv, field, span) => {
                let rt = self.check_expr(recv, None, scope)?;
                let FeTy::Record(rname) = rt else {
                    return Err(FrontendDiag::new(
                        codes::FE301_ILL_TYPED,
                        format!(
                            "field access `.{field}` on a non-record value ({})",
                            rt.show()
                        ),
                        span.clone(),
                    ));
                };
                let it = *self.records.get(rname.as_str()).expect("record exists");
                match it.fields.iter().find(|f| f.name == *field) {
                    Some(f) => resolve_ty(&f.ty, &self.records),
                    None => Err(FrontendDiag::new(
                        codes::FE301_ILL_TYPED,
                        format!("record `{rname}` has no field `{field}`"),
                        span.clone(),
                    )),
                }
            }
            TsExpr::Call(name, args, span) => {
                let (params, ret, cap_bearing) =
                    self.fns.get(name.as_str()).cloned().ok_or_else(|| {
                        FrontendDiag::new(
                            codes::FE308_UNRESOLVED_REFERENCE,
                            format!("call to undeclared function `{name}`"),
                            span.clone(),
                        )
                    })?;
                if cap_bearing {
                    return Err(FrontendDiag::new(
                        codes::FE040_CAP_CALLEE,
                        format!(
                            "function `{name}` carries a @cap and cannot be called intra-program"
                        ),
                        span.clone(),
                    ));
                }
                if args.len() != params.len() {
                    return Err(FrontendDiag::new(
                        codes::FE301_ILL_TYPED,
                        format!(
                            "call to `{name}` has {} argument(s); it declares {}",
                            args.len(),
                            params.len()
                        ),
                        span.clone(),
                    ));
                }
                for (a, pty) in args.iter().zip(params.iter()) {
                    self.check_expr(a, Some(pty), scope)?;
                }
                Ok(ret)
            }
        }
    }

    fn infer_bin(
        &mut self,
        op: BinOp,
        l: &TsExpr,
        r: &TsExpr,
        span: &Range<usize>,
        scope: &mut Vec<Block>,
    ) -> Result<FeTy, FrontendDiag> {
        match op {
            BinOp::And | BinOp::Or => {
                // The desugar pass (M3) removes every reachable `&&`/`||` before
                // the checker runs; reaching here is an internal invariant break.
                Err(FrontendDiag::new(
                    codes::FE301_ILL_TYPED,
                    "internal: undesugared `&&`/`||` reached the checker",
                    span.clone(),
                ))
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let lt = self.check_expr(l, None, scope)?;
                let rt = self.check_expr(r, None, scope)?;
                if lt != FeTy::I64 || rt != FeTy::I64 {
                    return Err(FrontendDiag::new(
                        codes::FE301_ILL_TYPED,
                        format!(
                            "arithmetic requires number operands, found {} and {}",
                            lt.show(),
                            rt.show()
                        ),
                        span.clone(),
                    ));
                }
                Ok(FeTy::I64)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let lt = self.check_expr(l, None, scope)?;
                let rt = self.check_expr(r, None, scope)?;
                if lt != FeTy::I64 || rt != FeTy::I64 {
                    return Err(FrontendDiag::new(
                        codes::FE311_OPERAND_TYPE,
                        format!(
                            "relational operators require number operands, found {} and {}",
                            lt.show(),
                            rt.show()
                        ),
                        span.clone(),
                    ));
                }
                Ok(FeTy::Bool)
            }
            BinOp::Eq | BinOp::Ne => {
                let lt = self.check_expr(l, None, scope)?;
                let rt = self.check_expr(r, None, scope)?;
                if lt != rt {
                    return Err(FrontendDiag::new(
                        codes::FE311_OPERAND_TYPE,
                        format!(
                            "`==`/`!=` require operands of equal type, found {} and {}",
                            lt.show(),
                            rt.show()
                        ),
                        span.clone(),
                    ));
                }
                Ok(FeTy::Bool)
            }
        }
    }
}
