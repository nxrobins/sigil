//! ANF desugaring of `&&`/`||` (FE2c). SIGIL has no logical operators and `if`
//! is a statement, so `a && b` / `a || b` are lowered to a `bool` temp plus a
//! guarded `if` that evaluates the RHS only on the short-circuit-reachable path
//! (M3: runs BEFORE check/emit; M4: the temp is declared in the nearest
//! enclosing block, immediately before its use, with a per-function-unique
//! monotonic index; M5: lowering is strictly intra-function — no new helpers,
//! no call relocated across a function boundary).
//!
//! `&&`/`||` are hoistable wherever the enclosing statement evaluates the
//! expression exactly once (return/let/assign/expr-stmt/if-cond/call-arg/field
//! value). A `while` condition is re-evaluated each iteration, so `&&`/`||`
//! there cannot be hoisted and are rejected (FE301; anti-goal M8).

use std::ops::Range;

use crate::FrontendDiag;
use crate::codes;

use super::parser::{BinOp, TsExpr, TsProgram, TsStmt, TsTypeAnn};

pub fn desugar(p: &mut TsProgram) -> Result<(), FrontendDiag> {
    for f in &mut p.functions {
        let mut d = D { counter: 0 };
        let body = std::mem::take(&mut f.body);
        f.body = d.block(body)?;
    }
    Ok(())
}

struct D {
    counter: u32,
}

impl D {
    fn fresh(&mut self, span: &Range<usize>) -> (String, Range<usize>) {
        let n = self.counter;
        self.counter += 1;
        (format!("__fe_{n}"), span.clone())
    }

    fn block(&mut self, stmts: Vec<TsStmt>) -> Result<Vec<TsStmt>, FrontendDiag> {
        let mut out = Vec::new();
        for s in stmts {
            self.stmt(s, &mut out)?;
        }
        Ok(out)
    }

    fn stmt(&mut self, s: TsStmt, out: &mut Vec<TsStmt>) -> Result<(), FrontendDiag> {
        match s {
            TsStmt::Let {
                name,
                name_span,
                decl_let,
                ann,
                value,
                span,
            } => {
                let value = self.expr(value, out)?;
                out.push(TsStmt::Let {
                    name,
                    name_span,
                    decl_let,
                    ann,
                    value,
                    span,
                });
            }
            TsStmt::Assign {
                name,
                name_span,
                value,
                span,
            } => {
                let value = self.expr(value, out)?;
                out.push(TsStmt::Assign {
                    name,
                    name_span,
                    value,
                    span,
                });
            }
            TsStmt::Return { value, span } => {
                let value = match value {
                    Some(e) => Some(self.expr(e, out)?),
                    None => None,
                };
                out.push(TsStmt::Return { value, span });
            }
            TsStmt::ExprStmt(e, span) => {
                let e = self.expr(e, out)?;
                out.push(TsStmt::ExprStmt(e, span));
            }
            TsStmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => {
                // An `if` condition is evaluated once, so its &&/|| hoist before
                // the `if` is correct.
                let cond = self.expr(cond, out)?;
                let then_body = self.block(then_body)?;
                let else_body = self.block(else_body)?;
                out.push(TsStmt::If {
                    cond,
                    then_body,
                    else_body,
                    span,
                });
            }
            TsStmt::While { cond, body, span } => {
                // A `while` condition is re-evaluated each iteration; hoisting
                // &&/|| out would evaluate them once → reject (M8/FE301).
                if contains_logical(&cond) {
                    return Err(FrontendDiag::new(
                        codes::FE301_ILL_TYPED,
                        "`&&`/`||` in a `while` condition are not supported in FE2 (lift the test into a helper)",
                        super::parser::expr_span(&cond),
                    ));
                }
                let body = self.block(body)?;
                out.push(TsStmt::While { cond, body, span });
            }
        }
        Ok(())
    }

    /// Replace every `&&`/`||` in `e` with a fresh bool temp, appending the
    /// hoist statements to `out` (in evaluation order). Non-logical sub-exprs
    /// hoist unconditionally; the RHS of a logical op hoists INSIDE the guard.
    fn expr(&mut self, e: TsExpr, out: &mut Vec<TsStmt>) -> Result<TsExpr, FrontendDiag> {
        match e {
            TsExpr::Bin(BinOp::And, l, r, span) => {
                let l = self.expr(*l, out)?;
                let (n, nspan) = self.fresh(&span);
                out.push(TsStmt::Let {
                    name: n.clone(),
                    name_span: nspan.clone(),
                    decl_let: true,
                    ann: Some(TsTypeAnn {
                        name: "boolean".to_string(),
                        span: nspan.clone(),
                    }),
                    value: l,
                    span: nspan.clone(),
                });
                // RHS only when LHS is true.
                let mut guarded = Vec::new();
                let r = self.expr(*r, &mut guarded)?;
                guarded.push(TsStmt::Assign {
                    name: n.clone(),
                    name_span: nspan.clone(),
                    value: r,
                    span: nspan.clone(),
                });
                out.push(TsStmt::If {
                    cond: TsExpr::Var(n.clone(), nspan.clone()),
                    then_body: guarded,
                    else_body: Vec::new(),
                    span: nspan.clone(),
                });
                Ok(TsExpr::Var(n, nspan))
            }
            TsExpr::Bin(BinOp::Or, l, r, span) => {
                let l = self.expr(*l, out)?;
                let (n, nspan) = self.fresh(&span);
                out.push(TsStmt::Let {
                    name: n.clone(),
                    name_span: nspan.clone(),
                    decl_let: true,
                    ann: Some(TsTypeAnn {
                        name: "boolean".to_string(),
                        span: nspan.clone(),
                    }),
                    value: l,
                    span: nspan.clone(),
                });
                // RHS only when LHS is false.
                let mut guarded = Vec::new();
                let r = self.expr(*r, &mut guarded)?;
                guarded.push(TsStmt::Assign {
                    name: n.clone(),
                    name_span: nspan.clone(),
                    value: r,
                    span: nspan.clone(),
                });
                out.push(TsStmt::If {
                    cond: TsExpr::Var(n.clone(), nspan.clone()),
                    then_body: Vec::new(),
                    else_body: guarded,
                    span: nspan.clone(),
                });
                Ok(TsExpr::Var(n, nspan))
            }
            TsExpr::Bin(op, l, r, span) => {
                let l = self.expr(*l, out)?;
                let r = self.expr(*r, out)?;
                Ok(TsExpr::Bin(op, Box::new(l), Box::new(r), span))
            }
            TsExpr::Unary(op, x, span) => {
                let x = self.expr(*x, out)?;
                Ok(TsExpr::Unary(op, Box::new(x), span))
            }
            TsExpr::Field(recv, f, span) => {
                let recv = self.expr(*recv, out)?;
                Ok(TsExpr::Field(Box::new(recv), f, span))
            }
            TsExpr::Call(name, args, span) => {
                let mut new_args = Vec::with_capacity(args.len());
                for a in args {
                    new_args.push(self.expr(a, out)?);
                }
                Ok(TsExpr::Call(name, new_args, span))
            }
            TsExpr::Object(fields, span) => {
                let mut new_fields = Vec::with_capacity(fields.len());
                for (fname, fspan, v) in fields {
                    new_fields.push((fname, fspan, self.expr(v, out)?));
                }
                Ok(TsExpr::Object(new_fields, span))
            }
            leaf @ (TsExpr::Int(..) | TsExpr::Bool(..) | TsExpr::Var(..)) => Ok(leaf),
        }
    }
}

fn contains_logical(e: &TsExpr) -> bool {
    match e {
        TsExpr::Bin(BinOp::And | BinOp::Or, _, _, _) => true,
        TsExpr::Bin(_, l, r, _) => contains_logical(l) || contains_logical(r),
        TsExpr::Unary(_, x, _) => contains_logical(x),
        TsExpr::Field(r, _, _) => contains_logical(r),
        TsExpr::Call(_, args, _) => args.iter().any(contains_logical),
        TsExpr::Object(fields, _) => fields.iter().any(|(_, _, v)| contains_logical(v)),
        TsExpr::Int(..) | TsExpr::Bool(..) | TsExpr::Var(..) => false,
    }
}
