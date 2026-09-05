//! Post-check normalization for Solidity enum, bool-map, and narrow-integer forms.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use super::super::parser::{AssignOp, BinOp, Enum, Expr, Program, Stmt, Struct, TypeRef};
use super::{SolTy, TyPos, arith_result_ty, infer, pow2_decimal, resolve_ty, struct_field_ty};
use crate::{FrontendDiag, codes};

/// Which width-trap helpers the lowering produced (emit defines ONLY these, so a contract
/// using no narrow arithmetic stays byte-identical — EX-9).
#[derive(Default, Clone, Copy)]
pub(crate) struct UintnHelpers {
    pub add: bool,
    pub mul: bool,
}

/// SOL-ENUM M2 — the enum-member LOWERING. Runs AFTER `check` (so every `EnumName.Member`
/// node is type-validated) and BEFORE `lower_uintn_arith` (which then sees only `Num`s).
/// Rewrites every `EnumName.Member` → the member's 0-based index literal (EX-1, ONE source of
/// truth via `position()`), where `EnumName` is a known enum NOT shadowed by an in-scope
/// binding (EX-8 — mirrors `check`'s `name ∉ tys` intercept guard). A member not in the enum
/// → FE466 (defense in depth with the `infer` intercept — EX-3). Mirrors `lower_stmts`' scope
/// tracking (state + params + accumulated locals, per-branch clones); NO `_ =>` catch-all on
/// the Stmt walk so a future Expr-bearing `Stmt` cannot silently skip lowering (EX-7).
pub(in crate::solidity) fn lower_enum_members(p: &mut Program) -> Result<(), FrontendDiag> {
    let contract = &mut p.contract;
    let enums = &contract.enums;
    // EX-10: a contract with no enum takes the byte-identical existing path (no-op).
    if enums.is_empty() {
        return Ok(());
    }
    let base: HashSet<String> = contract.state.iter().map(|s| s.name.clone()).collect();
    for f in &mut contract.functions {
        let mut scope = base.clone();
        for prm in &f.params {
            scope.insert(prm.name.clone());
        }
        lower_enum_stmts(&mut f.body, &mut scope, enums)?;
    }
    if let Some(ctor) = &mut contract.constructor {
        let mut scope = base.clone();
        for prm in &ctor.params {
            scope.insert(prm.name.clone());
        }
        lower_enum_stmts(&mut ctor.body, &mut scope, enums)?;
    }
    Ok(())
}

/// Walk a statement list, rewriting enum-member accesses in every `Expr` operand (mirrors
/// `lower_stmts`' LocalVar inserts + per-branch scope clones). NO `_ =>` catch-all (EX-7).
fn lower_enum_stmts(
    stmts: &mut [Stmt],
    scope: &mut HashSet<String>,
    enums: &[Enum],
) -> Result<(), FrontendDiag> {
    for s in stmts.iter_mut() {
        match s {
            Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => {
                rewrite_enum_expr(cond, scope, enums)?
            }
            Stmt::Return { value: Some(v), .. } => rewrite_enum_expr(v, scope, enums)?,
            Stmt::Return { value: None, .. } | Stmt::Revert { .. } => {}
            // SOL-CALLS: unreachable post-check (check_stmts FE500s a residual CallStmt before this
            // pass runs); no-op keeps the match exhaustive.
            Stmt::CallStmt { .. } => {}
            Stmt::LocalVar { name, value, .. } => {
                rewrite_enum_expr(value, scope, enums)?;
                scope.insert(name.clone());
            }
            Stmt::Assign { value, .. } => rewrite_enum_expr(value, scope, enums)?,
            Stmt::FieldAssign { value, .. } => rewrite_enum_expr(value, scope, enums)?,
            Stmt::IndexAssign { key, value, .. } => {
                rewrite_enum_expr(key, scope, enums)?;
                rewrite_enum_expr(value, scope, enums)?;
            }
            Stmt::IndexAssign2 { k1, k2, value, .. } => {
                rewrite_enum_expr(k1, scope, enums)?;
                rewrite_enum_expr(k2, scope, enums)?;
                rewrite_enum_expr(value, scope, enums)?;
            }
            Stmt::MapTransfer {
                from, to, amount, ..
            } => {
                rewrite_enum_expr(from, scope, enums)?;
                rewrite_enum_expr(to, scope, enums)?;
                rewrite_enum_expr(amount, scope, enums)?;
            }
            Stmt::Erc20TransferFrom {
                from,
                spender,
                to,
                amount,
                ..
            } => {
                rewrite_enum_expr(from, scope, enums)?;
                rewrite_enum_expr(spender, scope, enums)?;
                rewrite_enum_expr(to, scope, enums)?;
                rewrite_enum_expr(amount, scope, enums)?;
            }
            Stmt::MapSplitTransfer {
                from,
                amount,
                to,
                net,
                fee_to,
                fee,
                ..
            } => {
                rewrite_enum_expr(from, scope, enums)?;
                rewrite_enum_expr(amount, scope, enums)?;
                rewrite_enum_expr(to, scope, enums)?;
                rewrite_enum_expr(net, scope, enums)?;
                rewrite_enum_expr(fee_to, scope, enums)?;
                rewrite_enum_expr(fee, scope, enums)?;
            }
            Stmt::Erc20Update {
                from, to, value, ..
            } => {
                rewrite_enum_expr(from, scope, enums)?;
                rewrite_enum_expr(to, scope, enums)?;
                rewrite_enum_expr(value, scope, enums)?;
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                rewrite_enum_expr(cond, scope, enums)?;
                let mut t_scope = scope.clone();
                lower_enum_stmts(then_body, &mut t_scope, enums)?;
                let mut e_scope = scope.clone();
                lower_enum_stmts(else_body, &mut e_scope, enums)?;
            }
            // SOL-MULTIMAP: recurse into the batch's nested transfer + deferred writes so an enum member
            // in a key/operand is lowered (the values are hoisted `Var`s, but keys/operands may carry one).
            Stmt::ReservedBatch {
                transfer, writes, ..
            } => {
                if let Some(t) = transfer {
                    lower_enum_stmts(std::slice::from_mut(t.as_mut()), scope, enums)?;
                }
                lower_enum_stmts(writes, scope, enums)?;
            }
            // SOL-AIRDROP: the folded N-ary airdrop — lower an enum member in its `from` operand
            // (mirrors Erc20Update).
            Stmt::BatchTransfer { from, .. } => rewrite_enum_expr(from, scope, enums)?,
            // SOL-AIRDROP: `recognize_airdrop` folds every loop and check FE500s any residual, so
            // one cannot reach this post-check pass; no-op (the CallStmt/Placeholder precedent).
            Stmt::AirdropLoop { .. } => {}
            Stmt::Unchecked { .. } | Stmt::Placeholder { .. } => {}
        }
    }
    Ok(())
}

/// Rewrite enum-member accesses within an expression. The Member arm REWRITES an unshadowed
/// `EnumName.Member` to its index `Num` (EX-7/MC-1 — it does NOT merely recurse like
/// `elaborate`'s Member arm, which would leave every enum access in place); any other Member
/// (a struct-field access, or a name shadowed by a local) recurses the base. NO `_ =>`
/// catch-all so a new `Expr` variant is a compile error, never a silent skip.
fn rewrite_enum_expr(
    e: &mut Expr,
    scope: &HashSet<String>,
    enums: &[Enum],
) -> Result<(), FrontendDiag> {
    match e {
        Expr::Member(base, member, span) => {
            if let Expr::Var(name, _) = base.as_ref()
                && !scope.contains(name)
                && let Some(edef) = enums.iter().find(|en| en.name == *name)
            {
                let Some(idx) = edef
                    .members
                    .iter()
                    .position(|m| m.as_str() == member.as_str())
                else {
                    return Err(FrontendDiag::new(
                        codes::FE466_BAD_ENUM_MEMBER_SOL,
                        format!("`{name}.{member}` — `{member}` is not a member of enum `{name}`"),
                        span.clone(),
                    ));
                };
                *e = Expr::Num(idx.to_string(), span.clone());
                return Ok(());
            }
            rewrite_enum_expr(base, scope, enums)
        }
        Expr::Bin(_, l, r, _) => {
            rewrite_enum_expr(l, scope, enums)?;
            rewrite_enum_expr(r, scope, enums)
        }
        Expr::Call(_, args, _) => {
            for a in args.iter_mut() {
                rewrite_enum_expr(a, scope, enums)?;
            }
            Ok(())
        }
        Expr::Index(b, k, _) => {
            rewrite_enum_expr(b, scope, enums)?;
            rewrite_enum_expr(k, scope, enums)
        }
        Expr::Unary(_, inner, _) => rewrite_enum_expr(inner, scope, enums),
        Expr::Num(..) | Expr::Bool(..) | Expr::Var(..) => Ok(()),
    }
}

/// SOL-ACCESS PR3 — the bool-valued-map LOWERING. Runs AFTER `check` (every write value
/// is a type-validated `true`/`false` LITERAL — the check-side EX-4 gate; every read is
/// type-validated Bool) and BEFORE `lower_uintn_arith`. Storage is the SAME u256 bounded
/// map; this pass fixes the value representation to the CANONICAL 0/1 (EX-4, MC-6 — no
/// lax truthiness can exist because the ONLY writers are the rewritten literals):
///   - a write `m[k] = true|false`  → `m[k] = 1|0` (the plain u256 insert emit already handles);
///   - a read  `m[k]` / `m[k1][k2]` → `(<read> == 1)` (a SIGIL bool — `get_or` default 0 ≡ false,
///     Solidity's mapping default).
///
/// Emit stays type-blind (the rewritten AST is plain u256 map ops + comparisons). A map
/// name that PASSED check as an `Index` base is necessarily the state map (locals/params
/// cannot be mapping-typed), so no scope tracking is needed — unlike the enum pass. NO
/// `_ =>` catch-all on the Stmt walk (the EX-7 walker-totality discipline).
pub(in crate::solidity) fn lower_bool_maps(p: &mut Program) -> Result<(), FrontendDiag> {
    let contract = &mut p.contract;
    // The bool-valued map name sets, from the DECLARED TypeRefs: 1-key `mapping(K=>bool)`
    // and the 2-key AccessControl `hasRole` shape `mapping(K=>mapping(A=>bool))`.
    let mut bool1: HashSet<String> = HashSet::new();
    let mut bool2: HashSet<String> = HashSet::new();
    for sv in &contract.state {
        if let TypeRef::Mapping { value, .. } = &sv.ty {
            match value.as_ref() {
                TypeRef::Scalar { name, .. } if name == "bool" => {
                    bool1.insert(sv.name.clone());
                }
                TypeRef::Mapping { value: iv, .. } if matches!(iv.as_ref(), TypeRef::Scalar { name, .. } if name == "bool") =>
                {
                    bool2.insert(sv.name.clone());
                }
                _ => {}
            }
        }
    }
    // No bool-valued map → the byte-identical existing path (no-op).
    if bool1.is_empty() && bool2.is_empty() {
        return Ok(());
    }
    for f in &mut contract.functions {
        lower_bool_stmts(&mut f.body, &bool1, &bool2)?;
    }
    if let Some(ctor) = &mut contract.constructor {
        lower_bool_stmts(&mut ctor.body, &bool1, &bool2)?;
    }
    Ok(())
}

/// Walk a statement list, rewriting bool-map WRITES (literal → 0/1) and bool-map READS
/// (wrap `== 1`) in every `Expr` operand. Mirrors `lower_enum_stmts`' arm set exactly;
/// NO `_ =>` catch-all (EX-7).
fn lower_bool_stmts(
    stmts: &mut [Stmt],
    bool1: &HashSet<String>,
    bool2: &HashSet<String>,
) -> Result<(), FrontendDiag> {
    for s in stmts.iter_mut() {
        match s {
            Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => {
                rewrite_bool_read(cond, bool1, bool2)
            }
            Stmt::Return { value: Some(v), .. } => rewrite_bool_read(v, bool1, bool2),
            Stmt::Return { value: None, .. } | Stmt::Revert { .. } => {}
            // Unreachable post-check (a residual CallStmt is FE500 there); keeps the match total.
            Stmt::CallStmt { .. } => {}
            Stmt::LocalVar { value, .. } => rewrite_bool_read(value, bool1, bool2),
            Stmt::Assign { value, .. } => rewrite_bool_read(value, bool1, bool2),
            Stmt::FieldAssign { value, .. } => rewrite_bool_read(value, bool1, bool2),
            Stmt::IndexAssign {
                map, key, value, ..
            } => {
                rewrite_bool_read(key, bool1, bool2);
                if bool1.contains(map) {
                    lower_bool_write_value(value)?;
                } else {
                    rewrite_bool_read(value, bool1, bool2);
                }
            }
            Stmt::IndexAssign2 {
                map, k1, k2, value, ..
            } => {
                rewrite_bool_read(k1, bool1, bool2);
                rewrite_bool_read(k2, bool1, bool2);
                if bool2.contains(map) {
                    lower_bool_write_value(value)?;
                } else {
                    rewrite_bool_read(value, bool1, bool2);
                }
            }
            Stmt::MapTransfer {
                from, to, amount, ..
            } => {
                rewrite_bool_read(from, bool1, bool2);
                rewrite_bool_read(to, bool1, bool2);
                rewrite_bool_read(amount, bool1, bool2);
            }
            Stmt::Erc20TransferFrom {
                from,
                spender,
                to,
                amount,
                ..
            } => {
                rewrite_bool_read(from, bool1, bool2);
                rewrite_bool_read(spender, bool1, bool2);
                rewrite_bool_read(to, bool1, bool2);
                rewrite_bool_read(amount, bool1, bool2);
            }
            Stmt::MapSplitTransfer {
                from,
                amount,
                to,
                net,
                fee_to,
                fee,
                ..
            } => {
                rewrite_bool_read(from, bool1, bool2);
                rewrite_bool_read(amount, bool1, bool2);
                rewrite_bool_read(to, bool1, bool2);
                rewrite_bool_read(net, bool1, bool2);
                rewrite_bool_read(fee_to, bool1, bool2);
                rewrite_bool_read(fee, bool1, bool2);
            }
            Stmt::Erc20Update {
                from, to, value, ..
            } => {
                rewrite_bool_read(from, bool1, bool2);
                rewrite_bool_read(to, bool1, bool2);
                rewrite_bool_read(value, bool1, bool2);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                rewrite_bool_read(cond, bool1, bool2);
                lower_bool_stmts(then_body, bool1, bool2)?;
                lower_bool_stmts(else_body, bool1, bool2)?;
            }
            Stmt::ReservedBatch {
                transfer, writes, ..
            } => {
                if let Some(t) = transfer {
                    lower_bool_stmts(std::slice::from_mut(t.as_mut()), bool1, bool2)?;
                }
                lower_bool_stmts(writes, bool1, bool2)?;
            }
            // SOL-AIRDROP: recurse the folded airdrop's `from` operand (mirrors Erc20Update).
            Stmt::BatchTransfer { from, .. } => rewrite_bool_read(from, bool1, bool2),
            // SOL-AIRDROP: folded/rejected before this post-check pass; no-op (CallStmt precedent).
            Stmt::AirdropLoop { .. } => {}
            Stmt::Unchecked { .. } | Stmt::Placeholder { .. } => {}
        }
    }
    Ok(())
}

/// A bool-map write's value: the check gate guaranteed a `true`/`false` LITERAL, so a
/// non-literal here is a translator bug (FE500), never a user-facing reject.
fn lower_bool_write_value(value: &mut Expr) -> Result<(), FrontendDiag> {
    match value {
        Expr::Bool(b, span) => {
            *value = Expr::Num(if *b { "1" } else { "0" }.to_string(), span.clone());
            Ok(())
        }
        other => Err(FrontendDiag::new(
            codes::FE500_INTERNAL_MALFORMED_SOL,
            "internal: a bool-valued mapping write survived check with a non-literal value",
            other.span(),
        )),
    }
}

/// Rewrite bool-map READS bottom-up: children first, then wrap THIS node if it is a
/// complete bool-map read — `m[k]` (m 1-key bool-valued) or `m[k1][k2]` (m 2-key
/// bool-valued) — as `(<read> == 1)`. Bottom-up + single pass ⇒ the freshly-built `Bin`
/// is never revisited. A PARTIAL index of a 2-key map never passes check, and `bool1`/
/// `bool2` are disjoint (one declared type per state var), so the inner `Index` of a
/// 2-key read is never wrapped by the child recursion. NO `_ =>` catch-all.
fn rewrite_bool_read(e: &mut Expr, bool1: &HashSet<String>, bool2: &HashSet<String>) {
    match e {
        Expr::Unary(_, inner, _) => rewrite_bool_read(inner, bool1, bool2),
        Expr::Bin(_, l, r, _) => {
            rewrite_bool_read(l, bool1, bool2);
            rewrite_bool_read(r, bool1, bool2);
        }
        Expr::Member(base, _, _) => rewrite_bool_read(base, bool1, bool2),
        Expr::Call(_, args, _) => {
            for a in args.iter_mut() {
                rewrite_bool_read(a, bool1, bool2);
            }
        }
        Expr::Index(base, key, _) => {
            rewrite_bool_read(base, bool1, bool2);
            rewrite_bool_read(key, bool1, bool2);
        }
        Expr::Num(..) | Expr::Bool(..) | Expr::Var(..) => {}
    }
    let is_bool_read = match e {
        Expr::Index(base, _, _) => match base.as_ref() {
            Expr::Var(m, _) => bool1.contains(m),
            Expr::Index(inner, _, _) => {
                matches!(inner.as_ref(), Expr::Var(m, _) if bool2.contains(m))
            }
            _ => false,
        },
        _ => false,
    };
    if is_bool_read {
        let span = e.span();
        let read = std::mem::replace(e, Expr::Num("0".to_string(), span.clone()));
        *e = Expr::Bin(
            BinOp::Eq,
            Box::new(read),
            Box::new(Expr::Num("1".to_string(), span.clone())),
            span,
        );
    }
}

/// SOL-uintN M2 — the WIDTH-TRAP lowering. Runs AFTER `check` succeeds (so the program is
/// well-typed), rebuilding the SAME per-function type env as `check_function` and mirroring
/// `check_stmts`' if-branch scope clones (EX-8). It rewrites every SAME-WIDTH `uintN` `+`/`*`
/// — in any expression position, plus a `+=`/`*=` compound on a `uintN` scalar/struct-field
/// target — into a checked helper Call `__fe_{add,mul}_checked(l, r, 2^N)` that traps when
/// the result reaches `2^N` (EX-1; the `u256` carrier traps only at `2^256`). `-`/`/`/`%`
/// are width-safe and left as the bare op.
pub(in crate::solidity) fn lower_uintn_arith(p: &mut Program) -> UintnHelpers {
    // Borrow the contract's `structs` (shared) and `functions` (mut) as DISJOINT fields, so
    // the pass can read struct defs while rewriting function bodies without cloning.
    let contract = &mut p.contract;
    let structs = &contract.structs;
    let enums = &contract.enums;
    // Base env = state fields (post-check, `resolve_ty` cannot fail).
    let mut base: HashMap<String, SolTy> = HashMap::new();
    for sv in &contract.state {
        if let Ok(t) = resolve_ty(&sv.ty, TyPos::StateField, structs, enums) {
            base.insert(sv.name.clone(), t);
        }
    }
    let mut h = UintnHelpers::default();
    for f in &mut contract.functions {
        let mut env = base.clone();
        for prm in &f.params {
            if let Ok(t) = resolve_ty(&prm.ty, TyPos::Param, structs, enums) {
                env.insert(prm.name.clone(), t);
            }
        }
        lower_stmts(&mut f.body, &mut env, structs, enums, &mut h);
    }
    // SOL-CTOR: the constructor body is ALSO `uintN` arithmetic that must be width-trapped —
    // it is a separate AST field, so it must be walked explicitly or a `uint128` `+`/`*` in a
    // constructor emits a BARE (un-trapped) op = a silent overflow (the EX-1 failure). Same
    // env shape as a method (state fields + ctor params).
    if let Some(ctor) = &mut contract.constructor {
        let mut env = base.clone();
        for prm in &ctor.params {
            if let Ok(t) = resolve_ty(&prm.ty, TyPos::Param, structs, enums) {
                env.insert(prm.name.clone(), t);
            }
        }
        lower_stmts(&mut ctor.body, &mut env, structs, enums, &mut h);
    }
    h
}

/// Walk a statement list with the type env (mirrors `check_stmts`' LocalVar inserts +
/// if-branch scope clones — EX-8). EVERY `Expr` operand of EVERY variant is elaborated; no
/// `_ =>` catch-all, so a future Expr-bearing `Stmt` cannot silently skip the width-trap.
fn lower_stmts(
    stmts: &mut [Stmt],
    env: &mut HashMap<String, SolTy>,
    structs: &[Struct],
    enums: &[Enum],
    h: &mut UintnHelpers,
) {
    for s in stmts.iter_mut() {
        match s {
            Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => {
                elaborate(cond, env, structs, enums, h)
            }
            Stmt::Return { value: Some(v), .. } => elaborate(v, env, structs, enums, h),
            Stmt::Return { value: None, .. } | Stmt::Revert { .. } => {}
            // SOL-CALLS: unreachable post-check (check_stmts FE500s a residual CallStmt); no-op.
            Stmt::CallStmt { .. } => {}
            Stmt::LocalVar {
                name, ty, value, ..
            } => {
                elaborate(value, env, structs, enums, h);
                if let Ok(t) = resolve_ty(ty, TyPos::Local, structs, enums) {
                    env.insert(name.clone(), t);
                }
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                elaborate(value, env, structs, enums, h);
                let lhs = Expr::Var(target.clone(), value.span());
                rewrite_compound(op, value, env.get(target).cloned(), lhs, h);
            }
            Stmt::FieldAssign {
                obj,
                field,
                op,
                value,
                ..
            } => {
                elaborate(value, env, structs, enums, h);
                let fty = match env.get(obj) {
                    Some(SolTy::Named(sname)) => struct_field_ty(structs, enums, sname, field),
                    _ => None,
                };
                let lhs = Expr::Member(
                    Box::new(Expr::Var(obj.clone(), value.span())),
                    field.clone(),
                    value.span(),
                );
                rewrite_compound(op, value, fty, lhs, h);
            }
            Stmt::IndexAssign { key, value, .. } => {
                elaborate(key, env, structs, enums, h);
                elaborate(value, env, structs, enums, h);
            }
            Stmt::IndexAssign2 { k1, k2, value, .. } => {
                elaborate(k1, env, structs, enums, h);
                elaborate(k2, env, structs, enums, h);
                elaborate(value, env, structs, enums, h);
            }
            Stmt::MapTransfer {
                from, to, amount, ..
            } => {
                elaborate(from, env, structs, enums, h);
                elaborate(to, env, structs, enums, h);
                elaborate(amount, env, structs, enums, h);
            }
            Stmt::MapSplitTransfer {
                from,
                amount,
                to,
                net,
                fee_to,
                fee,
                ..
            } => {
                elaborate(from, env, structs, enums, h);
                elaborate(amount, env, structs, enums, h);
                elaborate(to, env, structs, enums, h);
                elaborate(net, env, structs, enums, h);
                elaborate(fee_to, env, structs, enums, h);
                elaborate(fee, env, structs, enums, h);
            }
            Stmt::Erc20Update {
                from, to, value, ..
            } => {
                elaborate(from, env, structs, enums, h);
                elaborate(to, env, structs, enums, h);
                elaborate(value, env, structs, enums, h);
            }
            Stmt::Erc20TransferFrom {
                from,
                spender,
                to,
                amount,
                ..
            } => {
                elaborate(from, env, structs, enums, h);
                elaborate(spender, env, structs, enums, h);
                elaborate(to, env, structs, enums, h);
                elaborate(amount, env, structs, enums, h);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                elaborate(cond, env, structs, enums, h);
                // Each branch gets its OWN env clone (a branch-local must not leak), exactly
                // like `check_stmts` — else a branch-local `uintN` would get the wrong width.
                let mut t_env = env.clone();
                lower_stmts(then_body, &mut t_env, structs, enums, h);
                let mut e_env = env.clone();
                lower_stmts(else_body, &mut e_env, structs, enums, h);
            }
            // SOL-MULTIMAP: recurse into the batch's nested transfer + deferred writes so a same-width
            // `uintN` op in a key/operand is width-trapped (values are hoisted `Var`s, but keys may carry one).
            Stmt::ReservedBatch {
                transfer, writes, ..
            } => {
                if let Some(t) = transfer {
                    lower_stmts(std::slice::from_mut(t.as_mut()), env, structs, enums, h);
                }
                lower_stmts(writes, env, structs, enums, h);
            }
            // SOL-AIRDROP: elaborate the folded airdrop's `from` operand (mirrors Erc20Update).
            Stmt::BatchTransfer { from, .. } => elaborate(from, env, structs, enums, h),
            // SOL-AIRDROP: folded/rejected before this post-check pass; no-op (CallStmt precedent).
            // (`lower_stmts` returns `()`, so a residual could not FE500 here even if reached.)
            Stmt::AirdropLoop { .. } => {}
            // No `Expr` operand (or never reaches the post-check pass).
            Stmt::Unchecked { .. } | Stmt::Placeholder { .. } => {}
        }
    }
}

/// Recursively rewrite every same-width `uintN` `+`/`*` sub-expression of `e` into the
/// checked helper Call. The node's operand types are computed via `infer` on the ORIGINAL
/// operands (BEFORE the children are rewritten — a rewritten child is a `Call` that `infer`
/// cannot type), so nested `a+b+c` / `f((a+b)*c)` each get their own `2^N` bound.
fn elaborate(
    e: &mut Expr,
    env: &HashMap<String, SolTy>,
    structs: &[Struct],
    enums: &[Enum],
    h: &mut UintnHelpers,
) {
    let rewrite = bin_uintn_rewrite(e, env, structs, enums);
    match e {
        Expr::Bin(_, l, r, _) => {
            elaborate(l, env, structs, enums, h);
            elaborate(r, env, structs, enums, h);
        }
        Expr::Call(_, args, _) => {
            for a in args.iter_mut() {
                elaborate(a, env, structs, enums, h);
            }
        }
        Expr::Index(b, k, _) => {
            elaborate(b, env, structs, enums, h);
            elaborate(k, env, structs, enums, h);
        }
        Expr::Member(b, _, _) => elaborate(b, env, structs, enums, h),
        Expr::Unary(_, inner, _) => elaborate(inner, env, structs, enums, h),
        Expr::Num(..) | Expr::Bool(..) | Expr::Var(..) => {}
    }
    if let Some((helper, n)) = rewrite {
        if helper == "__fe_add_checked" {
            h.add = true;
        } else {
            h.mul = true;
        }
        let span = e.span();
        // Take the (now child-elaborated) Bin out and wrap its operands in the helper.
        if let Expr::Bin(_, l, r, _) = std::mem::replace(e, Expr::Num(String::new(), span.clone()))
        {
            *e = make_checked_call(helper, *l, *r, n, &span);
        }
    }
}

/// If `e` is a same-width `uintN` `+`/`*`, the (helper-name, width) to wrap it in — computed
/// on the ORIGINAL (un-rewritten) operands. `None` otherwise. `infer` cannot fail here (the
/// program type-checked), so a `?`-bail is defensive only.
fn bin_uintn_rewrite(
    e: &Expr,
    env: &HashMap<String, SolTy>,
    structs: &[Struct],
    enums: &[Enum],
) -> Option<(&'static str, u16)> {
    let Expr::Bin(op, l, r, span) = e else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Mul) {
        return None;
    }
    let a = infer(l, env, structs, enums).ok()?;
    let b = infer(r, env, structs, enums).ok()?;
    match arith_result_ty(&a, &b, span.clone()) {
        Ok(SolTy::UintN(n)) => Some((
            if matches!(op, BinOp::Add) {
                "__fe_add_checked"
            } else {
                "__fe_mul_checked"
            },
            n,
        )),
        _ => None,
    }
}

/// Rewrite a `+=`/`*=` compound on a `uintN(n)` target into a plain `=` whose value is
/// `__fe_{add,mul}_checked(lhs, value, 2^n)` (so emit's bare-op expansion is replaced by the
/// trapping call). `-=`/`/=`/`%=` expand to a width-safe bare op and are left unchanged; a
/// non-`uintN` target is left unchanged (the `u256` checked op is already faithful).
fn rewrite_compound(
    op: &mut AssignOp,
    value: &mut Expr,
    target_ty: Option<SolTy>,
    lhs: Expr,
    h: &mut UintnHelpers,
) {
    let n = match (&*op, &target_ty) {
        (AssignOp::Plus | AssignOp::Star, Some(SolTy::UintN(n))) => *n,
        _ => return,
    };
    let helper = if matches!(*op, AssignOp::Plus) {
        h.add = true;
        "__fe_add_checked"
    } else {
        h.mul = true;
        "__fe_mul_checked"
    };
    let span = value.span();
    let rhs = std::mem::replace(value, Expr::Num(String::new(), span.clone()));
    *value = make_checked_call(helper, lhs, rhs, n, &span);
    *op = AssignOp::Eq;
}

/// Build `__fe_{add,mul}_checked(l, r, 2^n)`.
fn make_checked_call(helper: &str, l: Expr, r: Expr, n: u16, span: &Range<usize>) -> Expr {
    Expr::Call(
        Box::new(Expr::Var(helper.to_string(), span.clone())),
        vec![l, r, Expr::Num(pow2_decimal(n), span.clone())],
        span.clone(),
    )
}
