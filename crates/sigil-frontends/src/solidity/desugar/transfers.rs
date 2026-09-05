//! Recognition of canonical atomic transfer and update patterns.

use super::*;

// ── pass 3: recognize the canonical transfer idiom ───────────────────────────

/// Fold the canonical `M[from] -= amount; M[to] += amount;` debit/credit idiom
/// (whether written compound `-=`/`+=` or expanded `M[k] = M[k] - x`) into a single
/// `Stmt::MapTransfer`, lowered to the TRUSTED `M.transfer(from, to, amount)` stdlib
/// method (atomic checks-then-effects, aliasing-correct). ONLY adjacent debit→credit
/// pairs on the SAME map with the SAME amount are folded; anything else is left as-is
/// (a lone second map write stays an `IndexAssign` and is FE412-rejected — fail-closed).
pub(super) fn recognize_transfers(stmts: Vec<Stmt>) -> Vec<Stmt> {
    // Recurse into nested branch bodies first.
    let stmts: Vec<Stmt> = stmts
        .into_iter()
        .map(|s| match s {
            Stmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => Stmt::If {
                cond,
                then_body: recognize_transfers(then_body),
                else_body: recognize_transfers(else_body),
                span,
            },
            other => other,
        })
        .collect();

    let mut out: Vec<Stmt> = Vec::with_capacity(stmts.len());
    // SOL-UNCHECKED Part B: track locals that alias a map slot (`let V = M[k]`) so the OZ
    // local-indirection debit `M[k] = V - x` folds. An alias is live ONLY while every statement
    // since its bind is a pure check; any other statement clears it (EX-B1 — `update_aliases`).
    let mut aliases: std::collections::HashMap<String, (String, Expr)> =
        std::collections::HashMap::new();
    let mut it = stmts.into_iter().peekable();
    while let Some(s) = it.next() {
        let folded = if let Some((map, from, amount)) = as_debit_aliased(&s, &aliases) {
            match it.peek() {
                Some(next) => match as_credit(next) {
                    // Fold ONLY when from/to/amount are free of map reads (no Index) so
                    // their values are stable across the two writes — otherwise the fold
                    // could mis-translate aliasing (the credit would read the pre-debit
                    // value). The unfolded pair then FE412s (fail-closed).
                    Some((map2, to, amount2))
                        if map == map2
                            && expr_eq(amount, amount2)
                            && is_transfer_operand(from)
                            && is_transfer_operand(to)
                            && is_transfer_operand(amount) =>
                    {
                        Some((map.clone(), from.clone(), amount.clone(), stmt_span(&s)))
                    }
                    _ => None,
                },
                None => None,
            }
        } else {
            None
        };
        match folded {
            Some((map, from, amount, dspan)) => {
                let credit = it.next().expect("peeked credit");
                let cspan = stmt_span(&credit);
                let to = as_credit(&credit).expect("re-extract credit").1.clone();
                out.push(Stmt::MapTransfer {
                    map,
                    from,
                    to,
                    amount,
                    span: dspan.start..cspan.end,
                });
                aliases.clear(); // the fold is a write; no alias survives it
            }
            None => {
                update_aliases(&mut aliases, &s);
                out.push(s);
            }
        }
    }
    out
}

/// Alias-table update for `recognize_transfers` Part B (EX-B1). A pure check
/// (`require`/`assert`) leaves aliases intact (it cannot write a slot or rebind a local); a
/// map-read bind `let V = M[k]` clears all aliases then records `V → (M, k)` (opening a fresh
/// window); ANY other statement clears all aliases — a deliberately conservative invalidation
/// that covers an intervening map write, a reassignment of the local OR of a variable in the
/// key, a call, or an `if`. So an alias is live at a debit ONLY when every statement between
/// its bind and the debit is a pure check ⇒ `V == M[k]` provably still holds.
pub(super) fn update_aliases(
    aliases: &mut std::collections::HashMap<String, (String, Expr)>,
    s: &Stmt,
) {
    match s {
        Stmt::Require { .. } | Stmt::Assert { .. } => {} // pure check — aliases preserved
        Stmt::LocalVar {
            name,
            value: Expr::Index(base, key, _),
            ..
        } if matches!(base.as_ref(), Expr::Var(_, _)) => {
            let Expr::Var(mapname, _) = base.as_ref() else {
                unreachable!("guarded by the `if matches!` above")
            };
            aliases.clear();
            aliases.insert(name.clone(), (mapname.clone(), (**key).clone()));
        }
        _ => aliases.clear(),
    }
}

/// Like [`as_debit`], plus the OZ local-indirection form `M[k] = V - x` where the local `V`
/// aliases `M[k]` — recognized ONLY when `aliases[V] == (M, k)` (the alias table guarantees no
/// intervening write since the `let V = M[k]` bind — EX-B1) and the write key `expr_eq`s the
/// aliased key (EX-B2). Returns `(map, key, amount)`, all borrowing `s`.
pub(super) fn as_debit_aliased<'a>(
    s: &'a Stmt,
    aliases: &std::collections::HashMap<String, (String, Expr)>,
) -> Option<(&'a String, &'a Expr, &'a Expr)> {
    if let Some(d) = as_debit(s) {
        return Some(d);
    }
    let Stmt::IndexAssign {
        map,
        key,
        op,
        value,
        ..
    } = s
    else {
        return None;
    };
    if *op != AssignOp::Eq {
        return None;
    }
    let Expr::Bin(BinOp::Sub, l, r, _) = value else {
        return None;
    };
    let Expr::Var(v, _) = l.as_ref() else {
        return None;
    };
    let (amap, akey) = aliases.get(v)?;
    if amap == map && expr_eq(akey, key) {
        return Some((map, key, r));
    }
    None
}

// ── pass 4: recognize the canonical ERC20 transferFrom idiom (SOL-ERC20) ──────

/// Fold the canonical ERC20 `transferFrom` body into a single atomic
/// `Erc20TransferFrom`. After `recognize_transfers`, the body is:
///   require(allowance[from][spender] >= amount);   // optional; left in place (a check)
///   allowance[from][spender] -= amount;            // a two-key `IndexAssign2` debit
///   <balance debit/credit, already folded to> MapTransfer { balances, from, to, amount }
/// The two WRITES (the allowance debit + the balance `MapTransfer`) are folded into one
/// `Erc20TransferFrom` ⇒ the trusted `alw.transfer_from(bal, from, spender, to, amount)`,
/// which the CEI checker treats as ONE atomic op. The fold fires ONLY when the allowance
/// debit is immediately followed by a balance `MapTransfer` with the SAME `from` and
/// `amount` and all operands pure (EX-2); otherwise the pair is left as-is and its two
/// writes are rejected by the CEI gate (FE412) — no non-atomic transferFrom can compile.
pub(super) fn recognize_transfer_from(stmts: Vec<Stmt>) -> Vec<Stmt> {
    // Recurse into nested branch bodies first.
    let stmts: Vec<Stmt> = stmts
        .into_iter()
        .map(|s| match s {
            Stmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => Stmt::If {
                cond,
                then_body: recognize_transfer_from(then_body),
                else_body: recognize_transfer_from(else_body),
                span,
            },
            other => other,
        })
        .collect();

    let mut out: Vec<Stmt> = Vec::with_capacity(stmts.len());
    let mut it = stmts.into_iter().peekable();
    while let Some(s) = it.next() {
        let folded = if let Some((alw, from, spender, amount)) = as_allowance_debit(&s) {
            match it.peek() {
                Some(next) => match as_balance_transfer(next) {
                    // EX-2: the allowance debit's `from`/`amount` must match the balance
                    // transfer's, and every operand must be pure (no Index/Member/Call) so
                    // the folded atomic call cannot mis-translate aliasing.
                    Some((bal, bfrom, to, bamount))
                        if expr_eq(from, bfrom)
                            && expr_eq(amount, bamount)
                            && is_transfer_operand(from)
                            && is_transfer_operand(spender)
                            && is_transfer_operand(to)
                            && is_transfer_operand(amount) =>
                    {
                        Some((
                            bal.clone(),
                            alw.clone(),
                            from.clone(),
                            spender.clone(),
                            to.clone(),
                            amount.clone(),
                            stmt_span(&s),
                        ))
                    }
                    _ => None,
                },
                None => None,
            }
        } else {
            None
        };
        match folded {
            Some((bal_map, alw_map, from, spender, to, amount, dspan)) => {
                let mt = it.next().expect("peeked balance transfer");
                let cspan = stmt_span(&mt);
                out.push(Stmt::Erc20TransferFrom {
                    bal_map,
                    alw_map,
                    from,
                    spender,
                    to,
                    amount,
                    oz5_infinite: false,
                    span: dspan.start..cspan.end,
                });
            }
            None => out.push(s),
        }
    }
    out
}

// ── pass 3b: OZ 5.x transferFrom (`_spendAllowance` + `_transfer`) — SOL-XFILE PR6/AC-2 ──

/// `type(uint256).max` = 2^256 − 1, the infinite-allowance sentinel (`normalize_literals` folds the
/// source `type(uint256).max` to exactly this decimal).
const U256_MAX_DECIMAL: &str =
    "115792089237316195423570985008687907853269984665640564039457584007913129639935";

/// Fold the inlined OZ 5.x `transferFrom` spine into ONE atomic `Erc20TransferFrom { oz5_infinite:
/// true }`. After inlining + `recognize_update`, the shape (with the `__fe_inl*` copies resolved to
/// their roots) is:
///   let CA = _allowances[owner][spender];            // a two-key allowance read
///   if (CA < <2^256-1>) {                            // the INFINITE-allowance dispatch
///       <pure filler + the sufficiency `if (CA < value) revert` + the owner/spender zero-guards>
///       _allowances[owner][spender] = CA - value;    // the allowance decrement (op `=`)
///   }
///   <pure filler + the `_transfer` `if (from==0) revert; if (to==0) revert` guards>
///   Erc20Update { _balances, _totalSupply, from, to, value }   // the balance move
/// with `owner`/`from` sharing a root and every `value` sharing a root. The CA-read + the whole
/// `if (CA<MAX){…}` block are REMOVED (the trusted `erc20_transfer_from` re-establishes the
/// allowance check + decrement + infinite skip); the from/to zero-guards STAY as pure trap-checks
/// before the single atomic op; the `Erc20Update` is REPLACED by the folded transferFrom. The
/// primitive additionally traps on a zero from/to (never mint/burn), so the balance move is a plain
/// non-zero transfer and totalSupply is unchanged (the `ts_field` is dropped — sound because the
/// guards prove from/to ≠ 0, exec-proven by `ec_*`). ANY deviation from this rigid shape → NOT
/// folded → the two committed map writes hit the CEI gate → FE412 (fail-closed).
pub(super) fn recognize_spend_transfer(stmts: Vec<Stmt>) -> Vec<Stmt> {
    // Recurse into branch bodies first (defensive totality; the real shape is a top-level body).
    let stmts: Vec<Stmt> = stmts
        .into_iter()
        .map(|s| match s {
            Stmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => Stmt::If {
                cond,
                then_body: recognize_spend_transfer(then_body),
                else_body: recognize_spend_transfer(else_body),
                span,
            },
            other => other,
        })
        .collect();

    // Resolve the `let x = <Var>;` copy chains to a stable ROOT for cross-position identity checks,
    // and the FULL `let x = <expr>;` def map so a hoisted value-let (`let w = CA - value;`) can be
    // resolved one level when it appears as the allowance-write RHS.
    let mut alias: HashMap<String, String> = HashMap::new();
    collect_copy_aliases(&stmts, &mut alias);
    let mut defs: HashMap<String, Expr> = HashMap::new();
    collect_defs(&stmts, &mut defs);

    let mut out: Vec<Stmt> = Vec::with_capacity(stmts.len());
    let mut i = 0usize;
    while i < stmts.len() {
        if let Some((next, kept, folded)) = try_spend_transfer(&stmts, i, &alias, &defs) {
            out.extend(kept);
            out.push(folded);
            i = next;
        } else {
            out.push(stmts[i].clone());
            i += 1;
        }
    }
    out
}

/// Collect `let x = <Var(src)>;` copies as `x → src` (recursing into `if` branches).
pub(super) fn collect_copy_aliases(stmts: &[Stmt], m: &mut HashMap<String, String>) {
    for s in stmts {
        match s {
            Stmt::LocalVar {
                name,
                value: Expr::Var(src, _),
                ..
            } => {
                m.insert(name.clone(), src.clone());
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_copy_aliases(then_body, m);
                collect_copy_aliases(else_body, m);
            }
            _ => {}
        }
    }
}

/// Collect the FULL `let x = <expr>;` def map (name → its value expr), recursing `if` branches.
pub(super) fn collect_defs(stmts: &[Stmt], m: &mut HashMap<String, Expr>) {
    for s in stmts {
        match s {
            Stmt::LocalVar { name, value, .. } => {
                m.insert(name.clone(), value.clone());
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_defs(then_body, m);
                collect_defs(else_body, m);
            }
            _ => {}
        }
    }
}

/// Follow the copy-alias chain to a ROOT name (bounded to stay total under any accidental cycle).
pub(super) fn alias_root<'a>(name: &'a str, alias: &'a HashMap<String, String>) -> &'a str {
    let mut cur = name;
    for _ in 0..64 {
        match alias.get(cur) {
            Some(next) => cur = next.as_str(),
            None => return cur,
        }
    }
    cur
}

/// Two exprs are the same VALUE iff both are `Var` with the same alias-root.
pub(super) fn same_root(a: &Expr, b: &Expr, alias: &HashMap<String, String>) -> bool {
    match (a, b) {
        (Expr::Var(x, _), Expr::Var(y, _)) => alias_root(x, alias) == alias_root(y, alias),
        _ => false,
    }
}

/// A statement with NO storage-write / control-effect that may sit between the recognized pieces
/// (a pure `let`, a `revert`-guard `if (c) { revert }`, an empty `if`, or the dropped `_;`). A write
/// (`Assign`/`Index*`/`Field*`/an atomic), a `require`/`assert`/`return`, or a `CallStmt` is NOT
/// pure — its presence means the body is not the rigid transferFrom shape → the match bails.
pub(super) fn is_pure_filler(s: &Stmt) -> bool {
    match s {
        Stmt::LocalVar { .. } | Stmt::Revert { .. } | Stmt::Placeholder { .. } => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => then_body.iter().all(is_pure_filler) && else_body.iter().all(is_pure_filler),
        _ => false,
    }
}

/// Try to fold an OZ 5.x transferFrom starting at `stmts[i]`. Returns `(next_index, kept_filler,
/// folded)` on a match: `next_index` is just past the consumed `Erc20Update`; `kept_filler` is the
/// pure filler (the from/to zero-guards + copy-lets) between the `if (CA<MAX)` block and the
/// `Erc20Update`, preserved in place; `folded` is the atomic `Erc20TransferFrom { oz5_infinite:
/// true }` replacing the `Erc20Update`. `None` (fail-closed) on any deviation.
pub(super) fn try_spend_transfer(
    stmts: &[Stmt],
    i: usize,
    alias: &HashMap<String, String>,
    defs: &HashMap<String, Expr>,
) -> Option<(usize, Vec<Stmt>, Stmt)> {
    // (1) `let CA = alw[owner][spender];` — a two-key allowance read into a fresh local.
    let (ca_name, alw_map, owner_e, spender_e) = match stmts.get(i)? {
        Stmt::LocalVar {
            name,
            value: Expr::Index(outer, k2, _),
            ..
        } => match outer.as_ref() {
            Expr::Index(base, k1, _) => match base.as_ref() {
                Expr::Var(map, _) => (name.clone(), map.clone(), (**k1).clone(), (**k2).clone()),
                _ => return None,
            },
            _ => return None,
        },
        _ => return None,
    };
    // Keys must be pure Vars (resolvable to a root, re-emittable).
    if !matches!(owner_e, Expr::Var(..)) || !matches!(spender_e, Expr::Var(..)) {
        return None;
    }

    // (2) `if (CA < <2^256-1>) { … alw[owner][spender] = CA - value … }` (else empty). The block's
    //     internal structure is verified by `match_spend_block`, which returns the `value` operand.
    let value_e = match stmts.get(i + 1)? {
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            if !else_body.is_empty() {
                return None;
            }
            match cond {
                Expr::Bin(BinOp::Lt, l, r, _)
                    if matches!(l.as_ref(), Expr::Var(n, _) if *n == ca_name)
                        && matches!(r.as_ref(), Expr::Num(v, _) if v == U256_MAX_DECIMAL) => {}
                _ => return None,
            }
            match_spend_block(
                then_body, &ca_name, &alw_map, &owner_e, &spender_e, alias, defs,
            )?
        }
        _ => return None,
    };

    // (3) Scan forward over PURE filler (copy-lets + the from/to zero-guards), collecting the KEPT
    //     statements, until the balance `Erc20Update`. Any impure statement → bail.
    let mut kept: Vec<Stmt> = Vec::new();
    let mut j = i + 2;
    loop {
        match stmts.get(j)? {
            Stmt::Erc20Update {
                map: bal_map,
                from,
                to,
                value,
                span,
                ..
            } => {
                // (4) The balance move must match the allowance owner + value, `to` a pure Var.
                if !same_root(from, &owner_e, alias)
                    || !same_root(value, &value_e, alias)
                    || !matches!(to, Expr::Var(..))
                {
                    return None;
                }
                // Fold using RESOLVED ROOTS (all params / the `__fe_sender` param — in scope at emit).
                let root_var = |e: &Expr| -> Expr {
                    match e {
                        Expr::Var(n, sp) => Expr::Var(alias_root(n, alias).to_string(), sp.clone()),
                        other => other.clone(),
                    }
                };
                let folded = Stmt::Erc20TransferFrom {
                    bal_map: bal_map.clone(),
                    alw_map: alw_map.clone(),
                    from: root_var(&owner_e),
                    spender: root_var(&spender_e),
                    to: root_var(to),
                    amount: root_var(value),
                    oz5_infinite: true,
                    span: span.clone(),
                };
                return Some((j + 1, kept, folded));
            }
            s if is_pure_filler(s) => {
                kept.push(s.clone());
                j += 1;
            }
            _ => return None,
        }
    }
}

/// Verify the `if (CA < MAX)` block body: EXACTLY one `_allowances[owner][spender] = CA - value`
/// two-key decrement (op `=`, matching keys), everything else pure filler (the sufficiency
/// `if (CA < value) revert` + the owner/spender zero-guards + copy-lets + the dropped-emit empty
/// `if`). Returns the `value` operand of the decrement. Any second write / unexpected statement →
/// `None` (bail — the block is not the `_spendAllowance`/`_approve` shape).
pub(super) fn match_spend_block(
    then_body: &[Stmt],
    ca_name: &str,
    alw_map: &str,
    owner_e: &Expr,
    spender_e: &Expr,
    alias: &HashMap<String, String>,
    defs: &HashMap<String, Expr>,
) -> Option<Expr> {
    let mut value_e: Option<Expr> = None;
    for s in then_body {
        match s {
            Stmt::IndexAssign2 {
                map,
                k1,
                k2,
                op: AssignOp::Eq,
                value,
                ..
            } if map == alw_map
                && same_root(k1, owner_e, alias)
                && same_root(k2, spender_e, alias) =>
            {
                // The RHS is `CA - <amount>`, either inline or (post-hoist) a `Var` bound to it —
                // resolve one level through `defs` before matching.
                let rhs: &Expr = match value {
                    Expr::Var(x, _) => defs.get(x).unwrap_or(value),
                    other => other,
                };
                match rhs {
                    Expr::Bin(BinOp::Sub, l, r, _)
                        if matches!(l.as_ref(), Expr::Var(n, _)
                            if alias_root(n, alias) == alias_root(ca_name, alias)) =>
                    {
                        if value_e.is_some() {
                            return None; // two allowance writes → not the shape
                        }
                        value_e = Some((**r).clone());
                    }
                    _ => return None,
                }
            }
            _ if is_pure_filler(s) => {}
            _ => return None, // any other write / impure statement → bail
        }
    }
    value_e
}

// ── pass 4a2: N-ary atomic airdrop (SOL-AIRDROP Rung C) ───────────────────────

/// Fold every `Stmt::AirdropLoop` (the parser's rigid `for (uint i; i<recipients.length; ++i) {
/// M[from] -= amounts[i]; M[recipients[i]] += amounts[i]; }`, post-inline/lower_sender) into ONE
/// `Stmt::BatchTransfer` (the trusted `M.batch_transfer(from, recipients, amounts)` — debit `from`
/// by each amount, credit each recipient, reserve-all-then-write, aliasing-correct over N). Runs
/// AFTER `recognize_transfers` (which LEAVES the counter-indexed pair unfolded, since
/// `is_transfer_operand` rejects the `Index` operands — Correction A). The exact-shape gate below is
/// the recognizer's SOLE duty (the aliasing lives in the exec-proven primitive); ANY deviation →
/// FE492 (fail-closed), never a mistranslation. A residual `AirdropLoop` reaching `check` → FE500.
pub(super) fn recognize_airdrop(stmts: Vec<Stmt>) -> Result<Vec<Stmt>, FrontendDiag> {
    let mut out = Vec::with_capacity(stmts.len());
    for s in stmts {
        match s {
            Stmt::AirdropLoop {
                idx,
                len_array,
                body,
                span,
            } => out.push(fold_airdrop(&idx, &len_array, &body, span)?),
            // Recurse into `if` branches (an airdrop loop can be nested), like recognize_split.
            Stmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => out.push(Stmt::If {
                cond,
                then_body: recognize_airdrop(then_body)?,
                else_body: recognize_airdrop(else_body)?,
                span,
            }),
            other => out.push(other),
        }
    }
    Ok(out)
}

pub(super) fn fe492(span: &Range<usize>, msg: &str) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE492_AIRDROP_SHAPE_SOL,
        msg.to_string(),
        span.clone(),
    )
}

/// The exact-shape gate: `body == [ M[from] -= amounts[i] ; M[recipients[i]] += amounts[i] ]` on ONE
/// map, with `from` loop-INVARIANT + pure, `recipients` = the loop's `len_array`, and both amounts
/// the SAME `amounts[i]`. On success → `BatchTransfer`; else FE492.
pub(super) fn fold_airdrop(
    idx: &str,
    len_array: &str,
    body: &[Stmt],
    span: Range<usize>,
) -> Result<Stmt, FrontendDiag> {
    // The body is `[ <optional inliner let-prelude> , M[from] -= amt , M[recip] += amt ]`. An
    // inlined `_transfer(msg.sender, recipients[i], amounts[i])` produces a 3-`let` eval-once
    // prelude (`let __fe_inl_from = __fe_sender; let __fe_inl_to = recipients[i]; let __fe_inl_amt
    // = amounts[i];`) then the pair over those bound Vars; a DIRECT `balances[msg.sender] -=
    // amounts[i]; balances[recipients[i]] += amounts[i];` has no prelude. Collect the leading
    // `let`s into a one-level substitution; the LAST two statements must be the debit + credit,
    // whose operands are then RESOLVED through the prelude before the exact-shape gate. Any
    // non-`let` before the pair (a require, a second write) → FE492 (fail-closed).
    if body.len() < 2 {
        return Err(fe492(
            &span,
            "an airdrop loop body must be a `M[from] -= amounts[i];` debit + `M[recipients[i]] += amounts[i];` credit pair (optionally an inlined `_transfer`)",
        ));
    }
    let n = body.len();
    let mut subst: HashMap<&str, &Expr> = HashMap::new();
    for s in &body[..n - 2] {
        match s {
            Stmt::LocalVar { name, value, .. } => {
                subst.insert(name.as_str(), value);
            }
            _ => {
                return Err(fe492(
                    &span,
                    "an airdrop loop body may contain only an inlined `_transfer` let-prelude before its debit/credit pair",
                ));
            }
        }
    }
    // TRANSITIVE resolution of a `Var` bound by the prelude (the inliner binds each call arg
    // eval-once to a `__fe_inl` local, so the debit/credit see those Vars, not the raw args).
    // Follow `Var → Var` chains to the fully-resolved operand, so the loop-invariance /
    // counter-index gates below see the TRUE source expression. This makes the invariance gate
    // SELF-SUFFICIENT: a multi-level launder (`from = f; f = t; t = recipients[i];`) resolves to
    // `recipients[i]` and is rejected as loop-variant HERE (FE492) — not merely fail-closed by
    // the downstream dropped-prelude → unresolved-ref path. The chain is acyclic (source-order
    // `let`s bind fresh names referencing only earlier ones) and bounded by the prelude length;
    // `guard` is a pure backstop. The happy path is unchanged: `__fe_inl_from → __fe_sender`
    // stops at `__fe_sender` (the method param, not a prelude binding).
    let resolve = |e: &Expr| -> Expr {
        let mut cur = e.clone();
        let mut guard = 0usize;
        loop {
            let next = match &cur {
                Expr::Var(x, _) => subst.get(x.as_str()).map(|v| (**v).clone()),
                _ => None,
            };
            match next {
                Some(v) => {
                    cur = v;
                    guard += 1;
                    if guard > n {
                        break;
                    }
                }
                None => break,
            }
        }
        cur
    };
    let (dmap, dkey, damt) = as_debit(&body[n - 2]).ok_or_else(|| {
        fe492(
            &span,
            "the airdrop loop's debit must be `M[from] -= amounts[i];`",
        )
    })?;
    let (cmap, ckey, camt) = as_credit(&body[n - 1]).ok_or_else(|| {
        fe492(
            &span,
            "the airdrop loop's credit must be `M[recipients[i]] += amounts[i];`",
        )
    })?;
    if dmap != cmap {
        return Err(fe492(
            &span,
            "the airdrop debit and credit must write the SAME map",
        ));
    }
    let from = resolve(dkey);
    let recip = resolve(ckey);
    let damt_r = resolve(damt);
    let camt_r = resolve(camt);
    // `from` must be loop-INVARIANT (free of the counter) + pure (`is_transfer_operand` rejects
    // Index/Member/Call — the aliasing-stability guard).
    if !is_transfer_operand(&from) || expr_mentions_var(&from, idx) {
        return Err(fe492(
            &span,
            "the airdrop `from` must be a loop-invariant pure operand (not indexed by the loop counter)",
        ));
    }
    // The credit key must be `recipients[i]` where `recipients` is the loop's own `len_array`.
    let recipients = as_counter_index(&recip, idx).ok_or_else(|| {
        fe492(
            &span,
            "the airdrop recipient must be `recipients[i]` indexed by the loop counter",
        )
    })?;
    if recipients != *len_array {
        return Err(fe492(
            &span,
            "the airdrop loop must iterate the SAME array it credits (`recipients.length` and `recipients[i]`)",
        ));
    }
    // Both amounts must be `amounts[i]` (same array, the loop counter).
    let a_debit = as_counter_index(&damt_r, idx)
        .ok_or_else(|| fe492(&span, "the airdrop debit amount must be `amounts[i]`"))?;
    let a_credit = as_counter_index(&camt_r, idx)
        .ok_or_else(|| fe492(&span, "the airdrop credit amount must be `amounts[i]`"))?;
    if a_debit != a_credit {
        return Err(fe492(
            &span,
            "the airdrop debit and credit must use the SAME `amounts[i]` array",
        ));
    }
    Ok(Stmt::BatchTransfer {
        map: dmap.clone(),
        from,
        recipients,
        amounts: a_debit,
        span,
    })
}

/// If `e` is EXACTLY `Var(arr)[Var(idx)]` (an array indexed by the loop counter), return `arr`.
pub(super) fn as_counter_index(e: &Expr, idx: &str) -> Option<String> {
    if let Expr::Index(base, key, _) = e
        && let (Expr::Var(arr, _), Expr::Var(i, _)) = (base.as_ref(), key.as_ref())
        && i == idx
    {
        return Some(arr.clone());
    }
    None
}

/// Whether `e` mentions the variable `name` anywhere (used to prove `from` is loop-invariant).
pub(super) fn expr_mentions_var(e: &Expr, name: &str) -> bool {
    match e {
        Expr::Var(n, _) => n == name,
        Expr::Bin(_, l, r, _) => expr_mentions_var(l, name) || expr_mentions_var(r, name),
        Expr::Unary(_, inner, _) => expr_mentions_var(inner, name),
        Expr::Index(b, k, _) => expr_mentions_var(b, name) || expr_mentions_var(k, name),
        Expr::Member(b, _, _) => expr_mentions_var(b, name),
        Expr::Call(c, args, _) => {
            expr_mentions_var(c, name) || args.iter().any(|a| expr_mentions_var(a, name))
        }
        _ => false,
    }
}

// ── pass 4b: same-map fee-on-transfer split (SOL-MULTIMAP M-B) ────────────────

/// Fold the canonical fee-on-transfer split `M[from] -= amount; M[to] += net; M[feeTo] += fee;` — a
/// debit + TWO credits on the SAME map, ADJACENT, all operands `is_transfer_operand`-pure — into ONE
/// `Stmt::MapSplitTransfer` (the trusted `M.transfer_split(...)`, aliasing-correct in verified stdlib).
/// Uses a 3-statement lookahead window (a debit needs two following credits). A non-split 3-write shape
/// (≥3 credits, a second debit, cross-map, an impure operand) is NOT folded → its writes hit the CEI
/// gate (FE412), fail-closed. Runs AFTER `recognize_transfers` (a matching-amount `debit;credit` already
/// folded to a `MapTransfer`, so the debit `s0` is only an `IndexAssign` when `net ≠ amount`).
pub(super) fn recognize_split(stmts: Vec<Stmt>) -> Vec<Stmt> {
    let stmts: Vec<Stmt> = stmts
        .into_iter()
        .map(|s| match s {
            Stmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => Stmt::If {
                cond,
                then_body: recognize_split(then_body),
                else_body: recognize_split(else_body),
                span,
            },
            other => other,
        })
        .collect();

    let mut slots: Vec<Option<Stmt>> = stmts.into_iter().map(Some).collect();
    let mut out: Vec<Stmt> = Vec::with_capacity(slots.len());
    let mut i = 0;
    while i < slots.len() {
        let fold = if i + 2 < slots.len() {
            match (&slots[i], &slots[i + 1], &slots[i + 2]) {
                (Some(a), Some(b), Some(c)) => as_split(a, b, c),
                _ => None,
            }
        } else {
            None
        };
        match fold {
            Some((map, from, amount, to, net, feeto, fee, span)) => {
                out.push(Stmt::MapSplitTransfer {
                    map,
                    from,
                    amount,
                    to,
                    net,
                    fee_to: feeto,
                    fee,
                    span,
                });
                slots[i] = None;
                slots[i + 1] = None;
                slots[i + 2] = None;
                i += 3;
            }
            None => {
                out.push(slots[i].take().expect("slot present at index i"));
                i += 1;
            }
        }
    }
    out
}

/// `M[from] -= amount; M[to] += net; M[feeTo] += fee;` (all on the SAME map, pure operands) →
/// `(map, from, amount, to, net, feeTo, fee, span)`. Reuses `as_debit`/`as_credit` + `is_transfer_operand`.
#[allow(clippy::type_complexity)]
pub(super) fn as_split(
    s0: &Stmt,
    s1: &Stmt,
    s2: &Stmt,
) -> Option<(String, Expr, Expr, Expr, Expr, Expr, Expr, Range<usize>)> {
    let (m0, from, amount) = as_debit(s0)?;
    let (m1, to, net) = as_credit(s1)?;
    let (m2, feeto, fee) = as_credit(s2)?;
    if m0 == m1
        && m1 == m2
        && is_transfer_operand(from)
        && is_transfer_operand(amount)
        && is_transfer_operand(to)
        && is_transfer_operand(net)
        && is_transfer_operand(feeto)
        && is_transfer_operand(fee)
    {
        let span = stmt_span(s0).start..stmt_span(s2).end;
        Some((
            m0.clone(),
            from.clone(),
            amount.clone(),
            to.clone(),
            net.clone(),
            feeto.clone(),
            fee.clone(),
            span,
        ))
    } else {
        None
    }
}

// ── pass 2b: OZ 5.x `_update` fold (SOL-UPDATE) ──────────────────────────────

/// Fold the rigid OZ 5.x `_update` zero-address-dispatch pair — post-`normalize_literals`
/// and post-inline, two ADJACENT `if`s:
///   `if (from == 0) { TS += value; } else { <debit M[from] by value> }`
///   `if (to   == 0) { TS -= value; } else { M[to] += value; }`
/// — into ONE atomic `Stmt::Erc20Update` (the trusted `M.erc20_update(TS, from, to, value)`:
/// dynamic mint/burn/transfer dispatch + the `from == to` aliasing live in verified stdlib,
/// exec-proven by the `eu_*` oracle; `M[0]` is never written). Runs FIRST among the folds
/// (before `recognize_transfers`) so the matcher sees the pristine post-ANF shape. EVERY
/// structural slot is pinned (EX-1): the conditions are exactly `<pure operand> == 0`; the
/// then-branches exactly `TS += value` / `TS -= value` on ONE totalSupply target; the
/// else-branches exactly a recognized debit / credit on ONE map keyed by the SAME `from`/`to`
/// with the SAME `value` (every occurrence `expr_eq`; all operands `is_transfer_operand`-pure).
/// ANY deviation → not folded → the branch writes hit the CEI gate → FE412 (fail-closed).
pub(super) fn recognize_update(stmts: Vec<Stmt>) -> Vec<Stmt> {
    let stmts: Vec<Stmt> = stmts
        .into_iter()
        .map(|s| match s {
            Stmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => Stmt::If {
                cond,
                then_body: recognize_update(then_body),
                else_body: recognize_update(else_body),
                span,
            },
            other => other,
        })
        .collect();

    let mut slots: Vec<Option<Stmt>> = stmts.into_iter().map(Some).collect();
    let mut out: Vec<Stmt> = Vec::with_capacity(slots.len());
    let mut i = 0;
    while i < slots.len() {
        let fold = if i + 1 < slots.len() {
            match (&slots[i], &slots[i + 1]) {
                (Some(a), Some(b)) => as_update(a, b),
                _ => None,
            }
        } else {
            None
        };
        match fold {
            Some((map, ts_field, from, to, value, span)) => {
                out.push(Stmt::Erc20Update {
                    map,
                    ts_field,
                    from,
                    to,
                    value,
                    span,
                });
                slots[i] = None;
                slots[i + 1] = None;
                i += 2;
            }
            None => {
                out.push(slots[i].take().expect("slot present at index i"));
                i += 1;
            }
        }
    }
    out
}

/// The `_update` if-pair → `(map, ts_field, from, to, value, span)`, or `None` on ANY
/// structural deviation. The six operand identities: the debit key ≡ `s1.cond`'s `from`, the
/// credit key ≡ `s2.cond`'s `to`, and the four amount occurrences (mint-add, burn-sub, debit,
/// credit) all `expr_eq` one `value`.
#[allow(clippy::type_complexity)]
pub(super) fn as_update(
    s1: &Stmt,
    s2: &Stmt,
) -> Option<(String, String, Expr, Expr, Expr, Range<usize>)> {
    let (
        Stmt::If {
            cond: c1,
            then_body: t1,
            else_body: e1,
            ..
        },
        Stmt::If {
            cond: c2,
            then_body: t2,
            else_body: e2,
            ..
        },
    ) = (s1, s2)
    else {
        return None;
    };
    // The two dispatch conditions: `from == 0` / `to == 0`, pure operands.
    let from = as_eq_zero(c1)?;
    let to = as_eq_zero(c2)?;
    // The two totalSupply deltas: `TS += value` (mint) / `TS -= value` (burn), ONE target.
    let (ts1, v_mint) = as_ts_delta(t1, AssignOp::Plus, BinOp::Add)?;
    let (ts2, v_burn) = as_ts_delta(t2, AssignOp::Minus, BinOp::Sub)?;
    if ts1 != ts2 {
        return None;
    }
    // The debit block (D1 local-indirection + if-revert, or D2 compound) on `M[from]`.
    let (map_d, key_d, v_debit) = as_update_debit(e1)?;
    // The credit: EXACTLY one `M[to] += value` on the SAME map.
    let [credit] = e2.as_slice() else {
        return None;
    };
    let (map_c, key_c, v_credit) = as_credit(credit)?;
    if *map_c != map_d {
        return None;
    }
    // Key identity: the debit writes the slot the MINT test dispatched on, the credit the
    // BURN test's — a mismatched key is a different (unfoldable) program.
    if !expr_eq(&key_d, from) || !expr_eq(key_c, to) {
        return None;
    }
    // Amount identity across all four occurrences, and operand purity (from/to are pure via
    // `as_eq_zero`; the keys are `expr_eq` to them; one purity check covers every `value`).
    if !expr_eq(&v_debit, v_mint) || !expr_eq(v_burn, v_mint) || !expr_eq(v_credit, v_mint) {
        return None;
    }
    if !is_transfer_operand(v_mint) {
        return None;
    }
    let span = stmt_span(s1).start..stmt_span(s2).end;
    Some((
        map_d,
        ts1.clone(),
        from.clone(),
        to.clone(),
        v_mint.clone(),
        span,
    ))
}

/// `<operand> == 0` (post-`normalize_literals`, the zero-address dispatch test) → the
/// operand, which must be `is_transfer_operand`-pure. The literal must be EXACTLY `0`.
pub(super) fn as_eq_zero(cond: &Expr) -> Option<&Expr> {
    let Expr::Bin(BinOp::Eq, l, r, _) = cond else {
        return None;
    };
    let Expr::Num(lit, _) = r.as_ref() else {
        return None;
    };
    if lit != "0" || !is_transfer_operand(l) {
        return None;
    }
    Some(l.as_ref())
}

/// A one-statement `TS op= value` / `TS = TS <bin> value` totalSupply delta (the scalar twin
/// of `sub_add_assign`) → `(target, value)`.
pub(super) fn as_ts_delta(
    body: &[Stmt],
    compound: AssignOp,
    bin: BinOp,
) -> Option<(&String, &Expr)> {
    let [
        Stmt::Assign {
            target, op, value, ..
        },
    ] = body
    else {
        return None;
    };
    if *op == compound {
        return Some((target, value));
    }
    if *op == AssignOp::Eq
        && let Expr::Bin(b, l, r, _) = value
        && *b == bin
        && let Expr::Var(t2, _) = l.as_ref()
        && t2 == target
    {
        return Some((target, r.as_ref()));
    }
    None
}

/// The `_update` debit block (the `from != 0` else-branch) → `(map, key, value)`:
///   D1 — the verbatim OZ 5.x local-indirection + if-revert form:
///     `[ uint256 fb = M[from];  if (fb < value) { revert; }  M[from] = fb - value; ]`
///     (the guard pinned to `Bin(Lt, Var(fb), value)` with an EMPTY else and a bare
///     `revert` — a custom error's args are already dropped at parse);
///   D2 — the bare compound/expanded debit: `[ M[from] -= value ]` (via `as_debit`).
/// A guarded-compound 2-statement block, a `require`-form guard (4.x), or any other shape
/// → `None` (declared anti-goals; the writes then hit the CEI gate → FE412, fail-closed).
pub(super) fn as_update_debit(body: &[Stmt]) -> Option<(String, Expr, Expr)> {
    match body {
        [d] => as_debit(d).map(|(m, k, v)| (m.clone(), k.clone(), v.clone())),
        [
            Stmt::LocalVar {
                name: fb,
                value: bind_v,
                ..
            },
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            },
            w,
        ] => {
            // The bind: `fb = M[k]` (a pure single-level map read).
            let Expr::Index(base, bk, _) = bind_v else {
                return None;
            };
            let Expr::Var(bm, _) = base.as_ref() else {
                return None;
            };
            // The guard: `if (fb < value) { revert; } else { }`.
            let Expr::Bin(BinOp::Lt, gl, gv, _) = cond else {
                return None;
            };
            let Expr::Var(gn, _) = gl.as_ref() else {
                return None;
            };
            if gn != fb || !else_body.is_empty() {
                return None;
            }
            let [Stmt::Revert { .. }] = then_body.as_slice() else {
                return None;
            };
            // The write: `M[k] = fb - value` — SAME map, SAME key, the BOUND local.
            let Stmt::IndexAssign {
                map,
                key,
                op: AssignOp::Eq,
                value,
                ..
            } = w
            else {
                return None;
            };
            let Expr::Bin(BinOp::Sub, wl, wv, _) = value else {
                return None;
            };
            let Expr::Var(wn, _) = wl.as_ref() else {
                return None;
            };
            if wn != fb || bm != map || !expr_eq(bk, key) || !expr_eq(gv, wv) {
                return None;
            }
            Some((map.clone(), key.clone(), wv.as_ref().clone()))
        }
        _ => None,
    }
}
