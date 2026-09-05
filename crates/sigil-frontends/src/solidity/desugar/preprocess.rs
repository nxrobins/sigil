//! Pre-inference normalization, dead-function pruning, and safety gates.

use super::*;

// ── pass -1: unchecked-block unwrap (SOL-UNCHECKED) ──────────────────────────

/// Splice every `unchecked { … }` block's body into its enclosing statement list, over every
/// function, modifier, and constructor body. Called by `translate` AFTER `validate_user_identifiers`
/// (so the alpha-rename below injects no `__fe_unchk` name that identifier validation would see and
/// reject) but BEFORE `recognize_cap_guards` (so no `unchecked` wrapper ever reaches the SOL-CAP
/// security scans — a wrapper hiding a `msg.sender`/owner use there is an authority-widening bypass,
/// adversarial-review F2/F3/F4). SIGIL `u256` arithmetic is always CHECKED (traps on overflow), so
/// removing the wrapper is the whole change — where Solidity WRAPS, SIGIL TRAPS (fail-closed, EX-3).
pub(in crate::solidity) fn unwrap_unchecked(c: &mut Contract) {
    let mut counter: usize = 0;
    for f in &mut c.functions {
        let body = std::mem::take(&mut f.body);
        f.body = unwrap_unchecked_stmts(body, &mut counter);
    }
    for m in &mut c.modifiers {
        let body = std::mem::take(&mut m.body);
        m.body = unwrap_unchecked_stmts(body, &mut counter);
    }
    if let Some(ctor) = &mut c.constructor {
        let body = std::mem::take(&mut ctor.body);
        ctor.body = unwrap_unchecked_stmts(body, &mut counter);
    }
}

/// Recurse a statement list, replacing each `Stmt::Unchecked { body }` with its (recursively
/// unwrapped) body spliced in place, and descending into `if` branches (the only other
/// block-bearing statement in the subset). A block's TOP-LEVEL locals are ALPHA-RENAMED to a fresh
/// `__fe_unchk<N>_` prefix (the inline-splice hygiene pattern — reuse `rename_body`) so that erasing
/// the block boundary can NEITHER leak the local's binding into the enclosing scope NOR let it
/// shadow a same-named state field. (A local nested inside an inner `if` within the block is already
/// block-scoped by that `if`, but `rename_body` renaming it too is harmless — the shadowing is
/// preserved.) Runs after identifier validation, so the injected `__fe_unchk` name is never mistaken
/// for — nor collides with — a user identifier (`__fe_` is a reserved prefix, FE420).
pub(super) fn unwrap_unchecked_stmts(stmts: Vec<Stmt>, counter: &mut usize) -> Vec<Stmt> {
    let mut out = Vec::with_capacity(stmts.len());
    for s in stmts {
        match s {
            Stmt::Unchecked { body, .. } => {
                let names: HashSet<String> = body
                    .iter()
                    .filter_map(|st| match st {
                        Stmt::LocalVar { name, .. } => Some(name.clone()),
                        _ => None,
                    })
                    .collect();
                let body = if names.is_empty() {
                    body
                } else {
                    let prefix = format!("__fe_unchk{counter}_");
                    *counter += 1;
                    rename_body(body, &names, &prefix)
                };
                out.extend(unwrap_unchecked_stmts(body, counter));
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => out.push(Stmt::If {
                cond,
                then_body: unwrap_unchecked_stmts(then_body, counter),
                else_body: unwrap_unchecked_stmts(else_body, counter),
                span,
            }),
            other => out.push(other),
        }
    }
    out
}

// ── pass -1b: literal normalization — `address(0)` + `type(uint256).max` (SOL-UPDATE / SOL-XFILE) ─

/// Rewrite every EXACT `address(0)` cast — `Call(Var("address"), [Num("0")])` — to the numeric
/// literal `0`, over every function and modifier body (NOT the constructor: the ctor path runs no
/// recognizers and constructor initial-mint is a declared SOL-UPDATE anti-goal, so a ctor
/// `address(0)` keeps failing loudly at FE401 rather than half-translating). Sound: `address` is
/// the u256 carrier and the zero address IS the u256 zero — `require_eq_compatible` and
/// `require_assignable` both already accept a 160-bit-fitting numeric literal against `address`
/// (NC-L3c), so the rewritten forms type-check with no checker change. This makes the OZ 5.x
/// zero-address idioms compile: the leading guards (`if (x == address(0)) revert;` →
/// `if (x == 0) { trap }` — the revert-on-zero is PRESERVED; deleting the guard would silently
/// turn a transfer-to-zero into a burn), the inline param binds (`let __fe_inlN_from =
/// address(0)` → `= 0`), and the `_update` dispatch conditions that `recognize_update` matches.
/// Called by `translate` right after `unwrap_unchecked`: a pure LEAF rewrite — erases no
/// statement, injects no identifier — so the SOL-CAP scans downstream see everything they saw
/// before, and the `__fe_inl_*` binds created later by `inline_internal_calls` clone
/// already-normalized args. The rewrite is bottom-up, so the degenerate nested spelling
/// `address(address(0))` also collapses to `0`. Any OTHER `address(<expr>)` cast — including
/// alternative zero spellings like `address(0x0)` — is left intact for check to reject (FE401),
/// fail-closed.
///
/// SOL-XFILE PR5/L4: this pass ALSO normalizes the OZ `_spendAllowance` infinite-allowance literal
/// `type(uint256).max` / `type(uint).max` — `Member(Call(Var("type"), [Var("uint256")]), "max")` —
/// to the u256-max decimal `2^256 − 1` (computed, never transcribed). Only that EXACT shape is
/// rewritten; any other `type(...)` or `.max` stays intact for check to reject (FE401), fail-closed.
/// (The pass now normalizes two literal idioms; the `naz_*` helper names are historical.)
pub(in crate::solidity) fn normalize_literals(c: &mut Contract) {
    for f in &mut c.functions {
        for s in &mut f.body {
            naz_stmt(s);
        }
    }
    for m in &mut c.modifiers {
        for s in &mut m.body {
            naz_stmt(s);
        }
    }
}

/// Total over EVERY `Stmt` variant — including the recognizer-produced atomics that cannot exist
/// this early (created by later desugar passes): their operand exprs are recursed anyway so the
/// pass stays total under any future pipeline reorder (the walker-arm bug class).
pub(super) fn naz_stmt(s: &mut Stmt) {
    match s {
        Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => naz_expr(cond),
        Stmt::Revert { .. } | Stmt::Placeholder { .. } => {}
        Stmt::Assign { value, .. } => naz_expr(value),
        Stmt::IndexAssign { key, value, .. } => {
            naz_expr(key);
            naz_expr(value);
        }
        Stmt::IndexAssign2 { k1, k2, value, .. } => {
            naz_expr(k1);
            naz_expr(k2);
            naz_expr(value);
        }
        Stmt::FieldAssign { value, .. } => naz_expr(value),
        Stmt::LocalVar { value, .. } => naz_expr(value),
        Stmt::Return { value, .. } => {
            if let Some(v) = value {
                naz_expr(v);
            }
        }
        Stmt::CallStmt { args, .. } => {
            for a in args.iter_mut() {
                naz_expr(a);
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            naz_expr(cond);
            for t in then_body.iter_mut() {
                naz_stmt(t);
            }
            for t in else_body.iter_mut() {
                naz_stmt(t);
            }
        }
        Stmt::Unchecked { body, .. } => {
            for t in body.iter_mut() {
                naz_stmt(t);
            }
        }
        Stmt::MapTransfer {
            from, to, amount, ..
        } => {
            naz_expr(from);
            naz_expr(to);
            naz_expr(amount);
        }
        Stmt::Erc20TransferFrom {
            from,
            spender,
            to,
            amount,
            ..
        } => {
            naz_expr(from);
            naz_expr(spender);
            naz_expr(to);
            naz_expr(amount);
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
            naz_expr(from);
            naz_expr(amount);
            naz_expr(to);
            naz_expr(net);
            naz_expr(fee_to);
            naz_expr(fee);
        }
        Stmt::ReservedBatch {
            transfer, writes, ..
        } => {
            if let Some(t) = transfer {
                naz_stmt(t);
            }
            for w in writes.iter_mut() {
                naz_stmt(w);
            }
        }
        Stmt::Erc20Update {
            from, to, value, ..
        } => {
            naz_expr(from);
            naz_expr(to);
            naz_expr(value);
        }
        // SOL-AIRDROP: the raw airdrop loop exists at this pre-desugar pass — recurse its
        // body so `address(0)`/`type(uint).max` normalization reaches the loop body.
        Stmt::AirdropLoop { body, .. } => {
            for w in body.iter_mut() {
                naz_stmt(w);
            }
        }
        // BatchTransfer is produced later by `recognize_airdrop`; `from` is its only Expr.
        Stmt::BatchTransfer { from, .. } => {
            naz_expr(from);
        }
    }
}

/// Bottom-up: rewrite children first, then replace the node itself if it is EXACTLY
/// `Call(Var("address"), [Num("0")])`. `address` is a reserved type name (never a user
/// identifier), so the match is unambiguous.
pub(super) fn naz_expr(e: &mut Expr) {
    match e {
        Expr::Member(base, _, _) => naz_expr(base),
        Expr::Call(callee, args, _) => {
            naz_expr(callee);
            for a in args.iter_mut() {
                naz_expr(a);
            }
        }
        Expr::Index(b, k, _) => {
            naz_expr(b);
            naz_expr(k);
        }
        Expr::Unary(_, x, _) => naz_expr(x),
        Expr::Bin(_, l, r, _) => {
            naz_expr(l);
            naz_expr(r);
        }
        Expr::Num(..) | Expr::Bool(..) | Expr::Var(..) => {}
    }
    if let Expr::Call(callee, args, span) = e
        && matches!(callee.as_ref(), Expr::Var(n, _) if n == "address")
        && args.len() == 1
        && matches!(&args[0], Expr::Num(lit, _) if lit == "0")
    {
        *e = Expr::Num("0".to_string(), span.clone());
    }
    // SOL-XFILE PR5/L4: `type(uint256).max` / `type(uint).max` → the u256-max literal `2^256 − 1`.
    // The bottom-up recursion above left the inner `Call(Var("type"), [Var("uint256")])` untouched
    // (its callee is `type`, not `address`), so we match the whole `Member(…, "max")` here. `type`
    // is a Solidity reserved word (never a user identifier), so the match is unambiguous.
    if let Expr::Member(base, member, span) = e
        && member == "max"
        && let Expr::Call(callee, args, _) = base.as_ref()
        && matches!(callee.as_ref(), Expr::Var(n, _) if n == "type")
        && args.len() == 1
        && matches!(&args[0], Expr::Var(w, _) if w == "uint256" || w == "uint")
    {
        *e = Expr::Num(uint256_max_decimal(), span.clone());
    }
}

/// `type(uint256).max` = 2^256 − 1, as a decimal string COMPUTED (never a transcribed 78-digit
/// magic constant — a single mistyped digit would be a silent value bug, exactly the "compiles but
/// means something different" hazard a security translator exists to avoid). 2^256 ends in 6, so
/// 2^256 − 1 ends in 5 with no borrow.
pub(super) fn uint256_max_decimal() -> String {
    // Base-10 digits, least-significant first; start at 2^0 = 1 and double 256 times → 2^256.
    let mut digits: Vec<u8> = vec![1];
    for _ in 0..256 {
        let mut carry = 0u8;
        for d in digits.iter_mut() {
            let v = *d * 2 + carry; // ≤ 9*2+1 = 19, so carry stays 0/1
            *d = v % 10;
            carry = v / 10;
        }
        if carry > 0 {
            digits.push(carry);
        }
    }
    digits[0] -= 1; // 2^256 ends in 6 ⇒ the −1 touches only the least-significant digit
    digits.iter().rev().map(|d| (b'0' + d) as char).collect()
}

// ── pass 0.5: dead-internal sweep + metadata-getter drop (SOL-XFILE PR5/L4) ──

/// Prune two classes of functions BEFORE the per-function lowering / check / emit — both additive
/// (a raw contract can't reach here without them being dead or FE410) and fail-closed:
///  (a) the DEAD-INTERNAL SWEEP — every `internal`/`private` function with ZERO remaining call
///      sites. `inline_internal_calls` (which ran just before this) splices EVERY call to a contract
///      function and errors on anything it cannot inline, so an internal fn is now call-site-free by
///      construction. Dropping it is MORE faithful than keeping it: internal fns are not part of
///      Solidity's external ABI, but `emit` lowers every surviving function and the trusted compiler
///      forces impl methods `Public` — so a retained internal WIDENS the contract surface. It is also
///      REQUIRED for the OZ closure: `Context._msgData()` (`returns (bytes)`) rides in via the
///      `Context` base, is never called by ERC20, and is a hard FE410 that would block the whole
///      contract. Public / external / (visibility-less) `Default` functions are NEVER swept.
///  (b) the METADATA-GETTER DROP — a PUBLIC function returning the (unrepresentable) `string` type
///      whose body is EXACTLY `return <ident>;` (the OZ `name()`/`symbol()` shape over a string state
///      field dropped at parse). A `string` return is FE410 and the field is gone, so the faithful
///      lowering is nothing.
/// Fail-closed in both directions: a function with a surviving call is KEPT (its residual call still
/// resolves, or fails loud at check/emit); a getter with any fancier body is KEPT (→ FE410).
pub(super) fn prune_functions(c: &mut Contract) {
    // Call-site census over every SURVIVING body (functions + constructor). Post-inline no call to a
    // contract function survives, so this is exact for the real OZ closure; were a residual call ever
    // to survive (a future inliner change), keeping its callee is the conservative (fail-closed)
    // direction — the residual call then fails loud downstream rather than dangling silently.
    let mut called: HashSet<String> = HashSet::new();
    for f in &c.functions {
        collect_callees_stmts(&f.body, &mut called);
    }
    if let Some(ctor) = &c.constructor {
        collect_callees_stmts(&ctor.body, &mut called);
    }
    c.functions.retain(|f| {
        if is_metadata_string_getter(f) || is_erc165_supports_interface(f) {
            return false;
        }
        let dead_internal = matches!(f.visibility, Visibility::Internal | Visibility::Private)
            && !called.contains(&f.name);
        !dead_internal
    });
}

/// The OZ `name()`/`symbol()` shape: PUBLIC, returns the (unrepresentable) `string` type, body is
/// EXACTLY `return <ident>;` over a string state field dropped at parse. Deliberately TIGHT — any
/// other body (a computed string, `string.concat`, extra statements, a non-`Var` return) is not a
/// metadata getter, is not dropped, and stays FE410 (fail-closed).
/// SOL-ACCESS W3: enforce that EVERY function named `_msgSender` is the pure OZ Context
/// shim `return msg.sender;` (no params, no modifiers) — the precondition for
/// `emit_arg_discard_safe` treating a `_msgSender()` emit arg as a droppable pure read. A
/// `_msgSender` with any other body / a modifier / parameters could carry a side effect or
/// guard that a discarded `emit` would silently drop (the "compiles-but-drops-an-effect"
/// existential), so it fails closed (FE481). MUST run BEFORE `disambiguate_overloads` — an
/// OVERLOADED `_msgSender` is renamed to `__fe_ov{arity}__msgSender`, which a literal-name
/// check would skip → a CRITICAL authority bypass (adversarial-review finding: a
/// guard-bearing overloaded `_msgSender` called only in a discarded emit left the method
/// ungated). Checking under the ORIGINAL name catches every overload: the guard-bearing
/// 0-arg one fails the body check, and any non-0-arg sibling fails the param check. Absent
/// `_msgSender` = no-op.
pub(in crate::solidity) fn reject_impure_msgsender(c: &Contract) -> Result<(), FrontendDiag> {
    for f in &c.functions {
        if f.name != "_msgSender" {
            continue;
        }
        // The pure shim has NO params, NO modifiers, and a body of exactly `return
        // msg.sender;`. The `modifiers.is_empty()` clause is load-bearing (adversarial-
        // review finding): a gating modifier on `_msgSender` (`onlyController { require(…);
        // _; }`) attaches a side-effect/guard the body-only check misses — inlined LATER
        // than this guard runs, so its `require` (a revert Solidity would raise when
        // `_msgSender()` is evaluated in a discarded emit) would be silently dropped with
        // the emit, WEAKENING authority. A modifier'd `_msgSender` is not the pure shim.
        let is_shim = f.params.is_empty()
            && f.modifiers.is_empty()
            && matches!(
                f.body.as_slice(),
                [Stmt::Return { value: Some(Expr::Member(base, field, _)), .. }]
                    if matches!(base.as_ref(), Expr::Var(n, _) if n == "msg") && field == "sender"
            );
        if !is_shim {
            return Err(FrontendDiag::new(
                codes::FE481_EMIT_ARG_EFFECTFUL_SOL,
                "`_msgSender` is treated as the pure `msg.sender` shim (so `_msgSender()` is discard-safe inside an `emit`); a `_msgSender` with a modifier, parameters, or any other body could hide a side effect / guard a discarded emit would silently drop — it must be exactly a parameter- and modifier-less `return msg.sender;`",
                f.span.clone(),
            ));
        }
    }
    Ok(())
}

/// SOL-ACCESS W2: the ERC165 introspection drop — a PUBLIC `view`/`pure` function named
/// `supportsInterface` with EXACTLY ONE `bytes4` param returning `bool`. It is pure
/// interface-id introspection over compile-time constants (`type(I).interfaceId ||
/// super.supportsInterface(id)`) — no mutable state, no authority, no funds, and SIGIL has
/// no ERC165/interface-id concept — so the faithful lowering is nothing (the
/// name()/symbol() metadata-drop precedent). Dropping it before check means its
/// out-of-subset body (`super.`, `type(I).interfaceId`, the `bytes4` param) is never
/// type-checked. The `view`/`pure` gate is load-bearing: a NON-view function of that name
/// (which could mutate state / grant authority) does NOT match → stays rejected on its
/// body. If it were somehow called internally, the residual call fails loud downstream
/// (the metadata-getter-drop fail-loud precedent).
pub(super) fn is_erc165_supports_interface(f: &Function) -> bool {
    f.name == "supportsInterface"
        && matches!(f.visibility, Visibility::Public | Visibility::External)
        && matches!(f.mutability, StateMutability::View | StateMutability::Pure)
        && matches!(&f.ret, Some(TypeRef::Scalar { name, .. }) if name == "bool")
        && matches!(
            f.params.as_slice(),
            [p] if matches!(&p.ty, TypeRef::Scalar { name, .. } if name == "bytes4")
        )
}

pub(super) fn is_metadata_string_getter(f: &Function) -> bool {
    matches!(f.visibility, Visibility::Public)
        && matches!(&f.ret, Some(TypeRef::Scalar { name, .. }) if name == "string")
        && matches!(
            f.body.as_slice(),
            [Stmt::Return {
                value: Some(Expr::Var(..)),
                ..
            }]
        )
}

/// Collect the name of every `Var`-callee call site (statement- and expression-position) reachable
/// in a statement list. Total over `Stmt` (mirrors `naz_stmt`) so no call site is missed under any
/// pipeline order — a struct-constructor `Var` callee is harmlessly included (no function shares a
/// struct's name, per `validate_user_identifiers`), so it never affects which functions are swept.
pub(super) fn collect_callees_stmts(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        collect_callees_stmt(s, out);
    }
}

pub(super) fn collect_callees_stmt(s: &Stmt, out: &mut HashSet<String>) {
    match s {
        Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => collect_callees_expr(cond, out),
        Stmt::Revert { .. } | Stmt::Placeholder { .. } => {}
        Stmt::Assign { value, .. }
        | Stmt::FieldAssign { value, .. }
        | Stmt::LocalVar { value, .. } => collect_callees_expr(value, out),
        Stmt::IndexAssign { key, value, .. } => {
            collect_callees_expr(key, out);
            collect_callees_expr(value, out);
        }
        Stmt::IndexAssign2 { k1, k2, value, .. } => {
            collect_callees_expr(k1, out);
            collect_callees_expr(k2, out);
            collect_callees_expr(value, out);
        }
        Stmt::Return { value, .. } => {
            if let Some(v) = value {
                collect_callees_expr(v, out);
            }
        }
        Stmt::CallStmt { callee, args, .. } => {
            out.insert(callee.clone());
            for a in args {
                collect_callees_expr(a, out);
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            collect_callees_expr(cond, out);
            collect_callees_stmts(then_body, out);
            collect_callees_stmts(else_body, out);
        }
        Stmt::Unchecked { body, .. } => collect_callees_stmts(body, out),
        // The recognizer-produced atomics cannot exist this early (they are created by later desugar
        // passes), but recursing their pure operand exprs keeps the walker total under any reorder.
        Stmt::MapTransfer {
            from, to, amount, ..
        } => {
            collect_callees_expr(from, out);
            collect_callees_expr(to, out);
            collect_callees_expr(amount, out);
        }
        Stmt::Erc20TransferFrom {
            from,
            spender,
            to,
            amount,
            ..
        } => {
            collect_callees_expr(from, out);
            collect_callees_expr(spender, out);
            collect_callees_expr(to, out);
            collect_callees_expr(amount, out);
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
            collect_callees_expr(from, out);
            collect_callees_expr(amount, out);
            collect_callees_expr(to, out);
            collect_callees_expr(net, out);
            collect_callees_expr(fee_to, out);
            collect_callees_expr(fee, out);
        }
        Stmt::ReservedBatch {
            transfer, writes, ..
        } => {
            if let Some(t) = transfer {
                collect_callees_stmt(t, out);
            }
            for w in writes {
                collect_callees_stmt(w, out);
            }
        }
        Stmt::Erc20Update {
            from, to, value, ..
        } => {
            collect_callees_expr(from, out);
            collect_callees_expr(to, out);
            collect_callees_expr(value, out);
        }
        // SOL-AIRDROP: the airdrop loop's body holds the `_transfer(...)` callee to inline.
        Stmt::AirdropLoop { body, .. } => {
            for w in body {
                collect_callees_stmt(w, out);
            }
        }
        Stmt::BatchTransfer { from, .. } => {
            collect_callees_expr(from, out);
        }
    }
}

pub(super) fn collect_callees_expr(e: &Expr, out: &mut HashSet<String>) {
    match e {
        Expr::Call(callee, args, _) => {
            if let Expr::Var(n, _) = callee.as_ref() {
                out.insert(n.clone());
            }
            collect_callees_expr(callee, out);
            for a in args {
                collect_callees_expr(a, out);
            }
        }
        Expr::Member(base, _, _) => collect_callees_expr(base, out),
        Expr::Index(b, k, _) => {
            collect_callees_expr(b, out);
            collect_callees_expr(k, out);
        }
        Expr::Unary(_, x, _) => collect_callees_expr(x, out),
        Expr::Bin(_, l, r, _) => {
            collect_callees_expr(l, out);
            collect_callees_expr(r, out);
        }
        Expr::Num(..) | Expr::Bool(..) | Expr::Var(..) => {}
    }
}
