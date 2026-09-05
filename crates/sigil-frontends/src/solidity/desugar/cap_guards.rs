//! Capability directive detection and owner-gate recognition.

use super::*;

// ── SOL-CAP: onlyOwner → unforgeable &Cap gate (opt-in) ──────────────────────
// See docs/specs/solidity-access-control-via-capabilities.md (§7 E-1..E-6, §IMPL-1..5).
// recognize_cap_guards runs BEFORE inline_modifiers (it needs the un-inlined modifiers +
// raw `msg.sender`) and is READ-ONLY (IMPL-5). It returns the owner field + the guarded
// methods, or None (cap-mode off / no strict match → byte-identical SOL1c), or rejects
// (FE454-457) when cap-mode IS on but the contract can't be faithfully cap-translated.

/// The opt-in directive — a comment (invisible to the lexer), matched as an EXACT
/// whole-line-trimmed string. A typo does not match → the safe default (SOL1c).
pub const CAP_DIRECTIVE: &str = "// sigil:cap-access-control";

pub fn detect_cap_directive(src: &str) -> bool {
    src.lines().any(|l| l.trim() == CAP_DIRECTIVE)
}

/// SOL-CAP recognizer output: the access-controlling address field + the methods gated by
/// an `onlyOwner`-shaped modifier. `None` keeps the byte-identical SOL1c path (IMPL-2).
#[derive(Debug)]
pub struct CapGuardInfo {
    pub owner_field: String,
    pub guarded_methods: HashSet<String>,
}

pub(super) enum GateClass<'a> {
    /// An exact `onlyOwner` gate over the named address field.
    Gate(&'a str),
    /// Uses `msg.sender` in a guard but is NOT the exact gate shape (E-1 near-miss).
    NearMiss,
    /// Not identity-based (no `msg.sender`); a normal modifier, left to SOL1c.
    Other,
}

pub fn recognize_cap_guards(
    c: &Contract,
    cap_mode: bool,
) -> Result<Option<CapGuardInfo>, FrontendDiag> {
    if !cap_mode {
        return Ok(None);
    }
    // SOL-CTOR (EX-5/FE465): a `constructor` + cap-mode is a deferred combination. The
    // cap-mint `new()` DROPS the owner field; a constructor body writing that field would
    // emit a write to a non-existent field (a type error the FE500 parse self-check misses),
    // and the cap E-2 dataflow gate (`check_field_only_in_gate`) does not scan the ctor — a
    // ctor `msg.sender`/owner-field use would slip the cap soundness net. Reject; cap-mode
    // WITHOUT a constructor stays byte-identical.
    if c.constructor.is_some() {
        return Err(FrontendDiag::new(
            codes::FE465_CTOR_CAP_UNSUPPORTED_SOL,
            "a `constructor` combined with cap-mode (`// sigil:cap-access-control`) is unsupported (deferred — the cap mint and a deploy-time init body cannot yet be merged soundly)",
            c.span.clone(),
        ));
    }
    // The only legal gate operand is a state field of type `address`.
    let addr_fields: HashSet<&str> = c
        .state
        .iter()
        .filter(|sv| matches!(&sv.ty, TypeRef::Scalar { name, .. } if name == "address"))
        .map(|sv| sv.name.as_str())
        .collect();

    // Classify each modifier; collect the gate modifiers + the single owner field (E-1).
    let mut gate_mods: HashSet<&str> = HashSet::new();
    let mut gate_field: Option<&str> = None;
    for m in &c.modifiers {
        match classify_gate_modifier(m, &addr_fields) {
            GateClass::Gate(field) => {
                match gate_field {
                    Some(prev) if prev != field => {
                        return Err(FrontendDiag::new(
                            codes::FE456_MULTIPLE_OWNER_AUTHORITIES_SOL,
                            format!(
                                "cap-mode: gate modifiers reference distinct owner fields `{prev}` and `{field}` — multiple owner authorities are deferred"
                            ),
                            m.span.clone(),
                        ));
                    }
                    _ => gate_field = Some(field),
                }
                gate_mods.insert(m.name.as_str());
            }
            GateClass::NearMiss => {
                return Err(FrontendDiag::new(
                    codes::FE455_CAP_NEAR_MISS_SOL,
                    format!(
                        "cap-mode: modifier `{}` uses `msg.sender` but is not the exact `require(msg.sender == <address field>); _;` gate shape — cannot be faithfully cap-translated",
                        m.name
                    ),
                    m.span.clone(),
                ));
            }
            GateClass::Other => {}
        }
    }

    let Some(owner_field) = gate_field else {
        return Ok(None); // cap-mode on but no owner pattern → no-op (anti-goal A-2)
    };

    // Finding 2 (review): a capability cannot represent a SPECIFIC pinned owner address. If
    // the owner field has an initializer (`address owner = 0x..`), cap-translating would
    // silently DROP it (granting authority to whoever holds the minted cap, not to that
    // address). Reject. A field with NO initializer is the canonical "deployer becomes
    // owner": the `C_Owner` minted in `new()` and returned IS that authority (E-5).
    if let Some(sv) = c.state.iter().find(|sv| sv.name == owner_field)
        && sv.init.is_some()
    {
        return Err(FrontendDiag::new(
            codes::FE454_ADDRESS_USED_AS_DATA_SOL,
            format!(
                "cap-mode: the owner field `{owner_field}` has a fixed initializer — a capability cannot represent a pinned owner address; keep the address model"
            ),
            sv.span.clone(),
        ));
    }

    // Guarded methods: functions applying a gate modifier. A guarded method must apply
    // ONLY the gate (mixed onlyOwner + another modifier is deferred → FE455) so the
    // contract-global decision stays all-or-nothing (E-4).
    let mut guarded_methods: HashSet<String> = HashSet::new();
    for f in &c.functions {
        if f.modifiers
            .iter()
            .any(|nm| gate_mods.contains(nm.name.as_str()))
        {
            if f.modifiers.len() != 1 {
                return Err(FrontendDiag::new(
                    codes::FE455_CAP_NEAR_MISS_SOL,
                    format!(
                        "cap-mode: function `{}` applies the owner gate alongside another modifier — mixed access control is deferred",
                        f.name
                    ),
                    f.span.clone(),
                ));
            }
            guarded_methods.insert(f.name.clone());
        }
    }
    if guarded_methods.is_empty() {
        return Ok(None); // a gate modifier exists but is never applied → no-op
    }

    // Finding 1 (review — the load-bearing fix): inside an `onlyOwner` body, `msg.sender` IS
    // the authorized owner identity (the gate pinned `msg.sender == owner`). Cap-translation
    // DROPS the gate, freeing `msg.sender` into the unconstrained `__fe_sender` data param —
    // so an `&C_Owner` holder could pass ANY address (the H7 "coexistence" was unsound: an
    // owner-cap holder could drain any account). The cap is opaque and cannot rebind the
    // owner's address, so a guarded body that uses `msg.sender` CANNOT be faithfully
    // cap-translated. Reject (the source's `debited == owner` invariant is unrepresentable).
    for f in &c.functions {
        if guarded_methods.contains(&f.name) && body_uses_msg_sender(&f.body) {
            return Err(FrontendDiag::new(
                codes::FE454_ADDRESS_USED_AS_DATA_SOL,
                format!(
                    "cap-mode: guarded method `{}` reads `msg.sender` in its body — under `onlyOwner` that identity equals the owner, but the opaque `&C_Owner` cap cannot supply it (dropping the gate would free `msg.sender` to any address); keep the address model",
                    f.name
                ),
                f.span.clone(),
            ));
        }
    }

    // E-2 / IMPL-1: the owner field may appear ONLY in the gate modifier (exactly once,
    // guaranteed by the exact-shape match). Scan EVERY OTHER site and require zero uses.
    check_field_only_in_gate(c, owner_field, &gate_mods)?;

    Ok(Some(CapGuardInfo {
        owner_field: owner_field.to_string(),
        guarded_methods,
    }))
}

/// E-1: a modifier is a gate iff its body is EXACTLY `require(msg.sender == <F>); _;`
/// (one require + the placeholder), `<F>` a state `address` field, either operand order.
pub(super) fn classify_gate_modifier<'a>(
    m: &'a Modifier,
    addr_fields: &HashSet<&str>,
) -> GateClass<'a> {
    if m.body.len() == 2
        && matches!(m.body[1], Stmt::Placeholder { .. })
        && let Stmt::Require { cond, .. } = &m.body[0]
        && let Expr::Bin(BinOp::Eq, l, r, _) = cond
        && let Some(field) = gate_field_of(l, r, addr_fields)
    {
        return GateClass::Gate(field);
    }
    // A msg.sender-bearing guard that isn't the exact shape is a near-miss (FE455);
    // a modifier with no msg.sender is just a normal (non-identity) modifier.
    if body_uses_msg_sender(&m.body) {
        GateClass::NearMiss
    } else {
        GateClass::Other
    }
}

/// If one of `l`/`r` is `msg.sender` and the other is a `Var` naming an address field,
/// return that field name (either operand order).
pub(super) fn gate_field_of<'a>(
    l: &'a Expr,
    r: &'a Expr,
    addr_fields: &HashSet<&str>,
) -> Option<&'a str> {
    let one = |a: &Expr, b: &'a Expr| -> Option<&'a str> {
        if is_msg_sender(a)
            && let Expr::Var(name, _) = b
            && addr_fields.contains(name.as_str())
        {
            Some(name.as_str())
        } else {
            None
        }
    };
    one(l, r).or_else(|| one(r, l))
}

/// `msg.sender` = `Member(Var("msg"), "sender")` (matches `desugar::rewrite_sender_expr`).
pub(super) fn is_msg_sender(e: &Expr) -> bool {
    matches!(e, Expr::Member(base, member, _)
        if member == "sender" && matches!(base.as_ref(), Expr::Var(n, _) if n == "msg"))
}

/// Whether any statement in `stmts` references `msg.sender` ANYWHERE (every Stmt + Expr
/// position — not just guard conditions, so `bal[msg.sender] = v` is caught). Used for both
/// the near-miss modifier check and the guarded-body data-use check (finding 1).
pub(super) fn body_uses_msg_sender(stmts: &[Stmt]) -> bool {
    stmts.iter().any(stmt_uses_msg_sender)
}

pub(super) fn stmt_uses_msg_sender(s: &Stmt) -> bool {
    match s {
        Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => expr_mentions_msg_sender(cond),
        Stmt::Assign { value, .. } | Stmt::LocalVar { value, .. } => {
            expr_mentions_msg_sender(value)
        }
        Stmt::IndexAssign { key, value, .. } => {
            expr_mentions_msg_sender(key) || expr_mentions_msg_sender(value)
        }
        // SOL-ERC20: a two-key write `allowance[k1][k2] op= e` — `approve` /
        // `transferFrom` put `msg.sender` in a key. Without this arm a cap-mode
        // `onlyOwner` method whose ONLY `msg.sender` use is a two-key write would
        // escape the E-2 data-use gate (FE454), drop its gate, and free `__fe_sender`
        // — a silent authority weakening (adversarial-review finding).
        Stmt::IndexAssign2 { k1, k2, value, .. } => {
            expr_mentions_msg_sender(k1)
                || expr_mentions_msg_sender(k2)
                || expr_mentions_msg_sender(value)
        }
        // SOL-STRUCT: a struct field write `obj.field = e` — the VALUE may read
        // `msg.sender` (e.g. `s.who = msg.sender`). Without this arm a cap-mode
        // `onlyOwner` method whose ONLY `msg.sender` use is a struct field write would
        // escape the E-2 gate (FE454) — the IndexAssign2 finding, recurring via FieldAssign.
        Stmt::FieldAssign { value, .. } => expr_mentions_msg_sender(value),
        Stmt::MapTransfer {
            from, to, amount, ..
        } => {
            expr_mentions_msg_sender(from)
                || expr_mentions_msg_sender(to)
                || expr_mentions_msg_sender(amount)
        }
        Stmt::Return { value: Some(v), .. } => expr_mentions_msg_sender(v),
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            expr_mentions_msg_sender(cond)
                || then_body.iter().any(stmt_uses_msg_sender)
                || else_body.iter().any(stmt_uses_msg_sender)
        }
        // SOL-CALLS: a bare internal call `helper(args);` — recognize_cap_guards runs BEFORE the
        // inline pass, so a `msg.sender` smuggled into a call arg would escape the E-2 data-use gate
        // (FE454) and free `__fe_sender` without this arm (the IndexAssign2/FieldAssign finding,
        // recurring via a call statement).
        Stmt::CallStmt { args, .. } => args.iter().any(expr_mentions_msg_sender),
        // SOL-AIRDROP (Rung C, Correction B): the raw airdrop loop exists at cap-scan time
        // (`recognize_cap_guards` runs BEFORE desugar/`recognize_airdrop`). A `msg.sender` in
        // its BODY (e.g. an inlined `_transfer(msg.sender, to[i], amt[i])`) would otherwise
        // escape the E-2 data-use gate (FE454) and free `__fe_sender` — a cap-mode authority
        // bypass. Scan the body (the header's `idx`/`len_array` are bare names, no `msg.sender`).
        Stmt::AirdropLoop { body, .. } => body.iter().any(stmt_uses_msg_sender),
        _ => false,
    }
}

pub(super) fn expr_mentions_msg_sender(e: &Expr) -> bool {
    if is_msg_sender(e) {
        return true;
    }
    match e {
        Expr::Member(b, _, _) | Expr::Unary(_, b, _) => expr_mentions_msg_sender(b),
        Expr::Index(b, k, _) => expr_mentions_msg_sender(b) || expr_mentions_msg_sender(k),
        Expr::Bin(_, l, r, _) => expr_mentions_msg_sender(l) || expr_mentions_msg_sender(r),
        Expr::Call(c, args, _) => {
            expr_mentions_msg_sender(c) || args.iter().any(expr_mentions_msg_sender)
        }
        _ => false,
    }
}

/// E-2 / IMPL-1: scan every site EXCEPT the gate modifiers for any use of the owner field;
/// any reference → FE454 (the field is used as data, not purely as a gate).
pub(super) fn check_field_only_in_gate(
    c: &Contract,
    field: &str,
    gate_mods: &HashSet<&str>,
) -> Result<(), FrontendDiag> {
    for f in &c.functions {
        for s in &f.body {
            if let Some(span) = stmt_references_field(s, field) {
                return Err(fe454(field, &f.name, span));
            }
        }
    }
    for sv in &c.state {
        if let Some(init) = &sv.init
            && expr_references_field(init, field)
        {
            return Err(fe454(field, &sv.name, sv.span.clone()));
        }
    }
    for m in &c.modifiers {
        if gate_mods.contains(m.name.as_str()) {
            continue; // the gate modifier's single owner use is the allowed one
        }
        for s in &m.body {
            if let Some(span) = stmt_references_field(s, field) {
                return Err(fe454(field, &m.name, span));
            }
        }
    }
    Ok(())
}

pub(super) fn fe454(field: &str, site: &str, span: Range<usize>) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE454_ADDRESS_USED_AS_DATA_SOL,
        format!(
            "cap-mode: the access-controlling address field `{field}` is used outside the `onlyOwner` gate (in `{site}`) — capabilities translate an address used PURELY as an authorization gate; keep the address model or remove the data use"
        ),
        span,
    )
}

/// Whether a statement references `field` (the state field name) anywhere; returns its
/// span for the diagnostic. Mirrors the `rewrite_sender_*` walker shape. A write target
/// (`field = …` / `field[k] = …`) counts as a use too (e.g. `transferOwnership`).
pub(super) fn stmt_references_field(s: &Stmt, field: &str) -> Option<Range<usize>> {
    let direct = match s {
        Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => {
            expr_references_field(cond, field)
        }
        Stmt::Assign { target, value, .. } => {
            target == field || expr_references_field(value, field)
        }
        Stmt::IndexAssign {
            map, key, value, ..
        } => {
            map == field || expr_references_field(key, field) || expr_references_field(value, field)
        }
        // SOL-ERC20: a two-key write — the owner field could be smuggled in as a key or
        // value outside the gate; mirror the single-key arm (adversarial-review finding).
        Stmt::IndexAssign2 {
            map, k1, k2, value, ..
        } => {
            map == field
                || expr_references_field(k1, field)
                || expr_references_field(k2, field)
                || expr_references_field(value, field)
        }
        // SOL-STRUCT: a struct field write — the owner field could be smuggled in as the
        // written object or in the value, outside the gate; mirror the index-write arms.
        Stmt::FieldAssign { obj, value, .. } => obj == field || expr_references_field(value, field),
        Stmt::LocalVar { value, .. } => expr_references_field(value, field),
        Stmt::MapTransfer {
            map,
            from,
            to,
            amount,
            ..
        } => {
            map == field
                || expr_references_field(from, field)
                || expr_references_field(to, field)
                || expr_references_field(amount, field)
        }
        Stmt::Return { value: Some(v), .. } => expr_references_field(v, field),
        Stmt::If { cond, .. } => expr_references_field(cond, field),
        // SOL-CALLS: the owner field smuggled into a call arg (`helper(owner);`) — the same pre-inline
        // E-2 escape as the msg.sender case; scan the args (the C2-class data-use hole for calls).
        Stmt::CallStmt { args, .. } => args.iter().any(|a| expr_references_field(a, field)),
        _ => false,
    };
    if direct {
        return Some(stmt_span(s));
    }
    if let Stmt::If {
        then_body,
        else_body,
        ..
    } = s
    {
        return then_body
            .iter()
            .find_map(|x| stmt_references_field(x, field))
            .or_else(|| {
                else_body
                    .iter()
                    .find_map(|x| stmt_references_field(x, field))
            });
    }
    // SOL-AIRDROP (Rung C, Correction B): scan the raw airdrop loop body for the owner field —
    // the loop exists at cap-scan time; a missing scan is the same E-2 owner-data escape as `If`.
    if let Stmt::AirdropLoop { body, .. } = s {
        return body.iter().find_map(|x| stmt_references_field(x, field));
    }
    None
}

pub(super) fn expr_references_field(e: &Expr, field: &str) -> bool {
    match e {
        Expr::Var(name, _) => name == field,
        Expr::Member(b, _, _) | Expr::Unary(_, b, _) => expr_references_field(b, field),
        Expr::Index(b, k, _) => expr_references_field(b, field) || expr_references_field(k, field),
        Expr::Bin(_, l, r, _) => expr_references_field(l, field) || expr_references_field(r, field),
        Expr::Call(c, args, _) => {
            expr_references_field(c, field) || args.iter().any(|a| expr_references_field(a, field))
        }
        Expr::Num(..) | Expr::Bool(..) => false,
    }
}
