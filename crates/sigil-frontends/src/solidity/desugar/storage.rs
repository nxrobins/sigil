//! Checks-effects-interactions scheduling and multi-map reservation lowering.

use super::*;

// ── pass 5: total-CEI hoist+reorder (SOL-MULTIWRITE) ─────────────────────────

/// A storage location, for the RAW/WAW independence analysis. `Scalar` is a scalar or
/// struct-typed state field (by name); `Map` is a mapping (by name, ANY key — the frontend
/// has no `a != b` proof, so two reads/writes on the same map are conservatively aliasing).
#[derive(Debug, PartialEq, Clone)]
pub(super) enum Loc {
    Scalar(String),
    Map(String),
}

/// SOL-MULTIWRITE: the "total-CEI" transform. SIGIL has NO rollback, so the CEI gate (FE412)
/// rejects any trap-capable op after a committed storage write — blocking a legitimate straight-line
/// multi-write body (the OZ `_burn`/`_mint` shape). Such a body is rollback-SAFE once every
/// trap-capable write's arithmetic is hoisted into a pre-write local and the single map write is
/// reordered FIRST: then every trapping computation runs before any commit, and the only stores
/// after the map write read a pre-computed local (trap-free). This pass produces exactly that form —
/// which the UNCHANGED FE412 gate then accepts — or BAILS (returns the body untouched → the original
/// is FE412-rejected). It is SEMANTICS-PRESERVING (a reorder that moves all reads/computations
/// before all writes), sound iff: no read depends on an earlier write (EX-1, no RAW), no location is
/// written twice (EX-2, no WAW), the reordered writes are independent (EX-3, exactly one map write,
/// distinct from every scalar), and the body is straight-line (EX-4). The gate stays the oracle
/// (EX-5): the transform NEVER weakens it. Fires ONLY on a body that currently VIOLATES CEI, so any
/// body that already passes is returned byte-identical.
pub(super) fn total_cei(
    body: Vec<Stmt>,
    state: &HashSet<String>,
    numeric: &HashSet<String>,
    state_tys: &HashMap<String, TypeRef>,
    locals: &HashSet<String>,
) -> Vec<Stmt> {
    // SOL-ACCESS PR3: a bool-valued-map write's value is a `true`/`false` LITERAL (the
    // check gate), but the hoist types every `let __fe_wN` as u256 — a hoisted bool
    // literal would emit ill-typed SIGIL. Boring v1 limit: a body containing ANY
    // bool-map write is not transformed (its natural CEI verdict stands — the AC
    // grant/revoke idiom is a single write per function and never needs the hoist).
    if bool_map_write_present(&body, state_tys) {
        return body;
    }
    if !mw_applicable(&body, state, numeric, locals) || !mw_violates_cei(&body, state, locals) {
        return body;
    }
    mw_transform(body, state_tys)
}

/// SOL-ACCESS PR3: does the declared type carry a `bool` VALUE (a 1-key `mapping(K =>
/// bool)` or the 2-key `mapping(K => mapping(A => bool))` AccessControl `hasRole`
/// shape)? Used by `total_cei`/`reserve_multi_map` to bail (their hoists type values
/// as u256) — the body then keeps its natural FE412 verdict (fail-closed).
pub(super) fn is_bool_valued_map(ty: &TypeRef) -> bool {
    match ty {
        TypeRef::Mapping { value, .. } => match value.as_ref() {
            TypeRef::Scalar { name, .. } => name == "bool",
            TypeRef::Mapping { value: iv, .. } => {
                matches!(iv.as_ref(), TypeRef::Scalar { name, .. } if name == "bool")
            }
            // SOL-AIRDROP: an array-valued map is never the bool-map shape.
            TypeRef::Array { .. } => false,
        },
        _ => false,
    }
}

/// Any TOP-LEVEL bool-valued-map write in the body (both transforms are straight-line
/// only — a write inside an `if` already bails their applicability — so the top-level
/// scan is complete).
pub(super) fn bool_map_write_present(body: &[Stmt], state_tys: &HashMap<String, TypeRef>) -> bool {
    body.iter().any(|s| match s {
        Stmt::IndexAssign { map, .. } | Stmt::IndexAssign2 { map, .. } => {
            state_tys.get(map).is_some_and(is_bool_valued_map)
        }
        _ => false,
    })
}

/// Is a state field's declared type a NUMERIC scalar (`uint`, `uint8`..`uint256`)? A trap-capable
/// scalar write is hoisted, and its hoisted value is numeric arithmetic — a trap-capable write to a
/// non-numeric field (a struct construction whose args hide arithmetic — `struct_construct_arith_cei`)
/// is NOT a target and bails, keeping that adversarial pin FE412-rejected. `address`/`bool`/struct/
/// enum fields never carry trap-capable arithmetic, so they are only ever trap-free stores (moved
/// as-is, no hoist).
pub(super) fn mw_is_numeric_ty(ty: &TypeRef) -> bool {
    matches!(ty, TypeRef::Scalar { name, .. } if name.starts_with("uint"))
}

/// Whether `total_cei` may safely transform this body: a straight-line sequence of pure binds/guards
/// plus EXACTLY ONE map write and any number of scalar writes to state fields, with no RAW/WAW hazard.
/// Any deviation (control flow, early exit, a local reassignment, a struct-field write, a
/// trap-capable write to a non-numeric field, ≠1 map write, a read of an already-written location, or
/// a double-written location) → `false` (bail → the UNCHANGED FE412 gate rejects the original).
pub(super) fn mw_applicable(
    body: &[Stmt],
    state: &HashSet<String>,
    numeric: &HashSet<String>,
    locals: &HashSet<String>,
) -> bool {
    let mut map_writes = 0usize;
    for s in body {
        match s {
            Stmt::LocalVar { .. } | Stmt::Require { .. } | Stmt::Assert { .. } => {}
            Stmt::IndexAssign { .. }
            | Stmt::IndexAssign2 { .. }
            | Stmt::MapTransfer { .. }
            | Stmt::Erc20TransferFrom { .. } => map_writes += 1,
            Stmt::Assign {
                target, op, value, ..
            } => {
                // A local reassignment (or an undeclared target) is not a straight-line storage
                // write — bail (keeps the hoist reasoning trivial; OZ never reassigns a local here).
                let is_storage = state.contains(target) && !locals.contains(target);
                if !is_storage {
                    return false;
                }
                // A trap-capable scalar write must target a NUMERIC field (see `mw_is_numeric_ty`).
                let trap_capable = expr_has_checked_arith(value) || *op != AssignOp::Eq;
                if trap_capable && !numeric.contains(target) {
                    return false;
                }
            }
            // Control flow / early exit / a struct-field write / a residual inline/unchecked node →
            // not a straight-line ≤1-map body.
            _ => return false,
        }
    }
    // EX-3: exactly one map write (the OZ `_burn`/`_mint` shape). Zero maps (a pure-scalar
    // multi-write) is out of the approved scope; ≥2 independent map writes need a key-distinctness
    // proof the frontend lacks — both bail (fail-closed).
    if map_writes != 1 {
        return false;
    }
    // EX-1 (no RAW) + EX-2 (no WAW): a forward scan. A read of an already-written location, or a
    // second write to one, makes the reorder unsound → bail. Reads are checked BEFORE this
    // statement's own writes are recorded, so a compound `x op= e` (which reads its own target) is
    // not a self-RAW.
    let mut written: Vec<Loc> = Vec::new();
    for s in body {
        for r in mw_reads(s, state, locals) {
            if written.contains(&r) {
                return false;
            }
        }
        for w in mw_writes(s, state, locals) {
            if written.contains(&w) {
                return false;
            }
            written.push(w);
        }
    }
    true
}

/// Does this straight-line body currently VIOLATE the CEI gate (a trap-capable op after a committed
/// storage write)? Mirrors `check::check_stmts`'s `committed_write` logic over the top-level list, so
/// `total_cei` transforms ONLY bodies the gate would reject — a body that already passes is left
/// byte-identical (`mw_applicable` guarantees the straight-line shape, so no `if`/return recursion is
/// needed here).
pub(super) fn mw_violates_cei(
    body: &[Stmt],
    state: &HashSet<String>,
    locals: &HashSet<String>,
) -> bool {
    let mut committed = false;
    for s in body {
        match s {
            // A guard (require/assert) after a committed write is a CEI violation.
            Stmt::Require { .. } | Stmt::Assert { .. } if committed => return true,
            // Trap-capable arithmetic in a local bind after a committed write is a violation.
            Stmt::LocalVar { value, .. } if committed && expr_has_checked_arith(value) => {
                return true;
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let storage = state.contains(target) && !locals.contains(target);
                let traps = expr_has_checked_arith(value) || *op != AssignOp::Eq;
                if committed && traps {
                    return true;
                }
                if storage {
                    committed = true;
                }
            }
            Stmt::IndexAssign { .. }
            | Stmt::IndexAssign2 { .. }
            | Stmt::MapTransfer { .. }
            | Stmt::Erc20TransferFrom { .. } => {
                if committed {
                    return true;
                }
                committed = true;
            }
            // Straight-line guaranteed by `mw_applicable`; nothing else commits or traps.
            _ => {}
        }
    }
    false
}

/// The hoist+reorder. `mw_applicable`/`mw_violates_cei` have already vetted the body, so every
/// `Assign` here targets a state field, and there is exactly one map write. Emits: the pure binds/
/// guards and the hoisted `let __fe_wN = <arith>` (each in source position) as a PREFIX, then the
/// single map write, then the scalar store-backs (in source order) — every store after the map write
/// trap-free.
pub(super) fn mw_transform(body: Vec<Stmt>, state_tys: &HashMap<String, TypeRef>) -> Vec<Stmt> {
    let mut prefix: Vec<Stmt> = Vec::new();
    let mut map_write: Option<Stmt> = None;
    let mut scalar_backs: Vec<Stmt> = Vec::new();
    let mut wc: usize = 0;
    for s in body {
        match s {
            Stmt::LocalVar { .. } | Stmt::Require { .. } | Stmt::Assert { .. } => prefix.push(s),
            Stmt::IndexAssign { .. }
            | Stmt::IndexAssign2 { .. }
            | Stmt::MapTransfer { .. }
            | Stmt::Erc20TransferFrom { .. } => {
                // Exactly one (EX-3): kept whole and reordered first — as the first storage write its
                // own (possibly checked) arithmetic runs before any commit, so it needs no hoist.
                map_write = Some(s);
            }
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => {
                // Hoist EVERY scalar store's RHS into a pre-write local, leaving a trap-free
                // `target = __fe_wN` back-store. This is LOAD-BEARING: the back-store is emitted AFTER
                // the reordered-to-front map write, so if the RHS reads that map (e.g. a trap-free
                // snapshot `s = m[a];` sitting before the map write in source), moving the whole store
                // to the suffix would make it read the POST-write value (adversarial-review CRITICAL).
                // Hoisting the RHS keeps the read in the prefix, BEFORE the map write — so every read
                // observes the pre-write state, and the source-order RAW scan (`mw_applicable`) is the
                // exact soundness condition (a read that depends on an earlier write already bails).
                let w = format!("{SYNTH_PREFIX}w{wc}");
                wc += 1;
                let rhs = if op == AssignOp::Eq {
                    value
                } else {
                    // `target op= v` ≡ `target = target <binop> v`.
                    Expr::Bin(
                        assign_binop(op),
                        Box::new(Expr::Var(target.clone(), span.clone())),
                        Box::new(value),
                        span.clone(),
                    )
                };
                let ty = state_tys.get(&target).cloned().unwrap_or(TypeRef::Scalar {
                    name: "uint256".to_string(),
                    span: span.clone(),
                });
                prefix.push(Stmt::LocalVar {
                    name: w.clone(),
                    ty,
                    value: rhs,
                    span: span.clone(),
                });
                scalar_backs.push(Stmt::Assign {
                    target,
                    op: AssignOp::Eq,
                    value: Expr::Var(w, span.clone()),
                    span,
                });
            }
            // Unreachable: `mw_applicable` rejected every other shape. Keep it (never drop a statement)
            // so a logic slip surfaces at check/emit rather than silently vanishing.
            other => prefix.push(other),
        }
    }
    let mut out = prefix;
    if let Some(mw) = map_write {
        out.push(mw);
    }
    out.extend(scalar_backs);
    out
}

/// The `BinOp` a compound `AssignOp` expands to (`+=` → `+`, …). Only ever called for a compound op
/// (`Eq` is handled inline); the `Eq` arm is an unreachable defensive default.
pub(super) fn assign_binop(op: AssignOp) -> BinOp {
    match op {
        AssignOp::Plus => BinOp::Add,
        AssignOp::Minus => BinOp::Sub,
        AssignOp::Star => BinOp::Mul,
        AssignOp::Slash => BinOp::Div,
        AssignOp::Percent => BinOp::Mod,
        AssignOp::Eq => BinOp::Add,
    }
}

/// The storage locations a statement READS (for the RAW scan). A compound `x op= e` / `m[k] op= e`
/// also reads its own place. Operands of the atomic transfers are pure (no `Index`), but their own
/// map is included conservatively.
pub(super) fn mw_reads(s: &Stmt, state: &HashSet<String>, locals: &HashSet<String>) -> Vec<Loc> {
    let mut out = Vec::new();
    match s {
        Stmt::LocalVar { value, .. } => expr_reads(value, state, locals, &mut out),
        Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => {
            expr_reads(cond, state, locals, &mut out)
        }
        Stmt::Assign {
            target, op, value, ..
        } => {
            if *op != AssignOp::Eq && state.contains(target) && !locals.contains(target) {
                out.push(Loc::Scalar(target.clone()));
            }
            expr_reads(value, state, locals, &mut out);
        }
        Stmt::IndexAssign {
            map,
            key,
            op,
            value,
            ..
        } => {
            if *op != AssignOp::Eq {
                out.push(Loc::Map(map.clone()));
            }
            expr_reads(key, state, locals, &mut out);
            expr_reads(value, state, locals, &mut out);
        }
        Stmt::IndexAssign2 {
            map,
            k1,
            k2,
            op,
            value,
            ..
        } => {
            if *op != AssignOp::Eq {
                out.push(Loc::Map(map.clone()));
            }
            expr_reads(k1, state, locals, &mut out);
            expr_reads(k2, state, locals, &mut out);
            expr_reads(value, state, locals, &mut out);
        }
        Stmt::MapTransfer {
            map,
            from,
            to,
            amount,
            ..
        } => {
            out.push(Loc::Map(map.clone()));
            expr_reads(from, state, locals, &mut out);
            expr_reads(to, state, locals, &mut out);
            expr_reads(amount, state, locals, &mut out);
        }
        Stmt::Erc20TransferFrom {
            bal_map,
            alw_map,
            from,
            spender,
            to,
            amount,
            ..
        } => {
            out.push(Loc::Map(bal_map.clone()));
            out.push(Loc::Map(alw_map.clone()));
            expr_reads(from, state, locals, &mut out);
            expr_reads(spender, state, locals, &mut out);
            expr_reads(to, state, locals, &mut out);
            expr_reads(amount, state, locals, &mut out);
        }
        _ => {}
    }
    out
}

/// The storage locations a statement WRITES (for the RAW/WAW scan). A `LocalVar` writes a LOCAL, not
/// storage → none. `mw_applicable` bails before any non-storage `Assign`/`FieldAssign` reaches here.
pub(super) fn mw_writes(s: &Stmt, state: &HashSet<String>, locals: &HashSet<String>) -> Vec<Loc> {
    match s {
        Stmt::Assign { target, .. } if state.contains(target) && !locals.contains(target) => {
            vec![Loc::Scalar(target.clone())]
        }
        Stmt::IndexAssign { map, .. }
        | Stmt::IndexAssign2 { map, .. }
        | Stmt::MapTransfer { map, .. } => vec![Loc::Map(map.clone())],
        Stmt::Erc20TransferFrom {
            bal_map, alw_map, ..
        } => vec![Loc::Map(bal_map.clone()), Loc::Map(alw_map.clone())],
        _ => vec![],
    }
}

/// Collect the storage locations an expression READS: a bare `Var` naming a state field → `Scalar`;
/// `m[k]` → `Map(m)` (+ the key's reads); `obj.field` on a state field → `Scalar(obj)` (the whole
/// struct). A `Var` shadowed by a local reads the local, not storage.
pub(super) fn expr_reads(
    e: &Expr,
    state: &HashSet<String>,
    locals: &HashSet<String>,
    out: &mut Vec<Loc>,
) {
    match e {
        Expr::Num(..) | Expr::Bool(..) => {}
        Expr::Var(name, _) => {
            if state.contains(name) && !locals.contains(name) {
                out.push(Loc::Scalar(name.clone()));
            }
        }
        Expr::Index(base, key, _) => {
            if let Expr::Var(m, _) = base.as_ref() {
                out.push(Loc::Map(m.clone()));
            } else {
                expr_reads(base, state, locals, out);
            }
            expr_reads(key, state, locals, out);
        }
        Expr::Member(base, _, _) => {
            if let Expr::Var(o, _) = base.as_ref() {
                if state.contains(o) && !locals.contains(o) {
                    out.push(Loc::Scalar(o.clone()));
                }
            } else {
                expr_reads(base, state, locals, out);
            }
        }
        Expr::Unary(_, x, _) => expr_reads(x, state, locals, out),
        Expr::Bin(_, l, r, _) => {
            expr_reads(l, state, locals, out);
            expr_reads(r, state, locals, out);
        }
        Expr::Call(callee, args, _) => {
            expr_reads(callee, state, locals, out);
            for a in args {
                expr_reads(a, state, locals, out);
            }
        }
    }
}

// ── pass 6: reserve-all-then-write for ≥2 DISTINCT-map writes (SOL-MULTIMAP M-A) ──

/// The maps a single storage op WRITES (by name). A transfer writes its map(s); a plain index write
/// writes its map. Used to enforce the distinct-map-names gate.
pub(super) fn rmm_write_maps(s: &Stmt) -> Vec<String> {
    match s {
        Stmt::MapTransfer { map, .. } => vec![map.clone()],
        Stmt::Erc20TransferFrom {
            bal_map, alw_map, ..
        } => vec![bal_map.clone(), alw_map.clone()],
        Stmt::IndexAssign { map, .. } | Stmt::IndexAssign2 { map, .. } => vec![map.clone()],
        _ => vec![],
    }
}

/// The LEAF value type of a (possibly nested) mapping — `mapping(a=>uint256)` → `uint256`,
/// `mapping(a=>mapping(b=>uint256))` → `uint256`. The type of a plain map write's hoisted value.
pub(super) fn rmm_map_value_ty(ty: Option<&TypeRef>) -> Option<TypeRef> {
    let mut cur = ty?;
    loop {
        match cur {
            TypeRef::Mapping { value, .. } => cur = value,
            other => return Some(other.clone()),
        }
    }
}

/// SOL-MULTIMAP M-A: fold a straight-line body whose storage writes are ≥2 map writes to DISTINCT
/// mappings (≤1 folded transfer + plain index writes to OTHER maps) into ONE atomic `ReservedBatch`.
/// SIGIL has no rollback, so ≥2 sequential map writes hit FE412; but writes to DIFFERENT map names are
/// provably distinct storage (no `a != b` needed), so the batch is made atomic by reserve-all-then-write
/// (emit: reserve every deferred map read-only → the ≤1 self-atomic transfer → the trap-free inserts).
/// Values are HOISTED (like `total_cei`) so every read precedes every write; the source-order RAW scan is
/// then the exact soundness condition. BAILS (returns the body untouched → the original is FE412-rejected)
/// on: a same map name written twice, ≥2 transfers, a scalar/struct/other write, control flow, >4 maps,
/// or a RAW hazard. Runs AFTER `total_cei` (which handles the ≤1-map case), so it only ever sees a body
/// `total_cei` left unchanged.
pub(super) fn reserve_multi_map(
    body: Vec<Stmt>,
    state: &HashSet<String>,
    map_tys: &HashMap<String, TypeRef>,
    locals: &HashSet<String>,
    counter: &mut usize,
) -> Vec<Stmt> {
    // SOL-ACCESS PR3: same bool-map bail as `total_cei` — the batch hoist types every
    // deferred value as u256, so a bool-map write (a `true`/`false` literal) is never
    // batched; the body keeps its natural CEI verdict (fail-closed).
    if bool_map_write_present(&body, map_tys) {
        return body;
    }
    if !rmm_applicable(&body, state, locals) {
        return body;
    }
    rmm_transform(body, map_tys, counter)
}

/// Whether `reserve_multi_map` may safely fold this body: straight-line, storage writes are ONLY map
/// ops (no scalar/struct write), EXACTLY the map names are pairwise DISTINCT, ≤1 transfer, ≥2 map ops,
/// ≤4 distinct maps, no RAW. Any deviation → `false` (bail → FE412).
pub(super) fn rmm_applicable(
    body: &[Stmt],
    state: &HashSet<String>,
    locals: &HashSet<String>,
) -> bool {
    let mut transfers = 0usize;
    let mut ops = 0usize;
    let mut maps: Vec<String> = Vec::new();
    for s in body {
        match s {
            Stmt::LocalVar { .. } | Stmt::Require { .. } | Stmt::Assert { .. } => {}
            Stmt::MapTransfer { .. } | Stmt::Erc20TransferFrom { .. } => {
                transfers += 1;
                ops += 1;
                for m in rmm_write_maps(s) {
                    if maps.contains(&m) {
                        return false; // a map written twice — the same-map aliasing case (M-B)
                    }
                    maps.push(m);
                }
            }
            // A plain deferred write's KEY(s) MUST be pure (no `Index`/`Member`/`Call`). The value is
            // HOISTED (snapshotted pre-write), but the KEY is re-emitted verbatim in the deferred insert,
            // which emit places AFTER the reordered-to-middle transfer — so a KEY that reads a map the
            // batch writes (e.g. `ledger[balances[to]] = 5`) would be re-evaluated POST-transfer and write
            // the WRONG slot (adversarial-review CRITICAL). A pure key (a param/local/arith of them) is
            // identical before and after the transfer, so re-evaluation is safe; an impure key bails →
            // FE412 (fail-closed). Mirrors the transfer's own `is_transfer_operand` operand guard.
            Stmt::IndexAssign { map, key, .. } => {
                ops += 1;
                if maps.contains(map) || !is_transfer_operand(key) {
                    return false;
                }
                maps.push(map.clone());
            }
            Stmt::IndexAssign2 { map, k1, k2, .. } => {
                ops += 1;
                if maps.contains(map) || !is_transfer_operand(k1) || !is_transfer_operand(k2) {
                    return false;
                }
                maps.push(map.clone());
            }
            // A scalar/struct write, control flow, early exit, or a residual node → not a
            // pure straight-line distinct-map batch. (Scalar-in-mix is a declared M-A anti-goal.)
            _ => return false,
        }
    }
    if transfers > 1 || ops < 2 || maps.len() > 4 {
        return false;
    }
    // No RAW: a read of a location an EARLIER op wrote (reuse `total_cei`'s forward scan). Distinct map
    // names already preclude WAW, but keep the write-vs-write guard for safety.
    let mut written: Vec<Loc> = Vec::new();
    for s in body {
        for r in mw_reads(s, state, locals) {
            if written.contains(&r) {
                return false;
            }
        }
        for w in mw_writes(s, state, locals) {
            if written.contains(&w) {
                return false;
            }
            written.push(w);
        }
    }
    true
}

/// The fold. `rmm_applicable` has vetted the body: hoist each plain write's value into a pre-batch
/// `let __fe_rbN` (read pre-write) and defer the write as a trap-free `insert(k, __fe_rbN)`; the ≤1
/// transfer is kept whole. Output = [binds, guards, hoisted lets] ++ [ReservedBatch { transfer, writes }].
pub(super) fn rmm_transform(
    body: Vec<Stmt>,
    map_tys: &HashMap<String, TypeRef>,
    counter: &mut usize,
) -> Vec<Stmt> {
    let mut prefix: Vec<Stmt> = Vec::new();
    let mut transfer: Option<Box<Stmt>> = None;
    let mut writes: Vec<Stmt> = Vec::new();
    let mut lo: Option<usize> = None;
    let mut hi: Option<usize> = None;
    for s in body {
        match s {
            Stmt::LocalVar { .. } | Stmt::Require { .. } | Stmt::Assert { .. } => prefix.push(s),
            Stmt::MapTransfer { .. } | Stmt::Erc20TransferFrom { .. } => {
                let sp = stmt_span(&s);
                lo = Some(lo.map_or(sp.start, |v| v.min(sp.start)));
                hi = Some(hi.map_or(sp.end, |v| v.max(sp.end)));
                transfer = Some(Box::new(s));
            }
            Stmt::IndexAssign {
                map,
                key,
                op,
                value,
                span,
            } => {
                lo = Some(lo.map_or(span.start, |v| v.min(span.start)));
                hi = Some(hi.map_or(span.end, |v| v.max(span.end)));
                let w = format!("{SYNTH_PREFIX}rb{counter}");
                *counter += 1;
                let rhs = if op == AssignOp::Eq {
                    value
                } else {
                    Expr::Bin(
                        assign_binop(op),
                        Box::new(Expr::Index(
                            Box::new(Expr::Var(map.clone(), span.clone())),
                            Box::new(key.clone()),
                            span.clone(),
                        )),
                        Box::new(value),
                        span.clone(),
                    )
                };
                let ty = rmm_map_value_ty(map_tys.get(&map)).unwrap_or(TypeRef::Scalar {
                    name: "uint256".to_string(),
                    span: span.clone(),
                });
                prefix.push(Stmt::LocalVar {
                    name: w.clone(),
                    ty,
                    value: rhs,
                    span: span.clone(),
                });
                writes.push(Stmt::IndexAssign {
                    map,
                    key,
                    op: AssignOp::Eq,
                    value: Expr::Var(w, span.clone()),
                    span,
                });
            }
            Stmt::IndexAssign2 {
                map,
                k1,
                k2,
                op,
                value,
                span,
            } => {
                lo = Some(lo.map_or(span.start, |v| v.min(span.start)));
                hi = Some(hi.map_or(span.end, |v| v.max(span.end)));
                let w = format!("{SYNTH_PREFIX}rb{counter}");
                *counter += 1;
                let rhs = if op == AssignOp::Eq {
                    value
                } else {
                    let inner = Expr::Index(
                        Box::new(Expr::Var(map.clone(), span.clone())),
                        Box::new(k1.clone()),
                        span.clone(),
                    );
                    Expr::Bin(
                        assign_binop(op),
                        Box::new(Expr::Index(
                            Box::new(inner),
                            Box::new(k2.clone()),
                            span.clone(),
                        )),
                        Box::new(value),
                        span.clone(),
                    )
                };
                let ty = rmm_map_value_ty(map_tys.get(&map)).unwrap_or(TypeRef::Scalar {
                    name: "uint256".to_string(),
                    span: span.clone(),
                });
                prefix.push(Stmt::LocalVar {
                    name: w.clone(),
                    ty,
                    value: rhs,
                    span: span.clone(),
                });
                writes.push(Stmt::IndexAssign2 {
                    map,
                    k1,
                    k2,
                    op: AssignOp::Eq,
                    value: Expr::Var(w, span.clone()),
                    span,
                });
            }
            // Unreachable (applicable gated); keep it so a slip surfaces downstream.
            other => prefix.push(other),
        }
    }
    let span = lo.unwrap_or(0)..hi.unwrap_or(0);
    let mut out = prefix;
    out.push(Stmt::ReservedBatch {
        transfer,
        writes,
        span,
    });
    out
}

/// `allowance[from][spender] -= amount` (compound) or `= allowance[from][spender] -
/// amount` (expanded) → `(alw_map, from, spender, amount)`. The two-key analogue of
/// `as_debit`; the read keys of the expanded form must match the write keys.
pub(super) fn as_allowance_debit(s: &Stmt) -> Option<(&String, &Expr, &Expr, &Expr)> {
    let Stmt::IndexAssign2 {
        map,
        k1,
        k2,
        op,
        value,
        ..
    } = s
    else {
        return None;
    };
    if *op == AssignOp::Minus {
        return Some((map, k1, k2, value));
    }
    if *op == AssignOp::Eq
        && let Expr::Bin(BinOp::Sub, l, r, _) = value
        && let Expr::Index(outer, ik2, _) = l.as_ref()
        && let Expr::Index(base, ik1, _) = outer.as_ref()
        && let Expr::Var(bn, _) = base.as_ref()
        && bn == map
        && expr_eq(ik1, k1)
        && expr_eq(ik2, k2)
    {
        return Some((map, k1, k2, r));
    }
    None
}

/// A recognized balance `MapTransfer` → `(map, from, to, amount)`.
pub(super) fn as_balance_transfer(s: &Stmt) -> Option<(&String, &Expr, &Expr, &Expr)> {
    if let Stmt::MapTransfer {
        map,
        from,
        to,
        amount,
        ..
    } = s
    {
        Some((map, from, to, amount))
    } else {
        None
    }
}

/// `M[k] -= x` or `M[k] = M[k] - x` → `(map, key, amount)`.
pub(super) fn as_debit(s: &Stmt) -> Option<(&String, &Expr, &Expr)> {
    sub_add_assign(s, AssignOp::Minus, BinOp::Sub)
}

/// `M[k] += x` or `M[k] = M[k] + x` → `(map, key, amount)`.
pub(super) fn as_credit(s: &Stmt) -> Option<(&String, &Expr, &Expr)> {
    sub_add_assign(s, AssignOp::Plus, BinOp::Add)
}

pub(super) fn sub_add_assign(
    s: &Stmt,
    compound: AssignOp,
    bin: BinOp,
) -> Option<(&String, &Expr, &Expr)> {
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
    if *op == compound {
        // `M[k] op= x` → amount is the RHS verbatim.
        return Some((map, key, value));
    }
    if *op == AssignOp::Eq {
        // `M[k] = M[k] <bin> x` — the read key must match the write key.
        if let Expr::Bin(b, l, r, _) = value
            && *b == bin
            && let Expr::Index(base, ik, _) = l.as_ref()
            && let Expr::Var(bn, _) = base.as_ref()
            && bn == map
            && expr_eq(ik, key)
        {
            return Some((map, key, r));
        }
    }
    None
}

pub(super) fn stmt_span(s: &Stmt) -> Range<usize> {
    match s {
        Stmt::Require { span, .. }
        | Stmt::Assert { span, .. }
        | Stmt::Revert { span }
        | Stmt::Assign { span, .. }
        | Stmt::IndexAssign { span, .. }
        | Stmt::IndexAssign2 { span, .. }
        | Stmt::FieldAssign { span, .. }
        | Stmt::MapTransfer { span, .. }
        | Stmt::Erc20TransferFrom { span, .. }
        | Stmt::LocalVar { span, .. }
        | Stmt::If { span, .. }
        | Stmt::Return { span, .. }
        | Stmt::Unchecked { span, .. }
        | Stmt::Placeholder { span }
        | Stmt::CallStmt { span, .. }
        | Stmt::ReservedBatch { span, .. }
        | Stmt::MapSplitTransfer { span, .. }
        | Stmt::Erc20Update { span, .. }
        | Stmt::AirdropLoop { span, .. }
        | Stmt::BatchTransfer { span, .. } => span.clone(),
    }
}

/// A transfer operand (`from`/`to`/`amount`) must be FREE of map reads (`Index`) and
/// other impure/aliasing forms (`Member`/`Call`), so its value is stable across the
/// two folded writes. Otherwise the fold could mis-translate aliasing — e.g.
/// `bal[a] -= bal[a]; bal[b] += bal[a];`, where Solidity credits `b` with the
/// POST-debit value (0) but `transfer(a, b, bal[a])` would read the original. Such a
/// pair is left UNFOLDED (the second write is then FE412, fail-closed). A user who
/// wants it folded can bind the amount to a local first (an explicit pre-read).
pub(super) fn is_transfer_operand(e: &Expr) -> bool {
    match e {
        Expr::Num(..) | Expr::Bool(..) | Expr::Var(..) => true,
        Expr::Unary(_, x, _) => is_transfer_operand(x),
        Expr::Bin(_, l, r, _) => is_transfer_operand(l) && is_transfer_operand(r),
        Expr::Index(..) | Expr::Member(..) | Expr::Call(..) => false,
    }
}

/// Structural expression equality, ignoring spans.
pub(super) fn expr_eq(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::Num(x, _), Expr::Num(y, _)) => x == y,
        (Expr::Bool(x, _), Expr::Bool(y, _)) => x == y,
        (Expr::Var(x, _), Expr::Var(y, _)) => x == y,
        (Expr::Member(b1, m1, _), Expr::Member(b2, m2, _)) => m1 == m2 && expr_eq(b1, b2),
        (Expr::Index(b1, k1, _), Expr::Index(b2, k2, _)) => expr_eq(b1, b2) && expr_eq(k1, k2),
        (Expr::Unary(o1, x1, _), Expr::Unary(o2, x2, _)) => o1 == o2 && expr_eq(x1, x2),
        (Expr::Bin(o1, l1, r1, _), Expr::Bin(o2, l2, r2, _)) => {
            o1 == o2 && expr_eq(l1, l2) && expr_eq(r1, r2)
        }
        (Expr::Call(c1, a1, _), Expr::Call(c2, a2, _)) => {
            expr_eq(c1, c2) && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| expr_eq(x, y))
        }
        _ => false,
    }
}
