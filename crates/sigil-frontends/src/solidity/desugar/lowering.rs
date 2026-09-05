//! Sender, overload, struct-map, and short-circuit expression lowering.

use super::*;

// ── pass 1: msg.sender → __fe_sender param ───────────────────────────────────

/// The synthesized caller-authority param name (reserved `__fe_` prefix, so it can
/// never collide with a user identifier — `check_identifier` rejects user `__fe_*`).
/// `check` exempts exactly this name from the reserved-prefix guard (it is ours).
pub const SENDER_PARAM: &str = "__fe_sender";

pub(super) fn lower_sender(f: &mut Function) {
    let mut used = false;
    for s in &mut f.body {
        rewrite_sender_stmt(s, &mut used);
    }
    if used {
        // Prepend the param (it appears right after `self` in the emitted signature).
        // Typed `address` so it is a legal address-keyed map index and inherits the
        // address-distinctness checks (no arithmetic on the sender).
        f.params.insert(
            0,
            crate::solidity::parser::Param {
                name: SENDER_PARAM.to_string(),
                ty: TypeRef::Scalar {
                    name: "address".to_string(),
                    span: 0..0,
                },
                span: 0..0,
            },
        );
    }
}

/// SOL-CTOR: `lower_sender` for a constructor body — no `self`; the `__fe_sender` DEPLOYER
/// param is prepended when the body uses `msg.sender`. Reuses the shared sender walkers.
pub(super) fn lower_sender_ctor(c: &mut Constructor) {
    let mut used = false;
    for s in &mut c.body {
        rewrite_sender_stmt(s, &mut used);
    }
    if used {
        c.params.insert(
            0,
            crate::solidity::parser::Param {
                name: SENDER_PARAM.to_string(),
                ty: TypeRef::Scalar {
                    name: "address".to_string(),
                    span: 0..0,
                },
                span: 0..0,
            },
        );
    }
}

pub(super) fn rewrite_sender_stmt(s: &mut Stmt, used: &mut bool) {
    match s {
        Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => rewrite_sender_expr(cond, used),
        // MapTransfer/Erc20TransferFrom/ReservedBatch/BatchTransfer are produced by LATER recognize
        // passes; never seen here. Placeholder is removed by the EARLIER inline_modifiers pass.
        Stmt::Revert { .. }
        | Stmt::Unchecked { .. }
        | Stmt::MapTransfer { .. }
        | Stmt::Erc20TransferFrom { .. }
        | Stmt::ReservedBatch { .. }
        | Stmt::MapSplitTransfer { .. }
        | Stmt::Erc20Update { .. }
        | Stmt::BatchTransfer { .. }
        | Stmt::Placeholder { .. } => {}
        // SOL-CALLS: inline runs BEFORE lower_sender, so a CallStmt is normally already gone; recurse
        // into args for robustness (a survivor's `msg.sender` would otherwise be left un-lowered).
        Stmt::CallStmt { args, .. } => {
            for a in args.iter_mut() {
                rewrite_sender_expr(a, used);
            }
        }
        Stmt::Assign { value, .. } => rewrite_sender_expr(value, used),
        Stmt::IndexAssign { key, value, .. } => {
            rewrite_sender_expr(key, used);
            rewrite_sender_expr(value, used);
        }
        // SOL-ERC20: a two-key write `m[k1][k2] op= e` — `approve` puts `msg.sender`
        // in the FIRST key, so BOTH keys and the value must be scanned.
        Stmt::IndexAssign2 { k1, k2, value, .. } => {
            rewrite_sender_expr(k1, used);
            rewrite_sender_expr(k2, used);
            rewrite_sender_expr(value, used);
        }
        // SOL-STRUCT: a struct field write `obj.field = e` — `obj`/`field` are plain
        // idents, but the VALUE may read `msg.sender` (e.g. `s.owner = msg.sender`).
        Stmt::FieldAssign { value, .. } => rewrite_sender_expr(value, used),
        Stmt::LocalVar { value, .. } => rewrite_sender_expr(value, used),
        Stmt::Return { value, .. } => {
            if let Some(v) = value {
                rewrite_sender_expr(v, used);
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            rewrite_sender_expr(cond, used);
            for s in then_body.iter_mut() {
                rewrite_sender_stmt(s, used);
            }
            for s in else_body.iter_mut() {
                rewrite_sender_stmt(s, used);
            }
        }
        // SOL-AIRDROP: the raw loop exists at lower_sender time (pre-recognize) — recurse its
        // body like an `if` so a `msg.sender` read inside the loop is lowered to the param.
        Stmt::AirdropLoop { body, .. } => {
            for s in body.iter_mut() {
                rewrite_sender_stmt(s, used);
            }
        }
    }
}

/// Rewrite every `msg.sender` (a `Member(Var("msg"), "sender")`) to a reference to
/// the synthesized param. Only `.sender` on the global `msg` is rewritten; every
/// other member (msg.value, tx.origin, block.*, struct fields) is left intact for
/// `check` to reject (FE410). `msg` is a reserved global (`check_identifier` forbids
/// a user identifier named `msg`), so this match is unambiguous.
pub(super) fn rewrite_sender_expr(e: &mut Expr, used: &mut bool) {
    match e {
        Expr::Member(base, member, span) => {
            if member == "sender" && matches!(base.as_ref(), Expr::Var(name, _) if name == "msg") {
                *used = true;
                *e = Expr::Var(SENDER_PARAM.to_string(), span.clone());
            } else {
                rewrite_sender_expr(base, used);
            }
        }
        Expr::Index(b, k, _) => {
            rewrite_sender_expr(b, used);
            rewrite_sender_expr(k, used);
        }
        Expr::Unary(_, x, _) => rewrite_sender_expr(x, used),
        Expr::Bin(_, l, r, _) => {
            rewrite_sender_expr(l, used);
            rewrite_sender_expr(r, used);
        }
        Expr::Call(callee, args, _) => {
            rewrite_sender_expr(callee, used);
            for a in args.iter_mut() {
                rewrite_sender_expr(a, used);
            }
        }
        Expr::Num(..) | Expr::Bool(..) | Expr::Var(..) => {}
    }
}

// ── SOL-XFILE PR3/OVL: overload arity-disambiguation ─────────────────────────

/// The mangled name for one overload of `name` at a given `arity`. The reserved `__fe_` prefix is
/// collision-free with any user identifier (`check::check_identifier` forbids a user `__fe_`), so a
/// mangled overload can never clash with a real method.
pub(super) fn mangle_overload(name: &str, arity: usize) -> String {
    format!("__fe_ov{arity}_{name}")
}

/// SOL-XFILE PR3/OVL: disambiguate Solidity method OVERLOADS (same name, different arity) that the
/// flatten + `validate_user_identifiers` gates deliberately kept as a same-name set (SIGIL impl
/// methods cannot share a name). Each overload's DEFINITION is renamed to a unique
/// `__fe_ov{arity}_{name}`, and every CALL SITE is rewritten to the mangled name BY ARG COUNT.
///
/// Runs AFTER `validate_user_identifiers` (so the injected `__fe_` names are never validated as user
/// identifiers) and BEFORE `inline_internal_calls` (which resolves callees by name — the mangled
/// names + rewritten calls flow through inlining unchanged). Renaming a callee hides no `msg.sender`/
/// owner data-use (arguments are untouched), so running it after the SOL-CAP scan is safe. A call
/// whose arg count matches NO declared overload arity → FE420 (a shape valid Solidity never produces).
/// SOL-ACCESS PR4 — explode `mapping(K => Struct)` into one synthesized per-field map
/// (the AccessControl `mapping(bytes32 => RoleData)` storage shape). The ACCESS rewrite
/// already happened AT PARSE (`M[k].f` → `__fe_sm_M_f[k]`, parse_postfix's Dot arm —
/// one shared `struct_map_synth_name`, so decl and access can never disagree, MC-4);
/// this pass does the DECLARATION side + the fail-closed sweep:
///   1. every state var `M: mapping(K => S)` (S a declared struct whose fields are ALL
///      scalar or single-level scalar-mapping — EX-5) is replaced IN PLACE by one map
///      per field: scalar `f: V` → `__fe_sm_M_f: mapping(K => V)`; `f: mapping(A => V)`
///      → `__fe_sm_M_f: mapping(K => mapping(A => V))` — the (outer, inner) key order
///      is the source access order (MI-3), and check re-validates every synthesized
///      TypeRef (a struct/uintN field value rejects there — no type reasoning here);
///   2. a struct left with ZERO remaining type references is dropped (its only job was
///      the exploded storage); a still-referenced struct stays (and a mapping-bearing
///      struct used as a plain type fail-closes at check on its field);
///   3. any `__fe_sm_` variable reference this pass did NOT synthesize — a `x[k].f`
///      path on a non-struct-map, a chained `M[k].f.g`, or a name-scheme collision —
///      → a PRECISE FE441 (never the cryptic undeclared-variable fallthrough, and
///      never a silent shared slot: two (var, field) pairs mangling identically —
///      var `a_b`/field `c` vs var `a`/field `b_c` — are caught by the duplicate
///      check in step 1, MC-5).
///
/// Runs AFTER `validate_user_identifiers` (the `__fe_` names must not be validated as
/// user idents — the disambiguate_overloads precedent) and BEFORE the SOL-CAP scans +
/// `desugar` (they then see only plain 1/2-key map shapes they already understand —
/// the F2/F3/F4 ordering lesson). A bailed var (non-bounded struct) keeps its original
/// `mapping(K => S)` type → FE441 at check (fail-closed).
pub(in crate::solidity) fn explode_struct_maps(p: &mut Program) -> Result<(), FrontendDiag> {
    let c = &mut p.contract;
    // NO structs-empty early return: the parse rewrite mints `__fe_sm_` names for ANY
    // `x[k].f` shape (structs present or not), so the step-3 residual sweep must
    // ALWAYS run — a `balances[a].total` in a struct-free contract still needs the
    // precise reject, not check's generic unresolved-reference fallthrough.
    // EX-5: a struct is EXPLODABLE iff every field is a scalar or a single-level
    // mapping (both sides scalar). Check re-validates the synthesized types, so no
    // scalar-name reasoning happens here (a struct-named scalar field synthesizes a
    // map check then rejects FE441).
    let explodable = |s: &crate::solidity::parser::Struct| {
        s.fields.iter().all(|f| match &f.ty {
            TypeRef::Scalar { .. } => true,
            TypeRef::Mapping { key, value, .. } => {
                matches!(key.as_ref(), TypeRef::Scalar { .. })
                    && matches!(value.as_ref(), TypeRef::Scalar { .. })
            }
            // SOL-AIRDROP: an array-typed field ⇒ NOT a bounded struct-map (fail-closed: the
            // struct stays unexploded, its array field rejected downstream at check).
            TypeRef::Array { .. } => false,
        })
    };
    // Step 1: rebuild the state list, replacing each qualifying struct-map var in
    // place with its synthesized per-field maps (deterministic order: var order ×
    // field order — stable goldens).
    let mut synthesized: HashSet<String> = HashSet::new();
    let mut exploded_structs: HashSet<String> = HashSet::new();
    let mut removed: HashSet<String> = HashSet::new();
    let mut new_state: Vec<StateVar> = Vec::with_capacity(c.state.len());
    let old_state = std::mem::take(&mut c.state);
    let existing_names: HashSet<String> = old_state.iter().map(|sv| sv.name.clone()).collect();
    for sv in old_state {
        let target = match &sv.ty {
            TypeRef::Mapping { key, value, .. } => match value.as_ref() {
                TypeRef::Scalar { name, .. } => c
                    .structs
                    .iter()
                    .find(|s| s.name == *name)
                    .filter(|s| explodable(s))
                    .map(|s| (key.as_ref().clone(), s.clone())),
                _ => None,
            },
            _ => None,
        };
        let Some((outer_key, sdef)) = target else {
            new_state.push(sv);
            continue;
        };
        removed.insert(sv.name.clone());
        for f in &sdef.fields {
            let synth = struct_map_synth_name(&sv.name, &f.name);
            // MC-5: a collision — with a user state var (impossible via the `__fe_`
            // ident gate, but a second explode could collide under the mangling
            // scheme) or with another synthesized map — is a LOUD reject, never a
            // silently shared slot.
            if existing_names.contains(&synth) || !synthesized.insert(synth.clone()) {
                return Err(FrontendDiag::new(
                    codes::FE441_BAD_MAP_KV_SOL,
                    format!(
                        "struct-map explode name collision: `{synth}` (from `{}`.`{}`) is already declared",
                        sv.name, f.name
                    ),
                    sv.span.clone(),
                ));
            }
            let ty = match &f.ty {
                TypeRef::Scalar { .. } => TypeRef::Mapping {
                    key: Box::new(outer_key.clone()),
                    value: Box::new(f.ty.clone()),
                    span: f.span.clone(),
                },
                TypeRef::Mapping { .. } => TypeRef::Mapping {
                    key: Box::new(outer_key.clone()),
                    value: Box::new(f.ty.clone()),
                    span: f.span.clone(),
                },
                // SOL-AIRDROP: unreachable — `explodable` (above) rejects a struct with an array
                // field, so an exploded struct never has one. Kept exhaustive; the same wrap means
                // a stray one fails closed at check (which re-validates every synthesized type),
                // never here.
                TypeRef::Array { .. } => TypeRef::Mapping {
                    key: Box::new(outer_key.clone()),
                    value: Box::new(f.ty.clone()),
                    span: f.span.clone(),
                },
            };
            new_state.push(StateVar {
                name: synth,
                ty,
                init: None,
                span: sv.span.clone(),
            });
        }
        exploded_structs.insert(sdef.name.clone());
    }
    c.state = new_state;
    // Step 2: drop each exploded struct with no REMAINING type reference (state,
    // params/returns, ctor params, locals in every body, other structs' fields).
    if !exploded_structs.is_empty() {
        let mut referenced: HashSet<String> = HashSet::new();
        let note_ty = |ty: &TypeRef, referenced: &mut HashSet<String>| {
            collect_scalar_names(ty, referenced);
        };
        for sv in &c.state {
            note_ty(&sv.ty, &mut referenced);
        }
        for s in &c.structs {
            for f in &s.fields {
                note_ty(&f.ty, &mut referenced);
            }
        }
        for f in &c.functions {
            for prm in &f.params {
                note_ty(&prm.ty, &mut referenced);
            }
            if let Some(r) = &f.ret {
                note_ty(r, &mut referenced);
            }
            collect_local_tys(&f.body, &mut referenced);
        }
        for m in &c.modifiers {
            collect_local_tys(&m.body, &mut referenced);
        }
        if let Some(ctor) = &c.constructor {
            for prm in &ctor.params {
                note_ty(&prm.ty, &mut referenced);
            }
            collect_local_tys(&ctor.body, &mut referenced);
        }
        c.structs
            .retain(|s| !exploded_structs.contains(&s.name) || referenced.contains(&s.name));
    }
    // Step 3: the fail-closed sweep — a `__fe_sm_` reference the parse rewrite minted
    // that step 1 did NOT synthesize (a non-struct-map `x[k].f`, a chained `.f.g`, a
    // bailed non-bounded struct) → a PRECISE reject.
    let mut residual: Option<(String, Range<usize>)> = None;
    for f in &c.functions {
        scan_residual_sm(&f.body, &synthesized, &removed, &mut residual);
    }
    for m in &c.modifiers {
        scan_residual_sm(&m.body, &synthesized, &removed, &mut residual);
    }
    if let Some(ctor) = &c.constructor {
        scan_residual_sm(&ctor.body, &synthesized, &removed, &mut residual);
    }
    if let Some((name, span)) = residual {
        if removed.contains(&name) {
            // A surviving reference to the EXPLODED map itself — a whole-`M[k]` struct
            // copy / read (illegal Solidity for a mapping-bearing struct anyway) or the
            // bare var passed around. Without this, the user would see a baffling
            // "undeclared variable `M`" for a variable they declared.
            return Err(FrontendDiag::new(
                codes::FE441_BAD_MAP_KV_SOL,
                format!(
                    "`{name}` is a mapping-to-struct exploded into per-field maps; only `{name}[key].<field>` accesses are supported (a whole-struct read/copy is not)"
                ),
                span,
            ));
        }
        // Recover the `<var>.<field>` the parse rewrite encoded (`__fe_sm_<len>_<var>_<field>`),
        // for the diagnostic — read the length prefix, then split var/field precisely.
        let path = decode_struct_map_name(&name).unwrap_or_else(|| name.clone());
        return Err(FrontendDiag::new(
            codes::FE441_BAD_MAP_KV_SOL,
            format!(
                "`{path}` (a `var[key].field` access) does not resolve to a bounded struct-map: the base is not a `mapping(K => Struct)` whose fields are all scalars or single-level mappings"
            ),
            span,
        ));
    }
    Ok(())
}

/// Decode `__fe_sm_<len>_<var>_<field>` back to `<var>.<field>` for a diagnostic (the
/// length prefix pins the var/field split unambiguously — the injective encoding). `None`
/// on any malformed shape (a defensive fallback to the raw name in the caller).
pub(super) fn decode_struct_map_name(name: &str) -> Option<String> {
    let rest = name.strip_prefix("__fe_sm_")?;
    let us = rest.find('_')?;
    let len: usize = rest[..us].parse().ok()?;
    let after = &rest[us + 1..];
    if after.len() < len + 1 || after.as_bytes().get(len) != Some(&b'_') {
        return None;
    }
    let var = &after[..len];
    let field = &after[len + 1..];
    Some(format!("{var}.{field}"))
}

/// Every `Scalar` type NAME mentioned in a TypeRef (recursing mappings) — the
/// struct-drop reference scan.
pub(super) fn collect_scalar_names(ty: &TypeRef, out: &mut HashSet<String>) {
    match ty {
        TypeRef::Scalar { name, .. } => {
            out.insert(name.clone());
        }
        TypeRef::Mapping { key, value, .. } => {
            collect_scalar_names(key, out);
            collect_scalar_names(value, out);
        }
        // SOL-AIRDROP: recurse the element so the array's scalar element name is counted as a
        // reference (mirrors the mapping recursion; keeps the struct-drop scan conservative).
        TypeRef::Array { elem, .. } => collect_scalar_names(elem, out),
    }
}

/// Local-declaration types in a body (recursing branches) — the struct-drop scan.
pub(super) fn collect_local_tys(body: &[Stmt], out: &mut HashSet<String>) {
    for s in body {
        match s {
            Stmt::LocalVar { ty, .. } => collect_scalar_names(ty, out),
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_local_tys(then_body, out);
                collect_local_tys(else_body, out);
            }
            Stmt::Unchecked { body, .. } => collect_local_tys(body, out),
            _ => {}
        }
    }
}

/// First `__fe_sm_`-prefixed `Var` NOT in the synthesized set, anywhere in a body
/// (statements + expressions). Runs PRE-desugar, so the recognizer-produced atomic
/// `Stmt`s cannot exist yet — their arms are defensive recursion, kept total (no
/// `_ =>` catch-all; the walker-totality discipline).
pub(super) fn scan_residual_sm(
    body: &[Stmt],
    synthesized: &HashSet<String>,
    removed: &HashSet<String>,
    out: &mut Option<(String, Range<usize>)>,
) {
    let expr = |e: &Expr, out: &mut Option<(String, Range<usize>)>| {
        scan_residual_sm_expr(e, synthesized, removed, out);
    };
    for s in body {
        match s {
            Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => expr(cond, out),
            Stmt::Return { value: Some(v), .. } => expr(v, out),
            Stmt::Return { value: None, .. } | Stmt::Revert { .. } | Stmt::Placeholder { .. } => {}
            Stmt::CallStmt { args, .. } => {
                for a in args {
                    expr(a, out);
                }
            }
            Stmt::LocalVar { value, .. }
            | Stmt::Assign { value, .. }
            | Stmt::FieldAssign { value, .. } => expr(value, out),
            Stmt::IndexAssign { key, value, .. } => {
                expr(key, out);
                expr(value, out);
            }
            Stmt::IndexAssign2 { k1, k2, value, .. } => {
                expr(k1, out);
                expr(k2, out);
                expr(value, out);
            }
            Stmt::MapTransfer {
                from, to, amount, ..
            } => {
                expr(from, out);
                expr(to, out);
                expr(amount, out);
            }
            Stmt::Erc20TransferFrom {
                from,
                spender,
                to,
                amount,
                ..
            } => {
                expr(from, out);
                expr(spender, out);
                expr(to, out);
                expr(amount, out);
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
                expr(from, out);
                expr(amount, out);
                expr(to, out);
                expr(net, out);
                expr(fee_to, out);
                expr(fee, out);
            }
            Stmt::Erc20Update {
                from, to, value, ..
            } => {
                expr(from, out);
                expr(to, out);
                expr(value, out);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                expr(cond, out);
                scan_residual_sm(then_body, synthesized, removed, out);
                scan_residual_sm(else_body, synthesized, removed, out);
            }
            Stmt::Unchecked { body, .. } => scan_residual_sm(body, synthesized, removed, out),
            Stmt::ReservedBatch {
                transfer, writes, ..
            } => {
                if let Some(t) = transfer {
                    scan_residual_sm(std::slice::from_ref(t.as_ref()), synthesized, removed, out);
                }
                scan_residual_sm(writes, synthesized, removed, out);
            }
            // SOL-AIRDROP: the raw loop is present PRE-desugar — recurse its body (defensive
            // totality, like the other body-bearing arms; the fn keeps no `_ =>` catch-all).
            Stmt::AirdropLoop { body, .. } => scan_residual_sm(body, synthesized, removed, out),
            // BatchTransfer is produced post-recognize; recurse its lone `from` operand (Erc20Update).
            Stmt::BatchTransfer { from, .. } => expr(from, out),
        }
    }
}

pub(super) fn scan_residual_sm_expr(
    e: &Expr,
    synthesized: &HashSet<String>,
    removed: &HashSet<String>,
    out: &mut Option<(String, Range<usize>)>,
) {
    if out.is_some() {
        return;
    }
    match e {
        Expr::Var(name, span) => {
            if (name.starts_with("__fe_sm_") && !synthesized.contains(name))
                || removed.contains(name)
            {
                *out = Some((name.clone(), span.clone()));
            }
        }
        Expr::Unary(_, inner, _) => scan_residual_sm_expr(inner, synthesized, removed, out),
        Expr::Bin(_, l, r, _) => {
            scan_residual_sm_expr(l, synthesized, removed, out);
            scan_residual_sm_expr(r, synthesized, removed, out);
        }
        Expr::Member(base, _, _) => scan_residual_sm_expr(base, synthesized, removed, out),
        Expr::Call(callee, args, _) => {
            scan_residual_sm_expr(callee, synthesized, removed, out);
            for a in args {
                scan_residual_sm_expr(a, synthesized, removed, out);
            }
        }
        Expr::Index(b, k, _) => {
            scan_residual_sm_expr(b, synthesized, removed, out);
            scan_residual_sm_expr(k, synthesized, removed, out);
        }
        Expr::Num(..) | Expr::Bool(..) => {}
    }
}

pub(in crate::solidity) fn disambiguate_overloads(c: &mut Contract) -> Result<(), FrontendDiag> {
    // A name is overloaded iff it has ≥2 distinct arities (post-merge each `(name, arity)` is unique,
    // so ≥2 functions of one name ⇒ ≥2 arities).
    let mut arities: std::collections::HashMap<String, std::collections::HashSet<usize>> =
        std::collections::HashMap::new();
    for f in &c.functions {
        arities
            .entry(f.name.clone())
            .or_default()
            .insert(f.params.len());
    }
    let ov: std::collections::HashMap<String, std::collections::HashSet<usize>> = arities
        .into_iter()
        .filter(|(_, set)| set.len() > 1)
        .collect();
    if ov.is_empty() {
        return Ok(());
    }
    // 1. Rename the definitions.
    for f in &mut c.functions {
        if ov.contains_key(&f.name) {
            f.name = mangle_overload(&f.name, f.params.len());
        }
    }
    // 2. Rewrite every call site (function bodies + modifier bodies + the constructor body).
    for f in &mut c.functions {
        rewrite_ov_stmts(&mut f.body, &ov)?;
    }
    for m in &mut c.modifiers {
        rewrite_ov_stmts(&mut m.body, &ov)?;
    }
    if let Some(ctor) = &mut c.constructor {
        rewrite_ov_stmts(&mut ctor.body, &ov)?;
    }
    Ok(())
}

pub(super) fn ov_arity_err(name: &str, n: usize, span: Range<usize>) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE420_BAD_IDENTIFIER_SOL,
        format!(
            "call to overloaded `{name}` with {n} argument(s) matches no declared overload arity"
        ),
        span,
    )
}

pub(super) fn rewrite_ov_stmts(
    stmts: &mut [Stmt],
    ov: &std::collections::HashMap<String, std::collections::HashSet<usize>>,
) -> Result<(), FrontendDiag> {
    for s in stmts.iter_mut() {
        rewrite_ov_stmt(s, ov)?;
    }
    Ok(())
}

pub(super) fn rewrite_ov_stmt(
    s: &mut Stmt,
    ov: &std::collections::HashMap<String, std::collections::HashSet<usize>>,
) -> Result<(), FrontendDiag> {
    match s {
        // SOL-CALLS: a bare void internal call — the overload rewrite's primary target (e.g. the
        // OZ `_approve(owner, spender, value, false);` 4-arg call). Rewrite args first, then the
        // callee by its argument count.
        Stmt::CallStmt { callee, args, span } => {
            for a in args.iter_mut() {
                rewrite_ov_expr(a, ov)?;
            }
            if let Some(set) = ov.get(callee.as_str()) {
                if !set.contains(&args.len()) {
                    return Err(ov_arity_err(callee, args.len(), span.clone()));
                }
                *callee = mangle_overload(callee, args.len());
            }
        }
        Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => rewrite_ov_expr(cond, ov)?,
        Stmt::Assign { value, .. }
        | Stmt::LocalVar { value, .. }
        | Stmt::FieldAssign { value, .. } => rewrite_ov_expr(value, ov)?,
        Stmt::IndexAssign { key, value, .. } => {
            rewrite_ov_expr(key, ov)?;
            rewrite_ov_expr(value, ov)?;
        }
        Stmt::IndexAssign2 { k1, k2, value, .. } => {
            rewrite_ov_expr(k1, ov)?;
            rewrite_ov_expr(k2, ov)?;
            rewrite_ov_expr(value, ov)?;
        }
        Stmt::Return { value, .. } => {
            if let Some(v) = value {
                rewrite_ov_expr(v, ov)?;
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            rewrite_ov_expr(cond, ov)?;
            rewrite_ov_stmts(then_body, ov)?;
            rewrite_ov_stmts(else_body, ov)?;
        }
        // Defensive: `unwrap_unchecked` already ran (translate order), so this is normally gone.
        Stmt::Unchecked { body, .. } => rewrite_ov_stmts(body, ov)?,
        // SOL-AIRDROP: the raw loop can hold an overloaded call in its body — recurse like `if`.
        Stmt::AirdropLoop { body, .. } => rewrite_ov_stmts(body, ov)?,
        // No overloaded call to rewrite: `revert()`/`_;`, and the recognized-atomic statements
        // (produced by LATER recognize passes — none exist at this early pass; pure operands only).
        Stmt::Revert { .. }
        | Stmt::Placeholder { .. }
        | Stmt::MapTransfer { .. }
        | Stmt::Erc20TransferFrom { .. }
        | Stmt::ReservedBatch { .. }
        | Stmt::MapSplitTransfer { .. }
        | Stmt::Erc20Update { .. }
        | Stmt::BatchTransfer { .. } => {}
    }
    Ok(())
}

pub(super) fn rewrite_ov_expr(
    e: &mut Expr,
    ov: &std::collections::HashMap<String, std::collections::HashSet<usize>>,
) -> Result<(), FrontendDiag> {
    match e {
        Expr::Call(callee, args, span) => {
            for a in args.iter_mut() {
                rewrite_ov_expr(a, ov)?;
            }
            // An overloaded VALUE-returning call in expression position (a bare `Var` callee).
            if let Expr::Var(name, _) = callee.as_ref() {
                if let Some(set) = ov.get(name.as_str()) {
                    if !set.contains(&args.len()) {
                        return Err(ov_arity_err(name, args.len(), span.clone()));
                    }
                    let mangled = mangle_overload(name, args.len());
                    if let Expr::Var(n, _) = callee.as_mut() {
                        *n = mangled;
                    }
                }
            } else {
                rewrite_ov_expr(callee, ov)?;
            }
        }
        Expr::Member(b, _, _) => rewrite_ov_expr(b, ov)?,
        Expr::Index(b, k, _) => {
            rewrite_ov_expr(b, ov)?;
            rewrite_ov_expr(k, ov)?;
        }
        Expr::Unary(_, x, _) => rewrite_ov_expr(x, ov)?,
        Expr::Bin(_, l, r, _) => {
            rewrite_ov_expr(l, ov)?;
            rewrite_ov_expr(r, ov)?;
        }
        Expr::Num(..) | Expr::Bool(..) | Expr::Var(..) => {}
    }
    Ok(())
}

// ── pass 2: &&/|| ANF desugar ────────────────────────────────────────────────

#[derive(Default)]
pub(super) struct D {
    counter: u32,
}

impl D {
    fn fresh(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("{SYNTH_PREFIX}{n}")
    }

    pub(super) fn block(&mut self, stmts: Vec<Stmt>) -> Result<Vec<Stmt>, FrontendDiag> {
        let mut out = Vec::new();
        for s in stmts {
            self.stmt(s, &mut out)?;
        }
        Ok(out)
    }

    fn stmt(&mut self, s: Stmt, out: &mut Vec<Stmt>) -> Result<(), FrontendDiag> {
        match s {
            Stmt::Require { cond, span } => {
                let cond = self.expr(cond, out)?;
                out.push(Stmt::Require { cond, span });
            }
            Stmt::Assert { cond, span } => {
                let cond = self.expr(cond, out)?;
                out.push(Stmt::Assert { cond, span });
            }
            // MapTransfer is produced by the LATER recognize pass; Placeholder is removed
            // by the EARLIER inline_modifiers pass — neither is seen here. `ReservedBatch` is
            // produced by the LATER `reserve_multi_map` pass. Push as-is so a stray one survives
            // to check/emit's defensive FE500 rather than vanishing.
            Stmt::Revert { .. }
            | Stmt::Unchecked { .. }
            | Stmt::MapTransfer { .. }
            | Stmt::Erc20TransferFrom { .. }
            | Stmt::CallStmt { .. }
            | Stmt::ReservedBatch { .. }
            | Stmt::MapSplitTransfer { .. }
            | Stmt::Erc20Update { .. }
            | Stmt::BatchTransfer { .. }
            | Stmt::Placeholder { .. } => out.push(s),
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => {
                let value = self.expr(value, out)?;
                out.push(Stmt::Assign {
                    target,
                    op,
                    value,
                    span,
                });
            }
            Stmt::FieldAssign {
                obj,
                field,
                op,
                value,
                span,
            } => {
                let value = self.expr(value, out)?;
                out.push(Stmt::FieldAssign {
                    obj,
                    field,
                    op,
                    value,
                    span,
                });
            }
            Stmt::IndexAssign {
                map,
                key,
                op,
                value,
                span,
            } => {
                let key = self.expr(key, out)?;
                let value = self.expr(value, out)?;
                out.push(Stmt::IndexAssign {
                    map,
                    key,
                    op,
                    value,
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
                let k1 = self.expr(k1, out)?;
                let k2 = self.expr(k2, out)?;
                let value = self.expr(value, out)?;
                out.push(Stmt::IndexAssign2 {
                    map,
                    k1,
                    k2,
                    op,
                    value,
                    span,
                });
            }
            Stmt::LocalVar {
                name,
                ty,
                value,
                span,
            } => {
                let value = self.expr(value, out)?;
                out.push(Stmt::LocalVar {
                    name,
                    ty,
                    value,
                    span,
                });
            }
            Stmt::Return { value, span } => {
                let value = match value {
                    Some(e) => Some(self.expr(e, out)?),
                    None => None,
                };
                out.push(Stmt::Return { value, span });
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => {
                // An `if` condition is evaluated once, so hoisting its &&/|| before the
                // `if` is correct.
                let cond = self.expr(cond, out)?;
                let then_body = self.block(then_body)?;
                let else_body = self.block(else_body)?;
                out.push(Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    span,
                });
            }
            // SOL-AIRDROP: ANF the loop body like an `if` block (the header names carry no
            // &&/|| to hoist; keep idx/len_array/span).
            Stmt::AirdropLoop {
                idx,
                len_array,
                body,
                span,
            } => {
                let body = self.block(body)?;
                out.push(Stmt::AirdropLoop {
                    idx,
                    len_array,
                    body,
                    span,
                });
            }
        }
        Ok(())
    }

    /// Replace every `&&`/`||` in `e` with a fresh `bool` temp, appending the hoist
    /// statements to `out` in evaluation order. The RHS of a logical op hoists INSIDE
    /// the guard so it runs only on the short-circuit-reachable path.
    fn expr(&mut self, e: Expr, out: &mut Vec<Stmt>) -> Result<Expr, FrontendDiag> {
        match e {
            Expr::Bin(BinOp::And, l, r, span) => {
                let l = self.expr(*l, out)?;
                let n = self.fresh();
                self.push_bool_let(out, &n, l, &span);
                // RHS only when LHS is true.
                let mut guarded = Vec::new();
                let r = self.expr(*r, &mut guarded)?;
                guarded.push(assign(&n, r, &span));
                out.push(Stmt::If {
                    cond: Expr::Var(n.clone(), span.clone()),
                    then_body: guarded,
                    else_body: Vec::new(),
                    span: span.clone(),
                });
                Ok(Expr::Var(n, span))
            }
            Expr::Bin(BinOp::Or, l, r, span) => {
                let l = self.expr(*l, out)?;
                let n = self.fresh();
                self.push_bool_let(out, &n, l, &span);
                // RHS only when LHS is false.
                let mut guarded = Vec::new();
                let r = self.expr(*r, &mut guarded)?;
                guarded.push(assign(&n, r, &span));
                out.push(Stmt::If {
                    cond: Expr::Var(n.clone(), span.clone()),
                    then_body: Vec::new(),
                    else_body: guarded,
                    span: span.clone(),
                });
                Ok(Expr::Var(n, span))
            }
            Expr::Bin(op, l, r, span) => {
                let l = self.expr(*l, out)?;
                let r = self.expr(*r, out)?;
                Ok(Expr::Bin(op, Box::new(l), Box::new(r), span))
            }
            Expr::Unary(op, x, span) => {
                let x = self.expr(*x, out)?;
                Ok(Expr::Unary(op, Box::new(x), span))
            }
            Expr::Index(b, k, span) => {
                let b = self.expr(*b, out)?;
                let k = self.expr(*k, out)?;
                Ok(Expr::Index(Box::new(b), Box::new(k), span))
            }
            Expr::Member(b, m, span) => {
                let b = self.expr(*b, out)?;
                Ok(Expr::Member(Box::new(b), m, span))
            }
            Expr::Call(callee, args, span) => {
                let callee = self.expr(*callee, out)?;
                let mut new_args = Vec::with_capacity(args.len());
                for a in args {
                    new_args.push(self.expr(a, out)?);
                }
                Ok(Expr::Call(Box::new(callee), new_args, span))
            }
            leaf @ (Expr::Num(..) | Expr::Bool(..) | Expr::Var(..)) => Ok(leaf),
        }
    }

    fn push_bool_let(&self, out: &mut Vec<Stmt>, name: &str, value: Expr, span: &Range<usize>) {
        out.push(Stmt::LocalVar {
            name: name.to_string(),
            ty: TypeRef::Scalar {
                name: "bool".to_string(),
                span: span.clone(),
            },
            value,
            span: span.clone(),
        });
    }
}

pub(super) fn assign(name: &str, value: Expr, span: &Range<usize>) -> Stmt {
    Stmt::Assign {
        target: name.to_string(),
        op: AssignOp::Eq,
        value,
        span: span.clone(),
    }
}
