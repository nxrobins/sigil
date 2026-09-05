//! SIGIL emitter for the SOL0 subset. Runs AFTER `check::check`, so it may assume
//! the program is in-subset. Lowering, in brief:
//! `contract X { state… fns… }` becomes `record X { fields }` + `impl X { new(); methods }`;
//! `uint256`/`uint` become `u256` and `bool` stays `bool`; state-var initializers
//! (or the zero-default) populate a synthesized `new()` constructor — the single
//! construction site (NC-S4); `require(c)`/`assert(c)` become `trap_if(!(c));` and
//! `revert …` becomes `trap_if(true);`; compound assigns expand (`x -= e` to
//! `x = x - e`) and a bare state-field reference resolves to `self.field`.
//! Ends with a parse self-check (FE500): emitted SIGIL that does not parse is a
//! translator bug, never a user fault.

use super::desugar::CapGuardInfo;
use super::parser::{
    AssignOp, BinOp, Contract, Enum, Expr, Function, Program, StateMutability, StateVar, Stmt,
    Struct, TypeRef, UnOp, Visibility,
};
use crate::{
    EmittedSigil, FrontendDiag, SourceMap, codes, is_legal_identifier, parse_emitted_sigil,
    sanitize_module_name,
};
use std::collections::HashSet;

pub(crate) fn emit(
    p: &Program,
    source_name: &str,
    cap: Option<&CapGuardInfo>,
    uintn: super::check::UintnHelpers,
) -> Result<EmittedSigil, FrontendDiag> {
    let c = &p.contract;
    let state: HashSet<&str> = c.state.iter().map(|s| s.name.as_str()).collect();

    let mut out = String::new();
    let module = sanitize_module_name(source_name, "contract");
    out.push_str(&format!("module {module};\n\n"));

    // SOL-uintN: the width-trap helpers the lowering pass produced (free fns, reserved
    // `__fe_` prefix). Emitted ONLY when used, so a no-uintN-arithmetic contract is
    // byte-identical (EX-9). Each does the checked `u256` op then traps at the per-width
    // `2^N` bound — the carrier alone only traps at `2^256` (EX-1). The trusted compiler
    // re-verifies these bodies (the M-spike proves they compile + trap).
    if uintn.add {
        out.push_str(
            "fn __fe_add_checked(a: u256, b: u256, bound: u256) -> u256 { let r = (a + b); trap_if(r >= bound); return r; }\n\n",
        );
    }
    if uintn.mul {
        out.push_str(
            "fn __fe_mul_checked(a: u256, b: u256, bound: u256) -> u256 { let r = (a * b); trap_if(r >= bound); return r; }\n\n",
        );
    }

    // SOL-CAP: the access-controlling address field is replaced by an unforgeable cap. Emit
    // the per-contract authority cap decls, and DROP that field from the record/constructor
    // (E-2 guarantees it has no other use). `cap` is `None` ⇒ none of this runs ⇒ the output
    // is byte-identical SOL1c (IMPL-2).
    let owner_field: Option<&str> = cap.map(|i| i.owner_field.as_str());
    if cap.is_some() {
        let owner = owner_cap_name(c);
        let deploy = deploy_cap_name(c);
        validate_cap_names(c, &owner, &deploy)?; // IMPL-3 / FE457
        out.push_str(&format!("cap type {deploy} {{ mint_owner }}\n"));
        out.push_str(&format!(
            "cap type {owner} mintable_by {deploy} {{ all }}\n\n"
        ));
    }

    // SOL-STRUCT: emit each user `struct` as a top-level `record` BEFORE the contract
    // record (declaration order). A struct field lowers via `map_type` like any field.
    for st in &c.structs {
        out.push_str(&format!("record {} {{", st.name));
        for (i, f) in st.fields.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            out.push_str(&format!(" {}: {}", f.name, map_type(&f.ty, &c.enums)));
        }
        out.push_str(" }\n\n");
    }

    // record (state fields, in source order; SOL-CAP drops the owner field).
    out.push_str(&format!("record {} {{", c.name));
    let mut nfields = 0;
    for sv in c
        .state
        .iter()
        .filter(|sv| Some(sv.name.as_str()) != owner_field)
    {
        if nfields > 0 {
            out.push(',');
        }
        out.push_str(&format!(" {}: {}", sv.name, map_type(&sv.ty, &c.enums)));
        nfields += 1;
    }
    if nfields == 0 {
        // SIGIL records need at least one field; a stateless contract gets a unit marker.
        out.push_str(" __fe_unit: bool");
    }
    out.push_str(" }\n\n");

    // impl block: a `new()` constructor (zero-default, NC-S4) + the methods.
    out.push_str(&format!("impl {} {{\n", c.name));
    emit_constructor(&mut out, c, owner_field)?;
    for f in &c.functions {
        out.push('\n');
        emit_function(&mut out, c, f, &state, cap)?;
    }
    out.push_str("}\n");

    let text = out;
    parse_emitted_sigil(&module, &text, codes::FE500_INTERNAL_MALFORMED_SOL)?;
    Ok(EmittedSigil {
        source_name: format!("{module}.sigil"),
        map: SourceMap {
            entries: Vec::new(),
            emitted_len: text.len(),
        },
        text,
    })
}

/// `new()` — the single construction site. Each field gets its literal initializer
/// or the implicit zero-default (NC-S4): `0` for `u256`, `false` for `bool`.
/// SOL-CTOR (`c.constructor` = `Some`): `new(params)` BUILDS the record as a local
/// `__fe_c`, runs the deploy-time init body on it (recv = `"__fe_c"`), and returns it
/// (cap+ctor is FE465-rejected upstream, so `owner_field` is `None` here).
/// SOL-CAP (`owner_field` = `Some`): `new` additionally takes the deploy authority,
/// mints the root owner cap, and returns `(C, C_Owner)`; the owner field is dropped.
fn emit_constructor(
    out: &mut String,
    c: &Contract,
    owner_field: Option<&str>,
) -> Result<(), FrontendDiag> {
    let fields: Vec<&StateVar> = c
        .state
        .iter()
        .filter(|sv| Some(sv.name.as_str()) != owner_field)
        .collect();
    if let Some(ctor) = &c.constructor {
        // SOL-CTOR: build the record (EX-1: every field seeded), run the body on the LOCAL
        // `__fe_c` (EX-2: CEI-moot), return it. Params were already augmented by desugar
        // (a `__fe_sender` deployer param prepended iff the body uses `msg.sender`).
        let state: HashSet<&str> = c.state.iter().map(|s| s.name.as_str()).collect();
        out.push_str("    pub fn new(");
        let mut locals: HashSet<String> = HashSet::new();
        for (i, p) in ctor.params.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            out.push_str(&format!("{}: {}", p.name, map_type(&p.ty, &c.enums)));
            locals.insert(p.name.clone());
        }
        out.push_str(&format!(") -> {} {{\n", c.name));
        out.push_str(&format!("        let mut __fe_c = {} {{", c.name));
        emit_field_inits(out, &fields, &c.structs, &c.enums);
        out.push_str(" };\n");
        emit_stmts(
            out,
            &ctor.body,
            &state,
            &mut locals,
            2,
            &c.structs,
            &c.enums,
            "__fe_c",
        )?;
        out.push_str("        return __fe_c;\n    }\n");
        return Ok(());
    }
    if owner_field.is_some() {
        let owner = owner_cap_name(c);
        let deploy = deploy_cap_name(c);
        out.push_str(&format!(
            "    pub fn new(__fe_deploy: &{deploy}) -> ({}, {owner}) {{\n",
            c.name
        ));
        out.push_str(&format!("        let __fe_c = {} {{", c.name));
        emit_field_inits(out, &fields, &c.structs, &c.enums);
        out.push_str(" };\n");
        out.push_str(&format!(
            "        return (__fe_c, mint {owner} for __fe_c);\n"
        ));
        out.push_str("    }\n");
    } else {
        out.push_str(&format!("    pub fn new() -> {} {{\n", c.name));
        out.push_str(&format!("        return {} {{", c.name));
        emit_field_inits(out, &fields, &c.structs, &c.enums);
        out.push_str(" };\n    }\n");
    }
    Ok(())
}

/// Emit ` field: value, …` for a record literal (literal initializer or zero-default).
/// An empty field set emits the `__fe_unit` marker (SIGIL records need ≥1 field).
fn emit_field_inits(out: &mut String, fields: &[&StateVar], structs: &[Struct], enums: &[Enum]) {
    if fields.is_empty() {
        out.push_str(" __fe_unit: false");
    }
    for (i, sv) in fields.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let val = match &sv.init {
            Some(Expr::Num(t, _)) => t.clone(),
            Some(Expr::Bool(b, _)) => b.to_string(),
            _ => zero_default(&sv.ty, structs, enums),
        };
        out.push_str(&format!(" {}: {}", sv.name, val));
    }
}

/// SOL-CAP synthesized cap-type names (`{Contract}_Owner` / `{Contract}_Deploy`).
fn owner_cap_name(c: &Contract) -> String {
    format!("{}_Owner", c.name)
}
fn deploy_cap_name(c: &Contract) -> String {
    format!("{}_Deploy", c.name)
}

/// IMPL-3 / FE457: every synthesized cap-type name must be a legal SIGIL identifier
/// (≤ 64 bytes, charset) AND not collide with the contract record or a function name (a
/// collision would be N002 at name-resolution, invisible to the FE500 parse self-check).
fn validate_cap_names(c: &Contract, owner: &str, deploy: &str) -> Result<(), FrontendDiag> {
    let mut taken: HashSet<&str> = HashSet::new();
    taken.insert(c.name.as_str());
    for f in &c.functions {
        taken.insert(f.name.as_str());
    }
    for nm in [owner, deploy] {
        if !is_legal_identifier(nm) {
            return Err(FrontendDiag::new(
                codes::FE457_CAP_NAME_COLLISION_SOL,
                format!(
                    "cap-mode: synthesized cap-type name `{nm}` is not a legal SIGIL identifier (exceeds 64 bytes?)"
                ),
                c.span.clone(),
            ));
        }
        if taken.contains(nm) {
            return Err(FrontendDiag::new(
                codes::FE457_CAP_NAME_COLLISION_SOL,
                format!(
                    "cap-mode: synthesized cap-type name `{nm}` collides with the contract record or a function name"
                ),
                c.span.clone(),
            ));
        }
    }
    Ok(())
}

fn emit_function(
    out: &mut String,
    c: &Contract,
    f: &Function,
    state: &HashSet<&str>,
    cap: Option<&CapGuardInfo>,
) -> Result<(), FrontendDiag> {
    // E1 (the headline SOL1c guard): a function reaching emit MUST have had every modifier
    // inlined by desugar::inline_modifiers. A non-empty list here means a guard was NOT
    // inlined — for a security translator, emitting a function with a dropped `onlyOwner`
    // check is the existential failure. Fail loud (FE500), never best-effort.
    if !f.modifiers.is_empty() {
        return Err(FrontendDiag::new(
            codes::FE500_INTERNAL_MALFORMED_SOL,
            format!(
                "internal: function `{}` reached emit with un-inlined modifiers {:?}",
                f.name, f.modifiers
            ),
            f.span.clone(),
        ));
    }
    // Visibility (AG-S1 fidelity nicety: private/internal → non-pub).
    let pub_kw = match f.visibility {
        Visibility::Private | Visibility::Internal => "",
        _ => "pub ",
    };
    // view/pure read-only → `self: X`; otherwise `self: X @Mut`.
    let self_mut = match f.mutability {
        StateMutability::View | StateMutability::Pure => "",
        StateMutability::NonPayable => " @Mut",
    };
    out.push_str(&format!(
        "    {pub_kw}fn {}(self: {}{self_mut}",
        f.name, c.name
    ));
    // SOL-CAP: a guarded method takes the unforgeable owner cap right after `self` — the
    // gate. A caller without `&C_Owner` cannot form the call (vs the dropped forgeable
    // `__fe_sender == owner` trap). The borrow is unreferenced in the body (no consume-sink
    // needed; the spike confirmed an unused `&Cap` param compiles).
    if let Some(info) = cap
        && info.guarded_methods.contains(&f.name)
    {
        out.push_str(&format!(", __fe_owner: &{}", owner_cap_name(c)));
    }
    // Locals visible in the body = params (+ LocalVar decls, tracked as we go).
    let mut locals: HashSet<String> = HashSet::new();
    for p in &f.params {
        out.push_str(&format!(", {}: {}", p.name, map_type(&p.ty, &c.enums)));
        locals.insert(p.name.clone());
    }
    out.push(')');
    if let Some(rt) = &f.ret {
        out.push_str(&format!(" -> {}", map_type(rt, &c.enums)));
    }
    out.push_str(" {\n");
    emit_stmts(
        out,
        &f.body,
        state,
        &mut locals,
        2,
        &c.structs,
        &c.enums,
        "self",
    )?;
    out.push_str("    }\n");
    Ok(())
}

#[allow(clippy::too_many_arguments)] // SOL-ENUM added `enums` alongside `structs`; the emit
// walker threads the full lowering context (state/locals/structs/enums/recv) by necessity.
fn emit_stmts(
    out: &mut String,
    stmts: &[Stmt],
    state: &HashSet<&str>,
    locals: &mut HashSet<String>,
    indent: usize,
    structs: &[Struct],
    enums: &[Enum],
    recv: &str,
) -> Result<(), FrontendDiag> {
    let pad = "    ".repeat(indent);
    for s in stmts {
        match s {
            // SOL-CALLS: desugar must have inlined every internal call; a residual CallStmt at emit
            // is a translator bug (FE500), never user-facing.
            Stmt::CallStmt { span, .. } => {
                return Err(FrontendDiag::new(
                    codes::FE500_INTERNAL_MALFORMED_SOL,
                    "internal: an internal call statement reached emit (must be inlined by desugar)",
                    span.clone(),
                ));
            }
            // SOL-AIRDROP: `recognize_airdrop` folds every airdrop loop into a `BatchTransfer`
            // before emit; a residual loop is a fold bug (FE500).
            Stmt::AirdropLoop { span, .. } => {
                return Err(FrontendDiag::new(
                    codes::FE500_INTERNAL_MALFORMED_SOL,
                    "internal: an airdrop loop reached emit (must be folded by recognize_airdrop)",
                    span.clone(),
                ));
            }
            Stmt::BatchTransfer {
                map,
                from,
                recipients,
                amounts,
                ..
            } => {
                // SOL-AIRDROP (Rung C): the recognized N-ary airdrop → the TRUSTED atomic
                // `self.<map>.batch_transfer(from, recipients, amounts)` (debit `from` by each
                // amount, credit each recipient; reserve-all-then-write, aliasing-correct over N,
                // exec-proven). ONE storage op; the returned bool is discarded. `recipients`/
                // `amounts` are the bare array-param names (emitted `BoundedVec_u256_64`).
                let fe = emit_expr(from, state, locals, structs, recv)?;
                let mrecv = resolve_name(map, state, locals, recv);
                let re = resolve_name(recipients, state, locals, recv);
                let ame = resolve_name(amounts, state, locals, recv);
                out.push_str(&format!(
                    "{pad}{mrecv}.batch_transfer({fe}, {re}, {ame});\n"
                ));
            }
            Stmt::Require { cond, .. } | Stmt::Assert { cond, .. } => {
                // SOL-DIVERGE: a literal-`false` `require`/`assert` is an UNCONDITIONAL abort, so it
                // lowers to the divergent `trap()` (the bottom type `Never`, #442-444) — a
                // value-returning function whose tail is the abort then satisfies the return checker
                // (no T044 missing-return). A NON-constant condition STAYS the conditional
                // `trap_if(!(c))` (EX-1: emitting `trap()` for it would abort the fn unconditionally).
                if matches!(cond, Expr::Bool(false, _)) {
                    out.push_str(&format!("{pad}trap();\n"));
                } else {
                    let ce = emit_expr(cond, state, locals, structs, recv)?;
                    out.push_str(&format!("{pad}trap_if(!({ce}));\n"));
                }
            }
            Stmt::Revert { .. } => {
                // SOL-DIVERGE: `revert()` is ALWAYS an unconditional abort → the divergent `trap()`
                // (was `trap_if(true)`, a conditional Unit trap the return checker did not know
                // diverges — a value-returning fn ending in `revert()` was T044). The trusted compiler
                // accepts dead code after a diverging `trap()`, so no block truncation is needed.
                out.push_str(&format!("{pad}trap();\n"));
            }
            Stmt::Return { value, .. } => match value {
                Some(v) => {
                    let ve = emit_expr(v, state, locals, structs, recv)?;
                    out.push_str(&format!("{pad}return {ve};\n"));
                }
                None => out.push_str(&format!("{pad}return;\n")),
            },
            Stmt::LocalVar {
                name, ty, value, ..
            } => {
                let ve = emit_expr(value, state, locals, structs, recv)?;
                out.push_str(&format!(
                    "{pad}let mut {}: {} = {ve};\n",
                    name,
                    map_type(ty, enums)
                ));
                locals.insert(name.clone());
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let lhs = resolve_name(target, state, locals, recv);
                let ve = emit_expr(value, state, locals, structs, recv)?;
                let rhs = match op {
                    AssignOp::Eq => ve,
                    AssignOp::Plus => format!("{lhs} + ({ve})"),
                    AssignOp::Minus => format!("{lhs} - ({ve})"),
                    AssignOp::Star => format!("{lhs} * ({ve})"),
                    AssignOp::Slash => format!("{lhs} / ({ve})"),
                    AssignOp::Percent => format!("{lhs} % ({ve})"),
                };
                out.push_str(&format!("{pad}{lhs} = {rhs};\n"));
            }
            Stmt::FieldAssign {
                obj,
                field,
                op,
                value,
                ..
            } => {
                // A struct field write `obj.field op= v`: `obj` → `self.obj` (state field)
                // or `obj` (local); `op=` is read-modify-write via the field place.
                let ve = emit_expr(value, state, locals, structs, recv)?;
                let recv = resolve_name(obj, state, locals, recv);
                let lhs = format!("{recv}.{field}");
                let rhs = match op {
                    AssignOp::Eq => ve,
                    AssignOp::Plus => format!("{lhs} + ({ve})"),
                    AssignOp::Minus => format!("{lhs} - ({ve})"),
                    AssignOp::Star => format!("{lhs} * ({ve})"),
                    AssignOp::Slash => format!("{lhs} / ({ve})"),
                    AssignOp::Percent => format!("{lhs} % ({ve})"),
                };
                out.push_str(&format!("{pad}{lhs} = {rhs};\n"));
            }
            Stmt::IndexAssign {
                map,
                key,
                op,
                value,
                ..
            } => {
                // A mapping is always a state field → `self.<map>`. `m[k] = v` is a
                // single `insert`; `m[k] op= v` is read-modify-write via `get_or(k, 0)`
                // (the key is re-emitted, but SOL1 keys are pure — a var/literal — so
                // the double evaluation is benign).
                let ke = emit_expr(key, state, locals, structs, recv)?;
                let ve = emit_expr(value, state, locals, structs, recv)?;
                let recv = resolve_name(map, state, locals, recv);
                let stored = match op {
                    AssignOp::Eq => ve,
                    AssignOp::Plus => format!("{recv}.get_or({ke}, 0) + ({ve})"),
                    AssignOp::Minus => format!("{recv}.get_or({ke}, 0) - ({ve})"),
                    AssignOp::Star => format!("{recv}.get_or({ke}, 0) * ({ve})"),
                    AssignOp::Slash => format!("{recv}.get_or({ke}, 0) / ({ve})"),
                    AssignOp::Percent => format!("{recv}.get_or({ke}, 0) % ({ve})"),
                };
                out.push_str(&format!("{pad}{recv}.insert({ke}, {stored});\n"));
            }
            Stmt::IndexAssign2 {
                map,
                k1,
                k2,
                op,
                value,
                ..
            } => {
                // A two-key mapping field → `self.<map>`. `m[k1][k2] = v` is one
                // `insert(k1, k2, v)`; `m[k1][k2] op= v` is read-modify-write via
                // `get_or(k1, k2, 0)` (keys re-emitted, but SOL1 keys are pure).
                let k1e = emit_expr(k1, state, locals, structs, recv)?;
                let k2e = emit_expr(k2, state, locals, structs, recv)?;
                let ve = emit_expr(value, state, locals, structs, recv)?;
                let recv = resolve_name(map, state, locals, recv);
                let stored = match op {
                    AssignOp::Eq => ve,
                    AssignOp::Plus => format!("{recv}.get_or({k1e}, {k2e}, 0) + ({ve})"),
                    AssignOp::Minus => format!("{recv}.get_or({k1e}, {k2e}, 0) - ({ve})"),
                    AssignOp::Star => format!("{recv}.get_or({k1e}, {k2e}, 0) * ({ve})"),
                    AssignOp::Slash => format!("{recv}.get_or({k1e}, {k2e}, 0) / ({ve})"),
                    AssignOp::Percent => format!("{recv}.get_or({k1e}, {k2e}, 0) % ({ve})"),
                };
                out.push_str(&format!("{pad}{recv}.insert({k1e}, {k2e}, {stored});\n"));
            }
            Stmt::MapTransfer {
                map,
                from,
                to,
                amount,
                ..
            } => {
                // The recognized debit/credit idiom → the TRUSTED atomic transfer. The
                // bool result is discarded (it is always `true` when it returns; a failure
                // traps), exactly as `insert`'s i64 result is discarded above.
                let fe = emit_expr(from, state, locals, structs, recv)?;
                let te = emit_expr(to, state, locals, structs, recv)?;
                let ae = emit_expr(amount, state, locals, structs, recv)?;
                let recv = resolve_name(map, state, locals, recv);
                out.push_str(&format!("{pad}{recv}.transfer({fe}, {te}, {ae});\n"));
            }
            Stmt::MapSplitTransfer {
                map,
                from,
                amount,
                to,
                net,
                fee_to,
                fee,
                ..
            } => {
                // SOL-MULTIMAP M-B: the recognized fee-on-transfer split → the TRUSTED atomic
                // `transfer_split(from, amount, to, net, fee_to, fee)` (aliasing-correct across all 5
                // partitions of {from,to,fee_to}, all checks before any write). The bool is discarded.
                let fe = emit_expr(from, state, locals, structs, recv)?;
                let ae = emit_expr(amount, state, locals, structs, recv)?;
                let te = emit_expr(to, state, locals, structs, recv)?;
                let ne = emit_expr(net, state, locals, structs, recv)?;
                let xe = emit_expr(fee_to, state, locals, structs, recv)?;
                let ye = emit_expr(fee, state, locals, structs, recv)?;
                let recv = resolve_name(map, state, locals, recv);
                out.push_str(&format!(
                    "{pad}{recv}.transfer_split({fe}, {ae}, {te}, {ne}, {xe}, {ye});\n"
                ));
            }
            Stmt::Erc20Update {
                map,
                ts_field,
                from,
                to,
                value,
                ..
            } => {
                // SOL-UPDATE: the recognized OZ 5.x `_update` → the TRUSTED atomic
                // `erc20_update(ts, from, to, value)` (dynamic zero-address mint/burn/transfer
                // dispatch, aliasing-correct, ALL traps before any write — the `eu_*`
                // exec-proof), then the TRAP-FREE totalSupply store-back: a bare-Var `=` store,
                // which the CEI gate accepts after the committed map op. `__fe_ts` is
                // block-scoped and collision-free: at most ONE Erc20Update per block passes the
                // CEI gate (a second → FE412), a sibling `if` branch is its own emitted block,
                // and `__fe_` is a reserved prefix (no user identifier can collide).
                let fe = emit_expr(from, state, locals, structs, recv)?;
                let te = emit_expr(to, state, locals, structs, recv)?;
                let ve = emit_expr(value, state, locals, structs, recv)?;
                let mrecv = resolve_name(map, state, locals, recv);
                let tsrecv = resolve_name(ts_field, state, locals, recv);
                out.push_str(&format!(
                    "{pad}let __fe_ts: u256 = {mrecv}.erc20_update({tsrecv}, {fe}, {te}, {ve});\n"
                ));
                out.push_str(&format!("{pad}{tsrecv} = __fe_ts;\n"));
            }
            Stmt::Erc20TransferFrom {
                bal_map,
                alw_map,
                from,
                spender,
                to,
                amount,
                oz5_infinite,
                ..
            } => {
                // The recognized ERC20 transferFrom → the TRUSTED atomic cross-map primitive (S1: a
                // method on the allowance map taking the balances map as a `@Mut` param). Both maps
                // are state fields → `self.<field>`. The OZ 5.x shape (`oz5_infinite`) selects
                // `erc20_transfer_from` (zero-guarded + infinite-allowance skip); the OZ 4.x shape
                // selects `transfer_from`. Same operands either way.
                let alw = resolve_name(alw_map, state, locals, recv);
                let bal = resolve_name(bal_map, state, locals, recv);
                let fe = emit_expr(from, state, locals, structs, recv)?;
                let se = emit_expr(spender, state, locals, structs, recv)?;
                let te = emit_expr(to, state, locals, structs, recv)?;
                let ae = emit_expr(amount, state, locals, structs, recv)?;
                let method = if *oz5_infinite {
                    "erc20_transfer_from"
                } else {
                    "transfer_from"
                };
                out.push_str(&format!(
                    "{pad}{alw}.{method}({bal}, {fe}, {se}, {te}, {ae});\n"
                ));
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let ce = emit_expr(cond, state, locals, structs, recv)?;
                out.push_str(&format!("{pad}if {ce} {{\n"));
                // Each branch gets its OWN locals scope (a clone) so a block-local
                // does not leak past the branch — matching Solidity block scoping and
                // check::check_stmts, so a name resolves to the state field outside
                // the branch that shadowed it.
                let mut then_locals = locals.clone();
                emit_stmts(
                    out,
                    then_body,
                    state,
                    &mut then_locals,
                    indent + 1,
                    structs,
                    enums,
                    recv,
                )?;
                if else_body.is_empty() {
                    out.push_str(&format!("{pad}}}\n"));
                } else {
                    out.push_str(&format!("{pad}}} else {{\n"));
                    let mut else_locals = locals.clone();
                    emit_stmts(
                        out,
                        else_body,
                        state,
                        &mut else_locals,
                        indent + 1,
                        structs,
                        enums,
                        recv,
                    )?;
                    out.push_str(&format!("{pad}}}\n"));
                }
            }
            Stmt::Unchecked { span, .. } => {
                // Unreachable: `desugar::unwrap_unchecked` splices every `unchecked` body away.
                // Defensive (EX-4) — a residual node is an internal pass bug, fail loud.
                return Err(FrontendDiag::new(
                    codes::FE500_INTERNAL_MALFORMED_SOL,
                    "internal: an `unchecked` block reached emit (should be spliced by unwrap_unchecked)",
                    span.clone(),
                ));
            }
            Stmt::Placeholder { span } => {
                // Unreachable: inline_modifiers removed every placeholder. Defensive (E1).
                return Err(FrontendDiag::new(
                    codes::FE500_INTERNAL_MALFORMED_SOL,
                    "internal: a modifier `_` placeholder reached emit",
                    span.clone(),
                ));
            }
            Stmt::ReservedBatch {
                transfer,
                writes,
                span,
            } => {
                // SOL-MULTIMAP (M-A): reserve-all-then-write. Phase 2 — reserve every deferred plain
                // write's map (read-only, commits nothing). Phase 3 — the ≤1 self-atomic transfer (if it
                // traps, only reservations ran → nothing committed). Phase 4 — the trap-free inserts
                // (`reserve1/2` guaranteed room; the value was hoisted to a preceding `let __fe_rbN`). The
                // deferred maps are DISTINCT from each other and from the transfer's map(s), so the order
                // among the writes is immaterial and no write can trap after a commit.
                for w in writes {
                    match w {
                        Stmt::IndexAssign { map, key, .. } => {
                            let ke = emit_expr(key, state, locals, structs, recv)?;
                            let m = resolve_name(map, state, locals, recv);
                            out.push_str(&format!("{pad}{m}.reserve1({ke});\n"));
                        }
                        Stmt::IndexAssign2 { map, k1, k2, .. } => {
                            let k1e = emit_expr(k1, state, locals, structs, recv)?;
                            let k2e = emit_expr(k2, state, locals, structs, recv)?;
                            let m = resolve_name(map, state, locals, recv);
                            out.push_str(&format!("{pad}{m}.reserve2({k1e}, {k2e});\n"));
                        }
                        _ => {
                            return Err(FrontendDiag::new(
                                codes::FE500_INTERNAL_MALFORMED_SOL,
                                "internal: a ReservedBatch deferred write is not a map insert",
                                span.clone(),
                            ));
                        }
                    }
                }
                if let Some(t) = transfer {
                    emit_stmts(
                        out,
                        std::slice::from_ref(t.as_ref()),
                        state,
                        locals,
                        indent,
                        structs,
                        enums,
                        recv,
                    )?;
                }
                emit_stmts(out, writes, state, locals, indent, structs, enums, recv)?;
            }
        }
    }
    Ok(())
}

fn emit_expr(
    e: &Expr,
    state: &HashSet<&str>,
    locals: &HashSet<String>,
    structs: &[Struct],
    recv: &str,
) -> Result<String, FrontendDiag> {
    match e {
        Expr::Num(t, _) => Ok(t.clone()),
        Expr::Bool(b, _) => Ok(b.to_string()),
        Expr::Var(name, _) => Ok(resolve_name(name, state, locals, recv)),
        Expr::Unary(UnOp::Not, inner, _) => {
            let ie = emit_expr(inner, state, locals, structs, recv)?;
            Ok(format!("!({ie})"))
        }
        Expr::Unary(UnOp::Neg, _, span) => Err(FrontendDiag::new(
            codes::FE401_UNSUPPORTED_SOL,
            "unary minus is unsupported (u256 is unsigned)",
            span.clone(),
        )),
        Expr::Bin(op, l, r, _) => {
            let le = emit_expr(l, state, locals, structs, recv)?;
            let re = emit_expr(r, state, locals, structs, recv)?;
            Ok(format!("({le} {} {re})", bin_op(*op)))
        }
        // A mapping read `m[k]` → `self.m.get_or(k, 0)`; a two-key read `m[k1][k2]` →
        // `self.m.get_or(k1, k2, 0)` (the SOL default for an unset key is 0). check.rs
        // has verified `m` is a mapping field of the matching arity and the key types
        // match; the AST shape (`Var[k]` vs `Var[k1][k2]`) disambiguates the arity.
        Expr::Index(base, key, span) => match base.as_ref() {
            Expr::Var(name, _) => {
                let ke = emit_expr(key, state, locals, structs, recv)?;
                let recv = resolve_name(name, state, locals, recv);
                Ok(format!("{recv}.get_or({ke}, 0)"))
            }
            Expr::Index(inner, k1, _) => match inner.as_ref() {
                Expr::Var(name, _) => {
                    let k1e = emit_expr(k1, state, locals, structs, recv)?;
                    let k2e = emit_expr(key, state, locals, structs, recv)?;
                    let recv = resolve_name(name, state, locals, recv);
                    Ok(format!("{recv}.get_or({k1e}, {k2e}, 0)"))
                }
                _ => Err(FrontendDiag::new(
                    codes::FE442_BAD_INDEX_SOL,
                    "mapping nesting deeper than 2 levels is unsupported",
                    span.clone(),
                )),
            },
            _ => Err(FrontendDiag::new(
                codes::FE442_BAD_INDEX_SOL,
                "unsupported mapping index shape",
                span.clone(),
            )),
        },
        // SOL-STRUCT: field access `base.field` → `<base>.<field>` (check.rs verified the
        // struct type + the field). `msg.sender` etc. were rewritten away by desugar.
        Expr::Member(base, field, _) => {
            let be = emit_expr(base, state, locals, structs, recv)?;
            // SOL-AIRDROP (Rung C) UP-LENGTH: `<array>.length` → the bounded-vec `.len()`
            // method (check typed it `u256`), so a surviving `require(recipients.length ==
            // amounts.length)` lowers to a faithful runtime check. A struct declaring a field
            // named `length` would mislower to `.len()` and be REJECTED by the trusted
            // compiler (fail-LOUD, never silent) — an accepted, rare v1 edge.
            if field == "length" {
                return Ok(format!("{be}.len()"));
            }
            Ok(format!("{be}.{field}"))
        }
        // SOL-STRUCT: positional struct construction `Name(args)` → a record literal in
        // DECLARATION order (check.rs verified arity + field types). A non-struct call
        // never reaches emit (check.rs rejects internal/external calls as FE401).
        Expr::Call(callee, args, span) => {
            // SOL-uintN: the width-trap pass synthesizes `__fe_{add,mul}_checked(l, r, 2^n)`
            // calls (reserved `__fe_` prefix, disjoint from user idents) — emit them verbatim.
            if let Expr::Var(name, _) = callee.as_ref()
                && name.starts_with("__fe_")
            {
                let parts: Result<Vec<String>, _> = args
                    .iter()
                    .map(|a| emit_expr(a, state, locals, structs, recv))
                    .collect();
                return Ok(format!("{name}({})", parts?.join(", ")));
            }
            if let Expr::Var(name, _) = callee.as_ref()
                && let Some(sdef) = structs.iter().find(|s| s.name == *name)
            {
                let mut parts: Vec<String> = Vec::with_capacity(args.len());
                for (arg, fld) in args.iter().zip(sdef.fields.iter()) {
                    let ae = emit_expr(arg, state, locals, structs, recv)?;
                    parts.push(format!("{}: {}", fld.name, ae));
                }
                return Ok(format!("{name} {{ {} }}", parts.join(", ")));
            }
            Err(FrontendDiag::new(
                codes::FE401_UNSUPPORTED_SOL,
                "construct reached emit but is outside the SOL0 subset",
                span.clone(),
            ))
        }
    }
}

/// A bare name → `<recv>.<name>` when it is a state field not shadowed by a local;
/// otherwise the bare name (a param/local). `recv` is `"self"` in a method body and
/// `"__fe_c"` in the constructor (which builds the record as a local, SOL-CTOR).
fn resolve_name(name: &str, state: &HashSet<&str>, locals: &HashSet<String>, recv: &str) -> String {
    if state.contains(name) && !locals.contains(name) {
        format!("{recv}.{name}")
    } else {
        name.to_string()
    }
}

fn bin_op(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        // And/Or are rejected by check.rs.
        BinOp::And => "&&",
        BinOp::Or => "||",
    }
}

fn map_type(t: &TypeRef, enums: &[Enum]) -> String {
    match t {
        TypeRef::Scalar { name, .. } => match name.as_str() {
            "uint256" | "uint" => "u256".to_string(),
            "address" => "u256".to_string(), // address ≡ u256 carrier (check enforces distinctness)
            // SOL-ACCESS: `bytes32` ≡ the same u256 carrier (full 256-bit opaque id; check
            // admits ONLY the full width — bytesN<32 is FE410). Must precede the struct
            // fallthrough or `record bytes32` (nonexistent) would be emitted.
            "bytes32" => "u256".to_string(),
            "bool" => "bool".to_string(),
            // SOL-uintN: a narrow `uintN` lowers to the SAME `u256` carrier (check enforces
            // its width + the arithmetic width-trap). Must precede the struct fallthrough.
            other if super::check::parse_uint_width(other).is_some() => "u256".to_string(),
            // SOL-ENUM (EX-6): an enum-typed field/param/return/local lowers to the `u256`
            // tag carrier (the decl is erased; members were already lowered to index
            // literals). MUST precede the struct fallthrough — else `record <enum>` (which
            // does not exist) is emitted, breaking the trusted compile / FE500 self-check.
            other if enums.iter().any(|e| e.name.as_str() == other) => "u256".to_string(),
            // SOL-STRUCT: any other name is a VALIDATED struct (check.rs passed) → the
            // SIGIL `record` of that name.
            other => other.to_string(),
        },
        // A single-level `mapping(K=>V)` → the bounded u256→u256 map; a nested
        // `mapping(K=>mapping(K2=>V))` (its value is itself a mapping) → the two-key
        // map. Both K/V are u256-family by check.rs's map-kv allow-list.
        TypeRef::Mapping { value, .. } => match value.as_ref() {
            TypeRef::Mapping { .. } => "BoundedMap2_u256_u256_u256_64".to_string(),
            _ => "BoundedMap_u256_u256_64".to_string(),
        },
        // SOL-AIRDROP: a dynamic array `T[]` of a scalar element lowers to the bounded-vec carrier
        // (parser.rs: the airdrop recipients/amounts arrays); the element is u256-family by check.
        TypeRef::Array { .. } => "BoundedVec_u256_64".to_string(),
    }
}

/// The zero/default initializer for a declared type (NC-S4). A struct field zero-inits
/// RECURSIVELY to an all-zero record literal (EX-7), e.g. `Point { x: 0, y: 0 }`.
fn zero_default(t: &TypeRef, structs: &[Struct], enums: &[Enum]) -> String {
    match t {
        TypeRef::Scalar { name, .. } if name == "bool" => "false".to_string(),
        // SOL-ENUM (EX-6): the enum zero-default is its 0th member = tag `0` (Solidity's
        // default enum value). MUST precede the struct branch (an enum name is neither a
        // builtin nor a struct, so it would otherwise fall into the struct lookup).
        TypeRef::Scalar { name, .. } if enums.iter().any(|e| e.name.as_str() == name) => {
            "0".to_string()
        }
        TypeRef::Scalar { name, .. }
            if name != "uint256"
                && name != "uint"
                && name != "address"
                && name != "bytes32" // SOL-ACCESS: numeric-carrier zero (`0`), not a struct
                && super::check::parse_uint_width(name).is_none() =>
        {
            // A struct type → a recursive all-zero record literal of its fields.
            match structs.iter().find(|s| s.name == *name) {
                Some(sdef) => {
                    let inits: Vec<String> = sdef
                        .fields
                        .iter()
                        .map(|f| format!("{}: {}", f.name, zero_default(&f.ty, structs, enums)))
                        .collect();
                    format!("{name} {{ {} }}", inits.join(", "))
                }
                // Unreachable: check.rs validated every scalar name is a known struct.
                None => "0".to_string(),
            }
        }
        TypeRef::Scalar { .. } => "0".to_string(),
        TypeRef::Mapping { value, .. } => match value.as_ref() {
            TypeRef::Mapping { .. } => "BoundedMap2_u256_u256_u256_64::new()".to_string(),
            _ => "BoundedMap_u256_u256_64::new()".to_string(),
        },
        // SOL-AIRDROP: airdrop arrays are parameter-only (never state/local), so this default is
        // not normally reached; an empty bounded vec keeps the match total + fail-safe.
        TypeRef::Array { .. } => "BoundedVec_u256_64::new()".to_string(),
    }
}
