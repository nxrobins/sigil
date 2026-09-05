//! The RS0–RS3 sound type + scope checker — the oracle-agreement spine (SC-7).
//!
//! Every node is assigned the type the SIGIL compiler *would* resolve; any
//! in-subset type/scope error is a precise `FE6xx` here rather than a masquerading
//! compiler `T`-code. A block-scoped binding stack handles locals, reassignment,
//! and control flow (increment 2); RS1/RS2 add capability/effect hygiene; RS3a adds
//! nominal struct types (`Ty::Struct`), the struct registry, construction
//! field-completeness (FE640 — the compiler fails OPEN on missing record fields,
//! so the frontend is the sole gate), and field access (FE642); RS3b adds nominal
//! enum types (`Ty::Enum`), the enum registry, `Name::Variant` construction, and
//! `match` — where exhaustiveness (FE651) is checked here so an accepted input never
//! trips the compiler's own T087/T088 (the same discipline as RS0's return-path);
//! RS3c adds enum payloads (per-variant field types), construction arity/typing, and
//! pattern bindings captured into a per-arm scope (T085 arity backstop).
//!
//! It is also the emit-safety gate (SC-2): every identifier the emitter writes is
//! a function/parameter/capability/struct/field name, validated in
//! [`validate_ident`]; a variable/call reference resolves to a live binding or a
//! declared name, or is `FE634`.
//!
//! Recursion is bounded by construction: the parser capped AST depth at
//! `limits::MAX_DEPTH`, so this walk (and the emitter's) cannot overflow (SC-8).

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use crate::FrontendDiag;
use crate::codes;
use crate::limits;

use super::parser::{
    BinOp, RsBlock, RsExpr, RsInvRhs, RsMatchArm, RsPattern, RsProgram, RsStmt, RsTaintSel, UnOp,
    expr_span,
};

#[derive(Clone, PartialEq, Eq, Debug)]
enum Ty {
    I64,
    Bool,
    /// A nominal struct type (RS3a), identified by its declared name.
    Struct(String),
    /// A nominal enum type (RS3b), identified by its declared name.
    Enum(String),
}

impl Ty {
    fn name(&self) -> String {
        match self {
            Ty::I64 => "i64".to_string(),
            Ty::Bool => "bool".to_string(),
            Ty::Struct(s) => s.clone(),
            Ty::Enum(e) => e.clone(),
        }
    }
}

/// A declared struct's fields, in declaration order (RS3a).
struct StructDef {
    fields: Vec<(String, Ty)>,
}

impl StructDef {
    fn field_ty(&self, name: &str) -> Option<&Ty> {
        self.fields.iter().find(|(n, _)| n == name).map(|(_, t)| t)
    }
}

type StructReg = HashMap<String, StructDef>;

/// A declared enum's variants, in declaration order: each carries its positional
/// payload types (empty for a dataless variant; RS3b/RS3c).
struct EnumDef {
    variants: Vec<(String, Vec<Ty>)>,
}

impl EnumDef {
    /// The variant's positional payload types, or `None` if no such variant.
    fn variant_payloads(&self, name: &str) -> Option<&Vec<Ty>> {
        self.variants
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, p)| p)
    }
}

type EnumReg = HashMap<String, EnumDef>;

/// Resolve a type annotation to a `Ty`; `None` if the name is neither `i64`/
/// `bool` nor a declared struct/enum (→ FE610 at the call site).
fn resolve_ty(name: &str, structs: &StructReg, enums: &EnumReg) -> Option<Ty> {
    match name {
        "i64" => Some(Ty::I64),
        "bool" => Some(Ty::Bool),
        _ if structs.contains_key(name) => Some(Ty::Struct(name.to_string())),
        _ if enums.contains_key(name) => Some(Ty::Enum(name.to_string())),
        _ => None,
    }
}

#[derive(Clone)]
struct Binding {
    ty: Ty,
    is_mut: bool,
}

struct Sig {
    params: Vec<Ty>,
    ret: Ty,
}

/// Program-wide context: call signatures, the set of cap-bearing function names
/// (FE040), and the struct registry (RS3). Bundled so the recursive walk carries
/// one reference.
struct Ctx<'a> {
    sigs: HashMap<&'a str, Sig>,
    cap_fns: HashSet<&'a str>,
    structs: StructReg,
    enums: EnumReg,
}

/// A stack of block scopes: innermost last. Params occupy the outermost scope.
type Scopes = Vec<HashMap<String, Binding>>;

fn resolve<'a>(scopes: &'a Scopes, name: &str) -> Option<&'a Binding> {
    scopes.iter().rev().find_map(|s| s.get(name))
}

pub fn check(program: &RsProgram) -> Result<(), FrontendDiag> {
    // 0. Whole-file mode: caps (inner ring) and effects (outer ring) are mutually
    //    exclusive — a mixed file would need a cross-ring `grant` bridge (deferred).
    let has_cap = program.functions.iter().any(|f| !f.caps.is_empty());
    let has_effect = program.functions.iter().any(|f| f.effects.is_some());
    if has_cap && has_effect {
        let span = program
            .functions
            .iter()
            .find(|f| f.effects.is_some())
            .map(|f| f.name_span.clone())
            .unwrap_or(0..0);
        return Err(FrontendDiag::new(
            codes::FE201_MIXED_MODE,
            "a file may not mix `#[sigil::cap]` and `#[sigil::effects]` (cap-mode is inner-ring, \
             effect-mode is outer-ring; mixed-mode is deferred)",
            span,
        ));
    }

    // 0b. RS4a mode: `#[sigil::requires]` is inner-ring-only and does not combine
    //     with caps or effects in the same file yet (AG-4). Deferred, fail-closed.
    let requiring = program.functions.iter().find(|f| f.requires.is_some());
    if let Some(f) = requiring
        && (has_cap || has_effect)
    {
        return Err(FrontendDiag::new(
            codes::FE660_BAD_REFINEMENT_RS,
            "a file may not mix `#[sigil::requires]` with `#[sigil::cap]`/`#[sigil::effects]` \
             (RS4a is requires-only, inner-ring; the interaction is deferred)",
            f.name_span.clone(),
        ));
    }

    // 0c. RS5a mode: `#[sigil::taint]` is taint-only — it does not combine with
    //     cap/effects/requires/invariant in the same file yet (AG-T7). Fail-closed.
    if let Some(f) = program.functions.iter().find(|f| f.taints.is_some()) {
        let has_requires = program.functions.iter().any(|f| f.requires.is_some());
        let has_invariant = program.structs.iter().any(|s| s.invariant.is_some());
        if has_cap || has_effect || has_requires || has_invariant {
            return Err(FrontendDiag::new(
                codes::FE670_BAD_TAINT_RS,
                "a file may not mix `#[sigil::taint]` with `#[sigil::cap]`/`effects`/`requires`/\
                 `invariant` (RS5a is taint-only; the interaction is deferred)",
                f.name_span.clone(),
            ));
        }
    }

    // 0d. RS5b mode: a `declassify(...)` call is taint-mode (inner ring). It pairs
    //     with `#[sigil::taint]` (the intended use) but does NOT combine with
    //     cap/effects/requires/invariant in the same file yet (SR-B6). Fail-closed.
    if let Some(f) = program
        .functions
        .iter()
        .find(|f| block_has_declassify(&f.body))
    {
        let has_requires = program.functions.iter().any(|f| f.requires.is_some());
        let has_invariant = program.structs.iter().any(|s| s.invariant.is_some());
        if has_cap || has_effect || has_requires || has_invariant {
            return Err(FrontendDiag::new(
                codes::FE672_BAD_DECLASSIFY_RS,
                "a file may not mix `declassify(...)` with `#[sigil::cap]`/`effects`/`requires`/\
                 `invariant` (RS5b declassify is taint-mode, inner-ring; the interaction is deferred)",
                f.name_span.clone(),
            ));
        }
    }

    // 1a. Function + parameter name hygiene/uniqueness (emit-safety, SC-2).
    let mut fn_names: HashMap<&str, ()> = HashMap::new();
    for f in &program.functions {
        validate_ident(&f.name, "function", &f.name_span)?;
        if fn_names.insert(f.name.as_str(), ()).is_some() {
            return Err(FrontendDiag::new(
                codes::FE620_BAD_IDENTIFIER_RS,
                format!("duplicate function name `{}`", f.name),
                f.name_span.clone(),
            ));
        }
        let mut param_names: HashMap<&str, ()> = HashMap::new();
        for p in &f.params {
            validate_ident(&p.name, "parameter", &p.name_span)?;
            if param_names.insert(p.name.as_str(), ()).is_some() {
                return Err(FrontendDiag::new(
                    codes::FE620_BAD_IDENTIFIER_RS,
                    format!(
                        "duplicate parameter name `{}` in function `{}`",
                        p.name, f.name
                    ),
                    p.name_span.clone(),
                ));
            }
        }
        // SR-3: a `#[sigil::requires]` predicate's LHS must be a parameter of this
        // function — the emitted `where` clause only ever names a validated param.
        if let Some(r) = &f.requires
            && !param_names.contains_key(r.param.as_str())
        {
            return Err(FrontendDiag::new(
                codes::FE661_REFINEMENT_UNKNOWN_PARAM_RS,
                format!(
                    "refinement references `{}`, which is not a parameter of `{}`",
                    r.param, f.name
                ),
                r.span.clone(),
            ));
        }
        // SR-T2 + SR-T10: every `#[sigil::taint]` target is `ret` or a parameter of
        // this function, and its type is scalar (`i64`/`bool`) — the emitted `@Label`
        // only ever lands on a validated scalar param or the return.
        if let Some(t) = &f.taints {
            for (sel, _level, tspan) in &t.targets {
                let ty_name = match sel {
                    RsTaintSel::Ret => f.ret.name.as_str(),
                    RsTaintSel::Param(n) => match f.params.iter().find(|p| &p.name == n) {
                        Some(p) => p.ty.name.as_str(),
                        None => {
                            return Err(FrontendDiag::new(
                                codes::FE671_TAINT_UNKNOWN_TARGET_RS,
                                format!("taint target `{n}` is not a parameter of `{}`", f.name),
                                tspan.clone(),
                            ));
                        }
                    },
                };
                if ty_name != "i64" && ty_name != "bool" {
                    return Err(FrontendDiag::new(
                        codes::FE670_BAD_TAINT_RS,
                        format!(
                            "taint on a non-scalar type `{ty_name}` is deferred (RS5a taints only \
                             `i64`/`bool` params and returns)"
                        ),
                        tspan.clone(),
                    ));
                }
            }
        }
    }

    // 1b. Capability-name hygiene + collision with function names. A `cap type`
    //     and a `fn` of the same name would be N002 at name-resolution — invisible
    //     to the FE500 parse self-check — so the frontend must catch it.
    let mut cap_names: HashSet<&str> = HashSet::new();
    for f in &program.functions {
        for c in &f.caps {
            validate_ident(&c.name, "capability", &c.span)?;
            if fn_names.contains_key(c.name.as_str()) {
                return Err(FrontendDiag::new(
                    codes::FE620_BAD_IDENTIFIER_RS,
                    format!("capability type `{}` collides with a function name", c.name),
                    c.span.clone(),
                ));
            }
            cap_names.insert(c.name.as_str());
        }
    }

    // 1c. Effect-name hygiene (effect-mode): compiler-reserved names (FE213), a
    //     legal identifier, and collision with a function name (FE211 — the
    //     emitted `effect NetIO;` + a `fn NetIO` would be N002, invisible to FE500).
    for f in &program.functions {
        if let Some(es) = &f.effects {
            for e in es {
                if limits::RESERVED_EFFECTS.contains(&e.name.as_str()) {
                    return Err(FrontendDiag::new(
                        codes::FE213_RESERVED_EFFECT,
                        format!("effect name `{}` is compiler-reserved", e.name),
                        e.span.clone(),
                    ));
                }
                validate_ident(&e.name, "effect", &e.span)?;
                if fn_names.contains_key(e.name.as_str()) {
                    return Err(FrontendDiag::new(
                        codes::FE211_NAME_COLLISION,
                        format!("effect `{}` collides with a function name", e.name),
                        e.span.clone(),
                    ));
                }
            }
        }
    }

    // 1d. Struct hygiene + the struct registry (RS3). A struct name is an emitted
    //     top-level `record` name → it must not collide with a function or
    //     capability name (else N002). Two passes: collect names, then resolve
    //     field types (a field may itself be another struct).
    let mut structs: StructReg = HashMap::new();
    for s in &program.structs {
        validate_ident(&s.name, "struct", &s.name_span)?;
        if fn_names.contains_key(s.name.as_str())
            || cap_names.contains(s.name.as_str())
            || structs.contains_key(&s.name)
        {
            return Err(FrontendDiag::new(
                codes::FE620_BAD_IDENTIFIER_RS,
                format!(
                    "struct name `{}` collides with another top-level name",
                    s.name
                ),
                s.name_span.clone(),
            ));
        }
        let mut fnames: HashSet<&str> = HashSet::new();
        for fld in &s.fields {
            validate_ident(&fld.name, "field", &fld.name_span)?;
            if !fnames.insert(fld.name.as_str()) {
                return Err(FrontendDiag::new(
                    codes::FE640_STRUCT_FIELD_MISMATCH_RS,
                    format!("duplicate field `{}` in struct `{}`", fld.name, s.name),
                    fld.name_span.clone(),
                ));
            }
        }
        structs.insert(s.name.clone(), StructDef { fields: Vec::new() });
    }

    // 1e. Enum hygiene + the enum registry (RS3b/RS3c). An enum name is an emitted
    //     top-level `enum` name → it must not collide with a function, capability,
    //     or struct name. Variant names are emitted too (SC-2) and must be unique
    //     within the enum. Pass 1 registers names (empty payload types) so both
    //     struct field-types and enum payload-types may reference any struct/enum;
    //     pass 2 (below, after the struct field pass) resolves the payload types.
    let mut enums: EnumReg = HashMap::new();
    for e in &program.enums {
        validate_ident(&e.name, "enum", &e.name_span)?;
        if fn_names.contains_key(e.name.as_str())
            || cap_names.contains(e.name.as_str())
            || structs.contains_key(&e.name)
            || enums.contains_key(&e.name)
        {
            return Err(FrontendDiag::new(
                codes::FE620_BAD_IDENTIFIER_RS,
                format!(
                    "enum name `{}` collides with another top-level name",
                    e.name
                ),
                e.name_span.clone(),
            ));
        }
        let mut vnames: HashSet<&str> = HashSet::new();
        let mut variants = Vec::new();
        for v in &e.variants {
            validate_ident(&v.name, "variant", &v.name_span)?;
            if !vnames.insert(v.name.as_str()) {
                return Err(FrontendDiag::new(
                    codes::FE650_BAD_ENUM_SHAPE_RS,
                    format!("duplicate variant `{}` in enum `{}`", v.name, e.name),
                    v.name_span.clone(),
                ));
            }
            variants.push((v.name.clone(), Vec::new()));
        }
        enums.insert(e.name.clone(), EnumDef { variants });
    }

    for s in &program.structs {
        let mut fields = Vec::new();
        for fld in &s.fields {
            let fty = resolve_ty(&fld.ty.name, &structs, &enums).ok_or_else(|| {
                FrontendDiag::new(
                    codes::FE610_UNSUPPORTED_TYPE_RS,
                    format!(
                        "field `{}` of struct `{}` has unknown type `{}`",
                        fld.name, s.name, fld.ty.name
                    ),
                    fld.ty.span.clone(),
                )
            })?;
            // A field of the struct's own type is an infinite-size record (and
            // invalid Rust without `Box`) — reject rather than emit a bad record.
            if fty == Ty::Struct(s.name.clone()) {
                return Err(FrontendDiag::new(
                    codes::FE641_BAD_STRUCT_SHAPE_RS,
                    format!(
                        "struct `{}` is directly self-referential (infinite size)",
                        s.name
                    ),
                    fld.ty.span.clone(),
                ));
            }
            fields.push((fld.name.clone(), fty));
        }
        structs.get_mut(&s.name).expect("inserted above").fields = fields;
    }

    // 1d-inv. Struct invariant validation (RS4b): the clause's field(s) must be
    //     declared `i64` fields (FE661 undeclared, FE660 non-i64 — mirroring the
    //     compiler's T212); a cross-field clause may not self-reference (`lo == lo`
    //     is vacuous, FE660, mirroring T218). Construction enforcement is SIGIL's Z3.
    for s in &program.structs {
        if let Some(inv) = &s.invariant {
            let def = structs.get(&s.name).expect("struct registered");
            let lhs_ty = def.field_ty(&inv.field).ok_or_else(|| {
                FrontendDiag::new(
                    codes::FE661_REFINEMENT_UNKNOWN_PARAM_RS,
                    format!(
                        "invariant references `{}`, which is not a field of `{}`",
                        inv.field, s.name
                    ),
                    inv.span.clone(),
                )
            })?;
            if *lhs_ty != Ty::I64 {
                return Err(FrontendDiag::new(
                    codes::FE660_BAD_REFINEMENT_RS,
                    format!(
                        "invariant field `{}` of `{}` is `{}`, not `i64` (refinements are over i64)",
                        inv.field,
                        s.name,
                        lhs_ty.name()
                    ),
                    inv.span.clone(),
                ));
            }
            if let RsInvRhs::Field(rf) = &inv.rhs {
                if rf == &inv.field {
                    return Err(FrontendDiag::new(
                        codes::FE660_BAD_REFINEMENT_RS,
                        format!(
                            "invariant `{} {} {}` is self-referential (vacuous)",
                            inv.field,
                            inv.op.as_str(),
                            rf
                        ),
                        inv.span.clone(),
                    ));
                }
                let rhs_ty = def.field_ty(rf).ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE661_REFINEMENT_UNKNOWN_PARAM_RS,
                        format!(
                            "invariant right-hand side `{}` is not a field of `{}`",
                            rf, s.name
                        ),
                        inv.span.clone(),
                    )
                })?;
                if *rhs_ty != Ty::I64 {
                    return Err(FrontendDiag::new(
                        codes::FE660_BAD_REFINEMENT_RS,
                        format!(
                            "invariant right-hand side field `{}` of `{}` is `{}`, not `i64`",
                            rf,
                            s.name,
                            rhs_ty.name()
                        ),
                        inv.span.clone(),
                    ));
                }
            }
        }
    }

    // 1e-pass2. Resolve enum variant payload types (RS3c). A payload may be any
    //     `i64`/`bool`/struct/enum — all names are now registered. (SIGIL enums are
    //     tag+pointer, so a self-referential payload is NOT infinite-size like a
    //     record field — no self-ref reject here, unlike structs.)
    for e in &program.enums {
        let mut variants = Vec::new();
        for v in &e.variants {
            let mut payloads = Vec::new();
            for pty in &v.payloads {
                let ty = resolve_ty(&pty.name, &structs, &enums).ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE610_UNSUPPORTED_TYPE_RS,
                        format!(
                            "payload of `{}::{}` has unknown type `{}`",
                            e.name, v.name, pty.name
                        ),
                        pty.span.clone(),
                    )
                })?;
                payloads.push(ty);
            }
            variants.push((v.name.clone(), payloads));
        }
        enums.get_mut(&e.name).expect("inserted above").variants = variants;
    }

    // 2. Signature table + the cap-bearing-fn set (FE040 gate). Types are resolved
    //    against the struct registry (an unknown type → FE610).
    let mut sigs: HashMap<&str, Sig> = HashMap::new();
    let mut cap_fns: HashSet<&str> = HashSet::new();
    for f in &program.functions {
        let params = f
            .params
            .iter()
            .map(|p| {
                resolve_ty(&p.ty.name, &structs, &enums).ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE610_UNSUPPORTED_TYPE_RS,
                        format!(
                            "parameter `{}` of `{}` has unknown type `{}`",
                            p.name, f.name, p.ty.name
                        ),
                        p.ty.span.clone(),
                    )
                })
            })
            .collect::<Result<Vec<Ty>, _>>()?;
        let ret = resolve_ty(&f.ret.name, &structs, &enums).ok_or_else(|| {
            FrontendDiag::new(
                codes::FE610_UNSUPPORTED_TYPE_RS,
                format!(
                    "function `{}` has unknown return type `{}`",
                    f.name, f.ret.name
                ),
                f.ret.span.clone(),
            )
        })?;
        sigs.insert(f.name.as_str(), Sig { params, ret });
        // A cap-bearing fn OR a declassify-bearing fn (RS5b) gets synthetic cap
        // parameters an in-subset call site cannot supply, so it may not be called
        // intra-program (FE040, SR-B5). Otherwise the emitted call under-supplies
        // the synthetic cap → a SIGIL arity error (T070) leaks through.
        if !f.caps.is_empty() || block_has_declassify(&f.body) {
            cap_fns.insert(f.name.as_str());
        }
    }
    let ctx = Ctx {
        sigs,
        cap_fns,
        structs,
        enums,
    };

    // 3. Type-check each body against its declared return type + return-path.
    for f in &program.functions {
        let sig = &ctx.sigs[f.name.as_str()];
        let ret = sig.ret.clone();
        let mut params_scope: HashMap<String, Binding> = HashMap::new();
        for (p, pty) in f.params.iter().zip(sig.params.iter()) {
            // Params are immutable in RS0 (reassigning one → FE633).
            params_scope.insert(
                p.name.clone(),
                Binding {
                    ty: pty.clone(),
                    is_mut: false,
                },
            );
        }
        let mut scopes: Scopes = vec![params_scope];
        check_block(&f.body, &mut scopes, &ctx, &ret, true)?;

        // Return-path (FE632): a non-unit function must return on every path.
        if !block_returns(&f.body) {
            return Err(FrontendDiag::new(
                codes::FE632_NON_EXHAUSTIVE_RETURN_RS,
                format!(
                    "function `{}` may reach the end without returning a `{}` (add a `return` or a \
                     tail expression on every path)",
                    f.name,
                    ret.name()
                ),
                f.name_span.clone(),
            ));
        }
    }
    Ok(())
}

fn check_block(
    block: &RsBlock,
    scopes: &mut Scopes,
    ctx: &Ctx,
    ret: &Ty,
    allow_tail: bool,
) -> Result<(), FrontendDiag> {
    scopes.push(HashMap::new());
    for stmt in &block.stmts {
        check_stmt(stmt, scopes, ctx, ret)?;
    }
    if let Some(tail) = &block.tail {
        if !allow_tail {
            return Err(FrontendDiag::new(
                codes::FE690_EXPR_POSITION_RS,
                "a value-producing tail expression in a statement-position block \
                 (`if`/`while` body) is deferred in RS0",
                expr_span(tail),
            ));
        }
        let t = check_expr(tail, scopes, ctx)?;
        if &t != ret {
            return Err(FrontendDiag::new(
                codes::FE630_ILL_TYPED_RS,
                format!(
                    "the tail expression has type `{}` but the function returns `{}`",
                    t.name(),
                    ret.name()
                ),
                expr_span(tail),
            ));
        }
    }
    scopes.pop();
    Ok(())
}

fn check_stmt(stmt: &RsStmt, scopes: &mut Scopes, ctx: &Ctx, ret: &Ty) -> Result<(), FrontendDiag> {
    match stmt {
        RsStmt::Let {
            name,
            name_span,
            is_mut,
            ann,
            value,
            ..
        } => {
            let vt = check_expr(value, scopes, ctx)?;
            // The binding's type is the annotation (which must match the value)
            // or, absent one, the inferred initializer type.
            let declared = match ann {
                Some(t) => {
                    let a = resolve_ty(&t.name, &ctx.structs, &ctx.enums).ok_or_else(|| {
                        FrontendDiag::new(
                            codes::FE610_UNSUPPORTED_TYPE_RS,
                            format!("`let {name}` is annotated with unknown type `{}`", t.name),
                            t.span.clone(),
                        )
                    })?;
                    if vt != a {
                        return Err(FrontendDiag::new(
                            codes::FE630_ILL_TYPED_RS,
                            format!(
                                "`let {name}`: the value has type `{}` but is annotated `{}`",
                                vt.name(),
                                a.name()
                            ),
                            expr_span(value),
                        ));
                    }
                    a
                }
                None => vt,
            };
            // Shadowing of a live binding is rejected (FE635), not renamed.
            if resolve(scopes, name).is_some() {
                return Err(FrontendDiag::new(
                    codes::FE635_SHADOWING_RS,
                    format!(
                        "`let {name}` shadows a binding already in scope (RS0 rejects shadowing; \
                         rename it)"
                    ),
                    name_span.clone(),
                ));
            }
            scopes.last_mut().expect("scope pushed").insert(
                name.clone(),
                Binding {
                    ty: declared,
                    is_mut: *is_mut,
                },
            );
            Ok(())
        }
        RsStmt::Assign {
            name,
            name_span,
            value,
            ..
        } => {
            let b = match resolve(scopes, name) {
                Some(b) => b.clone(),
                None => {
                    return Err(FrontendDiag::new(
                        codes::FE634_UNRESOLVED_REFERENCE_RS,
                        format!("assignment to `{name}`, which has no binding in scope"),
                        name_span.clone(),
                    ));
                }
            };
            if !b.is_mut {
                return Err(FrontendDiag::new(
                    codes::FE633_ILLEGAL_REASSIGNMENT_RS,
                    format!("cannot assign to `{name}` (a non-`mut` binding or a parameter)"),
                    name_span.clone(),
                ));
            }
            let vt = check_expr(value, scopes, ctx)?;
            if vt != b.ty {
                return Err(FrontendDiag::new(
                    codes::FE630_ILL_TYPED_RS,
                    format!(
                        "assignment to `{name}`: the value has type `{}` but `{name}` is `{}`",
                        vt.name(),
                        b.ty.name()
                    ),
                    expr_span(value),
                ));
            }
            Ok(())
        }
        RsStmt::Return { value, span } => {
            match value {
                Some(e) => {
                    let t = check_expr(e, scopes, ctx)?;
                    if &t != ret {
                        return Err(FrontendDiag::new(
                            codes::FE630_ILL_TYPED_RS,
                            format!(
                                "the return value has type `{}` but the function returns `{}`",
                                t.name(),
                                ret.name()
                            ),
                            expr_span(e),
                        ));
                    }
                }
                None => {
                    return Err(FrontendDiag::new(
                        codes::FE630_ILL_TYPED_RS,
                        format!("a bare `return;` in a function returning `{}`", ret.name()),
                        span.clone(),
                    ));
                }
            }
            Ok(())
        }
        RsStmt::If {
            cond,
            then_block,
            else_block,
            ..
        } => {
            let ct = check_expr(cond, scopes, ctx)?;
            if ct != Ty::Bool {
                return Err(FrontendDiag::new(
                    codes::FE630_ILL_TYPED_RS,
                    format!(
                        "`if` condition must be `bool`, found `{}` (RS0 has no truthiness)",
                        ct.name()
                    ),
                    expr_span(cond),
                ));
            }
            check_block(then_block, scopes, ctx, ret, false)?;
            if let Some(eb) = else_block {
                check_block(eb, scopes, ctx, ret, false)?;
            }
            Ok(())
        }
        RsStmt::While { cond, body, .. } => {
            let ct = check_expr(cond, scopes, ctx)?;
            if ct != Ty::Bool {
                return Err(FrontendDiag::new(
                    codes::FE630_ILL_TYPED_RS,
                    format!("`while` condition must be `bool`, found `{}`", ct.name()),
                    expr_span(cond),
                ));
            }
            check_block(body, scopes, ctx, ret, false)?;
            Ok(())
        }
        RsStmt::Match {
            scrutinee, arms, ..
        } => check_match(scrutinee, arms, scopes, ctx, ret),
    }
}

/// Type-check a `match` (RS3b/RS3c): each arm's pattern against the scrutinee type,
/// each arm's value against the function return type (arms lower to `return value`),
/// and exhaustiveness. A variant pattern's payload bindings (RS3c) are captured into
/// a per-arm scope, typed by the variant's declared field types.
///
/// The frontend rejects a non-exhaustive match (FE651) even though SIGIL enforces
/// exhaustiveness too (T087/T088), so an ACCEPTED input never trips a T-code (SC-7).
fn check_match(
    scrutinee: &RsExpr,
    arms: &[RsMatchArm],
    scopes: &mut Scopes,
    ctx: &Ctx,
    ret: &Ty,
) -> Result<(), FrontendDiag> {
    let st = check_expr(scrutinee, scopes, ctx)?;
    let mut wildcard = false;
    let mut ints: HashSet<i64> = HashSet::new();
    let mut bools: HashSet<bool> = HashSet::new();
    let mut variants: HashSet<&str> = HashSet::new();

    for arm in arms {
        // An arm after a `_` catch-all can never be reached (T080 backstop).
        if wildcard {
            return Err(FrontendDiag::new(
                codes::FE652_BAD_MATCH_ARM_RS,
                "unreachable match arm after a `_` catch-all",
                arm.pattern.span(),
            ));
        }
        // Payload bindings captured by a variant pattern, typed for the arm scope.
        let mut arm_bindings: Vec<(String, Ty)> = Vec::new();
        match &arm.pattern {
            RsPattern::Wildcard(_) => wildcard = true,
            RsPattern::Int(v, ps) => {
                if st != Ty::I64 {
                    return Err(FrontendDiag::new(
                        codes::FE652_BAD_MATCH_ARM_RS,
                        format!(
                            "integer pattern against a scrutinee of type `{}` (expected `i64`)",
                            st.name()
                        ),
                        ps.clone(),
                    ));
                }
                if !ints.insert(*v) {
                    return Err(FrontendDiag::new(
                        codes::FE652_BAD_MATCH_ARM_RS,
                        format!("duplicate literal pattern `{v}`"),
                        ps.clone(),
                    ));
                }
            }
            RsPattern::Bool(b, ps) => {
                if st != Ty::Bool {
                    return Err(FrontendDiag::new(
                        codes::FE652_BAD_MATCH_ARM_RS,
                        format!("`bool` pattern against a scrutinee of type `{}`", st.name()),
                        ps.clone(),
                    ));
                }
                if !bools.insert(*b) {
                    return Err(FrontendDiag::new(
                        codes::FE652_BAD_MATCH_ARM_RS,
                        format!("duplicate literal pattern `{b}`"),
                        ps.clone(),
                    ));
                }
            }
            RsPattern::Variant {
                enum_name,
                variant,
                bindings,
                span: ps,
            } => match &st {
                Ty::Enum(e) if e == enum_name => {
                    let def = ctx.enums.get(e).expect("scrutinee enum is registered");
                    let payloads = def.variant_payloads(variant).ok_or_else(|| {
                        FrontendDiag::new(
                            codes::FE652_BAD_MATCH_ARM_RS,
                            format!("enum `{e}` has no variant `{variant}`"),
                            ps.clone(),
                        )
                    })?;
                    if !variants.insert(variant.as_str()) {
                        return Err(FrontendDiag::new(
                            codes::FE652_BAD_MATCH_ARM_RS,
                            format!("duplicate variant pattern `{enum_name}::{variant}`"),
                            ps.clone(),
                        ));
                    }
                    // Binding arity must equal the variant's field count (T085).
                    if bindings.len() != payloads.len() {
                        return Err(FrontendDiag::new(
                            codes::FE652_BAD_MATCH_ARM_RS,
                            format!(
                                "variant `{enum_name}::{variant}` has {} field(s), pattern binds {}",
                                payloads.len(),
                                bindings.len()
                            ),
                            ps.clone(),
                        ));
                    }
                    // Capture each payload into the arm scope: validate the name
                    // (SC-2), reject a `_` placeholder / a duplicate / shadowing.
                    let mut seen: HashSet<&str> = HashSet::new();
                    for ((bname, bspan), pty) in bindings.iter().zip(payloads.iter()) {
                        if bname == "_" {
                            return Err(FrontendDiag::new(
                                codes::FE652_BAD_MATCH_ARM_RS,
                                "a `_` payload placeholder is deferred; name the binding",
                                bspan.clone(),
                            ));
                        }
                        validate_ident(bname, "binding", bspan)?;
                        if !seen.insert(bname.as_str()) {
                            return Err(FrontendDiag::new(
                                codes::FE652_BAD_MATCH_ARM_RS,
                                format!("payload binding `{bname}` is bound twice in the pattern"),
                                bspan.clone(),
                            ));
                        }
                        if resolve(scopes, bname).is_some() {
                            return Err(FrontendDiag::new(
                                codes::FE635_SHADOWING_RS,
                                format!(
                                    "payload binding `{bname}` shadows a binding already in scope (rename it)"
                                ),
                                bspan.clone(),
                            ));
                        }
                        arm_bindings.push((bname.clone(), pty.clone()));
                    }
                }
                Ty::Enum(e) => {
                    return Err(FrontendDiag::new(
                        codes::FE652_BAD_MATCH_ARM_RS,
                        format!(
                            "variant pattern `{enum_name}::{variant}` does not belong to the scrutinee enum `{e}`"
                        ),
                        ps.clone(),
                    ));
                }
                other => {
                    return Err(FrontendDiag::new(
                        codes::FE652_BAD_MATCH_ARM_RS,
                        format!(
                            "variant pattern `{enum_name}::{variant}` against a non-enum scrutinee of type `{}`",
                            other.name()
                        ),
                        ps.clone(),
                    ));
                }
            },
        }
        // The arm value is checked in a scope carrying the payload bindings; it
        // lowers to `return <value>;`, so its type must match the return type.
        scopes.push(
            arm_bindings
                .into_iter()
                .map(|(n, t)| {
                    (
                        n,
                        Binding {
                            ty: t,
                            is_mut: false,
                        },
                    )
                })
                .collect(),
        );
        let vt = check_expr(&arm.value, scopes, ctx);
        scopes.pop();
        let vt = vt?;
        if &vt != ret {
            return Err(FrontendDiag::new(
                codes::FE630_ILL_TYPED_RS,
                format!(
                    "match arm value has type `{}` but the function returns `{}`",
                    vt.name(),
                    ret.name()
                ),
                expr_span(&arm.value),
            ));
        }
    }

    // Exhaustiveness (FE651) — unless a `_` catch-all covers the remainder.
    if !wildcard {
        match &st {
            Ty::Enum(e) => {
                let def = ctx.enums.get(e).expect("scrutinee enum is registered");
                let missing: Vec<&str> = def
                    .variants
                    .iter()
                    .filter(|(vn, _)| !variants.contains(vn.as_str()))
                    .map(|(vn, _)| vn.as_str())
                    .collect();
                if !missing.is_empty() {
                    return Err(FrontendDiag::new(
                        codes::FE651_NONEXHAUSTIVE_MATCH_RS,
                        format!(
                            "non-exhaustive match on enum `{e}`: missing variant(s) {}; add the arm(s) or a `_`",
                            missing.join(", ")
                        ),
                        expr_span(scrutinee),
                    ));
                }
            }
            Ty::Bool => {
                if !(bools.contains(&true) && bools.contains(&false)) {
                    return Err(FrontendDiag::new(
                        codes::FE651_NONEXHAUSTIVE_MATCH_RS,
                        "non-exhaustive match on `bool`: cover both `true` and `false`, or add a `_`",
                        expr_span(scrutinee),
                    ));
                }
            }
            Ty::I64 => {
                return Err(FrontendDiag::new(
                    codes::FE651_NONEXHAUSTIVE_MATCH_RS,
                    "non-exhaustive match on `i64`: add a `_` catch-all (i64 cannot be enumerated)",
                    expr_span(scrutinee),
                ));
            }
            Ty::Struct(s) => {
                return Err(FrontendDiag::new(
                    codes::FE651_NONEXHAUSTIVE_MATCH_RS,
                    format!("non-exhaustive match on struct `{s}`: add a `_` catch-all"),
                    expr_span(scrutinee),
                ));
            }
        }
    }
    Ok(())
}

fn check_expr(e: &RsExpr, scopes: &Scopes, ctx: &Ctx) -> Result<Ty, FrontendDiag> {
    match e {
        RsExpr::Int(_, _) => Ok(Ty::I64),
        RsExpr::Bool(_, _) => Ok(Ty::Bool),
        RsExpr::Var(n, span) => resolve(scopes, n).map(|b| b.ty.clone()).ok_or_else(|| {
            FrontendDiag::new(
                codes::FE634_UNRESOLVED_REFERENCE_RS,
                format!("no binding named `{n}` in scope"),
                span.clone(),
            )
        }),
        RsExpr::Unary(UnOp::Not, x, span) => {
            let t = check_expr(x, scopes, ctx)?;
            if t != Ty::Bool {
                return Err(FrontendDiag::new(
                    codes::FE630_ILL_TYPED_RS,
                    format!("unary `!` requires `bool`, found `{}`", t.name()),
                    span.clone(),
                ));
            }
            Ok(Ty::Bool)
        }
        RsExpr::Unary(UnOp::Neg, x, span) => {
            let t = check_expr(x, scopes, ctx)?;
            if t != Ty::I64 {
                return Err(FrontendDiag::new(
                    codes::FE630_ILL_TYPED_RS,
                    format!("unary `-` requires `i64`, found `{}`", t.name()),
                    span.clone(),
                ));
            }
            Ok(Ty::I64)
        }
        RsExpr::Bin(op, l, r, span) => {
            let tl = check_expr(l, scopes, ctx)?;
            let tr = check_expr(r, scopes, ctx)?;
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => {
                    if tl != Ty::I64 || tr != Ty::I64 {
                        return Err(bin_err(
                            "arithmetic `+ - *` requires `i64` operands",
                            &tl,
                            &tr,
                            span,
                        ));
                    }
                    Ok(Ty::I64)
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    if tl != Ty::I64 || tr != Ty::I64 {
                        return Err(bin_err(
                            "relational `< <= > >=` requires `i64` operands",
                            &tl,
                            &tr,
                            span,
                        ));
                    }
                    Ok(Ty::Bool)
                }
                BinOp::Eq | BinOp::Ne => {
                    if tl != tr {
                        return Err(bin_err(
                            "`==`/`!=` requires operands of the same type",
                            &tl,
                            &tr,
                            span,
                        ));
                    }
                    // `==`/`!=` on structs would emit a SIGIL record comparison the
                    // compiler does not support — restrict to scalars.
                    if !matches!(tl, Ty::I64 | Ty::Bool) {
                        return Err(FrontendDiag::new(
                            codes::FE630_ILL_TYPED_RS,
                            format!(
                                "`==`/`!=` on a `{}` value is not supported (scalars only)",
                                tl.name()
                            ),
                            span.clone(),
                        ));
                    }
                    Ok(Ty::Bool)
                }
            }
        }
        RsExpr::Call(n, args, span) => {
            // FE040: a cap-bearing function cannot be called intra-program (its
            // emitted signature has an extra synthetic cap parameter the call site
            // cannot supply; the cross-call cap-passing convention is deferred).
            if ctx.cap_fns.contains(n.as_str()) {
                return Err(FrontendDiag::new(
                    codes::FE040_CAP_CALLEE,
                    format!(
                        "`{n}` takes a synthesized capability parameter (from `#[sigil::cap]` or a \
                         `declassify`) and cannot be called intra-program — the call site cannot \
                         supply the synthetic cap (the cross-call cap-passing convention is deferred)"
                    ),
                    span.clone(),
                ));
            }
            let sig = ctx.sigs.get(n.as_str()).ok_or_else(|| {
                FrontendDiag::new(
                    codes::FE634_UNRESOLVED_REFERENCE_RS,
                    format!("call to undeclared function `{n}`"),
                    span.clone(),
                )
            })?;
            if args.len() != sig.params.len() {
                return Err(FrontendDiag::new(
                    codes::FE630_ILL_TYPED_RS,
                    format!(
                        "function `{n}` expects {} argument(s), found {}",
                        sig.params.len(),
                        args.len()
                    ),
                    span.clone(),
                ));
            }
            for (arg, pty) in args.iter().zip(sig.params.iter()) {
                let at = check_expr(arg, scopes, ctx)?;
                if &at != pty {
                    return Err(FrontendDiag::new(
                        codes::FE630_ILL_TYPED_RS,
                        format!(
                            "argument to `{n}` has type `{}` but the parameter is `{}`",
                            at.name(),
                            pty.name()
                        ),
                        expr_span(arg),
                    ));
                }
            }
            Ok(sig.ret.clone())
        }
        RsExpr::StructLit(name, fields, span) => {
            let def = ctx.structs.get(name).ok_or_else(|| {
                FrontendDiag::new(
                    codes::FE642_BAD_FIELD_ACCESS_RS,
                    format!("`{name}` is not a declared struct"),
                    span.clone(),
                )
            })?;
            // Exactly the declared fields, once each (SIGIL fails OPEN on a missing
            // record field — the frontend is the sole gate; FE640).
            let mut seen: HashSet<&str> = HashSet::new();
            for (fname, value, fspan) in fields {
                let want = def.field_ty(fname).ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE640_STRUCT_FIELD_MISMATCH_RS,
                        format!("struct `{name}` has no field `{fname}`"),
                        fspan.clone(),
                    )
                })?;
                if !seen.insert(fname.as_str()) {
                    return Err(FrontendDiag::new(
                        codes::FE640_STRUCT_FIELD_MISMATCH_RS,
                        format!("field `{fname}` is given twice in `{name}`"),
                        fspan.clone(),
                    ));
                }
                let got = check_expr(value, scopes, ctx)?;
                if &got != want {
                    return Err(FrontendDiag::new(
                        codes::FE640_STRUCT_FIELD_MISMATCH_RS,
                        format!(
                            "field `{fname}` of `{name}`: the value has type `{}` but the field is `{}`",
                            got.name(),
                            want.name()
                        ),
                        expr_span(value),
                    ));
                }
            }
            if seen.len() != def.fields.len() {
                let missing: Vec<&str> = def
                    .fields
                    .iter()
                    .map(|(fn_name, _)| fn_name.as_str())
                    .filter(|fn_name| !seen.contains(fn_name))
                    .collect();
                return Err(FrontendDiag::new(
                    codes::FE640_STRUCT_FIELD_MISMATCH_RS,
                    format!(
                        "struct `{name}` construction is missing field(s): {}",
                        missing.join(", ")
                    ),
                    span.clone(),
                ));
            }
            Ok(Ty::Struct(name.clone()))
        }
        RsExpr::Field(recv, fname, span) => {
            let rt = check_expr(recv, scopes, ctx)?;
            match rt {
                Ty::Struct(sname) => {
                    let def = ctx.structs.get(&sname).expect("struct type is registered");
                    let fty = def.field_ty(fname).ok_or_else(|| {
                        FrontendDiag::new(
                            codes::FE642_BAD_FIELD_ACCESS_RS,
                            format!("struct `{sname}` has no field `{fname}`"),
                            span.clone(),
                        )
                    })?;
                    Ok(fty.clone())
                }
                other => Err(FrontendDiag::new(
                    codes::FE642_BAD_FIELD_ACCESS_RS,
                    format!(
                        "field access `.{fname}` on a non-struct value of type `{}`",
                        other.name()
                    ),
                    span.clone(),
                )),
            }
        }
        RsExpr::EnumCtor(enum_name, variant, args, span) => {
            let def = ctx.enums.get(enum_name).ok_or_else(|| {
                FrontendDiag::new(
                    codes::FE652_BAD_MATCH_ARM_RS,
                    format!("`{enum_name}` is not a declared enum"),
                    span.clone(),
                )
            })?;
            let payloads = def.variant_payloads(variant).ok_or_else(|| {
                FrontendDiag::new(
                    codes::FE652_BAD_MATCH_ARM_RS,
                    format!("enum `{enum_name}` has no variant `{variant}`"),
                    span.clone(),
                )
            })?;
            // Construction arity is an enum-variant reference error (FE652); a
            // per-argument type mismatch is ill-typed (FE630).
            if args.len() != payloads.len() {
                return Err(FrontendDiag::new(
                    codes::FE652_BAD_MATCH_ARM_RS,
                    format!(
                        "variant `{enum_name}::{variant}` has {} field(s), construction supplies {}",
                        payloads.len(),
                        args.len()
                    ),
                    span.clone(),
                ));
            }
            for (arg, pty) in args.iter().zip(payloads.iter()) {
                let at = check_expr(arg, scopes, ctx)?;
                if &at != pty {
                    return Err(FrontendDiag::new(
                        codes::FE630_ILL_TYPED_RS,
                        format!(
                            "payload argument to `{enum_name}::{variant}` has type `{}` but the field is `{}`",
                            at.name(),
                            pty.name()
                        ),
                        expr_span(arg),
                    ));
                }
            }
            Ok(Ty::Enum(enum_name.clone()))
        }
        RsExpr::Declassify(inner, _, span) => {
            // RS5b: `declassify(value)` lowers the value's taint to @Public via a
            // frontend-synthesized linear cap. The frontend does NO flow analysis
            // (taint_check is the oracle); it only enforces the value is a scalar
            // (SR-B2 — `@Label` was only ever observed on `i64`/`bool`) and preserves
            // the value type (declassify changes taint, never the underlying type).
            let t = check_expr(inner, scopes, ctx)?;
            if !matches!(t, Ty::I64 | Ty::Bool) {
                return Err(FrontendDiag::new(
                    codes::FE672_BAD_DECLASSIFY_RS,
                    format!(
                        "`declassify` requires a scalar (`i64`/`bool`) value, found `{}`",
                        t.name()
                    ),
                    span.clone(),
                ));
            }
            Ok(t)
        }
    }
}

/// Return-path analysis (FE632): does control definitely leave `block` via a
/// `return` (or a value-producing tail)? A `while`/`let`/`assign`/`if`-without-
/// `else` does not guarantee it; an `if`/`else` does iff both branches do.
fn block_returns(block: &RsBlock) -> bool {
    block.tail.is_some() || block.stmts.iter().any(stmt_returns)
}

fn stmt_returns(stmt: &RsStmt) -> bool {
    match stmt {
        RsStmt::Return { .. } => true,
        RsStmt::If {
            then_block,
            else_block: Some(eb),
            ..
        } => block_returns(then_block) && block_returns(eb),
        // Every match arm lowers to `return <value>;`, so an arm always returns; the
        // checker already proved the match exhaustive (FE651) before this runs, so a
        // non-empty match returns on every path.
        RsStmt::Match { arms, .. } => !arms.is_empty(),
        _ => false,
    }
}

/// RS5b: does this block/statement/expression contain a `declassify(...)`? Walks
/// EVERY expression position (SR-B10) so a declassify nested anywhere is seen. Used
/// to (a) mark declassify-bearing fns for the FE040 leaf rule (SR-B5) and (b) gate
/// declassify against cap/effect/requires/invariant mode (SR-B6). The emitter runs
/// the same walk to provision one synthetic linear cap per call.
fn block_has_declassify(block: &RsBlock) -> bool {
    block.stmts.iter().any(stmt_has_declassify)
        || block.tail.as_ref().is_some_and(expr_has_declassify)
}

fn stmt_has_declassify(stmt: &RsStmt) -> bool {
    match stmt {
        RsStmt::Let { value, .. } | RsStmt::Assign { value, .. } => expr_has_declassify(value),
        RsStmt::Return { value, .. } => value.as_ref().is_some_and(expr_has_declassify),
        RsStmt::If {
            cond,
            then_block,
            else_block,
            ..
        } => {
            expr_has_declassify(cond)
                || block_has_declassify(then_block)
                || else_block.as_ref().is_some_and(block_has_declassify)
        }
        RsStmt::While { cond, body, .. } => expr_has_declassify(cond) || block_has_declassify(body),
        RsStmt::Match {
            scrutinee, arms, ..
        } => expr_has_declassify(scrutinee) || arms.iter().any(|a| expr_has_declassify(&a.value)),
    }
}

fn expr_has_declassify(e: &RsExpr) -> bool {
    match e {
        RsExpr::Declassify(..) => true,
        RsExpr::Unary(_, x, _) => expr_has_declassify(x),
        RsExpr::Bin(_, l, r, _) => expr_has_declassify(l) || expr_has_declassify(r),
        RsExpr::Call(_, args, _) | RsExpr::EnumCtor(_, _, args, _) => {
            args.iter().any(expr_has_declassify)
        }
        RsExpr::StructLit(_, fields, _) => fields.iter().any(|(_, v, _)| expr_has_declassify(v)),
        RsExpr::Field(recv, _, _) => expr_has_declassify(recv),
        RsExpr::Int(..) | RsExpr::Bool(..) | RsExpr::Var(..) => false,
    }
}

fn bin_err(msg: &str, tl: &Ty, tr: &Ty, span: &Range<usize>) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE630_ILL_TYPED_RS,
        format!("{msg} (found `{}` and `{}`)", tl.name(), tr.name()),
        span.clone(),
    )
}

/// Emit-safety gate (SC-2): every function/parameter/capability/struct/field name
/// — the only identifiers the emitter ever writes — must be a legal SIGIL
/// identifier that collides with neither a keyword, an emittable builtin
/// call-name, nor the `__fe_` prefix.
fn validate_ident(name: &str, kind: &str, span: &Range<usize>) -> Result<(), FrontendDiag> {
    if !crate::is_legal_identifier(name) {
        return Err(FrontendDiag::new(
            codes::FE620_BAD_IDENTIFIER_RS,
            format!("{kind} name `{name}` is not a legal SIGIL identifier"),
            span.clone(),
        ));
    }
    if name.starts_with(limits::SYNTH_PREFIX) {
        return Err(FrontendDiag::new(
            codes::FE620_BAD_IDENTIFIER_RS,
            format!(
                "{kind} name `{name}` uses the reserved `{}` prefix",
                limits::SYNTH_PREFIX
            ),
            span.clone(),
        ));
    }
    if crate::is_sigil_keyword(name) {
        return Err(FrontendDiag::new(
            codes::FE620_BAD_IDENTIFIER_RS,
            format!("{kind} name `{name}` collides with a SIGIL keyword"),
            span.clone(),
        ));
    }
    if is_reserved_builtin(name) {
        return Err(FrontendDiag::new(
            codes::FE620_BAD_IDENTIFIER_RS,
            format!("{kind} name `{name}` collides with a SIGIL builtin call-name"),
            span.clone(),
        ));
    }
    Ok(())
}

/// The census of bare-callable SIGIL builtins an emitted call could accidentally
/// bind. Conservative; grows as RS0 emits more surface. `trap_if` is the named
/// SC-2 example (a user `fn trap_if` would otherwise emit a call binding the
/// builtin — an authority leak invisible to the FE500 parse self-check).
fn is_reserved_builtin(name: &str) -> bool {
    matches!(name, "trap_if")
}
