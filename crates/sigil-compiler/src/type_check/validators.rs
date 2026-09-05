//! Declaration-time validators.
//!
//! Each function takes a read-only AST + (where needed) the type
//! universe, accumulates diagnostics, and returns nothing. They all
//! run BEFORE the main body type-checker so downstream code can
//! assume:
//!
//! - No type name shadows a reserved built-in (`Slot`).
//! - No record field is capability-typed (closes the LoadField
//!   aggregate-smuggling vector).
//! - No enum variant payload is capability-typed (closes the
//!   pattern-destructure variant of the same vector).
//! - No cap type declares more than 32 authorities (the bitvector
//!   width limit of the Z3 authority tracker).
//! - No inner-ring function declares `Unsafe` or `FFI` effects
//!   (privilege effects are outer-ring only).
//! - At most one `Main`-named entry actor exists in the program.
//! - Every actor capability state field is sourced from its
//!   `init` parameter.
//!
//! Extracted from `type_check/mod.rs` in structural-extraction PR 1.
//! Verbatim move — zero logic change. Validation order at the call
//! site (`check_with_options`) is preserved; the shadow CI gate
//! validates byte-equality of every diagnostic.

use std::collections::HashMap;

use super::{
    Type, TypeUniverse, render_type, resolve_type, resolve_type_expr, type_compatible,
    type_contains_cap, type_contains_typestate,
};
use crate::ast::Item;
use crate::diagnostics::{Diagnostic, codes};
use crate::span::Span;

/// T193 (Wall 1 Step 2): `Slot` is the name of a built-in linear
/// container; user records, enums, and cap types cannot shadow it.
/// Without this guard, an adversarial user could define
/// `enum Slot<T> { Empty, Full(T) }` and re-introduce the
/// aggregate-smuggling vector that T184 closes for user enums — the
/// built-in `Slot<Cap>` is sound only because its operations route
/// through dedicated AIR ops (SlotPut/SlotTake) that the Z3 tracker
/// special-cases, never through `EnumExtract`.
pub(super) fn validate_no_reserved_type_names(
    program: &crate::ast::Program,
    diagnostics: &mut Vec<Diagnostic>,
) {
    const RESERVED: &[&str] = &["Slot"];
    for module in &program.modules {
        for item in &module.items {
            let (name, span) = match item {
                Item::RecordDef(def) => (&def.name, def.span),
                Item::EnumDef(def) => (&def.name, def.span),
                Item::CapTypeDef(def) => (&def.name, def.span),
                _ => continue,
            };
            if RESERVED.contains(&name.as_str()) {
                diagnostics.push(Diagnostic::error(
                    codes::T193,
                    format!(
                        "type name `{name}` is reserved for a built-in; rename your type (e.g., `{name}State`, `My{name}`)"
                    ),
                    Some(span),
                ));
            }
            // R2 (HK3 hardening): reserve the `__` infix for compiler-generated
            // monomorphization instance names. `mangle_type(Box<i64>)` →
            // `Box__i64`; a user `record Box__i64` would collide with that
            // instance in the type registry, shadow its fields, and ICE AIR's
            // field-offset lookup. A single `_` is unaffected.
            if name.contains("__") {
                diagnostics.push(Diagnostic::error(
                    codes::T271,
                    format!(
                        "type name `{name}` contains `__` (double underscore), which is reserved for compiler-generated monomorphization names; use a single underscore or camelCase"
                    ),
                    Some(span),
                ));
            }
        }
    }
}

/// EX-1 (HK3 hardening): record FIELD types and enum PAYLOAD types are resolved
/// into the universe through the raw, sink-less `resolve_type_expr`
/// (`collect_type_universe` has no diagnostics access). So a wrong-arity generic
/// record there — `record H { p: Pair<i64> }` against `record Pair<A, B>` — is
/// admitted, then ICEs in AIR's field-registry lookup once a field of `p` is
/// read. This pass re-resolves each field/payload type WITH the diagnostics sink
/// and flags an arity mismatch as T231. It is deliberately arity-ONLY (not the
/// full `validate_lowered_type`) so it can't double-emit T066 / cap diagnostics
/// that other passes own.
pub(super) fn validate_field_payload_type_arity(
    program: &crate::ast::Program,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for module in &program.modules {
        for item in &module.items {
            match item {
                Item::RecordDef(def) => {
                    let scope = crate::ast::type_param_names(&def.type_params);
                    for f in &def.fields {
                        let resolved = resolve_type_expr(&f.ty, universe, &HashMap::new(), &scope);
                        check_type_arg_arity(&resolved, universe, f.ty.span, diagnostics);
                    }
                }
                Item::EnumDef(def) => {
                    let scope = crate::ast::type_param_names(&def.type_params);
                    for v in &def.variants {
                        for f in &v.fields {
                            let resolved =
                                resolve_type_expr(&f.ty, universe, &HashMap::new(), &scope);
                            check_type_arg_arity(&resolved, universe, f.ty.span, diagnostics);
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

/// The declared type-argument arity of a known record / enum / built-in carrier,
/// or `None` for an unknown / non-parametric name.
fn declared_type_arity(name: &str, universe: &TypeUniverse) -> Option<usize> {
    if let Some((tp, _)) = universe.records.get(name) {
        return Some(tp.len());
    }
    if let Some((tp, _)) = universe.enums.get(name) {
        return Some(tp.len());
    }
    match name {
        "Option" | "Slot" => Some(1),
        "Result" => Some(2),
        _ => None,
    }
}

/// Arity-only recursive walk — mirrors the T231 arm of `validate_lowered_type`,
/// descending every composite position. Emits ONLY T231 (no T066 / cap codes).
fn check_type_arg_arity(
    ty: &Type,
    universe: &TypeUniverse,
    span: Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match ty {
        Type::Named(name, args) => {
            if let Some(arity) = declared_type_arity(name, universe)
                && arity != args.len()
                && (arity > 0 || !args.is_empty())
            {
                diagnostics.push(Diagnostic::error(
                    codes::T231,
                    format!(
                        "type `{name}` takes {arity} type argument(s), but {} {} supplied",
                        args.len(),
                        if args.len() == 1 { "was" } else { "were" },
                    ),
                    Some(span),
                ));
            }
            for a in args {
                check_type_arg_arity(a, universe, span, diagnostics);
            }
        }
        Type::Tuple(elems) => {
            for e in elems {
                check_type_arg_arity(e, universe, span, diagnostics);
            }
        }
        Type::Array { elem, .. } => check_type_arg_arity(elem, universe, span, diagnostics),
        // F1: recurse into Ptr's inner like its MutPtr twin (asymmetric omission).
        Type::Slice(inner) | Type::Ref(inner, _) | Type::Ptr(inner) | Type::MutPtr(inner) => {
            check_type_arg_arity(inner, universe, span, diagnostics)
        }
        Type::Fn(params, ret, _, _) => {
            for p in params {
                check_type_arg_arity(p, universe, span, diagnostics);
            }
            check_type_arg_arity(ret, universe, span, diagnostics);
        }
        _ => {}
    }
}

/// T183 (step 25, axis-2 fourth touch): caps cannot be stored in record
/// fields. The Z3 capability authority tracker defaults `LoadField` to
/// full-authority — caps that flow through a record's field then read
/// back out lose their restriction mask. `tests/attack/KNOWN_GAPS.md`
/// labeled this the aggregate-smuggling vector (Attack 06b) and assumed
/// the parser blocked it, but the parser only rejects the literal field
/// name `cap` (a reserved keyword). A field named `f: Fuel` (or any
/// non-keyword name) slipped through. This pass closes the gap at the
/// source: a record whose field type contains a cap is rejected with
/// T183.
/// T248 / T249 / T250 (trait Wall, PR-5): coherence of explicit
/// `impl Trait for Type` blocks.
/// - The named trait must be in scope (else T248).
/// - Orphan proxy (AG-T2): the implementing type must be a record or enum
///   declared in this program — never a primitive — so the built-in primitive
///   impls cannot be overridden from userland. The full author-identity rule is
///   deferred to the capability model.
/// - No two explicit impls of the same `(trait, type)` pair (T250).
///
/// Inherent `impl Type { ... }` blocks (`trait_name == None`) are not checked
/// here. Satisfaction itself is handled structurally (the methods register as
/// `Type::method` either way); this pass only polices coherence.
pub(super) fn validate_trait_impls(
    program: &crate::ast::Program,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut seen: std::collections::BTreeSet<(String, String)> = std::collections::BTreeSet::new();
    for module in &program.modules {
        for item in &module.items {
            let Item::ImplDef(def) = item else {
                continue;
            };
            let Some(trait_name) = &def.trait_name else {
                continue; // inherent impl — nothing to police
            };

            if !universe.traits.contains_key(trait_name) {
                diagnostics.push(Diagnostic::error(
                    codes::T248,
                    format!(
                        "`impl {trait_name} for {}` names trait `{trait_name}`, which is not in scope — declare it (`trait {trait_name} {{ … }}`) or import the module that does",
                        def.type_name
                    ),
                    Some(def.span),
                ));
                continue;
            }

            let is_local_type = universe.records.contains_key(&def.type_name)
                || universe.enums.contains_key(&def.type_name);
            if !is_local_type {
                diagnostics.push(Diagnostic::error(
                    codes::T249,
                    format!(
                        "cannot write `impl {trait_name} for {}` — an explicit trait impl is only allowed for a record or enum declared in this program. `{}` is a primitive or foreign type; its trait impls are fixed (the built-in primitive impls are unoverridable)",
                        def.type_name, def.type_name
                    ),
                    Some(def.span),
                ));
                continue;
            }

            if !seen.insert((trait_name.clone(), def.type_name.clone())) {
                diagnostics.push(Diagnostic::error(
                    codes::T250,
                    format!(
                        "duplicate `impl {trait_name} for {}` — a (trait, type) pair may be implemented at most once",
                        def.type_name
                    ),
                    Some(def.span),
                ));
            }
        }
    }
}

pub(super) fn validate_records_no_cap_fields(
    program: &crate::ast::Program,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for module in &program.modules {
        for item in &module.items {
            let Item::RecordDef(def) = item else {
                continue;
            };
            for field in &def.fields {
                let field_ty = resolve_type_expr(
                    &field.ty,
                    universe,
                    &HashMap::new(),
                    &crate::ast::type_param_names(&def.type_params),
                );
                if type_contains_cap(&field_ty) {
                    diagnostics.push(Diagnostic::error(
                        codes::T183,
                        format!(
                            "record `{}` field `{}` is capability-typed (`{}`) — caps cannot be stored in record fields because LoadField bypasses Z3's authority tracker. Pass the cap by name through actor messages or function arguments, or replace the field with a non-cap surrogate (e.g., an `i64` amount).",
                            def.name,
                            field.name,
                            render_type(&field_ty),
                        ),
                        Some(def.span),
                    ));
                }
                // Typestate (TS4, ST-6 / BL-2): a typestate value is affine; stashing
                // it in a field and extracting it twice via LoadField would mint two
                // handles from one and defeat the use-after-transition guarantee — the
                // same aggregate-smuggle channel T183 closes for caps.
                if type_contains_typestate(&field_ty, universe) {
                    diagnostics.push(Diagnostic::error(
                        codes::T275,
                        format!(
                            "record `{}` field `{}` is typestate-typed (`{}`) — a typestate value is affine, and extracting it twice via field access would mint two handles from one and defeat the use-after-transition guarantee (the same aggregate-smuggling channel T183 closes for caps). Pass it by value through function arguments / return values instead of storing it in a record field.",
                            def.name,
                            field.name,
                            render_type(&field_ty),
                        ),
                        Some(def.span),
                    ));
                }
            }
        }
    }
}

/// T185 (step 31, axis-2 fifth touch): cap types are limited to 32
/// authorities because the Z3 capability layer encodes authority
/// masks as 32-bit bitvectors (QF_BV). A cap type with 33+
/// authorities would overflow the bit-shift in `full_mask`:
/// `1u32 << 32+` is implementation-defined; on x86, the shift
/// instruction masks the count modulo 32, so the 33rd authority
/// (bit index 32) collapses onto bit 0, the 34th onto bit 1, etc.
/// The corrupted mask would make Z3 compute the wrong required-
/// authority set, leading to false negatives (accepting unsafe
/// programs) or false positives (rejecting safe ones).
///
/// Pre-step-31, the compiler accepted any number of authorities
/// silently — the bug was a latent soundness gap waiting for a
/// policy author (or adversary) to declare a 32+ authority cap
/// type. Step 31 closes the bound at the declaration site.
pub(super) fn validate_cap_type_authority_count(
    program: &crate::ast::Program,
    diagnostics: &mut Vec<Diagnostic>,
) {
    const MAX_AUTHORITIES: usize = 32;

    for module in &program.modules {
        for item in &module.items {
            let Item::CapTypeDef(def) = item else {
                continue;
            };
            if def.authorities.len() > MAX_AUTHORITIES {
                diagnostics.push(Diagnostic::error(
                    codes::T185,
                    format!(
                        "cap type `{}` declares {} authorities — the Z3 capability layer encodes authority masks as 32-bit bitvectors, so at most {MAX_AUTHORITIES} authorities are allowed per cap type. Split into multiple narrower cap types (e.g., one per authority cluster) or factor the authority space differently.",
                        def.name,
                        def.authorities.len(),
                    ),
                    Some(def.span),
                ));
            }
        }
    }
}

/// E003 (step 30, axis-6 fourth touch): inner-ring functions cannot
/// declare `Unsafe` or `FFI` effects. Both are outer-ring privileges:
/// `Unsafe` gates `handle Unsafe { ... }` blocks (E002 would normally
/// fire) and `FFI` gates extern calls (R003 fires per step 24). But
/// `effect_check.rs` explicitly skips inner-ring modules ("inner ring
/// exempt"), so E002 never fires for inner-ring `handle Unsafe` and
/// the trust system is silently bypassed at the function-signature
/// level.
///
/// Concrete abuse vector (verified live against the pre-step-30
/// commit):
///
///   module ext;  // inner ring, not trusted
///   fn do_dangerous() ! { Unsafe } {
///       handle Unsafe { ... };       // bypassed E002
///       return;
///   }
///
/// Pre-step-30: compiled cleanly. E003 was declared in the registry
/// since the ring system was introduced, but never emitted. After
/// step 30, the validator walks each inner-ring module's free
/// functions and emits E003 if the effect row declares `Unsafe` or
/// `FFI` — the two privilege effects that should never appear in the
/// safe-by-construction tier. Other effects (`Alloc` for memory,
/// user-declared `NetIO`/`Filesystem` for policy-domain audit
/// labels) are allowed in inner ring because they don't have
/// trust-bypass semantics.
pub(super) fn validate_inner_ring_no_effects(
    program: &crate::ast::Program,
    diagnostics: &mut Vec<Diagnostic>,
) {
    const FORBIDDEN_INNER_EFFECTS: &[&str] = &["Unsafe", "FFI"];

    for module in &program.modules {
        if !matches!(module.ring, crate::ast::Ring::Inner) {
            continue;
        }
        for item in &module.items {
            let Item::FnDef(def) = item else {
                continue;
            };
            let Some(effects) = &def.effects else {
                continue;
            };
            let mut forbidden_present: Vec<&str> = effects
                .iter()
                .filter(|e| FORBIDDEN_INNER_EFFECTS.contains(&e.as_str()))
                .map(|s| s.as_str())
                .collect();
            if forbidden_present.is_empty() {
                continue;
            }
            forbidden_present.sort();
            forbidden_present.dedup();
            let names = forbidden_present
                .iter()
                .map(|e| format!("`{e}`"))
                .collect::<Vec<_>>()
                .join(", ");
            diagnostics.push(Diagnostic::error(
                codes::E003,
                format!(
                    "inner-ring function `{}` declares privilege effect(s) [{}] — `Unsafe` and `FFI` are outer-ring privileges. Move the function to a `#[ring(outer)] #[trusted]` module if it genuinely needs them, or drop those effects from the row (other effects like `Alloc` or user-declared effects are fine in inner ring).",
                    def.name, names,
                ),
                Some(def.span),
            ));
        }
    }
}

/// Taint polymorphism scope gate (T001 family). `@Flow` is sound only because the
/// taint checker re-verifies the ANNOTATED FUNCTION'S BODY once per admissible
/// label. That per-instantiation check runs over plain module functions; a generic
/// function or an impl method instead reaches the checker through
/// monomorphization, which rebuilds its `TypedParam`s and would drop the `@Flow`
/// marker. Rather than let the contract degrade silently to `@Public` there,
/// reject it at declaration with the reason.
///
/// Free non-generic functions — every `json::` helper this exists for — are
/// unaffected. Lifting the restriction means teaching the monomorph paths in
/// `expressions/calls.rs` and `expressions/methods.rs` to carry `flow` through.
pub(super) fn validate_flow_polymorphism_scope(
    program: &crate::ast::Program,
    diagnostics: &mut Vec<Diagnostic>,
) {
    fn uses_flow(def: &crate::ast::FnDef) -> bool {
        def.ret_flow || def.params.iter().any(|p| p.flow)
    }

    for module in &program.modules {
        for item in &module.items {
            match item {
                Item::FnDef(def) if uses_flow(def) && !def.type_params.is_empty() => {
                    diagnostics.push(Diagnostic::error(
                        codes::P021,
                        format!(
                            "`@Flow` is not supported on generic function `{}`: a generic function \
                             is taint-checked per monomorphized instance, which does not carry the \
                             polymorphic label. Remove the type parameters or annotate a concrete \
                             label.",
                            def.name
                        ),
                        Some(def.span),
                    ));
                }
                Item::ImplDef(imp) => {
                    for method in imp.methods.iter().filter(|m| uses_flow(m)) {
                        diagnostics.push(Diagnostic::error(
                            codes::P021,
                            format!(
                                "`@Flow` is not supported on impl method `{}::{}`: impl methods are \
                                 taint-checked per monomorphized instance, which does not carry the \
                                 polymorphic label. Use a free function, or annotate a concrete label.",
                                imp.type_name, method.name
                            ),
                            Some(method.span),
                        ));
                    }
                }
                _ => {}
            }
        }
    }
}

/// Mutation-as-capability (PR-4, LD-6): the honesty WARNING (T252). A `@ReadOnly`
/// parameter whose declared type is an aliasable REFERENCE/VIEW — `&T` / `&[T]`,
/// i.e. `Param.ty.ref_kind.is_some()` — gets a non-blocking warning: without a
/// borrow/aliasing pass the no-mutation guarantee is only partial for a view (a
/// different alias elsewhere could still mutate the pointee). By-value heap params
/// (records / `Vec` / `Map`, `ref_kind == None`) carry the same partial guarantee
/// but are NOT linted (AG-11) — else every `@ReadOnly self` in the stdlib would
/// flood warnings. Fires once per parameter at the DECLARATION site (free fns,
/// impl methods, extern decls), so it is independent of monomorphization and of
/// call sites. This is the ONLY warning-severity diagnostic SIGIL emits today.
pub(super) fn lint_readonly_reference_params(
    program: &crate::ast::Program,
    diagnostics: &mut Vec<Diagnostic>,
) {
    fn lint_params(params: &[crate::ast::Param], diagnostics: &mut Vec<Diagnostic>) {
        for param in params {
            if param.mutability == crate::ast::Mutability::ReadOnly && param.ty.ref_kind.is_some() {
                diagnostics.push(Diagnostic::warning(
                    codes::T252,
                    format!(
                        "`@ReadOnly` on the reference/view parameter `{}`: the no-mutation \
                         guarantee is partial until borrow checking lands — a different alias \
                         could still mutate the pointee. The promise is honored as far as v1 \
                         enforces it (this function won't mutate through the handle).",
                        param.name
                    ),
                    Some(param.span),
                ));
            }
        }
    }
    for module in &program.modules {
        for item in &module.items {
            match item {
                Item::FnDef(def) => lint_params(&def.params, diagnostics),
                Item::ImplDef(def) => {
                    for method in &def.methods {
                        lint_params(&method.params, diagnostics);
                    }
                }
                Item::ExternFnDecl(def) => lint_params(&def.params, diagnostics),
                _ => {}
            }
        }
    }
}

/// T184 (step 27, axis-6 third touch): companion to T183 for enum
/// variant payloads. Pattern-destructure bindings on a cap-typed
/// payload produce a fresh cap that Z3's authority tracker treats as
/// full authority — the SAME aggregate-smuggling vector that step 25
/// closed for records, but through a different AIR channel
/// (EnumConstruct + match-bindings instead of record field access).
///
/// Concrete attack (verified live against the pre-change commit):
///
///   enum CapBox { Wrapped(Fuel), Empty }
///   let restricted: Fuel = fuel.restrict(burn);  // burn-only
///   let wrapped = Wrapped(restricted);           // smuggle via enum
///   match wrapped {
///       Wrapped(extracted) => needs_full(extracted),  // Z3 sees full
///       Empty => {},
///   }
///
/// Pre-step-27: compiled cleanly. The restricted cap passed
/// needs_full's full-authority sink because the match binding
/// `extracted` lost its restriction provenance. Step 27 closes this
/// at the source by rejecting any enum variant payload whose type
/// contains a cap.
pub(super) fn validate_enums_no_cap_payloads(
    program: &crate::ast::Program,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for module in &program.modules {
        for item in &module.items {
            let Item::EnumDef(def) = item else {
                continue;
            };
            for variant in &def.variants {
                for (idx, payload_field) in variant.fields.iter().enumerate() {
                    // Wall 4 Step 6: variant field carries `name` +
                    // `ty`; resolve from `.ty`.
                    let payload_ty = resolve_type_expr(
                        &payload_field.ty,
                        universe,
                        &HashMap::new(),
                        &crate::ast::type_param_names(&def.type_params),
                    );
                    if type_contains_cap(&payload_ty) {
                        diagnostics.push(Diagnostic::error(
                            codes::T184,
                            format!(
                                "enum `{}` variant `{}` payload position {idx} is capability-typed (`{}`) — caps cannot be carried by enum variant payloads because pattern-destructure bindings bypass Z3's authority tracker (the same aggregate-smuggling channel T183 closes for records). Pass the cap by name through actor messages or function arguments, or replace the payload with a non-cap surrogate (e.g., an `i64` amount).",
                                def.name,
                                variant.name,
                                render_type(&payload_ty),
                            ),
                            Some(def.span),
                        ));
                    }
                    // Typestate (TS4, ST-6 / BL-2): a typestate payload is affine; a
                    // pattern-destructure can bind it twice across arms → two handles
                    // from one → defeats the use-after-transition guarantee (T275).
                    if type_contains_typestate(&payload_ty, universe) {
                        diagnostics.push(Diagnostic::error(
                            codes::T275,
                            format!(
                                "enum `{}` variant `{}` payload position {idx} is typestate-typed (`{}`) — a typestate value is affine, and a pattern-destructure can extract it more than once, defeating the use-after-transition guarantee (the same aggregate-smuggling channel T184 closes for caps). Pass it by value through function arguments / return values instead of an enum payload.",
                                def.name,
                                variant.name,
                                render_type(&payload_ty),
                            ),
                            Some(def.span),
                        ));
                    }
                }
            }
        }
    }
}

/// A free `tool_main` must be `pub`: export hygiene exports only externally
/// callable functions, so a private entry point produces a module the runtime
/// cannot run. Rejecting it here names the fix at the declaration instead of
/// surfacing as a runtime `no tool_main entry point found` on first use.
pub(super) fn validate_tool_main_visibility(
    program: &crate::ast::Program,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for module in &program.modules {
        for item in &module.items {
            let Item::FnDef(def) = item else {
                continue;
            };
            if def.name == "tool_main" && !matches!(def.visibility, crate::ast::Visibility::Public)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T283,
                    format!(
                        "`tool_main` in module `{}` is not `pub`: a private entry point is never exported, so the compiled tool has no entry point (T283)",
                        module.name
                    ),
                    Some(def.span),
                ));
            }
        }
    }
}

pub(super) fn validate_entry_actors(
    program: &crate::ast::Program,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut first_entry = None::<(String, String, Span)>;

    for module in &program.modules {
        for item in &module.items {
            let Item::ActorDef(def) = item else {
                continue;
            };

            if !def.is_entry {
                continue;
            }

            if def.name != "Main" {
                diagnostics.push(Diagnostic::error(
                    codes::T090,
                    format!(
                        "entry actor must be named `Main`, found `{}` in module `{}`",
                        def.name, module.name
                    ),
                    Some(def.span),
                ));
            }

            if let Some((existing_module, existing_name, existing_span)) = &first_entry {
                diagnostics.push(Diagnostic::error(
                    codes::T091,
                    format!(
                        "multiple entry actors defined; `{existing_name}` in module `{existing_module}` was already marked as entry"
                    ),
                    Some(existing_span.join(def.span)),
                ));
            } else {
                first_entry = Some((module.name.clone(), def.name.clone(), def.span));
            }
        }
    }
}

pub(super) fn validate_actor_capability_state(
    program: &crate::ast::Program,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for module in &program.modules {
        for item in &module.items {
            let Item::ActorDef(def) = item else {
                continue;
            };

            if def.is_entry {
                continue;
            }

            let init_params = def
                .init
                .as_ref()
                .map(|init| {
                    init.params
                        .iter()
                        .map(|param| resolve_type(&param.ty, universe, diagnostics))
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();

            for field in &def.state_fields {
                let field_ty = resolve_type(&field.ty, universe, diagnostics);
                let Type::Cap(cap_name, _) = &field_ty else {
                    continue;
                };

                if !init_params
                    .iter()
                    .any(|param_ty| type_compatible(&field_ty, param_ty))
                {
                    diagnostics.push(Diagnostic::error(
                        codes::T092,
                        format!(
                            "actor `{}` capability state field `{}` of type `{}` must be provided by an `init` parameter",
                            def.name, field.name, cap_name
                        ),
                        Some(field.span),
                    ));
                }
            }
        }
    }
}

/// Typestate (TS4, ST-6 / BL-2): a typestate value may not be an actor STATE field.
/// Caps are deliberately allowed in actor state (the sanctioned holding place, gated
/// by T092); a typestate value is NOT — the actor could take it out of its state
/// across handler invocations more than once and double-consume it (the actor-side
/// sibling of the T275 record/enum/array gate). Covers EVERY actor (incl. entry).
/// Uses the non-validating resolver so it does not double-emit resolution
/// diagnostics already raised by `validate_actor_capability_state`.
pub(super) fn validate_actors_no_typestate_state(
    program: &crate::ast::Program,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for module in &program.modules {
        for item in &module.items {
            let Item::ActorDef(def) = item else {
                continue;
            };
            for field in &def.state_fields {
                let field_ty = resolve_type_expr(&field.ty, universe, &HashMap::new(), &[]);
                if type_contains_typestate(&field_ty, universe) {
                    diagnostics.push(Diagnostic::error(
                        codes::T275,
                        format!(
                            "actor `{}` state field `{}` is typestate-typed (`{}`) — a typestate value is affine, and an actor can extract it from its state across handler calls more than once, defeating the use-after-transition guarantee (the actor-side sibling of the record/enum/array aggregate-smuggle channel). Hold an `i64` surrogate in actor state and pass the typestate value by value through handler arguments instead.",
                            def.name,
                            field.name,
                            render_type(&field_ty),
                        ),
                        Some(field.span),
                    ));
                }
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Effect-row variables (roadmap Phase 4, row polymorphism).
//
// A type parameter used inside an effect row (`fn h<e>(f: Fn(i64) -> i64
// ! { e }) -> i64 ! { e }`) is EFFECT-kinded ("kind-by-use", see
// `ast::effect_row_param_names`). Kind-by-use is only unambiguous because this
// pass hard-errors (E011) every ambiguous or unsupported shape FIRST, before
// any body is checked — downstream consumers (the generic call path's binding
// walk, mono-key row component, cert collection) may then assume the
// classification is total and disjoint.
//
// v1 boring limits (each fails CLOSED with E011; relaxable later with
// dedicated designs):
//   - free generic fns only — impl/trait/record/enum binders in row position
//     are rejected (the parallel method mono paths never learned rows);
//   - occurrences only in the declared row, the TOP-LEVEL row of a Fn-typed
//     parameter (the binding position; at most ONE variable per binding row so
//     the union-binding has a unique least solution), or the return type;
//   - no body-annotation occurrences (`let g: Fn(..) ! { e }`) — body
//     annotations resolve without substitution, so the row would silently
//     drop to the empty set and produce per-instance confusion;
//   - no shadowing a registered effect, no type-position use, no duplicate
//     binder names, no higher-kinded/state binders in rows.
//
// This pass also closes the T069 generic-signature hole: generic fns never
// pass through `resolve_type` (they are stashed as AST and resolved via the
// PURE path at mono time), so an unknown effect name in a generic signature's
// type row was silently dropped. Here it gets the same strict T069 +
// closest-name hint the non-generic path has.

/// Does `ty` mention `name` as a TYPE (a single-segment nominal head), at any
/// depth? Used for the both-kinds E011 — a binder cannot be a row variable and
/// a type parameter at once.
fn type_position_mentions(ty: &crate::ast::TypeExpr, name: &str) -> bool {
    // WALKER FENCE (Phase 4 sweep): exhaustive destructure, no `..` — see
    // `ast::collect_type_row_names`.
    let crate::ast::TypeExpr {
        path: _,
        ref_kind: _,
        deadline: _,
        span: _,
        fn_type: _,
        array_type: _,
        tuple_type: _,
    } = ty;
    if let Some(ft) = &ty.fn_type {
        return ft.params.iter().any(|p| type_position_mentions(p, name))
            || type_position_mentions(&ft.return_type, name);
    }
    if let Some(arr) = &ty.array_type {
        return type_position_mentions(&arr.elem, name);
    }
    if let Some(elems) = &ty.tuple_type {
        return elems.iter().any(|e| type_position_mentions(e, name));
    }
    (ty.path.segments.len() == 1 && ty.path.segments[0] == name)
        || ty
            .path
            .type_args
            .iter()
            .any(|a| type_position_mentions(a, name))
}

/// First row-variable name mentioned in any effect row within `ty`, at any
/// depth. `None` if no row in `ty` mentions one.
fn first_row_var_mention<'a>(
    ty: &crate::ast::TypeExpr,
    row_params: &'a [String],
) -> Option<&'a str> {
    let mut occ = Vec::new();
    crate::ast::collect_type_row_names(ty, &mut occ);
    row_params
        .iter()
        .find(|r| occ.contains(&r.as_str()))
        .map(String::as_str)
}

/// Body walk for the no-body-annotation rule: visits every `let` / tuple-`let`
/// type annotation and every closure param/return annotation reachable in the
/// block, at any nesting depth. Total match over `Stmt`/`Expr` (the
/// walker-fence discipline) so a future statement or expression form cannot
/// silently escape the walk.
fn check_body_annotations(
    block: &crate::ast::Block,
    row_params: &[String],
    diagnostics: &mut Vec<Diagnostic>,
) {
    for stmt in &block.statements {
        check_stmt_annotations(stmt, row_params, diagnostics);
    }
}

#[deny(clippy::wildcard_enum_match_arm)]
fn check_stmt_annotations(
    stmt: &crate::ast::Stmt,
    row_params: &[String],
    diagnostics: &mut Vec<Diagnostic>,
) {
    use crate::ast::Stmt;
    let check_annotation =
        |ty: &Option<crate::ast::TypeExpr>, span: Span, diagnostics: &mut Vec<Diagnostic>| {
            if let Some(ty) = ty
                && let Some(v) = first_row_var_mention(ty, row_params)
            {
                diagnostics.push(Diagnostic::error(
                    codes::E011,
                    format!(
                        "effect-row variable `{v}` cannot appear in a body type \
                         annotation — rows are instantiated per call site (v1 restriction)"
                    ),
                    Some(span),
                ));
            }
        };
    match stmt {
        Stmt::Let(s) => {
            check_annotation(&s.ty, s.span, diagnostics);
            check_expr_annotations(&s.value, row_params, diagnostics);
        }
        Stmt::LetTuple(s) => {
            check_annotation(&s.ty, s.span, diagnostics);
            check_expr_annotations(&s.value, row_params, diagnostics);
        }
        Stmt::Assign(s) => {
            check_expr_annotations(&s.target, row_params, diagnostics);
            check_expr_annotations(&s.value, row_params, diagnostics);
        }
        Stmt::Expr(s) => check_expr_annotations(&s.expr, row_params, diagnostics),
        Stmt::If(s) => {
            check_expr_annotations(&s.condition, row_params, diagnostics);
            check_body_annotations(&s.then_branch, row_params, diagnostics);
            check_body_annotations(&s.else_branch, row_params, diagnostics);
        }
        Stmt::Match(s) => {
            check_expr_annotations(&s.scrutinee, row_params, diagnostics);
            for arm in &s.arms {
                if let Some(g) = &arm.guard {
                    check_expr_annotations(g, row_params, diagnostics);
                }
                check_body_annotations(&arm.body, row_params, diagnostics);
            }
        }
        Stmt::While(s) => {
            check_expr_annotations(&s.condition, row_params, diagnostics);
            check_body_annotations(&s.body, row_params, diagnostics);
        }
        Stmt::ForIn(s) => {
            check_expr_annotations(&s.iterable, row_params, diagnostics);
            check_body_annotations(&s.body, row_params, diagnostics);
        }
        Stmt::ForRange(s) => {
            check_expr_annotations(&s.start, row_params, diagnostics);
            check_expr_annotations(&s.end, row_params, diagnostics);
            check_body_annotations(&s.body, row_params, diagnostics);
        }
        Stmt::Return(s) => {
            if let Some(v) = &s.value {
                check_expr_annotations(v, row_params, diagnostics);
            }
        }
        Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

#[deny(clippy::wildcard_enum_match_arm)]
fn check_expr_annotations(
    expr: &crate::ast::Expr,
    row_params: &[String],
    diagnostics: &mut Vec<Diagnostic>,
) {
    use crate::ast::Expr;
    match expr {
        Expr::Closure(c) => {
            for p in &c.params {
                if let Some(v) = first_row_var_mention(&p.ty, row_params) {
                    diagnostics.push(Diagnostic::error(
                        codes::E011,
                        format!(
                            "effect-row variable `{v}` cannot appear in a closure \
                             annotation — rows are instantiated per call site (v1 \
                             restriction)"
                        ),
                        Some(p.span),
                    ));
                }
            }
            if let Some(ret) = &c.return_type
                && let Some(v) = first_row_var_mention(ret, row_params)
            {
                diagnostics.push(Diagnostic::error(
                    codes::E011,
                    format!(
                        "effect-row variable `{v}` cannot appear in a closure \
                         annotation — rows are instantiated per call site (v1 restriction)"
                    ),
                    Some(c.span),
                ));
            }
            check_body_annotations(&c.body, row_params, diagnostics);
        }
        Expr::Call(c) => {
            for a in &c.args {
                check_expr_annotations(a, row_params, diagnostics);
            }
        }
        Expr::MethodCall(m) => {
            check_expr_annotations(&m.receiver, row_params, diagnostics);
            for a in &m.args {
                check_expr_annotations(a, row_params, diagnostics);
            }
        }
        Expr::Binary(b) => {
            check_expr_annotations(&b.lhs, row_params, diagnostics);
            check_expr_annotations(&b.rhs, row_params, diagnostics);
        }
        Expr::FieldAccess(f) => check_expr_annotations(&f.object, row_params, diagnostics),
        Expr::Index(i) => {
            check_expr_annotations(&i.array, row_params, diagnostics);
            check_expr_annotations(&i.index, row_params, diagnostics);
        }
        Expr::Slice(s) => {
            check_expr_annotations(&s.array, row_params, diagnostics);
            if let Some(start) = &s.start {
                check_expr_annotations(start, row_params, diagnostics);
            }
            if let Some(end) = &s.end {
                check_expr_annotations(end, row_params, diagnostics);
            }
        }
        Expr::ArrayLit(a) => {
            for e in &a.elements {
                check_expr_annotations(e, row_params, diagnostics);
            }
        }
        Expr::Tuple(t) => {
            for e in &t.elements {
                check_expr_annotations(e, row_params, diagnostics);
            }
        }
        Expr::Try(t) => check_expr_annotations(&t.value, row_params, diagnostics),
        Expr::ResultCtor(r) => check_expr_annotations(&r.value, row_params, diagnostics),
        Expr::RecordConstruct(r) => {
            for (_, e) in &r.fields {
                check_expr_annotations(e, row_params, diagnostics);
            }
        }
        Expr::EnumConstruct(e) => {
            for f in &e.fields {
                check_expr_annotations(f, row_params, diagnostics);
            }
        }
        Expr::Send(s) => check_expr_annotations(&s.message, row_params, diagnostics),
        Expr::Ask(a) => {
            check_expr_annotations(&a.message, row_params, diagnostics);
            check_expr_annotations(&a.timeout, row_params, diagnostics);
        }
        Expr::Spawn(s) => {
            for a in &s.args {
                check_expr_annotations(a, row_params, diagnostics);
            }
        }
        Expr::Mint(m) => check_expr_annotations(&m.target, row_params, diagnostics),
        Expr::Borrow(b) => check_expr_annotations(&b.inner, row_params, diagnostics),
        Expr::Grant(g) => {
            check_expr_annotations(&g.cap, row_params, diagnostics);
            check_expr_annotations(&g.body, row_params, diagnostics);
        }
        Expr::Handle(h) => {
            // `handle e { .. }` of a row VARIABLE: rejected at the declaration
            // (fail-fast) rather than as a mono-time "unknown effect" T069 —
            // which an UNCALLED row-poly fn would never even reach (generic
            // bodies are only checked at instantiation).
            for eff in &h.effects {
                if row_params.contains(eff) {
                    diagnostics.push(Diagnostic::error(
                        codes::E011,
                        format!(
                            "effect-row variable `{eff}` cannot be handled — a handler \
                             discharges CONCRETE effects (v1 restriction)"
                        ),
                        Some(h.span),
                    ));
                }
            }
            check_body_annotations(&h.body, row_params, diagnostics);
        }
        Expr::Perform(p) => {
            for a in &p.args {
                check_expr_annotations(a, row_params, diagnostics);
            }
        }
        Expr::ClauseHandle(c) => {
            check_expr_annotations(&c.scrutinee, row_params, diagnostics);
            for clause in &c.clauses {
                if row_params.contains(&clause.effect) {
                    diagnostics.push(Diagnostic::error(
                        codes::E011,
                        format!(
                            "effect-row variable `{}` cannot be handled — a handler \
                             discharges CONCRETE effects (v1 restriction)",
                            clause.effect
                        ),
                        Some(c.span),
                    ));
                }
                check_body_annotations(&clause.body, row_params, diagnostics);
            }
        }
        Expr::Resume(r) => check_expr_annotations(&r.value, row_params, diagnostics),
        Expr::Declassify(d) => {
            check_expr_annotations(&d.value, row_params, diagnostics);
            check_expr_annotations(&d.cap, row_params, diagnostics);
        }
        Expr::DeclassifyCt(d) => {
            check_expr_annotations(&d.value, row_params, diagnostics);
            check_expr_annotations(&d.cap, row_params, diagnostics);
        }
        Expr::Region(r) => {
            check_expr_annotations(&r.limit, row_params, diagnostics);
            check_body_annotations(&r.body, row_params, diagnostics);
        }
        Expr::FString(f) => {
            for part in &f.parts {
                if let crate::ast::FStringPart::Hole(e) = part {
                    check_expr_annotations(e, row_params, diagnostics);
                }
            }
        }
        Expr::Literal(_)
        | Expr::Path(_)
        | Expr::CapRestrict(_)
        | Expr::CapRestrictDeadline(_)
        | Expr::CapSplit(_)
        | Expr::CapDraw(_) => {}
    }
}

/// A non-fn item's binder used in a row position anywhere in `tys` → E011
/// (v1: free generic fns only).
fn reject_item_row_binders(
    kind: &str,
    type_params: &[crate::ast::TypeParam],
    row_lists: &[&Option<Vec<String>>],
    tys: &[&crate::ast::TypeExpr],
    span: Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if type_params.is_empty() {
        return;
    }
    let mut occ: Vec<&str> = Vec::new();
    for names in row_lists.iter().filter_map(|rl| rl.as_ref()) {
        occ.extend(names.iter().map(String::as_str));
    }
    for ty in tys {
        crate::ast::collect_type_row_names(ty, &mut occ);
    }
    for tp in type_params {
        if occ.iter().any(|n| *n == tp.name) {
            diagnostics.push(Diagnostic::error(
                codes::E011,
                format!(
                    "effect-row variables are only supported on free generic functions — \
                     `{}` is a {kind} type parameter used in an effect row (v1 restriction)",
                    tp.name
                ),
                Some(span),
            ));
        }
    }
}

/// Phase 4 (row polymorphism): validate every effect-row variable shape, and
/// close the T069 generic-signature hole. See the module-level comment above.
pub(super) fn validate_effect_row_params(
    program: &crate::ast::Program,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for module in &program.modules {
        for item in &module.items {
            match item {
                Item::FnDef(def) => {
                    validate_fn_row_params(def, universe, diagnostics);
                }
                Item::RecordDef(def) => {
                    let tys: Vec<&crate::ast::TypeExpr> =
                        def.fields.iter().map(|f| &f.ty).collect();
                    reject_item_row_binders(
                        "record",
                        &def.type_params,
                        &[],
                        &tys,
                        def.span,
                        diagnostics,
                    );
                }
                Item::EnumDef(def) => {
                    let tys: Vec<&crate::ast::TypeExpr> = def
                        .variants
                        .iter()
                        .flat_map(|v| v.fields.iter().map(|f| &f.ty))
                        .collect();
                    reject_item_row_binders(
                        "enum",
                        &def.type_params,
                        &[],
                        &tys,
                        def.span,
                        diagnostics,
                    );
                }
                Item::ImplDef(def) => {
                    for method in &def.methods {
                        // Impl-level and method-level binders both scope over a
                        // method signature; either kind used in one of its rows
                        // is rejected (the method mono paths never learned rows).
                        let mut binders = def.type_params.clone();
                        binders.extend(method.type_params.iter().cloned());
                        let mut tys: Vec<&crate::ast::TypeExpr> =
                            method.params.iter().map(|p| &p.ty).collect();
                        if let Some(ret) = &method.return_type {
                            tys.push(ret);
                        }
                        reject_item_row_binders(
                            "impl/method",
                            &binders,
                            &[&method.effects],
                            &tys,
                            method.span,
                            diagnostics,
                        );
                    }
                }
                Item::TraitDef(def) => {
                    for method in &def.methods {
                        let mut tys: Vec<&crate::ast::TypeExpr> =
                            method.params.iter().map(|p| &p.ty).collect();
                        if let Some(ret) = &method.return_type {
                            tys.push(ret);
                        }
                        reject_item_row_binders(
                            "trait-method",
                            &method.type_params,
                            &[],
                            &tys,
                            method.span,
                            diagnostics,
                        );
                    }
                }
                _ => {}
            }
        }
    }
}

fn validate_fn_row_params(
    def: &crate::ast::FnDef,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if def.type_params.is_empty() {
        return;
    }
    let row_params = crate::ast::effect_row_param_names(def);

    // T069 hole closure: unknown names in a GENERIC signature's TYPE rows.
    // (Non-generic fns get this from `resolve_type`; generic fns resolve via
    // the pure path and silently dropped typos until this pass.) Declared rows
    // keep their documented silent drop, matching the non-generic asymmetry.
    let mut sig_rows: Vec<&str> = Vec::new();
    for p in &def.params {
        crate::ast::collect_type_row_names(&p.ty, &mut sig_rows);
    }
    if let Some(ret) = &def.return_type {
        crate::ast::collect_type_row_names(ret, &mut sig_rows);
    }
    let mut reported: Vec<&str> = Vec::new();
    for name in &sig_rows {
        if universe.effect_registry.lookup(name).is_none()
            && !row_params.iter().any(|r| r == name)
            && !reported.contains(name)
        {
            reported.push(name);
            let message = format!("unknown effect `{name}` in `Fn` type effect row");
            let diag = match super::closest_name(name, universe.effect_registry.names()) {
                Some(suggestion) => Diagnostic::error_with_hint(
                    codes::T069,
                    message,
                    Some(def.span),
                    format!(
                        "did you mean `{suggestion}`? Otherwise declare the effect with \
                         `effect {name};`, or bind it as a row variable with `<{name}>`"
                    ),
                ),
                None => Diagnostic::error_with_hint(
                    codes::T069,
                    message,
                    Some(def.span),
                    format!(
                        "declare the effect with `effect {name};`, bind it as a row \
                         variable with `<{name}>`, or check the spelling"
                    ),
                ),
            };
            diagnostics.push(diag);
        }
    }

    // T281 for GENERIC signatures (all of them, row-variable or not): a
    // ref/slice of a fn type anywhere in the signature — see
    // `check_ref_of_structural_ty` for why the non-generic gate cannot cover these.
    for p in &def.params {
        check_ref_of_structural_ty(&p.ty, diagnostics);
    }
    if let Some(ret) = &def.return_type {
        check_ref_of_structural_ty(ret, diagnostics);
    }

    if row_params.is_empty() {
        return;
    }

    // Duplicate binder names need no check HERE: N017 rejects duplicate type
    // params during name resolution, which short-circuits before this pass
    // ever runs (pinned by `duplicate_binder_names_are_rejected`).

    for v in &row_params {
        let tp = def
            .type_params
            .iter()
            .find(|p| &p.name == v)
            .expect("row param is a type param by construction");
        // Shadowing a registered effect: kind-by-use cannot distinguish "the
        // variable Alloc" from "the effect Alloc" — the binding walk would
        // hijack the concrete effect's meaning.
        if universe.effect_registry.lookup(v).is_some() {
            diagnostics.push(Diagnostic::error(
                codes::E011,
                format!(
                    "effect-row variable `{v}` shadows the declared effect `{v}` — \
                     rename the type parameter"
                ),
                Some(tp.span),
            ));
        }
        // Higher-kinded / state binders make no sense in a row.
        if !matches!(tp.kind, crate::ast::ParamKind::Star) {
            diagnostics.push(Diagnostic::error(
                codes::E011,
                format!(
                    "`{v}` is declared with a non-`*` kind but used in an effect row — \
                     an effect-row variable must be an ordinary `<{v}>` binder"
                ),
                Some(tp.span),
            ));
        }
        // Both-kinds: used as a type anywhere in the signature.
        let in_type_position = def.params.iter().any(|p| type_position_mentions(&p.ty, v))
            || def
                .return_type
                .as_ref()
                .is_some_and(|ret| type_position_mentions(ret, v));
        if in_type_position {
            diagnostics.push(Diagnostic::error(
                codes::E011,
                format!(
                    "`{v}` is used both as a type and in an effect row — a type \
                     parameter must be one kind or the other"
                ),
                Some(tp.span),
            ));
        }
    }

    // Position restrictions over parameters. Allowed binding position: the
    // TOP-LEVEL row of a BARE Fn-typed parameter (`ref_kind.is_none()` — a
    // `&Fn`/`&[Fn]`-modified node carries `fn_type` on the SAME node but is
    // NOT a callable Fn value, so it cannot bind), with at most one variable.
    // Everything else in a parameter (rows nested inside the Fn's own
    // params/return, rows under refs / slices / generic args / arrays /
    // tuples) is E011.
    for param in &def.params {
        if param.ty.ref_kind.is_none()
            && let Some(ft) = &param.ty.fn_type
        {
            if let Some(names) = &ft.effects {
                let vars_here: Vec<&String> =
                    names.iter().filter(|n| row_params.contains(n)).collect();
                if vars_here.len() > 1 {
                    diagnostics.push(Diagnostic::error(
                        codes::E011,
                        format!(
                            "binding row on parameter `{}` mentions {} effect-row \
                             variables — at most one per binding row (v1 restriction), \
                             so the inferred binding has a unique least solution",
                            param.name,
                            vars_here.len()
                        ),
                        Some(param.span),
                    ));
                }
            }
            let nested = ft
                .params
                .iter()
                .filter_map(|p| first_row_var_mention(p, &row_params))
                .next()
                .or_else(|| first_row_var_mention(&ft.return_type, &row_params));
            if let Some(v) = nested {
                diagnostics.push(Diagnostic::error(
                    codes::E011,
                    format!(
                        "effect-row variable `{v}` may only appear in the top-level row \
                         of a `Fn`-typed parameter, the declared row, or the return type \
                         (v1 restriction) — here it is nested inside the parameter's type"
                    ),
                    Some(param.span),
                ));
            }
        } else if let Some(v) = first_row_var_mention(&param.ty, &row_params) {
            diagnostics.push(Diagnostic::error(
                codes::E011,
                format!(
                    "effect-row variable `{v}` may only appear in the top-level row of a \
                     bare `Fn`-typed parameter, the declared row, or the return type (v1 \
                     restriction) — here it is nested under a reference, slice, or \
                     non-`Fn` parameter type"
                ),
                Some(param.span),
            ));
        }
    }

    // Body annotations cannot mention a row variable (they resolve without
    // substitution — the row would silently become the empty set).
    check_body_annotations(&def.body, &row_params, diagnostics);
}

/// Phase 4 sweep (T281, generic-signature half): a reference or slice of a
/// STRUCTURAL type (fn / tuple / array), at any depth in a GENERIC fn's
/// signature. Non-generic signatures get this from `validate_lowered_type`
/// via `resolve_type`; generic signatures never pass through it (they are
/// stashed as AST and resolved via the pure path at mono time), so without
/// this walk the shape would stay silent exactly like the T069 hole did.
fn check_ref_of_structural_ty(ty: &crate::ast::TypeExpr, diagnostics: &mut Vec<Diagnostic>) {
    // WALKER FENCE (Phase 4 sweep): exhaustive destructure, no `..` — see
    // `ast::collect_type_row_names`.
    let crate::ast::TypeExpr {
        path,
        ref_kind,
        deadline: _,
        span,
        fn_type,
        array_type,
        tuple_type,
    } = ty;
    if ref_kind.is_some() && (fn_type.is_some() || array_type.is_some() || tuple_type.is_some()) {
        diagnostics.push(Diagnostic::error(
            codes::T281,
            "references and slices of function, tuple, or array types are not \
             supported — pass the value directly or store it in a record field"
                .to_string(),
            Some(*span),
        ));
    }
    if let Some(ft) = fn_type {
        for p in &ft.params {
            check_ref_of_structural_ty(p, diagnostics);
        }
        check_ref_of_structural_ty(&ft.return_type, diagnostics);
        return;
    }
    if let Some(arr) = array_type {
        check_ref_of_structural_ty(&arr.elem, diagnostics);
        return;
    }
    if let Some(elems) = tuple_type {
        for e in elems {
            check_ref_of_structural_ty(e, diagnostics);
        }
        return;
    }
    for arg in &path.type_args {
        check_ref_of_structural_ty(arg, diagnostics);
    }
}
