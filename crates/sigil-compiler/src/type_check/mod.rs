//! The type-check pass orchestrator: wires this directory's submodules
//! (declaration validators, type-universe construction, statement and
//! expression checking, monomorphization tracking) into the public entry
//! points, producing the `TypedProgram` + `AuthorityRegistry` that the
//! downstream security passes and AIR lowering consume.
//!
//! Invariants owned here:
//! * `check_with_warnings` is the type-check severity gate: `Err` ONLY on
//!   a `Severity::Error` diagnostic; warnings ride the success path (today
//!   only the T252 lint from `validators.rs`).
//! * `check_collecting` returns the partial typed program even on failure
//!   so refinement discharge reports alongside structural errors
//!   (`tests/refinement_mixed_error.rs`); the IntLit post-pass and the
//!   residual-`Never` gate (T279, `residual.rs`) run success-only, which
//!   keeps AIR's C-NEVER panic backstops unreachable from user source.
//! * Diagnostic order is semantic emission order: structural stream first,
//!   refinement stream appended, never a global sort -- callers inspect
//!   the first diagnostic.
//! * Function sigs are collected ONCE per module (I16); the always-on
//!   thread-local counter lets `tests/cross_module.rs` assert it.
//!
//! Failure discipline: typed `Diagnostic`s accumulated into a Vec; this
//! file itself emits T060 (with did-you-mean hints), T040, T160/T161
//! (extern effect rows), T263, R006, and I001 for internal malformation.
//! `check_with_options` is the differential oracle named by
//! `docs/specs/type-checker-in-sigil.md` section 2 and exercised by
//! `crates/sigil-runtime/tests/typecheck_differential.rs`.

use std::collections::{HashMap, HashSet};

use crate::{
    ast::{Block, Expr, Item, Pattern, Stmt},
    diagnostics::{Diagnostic, SuggestedEdit, codes},
    name_resolution::ResolvedProgram,
    span::Span,
};

pub use crate::registries::{AuthorityRegistry, EffectRegistry, EffectSet};
pub use crate::typed_ast::*;

// Declaration-time validators.
mod effect_infer;
mod validators;

// Type-universe and actor/function signature construction.
mod universe;
use universe::{
    build_actor_captures, build_actor_env, check_state_field_definite_assignment,
    check_state_field_types, collect_actor_sigs, collect_function_sigs, collect_type_universe,
    param_region_outlives_of, param_regions_of,
};

// Type resolution, substitution, unification, comparison, and rendering.
mod resolve;
use resolve::*;
// Keep the crate-level path consumed by AIR lowering.
pub(crate) use resolve::apply_subst;
// EH4.1: the effect-handler desugar reuses the type-checker's assignability
// predicate for its resume-type-match guard (so `resume 42` for an `-> i64`
// operation is accepted via `int_literal_fits`, matching the rest of the
// compiler), rather than a private re-derivation that could diverge.
pub(crate) use resolve::type_compatible;

// Type-check-time capability expression inference (`restrict`, `split`, and
// `draw`). This module owns shape checks; AIR capability verification owns
// flow soundness.
mod capability_tc;

// Statement checking and block orchestration.
mod statements;
use statements::*;

// Expression inference and its specialized dispatch modules.
mod expressions;
use expressions::*;

// F003 defense-in-depth: the whole-program residual-`Never` gate. Runs at the
// end of `check_with_warnings` on an otherwise error-free program; rejects
// (T279) any value-position `Never` that escaped the site checks, so AIR's
// C-NEVER `panic!` backstops can never fire on user source.
mod residual;

// Refinement declaration validation, narrowing, array intrinsics, and shared
// rendering helpers. Z3-backed discharge lives solely in `type_check_v2`.
mod refinement;
use refinement::*;
// Keep the crate-level helper paths used by the discharge and capability
// modules stable.
pub(crate) use refinement::{
    format_refinement_rhs, refinement_value_for, refinements_match, render_ref_value,
};

// Type-check data structures and scoped state guards.
mod types;
// `crate::type_check::Type` is a public API path.
pub use types::Type;
/// Lookup-only generic bindings shared with AIR field-layout lowering.
pub(crate) type TypeSubstitution = HashMap<String, Type>;
// Internal items are pub(super) in types.rs. Bring them into mod.rs's
// namespace so the existing `super::FunctionSig` / `super::TypeUniverse`
// imports from sibling modules continue to resolve.
use types::*;

// Cross-module function-call resolution.
mod call_resolve;
use call_resolve::*;

// Trait satisfaction and bound enforcement.
mod traits;

/// Compute Levenshtein distance between two strings. Used by T060
/// diagnostics to suggest the closest in-scope name when the user types a
/// likely typo. Small ASCII strings are the common case; this is the
/// straightforward O(m*n) DP. No external crate added.
fn levenshtein_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    if a.is_empty() {
        return b.len();
    }
    if b.is_empty() {
        return a.len();
    }
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut curr = vec![0usize; b.len() + 1];
    for i in 1..=a.len() {
        curr[0] = i;
        for j in 1..=b.len() {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            curr[j] = (curr[j - 1] + 1).min(prev[j] + 1).min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    prev[b.len()]
}

/// Find the closest candidate to `needle` from an iterator of names.
/// Returns `None` when no candidate is close enough (per the bound
/// below) to be a likely typo correction.
///
/// Bound: at most 2 edits for names ≥4 chars, 1 edit for shorter names.
/// Tighter than uncapped Levenshtein — prevents nonsensical suggestions
/// like `x` for `fuel`. Used to produce "did you mean `X`?" hints on
/// undefined-name diagnostics (T060 locals, T064 actors in spawn/dispatch,
/// T065 handlers, T066 types, T067 actors in ActorRef).
pub(super) fn closest_name<'a, I: IntoIterator<Item = &'a str>>(
    needle: &str,
    candidates: I,
) -> Option<&'a str> {
    let max_distance = if needle.len() >= 4 { 2 } else { 1 };
    candidates
        .into_iter()
        .filter(|name| *name != needle)
        .map(|name| (levenshtein_distance(needle, name), name))
        .filter(|(d, _)| *d <= max_distance)
        .min_by_key(|(d, name)| (*d, name.to_string()))
        .map(|(_, name)| name)
}

/// Find the closest in-scope local name (T060). Thin wrapper over
/// `closest_name` that walks a HashMap's keys.
fn closest_in_scope<'a, T>(needle: &str, env: &'a HashMap<String, T>) -> Option<&'a str> {
    closest_name(needle, env.keys().map(String::as_str))
}

/// Build a T060 "undefined local" diagnostic, with a "did you mean ..."
/// hint when an in-scope name is close enough to be a likely typo. The
/// hint is attached via `error_with_hint` only when a match exists;
/// otherwise the registry's default hint applies.
pub(super) fn undefined_local_diagnostic(
    name: &str,
    message: String,
    env: &HashMap<String, Type>,
    span: Span,
) -> Diagnostic {
    if let Some(suggestion) = closest_in_scope(name, env) {
        Diagnostic::error_with_hint(
            codes::T060,
            message,
            Some(span),
            format!("did you mean `{suggestion}`?"),
        )
    } else {
        Diagnostic::error(codes::T060, message, Some(span))
    }
}

/// T060 for a BARE identifier reference, where `span` covers exactly the
/// identifier — so a structured [`SuggestedEdit`] (replace the span with the
/// suggestion) is a safe drop-in. Identical to [`undefined_local_diagnostic`]
/// plus the edit. MUST NOT be used for capability-path sites: their `name` is a
/// normalized `display_name()` and `span` is a cap-path span, so the spanned
/// bytes are not the replaced identifier (see the cap callers of the plain
/// helper). Offsets are re-validated against the rendered source at emission.
pub(super) fn undefined_local_diagnostic_with_edit(
    name: &str,
    message: String,
    env: &HashMap<String, Type>,
    span: Span,
) -> Diagnostic {
    if let Some(suggestion) = closest_in_scope(name, env) {
        Diagnostic::error_with_hint(
            codes::T060,
            message,
            Some(span),
            format!("did you mean `{suggestion}`?"),
        )
        .with_suggested_edits(vec![SuggestedEdit {
            start: span.start,
            end: span.end,
            replacement: suggestion.to_string(),
        }])
    } else {
        Diagnostic::error(codes::T060, message, Some(span))
    }
}

pub fn check(
    program: &ResolvedProgram,
) -> Result<(TypedProgram, AuthorityRegistry), Vec<Diagnostic>> {
    check_with_options(program, &crate::CompileOptions::default())
}

/// Type-check `program`, returning the assembled `TypedProgram` ALONGSIDE
/// diagnostics even when type-checking fails. The IntLit post-pass is NOT
/// run here — it runs success-only in [`check_with_options`] — so on the
/// error path the returned program is the pre-post-pass program. This lets
/// [`check_with_warnings`] collect refinement obligations from a partial,
/// possibly rejected program so structural and refinement errors are reported
/// together (see `tests/refinement_mixed_error.rs`).
///
/// **Visibility:** `pub` because the mixed-error integration test is a
/// separate crate compilation unit. Production callers use
/// [`check_with_options`]; the `_collecting` suffix marks this as the
/// diagnostics-and-partial-program entry point.
pub fn check_collecting(
    program: &ResolvedProgram,
    options: &crate::CompileOptions,
) -> (TypedProgram, AuthorityRegistry, Vec<Diagnostic>) {
    let mut diagnostics = Vec::new();
    let mut modules = Vec::new();
    let mut universe = collect_type_universe(&program.ast);
    // Wall 2 Stage 2: thread the build-time deadline reference into the
    // universe so `validate_lowered_type` can emit T199 when any
    // parametric cap-type literal `Cap(D)` declares `D < BUILD_NOW`.
    universe.build_deadline = options.build_deadline;
    // PR-E4: report cyclic type aliases. They are collected diagnostics-free during
    // the universe build (which has no channel) and excluded from `alias_bodies`, so
    // they resolve to an opaque type rather than expanding — emit T263 here.
    for (name, span) in &universe.cyclic_aliases {
        diagnostics.push(crate::diagnostics::Diagnostic::error(
            crate::diagnostics::codes::T263,
            format!("cyclic type alias `{name}`"),
            Some(*span),
        ));
    }
    let actor_sigs = collect_actor_sigs(&program.ast, &universe, &mut diagnostics);

    validators::validate_entry_actors(&program.ast, &mut diagnostics);
    validators::validate_actor_capability_state(&program.ast, &universe, &mut diagnostics);
    validators::validate_actors_no_typestate_state(&program.ast, &universe, &mut diagnostics);
    validators::validate_no_reserved_type_names(&program.ast, &mut diagnostics);
    validators::validate_field_payload_type_arity(&program.ast, &universe, &mut diagnostics);
    validators::validate_records_no_cap_fields(&program.ast, &universe, &mut diagnostics);
    validators::validate_enums_no_cap_payloads(&program.ast, &universe, &mut diagnostics);
    validators::validate_inner_ring_no_effects(&program.ast, &mut diagnostics);
    validators::validate_cap_type_authority_count(&program.ast, &mut diagnostics);
    // Taint polymorphism: `@Flow` only where the per-instantiation body check
    // actually runs (free non-generic functions).
    validators::validate_flow_polymorphism_scope(&program.ast, &mut diagnostics);
    // Export hygiene: a private `tool_main` would compile to a module with no entry point.
    validators::validate_tool_main_visibility(&program.ast, &mut diagnostics);
    // Phase 4 (row polymorphism): every effect-row-variable shape rule (E011)
    // plus the T069 generic-signature-row hole closure. Runs BEFORE bodies so
    // the generic call path may assume kind-by-use classification is total
    // and disjoint (`ast::effect_row_param_names`).
    validators::validate_effect_row_params(&program.ast, &universe, &mut diagnostics);
    validators::validate_trait_impls(&program.ast, &universe, &mut diagnostics);
    // Mutation-as-capability (PR-4, LD-6): the honesty WARNING for `@ReadOnly`
    // reference/view params (T252, non-blocking). Pure AST pass; emits only
    // `Severity::Warning` diagnostics, which `check_with_warnings`'s errors-only
    // gate lets through to the success path.
    validators::lint_readonly_reference_params(&program.ast, &mut diagnostics);
    // Wall 4 Step 5 commit #2 (A11): declaration-time T217 validation
    // for `LengthOf(field)` refinement-RHS clauses. Without this,
    // records that declare bad refinements but are never constructed
    // would silently pass. The validator runs the resolver in dry-run
    // mode (return value discarded; diagnostics propagated) for every
    // refinement clause of every record.
    validate_refinement_shapes_at_decls(&universe, &mut diagnostics);

    let mut tracker = MonomorphTracker::new();

    // Phase 5a: build the workspace-wide function-sig index and the
    // module-name → ring lookup BEFORE we start checking bodies, so that
    // cross-module call resolution has a complete view.
    //
    // Phase 5a-1.6 (I16 / Op A): single-pass sig collection. We build
    // each module's sigs ONCE here and consult `tracker.workspace_sigs`
    // for both cross-module dispatch and the per-module body checker.
    // The body checker takes a `&std::collections::BTreeMap<String, FunctionSig>` while
    // also taking `&mut tracker`, so we can't directly borrow
    // `tracker.workspace_sigs[name]` — we clone the small per-module
    // map per body-check iteration. The clone is bounded (~10-30 entries
    // per module typically) and *much* cheaper than re-running
    // `collect_function_sigs`, which is the actual O(items × type-resolve)
    // cost we're avoiding.
    for ast_module in &program.ast.modules {
        let module_sigs = collect_function_sigs(ast_module, &universe);
        tracker
            .workspace_sigs
            .insert(ast_module.name.clone(), module_sigs);
        tracker
            .module_rings
            .insert(ast_module.name.clone(), ast_module.ring);
    }

    for resolved_module in &program.modules {
        let Some(ast_module) = program
            .ast
            .modules
            .iter()
            .find(|module| module.name == resolved_module.name)
        else {
            diagnostics.push(Diagnostic::error(
                codes::I001,
                format!(
                    "internal compiler error: unresolved AST module `{}` missing",
                    resolved_module.name
                ),
                Some(resolved_module.span),
            ));
            continue;
        };

        // Set per-module context for cross-module dispatch.
        tracker.current_use_scope = resolved_module.use_scope.clone();
        tracker.current_module_ring = ast_module.ring;

        // R006: `#[trusted]` is only meaningful in the outer ring. The trust
        // privilege unlocks `handle Unsafe` (effect_check.rs E002 path) and
        // FFI extern declarations — both legitimate outer-ring activities.
        // An inner-ring module claiming `#[trusted]` could silently bypass
        // ring discipline (verified by step 21's abuse fixture: a
        // `#[ring(inner)] #[trusted]` module compiled with a `handle Unsafe`
        // block and produced WASM before this check existed).
        if ast_module.trusted && !matches!(ast_module.ring, crate::ast::Ring::Outer) {
            diagnostics.push(Diagnostic::error(
                codes::R006,
                format!(
                    "module `{}` declares `#[trusted]` but is in the inner ring — `#[trusted]` requires `#[ring(outer)]`. Add `#[ring(outer)]` to the module, or drop `#[trusted]` if the module does not need FFI / handle Unsafe.",
                    ast_module.name
                ),
                Some(ast_module.span),
            ));
        }

        // I16: clone from workspace_sigs instead of recomputing. The
        // clone is bounded and cheap; the work we're saving is
        // collect_function_sigs's per-fn type resolution.
        let function_sigs = tracker
            .workspace_sigs
            .get(&ast_module.name)
            .cloned()
            .unwrap_or_default();
        let mut functions = Vec::new();
        let context =
            TypeCheckContext::new(&function_sigs, &actor_sigs, &ast_module.name, &universe);

        for item in &ast_module.items {
            match item {
                Item::FnDef(def) if def.type_params.is_empty() => {
                    let params = def
                        .params
                        .iter()
                        .map(|param| TypedParam {
                            mutability: crate::ast::Mutability::Default,
                            name: param.name.clone(),
                            ty: resolve_type(&param.ty, &universe, &mut diagnostics),
                            taint: param.taint.unwrap_or(crate::ast::TaintLabel::Public),
                            flow: param.flow,
                        })
                        .collect::<Vec<_>>();
                    let ret = def
                        .return_type
                        .as_ref()
                        .map(|ty| resolve_type(ty, &universe, &mut diagnostics))
                        .unwrap_or(Type::Unit);
                    // Resolve effect row from AST annotations
                    let fn_effects = resolve_effect_row(&def.effects, &universe);
                    tracker.current_effects = fn_effects.clone();

                    // Wall 4 Step 7: build param_refinements vec keyed
                    // by param-position to match the FunctionSig shape.
                    let body_param_refinements: Vec<
                        Option<Vec<crate::ast::RefinementClause>>,
                    > = def
                        .params
                        .iter()
                        .map(|param| {
                            let matching: Vec<crate::ast::RefinementClause> = def
                                .param_refinements
                                .iter()
                                .filter(|c| c.field == param.name)
                                .cloned()
                                .collect();
                            if matching.is_empty() {
                                None
                            } else {
                                Some(matching)
                            }
                        })
                        .collect();
                    let body_return_refinement =
                        def.return_refinement.as_ref().map(|c| vec![c.clone()]);
                    let body = check_function_block(
                        &params,
                        &ret,
                        &HashMap::new(),
                        &def.body,
                        context,
                        &mut tracker,
                        &mut diagnostics,
                        &body_param_refinements,
                        body_return_refinement,
                        &def.params.iter().map(|p| p.mutability).collect::<Vec<_>>(),
                        &param_regions_of(&def.params),
                        &param_region_outlives_of(&def.params, &def.region_outlives),
                        // A module function has no actor state in scope.
                        &std::collections::HashMap::new(),
                        &std::collections::HashSet::new(),
                        BodyKind::Free,
                    );

                    functions.push(TypedFunction {
                        name: format!("{}::{}", ast_module.name, def.name),
                        export_name: format!("{}__{}", ast_module.name, def.name),
                        kind: TypedFunctionKind::ModuleFunction,
                        externally_callable: matches!(def.visibility, crate::ast::Visibility::Public),
                        params,
                        captures: Vec::new(),
                        ret,
                        ret_taint: def.ret_taint.unwrap_or(crate::ast::TaintLabel::Public),
                        ret_flow: def.ret_flow,
                        effects: fn_effects,
                        body,
                        span: def.span,
                    });
                }
                Item::ActorDef(def) => {
                    // Actor-state (M2): `actor_env` (state field name → type) is
                    // threaded into every init/handler body as the `state_fields`
                    // map — NOT as `outer_bindings` — so state reads resolve to
                    // `StateField` only after params/locals (natural shadowing) and
                    // `check_assign` gates writes by construction phase.
                    let actor_env = build_actor_env(def, &universe, &mut diagnostics);
                    let actor_captures = build_actor_captures(def, &universe, &mut diagnostics);
                    // Reject a `mut` state field whose type is
                    // not plain reassignable data (cap/ref/borrow/Fn/Ptr → C011). Once
                    // per actor, so it fires exactly once per offending field.
                    check_state_field_types(def, &universe, &mut diagnostics);
                    // Every mutable state field must be assigned exactly once,
                    // unconditionally, in `init` (T124 double / T125 missing).
                    check_state_field_definite_assignment(def, &mut diagnostics);
                    // The `mut`-declared state fields are
                    // the only fields a handler write is permitted to target (F1
                    // guaranteed to be plain reassignable data. Empty for a
                    // mut-free actor.
                    let actor_mut_fields: std::collections::HashSet<String> = def
                        .state_fields
                        .iter()
                        .filter(|f| f.mutability == crate::ast::Mutability::Mut)
                        .map(|f| f.name.clone())
                        .collect();

                    if let Some(init) = &def.init {
                        let params = init
                            .params
                            .iter()
                            .map(|param| TypedParam {
                                flow: false,
                                mutability: crate::ast::Mutability::Default,
                                name: param.name.clone(),
                                ty: resolve_type(&param.ty, &universe, &mut diagnostics),
                                // Honor user-declared taint annotation on
                                // actor init parameters (`init(secret: i64
                                // @SecretCT)`). Defaults to @Public when no
                                // annotation is present.
                                taint: param
                                    .taint
                                    .unwrap_or(crate::ast::TaintLabel::Public),
                            })
                            .collect::<Vec<_>>();
                        // Wall 4 Step 7: actor init blocks don't carry
                        // refinements (anti-goal MC-S7-E for handlers
                        // applies similarly to init blocks).
                        let init_param_refinements: Vec<
                            Option<Vec<crate::ast::RefinementClause>>,
                        > = vec![None; init.params.len()];
                        let body = check_function_block(
                            &params,
                            &Type::Unit,
                            // State fields seed the env (so cap-op/method receivers
                            // and other direct lookups resolve them) AND are passed as
                            // `state_fields` (membership → `StateField`). A binding
                            // cannot shadow a state field (N006 + the shadow guard), so
                            // env membership is unambiguous.
                            &actor_env,
                            &init.body,
                            context,
                            &mut tracker,
                            &mut diagnostics,
                            &init_param_refinements,
                            None, // actor init has no return refinement
                            &init.params.iter().map(|p| p.mutability).collect::<Vec<_>>(),
                            &param_regions_of(&init.params),
                            // Actor `init` blocks take no `where region` clause (not `FnDef`).
                            &[],
                            // Actor-state (M2): `init` is the sole state-write site.
                            &actor_env,
                            // S2 relax: moot in `init` (all writes already allowed),
                            // passed for symmetry with the handler path.
                            &actor_mut_fields,
                            BodyKind::Init,
                        );

                        functions.push(TypedFunction {
                            ret_flow: false,
                            name: format!("{}::{}::init", ast_module.name, def.name),
                            export_name: format!("{}__init", def.name),
                            kind: TypedFunctionKind::ActorInit {
                                actor: def.name.clone(),
                                is_entry: def.is_entry,
                            },
                            externally_callable: true,
                            params,
                            captures: actor_captures.clone(),
                            ret: Type::Unit,
                            ret_taint: crate::ast::TaintLabel::Public,
                            effects: EffectSet::empty(),
                            body,
                            span: init.span,
                        });
                    }

                    for handler in &def.handlers {
                        let params = handler
                            .params
                            .iter()
                            .map(|param| TypedParam {
                                flow: false,
                                mutability: crate::ast::Mutability::Default,
                                name: param.name.clone(),
                                ty: resolve_type(&param.ty, &universe, &mut diagnostics),
                                // Honor user-declared taint annotation on
                                // actor handler parameters (`on Process(s:
                                // i64 @SecretCT)`). Defaults to @Public.
                                taint: param
                                    .taint
                                    .unwrap_or(crate::ast::TaintLabel::Public),
                            })
                            .collect::<Vec<_>>();
                        let ret = handler
                            .return_type
                            .as_ref()
                            .map(|ty| resolve_type(ty, &universe, &mut diagnostics))
                            .unwrap_or(Type::Unit);
                        // Wall 4 Step 7 / MC-S7-E: actor handlers don't
                        // admit refinements (anti-goal). No frame
                        // population.
                        let handler_param_refinements: Vec<
                            Option<Vec<crate::ast::RefinementClause>>,
                        > = vec![None; handler.params.len()];
                        let body = check_function_block(
                            &params,
                            &ret,
                            // State fields seed the env (direct receiver/name lookups)
                            // AND are passed as `state_fields` (membership). No binding
                            // may shadow a state field, so membership is unambiguous.
                            &actor_env,
                            &handler.body,
                            context,
                            &mut tracker,
                            &mut diagnostics,
                            &handler_param_refinements,
                            None, // MC-S7-E: handlers don't admit return refinement
                            &handler.params.iter().map(|p| p.mutability).collect::<Vec<_>>(),
                            &param_regions_of(&handler.params),
                            // Actor handlers take no `where region` clause (not `FnDef`).
                            &[],
                            // Actor-state (M2): a handler reads state (borrow-only). The
                            // entry actor's boot `Start` is the construction-phase carve-out
                            // (M4 allows state-cap consumption there); every other handler is
                            // steady-state.
                            &actor_env,
                            // S2 relax: a handler write to one of these `mut` fields
                            // is permitted; every other state field stays read-only.
                            &actor_mut_fields,
                            if def.is_entry && handler.message_name == "Start" {
                                BodyKind::EntryStart
                            } else {
                                BodyKind::Handler
                            },
                        );

                        functions.push(TypedFunction {
                            ret_flow: false,
                            name: format!(
                                "{}::{}::{}",
                                ast_module.name, def.name, handler.message_name
                            ),
                            export_name: format!("{}__{}", def.name, handler.message_name),
                            kind: TypedFunctionKind::ActorHandler {
                                actor: def.name.clone(),
                                handler: handler.message_name.clone(),
                                is_entry: def.is_entry,
                            },
                            externally_callable: true,
                            params,
                            captures: actor_captures.clone(),
                            ret,
                            ret_taint: crate::ast::TaintLabel::Public,
                            effects: EffectSet::empty(),
                            body,
                            span: handler.span,
                        });
                    }
                }
                Item::ConstDef(def) => {
                    let expected = resolve_type(&def.ty, &universe, &mut diagnostics);
                    let actual = infer_literal_type(&def.value);
                    if !type_compatible(&expected, &actual) {
                        diagnostics.push(Diagnostic::error(
                            codes::T040,
                            format!(
                                "constant `{}` expected type `{}`, found `{}`",
                                def.name,
                                render_type(&expected),
                                render_type(&actual)
                            ),
                            Some(def.span),
                        ));
                    }
                }
                Item::ImplDef(impl_def) => {
                    // PR D: for generic impl blocks, skip the one-shot
                    // typed_ast emission. Dispatch-time monomorphization
                    // in `infer_method_call_expr` produces a concrete
                    // TypedFunction per receiver instantiation, registered
                    // via `tracker.functions.push`. Emitting the original
                    // generic body here would (a) type-check `self.value`
                    // and surface Type::Generic("T") in type_compatible
                    // ICEs at line 9161, and (b) emit a wasm function with
                    // unresolved generics — both fatal.
                    //
                    // Non-generic impl blocks continue to use the one-shot
                    // emission (pre-PR-D path).
                    if !impl_def.type_params.is_empty() {
                        continue;
                    }
                    for method in &impl_def.methods {
                        // HK2 / generic impl methods: a method with its OWN type
                        // parameters (`fn fmap<A, B>`) is monomorphized ON DEMAND
                        // at each call site (registered in `generic_impl_methods`),
                        // NOT emitted one-shot here — a one-shot emission would
                        // carry unresolved `Generic("A")` into AIR and ICE in
                        // `mangle_type`. (A generic impl BLOCK already `continue`d
                        // above; this is the generic-METHOD-on-non-generic-impl
                        // case, e.g. `impl Functor for Box { fn fmap<A, B> … }`.)
                        if !method.type_params.is_empty() {
                            continue;
                        }
                        // SIGIL Complete v0 / Phase 6 supremum path:
                        // methods declare `self` EXPLICITLY in their
                        // source param list. No synthetic self
                        // prepended — `method.params` is the
                        // authoritative param list (which includes the
                        // user's `self: TypeName<...>` declaration).
                        //
                        // PR A inconsistency fix: typed_ast build must
                        // use the SAME generic scope as
                        // `collect_function_sigs` (combined impl-block
                        // + method type_params), otherwise the body's
                        // return-type check sees `Type::Named("T",[])`
                        // (untyped) while the field-access typed-expr
                        // produces `Type::Generic("T")` from the sig.
                        // Pre-PR-A this didn't fire because no real
                        // generic-impl-method body was ever
                        // type-checked end-to-end.
                        let mut combined_generic_scope: Vec<String> =
                            crate::ast::type_param_names(&impl_def.type_params);
                        combined_generic_scope.extend(method.type_params.iter().map(|p| p.name.clone()));
                        let params: Vec<TypedParam> = method
                            .params
                            .iter()
                            .map(|param| TypedParam {
                                flow: false,
                                mutability: crate::ast::Mutability::Default,
                                name: param.name.clone(),
                                ty: resolve_type_expr(
                                    &param.ty,
                                    &universe,
                                    &HashMap::new(),
                                    &combined_generic_scope,
                                ),
                                taint: param.taint.unwrap_or(crate::ast::TaintLabel::Public),
                            })
                            .collect();

                        let ret = method
                            .return_type
                            .as_ref()
                            .map(|ty| {
                                resolve_type_expr(
                                    ty,
                                    &universe,
                                    &HashMap::new(),
                                    &combined_generic_scope,
                                )
                            })
                            .unwrap_or(Type::Unit);
                        // EX-1 (HK3 hardening): impl-method params/return resolve
                        // through the raw, sink-less `resolve_type_expr` (unlike
                        // free fns, which go through the validated `resolve_type`).
                        // Validate them HERE — we have the diagnostics sink — so a
                        // wrong-arity generic record in an impl-method signature
                        // (`fn use_it(self, p: Pair<i64>)`) is a clean T231 at
                        // type-check, not an AIR field-registry ICE.
                        for (typed, src) in params.iter().zip(method.params.iter()) {
                            validate_lowered_type(&typed.ty, &universe, src.ty.span, &mut diagnostics);
                        }
                        if let Some(rt) = &method.return_type {
                            validate_lowered_type(&ret, &universe, rt.span, &mut diagnostics);
                        }
                        // Wall 4 Step 7 / N18-S7: impl methods admit
                        // refinements identically to free fns. Slot 0
                        // is `self`, unrefined; slots 1..=N are the
                        // declared method params.
                        let mut method_param_refinements: Vec<
                            Option<Vec<crate::ast::RefinementClause>>,
                        > = vec![None];
                        for param in &method.params {
                            let matching: Vec<crate::ast::RefinementClause> = method
                                .param_refinements
                                .iter()
                                .filter(|c| c.field == param.name)
                                .cloned()
                                .collect();
                            method_param_refinements.push(if matching.is_empty() {
                                None
                            } else {
                                Some(matching)
                            });
                        }
                        let method_return_refinement =
                            method.return_refinement.as_ref().map(|c| vec![c.clone()]);
                        let body = check_function_block(
                            &params,
                            &ret,
                            &HashMap::new(),
                            &method.body,
                            context,
                            &mut tracker,
                            &mut diagnostics,
                            &method_param_refinements,
                            method_return_refinement,
                            &method.params.iter().map(|p| p.mutability).collect::<Vec<_>>(),
                            &param_regions_of(&method.params),
                            &param_region_outlives_of(&method.params, &method.region_outlives),
                            // An impl method has no actor state in scope.
                            &std::collections::HashMap::new(),
                            &std::collections::HashSet::new(),
                            BodyKind::Free,
                        );

                        let mangled_name = format!(
                            "{}::{}__{}",
                            ast_module.name, impl_def.type_name, method.name
                        );
                        let export_name = format!(
                            "{}__{}__{}",
                            ast_module.name, impl_def.type_name, method.name
                        );

                        functions.push(TypedFunction {
                            ret_flow: false,
                            name: mangled_name,
                            export_name,
                            kind: TypedFunctionKind::ModuleFunction,
                            externally_callable: matches!(
                                method.visibility,
                                crate::ast::Visibility::Public
                            ),
                            params,
                            captures: Vec::new(),
                            ret,
                            ret_taint: crate::ast::TaintLabel::Public,
                            // Propagate the method's DECLARED effect row (the
                            // mono path's PR-0 fix, mirrored). Empty here let
                            // every NON-generic impl-method call escape the
                            // effect requirement: effect_check reads the callee
                            // TypedFunction's row, and empty ⊆ any caller — so
                            // a `! { }` caller of a `! { Danger }` method
                            // compiled clean (E001 launder).
                            effects: resolve_effect_row(&method.effects, &universe),
                            body,
                            span: method.span,
                        });
                    }
                }
                Item::ExternFnDecl(def) => {
                    // Validate extern fns declare both FFI and Unsafe effects
                    if !def.effects.iter().any(|e| e == "FFI") {
                        diagnostics.push(Diagnostic::error(
                            codes::T160,
                            "extern functions must declare FFI effect (! { FFI, Unsafe })",
                            Some(def.span),
                        ));
                    }
                    if !def.effects.iter().any(|e| e == "Unsafe") {
                        diagnostics.push(Diagnostic::error(
                            codes::T161,
                            "extern functions must declare Unsafe effect (! { FFI, Unsafe })",
                            Some(def.span),
                        ));
                    }
                }
                Item::FnDef(_) // generic fns — compiled on-demand during monomorphization
                | Item::UseDecl(_)
                | Item::CapTypeDef(_)
                | Item::RecordDef(_)
                | Item::EnumDef(_)
                | Item::EffectDecl(_)
                | Item::TraitDef(_)
                // Typestate (Epic 1): a `state Name {…}` decl is type-level metadata
                // (collected into universe.typestate_states); it produces no typed
                // item / function and emits no code.
                | Item::StateDef(_)
                // PR-E4: a type alias is substitutive — it lives in universe.alias_bodies
                // and produces no typed item / function.
                | Item::TypeAlias(_) => {} // trait contract already lives in universe.traits
            }
        }

        if functions.is_empty() {
            functions.push(TypedFunction {
                ret_flow: false,
                name: format!("{}::init", ast_module.name),
                export_name: format!("{}__init", ast_module.name),
                kind: TypedFunctionKind::ModuleInit,
                externally_callable: true,
                params: Vec::new(),
                captures: Vec::new(),
                ret: Type::Unit,
                ret_taint: crate::ast::TaintLabel::Public,
                effects: EffectSet::empty(),
                body: TypedBlock {
                    statements: Vec::new(),
                    span: ast_module.span,
                    guaranteed_return: false,
                },
                span: ast_module.span,
            });
        }

        modules.push(TypedModule {
            def_id: resolved_module.def_id,
            name: resolved_module.name.clone(),
            ring: ast_module.ring,
            trusted: ast_module.trusted,
            span: resolved_module.span,
            functions,
        });
    }

    // Drain monomorphized outputs into the module that DEFINED them.
    //
    // Lambda-lifted closures and monomorphized functions carry a module-qualified
    // name (`{module}::__closure_{id}` — see `expressions.rs`), so the definer is
    // recoverable from the name. Routing by it is load-bearing in two independent
    // ways; the previous `modules.first_mut()` broke both by attributing every
    // lifted function to an unrelated module:
    //
    //   1. SECURITY (fail-open). `check_effects` skips `Ring::Inner` modules and
    //      passes `module.trusted` as the E002 authority. With the offending
    //      closure filed under module[0], the ring and trustedness it was checked
    //      under were decided by whichever module happened to sort first — so an
    //      inner-ring module anywhere in the project exempted EVERY lifted closure
    //      in the program from effect checking (verified: the E001 leak vanished).
    //   2. CODEGEN (ICE). The closure's signature is registered in its own
    //      module's type section, so emitting it from a different module hit
    //      `ICE: call_indirect signature not found in type map` in `wasm.rs`.
    //
    // SCOPE: lambda-lifted CLOSURES only. Monomorphized generic instances keep
    // their historical destination — their emission order is pinned by the
    // SH-MONO self-hosting differential (`monomorph_differential.rs`), which the
    // self-hosted shadow must reproduce instance-for-instance, and re-homing them
    // reorders that census for no security benefit. The fail-open demonstrated
    // here is a closure one; narrowing the fix keeps the blast radius to it.
    //
    // Longest-prefix match, because a name may contain further `::` segments
    // (e.g. `app::Type::method$...`) and a plain `rfind` would mis-attribute it.
    // A name matching no module keeps the historical destination rather than
    // being dropped.
    for func in tracker.functions {
        let owner = if func.name.contains("::__closure_") {
            modules
                .iter()
                .enumerate()
                .filter(|(_, md)| func.name.starts_with(&format!("{}::", md.name)))
                .max_by_key(|(_, md)| md.name.len())
                .map(|(idx, _)| idx)
                .unwrap_or(0)
        } else {
            0
        };
        if let Some(module) = modules.get_mut(owner) {
            module.functions.push(func);
        }
    }
    let mut records = universe.records.clone();
    for (mangled, fields) in tracker.records {
        records.insert(mangled, (vec![], fields));
    }
    let mut enums = universe.enums.clone();
    for (mangled, variants) in tracker.enums {
        enums.insert(mangled, (vec![], variants));
    }

    // Assemble the typed program UNCONDITIONALLY so the error path can expose
    // it (NC1). The IntLit post-pass is deliberately NOT run here — it runs
    // success-only in `check_with_options`, so it never touches an
    // errored/partial program and the error-path program stays in exactly the
    // state the in-loop refinement checks observed.
    let program = TypedProgram {
        modules,
        // TypedProgram.records and .enums are BTreeMap (for snapshot
        // determinism per PR 5); the upstream universe + tracker
        // maps stay HashMap (lookup-only, no iteration-order
        // dependency). One-shot `.into_iter().collect()` at the
        // drain site keeps the upstream code untouched.
        records: records.into_iter().collect(),
        enums: enums.into_iter().collect(),
        effect_registry: universe.effect_registry,
        // EH4.3: carry the resolved operation signatures so the effect-handler
        // desugar can thread evidence through the call graph.
        effect_ops: universe
            .effect_ops
            .into_iter()
            .map(|(name, ops)| {
                let sigs = ops
                    .into_iter()
                    .map(|op| crate::typed_ast::EffectOpSig {
                        name: op.name,
                        params: op.params,
                        param_taints: op.param_taints,
                        ret: op.ret,
                    })
                    .collect();
                (name, sigs)
            })
            .collect(),
    };
    (program, universe.authority_registry, diagnostics)
}

/// PIL final post-pass — default any orphan `Type::IntLit` to I64. Per-site
/// walker invocations at check_let etc. handle context-pinned cases; this
/// pass mops up everything else (bare expression statements, top-level
/// no-context literals, …). Runs ONLY after type-check SUCCEEDS, BEFORE AIR
/// lowering (which would ICE on any IntLit via lower_type's `unreachable!()`
/// — N3-PIL). Kept success-only per NC1 so it never runs on the partial
/// program `check_collecting` returns on the error path.
fn run_intlit_post_pass(program: &mut TypedProgram) {
    for module in &mut program.modules {
        for func in &mut module.functions {
            for p in &mut func.params {
                default_int_lit_in_type(&mut p.ty);
            }
            for c in &mut func.captures {
                default_int_lit_in_type(&mut c.ty);
            }
            default_int_lit_in_type(&mut func.ret);
            default_remaining_int_literals_in_block(&mut func.body);
        }
    }
}

/// Type-check `program`, returning the typed program + authority registry on
/// success or the diagnostics on failure. Thin wrapper over
/// [`check_collecting`]: the IntLit post-pass runs success-only here, exactly
/// where it ran before this split, so production behavior is byte-identical.
/// Type-check, surfacing non-blocking WARNINGS alongside the program. Aborts
/// (`Err`) ONLY on a `Severity::Error` diagnostic; on success the third tuple
/// element is the warnings (today only T252, the `@ReadOnly` partial-guarantee
/// lint — SIGIL's first warning). The compile pipeline
/// (`compiler::compile_ast_with_options`) uses this so warnings reach
/// `Compilation`/`CompileResult`. Byte-identical to the old errors-only gate for
/// every program that emits no warnings (`errors == diagnostics` there).
pub fn check_with_warnings(
    program: &ResolvedProgram,
    options: &crate::CompileOptions,
) -> Result<(TypedProgram, AuthorityRegistry, Vec<Diagnostic>), Vec<Diagnostic>> {
    // NB: `check_collecting` returns the TypedProgram (bound to `typed`); the
    // `program: &ResolvedProgram` parameter stays live for the v2 pass below.
    let (mut typed, authority_registry, mut diagnostics) = check_collecting(program, options);
    let has_error = |diags: &[Diagnostic]| {
        diags
            .iter()
            .any(|d| d.severity() == crate::diagnostics::Severity::Error)
    };

    // Run the sole refinement-discharge pipeline over the possibly partial typed
    // program. Running after structural failures preserves mixed-error reporting;
    // `check_collecting` deliberately has not applied the IntLit post-pass yet.
    let discharged =
        crate::type_check_v2::run_obligation_passes(program, &typed, &authority_registry);
    // Append refinement diagnostics after the structural stream. Structural
    // diagnostics use semantic emission order rather than span order, and callers
    // may inspect the first diagnostic. The refinement walk is deterministic, so
    // concatenation preserves both contracts without a global sort.
    diagnostics.extend(discharged.diagnostics);

    if !has_error(&diagnostics) {
        run_intlit_post_pass(&mut typed);
        // F003 defense-in-depth: the residual-`Never` gate (see residual.rs).
        // Runs ONLY on an otherwise error-free program — exactly the inputs
        // that would proceed to AIR — and rejects (T279) any value-position
        // `Never` that escaped the site checks, so the C-NEVER `panic!`
        // backstops in `mangle_type`/`lower_type` can never fire on user
        // source. Appends nothing on a clean program (byte-identical
        // diagnostics for every previously-passing input).
        residual::scan_residual_never(&typed, &mut diagnostics);
    }
    if has_error(&diagnostics) {
        // Errors abort, carrying the full list (errors + any warnings) exactly as
        // the pre-warning gate did — identical for every error-free-of-warnings input.
        Err(diagnostics)
    } else {
        // No errors ⇒ every remaining diagnostic is a warning.
        Ok((typed, authority_registry, diagnostics))
    }
}

/// Back-compat 2-tuple wrapper over [`check_with_warnings`]: drops the warnings.
/// Kept for the callers (and tests) that only need the typed program + registry.
/// The gate is now errors-only, but since these callers never produce warnings
/// today, the Ok/Err split is unchanged from the historical `is_empty()` gate.
pub fn check_with_options(
    program: &ResolvedProgram,
    options: &crate::CompileOptions,
) -> Result<(TypedProgram, AuthorityRegistry), Vec<Diagnostic>> {
    check_with_warnings(program, options).map(|(program, registry, _warnings)| (program, registry))
}

/// Resolve an AST effect row (Option<Vec<String>>) into an EffectSet.
/// None → empty (inner ring, no annotation). Some([]) → pure. Some(["Alloc"]) → {Alloc}.
fn resolve_effect_row(effects: &Option<Vec<String>>, universe: &TypeUniverse) -> EffectSet {
    match effects {
        None => EffectSet::empty(),
        Some(names) => {
            let mut set = EffectSet::empty();
            for name in names {
                if let Some(id) = universe.effect_registry.lookup(name) {
                    set.effects.insert(id);
                }
            }
            set
        }
    }
}

/// Row-aware variant of [`resolve_effect_row`] (Phase 4, row polymorphism): a
/// name that is a bound row VARIABLE contributes its binding's effects; every
/// other name resolves (or silently drops) exactly as before. Used by the
/// generic-fn mono path to instantiate a declared row like `! { Alloc, e }`.
fn resolve_effect_row_with_vars(
    effects: &Option<Vec<String>>,
    universe: &TypeUniverse,
    row_bindings: &HashMap<String, EffectSet>,
) -> EffectSet {
    let mut set = resolve_effect_row(effects, universe);
    if let Some(names) = effects {
        for name in names {
            if let Some(b) = row_bindings.get(name) {
                set.effects.extend(b.effects.iter().copied());
            }
        }
    }
    set
}

// I16 instrumentation: count `collect_function_sigs` invocations per
// `check()` call so a test can assert single-pass discipline. Always-on
// (not `#[cfg(test)]`) so integration tests in `tests/` can read the
// counter; the thread-local read+write per call is a single uncontended
// cell access, negligible in production.
thread_local! {
    pub static COLLECT_FUNCTION_SIGS_CALL_COUNT: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

/// Reset the I16 single-pass counter. Use at the start of a test that
/// asserts collection happens exactly N times.
pub fn reset_collect_function_sigs_counter() {
    COLLECT_FUNCTION_SIGS_CALL_COUNT.with(|c| c.set(0));
}

/// Read the I16 single-pass counter.
pub fn collect_function_sigs_call_count() -> usize {
    COLLECT_FUNCTION_SIGS_CALL_COUNT.with(std::cell::Cell::get)
}

// --- Closure capture analysis: recursive free variable detection ---

pub(super) fn find_free_vars(block: &Block, bound_init: &HashSet<String>) -> HashSet<String> {
    let mut free = HashSet::new();
    let mut bound = bound_init.clone();

    for stmt in &block.statements {
        match stmt {
            Stmt::Let(s) => {
                free.extend(find_free_vars_in_expr(&s.value, &bound));
                bound.insert(s.name.clone());
            }
            Stmt::LetTuple(s) => {
                free.extend(find_free_vars_in_expr(&s.value, &bound));
                for (name, _) in &s.bindings {
                    bound.insert(name.clone());
                }
            }
            Stmt::Assign(s) => {
                // NC5: the place's variables (base local + any index
                // sub-expressions) are USES — a write to an outer local still
                // captures it, and an index expr reads its variables. Walking
                // the place expr preserves the capture semantics that held
                // when `target` was a bare local string.
                free.extend(find_free_vars_in_expr(&s.target, &bound));
                free.extend(find_free_vars_in_expr(&s.value, &bound));
            }
            Stmt::Expr(s) => free.extend(find_free_vars_in_expr(&s.expr, &bound)),
            Stmt::If(s) => {
                free.extend(find_free_vars_in_expr(&s.condition, &bound));
                free.extend(find_free_vars(&s.then_branch, &bound));
                free.extend(find_free_vars(&s.else_branch, &bound));
            }
            Stmt::While(s) => {
                free.extend(find_free_vars_in_expr(&s.condition, &bound));
                free.extend(find_free_vars(&s.body, &bound));
            }
            Stmt::ForIn(s) => {
                free.extend(find_free_vars_in_expr(&s.iterable, &bound));
                let mut body_bound = bound.clone();
                body_bound.insert(s.var.clone());
                free.extend(find_free_vars(&s.body, &body_bound));
            }
            Stmt::ForRange(s) => {
                // Bounds are evaluated OUTSIDE the loop var's scope; the var
                // binds over the body only (closure-capture correctness).
                free.extend(find_free_vars_in_expr(&s.start, &bound));
                free.extend(find_free_vars_in_expr(&s.end, &bound));
                let mut body_bound = bound.clone();
                body_bound.insert(s.var.clone());
                free.extend(find_free_vars(&s.body, &body_bound));
            }
            Stmt::Match(s) => {
                free.extend(find_free_vars_in_expr(&s.scrutinee, &bound));
                for arm in &s.arms {
                    let mut arm_bound = bound.clone();
                    match &arm.pattern {
                        Pattern::Binding(b) => {
                            arm_bound.insert(b.name.clone());
                        }
                        Pattern::EnumVariant(v) => {
                            for b in &v.bindings {
                                if b != "_" {
                                    arm_bound.insert(b.clone());
                                }
                            }
                        }
                        _ => {}
                    }
                    if let Some(g) = &arm.guard {
                        free.extend(find_free_vars_in_expr(g, &arm_bound));
                    }
                    free.extend(find_free_vars(&arm.body, &arm_bound));
                }
            }
            Stmt::Return(s) => {
                if let Some(v) = &s.value {
                    free.extend(find_free_vars_in_expr(v, &bound));
                }
            }
            Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }
    free
}

#[allow(clippy::collapsible_if)]
fn find_free_vars_in_expr(expr: &Expr, bound: &HashSet<String>) -> HashSet<String> {
    let mut free = HashSet::new();
    match expr {
        Expr::Path(p) => {
            if let Some(root) = p.path.segments.first() {
                if !bound.contains(root) {
                    free.insert(root.clone());
                }
            }
        }
        Expr::Call(c) => {
            if let Some(root) = c.callee.segments.first() {
                if !bound.contains(root) {
                    free.insert(root.clone());
                }
            }
            for arg in &c.args {
                free.extend(find_free_vars_in_expr(arg, bound));
            }
        }
        Expr::Binary(b) => {
            free.extend(find_free_vars_in_expr(&b.lhs, bound));
            free.extend(find_free_vars_in_expr(&b.rhs, bound));
        }
        Expr::Closure(c) => {
            let mut inner_bound = bound.clone();
            for p in &c.params {
                inner_bound.insert(p.name.clone());
            }
            free.extend(find_free_vars(&c.body, &inner_bound));
        }
        Expr::FieldAccess(f) => free.extend(find_free_vars_in_expr(&f.object, bound)),
        // Capabilities-as-values: `mint <Cap> for <target>` — the target is the
        // only sub-expression (the minting authority is referenced by name as a
        // normal Path elsewhere in the body).
        Expr::Mint(m) => free.extend(find_free_vars_in_expr(&m.target, bound)),
        Expr::Index(i) => {
            free.extend(find_free_vars_in_expr(&i.array, bound));
            free.extend(find_free_vars_in_expr(&i.index, bound));
        }
        Expr::Slice(s) => {
            free.extend(find_free_vars_in_expr(&s.array, bound));
            if let Some(start) = &s.start {
                free.extend(find_free_vars_in_expr(start, bound));
            }
            if let Some(end) = &s.end {
                free.extend(find_free_vars_in_expr(end, bound));
            }
        }
        Expr::ArrayLit(a) => {
            for e in &a.elements {
                free.extend(find_free_vars_in_expr(e, bound));
            }
        }
        Expr::Tuple(t) => {
            for e in &t.elements {
                free.extend(find_free_vars_in_expr(e, bound));
            }
        }
        Expr::Try(t) => free.extend(find_free_vars_in_expr(&t.value, bound)),
        Expr::ResultCtor(r) => free.extend(find_free_vars_in_expr(&r.value, bound)),
        Expr::RecordConstruct(r) => {
            for (_, e) in &r.fields {
                free.extend(find_free_vars_in_expr(e, bound));
            }
        }
        Expr::EnumConstruct(e) => {
            for f in &e.fields {
                free.extend(find_free_vars_in_expr(f, bound));
            }
        }
        Expr::MethodCall(m) => {
            free.extend(find_free_vars_in_expr(&m.receiver, bound));
            for a in &m.args {
                free.extend(find_free_vars_in_expr(a, bound));
            }
        }
        Expr::Send(s) => {
            if let Some(root) = s.target.segments.first() {
                if !bound.contains(root) {
                    free.insert(root.clone());
                }
            }
            free.extend(find_free_vars_in_expr(&s.message, bound));
        }
        Expr::Ask(a) => {
            if let Some(root) = a.target.segments.first() {
                if !bound.contains(root) {
                    free.insert(root.clone());
                }
            }
            free.extend(find_free_vars_in_expr(&a.message, bound));
            free.extend(find_free_vars_in_expr(&a.timeout, bound));
        }
        Expr::Spawn(s) => {
            for a in &s.args {
                free.extend(find_free_vars_in_expr(a, bound));
            }
        }
        Expr::CapRestrict(c) => {
            if let Some(root) = c.cap.segments.first() {
                if !bound.contains(root) {
                    free.insert(root.clone());
                }
            }
        }
        Expr::CapRestrictDeadline(c) => {
            if let Some(root) = c.cap.segments.first() {
                if !bound.contains(root) {
                    free.insert(root.clone());
                }
            }
        }
        Expr::CapSplit(c) => {
            if let Some(root) = c.cap.segments.first() {
                if !bound.contains(root) {
                    free.insert(root.clone());
                }
            }
        }
        Expr::CapDraw(c) => {
            if let Some(root) = c.cap.segments.first() {
                if !bound.contains(root) {
                    free.insert(root.clone());
                }
            }
        }
        Expr::Borrow(b) => free.extend(find_free_vars_in_expr(&b.inner, bound)),
        Expr::Grant(g) => {
            free.extend(find_free_vars_in_expr(&g.cap, bound));
            free.extend(find_free_vars_in_expr(&g.body, bound));
        }
        Expr::Handle(h) => {
            free.extend(find_free_vars(&h.body, bound));
        }
        // Effect Handlers (EH0): walk the new nodes' sub-expressions so closure
        // free-var analysis stays sound over them (C-VIS).
        Expr::Perform(p) => {
            for arg in &p.args {
                free.extend(find_free_vars_in_expr(arg, bound));
            }
        }
        Expr::ClauseHandle(c) => {
            free.extend(find_free_vars_in_expr(&c.scrutinee, bound));
            for clause in &c.clauses {
                free.extend(find_free_vars(&clause.body, bound));
            }
        }
        Expr::Resume(r) => {
            free.extend(find_free_vars_in_expr(&r.value, bound));
        }
        Expr::Declassify(d) => {
            free.extend(find_free_vars_in_expr(&d.value, bound));
            free.extend(find_free_vars_in_expr(&d.cap, bound));
        }
        Expr::DeclassifyCt(d) => {
            free.extend(find_free_vars_in_expr(&d.value, bound));
            free.extend(find_free_vars_in_expr(&d.cap, bound));
        }
        Expr::Region(r) => {
            free.extend(find_free_vars_in_expr(&r.limit, bound));
            free.extend(find_free_vars(&r.body, bound));
        }
        // PR-E3: an f-string's free vars are those of its interpolation holes
        // (literal chunks bind nothing).
        Expr::FString(f) => {
            for part in &f.parts {
                if let crate::ast::FStringPart::Hole(e) = part {
                    free.extend(find_free_vars_in_expr(e, bound));
                }
            }
        }
        Expr::Literal(_) => {}
    }
    free
}

// Unit-test modules.
// (step10_narrowing_helpers_tests, step2_refinement_tests,
// pr_a_record_subst_tests) moved to a sibling `tests.rs`. They retain
// access to mod.rs's private items because Rust allows descendant
// modules to see their ancestors' private items — no pub(super)
// cascade was needed.
#[cfg(test)]
mod tests;
