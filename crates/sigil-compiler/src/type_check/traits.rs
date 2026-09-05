//! Trait satisfaction + bound enforcement (the trait Wall).
//!
//! `type_satisfies_trait` is the SINGLE resolution predicate — CM-T2's "one
//! resolution path": given a concrete type and a trait name, is there an impl?
//! Impls come from two sources, resolved uniformly:
//!
//!   1. **Built-in** (PR-3b, CM-T7) — a closed table for the primitives `i64` /
//!      `str` / `bool` × `Hash` / `Eq` (exactly 6 entries).
//!   2. **Structural** (PR-4, heuristic 5) — a user `record` satisfies a trait
//!      iff it declares the trait's method(s) with an EXACTLY matching signature
//!      (CM-T1); no `impl Trait for Type` line required. Reuses the ordinary
//!      method-resolution machinery (`resolve_impl_member_global`).
//!
//! Explicit `impl Trait for Type` + the orphan rule are PR-5. `check_bounds`
//! runs the predicate at a generic instantiation site (CM-T5), concrete
//! type-args in hand, BEFORE the body is monomorphized — a clean diagnostic at
//! the call span (CM-T1 / T4).
//!
//! Under SIGIL's EAGER monomorphization the predicate sees concrete types here;
//! the `Type::Generic` / `Type::Error` arm is a defensive conservative-allow.

use std::collections::{BTreeMap, HashMap};

use super::resolve::apply_subst;
use super::{FunctionSig, MonomorphTracker, TraitContract, Type, TypeUniverse, render_type};
use crate::ast::TypeParam;
use crate::diagnostics::{Diagnostic, codes};
use crate::span::Span;
use crate::type_check::call_resolve::{GlobalImplVerdict, resolve_impl_member_global};

/// The result of asking "does `T` satisfy trait `Tr`?".
pub(super) enum Satisfaction {
    Ok,
    /// No impl: a primitive outside the built-in table, or a record missing a
    /// required method. `missing_method` names the absent method for records;
    /// `None` when the whole type has no impl (a primitive). → T245.
    NoImpl {
        missing_method: Option<String>,
    },
    /// A method with the trait's name exists, but its signature does not match
    /// the trait's (after `Self` substitution). → T246.
    SignatureMismatch {
        method: String,
    },
    /// The bound names a trait that was never declared / imported. → T248.
    UnknownTrait,
    /// HK2 (EX-2): a constructor bound to a higher-kinded-trait-bounded type
    /// parameter has the wrong arity for the trait's `Self` kind slot (e.g. a
    /// 2-param `Map` for a `* -> *` `Functor`). → T270.
    ConstructorArity {
        ctor: String,
        expected: usize,
        found: usize,
    },
}

/// CM-T7: the closed built-in impl table — exactly `{i64, str, bool} × {Hash,
/// Eq}` = 6 entries. There is no 7th primitive entry. This IS the impl lookup
/// for primitives; the resolver never branches on "is this a primitive?"
/// anywhere else.
fn is_builtin_impl(concrete: &Type, trait_name: &str) -> bool {
    matches!(concrete, Type::I64 | Type::Str | Type::Bool) && matches!(trait_name, "Hash" | "Eq")
}

/// CM-T1: an EXACT signature match — equal arity, and every parameter type and
/// the return type equal (by `Type` equality, after the caller has substituted
/// `Self`). Not "compatible"; equal. `self` is parameter 0 and is compared like
/// any other.
fn signature_matches(found: &FunctionSig, expected_params: &[Type], expected_ret: &Type) -> bool {
    found.params.len() == expected_params.len()
        && found
            .params
            .iter()
            .zip(expected_params)
            .all(|(a, b)| a == b)
        && &found.ret == expected_ret
}

/// Structural tier (PR-4): a `Type::Named` satisfies the trait iff it provides
/// every required method with a matching signature. Method lookup is the same
/// `function_sigs` → `resolve_impl_member_global` path the method-call dispatcher
/// uses (local module wins; a sibling module is the fallback; ambiguity is
/// treated as not-found here — coherence is PR-5's concern).
fn structural_satisfies(
    type_name: &str,
    concrete: &Type,
    contract: &TraitContract,
    function_sigs: &BTreeMap<String, FunctionSig>,
    current_module: &str,
    tracker: &MonomorphTracker,
) -> Satisfaction {
    // `Self` → the implementing type in the expected signatures.
    let mut subst = HashMap::new();
    subst.insert("Self".to_string(), concrete.clone());

    for (method, (expected_params, expected_ret)) in &contract.methods {
        let key = format!("{type_name}::{method}");
        let found: Option<FunctionSig> = match function_sigs.get(&key) {
            Some(s) => Some(s.clone()),
            None => match resolve_impl_member_global(&key, current_module, tracker) {
                GlobalImplVerdict::Found(s) => Some(s),
                GlobalImplVerdict::Ambiguous(_) | GlobalImplVerdict::None => None,
            },
        };
        let Some(sig) = found else {
            return Satisfaction::NoImpl {
                missing_method: Some(method.clone()),
            };
        };
        let exp_params: Vec<Type> = expected_params
            .iter()
            .map(|t| apply_subst(t, &subst))
            .collect();
        let exp_ret = apply_subst(expected_ret, &subst);
        if !signature_matches(&sig, &exp_params, &exp_ret) {
            return Satisfaction::SignatureMismatch {
                method: method.clone(),
            };
        }
    }
    Satisfaction::Ok
}

/// HK2: does a bare CONSTRUCTOR — the `TypeCtor("Box")` binding of a
/// higher-kinded type parameter `F` — satisfy a trait? Only a HIGHER-KINDED trait
/// (one whose `Self` is used applied, so `contract.hkt_param` is `Some`) can be
/// satisfied this way. The check is the EX-2 arity gate: the constructor's
/// declared arity must equal the trait's `Self` kind-arity. Per-method SIGNATURE
/// conformance is enforced where the method is actually called in the
/// monomorphized body — the receiver is concrete (`Box<i64>`) there and the
/// ordinary method-dispatch path type-checks the call (HK2 recon: mono-time
/// dispatch already validates conformance).
fn constructor_satisfies(
    ctor: &str,
    contract: &TraitContract,
    universe: &TypeUniverse,
) -> Satisfaction {
    let Some((_, self_arity)) = &contract.hkt_param else {
        // An ordinary (non-higher-kinded) trait cannot be satisfied by a bare
        // constructor — its methods take `Self` as a value, not `Self<…>`.
        return Satisfaction::NoImpl {
            missing_method: None,
        };
    };
    let ctor_arity = universe
        .records
        .get(ctor)
        .map(|(tp, _)| tp.len())
        .or_else(|| universe.enums.get(ctor).map(|(tp, _)| tp.len()));
    match ctor_arity {
        Some(n) if n == *self_arity => Satisfaction::Ok,
        Some(found) => Satisfaction::ConstructorArity {
            ctor: ctor.to_string(),
            expected: *self_arity,
            found,
        },
        None => Satisfaction::NoImpl {
            missing_method: None,
        },
    }
}

/// The single satisfaction predicate (built-in table → structural → conservative
/// allow for not-yet-concrete / errored types).
pub(super) fn type_satisfies_trait(
    concrete: &Type,
    trait_name: &str,
    universe: &TypeUniverse,
    function_sigs: &BTreeMap<String, FunctionSig>,
    current_module: &str,
    tracker: &MonomorphTracker,
) -> Satisfaction {
    let Some(contract) = universe.traits.get(trait_name) else {
        return Satisfaction::UnknownTrait;
    };
    if is_builtin_impl(concrete, trait_name) {
        return Satisfaction::Ok;
    }
    match concrete {
        // INV-2: a still-symbolic generic / higher-kinded var is conservatively
        // allowed — it erases to a concrete type/ctor before the bound is
        // meaningfully checked. Without the `HktVar` arm, an HKT-bounded param
        // would falsely fire T245.
        Type::Generic(_) | Type::Error | Type::HktVar { .. } => Satisfaction::Ok,
        Type::Named(name, _) => structural_satisfies(
            name,
            concrete,
            contract,
            function_sigs,
            current_module,
            tracker,
        ),
        // HK2: the binding target of a higher-kinded param `F |-> TypeCtor("Box")`.
        Type::TypeCtor(ctor) => constructor_satisfies(ctor, contract, universe),
        _ => Satisfaction::NoImpl {
            missing_method: None,
        },
    }
}

/// CM-T5: the shared bound-check helper. Called at a generic instantiation site
/// with the AST type-params (which carry the bounds) zipped against the resolved
/// concrete type-args. Emits T245 / T246 / T248 at `span`.
#[allow(clippy::too_many_arguments)]
pub(super) fn check_bounds(
    type_params: &[TypeParam],
    concrete_args: &[Type],
    span: Span,
    universe: &TypeUniverse,
    function_sigs: &BTreeMap<String, FunctionSig>,
    current_module: &str,
    tracker: &MonomorphTracker,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for (param, concrete) in type_params.iter().zip(concrete_args.iter()) {
        for bound in &param.bounds {
            match type_satisfies_trait(
                concrete,
                bound,
                universe,
                function_sigs,
                current_module,
                tracker,
            ) {
                Satisfaction::Ok => {}
                Satisfaction::UnknownTrait => {
                    diagnostics.push(Diagnostic::error(
                        codes::T248,
                        format!(
                            "type parameter `{}` is bound by `{bound}`, but no trait named `{bound}` is in scope — declare it (`trait {bound} {{ … }}`) or import the module that does",
                            param.name
                        ),
                        Some(span),
                    ));
                }
                Satisfaction::NoImpl { missing_method } => {
                    let detail = match &missing_method {
                        Some(m) => format!(": missing method `{m}`"),
                        None => String::new(),
                    };
                    diagnostics.push(Diagnostic::error(
                        codes::T245,
                        format!(
                            "type `{}` does not satisfy trait `{bound}`{detail}",
                            render_type(concrete)
                        ),
                        Some(span),
                    ));
                }
                Satisfaction::SignatureMismatch { method } => {
                    diagnostics.push(Diagnostic::error(
                        codes::T246,
                        format!(
                            "type `{}` has a method `{method}` but its signature does not match what trait `{bound}` requires",
                            render_type(concrete)
                        ),
                        Some(span),
                    ));
                }
                Satisfaction::ConstructorArity {
                    ctor,
                    expected,
                    found,
                } => {
                    diagnostics.push(Diagnostic::error(
                        codes::T270,
                        format!(
                            "constructor `{ctor}` has arity {found}, but trait `{bound}` is higher-kinded with a `Self` of arity {expected} — bind a constructor of arity {expected}"
                        ),
                        Some(span),
                    ));
                }
            }
        }
    }
}
