//! Cross-module function call resolution, extracted from `mod.rs` in
//! structural extraction PR 13.
//!
//! Three resolvers walk a parsed `crate::ast::Path` callee through the
//! workspace's function signature index, producing a
//! `CrossModuleResolution` verdict that the caller emits as a typed
//! call, a diagnostic, or both:
//!
//!   * `resolve_function_call_with_context` — entry point. Dispatches
//!     to one of the two resolvers below based on segment count.
//!   * `resolve_single_segment_in_use_scope` — for `foo(args)`-shape
//!     callees, walks the current module's `use` aliases looking for
//!     a `pub fn` in any `use`'d module. Emits Ambiguous when two
//!     candidates exist (N008).
//!   * `cross_module_lookup` — for `module::foo(args)`-shape callees,
//!     does a direct workspace_sigs lookup with private+cross-ring
//!     gating (T155 / R004).
//!
//! All four enum variants of `CrossModuleResolution` carry the
//! diagnostic context needed to produce the right error at the
//! call site — Private/CrossRing/Ambiguous attach module/name/
//! candidate info; Found wraps the resolved FunctionSig by
//! reference so the caller threads it directly into the call
//! checker without re-lookup.
//!
//! Pure data + lookup. No Z3 calls, no I/O, no global state.

use super::{FunctionSig, MonomorphTracker};

/// Result of a cross-module function call resolution.
///
/// Distinguishes "found and callable" from "found but private", "found
/// but cross-ring", and "ambiguous across multiple `use`'d modules".
/// Each non-Ok variant carries diagnostic context so the caller can emit
/// a precise message.
pub(super) enum CrossModuleResolution<'a> {
    Found(&'a FunctionSig),
    Private {
        module: String,
        name: String,
    },
    CrossRing {
        module: String,
        name: String,
        callee_ring: crate::ast::Ring,
    },
    /// N008: a single-segment fn name resolves to `pub fn` in 2+ `use`'d
    /// modules. Caller emits N008 with the candidate list.
    Ambiguous {
        name: String,
        candidates: Vec<String>, // module names where the symbol is pub
    },
}

/// PR C2 / CF-C1: verdict for a global (cross-module) impl-member lookup
/// `Type::name`, used when the current module has no local definition. OWNS the
/// resolved `FunctionSig` (the scan's `&MonomorphTracker` borrow must end before
/// the caller takes `&mut tracker` for monomorphization).
///
/// `Found` carries a `FunctionSig` (grown by PR-2b's `param_mutability`). This is
/// a TRANSIENT verdict — returned and matched immediately, never stored in bulk —
/// so the `large_enum_variant` size delta is irrelevant, and boxing would ripple
/// to all four match sites for no benefit.
#[allow(clippy::large_enum_variant)]
pub(super) enum GlobalImplVerdict {
    /// Exactly one sibling module defines `Type::name`.
    Found(FunctionSig),
    /// Two or more sibling modules define it — caller emits T244 with the list.
    Ambiguous(Vec<String>),
    /// No sibling module defines it.
    None,
}

/// PR C2 / CF-C1: resolve an impl member `Type::method` across sibling modules.
///
/// Scans every module OTHER than `current_module` in sorted `workspace_sigs`
/// order (deterministic) for the `"Type::method"` key, honoring the same-ring
/// rule (R004) like `cross_module_lookup`. The current module is never scanned
/// here — the caller consults it first, so a local impl always wins. Returns a
/// hard `Ambiguous` when ≥2 sibling modules define the key (never
/// first-match-wins). Impl methods register `Public` unconditionally, so there
/// is no T155 visibility gate to apply.
pub(super) fn resolve_impl_member_global(
    key: &str,
    current_module: &str,
    tracker: &MonomorphTracker,
) -> GlobalImplVerdict {
    let mut hits: Vec<FunctionSig> = tracker
        .workspace_sigs
        .iter()
        .filter(|(module, _)| module.as_str() != current_module)
        // R004: only siblings in the same ring are reachable; an unregistered
        // module defaults to reachable (matches `cross_module_lookup`).
        .filter(|(module, _)| {
            tracker
                .module_rings
                .get(module.as_str())
                .copied()
                .is_none_or(|ring| ring == tracker.current_module_ring)
        })
        .filter_map(|(_, sigs)| sigs.get(key).cloned())
        .collect();
    match hits.len() {
        0 => GlobalImplVerdict::None,
        1 => GlobalImplVerdict::Found(hits.pop().expect("len == 1")),
        _ => GlobalImplVerdict::Ambiguous(hits.iter().map(|s| s.module.clone()).collect()),
    }
}

pub(super) fn resolve_function_call_with_context<'a, 'b>(
    callee: &crate::ast::Path,
    module_name: &str,
    function_sigs: &'a std::collections::BTreeMap<String, FunctionSig>,
    tracker: &'b MonomorphTracker,
) -> Option<CrossModuleResolution<'a>>
where
    'b: 'a,
{
    match callee.segments.as_slice() {
        // Single-segment: same-module first; fall back to `use`'d modules
        // on no-match. Multiple matches across use'd modules → N008.
        [name] => {
            if let Some(sig) = function_sigs.get(name) {
                Some(CrossModuleResolution::Found(sig))
            } else {
                resolve_single_segment_in_use_scope(name, tracker)
            }
        }
        // Two-segment: self-ref (existing behavior) OR `use`-imported
        // alias (new) OR fully-qualified `<crate>::<module>` (treated as
        // module-only since we have one crate today; resolver below
        // handles three-segment paths with a leading `sigil::`).
        [module, name] if module == module_name => {
            function_sigs.get(name).map(CrossModuleResolution::Found)
        }
        [module, name] => {
            // Try use-scope first.
            if tracker.current_use_scope.lookup(module).is_some()
                || tracker.workspace_sigs.contains_key(module.as_str())
            {
                cross_module_lookup(module, name, tracker)
            } else {
                None
            }
        }
        // Three-segment: `<crate>::<module>::<fn>`. We accept any crate
        // name for forward compatibility, but today there's only one.
        [_crate, module, name] => cross_module_lookup(module, name, tracker),
        _ => None,
    }
}

/// Resolve a single-segment fn name across `use`'d modules. If exactly
/// one use'd module exposes a `pub fn` of this name, return Found. If
/// multiple expose it, return Ambiguous (N008). Zero matches → None
/// (caller falls through to the existing T062 / generic-fn path).
fn resolve_single_segment_in_use_scope<'a, 'b>(
    name: &str,
    tracker: &'b MonomorphTracker,
) -> Option<CrossModuleResolution<'a>>
where
    'b: 'a,
{
    let mut candidates: Vec<(&str, &FunctionSig)> = Vec::new();
    for target_module in tracker.current_use_scope.aliases.values() {
        if let Some(target_sigs) = tracker.workspace_sigs.get(target_module.as_str())
            && let Some(sig) = target_sigs.get(name)
            && matches!(sig.visibility, crate::ast::Visibility::Public)
        {
            candidates.push((target_module.as_str(), sig));
        }
    }
    match candidates.len() {
        0 => None,
        1 => {
            let (module, sig) = candidates[0];
            // Honor cross-ring rejection here too — a use'd module in a
            // different ring is not silently callable just because the
            // name happened to match.
            if let Some(callee_ring) = tracker.module_rings.get(module).copied()
                && callee_ring != tracker.current_module_ring
            {
                return Some(CrossModuleResolution::CrossRing {
                    module: module.to_owned(),
                    name: name.to_owned(),
                    callee_ring,
                });
            }
            Some(CrossModuleResolution::Found(sig))
        }
        _ => {
            let mut module_names: Vec<String> =
                candidates.iter().map(|(m, _)| (*m).to_owned()).collect();
            module_names.sort();
            Some(CrossModuleResolution::Ambiguous {
                name: name.to_owned(),
                candidates: module_names,
            })
        }
    }
}

fn cross_module_lookup<'a, 'b>(
    module: &str,
    name: &str,
    tracker: &'b MonomorphTracker,
) -> Option<CrossModuleResolution<'a>>
where
    'b: 'a,
{
    let target_sigs = tracker.workspace_sigs.get(module)?;
    let sig = target_sigs.get(name)?;

    // Visibility check (T155).
    if matches!(sig.visibility, crate::ast::Visibility::Private) {
        return Some(CrossModuleResolution::Private {
            module: module.to_owned(),
            name: name.to_owned(),
        });
    }

    // Cross-ring check (R004): caller and callee must be in the same ring.
    // Tools using FFI-backed stdlib must declare `#[ring(outer)] #[trusted]`.
    if let Some(callee_ring) = tracker.module_rings.get(module).copied()
        && callee_ring != tracker.current_module_ring
    {
        return Some(CrossModuleResolution::CrossRing {
            module: module.to_owned(),
            name: name.to_owned(),
            callee_ring,
        });
    }

    Some(CrossModuleResolution::Found(sig))
}
