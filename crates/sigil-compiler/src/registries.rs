//! Shared registry types for capability authority, effects, and effect sets.
//!
//! These are constructed during type checking and consumed by multiple
//! verification passes (effect_check, capability, z3_capability).

use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Maps cap type names to their declared authority names with bit indices.
#[derive(Debug, Default)]
pub struct AuthorityRegistry {
    entries: HashMap<String, Vec<(String, u32)>>,
}

impl AuthorityRegistry {
    pub fn register(&mut self, cap_type: &str, authorities: &[String]) {
        let entries = authorities
            .iter()
            .enumerate()
            .map(|(i, name)| (name.clone(), i as u32))
            .collect();
        self.entries.insert(cap_type.to_owned(), entries);
    }

    /// Full authority mask: all bits set for the cap type's authority count.
    ///
    /// Shifts are guarded with `checked_shl`: a cap type declaring >32
    /// authorities is rejected by `validate_cap_type_authority_count`
    /// (T185), but a bit index >= 32 can still reach this method during
    /// expression type-checking before that diagnostic is delivered.
    /// In debug builds `1 << 32` panics (shift-overflow check); folding
    /// the out-of-range bit to 0 keeps the mask harmless and lets T185
    /// deliver its clean diagnostic instead of an ICE.
    pub fn full_mask(&self, cap_type: &str) -> u32 {
        self.entries
            .get(cap_type)
            .map(|e| {
                e.iter().fold(0u32, |acc, (_, bit)| {
                    acc | 1u32.checked_shl(*bit).unwrap_or(0)
                })
            })
            .unwrap_or(0)
    }

    /// Convert an authority mask back to the set of declared authority
    /// names, sorted by bit position. Used by C003 diagnostics to tell the
    /// policy author *which* authorities are present vs. missing — instead
    /// of just "restricted" vs. "full". Returns an empty vec when the cap
    /// type is unknown OR no bits are set (both are caller's problem to
    /// distinguish; the empty case is well-defined and harmless to print).
    pub fn authority_names(&self, cap_type: &str, mask: u32) -> Vec<String> {
        self.entries
            .get(cap_type)
            .map(|entries| {
                let mut named: Vec<(u32, String)> = entries
                    .iter()
                    .filter(|(_, bit)| mask & 1u32.checked_shl(*bit).unwrap_or(0) != 0)
                    .map(|(name, bit)| (*bit, name.clone()))
                    .collect();
                named.sort_by_key(|(bit, _)| *bit);
                named.into_iter().map(|(_, name)| name).collect()
            })
            .unwrap_or_default()
    }

    /// Resolve a restriction name to a single-bit mask.
    pub fn restriction_mask(&self, cap_type: &str, restriction: &str) -> Result<u32, String> {
        let entries = self
            .entries
            .get(cap_type)
            .ok_or_else(|| format!("unknown cap type `{cap_type}`"))?;
        entries
            .iter()
            .find(|(n, _)| n == restriction)
            // Guarded like `full_mask`: a restriction at bit index >= 32
            // (only reachable on a cap type that T185 rejects) folds to 0
            // rather than panicking on `1 << 32` in debug builds.
            .map(|(_, bit)| 1u32.checked_shl(*bit).unwrap_or(0))
            .ok_or_else(|| {
                let valid: Vec<&str> = entries.iter().map(|(n, _)| n.as_str()).collect();
                format!(
                    "unknown restriction `{restriction}` for cap type `{cap_type}`. Valid: {valid:?}"
                )
            })
    }
}

/// Registry of declared effects (marker effects for security tracking).
///
/// `effects` uses BTreeMap rather than HashMap so the field's Debug
/// output is deterministic across runs. Snapshot tests
/// (`snap_typecheck.rs`, `workload_snapshots.rs`) include TypedProgram
/// transitively, which embeds an EffectRegistry per N1-W5S1 — without
/// sorted iteration the snapshots would diff across runs even when
/// the type-check is byte-identical. Lookup complexity is O(log n)
/// vs HashMap's O(1), but the effects map maxes out at ~10 entries
/// per program in practice; log of 10 is dominated by hash overhead.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct EffectRegistry {
    effects: BTreeMap<String, u32>,
    next_id: u32,
}

impl EffectRegistry {
    pub fn register(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.effects.get(name) {
            return id;
        }
        let id = self.next_id;
        self.effects.insert(name.to_owned(), id);
        self.next_id += 1;
        id
    }

    /// Registered effect names, sorted (BTreeMap order) — the candidate list for
    /// "did you mean" hints on unknown-effect diagnostics (T069).
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.effects.keys().map(String::as_str)
    }

    pub fn lookup(&self, name: &str) -> Option<u32> {
        self.effects.get(name).copied()
    }

    pub fn name_of(&self, id: u32) -> Option<&str> {
        self.effects
            .iter()
            .find(|(_, v)| **v == id)
            .map(|(k, _)| k.as_str())
    }
}

/// Concrete set of effect IDs — used for subset/union/difference operations.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct EffectSet {
    pub effects: BTreeSet<u32>,
}

impl EffectSet {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn is_subset_of(&self, other: &Self) -> bool {
        self.effects.is_subset(&other.effects)
    }
}
