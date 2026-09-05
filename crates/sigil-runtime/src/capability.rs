//! The runtime capability table -- the per-host store of fuel-capability
//! state behind `CapabilityId`, the "runtime capability tables" leg of
//! SND-CAP-001 enforcement (docs/SOUNDNESS_MATRIX.md).
//!
//! Owned invariants: ids come from a monotonic counter and are never
//! reused; `split` conserves total fuel units (the parent loses exactly
//! what the child gains) and refuses without mutating; `restrict` and
//! `mint` only allocate fresh ids over an aliased or zero-fuel payload --
//! non-fuel authority is proven at compile time by the Z3 capability
//! layer, so the runtime tracks fuel units and opaque identity, never
//! authority.
//!
//! Every fallible operation returns a typed `CapabilityError`; runtime.rs
//! lifts it into `RuntimeError` and the cap ABI shims surface it to the
//! guest as a trap. The invariants above are fuzzed as a proptest state
//! machine in `tests/proptest_capability_table.rs`.

use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CapabilityId(pub u32);

/// Runtime view of a capability. Today the runtime only ever stores
/// Fuel caps — non-fuel cap types (AliceAuth, custom user caps, etc.)
/// are type-system-only: the compiler proves their flow at compile time
/// and the runtime treats them all as opaque references via CapabilityId.
/// A previous `Capability::Opaque` variant existed for hypothetical
/// runtime-side opaque-cap state but was never constructed; removed in
/// step 18 of the supremum loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Capability {
    Fuel(FuelCapability),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FuelCapability {
    units: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CapabilityError {
    UnknownCapability(CapabilityId),
    NotFuel(CapabilityId),
    InsufficientFuel { available: u64, requested: u64 },
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CapabilityTable {
    caps: BTreeMap<CapabilityId, Capability>,
    next_id: u32,
}

impl FuelCapability {
    pub fn new(units: u64) -> Self {
        Self { units }
    }

    pub fn units(&self) -> u64 {
        self.units
    }
}

impl CapabilityTable {
    pub fn len(&self) -> usize {
        self.caps.len()
    }

    pub fn is_empty(&self) -> bool {
        self.caps.is_empty()
    }

    pub fn insert(&mut self, capability: Capability) -> CapabilityId {
        let id = CapabilityId(self.next_id);
        self.next_id += 1;
        self.caps.insert(id, capability);
        id
    }

    pub fn get(&self, id: CapabilityId) -> Option<&Capability> {
        self.caps.get(&id)
    }

    pub fn fuel_units(&self, id: CapabilityId) -> Result<u64, CapabilityError> {
        let Some(capability) = self.caps.get(&id) else {
            return Err(CapabilityError::UnknownCapability(id));
        };

        let Capability::Fuel(fuel) = capability;

        Ok(fuel.units())
    }

    /// Insert a fresh capability id aliasing the same Fuel value. The
    /// compile-time `.restrict(authority_set)` operation is enforced by
    /// the Z3 capability layer at proof time; at runtime, restriction is
    /// just an identity transform that produces a new id so the linear
    /// move semantics still track the new value separately. The
    /// `restriction_id` that the WASM ABI passes is informational only
    /// and is ignored here — Z3 has already verified the restriction is
    /// sound before the WASM ever runs.
    pub fn restrict(&mut self, id: CapabilityId) -> Result<CapabilityId, CapabilityError> {
        let Some(capability) = self.caps.get(&id) else {
            return Err(CapabilityError::UnknownCapability(id));
        };
        let Capability::Fuel(fuel) = capability;
        let aliased = Capability::Fuel(*fuel);
        Ok(self.insert(aliased))
    }

    /// Capabilities-as-values: allocate a fresh capability id for a `mint`.
    /// Non-fuel caps are opaque at runtime (authority is proven at compile
    /// time), so the minted cap carries a zero-fuel placeholder payload; its
    /// identity (the fresh id) is the only thing the runtime tracks. `restrict`
    /// and `split` alias this payload, preserving linear-move identity.
    pub fn mint(&mut self) -> CapabilityId {
        self.insert(Capability::Fuel(FuelCapability::new(0)))
    }

    pub fn split(
        &mut self,
        id: CapabilityId,
        amount: u64,
    ) -> Result<CapabilityId, CapabilityError> {
        let Some(capability) = self.caps.get_mut(&id) else {
            return Err(CapabilityError::UnknownCapability(id));
        };

        let Capability::Fuel(parent) = capability;

        if parent.units < amount {
            return Err(CapabilityError::InsufficientFuel {
                available: parent.units,
                requested: amount,
            });
        }

        parent.units -= amount;
        Ok(self.insert(Capability::Fuel(FuelCapability::new(amount))))
    }
}

#[cfg(test)]
mod tests {
    use super::{Capability, CapabilityError, CapabilityTable, FuelCapability};

    #[test]
    fn splits_fuel_caps() {
        let mut table = CapabilityTable::default();
        let parent = table.insert(Capability::Fuel(FuelCapability::new(12)));

        let child = table.split(parent, 5).expect("fuel should split");

        assert_eq!(
            table.get(parent),
            Some(&Capability::Fuel(FuelCapability::new(7)))
        );
        assert_eq!(
            table.get(child),
            Some(&Capability::Fuel(FuelCapability::new(5)))
        );
    }

    #[test]
    fn rejects_oversized_fuel_splits() {
        let mut table = CapabilityTable::default();
        let parent = table.insert(Capability::Fuel(FuelCapability::new(3)));

        assert_eq!(
            table.split(parent, 4),
            Err(CapabilityError::InsufficientFuel {
                available: 3,
                requested: 4,
            })
        );
    }

    #[test]
    fn reports_fuel_units_for_fuel_caps() {
        let mut table = CapabilityTable::default();
        let fuel = table.insert(Capability::Fuel(FuelCapability::new(9)));

        assert_eq!(table.fuel_units(fuel), Ok(9));
    }

    #[test]
    fn mint_allocates_a_fresh_registered_capability() {
        // Capabilities-as-values: `mint` allocates a fresh, distinct cap id that
        // is present in the table (so a later `restrict`/`split` on a minted cap
        // resolves), with no precondition on an existing cap.
        let mut table = CapabilityTable::default();
        let a = table.mint();
        let b = table.mint();

        assert_ne!(a, b, "each mint yields a distinct capability id");
        assert!(table.get(a).is_some(), "minted cap is registered");
        assert!(table.get(b).is_some(), "minted cap is registered");
        // A minted cap aliases like any other under restrict (no ownership panic).
        let restricted = table.restrict(a).expect("minted cap can be restricted");
        assert_ne!(restricted, a);
    }
}
