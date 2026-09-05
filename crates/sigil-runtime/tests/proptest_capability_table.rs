//! Pillar 4 — proptest state-machine fuzzer for [`CapabilityTable`].
//!
//! Drives action streams (`InsertFuel(units)`, `Split(idx, amount)`,
//! `Restrict(idx)`, `GetFuelUnits(idx)`) against a fresh
//! `CapabilityTable` and asserts the invariants that the runtime's
//! capability-passing ABI relies on.
//!
//! ## Invariants
//!
//!   1. **insert always extends**: after `insert(cap)`, `len()` grows
//!      by exactly 1, and the returned `CapabilityId` resolves to the
//!      inserted capability.
//!
//!   2. **split conserves fuel**: a successful `split(parent, amount)`
//!      reduces parent's units by exactly `amount` and creates a child
//!      cap with exactly `amount` units. The TOTAL units across all
//!      fuel caps in the table stays unchanged.
//!
//!   3. **insufficient split is non-mutating**: `split(parent, amount)`
//!      with `amount > parent.units` returns `InsufficientFuel` and
//!      leaves parent's units unchanged. `len()` unchanged.
//!
//!   4. **restrict aliases**: `restrict(id)` creates a new cap id with
//!      the SAME units as the source. Parent's units unchanged. Total
//!      units across the table DOUBLES at that source's value (the
//!      compile-time restrict is sound by Z3, runtime aliasing is
//!      just an identity transform per the doc-comment at
//!      `capability.rs:78`).
//!
//!   5. **unknown id is rejected uniformly**: every operation against
//!      a CapabilityId not present in the table returns
//!      `UnknownCapability(id)` and leaves the table unchanged.
//!
//! These properties pin the runtime-side capability ABI's contract.
//! The compile-time Z3 verifier proves "this restrict / split is sound
//! for the program"; the runtime invariants here prove "the table
//! implementation honors the operations the verifier authorized".
//!
//! ## Action stream design
//!
//! Actions reference existing capabilities by **index** into the set
//! of issued ids, not by absolute CapabilityId. The state-machine
//! harness tracks `issued: Vec<CapabilityId>` and indexes into it
//! modulo length — this avoids the "every action targets a freshly-
//! allocated unknown id" failure mode that random `u32` ids would
//! produce on an empty table.

use proptest::prelude::*;
use sigil_runtime::capability::{Capability, CapabilityError, CapabilityTable, FuelCapability};

/// One step in a capability-table action stream.
#[derive(Debug, Clone, Copy)]
enum CapAction {
    InsertFuel(u64),
    /// `(issued_index, amount)` — the index is taken mod len so it
    /// always resolves to a real id when at least one cap exists.
    Split(usize, u64),
    /// `(issued_index)` — same indexing scheme.
    Restrict(usize),
    /// `(issued_index)` — pure read, no mutation.
    GetFuelUnits(usize),
    /// Negative-control: target a CapabilityId guaranteed NOT to be
    /// in the table. The state machine asserts the operation rejects
    /// with `UnknownCapability` and leaves the table unchanged.
    SplitUnknown(u64),
}

fn cap_action_strategy() -> impl Strategy<Value = CapAction> {
    prop_oneof![
        2 => (1u64..=(u64::MAX / 8)).prop_map(CapAction::InsertFuel),
        3 => (any::<usize>(), 0u64..=(u64::MAX / 8)).prop_map(|(i, a)| CapAction::Split(i, a)),
        2 => any::<usize>().prop_map(CapAction::Restrict),
        1 => any::<usize>().prop_map(CapAction::GetFuelUnits),
        1 => (0u64..=(u64::MAX / 8)).prop_map(CapAction::SplitUnknown),
    ]
}

fn action_stream_strategy() -> impl Strategy<Value = Vec<CapAction>> {
    prop::collection::vec(cap_action_strategy(), 1..32)
}

/// Sum the fuel units across every entry in the table. The
/// state-machine asserts this against an oracle running in lockstep.
///
/// Uses u128 to avoid spurious overflow when accumulating large
/// aliased totals (restrict-heavy streams).
fn total_units(
    table: &CapabilityTable,
    issued: &[sigil_runtime::capability::CapabilityId],
) -> u128 {
    issued
        .iter()
        .filter_map(|id| match table.get(*id)? {
            Capability::Fuel(f) => Some(u128::from(f.units())),
        })
        .sum()
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        max_shrink_iters: 1024,
        ..ProptestConfig::default()
    })]

    /// Combined harness: all 5 invariants on the same action stream.
    /// One test rather than five because every invariant depends on
    /// the same lockstep oracle state; splitting them would re-run
    /// the action stream 5× per case.
    #[test]
    fn capability_table_invariants_hold_over_action_streams(
        actions in action_stream_strategy()
    ) {
        let mut table = CapabilityTable::default();
        let mut issued: Vec<sigil_runtime::capability::CapabilityId> = Vec::new();

        for action in &actions {
            let len_before = table.len();
            let total_before = total_units(&table, &issued);

            match action {
                CapAction::InsertFuel(units) => {
                    let id = table.insert(Capability::Fuel(FuelCapability::new(*units)));

                    // Invariant #1: len grows by exactly 1.
                    prop_assert_eq!(
                        table.len(),
                        len_before + 1,
                        "InsertFuel did not grow len by 1; before={}, after={}",
                        len_before,
                        table.len(),
                    );

                    // Invariant #1: returned id resolves to the inserted cap.
                    prop_assert_eq!(
                        table.fuel_units(id).ok(),
                        Some(*units),
                        "InsertFuel: fuel_units(returned id) != units inserted",
                    );

                    issued.push(id);
                }

                CapAction::Split(idx, amount) => {
                    if issued.is_empty() {
                        continue; // No targets yet.
                    }
                    let parent_id = issued[*idx % issued.len()];
                    let parent_units_before = table.fuel_units(parent_id)
                        .expect("issued id must resolve");

                    match table.split(parent_id, *amount) {
                        Ok(child_id) => {
                            // Invariant #2a: parent reduced by exactly amount.
                            prop_assert_eq!(
                                table.fuel_units(parent_id).ok(),
                                Some(parent_units_before - *amount),
                                "Split: parent units != before - amount",
                            );
                            // Invariant #2b: child has exactly amount.
                            prop_assert_eq!(
                                table.fuel_units(child_id).ok(),
                                Some(*amount),
                                "Split: child units != amount",
                            );
                            issued.push(child_id);

                            // Invariant #2c: total units across the table is
                            // CONSERVED (parent loses `amount`, child gains
                            // `amount`).
                            let total_after = total_units(&table, &issued);
                            prop_assert_eq!(
                                total_after,
                                total_before,
                                "Split did not conserve total units; \
                                 before={}, after={}",
                                total_before,
                                total_after,
                            );
                        }
                        Err(CapabilityError::InsufficientFuel { available, requested }) => {
                            // Invariant #3a: must have been over-spend.
                            prop_assert!(
                                requested > available,
                                "InsufficientFuel returned with requested ({}) <= available ({})",
                                requested,
                                available,
                            );
                            // Invariant #3b: parent untouched.
                            prop_assert_eq!(
                                table.fuel_units(parent_id).ok(),
                                Some(parent_units_before),
                                "Failed split mutated parent's units",
                            );
                            // Invariant #3c: len unchanged.
                            prop_assert_eq!(
                                table.len(),
                                len_before,
                                "Failed split changed len",
                            );
                        }
                        Err(other) => {
                            prop_assert!(false, "unexpected error from split: {:?}", other);
                        }
                    }
                }

                CapAction::Restrict(idx) => {
                    if issued.is_empty() {
                        continue;
                    }
                    let parent_id = issued[*idx % issued.len()];
                    let parent_units_before = table.fuel_units(parent_id)
                        .expect("issued id must resolve");

                    let aliased_id = table.restrict(parent_id)
                        .expect("restrict on known id must succeed");

                    // Invariant #4a: parent units unchanged.
                    prop_assert_eq!(
                        table.fuel_units(parent_id).ok(),
                        Some(parent_units_before),
                        "Restrict mutated parent's units",
                    );
                    // Invariant #4b: aliased cap has same units as source.
                    prop_assert_eq!(
                        table.fuel_units(aliased_id).ok(),
                        Some(parent_units_before),
                        "Restrict aliased cap has different units from source",
                    );
                    issued.push(aliased_id);

                    // Invariant #4c: total units increased by parent's value
                    // (aliasing duplicates the entry).
                    let total_after = total_units(&table, &issued);
                    prop_assert_eq!(
                        total_after,
                        total_before + u128::from(parent_units_before),
                        "Restrict did not duplicate parent's units in total",
                    );
                }

                CapAction::GetFuelUnits(idx) => {
                    if issued.is_empty() {
                        continue;
                    }
                    let id = issued[*idx % issued.len()];
                    let units = table.fuel_units(id).expect("issued id must resolve");

                    // Pure read: no mutation.
                    prop_assert_eq!(
                        table.len(),
                        len_before,
                        "fuel_units mutated table len",
                    );
                    prop_assert_eq!(
                        total_units(&table, &issued),
                        total_before,
                        "fuel_units mutated total units",
                    );

                    // Cross-check: the issued id MUST be in the table.
                    prop_assert!(
                        table.get(id).is_some(),
                        "issued id {:?} not in table",
                        id,
                    );
                    // Units consistent with what get() reports.
                    prop_assert_eq!(
                        Some(units),
                        table.get(id).map(|Capability::Fuel(f)| f.units()),
                        "fuel_units and get() disagree on units",
                    );
                }

                CapAction::SplitUnknown(amount) => {
                    // Construct an id guaranteed NOT to be in the table:
                    // u32::MAX - 1. The table allocates from 0 upward, so
                    // unless we've issued ~4 billion caps in one test
                    // (impossible given action-stream cap of 32), this is
                    // safe.
                    let unknown = sigil_runtime::capability::CapabilityId(u32::MAX - 1);
                    let result = table.split(unknown, *amount);

                    // Invariant #5: must return UnknownCapability.
                    prop_assert_eq!(
                        result,
                        Err(CapabilityError::UnknownCapability(unknown)),
                        "SplitUnknown did not return UnknownCapability",
                    );
                    // Table unchanged.
                    prop_assert_eq!(
                        table.len(),
                        len_before,
                        "SplitUnknown changed len",
                    );
                    prop_assert_eq!(
                        total_units(&table, &issued),
                        total_before,
                        "SplitUnknown changed total units",
                    );
                }
            }
        }
    }
}

/// Sanity unit test: confirm the harness actually exercises CapabilityTable.
#[test]
fn sanity_split_then_restrict_preserves_invariants() {
    let mut table = CapabilityTable::default();
    let parent = table.insert(Capability::Fuel(FuelCapability::new(20)));
    let child = table.split(parent, 7).expect("20 > 7");

    assert_eq!(table.fuel_units(parent), Ok(13));
    assert_eq!(table.fuel_units(child), Ok(7));

    let aliased = table.restrict(parent).expect("restrict known");
    assert_eq!(table.fuel_units(aliased), Ok(13));
    assert_eq!(table.fuel_units(parent), Ok(13));
}
