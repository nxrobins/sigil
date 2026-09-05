//! Pillar 4 — proptest state-machine fuzzer for [`FuelBudget`].
//!
//! Drives `proptest` action streams (`new(initial)` then a Vec of
//! `consume(amount)` calls) against a stateful invariant model and
//! verifies properties that must hold for ANY action stream:
//!
//!   1. **Monotone**: `remaining()` never INCREASES (only `new()` sets
//!      it; subsequent operations only decrease or no-op).
//!   2. **Exact accounting**: a successful `consume(amount)` reduces
//!      `remaining()` by EXACTLY `amount` — no rounding, no slack.
//!   3. **Exhausted is non-mutating**: a failed `consume(amount)` (when
//!      `amount > remaining()`) leaves `remaining()` unchanged AND
//!      returns `Err(FuelExhausted)`.
//!   4. **No over-spend**: sum of successful consumptions ≤ initial
//!      budget.
//!
//! These invariants are the contract every host-side fuel deduction
//! site (`fuel_decrement` ABI shim, supervisor-on-restart accounting,
//! ephemeral-tool budget tracking) relies on. A regression that breaks
//! any one surfaces as a `proptest` minimization down to the smallest
//! action stream that violates the property — the exact reproducer is
//! attached to the test failure.
//!
//! ## Configuration
//!
//! Default `proptest` config: 256 cases × up to 32 actions each. On
//! seeded reproducer rerun (after a CI failure), the seed file
//! `crates/sigil-runtime/proptest-regressions/proptest_fuel.txt` is
//! auto-loaded by proptest before fresh cases run.

use proptest::prelude::*;
use sigil_runtime::fuel::{FuelBudget, FuelExhausted};

/// One step in a fuel-action stream. Currently only `Consume`; future
/// operations (`refund`, `split`, etc.) extend this enum.
#[derive(Debug, Clone, Copy)]
enum FuelAction {
    Consume(u64),
}

/// proptest strategy for one fuel action. `u64::MAX/4` keeps amounts
/// well clear of overflow when summing across an action stream.
fn fuel_action_strategy() -> impl Strategy<Value = FuelAction> {
    (0u64..=(u64::MAX / 4)).prop_map(FuelAction::Consume)
}

/// proptest strategy for an action stream + the initial budget. Max
/// stream length capped at 32 so each case stays under ~5ms.
fn action_stream_strategy() -> impl Strategy<Value = (u64, Vec<FuelAction>)> {
    (
        0u64..=(u64::MAX / 4),
        prop::collection::vec(fuel_action_strategy(), 0..32),
    )
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        max_shrink_iters: 1024,
        ..ProptestConfig::default()
    })]

    /// Invariant #1: `remaining()` never INCREASES across any action stream.
    ///
    /// Walks the stream, comparing each post-action `remaining()` against
    /// the pre-action snapshot. Asserts monotone-down.
    #[test]
    fn fuel_remaining_is_monotone_non_increasing(
        (initial, actions) in action_stream_strategy()
    ) {
        let mut budget = FuelBudget::new(initial);
        let mut prev = budget.remaining();
        for action in &actions {
            match action {
                FuelAction::Consume(amount) => {
                    let _ = budget.consume(*amount);
                }
            }
            let curr = budget.remaining();
            prop_assert!(
                curr <= prev,
                "remaining() increased: {} -> {} after {:?}",
                prev, curr, action,
            );
            prev = curr;
        }
    }

    /// Invariant #2: successful `consume(amount)` reduces remaining by
    /// exactly `amount`. Failed consume leaves remaining unchanged.
    ///
    /// Combines invariants #2 and #3 — they're symmetric properties of
    /// the same call.
    #[test]
    fn fuel_consume_is_exact_or_no_op(
        (initial, actions) in action_stream_strategy()
    ) {
        let mut budget = FuelBudget::new(initial);
        for action in &actions {
            let FuelAction::Consume(amount) = action;
            let before = budget.remaining();
            match budget.consume(*amount) {
                Ok(()) => {
                    let after = budget.remaining();
                    prop_assert_eq!(
                        after,
                        before - *amount,
                        "successful consume did not reduce remaining by exactly amount; \
                         amount={}, before={}, after={}",
                        amount,
                        before,
                        after,
                    );
                }
                Err(FuelExhausted) => {
                    let after = budget.remaining();
                    prop_assert_eq!(
                        after,
                        before,
                        "failed consume mutated remaining; amount={}, before={}, after={}",
                        amount,
                        before,
                        after,
                    );
                    prop_assert!(
                        *amount > before,
                        "consume returned FuelExhausted but amount <= before; \
                         amount={}, before={}",
                        amount,
                        before,
                    );
                }
            }
        }
    }

    /// Invariant #4: sum of successful consumptions ≤ initial budget.
    ///
    /// The fundamental conservation property. If this is ever violated,
    /// fuel accounting has a fundamental bug.
    #[test]
    fn fuel_total_consumed_never_exceeds_initial(
        (initial, actions) in action_stream_strategy()
    ) {
        let mut budget = FuelBudget::new(initial);
        let mut total_consumed: u128 = 0; // u128 to avoid spurious overflow on the sum itself
        for action in &actions {
            let FuelAction::Consume(amount) = action;
            if budget.consume(*amount).is_ok() {
                total_consumed += u128::from(*amount);
            }
        }
        prop_assert!(
            total_consumed <= u128::from(initial),
            "total consumed {} exceeds initial budget {}",
            total_consumed,
            initial,
        );
        prop_assert_eq!(
            u128::from(initial) - total_consumed,
            u128::from(budget.remaining()),
            "initial - total_consumed should equal remaining"
        );
    }
}

/// Sanity unit test outside the proptest! macro to make sure the
/// invariants actually exercise FuelBudget (vs. silently being satisfied
/// by an empty stream).
#[test]
fn sanity_consume_reduces_remaining() {
    let mut budget = FuelBudget::new(100);
    budget.consume(40).expect("40 ≤ 100");
    assert_eq!(budget.remaining(), 60);
}
