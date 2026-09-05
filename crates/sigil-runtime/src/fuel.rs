//! The per-dispatch fuel ledger (`FuelBudget`). Owned invariant: the balance
//! only moves down, by exact successful `consume` amounts, until `reset`
//! restores the whole grant -- the ACTOR-LIVE AL-1 per-dispatch refill
//! (docs/specs/actor-live.md). Overdraw returns the typed `FuelExhausted`
//! marker and mutates nothing; the runtime's `fuel_decrement` shim lifts it
//! to `RuntimeError::FuelExhausted`. Fuzzed in `tests/proptest_fuel.rs`; the
//! refill contract is pinned by `tests/actor_live_fuel_refill.rs`.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FuelBudget {
    remaining: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FuelExhausted;

impl FuelBudget {
    pub fn new(units: u64) -> Self {
        Self { remaining: units }
    }

    pub fn remaining(&self) -> u64 {
        self.remaining
    }

    pub fn consume(&mut self, amount: u64) -> Result<(), FuelExhausted> {
        if self.remaining < amount {
            return Err(FuelExhausted);
        }

        self.remaining -= amount;
        Ok(())
    }

    /// Restore the budget to `units` — the per-dispatch refill primitive (ACTOR-LIVE AL-1).
    ///
    /// An actor's fuel is a per-DISPATCH grant, not a whole-life budget: the actor runtime's
    /// `Store` is long-lived across handler calls, so a budget set once at construction is consumed
    /// cumulatively and a resident actor dies forever. This mirrors the wasmtime backstop's
    /// per-dispatch `set_fuel` (runtime.rs). It is applied HOST-side at top-level dispatch only.
    pub fn reset(&mut self, units: u64) {
        self.remaining = units;
    }
}

#[cfg(test)]
mod tests {
    use super::{FuelBudget, FuelExhausted};

    #[test]
    fn consumes_within_budget() {
        let mut budget = FuelBudget::new(8);
        assert_eq!(budget.consume(3), Ok(()));
        assert_eq!(budget.remaining(), 5);
    }

    #[test]
    fn rejects_exhaustion() {
        let mut budget = FuelBudget::new(1);
        assert_eq!(budget.consume(2), Err(FuelExhausted));
        assert_eq!(budget.remaining(), 1);
    }

    #[test]
    fn reset_restores_the_grant() {
        // ACTOR-LIVE AL-1: the per-dispatch refill primitive. A partly/fully consumed budget is
        // restored to `units`, so the next dispatch starts fresh.
        let mut budget = FuelBudget::new(8);
        assert_eq!(budget.consume(8), Ok(()));
        assert_eq!(budget.remaining(), 0);
        budget.reset(8);
        assert_eq!(budget.remaining(), 8);
        assert_eq!(budget.consume(5), Ok(()));
    }
}
