//! The per-actor host ledger -- `ActorId` plus `ActorInstance`, the runtime's
//! record of one resident actor: fuel, owned capabilities, supervision
//! strategy, restart count, and the retained init-argument handles.
//!
//! Two spec obligations live in these fields:
//!
//! * AL-1 (docs/specs/actor-live.md): fuel is a PER-DISPATCH budget.
//!   `refill_fuel` restores `initial_budget` before every top-level dispatch
//!   and never on the re-entrant send/ask path: a synchronous call-tree
//!   shares one finite grant, yet a resident actor does not die forever
//!   from cumulative exhaustion across dispatches.
//!   `actor_live_fuel_refill.rs` pins both directions.
//! * PPS-4 (docs/specs/persistent-pointer-state.md): restart-as-GC.
//!   `init_caps` / `init_fuel_cap` retain the ORDERED spawn-time handles so
//!   a supervised restart replays a replay-safe init with the IDENTICAL
//!   authority the actor already holds -- replay moves nothing.
//!   `pps4_restart_as_gc.rs` and `actor_live_restart.rs` pin the replay.
//!
//! Failure discipline: `consume_fuel` is the only fallible path here and
//! returns the typed `FuelExhausted`; everything else is infallible
//! bookkeeping.

use std::{collections::BTreeSet, fmt};

use crate::{
    capability::CapabilityId,
    fuel::{FuelBudget, FuelExhausted},
    supervisor::SupervisionStrategy,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ActorId(pub u64);

impl ActorId {
    pub fn get(self) -> u64 {
        self.0
    }
}

impl fmt::Display for ActorId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActorInstance {
    actor_type: String,
    fuel: FuelBudget,
    /// The per-dispatch fuel grant, restored before every top-level dispatch (ACTOR-LIVE AL-1).
    /// Fuel is a per-dispatch budget, not a whole-life one; this is the value each dispatch starts
    /// from.
    initial_budget: u64,
    owned_caps: BTreeSet<CapabilityId>,
    supervision: SupervisionStrategy,
    restart_count: u32,
    /// PPS-4 (restart-as-GC): the ORDERED capability-argument vector the actor's
    /// `init` was originally called with, retained at spawn so a supervised
    /// restart can REPLAY a replay-safe init with the identical handles (the
    /// same authority the actor already holds — replay moves nothing). Empty
    /// for a no-arg init or a bootstrap-populated entry actor.
    init_caps: Vec<CapabilityId>,
    /// The fuel capability from the same spawn, completing `build_init_args`'s
    /// input. `None` until a spawn records it.
    init_fuel_cap: Option<CapabilityId>,
}

impl ActorInstance {
    pub fn new(
        actor_type: impl Into<String>,
        fuel_budget: u64,
        supervision: SupervisionStrategy,
    ) -> Self {
        Self {
            actor_type: actor_type.into(),
            fuel: FuelBudget::new(fuel_budget),
            initial_budget: fuel_budget,
            owned_caps: BTreeSet::new(),
            supervision,
            restart_count: 0,
            init_caps: Vec::new(),
            init_fuel_cap: None,
        }
    }

    /// PPS-4: record the init-argument handles at spawn (see `init_caps`).
    pub fn record_init_caps(&mut self, caps: Vec<CapabilityId>, fuel_cap: CapabilityId) {
        self.init_caps = caps;
        self.init_fuel_cap = Some(fuel_cap);
    }

    pub fn init_caps(&self) -> &[CapabilityId] {
        &self.init_caps
    }

    pub fn init_fuel_cap(&self) -> Option<CapabilityId> {
        self.init_fuel_cap
    }

    pub fn actor_type(&self) -> &str {
        &self.actor_type
    }

    pub fn supervision(&self) -> SupervisionStrategy {
        self.supervision
    }

    pub fn own_capability(&mut self, cap: CapabilityId) {
        self.owned_caps.insert(cap);
    }

    pub fn owns_capability(&self, cap: CapabilityId) -> bool {
        self.owned_caps.contains(&cap)
    }

    pub fn release_capability(&mut self, cap: CapabilityId) -> bool {
        self.owned_caps.remove(&cap)
    }

    pub fn restart_count(&self) -> u32 {
        self.restart_count
    }

    pub fn increment_restart_count(&mut self) {
        self.restart_count += 1;
    }

    pub fn consume_fuel(&mut self, amount: u64) -> Result<(), FuelExhausted> {
        self.fuel.consume(amount)
    }

    /// Fuel remaining in the current dispatch's budget (introspection; e.g. the governor's
    /// `fuel_consumed` axis and AL-1 tests).
    pub fn fuel_remaining(&self) -> u64 {
        self.fuel.remaining()
    }

    /// Restore this actor's fuel to its per-dispatch grant (ACTOR-LIVE AL-1). Called HOST-side
    /// before each TOP-LEVEL dispatch (`deliver_message`), never in the re-entrant call path, so a
    /// synchronous send/ask call-tree stays bounded by a single grant — mirroring the wasmtime
    /// backstop's per-dispatch reset. Without it a resident actor exhausts its budget cumulatively
    /// across dispatches and is dead forever.
    pub fn refill_fuel(&mut self) {
        self.fuel.reset(self.initial_budget);
    }
}
