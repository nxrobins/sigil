//! `SupervisionStrategy` -- the spawn-time restart-policy vocabulary: `Stop`
//! (the fail-closed member, and the derived default) or
//! `Restart { max_restarts }` (docs/specs/actor-live.md, Supervision). The
//! gate enforcing "no restart without spawn opt-in" lives in runtime.rs;
//! `actor_live_restart.rs` pins its reachability.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SupervisionStrategy {
    #[default]
    Stop,
    Restart {
        max_restarts: u32,
    },
}
