//! sigil-serve — the host-side trigger layer for ephemeral SIGIL tools.
//!
//! SIGIL tools are one-shot: no listener loops, no sleeping, no
//! resident state (see `docs/memory-model.md`). This crate is the other
//! half of that bargain — the HOST owns the long-lived concerns and
//! maps each external stimulus to one `execute_ephemeral` invocation:
//!
//! - **HTTP trigger** (`http`): a request arrives, the routed tool runs
//!   once with the request bytes as input, its packed output becomes
//!   the response body, its negative error codes become HTTP statuses.
//! - **Durable scheduler** (`scheduler`): fixed-interval entries whose
//!   last-run marks persist to disk, so a restarted host resumes the
//!   cadence instead of forgetting it. Overdue entries fire once, not
//!   N times.
//!
//! Tools keep their sandbox: per-tool grants (fail-closed), per-run
//! fuel budgets, 5 MB body caps. Cross-run state belongs in `kv` —
//! which is exactly what makes a stateful service out of stateless
//! runs.

pub mod config;
pub mod cron;
pub mod host;
pub mod http;
pub mod scheduler;
