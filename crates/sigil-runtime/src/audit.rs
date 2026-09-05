//! The host audit log -- the bounded record of runtime lifecycle events
//! (module load, spawn, enqueue, delivery, restart) that runtime.rs
//! records and `RuntimeHost::audit_log()` exposes.
//!
//! Owned invariants: retention stays bounded near 2 * `max_len` even under
//! an event flood (availability finding P2 -- a long-lived host must not
//! grow without limit), and `sequence` is monotonic and never reused across
//! evictions, so a truncated tail is detectable through `dropped()` and
//! sequence gaps instead of silently passing for the full history.
//!
//! `record` is infallible: the bound is enforced by amortized batch
//! eviction, never by refusing an event, and the `dropped` counter states
//! the loss. The in-file tests pin the flood bound and cross-eviction
//! monotonicity; `tests/actor_live_restart.rs` reads this log to pin the
//! restart-audited-only-on-success rule (docs/specs/actor-live.md).

use crate::actor::ActorId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AuditEventKind {
    ModuleLoaded {
        module: String,
        wasm_bytes: usize,
        export_count: usize,
    },
    ActorSpawned {
        actor_id: ActorId,
        actor_type: String,
        parent: Option<ActorId>,
    },
    MessageEnqueued {
        sender: Option<ActorId>,
        receiver: ActorId,
        handler: String,
    },
    MessageDelivered {
        sender: Option<ActorId>,
        receiver: ActorId,
        handler: String,
    },
    ActorRestarted {
        actor_id: ActorId,
        restart_count: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuditEvent {
    pub sequence: u64,
    pub kind: AuditEventKind,
}

/// Default upper bound on retained audit events. A long-lived or embedded
/// host records an event per module load / spawn / enqueue / delivery /
/// restart, so an unbounded `Vec` grows without limit for the lifetime of
/// the host (availability finding P2). The log is bounded to the most
/// recent events; older ones are evicted. `sequence` remains monotonic
/// across evictions so consumers can still detect gaps.
pub const DEFAULT_MAX_EVENTS: usize = 100_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuditLog {
    events: Vec<AuditEvent>,
    /// Monotonic sequence counter. Independent of `events.len()` so that
    /// evicting old entries never reuses or rewinds a sequence number.
    next_sequence: u64,
    /// Retention bound. `events.len()` is kept at or below `2 * max_len`
    /// (see `record`); steady-state retention is `max_len`.
    max_len: usize,
    /// Count of events evicted to stay within the bound. Non-zero means
    /// the log is a truncated tail, not the full history.
    dropped: u64,
}

impl Default for AuditLog {
    fn default() -> Self {
        Self {
            events: Vec::new(),
            next_sequence: 0,
            max_len: DEFAULT_MAX_EVENTS,
            dropped: 0,
        }
    }
}

impl AuditLog {
    /// Construct a log with a custom retention bound. A `max_len` of 0 is
    /// clamped to 1.
    pub fn with_max_events(max_len: usize) -> Self {
        Self {
            events: Vec::new(),
            next_sequence: 0,
            max_len: max_len.max(1),
            dropped: 0,
        }
    }

    pub fn record(&mut self, kind: AuditEventKind) -> u64 {
        let sequence = self.next_sequence;
        self.next_sequence += 1;
        self.events.push(AuditEvent { sequence, kind });
        // Amortized-O(1) eviction: let the buffer grow to twice the bound,
        // then drop the oldest half in a single shift. Evicting one entry
        // per record once full would make a flood of events O(n) each —
        // an O(n²) DoS in its own right — so we batch. Memory stays bounded
        // by ~2 * max_len.
        if self.events.len() > self.max_len.saturating_mul(2) {
            let drop_n = self.events.len() - self.max_len;
            self.events.drain(0..drop_n);
            self.dropped += drop_n as u64;
        }
        sequence
    }

    pub fn events(&self) -> &[AuditEvent] {
        &self.events
    }

    pub fn len(&self) -> usize {
        self.events.len()
    }

    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Number of events evicted to stay within the retention bound. `0`
    /// means the log still holds the complete history.
    pub fn dropped(&self) -> u64 {
        self.dropped
    }

    /// Total events ever recorded (retained + evicted). Equals the next
    /// sequence number that will be assigned.
    pub fn total_recorded(&self) -> u64 {
        self.next_sequence
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ev(n: u64) -> AuditEventKind {
        AuditEventKind::ActorRestarted {
            actor_id: ActorId(n),
            restart_count: 0,
        }
    }

    #[test]
    fn sequence_is_monotonic() {
        let mut log = AuditLog::default();
        assert_eq!(log.record(ev(0)), 0);
        assert_eq!(log.record(ev(1)), 1);
        assert_eq!(log.record(ev(2)), 2);
    }

    #[test]
    fn retention_is_bounded_under_a_flood() {
        let mut log = AuditLog::with_max_events(10);
        for i in 0..10_000 {
            log.record(ev(i));
        }
        // Memory is bounded by ~2 * max_len regardless of how many events
        // were recorded — never the full 10_000.
        assert!(
            log.len() <= 20,
            "retained events must stay bounded, got {}",
            log.len()
        );
        assert_eq!(log.total_recorded(), 10_000);
        assert!(log.dropped() > 0, "flood must have evicted old events");
    }

    #[test]
    fn sequence_stays_monotonic_across_evictions() {
        let mut log = AuditLog::with_max_events(4);
        for i in 0..100 {
            log.record(ev(i));
        }
        // Retained tail is strictly increasing and contiguous at the end.
        let seqs: Vec<u64> = log.events().iter().map(|e| e.sequence).collect();
        for w in seqs.windows(2) {
            assert!(w[1] == w[0] + 1, "sequences must be contiguous+monotonic");
        }
        assert_eq!(
            *seqs.last().unwrap(),
            99,
            "newest retained event is the last recorded"
        );
    }

    #[test]
    fn under_the_cap_keeps_everything() {
        let mut log = AuditLog::with_max_events(1000);
        for i in 0..50 {
            log.record(ev(i));
        }
        assert_eq!(log.len(), 50);
        assert_eq!(log.dropped(), 0);
    }
}
