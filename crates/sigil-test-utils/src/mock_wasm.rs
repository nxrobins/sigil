//! Mock WASM host-import recorder — Pillar 4 scaffolding.
//!
//! Records every host-import call (the ABI shims `fuel_decrement`,
//! `send`, `ask`, `spawn`, `cap_split`, `cap_restrict`, etc.) without
//! compiling or running real WASM. Lets a `proptest` action-stream
//! fuzzer drive the host-side state machine through scripted import
//! call sequences, then introspect the recorded sequence to assert
//! invariants like "every `cap_split` had a paired `cap_restrict` or
//! `cap_drop`".
//!
//! ## Scope in PR 4
//!
//! PR 4 ships the **recorder shell** and a fluent builder for canned
//! responses. Concrete fuzzers in `sigil-runtime/tests/proptest_*.rs`
//! drive `FuelBudget` and `CapabilityTable` directly (state-machine
//! fuzzers don't need a mock WASM layer — the targets are pure data
//! structures). When the runtime's actor-loop / message-dispatch
//! coverage grows in a future PR, that fuzzer will drive
//! `MockWasmInstance::call_import_*(...)` and assert against
//! `recorded_calls()`.
//!
//! Keeping the recorder here today rather than deferring further
//! means consumers (and future me) have a stable type to wire into
//! when the runtime fuzzer arrives — no Cargo.toml churn, no
//! scaffolding-vs-content debate on the next PR.

use std::collections::VecDeque;

/// One recorded host-import call. The variant tag identifies the
/// shim; the fields carry the call's argument(s) in the order the
/// ABI defines.
///
/// Add a new variant per ABI shim as the runtime fuzzer needs it.
/// The default-empty queue + `recorded_calls()` API is stable; the
/// enum may grow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MockCall {
    /// `fuel_decrement(amount)` — host charges fuel for a WASM op.
    FuelDecrement(u64),
    /// `cap_split(parent_id, amount)` — host returns a fresh
    /// CapabilityId in the canned response queue.
    CapSplit { parent_id: u32, amount: u64 },
    /// `cap_restrict(parent_id, authority_set)` — host returns a
    /// fresh CapabilityId (alias).
    CapRestrict { parent_id: u32, authority_set: u64 },
    /// `send(actor_ref, message_bytes)` — fire-and-forget mailbox.
    Send { actor_ref: u32, message_len: usize },
    /// `ask(actor_ref, message_bytes)` — request-response.
    Ask { actor_ref: u32, message_len: usize },
    /// `spawn(actor_type_id, init_args_len)` — create a new actor.
    Spawn {
        actor_type_id: u32,
        init_args_len: usize,
    },
}

/// A response the mock returns when the WASM guest calls a host
/// import. Pre-queued via [`MockWasmInstance::push_response`].
///
/// If the queue is empty, the mock falls back to a per-variant
/// sensible default (`Ok(0)` for ids; `Ok(())` for fuel) so the
/// guest can run without blocking on missing setup.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MockResponse {
    /// Numeric return (CapabilityId, fuel-remaining-after, etc.).
    Ok(u64),
    /// Fuel exhaustion / cap-error trap.
    Trap,
}

/// In-memory WASM-guest simulator. **Not a real WASM engine.** A
/// proptest fuzzer calls `call_import_*` in whatever order a guest
/// WASM body would generate them, the recorder logs each call, and
/// the canned response queue serves the return value.
///
/// Use from `proptest` harnesses:
///
/// ```rust,ignore
/// use sigil_test_utils::mock_wasm::{MockWasmInstance, MockResponse};
///
/// let mut mock = MockWasmInstance::new();
/// mock.push_response(MockResponse::Ok(42)); // cap_split returns id 42
///
/// mock.call_import_fuel_decrement(10);
/// mock.call_import_cap_split(0, 5);
///
/// let calls = mock.recorded_calls();
/// assert_eq!(calls.len(), 2);
/// ```
#[derive(Debug, Default)]
pub struct MockWasmInstance {
    recorded: Vec<MockCall>,
    response_queue: VecDeque<MockResponse>,
}

impl MockWasmInstance {
    pub fn new() -> Self {
        Self::default()
    }

    /// Pre-queue a response. Responses are consumed in FIFO order by
    /// import calls that need a return value. If the queue runs dry,
    /// imports fall back to `MockResponse::Ok(0)`.
    pub fn push_response(&mut self, response: MockResponse) {
        self.response_queue.push_back(response);
    }

    /// All recorded import calls in chronological order. The slice
    /// stays stable until the next `clear_recording()`.
    pub fn recorded_calls(&self) -> &[MockCall] {
        &self.recorded
    }

    /// Reset the recording (but NOT the response queue). Useful when
    /// a proptest case wants per-phase assertions on call sequences.
    pub fn clear_recording(&mut self) {
        self.recorded.clear();
    }

    fn pop_response(&mut self) -> MockResponse {
        self.response_queue
            .pop_front()
            .unwrap_or(MockResponse::Ok(0))
    }

    // ── Per-import shims ──────────────────────────────────────────────────
    //
    // Each `call_import_*` records the call and returns the next
    // queued response. The runtime fuzzer scripts these in whatever
    // order a guest WASM body would generate, then asserts against
    // `recorded_calls()`.

    pub fn call_import_fuel_decrement(&mut self, amount: u64) -> MockResponse {
        self.recorded.push(MockCall::FuelDecrement(amount));
        self.pop_response()
    }

    pub fn call_import_cap_split(&mut self, parent_id: u32, amount: u64) -> MockResponse {
        self.recorded.push(MockCall::CapSplit { parent_id, amount });
        self.pop_response()
    }

    pub fn call_import_cap_restrict(&mut self, parent_id: u32, authority_set: u64) -> MockResponse {
        self.recorded.push(MockCall::CapRestrict {
            parent_id,
            authority_set,
        });
        self.pop_response()
    }

    pub fn call_import_send(&mut self, actor_ref: u32, message_len: usize) -> MockResponse {
        self.recorded.push(MockCall::Send {
            actor_ref,
            message_len,
        });
        self.pop_response()
    }

    pub fn call_import_ask(&mut self, actor_ref: u32, message_len: usize) -> MockResponse {
        self.recorded.push(MockCall::Ask {
            actor_ref,
            message_len,
        });
        self.pop_response()
    }

    pub fn call_import_spawn(&mut self, actor_type_id: u32, init_args_len: usize) -> MockResponse {
        self.recorded.push(MockCall::Spawn {
            actor_type_id,
            init_args_len,
        });
        self.pop_response()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn records_calls_in_order() {
        let mut mock = MockWasmInstance::new();
        mock.call_import_fuel_decrement(10);
        mock.call_import_send(1, 4);
        mock.call_import_fuel_decrement(2);
        assert_eq!(
            mock.recorded_calls(),
            &[
                MockCall::FuelDecrement(10),
                MockCall::Send {
                    actor_ref: 1,
                    message_len: 4
                },
                MockCall::FuelDecrement(2),
            ]
        );
    }

    #[test]
    fn serves_queued_responses_fifo() {
        let mut mock = MockWasmInstance::new();
        mock.push_response(MockResponse::Ok(42));
        mock.push_response(MockResponse::Trap);

        assert_eq!(mock.call_import_cap_split(0, 5), MockResponse::Ok(42));
        assert_eq!(mock.call_import_cap_split(0, 5), MockResponse::Trap);
        assert_eq!(
            mock.call_import_cap_split(0, 5),
            MockResponse::Ok(0),
            "fallback to Ok(0) when queue is empty"
        );
    }

    #[test]
    fn clear_recording_drops_history_but_keeps_responses() {
        let mut mock = MockWasmInstance::new();
        mock.push_response(MockResponse::Ok(99));
        // Push a second response BEFORE recording any calls, so the
        // queue has something left after the first import consumes
        // one entry.
        mock.push_response(MockResponse::Ok(123));

        mock.call_import_fuel_decrement(1); // consumes Ok(99)
        assert_eq!(mock.recorded_calls().len(), 1);

        mock.clear_recording();
        assert!(mock.recorded_calls().is_empty());

        // Response queue preserved — next import gets the queued 123,
        // not the Ok(0) fallback.
        assert_eq!(mock.call_import_fuel_decrement(2), MockResponse::Ok(123));
    }
}
