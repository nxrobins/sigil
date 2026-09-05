//! Phase 5a-2 / I21 / AP17: typed trace events for sigil-runtime
//! (mirrors `crates/sigil-compiler/src/trace.rs`).
//!
//! Event surface (today):
//! - `shim_entry(shim, grant)` — every host-FFI shim call entry, with
//!   the shim name and grant decision.
//! - `shim_exit(shim, result_code, output_bytes)` — same call's exit,
//!   with the result code (0 for success packed-pointer; negative for
//!   error) and byte count.
//!
//! Discipline:
//! - Typed payloads (no free-text format strings).
//! - Payloads carry shim name, grant decision (allow/reject), result
//!   code, byte counts. NEVER raw guest-memory contents (URLs, paths,
//!   bodies) — those are user-controlled and may carry secrets.
//! - The `trace` Cargo feature gates all emission; without the feature,
//!   every emit function is a no-op (and gets inlined to nothing).
//!
//! Step 12 of the supremum loop collapsed the previous struct-wrapper
//! shape (FfiShimEntry / FfiShimExit) into direct function arguments.
//! The structs added no safety beyond what positional args give on a
//! 2-arg / 3-arg function, and were costing ~80 LOC of runtime TCB.

#![allow(dead_code)]

/// Decision made by the shim's grant check.
#[derive(Debug, Clone, Copy)]
pub enum GrantDecision {
    /// No grant required (e.g., pure-compute shims like crypto_sha256).
    NotRequired,
    /// Grant present and matched the request.
    Allowed,
    /// Grant absent or did not match the request — shim returns 403.
    Rejected,
}

#[cfg(feature = "trace")]
pub fn shim_entry(shim: &str, grant: GrantDecision) {
    tracing::trace!(
        target: "sigil_runtime::ffi",
        shim = shim,
        grant = ?grant,
        "ffi_shim_entry"
    );
}

#[cfg(not(feature = "trace"))]
pub fn shim_entry(_shim: &str, _grant: GrantDecision) {}

#[cfg(feature = "trace")]
pub fn shim_exit(shim: &str, result_code: i64, output_bytes: u32) {
    tracing::trace!(
        target: "sigil_runtime::ffi",
        shim = shim,
        result_code = result_code,
        output_bytes = output_bytes,
        "ffi_shim_exit"
    );
}

#[cfg(not(feature = "trace"))]
pub fn shim_exit(_shim: &str, _result_code: i64, _output_bytes: u32) {}
