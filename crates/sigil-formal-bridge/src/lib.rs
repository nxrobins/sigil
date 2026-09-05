//! Narrow, safe Rust facade for the statically linked Lean CSIR verifier.
//!
//! All unsafe code is confined to this crate. The compiler passes an immutable
//! canonical byte slice and receives the verifier's packed 64-bit verdict.
//! Separate declaration decoders do not authorize programs or produce evidence.

use std::sync::OnceLock;

const INITIALIZATION_FAILURE: u64 = u64::MAX;

unsafe extern "C" {
    fn sigil_csir_initialize() -> i32;
    fn sigil_csir_verify_raw(bytes: *const u8, len: usize) -> u64;
    fn sigil_host_profile_validate_raw(bytes: *const u8, len: usize) -> u64;
    fn sigil_csir_v9_validate_declarations_raw(bytes: *const u8, len: usize) -> u64;
    fn sigil_csir_v9_verify_raw(bytes: *const u8, len: usize) -> u64;
}

static INITIALIZED: OnceLock<Result<(), InitializeError>> = OnceLock::new();

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InitializeError;

impl std::fmt::Display for InitializeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("the statically linked Lean runtime or CSIR module failed to initialize")
    }
}

impl std::error::Error for InitializeError {}

/// Initialize the Lean runtime exactly once and evaluate the linked verifier.
///
/// The C shim copies `bytes` into a Lean `ByteArray`; Lean consumes that owned
/// object before the call returns. No Rust allocation is exposed to Lean.
pub fn verify(bytes: &[u8]) -> Result<u64, InitializeError> {
    initialize()?;

    // SAFETY: the shim reads exactly `len` bytes during this call and does not
    // retain the pointer. `bytes.as_ptr()` is valid for that duration, including
    // the conventional dangling-but-non-dereferenced pointer for an empty slice.
    let verdict = unsafe { sigil_csir_verify_raw(bytes.as_ptr(), bytes.len()) };
    verdict_result(verdict)
}

/// Validate canonical host declarations with the independent linked Lean decoder.
///
/// Zero attests to the profile's encoding and declared flow constraints only. It
/// neither verifies a program nor approves a host implementation, and cannot
/// construct a compiler's `FormalSecurityReport`.
pub fn validate_host_profile(bytes: &[u8]) -> Result<u64, InitializeError> {
    initialize()?;
    // SAFETY: the shim only reads this live immutable slice during the call and
    // copies it into an owned Lean ByteArray. It never retains the Rust pointer.
    let verdict = unsafe { sigil_host_profile_validate_raw(bytes.as_ptr(), bytes.len()) };
    verdict_result(verdict)
}

/// Decode canonical CSIR v9 declaration framing and exact host/actor/root bindings.
///
/// Zero attests only to declaration decoding. This function is **not** a security
/// verifier: it proves no occurrence policy, relational result, or host-provider
/// conformance, and cannot produce a compiler's `FormalSecurityReport`. Production
/// v9 authorization uses the distinct [`verify_v9`] entry; [`verify`] retains the
/// historical v8 ABI for differential tests and compatibility evidence.
pub fn validate_v9_declarations(bytes: &[u8]) -> Result<u64, InitializeError> {
    initialize()?;
    // SAFETY: the shim reads only this live immutable slice during the call,
    // copies it into an owned Lean ByteArray, and never retains its Rust pointer.
    let verdict = unsafe { sigil_csir_v9_validate_declarations_raw(bytes.as_ptr(), bytes.len()) };
    verdict_result(verdict)
}

/// Run the production CSIR v9 verifier.
///
/// This is distinct from declaration validation: the linked Lean entry re-runs every retained
/// v8 check over the exact prefix, derives occurrence/dataflow/invocation facts from the decoded
/// suffix, validates activation ownership, and enforces boundary ceilings.
pub fn verify_v9(bytes: &[u8]) -> Result<u64, InitializeError> {
    initialize()?;
    // SAFETY: the C shim copies this live immutable slice into an owned Lean ByteArray and never
    // retains the Rust pointer.
    let verdict = unsafe { sigil_csir_v9_verify_raw(bytes.as_ptr(), bytes.len()) };
    verdict_result(verdict)
}

fn initialize() -> Result<(), InitializeError> {
    let initialized = INITIALIZED.get_or_init(|| {
        // SAFETY: the no-argument shim initializes process-global Lean state.
        // OnceLock guarantees that this call occurs at most once per process.
        let status = unsafe { sigil_csir_initialize() };
        (status == 0).then_some(()).ok_or(InitializeError)
    });
    *initialized
}

fn verdict_result(verdict: u64) -> Result<u64, InitializeError> {
    if verdict == INITIALIZATION_FAILURE {
        Err(InitializeError)
    } else {
        Ok(verdict)
    }
}

#[cfg(test)]
mod tests {
    use super::verify;
    use std::time::{Duration, Instant};

    const EMPTY_CSIR: &[u8] = &[
        b'C', b'S', b'I', b'R', 8, 0, 0, 0, 1, 0, 0, 0, 33, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    ];

    #[test]
    fn linked_lean_accepts_canonical_empty_program_repeatedly() {
        assert_eq!(verify(EMPTY_CSIR), Ok(0));
        assert_eq!(verify(EMPTY_CSIR), Ok(0));
    }

    #[test]
    fn linked_warm_small_fixture_median_stays_below_one_millisecond() {
        // Initialization is deliberately outside the measurement. Release evidence records it
        // separately; the production retirement threshold applies to warm in-process FFI calls.
        assert_eq!(verify(EMPTY_CSIR), Ok(0));
        let mut samples = Vec::with_capacity(101);
        for _ in 0..101 {
            let started = Instant::now();
            assert_eq!(verify(EMPTY_CSIR), Ok(0));
            samples.push(started.elapsed());
        }
        samples.sort_unstable();
        let median = samples[samples.len() / 2];
        assert!(
            median < Duration::from_millis(1),
            "warm linked verifier median {median:?} exceeds the 1 ms retirement ceiling"
        );
    }

    #[test]
    fn linked_lean_rejects_malformed_input() {
        assert_ne!(verify(b"not-csir"), Ok(0));
    }

    #[test]
    fn linked_decoder_rejects_every_noncanonical_header_shape() {
        let cases: &[&[u8]] = &[
            b"CSIR\x07\x00\x00\x00\x00\x00\x00\x00",     // wrong version
            b"CSIR\x08\x00\x00\x00\x01\x00\x00\x00",     // missing declared node
            b"CSIR\x08\x00\x00\x00\x00\x00\x00\x00\x00", // trailing byte
            b"CSIX\x08\x00\x00\x00\x00\x00\x00\x00",     // wrong magic
        ];
        for bytes in cases {
            assert_ne!(verify(bytes), Ok(0), "decoder accepted {bytes:?}");
        }
    }

    #[test]
    fn linked_decoder_rejects_invalid_tags_and_reserved_bytes() {
        let mut invalid_op = EMPTY_CSIR.to_vec();
        invalid_op[12] = 0xff;
        assert_ne!(verify(&invalid_op), Ok(0));

        let mut reserved = EMPTY_CSIR.to_vec();
        reserved[43] = 1;
        assert_ne!(verify(&reserved), Ok(0));
    }

    #[test]
    fn linked_decoder_rejects_noncanonical_node_identifiers() {
        let mut bytes = EMPTY_CSIR.to_vec();
        // A one-node encoding has canonical node ID 1. The ID word starts at
        // byte 24 of the fixed-width node payload.
        bytes[36..40].copy_from_slice(&2_u32.to_le_bytes());
        assert_ne!(verify(&bytes), Ok(0));
    }
}
