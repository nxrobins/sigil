//! Load-bearing native tests for the production CSIR v9 verifier.
//!
//! Declaration validation is intentionally exercised beside verification so a
//! future refactor cannot silently substitute the non-authorizing decoder for
//! the production occurrence-policy gate.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use sigil_formal_bridge::{validate_v9_declarations, verify_v9};

const MALFORMED_CODE: u16 = 1;
const OCCURRENCE_POLICY_DETAIL: u16 = 40;
// The send boundary itself (`worker.send(Ping(7))` in
// proofs/lean/fixtures/occurrence-loop-header-send.sigil). Before main's
// postdominance-aware pc restore (merged 2026-09-02) the first violating site
// was the payload boundary five records earlier (node 83); the payload now
// converges and the Public send under the Secret loop is the exact site.
const OCCURRENCE_BOUNDARY_NODE: u32 = 88;
const MAX_CSIR_BYTES: usize = 64 * 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PackedViolation {
    code: u16,
    detail: u16,
    node_id: u32,
}

impl PackedViolation {
    fn decode(verdict: u64) -> Self {
        Self {
            code: (verdict & 0xffff) as u16,
            detail: ((verdict >> 16) & 0xffff) as u16,
            node_id: (verdict >> 32) as u32,
        }
    }
}

fn lean_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs/lean")
}

fn fixture(name: &str) -> Vec<u8> {
    let path = lean_root().join("fixtures/csir-v9").join(name);
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read {path:?}: {error}"));
    let hex = text.split_ascii_whitespace().collect::<String>();
    assert_eq!(hex.len() % 2, 0, "fixture must contain whole bytes");
    hex.as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            u8::from_str_radix(std::str::from_utf8(pair).expect("ASCII hex pair"), 16)
                .expect("canonical fixture hex")
        })
        .collect()
}

#[test]
fn declaration_success_does_not_authorize_an_occurrence_boundary_violation() {
    let pure = fixture("accept-loop-header-pure.hex");
    let boundary = fixture("accept-loop-header-send.hex");

    // Both envelopes are structurally canonical. Only the production verifier
    // is allowed to distinguish their occurrence policy.
    assert_eq!(validate_v9_declarations(&pure), Ok(0));
    assert_eq!(validate_v9_declarations(&boundary), Ok(0));
    assert_eq!(verify_v9(&pure), Ok(0));

    let verdict = verify_v9(&boundary).expect("the linked Lean runtime initializes");
    assert_eq!(
        PackedViolation::decode(verdict),
        PackedViolation {
            code: MALFORMED_CODE,
            detail: OCCURRENCE_POLICY_DETAIL,
            node_id: OCCURRENCE_BOUNDARY_NODE,
        },
        "the production gate must retain the exact rejected semantic site"
    );
}

#[test]
fn production_v9_verification_is_repeatable_after_process_initialization() {
    let pure = fixture("accept-loop-header-pure.hex");
    let boundary = fixture("accept-loop-header-send.hex");
    let expected_boundary = verify_v9(&boundary).expect("initial verifier call succeeds");

    assert_ne!(expected_boundary, 0);
    for _ in 0..8 {
        assert_eq!(verify_v9(&pure), Ok(0));
        assert_eq!(verify_v9(&boundary), Ok(expected_boundary));
    }
}

#[test]
fn production_v9_warm_small_fixture_median_stays_below_one_millisecond() {
    let pure = fixture("accept-loop-header-pure.hex");
    // Initialization remains outside the measurement and is recorded independently in tagged
    // evidence. This measures the authorizing v9 path, not the retained-v8 compatibility entry.
    assert_eq!(verify_v9(&pure), Ok(0));
    let mut samples = Vec::with_capacity(101);
    for _ in 0..101 {
        let started = Instant::now();
        assert_eq!(verify_v9(&pure), Ok(0));
        samples.push(started.elapsed());
    }
    samples.sort_unstable();
    let median = samples[samples.len() / 2];
    assert!(
        median < Duration::from_millis(1),
        "warm production-v9 verifier median {median:?} exceeds the 1 ms rollout ceiling"
    );
}

#[test]
fn production_v9_verifier_fails_closed_on_malformed_framing() {
    let pure = fixture("accept-loop-header-pure.hex");
    let malformed = PackedViolation {
        code: MALFORMED_CODE,
        detail: OCCURRENCE_POLICY_DETAIL,
        node_id: 0,
    };

    assert_eq!(
        verify_v9(b"not-csir").map(PackedViolation::decode),
        Ok(malformed)
    );
    assert_eq!(
        verify_v9(&pure[..pure.len() - 1]).map(PackedViolation::decode),
        Ok(malformed),
        "a truncated canonical fixture must fail in v9 decoding"
    );

    let mut trailing = pure;
    trailing.push(0);
    assert_eq!(
        verify_v9(&trailing).map(PackedViolation::decode),
        Ok(malformed),
        "noncanonical trailing bytes must fail in v9 decoding"
    );
}

#[test]
fn production_v9_shim_rejects_oversized_input_before_copying() {
    let oversized = vec![0; MAX_CSIR_BYTES + 1];
    assert_eq!(
        verify_v9(&oversized),
        Ok(MALFORMED_CODE.into()),
        "the native shim returns before allocating a Lean ByteArray"
    );
}
