//! Historical v8 probes plus the production-v9 occurrence-policy regression.
//!
//! The raw loop-header fixture remains accepted as immutable evidence of the old gap. The acyclic
//! backward escape is now rejected by the retained verifier itself, since the merge-block pc
//! restore became postdominance-aware; its fixture pins that kernel-checked verdict instead.
//! Production source compilation now projects v9 and must reject the repeated Public action.
//! This is a unary policy result, not evidence of the still-unfinished independent-length Public
//! theorem.

use sigil_compiler::compile_named_module;

fn fixture_bytes(fixture: &str) -> Vec<u8> {
    let digits = fixture
        .bytes()
        .filter(|byte| !byte.is_ascii_whitespace())
        .collect::<Vec<_>>();
    let (pairs, remainder) = digits.as_chunks::<2>();
    assert!(remainder.is_empty(), "fixture has an incomplete hex byte");
    pairs
        .iter()
        .map(|pair| {
            u8::from_str_radix(std::str::from_utf8(pair).expect("ASCII hex"), 16)
                .expect("fixture contains valid hex bytes")
        })
        .collect::<Vec<_>>()
}

#[test]
fn public_region_probe_shared_wire_is_accepted_by_linked_verifier() {
    let bytes = fixture_bytes(include_str!(
        "../../../proofs/lean/fixtures/public-loop-header-boundary.hex"
    ));
    assert_eq!(bytes.len(), 12 + 40 * 32);
    assert_eq!(
        sigil_formal_bridge::verify(&bytes).expect("native verifier runs"),
        0,
        "the linked verdict must match the kernel-checked feasibility witness"
    );
    assert_ne!(
        sigil_formal_bridge::verify(&bytes[..bytes.len() - 1]).expect("native verifier runs"),
        0,
        "the witness does not permit malformed/truncated CSIR"
    );
}

/// Mirrors `V8OccurrenceProbes.acyclic_backward_escape_shared_bytes_rejected`: the packed
/// native verdict is node-id 21 in the high word, detail 1 in bits 16..31, and the flow kind
/// code 2 in the low half-word.
const ACYCLIC_BACKWARD_ESCAPE_VERDICT: u64 = (21 << 32) | (1 << 16) | 2;

#[test]
fn public_region_probe_acyclic_backward_escape_matches_kernel_checked_rejection() {
    let bytes = fixture_bytes(include_str!(
        "../../../proofs/lean/fixtures/public-acyclic-backward-escape.hex"
    ));
    assert_eq!(bytes.len(), 12 + 26 * 32);
    assert_eq!(ACYCLIC_BACKWARD_ESCAPE_VERDICT, 90_194_378_754);
    assert_eq!(
        sigil_formal_bridge::verify(&bytes).expect("native verifier runs"),
        ACYCLIC_BACKWARD_ESCAPE_VERDICT,
        "the retained verifier's flow rejection must match the kernel-checked raw counterexample"
    );
    assert_ne!(
        sigil_formal_bridge::verify(&bytes[..bytes.len() - 1]).expect("native verifier runs"),
        0,
        "truncation must not become an accepted fixture"
    );
}

#[test]
fn production_v9_rejects_actor_send_in_secret_loop_header() {
    let source = r#"
module public_region_probe;
cap type Fuel {}

actor Worker {
    init(f: Fuel) {}
    on Ping(value: i64) {}
}

fn guard(worker: ActorRef<Worker>, again: bool @Secret) -> bool @Secret {
    worker.send(Ping(7));
    return again;
}

fn run(worker: ActorRef<Worker>, secret: bool @Secret) -> i64 {
    let mut again: bool @Secret = secret;
    while guard(worker, again) {
        again = false;
    }
    return 0;
}
"#;
    let error = compile_named_module("public_region_probe.sigil", source)
        .expect_err("production v9 must reject the secret-controlled Public occurrence");
    assert_eq!(
        error
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect::<Vec<_>>(),
        vec!["I013"],
        "during dual-gate rollout a v9-only policy rejection remains fail-closed I013"
    );
    assert!(error.diagnostics()[0].message().contains("detail=40"));
}

#[test]
fn production_v9_preserves_the_pure_secret_loop_header_twin() {
    compile_named_module(
        "public_region_pure.sigil",
        include_str!("../../../proofs/lean/fixtures/occurrence-loop-header-pure.sigil"),
    )
    .expect("a private pure guard with a justified Public continuation remains accepted");
}
