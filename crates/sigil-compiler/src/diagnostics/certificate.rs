//! Verification certificate — JSON-serializable summary of what the
//! compiler proved about a successfully-compiled Sigil program.
//!
//! Step 11 of the supremum loop introduced this as axis-5 progress
//! (option (a) from the prompt: "a verification-only artifact external
//! tools can trust"). Step 17 added `sigil verify-cert` to make the
//! certificate load-bearing — a consumer can pair a cert with the
//! claimed source and get a verdict. Step 22 (this file's current
//! schema bump) extends the cert to ALSO bind to the emitted WASM
//! bytes, so a deployment pipeline holding only the WASM artifact
//! (no source) can verify the binary matches what the cert was
//! issued for.
//!
//! What the certificate binds to:
//! * `compiler_version` — the CARGO_PKG_VERSION at build time. A
//!   verifier knows which compiler produced the claims and decides
//!   whether to trust that version.
//! * `source_fingerprint` — SHA-256 hash of source bytes plus their
//!   length. Schema v3 (iteration 36 of Spec A + E) upgraded from
//!   FNV-1a-64 because FNV is not collision-resistant against an
//!   adversary who chooses the source — and the run/forge cert gate
//!   makes the fingerprint load-bearing under attacker-chosen-source
//!   conditions. Note: the certificate is still NOT signed; provenance
//!   (proving the cert came from a SIGIL compiler we trust) is a
//!   separate problem with separate infrastructure (Out of Scope for
//!   this iteration; see plan MI-10).
//! * `wasm_inner_fingerprint` (schema v2+) — SHA-256 (v3+) /
//!   FNV-1a-64 (v2) hash of the emitted inner-module WASM bytes.
//!   Lets a consumer verify the *deployable artifact* matches the
//!   cert without needing the source. Source-fingerprint and
//!   wasm-fingerprint are independent checks: matching source implies
//!   matching WASM only if the compiler is deterministic (which it
//!   is, by design — locked by the determinism test in iteration 36).
//! * `wasm_outer_fingerprint` (schema v2+) — same for the outer
//!   module's WASM. `None` for programs that compile to a single
//!   inner module only.
//! * `capability_report` and `ownership_report` — the formal results
//!   of the proof passes. Each carries counts of what was checked,
//!   plus (for capability) the Z3 rlimit consumed (step 7).
//! * `schema_version` — bumped on any breaking change to the JSON
//!   shape so consumers can pin.

use serde::{Deserialize, Serialize};

use crate::capability::CapabilityReport;
use crate::formal::FormalSecurityReport;
use crate::ownership::OwnershipReport;

/// JSON schema version. Bump on any breaking change to field names,
/// types, or required-ness.
///
/// * v1: introduced in step 11 — source fingerprint + capability/
///   ownership reports + module names + effects_required.
/// * v2: step 22 — adds `wasm_inner_fingerprint` and
///   `wasm_outer_fingerprint`, binding the cert to the emitted
///   artifact in addition to the source. Used FNV-1a-64 for both.
/// * v3: iteration 36 of Spec A + E — upgrades both source and
///   WASM fingerprints from FNV-1a-64 to SHA-256. Required because
///   the new run/forge cert gate makes the fingerprint load-bearing
///   under attacker-chosen-source conditions; FNV is not collision-
///   resistant. The `verify-cert` reporter still reads v2 certs
///   (with a deprecation warning); the gate accepts v3 only.
/// * v4: Wall 4 Steps 4+5 — `RefinementClause.literal: i64` becomes
///   `.rhs: RefinementRhs { Literal(i64), Field(String), LengthOf(String) }`
///   (N9). The cert's refinement-clause serialization shape changes
///   accordingly. Pre-v4 cert consumers MUST fail-loud on schema
///   mismatch (no silent misparse).
/// * v5: Wall 4 Step 6 — `EnumVariant.fields: Vec<TypeExpr>` becomes
///   `Vec<EnumVariantField>` with `name: Option<String>` per field;
///   `EnumVariant.refinements: Vec<RefinementClause>` added for
///   per-variant refinement clauses (N1-S6, N10-S6). Pre-v5 cert
///   consumers MUST fail-loud on schema mismatch (no silent misparse).
/// * v6: Wall 4 Step 7 — `FnDef` gains `param_refinements:
///   Vec<RefinementClause>` and `return_refinement:
///   Option<RefinementClause>` (N1-S7, N28-S7). Pre-v6 cert consumers
///   MUST fail-loud on schema mismatch.
/// * v7: Wall 5 Step 1 — `source_fingerprint` becomes a SHA-256 hash
///   over a canonical-ordered framed concatenation of (source_name,
///   source_text) pairs across the entire compilation set. Framing per
///   source: `\x00 + name + \x00 + text`. Sources sorted by name
///   (UTF-8 byte-lexicographic) before concatenation. Single-file
///   inputs use the same framing with N=1, so v6 and v7 fingerprints
///   DIFFER even for byte-identical single-source compiles. Pre-v7
///   cert consumers MUST fail-loud on schema mismatch (N28-W5S1).
///   The framing is bijective because source filenames cannot contain
///   NUL bytes (M009 / N11-W5S1) and SIGIL source code rejects NUL via
///   the lexer.
/// * v8: the capability report gains `solver_verified: bool` — `true`
///   iff the Z3-backed verification actually ran (the `solver` feature
///   compiled AND the prover executed). It is DETERMINISTIC per build
///   config (unlike the run-varying rlimit/cache stats) and so is
///   INCLUDED in cert byte-equality: a solver-off cert differs from a
///   solver-on cert for byte-identical source. The witness for the
///   user's "solver-off silently weakens guarantees" concern. Pre-v8
///   cert consumers MUST fail-loud on schema mismatch (the `gate_cert`
///   strict check rejects v7; `verify_certificate` reads v7 with a
///   deprecation warning).
/// * v9: binds the mandatory combined Lean-verifier report and canonical
///   CSIR fingerprint. Missing formal evidence cannot authorize execution.
pub const CERTIFICATE_SCHEMA_VERSION: u32 = 9;

/// The version stamped into every certificate's `compiler_version`, and
/// the ONLY value a verifier may compare against when deciding whether
/// re-derivation is meaningful.
///
/// Exported because `env!("CARGO_PKG_VERSION")` expands to the version of
/// whichever crate it is written in: evaluated here it is
/// `sigil-compiler`'s, evaluated in `sigil-cli` it is the CLI's. Those are
/// separate `[package] version` fields that are equal today only by
/// coincidence. If they ever diverge, a verifier reading the CLI's value
/// would silently stop attempting re-derivation for certs this very
/// binary produced (`rederivation_attempted` is gated on the match), and
/// the cert would still verify — quietly checking less than it claims.
/// One constant, one source of truth.
pub const COMPILER_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Deterministic 64-bit FNV-1a hash. Kept exported for the
/// `verify-cert` reporter's v2-compatibility path; new certificates
/// (v3+) use SHA-256 instead. Do not use this for any *gating*
/// decision — FNV-1a-64 is not collision-resistant against an
/// adversary who chooses the source.
pub fn fnv1a_64(bytes: &[u8]) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        hash ^= b as u64;
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

/// SHA-256 hex digest of `bytes`. Used for source and WASM
/// fingerprinting in v3 certificates. The 64-character lowercase
/// hex output is canonical — no algorithm choice baked into the
/// format string. Cross-language verifiers can recompute from the
/// raw bytes with any standard SHA-256 implementation.
pub fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        write!(&mut out, "{byte:02x}").expect("write to String never fails");
    }
    out
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct CertificateJson {
    pub schema_version: u32,
    pub compiler_version: String,
    pub source_name: String,
    pub source_fingerprint: ArtifactFingerprint,
    /// FNV-1a 64-bit fingerprint of the emitted inner-module WASM.
    /// Step 22 (axis-5 fourth touch): the cert now binds to the
    /// deployable artifact, not just the source.
    pub wasm_inner_fingerprint: ArtifactFingerprint,
    /// Same shape, for the outer-module WASM. `None` for programs
    /// that don't emit an outer module (most policies).
    pub wasm_outer_fingerprint: Option<ArtifactFingerprint>,
    pub primary_module: Option<String>,
    pub module_names: Vec<String>,
    pub capability: CapabilityReportJson,
    pub ownership: OwnershipReportJson,
    /// Mandatory in schema v9. Optional only so reporters can deserialize and
    /// deprecate older certificates; execution gates require `Some` and compare
    /// it with freshly re-derived evidence.
    #[serde(default)]
    pub formal: Option<FormalSecurityReport>,
    /// Sorted, deduplicated names of every effect that ANY function in
    /// this program requires. Step 13 of the supremum loop: lets external
    /// policy authorities decide whether the program's effect surface is
    /// acceptable for their deployment context. Empty for programs that
    /// use no declared effects.
    pub effects_required: Vec<String>,
}

/// Deterministic fingerprint of an arbitrary byte sequence. Used both
/// for `source_fingerprint` and the WASM fingerprints. The `algorithm`
/// field is pinned so a future swap is visible to consumers — they
/// can refuse a cert whose algorithm they don't recognize.
///
/// Schema v3 (iteration 36): `algorithm = "sha2-256"`, `hash` is a
/// 64-character lowercase hex digest of SHA-256.
/// Schema v2 (legacy): `algorithm = "fnv1a-64"`, `hash` is a
/// 16-character hex of FNV-1a-64. Still produced by
/// `ArtifactFingerprint::new_fnv1a_v2` for the reporter's
/// backward-compat path; do not use for gating decisions.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ArtifactFingerprint {
    pub algorithm: String,
    pub bytes: u64,
    pub hash: String,
}

impl ArtifactFingerprint {
    /// Compute a v3 fingerprint over `bytes` using SHA-256.
    pub fn new(bytes: &[u8]) -> Self {
        Self {
            algorithm: "sha2-256".to_string(),
            bytes: bytes.len() as u64,
            hash: sha256_hex(bytes),
        }
    }

    /// Wall 5 Step 1 / N30-W5S1: compute the v7 `source_fingerprint`
    /// over the canonical-ordered framed concatenation of a project's
    /// source set. The single canonical computation site for both
    /// single-file (N=1) and multi-file inputs.
    ///
    /// Framing: for each `(name, text)` pair, emit `\x00 + name + \x00 + text`.
    /// Pairs are sorted by `name` (UTF-8 byte-lexicographic, `str::cmp`)
    /// before concatenation. The resulting buffer is SHA-256 hashed and
    /// the byte length is recorded on the `ArtifactFingerprint`.
    ///
    /// Determinism: sort order is locked to `str::cmp` (no `partial_cmp`,
    /// no `PathBuf::cmp`, no `to_lowercase`) so the fingerprint is
    /// platform-independent. Per N5-W5S1.
    ///
    /// Bijectivity: source filenames cannot contain NUL bytes per M009
    /// charset validation, and SIGIL source code rejects raw NUL via the
    /// lexer, so the framing parses unambiguously.
    pub fn compute_v7_source_fingerprint(sources: &[(String, String)]) -> Self {
        // Defensive sort by name. Callers are expected to have sorted
        // already, but locking it here makes the fingerprint impossible
        // to corrupt by caller mistake.
        let mut ordered: Vec<&(String, String)> = sources.iter().collect();
        ordered.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));

        let mut framed: Vec<u8> = Vec::new();
        for (name, text) in ordered {
            framed.push(0u8);
            framed.extend_from_slice(name.as_bytes());
            framed.push(0u8);
            framed.extend_from_slice(text.as_bytes());
        }
        Self::new(&framed)
    }

    /// Compute a v2 fingerprint over `bytes` using FNV-1a-64. Kept for
    /// the `verify-cert` reporter's backward-compat path; not used by
    /// the run/forge gate.
    pub fn new_fnv1a_v2(bytes: &[u8]) -> Self {
        Self {
            algorithm: "fnv1a-64".to_string(),
            bytes: bytes.len() as u64,
            hash: format!("{:016x}", fnv1a_64(bytes)),
        }
    }

    /// Recompute a fingerprint of `bytes` using THIS fingerprint's
    /// declared algorithm. Returns `None` if the algorithm is
    /// unrecognized — the caller treats that as a verification failure
    /// (the cert claims an algorithm this compiler doesn't understand).
    ///
    /// Lets `verify_certificate` handle both v2 (FNV) and v3 (SHA-256)
    /// certificates with one code path: it reads the cert's own
    /// `algorithm` field and recomputes accordingly. Gating callers
    /// (`gate_cert`) instead pin the algorithm by checking the
    /// schema_version first.
    pub fn recompute(&self, bytes: &[u8]) -> Option<Self> {
        match self.algorithm.as_str() {
            "sha2-256" => Some(Self::new(bytes)),
            "fnv1a-64" => Some(Self::new_fnv1a_v2(bytes)),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct CapabilityReportJson {
    pub verified_functions: usize,
    pub checked_blocks: usize,
    pub checked_sites: usize,
    pub z3_rlimit_consumed: Option<u64>,
    /// Axis-2 eighth touch: Z3 query-result cache hit/miss counts for
    /// this compile. Mirrors `z3_rlimit_consumed`'s treatment —
    /// non-deterministic across runs (cache warmup state), so excluded
    /// from cert byte-equality in `diff_certificates`,
    /// sigil-cli/src/cert_gate.rs.
    /// `#[serde(default)]` so v3 certs from older compilers parse cleanly.
    #[serde(default)]
    pub z3_cache_hits: u64,
    #[serde(default)]
    pub z3_cache_misses: u64,
    /// Whether the Z3-backed verification ran for this artifact (v8). See
    /// [`crate::capability::CapabilityReport::solver_verified`] for the
    /// contract. UNLIKE the cache/rlimit stats above, this is
    /// DETERMINISTIC per build config and is INCLUDED in cert
    /// byte-equality: a solver-off cert differs from a solver-on cert.
    /// `#[serde(default)]` (→ `false`) so pre-v8 certs parse as
    /// "solver verification status unknown / not asserted".
    #[serde(default)]
    pub solver_verified: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct OwnershipReportJson {
    pub verified_functions: usize,
    pub move_sites: usize,
    pub linear_values_checked: usize,
}

impl CertificateJson {
    /// Wall 5 Step 1: produce the source-bytes input that THIS cert's
    /// `source_fingerprint` was computed over, given the verifier's
    /// current source text. Dispatches on `self.schema_version`:
    ///
    /// - v7+: framed concatenation `\x00 + source_name + \x00 + source_text`
    ///   (single-file is the N=1 case of the multi-file canonicalization).
    /// - v3-v6: raw source bytes (legacy single-source compatibility).
    ///
    /// Verifiers (`gate_cert`, `verify_certificate`) call this to obtain
    /// the bytes they must hash to compare against `source_fingerprint.hash`.
    /// Hides the per-schema framing convention behind one canonical helper
    /// so callers cannot miswire it.
    pub fn canonical_source_bytes(&self, source_text: &[u8]) -> Vec<u8> {
        if self.schema_version >= 7 {
            let mut framed = Vec::with_capacity(2 + self.source_name.len() + source_text.len());
            framed.push(0u8);
            framed.extend_from_slice(self.source_name.as_bytes());
            framed.push(0u8);
            framed.extend_from_slice(source_text);
            framed
        } else {
            source_text.to_vec()
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn new(
        source_name: String,
        source_text: &str,
        wasm_inner: &[u8],
        wasm_outer: Option<&[u8]>,
        primary_module: Option<String>,
        module_names: Vec<String>,
        capability: &CapabilityReport,
        ownership: &OwnershipReport,
        formal: &FormalSecurityReport,
        effects_required: Vec<String>,
    ) -> Self {
        Self::new_for_sources(
            source_name.clone(),
            &[(source_name, source_text.to_owned())],
            wasm_inner,
            wasm_outer,
            primary_module,
            module_names,
            capability,
            ownership,
            formal,
            effects_required,
        )
    }

    /// Package/project form of the v7 source-set certificate constructor.
    /// Existing single-source callers continue through `new`, whose N=1 bytes
    /// are unchanged. Package compilation supplies every normalized logical
    /// source name here and wraps this base certificate in a package-graph
    /// certificate; legacy cert schema and verification remain untouched.
    #[allow(clippy::too_many_arguments)]
    pub fn new_for_sources(
        source_name: String,
        sources: &[(String, String)],
        wasm_inner: &[u8],
        wasm_outer: Option<&[u8]>,
        primary_module: Option<String>,
        module_names: Vec<String>,
        capability: &CapabilityReport,
        ownership: &OwnershipReport,
        formal: &FormalSecurityReport,
        effects_required: Vec<String>,
    ) -> Self {
        let source_fingerprint = ArtifactFingerprint::compute_v7_source_fingerprint(sources);
        Self {
            schema_version: CERTIFICATE_SCHEMA_VERSION,
            compiler_version: COMPILER_VERSION.to_string(),
            source_name,
            source_fingerprint,
            wasm_inner_fingerprint: ArtifactFingerprint::new(wasm_inner),
            wasm_outer_fingerprint: wasm_outer.map(ArtifactFingerprint::new),
            primary_module,
            module_names,
            capability: CapabilityReportJson {
                verified_functions: capability.verified_functions,
                checked_blocks: capability.checked_blocks,
                checked_sites: capability.checked_sites,
                z3_rlimit_consumed: capability.z3_rlimit_consumed,
                z3_cache_hits: capability.z3_cache_hits,
                z3_cache_misses: capability.z3_cache_misses,
                solver_verified: capability.solver_verified,
            },
            ownership: OwnershipReportJson {
                verified_functions: ownership.verified_functions,
                move_sites: ownership.move_sites,
                linear_values_checked: ownership.linear_values_checked,
            },
            formal: Some(formal.clone()),
            effects_required,
        }
    }
}

#[cfg(test)]
mod canonicalization_tests {
    //! Lock tests for the SHA-256 fingerprint canonicalization documented
    //! in `docs/z3-theory-inventory.md` Appendix A. If any of these golden
    //! hashes change, the canonicalization changed — a behavior break for
    //! any consumer that already trusts a v3 cert.
    //!
    //! Closes adversarial-review fix MI-2 (canonical module ordering and
    //! input bytes): the cert's source_fingerprint is computed over the
    //! raw UTF-8 bytes of the source string verbatim, with no
    //! normalization. The frozen golden value below proves the input
    //! convention by construction.
    use super::*;

    /// Source fingerprint of the literal `"hello"` (5 bytes) under
    /// SHA-256 is well-known across every SHA-256 implementation in any
    /// language. This test catches:
    ///   1. Accidental normalization (newline conversion, BOM stripping,
    ///      lowercasing) — would change the hash.
    ///   2. Hash algorithm regressions (a future "performance" PR that
    ///      swaps SHA-256 for something faster but less standard).
    ///   3. Hex encoding changes (uppercase vs lowercase, missing
    ///      leading zeros).
    #[test]
    fn sha256_hello_matches_known_value() {
        // From any standard SHA-256 implementation:
        //   echo -n "hello" | sha256sum
        //   → 2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824
        let expected = "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824";
        assert_eq!(sha256_hex(b"hello"), expected);
    }

    /// Source fingerprint of empty input is also well-known.
    #[test]
    fn sha256_empty_matches_known_value() {
        let expected = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
        assert_eq!(sha256_hex(b""), expected);
    }

    /// `ArtifactFingerprint::new` produces the same hash as the bare
    /// `sha256_hex` helper plus the byte length. Confirms the
    /// constructor doesn't accidentally inject any prefix/suffix bytes.
    #[test]
    fn artifact_fingerprint_records_raw_sha256_and_length() {
        let bytes = b"module sigil;\n";
        let fp = ArtifactFingerprint::new(bytes);
        assert_eq!(fp.algorithm, "sha2-256");
        assert_eq!(fp.bytes, bytes.len() as u64);
        assert_eq!(fp.hash, sha256_hex(bytes));
    }

    /// Two identical byte sequences produce identical fingerprints.
    /// Determinism floor.
    #[test]
    fn artifact_fingerprint_is_deterministic() {
        let bytes = b"deterministic source\n";
        let a = ArtifactFingerprint::new(bytes);
        let b = ArtifactFingerprint::new(bytes);
        assert_eq!(a.algorithm, b.algorithm);
        assert_eq!(a.bytes, b.bytes);
        assert_eq!(a.hash, b.hash);
    }

    /// A one-byte mutation produces a different hash — the load-bearing
    /// property of the gate's source-fingerprint check.
    #[test]
    fn artifact_fingerprint_changes_on_one_byte_mutation() {
        let a = ArtifactFingerprint::new(b"abc");
        let b = ArtifactFingerprint::new(b"abd");
        assert_ne!(a.hash, b.hash);
        // Byte count is also recorded; for same-length inputs only the
        // hash distinguishes them.
        assert_eq!(a.bytes, b.bytes);
    }

    // ── Wall 5 Step 1: v7 framed-concat source_fingerprint ──────────────────

    /// N30-W5S1: single-file v7 fingerprint applies the same framing
    /// as multi-file (N=1 case). Hand-computed expected hash locks the
    /// framing convention.
    #[test]
    fn v7_single_file_uses_framed_concat() {
        let fp = ArtifactFingerprint::compute_v7_source_fingerprint(&[(
            "main.sigil".to_string(),
            "hello".to_string(),
        )]);
        // Hand-computed: SHA-256 of `\x00main.sigil\x00hello`.
        // Reproducible: `printf '\x00main.sigil\x00hello' | sha256sum`.
        let framed = b"\x00main.sigil\x00hello";
        assert_eq!(fp.bytes, framed.len() as u64);
        assert_eq!(fp.hash, sha256_hex(framed));
        assert_eq!(fp.algorithm, "sha2-256");
        // Critically: v7 single-file fingerprint differs from v6's
        // bare `sha256("hello")`. Pre-v7 consumers MUST fail-loud.
        assert_ne!(fp.hash, sha256_hex(b"hello"));
    }

    /// N7/N29-W5S1: arg-order independence. Permuted input → identical
    /// fingerprint via the internal sort-by-name.
    #[test]
    fn v7_fingerprint_is_order_independent() {
        let abc = ArtifactFingerprint::compute_v7_source_fingerprint(&[
            ("a.sigil".to_string(), "alpha".to_string()),
            ("b.sigil".to_string(), "beta".to_string()),
            ("c.sigil".to_string(), "gamma".to_string()),
        ]);
        let bca = ArtifactFingerprint::compute_v7_source_fingerprint(&[
            ("b.sigil".to_string(), "beta".to_string()),
            ("c.sigil".to_string(), "gamma".to_string()),
            ("a.sigil".to_string(), "alpha".to_string()),
        ]);
        let cba_reverse = ArtifactFingerprint::compute_v7_source_fingerprint(&[
            ("c.sigil".to_string(), "gamma".to_string()),
            ("b.sigil".to_string(), "beta".to_string()),
            ("a.sigil".to_string(), "alpha".to_string()),
        ]);
        assert_eq!(abc.hash, bca.hash);
        assert_eq!(abc.hash, cba_reverse.hash);
        assert_eq!(abc.bytes, bca.bytes);
    }

    /// Changing any file's content changes the root fingerprint —
    /// the load-bearing property for multi-file cert binding.
    #[test]
    fn v7_fingerprint_changes_when_any_file_changes() {
        let baseline = ArtifactFingerprint::compute_v7_source_fingerprint(&[
            ("a.sigil".to_string(), "alpha".to_string()),
            ("b.sigil".to_string(), "beta".to_string()),
        ]);
        let mutated = ArtifactFingerprint::compute_v7_source_fingerprint(&[
            ("a.sigil".to_string(), "alpha".to_string()),
            ("b.sigil".to_string(), "BETA".to_string()), // one-char change
        ]);
        assert_ne!(baseline.hash, mutated.hash);
    }

    /// Empty source set produces SHA-256 of an empty buffer.
    /// `compile_project` rejects empty input with M008, but the
    /// fingerprint helper itself is total.
    #[test]
    fn v7_fingerprint_of_empty_set_is_sha256_of_empty() {
        let fp = ArtifactFingerprint::compute_v7_source_fingerprint(&[]);
        assert_eq!(fp.hash, sha256_hex(b""));
        assert_eq!(fp.bytes, 0);
    }
}
