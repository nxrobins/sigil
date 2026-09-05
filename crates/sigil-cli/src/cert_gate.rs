//! Certificate trust decisions: the pure verifier, the `verify-cert`
//! verb on top of it, and the strict-mode execution gate that `run`
//! and `forge` call before instantiating guest code.
//!
//! Owned invariant: the fail-closed execution gate. Executing verbs
//! refuse an artifact whose solver obligations were never discharged:
//! both gate on the freshly derived `solver_verified` (R817) whether
//! or not `--cert` was supplied (sole override:
//! `SIGIL_ALLOW_UNVERIFIED_CERT=1`); every `--cert` mismatch aborts
//! before instantiation with the `GateFailure` ladder R810..R819,
//! asserted by code, never by message substring. Pinned by the
//! in-file `verify_cert_tests`, `gate_tests`, and `forge_gate_tests`.

use std::fs;
use std::path::PathBuf;

use anyhow::{Context, bail};
use serde_json::json;
use sigil_compiler::diagnostics::codes;
use sigil_compiler::{
    Compilation, CompileOptions, CompilerContext, compile_named_module_with_context,
};

use crate::json_envelope;
use crate::json_envelope::{Envelope, OutputFormat};

#[cfg(test)]
use sigil_compiler::compile_named_module;

use crate::args::{CommandKind, VerifyCertCommand};

pub(crate) fn certificate_from_compilation(
    compilation: &Compilation,
    source_text: &str,
) -> sigil_compiler::certificate::CertificateJson {
    sigil_compiler::certificate::CertificateJson::new(
        compilation.source_name.clone(),
        source_text,
        &compilation.wasm_inner,
        compilation.wasm_outer.as_deref(),
        compilation.primary_module_name().map(str::to_owned),
        compilation.module_names.clone(),
        &compilation.capability_report,
        &compilation.ownership_report,
        &compilation.formal_security_report,
        compilation.effects_required.clone(),
    )
}

/// Pure verification core. Takes a supplied cert and the source text it
/// claims to certify; runs every check (schema, fingerprint, optional
/// re-derivation) and returns a structured result. Separated from CLI
/// plumbing so tests can exercise the logic without spawning subprocesses
/// or stubbing stdout. The CLI wrapper `run_verify_cert` is a thin shell
/// that reads files and dispatches output formatting.
pub(crate) struct VerifyResult {
    schema_ok: bool,
    hash_ok: bool,
    bytes_ok: bool,
    compiler_version_match: bool,
    rederivation_attempted: bool,
    rederivation_ok: bool,
    /// A `solver_verified: true` witness is accepted ONLY if it was actually
    /// re-derived and matched (`rederivation_ok`). `false` when the cert claims
    /// `true` but re-derivation was skipped (e.g. attacker also edited the
    /// unfingerprinted `compiler_version`) or failed — an unconfirmed,
    /// unsigned solver claim is rejected rather than given false assurance.
    solver_claim_ok: bool,
    /// `None` if no WASM file was provided; `Some(true)` if the hash
    /// matched `cert.wasm_inner_fingerprint`; `Some(false)` otherwise.
    /// Step 22: lets a deployment pipeline verify the deployable
    /// artifact without needing the source.
    wasm_inner_match: Option<bool>,
    /// Effects that the caller forbade via `--forbid-effect <NAME>` AND
    /// were present in the cert's `effects_required`. Empty means the
    /// cert satisfies all policy gates (or no gates were requested).
    /// Non-empty fails verification. Step 29 (axis-5 fifth touch).
    forbidden_effects_present: Vec<String>,
    /// Effects in the cert's `effects_required` that are NOT in the
    /// caller's `--allow-effect <NAME>` allowlist. Axis-5 ninth touch
    /// (complementary positive gate to `--forbid-effect`).
    ///
    /// Empty when (a) no `--allow-effect` flag was supplied at all
    /// (gate inactive), or (b) the gate is active and every cert
    /// effect is allowlisted. Non-empty fails verification.
    unauthorized_effects_present: Vec<String>,
    differences: Vec<String>,
    /// A profile-aware report is never successful without actual rederivation.
    /// Internal gate state only; the public JSON report fields are unchanged.
    context_rederivation_ok: bool,
    supplied_compiler_version: String,
    current_compiler_version: &'static str,
}

impl VerifyResult {
    fn all_ok(&self) -> bool {
        self.schema_ok
            && self.hash_ok
            && self.bytes_ok
            && (self.rederivation_ok || !self.rederivation_attempted)
            && self.wasm_inner_match.unwrap_or(true)
            && self.forbidden_effects_present.is_empty()
            && self.unauthorized_effects_present.is_empty()
            && self.solver_claim_ok
            && self.context_rederivation_ok
    }
}

#[cfg(test)]
pub(crate) fn verify_certificate(
    supplied: &sigil_compiler::certificate::CertificateJson,
    source_name: &str,
    source_text: &str,
    wasm_inner: Option<&[u8]>,
    forbidden_effects: &[String],
    allowed_effects: &[String],
) -> VerifyResult {
    verify_certificate_with_context(
        supplied,
        source_name,
        source_text,
        wasm_inner,
        forbidden_effects,
        allowed_effects,
        &CompilerContext::default(),
    )
}

pub(crate) fn verify_certificate_with_context(
    supplied: &sigil_compiler::certificate::CertificateJson,
    source_name: &str,
    source_text: &str,
    wasm_inner: Option<&[u8]>,
    forbidden_effects: &[String],
    allowed_effects: &[String],
    context: &CompilerContext,
) -> VerifyResult {
    use sigil_compiler::certificate::CERTIFICATE_SCHEMA_VERSION;

    let mut differences: Vec<String> = Vec::new();

    // Reporter accepts v2 (legacy FNV-1a-64) AND v3 (SHA-256). The
    // gate (`gate_cert`) is stricter and accepts v3 only. v2 fingerprints
    // are recomputed via the cert's own `algorithm` field — see
    // `ArtifactFingerprint::recompute`. Iteration 36 of the Spec A + E
    // plan upgraded the canonical schema to v3 for collision-resistance
    // under attacker-chosen source.
    let schema_ok = supplied.schema_version == CERTIFICATE_SCHEMA_VERSION
        || supplied.schema_version == CERTIFICATE_SCHEMA_VERSION - 1;
    if !schema_ok {
        differences.push(format!(
            "schema_version: supplied={}, current={}",
            supplied.schema_version, CERTIFICATE_SCHEMA_VERSION
        ));
    }

    // Wall 5 Step 1 / v7: source_fingerprint binds to the framed-concat
    // canonicalization for v7+ certs (single-file is N=1). The verifier
    // routes `source_text` through `canonical_source_bytes` to apply
    // the per-schema framing rule before recompute compares hashes.
    let canonical_source = supplied.canonical_source_bytes(source_text.as_bytes());
    let source_recomputed = supplied.source_fingerprint.recompute(&canonical_source);
    let (hash_ok, bytes_ok) = match &source_recomputed {
        Some(fresh) => {
            let hash_match = supplied.source_fingerprint.hash == fresh.hash;
            let bytes_match = supplied.source_fingerprint.bytes == fresh.bytes;
            if !hash_match {
                differences.push(format!(
                    "source_fingerprint.hash: supplied={}, fresh={}",
                    supplied.source_fingerprint.hash, fresh.hash
                ));
            }
            if !bytes_match {
                differences.push(format!(
                    "source_fingerprint.bytes: supplied={}, fresh={}",
                    supplied.source_fingerprint.bytes, fresh.bytes
                ));
            }
            (hash_match, bytes_match)
        }
        None => {
            differences.push(format!(
                "source_fingerprint.algorithm `{}` not recognized by this compiler",
                supplied.source_fingerprint.algorithm
            ));
            (false, false)
        }
    };

    // Step 22: optional WASM-byte verification. If a wasm buffer is
    // supplied, hash it and compare against `cert.wasm_inner_fingerprint`.
    // None when no wasm was provided — that's a downgrade to source-
    // only verification, not a failure (the gate uses a stricter helper
    // that requires WASM bytes to be supplied).
    let wasm_inner_match =
        wasm_inner.map(
            |bytes| match supplied.wasm_inner_fingerprint.recompute(bytes) {
                Some(fresh) => {
                    let hash_match = supplied.wasm_inner_fingerprint.hash == fresh.hash;
                    let bytes_match = supplied.wasm_inner_fingerprint.bytes == fresh.bytes;
                    if !hash_match {
                        differences.push(format!(
                            "wasm_inner_fingerprint.hash: supplied={}, fresh={}",
                            supplied.wasm_inner_fingerprint.hash, fresh.hash
                        ));
                    }
                    if !bytes_match {
                        differences.push(format!(
                            "wasm_inner_fingerprint.bytes: supplied={}, fresh={}",
                            supplied.wasm_inner_fingerprint.bytes, fresh.bytes
                        ));
                    }
                    hash_match && bytes_match
                }
                None => {
                    differences.push(format!(
                        "wasm_inner_fingerprint.algorithm `{}` not recognized",
                        supplied.wasm_inner_fingerprint.algorithm
                    ));
                    false
                }
            },
        );

    // NOT the CLI's own `env!("CARGO_PKG_VERSION")`: certs are stamped by
    // sigil-compiler, so the comparison has to read sigil-compiler's
    // version. Identical today (both 0.1.0), divergent the moment the two
    // packages are versioned separately — at which point the old code
    // would have stopped re-deriving without saying so.
    let current_compiler_version = sigil_compiler::certificate::COMPILER_VERSION;
    let compiler_version_match = supplied.compiler_version == current_compiler_version;

    // Re-derivation is meaningful only if the compiler versions match;
    // otherwise the schema is the same but the verified properties could
    // differ. Hash + schema checks above still rule out forgery in the
    // common case (cert detached from source). When versions differ we
    // surface the gap rather than silently skip.
    let rederivation_attempted = compiler_version_match && schema_ok && hash_ok;
    let mut rederivation_ok = false;
    if rederivation_attempted {
        match compile_named_module_with_context(
            source_name.to_string(),
            source_text.to_string(),
            CompileOptions::default(),
            context,
        ) {
            Ok(compilation) => {
                let fresh = certificate_from_compilation(&compilation, source_text);
                let field_diffs = diff_certificates(supplied, &fresh);
                if field_diffs.is_empty() {
                    rederivation_ok = true;
                } else {
                    differences.extend(field_diffs);
                }
            }
            Err(err) => {
                differences.push(format!(
                    "rederivation failed: source no longer compiles cleanly under compiler {current_compiler_version} ({} diagnostics)",
                    err.diagnostics().len()
                ));
            }
        }
    }

    // Step 29 (axis-5 fifth touch): policy-gate check. For each
    // effect the caller forbade via `--forbid-effect <NAME>`, check
    // if it appears in the cert's `effects_required`. Any intersection
    // fails verification — the cert claims an effect the deployment
    // context bans.
    let forbidden_effects_present: Vec<String> = forbidden_effects
        .iter()
        .filter(|forbidden| supplied.effects_required.iter().any(|e| e == *forbidden))
        .cloned()
        .collect();
    for forbidden in &forbidden_effects_present {
        differences.push(format!(
            "forbidden_effect_present: `{forbidden}` is in cert.effects_required but was forbidden by --forbid-effect"
        ));
    }

    // Axis-5 ninth touch: positive whitelist gate. When the caller
    // supplied any `--allow-effect <NAME>`, the verification step
    // enforces that EVERY effect in the cert's `effects_required`
    // appears in the allowlist; any cert effect NOT in the allowlist
    // fails. An empty `allowed_effects` slice means the gate is
    // INACTIVE (silent — no policy supplied), not "no effects
    // allowed"; deployment contexts that want to reject any effect
    // entirely should use `--forbid-effect` per known-bad name, or
    // supply an allowlist of permitted effects (which by
    // construction excludes everything else).
    let unauthorized_effects_present: Vec<String> = if allowed_effects.is_empty() {
        Vec::new()
    } else {
        supplied
            .effects_required
            .iter()
            .filter(|required| !allowed_effects.iter().any(|a| a == *required))
            .cloned()
            .collect()
    };
    for unauthorized in &unauthorized_effects_present {
        differences.push(format!(
            "unauthorized_effect_present: `{unauthorized}` is in cert.effects_required but was not allowlisted by --allow-effect"
        ));
    }

    // P0-a: a `solver_verified: true` witness is confirmed ONLY by a successful
    // re-derivation (which compares it via `diff_certificates`). Because
    // `solver_verified` and `compiler_version` are unfingerprinted cert fields,
    // an attacker can set the witness `true` AND change `compiler_version` so
    // re-derivation is skipped — dodging the diff and passing `all_ok()`. Reject
    // an unconfirmed `true` claim. When re-derivation was ATTEMPTED and failed,
    // `diff_certificates` already emitted the precise mismatch; only surface the
    // skip case here to avoid a duplicate line.
    let solver_claim_ok = !supplied.capability.solver_verified || rederivation_ok;
    if !solver_claim_ok && !rederivation_attempted {
        differences.push(format!(
            "capability.solver_verified: cert claims `true` but the witness could \
             not be confirmed (re-derivation was skipped: {}). An unsigned cert's \
             self-reported solver witness is not trusted — rejected.",
            if !compiler_version_match {
                "compiler_version differs from this binary"
            } else {
                "prerequisite checks did not pass"
            }
        ));
    }

    let context_rederivation_ok = context.host_profile().is_none() || rederivation_ok;
    if !context_rederivation_ok && !rederivation_attempted {
        differences
            .push("profile-aware certificate checking requires fresh rederivation".to_owned());
    }

    VerifyResult {
        schema_ok,
        hash_ok,
        bytes_ok,
        compiler_version_match,
        rederivation_attempted,
        rederivation_ok,
        solver_claim_ok,
        wasm_inner_match,
        forbidden_effects_present,
        unauthorized_effects_present,
        differences,
        context_rederivation_ok,
        supplied_compiler_version: supplied.compiler_version.clone(),
        current_compiler_version,
    }
}

// ---------------------------------------------------------------------------
// Certificate gate — strict-mode helper used by `sigil run --cert` and
// `sigil forge --cert` (iteration 36 of Spec A + E). Distinct from the
// `verify_certificate` reporter above: the reporter accepts schema v2 with
// a deprecation warning and downgrades gracefully on missing input; the
// gate accepts v3 only, requires WASM bytes non-optionally, and reports
// each failure class as a distinct R-code (R810-R816).
// ---------------------------------------------------------------------------

/// Cap on cert file size — refuses to parse arbitrary blobs as cert JSON.
/// Real certs are well under 10 KB; 1 MB is a generous upper bound for any
/// foreseeable program. Folded in from adversarial-review fix MI-3.
pub(crate) const CERT_FILE_SIZE_CAP: u64 = 1_048_576;

/// Distinct cert-gate failure classes. Each variant maps 1:1 to a
/// diagnostic code (R810-R816); the `code()` and `message()` methods
/// produce the structured + human-readable payloads. Returning a typed
/// enum from the gate (rather than a multi-field bool struct like
/// `VerifyResult`) makes the failure path uninvocable-via-`&[]`-back-door
/// (adversarial fix MC-1) and tests assertion-on-code instead of
/// substring-on-message (MC-7).
#[derive(Debug)]
pub(crate) enum GateFailure {
    /// R810: cert file does not exist, is not a regular file, or exceeds
    /// CERT_FILE_SIZE_CAP. Distinct from R811 (parse failure) so callers
    /// can disambiguate "file shape problem" from "format problem".
    FileShape { path: PathBuf, reason: String },
    /// R811: cert file exists at the filesystem level but its contents do
    /// not parse as cert JSON.
    JsonParse { path: PathBuf, error: String },
    /// R812: cert schema is not v3. The gate refuses pre-v3 schemas
    /// because their fingerprints used FNV-1a-64 which is not collision-
    /// resistant under attacker-chosen source.
    SchemaUnsupported { supplied: u32, expected: u32 },
    /// R813: cert's source_fingerprint does not match the source about to
    /// be compiled. Carries both hashes so the message can show which
    /// way they differ.
    SourceMismatch {
        supplied_hash: String,
        fresh_hash: String,
        supplied_bytes: u64,
        fresh_bytes: u64,
    },
    /// R814: cert's wasm_inner_fingerprint does not match the freshly-
    /// compiled inner WASM. Implies either non-determinism in the
    /// compiler (file a bug) or the cert was emitted from different
    /// source than what's currently being compiled.
    WasmInnerMismatch {
        supplied_hash: String,
        fresh_hash: String,
        supplied_bytes: u64,
        fresh_bytes: u64,
    },
    /// R815: cert's wasm_outer_fingerprint either does not match supplied
    /// outer bytes, or the cert claims outer + supplied is None, or vice
    /// versa. Single message variant carrying all three sub-cases keeps
    /// the diagnostic surface narrow.
    WasmOuterMismatch { reason: String },
    /// R816: bidirectional effect-set mismatch. The cert's effects_required
    /// and the runtime effect set are not equal. Both directions named:
    /// `missing_in_runtime` (cert requires X, runtime doesn't grant it)
    /// and `extra_in_runtime` (runtime grants Y, cert doesn't claim it).
    /// Empty arrays mean no mismatch in that direction.
    EffectsMismatch {
        missing_in_runtime: Vec<String>,
        extra_in_runtime: Vec<String>,
    },
    /// R817: the cert asserts `solver_verified: false` — the Z3 flow-
    /// sensitive proofs (capability flow, refinement discharge) never ran
    /// for this artifact, so only the structural half was checked. The
    /// gate fails closed rather than accept an artifact whose security
    /// obligations were never discharged. Overridable for dev/CI via
    /// `SIGIL_ALLOW_UNVERIFIED_CERT=1`.
    SolverUnverified,
    /// R819: schema-v9 formal evidence is absent or differs from the report
    /// freshly derived by the mandatory linked Lean verifier.
    FormalEvidenceMismatch { reason: String },
}

impl GateFailure {
    pub(crate) fn code(&self) -> sigil_compiler::DiagnosticCode {
        match self {
            Self::FileShape { .. } => codes::R810,
            Self::JsonParse { .. } => codes::R811,
            Self::SchemaUnsupported { .. } => codes::R812,
            Self::SourceMismatch { .. } => codes::R813,
            Self::WasmInnerMismatch { .. } => codes::R814,
            Self::WasmOuterMismatch { .. } => codes::R815,
            Self::EffectsMismatch { .. } => codes::R816,
            Self::SolverUnverified => codes::R817,
            Self::FormalEvidenceMismatch { .. } => codes::R819,
        }
    }

    pub(crate) fn message(&self) -> String {
        match self {
            Self::FileShape { path, reason } => {
                format!("cert file `{}`: {reason}", path.display())
            }
            Self::JsonParse { path, error } => {
                format!("cert JSON parse failure at `{}`: {error}", path.display())
            }
            Self::SchemaUnsupported { supplied, expected } => {
                format!(
                    "cert schema version {supplied} unsupported by gate (expected {expected}); \
                     re-emit with `sigil check <source> --cert <path>`"
                )
            }
            Self::SourceMismatch {
                supplied_hash,
                fresh_hash,
                supplied_bytes,
                fresh_bytes,
            } => {
                format!(
                    "source fingerprint mismatch: supplied hash={supplied_hash} ({supplied_bytes} bytes), \
                     fresh hash={fresh_hash} ({fresh_bytes} bytes)"
                )
            }
            Self::WasmInnerMismatch {
                supplied_hash,
                fresh_hash,
                supplied_bytes,
                fresh_bytes,
            } => {
                format!(
                    "wasm_inner fingerprint mismatch: supplied hash={supplied_hash} ({supplied_bytes} bytes), \
                     fresh hash={fresh_hash} ({fresh_bytes} bytes)"
                )
            }
            Self::WasmOuterMismatch { reason } => {
                format!("wasm_outer fingerprint check failed: {reason}")
            }
            Self::EffectsMismatch {
                missing_in_runtime,
                extra_in_runtime,
            } => {
                let mut parts = Vec::new();
                if !missing_in_runtime.is_empty() {
                    parts.push(format!(
                        "cert requires but runtime lacks: [{}]",
                        missing_in_runtime.join(", ")
                    ));
                }
                if !extra_in_runtime.is_empty() {
                    parts.push(format!(
                        "runtime grants but cert doesn't claim: [{}]",
                        extra_in_runtime.join(", ")
                    ));
                }
                format!("effect set mismatch: {}", parts.join("; "))
            }
            Self::SolverUnverified => {
                "artifact is not solver-verified (solver_verified: false): the Z3 \
                 flow-sensitive proofs (capability flow, refinement discharge) did NOT run \
                 for this artifact — this toolchain was built without the `solver` feature, \
                 so refinement and capability-flow obligations were skipped, not discharged. \
                 The gate fails closed rather than execute or accept unchecked code. Rebuild \
                 with the `solver` feature, or set SIGIL_ALLOW_UNVERIFIED_CERT=1 to proceed \
                 with a structural-only build deliberately."
                    .to_string()
            }
            Self::FormalEvidenceMismatch { reason } => {
                format!("formal security report or CSIR fingerprint mismatch: {reason}")
            }
        }
    }
}

/// Load and deserialize certificate JSON with strict file-shape guards.
/// Every certificate surface, including the package wrapper, goes through
/// this one bounded, open-once path before serde sees attacker-controlled
/// bytes.
fn load_bounded_cert_json<T: serde::de::DeserializeOwned>(
    path: &std::path::Path,
) -> Result<T, GateFailure> {
    use std::io::Read as _;

    let file_shape = |reason: String| GateFailure::FileShape {
        path: path.to_path_buf(),
        reason,
    };

    // Open ONCE, then fstat and read through that same descriptor. The previous
    // `stat(path)` then `read_to_string(path)` re-resolved the path twice, so a
    // local attacker could swap the target between the check and the read
    // (TOCTOU, finding P3). Binding both to one open fd closes that window. On
    // Unix we additionally refuse to follow a symlink at the cert path itself
    // (`O_NOFOLLOW`), removing the swap-in-a-symlink vector entirely.
    let mut opts = fs::OpenOptions::new();
    opts.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        // O_NOFOLLOW: refuse a symlink at the cert path (swap vector).
        // O_NONBLOCK: `open(O_RDONLY)` on a FIFO blocks until a writer connects,
        // so without it a FIFO planted at the --cert path would hang the gate
        // indefinitely (a local DoS) instead of being rejected by the is_file()
        // check below. With O_NONBLOCK the open returns immediately and fstat
        // then rejects the non-regular file.
        opts.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let mut file = opts
        .open(path)
        .map_err(|e| file_shape(format!("cannot open: {e}")))?;

    // fstat the OPEN descriptor — not the path — so these checks bind to
    // exactly the bytes we are about to read.
    let metadata = file
        .metadata()
        .map_err(|e| file_shape(format!("cannot stat: {e}")))?;
    if !metadata.is_file() {
        return Err(file_shape("not a regular file".to_string()));
    }
    if metadata.len() > CERT_FILE_SIZE_CAP {
        return Err(file_shape(format!(
            "file size {} bytes exceeds {} bytes cap",
            metadata.len(),
            CERT_FILE_SIZE_CAP
        )));
    }

    // Read with a hard byte cap regardless of what fstat reported — defence in
    // depth against a source whose length can't be trusted (e.g. a fifo that
    // reports size 0 but would stream forever). Read one byte past the cap so
    // an over-cap file is detected rather than silently truncated.
    let mut buf = Vec::new();
    file.by_ref()
        .take(CERT_FILE_SIZE_CAP + 1)
        .read_to_end(&mut buf)
        .map_err(|e| file_shape(format!("read error: {e}")))?;
    if buf.len() as u64 > CERT_FILE_SIZE_CAP {
        return Err(file_shape(format!(
            "file exceeds {CERT_FILE_SIZE_CAP} bytes cap"
        )));
    }

    let text = String::from_utf8(buf).map_err(|e| file_shape(format!("not valid UTF-8: {e}")))?;
    sigil_compiler::package::deserialize_json_without_duplicate_keys(text.as_bytes()).map_err(|e| {
        GateFailure::JsonParse {
            path: path.to_path_buf(),
            error: e.to_string(),
        }
    })
}

/// Load a base cert JSON file with strict file-shape guards. Closes
/// adversarial fix MI-3: any `--cert <path>` argument must point at a regular
/// file no larger than CERT_FILE_SIZE_CAP. Refuses fifos, sockets, special
/// devices (e.g. `/dev/zero` reading forever) and oversized blobs that would
/// crash the parser with OOM.
pub(crate) fn load_cert_file(
    path: &std::path::Path,
) -> Result<sigil_compiler::certificate::CertificateJson, GateFailure> {
    load_bounded_cert_json(path)
}

fn load_package_cert_file(
    path: &std::path::Path,
) -> Result<sigil_compiler::package::PackageCertificateJson, GateFailure> {
    load_bounded_cert_json(path)
}

/// Whether the run/forge gate must require `solver_verified: true` on the
/// supplied cert. Defaults to `true` (fail closed). An operator can opt out
/// deliberately — for a dev/CI toolchain built without the `solver` feature —
/// by setting `SIGIL_ALLOW_UNVERIFIED_CERT=1`. Any other value (including
/// unset/empty) keeps the gate closed. Read at the call site so the
/// `gate_cert` function itself stays free of ambient environment state.
pub(crate) fn require_solver_verified_from_env() -> bool {
    !matches!(
        std::env::var("SIGIL_ALLOW_UNVERIFIED_CERT").as_deref(),
        Ok("1")
    )
}

/// Verify a cert binds to the supplied (source, wasm_inner, wasm_outer,
/// runtime_effects) tuple. Returns `Ok(())` on full match, `Err(GateFailure)`
/// on any divergence. Strict-mode semantics:
///
/// - Schema must be exactly v9 (older schemas cannot authorize execution — see R812).
/// - `wasm_inner` is non-optional. Closes adversarial fix MC-2 (no
///   `Option<&[u8]>` that silently downgrades on `None`).
/// - `wasm_outer` is required iff `cert.wasm_outer_fingerprint.is_some()`.
///   Bidirectional check: present↔present, absent↔absent. Closes MC-3.
/// - `runtime_effects: Option<&[String]>`:
///     - `None` means "this caller doesn't enforce effect equality"
///       (used by `sigil run`, which has no grant-style flags).
///     - `Some(slice)` triggers a bidirectional check against
///       `cert.effects_required`. Both `slice` and `effects_required`
///       are expected to be sorted+deduplicated. Closes MI-8.
///
/// The first failure short-circuits — only one R-code fires per call.
/// Tests rely on this ordering (e.g. R812 fires before R813 when both
/// would apply).
// Keep the independently optional artifact inputs and the two distinct solver
// verdicts explicit at this security boundary. Bundling them would make it
// easier to confuse caller policy with the freshly derived witness.
#[allow(clippy::too_many_arguments)]
pub(crate) fn gate_cert(
    cert: &sigil_compiler::certificate::CertificateJson,
    source: &[u8],
    wasm_inner: &[u8],
    wasm_outer: Option<&[u8]>,
    runtime_effects: Option<&[String]>,
    require_solver_verified: bool,
    fresh_solver_verified: bool,
    fresh_formal: &sigil_compiler::formal::FormalSecurityReport,
) -> Result<(), GateFailure> {
    use sigil_compiler::certificate::{ArtifactFingerprint, CERTIFICATE_SCHEMA_VERSION};

    if cert.schema_version != CERTIFICATE_SCHEMA_VERSION {
        return Err(GateFailure::SchemaUnsupported {
            supplied: cert.schema_version,
            expected: CERTIFICATE_SCHEMA_VERSION,
        });
    }

    match cert.formal.as_ref() {
        None => {
            return Err(GateFailure::FormalEvidenceMismatch {
                reason: "schema-v9 certificate has no formal report".to_string(),
            });
        }
        Some(claimed) if claimed != fresh_formal => {
            return Err(GateFailure::FormalEvidenceMismatch {
                reason: format!(
                    "supplied CSIR={}, fresh CSIR={}",
                    claimed.csir_fingerprint, fresh_formal.csir_fingerprint
                ),
            });
        }
        Some(_) => {}
    }

    // Fail closed on an unverified artifact (P0). We decide on
    // `fresh_solver_verified` — the value the CURRENT toolchain derived when it
    // re-compiled `source` — and NOT on `cert.capability.solver_verified`.
    //
    // The cert is an unsigned, caller-supplied JSON file; `solver_verified` is
    // NOT covered by the source/wasm fingerprints, so an attacker who controls
    // the cert can flip `false`→`true` and the fingerprint checks below still
    // pass. Trusting the cert's own bit (as the original R817 gate did) is
    // therefore forgeable. Basing the decision on the fresh re-derivation makes
    // the flip inert: a solver-off toolchain derives `false` and fails closed
    // regardless of what the cert claims; a solver-on toolchain derives `true`
    // by actually running the prover. `require_solver_verified` stays threaded
    // from the caller (default `true`; `SIGIL_ALLOW_UNVERIFIED_CERT=1`
    // overrides). `verify_certificate` separately diffs the cert's claimed bit
    // against the fresh one so a tampered witness surfaces as a mismatch.
    if require_solver_verified && !fresh_solver_verified {
        return Err(GateFailure::SolverUnverified);
    }

    // Wall 5 Step 1 / v7: source_fingerprint binds to the framed-concat
    // canonicalization (single-file is N=1). `canonical_source_bytes`
    // dispatches on `cert.schema_version` — v3-v6 keep raw bytes,
    // v7+ apply the `\x00 + name + \x00 + text` framing.
    let canonical = cert.canonical_source_bytes(source);
    let fresh_source = ArtifactFingerprint::new(&canonical);
    if cert.source_fingerprint.hash != fresh_source.hash
        || cert.source_fingerprint.bytes != fresh_source.bytes
    {
        return Err(GateFailure::SourceMismatch {
            supplied_hash: cert.source_fingerprint.hash.clone(),
            fresh_hash: fresh_source.hash,
            supplied_bytes: cert.source_fingerprint.bytes,
            fresh_bytes: fresh_source.bytes,
        });
    }

    let fresh_inner = ArtifactFingerprint::new(wasm_inner);
    if cert.wasm_inner_fingerprint.hash != fresh_inner.hash
        || cert.wasm_inner_fingerprint.bytes != fresh_inner.bytes
    {
        return Err(GateFailure::WasmInnerMismatch {
            supplied_hash: cert.wasm_inner_fingerprint.hash.clone(),
            fresh_hash: fresh_inner.hash,
            supplied_bytes: cert.wasm_inner_fingerprint.bytes,
            fresh_bytes: fresh_inner.bytes,
        });
    }

    match (&cert.wasm_outer_fingerprint, wasm_outer) {
        (Some(claimed), Some(bytes)) => {
            let fresh = ArtifactFingerprint::new(bytes);
            if claimed.hash != fresh.hash || claimed.bytes != fresh.bytes {
                return Err(GateFailure::WasmOuterMismatch {
                    reason: format!(
                        "supplied hash={} ({} bytes), fresh hash={} ({} bytes)",
                        claimed.hash, claimed.bytes, fresh.hash, fresh.bytes
                    ),
                });
            }
        }
        (Some(_), None) => {
            return Err(GateFailure::WasmOuterMismatch {
                reason: "cert claims wasm_outer_fingerprint but no outer WASM was supplied"
                    .to_string(),
            });
        }
        (None, Some(_)) => {
            return Err(GateFailure::WasmOuterMismatch {
                reason: "outer WASM bytes were supplied but cert does not claim a wasm_outer_fingerprint"
                    .to_string(),
            });
        }
        (None, None) => {}
    }

    if let Some(runtime) = runtime_effects {
        let (missing_in_runtime, extra_in_runtime) =
            effect_set_difference(&cert.effects_required, runtime);
        if !missing_in_runtime.is_empty() || !extra_in_runtime.is_empty() {
            return Err(GateFailure::EffectsMismatch {
                missing_in_runtime,
                extra_in_runtime,
            });
        }
    }

    Ok(())
}

fn effect_set_difference(required: &[String], available: &[String]) -> (Vec<String>, Vec<String>) {
    let mut missing: Vec<String> = required
        .iter()
        .filter(|effect| !available.contains(effect))
        .cloned()
        .collect();
    let mut extra: Vec<String> = available
        .iter()
        .filter(|effect| !required.contains(effect))
        .cloned()
        .collect();
    missing.sort();
    extra.sort();
    (missing, extra)
}

/// Emit a `GateFailure` as a diagnostic and bail. JSON mode emits a
/// structured envelope via `emit_generic_error`; human mode prints
/// `error: <code>: <message>` to stderr. Either way, the caller's
/// `anyhow::Result` becomes `Err`.
pub(crate) fn emit_gate_failure(
    kind: CommandKind,
    fmt: OutputFormat,
    failure: GateFailure,
) -> anyhow::Result<()> {
    let code = failure.code();
    let message = failure.message();
    if fmt.is_json() {
        json_envelope::emit_generic_error(kind.json_name(), code, message.clone());
    } else {
        eprintln!("error: {}: {message}", code.as_str());
    }
    bail!("cert gate failed ({})", code.as_str());
}

/// Effects the CLI controls via grant flags on `sigil forge`. Other
/// effects in the language (`Alloc`, `Time`, `Random`, `FFI`, `Unsafe`)
/// are either implicit (granted unconditionally at runtime) or gated by
/// `#[trusted]` at the source level, not by CLI flags. Bidirectional
/// effects check on forge operates on this subset only — over/under-grant
/// on these two effects is what the user can actually control.
///
/// Iteration 38 of Spec A + E (axis-5 seventh touch). Folded-in fix MI-8.
pub(crate) const CLI_GATED_EFFECTS: &[&str] = &["FsIO", "NetIO"];

/// Derive the set of CLI-controlled effects that the user is granting on
/// this forge invocation. `fs_roots` non-empty grants `FsIO`; `net_hosts`
/// non-empty grants `NetIO`. Output is sorted + deduplicated for the
/// symmetric diff in `gate_forge_grants`.
pub(crate) fn grants_to_effect_set(fs_roots: &[PathBuf], net_hosts: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    if !fs_roots.is_empty() {
        out.push("FsIO".to_string());
    }
    if !net_hosts.is_empty() {
        out.push("NetIO".to_string());
    }
    out.sort();
    out
}

/// Bidirectional grant check for `sigil forge --cert`. Folded-in fix
/// MI-8: catches both over-grant (runtime grants effects the cert
/// doesn't claim) AND under-grant (cert requires effects the runtime
/// doesn't grant). Filters both sides to `CLI_GATED_EFFECTS` so
/// implicit effects (Alloc, Time, Random) don't appear as spurious
/// mismatches.
///
/// Returns `Ok(())` if the CLI-controlled effects match exactly,
/// `Err(GateFailure::EffectsMismatch)` otherwise. The error names both
/// directions for clarity.
pub(crate) fn gate_forge_grants(
    cert_effects_required: &[String],
    fs_roots: &[PathBuf],
    net_hosts: &[String],
) -> Result<(), GateFailure> {
    let runtime: Vec<String> = grants_to_effect_set(fs_roots, net_hosts);
    let mut cert_filtered: Vec<String> = cert_effects_required
        .iter()
        .filter(|e| CLI_GATED_EFFECTS.contains(&e.as_str()))
        .cloned()
        .collect();
    cert_filtered.sort();

    let (missing_in_runtime, extra_in_runtime) = effect_set_difference(&cert_filtered, &runtime);

    if missing_in_runtime.is_empty() && extra_in_runtime.is_empty() {
        Ok(())
    } else {
        Err(GateFailure::EffectsMismatch {
            missing_in_runtime,
            extra_in_runtime,
        })
    }
}

pub(crate) fn run_verify_cert(
    command: &VerifyCertCommand,
    fmt: OutputFormat,
    context: &CompilerContext,
) -> anyhow::Result<()> {
    use sigil_compiler::certificate::CertificateJson;

    let cert_path = &command.cert_path;
    if let Some(package_root) = &command.package_root {
        let supplied = match load_package_cert_file(cert_path) {
            Ok(certificate) => certificate,
            Err(failure) => {
                return emit_gate_failure(CommandKind::VerifyCert, fmt, failure);
            }
        };
        match sigil_compiler::package::verify_local_package_certificate_with_context(
            package_root,
            &supplied,
            CompileOptions::default(),
            context,
        ) {
            Ok(fresh) => {
                if fmt.is_json() {
                    Envelope::ok(
                        CommandKind::VerifyCert.json_name(),
                        json!({
                            "cert_path": cert_path.display().to_string(),
                            "package_root": package_root.display().to_string(),
                            "root_package": fresh.graph.root_package,
                            "package_graph_hash": fresh.graph.graph_hash,
                            "verified": true,
                        }),
                    )
                    .emit();
                } else {
                    println!(
                        "verify-cert: OK ({} ↔ package {})",
                        cert_path.display(),
                        fresh.graph.root_package
                    );
                }
                return Ok(());
            }
            Err(sigil_compiler::package::PackageCompileError::Package(error))
                if error.code == "E_SOLVER_UNVERIFIED" =>
            {
                return emit_gate_failure(
                    CommandKind::VerifyCert,
                    fmt,
                    GateFailure::SolverUnverified,
                );
            }
            Err(error) => {
                if fmt.is_json() {
                    Envelope::error_with_data(
                        CommandKind::VerifyCert.json_name(),
                        Vec::new(),
                        json!({
                            "cert_path": cert_path.display().to_string(),
                            "package_root": package_root.display().to_string(),
                            "verified": false,
                            "error": error.to_string(),
                        }),
                    )
                    .emit();
                    bail!("package certificate mismatch");
                }
                bail!("package certificate mismatch: {error}");
            }
        }
    }
    let cert_bytes = fs::read(cert_path)
        .with_context(|| format!("failed to read certificate `{}`", cert_path.display()))?;
    let supplied: CertificateJson = serde_json::from_slice(&cert_bytes)
        .with_context(|| format!("failed to parse certificate `{}`", cert_path.display()))?;

    // Step 22: optionally hash a WASM artifact and verify it against
    // the cert's wasm_inner_fingerprint. When --wasm is provided this
    // is the deployment-time check: pipeline holds the binary + the
    // cert, no source required.
    let wasm_inner_bytes = command
        .wasm_path
        .as_ref()
        .map(|p| fs::read(p).with_context(|| format!("failed to read wasm file `{}`", p.display())))
        .transpose()?;

    let result = verify_certificate_with_context(
        &supplied,
        &command.source_name,
        &command.source_text,
        wasm_inner_bytes.as_deref(),
        &command.forbidden_effects,
        &command.allowed_effects,
        context,
    );
    let all_ok = result.all_ok();

    if fmt.is_json() {
        let data = json!({
            "cert_path": cert_path.display().to_string(),
            "source_path": command.source_name,
            "wasm_path": command.wasm_path.as_ref().map(|p| p.display().to_string()),
            "schema_version_ok": result.schema_ok,
            "fingerprint_ok": result.hash_ok && result.bytes_ok,
            "wasm_inner_match": result.wasm_inner_match,
            "compiler_version_match": result.compiler_version_match,
            "rederivation_attempted": result.rederivation_attempted,
            "rederivation_ok": result.rederivation_ok,
            "forbidden_effects_requested": command.forbidden_effects,
            "forbidden_effects_present": result.forbidden_effects_present,
            "allowed_effects_requested": command.allowed_effects,
            "unauthorized_effects_present": result.unauthorized_effects_present,
            "differences": result.differences,
            "supplied_compiler_version": result.supplied_compiler_version,
            "current_compiler_version": result.current_compiler_version,
        });
        if all_ok {
            Envelope::ok(CommandKind::VerifyCert.json_name(), data).emit();
        } else {
            let diag_message = if result.differences.is_empty() {
                "verification failed".to_string()
            } else {
                format!(
                    "verification failed:\n  - {}",
                    result.differences.join("\n  - ")
                )
            };
            json_envelope::emit_generic_error_with_data(
                CommandKind::VerifyCert.json_name(),
                codes::R809,
                diag_message,
                data,
            );
        }
    } else if all_ok {
        println!(
            "verify-cert: OK ({} ↔ {})",
            cert_path.display(),
            command.source_name
        );
        if !result.compiler_version_match {
            println!(
                "  note: cert compiler_version={} differs from current={}; rederivation skipped",
                result.supplied_compiler_version, result.current_compiler_version
            );
        }
    } else {
        eprintln!(
            "verify-cert: MISMATCH ({} ↔ {})",
            cert_path.display(),
            command.source_name
        );
        for diff in result.differences.iter() {
            eprintln!("  - {diff}");
        }
    }

    if all_ok {
        Ok(())
    } else {
        bail!("verification failed")
    }
}

/// Compare every field of two certificates except non-deterministic
/// stats: `z3_rlimit_consumed` (Z3's reported usage varies slightly
/// between runs even on identical input) and `z3_cache_hits` /
/// `z3_cache_misses` (axis-2 eighth touch: depend on cache warmup
/// state — first compile is all misses, second is mostly hits, but
/// the verdict is identical). Returns a list of human-readable diff
/// lines; empty if all compared fields match.
fn diff_certificates(
    supplied: &sigil_compiler::certificate::CertificateJson,
    fresh: &sigil_compiler::certificate::CertificateJson,
) -> Vec<String> {
    let mut diffs = Vec::new();
    if supplied.source_name != fresh.source_name {
        diffs.push(format!(
            "source_name: supplied={:?}, fresh={:?}",
            supplied.source_name, fresh.source_name
        ));
    }
    if supplied.primary_module != fresh.primary_module {
        diffs.push(format!(
            "primary_module: supplied={:?}, fresh={:?}",
            supplied.primary_module, fresh.primary_module
        ));
    }
    if supplied.module_names != fresh.module_names {
        diffs.push(format!(
            "module_names: supplied={:?}, fresh={:?}",
            supplied.module_names, fresh.module_names
        ));
    }
    if supplied.capability.verified_functions != fresh.capability.verified_functions {
        diffs.push(format!(
            "capability.verified_functions: supplied={}, fresh={}",
            supplied.capability.verified_functions, fresh.capability.verified_functions
        ));
    }
    if supplied.capability.checked_blocks != fresh.capability.checked_blocks {
        diffs.push(format!(
            "capability.checked_blocks: supplied={}, fresh={}",
            supplied.capability.checked_blocks, fresh.capability.checked_blocks
        ));
    }
    if supplied.capability.checked_sites != fresh.capability.checked_sites {
        diffs.push(format!(
            "capability.checked_sites: supplied={}, fresh={}",
            supplied.capability.checked_sites, fresh.capability.checked_sites
        ));
    }
    if supplied.ownership != fresh.ownership {
        diffs.push(format!(
            "ownership: supplied={:?}, fresh={:?}",
            supplied.ownership, fresh.ownership
        ));
    }
    if supplied.formal != fresh.formal {
        diffs.push(format!(
            "formal: supplied={:?}, fresh={:?}",
            supplied.formal, fresh.formal
        ));
    }
    if supplied.effects_required != fresh.effects_required {
        diffs.push(format!(
            "effects_required: supplied={:?}, fresh={:?}",
            supplied.effects_required, fresh.effects_required
        ));
    }
    // P0: the `solver_verified` witness MUST be re-derived and compared. It is
    // not covered by the source/wasm fingerprints, so an attacker who edits the
    // cert file can flip it `false`→`true` and every other field still matches.
    // Diffing it against the freshly re-compiled cert makes such tampering
    // surface as a verify-cert MISMATCH instead of a silent `OK`.
    if supplied.capability.solver_verified != fresh.capability.solver_verified {
        diffs.push(format!(
            "capability.solver_verified: supplied={}, fresh={}",
            supplied.capability.solver_verified, fresh.capability.solver_verified
        ));
    }
    diffs
}

#[cfg(test)]
mod verify_cert_tests {
    //! Unit tests for the verify-cert subcommand's pure verification core.
    //!
    //! Step 17 (axis 5) added `sigil verify-cert` to make the verification
    //! certificate load-bearing. These tests pin the behavior so a future
    //! regression to the cert format or the fingerprint algorithm flips a
    //! red light here before it ships.
    //!
    //! Each test constructs an in-memory cert + source and calls
    //! `verify_certificate` directly. No file I/O, no subprocesses — keeps
    //! the test fast and deterministic.
    use super::*;
    use sigil_compiler::certificate::CertificateJson;

    /// A trivially-compileable Sigil program. Picked because it produces a
    /// non-empty certificate (a primary module name, capability/ownership
    /// reports with non-zero counts).
    const HAPPY_SOURCE: &str = "module sigil;\ncap type Fuel {}\nentry actor Main { state { fuel: Fuel } on Start() -> i64 { return 1; } }\n";

    fn fresh_cert(source: &str) -> CertificateJson {
        let compilation = compile_named_module("happy.sigil".to_string(), source.to_string())
            .expect("HAPPY_SOURCE compiles");
        CertificateJson::new(
            compilation.source_name.clone(),
            source,
            &compilation.wasm_inner,
            compilation.wasm_outer.as_deref(),
            compilation.primary_module_name().map(str::to_owned),
            compilation.module_names.clone(),
            &compilation.capability_report,
            &compilation.ownership_report,
            &compilation.formal_security_report,
            compilation.effects_required.clone(),
        )
    }

    /// A cert paired with the exact source that produced it must verify.
    #[test]
    fn happy_path_verifies() {
        let cert = fresh_cert(HAPPY_SOURCE);
        let result = verify_certificate(&cert, "happy.sigil", HAPPY_SOURCE, None, &[], &[]);
        assert!(result.all_ok(), "differences: {:?}", result.differences);
        assert!(result.rederivation_attempted);
        assert!(result.rederivation_ok);
    }

    #[test]
    fn profile_context_rederives_the_exact_model_nine_report_and_rejects_drift() {
        use sigil_compiler::compiler_context::HostContractProfile;
        let first_context = CompilerContext::with_host_profile(
            HostContractProfile::new("cli-context".into(), 1, vec![], vec![])
                .expect("an empty named profile is structurally valid"),
        );
        let first = compile_named_module_with_context(
            "happy.sigil".to_owned(),
            HAPPY_SOURCE.to_owned(),
            CompileOptions::default(),
            &first_context,
        )
        .expect("the Public fixture compiles under an explicit host profile");
        assert_eq!(first.formal_security_report.model_version, 9);
        let cert = certificate_from_compilation(&first, HAPPY_SOURCE);
        assert_eq!(cert.schema_version, 9);

        let exact = verify_certificate_with_context(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            Some(&first.wasm_inner),
            &[],
            &[],
            &first_context,
        );
        assert!(exact.rederivation_attempted);
        assert!(
            exact.rederivation_ok,
            "differences: {:?}",
            exact.differences
        );
        assert!(exact.context_rederivation_ok);
        assert!(exact.all_ok(), "differences: {:?}", exact.differences);

        let changed_context = CompilerContext::with_host_profile(
            HostContractProfile::new("cli-context".into(), 2, vec![], vec![])
                .expect("the changed profile is structurally valid"),
        );
        let changed = compile_named_module_with_context(
            "happy.sigil".to_owned(),
            HAPPY_SOURCE.to_owned(),
            CompileOptions::default(),
            &changed_context,
        )
        .expect("the same source also compiles under the changed profile");
        assert_eq!(changed.formal_security_report.model_version, 9);
        assert_eq!(
            first.formal_security_report.checker_source_fingerprint,
            changed.formal_security_report.checker_source_fingerprint,
            "only the checked CSIR input, not the linked checker, changed",
        );
        assert_ne!(
            first.formal_security_report.csir_fingerprint,
            changed.formal_security_report.csir_fingerprint,
            "canonical host declarations must participate in the production CSIR fingerprint",
        );

        let drift = verify_certificate_with_context(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            Some(&first.wasm_inner),
            &[],
            &[],
            &changed_context,
        );
        assert!(drift.rederivation_attempted);
        assert!(!drift.rederivation_ok);
        assert!(!drift.context_rederivation_ok);
        assert!(!drift.all_ok());
        assert!(
            drift
                .differences
                .iter()
                .any(|difference| difference.starts_with("formal:")),
            "the exact freshly derived model-9 report must be compared: {:?}",
            drift.differences,
        );

        // A caller cannot turn the explicit-profile requirement into a
        // report-only check by making the compiler identity suppress fresh
        // derivation. Keep this independent of the solver-witness fence.
        let mut skipped_cert = cert;
        skipped_cert.capability = sigil_compiler::certificate::CapabilityReportJson {
            solver_verified: false,
            ..skipped_cert.capability.clone()
        };
        skipped_cert.compiler_version = "different-compiler".to_owned();
        let skipped = verify_certificate_with_context(
            &skipped_cert,
            "happy.sigil",
            HAPPY_SOURCE,
            Some(&first.wasm_inner),
            &[],
            &[],
            &first_context,
        );
        assert!(!skipped.rederivation_attempted);
        assert!(skipped.solver_claim_ok);
        assert!(!skipped.context_rederivation_ok);
        assert!(!skipped.all_ok());
        assert!(skipped.differences.iter().any(|difference| difference
            == "profile-aware certificate checking requires fresh rederivation"));
    }

    /// Tampering with the source (even a single byte) must break the
    /// fingerprint check. This is the core trust property — without it,
    /// anyone could pair any cert with any source.
    #[test]
    fn tampered_source_breaks_fingerprint() {
        let cert = fresh_cert(HAPPY_SOURCE);
        let tampered = HAPPY_SOURCE.replace("return 1;", "return 2;");
        let result = verify_certificate(&cert, "happy.sigil", &tampered, None, &[], &[]);
        assert!(!result.all_ok());
        assert!(!result.hash_ok);
        assert!(
            result.differences.iter().any(|d| d.contains("hash")),
            "should report hash mismatch; got {:?}",
            result.differences
        );
        // Re-derivation should be skipped because hash already failed.
        assert!(!result.rederivation_attempted);
    }

    /// A cert with a different recorded source size also breaks the
    /// fingerprint check independently of the hash. This catches a forge
    /// attempt that engineers a hash collision but forgets to update
    /// `bytes`.
    #[test]
    fn tampered_bytes_breaks_fingerprint() {
        let mut cert = fresh_cert(HAPPY_SOURCE);
        cert.source_fingerprint.bytes += 1;
        let result = verify_certificate(&cert, "happy.sigil", HAPPY_SOURCE, None, &[], &[]);
        assert!(!result.all_ok());
        assert!(!result.bytes_ok);
    }

    /// A cert claiming a future schema_version must be refused (we don't
    /// know how to interpret it).
    #[test]
    fn unknown_schema_version_refused() {
        let mut cert = fresh_cert(HAPPY_SOURCE);
        cert.schema_version = u32::MAX;
        let result = verify_certificate(&cert, "happy.sigil", HAPPY_SOURCE, None, &[], &[]);
        assert!(!result.all_ok());
        assert!(!result.schema_ok);
        // Re-derivation should not be attempted — schema mismatch is fatal.
        assert!(!result.rederivation_attempted);
    }

    /// A cert with a different (compatible-schema) compiler_version must
    /// still pass the fingerprint check, but skip re-derivation. The
    /// `compiler_version_match` flag should reflect this so audit pipelines
    /// can decide whether to trust the fingerprint-only check.
    #[test]
    fn different_compiler_version_skips_rederivation_but_can_pass() {
        let mut cert = fresh_cert(HAPPY_SOURCE);
        // Pin the witness to an honest `false` (struct literal, not
        // `solver_verified =` — grep-safe, mirroring the forged-witness test
        // below). On a solver-on build — e.g. a plain local `cargo test
        // --workspace`, where feature unification links a solver-on
        // sigil-compiler even though CI runs --no-default-features —
        // `fresh_cert` records `true`, and an unconfirmed TRUE claim with
        // re-derivation dodged is exactly what the solver_claim_ok gate
        // rejects. This test's subject is fingerprint-only verification, not
        // the witness gate, so make the claim honest under BOTH feature
        // resolutions; an honest `false` always passes solver_claim_ok.
        cert.capability = sigil_compiler::certificate::CapabilityReportJson {
            solver_verified: false,
            ..cert.capability.clone()
        };
        cert.compiler_version = "9.9.9-not-this-build".to_string();
        let result = verify_certificate(&cert, "happy.sigil", HAPPY_SOURCE, None, &[], &[]);
        // Hash + schema still match, so fingerprint passes.
        assert!(result.hash_ok);
        assert!(result.bytes_ok);
        assert!(result.schema_ok);
        // But compiler version differs and re-derivation is skipped.
        assert!(!result.compiler_version_match);
        assert!(!result.rederivation_attempted);
        // Overall verdict: passes (fingerprint-only mode).
        assert!(result.all_ok());
    }

    /// A cert whose recorded field counts diverge from what the compiler
    /// re-derives (e.g. cert claims more verified functions than actually
    /// exist) must fail re-derivation.
    #[test]
    fn forged_field_counts_break_rederivation() {
        let mut cert = fresh_cert(HAPPY_SOURCE);
        cert.capability.verified_functions += 7;
        let result = verify_certificate(&cert, "happy.sigil", HAPPY_SOURCE, None, &[], &[]);
        assert!(!result.all_ok());
        assert!(result.rederivation_attempted);
        assert!(!result.rederivation_ok);
        assert!(
            result
                .differences
                .iter()
                .any(|d| d.contains("verified_functions")),
            "differences: {:?}",
            result.differences
        );
    }

    #[test]
    fn verify_cert_rejects_forged_solver_verified_when_rederivation_skipped() {
        // The audit's escalation of the forgery: flip solver_verified false→true
        // AND edit the unfingerprinted `compiler_version` so re-derivation — the
        // ONLY place the witness is diffed (diff_certificates) — is skipped. The
        // source/wasm fingerprints still match (genuine source), so schema/hash/
        // bytes all pass. Without the solver_claim_ok gate, `all_ok()` would
        // return true and `verify-cert` would print OK for a forged witness.
        let mut forged = fresh_cert(HAPPY_SOURCE);
        // Grep-safe (struct literal, not `solver_verified =`): forge the witness.
        forged.capability = sigil_compiler::certificate::CapabilityReportJson {
            solver_verified: true,
            ..forged.capability.clone()
        };
        // Dodge re-derivation: any compiler_version != this binary's.
        forged.compiler_version = "0.0.0-forged".to_owned();

        let result = verify_certificate(&forged, "happy.sigil", HAPPY_SOURCE, None, &[], &[]);
        assert!(
            !result.rederivation_attempted,
            "a compiler_version mismatch must skip re-derivation (the dodge)"
        );
        assert!(
            !result.all_ok(),
            "an unconfirmed forged solver_verified must NOT verify OK: {:?}",
            result.differences
        );
        assert!(
            result
                .differences
                .iter()
                .any(|d| d.contains("solver_verified")),
            "the rejection must name solver_verified; got {:?}",
            result.differences
        );
    }

    #[test]
    fn verify_cert_honest_unverified_cert_still_ok() {
        // A cert honestly recording solver_verified:false (the normal solver-off
        // artifact) must still verify OK — the new gate only rejects an
        // unconfirmed `true` CLAIM, not an honest `false`.
        let cert = fresh_cert(HAPPY_SOURCE); // solver-off test build → solver_verified:false
        let result = verify_certificate(&cert, "happy.sigil", HAPPY_SOURCE, None, &[], &[]);
        assert!(
            result.all_ok(),
            "honest solver_verified:false must verify OK: {:?}",
            result.differences
        );
    }

    /// Step 22: a cert paired with its matching WASM bytes verifies
    /// at the WASM layer too. `wasm_inner_match` is Some(true).
    #[test]
    fn matching_wasm_bytes_verify() {
        let compilation = compile_named_module("wasm.sigil".to_string(), HAPPY_SOURCE.to_string())
            .expect("compiles");
        let cert = fresh_cert(HAPPY_SOURCE);
        let result = verify_certificate(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            Some(&compilation.wasm_inner),
            &[],
            &[],
        );
        assert!(result.all_ok(), "differences: {:?}", result.differences);
        assert_eq!(result.wasm_inner_match, Some(true));
    }

    /// Step 22: a cert paired with tampered WASM (any byte changed)
    /// fails the WASM-fingerprint check. This is the deployment-time
    /// trust handover: if the binary was modified after cert issuance,
    /// verification rejects it even if the cert and source match.
    #[test]
    fn tampered_wasm_bytes_break_verification() {
        let compilation = compile_named_module("wasm.sigil".to_string(), HAPPY_SOURCE.to_string())
            .expect("compiles");
        let cert = fresh_cert(HAPPY_SOURCE);
        let mut tampered_wasm = compilation.wasm_inner.clone();
        // Flip the last byte — any single-bit change must be detected.
        if let Some(last) = tampered_wasm.last_mut() {
            *last = last.wrapping_add(1);
        }
        let result = verify_certificate(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            Some(&tampered_wasm),
            &[],
            &[],
        );
        assert!(!result.all_ok());
        assert_eq!(result.wasm_inner_match, Some(false));
        assert!(
            result
                .differences
                .iter()
                .any(|d| d.contains("wasm_inner_fingerprint")),
            "expected wasm_inner_fingerprint diff; got: {:?}",
            result.differences
        );
    }

    /// Step 22: omitting WASM bytes keeps `wasm_inner_match` as None
    /// (downgrade to source-only verification, not a failure). This
    /// preserves backward compatibility for verify-cert callers that
    /// don't have the binary on hand.
    #[test]
    fn missing_wasm_is_source_only_verification() {
        let cert = fresh_cert(HAPPY_SOURCE);
        let result = verify_certificate(&cert, "happy.sigil", HAPPY_SOURCE, None, &[], &[]);
        assert!(result.all_ok());
        assert_eq!(result.wasm_inner_match, None);
    }

    /// Step 29: a cert that doesn't claim any effects passes even when
    /// --forbid-effect names something. The gate only fires on actual
    /// intersection.
    #[test]
    fn forbid_effect_passes_when_cert_has_no_matching_effect() {
        // HAPPY_SOURCE has no effect declarations — effects_required is
        // empty. Forbidding `NetIO` is a no-op.
        let cert = fresh_cert(HAPPY_SOURCE);
        assert!(
            cert.effects_required.is_empty(),
            "precondition: HAPPY_SOURCE produces no required effects"
        );
        let result = verify_certificate(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            None,
            &["NetIO".to_string()],
            &[],
        );
        assert!(result.all_ok(), "differences: {:?}", result.differences);
        assert!(result.forbidden_effects_present.is_empty());
    }

    /// Step 29: a cert that claims a forbidden effect fails the gate.
    /// The deployment-time use case: a pipeline gates on
    /// `--forbid-effect NetIO` and a tool that requires `NetIO`
    /// produces a cert that fails to verify, blocking deployment.
    #[test]
    fn forbid_effect_fails_when_cert_claims_forbidden_effect() {
        // Construct a cert with an effect in `effects_required` (synthesize
        // it directly — we don't need to compile a source that has the
        // effect; we just need a cert whose effects_required contains
        // the name we're forbidding).
        let mut cert = fresh_cert(HAPPY_SOURCE);
        cert.effects_required = vec!["NetIO".to_string()];
        let result = verify_certificate(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            None,
            &["NetIO".to_string()],
            &[],
        );
        assert!(!result.all_ok());
        assert_eq!(result.forbidden_effects_present, vec!["NetIO".to_string()]);
        assert!(
            result
                .differences
                .iter()
                .any(|d| d.contains("NetIO") && d.contains("forbidden")),
            "expected NetIO + forbidden in differences; got: {:?}",
            result.differences
        );
    }

    /// Step 29: multiple --forbid-effect flags accumulate; the gate
    /// surfaces every intersection (not just the first one) so a
    /// deployment pipeline gets the complete violation list in one
    /// pass.
    #[test]
    fn forbid_effect_accumulates_multiple_violations() {
        let mut cert = fresh_cert(HAPPY_SOURCE);
        cert.effects_required = vec!["NetIO".to_string(), "FFI".to_string(), "Unsafe".to_string()];
        let result = verify_certificate(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            None,
            &["NetIO".to_string(), "FFI".to_string()],
            &[],
        );
        assert!(!result.all_ok());
        assert_eq!(result.forbidden_effects_present.len(), 2);
        assert!(
            result
                .forbidden_effects_present
                .contains(&"NetIO".to_string())
        );
        assert!(
            result
                .forbidden_effects_present
                .contains(&"FFI".to_string())
        );
        // `Unsafe` was in effects_required but NOT in the forbid list,
        // so it shouldn't appear in the violation report.
        assert!(
            !result
                .forbidden_effects_present
                .contains(&"Unsafe".to_string())
        );
    }

    /// Axis-5 ninth touch: empty `--allow-effect` slice means the gate
    /// is INACTIVE. Even with synthesized cert effects (which fail
    /// rederivation), the allow-effect gate itself produces no
    /// violations — isolation of gate mechanics from other checks.
    #[test]
    fn allow_effect_inactive_when_no_allowlist_supplied() {
        let mut cert = fresh_cert(HAPPY_SOURCE);
        cert.effects_required = vec!["NetIO".to_string(), "Alloc".to_string()];
        let result = verify_certificate(&cert, "happy.sigil", HAPPY_SOURCE, None, &[], &[]);
        // The allow-effect gate is silent (empty allowlist = gate off).
        assert!(
            result.unauthorized_effects_present.is_empty(),
            "empty allowlist must produce zero unauthorized effects; got {:?}",
            result.unauthorized_effects_present
        );
    }

    /// Axis-5 ninth touch: empty cert effects + non-empty allowlist
    /// passes (the allowlist's upper bound is trivially satisfied by
    /// the empty set).
    #[test]
    fn allow_effect_passes_when_cert_has_no_effects() {
        let cert = fresh_cert(HAPPY_SOURCE);
        assert!(
            cert.effects_required.is_empty(),
            "precondition: HAPPY_SOURCE produces no required effects"
        );
        let result = verify_certificate(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            None,
            &[],
            &["NetIO".to_string(), "Alloc".to_string()],
        );
        assert!(result.all_ok(), "differences: {:?}", result.differences);
        assert!(result.unauthorized_effects_present.is_empty());
    }

    /// Axis-5 ninth touch: every cert effect is in the allowlist →
    /// gate produces no violations. The deployment-context use case:
    /// "I'm willing to run programs that need at most NetIO + Alloc —
    /// and this program does." Synthesized cert effects fail
    /// rederivation, but the allow-effect gate is isolated and silent.
    #[test]
    fn allow_effect_passes_when_all_cert_effects_in_allowlist() {
        let mut cert = fresh_cert(HAPPY_SOURCE);
        cert.effects_required = vec!["NetIO".to_string()];
        let result = verify_certificate(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            None,
            &[],
            &["NetIO".to_string(), "Alloc".to_string()],
        );
        // Gate-specific assertion: NetIO is allowlisted, so no
        // unauthorized effects.
        assert!(
            result.unauthorized_effects_present.is_empty(),
            "all cert effects in allowlist → zero unauthorized; got {:?}",
            result.unauthorized_effects_present
        );
    }

    /// Axis-5 ninth touch: a cert effect NOT in the allowlist fails
    /// the gate. The complement of `--forbid-effect`'s use case:
    /// instead of naming each forbidden effect, enumerate the small
    /// set tolerated and reject anything outside.
    #[test]
    fn allow_effect_fails_when_cert_has_unauthorized_effect() {
        let mut cert = fresh_cert(HAPPY_SOURCE);
        cert.effects_required = vec!["Alloc".to_string()];
        let result = verify_certificate(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            None,
            &[],
            &["NetIO".to_string()],
        );
        assert!(!result.all_ok());
        assert_eq!(
            result.unauthorized_effects_present,
            vec!["Alloc".to_string()]
        );
        assert!(
            result
                .differences
                .iter()
                .any(|d| d.contains("Alloc") && d.contains("allowlist")),
            "expected Alloc + allowlist in differences; got: {:?}",
            result.differences
        );
    }

    /// Axis-5 ninth touch: multiple unauthorized effects all surface
    /// in one pass (parallel to forbid-effect's accumulation behavior).
    #[test]
    fn allow_effect_accumulates_multiple_unauthorized() {
        let mut cert = fresh_cert(HAPPY_SOURCE);
        cert.effects_required = vec!["NetIO".to_string(), "FFI".to_string(), "Unsafe".to_string()];
        let result = verify_certificate(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            None,
            &[],
            &["NetIO".to_string()],
        );
        assert!(!result.all_ok());
        assert_eq!(result.unauthorized_effects_present.len(), 2);
        assert!(
            result
                .unauthorized_effects_present
                .contains(&"FFI".to_string())
        );
        assert!(
            result
                .unauthorized_effects_present
                .contains(&"Unsafe".to_string())
        );
        // `NetIO` was in effects_required AND in the allowlist, so it
        // shouldn't appear in the violation report.
        assert!(
            !result
                .unauthorized_effects_present
                .contains(&"NetIO".to_string())
        );
    }

    /// Axis-5 ninth touch: forbid and allow gates compose — a cert
    /// can fail BOTH (forbidden effect present AND unauthorized
    /// effect present), and both lists must populate in one pass.
    /// Useful when a deployment context uses allowlist as the
    /// baseline but forbids a specific subset more loudly.
    #[test]
    fn forbid_and_allow_gates_compose() {
        let mut cert = fresh_cert(HAPPY_SOURCE);
        cert.effects_required = vec!["NetIO".to_string(), "Alloc".to_string()];
        let result = verify_certificate(
            &cert,
            "happy.sigil",
            HAPPY_SOURCE,
            None,
            &["NetIO".to_string()],
            &["Alloc".to_string()],
        );
        assert!(!result.all_ok());
        // NetIO is BOTH forbidden AND in effects_required → forbidden_effects_present.
        assert_eq!(result.forbidden_effects_present, vec!["NetIO".to_string()]);
        // NetIO is also unauthorized (not in allowlist), even though it's
        // also forbidden. The two gates are independent.
        assert!(
            result
                .unauthorized_effects_present
                .contains(&"NetIO".to_string())
        );
    }
}

#[cfg(test)]
mod gate_tests {
    //! Unit tests for the strict-mode cert gate (iteration 36 of Spec A + E).
    //!
    //! Distinct from `verify_cert_tests` above: the gate has strict-mode
    //! semantics (schema v3 only, non-optional wasm_inner, bidirectional
    //! effects check). Each test asserts on `GateFailure` variants and
    //! their `code()` mapping to R810-R816 — never on substring of the
    //! human-readable message. Tests that need actual files on disk use
    //! `std::env::temp_dir()` with PID + nanosecond-suffixed names for
    //! parallel-safe isolation.
    use super::*;
    use sigil_abi::host_contract::{
        HostContractProfile, HostOperationContract, HostValueContract, HostValueType,
        OccurrenceVisibility, SecurityLabel,
    };
    use sigil_compiler::certificate::{
        ArtifactFingerprint, CERTIFICATE_SCHEMA_VERSION, CertificateJson,
    };

    /// Same HAPPY_SOURCE as verify_cert_tests but inlined here to keep
    /// this module's tests self-contained.
    const HAPPY_SOURCE: &str = "module sigil;\ncap type Fuel {}\nentry actor Main { state { fuel: Fuel } on Start() -> i64 { return 1; } }\n";

    fn fresh_compilation() -> sigil_compiler::Compilation {
        compile_named_module("gate.sigil".to_string(), HAPPY_SOURCE.to_string())
            .expect("HAPPY_SOURCE compiles")
    }

    fn fresh_cert(compilation: &sigil_compiler::Compilation) -> CertificateJson {
        CertificateJson::new(
            compilation.source_name.clone(),
            HAPPY_SOURCE,
            &compilation.wasm_inner,
            compilation.wasm_outer.as_deref(),
            compilation.primary_module_name().map(str::to_owned),
            compilation.module_names.clone(),
            &compilation.capability_report,
            &compilation.ownership_report,
            &compilation.formal_security_report,
            compilation.effects_required.clone(),
        )
    }

    fn occurrence_context(occurrence: OccurrenceVisibility) -> CompilerContext {
        let operation = HostOperationContract {
            module: "ffi".to_owned(),
            name: "tick".to_owned(),
            occurrence,
            params: vec![HostValueContract {
                ty: HostValueType::I64,
                label: SecurityLabel::Public,
            }],
            results: vec![HostValueContract {
                ty: HostValueType::I64,
                label: SecurityLabel::Internal,
            }],
            domains: vec![],
        };
        CompilerContext::with_host_profile(
            HostContractProfile::new("cert-occurrence".to_owned(), 1, vec![], vec![operation])
                .expect("the occurrence fixture is a valid canonical host profile"),
        )
    }

    /// A synthetic version-1 reserved requirement, not compiler-produced
    /// host approval. Both lengths fit one unsigned-LEB byte; the payload is
    /// the ABI's fixed little-endian version followed by a 32-byte digest.
    fn with_test_host_profile(wasm: &[u8], fingerprint: u8) -> Vec<u8> {
        const NAME: &[u8] = b"sigil.host-profile";
        let mut tagged = wasm.to_vec();
        tagged.extend_from_slice(&[
            0,
            u8::try_from(1 + NAME.len() + 36).expect("test section fits one LEB byte"),
            u8::try_from(NAME.len()).expect("test section name fits one LEB byte"),
        ]);
        tagged.extend_from_slice(NAME);
        tagged.extend_from_slice(&1_u32.to_le_bytes());
        tagged.extend_from_slice(&[fingerprint; 32]);
        wasmprinter::print_bytes(&tagged)
            .expect("synthetic custom section must preserve a parseable Wasm module");
        tagged
    }

    /// Return `cert` with its `solver_verified` witness set to `verified`,
    /// using struct-literal construction (`solver_verified:`) rather than field
    /// assignment. The grep-pin
    /// `z3_guard_fences::solver_verified_has_exactly_one_assignment_site`
    /// reserves the `solver_verified =` assignment form for the single
    /// production site (capability::verify), so tests must not use it.
    fn with_solver_verified(mut cert: CertificateJson, verified: bool) -> CertificateJson {
        cert.capability = sigil_compiler::certificate::CapabilityReportJson {
            solver_verified: verified,
            ..cert.capability.clone()
        };
        cert
    }

    /// Temp file path with a unique suffix so parallel tests don't collide.
    fn unique_temp_path(stem: &str, ext: &str) -> PathBuf {
        use std::time::{SystemTime, UNIX_EPOCH};
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let mut p = std::env::temp_dir();
        p.push(format!("sigil_gate_test_{stem}_{pid}_{nanos}.{ext}"));
        p
    }

    // ── gate_cert: happy path ─────────────────────────────────────────

    #[test]
    fn gate_cert_happy_path_succeeds() {
        let compilation = fresh_compilation();
        let cert = fresh_cert(&compilation);
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            compilation.wasm_outer.as_deref(),
            None,
            false,
            false,
            &compilation.formal_security_report,
        );
        assert!(result.is_ok(), "happy path must succeed: {result:?}");
    }

    // ── gate_cert: solver-verified fail-closed (R817) ────────────────
    // P0 (post-512): the gate decides on the FRESHLY-DERIVED solver_verified
    // that the caller passes, NOT on the cert's own bit — that bit is not
    // covered by the source/wasm fingerprints and is attacker-forgeable. These
    // tests pin that the fresh value is authoritative and a forged cert bit is
    // inert either way.

    #[test]
    fn gate_cert_fails_closed_when_fresh_unverified_even_if_cert_claims_true() {
        // The forgery from the audit: the cert CLAIMS solver_verified = true,
        // but the current toolchain derived false. The gate must still refuse.
        let compilation = fresh_compilation();
        let cert = with_solver_verified(fresh_cert(&compilation), true);
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            compilation.wasm_outer.as_deref(),
            None,
            true,  // require_solver_verified
            false, // fresh_solver_verified — the unforgeable truth
            &compilation.formal_security_report,
        );
        match result {
            Err(failure @ GateFailure::SolverUnverified) => {
                assert_eq!(failure.code(), codes::R817);
            }
            other => panic!("a forged cert bit must not bypass the gate; got {other:?}"),
        }
    }

    #[test]
    fn gate_cert_passes_when_fresh_verified_even_if_cert_claims_false() {
        // Mirror: the cert claims false, but the current toolchain actually
        // verified it. The fresh value wins, so the gate passes.
        let compilation = fresh_compilation();
        let cert = with_solver_verified(fresh_cert(&compilation), false);
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            compilation.wasm_outer.as_deref(),
            None,
            true, // require_solver_verified
            true, // fresh_solver_verified
            &compilation.formal_security_report,
        );
        assert!(
            result.is_ok(),
            "a fresh-verified artifact must pass regardless of the cert bit: {result:?}"
        );
    }

    #[test]
    fn gate_cert_override_accepts_unverified() {
        // Explicit dev/CI opt-out (SIGIL_ALLOW_UNVERIFIED_CERT=1 →
        // require_solver_verified = false): an unverified artifact is accepted.
        let compilation = fresh_compilation();
        let cert = fresh_cert(&compilation);
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            compilation.wasm_outer.as_deref(),
            None,
            false, // require_solver_verified (override)
            false, // fresh_solver_verified
            &compilation.formal_security_report,
        );
        assert!(
            result.is_ok(),
            "override must accept an unverified artifact: {result:?}"
        );
    }

    // ── gate_cert: schema (R812) ─────────────────────────────────────

    #[test]
    fn gate_cert_legacy_schema_emits_r812() {
        let compilation = fresh_compilation();
        let mut cert = fresh_cert(&compilation);
        cert.schema_version = CERTIFICATE_SCHEMA_VERSION - 1; // legacy v8
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            compilation.wasm_outer.as_deref(),
            None,
            false,
            false,
            &compilation.formal_security_report,
        );
        match result {
            Err(GateFailure::SchemaUnsupported { supplied, expected }) => {
                assert_eq!(supplied, CERTIFICATE_SCHEMA_VERSION - 1);
                assert_eq!(expected, CERTIFICATE_SCHEMA_VERSION);
                assert_eq!(
                    GateFailure::SchemaUnsupported { supplied, expected }.code(),
                    codes::R812
                );
            }
            other => panic!("expected SchemaUnsupported (R812); got {other:?}"),
        }
    }

    #[test]
    fn gate_cert_missing_formal_report_emits_r819() {
        let compilation = fresh_compilation();
        let mut cert = fresh_cert(&compilation);
        cert.formal = None;
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            compilation.wasm_outer.as_deref(),
            None,
            false,
            false,
            &compilation.formal_security_report,
        );
        match result {
            Err(failure @ GateFailure::FormalEvidenceMismatch { .. }) => {
                assert_eq!(failure.code(), codes::R819);
            }
            other => panic!("expected FormalEvidenceMismatch (R819); got {other:?}"),
        }
    }

    #[test]
    fn gate_cert_tampered_csir_fingerprint_emits_r819() {
        let compilation = fresh_compilation();
        let mut cert = fresh_cert(&compilation);
        cert.formal
            .as_mut()
            .expect("fresh v9 certificate has formal evidence")
            .csir_fingerprint = "00".repeat(32);
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            compilation.wasm_outer.as_deref(),
            None,
            false,
            false,
            &compilation.formal_security_report,
        );
        match result {
            Err(failure @ GateFailure::FormalEvidenceMismatch { .. }) => {
                assert_eq!(failure.code(), codes::R819);
            }
            other => panic!("expected FormalEvidenceMismatch (R819); got {other:?}"),
        }
    }

    #[test]
    fn gate_cert_rejects_every_changed_native_formal_report_field() {
        let compilation = fresh_compilation();
        let clean = fresh_cert(&compilation);
        let check = |cert: &CertificateJson| {
            gate_cert(
                cert,
                HAPPY_SOURCE.as_bytes(),
                &compilation.wasm_inner,
                compilation.wasm_outer.as_deref(),
                None,
                false,
                compilation.capability_report.solver_verified,
                &compilation.formal_security_report,
            )
        };
        check(&clean).expect("the unchanged native report must pass its accept twin");
        for field in [
            "model_version",
            "lean_toolchain",
            "checker_source_fingerprint",
            "csir_fingerprint",
            "checked_functions",
            "checked_nodes",
            "checked_capabilities",
            "checked_flows",
            "checked_releases",
            "checked_ct_operations",
        ] {
            let mut changed = clean.clone();
            let report = changed
                .formal
                .as_mut()
                .expect("the freshly compiled certificate contains native evidence");
            match field {
                "model_version" => report.model_version += 1,
                "lean_toolchain" => report.lean_toolchain.push_str("-changed"),
                "checker_source_fingerprint" => report.checker_source_fingerprint.push('0'),
                "csir_fingerprint" => report.csir_fingerprint.push('0'),
                "checked_functions" => report.checked_functions += 1,
                "checked_nodes" => report.checked_nodes += 1,
                "checked_capabilities" => report.checked_capabilities += 1,
                "checked_flows" => report.checked_flows += 1,
                "checked_releases" => report.checked_releases += 1,
                "checked_ct_operations" => report.checked_ct_operations += 1,
                _ => unreachable!("the field list above is exhaustive"),
            }
            let failure = check(&changed)
                .expect_err("changed native evidence must fail before artifact execution");
            assert!(matches!(
                failure,
                GateFailure::FormalEvidenceMismatch { .. }
            ));
            assert_eq!(failure.code(), codes::R819, "changed field {field}");
        }
    }

    #[test]
    fn gate_cert_rejects_changed_host_occurrence_metadata_as_r819() {
        const SOURCE: &str = r#"
#[ring(outer)] #[trusted]
module cert_occurrence;
extern "C" fn tick(value: i64) -> i64 ! { FFI, Unsafe };
fn run(value: i64) -> i64 @Internal ! { FFI, Unsafe } {
    return tick(value);
}
"#;
        let public_context = occurrence_context(OccurrenceVisibility::Public);
        let private_context = occurrence_context(OccurrenceVisibility::Internal);
        let public = compile_named_module_with_context(
            "cert_occurrence.sigil".to_owned(),
            SOURCE.to_owned(),
            CompileOptions::default(),
            &public_context,
        )
        .expect("the Public-occurrence declaration must pass production v9");
        let private = compile_named_module_with_context(
            "cert_occurrence.sigil".to_owned(),
            SOURCE.to_owned(),
            CompileOptions::default(),
            &private_context,
        )
        .expect("the Internal-occurrence declaration must pass production v9");

        assert_eq!(public.formal_security_report.model_version, 9);
        assert_eq!(private.formal_security_report.model_version, 9);
        assert_eq!(
            public.formal_security_report.checker_source_fingerprint,
            private.formal_security_report.checker_source_fingerprint,
            "the linked checker is identical across the two declarations",
        );
        assert_ne!(
            public.formal_security_report.csir_fingerprint,
            private.formal_security_report.csir_fingerprint,
            "changing only the host occurrence contract must change canonical production CSIR",
        );

        let cert = certificate_from_compilation(&public, SOURCE);
        assert_eq!(cert.schema_version, 9);
        gate_cert(
            &cert,
            SOURCE.as_bytes(),
            &public.wasm_inner,
            public.wasm_outer.as_deref(),
            None,
            false,
            public.capability_report.solver_verified,
            &public.formal_security_report,
        )
        .expect("the exact model-9 report and artifact must pass their accept twin");

        let failure = gate_cert(
            &cert,
            SOURCE.as_bytes(),
            &public.wasm_inner,
            public.wasm_outer.as_deref(),
            None,
            false,
            private.capability_report.solver_verified,
            &private.formal_security_report,
        )
        .expect_err("a different occurrence declaration must not reuse the earlier certificate");
        assert!(matches!(
            failure,
            GateFailure::FormalEvidenceMismatch { .. }
        ));
        assert_eq!(failure.code(), codes::R819);
    }

    #[test]
    fn gate_cert_binds_host_profile_addition_change_removal_and_duplicates_in_inner_wasm() {
        let compilation = fresh_compilation();
        let clean = fresh_cert(&compilation);
        let check = |cert: &CertificateJson, wasm: &[u8]| {
            gate_cert(
                cert,
                HAPPY_SOURCE.as_bytes(),
                wasm,
                compilation.wasm_outer.as_deref(),
                None,
                false,
                compilation.capability_report.solver_verified,
                &compilation.formal_security_report,
            )
        };
        check(&clean, &compilation.wasm_inner)
            .expect("the genuine ordinary compilation must pass its certificate gate");

        let tagged = with_test_host_profile(&compilation.wasm_inner, 7);
        let addition = check(&clean, &tagged)
            .expect_err("adding a reserved section changes the certified artifact");
        assert!(matches!(addition, GateFailure::WasmInnerMismatch { .. }));
        assert_eq!(addition.code(), codes::R814);

        // The compiler does not emit this profile-bearing artifact. Bind its
        // bytes explicitly ONLY to isolate the certificate's generic artifact
        // comparison. A matching fingerprint is not host-profile approval:
        // the legacy runtime still refuses the exact matching artifact below.
        let mut synthetic = clean;
        synthetic.wasm_inner_fingerprint = ArtifactFingerprint::new(&tagged);
        check(&synthetic, &tagged)
            .expect("identical synthetic artifact bytes must match the artifact comparator");
        let mut runtime = sigil_runtime::RuntimeHost::new(compilation.fuel_budget);
        assert_eq!(
            runtime
                .bootstrap(&compilation.runtime_module, &tagged)
                .expect_err(
                    "a matching certificate hash cannot approve an unsupported host profile"
                ),
            sigil_runtime::RuntimeError::Wasm {
                message: "host security profile requires contract-bound instantiation".to_owned(),
            }
        );

        for (mutation, bytes) in [
            (
                "changed",
                with_test_host_profile(&compilation.wasm_inner, 8),
            ),
            ("removed", compilation.wasm_inner.clone()),
            ("duplicated", with_test_host_profile(&tagged, 7)),
        ] {
            let failure = check(&synthetic, &bytes)
                .expect_err("a changed reserved requirement must not match its earlier artifact");
            assert!(matches!(failure, GateFailure::WasmInnerMismatch { .. }));
            assert_eq!(failure.code(), codes::R814, "requirement {mutation}");
        }
    }

    #[test]
    fn gate_cert_binds_host_profile_change_removal_and_duplicates_in_outer_wasm() {
        const SOURCE: &str = "#[ring(outer)] module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }";
        let compilation = compile_named_module("outer.sigil", SOURCE)
            .expect("the ordinary outer-ring tool must compile");
        let clean = certificate_from_compilation(&compilation, SOURCE);
        let outer = compilation
            .wasm_outer
            .as_deref()
            .expect("the outer-ring fixture must actually emit an outer artifact");
        let check = |cert: &CertificateJson, wasm: &[u8]| {
            gate_cert(
                cert,
                SOURCE.as_bytes(),
                &compilation.wasm_inner,
                Some(wasm),
                None,
                false,
                compilation.capability_report.solver_verified,
                &compilation.formal_security_report,
            )
        };
        check(&clean, outer).expect("the unchanged outer artifact must pass");
        let tagged = with_test_host_profile(outer, 7);
        let addition = check(&clean, &tagged)
            .expect_err("outer custom sections are included in the artifact fingerprint");
        assert!(matches!(addition, GateFailure::WasmOuterMismatch { .. }));
        assert_eq!(addition.code(), codes::R815);

        // Synthetic artifact-comparator fixture only, not compiler approval of
        // a profile or a new runtime entry point.
        let mut synthetic = clean;
        synthetic.wasm_outer_fingerprint = Some(ArtifactFingerprint::new(&tagged));
        check(&synthetic, &tagged).expect("identical synthetic outer bytes must match");
        for (mutation, bytes) in [
            ("changed", with_test_host_profile(outer, 8)),
            ("removed", outer.to_vec()),
            ("duplicated", with_test_host_profile(&tagged, 7)),
        ] {
            let failure = check(&synthetic, &bytes)
                .expect_err("outer requirement mutation must not match its earlier artifact");
            assert!(matches!(failure, GateFailure::WasmOuterMismatch { .. }));
            assert_eq!(failure.code(), codes::R815, "requirement {mutation}");
        }
    }

    // ── gate_cert: source mismatch (R813) ────────────────────────────

    #[test]
    fn gate_cert_tampered_source_emits_r813() {
        let compilation = fresh_compilation();
        let cert = fresh_cert(&compilation);
        let tampered = format!("{HAPPY_SOURCE}// extra byte\n");
        let result = gate_cert(
            &cert,
            tampered.as_bytes(),
            &compilation.wasm_inner,
            compilation.wasm_outer.as_deref(),
            None,
            false,
            false,
            &compilation.formal_security_report,
        );
        match result {
            Err(failure @ GateFailure::SourceMismatch { .. }) => {
                assert_eq!(failure.code(), codes::R813);
            }
            other => panic!("expected SourceMismatch (R813); got {other:?}"),
        }
    }

    // ── gate_cert: wasm_inner mismatch (R814) ────────────────────────

    #[test]
    fn gate_cert_tampered_wasm_emits_r814() {
        let compilation = fresh_compilation();
        let cert = fresh_cert(&compilation);
        let mut tampered_wasm = compilation.wasm_inner.clone();
        // Mutate any non-magic byte. Wasm prefix is [0,1,2,3] = magic
        // bytes — alter byte 10 which is in the middle of the section
        // payload, safe to flip without breaking module parsing.
        tampered_wasm[10] ^= 0xff;
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &tampered_wasm,
            compilation.wasm_outer.as_deref(),
            None,
            false,
            false,
            &compilation.formal_security_report,
        );
        match result {
            Err(failure @ GateFailure::WasmInnerMismatch { .. }) => {
                assert_eq!(failure.code(), codes::R814);
            }
            other => panic!("expected WasmInnerMismatch (R814); got {other:?}"),
        }
    }

    // ── gate_cert: wasm_outer mismatch (R815) ────────────────────────

    #[test]
    fn gate_cert_outer_supplied_but_cert_doesnt_claim_emits_r815() {
        // HAPPY_SOURCE compiles to a single-module (no outer) program,
        // so its cert has wasm_outer_fingerprint = None. Supplying outer
        // bytes anyway should trigger R815.
        let compilation = fresh_compilation();
        let cert = fresh_cert(&compilation);
        assert!(
            cert.wasm_outer_fingerprint.is_none(),
            "HAPPY_SOURCE should be single-module"
        );
        let fake_outer = vec![0u8; 100];
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            Some(&fake_outer),
            None,
            false,
            false,
            &compilation.formal_security_report,
        );
        match result {
            Err(failure @ GateFailure::WasmOuterMismatch { .. }) => {
                assert_eq!(failure.code(), codes::R815);
            }
            other => panic!("expected WasmOuterMismatch (R815); got {other:?}"),
        }
    }

    #[test]
    fn gate_cert_cert_claims_outer_but_none_supplied_emits_r815() {
        // Construct a synthetic cert that claims a wasm_outer_fingerprint
        // (real two-module programs are larger; we don't need one here —
        // we only test the gate's reaction to the claim-vs-supplied mismatch).
        let compilation = fresh_compilation();
        let mut cert = fresh_cert(&compilation);
        cert.wasm_outer_fingerprint = Some(ArtifactFingerprint::new(b"fake outer"));
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            None,
            None,
            false,
            false,
            &compilation.formal_security_report,
        );
        match result {
            Err(failure @ GateFailure::WasmOuterMismatch { .. }) => {
                assert_eq!(failure.code(), codes::R815);
            }
            other => panic!("expected WasmOuterMismatch (R815); got {other:?}"),
        }
    }

    // ── gate_cert: effects mismatch (R816) ───────────────────────────

    #[test]
    fn gate_cert_effects_equal_succeeds() {
        let compilation = fresh_compilation();
        let mut cert = fresh_cert(&compilation);
        // Set cert.effects_required to a known sorted list, then pass
        // the same list as runtime_effects.
        cert.effects_required = vec!["Alloc".to_string(), "FsIO".to_string()];
        let runtime = vec!["Alloc".to_string(), "FsIO".to_string()];
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            None,
            Some(&runtime),
            false,
            false,
            &compilation.formal_security_report,
        );
        assert!(result.is_ok(), "equal effect sets must pass: {result:?}");
    }

    #[test]
    fn gate_cert_effects_undergrant_emits_r816() {
        let compilation = fresh_compilation();
        let mut cert = fresh_cert(&compilation);
        cert.effects_required = vec!["Alloc".to_string(), "FsIO".to_string()];
        // Runtime grants only Alloc → cert requires FsIO that runtime lacks.
        let runtime = vec!["Alloc".to_string()];
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            None,
            Some(&runtime),
            false,
            false,
            &compilation.formal_security_report,
        );
        match result {
            Err(GateFailure::EffectsMismatch {
                missing_in_runtime,
                extra_in_runtime,
            }) => {
                assert_eq!(missing_in_runtime, vec!["FsIO".to_string()]);
                assert!(extra_in_runtime.is_empty());
            }
            other => panic!("expected EffectsMismatch (R816); got {other:?}"),
        }
    }

    #[test]
    fn gate_cert_effects_overgrant_emits_r816() {
        let compilation = fresh_compilation();
        let mut cert = fresh_cert(&compilation);
        cert.effects_required = vec!["Alloc".to_string()];
        // Runtime grants Alloc + NetIO → cert doesn't claim NetIO.
        let runtime = vec!["Alloc".to_string(), "NetIO".to_string()];
        let result = gate_cert(
            &cert,
            HAPPY_SOURCE.as_bytes(),
            &compilation.wasm_inner,
            None,
            Some(&runtime),
            false,
            false,
            &compilation.formal_security_report,
        );
        match result {
            Err(GateFailure::EffectsMismatch {
                missing_in_runtime,
                extra_in_runtime,
            }) => {
                assert!(missing_in_runtime.is_empty());
                assert_eq!(extra_in_runtime, vec!["NetIO".to_string()]);
            }
            other => panic!("expected EffectsMismatch (R816); got {other:?}"),
        }
    }

    // ── verify-cert: solver_verified tamper detection (P0) ───────────

    #[test]
    fn diff_certificates_flags_forged_solver_verified() {
        // The audit's forgery: flip the cert's `solver_verified` false→true.
        // `verify-cert` re-derives the honest cert and diffs it; that diff MUST
        // include `solver_verified`, or a tampered witness verifies as OK.
        let compilation = fresh_compilation();
        let honest = with_solver_verified(fresh_cert(&compilation), false); // fresh re-derivation
        let forged = with_solver_verified(fresh_cert(&compilation), true); // tampered supplied
        let diffs = diff_certificates(&forged, &honest);
        assert!(
            diffs.iter().any(|d| d.contains("solver_verified")),
            "a forged solver_verified must surface as a diff; got {diffs:?}"
        );
        // Matching witnesses must not spuriously diff.
        let clean = diff_certificates(&honest, &honest);
        assert!(
            !clean.iter().any(|d| d.contains("solver_verified")),
            "identical solver_verified must not diff; got {clean:?}"
        );
    }

    // ── load_cert_file: R810 / R811 ──────────────────────────────────

    #[test]
    fn load_cert_file_missing_emits_r810() {
        let path = unique_temp_path("missing", "cert");
        // Don't create the file.
        let result = load_cert_file(&path);
        match result {
            Err(failure @ GateFailure::FileShape { .. }) => {
                assert_eq!(failure.code(), codes::R810);
            }
            other => panic!("expected FileShape (R810); got {other:?}"),
        }
    }

    #[test]
    fn load_cert_file_too_large_emits_r810() {
        let path = unique_temp_path("toolarge", "cert");
        // Write CERT_FILE_SIZE_CAP + 1 bytes.
        fs::write(&path, vec![b'X'; (CERT_FILE_SIZE_CAP as usize) + 1])
            .expect("can write temp file");
        let result = load_cert_file(&path);
        let _ = fs::remove_file(&path);
        match result {
            Err(GateFailure::FileShape { reason, .. }) => {
                // The reason should mention the size cap, so a future
                // change to the cap surfaces here in addition to the
                // test failing.
                assert!(
                    reason.contains("cap"),
                    "reason should name the cap: {reason}"
                );
                assert_eq!(
                    GateFailure::FileShape {
                        path: path.clone(),
                        reason: reason.clone()
                    }
                    .code(),
                    codes::R810
                );
            }
            other => panic!("expected FileShape (R810); got {other:?}"),
        }
    }

    #[cfg(unix)]
    #[test]
    fn load_cert_file_rejects_symlinked_path() {
        // A cert path that is a symlink must be refused (O_NOFOLLOW). Combined
        // with fstat-on-the-descriptor, this removes the swap-a-symlink vector
        // in the check-then-read TOCTOU.
        let target = unique_temp_path("cert_target", "cert");
        fs::write(&target, b"{}").expect("write target");
        let link = unique_temp_path("cert_link", "cert");
        std::os::unix::fs::symlink(&target, &link).expect("make symlink");

        let result = load_cert_file(&link);
        let _ = fs::remove_file(&link);
        let _ = fs::remove_file(&target);
        match result {
            Err(failure @ GateFailure::FileShape { .. }) => {
                assert_eq!(failure.code(), codes::R810);
            }
            other => panic!("expected FileShape (R810) for a symlinked cert path; got {other:?}"),
        }
    }

    #[test]
    fn load_cert_file_valid_cert_round_trips() {
        // Behaviour-preserving check: the open-once/fstat/capped-read rewrite
        // must still load a well-formed cert. Emit one via the compiler, then
        // load it back through the hardened path.
        let compilation = fresh_compilation();
        let cert = fresh_cert(&compilation);
        let path = unique_temp_path("valid", "cert");
        fs::write(&path, serde_json::to_string(&cert).expect("serialize cert"))
            .expect("write cert");
        let loaded = load_cert_file(&path);
        let _ = fs::remove_file(&path);
        assert!(loaded.is_ok(), "a well-formed cert must load: {loaded:?}");
    }

    #[test]
    fn load_cert_file_invalid_json_emits_r811() {
        let path = unique_temp_path("badjson", "cert");
        fs::write(&path, b"{not valid json").expect("can write temp file");
        let result = load_cert_file(&path);
        let _ = fs::remove_file(&path);
        match result {
            Err(failure @ GateFailure::JsonParse { .. }) => {
                assert_eq!(failure.code(), codes::R811);
            }
            other => panic!("expected JsonParse (R811); got {other:?}"),
        }
    }

    // ── Determinism: same source → same wasm_inner ───────────────────

    /// Closes adversarial-review fix MI-1: the gate's source/wasm
    /// fingerprint equality only means "matching source ⇒ matching cert"
    /// if compilation is a pure function of (source, compiler version).
    /// If a future change introduces a timestamp, randomized HashMap
    /// hasher seed, or other non-determinism into wasm emission, this
    /// test fails immediately with byte-level evidence.
    #[test]
    fn compile_is_deterministic_on_same_source() {
        let c1 = compile_named_module("det.sigil".to_string(), HAPPY_SOURCE.to_string())
            .expect("compiles");
        let c2 = compile_named_module("det.sigil".to_string(), HAPPY_SOURCE.to_string())
            .expect("compiles");
        assert_eq!(
            c1.wasm_inner, c2.wasm_inner,
            "two compiles of the same source must produce byte-identical WASM"
        );
        // And so the fingerprints — which the gate compares — must be
        // identical too.
        let f1 = ArtifactFingerprint::new(&c1.wasm_inner);
        let f2 = ArtifactFingerprint::new(&c2.wasm_inner);
        assert_eq!(f1.hash, f2.hash);
        assert_eq!(f1.bytes, f2.bytes);
    }
}

#[cfg(test)]
mod forge_gate_tests {
    //! Unit tests for the forge-specific grant check (iteration 38 of
    //! Spec A + E, axis-5 seventh touch).
    //!
    //! Distinct from `gate_tests` (which covers the shared `gate_cert`
    //! helper): these tests exercise `grants_to_effect_set` and
    //! `gate_forge_grants` — the bidirectional CLI-controlled-effects
    //! check that forge layers on top of the base gate. Closes
    //! adversarial-review fix MI-8 (grant ⊇ AND ⊆ cert, not just one
    //! direction).
    use super::*;

    // ── grants_to_effect_set ─────────────────────────────────────────

    #[test]
    fn grants_to_effect_set_empty_inputs() {
        let out = grants_to_effect_set(&[], &[]);
        assert!(out.is_empty(), "no grants → no effects: got {out:?}");
    }

    #[test]
    fn grants_to_effect_set_fs_only() {
        let out = grants_to_effect_set(&[PathBuf::from("/tmp")], &[]);
        assert_eq!(out, vec!["FsIO".to_string()]);
    }

    #[test]
    fn grants_to_effect_set_net_only() {
        let out = grants_to_effect_set(&[], &["example.com".to_string()]);
        assert_eq!(out, vec!["NetIO".to_string()]);
    }

    #[test]
    fn grants_to_effect_set_both_sorted() {
        let out = grants_to_effect_set(&[PathBuf::from("/tmp")], &["example.com".to_string()]);
        // Sorted output: FsIO before NetIO alphabetically.
        assert_eq!(out, vec!["FsIO".to_string(), "NetIO".to_string()]);
    }

    // ── gate_forge_grants: matched ───────────────────────────────────

    #[test]
    fn gate_forge_grants_empty_both_sides_succeeds() {
        let result = gate_forge_grants(&[], &[], &[]);
        assert!(
            result.is_ok(),
            "no claims and no grants must pass: {result:?}"
        );
    }

    #[test]
    fn gate_forge_grants_matched_fs_succeeds() {
        let cert_effects = vec!["FsIO".to_string()];
        let result = gate_forge_grants(&cert_effects, &[PathBuf::from("/tmp")], &[]);
        assert!(result.is_ok(), "cert FsIO + --fs must pass: {result:?}");
    }

    #[test]
    fn gate_forge_grants_matched_both_succeeds() {
        let cert_effects = vec!["FsIO".to_string(), "NetIO".to_string()];
        let result = gate_forge_grants(
            &cert_effects,
            &[PathBuf::from("/tmp")],
            &["example.com".to_string()],
        );
        assert!(result.is_ok(), "matching FsIO+NetIO must pass: {result:?}");
    }

    // ── gate_forge_grants: mismatched ────────────────────────────────

    /// Undergrant: cert requires FsIO but no --fs supplied.
    #[test]
    fn gate_forge_grants_undergrant_emits_r816() {
        let cert_effects = vec!["FsIO".to_string()];
        let result = gate_forge_grants(&cert_effects, &[], &[]);
        match result {
            Err(GateFailure::EffectsMismatch {
                missing_in_runtime,
                extra_in_runtime,
            }) => {
                assert_eq!(missing_in_runtime, vec!["FsIO".to_string()]);
                assert!(extra_in_runtime.is_empty());
            }
            other => panic!("expected EffectsMismatch (R816); got {other:?}"),
        }
    }

    /// Overgrant: --fs supplied but cert doesn't claim FsIO.
    #[test]
    fn gate_forge_grants_overgrant_emits_r816() {
        let cert_effects: Vec<String> = vec![];
        let result = gate_forge_grants(&cert_effects, &[PathBuf::from("/tmp")], &[]);
        match result {
            Err(GateFailure::EffectsMismatch {
                missing_in_runtime,
                extra_in_runtime,
            }) => {
                assert!(missing_in_runtime.is_empty());
                assert_eq!(extra_in_runtime, vec!["FsIO".to_string()]);
            }
            other => panic!("expected EffectsMismatch (R816); got {other:?}"),
        }
    }

    /// Both directions: cert requires NetIO but no --net; --fs supplied
    /// but cert doesn't claim FsIO. Single R816 names both.
    #[test]
    fn gate_forge_grants_both_directions_emits_r816() {
        let cert_effects = vec!["NetIO".to_string()];
        let result = gate_forge_grants(&cert_effects, &[PathBuf::from("/tmp")], &[]);
        match result {
            Err(GateFailure::EffectsMismatch {
                missing_in_runtime,
                extra_in_runtime,
            }) => {
                assert_eq!(missing_in_runtime, vec!["NetIO".to_string()]);
                assert_eq!(extra_in_runtime, vec!["FsIO".to_string()]);
            }
            other => panic!("expected EffectsMismatch (R816); got {other:?}"),
        }
    }

    // ── Filter behavior: non-CLI effects don't trigger mismatch ──────

    /// Cert claims Alloc + FFI + Unsafe (all non-CLI-controlled
    /// effects). No --fs / --net. Should pass — these effects are not
    /// gated by CLI flags so they don't enter the comparison.
    #[test]
    fn gate_forge_grants_ignores_non_cli_effects() {
        let cert_effects = vec!["Alloc".to_string(), "FFI".to_string(), "Unsafe".to_string()];
        let result = gate_forge_grants(&cert_effects, &[], &[]);
        assert!(
            result.is_ok(),
            "non-CLI effects in cert + no CLI grants must pass: {result:?}"
        );
    }

    /// Mixed: cert claims Alloc (ignored) + FsIO (CLI), and user passes
    /// --fs (CLI). The Alloc is filtered out; FsIO matches. Pass.
    #[test]
    fn gate_forge_grants_filters_alloc_compares_fsio() {
        let cert_effects = vec!["Alloc".to_string(), "FsIO".to_string()];
        let result = gate_forge_grants(&cert_effects, &[PathBuf::from("/tmp")], &[]);
        assert!(result.is_ok(), "filtered FsIO must match --fs: {result:?}");
    }
}
