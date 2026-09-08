//! Authenticated certificate provenance profile.
//!
//! A SIGIL certificate already binds source, Wasm, policy, and formal evidence.
//! This module adds the optional production-authentication layer around that
//! certificate without changing the base schema: `sigil check --cert ...` can
//! write a signed envelope, and `verify-cert`/execution gates can require a
//! trusted signer and deployment context.

use anyhow::{Context, bail};
use ring::signature::{ED25519, Ed25519KeyPair, KeyPair, UnparsedPublicKey};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_json::json;
use sigil_compiler::certificate::ArtifactFingerprint;

pub(crate) const SIGNED_CERTIFICATE_ENVELOPE_VERSION: u32 = 1;
pub(crate) const AUTHENTICATED_RELEASE_PROFILE: &str = "authenticated-release";
pub(crate) const CERT_PROVENANCE_ALGORITHM_ED25519: &str = "ed25519-v1";
pub(crate) const DEFAULT_CERT_PROVENANCE_CONTEXT: &str = "sigil://local";

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct CertificateSigningOptions {
    pub(crate) signer_id: Option<String>,
    pub(crate) key_seed_hex: Option<String>,
    pub(crate) context: Option<String>,
    pub(crate) issued_at_unix_ms: Option<i64>,
}

impl CertificateSigningOptions {
    pub(crate) fn is_requested(&self) -> bool {
        self.signer_id.is_some()
            || self.key_seed_hex.is_some()
            || self.context.is_some()
            || self.issued_at_unix_ms.is_some()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TrustedSigner {
    pub(crate) signer_id: String,
    pub(crate) public_key_hex: String,
}

impl TrustedSigner {
    pub(crate) fn parse_cli(value: &str) -> anyhow::Result<Self> {
        let (signer_id, public_key_hex) = value.split_once('=').ok_or_else(|| {
            anyhow::anyhow!("--require-cert-provenance requires SIGNER_ID=PUBLIC_KEY_HEX")
        })?;
        if signer_id.is_empty() {
            bail!("--require-cert-provenance signer id must not be empty");
        }
        decode_hex_exact(public_key_hex, 32, "--require-cert-provenance public key")
            .map_err(anyhow::Error::msg)?;
        Ok(Self {
            signer_id: signer_id.to_owned(),
            public_key_hex: public_key_hex.to_owned(),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct CertificateProvenancePolicy {
    pub(crate) trusted_signer: Option<TrustedSigner>,
    pub(crate) expected_context: Option<String>,
    pub(crate) revoked_signers: Vec<String>,
}

impl CertificateProvenancePolicy {
    pub(crate) fn requires_authenticated(&self) -> bool {
        self.trusted_signer.is_some()
            || self.expected_context.is_some()
            || !self.revoked_signers.is_empty()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(crate) struct SignedCertificateEnvelope<T> {
    pub(crate) envelope_version: u32,
    pub(crate) profile: String,
    pub(crate) certificate: T,
    pub(crate) provenance: CertificateProvenance,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(crate) struct CertificateProvenance {
    pub(crate) algorithm: String,
    pub(crate) signer_id: String,
    pub(crate) public_key: String,
    pub(crate) context: String,
    pub(crate) issued_at_unix_ms: i64,
    pub(crate) certificate_payload: ArtifactFingerprint,
    pub(crate) signature: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LoadedCertificate<T> {
    pub(crate) certificate: T,
    pub(crate) provenance: ProvenanceReport,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CertificateDocumentError {
    CertificateJson(String),
    Provenance(String),
}

impl std::fmt::Display for CertificateDocumentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CertificateJson(error) | Self::Provenance(error) => f.write_str(error),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProvenanceReport {
    pub(crate) envelope_present: bool,
    pub(crate) profile: Option<String>,
    pub(crate) algorithm: Option<String>,
    pub(crate) signer_id: Option<String>,
    pub(crate) context: Option<String>,
    pub(crate) certificate_payload_hash: Option<String>,
    pub(crate) signature_verified: bool,
    pub(crate) trusted: bool,
}

impl ProvenanceReport {
    pub(crate) fn unsigned() -> Self {
        Self {
            envelope_present: false,
            profile: None,
            algorithm: None,
            signer_id: None,
            context: None,
            certificate_payload_hash: None,
            signature_verified: false,
            trusted: false,
        }
    }

    pub(crate) fn to_json(&self) -> serde_json::Value {
        json!({
            "envelope_present": self.envelope_present,
            "profile": self.profile,
            "algorithm": self.algorithm,
            "signer_id": self.signer_id,
            "context": self.context,
            "certificate_payload_hash": self.certificate_payload_hash,
            "signature_verified": self.signature_verified,
            "trusted": self.trusted,
        })
    }
}

pub(crate) fn serialize_certificate_document<T>(
    certificate: &T,
    signing: &CertificateSigningOptions,
) -> anyhow::Result<String>
where
    T: Clone + Serialize,
{
    if signing.is_requested() {
        let envelope = sign_certificate(certificate.clone(), signing)?;
        serde_json::to_string_pretty(&envelope).context("failed to serialize signed certificate")
    } else {
        serde_json::to_string_pretty(certificate).context("failed to serialize certificate")
    }
}

pub(crate) fn decode_certificate_document<T>(
    value: serde_json::Value,
    policy: &CertificateProvenancePolicy,
) -> Result<LoadedCertificate<T>, CertificateDocumentError>
where
    T: Clone + DeserializeOwned + Serialize,
{
    if value.get("envelope_version").is_some() {
        let envelope: SignedCertificateEnvelope<T> =
            serde_json::from_value(value).map_err(|error| {
                CertificateDocumentError::Provenance(format!(
                    "signed certificate envelope did not parse: {error}"
                ))
            })?;
        let provenance = verify_signed_envelope(&envelope, policy)
            .map_err(CertificateDocumentError::Provenance)?;
        return Ok(LoadedCertificate {
            certificate: envelope.certificate,
            provenance,
        });
    }

    let certificate: T = serde_json::from_value(value).map_err(|error| {
        CertificateDocumentError::CertificateJson(format!(
            "certificate JSON did not parse: {error}"
        ))
    })?;
    if policy.requires_authenticated() {
        return Err(CertificateDocumentError::Provenance(
            "authenticated certificate provenance is required, but the certificate is unsigned"
                .to_owned(),
        ));
    }
    Ok(LoadedCertificate {
        certificate,
        provenance: ProvenanceReport::unsigned(),
    })
}

fn sign_certificate<T>(
    certificate: T,
    signing: &CertificateSigningOptions,
) -> anyhow::Result<SignedCertificateEnvelope<T>>
where
    T: Serialize,
{
    let signer_id = signing
        .signer_id
        .as_ref()
        .filter(|value| !value.is_empty())
        .context("--cert-signer is required when certificate signing is requested")?;
    let key_seed_hex = signing
        .key_seed_hex
        .as_ref()
        .context("--cert-sign-key-hex is required when certificate signing is requested")?;
    let key_seed =
        decode_hex_exact(key_seed_hex, 32, "--cert-sign-key-hex").map_err(anyhow::Error::msg)?;
    let key_pair = Ed25519KeyPair::from_seed_unchecked(&key_seed)
        .map_err(|_| anyhow::anyhow!("--cert-sign-key-hex is not a valid Ed25519 seed"))?;
    let public_key = hex_encode(key_pair.public_key().as_ref());
    let context = signing
        .context
        .clone()
        .unwrap_or_else(|| DEFAULT_CERT_PROVENANCE_CONTEXT.to_owned());
    let issued_at_unix_ms = signing
        .issued_at_unix_ms
        .unwrap_or_else(current_time_millis);
    let certificate_payload = certificate_payload_fingerprint(&certificate)?;
    let payload = provenance_signing_bytes(ProvenanceSigningInput {
        envelope_version: SIGNED_CERTIFICATE_ENVELOPE_VERSION,
        profile: AUTHENTICATED_RELEASE_PROFILE,
        algorithm: CERT_PROVENANCE_ALGORITHM_ED25519,
        signer_id,
        public_key: &public_key,
        context: &context,
        issued_at_unix_ms,
        certificate_payload: &certificate_payload,
    });
    let signature = hex_encode(key_pair.sign(&payload).as_ref());

    Ok(SignedCertificateEnvelope {
        envelope_version: SIGNED_CERTIFICATE_ENVELOPE_VERSION,
        profile: AUTHENTICATED_RELEASE_PROFILE.to_owned(),
        certificate,
        provenance: CertificateProvenance {
            algorithm: CERT_PROVENANCE_ALGORITHM_ED25519.to_owned(),
            signer_id: signer_id.clone(),
            public_key,
            context,
            issued_at_unix_ms,
            certificate_payload,
            signature,
        },
    })
}

fn verify_signed_envelope<T>(
    envelope: &SignedCertificateEnvelope<T>,
    policy: &CertificateProvenancePolicy,
) -> Result<ProvenanceReport, String>
where
    T: Serialize,
{
    if envelope.envelope_version != SIGNED_CERTIFICATE_ENVELOPE_VERSION {
        return Err(format!(
            "signed certificate envelope version {} unsupported (expected {})",
            envelope.envelope_version, SIGNED_CERTIFICATE_ENVELOPE_VERSION
        ));
    }
    if envelope.profile != AUTHENTICATED_RELEASE_PROFILE {
        return Err(format!(
            "signed certificate profile `{}` unsupported (expected `{}`)",
            envelope.profile, AUTHENTICATED_RELEASE_PROFILE
        ));
    }
    if envelope.provenance.algorithm != CERT_PROVENANCE_ALGORITHM_ED25519 {
        return Err(format!(
            "certificate provenance algorithm `{}` unsupported (expected `{}`)",
            envelope.provenance.algorithm, CERT_PROVENANCE_ALGORITHM_ED25519
        ));
    }

    let fresh_payload = certificate_payload_fingerprint(&envelope.certificate)
        .map_err(|error| format!("certificate payload could not be canonicalized: {error}"))?;
    if envelope.provenance.certificate_payload != fresh_payload {
        return Err(format!(
            "certificate payload hash mismatch: signed={} ({} bytes), fresh={} ({} bytes)",
            envelope.provenance.certificate_payload.hash,
            envelope.provenance.certificate_payload.bytes,
            fresh_payload.hash,
            fresh_payload.bytes
        ));
    }

    if policy
        .revoked_signers
        .iter()
        .any(|revoked| revoked == &envelope.provenance.signer_id)
    {
        return Err(format!(
            "certificate signer `{}` is revoked by the active provenance policy",
            envelope.provenance.signer_id
        ));
    }
    if let Some(expected_context) = &policy.expected_context
        && &envelope.provenance.context != expected_context
    {
        return Err(format!(
            "certificate provenance context mismatch: signed={:?}, expected={:?}",
            envelope.provenance.context, expected_context
        ));
    }
    let trusted = if let Some(trusted) = &policy.trusted_signer {
        if envelope.provenance.signer_id != trusted.signer_id {
            return Err(format!(
                "certificate signer mismatch: signed={:?}, expected={:?}",
                envelope.provenance.signer_id, trusted.signer_id
            ));
        }
        if envelope.provenance.public_key != trusted.public_key_hex {
            return Err(format!(
                "certificate public key mismatch for signer `{}`",
                trusted.signer_id
            ));
        }
        true
    } else {
        false
    };

    let public_key = decode_hex_exact(&envelope.provenance.public_key, 32, "public_key")?;
    let signature = decode_hex_exact(&envelope.provenance.signature, 64, "signature")?;
    let payload = provenance_signing_bytes(ProvenanceSigningInput {
        envelope_version: envelope.envelope_version,
        profile: &envelope.profile,
        algorithm: &envelope.provenance.algorithm,
        signer_id: &envelope.provenance.signer_id,
        public_key: &envelope.provenance.public_key,
        context: &envelope.provenance.context,
        issued_at_unix_ms: envelope.provenance.issued_at_unix_ms,
        certificate_payload: &envelope.provenance.certificate_payload,
    });
    UnparsedPublicKey::new(&ED25519, public_key)
        .verify(&payload, &signature)
        .map_err(|_| "certificate provenance signature did not verify".to_owned())?;

    Ok(ProvenanceReport {
        envelope_present: true,
        profile: Some(envelope.profile.clone()),
        algorithm: Some(envelope.provenance.algorithm.clone()),
        signer_id: Some(envelope.provenance.signer_id.clone()),
        context: Some(envelope.provenance.context.clone()),
        certificate_payload_hash: Some(envelope.provenance.certificate_payload.hash.clone()),
        signature_verified: true,
        trusted,
    })
}

fn certificate_payload_fingerprint<T>(certificate: &T) -> anyhow::Result<ArtifactFingerprint>
where
    T: Serialize,
{
    let bytes =
        serde_json::to_vec(certificate).context("failed to canonicalize certificate payload")?;
    Ok(ArtifactFingerprint::new(&bytes))
}

struct ProvenanceSigningInput<'a> {
    envelope_version: u32,
    profile: &'a str,
    algorithm: &'a str,
    signer_id: &'a str,
    public_key: &'a str,
    context: &'a str,
    issued_at_unix_ms: i64,
    certificate_payload: &'a ArtifactFingerprint,
}

fn provenance_signing_bytes(input: ProvenanceSigningInput<'_>) -> Vec<u8> {
    let mut out = b"SIGIL-CERT-PROVENANCE\0v1".to_vec();
    push_frame(
        &mut out,
        "envelope_version",
        input.envelope_version.to_string().as_bytes(),
    );
    push_frame(&mut out, "profile", input.profile.as_bytes());
    push_frame(&mut out, "algorithm", input.algorithm.as_bytes());
    push_frame(&mut out, "signer_id", input.signer_id.as_bytes());
    push_frame(&mut out, "public_key", input.public_key.as_bytes());
    push_frame(&mut out, "context", input.context.as_bytes());
    push_frame(
        &mut out,
        "issued_at_unix_ms",
        input.issued_at_unix_ms.to_string().as_bytes(),
    );
    push_frame(
        &mut out,
        "certificate_payload.algorithm",
        input.certificate_payload.algorithm.as_bytes(),
    );
    push_frame(
        &mut out,
        "certificate_payload.bytes",
        input.certificate_payload.bytes.to_string().as_bytes(),
    );
    push_frame(
        &mut out,
        "certificate_payload.hash",
        input.certificate_payload.hash.as_bytes(),
    );
    out
}

fn push_frame(out: &mut Vec<u8>, label: &str, value: &[u8]) {
    out.extend_from_slice(label.as_bytes());
    out.push(0);
    out.extend_from_slice(&(value.len() as u64).to_be_bytes());
    out.extend_from_slice(value);
}

fn current_time_millis() -> i64 {
    let millis = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_millis())
        .unwrap_or(0);
    i64::try_from(millis).unwrap_or(i64::MAX)
}

fn decode_hex_exact(value: &str, expected_bytes: usize, label: &str) -> Result<Vec<u8>, String> {
    if value.len() != expected_bytes * 2 {
        return Err(format!(
            "{label} must be {} lowercase hex characters",
            expected_bytes * 2
        ));
    }
    if !value
        .bytes()
        .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(format!(
            "{label} must be canonical lowercase hex with no prefix, separators, or whitespace"
        ));
    }
    let mut out = Vec::with_capacity(expected_bytes);
    for index in (0..value.len()).step_by(2) {
        let byte = u8::from_str_radix(&value[index..index + 2], 16)
            .map_err(|error| format!("{label} has invalid hex: {error}"))?;
        out.push(byte);
    }
    Ok(out)
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(char::from(HEX[(byte >> 4) as usize]));
        out.push(char::from(HEX[(byte & 0x0f) as usize]));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use sigil_compiler::certificate::CertificateJson;

    const TEST_SEED_A: &str = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";
    const TEST_SEED_B: &str = "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100";

    fn certificate() -> CertificateJson {
        let compilation = sigil_compiler::compile_named_module(
            "signed.sigil".to_owned(),
            "module sigil; fn boot() -> i64 { return 7; }".to_owned(),
        )
        .expect("fixture compiles");
        CertificateJson::new(
            compilation.source_name.clone(),
            "module sigil; fn boot() -> i64 { return 7; }",
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

    fn signing(seed: &str) -> CertificateSigningOptions {
        CertificateSigningOptions {
            signer_id: Some("sigil-ci".to_owned()),
            key_seed_hex: Some(seed.to_owned()),
            context: Some("sigil://release/linux-x86_64".to_owned()),
            issued_at_unix_ms: Some(1_804_000_000_000),
        }
    }

    fn public_key(seed: &str) -> String {
        let key_seed = decode_hex_exact(seed, 32, "test seed").expect("test seed is valid");
        let key_pair = Ed25519KeyPair::from_seed_unchecked(&key_seed).expect("test key builds");
        hex_encode(key_pair.public_key().as_ref())
    }

    fn policy(seed: &str) -> CertificateProvenancePolicy {
        CertificateProvenancePolicy {
            trusted_signer: Some(TrustedSigner {
                signer_id: "sigil-ci".to_owned(),
                public_key_hex: public_key(seed),
            }),
            expected_context: Some("sigil://release/linux-x86_64".to_owned()),
            revoked_signers: Vec::new(),
        }
    }

    fn signed_value(seed: &str) -> serde_json::Value {
        serde_json::from_str(
            &serialize_certificate_document(&certificate(), &signing(seed))
                .expect("signing succeeds"),
        )
        .expect("signed envelope is JSON")
    }

    #[test]
    fn signed_envelope_accepts_trusted_signer_and_context() {
        let loaded: LoadedCertificate<CertificateJson> =
            decode_certificate_document(signed_value(TEST_SEED_A), &policy(TEST_SEED_A))
                .expect("trusted provenance verifies");
        assert_eq!(loaded.certificate.source_name, "signed.sigil");
        assert!(loaded.provenance.envelope_present);
        assert!(loaded.provenance.signature_verified);
        assert!(loaded.provenance.trusted);
        assert_eq!(
            loaded.provenance.context.as_deref(),
            Some("sigil://release/linux-x86_64")
        );
    }

    #[test]
    fn signed_envelope_rejects_tampered_certificate_payload() {
        let mut value = signed_value(TEST_SEED_A);
        value["certificate"]["source_name"] = serde_json::Value::String("evil.sigil".to_owned());
        let error = decode_certificate_document::<CertificateJson>(value, &policy(TEST_SEED_A))
            .expect_err("tampered certificate must fail provenance verification");
        assert!(
            error.to_string().contains("payload hash mismatch"),
            "{error}"
        );
    }

    #[test]
    fn signed_envelope_rejects_wrong_trust_root_key() {
        let error = decode_certificate_document::<CertificateJson>(
            signed_value(TEST_SEED_A),
            &policy(TEST_SEED_B),
        )
        .expect_err("wrong trust root must fail closed");
        assert!(error.to_string().contains("public key mismatch"), "{error}");
    }

    #[test]
    fn signed_envelope_rejects_replayed_context() {
        let mut wrong_context = policy(TEST_SEED_A);
        wrong_context.expected_context = Some("sigil://release/macos-arm64".to_owned());
        let error = decode_certificate_document::<CertificateJson>(
            signed_value(TEST_SEED_A),
            &wrong_context,
        )
        .expect_err("context replay must fail closed");
        assert!(error.to_string().contains("context mismatch"), "{error}");
    }

    #[test]
    fn signed_envelope_rejects_unknown_algorithm() {
        let mut value = signed_value(TEST_SEED_A);
        value["provenance"]["algorithm"] = serde_json::Value::String("ed25519-v2".to_owned());
        let error = decode_certificate_document::<CertificateJson>(value, &policy(TEST_SEED_A))
            .expect_err("unknown signature algorithm must fail closed");
        assert!(error.to_string().contains("algorithm"), "{error}");
    }

    #[test]
    fn signed_envelope_rejects_revoked_signer() {
        let mut revoked = policy(TEST_SEED_A);
        revoked.revoked_signers.push("sigil-ci".to_owned());
        let error =
            decode_certificate_document::<CertificateJson>(signed_value(TEST_SEED_A), &revoked)
                .expect_err("revoked signer must fail closed");
        assert!(error.to_string().contains("revoked"), "{error}");
    }

    #[test]
    fn unsigned_certificate_rejects_authenticated_policy() {
        let value = serde_json::to_value(certificate()).expect("certificate is JSON");
        let error = decode_certificate_document::<CertificateJson>(value, &policy(TEST_SEED_A))
            .expect_err("unsigned cert must fail when provenance is required");
        assert!(error.to_string().contains("unsigned"), "{error}");
    }
}
