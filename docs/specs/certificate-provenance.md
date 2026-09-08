# Certificate provenance profile

SIGIL certificates are still content certificates first: the base schema binds
source framing, inner/outer Wasm fingerprints, effect policy, solver witness,
ownership/capability summaries, and the mandatory schema-v9 formal report. The
provenance profile adds an authentication envelope around that base certificate
for deployment systems that need to know who issued the certificate.

## Threat model

The authenticated profile assumes an attacker may copy, edit, replay, or replace
certificate files and artifacts. It does not assume the certificate transport is
trusted. It does assume the verifier is running the intended SIGIL binary, has an
untampered Ed25519 trust root for the signer, and selects the intended deployment
context string.

The profile authenticates the certificate issuer and context. It does not prove
that the signer is operationally safe, that a CI job was honestly configured, or
that the compiler/runtime binary is uncompromised. Those remain deployment
responsibilities.

## Deployment profiles

- `unsigned-local`: the existing default. A plain schema-v9 certificate can be
  used for local integrity checks and re-derivation. It binds content but does
  not authenticate origin.
- `authenticated-release`: a signed envelope with `envelope_version = 1`,
  `profile = "authenticated-release"`, and `provenance.algorithm =
  "ed25519-v1"`. Deployment verification supplies a trust root with
  `--require-cert-provenance SIGNER_ID=PUBLIC_KEY_HEX` and normally supplies
  `--cert-context <CTX>`.

## Envelope

An authenticated certificate file wraps the existing certificate:

```json
{
  "envelope_version": 1,
  "profile": "authenticated-release",
  "certificate": { "...": "the existing schema-v9 CertificateJson" },
  "provenance": {
    "algorithm": "ed25519-v1",
    "signer_id": "sigil-ci",
    "public_key": "<32-byte lowercase hex Ed25519 public key>",
    "context": "sigil://release/linux-x86_64",
    "issued_at_unix_ms": 1804000000000,
    "certificate_payload": {
      "algorithm": "sha2-256",
      "bytes": 1234,
      "hash": "<sha256 of the canonical certificate payload>"
    },
    "signature": "<64-byte lowercase hex Ed25519 signature>"
  }
}
```

The signed certificate payload is the compact JSON serialization of the typed
base certificate after parsing. The Ed25519 signature covers framed fields:
envelope version, profile, signature algorithm, signer id, public key, context,
issued-at time, and the complete certificate-payload fingerprint. The framing is
length-delimited and prefixed with `SIGIL-CERT-PROVENANCE\0v1`, so a verifier
does not depend on raw JSON field order.

## CLI flow

Emit a signed certificate:

```sh
sigil check tool.sigil \
  --cert tool.cert.json \
  --cert-signer sigil-ci \
  --cert-sign-key-hex <32-byte-seed-hex> \
  --cert-context sigil://release/linux-x86_64
```

Verify it in an authenticated deployment profile:

```sh
sigil verify-cert \
  --cert tool.cert.json \
  --source tool.sigil \
  --require-cert-provenance sigil-ci=<public-key-hex> \
  --cert-context sigil://release/linux-x86_64
```

`sigil run --cert` and `sigil forge --cert` accept the same
`--require-cert-provenance`, `--cert-context`, and `--revoke-cert-signer` gates.
If a command requires provenance and receives a plain unsigned certificate, a
certificate with the wrong signer/key, an unsupported algorithm, a mismatched
context, a revoked signer, or a tampered payload/signature, it fails closed with
`R820`.

## Rotation and revocation

Trust roots are selected by the deployment command, not by the certificate. To
rotate keys, publish the new `SIGNER_ID=PUBLIC_KEY_HEX` pair and update
deployment jobs to require it. During overlap, use distinct signer ids such as
`sigil-ci-2026q3` and `sigil-ci-2026q4` so logs identify which key signed each
artifact.

To revoke a key immediately, remove it from the trusted deployment configuration
and pass `--revoke-cert-signer <ID>` anywhere stale envelopes may still be
present. A revoked signer fails even if the Ed25519 signature is valid.
