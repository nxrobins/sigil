# Self-hosting closure and trusting-trust contract

**Status:** Implemented. This document states the current Stage-3 guarantees and boundaries; the
phase-by-phase journals are retired.

## Terms

- **Stage 1:** the SIGIL self-hosted compiler logic, compiled to Wasm by the Rust compiler and then
  run as a compiler.
- **Stage 2:** the Wasm module emitted directly by the Rust oracle for the same certified source.
- **Certified library:** the composed self-host source without a public `tool_main` entry.
- **With-driver image:** the certified source including the real input-reading `tool_main`.

## Established guarantees

### Byte identity

`boot_self_byte_capstone` requires Stage 1 and Stage 2 to emit the certified library byte for byte.
`boot_self_runnable_byte_capstone` preserves that identity when the internal `run_from_str` pipeline
entry is included. `ag6_5_with_driver_byte_capstone` extends the identity claim to the whole
with-driver image, including `Option<str>::unwrap_or`, without modifying the emitted module.

The poison censuses are anti-regression instruments for unsupported emission, but equality is the
actual correctness criterion. Digest and size pins detect accidental movement of the certified
source and output; they do not replace the byte comparison.

### Executable fixed point

The certified library intentionally has no runtime entry point. `stage3a_executable_closure` appends
a deterministic raw-Wasm `tool_main` shim that builds one `str` header and calls the library's own
`run_from_str`. The shim contains no compiler logic. Running that image on its certified source
reproduces the unmodified self-host-emitted library byte for byte.

This result is narrower than saying the with-driver image executes itself without assistance. The
with-driver image is proven byte-identical without a splice; the executable fixed-point proof still
uses the fixed entry shim. Both claims remain separately machine-checked.

### Trusting-trust discrimination

The Stage-3-B canary creates a self-recognizing emitter variant that remains functional but diverges
on compiler source. The Rust-oracle/self-host byte comparison accepts the honest emitter and rejects
the marked variant. This demonstrates the discrimination expected from a Diverse Double-Compiling
shape; it does not make the Rust oracle an independently diverse or independently trusted compiler.

## Authorities

- `crates/sigil-runtime/tests/pipeline_differential.rs` owns byte identity, poison censuses, the
  entry shim, executable closure, the divergence canary, and certified artifact pins.
- `crates/sigil-runtime/tests/support/preservation_manifest.rs` owns required semantic test names.
- `crates/sigil-runtime/tests/preserve_pins.rs` validates manifests and workflow contexts.
- `docs/CLAIMS.md` is the public claim ledger; `docs/SOUNDNESS_MATRIX.md` records exclusions and
  residual risks.
- `docs/specs/ag-6-full-emit.md` defines the generic-enum surface that closes the with-driver image.

## Non-claims

- The Rust oracle has not been retired from the trusted computing base.
- The comparison is not independent DDC with a separately implemented trusted compiler.
- Equality is claimed only for the committed certified source and named differential corpora.
- The fixed entry shim is part of the executable-closure instrument and must remain deterministic,
  single-call glue unless a replacement executable proof lands first.

## Required verification

```text
cargo test -p sigil-runtime --test pipeline_differential
cargo test -p sigil-runtime --test monomorph_differential
cargo test -p sigil-runtime --test preserve_pins
cargo test -p sigil-runtime --test claims_ledger
```
