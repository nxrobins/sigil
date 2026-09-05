# Diagnostic coverage census

This census distinguishes registration, production wiring, direct test references, dedicated
fixtures, and self-host representation. A textual reference is an anti-deletion signal, not proof
that every diagnostic path is semantically exercised.

The machine check is `diagnostic_security_surface_is_censused` in
`crates/sigil-runtime/tests/soundness_contract.rs`.

```pins
PIN_REGISTERED_CODES = 319
PIN_SECURITY_CODES = 245
PIN_PRODUCTION_WIRED_SECURITY_CODES = 243
PIN_DIRECT_TEST_REFERENCED_SECURITY_CODES = 183
PIN_DEDICATED_SOURCE_FIXTURES = 51
PIN_SELFHOST_SHADOW_CODES = 28
PIN_DIRECT_TEST_GAPS = 62
PIN_NONEMITTING_COMPATIBILITY_ALIASES = 2
```

## Interpretation

- **Registered:** every entry in `diagnostics::registry::CODES`; prefix totals are C=8, E=11,
  I=5, L=5, M=11, N=16, O=3, P=30, R=29, S=7, T=194.
- **Security:** the C/E/O/R/T families. This intentionally includes runtime feedback (`R8xx`) and
  stable compatibility aliases.
- **Production wired:** a compiler `codes::XXXX` reference or, for `R8xx`, a runtime/CLI/MCP source
  reference. The only exceptions are the two aliases in
  [`diagnostic-coverage-exceptions.tsv`](diagnostic-coverage-exceptions.tsv).
- **Direct test referenced:** the code token occurs in a Rust or SIGIL file under a crate's test
  tree, excluding the registry golden list. The exact missing set is
  [`diagnostic-test-gaps.txt`](diagnostic-test-gaps.txt); additions and removals require review.
- **Dedicated source fixture:** `crates/sigil-compiler/tests/fixtures/XXXX.sigil` exists. The existing
  registry-wiring suite verifies every present fixture actually emits its code or uses a declared
  programmatic source.
- **Self-host shadow:** the code token is emitted or named by a `selfhost/*.sigil` checker. This is
  correspondence evidence only for each checker's declared corpus.

## Compatibility aliases

`O006` and `R005` remain registered to preserve the public diagnostic namespace, but are not active
emission authorities. Region escape is enforced as `T254`; cross-ring rich error sanitization is
enforced as `T109`. They must not silently regain an independent production role without removing
their exception and adding direct tests.

## Review rule

New C/E/O/R/T codes must have a production reference and update this census. A new direct test or
self-host mapping should ratchet the corresponding count upward and remove the code from the gap
manifest where applicable. Lowering a count requires an explicit rationale.

## Regression axes

`tools/diag_axes_scoreboard.py` is a directional regression guard, not a substitute for semantic
tests. Its committed baseline covers these ten independently reviewable properties:

| Axis | Property | Metric |
|---|---|---|
| a1 | Coverage | declared diagnostic codes minus code tokens absent from production source |
| a2 | Payload structure | rich `DiagnosticJson` fields beyond the stable base envelope |
| a3 | Hint actionability | registry hints containing a pasteable token or construct |
| a4 | Contextualization | diagnostic sites that interpolate a relevant token into a hint |
| a5 | Resolvability | availability through fuzzy MCP lookup, `--explain`, and generated error pages |
| a6 | Stability contract | golden registry snapshot and per-message schema-version coverage |
| a7 | Enforcement rigor | required fixture coverage, debited by registered codes absent from production |
| a8 | Implementation parity | structured fields emitted by the self-host checker |
| a9 | Measured efficacy | scoreboard, baseline, and a complete live A/B evidence bundle |
| a10 | Single-error precision | rejecting fixtures under exact-error enforcement, debited by allowlisted extras |

Run `python tools/diag_axes_scoreboard.py --check` to compare the current tree with
`tools/diag_axes_baseline.json`. Metric changes require the focused tests for the behavior they
claim; a regex-derived increase alone is not evidence of correctness.
