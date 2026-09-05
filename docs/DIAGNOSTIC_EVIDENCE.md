# Diagnostic Evidence

SIGIL treats diagnostics as a stable machine interface. The registry,
structured envelopes, generated error pages, CLI explanation command, and MCP
lookup surface are covered by executable synchronization tests. This document
retains the measured evidence for whether richer diagnostic envelopes help an
agent repair programs.

## Published A/B results

Each experiment compared a bare `code + message` control with the full
diagnostic envelope. All runs used nine tasks, five repeats per arm, and at
most five attempts. The preregistration, report, summary, and run identifier
remain in Git. Raw per-repeat transcripts are stored as versioned release
assets; each compact run directory pins the archive and every transcript by
SHA-256.

| Run | Model | Bare pass | Full pass | Task wins (full/bare) | Verdict |
| --- | --- | ---: | ---: | ---: | --- |
| [`20260621T012217Z-ab`](../bench/runs/20260621T012217Z-ab/report.md) | Claude Sonnet 4.6 | 95.6% | 82.2% | 0 / 2 | no significant difference |
| [`20260621T054956Z-ab`](../bench/runs/20260621T054956Z-ab/report.md) | Claude Sonnet 4.6 | 86.7% | 93.3% | 2 / 0 | no significant difference |
| [`20260621T143440Z-ab`](../bench/runs/20260621T143440Z-ab/report.md) | Claude Haiku 4.5 | 82.2% | 88.9% | 3 / 1 | treatment helps |

The first run exposed a harness defect: diagnostics for stdlib-composed tasks
used composed-source line numbers that were not actionable against the source
shown to the model. After coordinate remapping, the direction reversed on the
same Sonnet task set. The weaker-model run met the preregistered decision rule
in favor of the full envelope.

These experiments are directional evidence, not a universal performance
claim. They are small, temperature was approximately 1.0, and no seed was
available. `suggested_edits` appeared in none of the observed treatment
diagnostics, so the measured effect belongs to the envelope as a whole rather
than that field.

## Retention and verification

The raw archives are retained outside this repository and are available on
request; the release tag `diagnostic-evidence-2026-06` names the archive set.
For each run:

1. Read `transcripts.archive.json` for the archive name, byte size, and archive
   SHA-256.
2. Verify the obtained archive against that digest.
3. Extract at the repository root.
4. Verify every restored transcript against `transcripts.sha256`.

The current retention contract is defined in
[`bench/ARTIFACT_POLICY.md`](../bench/ARTIFACT_POLICY.md).
