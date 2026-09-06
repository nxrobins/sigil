# diagnostics-axes a9 — A/B: full envelope vs bare diagnostics

- **Variable**: `diagnostic_detail` (control=`bare`, treatment=`full`)
- **Model**: claude-sonnet-4-6 · **live**: True · **git**: `1868c875a4c5`
- **Design**: 9 tasks × 5 repeats/arm, max 5 attempts
- **Verdict**: **no_significant_difference** (treatment wins 0, control 2, tie 7)

## Headline (per arm)

| Arm | pass_rate | median attempts (passers) |
|---|---:|---:|
| `bare` | 95.6% (43/45) | 1.0 |
| `full` | 82.2% (37/45) | 1.0 |

## Per-task (within-task pairing)

| Task | control pass | treatment pass | control med | treatment med | favors |
|---|---:|---:|---:|---:|---|
| `task001_echo` | 5/5 | 5/5 | 1.0 | 1.0 | tie |
| `task011_palindrome` | 5/5 | 5/5 | 1.0 | 1.0 | tie |
| `task020_rot13` | 5/5 | 5/5 | 1.0 | 1.0 | tie |
| `task028_count_lines` | 5/5 | 5/5 | 1.0 | 1.0 | tie |
| `task029_count_lines_via_stdlib` | 3/5 | 0/5 | 5.0 | — | control |
| `task032_sha256_hex` | 5/5 | 5/5 | 2.0 | 2.0 | tie |
| `task045_http_size_via_stdlib` | 5/5 | 2/5 | 2.0 | 2.0 | control |
| `task061_json_field` | 5/5 | 5/5 | 1.0 | 1.0 | tie |
| `task151_http_size` | 5/5 | 5/5 | 1.0 | 1.0 | tie |

## Decision rule (pre-registered)

- per-task win: |Δ pass-count| ≥ 2 (else attempts tie-break by ≥ 1)
- global: an arm needs ≥ 3 wins AND ≥ 2× the other's

## Caveats

- Underpowered: 9 tasks × 5 repeats; temp≈1.0, no seed. Directional evidence, not proof.
- suggested_edits appeared on 0/166 treatment diagnostics; the envelope-level verdict is not attributable to that one field.
