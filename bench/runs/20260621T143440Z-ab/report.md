# diagnostics-axes a9 — A/B: full envelope vs bare diagnostics

- **Variable**: `diagnostic_detail` (control=`bare`, treatment=`full`)
- **Model**: claude-haiku-4-5 · **live**: True · **git**: `10f23bb175f4`
- **Design**: 9 tasks × 5 repeats/arm, max 5 attempts
- **Verdict**: **treatment_helps** (treatment wins 3, control 1, tie 5)

## Headline (per arm)

| Arm | pass_rate | median attempts (passers) |
|---|---:|---:|
| `bare` | 82.2% (37/45) | 2.0 |
| `full` | 88.9% (40/45) | 2.0 |

## Per-task (within-task pairing)

| Task | control pass | treatment pass | control med | treatment med | favors |
|---|---:|---:|---:|---:|---|
| `task001_echo` | 5/5 | 5/5 | 1.0 | 1.0 | tie |
| `task011_palindrome` | 2/5 | 1/5 | 2.5 | 5.0 | tie |
| `task020_rot13` | 5/5 | 5/5 | 1.0 | 1.0 | tie |
| `task028_count_lines` | 5/5 | 5/5 | 2.0 | 2.0 | tie |
| `task029_count_lines_via_stdlib` | 2/5 | 4/5 | 4.0 | 3.0 | treatment |
| `task032_sha256_hex` | 5/5 | 5/5 | 2.0 | 3.0 | control |
| `task045_http_size_via_stdlib` | 5/5 | 5/5 | 3.0 | 2.0 | treatment |
| `task061_json_field` | 5/5 | 5/5 | 1.0 | 1.0 | tie |
| `task151_http_size` | 3/5 | 5/5 | 2.0 | 2.0 | treatment |

## Decision rule (pre-registered)

- per-task win: |Δ pass-count| ≥ 2 (else attempts tie-break by ≥ 1)
- global: an arm needs ≥ 3 wins AND ≥ 2× the other's

## Caveats

- Underpowered: 9 tasks × 5 repeats; temp≈1.0, no seed. Directional evidence, not proof.
- suggested_edits appeared on 0/236 treatment diagnostics; the envelope-level verdict is not attributable to that one field.
