# Autoresearch fitting protocol

This page specifies the fitting interface retained by the growing autoresearch
consumer. The [search interface](SEARCH_API.md) composes it with seeded RNG,
bytes and checkpoint packages. Inner ring, Public-only, allocation at construction and
record encoding, no host imports or grants.
The earlier CPU evaluator and proposal examples remain independent references;
the search interface adds population and checkpoint behavior, while external
evaluation exchange remains pending.

## Request and fitting policy

Input is canonical lowercase hex of: ASCII AFIT, version byte 1 or 2, fitting-round
limit byte 0..6, two zero reserved bytes, then one complete ACPU v1 request.
The ACPU record retains its steps 0..20, 1..12 instructions, eight finite
weights in [-4096,4096], and saturating-f64-v1 semantics. Raw payload length
84..128 bytes; textual input 168..256 characters. Both framing layers validate.
Total requested graph work must also satisfy
`(rounds+1)*(24+steps*(7+2*instructions)) <= 2600`; otherwise refuse -413 before
evaluation, even if a zero gradient might have stopped fitting early. This
conservative envelope permits three rounds for the 12-instruction, 20-step
maximum and six for smaller requests. Engine fuel remains 10,000,000;
cooperative fuel is 500,000 and memory 16 MiB, unchanged from the CPU evaluator.

Evaluate the original candidate once. For each fitting attempt, use its eight
reverse-mode gradients to stage a clipped sign step through optim::begin_sign.
If all gradients are zero, stop without a proposal. Evaluate the proposed
weights using a reset/rebuilt tape, including fresh clipping decisions.
Accept only strictly lower complexity-penalized fitness; commit the staged
weights and retain that report. Otherwise discard the proposal; accepted
weights and report remain unchanged. Copying reports uses numeric::scale_into.

Initial step is 3277/65536. On acceptance multiply by 1.5, capped at 13107/65536;
on rejection divide by 2. These are floating-point operations, not the old
Q16 integer rounding. Strict fitness comparison has no noise-margin rule.
Policy, objective and instruction semantics belong to this application.
The library owns staged update validation, copying, conflict checks and rollback.

Every numerical/metadata failure refuses the whole request without a fitted
candidate. It is not silently assigned a poor score. Returned error statuses
propagate from numeric/optim/autodiff; malformed input is -422, excess input
bounds -413 and allocation growth -500. Runtime interruption remains separate.

## Native report

Version 1 returns 840 bytes plus the exact binary request echo:

| Offset | Encoding | Contents |
| --- | --- | --- |
| 0 | eight LE i64 | version=1, task steps, instruction count, requested rounds, attempted, accepted, rejected, zero-gradient stop flag |
| 64 | three LE f64 | initial loss, initial fitness, next step size |
| 88 | eight LE f64 | accepted final weights |
| 152 | fourteen LE f64 | accepted loss, fitness, positions[2], momentum[2], gradients[8], matching the CPU evaluator's value layout |
| 264 | six LE i64 | decisions: accepted=1, rejected=0, unused=-1 |
| 312 | six rows of eleven LE f64 | attempted step size, base fitness, proposed fitness, eight base gradients; unused rows are zero |
| 840 | exact bytes | original binary request |

Attempted equals accepted+rejected and cannot exceed the requested limit. A
zero-gradient stop may occur before that limit. The final report belongs to
the accepted weights even after a rejected last attempt. At most seven
evaluations use a fixed 768-node tape, reset between evaluations. No heap
growth is permitted during evaluation/fitting after construction. Record
encoding occurs afterward and may allocate. Current global runtime caps remain.

## Native JSON record

Version 2 runs the same fitting policy and returns a bounded JSON object through
records::put_string, put_hex and put_f64le; the application owns only the schema.
Maximum encoded output is 4096 bytes. The exact field set is:

| Field | Value |
| --- | --- |
| format | `sigil-autoresearch-fit-record-v1` |
| numeric | `binary64le-hex-v1` |
| request_hex | exact binary AFIT v2 request, lowercase hex |
| header_le | the 64-byte version-1 report header as lowercase hex |
| summary_f64le | three finite little-endian binary64 words, hex |
| weights_f64le | eight accepted weights, finite binary64 hex |
| accepted_f64le | fourteen accepted report values, finite binary64 hex |
| decisions_le | six little-endian i64 decisions, hex |
| trace_f64le | 66 finite binary64 trace values, hex |

Numeric bit patterns are exact, including signed zero; they are deliberately
strings, not JSON decimal numbers. The request echo binds the v2 request while
the header retains the numerical report-layout version 1. `--record` selects
this native output. The wrapper rejects duplicate/unknown/missing fields,
unknown profiles, wrong lengths, noncanonical hex, nonfinite data and mismatched
requests before displaying or exporting anything. It can decode either record
to the same human-readable result without host-side fitting.

This is a fitting result, not a whole-search checkpoint, an authenticated trial
receipt, or a persistence protocol. Population, lineage, RNG and remaining
search budget are not represented here.

The wrapper validates record and report structure, identity, finite data,
decision arithmetic and step/fitness transitions; it does not compute gradients,
proposals or scores. Native results, including the candidate's final weights,
are returned as JSON. The request hash is an unsigned identity, not an
authenticated trial certificate.
