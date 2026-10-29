# Bounded population search and checkpoints

This experimental application runs the original eight-candidate, two-elite search
policy with the declared binary64/PCG migration. It supports discrete-only and
hybrid arms, one to forty generations and zero to twenty task steps. Hybrid
scoring uses the existing three-round bounded fitter; final scoring does not
fit. Stable ranking breaks ties by existing population order. Parent choice
uses the best four candidates; crossover is chosen with probability one half.
Application policy remains here, not in the generic packages.

Each command is canonical lowercase hex. Every execution retains 500000
cooperative fuel, 10000000 engine fuel and 16 MiB memory. A scoring command
processes one candidate. A breeding command produces the complete next
population. No fit spans commands, so adaptive fitting state is not omitted
from a suspended update. Failure emits no new state; callers retain their
previous snapshot. Whole-job limits are at most 328 candidates and 368 state
transitions; the separately tracked graph-evaluation count includes fitting.

## Commands

All commands begin with four ASCII bytes and version byte 1.

| Command | Remaining bytes after version | Result |
| --- | --- | --- |
| ASIN | generations, task steps, hybrid flag; three LE u64 words: seed, stream, candidate budget | Initial state |
| ASST | three zero bytes; complete state | One next state; -409 if already complete |
| ASVA | three zero bytes; complete state | Validated state, unchanged |
| ASCK | three zero bytes; initial state | Checkpoint revision zero; nonzero-transition states refuse |
| ASOP | three zero bytes; original 32-byte ASIN request; checkpoint JSON | Restored complete state for that exact configuration |
| ASAD | three zero bytes; next state; previous checkpoint JSON | New checkpoint retaining old current as previous |
| ASEQ | three zero bytes; 64-byte identity; complete state | Canonical pending evaluation request; requires scoring phase and budget |
| ASED | three zero bytes; canonical request JSON | Validated AFIT-v1 bytes for the existing fitter |
| ASER | three zero bytes; request length as LE u16; status byte; request JSON; report bytes | Canonical response; success requires a structurally valid fitting report |
| ASEA | three zero bytes; 64-byte identity; current state; response JSON | Matched and validated next state |

ASIN seeds are unsigned 64-bit; streams are 0..2^63-1. The budget is 0 through
8*(generations+1); attempting to score after budget exhaustion refuses -413.
It is part of immutable job identity, not silently increased on resume.
Malformed fields refuse -422, incompatible profiles/jobs/revisions -409 and
excess bounds -413. Library errors and runtime interruptions propagate.
ASIN is 32 bytes. ASST/ASVA/ASCK are 1744 bytes. Checkpoint commands bound the
textual input at 20000 characters, decoding state and envelope separately
within the existing records codec bounds. No codec bound is raised.

## Complete state

The state is 1736 bytes: 32 little-endian u64 header words, eight 144-byte
candidate slots, and 41 little-endian binary64 history entries. Unused header,
instruction and history storage must be zero. All numeric values are finite.

| Header word | Meaning |
| --- | --- |
| 0, 1, 2 | Magic 1397904193, state version 1, task/numeric/policy profile 1 |
| 3, 4 | Original seed and stream |
| 5, 6 | Exact RNG value and increment |
| 7, 8, 9 | Generation limit, task steps, hybrid flag |
| 10, 11, 12 | Generation, scored-candidate cursor, phase: scoring=0, breeding=1, done=2 |
| 13, 14, 15 | Completed transitions, candidates evaluated, candidate budget |
| 16, 17, 18 | Graph evaluations, accepted fitting steps, rejected fitting steps |
| 19 | History length |
| 20 through 31 | Reserved zero |

Each candidate slot stores the ACPU record in bytes 0..119, zero-padded after
its last instruction; lineage u64 at 120; loss and fitness f64 at 128 and 136.
The candidate's task steps match the job. Unscored slots have zero scores.
Generation-end populations are sorted and history ends with the champion's
loss. Counts, phases, budgets, score/fitness relationships and RNG stream
consistency are checked before the next command.

Checkpoints use sigil/checkpoint with domain autoresearch and compatibility
search-f64-pcg-v1. Envelope revision equals completed transitions. The previous
state must have the same job identity and revision one lower. ASOP also checks
the caller's original ASIN request, preventing accidental cross-job restoration.

These are structurally validated, unsigned local records. They do not prove
that an untrusted writer computed a claimed score or followed a transition;
ASAD validates identity/revision/schema, not a second execution of the step.
No rollback authorization, multiwriter CAS or external trial attestation is
implied. The file driver writes only new revisions; generic grant-controlled
KV publication remains a separately tested adapter, not this execution path.

## Evaluation identity and acceptance

The 64-byte identity is a 32-byte job identifier followed by a 32-byte producer
program identifier. The file driver derives the latter from the freshly checked
package certificate's artifact identity. Native callers must provide their own
trusted identity; opaque bytes alone are not authentication.

ASEQ uses profile autoresearch-fit-v1 and a 112-byte context containing seed,
stream, generation limit, steps, hybrid flag and candidate budget as six LE
u64 words, followed by the identity. Sequence equals completed transitions;
payload is the exact current candidate's AFIT-v1 request. Checkpoint restoration
with the same identity recreates that request. No pending numerical step is
suspended between calls.

The CPU worker calls ASED, runs the returned AFIT request unchanged, then calls
ASER with its report. These calls have independent unchanged execution budgets;
the maximum fit plus JSON packaging does not fit one call. ASED only produces
the declared AFIT-v1 family, not arbitrary tool commands. ASER validates success
reports; nonzero status represents a failure and does not require a report.

ASEA reconstructs the expected request from current state, matches the complete
echo, then validates report lengths, headers, candidate echo, finite numbers,
counts, accepted weights, rate/fitness trace arithmetic and unused fields.
It does not recompute reported objective values or gradients. Only success
advances state. Status 1..4 (candidate-refused, worker-failed, cancelled,
timed-out) returns -502 without issuing a new state; malformed success reports
return -422 or identity mismatch -409. Size excess returns -413. Underlying
runtime traps can produce no response at all.

A consumed reply refuses against the next state. Intentionally restoring an
older trusted state can repeat work; no exactly-once delivery or authenticated
history is promised. The host must serialize state publication. Requests and
responses use the generic exchange limits of 1536 and 6144 bytes; combined
command input is at most 15904 lowercase hex characters. No runtime limit or
Public-only package execution rule is widened.
