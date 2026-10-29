# Fixed regression workload contract

Inner-ring Public input/output, Alloc only, no host imports. The existing
libraries are pinned unchanged. Candidate instruction semantics, seeded
initialization, mutation, crossover, stable ranking and staged sign fitting
are the preserved application's policy, not new library APIs.

## Objective

Parameters are slope and bias, initialized to (-1, 0.5); momentum starts at
zero. Training rows are (-1,-1), (0,1), (1,2.5), (2,5.5). Each step computes
both coordinates' full-batch MSE gradient at the same pre-update parameters.
The candidate update rule then advances each parameter and momentum. Time is
step/12. Register and parameter clipping remains [-4096,4096], with zero
derivatives at either endpoint. Final training MSE drives all eight reverse-mode
candidate gradients; fitness adds 66/65536 per instruction.

The native gradient uses training-only sufficient statistics; final loss uses
the four individual observations. No validation observation enters the fitting
graph. Validation rows (-0.5,0) and (1.5,4) are used only by RGPR after fitting.
Candidate updates, acceptance, rollback and adaptive rates are unchanged.

## Bounds and fitting format

At most eight constants, twelve instructions and twelve inner steps. The
fixed-capacity tape stays at 768 nodes, with no allocation during numerical
fitting. Requests must satisfy
`(rounds+1)*(64+steps*(14+2*instructions)) <= 2600`, with rounds in 0..6.
This stricter workload-specific bound leaves the existing engine fuel,
500000 cooperative fuel and 16 MiB memory ceilings unchanged.

AFIT v1/v2 framing and the 840-byte binary fitting report prefix are retained;
the embedded ACPU numeric/task-profile byte at offset 7 is 2, not the quadratic
profile 1. Request echo, finite-number and fitting arithmetic checks remain.
The JSON report format is `sigil-autoresearch-regression-fit-record-v1`.
Raw request length is 84..128; binary output is 840 plus the request length.
Wrong framing/profile refuses; oversized work refuses before evaluation.

## Search state and resume

ASIN, ASST, ASVA and checkpoint command framing retain their previous byte
layout. State length remains 1736; header word 2 is task profile 2. Words 20..23
hold the 32-byte dataset SHA-256, and words 24..31 must remain zero. Population,
RNG, lineage, counters, history and complete search budgets remain serialized.
Population is eight, with two elites; generations are 1..40, at most 368
transitions. Only fitting-call boundaries can be checkpointed.

Checkpoint domain is `autoresearch-regression-v1`; compatibility is the
64-character dataset SHA-256. Native validation checks both identity and state.
File publication is create-new; an interrupted newest file may be incomplete,
so resume from the preceding complete checkpoint into a new directory. The
driver also binds program identity and mode in `program-identity.hex`.
This is not authenticated history or exactly-once execution.

The exchange profile is `autoresearch-regression-fit-v1`; its 128-byte context
contains 32 configuration bytes, 64-byte job/program identity and 32-byte
dataset identity. Configuration is four little-endian u64 words: seed, stream,
`generations | steps<<8 | hybrid<<16 | budget<<24`, then zero. The bounded
fields fit without overlap; all six original settings remain bound. The
worker checks dataset/task profile and the
acceptor matches the whole request before state changes. Generic exchange and
command-size limits are unchanged. Scores remain structurally checked, not
independently recomputed or authenticated during reply acceptance.

## Dataset and reporting commands

All commands are lowercase hex on the tool boundary. RGDS followed by
`01 00 00 00` returns 104 bytes: ASCII RGRD, version 1, counts 4 and 2, zero,
then six (x,y) pairs as little-endian f64. Its SHA-256 is
`028b1578cc66135645d790d76337e6f047c2ebd013e40f61dde1c68fde907b98`.
The manifest binds dataset.json; the driver additionally compares its actual
rows to RGDS output. A hash is an identity, not permission or a signature.

RGPR followed by `01 00 00 00` and two little-endian f64 parameters returns two
f64 values: training MSE, then validation MSE, computed using numeric::mse_into.
Parameters must be finite and within [-4096,4096]. Reporting cannot advance or
mutate search state. Malformed inputs refuse rather than returning partial data.

Native statuses preserve the existing distinction: incompatible identity -409,
bound excess -413, malformed/nonfinite data -422, allocation growth -500;
underlying library failures propagate. Runtime interruption is not a returned
status or a transactionality guarantee. No capability, admission or branch
protection is changed.
