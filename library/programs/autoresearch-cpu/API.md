# Bounded autoresearch CPU interface

Private `autoresearch-cpu/tool` `0.1.0-public.1`, experimental, unreviewed and
not admitted. `tool::tool_main(input_ptr:i64@Public,input_len:i64@Public)`
returns packed output bytes as i64@Public with Alloc only. Its sole source
dependency is the unchanged `sigil/autodiff` package. No host grants or imports.

## Candidate record

JSON has exactly `format`, `numeric`, `ops`, `dst`, `a`, `b`, `w` fields.
`format` is `sigil-autoresearch-cpu-v1`. Four equally sized instruction columns
contain 1..12 integer entries; `w` contains exactly eight numbers. Booleans,
duplicate/unknown fields, nonfinite values and JSON above 16384 bytes refuse.
Computed source fields such as fitness/loss are not accepted as inputs.

`numeric` selects one of two explicit weight encodings:

- `saturating-f64-v1`: finite weights in [-4096,4096].
- `q16-import-f64-v1`: integer weights in [-268435456,268435456], divided by
  65536 exactly before transport. This is a weight import, not Q16 execution.

There are 16 registers. At each coordinate/step, registers reset to zero;
r0 is the clipped quadratic gradient, r1 the prior momentum, r2 time t/20,
r3 one, and r15 the prior momentum. Instructions execute sequentially and may
overwrite only r4..r15. Sources a use r0..r15, including currently zero registers.
Final r14 is the parameter delta and r15 is next momentum.

| Opcode | Operation | Meaning of b |
| --- | --- | --- |
| 0 ADD | a+b | Register 0..15 |
| 1 SUB | a-b | Register 0..15 |
| 2 MUL | a*b | Register 0..15 |
| 3 RELU | max(a,0) | Ignored, but bounded 0..15 |
| 4 WMUL | a*w[b] | Weight 0..7 |
| 5 WADD | a+w[b] | Weight 0..7 |
| 6 STEP | clip(a*w[b],0,1) | Weight 0..7 |
| 7 NEG | -a | Ignored, but bounded 0..15 |

## Numerical profile and task

Evaluate `(p0-3)^2 + 50*(p1+2)^2`, starting at (-4,3) with zero momentum.
Each coordinate uses its analytic task gradient (2*(p0-3), 100*(p1+2)) as a
differentiable expression. The reverse sweep differentiates through the entire
selected prefix, including momentum and parameter updates, with respect to all
eight binary64 weights. Gradients are not derivatives with respect to raw Q16
integer units. There is one backward sweep per request, no per-weight reruns.

Clip task gradients, every instruction output and updated positions to
[-4096,4096]. STEP clips to [0,1]. At both endpoints and outside the interval,
the derivative of clipping is zero; ReLU's derivative at zero is zero. Graphs
are rebuilt on every request so primal-dependent clip decisions cannot become
stale through replay. Fitness is loss + instruction_count*(66/65536).

Unlike the source port, there is no integer rounding between operations and
no independent saturation of derivative accumulators. Its implementation clips
value and derivative registers separately, despite a comment claiming saturated
values zero their derivatives. This profile instead differentiates the stated
clipped floating-point computation. Nonfinite arithmetic/derivatives refuse.
Compatibility means the declared profile agrees with an independent PyTorch
implementation; it does not mean identical Q16 losses or evolution winners.

## Native wire and report

The package CLI accepts text, so transport is canonical lowercase hex of:
four magic bytes `ACPU`, then u8 version=1, prefix_steps=0..20,
instruction_count=1..12, profile=1; eight little-endian f64 weights; then
instruction rows of four u8 values (op,dst,a,b). Exact binary length is
72+4*instruction_count (76..120 bytes); no whitespace/trailing data is accepted.
Native code independently checks all bounds, operands, weights and lengths.

The report is four little-endian i64 values (version=1, prefix steps,
instruction count, used tape nodes), then 14 f64 values: loss, fitness,
p0,p1,m0,m1, and eight weight gradients. It ends with the exact binary request
bytes. Total length is 144+request_length. The wrapper verifies the echo and
header, rejects nonfinite/malformed results and prints JSON with canonical
candidate and request SHA-256 identities. These unsigned identities are not
certificate-backed fitness attestations. Ordinary program certificates retain
their existing program/graph meaning.

## Resource and failure contract

Reserve a fixed 768-node tape, no sum edges, 16-register scratch and bounded
input/output buffers before execution. Heap growth during the unrolled task
and backward pass refuses (-500). Input over 240 text bytes, more than 12
instructions or more than 20 steps refuses (-413); malformed input, operands,
weights or profile refuses (-422). Tape/arithmetic errors propagate; no partial
successful report is returned. Runtime interruptions are not atomic.

Used tape nodes are `24 + steps*(7 + 2*instruction_count)`: at most 644 for
the 12-instruction, 20-step case. This is a storage bound, not a guarantee that
every permitted candidate has finite derivatives; reverse overflow refuses.

The wrapper requests 500000 cooperative fuel. The global default, 10000000
engine backstop and 16 MiB memory ceiling are unchanged; lower caller budgets
can still refuse. No arbitrary SIGIL/Python source, shell, GPU work, new
provider API, persistence, candidate mutation or fitting loop is introduced.
