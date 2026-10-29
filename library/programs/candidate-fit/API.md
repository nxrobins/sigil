# Bounded candidate fitting

Private `candidate-fit/tool` `0.1.0-public.1`, experimental, unreviewed and not
admitted. Entry `tool::tool_main(input_ptr:i64@Public,input_len:i64@Public)`
returns packed bytes as i64@Public with the Alloc effect. No host import, grant,
network, process launch or GPU backend is requested.

## Candidate expressions

All eight constants w0..w7 are trainable. ReLU is max(z,0), with derivative zero
at zero, as documented by the unchanged autodiff package.

- Candidate 0: `w0+w1*x+w2*relu(w3*x+w4)+w5*relu(w6*x+w7)`.
  Initial constants: `[0, .1, .3, .8, -.1, -.2, -.7, .15]`.
- Candidate 1: `w0+w1*x+w2*x*x+w3*x*x*x+w4*relu(w5*x+w6)+w7*relu(-x)`.
  Initial constants: `[0, .1, .05, 0, .3, .8, -.1, -.2]`.

The eight training x values are `[-1,-.75,-.5,-.25,.25,.5,.75,1]`; validation x
values are `[-.875,-.375,.125,.625]`. Both use target function
`.3+.5*x+.7*relu(1.1*x+.2)-.4*relu(-.8*x+.1)`; its separately emitted float64
target values are fixed inputs. Training minimizes mean squared error with
plain numeric SGD at rate .1. Validation values never enter gradient updates:
their separate tape graph is discarded before training and rebuilt afterwards.
This is a demonstration dataset, not evidence of general model quality.

## Input and bounds

Empty input defaults to candidate 0 and 16 updates. Otherwise input is exactly
`C:S`, where C is 0 or 1 and S is a canonical unsigned decimal integer 0..16
(one digit or two without a leading zero). No whitespace, sign, trailing data,
custom expression, external dataset or initial-constant override is accepted.
Input above four bytes returns -413; other malformed/out-of-domain input -422.

A 256-node/eight-sum-edge tape holds one fixed objective. It is built once for
training, then replayed after each update; reverse mode supplies every gradient
without handwritten derivatives. All buffers and output storage exist before
the update loop. Heap growth across that loop returns -500. Library errors
propagate as negative entry results; the runtime refuses rather than returning
a successful partial report. Runtime interruptions are not atomic.

The viewer requests 500000 cooperative fuel. The global default (100000),
engine backstop (10000000) and memory cap (16 MiB) are unchanged. The fixed
iteration limit applies before graph allocation; normal lower budgets can
still refuse. Constructor-owned live, Public, non-aliased storage is required
by the unchanged numeric/autodiff contracts; records are not sealed.

## Output

Success returns exactly 304 bytes, packed as pointer*4294967296+304:

| Offset | Encoding | Meaning |
| --- | --- | --- |
| 0 | two little-endian i64 | Candidate id, completed update count |
| 16 | four little-endian f64 | Initial training MSE, final training MSE, initial validation MSE, final validation MSE |
| 48 | eight f64 | Initial constants in parameter order |
| 112 | eight f64 | Final constants |
| 176 | eight f64 | Initial training gradient |
| 240 | eight f64 | Final training gradient |

The stdlib-only viewer decodes native output, validates its length, finiteness
and request identity, and prints readable JSON. It performs no forward pass,
gradient, update or fallback training. PyTorch CPU float64 is an independent
test oracle; comparisons use absolute 1e-12 plus relative 1e-11 tolerance.

The input/output ABI is a local example protocol, not the other machine's
candidate record or a portable register IR. Ordinary package certificates bind
program/graph inputs, not authenticated fitness measurements. No candidate
generation, untrusted-code service, archive, autonomous search or admission is
introduced.

The viewer emits `candidate-fit-v2` JSON, with `initial_validation_loss` and
`validation_loss`. This replaces the v1 display schema; the 304-byte native
ABI and numerical results are unchanged.
