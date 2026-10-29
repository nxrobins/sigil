# Native linear regression tool

`tool::tool_main(input_ptr:i64@Public,input_len:i64@Public)->i64@Public !{Alloc}`
trains y = bias + slope*x using full-batch MSE gradients and SGD at learning
rate 0.05. Training inputs x=0,1,2,3 have targets 1,3,5,7. Separate validation
inputs x=4,5 have targets 9,11 and never enter gradient updates. Initial weights
are zero. Input is an ASCII integer in 0..200, at most three bytes; empty input
defaults to 100 epochs. The existing UTF-8 and integer readers are reused;
the short length bound excludes their unspecified integer-overflow domain.
Malformed/out-of-range epochs return -422; oversized input -413. Valid signed
zero/leading-zero forms accepted by that reader are not a canonical text codec.

The objective is built from scalar tape operations; one reverse sweep supplies
both weight gradients, without a handwritten MSE derivative or X-transpose
gradient formula. A 32-node/four-sum-edge tape is built once and replayed with
updated weights each step, without reallocating or rebuilding its topology.
The numeric package still supplies SGD and validation matrix evaluation. All
training arithmetic executes inside SIGIL/Wasm using sigil/autodiff,
sigil/numeric and identified ambient stdlib modules. No Python/Torch
service, GPU, host import, grant or trusted surface is used at runtime.

All matrices, tape buffers, cells, node lists and output storage exist before the epoch loop.
The bump pointer must remain unchanged across the entire loop or execution
refuses with -500. Dependency failures propagate as negative entry results;
the ordinary runtime treats them as refusal, not successful output. Normal
fuel/memory limits can still interrupt the program.
The viewer requests a bounded 250000 cooperative fuel units for this heavier
tape workload. The package runner's 100000 default, 10000000 engine-fuel
backstop and 16 MiB memory cap remain unchanged; explicit smaller budgets refuse.

Success returns exactly 72 bytes: nine little-endian IEEE-754 f64 values in
this order: initial training MSE, final training MSE, bias, slope, initial bias
gradient, initial slope gradient, final bias gradient, final slope gradient,
validation MSE. The value is packed as pointer*4294967296+72. Raw backing is used
only to emit this declared output ABI; matrix math uses the library API.

The stdlib-only run.py viewer invokes the normal package CLI and decodes those
bytes to readable JSON. It performs no forward pass, gradient or update; Torch
is an independent test oracle only. This is tiny CPU training, not large-model
autoresearch, a Torch launcher, accelerated training or a general tensor engine.
The original handwritten-gradient program remains a regression fixture;
this migrated consumer is version 0.1.0-public.2. The package and evidence are
experimental, unreviewed and not admitted.
