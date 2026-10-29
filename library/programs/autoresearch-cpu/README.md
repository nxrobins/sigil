# Evaluate autoresearch candidates on CPU

This example imports the instruction/weight layout from the SIGIL
autoresearch port and returns loss, fitness, final optimizer state and all eight
weight gradients. The candidate executes entirely in SIGIL/Wasm using the
unchanged autodiff package. Python validates/transports records and displays
native output; it does not evaluate candidates or substitute training results.

With the solver-enabled development CLI on PATH, from the repository root:

```sh
sigil package-lock --root library/programs/autoresearch-cpu --dependency sigil/autodiff=library/packages/autodiff
sigil check --package library/programs/autoresearch-cpu
python3 library/programs/autoresearch-cpu/run.py --candidate library/programs/autoresearch-cpu/candidates/momentum.json
python3 library/programs/autoresearch-cpu/run.py --candidate library/programs/autoresearch-cpu/candidates/sgd.json --steps 5
```

Create the lock once; existing locks refuse overwrite. The wrapper accepts
`--sigil PATH` and `--package ROOT`. Change the candidate's instruction columns
or weights, not SIGIL source, to evaluate another bounded update rule.
`--steps 0..20` selects a prefix of the original 20-step task.

The supplied SGD, momentum and step-decay records preserve the source seed
instructions and Q16 weights, including its deliberately imperfect momentum
updates. [Provenance](PROVENANCE.md) identifies the source revision.
[The API](API.md) defines the numerical migration and strict record/wire format.
`q16-import-f64-v1` converts weights exactly to binary64; subsequent evaluation
is floating point, not emulation of the source's fixed-point derivative rules.

This is the CPU evaluation interface, not the full mutation/fine-tuning loop,
a GPU trial runner or an authenticated fitness record. Admission guards,
runtime ceilings and branch protections are unchanged.

This public source revision is experimental, unreviewed and not admitted.
The previous package revision and development records remain unchanged.
