# Fixed dataset regression search

This second autoresearch workload searches for a small optimizer program that
fits `slope*x+bias` to four fixed noisy training observations. It reuses the
existing numeric, autodiff, optim, RNG, bytes, records, JSON, checkpoint and
exchange packages without changing their versions or implementations.
The quadratic consumer remains unchanged in `../autoresearch`.

The two validation observations are report-only. Candidate gradients, fitting
acceptance and population ranking use training MSE plus the existing instruction
penalty. Validation scores do not influence search. This is a bounded synthetic
workload, not evidence of improved model training.

## Setup and run

From the repository root, with a solver-enabled CLI:

```sh
sigil package-lock --root library/programs/autoresearch-regression --dependency sigil/autodiff=library/packages/autodiff --dependency sigil/numeric=library/packages/numeric --dependency sigil/optim=library/packages/optim --dependency sigil/records=library/packages/records --dependency sigil/json=library/packages/json --dependency sigil/rng=library/packages/rng --dependency sigil/bytes=library/packages/bytes/versions/0.1.0-public.5 --dependency sigil/checkpoint=library/packages/checkpoint --dependency sigil/exchange=library/packages/exchange
sigil check --package library/programs/autoresearch-regression
python3 library/programs/autoresearch-regression/search.py --generations 1 --steps 2 --transitions 5 --out-dir /tmp/regression-part
python3 library/programs/autoresearch-regression/search.py --generations 1 --steps 2 --resume /tmp/regression-part/checkpoint-0005.json --out-dir /tmp/regression-resumed
```

Use new output directories and run package-lock only once on a fresh consumer.
Omit `--transitions` and `--resume` for an uninterrupted run. Both `--arm hybrid`
and `--arm discrete` are supported. The default workload uses twelve training
steps and two generations; the small example above checks the workflow.
Completed summaries include native training/validation losses, fitted slope/bias
and eight candidate-constant gradients.

Add `--evaluation exchange --job-id` with a 32-byte lowercase hexadecimal ID
to exercise the CPU request/reply interface. Keep the same options and
`program-identity.hex` with the checkpoint on resume. Requests bind task,
dataset, program, job and transition; this does not authenticate worker scores.
The driver supports file checkpoints only, not KV or GPU execution.

## Dataset and compatibility

[dataset.json](dataset.json) defines the six observations and their canonical
binary SHA-256. The driver compares it with actual native dataset output before
creating any output directory. Checkpoints carry a distinct task profile and
the dataset identity; restoring quadratic or changed-dataset state refuses.
Program identity and evaluation mode are also checked by the host on resume.
Changing data or code starts a new experiment; previous archives are preserved.

[API.md](API.md) defines the finite bounds, fitting and wire formats. The
independent reference and native tests live in
`library/tests/fixtures/autoresearch-regression` and
`library/tests/test_autoresearch_regression.py`. PyTorch is a test oracle, not a
runtime backend. This experimental source consumer is not admitted or a registry release.
See [the executed checks](MEASUREMENTS.md) for results, reproduction commands
and the source-publication checks required before delivery.
