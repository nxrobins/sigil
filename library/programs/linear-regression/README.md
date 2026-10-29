# Train linear regression in SIGIL

This useful native program learns bias and slope from four points, using the
shared autodiff tape for its objective and reverse-mode gradients, and numeric
for plain SGD and validation evaluation. Two
other points measure validation error. No Torch/Python training backend runs
inside or on behalf of the program. The [API](API.md) defines its small CPU
scope, bounded inputs and binary float output.

With a solver-enabled development sigil on PATH, from the repository root:

```sh
sigil package-lock --root library/programs/linear-regression --dependency sigil/autodiff=library/packages/autodiff --dependency sigil/numeric=library/packages/numeric
sigil check --package library/programs/linear-regression
python3 library/programs/linear-regression/run.py --steps 100
```

Create the lock only once on a fresh project. Existing locks refuse overwrite;
subsequent runs use that lock and its local cache. The viewer accepts an
explicit CLI path through `--sigil PATH`. Its Python dependency is the standard
library only; it displays native output rather than computing training results.
It requests 250000 fuel for the tape workload. For a direct CLI run, supply
`--fuel 250000`; global runtime defaults and the engine/memory caps are unchanged.

At 100 steps the observed training MSE falls from 21 to approximately 0.00000233,
with bias about 0.9975 and slope about 2.0012. Use `--steps 0` or `--steps 1` to
inspect the initial state or first update. Values are floating-point results,
not fixed-output strings. Ordinary package check/run/verify-cert, stale-source
refusal and runtime budgets remain in force. The solver CLI numerical suites
compare the results with the committed synthetic PyTorch references.

This public source revision is experimental, unreviewed and not admitted.
The previous package revision and development records remain unchanged.
