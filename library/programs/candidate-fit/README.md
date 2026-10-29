# Fit candidate constants in SIGIL

This local example tunes eight constants in either of two fixed expression
families using the existing numeric and autodiff packages. It reports constants,
gradients, training loss and validation loss. All fitting runs inside SIGIL/Wasm;
Python only displays its output. [The API](API.md) defines the expressions,
dataset, fixed initializers, bounds and binary report.

With the solver-enabled development CLI on PATH, from the repository root:

```sh
sigil package-lock --root library/programs/candidate-fit --dependency sigil/autodiff=library/packages/autodiff --dependency sigil/numeric=library/packages/numeric
sigil check --package library/programs/candidate-fit
python3 library/programs/candidate-fit/run.py --candidate 0 --steps 16
python3 library/programs/candidate-fit/run.py --candidate 1 --steps 16
```

Create the lock once on a fresh checkout; existing locks refuse overwrite.
The viewer accepts `--sigil PATH` and needs only Python's standard library.
For the ordinary CLI, pass `--input 1:16 --fuel 500000`. Smaller step counts,
including zero, expose the initial state or a partial optimization run.

The two models are fixed fixtures, not an arbitrary expression parser or a
connection to the separate GPU trial runner. This milestone establishes a
second consumer of numeric/autodiff and exercises constant fitting. A shared
candidate protocol and worker connection require their own concrete interface.

This public source revision is experimental, unreviewed and not admitted.
The previous package revision and development records remain unchanged.
