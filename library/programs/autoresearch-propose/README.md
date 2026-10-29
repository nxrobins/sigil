# Autoresearch candidate proposals

This application consumes the [seeded RNG package](../../packages/rng/README.md).
It mutates the actual bounded autoresearch candidate records in native SIGIL;
the wrapper only validates/transports data. The handwritten LCG is absent.
No GPU, network, disk grants, host evaluator or PyTorch runtime is used.

From the repository root with a solver-enabled SIGIL compiler:

```sh
sigil package-lock --root library/programs/autoresearch-propose --dependency sigil/rng=library/packages/rng --json
sigil check --package library/programs/autoresearch-propose --json
python3 library/programs/autoresearch-propose/run.py --sigil /absolute/path/to/sigil --candidate library/programs/autoresearch-cpu/candidates/sgd.json --seed 42 --stream 54
```

The output is a proposal checkpoint containing the new candidate and RNG state.
Save it as a new file and pass `--resume FILE` instead of seed/candidate options
for the next mutation. Use `--candidate-out NEW_FILE` to export the candidate
with create-new semantics, then evaluate it with the CPU example's run.py.
The compiler and JSON wrapper are not required libraries inside the algorithm.

This changes the old random stream and Q16 mutation rounding deliberately.
It is not a complete search: no selection, crossover, fitting loop or archive
is claimed. A proposal checkpoint is not a whole-search checkpoint. See
[the exact contract](API.md) and [public workflow](../../WORKFLOW.md).
The [public workflow](../../WORKFLOW.md) describes setup and explicit pins.

This public source revision is experimental, unreviewed and not admitted.
The previous package revision and development records remain unchanged.
