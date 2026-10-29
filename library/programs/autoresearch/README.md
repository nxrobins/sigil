# Autoresearch composed from SIGIL libraries

This experimental consumer fits and evolves the real autoresearch candidates using
numeric, autodiff, optim, RNG, bytes, records, JSON, checkpoint and exchange packages.
Both discrete and hybrid arms use eight candidates, two elites, crossover and
mutation. One native call fits one candidate or breeds the next population;
complete state can be checkpointed between any two calls.
The earlier CPU/proposal examples remain regression references, not runtime
backends. This application uses no Python training, network or GPU worker.

From the repository root with a solver-enabled SIGIL CLI:

```sh
sigil package-lock --root library/programs/autoresearch --dependency sigil/autodiff=library/packages/autodiff --dependency sigil/numeric=library/packages/numeric --dependency sigil/optim=library/packages/optim --dependency sigil/records=library/packages/records --dependency sigil/json=library/packages/json --dependency sigil/rng=library/packages/rng --dependency sigil/bytes=library/packages/bytes/versions/0.1.0-public.5 --dependency sigil/checkpoint=library/packages/checkpoint --dependency sigil/exchange=library/packages/exchange
sigil check --package library/programs/autoresearch
python3 library/programs/autoresearch/run.py --candidate library/programs/autoresearch-cpu/candidates/sgd.json --rounds 3
```

The wrapper displays the fitted candidate, accepted/rejected steps, final
gradient and score. `--rounds 0` only evaluates; `--rounds 6` exercises the
maximum fitting-round limit for requests within the total-work bound.
The 12-instruction, 20-step maximum permits three rounds, not six; larger
combined requests refuse before evaluation. `--steps 0..20` chooses the task prefix.
Use `--candidate-out NEW_FILE` for create-new export and feed that file to the
earlier CPU evaluator to independently exercise the same accepted parameters.
Existing files or symlinks refuse overwrite.

Add `--record` to emit the native exact-bit JSON result instead of the display
summary. Native records preserve all numeric bits and bind the request; the
wrapper validates them before forwarding. This mode still supports create-new
candidate export. It is not yet a full-search checkpoint or resume command.

## Run and resume the search

After locking the ten-node graph above, use fresh output directory names:

```sh
python3 library/programs/autoresearch/search.py --generations 2 --transitions 5 --out-dir /tmp/autoresearch-part
python3 library/programs/autoresearch/search.py --generations 2 --resume /tmp/autoresearch-part/checkpoint-0005.json --out-dir /tmp/autoresearch-resumed
```

The same seed, stream, generations, task steps, arm and candidate budget must
be supplied on resume; SIGIL rejects a checkpoint from another configuration.
Defaults are seed 42, stream 54, twelve generations, twenty task steps and the
hybrid arm. `--arm discrete` disables fitting. `--transitions` limits this
invocation, not the total job. `--budget` caps scored candidates; exhaustion
refuses without publishing a new state. A completed run refuses further steps.

The Python driver forwards native requests and saves returned checkpoints in
create-new files. It never constructs the checkpoint JSON or evaluates,
mutates, fits or ranks candidates. Every earlier revision remains available;
existing output directories and files refuse replacement. An interrupted file
write can leave an incomplete newest file, which native restoration rejects.
Resume from the preceding complete revision into another new directory.

The [search protocol](SEARCH_API.md) defines the complete state, bounds and
identity checks. The solver CLI suite compares the search against committed
Torch/C references and tests checkpoint restoration. The generic KV adapter is
tested separately and is not used by this host-free file workflow.

## Exercise the evaluation exchange

Use the same native CPU fitter through versioned request/response messages:

```sh
python3 library/programs/autoresearch/search.py --generations 1 --steps 2 --evaluation exchange --job-id 1717171717171717171717171717171717171717171717171717171717171717 --transitions 5 --out-dir /tmp/autoresearch-exchange-part
python3 library/programs/autoresearch/search.py --generations 1 --steps 2 --evaluation exchange --job-id 1717171717171717171717171717171717171717171717171717171717171717 --resume /tmp/autoresearch-exchange-part/checkpoint-0005.json --out-dir /tmp/autoresearch-exchange-resumed
```

Choose a new 32-byte lowercase hexadecimal job identity for a new experiment;
the repeated example value is only a walkthrough fixture. The driver also binds
the freshly checked package certificate's artifact identity. Resume requires
the same job/program identity, configuration and exchange mode. It reads the
bounded `evaluation-identity.hex` companion file, so preserve that file with
the checkpoint. Changing the program requires an explicit new experiment;
this workflow does not silently migrate identity.

Each scoring transition saves a request and response in new files. Native
commands construct, decode, fit, package and accept the exchange; Python only
frames commands and transports returned bytes. Fitting and JSON packaging are
separate calls so the maximum candidate stays within the existing per-call
limits. Breeding still runs locally. A failure leaves earlier checkpoints and
any completed request/reply files; resume into a new directory from the last
complete checkpoint. Retrying may execute the worker again.

This exercises the host-neutral interface with a CPU worker, not a network
service or GPU runner. A matching response and unsigned certificate identity
do not authenticate an external score. The solver CLI suite exercises the CPU
exchange and rejects mismatched identities and malformed responses.

## Persist explicitly Public checkpoints in KV

The optional storage path uses the existing storage/KV packages through a
separately invoked [host example](../autoresearch-store/README.md). First lock
that three-node package and build its solver-enabled host as described there.
Then use new store/output directories:

```sh
python3 library/programs/autoresearch/search.py --generations 1 --steps 2 --transitions 5 --kv-store /tmp/autoresearch-store --storage-host target/debug/examples/autoresearch-storage --allow-public-checkpoint-import --out-dir /tmp/autoresearch-stored-part
python3 library/programs/autoresearch/search.py --generations 1 --steps 2 --resume-kv --kv-store /tmp/autoresearch-store --storage-host target/debug/examples/autoresearch-storage --allow-public-checkpoint-import --out-dir /tmp/autoresearch-stored-resumed
```

Use the opt-in only when you declare this job's checkpoint data Public. KV
results remain Internal in SIGIL; the trusted host explicitly imports them for
Public numerical computation. This does not publish them. The flag is required
again on every invocation, and is separate from read/write grants. It neither
changes compiler checks nor permits the storage tool through normal package-run.
The host itself is trusted code, not covered by the SIGIL package certificate.

Native search validates checkpoints before publication and after load. An
immutable local identity file binds configuration, evaluation mode, job and the
freshly checked program identity. Changing any requires a new experiment, not
silent migration. The Unix driver holds an advisory writer lease for the whole
invocation; use a local directory owned by this workflow and only cooperating
writers. It is not a distributed lock or concurrent compare-and-swap.

KV atomically replaces the latest complete envelope after comparing prior bytes.
The envelope includes a predecessor, and create-new files retain earlier
revisions. A timed-out publication has an uncertain outcome: resume with
--resume-kv to read and validate the stored value, rather than blindly retrying
the old write. A newer local file can exist even if its KV publication failed.
The workflow retains KV's OS-write-back durability, not database crash recovery.
File resume remains a separate path. Exchange mode supports the same storage
options and still requires its explicit job identity.

See [the precise protocol](API.md) for finite bounds, floating-point semantics
and errors. This is not historical Q16 trajectory equivalence or evidence of
improved real model training. The [public workflow](../../WORKFLOW.md) describes
setup, explicit upgrades and rollback.

This public source revision is experimental, unreviewed and not admitted.
The previous package revision and development records remain unchanged.
