# Public library workflow

Use the source packages in `library/packages` and runnable consumers in
`library/programs`. They are experimental public revisions, not admitted
registry packages. Dependencies are explicitly selected by path and pinned by
version and content hash; no dependency is downloaded or selected implicitly.

## Build the compiler

Install the repository-pinned Rust/Lean prerequisites and native Z3 as described
in [CONTRIBUTING](../CONTRIBUTING.md). From the repository root:

```sh
cargo build --locked -p sigil --features solver
export PATH="$PWD/target/debug:$PATH"
sigil --version
```

The version must report solver on. If discovery needs configuring, set
`Z3_SYS_Z3_HEADER` and `LIBRARY_PATH` to the installed native header/library
locations. Solver-off tests are useful portability checks, not package execution
evidence. No unverified-certificate override enables package execution.

## Create a bytes and fmt tool

Choose a new directory. The starter derives tool names, manifest hashes and the
three-node lock from the selected providers:

```sh
project_workspace=$(mktemp -d)
sigil package-init --root "$project_workspace/header" --namespace header --dependency sigil/bytes=library/packages/bytes/versions/0.1.0-public.4 --dependency sigil/fmt=library/packages/fmt
sigil check --package "$project_workspace/header"
```

Edit its `src/tool.sigil`, API, card and README, then use
`sigil package-refresh --root "$project_workspace/header"` to bind the reviewed
application changes. Refresh preserves previous state and refuses changed
dependencies. The starter/refresh profile is for bytes/fmt tools, not arbitrary
numeric or host-capability programs.

For a ready-made application, follow the
[PNG reader](programs/png-dimensions/README.md),
[word counter](programs/word-frequency/README.md), or
[bracket validator](programs/bracket-match/README.md).
Run each `package-lock` command only once on a fresh materialization. Existing
locks refuse replacement; repeated checks/runs use the existing lock and cache.

## Explicit upgrade and rollback

Keep the previous application root, lock, cache and certificates intact. Create
a separate candidate with the new providers, then copy the reviewed application
files and refresh that candidate:

```sh
upgrade_workspace=$(mktemp -d)
sigil package-init --root "$upgrade_workspace/png-next" --namespace png-dimensions --dependency sigil/bytes=library/packages/bytes/versions/0.1.0-public.4 --dependency sigil/fmt=library/packages/fmt
cp library/programs/png-dimensions/src/tool.sigil "$upgrade_workspace/png-next/src/tool.sigil"
cp library/programs/png-dimensions/API.md library/programs/png-dimensions/README.md library/programs/png-dimensions/api-card.json "$upgrade_workspace/png-next/"
sigil package-refresh --root "$upgrade_workspace/png-next"
sigil check --package "$upgrade_workspace/png-next" --cert "$upgrade_workspace/png-next.cert.json"
sigil run --package "$upgrade_workspace/png-next" --cert "$upgrade_workspace/png-next.cert.json" --input 89504e470d0a1a0a0000000d494844520000032000000258
sigil verify-cert --package "$upgrade_workspace/png-next" --cert "$upgrade_workspace/png-next.cert.json"
```

The result is `800x600`, without a newline. Rollback selects the preserved old
root and its own lock/cache/certificate. Do not place an old lock over changed
source, rewrite cached providers, or use metadata refresh as an implicit upgrade.
Public revisions also require explicit new selection: identical SIGIL source
does not make changed metadata, version and graph identities interchangeable.

## Numerical and search examples

[Linear regression](programs/linear-regression/README.md) and
[candidate fitting](programs/candidate-fit/README.md) compose numeric/autodiff.
The viewers need only Python's standard library and display native output.
PyTorch is an independent test oracle, not a runtime backend.

[Autoresearch](programs/autoresearch/README.md) gives the nine-provider lock
command, bounded search, file checkpoints/resume and the CPU evaluation exchange.
The optional [storage consumer](programs/autoresearch-store/README.md) requires
explicit read/write capabilities and an opt-in for operator-declared Public
checkpoints. It is separate from ordinary package-run.

All native checks, fuel/memory ceilings and certificate refusals remain active.
Source publication neither authenticates external fitness results nor grants
registry admission, GPU execution or permission to bypass protected merges.
