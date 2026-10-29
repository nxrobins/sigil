# SIGIL libraries and examples

SIGIL's experimental libraries provide reusable code for ordinary programs and
bounded CPU search. They ship as source in this repository; there is no public
package registry or automatic package admission. Use a solver-enabled CLI from
the same revision and pin every provider by version and content hash.

## Available packages

| Package | Purpose |
| --- | --- |
| [fmt](packages/fmt/README.md) | Integer and byte output formatting |
| [bytes](packages/bytes/versions/0.1.0-public.5/README.md) | Byte access, big-endian reads, copying, bounded output, search and equality |
| [numeric](packages/numeric/README.md) | Small CPU matrices and numerical operations |
| [autodiff](packages/autodiff/README.md) | Fixed-capacity scalar reverse-mode differentiation |
| [optim](packages/optim/README.md) | Bounded optimization of candidate constants |
| [rng](packages/rng/README.md) | Seeded reproducible random numbers |
| [records](packages/records/README.md) and [json](packages/json/README.md) | Exact-bit candidate records and bounded JSON output |
| [checkpoint](packages/checkpoint/README.md) | Validated checkpoint envelopes |
| [exchange](packages/exchange/README.md) | Host-neutral evaluation requests and responses |
| [kv](packages/kv/README.md) and [storage](packages/storage/README.md) | Explicit-capability persistence for declared Public checkpoints |

The sources, API contracts, manifests, synthetic numerical fixtures and native
CLI regression tests are public. The public byte-provider revisions preserve
each earlier API subset, so explicit
upgrade and rollback can be exercised. Every public provider has a new version
and metadata hashes; its implementation bytes match the preceding dogfood
revision. The old directories and private admission records remain unchanged
and are not exported. All packages remain experimental, unreviewed and not admitted.

## Start with a working program

Build the CLI with `cargo build -p sigil --features solver --locked` after
following the repository's compiler prerequisites. Put `target/debug/sigil` on
PATH. The [PNG reader](programs/png-dimensions/README.md) and
[word-frequency tool](programs/word-frequency/README.md) combine bytes and fmt.
The [linear-regression example](programs/linear-regression/README.md) and
[candidate fitter](programs/candidate-fit/README.md) exercise numeric/autodiff.
Each example gives its exact first-time `package-lock` command.

For a new byte-processing tool, `sigil package-init --help` describes the
tested starter. `package-refresh` handles metadata-only changes. For an
[explicit upgrade](WORKFLOW.md#explicit-upgrade-and-rollback), create a
new project with the selected providers and retain the previous root for rollback.
Use each command's help for required paths. Existing locks are never silently
replaced. `check --package`, `verify-cert --package` and `run --package` use the
same dependency graph and refuse stale sources or mismatched evidence.

## Autoresearch on CPU

The [composed search example](programs/autoresearch/README.md) provides bounded
evaluation, fitting, seeded mutation, ranking, checkpoint/resume and an
evaluation exchange. Follow its nine-provider lock command, then run the Python
transport driver. SIGIL performs the numerical and search operations; Python
transports bytes and creates checkpoint files. The optional KV host is separate
and requires explicit capabilities and Public-checkpoint opt-in.

The second [fixed-dataset regression workload](programs/autoresearch-regression/README.md)
uses the same nine providers unchanged. It searches optimizer programs against
four synthetic training rows and reports two validation rows separately. Its
PyTorch references, native search comparisons and file-resume tests exercise a
different objective, with distinct task and dataset identities. This addition
is experimental and packaged separately from the initial library publication.

This is not a GPU backend, Torch launcher or general tensor framework. An
external GPU worker is still a separate integration. Unsigned certificate
identities bind program inputs, not the truth of an external fitness result.

## Tests and publication

The solver-enabled Rust integration suites in `crates/sigil-cli/tests` exercise
the native package workflow, numerical operations and refusal paths. Python
wrapper tests live in `library/tests`; numerical reference fixtures are fixed
synthetic inputs, with opt-in generators rather than runtime Torch dependencies.
Changing a generator does not authorize replacing its expected answers.

Source publication does not grant candidate admission, registry publication,
new host capabilities or authority to bypass branch protections. Private
research/training archives, trial evidence, admission governance and the legacy
private fmt judge harness are not exported. Public changes are reviewed as
ordinary pull requests; no private Git history is included.
