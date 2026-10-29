# Split count, using fmt

This existing SIGIL tool now imports `sigil::fmt` instead of maintaining its own
decimal renderer. It counts comma-separated fields, not quoted CSV records.
The formatter and this consumer remain experimental and unreviewed.
The consumer identity is `split-count/tool`: `tool` owns the canonical execution
module, in accordance with the existing package module-name constraint.

From the repository root, with a solver-enabled `sigil` on PATH:

```sh
sigil package-lock --root library/programs/split-count --dependency sigil/fmt=library/packages/fmt
sigil check --package library/programs/split-count
sigil run --package library/programs/split-count --input 'alpha,beta,gamma'
```

The last command writes exactly `3` (no appended newline). No package-specific
Python driver, private judge or manual graph/certificate assembly is needed.
See [public workflow](../../WORKFLOW.md) for setup,
repeated runs, stale pins and upgrading. The manifest is checked in; the local
lock and dependency cache are generated. The manifest's evidence hashes refer
to the actual API card, API, this README and source bytes, not an accepting certificate.
Runtime equivalence against the original standalone tool is tested in the
CLI package-tools suite. The original remains byte-for-byte unchanged at
`tools/task018_split_count.sigil` as the frozen standalone training/reference
program. It is the before-migration oracle, not this application's execution
path. The public CLI package-tools suite retains those runtime comparisons.

This public source revision is experimental, unreviewed and not admitted.
The previous package revision and development records remain unchanged.
