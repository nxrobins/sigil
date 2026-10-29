# Word frequency using bytes and fmt

This experimental library consumer of `tools/task096_word_frequency.sigil` uses the
shared u32 operations for word offsets, the fixed-capacity `bytes_out` builder for
assembly, and `fmt::decimal_i64` for counts. The explicitly selected
bytes version is `0.1.0-public.5`; `bytes_scan::equal` also retires the local
word-equality loop. No compiler/runtime mechanism is added. The original
standalone tool remains unchanged.

From the repository root, use a current solver-enabled SIGIL CLI:

```sh
sigil package-lock --root library/programs/word-frequency --dependency sigil/bytes=library/packages/bytes/versions/0.1.0-public.5 --dependency sigil/fmt=library/packages/fmt
sigil check --package library/programs/word-frequency
sigil run --package library/programs/word-frequency --input 'red blue red'
```

The exact output is `red:2,blue:1`, without a newline. Dependencies are selected
explicitly and content-pinned in a three-node graph; a changed source must not
silently repin an existing lock. Generated locks and cache files remain local.
Lock only a fresh materialization. Preserve the old application root, lock,
cache and certificates before an explicit dependency upgrade; refresh refuses
dependency changes. See the [public workflow](../../WORKFLOW.md).

[The API contract](API.md) defines raw-byte word boundaries, ordering, ambiguous
punctuation and execution limits. Negative byte-operation results refuse
execution. Builder failure is sticky, so `finish` refuses instead of returning
partial output. Local tests do not satisfy GitHub's required merge checks.

This public source revision is experimental, unreviewed and not admitted.
The previous package revision and development records remain unchanged.
