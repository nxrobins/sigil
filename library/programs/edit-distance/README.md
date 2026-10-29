# Byte edit distance using bytes and fmt

This existing SIGIL Levenshtein tool uses `sigil/bytes` for bounds-checked row
reads/writes and `sigil/fmt` for decimal output. Version `0.1.0-public.2` retires
its remaining local endian helpers while preserving the distance recurrence and
input semantics. This revision explicitly selects bytes `0.1.0-public.5`
and also retires the first-LF byte scan through `bytes_scan::find_byte`. All three
packages remain experimental, unreviewed and not admitted.

With a solver-enabled `sigil` on PATH, run from the repository root in Bash or zsh:

```sh
sigil package-lock --root library/programs/edit-distance --dependency sigil/bytes=library/packages/bytes/versions/0.1.0-public.5 --dependency sigil/fmt=library/packages/fmt
sigil check --package library/programs/edit-distance
sigil run --package library/programs/edit-distance --input $'kitten\nsitting'
```

The final command writes exactly `3`, with no appended newline. The shell's
`$'...\n...'` quoting supplies the LF separator. Reuse the generated lock for
later checks/runs; lock creation refuses to overwrite it. When upgrading from
the earlier two-node version, preserve the old project/lock and deliberately
create the new three-node lock; an old lock must reject changed source. See the
[public workflow](../../WORKFLOW.md) for setup and deliberate upgrades,
and the [API contract](API.md) for byte semantics, ownership and fuel limits.

The package identity is `edit-distance/tool`; `tool` owns the canonical execution
module. The manifest's evidence hashes bind the API card, API, this README and
source bytes, not an accepting certificate. Lock and dependency cache are generated.

The approved standalone reference at `tools/task098_levenshtein_distance.sigil`
remains unchanged as the before-migration oracle and training input. The public
CLI package-tools suite compares the composed tool against that reference.

This public source revision is experimental, unreviewed and not admitted.
The previous package revision and development records remain unchanged.
