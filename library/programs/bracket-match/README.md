# Bracket matching using fmt

This existing SIGIL bracket validator imports `sigil::fmt` and calls
`fmt::boolean(valid == 1)` instead of maintaining a duplicate boolean renderer.
It checks nested `()`, `[]` and `{}` and ignores other bytes. It does not parse
strings or comments. The formatter and consumer remain experimental,
unreviewed and not admitted.

From the repository root, with a solver-enabled `sigil` on PATH:

```sh
sigil package-lock --root library/programs/bracket-match --dependency sigil/fmt=library/packages/fmt
sigil check --package library/programs/bracket-match
sigil run --package library/programs/bracket-match --input 'a{b[c(d)e]f}g'
sigil run --package library/programs/bracket-match --input '([)]'
```

The last two commands write exactly `true` and `false`, without appended
newlines. Use the generated lock for repeated runs; lock creation refuses to
overwrite it. See the [public workflow](../../WORKFLOW.md) for
setup, source pins, bounded execution and deliberate upgrades, and the
[API contract](API.md) for byte semantics and ownership.

The consumer identity is `bracket-match/tool`; `tool` owns the canonical
execution module under the existing package naming constraint. The manifest's
evidence hashes bind the actual API card, API, this README and source bytes,
not an accepting certificate. Lock and dependency cache files are generated.

`tools/task092_validate_bracket_matching.sigil` remains unchanged as the approved
standalone training/reference program and before-migration oracle. Runtime
regressions are in the public CLI package-tools suite, including the ordinary
solver CI lane. See the [public workflow](../../WORKFLOW.md) for setup.

This public source revision is experimental, unreviewed and not admitted.
The previous package revision and development records remain unchanged.
