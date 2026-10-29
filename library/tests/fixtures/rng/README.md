# PCG reference fixture

The `upstream` directory retains the minimal C implementation from
`imneme/pcg-c-basic` revision `bc39cd76ac3d541e618606bcc6e1e5ba5e5e6aa3`,
with its Apache-2.0 license. See the
[SIGIL adaptation provenance](../../../packages/rng/PROVENANCE.md).

Local formatting changes to `pcg_basic.c` remove one trailing space in a comment
and one empty line at EOF to satisfy repository whitespace checks. The original
retrieved file's SHA-256 was
`b6582a071a8a090a293621523c063d125a532d772a2a1eb7d60b3e695fe47746`.
No C statement, header or license text is changed. The source hashes in
`pcg-v1.json` bind the actual local reference inputs, including this normalized
C file, rather than claiming a byte-identical upstream copy.

Regenerate the reference answers explicitly:

```sh
SIGIL_REGENERATE_RNG=1 python3 library/tests/fixtures/rng/generate.py
```

The generator compiles and runs the C reference independently of SIGIL. During
packaging, regeneration after whitespace normalization must retain every case,
draw and post-draw state; only the C source hash changes.
