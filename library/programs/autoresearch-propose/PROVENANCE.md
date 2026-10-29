# Consumer provenance

Mutation kinds and candidate layout are adapted from the inspected local
autoresearch-sigil clone at revision
`d01fbfe12df434408a19ffac2e8c602c681739a9`, whose
`sigil/autoresearch.sigil` SHA-256 is
`04b30dcb1498258ce66e210cab31cc1120bd5c957c6ea1c0592c40d13ccbd54b`.
The clone stays untouched. The existing CPU example documents its numerical
migration and preserved seeds. This consumer uses that same strict candidate
format but replaces handwritten random generation with imported PCG32 and
floating-point mutation jitter. It does not claim old-seed trajectory equality.

The reusable algorithm's own reference/license are recorded in
[rng provenance](../../packages/rng/PROVENANCE.md). New application transport,
validation and checked mutation code is experimental source under the
repository license, not an admitted package or exported training program.
