# Autoresearch seed provenance

The seed records transcribe `seed_sgd`, `seed_momentum` and `seed_step_decay`
from `sigil/autoresearch.sigil` in
[nxrobins/autoresearch-sigil](https://github.com/nxrobins/autoresearch-sigil/tree/d01fbfe12df434408a19ffac2e8c602c681739a9).
Source revision: `d01fbfe12df434408a19ffac2e8c602c681739a9`.
Source file SHA-256: `04b30dcb1498258ce66e210cab31cc1120bd5c957c6ea1c0592c40d13ccbd54b`.
The local clone was inspected on 2026-10-28 and is not modified by this work.

Instruction integers preserve its opcode/register conventions. Seed weights
remain the original Q16 integers, including -3277 rather than replacing it
with an idealized -0.05. The importer divides by 65536; neither seed structure
nor seemingly unused instructions are cleaned up. The new evaluator and
PyTorch reference implementation are original code, not vendored source.

The seed records are inputs, not measured answers. Fresh PyTorch execution
generates the independent numerical answers in
`library/tests/fixtures/autoresearch-cpu/torch-v1.json` under the explicitly
different floating-point profile in [the API](API.md). No claim is made that
the source Q16 search loop or GPU training script was run by this integration.
