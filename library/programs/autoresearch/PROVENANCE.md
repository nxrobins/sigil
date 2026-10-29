# Autoresearch fitting provenance

The application objective and instruction interpreter are reorganized from
the local CPU evaluator at source SHA-256
`dd8c95de98aa0d17f7101bcada6b0c2f1fae6d416012dc4823e008d06331a48c`.
Its [provenance](../autoresearch-cpu/PROVENANCE.md) pins the original
autoresearch-sigil clone and three seed records. Those files remain intact.

The fitting policy follows the original sign-based fine-tuner: strict
fitness improvement, bounded adaptive step size, and rejection preserving
accepted weights. This consumer uses one reverse sweep for all eight weights
and stages updates through the new reusable optim package, rather than
handwritten save/update/restore loops. It reuses accepted reports and needs no
extra evaluation merely to restore rejected weights.

Q16 initial step and maximum import exactly; multiplication/division of the
step and numerical evaluation use binary64. Intermediate sign-step overflow
refuses before clipping. Floating-point gradients and clipping follow the
CPU evaluator's documented profile, not the old dual-number implementation.

## Population search

The population policy follows the same preserved original clone: three seeds,
eight candidates, two elites, stable fitness ranking, top-half parent choice,
one-point instruction crossover with alternating-parent weights, then one of
six mutations. Both arms finish with scoring without additional fitting.
Seeded PCG replaces the original LCG; binary64 reverse mode replaces Q16 duals.
Consequently the old random stream and numerical trajectory are not retained.

The fitting implementation moved into tool_fit without changing its numerical
body. Its input decoding and binary report copying now call records::unhex and
bytes::copy_into, replacing the local nibble decoder and copying loops without
changing the AFIT formats. Instruction deletion also uses overlap-safe library
copying. tool_population and tool_search contain application policy and the state
machine; their copying, randomness, number fitting and wire encoding come from
library packages. tool_state composes generic checkpoint operations with this
application's schema and job identity. Earlier CPU/proposal consumers and the
original clone remain independent regression inputs.
