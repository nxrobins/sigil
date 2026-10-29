# Fixed regression workload: local validation

Implementation and local checks on 2026-10-28. This is an experimental second
CPU search workload, not a release, admission decision or GPU benchmark.
The earlier quadratic application and all nine provider versions, hashes and
implementation files remain unchanged. No compiler or runtime implementation
changed. Hosted CI was not run. Source delivery through draft PRs is authorized;
merge, registry release and admission are not part of that authorization.

## Executed checks

The native executable was built with solver support. Its SHA-256 was
`786e2844c95397928381c67c305e24e1700cea80d2938f58da0813f178e4368d`.
Each native test batch made a fresh consumer copy without a lock or dependency
cache, ran the nine-provider package-lock command, and required a new
solver-verified package check. Successful runs required `solver_verified` and
`admission=not_evaluated`. Python used `-W error::ResourceWarning`.

Ten test methods passed in separate local batches, with no skipped native
tests. This was not a single full-suite invocation:

| Coverage | Executed result |
| --- | --- |
| Three contract tests | Dataset/hash/configuration validation, opt-in-only reference generation, planted numeric/state/history errors detected |
| Native fitting | 33 PyTorch cases: losses, parameters, momentum, all eight gradients, accepted weights, fitting decisions and traces; three finite-difference comparisons |
| Native search | All 18 states in each of four trajectories: two seed/step configurations, both discrete and hybrid arms; structural fields exact, numerical fields within tolerance |
| Resource and identity refusals | Wrong task/dataset/checkpoint compatibility, malformed bounds, nonfinite data, excess work and fuel exhaustion; original quadratic accept twins still execute |
| Live mutations | A recompiled gradient-sign fault fails the oracle comparison; changed reporting rows leave fitting bytes identical but change reporting; the driver rejects file/native data mismatch |
| Direct file resume | Both arms complete one generation; uninterrupted and interrupted-at-five/resumed final checkpoint bytes agree, as do training and reporting losses; earlier files remain unchanged on refusal |
| CPU exchange | A complete request/decode/fit/reply/accept transition matches direct execution; wrong dataset, job and replay refuse; all configuration and identity bytes fit the unchanged 128-byte context limit |
| Exchange file resume | Two transitions plus two resumed transitions match four direct transitions; wrong mode, job, program identity and corrupt checkpoint refuse before output-directory creation; previous files remain unchanged |

The reference generator was actually executed with PyTorch 2.14.1, CPU float64,
one thread and deterministic algorithms. It uses autograd over individual
training observations, independently of SIGIL's sufficient-statistic formula.
The search reference uses the existing upstream C PCG implementation. Numeric
comparisons use absolute/relative tolerance 1e-10; finite differences use
2e-4/2e-6. Structural fields and acceptance decisions must match exactly.
PyTorch warned that NumPy was unavailable; this generator does not use NumPy.

A complete native demonstration used seed 42, one generation, twelve training
steps and the hybrid arm: 16 candidate evaluations, 40 graph evaluations,
24 accepted fitting proposals and 17 transitions. It produced slope
2.0984951477932623 and bias 0.9524349020185465, training MSE
0.11250566145041041 and validation MSE 0.009704124864021734. These describe this
synthetic example only, not general optimizer quality.

Additional local checks passed: the two provider/document inventory tests,
four preserved search-driver tests, 25 CI-hygiene tests, Ruff and Rust formatting.
The future solver CI step requires all ten new tests and refuses skipped native
execution; adding that step did not execute hosted CI.

## Reproduce

First follow [README.md](README.md) for the fresh package workflow. Set
SIGIL_INTEGRATION_CLI to an actual solver-enabled executable, not a command
name that is unavailable to subprocesses:

```sh
SIGIL_INTEGRATION_CLI=/absolute/path/to/sigil python3 -W error::ResourceWarning -m unittest -v library.tests.test_autoresearch_regression
```

The fixed reference answers are checked in. Normal native tests do not require
Torch. To independently regenerate them in an environment with PyTorch 2.14.1
and a C compiler, write a new file and compare it before any replacement:

```sh
SIGIL_GENERATE_REGRESSION_REFERENCE=1 python3 library/tests/fixtures/autoresearch-regression/generate_reference.py > /tmp/regression-reference-new.json
cmp /tmp/regression-reference-new.json library/tests/fixtures/autoresearch-regression/torch-pcg-v1.json
```

## Corrections and limits

An initial request used 144 context bytes and correctly hit the existing
exchange provider's size refusal. The consumer now packs its bounded settings
losslessly into 32 bytes, leaving 64 for job/program and 32 for dataset identity.
The provider and its ceiling were not changed; the corrected exchange and resume
tests passed. An initial large-u64 literal inference issue was corrected in the
consumer using explicitly typed words, without compiler changes.

The source-export link guard enumerates committed HEAD. Before this consumer
was committed, it could not resolve the catalog link to the new files. Source
delivery requires rerunning that gate against the commit; the earlier local
success does not waive it. The
export selections name only this program, its synthetic references and test;
private material remains excluded by default.

The precommit export suite finished at 11 passed and this one link failure.
A separate working-tree supplement included the untracked files:
2844 selected paths and 644 relative links passed, with planted refusals checked.
It does not mark the committed-tree gate passed. The new public files use the
repository's validation-set terminology; independently regenerating the
PyTorch reference after that field rename preserved every numerical answer and
search state.

Publication follow-up: after implementation commit
`56e98a4519cc13b1ec7a16e927effa8b3b294749`, all twelve committed-tree export tests
passed, including the formerly unresolved catalog link. The source exporter
verified the selected output byte-for-byte against that commit. Its twenty
self-test probes and the public token-sweep self-test passed. Hosted CI remains
skipped; these are local publication checks, not protected-merge approval.

The application caps inner training at twelve steps, retains the 768-node tape
and existing engine/cooperative-fuel and memory limits. The maximum tested
fitting shape is twelve instructions by twelve steps by three fitting rounds;
a smaller shape also exercises six rounds. This is not throughput evidence or
coverage of arbitrary datasets, long searches or GPU training. The new driver
supports file persistence, not a new KV integration. Unsigned program and data
identities are compatibility checks, not worker authentication or score proofs.
