# CSIR release-evidence records

`docs/CLAIMS.md` is the authority on proven guarantees. The v8 and v9 TOML files
in this directory are pending rollout records, not completed releases. The v8
record retains its historical meaning. The v9 verifier and Public theorem are
source-level, kernel-checked claims; this pending template does not attest the
compatibility matrix, cross-platform evidence, or a tagged release.

## Pending-template check

Python 3.11 or later is required. Run the refusal self-tests before the template
check, as separate required CI steps:

```sh
python tools/validate_release_evidence.py --self-test
python tools/validate_release_evidence.py --template docs/release-evidence/csir-v9-dual-gate.toml
```

The second command succeeds only for a strictly pending template: no completed
lane, measured result, release identity, or retirement claim is permitted. Its
success means **release remains blocked**, not that the release gates are green.
Unknown or missing fields, missing checks, and disabled mandatory gates reject.
The self-tests use synthetic in-memory records and scratch logs; they never
create a Git tag or produce a retained release record.

## Preparing actual tagged evidence

Actual evidence is a separate retained CI bundle, not an edit replacing the
committed pending template. Recording a commit's own hash inside that commit
would require a self-reference. Keep the subject commit immutable; generate the
evidence bundle separately and name the already existing tag and peeled commit.
The validator performs read-only Git operations and never creates tags, uploads
artifacts, publishes releases, or changes any gate.

Copy the template into that bundle only when assembling real measured evidence:

- Set `state = "complete"`, the exact `owner/repository`, existing tag, full
  lowercase subject commit, and actual Rust and Lean toolchains. The tagged
  subject must declare CSIR v9 and certificate schema v9. Its pinned Lean
  toolchain must match the record.
- Retain every mandatory gate as `true`, `retirement_eligible = false`, and the
  exact unresolved-risk list containing SR-013 and SR-017. A later retirement
  decision is outside this record format.
- Complete every named check with `status = "passed"`, `executed = true`, a
  positive integer `cases`, the identical subject commit, an exact GitHub job
  URL, a canonical bundle-relative artifact path, and its lowercase SHA-256.
  Cases mean actually executed tests, proof/audit checks, or benchmark samples,
  as appropriate; zero-test filtered runs do not qualify. A shared job or log
  is acceptable only when it really executed all the named checks it supports.
- Supply numeric measurements, not stringified numbers. Corpus regressions and
  unexplained disagreements must be zero; approved policy rejections must be
  separately enumerated and justified in the corpus artifact. Here
  `accepted_corpus_regressions` counts changes outside that approved set; the
  corpus artifact must account for both sets without silently reclassifying
  unexplained failures as approved policy rejections. The warm median must be below
  one millisecond, the p95 at least the median, and the existing self-host trio
  canary at most five seconds. Initialization is a separate measurement.
- Record a positive peak-memory measurement, a separately reviewed positive
  memory limit, and successful execution of at least one million records. The
  validator checks the peak against the declared limit; it does not decide
  whether that limit is an appropriate release budget.

Platform evidence includes actual Linux, macOS ARM64, macOS x86-64, and Windows
MSVC execution. An Intel Mac cross-build without execution, skipped job,
cancelled job, or unavailable runner does not satisfy the inventory. Existing
CI portability success must not be substituted for execution if its Rosetta
probe took the build-only branch. Workspace solver-on/off checks and named
consumer checks remain separate obligations even when one job executes several.

The proof artifacts must contain the audited independent-length Public theorem
chain, exact claim signatures and dependency closure checks, and preservation
of the separate SecretCT result. Native/decoder/diagnostic parity, occurrence
mutants, and constructor inventory each have their own mandatory record. A log
that merely repeats their names is not evidence that they ran.

```sh
python tools/validate_release_evidence.py --tagged /path/to/bundle/evidence.toml --artifacts /path/to/bundle --repo /path/to/checkout
```

This command checks the existing tag/subject relationship, typed completeness,
thresholds, nonempty regular artifacts, and exact artifact digests. It rejects
absolute paths, path traversal, and symlink components. Artifacts are hashed in
bounded-size chunks; the TOML record itself has a fixed byte ceiling.

## Trust boundary: this is not CI attestation verification

Neither a TOML `passed` string nor a matching hash proves that CI ran. This
offline validator does **not** fetch job results, verify signatures, authenticate
artifact provenance, or prove that a log supports the claimed measurements. A
successful tagged check is structural evidence validation only, explicitly not
release authorization. An actual release still requires independently verified
CI run/job identity, success and execution status, subject commit, and artifact
provenance for every check, plus review of the logs and memory budget. Missing
or unauthenticated evidence leaves the release blocked; there is no override in
this script that turns such a gap into approval.

No tagged release has been recorded by adding these files. No CI result, theorem
completion, risk resolution, or gate retirement is claimed.

## CI and release-enforcement boundary

The main CI and Lean workflows run for pull requests, pushes to `main`, and
`merge_group` checks targeting `main`. Repository tests pin the required job
names and the active commands for the production v9 native verifier, schema-v9
certificate and host-profile/runtime binding, warm latency, Lean build/audit,
and this validator's refusal and pending-template modes. `hygiene` is part of
that pinned required-context set because it owns the release-evidence checks.

Branch protection itself is GitHub state, not source in this repository. The
pins prove that the contexts can be produced; they cannot prove that GitHub is
currently configured to require them. Release administrators must independently
verify that `hygiene`, `test`, `checks`, `solver`, `interp-ddc`,
`workflows-parse`, and `λ-SIGIL soundness (Lean 4)` are required for `main`,
including its merge queue.

There is deliberately no tag-triggered authorization workflow yet. A tag job
could run the structural `--tagged` validator only after obtaining the separate
retained bundle, but this repository has no authenticated mechanism that binds
that bundle to the named GitHub jobs. Treating a checked-in file, an arbitrary
download URL, or a syntactically plausible Actions URL as attested evidence
would fabricate the missing provenance. Add a tag/release path only together
with authenticated artifact acquisition and verification of every job's subject
commit, conclusion, execution status, and retained log. Until then, tags and
GitHub releases remain externally controlled operations and cannot by themselves
make the pending v9 rollout release-eligible.
