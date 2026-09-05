# Contributing to SIGIL

SIGIL is a capability-safe language with effects, taint, and linear ownership, compiling to
wasm, with a self-hosting compiler, an independent reference interpreter, and mechanized
soundness proofs. It is built by agents as much as by people, so its rules live in tests
rather than in reviewers' heads. This file is the contribution bar. It is short because the
repository enforces most of it; `CLAUDE.md` is the same contract in the form an agent session
reads, and [`docs/STYLE.md`](docs/STYLE.md) is the full guide with evidence.

## The creed

1. **A claim no test enforces is a hope.** [`docs/CLAIMS.md`](docs/CLAIMS.md) is the single
   machine-checked authority on what SIGIL proves. State nothing as proven without a `@test:`
   tag; pin every load-bearing number at its measured value, never a documented one.
2. **Fail closed, and say so.** Every gate and fallback names its failure direction in a
   comment. No silent degradation, no best-effort partial output.
3. **An absence claim needs a proven detector.** A census, comparator, or "there are no X"
   test ships with an anti-stub shown detecting a planted X, in the same file.

## Build and test

    cargo test --workspace --no-default-features        # the gating lane
    cargo fmt --all && cargo clippy --workspace --all-targets --no-default-features -- -D warnings
    python interp/test_parse.py && python interp/test_eval.py
    python tools/selfhost_ergonomics_census.py --ratchet

`--no-default-features` is load-bearing: the default `solver` feature needs a native Z3, which
most machines lack, and CI runs that lane separately with a pinned Z3. `cargo test` exits 0 on
zero tests, so an un-flagged invocation can be a silent no-op.

## Every change is one of two classes

The parity manifest, `tests/parity/manifest.tsv`, records the compiler's output over the
fixture corpus and `crates/sigil-compiler/tests/parity_manifest.rs` enforces it.

- **Parity-preserving** (refactors, dependency bumps, docs, style): the manifest is untouched
  in your diff. A green checker plus an untouched manifest is a proof of zero behavior change.
- **Output-changing** (features, codegen, diagnostic wording, hints included): regenerate and
  commit the manifest; the changed rows are review content.

      SIGIL_PARITY_REGENERATE=1 cargo test -p sigil-compiler --no-default-features \
          --test parity_manifest -- --ignored regenerate_parity_manifest --nocapture

## What a pull request carries

- **Tests for the behavior, in the idiom of the file next to yours.** Diagnostics are asserted
  as exact code sets, never as substrings of debug output. Every reject fixture has an accept
  twin. Security fixtures carry one `// MUTATION_SITE` line.
- **Fixture headers** in order: a description line (the corpus extractor reads it as prose),
  then the machine expectation (`// expect-error: T044, T088`, exact codes).
- **Ledger updates in the same commit.** If a claim changes, [`docs/CLAIMS.md`](docs/CLAIMS.md)
  changes with it; if a test the ledger names is renamed, the ledger is renamed too. Debt goes
  to a ledger, never to a `TODO`: soundness debt to
  [`docs/RESIDUAL_RISKS.md`](docs/RESIDUAL_RISKS.md), coverage debt to
  `docs/diagnostic-test-gaps.txt`, attack-surface debt to
  [`tests/attack/KNOWN_GAPS.md`](tests/attack/KNOWN_GAPS.md).
- **Census discipline.** Code-shaped tokens such as `T044` are counted across
  `crates/**/tests`, comments and strings included, against pinned reference counts. Use codes
  that already carry direct test references, or split the literal with `concat!`.
- **Goldens through their regenerators.** Committed goldens and manifests are never edited by
  hand; every failure message names the exact env-armed command that regenerates them.
- **Source hygiene the censuses check:** a leading `//!` module doc on every new source file
  (its role and the constraint it carries), `.expect("the invariant that guarantees this")`
  rather than a bare `.unwrap()`, and LF line endings for `.sigil`, `.tsv`, and the other
  text files `.gitattributes` pins.

## How changes land

Every change reaches `main` through a pull request; nobody pushes to it directly, the
maintainer included. A pull request merges when the six required lanes are green (the build
and test lane, formatting and clippy, the solver lane, hygiene — which includes the DCO
sign-off check and the token sweep — the interpreter double-compilation, and workflow
validity) and, for changes from anyone other than the maintainer, one approving review from a
code owner (`.github/CODEOWNERS`). Workflow runs for pull requests from forks wait for the
maintainer's approval before they execute, and the workflow token is read-only; no lane uses a
secret. Release tags are created by the maintainer only.

## Proofs

The Lean development under `proofs/lean` is gated by `scripts/check-no-sorry.sh`: no `sorry`,
no `admit`, no kernel-external `native_decide`, a committed theorem manifest that must equal
the elaborated census, and an exact axiom allowlist. Run its `--self-test` first; it proves
the gate fails closed before the verdict counts. A theorem added or removed is a manifest
change in the same commit.

## Reporting a security issue

See [`SECURITY.md`](SECURITY.md). Please do not open a public issue for a program that the
compiler accepts and should not.

## Licensing and sign-off

SIGIL is dual-licensed under the MIT License and the Apache License 2.0
([`LICENSE-MIT`](LICENSE-MIT), [`LICENSE-APACHE`](LICENSE-APACHE)); recipients choose either.
Contributions are accepted under the same terms.

Every commit must carry a `Signed-off-by:` trailer certifying the
[Developer Certificate of Origin](DCO): that you wrote the change or have the right to submit
it under the project's licenses. `git commit -s` adds the trailer from your Git identity; the
hygiene lane fails a pull request with an unsigned commit, and `git commit --amend -s` fixes one
after the fact. No contributor license agreement is required.
