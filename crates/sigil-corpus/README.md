# sigil-corpus

A **compiler-validated** corpus extractor for SIGIL. It turns the committed self-hosting
artifacts into deterministic JSONL records, where **every emitted record has been validated
through the real compiler** — a positive parses + type-checks, a negative reproduces its
declared diagnostic code.

## Why validation is the whole point

A training corpus has no runtime oracle of its own, and a wrong record ships a confident lie
into model weights — discovered only after training. So the corpus borrows the compiler as its
oracle **at extraction time** and drops (loudly, counted) anything the compiler won't confirm.

## Usage

```sh
cargo run -p sigil-corpus -- build [--out corpus/out]   # extract → validate → write JSONL
cargo run -p sigil-corpus -- stats                       # extract → validate → print counts
cargo run -p sigil-corpus -- validate                    # re-gate; print the auditable green-light
```

Output (gitignored, regenerable) lands in `corpus/out/`:

- `<kind>.jsonl` — one file per record kind (`implementation`, `idiom`, `rejection`, …), records
  in stable id order.
- `manifest.json` — schema version, git sha, per-kind / per-extractor counts, validated /
  unvalidated / dropped totals (reconciled).
- `rejects.log` — one JSON line per dropped candidate, with the reason (auditable).

## Extractors

| Extractor | Source | Records |
|---|---|---|
| `error_corpus` | the 269 diagnostic codes ⋈ `docs/ERROR-CODES.md` prose | `rejection` references |
| `source_idiom` | `selfhost/*.sigil` + `stdlib/sigil/*.sigil`, function/type-level | `idiom` / `implementation`, validated by their compilation unit |
| `test_fixture` | the non-solver fixture dirs | `rejection` negatives (codes re-derived from the compiler) + positives |
| `pr_history` | merged-PR `.sigil` post-images (`gh` + `git`) | `implementation` (the self-hosting journey); offline-skippable |

## Guarantees (the §9 dumb bounds + fail-fast)

- **Validate-or-drop** — every record round-trips the compiler; failures go to `rejects.log`.
- **Negative codes from the compiler**, never the `// expect-error:` header.
- **Grounded prose** — `intent`/`reasoning` are verbatim substrings of their cited source, or empty.
- **Tracked-only inputs + secret/PII scan** — never reads untracked/`.gitignore`d paths; never
  emits a secret.
- **Byte-identical regeneration** — content-derived ids, BTree ordering, no timestamps.
- **Conservation** — `proposed == emitted + Σ(named drops)`, asserted every build.

A bad *candidate* is dropped + counted (the build continues); a pipeline *invariant breach*
panics (the build crashes). Nothing is swallowed.
