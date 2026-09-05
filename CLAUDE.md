# SIGIL — session contract

SIGIL is a capability-safe language with effects, taint, and linear ownership, compiling
to wasm, with a self-hosting compiler (`selfhost/`), an independent Python reference
interpreter (`interp/`), and mechanized soundness proofs (`proofs/lean`). It is designed
for provably-safe agent-generated code — and it is *built* by agents, which is why this
file exists: you infer house style from whatever files you happen to read, and this file
is the one guaranteed to be in every session's window. The full mined style guide with
evidence is `docs/STYLE.md`; read it before writing anything substantial.

## The creed

1. **A claim no test enforces is a hope.** `docs/CLAIMS.md` is the single machine-checked
   authority on what SIGIL proves. State nothing as proven without a `@test:` tag; pin
   every load-bearing number at its *measured* value (never the documented one).
2. **Fail closed, and say so.** Every gate/fallback names its failure direction in a
   comment. No silent degradation, no best-effort partial output, no fallback that isn't
   a stated decision.
3. **An absence claim requires a proven detector** (SC-P4): any census, comparator, or
   "there are no X" test ships an anti-stub shown detecting a planted X, in the same file.

## The PR-class contract (every change)

Every PR is one of two classes, enforced by `crates/sigil-compiler/tests/parity_manifest.rs`:

- **Parity-preserving** (refactors, dep bumps, docs, style work): `tests/parity/manifest.tsv`
  is UNTOUCHED in your diff. Checker green + manifest untouched = proven zero behavior
  change over the fixture corpus.
- **Output-changing** (features, codegen, diagnostic wording — hints included): regenerate
  and commit the manifest diff; the changed rows are review content. Regeneration:

      SIGIL_PARITY_REGENERATE=1 cargo test -p sigil-compiler --no-default-features \
          --test parity_manifest -- --ignored regenerate_parity_manifest --nocapture

  `--no-default-features` is load-bearing: defaults include `solver`, which compiles the
  parity file out, and `cargo test` exits 0 on zero tests — the un-flagged spelling is a
  silent no-op.

## Tripwires you WILL hit

- **The gating test lane is `cargo test --workspace --no-default-features`.** Default
  features include `solver` (needs native libz3, not present on most machines) — most
  local testing wants `--no-default-features`. The solver lane runs separately in CI with
  a SHA256-pinned Z3 4.12.2 (see `ci.yml` for the exact install ritual if you need it).
- **Code-shaped tokens in test files move census pins.** `soundness_contract.rs` counts
  every `[A-Z]{1,3}[0-9]{3}` token in `crates/**/tests` files — comments and strings
  included — against `docs/diagnostic-test-gaps.txt` and pinned reference counts. An
  illustrative diagnostic code in a doc comment can move a coverage pin. Use codes that
  already carry direct test references, or split the literal with `concat!`.
- **Names cited by ledgers are frozen.** `docs/CLAIMS.md` cites test fns by name
  (`pin6_every_claim_names_a_real_test` enforces existence); `preserve_pins.rs` pins CI
  check names; preservation manifests pin suite labels. Renames ship with the ledger
  update in the same commit.
- **The census tax is a coordinated multi-file edit.** Adding a test that references a
  code in `docs/diagnostic-test-gaps.txt` requires updating that manifest, the pinned
  constants in `soundness_contract.rs`, and the mirrored pins block in `docs/CLAIMS.md` —
  batch such changes rather than paying per-test.
- **Zero debt markers.** No TODO/FIXME/HACK/XXX in src (census-enforced). Debt goes to:
  `docs/RESIDUAL_RISKS.md` (soundness, with owner + review point), `docs/CLAIMS.md` §D
  (unproven claims, counted), `docs/diagnostic-test-gaps.txt` (coverage),
  `tests/attack/KNOWN_GAPS.md` (attack surface).
- **New src files need a leading `//!` module doc** (role + load-bearing constraint) or
  `style_census.rs` fails — the fix is writing the doc, never growing the gap manifest.
- **Bare `.unwrap()` in src is ceiling-pinned per crate.** Use
  `.expect("narrated invariant")` naming the guaranteeing fact, or a typed error.
- **Diagnostics are asserted as exact code sets** — never substring matches against
  Debug/Display output (that idiom self-satisfied for months before PR #706).
- **Committed goldens regenerate only via env-armed `#[ignore]` rituals** — never edit a
  golden or manifest by hand; run its regenerator (each failure message names the exact
  command).
- **`.sigil`, `.tsv`, and most text files are LF-pinned** in `.gitattributes`; tests
  byte-compare them on the Windows lane. `git diff --check` gates whitespace errors.
- **Fixture headers**: description line first (the corpus extractor reads it as prose),
  machine expectation second (`// expect-error: T044, T088` — exact codes, comma-set).

## Commands

    cargo test --workspace --no-default-features   # the gating lane
    cargo test -p <crate> --no-default-features    # one crate
    cargo fmt --all && cargo clippy --workspace --all-targets --no-default-features -- -D warnings
    python interp/test_parse.py && python interp/test_eval.py   # interpreter pins
    python tools/selfhost_ergonomics_census.py --ratchet        # selfhost ergonomics gate

CI lanes beyond `test`: `checks` (fmt/clippy), `solver` (pinned Z3), `interp-ddc`
(diverse double-compilation, digest-pinned), `hygiene` (python lint, workflow validity,
whitespace), portability (macOS/Windows — parity and the compiler-side censuses run
there too; **gated**: push-to-main, or a PR labelled `ci-portability`, which takes effect
on that PR's next push — macOS bills at 10x and Windows at 2x), Lean.

## Map

| where | what |
|---|---|
| `crates/sigil-compiler` | lexer → parser → type_check → security gates (taint/cap/ring/effect/ownership) → AIR → wasm |
| `crates/sigil-runtime` | wasmtime host: actors, fuel, capabilities, FFI shims; repo-wide census tests live in its `tests/` |
| `crates/sigil-frontends` | untrusted Rust/Solidity/TypeScript → SIGIL translators (fail-closed allowlists) |
| `crates/sigil-{cli,serve,mcp,corpus,registry,abi,test-utils}` | binary edges and support |
| `selfhost/`, `interp/`, `proofs/` | the second and third implementations + Lean; differentials compare them |
| `docs/CLAIMS.md`, `docs/RESIDUAL_RISKS.md`, `docs/SOUNDNESS_MATRIX.md` | machine-checked ledgers |
| `docs/specs/` | dated, statused specs whose obligation IDs (ET-1, PPS-4, ...) tests cite verbatim |
| `docs/STYLE.md` | the full style guide this contract summarizes |

When in doubt: imitate `crates/sigil-frontends` (structure), `claims_ledger.rs` /
`interp_corpus.rs` (evidence tests), `clippy.toml` / `ci.yml` (comment voice) — they are
the strong stratum this repo's conventions were mined from.
