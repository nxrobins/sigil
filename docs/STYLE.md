# The SIGIL style guide

**Status:** Living — mined 2026-08-17, enforced in part by `crates/sigil-runtime/tests/style_census.rs`
**Method:** Descriptive, not aspirational. Every rule below was mined from the codebase's
strongest stratum by a seven-dimension audit; each carried verbatim exemplars (207 quotes,
206 verified byte-exact against the tree at mining time) before it was admitted. Line
references are as of the mining commit and may drift; the quoted text is the anchor — grep it.

This repo is written by agent sessions, and that fact shapes everything here. A session
infers house style from whichever files land in its context window, so style drifts
stratigraphically: sessions that touch the same subsystems converge, subsystems that never
share a window diverge. This guide exists to be the shared window. The companion
`CLAUDE.md` at the repo root carries the compact per-session contract; this file is the
full reference with evidence.

**How to change this guide.** The same way it was built: a new rule needs exemplars already
in the tree (write the code first, then the rule), and a rule that can be counted must land
with its ratchet in `style_census.rs`. A rule no test enforces is a hope; most of what
follows is hope by necessity — judgment calls — which is why the enforceable slice is pinned
and the rest is written down with the evidence that earned it.

---

## §0 — The creed

Everything else in this guide is a corollary of three commitments the strong stratum makes
everywhere:

1. **A claim no test enforces is not a claim, it is a hope** (`docs/CLAIMS.md`). Prose
   drifts; pins and censuses do not. When you state something, either cite the test that
   proves it, pin the number it depends on, or mark it unproven where the unproven count
   is itself pinned.
2. **Fail closed, and say so.** Every gate, fallback, and partial path names its failure
   direction — closed or open, loud or silent — so a silent path is visibly a decision,
   never an accident.
3. **An absence is only evidence if the detector is proven** (SC-P4). Every "there are no
   X" assertion ships with the instrument shown detecting an X. This repo caught two
   vacuous detectors in a single day — one of them inside the very census that polices
   vacuity — which is why this is a commitment and not a nicety.

---

## §1 — Comments: voice and altitude

The house voice is the most recognizable thing in this codebase, and it is uniform from
`clippy.toml` to `ci.yml` to the census tests: long WHY-comments at the altitude of
constraints and consequences, never narrating the next line.

**1.1 — Write at the altitude of what the code cannot show.** When the design rejects an
obvious alternative, name the alternative and say exactly why it loses. The house pattern
is a literal block: `# Why clippy instead of a source grep:` (`clippy.toml:6`). A session
that lacks the rejection rationale will re-derive the obvious approach and "simplify" a
load-bearing choice.

**1.2 — Never write a number you did not measure.** A number in a comment carries units,
environment, and — when one exists — the incident that produced it, error text and dates
included: *"the CI runner's ~14GB disk (\"No space left on device, os error 28\")"*
(`Cargo.toml`), *"850s of the rust job's 18-minute test step on the 2-core runner; 133s
locally"* (`Cargo.toml`). A bare number is indistinguishable from a guess and rots
silently. Load-bearing numbers should not stay prose at all — they become `PIN_*`
constants (§6.3).

**1.3 — Attach an update protocol to every fragile pin.** Anything fencing an external
surface — a vendored version, an API namespace, a dependency's feature layout — states the
trigger event and the required action in so many words: *"Update protocol: bumping the
`z3` crate version in..."* (`clippy.toml:14`). The protocol turns "this broke mysteriously"
into "the bumper must extend this list."

**1.4 — Open evidence-bearing test files with shouted why-headers.** `WHY THIS TEST
EXISTS.` / `WHY IT CANNOT GO STALE.` / `WHAT IS COMPARED.` (`claims_ledger.rs`,
`interp_corpus.rs`). The header carries the threat the test defends against and the drift
incident that motivated it, so the test survives a refactor by a session that lacks the
history.

**1.5 — Place spec-tags at the discharging line.** The 215-tag vocabulary (SC-P4, PPS-4,
ET-Z8, HB-2, ...) is the repo's evidence graph; a tag belongs in the comment at the exact
code point that discharges the obligation, so spec, ledger, and proof are mutually
greppable. Gloss a tag at first use in a file — `SC-P4 (no assertion of absence without an
anti-stub)` — rather than assuming the reader holds 215 acronyms.

**1.6 — Name the failure direction, always.** *"L2 is silently disabled"* (`z3_cache.rs`),
*"fail-closed `Default` = false"* (`compiler.rs`), *"from a silent surprise at DDC time
into a failure on the PR that introduced it"* (`ci.yml`). The fail-closed vocabulary
(~280 occurrences) is what makes the security posture auditable.

**1.7 — Bound every admitted flaw in the same breath.** An admission states what the flaw
can and cannot affect and records the acceptance: *"`(parallel_threads - 1)` per contended
key. Not load-bearing — only..."* (`z3_cache.rs`). An unbounded admission invites either
panic or neglect.

**1.8 — No debt markers, ever.** Zero TODO/FIXME-family comments in 106k lines, enforced
by `style_census.rs`. Debt goes to a ledger with an owner and review point: soundness
risks → `docs/RESIDUAL_RISKS.md`; unproven claims → `docs/CLAIMS.md` §D (counted, pinned);
diagnostic coverage gaps → `docs/diagnostic-test-gaps.txt`; attack-surface gaps →
`tests/attack/KNOWN_GAPS.md`. Inline residue is phrased as a scoped acceptance decision,
not a wish.

**1.9 — Config files get evidence-grade comments.** Every non-default line in
`clippy.toml`, `.gitattributes`, `ci.yml`, or a `Cargo.toml` stanza names the concrete
consumer that breaks without it and how the break manifests (*"compared byte-wise by ...
which also runs in the Windows portability lane — a CRLF checkout there would fail every
row"*, `.gitattributes`). Config lines are the easiest thing for a later session to "clean
up" precisely because nothing in the file itself fails.

---

## §2 — Naming

Named so that a grep is a proof search.

**2.1 — Test functions are assertion sentences.** Subject, verb, expected outcome:
`cache_hit_returns_same_verdict_as_fresh`, `secret_entry_without_a_value_separator_refuses_to_boot`.
Never a `test_` prefix, never a bare topic noun — a failing test name must read as the
exact claim that was falsified. (The last seven `fn test_*` names — five in
`sigil-registry`, two in `forge_tests.rs` — were renamed in the registry cleanup;
`style_census.rs::style_test_prefix_is_extinct` now pins the prefix at zero.)

**2.2 — Tag prefixes only when discharging a numbered obligation.** `pin6_`, `hb2_`,
`pps0_`, `eh43c_` prefixes appear on ~180 of ~3,700 tests, exactly where a spec rung,
ledger tag, or preservation-manifest row cites them. The prefix is the obligation ID; the
remainder still reads as a sentence. Everything else stays unprefixed — decorative tags
are noise.

**2.3 — Ledger-cited names are frozen API.** `docs/CLAIMS.md` cites test functions by name
and `pin6_every_claim_names_a_real_test` fails the build if one stops existing;
`preserve_pins.rs` pins CI check names; preservation manifests pin suite labels. Before
renaming anything, grep the ledgers, and ship the manifest/floor update in the same
commit. A rename that silently orphans a claim converts "proven" into "lying."

**2.4 — A name that overclaims gets renamed, in place, with a note.** The house precedent:
*"RENAMED from `ids_match_lean_obligations` (task #254) — the old name and the ledger..."*
(`lambda_sigil_differential.rs`). A claim whose proving test was renamed is re-marked
unproven rather than left pointing at a ghost.

**2.5 — Diagnostic codes are the registry's, singular.** `^[A-Z][0-9]{3}$`, letter naming
the checker that fires it, declared exactly once through the registry macro. A test
witnessing one specific code may carry it lowercased as prefix
(`n007_hint_caps_at_5_suggestions`). Beware: any code-shaped token inside a
`crates/**/tests` file — comments and strings included — is counted by the
diagnostic-census in `soundness_contract.rs`; an illustrative mention can move a coverage
pin (§4.8, and yes, it happened).

**2.6 — Corpus fixtures are `NN_snake_description.<ext>` with in-band expectations.**
Numbers are permanent IDs — a retired fixture leaves a documented hole
(`tests/attack/` skips 04/06/07 with the write-up in `KNOWN_GAPS.md`), never renumbered.
Every fixture declares its contract in-band (`// expect-error:` with exact codes,
`// MUTATION_SITE` where the harness enforces mutation).

**2.7 — Golden pairs share a stem.** `add.rs` beside `add.sigil`;
`access_control_token.sol` beside its `.sigil`. The filename pairing is the manifest, and
every emitted golden must round-trip compile so it is a live artifact, not a snapshot that
rots.

**2.8 — Measured values are `PIN_*` constants.** The Rust constant owns the value, the
`CLAIMS.md` pins block mirrors it name-for-name, prose cites the name and never restates
the number (`PIN_CAP0_SRC_CHARS`). `pin6_ledger_numbers_match_the_code` makes any drift a
red build.

**2.9 — `_v2` means production successor, nothing else.** Both live instances
(`type_check_v2`, `air_capability_v2`) are the production path shipping beside the
original pass, and both open by declaring that role and the boundary tests pinning it.
Never `_v2` for an experiment or a parked copy. (Whether to rename or merge the two
live instances is decided — no, with stated revisit triggers — in
`docs/specs/v2-unification-decision.md`.)

---

## §3 — Error handling

Three dialects, one grammar of narrated evidence.

**3.1 — Libraries return typed errors; anyhow lives only in binaries.** `sigil-compiler`,
`sigil-frontends`, `sigil-runtime`, `sigil-abi`: `Diagnostic` aggregated into
`CompileError` (or a per-crate diag type with stable codes), zero `anyhow`. The
machine-actionable code surface is the contract with every consumer — CLI envelopes, MCP,
serve, and LLM drivers. Binaries (`cli`, `serve`, `corpus`, `mcp`) wrap I/O edges in
`anyhow` with `.with_context(|| ...)` naming the operation and the concrete path in
backticks.

**3.2 — Every user-facing error is a registered Diagnostic.** Stable code via the registry
(one declaration site, format-pinned), message interpolating the offending names in
backticks, hint from the registry unless the call site genuinely knows better.

**3.3 — `.expect` messages are proof citations, not apologies.** Legitimate only where an
earlier step in the same flow guarantees success, and the message names that guaranteeing
fact: `.expect("inserted above")`, `.expect("arity checked == 1")`. A panic backtrace then
reads as a pinpointed logic bug. Bare `.unwrap()` in src is ceiling-pinned per crate by
`style_census.rs` — counts fall freely, growth fails.

**3.4 — Impossible states panic with `ICE:`.** *"ICE: Type::Never reached mangle_type
(must be erased / gated before AIR)"* (`air.rs`). The prefix marks it a compiler bug (the
`I` code family, never a user error) and the message names the pass contract that was
violated, so the fix location falls out of the panic text.

**3.5 — `unreachable!()` always takes an argument citing the guard** that makes the arm
dead: `unreachable!("&&/|| are desugared before emission")`. The citation is what lets a
later editor change the guard safely.

**3.6 — Gates fail closed on unforgeable evidence.** A gate keys on a freshly derived bit,
never the artifact's own claim about itself; the only way through is an explicit named
override that the refusal message itself advertises (`SIGIL_ALLOW_UNVERIFIED_CERT=1`).
Deliberate, auditable, spelled out at the point of refusal.

**3.7 — Reject whole rather than degrade.** A malformed config entry refuses to boot
instead of being dropped (*"a config typo must refuse to boot, not silently narrow"*,
`serve/config.rs`); a frontend that cannot translate a construct emits a fail-closed
diagnostic and nothing else. Every partial-acceptance path is attack surface.

**3.8 — CLI failures map deterministically.** Usage errors exit 2, command errors exit
FAILURE; `--json` emits exactly one structured envelope carrying a diagnostic code even
for pre-parse failures, never double-emitting. The exit-code/envelope contract is what
makes automated remediation possible.

**3.9 — Test-side failure text is a contract sentence.** `"a malformed secret grant must
refuse to boot"` — the "X must Y" form names the property under test, because in a
3,700-test suite the panic text is the only context anyone gets.

---

## §4 — Tests and evidence

The canon that makes this repo unusual. Each pattern has a trigger condition — when it is
required, not optional.

**4.1 — Anti-stub every absence (SC-P4).** Any test asserting absence, zero, emptiness, or
agreement-between-artifacts must first prove its instrument detects a planted positive and
stays silent on a clean negative — in the same file. Required for: censuses, extractors,
comparators, differentials.

**4.2 — Mutation-gate security fixtures.** An `expect-error` security fixture carries
exactly one `// MUTATION_SITE` line, and the harness recompiles with it deleted and
requires a clean compile — proving the fixture rejects for the declared attack, not
incidental breakage. Required for adversarial corpora (`z3_corpus` is the reference
implementation; the older `tests/reject` corpus predates it — backlog).

**4.3 — Pin measured, choose the failure direction by what the number counts.** Evidence
corpora get deletion FLOORS (shrink fails, growth free); debt counts get CEILINGS (fall
free, growth fails); doc-claimed numbers get EXACT pins mirrored against same-named
constants. Always the measured value at introduction (SC-P1), never the documented one.

**4.4 — Nameable debt becomes an exact-set manifest, not a count.** A bare ceiling lets a
new gap trade places with a fixed old one invisibly; a committed manifest
(`diagnostic-test-gaps.txt`, `style-module-doc-gaps.txt`) makes every new exemption a diff
line and every cleanup a visible deletion.

**4.5 — Goldens get env-armed regenerators.** `#[ignore]` AND armed by an env var checked
`== "1"` — because `--include-ignored` is a plausible run-everything invocation.
Regenerators refuse to shrink below the floor, single-source the regen command in failure
messages, and carry a meta-test pinning that they stay ignored and armed. Reference:
the seed succession ritual (`pipeline_differential.rs`), `parity_manifest.rs`.

**4.6 — Every reject gets an accept twin.** The same construct made legal, minimally
different. A verdicts-match differential over an all-accept corpus passes trivially — and
all-accept is what a checker that stopped emitting codes produces. Corpus-level pins
assert both verdicts are present and every in-scope code headlines at least one reject.

**4.7 — Diagnostics are asserted as exact code sets.** Never substring-match prose, Debug
output, or one direction of containment. The historical comparator matched expectations
against `format!("{errors:?}")` — whose SourceMap embedded the fixture source including
the expectation comment itself, so every assertion self-satisfied for months. Exact sets
also catch the spurious extra diagnostic and the vanished one.

**4.8 — Mind the census when writing tests.** The diagnostic census counts code-shaped
tokens anywhere in `crates/**/tests` files — comments and strings included — against the
gap manifest and reference pins. Choose illustrative codes that already carry direct test
references, or construct strings so the token does not appear literally (`concat!`).

**4.9 — Feature-gated CI lanes grep for the pass count.** `cargo test` exits 0 on zero
tests, so a `#[cfg]`-disabled or filtered-out suite leaves a lane green while proving
nothing. Any lane using `--features`/filters greps its log for the exact `N passed` line,
keeps the invocation on one `run:` line, and gets a census pinning the wiring
(`interp_ddc_lane_is_wired_in_ci` is the template).

**4.10 — Differentials vary exactly one thing and never grade their own homework.** Both
sides execute the same source with one variable differing (implementation, stage,
machine); only the oracle side computes and commits the answer key; the failure message
names whose bug a disagreement is; and a live divergent witness proves the comparison can
fail.

---

## §5 — Module and crate structure

Structure is documentation.

**5.1 — Every src file opens with `//!`** naming its role as a definite noun phrase and
stating its load-bearing constraint, citing the governing spec or tag. Enforced: a file
without one fails `style_census.rs` (the pre-convention manifest is cleared and pinned
empty — write the doc, never grow it back). What a good one contains: role, the
invariant the file owns, the failure discipline, and where its proofs live.

**5.2 — Subsystem `mod.rs` spells the pipeline.** Stage order with `→` arrows plus the
failure discipline that holds across stages (`solidity/mod.rs`). A reader entering a
subsystem gets the map before the territory.

**5.3 — Stages that outgrow a file split into single-concern submodule directories**
(`desugar/lowering.rs`, `desugar/inlining.rs`), each with a one-line `//!`. The former
counter-example, the `sigil-cli/main.rs` monolith (4,761 lines when decomposed; 4,737 at
mining time), was split under this rule into per-verb modules (2026-08-19, PR #707).

**5.4 — Inline `#[cfg(test)]` is for private-fn unit tests only.** Everything repo-scale —
differential, census, golden, adversarial, corpus — lives in `tests/` integration files
named for a single concern.

**5.5 — Feature gating is documented at the gate.** Optional deps use `dep:` syntax with a
comment stating why gated and what a no-feature build avoids; every whole-file
`#![cfg(feature)]` test gets a `[[test]] required-features` stanza (and when the inverse
gate is inexpressible, a comment where the stanza would be — see `parity_manifest`);
every `#[cfg(not(feature))]` fallback states its exact semantics, fail-open or
fail-closed, and what becomes inert.

**5.6 — Feature-gated deps needed by integration tests are re-declared as dev-deps** with
the comment explaining that Cargo does not expose feature-gated `[dependencies]` to test
crates (the `tempfile`/`sha2` precedent in `sigil-compiler/Cargo.toml`).

**5.7 — Repo-wide censuses live in `crates/sigil-runtime/tests`**, reach the workspace
root via `CARGO_MANIFEST_DIR` ancestor traversal with an `.expect` naming the layout
assumption, and are structured as ratchets with pinned, measured constants.

---

## §6 — Docs, specs, and ledgers

Prose is never trusted to stay true on its own.

**6.1 — `docs/CLAIMS.md` is the single authority on what SIGIL proves.** Every other
document defers to it by name rather than restating; `soundness_contract.rs` pins the
deference phrasing in the public docs.

**6.2 — Proven claims carry `@test:<fn>`; a claim with no tag is not a claim.** The tag
must resolve to a real, un-`#[ignore]`d, un-`cfg`'d-out test.

**6.3 — Numbers live in the pins block**, mirrored name-for-name against Rust constants;
prose cites names. When a pin must move: re-measure, pin the measured value (SC-P1).

**6.4 — Unproven claims exist only as counted §D rows**, phrased as what is missing.

**6.5 — Corrections happen in place**: *"(Corrected, task #254: the prior claim said the
two lists \"match\". They do not...)"*. Silent rewrites destroy the audit trail that makes
the ledger trustworthy.

**6.6 — Specs open with `**Status:** / **Date:** / **Authors:**`** and the Status line is
updated in place as the feature lands. A spec's open risks compile into short-ID
obligations (ET-1..., PPS-0...) — each a strict MUST with an exact bound — and tests cite
those IDs verbatim.

**6.7 — Residual risk is schema-complete rows only**: ID, Severity, Status, Scope and
evidence, Disposition, Owner, Review point, Tracking issue. Accepted rows need a live
issue; no row stays Open at a completion gate.

**6.8 — Load-bearing prose gets `include_str!` pins**: required sentences that must
survive, forbidden phrases that must not return, with anti-stubs proving the extractors
see both.

**6.9 — Generated reference pages say so**, carry the regen command, and are byte-compared
against their generator; hand-curated narrative lives in explicitly different-purpose
files.

---

## §7 — Python, shell, and tooling

The tooling layer carries the same evidence culture — where it doesn't yet, that is
backlog, not license.

**7.1 — Every gate script ships `--self-test`** that deliberately triggers each failure
mode and asserts detection, run as its own CI step before the gate
(`check-no-sorry.sh --self-test` is the reference; the ergonomics census and the
workflow validator gained theirs in the tools cleanup, and the validator's first
self-test execution caught its colon-space hint blind to the `- run:` spelling —
the pattern paying for itself on day one).

**7.2 — Quality floors are ratchets** with pinned ceilings, a counts-may-fall-freely
comment, and printed slack.

**7.3 — Harnesses read answer keys, never compute them.** *"An implementation that
computed its own reference answers would be grading its own homework"*
(`interp/test_differential.py`).

**7.4 — Python modules open with role + the concrete failure mode they close**, quoting
the dated incident when one exists (*"WHY THIS EXISTS. On 2026-08-02 a `run:` step..."*,
`tools/validate_workflows.py`), and state what the check does NOT prove.

**7.5 — Deliberate interpreter semantics are named pins**: listed in the module docstring
with why an independent implementation would plausibly differ, pinned in `test_eval.py`.

**7.6 — Gate scripts are stdlib-only, direct-runnable Python**: `from __future__ import
annotations`, usage in the docstring, `main() -> int`, `raise SystemExit(main())`.

**7.7 — Shell gates run `set -euo pipefail`**, clean scratch via `trap cleanup EXIT`,
treat grep's exit statuses as three verdicts, and sha256-verify every downloaded artifact
before it touches an install path.

---

## Appendix A — The nonconforming backlog

The known weak-stratum areas, named so cleanup is a worklist rather than a rediscovery.
The posture is **ratchet, not big-bang**: new code conforms from day one; touched code
gets brought to code; the censuses make regression impossible. Every cleanup PR is
parity-preserving by definition — `tests/parity/manifest.tsv` must be untouched
(see `crates/sigil-compiler/tests/parity_manifest.rs` for the contract).

The worklist is EMPTY as of 2026-08-19: every row mined on 2026-08-17 has been either
brought to code or closed by a recorded decision — see the Completed notes below. New
weak strata get new rows; an empty list here is a claim about known areas, not a proof
of global conformance.

Completed: **the `_v2` unification row** (2026-08-19, PR #707) — closed by decision,
not by rewrite: `docs/specs/v2-unification-decision.md`. Measured, the row's framing
was wrong — the trees beside `type_check_v2`/`air_capability_v2` are complementary
phases of the same gates, not superseded versions (the real v1s were deleted in
2026-06/07 after shadow windows); the two-tree shape is the load-bearing quarantine
architecture and stays. The residue that WAS real — orphaned quarantine-contract IDs,
a clutch of stale migration-era citations (two z3_corpus fixture headers and a Lean
anchor included), and a documented-but-nonexistent rlimit sync test —
was fixed in the same commit (the sync test now exists:
`rlimit_constants_stay_in_sync`), with two follow-ons scheduled in the decision doc
(V2D-4 `refinement_queries` consolidation, V2D-6 the effect-handlers Handle-site
census re-anchor).

Completed: **the `sigil-cli/main.rs` decomposition** (2026-08-19, PR #707) — the
monolith (4,761 lines measured at decomposition; the Appendix row's 4,737 was its
mining-time size) split per §5.3 into per-verb modules (`args`, `cert_gate`,
`check_run`, `translate`, `forge`, `registry_cmd`, `info`), each opening with a §5.1
module doc; `main.rs` is now the 96-line binary root (entry, dispatch, module map).
The move is constructive: every module is a concatenation of verbatim line ranges of
the original, proven by a normalized line-multiset comparator whose only differences
are the generated headers, `pub(crate)` visibility tokens, and three rustfmt-rewrapped
signatures. All 68 inline tests moved with their subjects (test module docs decided
placement: `multi_file_cli_tests` documents itself as an arg-parsing suite and
`forge_gate_tests` covers `cert_gate` helpers) and pass unchanged; a before/after
behavior snapshot (help/version/explain/error paths, human and `--json`) is
byte-identical. The pre-§4.7 substring-match test idiom inside the moved suites was
deliberately NOT modernized — test-body edits do not belong in a decomposition commit.

Completed: **the module-doc backlog** (2026-08-18, PR #707) — all 25 remaining
pre-convention files now open with a §5.1 module doc (role, owned invariant, failure
discipline, proof locations). Every doc was drafted from the file and then adversarially
verified sentence-by-sentence against the source before landing; the verification pass
rejected several drafted claims outright (a restart-policy default presented as
load-bearing when no caller reads it, a stale nesting-cap description contradicted by
the actual gate, an off-by-one overflow boundary) — deletion over invention, per §0.
Census delta: `docs/style-module-doc-gaps.txt` 25 → 0 and pinned empty, so a src file
without a module doc is now a hard failure everywhere, not just for new files.

Completed: **the `tools/` gate scripts** (2026-08-17, PR #707) — `--self-test` fences for
the ergonomics census (every detector proven on planted input; empty-tree path now fails
closed instead of praising a zeroed census; discovery made recursive) and the workflow
validator (every refusal branch proven, including the colon-space hint — whose first-ever
execution revealed it blind to the `- run:` list-item spelling; fixed and both spellings
planted). Both fences wired as their own CI steps before their gates, in both lanes of
the mutual-coverage pair. `tools/` joined the ruff lane with its own `.ruff.toml`
(already clean under the strict set). `main() -> int` + `raise SystemExit(main())`
conventions applied. All three sabotage probes (dead regex, lobotomized hint, disabled
empty-tree refusal) verified red before landing.

Completed: **the fixture corpora** (2026-08-17, PR #707) — every expect-error fixture in
`tests/{reject,attack}` now carries a `// MUTATION_SITE` line and the harness enforces the
z3_corpus deletion contract (§4.2): the mutant must compile clean, making it the accept
twin (§4.6) — one line away from the reject, both verdict classes exercised on every run.
Corpus deletion floors landed for all four directories, and the corpora's code coverage is
pinned as an exact-set manifest (`tests/expected-reject-codes.txt`, 16 codes — kept at the
repo root because code literals inside `crates/**/tests` would move the diagnostic-census
pins). Gates were mutation-probed in all three failure classes before landing. One scope
decision, stated per §6.5: fixture **renumbering** (§2.6) was deliberately declined for
these legacy corpora — renames churn parity-manifest row keys and `sigil-corpus` record
identities for zero evidence gain; §2.6 binds new corpora, and the existing word-names
are already stable citation targets.

Completed: **`sigil-registry`** (2026-08-17, PR #707) — module doc written, banner and
signature-echo comments replaced with behavior-bearing ones (the `LIKE`-wildcard search
semantics, the `update_fuel` silent no-op, the additive-schema constraint), test names
converted to assertion sentences with contract-sentence expects, dependency rationale
added, and the one fail-open seam (tags deserialization) named in place with its bound
and revisit trigger rather than silently kept or silently "fixed" — a behavior change
does not belong in a style pass. Census deltas in the same commit: module-doc manifest
26 → 25, registry unwrap ceiling 25 → 0, `test_` prefix pinned extinct.

## Appendix B — Enforcement map

| rule | instrument |
|---|---|
| §1.8 zero debt markers | `style_census.rs::style_debt_markers_are_zero_in_src` |
| §5.1 module docs on new files | `style_census.rs::style_module_doc_gaps_match_the_manifest` + `docs/style-module-doc-gaps.txt` |
| §3.3 bare-unwrap ceilings | `style_census.rs::style_bare_unwrap_ceilings_hold` |
| §2.1 no `test_` prefix | `style_census.rs::style_test_prefix_is_extinct` |
| guide presence + cross-reference | `style_census.rs::style_guide_files_exist_and_are_cross_referenced` |
| §2.3 ledger-cited names | `claims_ledger.rs`, `preserve_pins.rs` |
| §2.8 / §6.3 pins | `pin6_ledger_numbers_match_the_code` |
| §6.1 / §6.7 doc schemas | `soundness_contract.rs` |
| behavior parity of all of the above | `parity_manifest.rs` + `tests/parity/manifest.tsv` |

Candidate next ratchets, in census-ready shape (from the mining pass): `unreachable!()`
with empty args forbidden in src; per-corpus filename-shape lints; a workflow census
requiring every CI-wired gate script to have a `--self-test` step preceding it.
