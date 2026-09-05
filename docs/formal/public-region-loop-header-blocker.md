# Public region proof: historical loop-header policy blocker

This checkpoint records why the independent-length Public theorem was blocked by an accepted v8
counterexample. Model 9 now rejects that occurrence pattern and the downstream Public theorem is
proved; this historical record is not itself the proof, release evidence, or authority to retire a
gate.

The occurrence-aware policy correction has since been approved for a **new CSIR v9** model.
See [the success contract and implementation status](public-occurrence-implementation.md).
The v8 counterexample below remains historical evidence, not a fix-verification result.

## Reproduction

`PublicRegionProbes.lean` contains a canonical 40-record CSIR v8 program. At the loop header it:

1. Emits a fixed Public actor-boundary payload.
2. Reads the next Internal input from a per-site stream.
3. Compares that input with a Secret parameter and enters the body or exits.

The body is just a backedge. Every SSA destination has one defining instruction; no malformed
target, fabricated frame, duplicate definition, or unreachable-code trick is used.

The two initial states have the same Public data, control position, empty call stacks, external
streams, and external cursors. Only the Secret limit differs: zero versus one. The shared input
stream is `[0, 1]`.

- The first run successfully returns after five raw steps and visits the header once.
- The second successfully returns after ten raw steps and visits the header twice.
- Both execute the real top-level output instruction, and neither traps.
- Their release traces are equal and empty, but their Public boundary traces differ.

The kernel-checked theorem `accepted_loop_header_public_counterexample` packages acceptance,
initial well-formedness and Public equivalence, successful executions, release equality, and
Public trace inequality. Separate lemmas establish the actual function entry, Public cut points,
identical input streams/cursors, and genuine final output steps.

`public-loop-header-boundary.hex` is shared between the Lean decoder witness and the linked-native
Rust test. The source probe also compiles a guard function that sends a Public message, returns a
Secret condition, and is called in a while header. Source acceptance and the decoded raw witness
are separate checks: this is not a proof of source/AIR/Wasm correspondence.

## Cause and required decision

The semantic graph propagates the loop selector to the body, but not to re-evaluation of the
header. Its backward-jump exception prevents the body's pc from flowing back into the header.
Consequently, a header and its guard callees can remain Public even though a Secret determines
how many times they execute. A fixed Public payload can therefore reveal a secret through the
number of boundary events, even when both runs terminate.

No missing relational lemma can make the proposed Public conclusion true for this accepted
program. Excluding trapped/divergent runs, strengthening frame provenance, comparing equal
release traces, or dropping internal Public cells from the conclusion does not repair it.

The proposed policy correction is to account for the loop decision's control dependence during
header/guard evaluation, including calls, and enforce the declared sink labels for effects there.
This must reject the resulting Public side effect with an approved source diagnostic; merely
relabeling the raw boundary event and filtering it from observation is not an acceptable repair.
Pure guards and already legal non-Public flows must retain coverage.

This is a new source-policy restriction. The implementation roadmap requires separate approval
before it can change acceptance. Any genuinely missing wire contract information must trigger
the specified CSIR v9 proposal rather than a reinterpretation of an existing v8 tag.

## Regression boundary

The feasibility probes intentionally record v8 acceptance. Preserve their historical semantics
under v9 and retain the old behavior as a test-only mutant/oracle. The corresponding v9/source
cases reject the actual occurrence violation, rather than merely rejecting a v8 header as an
unsupported version. Do not remove the paired execution counterexample or cite these feasibility
tests as the Public proof; that production theorem is recorded in
`PublicBisimulationSecurity.lean` and `RawClaimSurface.lean`.

The root Lean build and axiom census include the new witnesses; CI runs the source/native probes
in the no-solver lane and the existing solver-enabled compiler suite. The production raw-claim
audit remains pinned to one claim, SecretCT. Existing claim text and retirement eligibility stay
unchanged; only mechanical theorem-census counts are updated.

## Checkpoint validation

- Full Lean build: passed (887 jobs).
- No-placeholder, exact theorem-census, axiom, and production-claim dependency audit: passed
  (2,875 theorem targets; unchanged three-axiom allowlist and one production raw claim).
- Audit planted-failure self-tests: passed.
- Shared-byte linked-native and source-acceptance probes: passed with solver enabled and disabled
  (two tests in each configuration). The solver-enabled run uses the installed Z3 headers and
  library; no gate is bypassed.
- Runtime soundness-contract suite: passed (nine tests).
- Strict Clippy for the new compiler integration test, workspace formatting, and diff whitespace
  checks: passed.

The export-manifest suite is not green: three tests pass and two fail on existing branch state.
`docs/release-evidence/csir-v8-dual-gate.toml` lacks an export classification, and the recorded
`docs/RESIDUAL_RISKS.md` export patch no longer applies. Those source/patch files are unchanged by
this checkpoint. These failures still need resolution before merge; they are not waived or
counted as successful validation. The new evidence document has an explicit export classification.

The complete platform/corpus/performance matrix has not been rerun for this proof-only blocker
checkpoint. No production checker, compiler acceptance rule, certificate schema, or retirement
claim changes here, and unrelated benchmark work remains untouched.
