# Occurrence-aware Public security: success contract and implementation status

## Approved success contract

Unreleased non-Public information may influence private computation, but not the
occurrence, count, order, site, routing, or payload of Public actions, nor the full
final modeled Public state. Occurrence visibility is independent of payload and
response confidentiality. An empty message still has an occurrence. A Public send
carrying a permitted Secret payload remains legitimate when its occurrence is Public.

This milestone includes private stateful guards and explicitly contracted private
external crossings. It is not restricted to pure loop guards. Repetition analysis
must cover loop headers, body decisions, break/continue, nested regions, and direct,
closure, and recursive callees, while preserving one-time setup and justified Public
continuations. The verifier owns the control-region analysis; numeric block ordering
and Rust-supplied merge certificates are not proofs.

The new semantics require **CSIR v9**. CSIR v8 retains its historical meaning;
certificate schema v9 and `FormalSecurityReport` fields do not change. Compiler
projection must encode declared inputs/contracts, not derived security verdicts.
Canonical CSIR and checker fingerprints must bind the new contracts, with stale or
changed evidence rejected through R819. All existing security gates remain mandatory.

Completion requires the verifier-derived, independent-length Public theorem, not
just rejection of the known example. Its premises include matching verified cut
points, well-formed Public-equivalent starts, identical immutable external streams,
two independently sized successful executions, and equal **complete** release traces
(site, stage, payload, order, and occurrence). Traps and fuel exhaustion are not
successful completion. Its conclusions include every statically Public scalar and
aggregate cell, Public actor state, Public-site input positions, and ordered Public
output/boundary observations. Ordinary Secret timing/control/cost equality is not
claimed. The separate SecretCT result must be preserved.

Only approved policy violations may newly reject. Unexplained clean-corpus rejection
blocks integration. Completion also requires the audited Lean theorem chain and
claim signatures, native/decoder/diagnostic parity and mutants, complete consumer and
platform lanes, bounded memory, the existing five-second self-host canary and sub-1-ms
warm-verifier target, and a tagged dual-gate release with versioned evidence. No gate
retirement is authorized. SR-013 and SR-017 remain unresolved; retirement eligibility
remains false.

## Current implementation boundary

The current production boundary is **mandatory CSIR-v9 occurrence enforcement,
report/certificate/runtime-profile binding, and the decoded-CSIR independent-length
Public theorem**. It is not source-to-CSIR or general AIR/Wasm correspondence,
semantic authority/affine/quantity operational closure, a tagged release, or
authorization to retire any legacy gate. Several bullets below retain the narrower
claims of the intermediate layers from which the production check was built; those
layers do not authorize independently. The dated checkpoints at the end of this
document supersede earlier retained-v8 and unary-only status statements.

- `sigil-abi::host_contract` separates occurrence, parameter, and result labels;
  declares state/stream/output/guest-memory domains and their partition scopes;
  validates declared flows; encodes and decodes canonical bounded profiles; and
  fingerprints all fields with SHA-256.
- `sigil-runtime::host_contract` builds profiles from registered typed host
  callbacks, checks their actual Wasm signatures, and freezes the linker/profile
  together. Required profile matching happens before module instantiation/start.
- Existing actor and ephemeral paths reject the reserved host-profile requirement
  rather than ignore it. Modules with no such requirement keep their legacy path.
  The ephemeral path normalizes its existing binary-or-text input before inspecting
  requirements, then compiles those same bytes. Its bounded cache contains only
  checked modules, keyed by the complete original input including custom sections.
  The actor path remains binary-only.
- Tests cover private stream consumption affecting Public state, zero-argument
  occurrences, Public occurrence with Secret payload, malformed/noncanonical
  profiles, drift and tampering, start-function rejection, and concrete isolated
  private/public callback executions of different lengths.
- The compiler consumes an immutable `CompilerContext` declaration API. It
  resolves the exact `("ffi", name)` identity and ordered Wasm signature, preserves
  canonical profile bytes/fingerprints, and produces a requirement for independent
  runtime matching. Additive context-aware entry points pass the same context
  through single/multi-file, tool and package compilation, package re-derivation,
  CLI check/run/forge/registry/certificate reporting, MCP and server boot. Old APIs
  remain default-context wrappers. A configured profile is projected into the
  canonical model-9 envelope and checked by the linked production verifier at the
  shared formal choke point; only its zero verdict can create the formal report.
  The exact profile requirement is emitted for runtime matching. Merely constructing
  or decoding the context still does not approve a host implementation.
- `HostProfileKernel.lean` independently decodes the complete canonical provider
  declarations and checks bounds, ordering, names, enum tags, domain footprints
  and conservative declared flows. `HostProfileSecurity.lean` proves its resolved
  flow judgment, occurrence/parameter/read-domain influence bounds and decoded
  declaration bounds. The linked declaration-validation entry cannot construct a
  compilation report and is not a CSIR occurrence-safety verdict. Forty-five
  shared fixtures compare the production Rust codec, Lean evaluation and native
  Lean: seven acceptance cases and 38 malformed/unsafe rejection cases. Native
  shims check the 64 MiB ceiling before copying. Both modules participate in the
  checker fingerprint; report structure and model version are unchanged.
- `formal::project_v9_declarations`, the separate Rust `formal_v9` codec, and
  `OccurrenceWire.lean` now preserve the actual v8 prefix plus canonical tags
  44–48: full host profiles, exact FFI identity/ABI bindings, distinct actor
  operations and root-only entry/return occurrence contracts. The distinct decoded
  type retains version 9. Thirty-seven source-built shared fixtures (seven valid
  declaration envelopes, thirty refusals) agree across Rust, Lean evaluation and
  the linked declaration-only entry. The two additional positives deliberately
  include both the known repeated-send violation and its pure-guard twin:
  declaration acceptance is not occurrence-policy acceptance. Eight general
  version/binding facts and five kernel refusal witnesses are proved; five small
  positive local fixtures are executable checks, not decoder-acceptance theorems.
  Full retained profile bytes/counts are compared through Lean evaluation; the
  narrow native ABI returns only a verdict. The checker fingerprint binds the
  wire kernel and proof sources. The production occurrence verifier consumes this
  exact envelope, while the declaration-only call remains unable to issue a
  `FormalSecurityReport`. See
  [the wire contract](csir-v9-declarations.md).
- `V9BoundaryContracts` builds one bounded instruction index and rechecks actual
  FFI owners, complete operands, identities and signatures through the shared wire
  helpers. Missing, duplicate or mismatched bindings refuse extraction. Its 15
  general theorems establish returned-site/root correspondence and policy-field
  separation, not occurrence safety. Absent profiles retain Public occurrence,
  Internal parameter/result policy and an explicitly unknown footprint. Send,
  ask and spawn retain Public delivery defaults; serialization/deserialization are
  not deliveries. Root boundaries retain the exact tag-48 declaration site;
  internal returns are not root outputs. Invocation context is still explicit
  input, not proof of a genuine runtime frame. Fail-closed executable checks cover
  all seven valid shared envelopes and mutants for missing/wrong bindings, subtype
  conflation and private-payload policy laundering. No private actor endpoint
  contract or host implementation approval is supplied by this layer.
- The native build now generates matching `.olean` and C artifacts for every
  Init-only kernel in Cargo's build directory. Explicit import maps bind each
  dependent module and parity evaluation to those fresh artifacts; cached `.lake`
  imports no longer determine the native build's project-module definitions.
- AIR now records instruction provenance in private lowering buffers, including
  destination-free sends and stores. Nested expression lowering restores the
  enclosing operation's span. Finalized pre-memory/fuel statement and terminator
  maps feed the existing CSIR span side table, outside hashed bytes. A separate
  exhaustive 46-constructor classifier retains send/ask/spawn/serialize/deserialize
  identities with stable codes 1–5. These identities now feed model-9 projection;
  all five actor opcodes remain conservative Public-occurrence boundaries and no
  private actor crossing is approved.
- `OccurrenceReference.lean` is a deliberately slow, test-only control-dependence
  oracle. It uses successful-path postdominance, transitive control influence, and
  separate invocation/target-selection influence. It rejects repeated Public
  header actions and skipped actions while preserving balanced private branches,
  one-time setup, pure helpers, and justified Public continuations. Selector labels
  and possible call targets are inputs to this reference problem; this is not a
  verifier-derived security theorem or a performance-qualified checker.
- `OccurrenceReferenceProbes.lean` extracts actual targets from the decoded
  single-function counterexamples, without trusting merge markers or block-number
  ordering. It refuses calls rather than erase their effects. The original header
  action and the newly discovered acyclic backward-edge escape both reject in this
  oracle; the original Public continuation has a positive twin. Stable instruction
  IDs and requested sites must be unique, so duplicate IDs cannot mask a missing
  occurrence declaration.
- `OccurrenceRegions.lean` extracts actual instruction-level CFG edges with
  separate per-function return vertices and call sites. Its local checked-parent
  judgment proves non-vacuous successful-path continuation escape and positive
  repetition witnesses in `OccurrenceRegionSecurity.lean`; a live noncall raw
  step follows those extracted edges. Incomplete-parent and indirect-repetition
  counterexamples prevent treating this sound escape index as a complete
  occurrence classifier. Balanced calls, invocation propagation, efficient region
  transfer and the full Public proof are not consequences of this layer.
- `OccurrenceRegionConstruction.lean` builds reverse edges, a fixed-capacity
  marked-on-enqueue queue, and checked internal continuation candidates. Its
  proof layer establishes bounded queue arrays/counters and that returned
  success ranks exactly characterize finite successful CFG paths and their
  shortest lengths. Sixty-four generated three-vertex graphs agree with the slow
  oracle. Invalid candidates use an explicitly checked function-return fallback.
  This is conditional correctness of returned constructions, not solver totality,
  a complete occurrence classifier, or performance-qualified production enforcement.
- `OccurrenceTransfer.lean` and its construction/proof layers carry three private
  thresholds through actual edges until checked continuations. Rank-bounded
  replacement stops can conservatively enlarge regions but cannot clear influence
  early on a finite successful prefix. Repeated headers are covered without
  blanket SCC tainting. The constructor uses fixed `2V` queues per lane; queue
  bounds and each slot's two-change limit are proved. Sixty-four generated graphs
  construct and conservatively cover the independent reference oracle. Global
  operation-count/totality proofs and corpus precision qualification remain open;
  the parent-index check still has its separate ancestry-walk performance limit.
- `DecodedOccurrence.lean` derives selector labels from exact decoded operands,
  rejecting missing, wrong-kind, wrong-owner and out-of-bounds selectors. It
  constructs its own regions, roots and frontiers; callers supply none of those
  tables. `DecodedOccurrencePrefix.lean` derives successful-prefix private-lane
  coverage from the returned analysis. Both historical counterexamples receive
  private occurrence influence, while the loop's valid continuation remains Public.
  This is intraprocedural analysis, not v9 policy acceptance. Invocation propagation
  is a separate layer; balanced raw call/return simulation and the full Public
  theorem remain necessary.
- `AncestorIntervals.lean` builds one checked forest interval index, with fixed
  tables and constant-table ancestry queries; its proofs establish correspondence
  with parent ancestry, not completeness of postdominators. The new
  `PriorityOccurrence` layers process exact-stop offers by success rank, settle
  each node once, and prove `V + 2E` work, bounded pending storage and actual
  original-controller provenance. They retain the independent transfer postcheck
  and restore the nested diamond's Public continuation that the earlier two-change
  widening overtainted. Neither universal successful construction nor minimality
  is claimed. `RankedDecodedOccurrence` composes this path with actual selectors,
  internally checked candidates/fallbacks, and invocation propagation; it no
  longer executes historical parent-walk or two-change constructors.
- `OccurrenceInvocation` uses exact direct targets and the raw first value
  operand for closure selection. A shared dynamic summary avoids closure-by-
  function edge expansion; all-functions coverage remains conservative and
  precision-unqualified. The returned worklist closes checked call edges,
  including recursion; captures remain data, not blanket invocation control.
  `V9SourceOccurrenceChecks` executes the complete source-built declaration
  envelopes through ranked local and invocation analysis. The repeated send's
  helper receives Secret invocation influence, whereas the pure helper's caller
  retains a Public continuation. Serialization is retained separately from actual
  delivery. These are executable regression checks, not a Public theorem or a
  production-policy verdict.
- `OccurrenceActivation` derives a reusable ownership index from decoded function
  and value declarations. Entry snapshots every callee-owned scalar and aggregate
  cell, including nonparameter temporaries; return restores them before writing
  the result, including recursive destination aliases. Actor state, external
  streams/cursors and capability balances remain shared effects, not rolled-back
  locals. Its 35 public theorem declarations comprise 25 general storage,
  ownership and frame-construction results plus ten kernel-checked witnesses and
  mutants. A fail-closed check also uses the compiler-produced pure-guard envelope,
  real call/return declarations and explicit synthetic local-store mutations.
  This is not a complete instruction execution or source/machine correspondence
  proof. Genuine frame history and whole-machine activation preservation remain
  obligations; static frame coherence alone does not establish them.
- `SemanticDataflow.lean` proves the actual semantic worklist's unchanged
  `4 * cellCount` fuel bound, seed inclusion, edge closure, and leastness. Its
  structural premise is explicit: allocated block/value lookup cells and parameter
  cells must be bounded. Preservation of these bounds is proved through the actual
  edge builders, closure summaries, and graph-building folds. No fixed point or
  relational policy is assumed; these proofs are not yet the Public theorem.
- `SemanticIndexBounds.lean` derives those index bounds from actual source-record
  IDs and canonical numbering, through the real index-building fold. It also
  preserves a counterexample showing why `ProgramSafe` alone is insufficient:
  an in-memory program can pass that predicate with a noncanonical unused block
  ID outside the allocation. The wire decoder, not the in-memory judgment,
  supplies the missing numbering invariant.
- `DecoderNodeIds.lean` now proves that missing connection through the unchanged
  decoder loop: every successful decode has canonical IDs, therefore bounded
  semantic-index cells and the actual least semantic labeling. The report's
  checker-source fingerprint now binds all three proof modules; older reports
  require re-derivation even though CSIR remains v8 and certificate schema remains
  v9. No test-only occurrence oracle is included in this production proof chain.
- `V9OccurrenceDataflow` and its invocation layer add exact host-result and
  external-root entry seeds to the candidate v9 analyses. Host labels target the
  actual indexed result-value cell, not the instruction or function-local ID;
  absent-profile results remain Internal. Source seeds and semantic adjacency are
  preserved, with leastness proved using the unchanged `4 * cellCount` worklist.
  Root entry labels are invocation lower bounds, never caps on private internal
  calls; role-zero roots and return-occurrence labels add no entry seed. Nineteen
  general theorems cover exact seed provenance, leastness, preserved local seeds,
  call-graph closure and influence on actual direct/closure callees. Fail-closed
  executable checks include compiler-produced declared/legacy FFI envelopes,
  private-result branch influence, missing-seed/binding mutants and transitive
  root influence. They are not kernel fixture-acceptance proofs, balanced-run
  simulation or, by themselves, a production policy verdict.
- `V9OccurrenceKernel.lean` composes those analyses with retained-v8 verification
  and the unary instruction-indexed occurrence policy used by production. State
  ceilings use one precomputed sorted/coalesced index keyed by the exact
  `(functionId, offset)` pair. Forward coverage requires every matching declaration
  label to flow to the lookup result; a reverse witness carried by every index entry
  must resolve to a declaration with that same exact key and label. Binary-search
  soundness and a wrong-key/over-coalescing mutant make under-approximation and
  cross-actor offset laundering load-bearing failures rather than trusted lookup
  behavior. `V9OccurrenceKernelSecurity.lean` reflects successful execution into
  the unary `V9OccurrenceJudgment`; it does not prove the Public relational claim.
- `PublicRegionSecurity.lean` exposes every component of the existing Public data
  relation as a shape-preserving projection and proves the exact equivalence. It
  also proves immutable-stream preservation and successful-run accounting over
  actual `runPrefix`, including larger independent budgets and terminal starts
  with completion provenance. Invalid-PC fallback halts, traps, and fuel exhaustion
  cannot establish this success contract. Its stronger active-function/frame
  obligations remain explicit: their preservation and derivation from verifier
  acceptance have not been proved.
- `ReleaseSynchronization.lean` derives consumed prefixes and remaining suffixes
  from actual raw executions. Complete release equality aligns site, stage, and
  payload by occurrence without equal execution lengths or equal intermediate
  release counts. Its raw accounting witnesses execute four alternating release
  stages after unequal paths; mutations omit site, stage, order, later payloads,
  or duplicate occurrences. These hand-constructed accounting witnesses do not
  establish CSIR/capability-verifier acceptance. Neither new proof layer is a
  production Public claim or a current production-claim dependency.
- The v9 release-evidence template and validator are in required CI hygiene steps.
  Template success means strictly pending, not released. Tagged-evidence mode
  checks an existing tag, exact subject, complete lane inventory, numeric budgets,
  and retained artifact hashes; it does not authenticate CI provenance or authorize
  publication. No tag or completed release evidence has been created.

No existing random, actor, queue, audit, allocation, or foreign implementation is
approved as private by these changes. The production compiler emits **CSIR v9** and
the linked unary occurrence check is mandatory; declaration validation alone cannot
authorize a build. The exact envelope and checker identity are bound through the
formal report, schema-v9 certificate re-derivation/R819 checks, and the emitted
runtime host-profile section. The historical v8 acceptances remain regression
witnesses, not current authorization. There is still no production Public
corollary or completed tagged release evidence. All legacy gates remain enabled.

## Host-profile contract, version 1

This version is a separate host-profile encoding version, not a CSIR or certificate
version. Its canonical data starts with `SIGIL-HOST-PROFILE` plus a zero byte,
followed by fixed-width little-endian version, identity length/bytes, nonzero 64-bit
provider revision, domain list, and operation list. All list/string lengths are
32-bit. Domains and operations are sorted by exact identifiers; accesses are sorted
by domain. Duplicate identities/accesses and noncanonical incoming order reject.
Profiles have a 64 MiB byte ceiling, one-million-item ceiling, and 1,024-byte
identifier ceiling. Unknown enum tags or versions and trailing bytes reject.

The Wasm custom section `sigil.host-profile` contains a 32-bit requirement version
and the exact 32-byte profile fingerprint. Missing requirements reject on the
contract-bound path; duplicates, malformed requirements, unknown reserved section
versions, and mismatching profiles reject before start. A requirement is not a
certificate and does not independently authorize execution.

The initial dependency language is deliberately explicit and conservative: all
results/writes depend on occurrence, parameters, and read domains. Written domains
and results must admit that influence. An input-stream read includes cursor
advancement and must be declared read/write. Private activity cannot write a Public
domain, and a later Public result cannot read private shared state. A finer dependency
summary would require a reviewed profile-format extension, not an omitted footprint.

The provider owns these declarations and the callbacks. Registration checks identity
and ABI, **not the callback body**. Complete footprints, truthful revisions, absence
of undeclared shared state, and actual per-site/per-actor partitioning remain host
conformance assumptions. A shared PRNG cannot become per-site by annotation. A
caller-supplied decoded profile is never host approval. The generic binding helper
does not replace fuel, memory, capability, certificate, or sandbox policy.

## Remaining work

1. Complete policy enforcement of the projected context and extracted boundary
   contracts; preserve payload compatibility and add dedicated occurrence
   diagnostics. Exact extraction and host/root seeding are implemented, but they
   do not approve private endpoints or enable profile-bearing compilation.
2. Connect activation storage to the full v9 instruction/boundary machine. Prove
   genuine frame history, active-function preservation and balanced call/return
   behavior, deriving root versus internal-return context from execution rather
   than accepting it as authority. Retain shared actor/host effects across returns.
3. Connect the declaration codec and occurrence analyses to the complete policy
   judgment and raw semantics, then enable runtime/certificate binding across
   every consumer. Keep v8 witnesses and gates as independent oracles; declaration
   decoding, contract extraction and candidate analysis cannot enable production.
4. Use the source/host least-solution and root-invocation results to establish
   local and structured-region preservation, then prove the full release-conditioned
   Public weak bisimulation across independent execution lengths. Unary labeling
   and activation-restoration facts alone do not establish that relational result.
5. Wire exact claim signatures, dependency audits, constructor evidence and mutants;
   run the complete compatibility/platform/performance matrix and tagged release.

The separate implemented wire slice preserves v8 rather than just accepting a
second version in its historical decoder. Its new decoded `V9.Program` retains the
version, complete canonical host profile, exact per-FFI operation binding and
actor subtype. A digest alone cannot supply domain or occurrence
semantics, and operand counts cannot distinguish every ask/spawn shape. Send,
ask, spawn, serialize, and deserialize currently share the v8 actor opcode; local
serialization must not become an external-input operation in v9. Actual CFG
targets already exist and must be analyzed, not trusted as region certificates.
Instruction and terminator spans are now populated during AIR lowering, including
no-result instructions; synthetic prologue instructions retain the existing
declaration-level fallback. New metadata is keyed at the formal gate's pre-memory/
fuel cut, not at rewritten runtime statement indexes.

The host-profile tests are necessary groundwork. Passing them does not discharge any
of these remaining obligations or repair the original accepted counterexample.

## Validation record for this implementation slice

Local validation uses macOS ARM, Rust 1.98.0, the repository's pinned Lean toolchain,
and the installed Homebrew Z3 header/library for solver-enabled checks. Rust runs
use `CARGO_INCREMENTAL=0` (the CI setting); this affects build caching, not any
security gate. This is working-tree evidence, **not** a tagged release-evidence record.

### Existing issue and legitimate behavior

`cargo test -p sigil-compiler --no-default-features --test public_region_probes`
and the same target with `--features solver` both pass their two historical probes:
they confirm that the original loop-header boundary example **still compiles**.
The corresponding raw v8 witness remains kernel checked. Thus the occurrence-policy
finding is not fixed by this slice.

The compiler's `taint_constant_time`, `spawn_taint_sink`, `taint_join_soundness`, and
`taint_join_early_exit` targets pass in both solver configurations (64 tests per
configuration), including permitted Public occurrence with Secret payload. All 33
`formal::tests::linked_lean_` unit tests pass with solver disabled. No production
compiler acceptance rule changed.

The full compiler library unit target also passed with solver disabled: 367 tests,
including the linked verifier, malformed-IR, certificate fingerprint, source-identity,
and large-function indexing checks. This is not the complete integration/corpus matrix.

The combined invocation was `cargo test -p sigil-compiler -p sigil-runtime
--no-default-features --lib -j2`. Its runtime target initially passed 58 of 63 tests;
the five HTTP tests failed at their localhost server bind with `PermissionDenied`,
before exercising HTTP behavior. Re-running that exact built runtime test binary
with loopback permission passed **all 63 tests**. No source change or test skip was
used to obtain the passing retry.

### Contract and proof gates

- `cargo test -p sigil-abi --test host_contract`: 22 passed, including canonical
  round trips, all truncated prefixes, field-sensitive fingerprints, negative flow
  cases, and Public occurrence with permitted Secret payload.
- `cargo test -p sigil-runtime --no-default-features --test host_profile_binding`:
  10 passed; the same 10 also passed with `--features solver`. Coverage includes
  both text-input regressions, actual callback signature
  checks, pre-start refusal, and unequal private-call counts with equal Public
  state/results in the concrete isolated host witness.
- Runtime `runtime_import_contract`: 2 passed in each solver configuration;
  `z3_capability_shim`: all 8 passed with the solver enabled. The complete final
  solver-runtime command succeeded after one earlier pre-test loader stall was
  terminated and retried; the interrupted attempt is not counted as a pass.
- Runtime `export_manifest`, `soundness_contract`, and `style_census`: 5, 9, and 9
  passed respectively. The first style run exposed an existing 104-versus-92
  bare-unwrap ceiling failure; 14 test-only calls now use explanatory `expect`
  messages, without changing the ceiling or production logic.
- `lake build`: passed (887 jobs). `proofs/lean/scripts/check-no-sorry.sh` and
  `--self-test`: passed, with the existing exact 2,875-declaration census, three
  allowed standard axioms, and **one** production raw claim (SecretCT). This is
  not a new Public proof. The mechanically elaborated public-export census is 411;
  all scrub patches also pass application checks.
- `cargo clippy -p sigil-compiler --no-default-features --lib --tests -- -D warnings`:
  passed. Strict Clippy also passed for the ABI/runtime libraries and the
  `host_contract`, `host_profile_binding`, and `runtime_import_contract` targets.
  No lint budget was relaxed. Workflow validation and its planted self-tests passed.
- The existing v8 linked-verifier sub-1-ms warm-median test passed. The self-host
  five-second canary passed at 4.30 seconds before the text-input correction and
  4.28 seconds after it. Neither measures an implemented v9
  verifier; initialization, v9 peak memory, and million-record behavior remain open.

One fresh read-only candidate review found a compatibility regression in the first
host guard: it treated text-form WebAssembly as binary. The corrected path normalizes
text and validates the resulting binary, rather than exempting text from inspection.
Dedicated positive and tagged-text-before-start tests cover both ephemeral APIs.
The new positive test first failed with the binary parser's bad-magic diagnostic
against the pre-correction candidate; both text tests pass after normalization.
Host callback correctness, complete footprints, and real domain isolation remain
trusted, not established by signature checks or these test witnesses.

The complete workspace/corpus/platform matrix, v9 native and diagnostic parity,
certificate/R819 profile binding, the full Public theorem and claim audits, and the
tagged dual-gate release have **not** been completed. Existing production gates
remain enabled; no release or risk retirement is claimed.

## Continuation validation — 2026-08-31

This is additional working-tree evidence, not a replacement for the historical
slice above or the pending tagged-release record. Local Rust is 1.98.0 on macOS
ARM. Solver checks use Homebrew Z3 4.16.0, not the separately required pinned
Z3 4.12.2 CI lane. The original build directory was preserved after compiler
directory enumeration stalled; subsequent runs use an isolated temporary Cargo
target with incremental compilation disabled. Interrupted pre-test attempts are
not counted as passes.

- Full `lake build` passes (896 jobs). The complete theorem/axiom gate passes
  with a mechanically elaborated census of 3,019 and only the three allowed
  standard axioms. The separately elaborated public-export census is 555. The
  production raw-claim count remains **one**, the existing SecretCT claim.
  The proof gate's planted self-tests also pass, including refusal of a transitive
  dependency on the test-only occurrence oracle. Export scrub application checks,
  formatting, scoped whitespace checks, workflow validation and its self-tests pass.
- Compiler context integration tests: eight passed. They cover exact imported
  identity and ABI, immutable sharing, and canonical profile/requirement bytes.
  They do not assert that existing compile entry points consume the context.
- Certificate/compiler regression batch: 175 tests passed without the solver,
  and 174 with it (one package test is specific to solver-off). This covers CLI
  certificate tests, formal-security integration, local packages, three linked
  historical occurrence probes, runtime export/soundness/style censuses, and
  server certificate tests. The final 3,019-declaration soundness census was
  rerun and passed in both configurations after proof-source synchronization.
- All seven new certificate tests passed in both configurations. Synthetic host
  sections test add/change/remove/duplicate byte binding, not compiler-approved
  host-profile emission. Source re-derivation rejects those synthetic artifact
  claims; legacy runtime loading also refuses them. CLI tests vary all ten
  serialized formal-report fields. The exact eight-source checker-fingerprint
  unit passed in both configurations, as did both compiler-identity census tests.
- The release-evidence validator passed 132 planted refusal cases and the valid
  strictly pending template. That template cannot pass tagged-evidence mode.
- Strict Clippy passed for the selected compiler, CLI, server and runtime
  libraries/binary/integration targets, with `-D warnings` unchanged. The existing
  v8 linked empty-fixture warm-median canary passes its sub-1-ms bound; it does not
  print a numeric median or measure the required v9 small-fixture corpus. The
  existing five-second self-host canary passed with a 4.36-second test duration
  (build time excluded). V9 initialization/memory/platform measurements remain open.

The fresh parity run exposed an unresolved accepted-corpus blocker:
`stdlib/sigil/json.sigil` is committed as accepted but `compile_module` rejects
its `skip_ws` function with `I013`, native code 1/detail 9 at node 10018 (a loop).
Both the documented solver-off invocation and a JSON-enabled invocation reproduce
the same drift. Isolated compilation reproduces the rejection rather than a
timeout. The manifest has **not** been regenerated to accept this rejection.
An isolated checkout of pre-change branch HEAD
`a5be7f96c1c3e42e684b1496c2bda66cb769ede4` reproduces the same four-column
parity drift and diagnostic hash
`3813ee81a01f918c489a69dc493943d42f49e86b5607e6c7de4685622cf00c0f`.
Its kernels and compiler were rebuilt from that snapshot; both current and baseline
canonical parity runs report three passed, one failed, and one ignored test.
Thus this is an existing branch blocker, not a regression introduced by this slice.
A source-compatible region/call-return correction remains required before claiming
corpus parity or release readiness; the current parity failure is not counted green.

Independent review also exposed and confirmed two defects in the test-only
occurrence oracle/adapter: missing transitive control influence under a nested
Public selector, and duplicate instruction IDs masking an absent requested site.
Both now have kernel-checked rejection witnesses and legitimate positive twins.
These repairs strengthen the reference evidence; they do not fix the production
v8 occurrence counterexamples, which deliberately continue to record acceptance.

### Reproduction commands

The final targeted Rust batch was run twice using
`CARGO_TARGET_DIR=/private/tmp/sigil-cert-tests.4i99Ob` and
`CARGO_INCREMENTAL=0`. The second run adds `--features solver` and sets
`Z3_SYS_Z3_HEADER=/opt/homebrew/opt/z3/include/z3.h` plus
`LIBRARY_PATH=/opt/homebrew/opt/z3/lib`:

```sh
cargo test --offline --locked -p sigil -p sigil-serve -p sigil-compiler -p sigil-runtime \
  --no-default-features --bin sigil --test cert_gate --test local_package \
  --test public_region_probes --test formal_security --test soundness_contract \
  --test export_manifest --test style_census -j2
```

The strict lint command uses the same packages and targets, replacing `test` with
`clippy`, adding `--lib`, and appending `-- -D warnings`. Additional compiler
unit selections were `formal::tests::checker_fingerprint_binds_decoder_and_semantic_least_solution_proofs`
with `--exact` and `package::compiler_identity_coverage_tests`, using `--lib`
and `--features json` or `--features json,solver` respectively.

The parity failure is reproduced by this command both in the working tree and
the isolated HEAD snapshot `/private/tmp/sigil-head-parity.O84y5e`:

```sh
cargo test --offline --locked -p sigil-compiler --no-default-features --test parity_manifest -j2
```

Lean verification runs from `proofs/lean`: `lake build`,
`bash scripts/check-no-sorry.sh`, and `bash scripts/check-no-sorry.sh --self-test`.
No claim is made for unexecuted workspace/corpus, pinned-solver, platform, v9
performance, or authenticated tagged-release lanes.

## Continuation: native declarations, context propagation and constructed regions

The security-fix outcome remains **blocked on missing production v9 and relational
evidence**, not fixed. The original occurrence path still reproduces in the retained
v8 witnesses: a private decision changes Public action counts or skips a Public
action. No successful profile-bearing artifact or independent-length Public theorem
is claimed. The configured-context refusal is an authorization fence, not occurrence
enforcement over accepted source programs.

This continuation adds three bounded layers:

- Complete provider declarations are independently decoded and checked in Lean;
  native declaration validation never constructs a `FormalSecurityReport`.
- The same immutable context reaches every compiler and fresh certificate
  re-derivation path. Default wrappers preserve the old APIs, while configured
  profiles fail with I013 until an occurrence-aware verifier supports them.
- Internally constructed CFG continuation candidates are checked against actual
  edges, with exact successful-path rank results and bounded queue storage.
  No Rust merge certificate, assumed relational policy, or numeric backedge rule
  proves the new path lemmas. Full occurrence transfer and call/return simulation
  remain necessary before these lemmas can support a production Public claim.

The affected implementation is in `HostProfileKernel.lean`,
`HostProfileSecurity.lean`, `OccurrenceRegions.lean`,
`OccurrenceRegionSecurity.lean`, `OccurrenceRegionConstruction.lean`,
`OccurrenceRegionConstructionSecurity.lean`, the native bridge, and the compiler,
package, CLI, MCP and server context entry points. Host and raw-CSIR validation
remain distinct APIs. The native build now emits matching C and import artifacts
from the same source into its own build directory; the parity driver uses explicit
import maps, not cached project artifacts.

Ordered verification on this continuation:

1. Syntax/build/proof gates: the full Lean build passes 902 jobs. The elaborated
   census now contains exactly 3,066 public theorem declarations (47 added by this
   continuation); all use only the three allowed standard axioms. The separately
   elaborated export census is 602. The audit still exposes exactly **one** raw
   production claim, SecretCT, and all fail-closed audit self-tests pass.
2. Boundary/regression cases: all 45 committed host-profile fixtures agree across
   the production Rust codec, Lean evaluation and linked native decoder: seven
   accepted and 38 rejected. Native bridge tests pass six existing CSIR cases and
   four integration cases, including oversized-input rejection before copying,
   exact import-artifact maps, planted verdict corruption and missing reports.
   The ABI suite passes 26 tests, with only its explicitly armed fixture generator
   ignored. All 64 generated three-node CFGs agree with the slow success oracle;
   malformed-continuation, omitted-rank and duplicate-edge witnesses kernel-check.
3. Compatibility: the frozen-source selected compiler/CLI/MCP/server/package/
   certificate/formal/export/style/soundness batch passes 195 tests without the
   solver and 194 with it. Default-context twins compare real artifacts/reports;
   every configured-context entry rejects before artifact emission. All ten
   fingerprinted Lean sources and compiler identity mutation checks pass in both
   configurations. The retained historical occurrence probes still pass their
   **acceptance** expectations; they do not demonstrate remediation.
4. Release hygiene: workflow parsing and its self-test pass. The release-evidence
   validator catches all 132 planted refusals and accepts only the strictly pending
   template. No tag, completed platform matrix, authenticated CI bundle, or v9
   performance qualification has been produced. All legacy gates remain mandatory;
   SR-013/SR-017 and release eligibility remain open/false respectively.

Reproduction uses the same local toolchains and separate Cargo target documented
above. Additional commands for the new boundary are:

```sh
cargo test --offline --locked -p sigil-abi
cargo test --offline --locked -p sigil-formal-bridge
cargo test --offline --locked -p sigil-compiler --no-default-features --test compiler_context
```

The shared profile fixture driver is `proofs/lean/LambdaSigil/HostProfileParity.lean`;
the native integration target supplies the build-owned import map and requires
one exact report for every requested fixture. CI requires this triple-codec parity
on both the main checks and portability paths. These checks attest declarations and
compatibility only, not native host implementation conformance or complete Public NI.

## Continuation: decoded occurrence frontiers and source provenance

This checkpoint remains a foundation, not production v9 enforcement. The new
intraprocedural analysis reads real selector operands, constructs checked regions
and private frontiers, and proves coverage along finite successful prefixes.
It marks both retained counterexamples private and preserves the loop's Public
continuation. Those witnesses do not establish interprocedural invocation safety,
raw call-stack preservation, or the full independent-length Public theorem.

AIR now retains exact statement/terminator provenance and explicit actor subtypes.
The eight new provenance/actor tests include no-result operations, nested expression
sites, repeated identical source text, all 46 AIR statement constructors, and
planted missing/wrong classifications. Spans and actor metadata do not change
historical v8 bytes, AIR snapshots, or runtime code generation.

Validation of the frozen checkpoint:

- Full Lean build: 910 jobs. The complete elaborated theorem census is 3,104;
  the public-export census is 640. The allowed standard axioms remain three and
  the production raw-claim count remains one (SecretCT). The full audit and its
  planted self-tests pass, including transitive refusal of the new decoded
  occurrence witness namespace as a production dependency.
- All 41 selected AIR/provenance/formal/rollout/historical-probe/snapshot/style
  tests pass in both solver configurations. Strict compiler Clippy passes for
  the library and both new integration targets in both configurations.
- All 368 compiler library tests pass without the solver. The final soundness
  (nine), export (five), style (nine), checker-fingerprint (one), and compiler
  identity (two) tests pass in both configurations with the new census pins.
- The unchanged five-second self-host canary passes at 4.34 seconds. No v9
  warm-verifier, initialization, million-record or peak-memory claim follows.
- Formatting, whitespace checks and export scrub application checks pass. The
  release validator still accepts only the pending template and catches its
  132 planted refusal cases. No tag or completed release-evidence record exists.

Canonical parity still reports three passed, one failed and one intentionally
ignored generator. The sole failing fixture remains `stdlib/sigil/json.sigil`,
with the same I013/native code 1/detail 9/node 10018. Improved provenance now
identifies `i < end` at bytes 4533–4540 (line 78, column 11), instead of the whole
function at 4415–4790. Its diagnostic hash is
`4e224eb10ff712364978b219c97ab667f2b4c6e714e4eff306aed8cb09ae9e54`.
Replacing only that span in the canonical diagnostic framing reproduces the
earlier `3813ee81a01f918c489a69dc493943d42f49e86b5607e6c7de4685622cf00c0f`
hash exactly. The parity manifest is untouched; the lane is not counted green.
A narrowly scoped correction to the retained v8 helper-return check has been
raised for approval, rather than silently weakening or removing that gate.

A fresh read-only candidate review inspected the initial host declaration kernel,
proofs and native/Rust bridge without establishing another actionable defect.
It was interrupted before context/consumer threading, shared fixtures, fresh
import-artifact binding, structural bounds and these later changes. Those paths
are not independently cleared by that limited review. The executable tests and
kernel-checked proofs above are separate evidence, not a substitute claim of
complete independent review.

CSIR remains v8, certificate schema remains v9, configured profiles still refuse
compilation, and the four requested production/enforcement, end-to-end binding,
Public theorem and tagged-release outcomes remain unfinished. All legacy gates
remain mandatory; SR-013/SR-017 stay open and retirement eligibility stays false.

## Continuation: ranked regions, exact boundary seeds and activation storage

This foundation checkpoint added the ranked occurrence path, indexed boundary
contracts, host/result and root-entry propagation, and complete callee-local
storage restoration described above. The implementation outcome remains
**blocked**, not fixed: the historical source loop-header send and backward-edge
probes still reproduce acceptance through the production v8 verifier. The new
source-built checks classify the repeated send's actual helper invocation as
Secret and retain the pure helper's Public continuation, but that classification
is not yet a production policy verdict or a Public noninterference theorem.

Validation of this working-tree checkpoint, using the same local toolchains and
Cargo settings as above:

- `lake build`: 940 jobs passed. The elaborated full census is 3,274 and the
  separately elaborated public-export census is 810. Two generated equality
  instances initially exposed a mismatch in the independent Rust source census;
  replacing them with explicit, same-named theorem declarations restored exact
  agreement without changing either detector. Both instance proofs are axiom-free.
- The full proof audit and its planted dependency checks cover the new modules;
  the raw production claim inventory remains exactly one, not two. The added
  witness/source-check namespaces cannot become production proof dependencies.
- `cargo test -p sigil-compiler --no-default-features --features json --lib
  --test public_region_probes --test formal_v9_declarations
  --test formal_rollout_contract`: 368 library, three historical probe, six v9
  declaration and three rollout tests passed. The explicitly armed fixture
  generator remains ignored during normal testing. The 37 committed declaration
  cases include seven accepted envelopes and thirty refusals, not seven accepted
  secure programs.
- Solver-enabled compiler context, formal-security and v9 declaration targets:
  10, 16 and six tests passed. Source-fingerprint and complete compiler-identity
  checks passed with and without the solver. Native bridge tests: all 15 passed,
  including both shared-codec parity suites and planted verdict corruption.
- Runtime host binding, soundness, style and export targets: ten, nine, nine and
  five tests passed. Strict Clippy passed for compiler/bridge libraries and tests
  without the solver, and the compiler library plus context/formal/v9 targets
  with the solver. Formatting and whitespace checks passed.
- The unchanged self-host canary passed in 4.41 seconds. Ancestor-index and
  frontier component bounds do not establish full v9 verifier latency or memory.
  The pending release-evidence template and all 132 planted validator refusals
  passed; no actual tag, authenticated platform results or completed evidence
  bundle exists.

Canonical parity was rerun and remains red only for the same `json.sigil` row
and diagnostic hash recorded above: three tests passed, one failed, one generator
was ignored. Neither the retained v8 checker nor the parity manifest was changed
to conceal that result. Approval for the narrowly scoped helper-return correction
was still pending at that checkpoint; the subsequent approved correction is recorded below.
This is not the only remaining
work: whole-machine activation invariants, complete v9 occurrence policy and
native enforcement, successful certificate/runtime binding, the independent-length
Public theorem, and the complete tagged platform/corpus/performance evidence
remain unfinished. Unrelated `bench/**` edits remain untouched.

## Approved retained-v8 private-leaf return correction — 2026-08-31

The approved correction preserves the v8 wire format, raw execution machine and
every retained gate. It does **not** treat a module-function flag or a private
return contract as proof that an early return is harmless. A return can skip a
later Public destination, state write or boundary event even when its payload is
Secret. Full JSON compatibility, production v9 and the Public theorem remain
**blocked/unfinished**, not fixed by this slice.

The linked checker now derives a deliberately narrow private-leaf classification
once per program. Every owned instruction must pass, including instructions after
an earlier return. Every nonzero destination must have a derived non-Public label;
every return must have exactly one actual, non-Public value operand; at least one
return must exist. Calls, shared-state/external operations, releases, capability
operations, allocation and whole-machine halts cannot qualify. Address and index
operations qualify only in their nonzero-destination read form. Only this class
may use the return exception; all other functions retain the continuation check.

The fresh read-only candidate review found an error in the initial allowlist:
destination-free `Index` is also the production `StoreDynamic` representation.
The native regression first reproduced acceptance of both the read and store,
then passed after requiring a destination for `Index`, as for `Address`. The test
uses the actual two/three-value plus size/type/offset operand layouts and valid
policy records, so rejection is the continuation refusal, not malformed metadata.
This validates a classifier defect; it does not establish a source-level exploit
through array lowering, whose bounds-check traps can independently exclude leaves.

`PrivateLeafReturnSecurity.lean` proves ten general classification/cache facts and
seven kernel-checked source-program witnesses. It does not prove Public relational
preservation or genuine call-frame provenance. Its source is included in the
13-part checker fingerprint; the report layout, model version and certificate
schema stay unchanged. The witness namespace is banned from production raw-claim
dependencies and tested by the planted dependency audit.

Validation of the corrected slice:

- Full Lean build: 941 jobs passed. Independently elaborated censuses: 3,291 full
  repository and 827 public-export declarations. The full no-sorry/census/axiom
  audit and its planted fail-closed self-tests passed; one production raw claim and
  the three-axiom allowlist are unchanged.
- All three linked private-leaf regression tests passed, including skipped Public
  destinations and the read/store pair. Existing successful-escape, flat-match and
  callee-halt tests remain in the compiler unit suite.
- Solver-disabled compiler unit suite: 371 tests passed. Solver-enabled compiler
  unit, context, formal-security and declaration suites:
  418, ten, sixteen and six tests passed. Native bridge: fifteen tests passed,
  including shared codec/native parity, planted verdict corruption and the existing
  sub-1-ms warm small-fixture bound. These are not complete v9 performance evidence.
- Runtime host-binding, soundness, style and export checks passed (ten, nine, nine
  and five tests). Strict compiler/bridge Clippy without the solver and selected
  compiler checks with the solver passed. Formatting and whitespace checks passed.
- The unchanged self-host canary passed in 4.42 seconds. The release template and
  132 planted release-evidence refusals passed; no tagged evidence was produced.

The standalone whitespace helper now compiles through the linked checker. Full
`json.sigil` advances from `skip_ws` to `hex_nibble`, then still receives I013 at
semantic node 10320 (span 5318–5319, continuation detail 9). Inspection of the actual
decoded CFG found a synthetic unreachable zero-operand return in `hex_nibble`;
simply ignoring it would then reach non-leaf calls in `read_hex4`. Later functions
also contain stores, allocations and Public local destinations. They are not
covered by the proved leaf predicate, and no blanket helper-return bypass was added.

The explicit full-JSON acceptance test remains red. Canonical parity is also red
only for the committed JSON row: three tests passed, one failed, one generator was
ignored; the diagnostic digest is
`88c71e479f330fbf4ca510c342b4dbfd498f887d92e1cc199294ce611684f19f`.
The parity manifest is unchanged. Reachable-control, interprocedural effects and
activation-local storage still need a justified treatment before restoring this
whole accepted source program; weakening the final Public projection is not a fix.

Production still emits v8, profile-bearing compilation still refuses, and the
declaration-only v9 entry cannot issue a formal report. The historical occurrence
counterexamples still compile. SR-013/SR-017 remain open, retirement eligibility is
false, and all 61 unrelated `bench/**` working-tree entries remain untouched.

## Production v9 unary occurrence checkpoint — 2026-08-31

The statements immediately above record the earlier retained-v8 checkpoint. The
current production compiler now emits and authorizes **model 9**. This is a narrow,
load-bearing policy correction, not the unfinished Public theorem.

`V9OccurrenceKernel.lean` decodes the canonical envelope, re-runs the complete
retained-v8 raw-semantic verifier, constructs the semantic dataflow and ranked
occurrence analyses, derives invocation labels, validates activation ownership,
and enforces instruction-indexed occurrence ceilings. The linked C/Rust bridge has
a distinct `verify_v9` entry; declaration validation remains incapable of issuing
a report. `formal::verify_with_context` checks those exact bytes and only its zero
verdict can construct a model-9 `FormalSecurityReport`.

The production checks close the concrete unary omissions found during review:

- every destination is bounded by the join of local and invocation occurrence,
  preventing callee-global temporary writes from escaping the current historical
  raw storage model;
- every actual FFI value argument flows to its exact bound profile parameter, and
  effective occurrence flows to the operation occurrence contract;
- state-write ceilings come from a precomputed sorted/coalesced index at the exact
  `(functionId, offset)` key. Every matching declaration must flow to the coalesced
  label, and every index entry carries a reverse witness to a declaration at that
  same key and label. This prevents both dropped declarations and an invented or
  over-coalesced key from laundering a Public write through another actor's equal
  numeric offset;
- all five actor opcodes remain Public-occurrence boundaries while the current raw
  machine exposes all five as boundary events; and
- successful external return occurrence is checked once at the stable function-root
  contract rather than at the private-control-selected internal return instruction.

`V9OccurrenceKernelSecurity.lean` reflects the executable check into the unary
`V9OccurrenceJudgment`. Its analysis premise includes the least extended semantic
solution, the ranked local transfer postcheck, and the closed invocation graph.
The final Lean proof gate records an exact census of **3,320 theorem declarations**,
**three explicitly allowed axioms**, and **17 pinned legacy `native_decide` uses**;
the v9 occurrence additions introduce no new `native_decide` authorization path.
The theorem deliberately does not claim that the historical raw machine executes
activation-local save/restore, nor does it derive the independent-length Public
weak bisimulation.

Certificate and runtime binding use the same boundary. The report hashes the exact
v9 envelope and checker-source inventory; schema-v9 consumers compare every field
against fresh re-derivation and return R819 for model, checker, CSIR, count, or host
profile drift. Explicit profiles are emitted once into each Wasm ring. A
contract-bound runtime matches that section against the immutable profile whose
typed callbacks were installed. Legacy actor/ephemeral entry points fail closed on
profile-bearing artifacts; profile-free WAT is normalized, inspected, and compiled
from the same bytes so text is neither regressed nor a bypass.

Focused production validation is green for the compiler library, explicit-context
entry points, actual FFI argument policy, actor occurrence reject/accept twins,
model-9 report determinism, Wasm profile sections, certificate R819 drift, package
re-derivation, and runtime profile/WAT binding. The full retained-v8 JSON acceptance
row is still red at the previously recorded continuation check and the parity
manifest remains unchanged. Compiling Lean-generated C at the fingerprinted
production optimization level reduced the exact authorizing v9 warm-fixture median
from roughly 1.54 ms to roughly 220 µs without changing policy or the 1 ms threshold;
the complete 20-test native bridge suite passes. The full Lean build and proof audit
pass with the census above. Broader workspace/platform/corpus lanes remain release
gates rather than being inferred from these focused results.

The first production self-host run also exposed three input-linear native-stack
hazards: host-result seed collection recursively consumed the complete record list,
priority-frontier fuel sizing used a right-recursive list sum, and the retained-v8
state-label join recursed after visiting the tail. All three now use accumulator
folds with unchanged policy results. Executable Lean witnesses cover 400,000 records
for each traversal, Rust source lints forbid the recursive forms, and a linked v9
large-record fixture exercises the native path. The unchanged self-host canary now
passes on the ordinary test stack in 2.02 seconds, below its five-second ceiling.
These are availability and bounded-execution repairs; they do not supply the open
Public theorem or broaden the unary v9 claim.

No tagged evidence was produced. The full Public theorem, activation/raw
correspondence, retained-v8 JSON acceptance parity, cross-platform evidence,
semantic authority/affine/quantity closure, and tagged dual-gate release remain
open. The repository pins required CI context names, but GitHub branch-protection
configuration is external state and has not been independently verified here.
SR-013 and SR-017 therefore remain accepted risks, every legacy gate stays
mandatory, and retirement eligibility remains false.

## Raw Public theorem closure checkpoint — 2026-09-01

The preceding production-v9 checkpoint records the unary enforcement boundary at
the time it landed. The independent-length raw Public result is now proved as well;
this appended checkpoint supersedes only the earlier "theorem remains open" status,
not the historical implementation record or its still-open rollout conditions.

`PublicBisimulationSecurity.lean` provides
`raw_public_weak_bisimulation_of_v9_verified`. From production v9 verifier
acceptance and the unique successful `analyze?` result, it constructs a finite weak
alignment internally—there is no caller-supplied `FinitePublicAlignment`, merge
certificate, or relational policy. The construction uses the actual unsanitized
`rawSemanticProgram`, matching verifier-owned Public cut points, well-formed
Public-low-equivalent starts, and two independently sized successful executions.
Its exhaustive progress dispatcher covers matching instructions, unequal branch
and loop regions, direct and closure calls, recursive activations, genuine internal
and top-level returns, per-site external-input streams, actor/state operations, and
multiple releases.

Release accounting begins with equality of the complete raw release traces. That
premise retains every site, stage, payload, occurrence, and order. The proof derives
the Public-occurrence subsequence used while stuttering; private-region release
events remain in the raw trace and are not erased or replaced. The final pinned
claim, `RawClaimSurface.public_delimited_release_noninterference`, accepts separate
left and right fuel budgets backed by genuine successful runs and concludes equality
of the full modeled `publicProjection`—Public scalar and aggregate cells, Public
actor state, and Public-site external cursors—plus the ordered Public
output/boundary trace. Ordinary-Secret timing, control, address, allocation, and
cost equality remain outside this theorem; the equal-length SecretCT trace result
is separate.

The complete Public proof dependency closure participates in the checker-source
fingerprint, so changing it forces certificate re-derivation through R819.
`RawClaimSurface` exposes the pinned Public corollary alongside the SecretCT
corollary, and the proof gate performs a transitive two-claim audit that rejects
sanitized-machine, assumed-policy, retired-claim, and test-oracle dependencies. The
claim remains conditional on decoded-CSIR verifier acceptance; it does not establish
Rust source-to-CSIR projection or a general AIR/Wasm adequacy theorem.

Final production validation exposed and closed one performance bug in that authorizing path.
The output-policy loop reconstructed the complete decoded semantic program once per return site;
on the self-host trio (about 170 outputs and 250,000 CSIR records) this made the otherwise linear
V9 check behave as output-count times record-count. The verifier now constructs the decoded
machine and the occurrence-raised machine once and threads both through the instruction checks.
The executable judgment is unchanged, and `V9OccurrenceKernelSecurity` proves the cached entry
equivalent to the same declarative occurrence policy. A source-structural test forbids routing
the production loop back through the rebuilding wrappers, while the unchanged end-to-end canary
guards actual behavior. Locally, the pre-fix unlimited run took 24.93 seconds (23.14 seconds in
the native V9 verifier); the corrected canary completed in 2.37 seconds under the existing
five-second ceiling. These figures are regression evidence, not tagged release performance data.

This is not release or retirement evidence. The retained JSON acceptance/parity
blocker is still open, no tagged cross-platform zero-disagreement release has been
recorded, and the versioned v9 evidence record remains non-retirement-eligible.
Authority/BV32/slot, affine, and quantitative operational correspondence still
depends on the retained v6/Rust/Z3 layers. Source projection, Lean native
generation/runtime, AIR/Wasm lowering, Wasmtime, scheduling, queues, and hardware
timing correspondence remain explicit assumptions. SR-013 and SR-017 therefore
stay Accepted, and every legacy gate remains mandatory.

## JSON acceptance and stable root-output correction — 2026-09-01

The JSON blocker recorded above is now closed locally. The cause was a conflation of
two different facts: a function's declaration-owned external output occurrence, and
the local occurrence of the particular return expression selected by private control.
V9 now keeps them separate. Every top-level output uses the stable function-root node
as its boundary site, while payload visibility joins the operand label with the
verifier-derived local return occurrence. A private-path early return therefore emits
the real output occurrence but hides its payload; it is neither rejected solely for
choosing a different return instruction nor erased as a silent step.

Source callability is now preserved explicitly from typed functions through AIR.
Private module helpers and synthesized closures remain callable inside the semantic
machine, but receive role-zero root contracts and are not emitted as Wasm exports.
Public functions and runtime actor/handler entries retain their external roots. This
is a deliberate Wasm-output correction: canonical parity regeneration changed only
the inner/outer byte-hash columns for 97 accepted rows, with no accept/reject,
diagnostic, source, or metadata-column drift. A focused Wasm regression proves a
private helper remains internally callable while only its declared public caller is
exported.

The broader compiler sweep also exposed an existing `tool_main` rule that AIR had
not preserved: the embedding entry may return an `@Internal` packed pointer/length
value from FFI even when its written return annotation defaults to `@Public`. The
Rust taint oracle and retained-v6 projection already implemented that host-bridge
contract; semantic AIR had projected `@Public`, causing v9 alone to reject the
otherwise established tool fixture. `TypedFunction` now owns the single
`is_tool_main_entry` predicate and `effective_return_taint` rule consumed by taint,
formal projection, AIR lowering, and effect-entry preservation. A compiler test
pins the resulting `@Internal` AIR return contract before checking linked-v9
acceptance and certificate artifacts.

The final workspace lint sweep was initially mistaken for a hang because Cargo
prints only crate-level progress while `--all-targets` expands each integration
test into a separate frontend unit. A clean timing run found 125 `sigil-runtime`
units: 123 took more than 20 seconds under the host's implicit 32-job setting,
for 3,422 cumulative unit-seconds. There was no pathological target; the maximum
was 30.0 seconds. Capping the identical target set at eight jobs reduced the
runtime lane from 6m13s to 3m11s, cumulative unit time to 1,484 seconds, and
cumulative system time from 919 to 200 seconds. A separate concurrent Cargo
check also demonstrated that build-lock waiting was invisible in the old step.
`scripts/clippy-workspace.sh` now bounds only excessive implicit parallelism,
permits an explicit positive override, and emits 30-second heartbeats. Required
CI uses the runner for both no-default and JSON lanes, and `workflow_yaml_lint`
fails if either lane bypasses it or its job cap, coverage command, strict warning
policy, or heartbeat is removed.

The exact `stdlib/sigil/json.sigil` linked-verifier test passes, and the unmodified
248-row corpus followed by the prescribed output-changing regeneration now passes the
canonical parity comparator (four passed, one regeneration test ignored). The full
`RawClaimSurface` build passes, and the fail-closed proof audit now covers exactly
3,760 theorem declarations against the unchanged three-axiom allowlist and two raw
production-claim dependency closures.

This closes the retained JSON acceptance/parity blocker, not the release boundary.
No tagged cross-platform zero-disagreement evidence has been recorded, the v9 evidence
record remains non-retirement-eligible, and authority/affine/quantity operational
closure plus the SR-017 correspondence assumptions remain open. Every legacy gate
therefore stays mandatory.

## Retained-verifier rejection of the acyclic backward escape — 2026-09-02

The postdominance-aware merge restore recorded above changed the retained verifier's
verdict on the historical acyclic backward escape, and the probes that pinned the old
verdict had not been rebuilt. The declared merge block of that program is reached by
only one dispatch arm, so `semanticSuccessfulPathsReach` no longer lets it restore the
Public pc; its output of a Public-contract value under Secret control is now a flow
violation at node 21 (detail 1), and the shared fixture bytes decode to the packed
native verdict 90194378754. `V8OccurrenceProbes` and the Rust `public_region_probes`
lane pin that rejection instead of acceptance, while the raw-machine theorems in the
same module still show the two Public-equivalent starts producing different Public
output traces, which is why rejecting the program is the sound verdict. The lower
block's output is still decoded as a Public occurrence, so the fixture remains
regression evidence for the v9 occurrence policy rather than a production claim.

The same rule moved the private-leaf `laterWrite` witness: the later write runs under
the branch's private pc, its Secret result violates the written value's Public
contract, and the program is rejected as a flow violation at that contract node rather
than as a missing Public continuation. The leaf classification itself still holds for
that witness, because every result the function computes is private.

The same merge moves the production site of the loop-header-send rejection: the
`occurrence-loop-header-send.sigil` fixture is still refused with detail 40, but at
the send boundary (node 88, the `worker.send(Ping(7))` span) rather than at the
payload boundary before it (node 83, the `7` span), because the payload now converges
under the postdominance-aware pc restore. `v9_production_verifier` and
`formal_v9_declarations` pin the new site.

## Postdominator candidate for the region construction — 2026-09-02

The first Linux CI run of the bench slot-registry lane rejected every committed
datetime and uuid attestation with the v9 malformed verdict (detail 40), and main's
`taint_join_early_exit` pattern-collision programs (a `match` on a Secret enum inside
a `while`, every arm `break`ing or `continue`ing) were refused the same way. The cause
was precision, not policy: `RankedDecodedOccurrence.constructRegions?` built one
whole-program candidate from the structural merge hints, and a single controller
whose declared continuation is not its actual convergence point cannot satisfy the
rank and ancestry obligations. A branch whose arm returns has no in-function
postdominator except the return; a `match` whose arms all leave the loop never reaches
its declared merge. The all-or-nothing fallback then re-parented every controller in
the program to its function return, so a synthesized `tool_main`'s
`if test() { mask |= bit }` diamonds never converged (the second test call ran under
Internal occurrence, its callee inherited that invocation occurrence, and the FFI
clock/random site inside it violated its Public occurrence contract), and the
pattern-collision programs' Public `return x` after the loop sat under the Secret
match.

The structural candidate is still tried first, unchanged, so every program it already
satisfies keeps its exact regions and verdict. Only when it fails is a second candidate
built from the actual control graph: `OccurrenceRegionConstruction.postdominatorParents`
computes the immediate postdominators of the live nodes with respect to the successful
exits by rank-ordered iterative refinement (Cooper–Harvey–Kennedy over (rank, id) keys,
which strictly decrease toward the exit, with fuel-bounded chain intersection that
reports "no meeting point" instead of guessing). That is the exact continuation of every
controller, so neither shape above forces any other controller to its function return.
Dead nodes keep the structural hint, which the checks treat as unconstrained. This
changes only candidate selection: the interval and escape checks validate every parent,
the `constructed_regions_are_checked` obligation now covers three checked alternatives,
and the whole-program fallback behind a still-failing postdominator candidate is
unchanged, so the result remains exactly as validated as before.
`early_return_elsewhere_keeps_sibling_diamond_continuation_public` pins the shape in
`RankedDecodedOccurrenceWitnesses`: the structural candidate fails, the older
construction falls back and leaves the sibling diamond's continuation Secret, and the
postdominator construction keeps it Public while the early-returning branch's own
continuation correctly stays under that branch. The theorem census moves to 6400.

A rank-aware, locally repaired variant was tried first and rejected: re-parenting a
failing controller to its function return is always checkable but parents the
`break`-out-of-`match` shape to the return, which is exactly the false reject above.

## CT-source policy records on calls, and the legacy-host refusals of the tools corpus — 2026-09-02

The first run of the `checks` lane's tools/ compile sweep on the merged branch refused
28 of the 214 reference tools. One was a kernel bug: `formal.rs` deliberately emits the
CT-source policy record (class 10) for a call or state read whose result contract is
`@SecretCT` with an empty operand mask, because `semanticCtSourceObservedLabel` derives
that record's observed label from the callee's return contract or the state contract
rather than from a selection, but `semanticPolicyClassRecordOK` still demanded a
nonzero mask for every class outside `{3, 5, 7, 14}`. Every call to a `@SecretCT`
function (`ct_clamp` composing `ct_max`/`ct_min` in `tools/ct_demo.sigil`) was therefore
refused as malformed record detail 10. The record rule now exempts class 10 on `.call`
and `.stateRead`; the policy check itself is unchanged.

The other 27 are refused by design. Each performs a host call (`fs_read`, `http_get`)
inside a branch on an `@Internal` value, usually the error code of the previous host
call, and without a host profile every host operation's occurrence is declared Public
(`V9BoundaryContracts`: legacy host occurrence is Public, its parameter and result policy
Internal), so the second call's occurrence would leak Internal control to the host and
the production verifier refuses the program with occurrence detail 40. They are listed in
`tools/v9-legacy-policy-rejections.txt`, and the sweep pins exactly that refusal for each
row, so a relaxed policy, a stale row, or an unrelated failure all red the step. Bringing
those tools back needs either a host profile that declares the operations
Internal-occurrence, which `sigil check` cannot take today, or restructuring them so no
host call sits under Internal control; neither is decided here.

## Closure calls against secret-returning functions — 2026-09-02

`readme_compiles.rs` refused the README language tour on the merged branch: the tour's
`apply_twice(f: Fn(i64) -> i64, x)` calls `f` through a closure value, and the tour also
declares `ct_check`, which returns `bool @SecretCT`. The v8 semantic dual gate's dynamic-call
summary (`addSemanticClosureEdges` / `addSemanticDynamicFunctionSummaries`) is the
complete-bipartite relation over every decoded function, so the closure call's destination
receives every function's return label, `apply_twice`'s Public return contract sees a
SecretCT source, and the retained verifier reports flow detail 1 at that return. Named
functions are not first-class values in SIGIL (`apply_twice(plain, 3)` is an undefined
local), so the sound narrowing would be to closure-kind functions (wire kind 4) together
with a machine model in which closure calls select only closure targets; that touches the
raw-machine step relation and its security proofs and is not attempted here. The README tour
now keeps the information-flow example in its own block and says why; every other block is
unchanged. This is a precision gap, not a soundness gap: nothing is accepted that was refused
before.

## `@Flow` per-instantiation projection — 2026-09-02

The v8 semantic dual gate seeds a `@Flow` contract at `@Secret` and connects a
direct call's destination to the callee's return cells, so a Public or Internal
caller of any taint-polymorphic function was refused with flow detail 1 at its
own return: the type checker's polymorphism (the body re-checked once per
admissible label, the result carrying the join of the arguments) had no
counterpart in the projection. `formal::instantiate_flow_functions` now supplies
it without touching the kernel or its proofs. `taint_check::flow_call_instantiations`
re-runs the per-label body checks with a recorder and yields, for every call to a
`@Flow` callee, the label its arguments joined to under the checking context
(the enclosing `@Flow` instance, or none). The projection then clones each
callee once per Public or Internal label that occurs, with its `@Flow` contracts
made concrete at that label, `$`-prefixed export names (internal roots) and
`externally_callable` cleared, and routes the recorded call sites to the clones;
clones are routed the same way, so instances cascade through helper chains. A
`@Secret` site keeps the original, whose seed already covers it, and so does any
site the recorder did not see, which can only over-taint. The exported original
keeps its declared `@Flow` contracts and remains the host-facing root.

Every instance is an ordinary function to the kernel: its parameter contracts
refuse an argument above the instantiation, its return contract refuses a body
that launders, and the invocation and occurrence analyses see real functions.
Nothing computed in Rust reaches the CSIR as a verdict; the routing is a
declaration the kernel re-checks. Scope: a `@Flow` function that constructs a
closure is left uninstantiated, so its callers keep the conservative verdict.
`formal_flow_instantiation.rs` pins the recorder, the instances, their roles,
and the absence of instances for `@Secret`-only callers.

## The ephemeral host's declared profile — 2026-09-02

The legacy-host refusals above were the absence of a declaration, not a policy the tools
violate: without a host profile every host operation is Public-occurrence, while the host
these tools run under, `execute_ephemeral`, can perfectly well be called under Internal
control. `sigil_runtime::ephemeral_host_profile()` now states that host as a canonical
`HostContractProfile` (`sigil-ephemeral`, revision 1): every `ffi` operation the ephemeral
linker defines, name for name and type for type, with Internal occurrence, Internal
parameters, and Internal results. `ephemeral_profile_declares_exactly_the_linked_ffi_imports`
asserts the table against the real linker in both directions, so an operation added to one
side and not the other fails there.

The executor accepts a module that requires exactly that profile's fingerprint and still
refuses any other requirement (fail closed), while a module with no requirement keeps its
legacy semantics; `profile_bound_tools_run_only_under_the_matching_host` pins both edges.
Callers opt in by name: `sigil check|run|forge --host-profile ephemeral`, the
`"host_profile": "ephemeral"` service key in sigil-serve, and the `host_profile` argument of
the MCP `sigil_check`/`sigil_forge` tools. The tools/ compile sweep now pins both verdicts
for `tools/v9-legacy-policy-rejections.txt`: refused in the legacy context, accepted against
the ephemeral profile. Nothing in the kernel or the policy changed; the host merely declares
what it is.

A runtime built with the `solver` feature links one more `ffi` operation, the Cap<Z3> shim
`z3_check`, so it is a different host and declares itself as one: identity
`sigil-ephemeral-solver`, the same table plus that operation, and therefore a different
fingerprint. A tool bound to the default host is refused by the solver host and vice versa,
in the fail-closed direction the exact-fingerprint rule exists for: its declarations were
verified against an operation set the other build does not link. The inventory test runs in
both builds, so each declares exactly what it links.
