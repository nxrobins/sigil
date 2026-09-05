# The SIGIL Claims Ledger

> **This file is the single authoritative statement of what SIGIL proves.** Where any other
> document, README, paper, or PR description disagrees with this one, **this one is right and the
> other is stale** — because this one is machine-checked and they are not.

## Why this file is machine-checked

Every prose claim in this project has drifted at least once. Measured, not asserted:

* The documented capstone size was **9.6 KB stale** — six spec files carried a number that no
  assertion contained.
* A prose table declared constructs "fenced, never wrong bytes"; the executable registry showed one
  of them emitting **wrong bytes**, and two others already **byte-equal**.
* The document written *specifically to stop this* went stale about its own pins **within days**.

The lesson is not "write a better document." It is that **a claim no test enforces is not a claim,
it is a hope.** So this ledger carries tags that
`crates/sigil-runtime/tests/claims_ledger.rs` enforces on every CI run:

| tag | meaning | enforced by |
|---|---|---|
| `@test:<fn>` | proven by that test; the function **must exist** in the repo | `pin6_every_claim_names_a_real_test` |
| `@thm:<Name>` | proven by that Lean theorem; the name **must be in the axiom-target census** | `pin6_every_lean_claim_names_a_censused_theorem` |
| the *unproven* marker (§D rows) | **no executable proof**; allowed, but **counted and pinned** | `pin6_unproven_claim_count_is_pinned` |
| the fenced `pins` block | every number **must equal** the owning Rust constant | `pin6_ledger_numbers_match_the_code` |

`@thm:` names are manifest-relative — `Chk.sound`, never `LambdaSigil.Chk.sound`. Being in
`proofs/lean/axiom-targets.txt` is a strong statement: the axiom gate derives its census from Lean's
*elaborated environment* and requires it to equal that file, and `soundness_contract.rs`
independently requires that file to equal the complete source-derived theorem set. So a cited
theorem provably exists, is public, sits inside the root import closure, and was audited against the
three-axiom allowlist.

The `@thm:` tag was added on 2026-08-14 after an audit found this ledger's own formal-proof rows had
drifted exactly the way §"Why this file is machine-checked" predicts: claim 26 described the Lean
manifest with an entry count that was long stale. `@test:` coupled claims to Rust tests and
left the Lean side as unchecked prose — so the Lean side drifted, in the file written to stop drift.

Adding an unbacked claim therefore requires bumping a pinned constant with a stated reason. Removing
one is a ratchet win. **The ledger cannot quietly grow claims it cannot support.**

---

## §A — The pinned numbers

Mirrored from the Rust constants; a disagreement fails the build. Never hand-edit without
re-measuring (SC-P1: pin the measured value, never the documented one).

```pins
PIN_CAP0_SRC_CHARS = 1150219
PIN_CAP0_MODULE_BYTES = 454099
PIN_CAP0_RUNNABLE_SRC_CHARS = 1150574
PIN_CAP0_RUNNABLE_MODULE_BYTES = 454453
PIN_WITH_DRIVER_SRC_CHARS = 1151054
PIN_WITH_DRIVER_MODULE_BYTES = 454798
PIN_STAGE1_CAP0_MODULE_BYTES = 454099
PIN_STAGE1_RUNNABLE_MODULE_BYTES = 454453
PIN_STAGE1_WITH_DRIVER_MODULE_BYTES = 454798
PIN_FLOOR_SRC_CHARS = 1000000
PIN_FLOOR_MODULE_BYTES = 400000
PIN4_KNOWN_DIVERGENCES = 0
PIN_AXIOM_TARGETS = 1297
PIN_DIAGNOSTIC_TEST_GAPS = 62
PIN_STRIP_LIST_ENTRIES = 6
```

**Prose in §B does not restate these numbers.** Claims 26 and 29 each carried a figure that had
gone stale (a manifest size of 103 against an asserted 160; a gap count of 65 against an asserted
64), because a number written into a sentence has no owning assertion — the exact failure this
file exists to prevent, surviving inside the file itself. Measurements belong in this block, where
`pin6_ledger_numbers_match_the_code` checks them; claims cite them by name.
@test:pin6_section_b_prose_states_no_unpinned_measurement

---

## §B — What is proven

### Self-hosting / byte identity

1. **The self-hosted emitter reproduces the trusted oracle's WebAssembly byte-for-byte on the
   certified compiler source.** Stage-1 (the selfhost compiler running *as WASM*:
   `lex → parse → mn_expand → ai_encode_wasm`) emits a module hex-identical to Stage-2 (the Rust
   oracle stage chain). @test:boot_self_byte_capstone
2. **Adding a runnable pipeline entry preserves that identity.** @test:boot_self_runnable_byte_capstone
3. **The whole with-driver compiler — library + entry + a real `tool_main` — self-certifies
   byte-identically with no splice.** That `tool_main` is the GATED driver (claims 36–37): one
   artifact, not two, so the byte identity certified here is the identity of the thing that
   executes. @test:ag6_5_with_driver_byte_capstone
4. **The oracle independently accepts the certified input** (it is a real program, not a shape that
   only the shadow tolerates). @test:cap0_oracle_accepts_capstone_input
5. **An executable self-reproducing fixed point exists.** Running the selfhost-emitted runnable
   library (plus fixed raw glue) on its own source reproduces that library byte-for-byte.
   *(SUPERSEDED by claim 36 — that round trip needs a splice stub and runs the emit lane only.
   Kept because the splice path is still asserted and still green, not because it is the
   strongest form.)* @test:stage3a_executable_closure
6. **Every function in the certified input emits poison-free** — the per-function W-emit poison
   census returns exactly zero names (the 422 → 0 ratchet). @test:cap0_poison_census_ratchet
   and @test:cap0_runnable_poison_census_zero
7. **That census is not vacuous** — fed a known-poisoning construct it names the poisoned function.
   @test:pin_census_anti_vacuity

### Trusting-trust divergence detection

8. **A DDC-shaped byte-identity canary catches a self-recognizing divergent compiler**, and the
   marked compiler still functions (so detection is not merely "it broke"). *(This row's second
   compiler is the Rust oracle; claim 39 re-runs the same comparison with the frozen seed instead,
   and HB-3 states the bound that survives.)*
   @test:stage3b_ddc_honest_passes_backdoored_caught and @test:stage3b_backdoored_compiler_still_functions

### Fail-closed emit

9. **No known hole emits wrong-but-plausible bytes.** Every row of the fence registry is
   oracle-rejected, loudly poisoned, or byte-equal — never divergent. @test:pin_fence_registry_never_diverges
10. **Generic-enum method monomorphization is byte-identical**, and un-covered shapes fail closed
    rather than diverging. @test:ag6_generic_enum_method_corpus and @test:ag6_generic_enum_method_no_divergence
11. **Generic-enum instance cell sizing is byte-identical in both construct forms** (qualified and
    bare), at width-4/width-8 and with multiple type parameters, across annotations, returns, and
    free-call arguments. Unresolved self-host contexts fail closed.
    @test:generic_unit_variant_layout_is_context_independent
    @test:ag6_6_narrow_variant_size_corpus
    @test:ag6_7_unresolved_generic_enum_contexts_fail_closed

### Anti-erosion (the pins themselves)

12. **The certified artifact cannot silently shrink** — exact size pins plus catastrophic-shrink
    floors. @test:pin_certified_artifact_size
13. **Achievement-critical self-hosting and security evidence cannot silently shrink.** Named suite
    obligations, semantic corpus floors, and claim-tag coverage protect the pipeline, emit,
    frontend, taint, capability, effect, ring, ownership, claims, soundness-contract, and
    runtime-import suites. @test:pin_semantic_evidence_manifests and
    @test:air_semantic_evidence_manifest
14. **This ledger's own machinery is non-vacuous.** @test:pin6_extractors_are_not_vacuous

### CI gating (PIN-5)

15. **`main` is protected and requires green CI.** Required status checks: `test`, `checks`,
    `solver`, `hygiene`, `interp-ddc`, `workflows-parse`, and the two Lean lanes (the public
    development and the research overlay) — enforced on admins, so no one (human or agent) can
    merge red. The required-check NAMES are pinned to the workflow jobs that produce them, and
    every workflow producing one is asserted to carry no `paths:` filter (a path-filtered
    workflow can never satisfy a required check). @test:pin5_required_check_names_match_workflow_jobs

### Content integrity (PIN-7)

16. **The certified artifact's CONTENT is pinned, not merely its size.** SHA-256 digests of all
    three certified sources AND all three oracle-emitted modules, so a change that PRESERVES
    character and byte counts can no longer pass unnoticed. Demonstrated: a zero-delta edit leaves
    the size pins green and fails the digest by name. Includes a carriage-return guard, so a CRLF
    checkout reports a line-ending problem rather than an inscrutable digest mismatch.
    @test:pin_certified_artifact_digest — instrument proven against NIST known-answer vectors and
    for same-length sensitivity by @test:pin7_digest_instrument_is_not_vacuous

17. **The strip list — the certified surface's most sensitive dial — is pinned**
    (`PIN_STRIP_LIST_ENTRIES`, §A), with the names proven non-empty and distinct. Adding a name removes a function from what is
    certified while both stages move together, so the byte capstones cannot see it. The fixed-size
    array types make the edit a compile error first. @test:pin_strip_list_length
18. **The with-driver artifact's SOURCE length is pinned**, not only its module size — it is the
    artifact that actually self-certifies. @test:pin_certified_artifact_size
19. **The pins measure exactly what the capstone certifies.** The with-driver input is built by ONE
    shared function used by both `ag6_5_with_driver_byte_capstone` and the size/digest pins, so a
    pin cannot report green about an artifact nobody certified. Previously two duplicated
    constructions with nothing enforcing they matched. @test:ag6_5_with_driver_byte_capstone

### Runtime / host boundary

20. **Every registered actor, forge, unconditional FFI, and solver-gated FFI import is classified;
    declared imports really link, unknown imports fail closed, and the shared behavioral probes have
    zero unexplained drift.** This is import-totality plus bounded differential evidence, not a claim
    that every model-specific operation has identical semantics.
    @test:host_import_manifests_are_total_over_linker_registrations
    @test:declared_host_imports_really_link_and_unknown_imports_fail_closed
    @test:rtc_runtime_differential_census @test:rtc_import_set_is_fenced
21. **Forge-side actor/capability operations trap rather than silently no-op**, and reject hostile
    arguments. @test:rtc_forge_traps_actor_and_cap_ops and @test:rtc_actor_ops_reject_hostile_args

### Solver

22. **The Z3 surface is exactly the declared fragment** (set equality, not containment), and the
    guard's dispatch sites are isolated. @test:observed_fragment_matches_the_inventory_manifest and
    @test:fragment_guard_imports_are_isolated

### Formal proofs

23. **The λ-SIGIL fixture ids match an in-repo expected-id list, the Lean obligation-id set is
    pinned, and every id in their union has an explicit side classification and reason** — drift or
    an unexplained difference fails. This is deliberately NOT a 1:1 Rust↔Lean correspondence: some
    Lean rules map to solver-lane fixture families, and some mechanisms exist on only one side.
    *(Corrected, task #254: the prior claim said the two lists "match". They do not — the test that
    "backed" it never read Lean.)*
    @test:fixture_ids_match_expected_ids @test:lean_obligation_ids_are_pinned
24. **The production security pipeline has an explicit ordered typed-pass manifest, and its complete
    resolve, type, security, desugar, lower, capability, ownership, memory, fuel, runtime-spec, and
    Wasm sequence is pinned against deletion or reordering.**
    @test:compiler_security_pipeline_is_complete_and_ordered
25. **Production ownership state is propagated over AIR control flow.** A move or live borrow on any
    reachable predecessor is visible at joins and loop back-edges; returning paths do not flow into
    sibling continuations. O007 uses the same consuming-site census as O001 rather than a spawn-only
    special case. @test:own0_cfg_move_state_is_propagated
    @test:own0_cfg_borrow_state_is_propagated @test:own0_oracle_pins
26. **The Lean axiom audit covers exactly every declared theorem.** A committed manifest
    (`PIN_AXIOM_TARGETS` entries, §A) drives elaboration against an exact three-axiom allowlist; an
    independent Rust census derives the theorem set from source and rejects target deletion,
    addition, duplication, or drift. Two further fences close the ways a theorem used to escape that
    census: the manifest is compared against a census derived from Lean's *elaborated environment*
    (so any declaration syntax the text scraper cannot parse is still covered), and every file
    outside the root import closure — which the environment census cannot see — is required to
    declare nothing provable at all.
    @test:lean_axiom_gate_covers_every_declared_theorem
27. **Capability sinks deliberately require the capability type's full authority mask.** Callee
    bodies do not infer or weaken that contract; a narrowed three-authority capability is rejected
    while its full-authority twin is accepted. @test:cap_sink_contract_is_deliberately_full_mask
28. **Known unsupported self-host taint contexts reject explicitly.** Early exits in nonpublic
    contexts, tuple lets in nonpublic contexts, guarded matches, actor/spawn boundaries,
    closure-value taint, and unknown syntax emit `SH_TAINT_UNSUPPORTED`; the composed self-host
    compiler treats that verdict as a taint-stage rejection. (All-public tuple lets, `break`, and
    `continue` are SUPPORTED — the oracle desugars the first pre-taint and emits no codes for the
    other two, so the all-public projection is exact there.)
    @test:sh_taint_unsupported_shapes_are_explicit
    @test:boot1_unsupported_taint_shape_fails_closed
29. **The diagnostic security surface is measured and drift-pinned.** The census distinguishes
    registration, active production references, direct test references, dedicated fixtures, and
    self-host shadows; its direct-test backlog (`PIN_DIAGNOSTIC_TEST_GAPS` codes, §A) and two
    compatibility aliases are exact manifests rather than hidden omissions.
    @test:diagnostic_security_surface_is_censused
30. **Malformed ownership AIR fails closed without panicking.** Before dataflow, the verifier
    rejects duplicate block IDs, missing entries, and every missing direct or structural CFG
    reference, including unreachable blocks, branch merges, and dispatch exits.
    @test:malformed_air_cfg_fails_closed_without_panicking

### Absolutes on the selfhost side

31. **Stage-1's own output size is pinned absolutely, not merely transitively.** The six pins in §A
    measure the *oracle*: `pin_module_bytes` calls `oracle_compile`, so the selfhost side was
    reachable only through each capstone's `shex == ohex`. Three further pins measure the
    SELFHOST-emitted module directly, at the point each capstone already holds it — so a weakened
    or deleted equality assertion can no longer leave Stage-1's size unpinned, and moving both
    stages together now requires repinning both sides with their own stated reasons.
    @test:boot_self_byte_capstone @test:boot_self_runnable_byte_capstone
    @test:ag6_5_with_driver_byte_capstone
32. **The self-certified with-driver artifact is a real WASM module — it validates and compiles.**
    Byte-identity between two emitters is a statement about agreement, not about wellformedness:
    both stages emitting identical garbage satisfied every prior assertion. The module is
    constructed; two mutants invalid by construction (a broken magic header, and a truncation one
    byte inside the final section) are rejected, so the check is not vacuous. Its execution is
    claimed separately (claims 36–37). @test:ag6_5_with_driver_byte_capstone

### Proof-to-implementation bridges

33. **The λ-SIGIL taint obligations are consumed by the implementation.** Every id in
    `TaintSafety.lean`'s M-T4 table is paired with a `.sigil` fixture whose SIGIL verdict is asserted
    on the {T001, O001} surface — four rejects emitting exactly their headline code, four accept
    twins emitting none, each twin isolating the single property that made its reject illegal (a
    public-guarded branch of the same shape as the secret-guarded one; two declassifies through two
    caps against two through one). The id sets are required **equal in both directions**, so a new
    Lean obligation with no fixture and a fixture claiming an unproved correspondence both fail by
    name. This bridges VERDICTS, not mechanisms: the calculus is first-order while the Rust pass is
    interprocedural, and the shared scope is sink-safety.
    @test:lean_taint_obligation_ids_match_the_rust_half @test:taint_differential_verdicts_match
    @test:taint_corpus_carries_both_verdicts

### The checked capstone (HB-2's first clause retired)

34. **The certified artifact is checked by a seven-gate chain built from its own gate sources, and
    the module emitted behind those gates is byte-identical to the oracle's.** The composed
    Stage-1 tool — whose `sh_compile` body is nr → tc → ring → effect → taint → cap → own → emit,
    each gate short-circuiting — runs over `cap0_input`, which contains every gate's source, so
    the run is the gates checking themselves. The *executing* binary here is a test-side tool the
    oracle builds from the same gate text, not the artifact itself; claim 36 is the form where
    the artifact's own `tool_main` drives the chain.
    Each gate enforces its parity-covered code subset (the discipline all seven now share; tc was
    the one gate consuming a raw stream, and its multi-module walk was FIXED en route — before
    that fix its green over the multi-module artifact was vacuous, caught by the mutant suite
    below). @test:hb2_checked_byte_capstone
35. **That OK is a verdict, not sleep.** Five per-gate mutants — a minimal violation injected into
    the certified artifact — each reject at their gate carrying their headline code (nr N007, tc
    T041, taint T001, cap C003, own O001; the assertion is that the code is PRESENT in that gate's
    stream, not that it is alone there), through the capstone's own entry point, and — since the
    sweep of 2026-08-01 — through the executed artifact's entry point as well. Ring and effect have
    no injectable mutant: their registration is module-attr-gated and the artifact's modules carry
    no ring attr. That exemption is a documented census in the test's own comment rather than an
    assertion; what is executable is the composed-pipeline witness `boot1_every_gate_fires` and the
    corpus rows of claim 37. A genuinely-undefined callee rejects at the tc gate
    with T062 (the shadow resolves intrinsic calls and bare unit-variant values, so T060/T062 are
    enforced; the emit's `!!` poison remains the last-line backstop for shapes still outside the
    covered projection). @test:hb2_checked_capstone_mutants_reject
    @test:hb2_unknown_callee_rejects_at_tc @test:hb1_executed_artifact_rejects_mutants

### The stub-free gated fixed point (HB-1 retired to lineage)

36. **The with-driver artifact, EXECUTED on its own source, accepts it through its own gate chain
    and reproduces its own bytes — no splice, no glue, a real `tool_main` driving the full
    `sh_compile` chain.** F(source(F)) = `OK:` + hex(F): the executed body is ingestion → lex →
    parse → mn_expand → nr → tc → ring → effect → taint → cap → own → emit, the same chain the
    checked capstone certifies (claim 34), now inside the artifact itself rather than a test-side
    tool. Precisely: this test asserts an `OK` verdict and byte equality — that every gate FIRED
    is claim 37's corpus and the mutant witness in claim 35, not this row. The same executed
    artifact is a working COMPILER, not an echo chamber: fed one different covered program it
    emits exactly the oracle's bytes for THAT program and not its own. Claim 5's splice-stub round
    trip and the intermediate emit-lane driver are both superseded by this gated form. The source
    it certifies is harness-assembled (library + entry + driver), not a committed `.sigil` file.
    @test:hb1_stub_free_executable_fixed_point
    @test:hb1_executed_artifact_is_a_compiler_not_an_echo
37. **The gates FIRE in the executed body.** The executed artifact, fed the whole boot corpus,
    agrees with the composed test-side pipeline EXACTLY — accepts as `OK:<hex>`, rejects at the
    same gate with the same detail string — and the corpus's reject rows cover every gate,
    including ring and effect, which the append-mutant suite (claim 35) structurally cannot fire
    on the unringed artifact; a closing assertion pins that all-seven corpus coverage (a guard on
    the corpus, not on the artifact — per-row assertions are what the artifact must satisfy).
    A driver that routed around any gate would accept that gate's reject row and fail the
    differential. Accepts are checked against the ORACLE's bytes for each program, so an emit that
    poisoned to the `!!` sentinel cannot pass as a compile, and rejects must carry a real code
    rather than an empty stream or the fail-closed unsupported verdict. Four further rows place a
    violation in a program's SECOND module — the shape that made the tc gate vacuous in #682, and
    the one the rest of the corpus does not exercise.
    @test:hb1_executed_artifact_runs_the_gates
    @test:hb1_multi_module_rejects_fence_the_vacuous_gate_class

### The committed seed (lineage)

38. **The repo carries the compiler as a committed, digest-pinned SEED, and CI proves the seed
    regenerates itself.** `seed/sigil-seed.wasm` must be byte-identical to the oracle's emit of
    the certified source (a moved source without a same-PR succession fails), and EXECUTING the
    committed seed on that source must reproduce the seed byte-exactly. Stated exactly: while both
    tests are green the committed bytes and the freshly-oracle-compiled module are the SAME bytes,
    so this is not a new byte-level property over claim 36 — what it adds is **persistence and a
    checked lineage record**: the artifact survives in the repo, and `seed/PROVENANCE.md`'s newest
    row must describe it (source digest, seed digest, byte count). Succession is a fenced ritual,
    not CI: the next seed is written from the OLD seed's own output only after that output is
    asserted byte-equal to the oracle's emit (agreement in the Wheeler/DDC sense). When the
    certified source changes what the compiler EMITS, the old seed's output applies the old rule
    and cannot agree; the ritual then takes one more stage — the compiler the old seed built
    compiles the certified source again, and THAT output must agree with the oracle and be its own
    fixed point — so lineage still passes through the old seed. One such emitter-rule succession
    has been committed (2026-09-02, export hygiene); the ritual's unarmed verify mode recomputes
    the committed lineage and writes nothing.
    @test:seed_is_the_oracle_emit_of_the_certified_source @test:seed_self_regenerates
    @test:seed_provenance_row_matches_the_committed_seed
39. **The DDC's second compiler is the frozen seed, not the Rust oracle.** The committed seed
    compiles the DDC input itself and delivers the verdict: the honest selfhost emitter agrees
    with it byte-for-byte (clean bill), and the backdoored A′ diverges by exactly the benign
    marker (caught). Stated directly as the DDC conclusion: two compilers written in **different
    languages and frozen at different times** — the Rust oracle, hand-written and built by rustc,
    and the seed, written in SIGIL and executing as WASM — produce identical bytes for the same
    source, and that equality is not trivially satisfiable (A′ fails it under the same
    comparison). It is genuinely exercised: the DDC input is a DIFFERENT source from the one the
    seed is pinned against, so the seed computes rather than replays. **Scope, stated exactly:**
    their PROVENANCE is not different — the seed is oracle-built and claim 38 re-asserts it equal
    to a fresh oracle emit on every run. No `oracle_compile` adjudicates, and no rustc-built
    *compiler* produces either compared value; the seed side is committed bytes, though the
    wasmtime host executing them is Rust, and the honest side's BINARY is still built by the
    oracle from SIGIL source at test time (Rust's surviving bootstrap role, HB-2). The comparison
    is therefore a FROZEN SIGIL compiler against a FRESHLY-BUILT one, not an oracle-free pipeline.
    HB-3 states what that does and does not buy.
    @test:stage3b_ddc_second_compiler_is_the_seed
    @test:stage3b_seed_and_oracle_agree_on_the_ddc_input

### A second implementation (the DDC residue)

40. **An implementation whose lineage does not pass through the Rust oracle reproduces the
    committed seed byte-for-byte.** `interp/` is a SIGIL interpreter written in Python: no Rust,
    no build step, no third-party packages, and no code ported from `crates/sigil-compiler/`. It
    takes the certified source as INPUT — its composition digest-verified against the same pin the
    Rust side carries, machine-checked equal — and runs it through the real `selfhost/*.sigil`
    lexer, parser, monomorphizer, the `sh_compile` gate chain and the emitter, plus the stdlib's
    own `str_concat` / `str_join` / `str_itoa` / `str_bytes_eq` executing over a modelled linear
    memory. It emits a module whose SHA-256 equals `seed/sigil-seed.wasm`'s exactly. **This test
    observes no individual gate** — it asserts an `OK` verdict and byte equality; that the gates
    FIRE is claim 37's corpus and claim 35's mutants, and on this artifact ring and effect are
    structurally inert (module-attr-gated, and the certified modules carry no ring attr), the same
    disclosure claim 35 already carries. It runs in
    minutes, not hours — throughput figures are machine-dependent and deliberately not claims.
    A Thompson backdoor in the seed's BINARY — logic absent from its source — would make these
    differ. **Stated exactly**, because the looser reading is an overclaim: the program the
    interpreter loads is parsed from the digest-verified `S` itself — not from the source files it
    was composed out of, which would be a strict superset carrying six stripped functions the pin
    never covered — but it calls `lex`/`parser_parse`/`mn_expand`/`sh_compile` directly rather than
    through the artifact's own `tool_main`, and `Vec` is substituted (HB-3 bound 2). The artifact
    under test is read only AFTER the emission exists, so "the seed is never an input" holds by
    construction rather than by review. **The witness is an INPUT-MUTATION probe**: a perturbed
    `S` must emit different bytes, so an implementation that replayed stored bytes would fail even
    though the verdict alone cannot tell the two apart. Two earlier witnesses were vacuous with
    respect to the verdict and both were defeated by the same stub — one hashed a tampered seed
    against itself, the other compared the emission against a tampered seed, which can never fire
    on a passing run since `tamper(seed) != seed` by construction. HB-3 states what this does and
    does not establish.
    @test:interp_ddc_reproduces_the_committed_seed
    @test:interp_certified_digest_matches_the_rust_pin
    @test:interp_ddc_lane_is_wired_in_ci
41. **That interpreter agrees with the oracle layer by layer, not merely at the end.** A fixture
    corpus is compared at four layers — token encoding, parse-tree encoding, name-resolution
    encoding, and the whole compiler's frozen protocol (emitted WASM for the accepting fixtures, a
    reject verdict for the rest) — with ANY disagreement failing the run and a separate ratchet
    floor catching checks that silently stop being compared. Both sides run the same
    `selfhost/*.sigil` modules, so a disagreement is an
    interpreter-semantics bug rather than a difference of opinion about the language. The answer
    key is generated and kept current by the Rust side (a normal test recomputes every entry, so
    it cannot go stale), and the harness proves it can fail by requiring a perturbed source to
    produce a different encoding. The comparison RUNS as a named test in the required lane —
    the tags below previously named only the Rust-side key checks, which never invoke the
    interpreter at all.
    @test:interp_differential_agrees_layer_by_layer
    @test:interp_golden_is_current @test:interp_golden_is_not_vacuous

### Mechanized core soundness (Lean)

42. **The core soundness theorems are mechanized, censused, and audited under the three-axiom
    allowlist.** Type soundness — no configuration reachable from a well-typed program is stuck —
    is `@thm:type_soundness`, built on preservation (`@thm:preservation`). Capability safety — a
    well-typed program never exercises authority outside its declared ceiling — is
    `@thm:capability_safety`. Effect safety — only effects in the declared row escape a well-typed
    program — is `@thm:effect_safety`. Taint noninterference — a well-typed program never writes a
    value to a sink below its taint label — is `@thm:taint_noninterference`. Every name is in the
    censused manifest (claim 26), so each provably elaborates, is public, and was audited against
    the three-axiom allowlist. §D's bound governs the reach: these theorems model the calculi, not
    the shipped checker code.

43. **Every successful production compilation has passed the exact model-9 Lean CSIR occurrence
    verifier, including its complete retained-v8 joint decision.**
    Three typed-program walks remain exhaustive over every statement and expression constructor,
    and an exhaustive post-desugar AIR match emits a resolved semantic section. The canonical
    bounded CSIR contains a semantic manifest, functions, typed SSA values, blocks, instructions,
    variable-length contiguous operand records, numeric destinations and references, plus the v6
    obligation records, taint seeds, monotone edges,
    capability origins/derivations, authority and slot meets, branch/fallthrough and loop-edge
    markers, signed quantity cells, normalized literal-RHS difference constraints, mandatory
    split/draw guard links, Public amount sinks, sinks, CT uses, and release stages,
    Version 8 appends declarative label/flow contracts, capability-type declarations, exact
    refinement facts, runtime-guard declarations, and instruction policy classes. It contains no
    Rust-computed taint label, capability-legitimacy verdict, derived authority mask, affine
    verdict, or relational-policy claim. Model 9 wraps those exact v8 bytes with canonical host,
    FFI, actor, and function-root occurrence declarations. The compiler calls the statically linked
    Init-only `OccurrenceKernel.exportedVerify`, which first runs
    `SemanticKernel.verifyProgramWithRawSemantics` over the retained prefix and then derives v9
    semantic/dataflow, structured-region, invocation, and boundary facts, at the shared compiler
    choke point. The declaration decoder is a separate non-authorizing API. Only a zero production
    v9 verdict constructs a model-9 `FormalSecurityReport`;
    malformed projection, initialization failure, or disagreement is I013. The verifier's joint
    local-obligation implication is `@thm:Combined.joint_security_of_verified`. Certificates are schema v9 and
    execution compares the complete freshly re-derived report; absence or CSIR/checker/model drift
    is R819. Version 8 rejects inconsistent semantic counts, ownership/ID duplication,
    noncanonical owner order, empty or unterminated blocks, malformed destinations,
    noncontiguous operand slices, wrong instruction arities or operand order, and missing or
    cross-function CFG/function references. The retained v6 layer computes cyclic taint/pc-taint fixed points in Lean and checks every accepted
    edge as a post-fixed-point constraint; `@thm:Combined.graphLabels_least` proves the worklist
    result is below every independent solution, while `@thm:Combined.graph_verifier_sound_and_complete`
    relates the executable decision to the graph judgment over those least labels.
    `@thm:Combined.capability_verifier_sound_and_complete` relates the executable ordered
    capability derivation to its judgment: origins, restriction/split/draw BV32 propagation,
    control-flow meet, slot authority meet, sinks, and release-capability kinds are checked from
    Lean-produced states rather than Rust legitimacy flags or final masks. Empty slot takes remain
    accepted guarded runtime traps: the verifier checks any possible successful continuation at
    the slot ceiling, while the runtime produces no child on the empty path.
    `@thm:Combined.path_affine_verifier_sound_and_complete` relates the executable path-aware
    consumption state machine to its judgment: mutually exclusive `if`/`match` arms start from the
    same snapshot, only fallthrough arms reach the may-consume join, capability φ-results remain
    unavailable if any represented arm consumed its candidate, repeatable loop edges preserve
    loop-head origins, and `break` consumption reaches the loop-exit join. The v6 quantitative
    classifier is sound and complete for the emitted literal-RHS, zero-anchored fragment:
    `@thm:Combined.difference_classifier_sound_and_complete_of_nodes` derives its edge-shape and
    implicit-i64 premises from canonical, quantitatively well-formed records, while
    `@thm:Combined.unsupported_cross_cell_constraint_rejects` pins unsupported cross-cell input as
    malformed. Guard presence and successful transition conservation are also proved.
    The v8 verifier directly computes least taint and pc-taint over semantic SSA/CFG records. Rust
    gives reassigned AIR names security-only SSA versions, inserts predecessor-compressed phi
    records at reachable joins, and marks type-proved unreachable exhaustive-match fallthroughs;
    Lean checks the resulting envelope and applies structured branch/loop pc restoration. It then
    checks label/flow contracts, state/output sinks, T020--T029/T031--T033 policy classes, direct
    assignment/return/call/state-result T030 CT-source rules, Public quantity operands, required split/draw guards,
    release stages, capability type identities, and local
    BV32 attenuation shapes. `@thm:Combined.v8_semantic_verifier_sound_and_complete` relates that
    executable decision to `V8SecurityJudgment`. `SemanticSecurity.lean` decodes that production
    suffix into the unsanitized deterministic security-event machine; release events carry exact
    site, stage, and payload. `@thm:Combined.Semantic.state_well_formed_preserved` covers every raw
    constructor. `@thm:Combined.raw_secretCT_static_safe_of_v8_verified` proves that exact native
    acceptance supplies the decoded premise; `@thm:Combined.raw_secretCT_step_lockstep_of_v8_verified`
    and the claim-surface
    `@thm:Combined.RawClaimSurface.secretCT_delimited_release_trace_equality` therefore make the
    equal-length raw SecretCT result production-facing. A transitive elaborated-environment audit
    rejects any dependency of that corollary on a sanitized or assumed-policy symbol and includes
    a planted fail-closed self-test. Dynamic closure calls now conservatively propagate caller pc,
    selector, argument, and return edges to every possible target; the direct-call-only mutant is
    theorem-breaking. The linked relational decision also distinguishes ordinary early returns
    from non-Public control: a non-Public arm may trap, but a successful exit must occur only after
    a verifier-derived Public continuation. For flat matches, only the enclosing wrapper exit
    restores pc-taint; an inner test's else/catch-all target is not a post-dominator. The
    legacy-accepted early-output mutant and a linked catch-all escape mutant now fail at their
    enclosing control sites. Type-proved unreachable AIR fallthroughs are encoded as traps rather than successful
    halts, and a halt in a callee reached below a non-Public caller pc is rejected at the callee
    site; both mappings have structural or linked-native regression fences. The v9 occurrence
    decision has an instruction-indexed declarative surface:
    `@thm:Combined.V9.OccurrenceKernelSecurity.v9_occurrence_verifier_sound_and_complete`. Its accepted
    analysis carries least semantic labels, the ranked local transfer postcheck, and the closed
    invocation graph. Destination writes use the join of invocation and local occurrence; FFI
    checks cover every actual argument and the exact declared occurrence; state writes use the
    owning function's state contract rather than a global equal-offset join; and every actor opcode
    is conservatively Public while the raw machine exposes it as a boundary event. Root return
    occurrence is checked at the stable external function boundary, not at whichever internal
    return instruction private control selects. Those unary verifier facts are now connected to
    the actual raw call/return machine by
    `@thm:Combined.V9.PublicBisimulationSecurity.raw_public_weak_bisimulation_of_v9_verified`.
    The theorem constructs its finite weak alignment internally by strong induction over the sum
    of two independently sized successful executions. It handles matching Public steps,
    independently long structured private regions, direct and closure calls, recursive
    activations, per-site external inputs, genuine internal and top-level returns, and repeated
    releases without accepting a caller-supplied alignment or relational policy. Complete release
    equality retains every site, stage, payload, occurrence, and order; the proof derives the
    Public-occurrence subsequence used during stuttering rather than assuming per-step release
    alignment. The pinned production corollary
    `@thm:Combined.RawClaimSurface.public_delimited_release_noninterference` therefore gives, for
    separate successful-run fuel budgets, equality of the full `publicProjection` and the ordered
    Public output/boundary trace. Ordinary-Secret timing, control, address, allocation, and cost
    equality are deliberately outside that result and remain distinct from the equal-length
    SecretCT trace theorem. The complete Public proof dependency closure participates in the
    checker-source fingerprint, so its change requires certificate re-derivation through R819.

    This is not yet the retirement boundary. Full semantic origin/authority, slot-meet, affine CFG,
    and balance-transition derivation still relies on the retained v6 obligations and mandatory
    Rust/Z3 gates. The relational machine is a security abstraction, not a source/AIR/Wasm
    adequacy theorem, and tagged cross-platform zero-disagreement evidence has not yet been
    recorded; the committed v9 evidence record remains explicitly non-retirement-eligible. Those
    remaining operational and rollout conditions stay in SR-013; source projection and post-CSIR
    correspondence remain SR-017.
    Local accepted-corpus parity includes the committed JSON library. Private source helpers are
    represented as internal role-zero semantic functions and are not exposed as Wasm exports;
    the resulting intentional byte changes are pinned by the regenerated parity manifest.
    @test:every_successful_compilation_has_fresh_formal_evidence
    @test:formal_report_and_csir_fingerprint_are_deterministic
    @test:semantic_literal_payload_changes_the_csir_fingerprint
    @test:declaration_success_does_not_authorize_an_occurrence_boundary_violation
    @test:production_v9_rejects_actor_send_in_secret_loop_header
    @test:production_v9_preserves_the_pure_secret_loop_header_twin
    @test:production_v9_enforces_actual_ffi_arguments_against_the_bound_profile
    @test:gate_cert_rejects_changed_host_occurrence_metadata_as_r819
    @test:ci_keeps_production_v9_and_release_enforcement_commands
    @test:json_library_retains_its_committed_acceptance
    @test:private_source_helpers_are_callable_internally_but_not_wasm_exports
    @test:linked_lean_accepts_canonical_v8_semantic_envelope
    @test:linked_lean_rejects_wrong_v8_semantic_constructor_count
    @test:linked_lean_rejects_noncontiguous_v8_operand_slice
    @test:linked_lean_rejects_missing_v8_cfg_target
    @test:linked_lean_rejects_v8_without_a_semantic_manifest
    @test:planted_bad_authority_is_rejected_by_linked_lean
    @test:linked_lean_derives_transitive_taint_instead_of_trusting_a_sink_label
    @test:linked_lean_derives_bv32_attenuation_instead_of_trusting_a_mask
    @test:linked_lean_slot_take_uses_the_meet_of_put_authorities
    @test:linked_lean_accepts_a_guarded_empty_slot_take
    @test:linked_lean_empty_slot_take_still_enforces_the_ceiling
    @test:slot_take_on_empty_traps_unreachable
    @test:linked_lean_accepts_one_consumption_in_each_exclusive_arm
    @test:linked_lean_rejects_two_consumptions_on_one_path
    @test:linked_lean_rejects_use_after_a_may_consume_join
    @test:linked_lean_rejects_consuming_a_loop_head_capability_on_a_back_edge
    @test:linked_lean_accepts_a_single_consumption_on_a_break_exit
    @test:linked_lean_carries_break_consumption_to_the_loop_exit
    @test:exclusive_branches_may_each_consume_the_same_capability
    @test:use_after_a_may_consume_join_keeps_the_source_level_o001
    @thm:Combined.loop_backedge_taint_rejects
    @thm:Combined.loop_backedge_consumption_rejects
    @thm:Combined.loop_backedge_mutant_readmits_repetition
    @thm:Combined.missing_pc_join_mutant_readmits_violation
    @thm:Combined.empty_slot_take_accepts_guarded_continuation
    @thm:Combined.empty_slot_take_still_enforces_authority_ceiling
    @thm:Combined.capability_forgery_rejects
    @thm:Combined.capability_mask_mutant_readmits_violation
    @thm:Combined.alternative_path_consumption_accepts
    @thm:Combined.same_path_double_consumption_rejects
    @thm:Combined.canonical_semantic_envelope_accepts
    @thm:Combined.wrong_semantic_constructor_count_rejects
    @thm:Combined.missing_cfg_target_mutant_rejects
    @thm:Combined.noncontiguous_operand_mutant_rejects
    @thm:Combined.wrong_instruction_arity_mutant_rejects
    @thm:Combined.semantic_dispatch_policy_accepts
    @thm:Combined.missing_semantic_dispatch_policy_rejects
    @thm:Combined.policy_on_unconditional_jump_rejects
    @thm:Combined.public_ct_source_accepts
    @thm:Combined.missing_ct_source_policy_rejects
    @thm:Combined.internal_ct_source_rejects_t030
    @test:linked_lean_rejects_v8_block_without_a_terminator
    @test:linked_lean_rejects_v8_reordered_owner_records
    @test:linked_lean_rejects_v8_reordered_sibling_values
    @test:linked_lean_rejects_v8_reordered_sibling_blocks
    @test:linked_lean_rejects_v8_terminator_destination
    @test:linked_lean_rejects_v8_wrong_operand_order
    @test:linked_lean_rejects_v8_cap_restrict_without_mask
    @test:linked_lean_rejects_v8_cap_restrict_over_copy_values
    @test:rust_and_lean_wire_opcode_tables_are_identical
    @test:linked_lean_enforces_direct_t030_ct_source_policy
    @test:package_certificate_nested_unknown_fields_fail_closed
    @test:parity_manifest_matches_the_committed_rows
    @thm:Combined.use_after_may_consume_join_rejects
    @thm:Combined.divergent_arm_does_not_poison_join
    @test:gate_cert_missing_formal_report_emits_r819
    @test:gate_cert_tampered_csir_fingerprint_emits_r819

44. **Malformed generic-call and taint-recovery shapes reject diagnostically instead of aborting.**
    The established generic-call acceptance surface is unchanged, including its certified-selfhost
    parity. If recovery produces a monomorphized call whose positional counts disagree, the public
    partial-typed-program interface remains safe for diagnostic aggregation: taint analysis visits
    every supplied argument, rejects missing targets and positional-count mismatches with I013, and
    never truncates a mismatch into an accepted verdict. A source fence prevents always-on
    panic/assert/unwrap primitives from being reintroduced into this user-reachable pass.
    @test:every_wrong_generic_call_arity_is_i013_not_an_abort
    @test:malformed_partial_typed_call_fails_closed_in_taint
    @test:taint_checker_source_has_no_release_abort_primitives

45. **The production formal verifier retains bounded large-envelope coverage.** The real self-host
    trio projects roughly a quarter-million CSIR records and must pass the exact linked Lean verifier
    inside the corpus validator's unchanged five-second fail-closed budget. A separate structural
    canary rejects the measured regression patterns: rebuilding graph adjacency per cell;
    rescanning every semantic record for owners, references, or policy masks; using linear
    visited-list membership inside structured-CFG traversal; and materializing the dynamic
    closure×function taint-edge product. It also forbids reconstructing the complete decoded
    semantic machine once per output, and pins shared semantic indexes/labels, compact
    dynamic-call summary cells, cached decoded/occurrence-raised machines, and bounded
    tail-recursive operand traversal. The canary has an
    explicit command in a required CI lane, and another test
    prevents that command from disappearing. This is regression evidence for the measured fixture
    and known bug classes, not an asymptotic proof or a claim that all one-million-record inputs
    finish within five seconds.
    @test:selfhost_trio_completes_within_validation_budget
    @test:lean_kernel_caches_whole_program_indexes_outside_inner_loops
    @test:linked_lean_indexes_large_single_function_without_nested_copying
    @test:ci_keeps_formal_verifier_scaling_canary

---

## §C — The honest bounds (anti-claims)

**These are load-bearing. Every downstream claim — papers, README, PR prose — must stay inside
them.** They are stated as anti-claims so a future reader cannot quietly widen them.

* **HB-1 — seed lineage is AGREEMENT, not provenance.** One residue is retired and one is not.
  RETIRED: the emit-lane bound, by claims 36–37 — `tool_main` drives the full seven-gate chain,
  and every gate is witnessed firing in the executed body. NOT retired, only made explicit and
  CI-enforced: the artifact is **oracle-built**. Claim 38 does not remove that dependence, it pins
  it — the committed seed is re-asserted byte-equal to a fresh oracle emit on every run, and the
  only `seed/PROVENANCE.md` row is genesis, oracle-built. CI **checks** that the seed reproduces
  itself; it never re-derives or writes one (the writer is the ignored succession ritual). So
  nothing in the bytes can distinguish seed-built from oracle-built while the two agree —
  agreement is what DDC offers, and it is detection, not provenance (HB-3 governs that claim).
* **HB-2 — SIGIL checks SIGIL over a curated fragment, with Rust still the trust anchor.** The
  first clause of the original bound — *no checker runs in the executed Stage-1* — is retired by
  claim 34: the checked capstone's executed path is `lex → parse → mn_expand → the seven gates →
  emit` over the certified artifact. Three clauses SURVIVE, unweakened: the fragment is
  **monomorphic** (mn_expand'd, house-dialect); each gate enforces only its **parity-covered code
  subset** — the tc gate is an ALLOWLIST of 25 T-codes, so every other T-code the oracle can emit
  is dropped there; T046/T071 are merely the two singled out in the source comment because the
  certified artifact would otherwise trip them, while T060/T062 are ENFORCED (a genuinely
  undefined callee rejects at the tc gate, claim 35, with the emit's `!!` poison as the last-line
  backstop for shapes still outside the covered projection); and Rust remains **both bootstrap
  and oracle**. "SIGIL checks SIGIL" is now true exactly as far as the shadows' differential
  evidence reaches, and no further.
* **HB-3 — a second implementation now closes the binary-vs-source gap; what survives is the
  SPEC gap and the toolchain regress.** The history: the original bound was *circularity* (the
  "independent" second compiler was the Rust oracle); claim 39 narrowed it to *time* (the frozen
  seed judges, but is itself oracle-built); and claim 40 retires that too. `interp/` is a SIGIL
  interpreter in Python — no Rust, no build step, no third-party packages, nothing ported from
  `crates/sigil-compiler/` — and it executes the certified source and reproduces
  `seed/sigil-seed.wasm` byte-for-byte. A Thompson backdoor in the seed's **binary** would make
  those differ, so that class is now detectable by an implementation the oracle did not produce.

  Three things survive, and they are not small:

  1. **A shared misunderstanding of the language is invisible.** Both implementations were written
     against the same understanding of SIGIL; if that understanding is wrong in the same way
     twice, they agree and are both wrong. DDC never addressed this class — the layered
     differential (claim 41) is the evidence that bears on it, and it is differential evidence
     over chosen inputs, not a proof.
  2. **`Vec` is substituted, not executed, and the driver is bypassed.** The interpreter provides
     `Vec` natively, so `stdlib/sigil/vec.sigil` is not run by the second implementation. The word
     "substituted" understates the reach: measured over a self-compile prefix, the `Vec` shim
     intercepts **269,370** method dispatches against **34,825** record- and enum-method calls that
     do execute as SIGIL — roughly eight times every executed SIGIL method call combined. It also
     calls `lex`/`parser_parse`/`mn_expand`/`sh_compile` directly rather than through the certified
     artifact's own `tool_main`, so that driver and the ingestion methods it uses
     (`from_bytes`/`unwrap_or`/`as_output`) are not executed either. Nor are `str::len`,
     `str::byte_at` and `str::substr`, which the interpreter implements natively — they genuinely
     ARE compiler primitives (`str_concat` calls `.len()` and `.byte_at()`, so treating them as
     library functions would be circular), but "everything else executes as real SIGIL" read past
     them. `vec_load`/`vec_store` are NOT in the surface either, in the opposite direction: they
     appear nowhere in `interp/`, because the substituted `Vec` sits above them and they never
     execute. Everything else — including the stdlib string layer (`str_concat`, `str_join`,
     `str_itoa`, `str_bytes_eq`) over a modelled linear memory with
     `alloc`/`store8`/`load8`/`str_from_raw` — does execute as real SIGIL. That
     string layer was substituted until an audit on 2026-08-02 found it: those four are not
     primitives, they are ordinary SIGIL called hundreds of times including from the emitter, and
     faking them made the comparison blind over exactly the region it was meant to cover.
  3. **The regress does not terminate.** Naming the actual stack: the evidence-producing lane runs
     **rustc + PyPy 3.10** (CPython locally), and PyPy's own bootstrap passes through CPython — so
     "two independently-derived toolchains" is generous, since the second is not independent of
     the third. What changed is still the size of the required conspiracy: an attack must now
     compromise several toolchains in mutually consistent ways rather than one compiler binary.

  Also unchanged: the demonstrated backdoor remains a **benign passive marker** with **no
  second-generation self-perpetuation** (a self-perpetuating quine is an explicit anti-goal), and
  the *genesis* seed was oracle-built (`seed/PROVENANCE.md` records it). What would strengthen
  this further is not another implementation but **independent authorship** — a second party
  writing an implementation from the specification without reading ours, or reproducing the seed
  from source on their own machines.

Three further scope limits, equally load-bearing:

* **The byte capstones are RELATIONAL.** Their headline assertion is Stage-1 == Stage-2, which
  stays green when both stages move together. Absolute size is carried by the §A pins, which now
  measure **both** sides — the oracle's output and Stage-1's own (claim 31). What remains
  relational is the *identity*, not the *size*.
* **The certified surface excludes a strip list** of stdlib leaf functions and (for the two library
  capstones) the driver.
* **The SIGIL checker is partial.** Refinement types absent; capabilities reduced to a bitwise
  shadow valid only on slot-free, full-mask-sink programs; ring, effect, taint and ownership all
  restricted to named code subsets. Post-AIR memory/fuel lowering is absent.

---

## §D — Claims with NO executable proof

This deduplicated census accounts for 55 audit findings: **45 fixed**, **5 duplicate reports**,
**1 stale-note correction**, and **4 open** below. Treat 4 as a floor from that audit, not a claim
that no further gaps exist.

### Self-hosting and the capstones

@unproven **The 422 → 0 poison-census ratchet history is documentation only.** The narrative spine
of the self-hosting effort lives in a doc comment; only the terminal zero is asserted.

### Pins and anti-erosion

@unproven **The branch-protection configuration cannot be asserted from a test.** `solver` is now a
required check, so Z3 claims are enforced per-PR — but that requirement lives on GitHub. A test can
pin the check NAMES (claim 15); nothing in-repo can prove protection is still enabled.

### Lean and the proofs

@unproven **Self-declared unproven, accurately** — M6b scoped/resume-once effect handlers, full
origin/authority/slot/affine/balance derivation from the production CSIR-v8 semantic instructions,
AIR/Wasm adequacy for the abstract relational machine, and end-to-end hardware constant time.

@unproven **The production theorem begins at CSIR.** Rust source-to-CSIR projection, Lean native
code generation/runtime, Wasm emission, Wasmtime, scheduling, and hardware correspondence remain
trusted assumptions (SR-017); this specifically includes the Rust projector's security-only SSA
versioning, phi placement, and type-proved unreachable-edge facts. The linked verifier does not
prove those layers.

## §D2 — Known documentation drift (not claims; defects awaiting a fix)

<!-- Keep this section honest: if prose contradicts measurement today, it belongs here. -->


Distinct from the above: these are places where prose contradicts measurement TODAY. They are
listed for honesty and tracked as work, not counted as unproven claims.

**None open.** The single row here — retired capstone figures surviving in historical specs —
was re-measured on 2026-08-01 and found CLOSED: no capstone-scale byte figure exists anywhere in
`docs/**` or `README.md` outside §A's pins block above. (The drift ledger had itself drifted: the
row survived its own fix. That is the failure mode this file exists to catch, so it is recorded
rather than quietly deleted.)

## §E — Known holes in the emit surface

Superseding the prose table previously kept in an unmerged planning document. **Verdicts here are
measured by the fence registry, not asserted by prose** — that table's headline ("every item is
fail-closed, never wrong bytes") was **false as written** when first executed.

**Read this table as being about the SELF-HOSTED EMITTER, not about the language.** A **Poison**
row means the SIGIL-written emitter shadow refuses that construct and says so loudly. It does
**not** mean the construct is unsupported: every one of them parses, type-checks, lowers and runs
correctly under the production Rust compiler, and several are exercised by name elsewhere in this
file. The rows bound how far the self-hosted *projection* reaches — which is exactly the scope
§B claims for it.

| construct | measured verdict |
|---|---|
| 2+-binder match arm | **Poison** (fail-closed) |
| guarded match arm | **Poison** |
| wildcard-payload arm | **Poison** |
| string-literal pattern | **Poison** |
| range pattern | **Poison** *(was OracleRejects; fixture was malformed)* |
| closure capture | **Poison** *(was OracleRejects; fixture was malformed)* |
| recursive generic enum | **ByteEqual** *(was Diverge; fixed)* |
| u256 enum payload | **ByteEqual** *(prose said fenced — wrong)* |
| `?`, `Option::map` | **OracleRejects** — the fixture never reached the
  selfhost, so these rows are **unverified coverage**, not verified fences |

The exact unverified labels are pinned so one unverified row cannot silently replace another.

The range-pattern and closure rows moved on 2026-08-02, and how they moved is the point. Neither
was a fence and neither was a hole: both fixtures were simply written in the wrong language. The
range fixture used an exclusive `1..5`, which is not SIGIL grammar for a pattern (`..=` is), and
the closure fixture used Rust's `|x| …` spelling instead of SIGIL's `fn(..) -> T { .. }`. The
oracle rejected both on syntax, so neither row ever reached the shadow and neither measured
anything — while *reading* like evidence of an unsupported feature. Rewritten in SIGIL's own
grammar they reach the shadow and both measure Poison. A fixture that the oracle rejects is not a
finding about the implementation; it is a finding about the fixture.

---

*Authority: the Rust constants and the tests named above. If you are reading a number anywhere else
in this repository, assume it is stale until this file agrees with it.*
