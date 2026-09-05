# λ-SIGIL — mechanized soundness of SIGIL's capability core (Lean 4)

A machine-checked formalization of core SIGIL calculi for capabilities, affine ownership,
effects, and taint. These theorems provide independent pressure on the design; they are not a
proof of the shipped compiler or runtime. The production/model boundary is tracked in
[`docs/SOUNDNESS_MATRIX.md`](../../docs/SOUNDNESS_MATRIX.md) and
[`docs/RESIDUAL_RISKS.md`](../../docs/RESIDUAL_RISKS.md).

Everything here is checked by Lean 4 with **zero `sorry`/`admit`**. The current axiom audit reports
only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) for every declared
theorem in [`axiom-targets.txt`](axiom-targets.txt). Its exact count is independently pinned in
the proof gate, Rust source census, and claims ledger, including the smaller public-export
inventory. These checks prevent the audited set from shrinking with the gate; the exact
three-axiom allowlist rejects every undeclared axiom.

## What is proven

| Theorem | Statement | File |
|---|---|---|
| **`type_soundness`** | no configuration reachable from a well-typed program is stuck — every reachable term is a value, a terminal raise (escaping effect), or steps (progress + preservation) | `LambdaSigil/Preservation.lean` |
| **`capability_safety`** | a well-typed program never exercises authority outside its static ceiling `m`: `∀` reachable `c`, `c.auth ⊆ m` | `LambdaSigil/CapabilitySafety.lean` |
| **`WT.progress`** | a well-typed closed term is a value, terminal raise, trap, or steps (a well-typed `exercise` is never stuck for lack of authority) | `LambdaSigil/Preservation.lean` |
| **`preservation`** | reduction preserves type and effect row (proved over a usage-erased judgment `WT` via the de Bruijn substitution lemma `WT.subst_lemma`) | `LambdaSigil/Preservation.lean` |
| **`Typing.consumed_stays_consumed`** / **`usage_monotone`** | a consumed linear capability can never be reused — affine ownership, no use-after-move / no duplication | `LambdaSigil/Substitution.lean` |
| **`restrict_cannot_amplify`** / **`mint_attenuation_bounded`** | attenuation only ever shrinks authority | `LambdaSigil/Authority.lean` |
| **`effect_safety`** | a well-typed program only lets effects in its declared row `ε` escape — any reachable terminal raise `perform E v` has `E ∈ ε`; handlers **discharge** the rest (abortive handlers, M6) | `LambdaSigil/Preservation.lean` |
| **`rc_r001_*` … `rc_r006_*`** (RingCheck) | the **ring discipline** — first Lean coverage of the R family: R006 (`trusted → outer`), R004 cross-ring rejection **with its symmetry pinned** (and a mutant twin encoding the *documentation's* wrong "callable from either ring" claim, so the doc-vs-code divergence is itself machine-checked), R001/R002 as arm-for-arm miniatures of `ring_check.rs`' cap-channel walkers — with **mutant twins that resurrect the historical walker-forgot-an-arm bug** (the tuple/fn smuggle miss) — and R003's extern ban **with its deliberate non-descent stated as a derivable theorem** (`rc_r003_nondescent_hole`), not a footnote | `LambdaSigil/RingCheck.lean` |
| **`RP.union_binding_sound`** / **`RP.union_binding_least`** (RowPoly) | the **row-polymorphism instantiation algebra** (Phase 4): SIGIL's `fn h<e>(f: Fn(i64)->i64 ! { e })` is polymorphism-by-monomorphization, and the only novel trusted logic is the call-site binding — certified here as the canonical LEAST solution (per-occurrence residual `a \ C` is sound and least; the union across occurrences satisfies every constraint and any solution contains it), with `RP.variable_free_is_exact` pinning that a concrete row on a generic formal is exactly the subset acceptance check. Non-vacuous by the two-occurrence witness pair (`rp_union_witness_accepts` / `rp_pure_caller_rejects`) and the mutant twin `RPbad.intersection_launders` — intersection binding fails its own occurrences, so the union choice is load-bearing | `LambdaSigil/RowPoly.lean` |
| **`DI.if_meet_lower_bound`** / **`DI.ret_requires_assigned`** | **definite initialization** of actor state (T126) — the *dual* of the taint join: a **must**-analysis whose `if` merge is **intersection**, so a field counts as initialized only when *every* path assigns it, and a path may `return` out of `init` only once everything required is assigned. Rejects both shapes the registry names — a one-sided `if c { self.f = v }` (`one_sided_assign_incomplete`) and the guarded early `return` (`early_return_skips_field`) — with the accepting twin `both_sided_assign_complete`, and the mutant twin `DIbad.one_sided_admitted` proving a **union** merge (the wrong direction) re-admits the uninitialized field | `LambdaSigil/DefiniteInit.lean` |
| **`TS.if_join_ub`** / **`TS.while_post_fixpoint`** | the **control-flow join** (task #252): at an `if` merge the environment is an upper bound of *both* branches, and a loop's environment is a post-fixpoint that is also an upper bound of the entry env (so the **zero-iteration** path cannot lower a label). Non-vacuous by a **mutant twin**: `d1_join_leak_ill_typed` rejects the program that actually shipped (`if c { x = secret } else { x = 0 }; sink @Public x`), while `TSbad.d1_leak_derivable` proves the *same* program **is** derivable once the merge is weakened to last-write-wins — so the lub-join premise is load-bearing. Phase 1 (`assign`/`seq`/`if`/`while`/`sink`); `break`/`continue`/n-ary `match` deferred | `LambdaSigil/TaintJoin.lean` |
| **`MsgOk.checked`** / **`delivery_clean`** / **`requires_resolution`** | the actor **message boundary** is a checked, observed, fail-closed sink: *every* boundary constructor (`send`/`ask`/`spawn` — a closed inductive, so the census is total) resolves its entry point and discharges `lub pc ℓ ⊑ declared`; the `(delivered, declared)` pair it records is `Clean`, extending the trace invariant *across* the boundary; and a message whose entry does not resolve has **no derivation** (a lookup miss is never a skip). Witnessed by the F007 family — `@Secret` payloads rejected on all three constructors, with an accepting twin | `LambdaSigil/MessageBoundary.lean` |
| **`Chk.effect_safety_declared`** / **`Chk.app_latent_bounded`** | effect rows as SIGIL *declares* them, not merely as λ-SIGIL synthesizes them: a checked program only lets effects in its **declared** row `δ` escape, and at any application the callee's **latent** row is contained in `δ` — so a closure built with latent `{E}` has *no derivation* when applied under a row omitting `E` (`hof_latent_leak_rejected`, with the accepting twin `hof_declared_accepts`). Closes the Lean side of the E001 *mechanism gap*; the Rust half followed — `Type::Fn` row-threading + IndirectCall discharge (PR #655), precise closure-row inference (PR #659), and the `! { E }` fn-type row syntax (PR #663) | `LambdaSigil/EffectRows.lean` |
| **`taint_safety`** (`taint_noninterference`) | no reduction of a well-typed program lets a value reach a sink below its taint label (`@Public ⊑ @Internal ⊑ @Secret`, pc-taint for implicit flows): every reachable trace is **clean**; and every `@Secret → @Public` downgrade consumes a **distinct linear** declassification capability (`declassify_linear`, F002) — earning back the paper's retracted §4.1 taint clause | `LambdaSigil/Taint.lean` + `TaintSafety.lean` |
| **`Combined.joint_security_of_verified`** | the executable version-8 verifier jointly implies the direct v8 semantic judgment plus the retained v6-derived taint/pc, capability-origin/BV32/slot-meet, quantitative-guard, and branch/loop-sensitive affine judgments | `LambdaSigil/CombinedKernel.lean` + `CombinedSecurity.lean` |
| **`Combined.v8_semantic_verifier_sound_and_complete`** | v8 structure, declarative metadata, semantic least taint/pc, contracts, policy classes (including assignment/return/call/state-result T030), release/guard rules, and local capability shapes are equivalent to `V8SecurityJudgment` | `LambdaSigil/CombinedSecurity.lean` |
| **`Combined.V9.OccurrenceKernelSecurity.v9_occurrence_verifier_sound_and_complete`** | the production model-9 executable decision is equivalent to its unary occurrence judgment: exact retained-v8 acceptance, verifier-derived least semantic labels, ranked local occurrence transfer, closed invocation propagation, activation ownership layout, and instruction-indexed destination/FFI/actor/state/root boundary ceilings | `LambdaSigil/V9OccurrenceKernel.lean` + `V9OccurrenceKernelSecurity.lean` |
| **`Combined.RawClaimSurface.secretCT_delimited_release_trace_equality`** | the exact linked verifier supplies the decoded static premise for the unsanitized machine; equal release prefixes (exact site, stage, and payload) imply equal public control, address, boundary, allocation, cost, trap, and output traces for every equal-length finite prefix | `LambdaSigil/RawClaimSurface.lean` + `SemanticSecurity.lean` |
| **`Combined.V9.PublicBisimulationSecurity.raw_public_weak_bisimulation_of_v9_verified`** / **`Combined.RawClaimSurface.public_delimited_release_noninterference`** | production v9 acceptance yields a verifier-derived finite weak alignment across independently sized successful raw executions with equal complete release traces; the pinned corollary concludes equality of the full Public projection and ordered Public output/boundary trace, including calls, closures, recursive/private regions, per-site external inputs, genuine returns, and multiple releases | `LambdaSigil/PublicBisimulationSecurity.lean` + `RawClaimSurface.lean` |
| **`Combined.canonical_semantic_envelope_accepts`** / semantic-envelope mutants | the v8 semantic manifest, nested owner order, functions, SSA values, nonempty terminated blocks, instructions, contiguous operands, fixed arities and operand order, destinations, function references, same-function CFG targets, and canonical policy attachment are checked by the linked kernel; the Rust/Lean opcode tables are parity-fenced | `LambdaSigil/CombinedSecurity.lean` + linked-native Rust mutants |
| **`Combined.graphLabels_least`** / **`Combined.graph_verifier_sound_and_complete`** | graph acceptance includes an executable post-fixpoint backstop, and the linked worklist result is pointwise below every algorithm-independent seed/edge solution; cyclic, diamond, duplicate-edge, maximum-height, under-fuel, and missing-edge mutants make both directions load-bearing | `LambdaSigil/CombinedSecurity.lean` |
| **`Combined.capability_verifier_sound_and_complete`** | capability acceptance is equivalent to the ordered derivation judgment over Lean-produced origin, attenuation, control-flow meet, slot-meet, sink, and release states | `LambdaSigil/CombinedSecurity.lean` |
| **`Combined.path_affine_verifier_sound_and_complete`** | explicit `if`/`match` alternatives are checked from one consumption snapshot and joined over only fallthrough arms; loop-head origins cannot be consumed on repeatable edges, and `break` consumption joins into the exit | `LambdaSigil/CombinedSecurity.lean` |
| **`Combined.difference_classifier_sound_and_complete_of_nodes`** | canonical, quantitatively well-formed v6 records give a sound and complete classifier for the emitted literal-RHS, zero-anchored difference fragment; unsupported cross-cell records fail closed | `LambdaSigil/CombinedSecurity.lean` |
| **`Combined.verifier_sound_and_complete`** | executable acceptance is equivalent to the combined declarative CSIR judgment: local obligations, duplicate-free legacy origins, verifier-derived capability states, branch/loop-sensitive affine consumption, and the verifier-derived taint graph | `LambdaSigil/CombinedSecurity.lean` |
| **`Semantic.state_well_formed_preserved`** | every raw semantic constructor preserves the program-derived well-formed-state relation | `LambdaSigil/SemanticSecurity.lean` |

`LambdaSigil/Safety.lean` instantiates `type_soundness`, `capability_safety`, and `progress` on a
concrete mint-then-exercise program (non-vacuous), and proves `stuck_is_inhabited` — a genuinely
stuck ill-typed term — so `type_soundness` is not vacuously true.

The Combined theorem is over the same `verifyProgram` compiled into the production native bridge;
the older theorems remain calculus-level evidence. Version 8 requires a canonical semantic suffix
projected from post-desugar AIR and checks its manifest, functions, value declarations, blocks,
instructions, operands, references, destinations, and arities. The retained v6 obligation layer derives taint and pc-taint from
bounded seeds and monotone edges inside Lean, including cyclic loop back-edges. It also derives
capability legitimacy, BV32 restriction/split/draw attenuation, control-flow authority meet, slot
authority meet, sinks, and release kinds from canonical origin/derivation records. It also derives
fallthrough-aware affine consumption over explicit `if`/`match` alternatives, conservative
repeatable-edge checks at loop heads, and `break`-exit joins. It also checks signed quantitative
amounts, mandatory guest/host guards, and the supported zero-anchored difference fragment. The
semantic instruction stream directly derives taint/pc-taint, contracts, policy observations,
assignment/return/call/state-result CT-source rules, release/guard rules, and local capability
shapes. Complete origin/authority/slot-meet, affine CFG,
and quantitative balance/difference judgments still come from the v6 obligation records during the
mandatory dual-gate phase. The decoded raw semantic machine has a constructor-complete
well-formedness-preservation theorem and a production-linked static-safety-to-SecretCT
lockstep/delimited-release chain. Its transitive theorem dependencies are audited against sanitized
and assumed-policy symbols with a planted failing self-test. The structured-region Public gate
rejects non-Public arms that can successfully `output`/`halt` before their declared continuation,
with a legacy-accepted mutant and linked-native site check. Unreachable AIR is a raw trap, and a
second decoded invariant plus linked mutant rejects a whole-machine halt in a callee reached below
non-Public caller pc. The production v9 Public proof derives a finite alignment by strong induction
over two independent exact successful-execution lengths. Its constructor-complete dispatcher
combines matching raw steps with independently long private controller and invocation segments,
per-site external-input isolation, genuine call/closure/recursive returns, and repeated exact
release synchronization. The pinned final theorem equates the complete Public projection and the
ordered Public output/boundary trace; it does not assert ordinary-Secret timing, control, address,
allocation, or cost equality. The Public and SecretCT production claim dependency closures are
both checker-fingerprinted and audited without an assumed relational policy.
These results use a
security-event abstraction rather than an AIR/Wasm adequacy proof.
None proves Rust source-to-CSIR projection, Lean native generation/runtime, Wasm emission,
Wasmtime, scheduling, or hardware timing. Authority/affine/quantity operational closure is also
still outside the Public theorem, every legacy gate remains mandatory, and the v9 tagged-release
evidence is not retirement-eligible.

## The calculus

`λ-SIGIL` is the leftover/usage typing judgment of the SIGIL paper (§3.1),
`Γ ; Uin ⊢ e : τ ! ε @ m ⊣ Uout`, mechanized faithfully to the implementation:

* **Authority-indexed capabilities** `cap κ k` (the paper's `Cap[k]`); `restrict k e` attenuates to
  `k₀ ∩ k`; `mint κ tok` is gated by an in-scope `mintAuth κ` token (the `&Admin`/T273 gate) and
  yields exactly `fullMask κ`.  Caps are values created only by `mint`/`restrict` — there is no
  cap-forging term (C001 holds by construction).
* **Affine ownership** via a usage bit-vector threaded through the typing rules (`ownership.rs`,
  O001): a consumed linear variable is no longer `available`, so it cannot be used again.
* **Instrumented small-step semantics** whose configuration carries an authority/effect *trace*;
  `exercise a (capVal κ k)` (with `a ∈ k`) emits authority, and the **full-mask sink** `sink req e`
  (with `req ⊆ k` — the `sinkOk`/C003 check abstracting the Call/Spawn/Send/Return sinks) emits the
  required set `req`.  Both are bounded by the ceiling `m` (capability safety).

Faithfulness anchors to the Rust implementation are documented inline (e.g.
`crates/sigil-compiler/src/registries.rs`, `air.rs`, `ownership.rs`, `air_capability_v2`).

## Design note: two judgments

The affine `Typing` judgment (with a leftover/usage vector) carries the linearity discipline and is
the source of the **ownership** theorems. **Type soundness** is proved over a usage-erased judgment
`WT` (`Typing ⇒ WT` by erasure), because the de Bruijn substitution lemma then needs no usage
bookkeeping — `grind` does not close the `set`/`insertIdx` commutation that exact-usage weakening
would require, whereas `WT` eliminates it. Ownership stays on `Typing`; capability safety stays on
the structural `AuthBound` invariant; nothing is lost.

## Effect handlers (M6)

`perform E e` / `handle E h body` (abortive — SIGIL's no-multishot subset) are modeled by
**bubbling**: a raise `perform E v` propagates outward through elimination frames until an enclosing
`handle E` **catches** it (`→ app h v`, discharging `E`) or it reaches the top as a terminal raise.
The `perform` rule gives result type *any* `τ` (SIGIL `Type::Never`/bottom), so a raise re-types at
each frame and preservation goes through. `effect_safety` then falls out of preservation (a reachable
raise is `WT`-typed at a row `⊆ ε`, and the `perform` rule forces `E ∈` that row). Scoped/resume-once
handlers (which need evaluation contexts) are deferred to M6b.

## Differential cross-check (M7)

`LambdaSigil/Differential.lean` pairs each headline SIGIL violation pattern with a λ-SIGIL **verdict
obligation** (accept = a `Typing` derivation; reject = non-derivability or `Stuck`), and the Rust
tests `crates/sigil-runtime/tests/lambda_sigil_differential.rs` (rust lane) +
`crates/sigil-compiler/tests/lambda_sigil_c003.rs` (solver lane) assert the paired `.sigil` fixture
gets the corresponding `sigil_check` verdict. `LSD-…` ids tie the two halves through an explicit
classification of shared and intentionally one-sided obligations; the relation is not 1:1.

To make **C003** a *literal* ⇔ rather than a representative analogy, the calculus gains a real
full-mask **`sink`** rule (`sink req e`, `req ⊆ k`); `progress` / `preservation` / `capability_safety`
/ `effect_safety` / `type_soundness` are all re-proven over it.  Correspondence kinds are labelled
honestly: O001 / T273 / C003 are clean rejects (O001 = the capability sub-case of affine ownership;
T273 = the `&Admin` *type* gate), while **C001** (by construction — no forging term, front-end-rejected
in SIGIL), **E001** (mechanism gap — row *synthesis* + `effect_safety`, not annotation-checking), and
**T272** (out of model — no `mintable_by` policy layer) are documented, not over-claimed.

The older λ-SIGIL differential still has no automatic surface bridge. Combined CSIR separately has
a narrow native FFI bridge: Rust encodes canonical bytes and calls the exported Lean verifier. The
Rust half of the older differential
runs in the `test` and `solver` jobs; the Lean build and no-sorry/axiom gate run in the required Lean
workflow. The linked production verifier builds semantic cross-reference and taint-adjacency
indexes once per program. Required Rust CI also compiles the roughly quarter-million-record self-host
trio through that exact native verifier under the corpus validator's fixed five-second budget;
source canaries reject the measured whole-program-rescan regressions. This is a bounded regression
guard, not an asymptotic theorem.

The Rust projection assigns security-only SSA versions to reassigned AIR names and emits
predecessor-compressed phi instructions at reachable joins. The Lean semantic graph restores
structured pc-taint at branch/loop post-dominators and flat-match wrapper exits, never at an inner
arm-test else/catch-all target; paired witnesses show that retaining the secret pc after a true
merge falsely rejects a safe continuation, while a linked mutant shows that restoring at a local
match-test target admits an early successful escape. Type-proved unreachable exhaustive-match
fallthroughs are omitted from the semantic predecessor relation. Those projection decisions remain
inside the source-to-CSIR trusted assumption; the Lean verifier validates and reasons about the
canonical records it receives rather than proving that Rust selected the right versions or edges.

`csir-v8-constructor-manifest.tsv` is the mechanically checked numeric inventory for every v8
record, instruction, and policy class. The integration-release evidence state lives in
`docs/release-evidence/csir-v8-dual-gate.toml`; it intentionally records constructor evidence and
tagged platform/performance results as incomplete until real immutable release measurements exist.
CI forbids that file from claiming retirement and pins all compatibility gates in the meantime.

## Not yet proven (next milestones)

* **M6b** — scoped / resume-once effect handlers (need evaluation contexts).
* Complete constructor-level capability origin/authority/slot-meet, affine CFG, and quantitative
  balance derivation from the production v8 semantic records, followed by the tagged dual-gate
  evidence release and later removal of the duplicate v6 obligation projection.
* A mechanized Rust source-to-CSIR correspondence and native-code correctness result.
* Wasm/runtime/scheduling/microarchitectural correspondence for `SecretCT`.

## Build & verify

```sh
cd proofs/lean
lake exe cache get      # fetch prebuilt Mathlib oleans (first time)
lake build              # checks the whole development
bash scripts/check-no-sorry.sh   # CI gate: no sorry/admit, only standard axioms
```

Toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.32.0-rc1`); Mathlib is pinned in
`lakefile.toml`.
