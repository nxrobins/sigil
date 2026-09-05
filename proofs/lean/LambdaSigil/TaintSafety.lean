import LambdaSigil.Taint

/-!
# λ-SIGIL — Taint safety: non-vacuity witnesses and the M-T4 differential

This module makes the noninterference result of `Taint.lean` **bite**:

* **Non-vacuity (mandatory).**  Two concrete programs, mirroring `demoProg` / `stuck_is_inhabited`:
  (a) a `@Secret → @Public` leak that is **ill-typed** (the F007 shape) — and which, *if run anyway*,
      produces a **dirty** trace, so the type system (not the operational semantics) is the enforcement;
  (b) a well-typed program that **legally declassifies once** through a consumed capability — it types,
      it reduces to a value, and `taint_noninterference` certifies its trace is clean.
  Without (b) the theorem could be vacuously true (holding only because no program reaches a sink);
  (b) exhibits a program that *does* reach a sink with a clean flow.

* **M-T4 differential.**  A `LSD`-style correspondence table pairing each headline SIGIL taint verdict
  with a λ-SIGIL obligation (accept = an inhabited `TW`/`TT` derivation; reject = non-derivability),
  extending `Differential.lean`'s bridge onto the taint axis the paper flagged as open.

## Correction to the task's stated Rust code (honest scope note)

The task named "**T272**" as the Rust code for the M-T4 taint fixture.  Verified against the source
(`crates/sigil-compiler/src/diagnostics/codes.rs:1037`, `crates/sigil-compiler/tests/cap_mint.rs`),
**T272 is a *mint-policy* code** — "`mint` of a non-mintable / undeclared cap type (fail-closed)" —
and has nothing to do with taint.  The genuine taint-downgrade code (the F007 shape: a `@Secret` value
reaching a `@Public` sink) is **T001** ("taint DOWNGRADE without declassify", `taint_check.rs:168/325`,
`docs/specs/sh-security-checkers.md`), and the declassify-capability-reuse fix (F002) surfaces as the ownership code
**O001** (use-after-move of the linear cap).  This differential is therefore anchored to **T001** (the
value-flow reject) and **O001** (the linear-cap reject), the codes that actually correspond to F007/F002.
-/

namespace LambdaSigil

/-! ## Non-vacuity (a) — the `@Secret → @Public` leak (F007) -/

/-- `@Secret → @Public` leak `sink pub (data sec)`.  **Ill-typed**: the `sink` rule demands
    `pub ⊔ sec ⊑ pub`, i.e. `sec ⊑ pub`, which is false — there is no `TW` derivation. -/
theorem leak_ill_typed :
    ¬ ∃ τ ℓ, TW [] .pub (.sink .pub (.data .sec)) τ ℓ := by
  rintro ⟨τ, ℓ, h⟩
  cases h with
  | sink he hle => cases he; exact absurd hle (by decide)

/-- The same leak *steps* (the operational semantics does not block it) — `sink` delivers the secret
    to the public sink, recording the flow `(sec, pub)`. -/
theorem leak_steps :
    TStep ⟨.sink .pub (.data .sec), []⟩ ⟨.data .pub, [(.sec, .pub)]⟩ :=
  TStep.sinkRed

/-- …and that recorded trace is **dirty** (`sec ⋢ pub`).  So the leak is prevented *by typing*, not by
    the reduction relation — exactly why `taint_noninterference` quantifies over well-typed programs. -/
theorem leak_trace_dirty : ¬ Clean [((.sec : Label), (.pub : Label))] := by
  intro h
  exact absurd (h (.sec, .pub) (by simp)) (by decide)

/-! ## Non-vacuity (b) — a legal single declassification (types, runs, clean trace) -/

/-- A closed program that laundries a secret through a declassification capability and delivers it to a
    public sink: `sink pub (declassify (data sec) dcap)`.  **Well-typed** (`declassify` lowers the label
    to `@Public`, so the sink accepts it). -/
theorem declassify_leak_typed :
    TW [] .pub (.sink .pub (.declassify (.data .sec) .dcap)) .dat .pub :=
  TW.sink (TW.declassify TW.data TW.dcapVal) (by decide)

/-- It actually reaches the sink and emits the flow `(pub, pub)` — so the safety theorem is applied to a
    program that genuinely writes to a sink (not vacuously). -/
theorem declassify_leak_runs :
    TStepStar ⟨.sink .pub (.declassify (.data .sec) .dcap), []⟩ ⟨.data .pub, [(.pub, .pub)]⟩ :=
  Relation.ReflTransGen.head (TStep.sink1 TStep.declassRed)
    (Relation.ReflTransGen.head TStep.sinkRed Relation.ReflTransGen.refl)

/-- **Non-vacuity of `taint_noninterference`.**  Every configuration reachable from the legal
    declassification has a clean trace — in particular the emitted `(pub, pub)` flow is clean. -/
theorem declassify_leak_safe :
    ∀ c, TStepStar ⟨.sink .pub (.declassify (.data .sec) .dcap), []⟩ c → Clean c.out :=
  taint_noninterference declassify_leak_typed

/-- The witnessed clean flow, obtained from the theorem (not by hand): the reachable `(pub, pub)` is
    clean.  This is a *positive* instance — the theorem is not vacuous. -/
theorem declassify_leak_flow_clean : Clean [((.pub : Label), (.pub : Label))] :=
  declassify_leak_safe _ declassify_leak_runs

/-! ### The trace machinery is exercised across the WHOLE lattice (not just `(pub, pub)`) -/

/-- A well-typed program delivering an FFI `@Internal` result to a `@Secret` sink types (`int ⊑ sec`). -/
theorem demo_cross_label_typed : TW [] .pub (.sink .sec .host) .dat .pub :=
  TW.sink TW.host (by decide)

/-- …it emits the genuine cross-label flow `(int, sec)` — the trace is not trivially `(pub, pub)`. -/
theorem demo_cross_label_runs :
    TStepStar ⟨.sink .sec .host, []⟩ ⟨.data .pub, [(.int, .sec)]⟩ :=
  Relation.ReflTransGen.head (TStep.sink1 TStep.hostRed)
    (Relation.ReflTransGen.head TStep.sinkRed Relation.ReflTransGen.refl)

/-- …and `taint_noninterference` certifies that cross-label flow is clean (`int ⊑ sec`). -/
theorem demo_cross_label_flow_clean : Clean [((.int : Label), (.sec : Label))] :=
  taint_noninterference demo_cross_label_typed _ demo_cross_label_runs

/-- The implicit-flow leak of `lsd_t001_implicit_reject`, *if executed*, produces the dirty flow
    `(sec, pub)`: the value escaping the `@Secret`-guarded `ite` is stamped `@Secret` by the `raised`
    marker before reaching the `@Public` sink.  The program is ill-typed (correctly rejected), so
    `taint_noninterference` never reaches this trace — this witness shows the implicit leak is real, and
    that typing (not the reduction relation) is what prevents it. -/
theorem implicit_leak_steps_dirty :
    TStepStar ⟨.sink .pub (.ite (.data .sec) (.data .pub) (.data .pub)), []⟩
      ⟨.data .pub, [(.sec, .pub)]⟩ :=
  Relation.ReflTransGen.head (TStep.sink1 TStep.iteT)
    (Relation.ReflTransGen.head (TStep.sink1 (TStep.raisedVal TValue.data))
      (Relation.ReflTransGen.head TStep.sinkRed Relation.ReflTransGen.refl))

/-! ## M-T4 — the taint differential corpus

| ID | pattern | SIGIL code | kind | λ-SIGIL obligation |
|---|---|---|---|---|
| `LSD-T001-direct`   | `@Secret` value to a `@Public` sink | T001 | clean reject | `lsd_t001_direct_reject` (= `leak_ill_typed`) + `lsd_t001_direct_dirty` (operational) |
| `LSD-T001-implicit` | `@Public` sink fed by a `@Secret`-guarded `ite` (implicit flow) | T001 | clean reject | `lsd_t001_implicit_reject` |
| `LSD-T001-host`     | FFI `@Internal` result to a `@Public` sink | T001 | clean reject | `lsd_t001_host_reject` |
| `LSD-O001-declass`  | one declassify cap reused for two downgrades | O001 | clean reject (linear cap) | `lsd_o001_declass_reject` (= `declassify_linear`) |
| `LSD-ACC-declass`   | `@Secret → @Public` via one consumed declassify cap | — | clean accept | `lsd_acc_declass` (= `declassify_leak_typed`) |
| `LSD-ACC-once`      | a single declassify consumes exactly one cap bit | — | clean accept | `lsd_acc_declass_once` (= `declassify_once`) |
| `LSD-ACC-host`      | FFI `@Internal` result to an `@Internal` sink | — | clean accept | `lsd_acc_host` |
| `LSD-ACC-implicit`  | `@Public`-guarded `ite` result to a `@Public` sink | — | clean accept | `lsd_acc_implicit` |

`LSD-T001-*` are the F007 rejects; `LSD-O001-declass` is the F002 reject; the `LSD-ACC-*` twins prove
the analysis is not vacuously rejecting.  On the Rust side these correspond to `taint_check`'s T001
(value/implicit downgrade) and the ownership O001 (linear declassify cap), per the scope note above.

**Bridge status (honest).**  This is the **Lean half** of the taint differential, in the exact shape of
`Differential.lean`'s M7 corpus.  The Rust half now exists:
`crates/sigil-runtime/tests/lambda_sigil_taint_differential.rs` pairs a `.sigil` fixture to every id in
the table above and asserts SIGIL's verdict on the {T001, O001} surface — each reject fixture emits
exactly its headline code, each accept twin emits none.  Its
`lean_taint_obligation_ids_match_the_rust_half` reads THIS file and requires the two id sets to be
**equal in both directions**, so adding a row above without a paired fixture fails the Rust build by
name, and a Rust fixture claiming an unproved correspondence fails it too.  Unlike the M7 `LSD-…` ids,
whose Rust and Lean sets are intentionally not 1:1, the taint sets are exactly equal.

What is bridged is the **verdict**, not the mechanism: this calculus is first-order (no lam/let/call),
while the Rust pass propagates interprocedurally through signature tables, and the shared scope is
sink-safety — the terminal check.  Note that the prose above refers to id families as `LSD-T001-*` and
`LSD-ACC-*`; the Rust extractor skips a run followed by `*` so those globs do not become phantom ids. -/

/-! ### Reject obligations -/

/-- `LSD-T001-direct` — direct `@Secret → @Public` flow is not derivable. -/
theorem lsd_t001_direct_reject :
    ¬ ∃ τ ℓ, TW [] .pub (.sink .pub (.data .sec)) τ ℓ := leak_ill_typed

/-- `LSD-T001-direct` (operational) — the flow the reject prevents is a genuine leak (`sec ⋢ pub`). -/
theorem lsd_t001_direct_dirty : ¬ Clean [((.sec : Label), (.pub : Label))] := leak_trace_dirty

/-- `LSD-T001-implicit` — **implicit flow**.  A value escaping a `@Secret`-guarded `ite` carries the
    guard's label, so delivering it to a `@Public` sink is not derivable (the `ite` result label is
    `⊒ @Secret`, and the sink demands `⊑ @Public`). -/
theorem lsd_t001_implicit_reject :
    ¬ ∃ τ ℓ, TW [] .pub (.sink .pub (.ite (.data .sec) (.data .pub) (.data .pub))) τ ℓ := by
  rintro ⟨τ, ℓ, h⟩
  cases h with
  | sink he hle =>
      cases he with
      | ite hg h1 h2 =>
          cases hg; cases h1; cases h2
          exact absurd hle (by decide)

/-- `LSD-T001-host` — an FFI/host result (`@Internal`) cannot reach a `@Public` sink (M-T2). -/
theorem lsd_t001_host_reject :
    ¬ ∃ τ ℓ, TW [] .pub (.sink .pub .host) τ ℓ := by
  rintro ⟨τ, ℓ, h⟩
  cases h with
  | sink he hle => cases he; exact absurd hle (by decide)

/-- `LSD-O001-declass` — **declassify-cap reuse** (F002).  Two downgrades cannot share one linear
    capability. -/
theorem lsd_o001_declass_reject :
    ¬ ∃ τ ℓ U', TT [(.dcapT, .pub)] .pub [true]
      (.declassify (.declassify (.data .sec) (.var 0)) (.var 0)) τ ℓ U' := declassify_linear

/-! ### Accept obligations -/

/-- `LSD-ACC-declass` — the legal `@Secret → @Public` downgrade through a consumed cap types. -/
theorem lsd_acc_declass :
    TW [] .pub (.sink .pub (.declassify (.data .sec) .dcap)) .dat .pub := declassify_leak_typed

/-- `LSD-ACC-once` — a single declassify consumes exactly one capability bit (`[true] ↦ [false]`). -/
theorem lsd_acc_declass_once :
    TT [(.dcapT, .pub)] .pub [true] (.declassify (.data .sec) (.var 0)) .dat .pub [false] :=
  declassify_once

/-- `LSD-ACC-host` — an FFI/host result may reach an `@Internal` sink (its own level). -/
theorem lsd_acc_host : TW [] .pub (.sink .int .host) .dat .pub :=
  TW.sink TW.host (by decide)

/-- `LSD-ACC-implicit` — a `@Public`-guarded `ite` result may reach a `@Public` sink (no leak). -/
theorem lsd_acc_implicit :
    TW [] .pub (.sink .pub (.ite (.data .pub) (.data .pub) (.data .pub))) .dat .pub :=
  TW.sink (TW.ite TW.data TW.data TW.data) (by decide)

/-! ## Scope note — what the theorem does and does not cover

**Covers.**  `taint_noninterference` is exactly the SIGIL paper's §4.1 clause, mechanized: for a
well-typed program, *no reduction ever writes a value to a sink below its taint label*.  It bites on:

* **direct flows** — a `@Secret` datum reaching a `@Public` sink (F007) is ill-typed (`leak_ill_typed`);
* **implicit flows** — a value escaping a `@Secret`-guarded branch carries the guard's label, and a
  control-dependent sink is typed under the raised `pc`, so both leak shapes are rejected
  (`lsd_t001_implicit_reject`; the `pc`-taint of `ite`/`raised`, M-T1);
* **FFI provenance** — host results enter at `@Internal` and cannot silently reach `@Public` (M-T2);
* **declassification discipline** — an `@Secret → @Public` downgrade is possible *only* by consuming a
  **linear** declassification capability, and two downgrades need two distinct capabilities
  (`declassify_linear`, F002); a legal single declassification types and runs to a clean trace
  (`declassify_leak_safe`).

**Does not cover (honest boundaries).**

1. **Three-level lattice only.**  We model the paper's §4.1 lattice `@Public ⊑ @Internal ⊑ @Secret`.
   The Rust checker's fourth `@SecretCT` level (`docs/specs/secret-ct.md`) is a *constant-time / timing*
   discipline (reject-the-branch, not track-the-value); it is a different property (an operational
   restriction, not a value-flow lattice clause) and is out of this theorem's scope.
2. **First-order calculus — smaller than the Rust pass's first-order surface.**  The fragment is
   labelled data, a linear declassify cap, implicit-flow control (`ite`/`raised`), and terminal sinks.
   The Rust checker is likewise first-order per function ("a single forward pass, no fixpoint" —
   `docs/specs/sh-security-checkers.md`), but it additionally *propagates* taint interprocedurally through
   signature tables (a Call's `lub(ret_taint, args)`, the send/ask payload-vs-handler-param check that
   was the actual F007 fix site) and through `let`-rebinding.  This calculus has **no**
   call/`let`/sequencing constructs at all: its `sink` models only the *check* those sites run
   (`label ⊑ declared`), not the onward propagation.  Higher-order closures/captures (E4/CT012) are
   likewise out.  The theorem is exact over its fragment; the fragment is a strict core of the
   checker's surface.
3. **Flow-safety, not 2-run indistinguishability.**  The theorem is the single-run *taint-safety* /
   flow-safety property the paper stated ("never writes a value to a sink below its taint label").  It is
   not the relational "two runs differing only in secrets produce identical public outputs" formulation
   that the word *noninterference* sometimes denotes; with declassification present that would be
   *relaxed* noninterference (quantified over declassified values) and is the natural next milestone.
   The single-run flow-safety property is precisely the paper's clause, and it is the invariant that
   F002's fix (the linear cap consumption) and F007's fix (the taint sink added at the message
   boundary) each restored — the bugs themselves were violations of it at specific compiler sites.

With this module green and axiom-clean, the paper's §4.1 taint clause and a `taint_safety` property-table
row (alongside `capability_safety`) can be restored — earned by a mechanized proof rather than asserted.
-/

end LambdaSigil
