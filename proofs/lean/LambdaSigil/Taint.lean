import LambdaSigil.Differential

/-!
# λ-SIGIL — Information-flow taint & noninterference (Milestones M-T0 … M-T3)

This module earns back the taint clause the SIGIL paper had to retract (§4.1: *"a well-typed program
never writes a value to a sink below its taint label"* — dropped 2026-07-03 because
`git grep -ic taint proofs/lean/**/*.lean = 0`; there was no mechanized backing).  We give the core a
real **information-flow taint layer** and prove a **noninterference / taint-safety** theorem that
mechanizes the invariant whose violation each of the two recently-fixed Rust soundness bugs was:

* **F002** — `declassify` must consume a *linear* declassification capability; a second declassify with
  one cap is ill-typed (`declassify_linear`; the two-cap control `declassify_twice_two_caps` shows
  linearity is the sole cause of the rejection).
* **F007** — a `@Secret` value must not reach a `@Public`-labelled sink without such a declassification
  (`taint_noninterference` + the `leak_ill_typed` witness in `TaintSafety.lean`).  Honest scope: the
  Rust F007 bug was specifically a *missing* taint sink at the actor `send`/`ask` message boundary;
  this calculus proves the *flow invariant* that fix restored (every sink checks `label ⊑ declared`),
  it does not model the actor boundary itself (see the scope note in `TaintSafety.lean`).
  The boundary *itself* — entry-point resolution, delivery of a payload at the callee's declared
  label, and the totality of the `send`/`ask`/`spawn` census — is modelled separately in
  `MessageBoundary.lean` (`MsgOk.checked` / `delivery_clean` / `requires_resolution`).

## Design decision — a self-contained taint calculus, not a retrofit of the capability core

Two honest options were on the table (the task flags this as the real modeling decision):

1. **Thread taint labels into the existing `Typing`/`WT`/`Term`/`Step`.**  This means new `Term`
   constructors, which break *every* exhaustive `match`/`induction e` in `Subst.lean`,
   `CapabilitySafety.lean`, `Preservation.lean`, `Substitution.lean` — i.e. it forces edits to every
   existing proof and risks the hard constraint *"`lake build` must stay green over the whole tree,
   do not weaken/delete any existing theorem"*.
2. **A parallel, self-contained taint calculus** that *structurally mirrors* `capability_safety`
   (a structural invariant, preserved under `step`, lifted to reachability, then concluded) and reuses
   the same `Typing`/`WT` **split idiom** (an affine judgment `TT` carrying a linear `Use` vector for
   ownership, and a usage-erased judgment `TW` carrying the labels for the safety proof).

We take **option 2**.  It keeps every existing theorem byte-identical (this file only *adds*), and it
is faithful: the Rust taint checker (`taint_check.rs`, `docs/specs/sh-security-checkers.md`) is itself a **first-order
intraprocedural forward dataflow pass** ("a single forward pass — no fixpoint, no solver"), so a
first-order taint calculus (labelled data, a linear declassify cap, implicit-flow control, and sinks)
is the honest object.  Higher-order functions are out of the taint fragment exactly as they are out of
the Rust pass.  Because the running programs are first-order and closed, **no substitution lemma is
needed** — the entire safety proof is a preservation induction over the step relation, exactly the
shape of `step_authBound`/`reachable_invariant`.

## The lattice

Per the paper's §4.1 we model the **three-level** lattice `@Public ⊑ @Internal ⊑ @Secret`
(`Label.pub ⊑ Label.int ⊑ Label.sec`).  The Rust checker's fourth `@SecretCT` level
(`docs/specs/secret-ct.md`) is the *constant-time* refinement — a timing-channel discipline, not the
value-flow clause the paper's theorem stated — and is out of scope here (documented in the note at the
end of `TaintSafety.lean`).

## What the theorem says

`taint_noninterference` : for every configuration reachable from a `TW`-well-typed program, the
**output trace is clean** — every `(delivered-label, sink-declared-label)` pair it recorded satisfies
`delivered ⊑ declared`.  Equivalently: *no reduction of a well-typed program ever lets a value reach a
sink whose declared label is below the value's label.*  This is precisely the paper's retracted clause.
`declassify_linear` supplies the companion half of the F002/F007 statement: an `@Secret → @Public`
downgrade is possible only by consuming a linear declassification capability, and two downgrades need
two distinct capabilities.
-/

namespace LambdaSigil

/-! ## M-T0 — the taint lattice `pub ⊑ int ⊑ sec` -/

/-- Taint labels: the paper's three-level lattice `@Public ⊑ @Internal ⊑ @Secret`. -/
inductive Label where
  | pub | int | sec
  deriving DecidableEq, Repr

namespace Label

/-- Numeric rank witnessing the linear order `pub(0) < int(1) < sec(2)`. -/
def rank : Label → Nat
  | pub => 0
  | int => 1
  | sec => 2

/-- The lattice order `ℓ₁ ⊑ ℓ₂`, defined by rank so it inherits `Nat`'s order lemmas. -/
instance : LE Label := ⟨fun a b => a.rank ≤ b.rank⟩

instance (a b : Label) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.rank ≤ b.rank))

/-- Least upper bound (join) of two labels. -/
def lub (a b : Label) : Label := if a.rank ≤ b.rank then b else a

@[simp] theorem le_refl (a : Label) : a ≤ a := Nat.le_refl _

theorem le_trans {a b c : Label} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := Nat.le_trans h₁ h₂

theorem le_lub_left (a b : Label) : a ≤ lub a b := by
  cases a <;> cases b <;> decide

theorem le_lub_right (a b : Label) : b ≤ lub a b := by
  cases a <;> cases b <;> decide

theorem lub_le {a b c : Label} (h₁ : a ≤ c) (h₂ : b ≤ c) : lub a b ≤ c := by
  revert h₁ h₂; cases a <;> cases b <;> cases c <;> decide

/-- Join is monotone in both arguments. -/
theorem lub_mono {a a' b b' : Label} (ha : a ≤ a') (hb : b ≤ b') : lub a b ≤ lub a' b' := by
  revert ha hb; cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem pub_le (a : Label) : pub ≤ a := by cases a <;> decide

end Label

/-! ## M-T0 — syntax of the taint calculus

A first-order calculus, in de Bruijn form (`var` occurs only in the F002 witness, where a linear
declassification capability sits in the context; running programs are closed and `var`-free). -/

/-- Taint "types": either a data value (whose label is tracked in the judgment) or a **linear**
    declassification capability (the `DeclassifyCT`/`Declassify` cap of `docs/specs/secret-ct.md`). -/
inductive TTy where
  | dat
  | dcapT
  deriving DecidableEq, Repr

/-- A capability type is **linear** (affine), a data type is unrestricted — mirrors `Ty.isLinear`. -/
def TTy.isLinear : TTy → Bool
  | .dcapT => true
  | .dat => false

/-- Terms of the taint calculus. -/
inductive Tm where
  | var : Nat → Tm
  /-- A runtime data value carrying an intrinsic taint label (a *source*: a `@Secret` input is
      `data sec`, a public constant is `data pub`). -/
  | data : Label → Tm
  /-- An FFI / host-call result.  Enters at `@Internal` (M-T2; `docs/specs/secret-ct.md` §3.5). -/
  | host : Tm
  /-- A runtime linear **declassification capability** value. -/
  | dcap : Tm
  /-- `ite g e₁ e₂` — a branch on `g`; the guard's label taints the branch results (implicit flow). -/
  | ite : Tm → Tm → Tm → Tm
  /-- `raised ℓ e` — a runtime marker (introduced by `ite` reduction): evaluate `e` under control
      label `ℓ`, stamping its resulting value with `ℓ`.  Not written in source programs. -/
  | raised : Label → Tm → Tm
  /-- `declassify v c` — lower `v`'s label to `@Public`, consuming the linear cap `c` (models the
      `@Secret → @Public` downgrade; F002). -/
  | declassify : Tm → Tm → Tm
  /-- `sink ℓ e` — deliver `e` to a sink whose declared label is `ℓ` (the output / write).  This is a
      **terminal delivery check** abstracting the *check* `taint_check` runs at its sinks (the
      `can_flow_to(declared)` test at a `let`-annotation / `return` / message-payload site); it does not
      model the *propagating* half of a Call/Send node (`lub(ret_taint, args)` flowing onward) — see
      the scope note in `TaintSafety.lean`. -/
  | sink : Label → Tm → Tm
  deriving DecidableEq, Repr

/-- A de Bruijn variable-type context: each binding carries its type and its intrinsic label. -/
abbrev TCtx := List (TTy × Label)

/-! ## M-T0 — the usage-erased taint judgment `TW` (carries the labels; used for safety)

`TW Γ pc e τ ℓ` reads: under context `Γ` and ambient **control label** `pc`, term `e` is a value of
type `τ` carrying taint label `ℓ`.

The `pc` is the taint of the enclosing control flow (M-T1): `ite`/`raised` raise it for their bodies,
and it is folded into the check at every `sink`, so a value emitted inside a `@Secret` branch is treated
as `@Secret`.  Labels themselves never depend on `pc` (only the sink *side-condition* does), which makes
`TW` **antitone in `pc`** (`TW.pc_antitone`) — the one structural lemma preservation needs. -/
inductive TW : TCtx → Label → Tm → TTy → Label → Prop where
  | var {Γ pc i τ ℓ0} :
      Γ[i]? = some (τ, ℓ0) → TW Γ pc (.var i) τ ℓ0
  | data {Γ pc ℓ0} :
      TW Γ pc (.data ℓ0) .dat ℓ0
  | host {Γ pc} :
      TW Γ pc .host .dat .int
  | dcapVal {Γ pc} :
      TW Γ pc .dcap .dcapT .pub
  /-- Implicit flow: both branches are typed under the raised control label `pc ⊔ ℓg`, and the guard's
      label `ℓg` is folded into the result — so a value escaping a `@Secret`-guarded `ite` is `@Secret`. -/
  | ite {Γ pc g ℓg e1 e2 τ ℓ1 ℓ2} :
      TW Γ pc g .dat ℓg →
      TW Γ (Label.lub pc ℓg) e1 τ ℓ1 →
      TW Γ (Label.lub pc ℓg) e2 τ ℓ2 →
      TW Γ pc (.ite g e1 e2) τ (Label.lub ℓg (Label.lub ℓ1 ℓ2))
  | raised {Γ pc ℓg e τ ℓ} :
      TW Γ (Label.lub pc ℓg) e τ ℓ →
      TW Γ pc (.raised ℓg e) τ (Label.lub ℓg ℓ)
  /-- `declassify` consumes a `dcapT` capability and yields a `@Public` value. -/
  | declassify {Γ pc v ℓv c ℓc} :
      TW Γ pc v .dat ℓv → TW Γ pc c .dcapT ℓc →
      TW Γ pc (.declassify v c) .dat .pub
  /-- The flow-safety check: the delivered value's label, joined with the control label, must be `⊑`
      the sink's declared label.  This is the clause the theorem globalizes. -/
  | sink {Γ pc ℓs e ℓ} :
      TW Γ pc e .dat ℓ → Label.lub pc ℓ ≤ ℓs →
      TW Γ pc (.sink ℓs e) .dat .pub

/-! ## M-T2 — the affine taint judgment `TT` (carries the linear `Use` vector; used for F002)

`TT Γ pc Uin e τ ℓ Uout` is `TW` plus a leftover/usage bit-vector, exactly as the core's `Typing`
relates to `WT`.  A linear declassification capability is a `dcapT` variable; using it consumes its
`Use` bit, so a *second* `declassify` with one cap has no derivation (F002 — `declassify_linear`). -/
abbrev TUse := List Bool

inductive TT : TCtx → Label → TUse → Tm → TTy → Label → TUse → Prop where
  | var_lin {Γ pc U i τ ℓ0} :
      Γ[i]? = some (τ, ℓ0) → τ.isLinear = true → U[i]? = some true →
      TT Γ pc U (.var i) τ ℓ0 (U.set i false)
  | var_unr {Γ pc U i τ ℓ0} :
      Γ[i]? = some (τ, ℓ0) → τ.isLinear = false →
      TT Γ pc U (.var i) τ ℓ0 U
  | data {Γ pc U ℓ0} :
      TT Γ pc U (.data ℓ0) .dat ℓ0 U
  | host {Γ pc U} :
      TT Γ pc U .host .dat .int U
  | dcapVal {Γ pc U} :
      TT Γ pc U .dcap .dcapT .pub U
  | ite {Γ pc U g ℓg Umid e1 τ ℓ1 U1 e2 ℓ2} :
      TT Γ pc U g .dat ℓg Umid →
      TT Γ (Label.lub pc ℓg) Umid e1 τ ℓ1 U1 →
      TT Γ (Label.lub pc ℓg) Umid e2 τ ℓ2 U1 →
      TT Γ pc U (.ite g e1 e2) τ (Label.lub ℓg (Label.lub ℓ1 ℓ2)) U1
  | declassify {Γ pc U v ℓv Umid c ℓc Uout} :
      TT Γ pc U v .dat ℓv Umid → TT Γ pc Umid c .dcapT ℓc Uout →
      TT Γ pc U (.declassify v c) .dat .pub Uout
  | sink {Γ pc U ℓs e ℓ Umid} :
      TT Γ pc U e .dat ℓ Umid → Label.lub pc ℓ ≤ ℓs →
      TT Γ pc U (.sink ℓs e) .dat .pub Umid

/-- Erasure: every affine-well-typed term is usage-erased-well-typed (drop the `Use` vector). -/
theorem TT.toTW {Γ pc U e τ ℓ U'} (h : TT Γ pc U e τ ℓ U') : TW Γ pc e τ ℓ := by
  induction h with
  | var_lin hΓ _ _ => exact TW.var hΓ
  | var_unr hΓ _ => exact TW.var hΓ
  | data => exact TW.data
  | host => exact TW.host
  | dcapVal => exact TW.dcapVal
  | ite _ _ _ ihg ih1 ih2 => exact TW.ite ihg ih1 ih2
  | declassify _ _ ih1 ih2 => exact TW.declassify ih1 ih2
  | sink _ hle ih => exact TW.sink ih hle

/-- `TW` is **antitone in the control label**: lowering `pc` preserves typing at the same label
    (labels never depend on `pc`; a lower `pc` only makes each `sink` side-condition easier).  This is
    the sole structural lemma preservation needs — for the `ite`-guard congruence, where reducing the
    guard lowers its label and hence the branches' ambient `pc`. -/
theorem TW.pc_antitone {Γ pc e τ ℓ} (h : TW Γ pc e τ ℓ) :
    ∀ {pc' : Label}, pc' ≤ pc → TW Γ pc' e τ ℓ := by
  induction h with
  | var hΓ => intro pc' _; exact TW.var hΓ
  | data => intro pc' _; exact TW.data
  | host => intro pc' _; exact TW.host
  | dcapVal => intro pc' _; exact TW.dcapVal
  | ite _ _ _ ihg ih1 ih2 =>
      intro pc' hpc
      exact TW.ite (ihg hpc) (ih1 (Label.lub_mono hpc (Label.le_refl _)))
        (ih2 (Label.lub_mono hpc (Label.le_refl _)))
  | raised _ ih =>
      intro pc' hpc
      exact TW.raised (ih (Label.lub_mono hpc (Label.le_refl _)))
  | declassify _ _ ih1 ih2 => intro pc' hpc; exact TW.declassify (ih1 hpc) (ih2 hpc)
  | sink _ hle ih =>
      intro pc' hpc
      exact TW.sink (ih hpc) (Label.le_trans (Label.lub_mono hpc (Label.le_refl _)) hle)

/-! ## M-T3 — instrumented operational semantics

A configuration is a term plus an **output trace**: the list of `(delivered-label, sink-declared-label)`
pairs emitted at sinks so far (the taint analogue of the capability `auth` trace).  Only `sinkRed`
grows the trace.  `ite` reduction introduces a `raised` marker that stamps the branch's result value
with the control label — the operational realization of implicit flow (M-T1). -/

/-- Runtime values: labelled data and declassification capabilities. -/
inductive TValue : Tm → Prop where
  | data {ℓ} : TValue (.data ℓ)
  | dcap : TValue .dcap

/-- Stamp a value with a control label (used when a `raised` marker resolves): a datum's label is
    joined with the control label; a capability carries no data label and is unchanged. -/
def tstamp (ℓg : Label) : Tm → Tm
  | .data ℓv => .data (Label.lub ℓg ℓv)
  | t => t

/-- A configuration: the term under evaluation together with the accumulated output trace. -/
structure TConfig where
  tm : Tm
  out : List (Label × Label)

/-- Small-step reduction. -/
inductive TStep : TConfig → TConfig → Prop where
  | hostRed {out} :
      TStep ⟨.host, out⟩ ⟨.data .int, out⟩
  -- ite: the guard reduces to a value, then a branch is taken under a `raised` control marker.
  | iteT {ℓg e1 e2 out} :
      TStep ⟨.ite (.data ℓg) e1 e2, out⟩ ⟨.raised ℓg e1, out⟩
  | iteF {ℓg e1 e2 out} :
      TStep ⟨.ite (.data ℓg) e1 e2, out⟩ ⟨.raised ℓg e2, out⟩
  | ite1 {g g' e1 e2 out out'} :
      TStep ⟨g, out⟩ ⟨g', out'⟩ →
      TStep ⟨.ite g e1 e2, out⟩ ⟨.ite g' e1 e2, out'⟩
  -- raised: when its body is a value, stamp the value with the control label and drop the marker.
  | raisedVal {ℓg v out} :
      TValue v → TStep ⟨.raised ℓg v, out⟩ ⟨tstamp ℓg v, out⟩
  | raised1 {ℓg e e' out out'} :
      TStep ⟨e, out⟩ ⟨e', out'⟩ →
      TStep ⟨.raised ℓg e, out⟩ ⟨.raised ℓg e', out'⟩
  -- declassify: consume the cap, lower the value to @Public.
  | declassRed {ℓv out} :
      TStep ⟨.declassify (.data ℓv) .dcap, out⟩ ⟨.data .pub, out⟩
  | declass1 {v v' c out out'} :
      TStep ⟨v, out⟩ ⟨v', out'⟩ →
      TStep ⟨.declassify v c, out⟩ ⟨.declassify v' c, out'⟩
  | declass2 {v c c' out out'} :
      TValue v → TStep ⟨c, out⟩ ⟨c', out'⟩ →
      TStep ⟨.declassify v c, out⟩ ⟨.declassify v c', out'⟩
  -- sink: deliver a value, recording the (delivered, declared) pair in the trace.
  | sinkRed {ℓs ℓv out} :
      TStep ⟨.sink ℓs (.data ℓv), out⟩ ⟨.data .pub, out ++ [(ℓv, ℓs)]⟩
  | sink1 {ℓs e e' out out'} :
      TStep ⟨e, out⟩ ⟨e', out'⟩ →
      TStep ⟨.sink ℓs e, out⟩ ⟨.sink ℓs e', out'⟩

/-- Reflexive-transitive closure: multi-step reduction. -/
abbrev TStepStar : TConfig → TConfig → Prop := Relation.ReflTransGen TStep

/-- The output trace is **clean** when every recorded flow respects the sink's declared label. -/
def Clean (l : List (Label × Label)) : Prop := ∀ p ∈ l, p.1 ≤ p.2

theorem Clean_nil : Clean [] := by intro p hp; cases hp

theorem Clean_append {l : List (Label × Label)} {p : Label × Label}
    (h : Clean l) (hp : p.1 ≤ p.2) : Clean (l ++ [p]) := by
  intro q hq
  rcases List.mem_append.mp hq with hq' | hq'
  · exact h q hq'
  · rw [List.mem_singleton.mp hq']; exact hp

/-! ## M-T3 — preservation, reachability, and the noninterference theorem -/

/-- **Preservation.**  A step preserves the type `τ` at a **non-increasing** label (`ℓ' ⊑ ℓ`), and it
    keeps the output trace clean: whatever a `sinkRed` emits is `⊑` the sink's declared label, because
    the sink redex was well-typed.  Generalized over `pc` (needed for the `raised`/`ite` congruences). -/
theorem TW.preservation : ∀ {c c' : TConfig}, TStep c c' →
    ∀ {pc τ ℓ}, TW [] pc c.tm τ ℓ →
      (∃ ℓ', ℓ' ≤ ℓ ∧ TW [] pc c'.tm τ ℓ') ∧ (Clean c.out → Clean c'.out) := by
  intro c c' hs
  induction hs with
  | hostRed =>
      intro pc τ ℓ h; cases h
      exact ⟨⟨.int, Label.le_refl _, TW.data⟩, id⟩
  | iteT =>
      intro pc τ ℓ h
      cases h with
      | ite hg h1 _ =>
          cases hg
          refine ⟨⟨_, ?_, TW.raised h1⟩, id⟩
          exact Label.lub_mono (Label.le_refl _) (Label.le_lub_left _ _)
  | iteF =>
      intro pc τ ℓ h
      cases h with
      | ite hg _ h2 =>
          cases hg
          refine ⟨⟨_, ?_, TW.raised h2⟩, id⟩
          exact Label.lub_mono (Label.le_refl _) (Label.le_lub_right _ _)
  | ite1 _ ih =>
      intro pc τ ℓ h
      cases h with
      | ite hg h1 h2 =>
          obtain ⟨⟨_, hle, hg'⟩, hclean⟩ := ih hg
          refine ⟨⟨_, ?_, TW.ite hg' (h1.pc_antitone ?_) (h2.pc_antitone ?_)⟩, hclean⟩
          · exact Label.lub_mono hle (Label.le_refl _)
          · exact Label.lub_mono (Label.le_refl _) hle
          · exact Label.lub_mono (Label.le_refl _) hle
  | raisedVal hv =>
      intro pc τ ℓ h
      cases h with
      | raised he =>
          cases hv with
          | data =>
              cases he
              refine ⟨⟨_, Label.le_refl _, ?_⟩, id⟩
              simpa only [tstamp] using TW.data
          | dcap =>
              cases he
              refine ⟨⟨_, Label.le_lub_right _ _, ?_⟩, id⟩
              simpa only [tstamp] using TW.dcapVal
  | raised1 _ ih =>
      intro pc τ ℓ h
      cases h with
      | raised he =>
          obtain ⟨⟨_, hle, he'⟩, hclean⟩ := ih he
          refine ⟨⟨_, ?_, TW.raised he'⟩, hclean⟩
          exact Label.lub_mono (Label.le_refl _) hle
  | declassRed =>
      intro pc τ ℓ h; cases h
      exact ⟨⟨.pub, Label.le_refl _, TW.data⟩, id⟩
  | declass1 _ ih =>
      intro pc τ ℓ h
      cases h with
      | declassify hv hc =>
          obtain ⟨⟨_, _, hv'⟩, hclean⟩ := ih hv
          exact ⟨⟨.pub, Label.le_refl _, TW.declassify hv' hc⟩, hclean⟩
  | declass2 _ _ ih =>
      intro pc τ ℓ h
      cases h with
      | declassify hv hc =>
          obtain ⟨⟨_, _, hc'⟩, hclean⟩ := ih hc
          exact ⟨⟨.pub, Label.le_refl _, TW.declassify hv hc'⟩, hclean⟩
  | sinkRed =>
      intro pc τ ℓ h
      cases h with
      | sink he hle =>
          cases he
          refine ⟨⟨.pub, Label.le_refl _, TW.data⟩, ?_⟩
          intro hc
          exact Clean_append hc (Label.le_trans (Label.le_lub_right _ _) hle)
  | sink1 _ ih =>
      intro pc τ ℓ h
      cases h with
      | sink he hle =>
          obtain ⟨⟨_, hle', he'⟩, hclean⟩ := ih he
          refine ⟨⟨.pub, Label.le_refl _, TW.sink he' ?_⟩, hclean⟩
          exact Label.le_trans (Label.lub_mono (Label.le_refl _) hle') hle

/-- Every configuration reachable from a well-typed program stays well-typed and keeps a clean trace. -/
theorem taint_reachable {e τ ℓ} (h : TW [] .pub e τ ℓ) :
    ∀ {c : TConfig}, TStepStar ⟨e, []⟩ c → Clean c.out ∧ ∃ ℓ', TW [] .pub c.tm τ ℓ' := by
  intro c hstar
  induction hstar with
  | refl => exact ⟨Clean_nil, ℓ, h⟩
  | tail _ hstep ih =>
      obtain ⟨hclean, ℓm, hm⟩ := ih
      obtain ⟨⟨ℓ', _, hm'⟩, hcl⟩ := TW.preservation hstep hm
      exact ⟨hcl hclean, ℓ', hm'⟩

/-- **Noninterference / taint safety (M-T3).**  No reduction of a well-typed program ever lets a value
    reach a sink whose declared label is below the value's label: every reachable configuration has a
    **clean** output trace.  This is exactly the SIGIL paper's §4.1 clause
    *"a well-typed program never writes a value to a sink below its taint label."* -/
theorem taint_noninterference {e τ ℓ} (h : TW [] .pub e τ ℓ) :
    ∀ c, TStepStar ⟨e, []⟩ c → Clean c.out :=
  fun _ hstar => (taint_reachable h hstar).1

/-- The same, stated from the affine judgment `TT` (a source program with its linear caps). -/
theorem taint_noninterference_affine {e τ ℓ U'} (h : TT [] .pub [] e τ ℓ U') :
    ∀ c, TStepStar ⟨e, []⟩ c → Clean c.out :=
  taint_noninterference h.toTW

/-! ## M-T2 — declassification is linear (F002)

The `@Secret → @Public` downgrade consumes a linear declassification capability.  Two downgrades
through **one** capability are ill-typed: nesting two `declassify`s on a single context cap `var 0`
forces the second use of `var 0` after the first consumed its `Use` bit, so `var_lin` cannot fire and
`var_unr` is unavailable (the cap is linear).  This is the F002 fix (`declassify_cap_not_consumed`) at
the level of the calculus, and it is the "every downgrade consumes a *distinct* capability" half of the
noninterference statement. -/
theorem declassify_linear :
    ¬ ∃ τ ℓ U', TT [(.dcapT, .pub)] .pub [true]
      (.declassify (.declassify (.data .sec) (.var 0)) (.var 0)) τ ℓ U' := by
  rintro ⟨τ, ℓ, U', h⟩
  cases h with
  | declassify hv hc =>
      cases hv with
      | declassify hv' hc' =>
          cases hv' with
          | data =>
              cases hc' with
              | var_lin _ _ _ =>
                  cases hc with
                  | var_lin _ _ hU => exact absurd hU (by decide)
                  | var_unr _ hlin => exact absurd hlin (by decide)
              | var_unr _ hlin => exact absurd hlin (by decide)

/-- The positive companion: a **single** declassification through the cap is well-typed (so the
    linear discipline is not vacuously rejecting) and consumes the cap's `Use` bit. -/
theorem declassify_once :
    TT [(.dcapT, .pub)] .pub [true]
      (.declassify (.data .sec) (.var 0)) .dat .pub [false] :=
  TT.declassify TT.data (TT.var_lin rfl rfl rfl)

/-- The **control experiment** for `declassify_linear`: the *same* double-declassify term, given **two
    distinct** capabilities (`var 0` and `var 1`), IS well-typed — consuming both `Use` bits.  So the
    single-cap rejection is caused *solely* by the consumed linear bit (F002's "each downgrade consumes
    a distinct capability"), not by any incidental ill-formedness of the nested term. -/
theorem declassify_twice_two_caps :
    TT [(.dcapT, .pub), (.dcapT, .pub)] .pub [true, true]
      (.declassify (.declassify (.data .sec) (.var 0)) (.var 1)) .dat .pub [false, false] :=
  TT.declassify (TT.declassify TT.data (TT.var_lin rfl rfl rfl)) (TT.var_lin rfl rfl rfl)

end LambdaSigil
