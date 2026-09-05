import LambdaSigil.Subst
import LambdaSigil.Authority
import Mathlib.Logic.Relation

/-!
# λ-SIGIL — Instrumented operational semantics (Milestone M2)

Call-by-value, left-to-right small-step reduction over **configurations** that carry an
instrumentation *trace*: the set of authority bits exercised so far (`auth`) and effects
performed so far (`eff`).  The trace is what the safety theorems bound:

* `exercise a (capVal κ k)` (with `a ∈ k`) is the one rule that **emits authority** — it adds
  `a` to `auth`.  Capability-safety (M5) shows `auth ⊆ m` for the static ceiling `m`.
* No rule emits effects yet — `perform`/`handle` and the `eff` growth arrive in M6.

This covers the capability + ownership fragment (everything typable by `Typing.lean`).  A
`capVal` carrying authority `k` is produced only by `mint` (→ `fullMask κ`) or `restrict`
(→ `k ∩ k'`); there is no term that forges one from data (C001 holds by construction).
-/

namespace LambdaSigil

/-- Runtime values: units, booleans, lambdas, mint tokens, and capability values. -/
inductive Value : Term → Prop where
  | unit : Value .unit
  | true : Value .true
  | false : Value .false
  | lam {A b} : Value (.lam A b)
  | mintTok {κ} : Value (.mintTok κ)
  | capVal {κ k} : Value (.capVal κ k)

/-- A configuration: the term under evaluation together with the accumulated authority/effect
    trace.  `auth` = authorities exercised so far; `eff` = effects performed so far. -/
structure Config where
  tm : Term
  auth : Authority
  eff : EffectSet

/-- Small-step reduction on configurations.  Congruence rules thread the trace through the
    sub-step; only `exerciseRed` grows the trace (`auth`). -/
inductive Step (S : Sig) : Config → Config → Prop where
  -- β-reduction and application congruences (CBV, left-to-right)
  | beta {A body v Au Ef} :
      Value v →
      Step S ⟨.app (.lam A body) v, Au, Ef⟩ ⟨subst0 v body, Au, Ef⟩
  | app1 {f f' x Au Ef Au' Ef'} :
      Step S ⟨f, Au, Ef⟩ ⟨f', Au', Ef'⟩ →
      Step S ⟨.app f x, Au, Ef⟩ ⟨.app f' x, Au', Ef'⟩
  | app2 {f x x' Au Ef Au' Ef'} :
      Value f → Step S ⟨x, Au, Ef⟩ ⟨x', Au', Ef'⟩ →
      Step S ⟨.app f x, Au, Ef⟩ ⟨.app f x', Au', Ef'⟩
  -- let
  | letBeta {v e2 Au Ef} :
      Value v →
      Step S ⟨.letIn v e2, Au, Ef⟩ ⟨subst0 v e2, Au, Ef⟩
  | let1 {e1 e1' e2 Au Ef Au' Ef'} :
      Step S ⟨e1, Au, Ef⟩ ⟨e1', Au', Ef'⟩ →
      Step S ⟨.letIn e1 e2, Au, Ef⟩ ⟨.letIn e1' e2, Au', Ef'⟩
  -- mint  (the cap constructor; gated statically by the &Admin token's type)
  | mintRed {κ Au Ef} :
      Step S ⟨.mint κ (.mintTok κ), Au, Ef⟩ ⟨.capVal κ (S.fullMask κ), Au, Ef⟩
  | mint1 {κ t t' Au Ef Au' Ef'} :
      Step S ⟨t, Au, Ef⟩ ⟨t', Au', Ef'⟩ →
      Step S ⟨.mint κ t, Au, Ef⟩ ⟨.mint κ t', Au', Ef'⟩
  -- restrict  (attenuation: authority ↦ k₀ ∩ k)
  | restrictRed {k κ k0 Au Ef} :
      Step S ⟨.restrict k (.capVal κ k0), Au, Ef⟩ ⟨.capVal κ (LambdaSigil.restrict k0 k), Au, Ef⟩
  | restrict1 {k t t' Au Ef Au' Ef'} :
      Step S ⟨t, Au, Ef⟩ ⟨t', Au', Ef'⟩ →
      Step S ⟨.restrict k t, Au, Ef⟩ ⟨.restrict k t', Au', Ef'⟩
  -- exercise  (THE authority-emitting step: requires the cap to hold `a`, records `a`)
  | exerciseRed {a κ k Au Ef} :
      a ∈ k →
      Step S ⟨.exercise a (.capVal κ k), Au, Ef⟩ ⟨.unit, insert a Au, Ef⟩
  | exercise1 {a t t' Au Ef Au' Ef'} :
      Step S ⟨t, Au, Ef⟩ ⟨t', Au', Ef'⟩ →
      Step S ⟨.exercise a t, Au, Ef⟩ ⟨.exercise a t', Au', Ef'⟩
  -- sink  (M7: the full-mask authority sink; emits the whole required set `req` into the trace)
  | sinkRed {req κ k Au Ef} :
      req ⊆ k →
      Step S ⟨.sink req (.capVal κ k), Au, Ef⟩ ⟨.unit, Au ∪ req, Ef⟩
  | sink1 {req t t' Au Ef Au' Ef'} :
      Step S ⟨t, Au, Ef⟩ ⟨t', Au', Ef'⟩ →
      Step S ⟨.sink req t, Au, Ef⟩ ⟨.sink req t', Au', Ef'⟩
  | raiseSink {req E v Au Ef} :
      Value v → Step S ⟨.sink req (.perform E v), Au, Ef⟩ ⟨.perform E v, Au, Ef⟩
  -- M6: abortive effect handlers via bubbling.  A *raise* is `perform E v` (`v` a value); it
  -- propagates outward through elimination frames until an enclosing `handle E` catches it.
  | perform1 {E e e' Au Ef Au' Ef'} :
      Step S ⟨e, Au, Ef⟩ ⟨e', Au', Ef'⟩ →
      Step S ⟨.perform E e, Au, Ef⟩ ⟨.perform E e', Au', Ef'⟩
  | raiseApp1 {E v x Au Ef} :
      Value v → Step S ⟨.app (.perform E v) x, Au, Ef⟩ ⟨.perform E v, Au, Ef⟩
  | raiseApp2 {f E v Au Ef} :
      Value f → Value v → Step S ⟨.app f (.perform E v), Au, Ef⟩ ⟨.perform E v, Au, Ef⟩
  | raiseLet {E v e2 Au Ef} :
      Value v → Step S ⟨.letIn (.perform E v) e2, Au, Ef⟩ ⟨.perform E v, Au, Ef⟩
  | raiseMint {κ E v Au Ef} :
      Value v → Step S ⟨.mint κ (.perform E v), Au, Ef⟩ ⟨.perform E v, Au, Ef⟩
  | raiseRestrict {k E v Au Ef} :
      Value v → Step S ⟨.restrict k (.perform E v), Au, Ef⟩ ⟨.perform E v, Au, Ef⟩
  | raiseExercise {a E v Au Ef} :
      Value v → Step S ⟨.exercise a (.perform E v), Au, Ef⟩ ⟨.perform E v, Au, Ef⟩
  | raisePerform {E' E v Au Ef} :
      Value v → Step S ⟨.perform E' (.perform E v), Au, Ef⟩ ⟨.perform E v, Au, Ef⟩
  | handleBody {E h body body' Au Ef Au' Ef'} :
      Step S ⟨body, Au, Ef⟩ ⟨body', Au', Ef'⟩ →
      Step S ⟨.handle E h body, Au, Ef⟩ ⟨.handle E h body', Au', Ef'⟩
  /-- Catch (abortive): a raised `E` reaching its handler discharges to `app h v` (the handler
      applied to the operation argument; `app` then evaluates `h`, so `h` need not be a value). -/
  | handleCatch {E h v Au Ef} :
      Value v → Step S ⟨.handle E h (.perform E v), Au, Ef⟩ ⟨.app h v, Au, Ef⟩
  /-- A raise of a *different* effect propagates through a non-matching handler. -/
  | handlePropagate {E h E' v Au Ef} :
      E' ≠ E → Value v → Step S ⟨.handle E h (.perform E' v), Au, Ef⟩ ⟨.perform E' v, Au, Ef⟩
  /-- The handled computation completed normally — the handle is transparent. -/
  | handleReturn {E h w Au Ef} :
      Value w → Step S ⟨.handle E h w, Au, Ef⟩ ⟨w, Au, Ef⟩
  -- `trap` (SIGIL `Type::Never`) is an UNCATCHABLE raise: it bubbles out of every elimination frame
  -- exactly like `perform E v`, but no `handle` discharges it — it escapes to a terminal abort
  -- (`Stuck` excludes it; `progress` returns it as a fourth answer).  A bare `trap` does not step.
  | trapApp1 {x Au Ef} : Step S ⟨.app .trap x, Au, Ef⟩ ⟨.trap, Au, Ef⟩
  | trapApp2 {f Au Ef} : Value f → Step S ⟨.app f .trap, Au, Ef⟩ ⟨.trap, Au, Ef⟩
  | trapLet {e2 Au Ef} : Step S ⟨.letIn .trap e2, Au, Ef⟩ ⟨.trap, Au, Ef⟩
  | trapMint {κ Au Ef} : Step S ⟨.mint κ .trap, Au, Ef⟩ ⟨.trap, Au, Ef⟩
  | trapRestrict {k Au Ef} : Step S ⟨.restrict k .trap, Au, Ef⟩ ⟨.trap, Au, Ef⟩
  | trapExercise {a Au Ef} : Step S ⟨.exercise a .trap, Au, Ef⟩ ⟨.trap, Au, Ef⟩
  | trapSink {req Au Ef} : Step S ⟨.sink req .trap, Au, Ef⟩ ⟨.trap, Au, Ef⟩
  | trapPerform {E Au Ef} : Step S ⟨.perform E .trap, Au, Ef⟩ ⟨.trap, Au, Ef⟩
  | trapHandle {E h Au Ef} : Step S ⟨.handle E h .trap, Au, Ef⟩ ⟨.trap, Au, Ef⟩

/-- Reflexive-transitive closure: multi-step reduction. -/
abbrev StepStar (S : Sig) : Config → Config → Prop := Relation.ReflTransGen (Step S)

/-- The initial configuration for a program: empty authority/effect trace. -/
def initConfig (e : Term) : Config := ⟨e, ∅, ∅⟩

/-- A **raise**: the term is `perform E v` with `v` a value — a terminal "escaping effect" answer
    (like an uncaught exception), not a stuck state. -/
def Raised (c : Config) : Prop := ∃ E v, c.tm = .perform E v ∧ Value v

/-- A configuration is **stuck** if its term is neither a value, nor a raise, nor able to step —
    these are exactly the runtime errors (e.g. exercising authority a cap doesn't hold) that
    type-safety rules out via progress.  (M6 refines this to exclude `Raised`: a terminal escaping
    effect is a valid answer, not a violation.) -/
def Stuck (S : Sig) (c : Config) : Prop :=
  ¬ Value c.tm ∧ ¬ Raised c ∧ c.tm ≠ .trap ∧ ¬ ∃ c', Step S c c'

end LambdaSigil
