import LambdaSigil.Syntax

/-!
# λ-SIGIL — Static semantics: the typing judgment (Milestone M1)

`Typing S Γ Uin e τ ε m Uout` is the leftover/usage judgment

  `Γ ; Uin ⊢ e : τ ! ε @ m ⊣ Uout`

reading: under cap/effect signature `S` and de Bruijn variable-type context `Γ`, with linear
resources available as `Uin`, the term `e` has type `τ`, performs **at most** the effects `ε`,
exercises authority within the **ceiling** `m`, and leaves resources `Uout`.

This is the mechanized form of the paper's `Γ;Δ ⊢ e : τ ! ρ ⇒ Δ'`
(`docs/papers/sigil-agent-written-code.md` §3.1).

* `Uin`/`Uout : List Bool` run parallel to `Γ`: `true` = a (linear) variable is still
  available, `false` = it has been consumed.  Threading `Uin ⟶ Uout` through the rules is what
  enforces **affine** ownership (`ownership.rs`, O001): a consumed cap is no longer `some true`,
  so it cannot be used again (`var_lin` requires `U[i]? = some true`).
* The authority **ceiling** `m` is a single program-wide budget threaded unchanged; only
  `exercise` reads it (`a ∈ m`), which is what bounds the runtime authority trace
  (capability-safety, M5).
* Effects `ε` are **synthesized** (the exact set the term performs); `perform` adds an effect,
  function application unleashes the callee's latent row.  Bounding the effect trace by `ε`
  is effect-safety (M6).

`perform` and `handle` deliberately have **no rules here** — the entire effect story (operations,
handler discharge, and effect-safety) lands together in M6.  Until then those terms are simply
not well-typed, so the M1–M5 theorems range over the capability + ownership fragment (where the
synthesized effect row `ε` is uniformly `∅`) with no extra side condition.  The `ε` slot is
already threaded so M6 adds `perform`/`handle` without refactoring the judgment.
-/

namespace LambdaSigil

/-- de Bruijn variable-type context (index 0 = innermost binder). -/
abbrev Ctx := List Ty

/-- Usage / availability bit-vector, parallel to a `Ctx`. -/
abbrev Use := List Bool

/-- The λ-SIGIL typing judgment with leftover usage tracking. -/
inductive Typing (S : Sig) : Ctx → Use → Term → Ty → EffectSet → Authority → Use → Prop where
  /-- A **linear** variable: must be currently available; using it consumes it. -/
  | var_lin {Γ U i τ m} :
      Γ[i]? = some τ → τ.isLinear = true → U[i]? = some true →
      Typing S Γ U (.var i) τ ∅ m (U.set i false)
  /-- An **unrestricted** variable: usable freely, consumes nothing. -/
  | var_unr {Γ U i τ m} :
      Γ[i]? = some τ → τ.isLinear = false →
      Typing S Γ U (.var i) τ ∅ m U
  | unit {Γ U m} :
      Typing S Γ U .unit .unit ∅ m U
  | tt {Γ U m} :
      Typing S Γ U .true .bool ∅ m U
  | ff {Γ U m} :
      Typing S Γ U .false .bool ∅ m U
  /-- A lambda performs no effects when defined and consumes nothing; its body's effects become
      the function's **latent** row.  `Ub.tail = U` forbids capturing any outer linear resource
      (functions are unrestricted; linear closures are deferred to a later version). -/
  | lam {Γ U A body B εb m Ub} :
      Typing S (A :: Γ) (true :: U) body B εb m Ub →
      Ub.tail = U →
      Typing S Γ U (.lam A body) (.arrow A εb B) ∅ m U
  /-- Application threads usage left-to-right and unleashes the callee's latent effects `εf`. -/
  | app {Γ U f x A εf B ε1 ε2 m Umid Uout} :
      Typing S Γ U f (.arrow A εf B) ε1 m Umid →
      Typing S Γ Umid x A ε2 m Uout →
      Typing S Γ U (.app f x) B (ε1 ∪ ε2 ∪ εf) m Uout
  /-- `let`: bind `e₁`'s value, type `e₂` in the extended context, drop the bound var's bit. -/
  | letIn {Γ U e1 A ε1 e2 B ε2 m Umid ub Uout} :
      Typing S Γ U e1 A ε1 m Umid →
      Typing S (A :: Γ) (true :: Umid) e2 B ε2 m (ub :: Uout) →
      Typing S Γ U (.letIn e1 e2) B (ε1 ∪ ε2) m Uout
  /-- The mint-authorization token is an unrestricted value. -/
  | mintTok {Γ U κ m} :
      Typing S Γ U (.mintTok κ) (.mintAuth κ) ∅ m U
  /-- `mint κ tok` needs an in-scope `mintAuth κ` (the &Admin gate, T273) and yields a *full*
      authority cap — exactly `fullMask κ`, never more (no forgery, C001) nor less. -/
  | mint {Γ U κ tok εt m Uout} :
      Typing S Γ U tok (.mintAuth κ) εt m Uout →
      Typing S Γ U (.mint κ tok) (.cap κ (S.fullMask κ)) εt m Uout
  /-- A runtime cap value of authority `k`; well-formed only if `k` is within the cap type's
      full mask (a cap can never carry *more* than its declared authority). -/
  | capVal {Γ U κ k m} :
      k ⊆ S.fullMask κ →
      Typing S Γ U (.capVal κ k) (.cap κ k) ∅ m U
  /-- `restrict k e` attenuates the cap's authority index to `k0 ∩ k` (`restrict` of M0). -/
  | restrict {Γ U k e κ k0 εe m Uout} :
      Typing S Γ U e (.cap κ k0) εe m Uout →
      Typing S Γ U (.restrict k e) (.cap κ (LambdaSigil.restrict k0 k)) εe m Uout
  /-- `exercise a e` exercises authority bit `a` of cap `e`.  Two premises: `a ∈ k` (the cap
      actually carries it — used for *progress*) and `a ∈ m` (within the ceiling — used for
      *capability-safety*).  Consumes the cap; yields unit. -/
  | exercise {Γ U a e κ k εe m Uout} :
      Typing S Γ U e (.cap κ k) εe m Uout →
      a ∈ k → a ∈ m →
      Typing S Γ U (.exercise a e) .unit εe m Uout
  /-- `sink req e` (M7) delivers cap `e` to a full-mask authority sink (C003).  Two premises:
      `req ⊆ k` (the cap carries the required authority — the `sinkOk`/C003 check, for *progress*)
      and `req ⊆ m` (within the ceiling — for *capability-safety*).  Consumes the cap; yields unit.
      An attenuated cap (`k ⊊ req`, i.e. `req ⊄ k`) has no derivation — exactly the C003 rejection. -/
  | sink {Γ U req e κ k εe m Uout} :
      Typing S Γ U e (.cap κ k) εe m Uout →
      req ⊆ k → req ⊆ m →
      Typing S Γ U (.sink req e) .unit εe m Uout
  /-- `perform E e` performs effect operation `E` (M6).  Result type is **any** `τ` — the operation
      is abortive (SIGIL `Type::Never`/bottom), so a raised `perform` re-types at whatever frame it
      propagates into (H-1, load-bearing for preservation).  Adds `E` to the synthesized row. -/
  | perform {Γ U E e εe m Uout} {τ : Ty} :
      Typing S Γ U e (S.effParam E) εe m Uout →
      Typing S Γ U (.perform E e) τ (insert E εe) m Uout
  /-- `handle E h body` (M6, abortive): handler `h : effParam E →[εh] H`, body `: H` performing `εb`.
      **Discharges** `E` from the body's row: result row `(εb.erase E) ∪ εh ∪ ρh`. -/
  | handle {Γ U E h body H εh εb ρh m U1 Uout} :
      Typing S Γ U h (.arrow (S.effParam E) εh H) ρh m U1 →
      Typing S Γ U1 body H εb m Uout →
      Typing S Γ U (.handle E h body) H ((εb.erase E) ∪ εh ∪ ρh) m Uout
  /-- `trap` : the bottom type — well-typed at **any** `τ` (abortive, like `perform`), performs no
      effects (`∅`), and consumes nothing (it aborts).  This is `Type::Never`; a statement of this
      type terminates its path (the Rust divergence hook, PR #443). -/
  | trap {Γ U m} {τ : Ty} :
      Typing S Γ U .trap τ ∅ m U

/-- Typing preserves the length of the usage vector: the leftover context has the same shape as
    the input.  (Maintains the `Uin`/`Uout`-parallel-to-`Γ` invariant through the threading
    rules; needed by the substitution and preservation proofs.) -/
theorem Typing.use_length {S Γ Uin e τ ε m Uout}
    (h : Typing S Γ Uin e τ ε m Uout) : Uin.length = Uout.length := by
  induction h with
  | var_lin _ _ _ => simp
  | app _ _ ih1 ih2 => omega
  | letIn _ _ ih1 ih2 => simp only [List.length_cons] at ih2; omega
  | mint _ ih => exact ih
  | restrict _ ih => exact ih
  | exercise _ _ _ ih => exact ih
  | sink _ _ _ ih => exact ih
  | perform _ ih => exact ih
  | handle _ _ ih1 ih2 => omega
  | _ => rfl

end LambdaSigil
