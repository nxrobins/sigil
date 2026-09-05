import LambdaSigil.Authority

/-!
# λ-SIGIL — Syntax (Milestone M1)

Types and terms of the core calculus.  Capability types are **authority-indexed**
(`cap κ k` = a capability of cap-type `κ` currently carrying authority `k`), exactly the
`Cap[k]` of the SIGIL paper (`docs/papers/sigil-agent-written-code.md` §3.1).  Tracking
authority in the type is what lets capability-safety be a *type-level* confinement theorem.

Design (see plan): caps are authority-indexed **values** (`capVal κ k`), affinity is enforced
by a leftover/usage typing context (`Typing.lean`), and the operational semantics is
substitution-based with an instrumented authority/effect trace (`Semantics.lean`).  This
mirrors the paper's leftover judgment `Γ;Δ ⊢ e : τ ! ρ ⇒ Δ'` rather than a heap of locations.
-/

namespace LambdaSigil

/-- Capability type names (≅ the cap-type registry keys, `registries.rs`). -/
abbrev CapName := Nat

/-- Effect operation names (≅ the effect registry, `registries.rs:83`). -/
abbrev EffName := Nat

/-- Types.  `arrow A ε B` is a function `A →[ε] B` whose body may perform the effects `ε`
    (the *latent effect row*, `effect_check.rs`). -/
inductive Ty where
  | unit : Ty
  | bool : Ty
  /-- `cap κ k` : a capability of cap-type `κ` carrying authority `k` (a submask of its
      registered `fullMask κ`). -/
  | cap : CapName → Authority → Ty
  /-- `mintAuth κ` : the in-scope authorization token (the `&Admin` borrow, T273) needed to
      `mint` a capability of type `κ`.  It is a *borrow*, hence unrestricted (Copy). -/
  | mintAuth : CapName → Ty
  | arrow : Ty → EffectSet → Ty → Ty
  deriving DecidableEq

/-- A type is **linear** (affine: usable at most once) iff it is a capability.  Base types,
    the mint token (a borrow), and functions are unrestricted (Copy).

    Faithfulness: `AirValueKind::Cap`/`Linear` vs `Copy` (`air.rs:574`); the move-checker
    `ownership.rs` only fires O001 on `is_linear()` values. -/
def Ty.isLinear : Ty → Bool
  | .cap _ _ => true
  | _ => false

/-- Terms, in de Bruijn form.  Includes both *surface* operations (`mint`, `restrict`,
    `exercise`, `perform`, `handle`) and the *runtime values* they produce (`capVal`,
    `mintTok`). -/
inductive Term where
  | var : Nat → Term                       -- de Bruijn index (0 = innermost binder)
  | unit : Term
  | true : Term
  | false : Term
  | lam : Ty → Term → Term                 -- λ (_ : A). body
  | app : Term → Term → Term
  | letIn : Term → Term → Term             -- let _ = e₁ in e₂   (binds in e₂)
  /-- The mint-authorization token value for `κ` (models an in-scope `&Admin`). -/
  | mintTok : CapName → Term
  /-- `mint κ tok` : forge a fresh full-authority cap of type `κ`, gated by `tok : mintAuth κ`. -/
  | mint : CapName → Term → Term
  /-- A runtime capability value of type `κ` carrying authority `k`.  The *only* way caps come
      into being is `mint`/`restrict`/the initial environment — never record construction
      (this is what C001 enforces; here it is enforced by there being no cap-forging term). -/
  | capVal : CapName → Authority → Term
  /-- `restrict k e` : attenuate cap `e` to authority `auth ∩ k` (consumes `e`). -/
  | restrict : Authority → Term → Term
  /-- `exercise a e` : exercise authority bit `a` of cap `e` (the host-call / FFI sink). -/
  | exercise : Nat → Term → Term
  /-- `sink req e` : deliver capability `e` to a sink (Call/spawn/send/return) that demands authority
      `req` — the C003 full-mask sink check `sinkOk req k = req ⊆ k` (a full-authority sink takes
      `req = fullMask κ`).  One constructor abstracts all four surface sinks; an attenuated cap
      (`k ⊊ req`) is rejected (C003). -/
  | sink : Authority → Term → Term
  /-- `perform E e` : perform effect operation `E` with argument `e`. -/
  | perform : EffName → Term → Term
  /-- `handle E h body` : handle effect `E` over `body` with abortive handler `h`
      (a function from the operation argument to the handle's result). -/
  | handle : EffName → Term → Term → Term
  /-- `trap` : the naked bottom-typed abort (SIGIL `Type::Never` / `trap()`).  Nullary and
      effect-free, and *uncatchable*: it bubbles out of every elimination frame like a raise, but no
      `handle` discharges it — it escapes to a terminal abort.  Faithful to the Rust `air.rs`
      `trap()` lowering (`unreachable`), PR #443. -/
  | trap : Term
  deriving DecidableEq

/-- The capability/effect **signature** (registry): each cap type's full authority mask, and
    each effect operation's parameter and result type.  Parameterizes the whole development —
    the typing judgment and semantics are stated for an arbitrary `Sig`. -/
structure Sig where
  /-- `full_mask` of a cap type (`registries.rs:25`). -/
  fullMask : CapName → Authority
  /-- The argument type of an effect operation. -/
  effParam : EffName → Ty
  /-- The result (resumed-value) type of an effect operation. -/
  effRet : EffName → Ty

end LambdaSigil
