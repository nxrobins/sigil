import LambdaSigil.DefiniteInit

/-!
# λ-SIGIL — the ring discipline (R001 / R002 / R003 / R004 / R006)

The R family is SIGIL's *structural* privilege boundary: two rings, with the **inner**
ring the capability-owning, FFI-forbidden tier (and the default — absence of an
annotation is the restricted state, "secure by construction"), and the **outer** ring
the trust/FFI surface that may only *borrow* capabilities. Until this module the whole
family had zero Lean coverage — the largest uncovered code family in the registry.

Everything here is a self-contained leaf (the `MessageBoundary`/`DefiniteInit`
pattern): nothing in the core calculus is touched. Obligations follow
`Differential.lean`'s style — each check is a small decidable predicate mirroring the
shipped Rust, with an accept/reject **witness pair** and a **mutant twin** proving the
load-bearing premise is load-bearing. Two of the mutants are not hypothetical: one
re-derives the *historical* aggregate-smuggle bug class (the walker that forgot an
arm — F005/T183), and one encodes the *documentation's* wrong claim about R004, so
"the doc, not the code" is itself a machine-checked statement.

## Correspondences (ring_check.rs / call_resolve.rs / type_check/mod.rs)

| Code | Rust check | Here |
|---|---|---|
| R006 | `trusted && ring ≠ Outer` rejected (`type_check/mod.rs`) | `ModWf`, `rc_r006_*` |
| R004 | `callee_ring != caller_ring` rejected — SYMMETRIC (`call_resolve.rs`) | `crossRingOk`, `rc_r004_*` |
| R001 | `is_owned_cap` structural walker over params/ret/lets (`ring_check.rs`) | `isOwnedCap`, `rc_r001_*` |
| R002 | `contains_cap_ref` on the RETURN TYPE ONLY (`ring_check.rs`) | `containsCapRef`, `rc_r002_*` |
| R003 | extern-occurrence walk of inner-ring bodies (`ring_check.rs`) | `hasExtern`, `rc_r003_*` |

## Honest scope

* `RTy` is a **binary-arity** miniature of the Rust `Type` (pair instead of n-ary
  tuple; one param slot on `fn`): every aggregate CHANNEL the Rust walkers descend is
  represented, arity is not. The walkers here are arm-for-arm with
  `ring_check.rs`' `is_owned_cap`/`contains_cap_ref`, including `ref` being FALSE for
  ownership (a borrow is not ownership).
* **R002 is stated as the return-type test it is** — not grant-scope confinement.
  The registry title used to over-claim this; it was corrected (roadmap Phase 0)
  precisely so this module would not certify fiction. Grant-lifetime confinement is
  the ownership pass (O007), out of scope here.
* **R003's non-descent is a THEOREM, not a footnote**: the Rust walker deliberately
  does not descend into `IndirectCall` callees or `ClosureConstruct` bodies (closure
  bodies are separately walked as lifted functions). `rc_r003_nondescent_hole` proves
  the corresponding shape is *accepted* by this check — making the documented
  assumption visible as a derivable statement rather than burying it.
* There is no ring tag on the core `Typing` judgment — modules/rings live one level
  above the term calculus, exactly as in SIGIL (rings annotate modules, not
  expressions).
-/

namespace LambdaSigil

/-- The two rings. `inner` is the DEFAULT and the restricted tier (`ast.rs` `Ring`,
    parser default "secure by construction"). -/
inductive Ring where
  | inner | outer
  deriving DecidableEq, Repr

/-- A module declaration's ring-relevant surface: its ring and trust flag. -/
structure ModDecl where
  ring : Ring
  trusted : Bool
  deriving DecidableEq, Repr

/-! ## R006 — `#[trusted]` requires `#[ring(outer)]` -/

/-- **R006.** A module is well-formed only if trust implies the outer ring: the inner
    ring is the capability-owning tier and must never carry the FFI/Unsafe trust bit. -/
def ModWf (m : ModDecl) : Prop := m.trusted = true → m.ring = .outer

instance (m : ModDecl) : Decidable (ModWf m) := by unfold ModWf; infer_instance

/-- R006 reject: a trusted inner-ring module is ill-formed. -/
theorem rc_r006_trusted_inner_rejected : ¬ ModWf ⟨.inner, true⟩ := by decide

/-- R006 accepts: trusted-outer and untrusted-inner are both fine (the rejection is the
    specific combination, not trust or innerness per se). -/
theorem rc_r006_accepts : ModWf ⟨.outer, true⟩ ∧ ModWf ⟨.inner, false⟩ := by decide

/-- MUTANT TWIN: drop the implication (accept every module) and the trusted-inner
    module — the exact shape R006 exists to forbid — becomes well-formed. -/
def ModWfBad (_ : ModDecl) : Prop := True

theorem rc_r006_mutant_admits_trusted_inner : ModWfBad ⟨.inner, true⟩ := trivial

/-! ## R004 — cross-ring calls are rejected, in BOTH directions -/

/-- **R004.** A call is ring-legal iff caller and callee share a ring — the shipped
    check is `callee_ring != tracker.current_module_ring`, with no direction carve-out
    and no stdlib exception. -/
def crossRingOk (caller callee : Ring) : Prop := caller = callee

instance (a b : Ring) : Decidable (crossRingOk a b) := by unfold crossRingOk; infer_instance

/-- **The symmetry pin.** `lang-ref.md` claimed inner-ring modules are "callable from
    either ring without escalation"; the check is symmetric, so that claim is false of
    the code. This theorem pins the symmetry so the doc question has a machine-checked
    answer. -/
theorem rc_r004_symmetric (a b : Ring) : crossRingOk a b ↔ crossRingOk b a := by
  constructor <;> (intro h; exact h.symm)

/-- R004 rejects BOTH directions: inner→outer and outer→inner. -/
theorem rc_r004_cross_rejected :
    ¬ crossRingOk .inner .outer ∧ ¬ crossRingOk .outer .inner := by decide

/-- R004 accepts same-ring calls in both rings. -/
theorem rc_r004_same_ring_accepts :
    crossRingOk .inner .inner ∧ crossRingOk .outer .outer := by decide

/-- MUTANT TWIN — **the documentation's semantics**: "an inner callee is callable from
    either ring". Under it the outer→inner call is derivable, which the shipped check
    rejects. The divergence between doc and code is thereby itself machine-checked:
    `crossRingOkDoc` accepts what `crossRingOk` refuses. -/
def crossRingOkDoc (caller callee : Ring) : Prop :=
  caller = callee ∨ callee = .inner

theorem rc_r004_doc_mutant_admits_cross :
    (crossRingOkDoc .outer .inner) ∧ ¬ crossRingOk .outer .inner := by
  constructor
  · exact Or.inr rfl
  · decide

/-! ## R001 / R002 — the cap-channel walkers -/

/-- A binary-arity miniature of the Rust `Type` for the ring walkers: every aggregate
    CHANNEL `ring_check.rs` descends (tuple slots, closure param/return slots, array
    elements, references) is present; n-ary arity is collapsed to nesting. -/
inductive RTy where
  | base : RTy
  | cap : RTy
  | ref : RTy → RTy
  | pair : RTy → RTy → RTy
  | fn : RTy → RTy → RTy
  | array : RTy → RTy
  deriving DecidableEq, Repr

/-- **R001's walker** (`is_owned_cap`, arm-for-arm): a type OWNS a capability iff a
    `cap` sits in an ownership position. A `ref` is a borrow, NOT ownership — the
    walker is `false` at `ref` without descending, exactly like the Rust arm. -/
def isOwnedCap : RTy → Bool
  | .base => false
  | .cap => true
  | .ref _ => false
  | .pair a b => isOwnedCap a || isOwnedCap b
  | .fn p r => isOwnedCap p || isOwnedCap r
  | .array t => isOwnedCap t

/-- **R002's walker** (`contains_cap_ref`, arm-for-arm): a `&cap` anywhere — a `ref`
    whose target owns a cap (or itself carries one deeper), threaded through every
    aggregate channel. -/
def containsCapRef : RTy → Bool
  | .base => false
  | .cap => false
  | .ref t => isOwnedCap t || containsCapRef t
  | .pair a b => containsCapRef a || containsCapRef b
  | .fn p r => containsCapRef p || containsCapRef r
  | .array t => containsCapRef t

/-- R001 fires through a TUPLE slot — the historical aggregate-smuggle shape (T183:
    a cap wrapped in an aggregate evading the walker). -/
theorem rc_r001_tuple_smuggle : isOwnedCap (.pair .cap .base) = true := by decide

/-- R001 fires through BOTH closure slots (`Fn(Fuel) -> i64` and `Fn(i64) -> Fuel` —
    the `ring_cap_aggregate_smuggle.rs` pair). -/
theorem rc_r001_fn_slot_smuggle :
    isOwnedCap (.fn .cap .base) = true ∧ isOwnedCap (.fn .base .cap) = true := by decide

/-- R001's accept side: a BORROW of a cap is not ownership (`&cap T` is the legal way
    for the outer ring to touch a capability), and a cap-free aggregate is clean. -/
theorem rc_r001_borrow_accepts :
    isOwnedCap (.ref .cap) = false ∧ isOwnedCap (.pair .base (.array .base)) = false := by
  decide

/-- R002 fires on a cap-reference smuggled through an aggregate in the return type. -/
theorem rc_r002_ref_smuggle : containsCapRef (.pair (.ref .cap) .base) = true := by decide

/-- R002's accept side: an OWNED cap in the return type is not a cap-REFERENCE (that is
    R001's dimension), and a plain borrow of a non-cap is clean. -/
theorem rc_r002_owned_is_not_ref :
    containsCapRef .cap = false ∧ containsCapRef (.ref .base) = false := by decide

/-- MUTANT TWIN — **the F005 class resurrected**: the same walker with the `pair` arm
    forgotten (the "walker forgot an arm" bug that shipped as the Tuple/Fn miss). Under
    it the tuple-smuggled cap is INVISIBLE — `ring_check.rs` fences this class with
    `#[deny(clippy::wildcard_enum_match_arm)]` + `walker_fence_tests`; this is that
    fence as a theorem. -/
def isOwnedCapBadPair : RTy → Bool
  | .base => false
  | .cap => true
  | .ref _ => false
  | .pair _ _ => false -- the forgotten arm
  | .fn p r => isOwnedCapBadPair p || isOwnedCapBadPair r
  | .array t => isOwnedCapBadPair t

theorem rc_r001_mutant_misses_tuple_smuggle :
    isOwnedCapBadPair (.pair .cap .base) = false ∧ isOwnedCap (.pair .cap .base) = true := by
  decide

/-- MUTANT TWIN (second channel): forgetting the `fn` arm instead misses the
    closure-slot smuggle — the other half of the historical miss. -/
def isOwnedCapBadFn : RTy → Bool
  | .base => false
  | .cap => true
  | .ref _ => false
  | .pair a b => isOwnedCapBadFn a || isOwnedCapBadFn b
  | .fn _ _ => false -- the forgotten arm
  | .array t => isOwnedCapBadFn t

theorem rc_r001_mutant_misses_fn_smuggle :
    isOwnedCapBadFn (.fn .cap .base) = false ∧ isOwnedCap (.fn .cap .base) = true := by
  decide

/-! ## R003 — no extern calls in inner-ring bodies -/

/-- A miniature body shape for the R003 occurrence walk: extern calls, sequencing, and
    the two deliberate NON-DESCENT nodes (`IndirectCall` callee, `ClosureConstruct`
    body). -/
inductive RExpr where
  | leaf : RExpr
  | externCall : RExpr
  | seq : RExpr → RExpr → RExpr
  | indirect : RExpr → RExpr
  | closure : RExpr → RExpr
  deriving DecidableEq, Repr

/-- **R003's walker**: does an extern call occur in a position the walk reaches?
    `indirect`/`closure` are NOT descended — arm-for-arm with the Rust walk's
    documented assumption that closure bodies are separately checked as lifted
    functions. -/
def hasExtern : RExpr → Bool
  | .leaf => false
  | .externCall => true
  | .seq a b => hasExtern a || hasExtern b
  | .indirect _ => false
  | .closure _ => false

/-- **R003.** An inner-ring body must contain no reachable extern call; the outer ring
    is unrestricted. -/
def R003Ok (r : Ring) (e : RExpr) : Prop := r = .inner → hasExtern e = false

instance (r : Ring) (e : RExpr) : Decidable (R003Ok r e) := by unfold R003Ok; infer_instance

/-- R003 reject: an extern call in an inner-ring body — bare or nested under
    sequencing — is ill-formed. -/
theorem rc_r003_inner_extern_rejected :
    ¬ R003Ok .inner .externCall ∧ ¬ R003Ok .inner (.seq .leaf .externCall) := by decide

/-- R003 accepts: the outer ring may call externs (that is its purpose), and an
    extern-free inner body is fine. -/
theorem rc_r003_accepts :
    R003Ok .outer .externCall ∧ R003Ok .inner (.seq .leaf .leaf) := by decide

/-- **THE NON-DESCENT HOLE, AS A THEOREM.** An extern call sitting under an
    `indirect`/`closure` node is ACCEPTED by this walk — the Rust walker deliberately
    does not descend there, on the documented assumption that closure bodies are
    lambda-lifted into real functions that the ring check visits separately. If that
    assumption is ever broken (a body position that is neither inlined nor lifted),
    this is the exact shape that walks through. Stated as a derivability so the
    assumption is visible, auditable, and impossible to mistake for coverage. -/
theorem rc_r003_nondescent_hole :
    R003Ok .inner (.closure .externCall) ∧ R003Ok .inner (.indirect .externCall) := by
  decide

end LambdaSigil
