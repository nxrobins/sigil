import LambdaSigil.TaintSafety

/-!
# λ-SIGIL — the actor message boundary as a taint sink (F007 / T001)

`Taint.lean` proves the *flow invariant* every sink enforces, but says twice, in writing, that it
stops short of the actor boundary:

> the Rust F007 bug was specifically a *missing* taint sink at the actor `send`/`ask` message
> boundary; this calculus proves the *flow invariant* that fix restored … **it does not model the
> actor boundary itself**

> `sink ℓ e` … is a **terminal delivery check** … **it does not model the *propagating* half** of a
> Call/Send node

This module models that missing half: a **message delivery** that resolves a callee entry point and
rebinds the payload at the *declared* label of that entry.

## What is proven

* `MsgOk.checked` — the **total boundary census**: *every* boundary constructor (`send`, `ask`,
  `spawn`) both resolves its entry point and discharges the flow check.  There is no fourth
  constructor and no rule that skips either premise, so "we remembered all three sites" stops being
  a hand-audit and becomes a `cases` over a closed inductive.
* `MsgOk.delivery_clean` — **delivery is observed**: the `(delivered, declared)` pair a delivery
  records is `Clean`, so `Taint.lean`'s `Clean` invariant extends *across* the boundary instead of
  stopping at a terminal `sink`.
* `MsgOk.requires_resolution` — **fail-closed resolution**: a message whose entry point does not
  resolve has **no derivation** at all.  The check cannot be silently skipped.

## Faithfulness

The entry table is deliberately **partial** (`Nat → Option Label`) because the shipped lookup can
miss: `find_handler_param_taints` / `find_actor_init_param_taints` return an `Option`.  SIGIL now
handles that miss **fail-closed** — `unwrap_or_else(|| panic!(…))` plus an `assert_eq!` on payload
arity in `check_message_payload_taint` / `check_actor_init_payload_taint` (`taint_check.rs`) — and
`MsgOk.requires_resolution` is the calculus-side statement of exactly that discipline.  This is a
mirror of shipped behaviour, not a specification of a fix.

Historical note: both halves of this boundary have shipped as real bugs — **F007** (send/ask
payloads never checked against the receiving handler's declared param taints) and its twin on
`spawn`.  All three constructors now carry the check on both sides.

## Honest scope

`Msg` is **nullary in the payload's continuation**: a delivery checks and records, it does not bind
the payload into a callee body.  Modelling the callee body would require a binder, hence
substitution, and `Taint.lean`'s scope note (option-1 / option-2) prices that retrofit explicitly.
So this proves *the boundary is a checked, observed, fail-closed sink* — not that a handler body
re-checks what it does with a delivered value afterwards.
-/

namespace LambdaSigil

/-- Declared parameter label per callee entry point (handler or actor `init`).

    **Partial on purpose**: the shipped `find_handler_param_taints` /
    `find_actor_init_param_taints` return an `Option`, so an unresolvable entry must be
    representable — see `MsgOk.requires_resolution`. -/
abbrev EntryTable := Nat → Option Label

/-- The three actor message boundaries.  This closed inductive **is** the census: `send`, `ask`,
    `spawn` and nothing else. -/
inductive Msg where
  | send : Nat → Tm → Msg
  | ask : Nat → Tm → Msg
  | spawn : Nat → Tm → Msg
  deriving DecidableEq, Repr

/-- The callee entry point a message targets. -/
def Msg.entry : Msg → Nat
  | .send h _ => h
  | .ask h _ => h
  | .spawn h _ => h

/-- The payload delivered. -/
def Msg.payload : Msg → Tm
  | .send _ p => p
  | .ask _ p => p
  | .spawn _ p => p

/-- **Message delivery.**  `MsgOk E pc msg ℓdel ℓd` : under entry table `E` and control label `pc`,
    `msg` delivers a payload observed at label `ℓdel` to an entry whose declared label is `ℓd`.

    Each rule carries the same two premises the shipped checker runs at each of its three sites:
    the entry **resolves** (`E h = some ℓd`), and the payload's label joined with the control label
    **may flow** to the declared label (`lub pc ℓ ≤ ℓd`, i.e. `arg_taint.can_flow_to(param.taint)`
    after `compute_expr_taint` folds in `pc`). -/
inductive MsgOk (E : EntryTable) (pc : Label) : Msg → Label → Label → Prop where
  | sendOk {h p ℓ ℓd} :
      E h = some ℓd → TW [] pc p .dat ℓ → Label.lub pc ℓ ≤ ℓd →
      MsgOk E pc (.send h p) (Label.lub pc ℓ) ℓd
  | askOk {h p ℓ ℓd} :
      E h = some ℓd → TW [] pc p .dat ℓ → Label.lub pc ℓ ≤ ℓd →
      MsgOk E pc (.ask h p) (Label.lub pc ℓ) ℓd
  | spawnOk {h p ℓ ℓd} :
      E h = some ℓd → TW [] pc p .dat ℓ → Label.lub pc ℓ ≤ ℓd →
      MsgOk E pc (.spawn h p) (Label.lub pc ℓ) ℓd

/-- **The total boundary census.**  Every delivery — whichever of the three constructors it uses —
    both resolved its entry point and discharged the flow check.  A boundary that skipped either
    premise is not merely unproven, it is *underivable*. -/
theorem MsgOk.checked {E : EntryTable} {pc msg ℓdel ℓd} (h : MsgOk E pc msg ℓdel ℓd) :
    E msg.entry = some ℓd ∧ ℓdel ≤ ℓd := by
  cases h with
  | sendOk hE hw hle => exact ⟨hE, hle⟩
  | askOk hE hw hle => exact ⟨hE, hle⟩
  | spawnOk hE hw hle => exact ⟨hE, hle⟩

/-- **Delivery is observed.**  The `(delivered, declared)` pair recorded by a well-formed delivery
    is `Clean`, so the `Clean` trace invariant of `taint_noninterference` extends across the actor
    boundary rather than stopping at a terminal `sink`. -/
theorem MsgOk.delivery_clean {E : EntryTable} {pc msg ℓdel ℓd} (h : MsgOk E pc msg ℓdel ℓd) :
    Clean [(ℓdel, ℓd)] := by
  intro q hq
  simp at hq
  subst hq
  exact h.checked.2

/-- **Fail-closed resolution.**  A message whose entry point does not resolve has no derivation:
    the boundary check cannot be skipped by a lookup miss.  This is the calculus-side statement of
    the shipped `unwrap_or_else(|| panic!(…))` discipline. -/
theorem MsgOk.requires_resolution {E : EntryTable} {pc msg} (hnone : E msg.entry = none) :
    ¬ ∃ ℓdel ℓd, MsgOk E pc msg ℓdel ℓd := by
  rintro ⟨ℓdel, ℓd, hok⟩
  rw [hok.checked.1] at hnone
  simp at hnone

/-! ## Non-vacuity — the F007 witness family

Every entry declares `@Public`; the leak is a `@Secret` payload crossing the boundary. -/

/-- An entry table where every callee declares a `@Public` parameter. -/
def pubEntry : EntryTable := fun _ => some .pub

/-- An entry table that resolves nothing (models a lookup miss). -/
def noEntry : EntryTable := fun _ => none

/-- **F007 (`send`)** — a `@Secret` payload sent to a `@Public`-declared handler parameter has no
    derivation.  This is the exact bug that shipped: the payload was laundered to `@Public` inside
    the receiver because no sink checked it. -/
theorem secret_send_to_public_entry_rejected :
    ¬ ∃ ℓdel ℓd, MsgOk pubEntry .pub (.send 0 (.data .sec)) ℓdel ℓd := by
  rintro ⟨ℓdel, ℓd, h⟩
  cases h with
  | sendOk hE hw hle =>
    cases hw
    simp [pubEntry] at hE
    subst hE
    exact absurd hle (by decide)

/-- **F007 (`ask`)** — the same leak through `ask`. -/
theorem secret_ask_to_public_entry_rejected :
    ¬ ∃ ℓdel ℓd, MsgOk pubEntry .pub (.ask 0 (.data .sec)) ℓdel ℓd := by
  rintro ⟨ℓdel, ℓd, h⟩
  cases h with
  | askOk hE hw hle =>
    cases hw
    simp [pubEntry] at hE
    subst hE
    exact absurd hle (by decide)

/-- **F007's twin (`spawn`)** — the same leak through an actor `init` payload.  `spawn` was the
    boundary originally left exempt from the send/ask fix; here it carries the identical premise. -/
theorem secret_spawn_to_public_entry_rejected :
    ¬ ∃ ℓdel ℓd, MsgOk pubEntry .pub (.spawn 0 (.data .sec)) ℓdel ℓd := by
  rintro ⟨ℓdel, ℓd, h⟩
  cases h with
  | spawnOk hE hw hle =>
    cases hw
    simp [pubEntry] at hE
    subst hE
    exact absurd hle (by decide)

/-- **The accepting twin.**  A `@Public` payload crosses the same boundary fine — so the three
    rejections above are genuine flow violations, not a boundary that rejects everything. -/
theorem public_send_to_public_entry_accepts :
    MsgOk pubEntry .pub (.send 0 (.data .pub)) (Label.lub .pub .pub) .pub :=
  .sendOk rfl .data (by decide)

/-- **Fail-closed, witnessed.**  Even a perfectly clean `@Public` payload is *rejected* when the
    entry point cannot be resolved — a miss is never a skip. -/
theorem unresolved_entry_ill_typed :
    ¬ ∃ ℓdel ℓd, MsgOk noEntry .pub (.send 0 (.data .pub)) ℓdel ℓd :=
  MsgOk.requires_resolution rfl

end LambdaSigil
