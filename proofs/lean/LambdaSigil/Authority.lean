import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic

/-!
# λ-SIGIL — Authority and Effect algebra (Milestone M0)

This module fixes the algebraic core that the soundness theorems rest on: how capability
*authority* attenuates, what a capability *sink* demands, and how *effect rows* compose.

## Faithfulness anchors (SIGIL Rust implementation)

* **Authority = bitmask.** Authority masks are 32-bit bitvectors
  (`crates/sigil-compiler/src/registries.rs:25-69`, `full_mask` / `restriction_mask`).
  We model an authority as a `Finset ℕ` of bit indices; `⊆`/`∩` on `Finset` mirror submask /
  bitwise-and on `BitVec 32`.  (Finiteness is not load-bearing for soundness — only the
  ⊆/∩/∪ lattice structure is — so a `Finset` is a faithful and convenient choice.)
* **`restrict` = bitwise-and.** Attenuation narrows authority by a restriction mask
  (`crates/sigil-compiler/src/air.rs:246`, `dst = src & mask`, with the invariant `dst ⊆ src`).
* **Sinks demand full authority.** Capability sinks (Call / Spawn / Serialize / Return) require
  the cap to carry *all* of the cap type's authority
  (the diagnostic-C003 sink emissions in
  `crates/sigil-compiler/src/air_capability_v2/mod.rs` — the statement-sink loop
  covering call, spawn-argument, and serialize-message sinks, plus the
  return-terminator sink).
* **Effect discipline = subset.** A call is legal iff `callee.effects ⊆ caller.effects`
  (`crates/sigil-compiler/src/effect_check.rs:165`, diagnostic E001); a `handle E` block
  *widens* the ambient row by `E` (`effect_check.rs:231`).

The proofs below deliberately work at the membership level (`Finset.mem_inter`,
`Finset.mem_union`, `Finset.mem_insert_of_mem`) so they are robust to Mathlib renamings of the
higher-level subset lemmas.
-/

namespace LambdaSigil

/-- An authority is a finite set of authority-bit indices (≅ a submask of `BitVec 32`). -/
abbrev Authority := Finset Nat

/-- An effect row is a finite set of effect identifiers. -/
abbrev EffectSet := Finset Nat

/-- Attenuate `a` by restriction mask `k`: keep only authorities present in both.
    Mirrors `dst = src & mask` in AIR lowering. -/
def restrict (a k : Authority) : Authority := a ∩ k

/-- A capability sink with `required` authority accepts an `actual` cap iff the cap carries
    *all* required authorities.  Mirrors the C003 check `actual & required = required`. -/
abbrev sinkOk (required actual : Authority) : Prop := required ⊆ actual

/-! ## Restriction cannot amplify authority

The algebraic heart of capability confinement (ROADMAP item 8 (c)).  Once wired to the
dynamic semantics in M5 this becomes the invariant that a cap's runtime authority never
grows. -/

/-- Restriction only ever shrinks authority: `restrict a k ⊆ a`. -/
theorem restrict_cannot_amplify (a k : Authority) : restrict a k ⊆ a := by
  intro x hx
  simp only [restrict, Finset.mem_inter] at hx
  exact hx.1

/-- Restriction is also bounded by the mask: `restrict a k ⊆ k`. -/
theorem restrict_le_mask (a k : Authority) : restrict a k ⊆ k := by
  intro x hx
  simp only [restrict, Finset.mem_inter] at hx
  exact hx.2

/-- Restricting never lets a cap satisfy a sink that its *source* could not already satisfy:
    if `required ⊆ restrict a k` then `required ⊆ a`.  (No attenuation-then-escalation.) -/
theorem restrict_preserves_sink {required a k : Authority}
    (h : sinkOk required (restrict a k)) : sinkOk required a := by
  intro x hx
  exact restrict_cannot_amplify a k (h hx)

/-- Iterated restriction is monotone-decreasing: any chain of attenuations stays within the
    original authority. -/
theorem restrict_chain (a k₁ k₂ : Authority) : restrict (restrict a k₁) k₂ ⊆ a := by
  intro x hx
  exact restrict_cannot_amplify a k₁ (restrict_cannot_amplify (restrict a k₁) k₂ hx)

/-- `restrict` is commutative as a set operation (attenuating by `k₁` then `k₂` = vice versa).
    Useful when normalizing attenuation order. -/
theorem restrict_comm (a k₁ k₂ : Authority) :
    restrict (restrict a k₁) k₂ = restrict (restrict a k₂) k₁ := by
  simp only [restrict, Finset.inter_assoc]
  rw [Finset.inter_comm k₁ k₂]

/-! ## Mint produces exactly the declared authority

A minted capability carries *exactly* its cap type's `full_mask` — never more (no forgery /
amplification, diagnostic C001) and never less (mint is unattenuated).  The fully meaningful
statement relates `mint` to a store cell and is proved in M5; here we record the algebraic
fact that any attenuation of a minted (full) authority stays within it, which is what the
downstream confinement argument consumes. -/

/-- Any authority a minted (full) cap can ever exercise after attenuation is within its
    declared full mask.  (M5 lifts this to: the cap's store-cell authority ⊆ `full`.) -/
theorem mint_attenuation_bounded (full k : Authority) : restrict full k ⊆ full :=
  restrict_cannot_amplify full k

/-! ## Effect-row algebra (effect discipline, E001 / handler widening) -/

/-- The legality predicate for a call: the callee's effects must lie within the caller's row. -/
abbrev effectsOk (callee caller : EffectSet) : Prop := callee ⊆ caller

/-- A `handle E` block widens the ambient row so the body may use `E` (`effect_check.rs:231`). -/
def widen (caller : EffectSet) (E : Nat) : EffectSet := insert E caller

/-- Widening only grows the row: the original effects remain available in the body. -/
theorem subset_widen (caller : EffectSet) (E : Nat) : caller ⊆ widen caller E := by
  intro x hx
  simp only [widen]
  exact Finset.mem_insert_of_mem hx

/-- The widened effect `E` is itself available in the body. -/
theorem mem_widen_self (caller : EffectSet) (E : Nat) : E ∈ widen caller E := by
  simp only [widen]
  exact Finset.mem_insert_self E caller

/-- Effect-subset is transitive — threads the declared row through nested calls. -/
theorem effectsOk_trans {a b c : EffectSet} (h₁ : effectsOk a b) (h₂ : effectsOk b c) :
    effectsOk a c := by
  intro x hx
  exact h₂ (h₁ hx)

/-- Trace-bound lemma: if two effect sets are each within a bound `m`, so is their union.
    This is the shape consumed by effect-safety in M6 (each step's effect delta ⊆ `m`). -/
theorem union_subset_of_subset {a b m : EffectSet} (ha : a ⊆ m) (hb : b ⊆ m) :
    a ∪ b ⊆ m := by
  intro x hx
  rw [Finset.mem_union] at hx
  cases hx with
  | inl h => exact ha h
  | inr h => exact hb h

/-- Adding a single permitted effect to a bounded set keeps it bounded — the per-step shape
    consumed by the capability/effect trace invariants (M5/M6). -/
theorem insert_subset_of_mem {a m : EffectSet} {e : Nat}
    (hmem : e ∈ m) (ha : a ⊆ m) : insert e a ⊆ m := by
  intro x hx
  rw [Finset.mem_insert] at hx
  cases hx with
  | inl h => exact h ▸ hmem
  | inr h => exact ha h

end LambdaSigil
