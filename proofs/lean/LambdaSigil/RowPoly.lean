import LambdaSigil.RingCheck

/-!
# λ-SIGIL — the row-polymorphism instantiation algebra (Phase 4)

SIGIL's row polymorphism (`fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 ! { e }`) is
**polymorphism by monomorphization**: the checker never reasons about an abstract row.  At each
call site the row variable is BOUND from the actual arguments' rows, the mono key is extended so
instances at different rows cannot fuse, and every instance is checked with fully concrete rows by
the machinery `EffectRows.lean` already models (`Chk`, `Chk.app_latent_bounded`).

The ONLY novel trusted logic is therefore the **call-site binding/instantiation algebra** in
`bind_and_check_effect_rows` (`crates/sigil-compiler/src/type_check/expressions/calls.rs`):

* a formal row is a TEMPLATE `C ∪ e?` — a concrete part plus at most one variable
  (`validate_effect_row_params` rejects two variables in one binding row, so templates with a
  single optional variable are exhaustive);
* one occurrence paired with an actual row `a` contributes the residual `a \ C`;
* across occurrences the residuals UNION;
* an unconstrained variable stays `∅`;
* and every Fn-typed formal — variable or not — must pass the acceptance check
  `a ⊆ inst template binding`.

This module certifies that algebra:

| Rust behaviour (`calls.rs` / `tests/row_poly.rs`) | here |
|---|---|
| unconstrained variable defaults to the empty row | `RP.inst_empty` |
| a larger binding never shrinks an instantiated row | `RP.inst_monotone` |
| the residual `a \ C` satisfies its own constraint | `RP.principal_sound` |
| …and is the LEAST solution of `a ⊆ C ∪ e` | `RP.principal_least` |
| the union binding satisfies EVERY occurrence at once | `RP.union_binding_sound` |
| …and is the least binding that does | `RP.union_binding_least` |
| variable-free formals reduce to the plain subset check | `RP.variable_free_is_exact` |
| the two-occurrence `{EA}`/`{EB}` acceptance (`union_binding_across_two_occurrences`) | `rp_union_witness_accepts` |
| a pure caller of an effectful instantiation is rejected (`pure_caller_of_an_effectful_instantiation_is_e001`) | `rp_pure_caller_rejects` |
| binding by INTERSECTION would break the by-construction guarantee | `RPbad.intersection_launders` |

## Honest scope

* **Rust checks each instance concretely; Lean certifies the algebra only.**  There is no
  row-polymorphic `Chk` here on purpose: the shipped checker deliberately never reasons about an
  abstract row, so an abstract row-polymorphic judgment would OVER-claim the correspondence.  Once
  a binding is computed, every downstream obligation (declared-row containment, latent-row
  discharge) is discharged by the concrete-row machinery `EffectRows.lean` already covers.
* **The mutant twin targets a real single point of failure.**  The generic call path has no
  `type_compatible` argument loop, so for VARIABLE rows the binding walk is the sole gate — its
  acceptance holds *by construction* only because the binding is the union (`RP.principal_sound`
  lifted by `RP.union_binding_sound`).  `RPbad.intersection_launders` shows the intersection
  binding fails its own occurrences: with any weaker-than-union choice, soundness would rest
  entirely on the separate acceptance check, and before Phase 4 that check DID NOT EXIST (the
  TD-1 launder, pinned Rust-side by `concrete_row_on_a_generic_formal_is_now_enforced`).
* This is a self-contained LEAF (the `MessageBoundary`/`DefiniteInit`/`RingCheck` pattern):
  nothing in the core calculus is touched; `EffectSet` (`Finset Nat`) is shared with `Ty.arrow`'s
  rows so the algebra is stated over exactly the row type the checking judgment consumes.
* No FFI, no surface parser — the standing `Differential.lean` caveat applies: this is a reviewed
  correspondence, not a mechanized bridge.
-/

namespace LambdaSigil

namespace RP

/-- A formal row TEMPLATE: the concrete names `C` written alongside at most one row variable.
    `hasVar = false` models a fully concrete row (including the unannotated `Fn(T) -> U`, where
    `C = ∅`).  At most ONE variable per binding row is a v1 invariant enforced by E011, so a
    single flag is exhaustive. -/
structure RowTemplate where
  concrete : EffectSet
  hasVar : Bool
deriving DecidableEq

/-- Instantiation: substitute the binding `σ` for the variable (if any).  Mirrors
    `resolve_effect_row_with_vars` / `overlay_rows`: written concretes union the binding. -/
def inst (t : RowTemplate) (σ : EffectSet) : EffectSet :=
  t.concrete ∪ cond t.hasVar σ ∅

/-- One call site is a list of `(formal template, actual row)` occurrence pairs — the Fn-typed
    formals zipped with their arguments' latent rows. -/
abbrev Occurrences := List (RowTemplate × EffectSet)

/-- The binding Rust computes: the UNION of each variable-bearing occurrence's residual
    `a \ C`.  Variable-free occurrences contribute nothing (they are pure acceptance checks). -/
def unionBinding (pairs : Occurrences) : EffectSet :=
  pairs.foldr (fun p acc => cond p.1.hasVar (p.2 \ p.1.concrete) ∅ ∪ acc) ∅

/-- The acceptance check (`bind_and_check_effect_rows`, pass 2): every occurrence's actual row
    is bounded by its instantiated template. -/
def Sat (σ : EffectSet) (pairs : Occurrences) : Prop :=
  ∀ p ∈ pairs, p.2 ⊆ inst p.1 σ

instance (σ : EffectSet) (pairs : Occurrences) : Decidable (Sat σ pairs) :=
  List.decidableBAll _ pairs

/-- **Unconstrained default**: a variable no argument constrains instantiates every template to
    its written concretes — `fn h<e>() -> i64 ! { e }` behaves as `! { }`. -/
theorem inst_empty (t : RowTemplate) : inst t ∅ = t.concrete := by
  obtain ⟨C, hv⟩ := t
  cases hv <;> simp [inst]

/-- **Monotonicity**: growing the binding never shrinks an instantiated row.  This is what lets
    the per-occurrence residual survive the union — the lifting step inside
    `union_binding_sound`. -/
theorem inst_monotone (t : RowTemplate) {σ₁ σ₂ : EffectSet} (h : σ₁ ⊆ σ₂) :
    inst t σ₁ ⊆ inst t σ₂ := by
  obtain ⟨C, hv⟩ := t
  cases hv
  · exact Finset.Subset.refl _
  · exact Finset.union_subset_union (Finset.Subset.refl C) h

/-- **The residual satisfies its own constraint**: `a ⊆ C ∪ (a \ C)`.  The binding pass never
    manufactures an occurrence it cannot immediately justify. -/
theorem principal_sound (C a : EffectSet) : a ⊆ inst ⟨C, true⟩ (a \ C) := by
  intro x hx
  show x ∈ C ∪ (a \ C)
  by_cases hc : x ∈ C
  · exact Finset.mem_union_left _ hc
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hc⟩)

/-- **The residual is the LEAST solution** of the occurrence constraint `a ⊆ C ∪ σ` — any
    binding that satisfies the occurrence contains `a \ C`.  (Principality: Rust's choice is not
    merely sound, it is the canonical minimum, so the mono key is deterministic.) -/
theorem principal_least {C σ a : EffectSet} (h : a ⊆ inst ⟨C, true⟩ σ) : a \ C ⊆ σ := by
  intro x hx
  rw [Finset.mem_sdiff] at hx
  have hmem : x ∈ C ∪ σ := h hx.1
  exact (Finset.mem_union.mp hmem).resolve_left hx.2

/-- Each variable-bearing occurrence's residual survives into the union binding. -/
theorem residual_subset_unionBinding {pairs : Occurrences} {t : RowTemplate} {a : EffectSet}
    (hmem : (t, a) ∈ pairs) (hv : t.hasVar = true) :
    a \ t.concrete ⊆ unionBinding pairs := by
  induction pairs with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with heq | hmem'
    · subst heq
      show a \ t.concrete ⊆ cond t.hasVar (a \ t.concrete) ∅ ∪ unionBinding tl
      rw [hv]
      exact Finset.subset_union_left
    · exact (ih hmem').trans Finset.subset_union_right

/-- **Soundness of the union binding**: provided every VARIABLE-FREE occurrence already passes
    its concrete check (Rust's acceptance pass — the half that is a genuine rejection), the union
    binding satisfies EVERY occurrence.  For variable rows acceptance holds by construction —
    exactly why `bind_and_check_effect_rows`' pass 2 can never fire on a variable row. -/
theorem union_binding_sound {pairs : Occurrences}
    (hconc : ∀ p ∈ pairs, p.1.hasVar = false → p.2 ⊆ p.1.concrete) :
    Sat (unionBinding pairs) pairs := by
  intro p hp
  obtain ⟨⟨C, hv⟩, a⟩ := p
  cases hv
  · intro x hx
    exact Finset.mem_union_left _ (hconc _ hp rfl hx)
  · exact (principal_sound C a).trans
      (inst_monotone _ (residual_subset_unionBinding hp rfl))

/-- **Leastness of the union binding**: any binding satisfying every occurrence contains it.
    Together with `union_binding_sound` this makes Rust's binding the canonical least solution
    of the whole call site — inference is deterministic and minimal (accept-minimal: it never
    charges a caller for effects no argument forced). -/
theorem union_binding_least {pairs : Occurrences} {σ : EffectSet} (hsat : Sat σ pairs) :
    unionBinding pairs ⊆ σ := by
  induction pairs with
  | nil => simp [unionBinding]
  | cons hd tl ih =>
    obtain ⟨⟨C, hv⟩, a⟩ := hd
    refine Finset.union_subset ?_ (ih fun p hp => hsat p (List.mem_cons_of_mem _ hp))
    cases hv
    · exact Finset.empty_subset σ
    · exact principal_least (hsat _ (by simp))

/-- **Variable-free formals reduce to the plain subset check** — the acceptance pass is the ONLY
    gate for a concrete row on a generic formal, independent of any binding.  This is the row
    half of the TD-1 hole: before Phase 4 no path enforced the right-hand side. -/
theorem variable_free_is_exact (C a σ : EffectSet) :
    a ⊆ inst ⟨C, false⟩ σ ↔ a ⊆ C := by
  constructor
  · intro h x hx
    rcases Finset.mem_union.mp (h hx) with hc | he
    · exact hc
    · exact absurd he (by simp)
  · intro h x hx
    exact Finset.mem_union_left _ (h hx)

end RP

/-! ## Non-vacuity — the two-occurrence witness pair

The `union_binding_across_two_occurrences` scenario from `tests/row_poly.rs`: two `! { e }`
formals receive closures with rows `{EA}` and `{EB}` (encoded 0 and 1). -/

/-- Two variable-bearing `! { e }` occurrences with actual rows `{0}` and `{1}`. -/
def rpWitness : RP.Occurrences := [(⟨∅, true⟩, {0}), (⟨∅, true⟩, {1})]

/-- **The accepting half**: the union binding `{0, 1}` satisfies both occurrences. -/
theorem rp_union_witness_accepts : RP.Sat (RP.unionBinding rpWitness) rpWitness := by decide

/-- **The rejecting half**: the instantiated declared row `inst ⟨∅, e⟩ {0,1} = {0,1}` is NOT
    contained in a pure caller's empty row — the E001 the Rust test
    `pure_caller_of_an_effectful_instantiation_is_e001` pins.  Without the row-keyed mono cache
    the second instantiation would FUSE with an earlier one and skip this comparison entirely
    (the fusing launder). -/
theorem rp_pure_caller_rejects :
    ¬ RP.inst ⟨∅, true⟩ (RP.unionBinding rpWitness) ⊆ (∅ : EffectSet) := by decide

/-! ## The mutant twin — intersection binding launders -/

namespace RPbad

/-- The wrong algebra: bind the variable to the INTERSECTION of the residuals.  On the witness,
    `{0} ∩ {1} = ∅`. -/
def intersectionBinding : EffectSet := ({0} : EffectSet) ∩ ({1} : EffectSet)

/-- **The launder**: the intersection binding fails its own occurrences — `{0} ⊄ inst ⟨∅,e⟩ ∅`.
    The union choice is load-bearing: with any weaker binding, by-construction acceptance breaks
    and soundness for variable rows would rest entirely on a separate check that did not exist
    before Phase 4 (the generic call path had no `type_compatible` argument loop at all). -/
theorem intersection_launders : ¬ RP.Sat intersectionBinding rpWitness := by decide

end RPbad

end LambdaSigil
