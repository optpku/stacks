module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Field.Defs
public import ReasLib.CategoryTheory.Filtration.Strict.Abelian.Basic

/-!
# A Filtered Vector Space Counterexample

This module provides adjacent jump filtrations on a one-dimensional vector space and the
resulting filtered identity whose coimage-image comparison is not an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace CategoryTheory.FilteredObject

/-- The filtration on `V` that is whole in degrees `p ≤ n` and zero in later degrees. -/
def step (k : Type u) [Field k] (n : ℤ) (V : ModuleCat.{u} k) :
    FilteredObject (ModuleCat.{u} k) where
  obj := V
  filtration :=
    { toFun := fun p ↦ if OrderDual.ofDual p ≤ n then ⊤ else ⊥
      monotone' := sorry }

/-- The `p`-th stage of `step k n V` is whole for `p ≤ n` and zero otherwise. -/
theorem step_stage (k : Type u) [Field k] (n : ℤ) (V : ModuleCat.{u} k) (p : ℤ) :
    (step k n V).filtration.stage p = if p ≤ n then ⊤ else ⊥ := sorry

/-- The one-dimensional vector space equipped with the jump filtration at `n`. -/
def line (k : Type u) [Field k] (n : ℤ) :
    FilteredObject (ModuleCat.{u} k) :=
  step k n (ModuleCat.of k k)

/-- The underlying vector space of `line k n` is `ModuleCat.of k k`. -/
theorem line_obj (k : Type u) [Field k] (n : ℤ) :
    (line k n).obj = ModuleCat.of k k := sorry

/-- The identity of `k`, regarded as a filtered morphism from the jump at `-1` to the jump at `0`.
-/
def lineId (k : Type u) [Field k] : line k (-1) ⟶ line k 0 where
  hom := 𝟙 (ModuleCat.of k k)
  preserves := sorry

/-- The underlying morphism of `lineId k` is the identity morphism of `ModuleCat.of k k`. -/
theorem lineId_hom (k : Type u) [Field k] :
    (lineId k).hom = 𝟙 (ModuleCat.of k k) := sorry

/-- The filtered coimage-image comparison of `lineId k` is not an isomorphism. -/
theorem not_isIso_coimageImageComparison_lineId (k : Type u) [Field k] :
    ¬ IsIso (Hom.coimageImageComparison (lineId k)) := sorry

end CategoryTheory.FilteredObject

end
