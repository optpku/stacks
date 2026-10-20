/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Functors
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparisons between filtration quotients

For a decreasing filtration and `p ≤ q`, the inclusion `F^q A ⟶ F^p A` induces a
canonical map `A / F^q A ⟶ A / F^p A`. This file packages these maps as natural
transformations between the quotient functors and records their basic category laws.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.Quotient

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]

/-- The quotient projection, natural in the filtered object. -/
@[stacks 0121 "projection to a filtration quotient"]
def fromForget (p : ℤ) :
    (FilteredObject.forget : FilteredObject C ⥤ C) ⟶ FilteredObject.quotientFunctor p where
  app A := cokernel.π (A.filtration.stage p).arrow
  naturality := fun {_ _} f ↦ (FilteredObject.Hom.quotientMap_comm f p).symm

/-- For `p ≤ q`, the canonical comparison `A / F^q A ⟶ A / F^p A`, natural in `A`. -/
@[stacks 0121 "comparison between filtration quotients"]
def mapOfLE {p q : ℤ} (hpq : p ≤ q) :
    (FilteredObject.quotientFunctor q : FilteredObject C ⥤ C) ⟶
      FilteredObject.quotientFunctor p where
  app A := cokernel.map (A.filtration.stage q).arrow (A.filtration.stage p).arrow
    (A.filtration.inclusion hpq) (𝟙 A.obj) (by simp)
  naturality := by
    intro A B f
    sorry

/-- The component of the comparison between two filtration quotient functors. -/
@[stacks 0121 "comparison map between filtration quotients"]
abbrev comparison (A : FilteredObject C) {p q : ℤ} (hpq : p ≤ q) :
    A.quotient q ⟶ A.quotient p :=
  (mapOfLE hpq).app A

/-- The comparison between filtration quotients is the map of cokernels induced by the stage
inclusion and the identity of the underlying object. -/
@[simp, stacks 0121 "formula for a comparison between filtration quotients"]
theorem comparison_eq (A : FilteredObject C) {p q : ℤ} (hpq : p ≤ q) :
    comparison A hpq =
      cokernel.map (A.filtration.stage q).arrow (A.filtration.stage p).arrow
        (A.filtration.inclusion hpq) (𝟙 A.obj) (by simp) := rfl

/-- A filtered morphism commutes with comparisons between filtration quotients. -/
@[stacks 0121 "naturality of filtration quotient comparison"]
theorem naturality {A B : FilteredObject C} (f : A ⟶ B) {p q : ℤ} (hpq : p ≤ q) :
    f.quotientMap q ≫ comparison B hpq = comparison A hpq ≫ f.quotientMap p := sorry

/-- The comparison from a filtration quotient to itself is the identity. -/
@[simp, stacks 0121 "identity comparison between filtration quotients"]
theorem mapOfLE_refl (p : ℤ) :
    (mapOfLE (le_refl p) :
      (FilteredObject.quotientFunctor p : FilteredObject C ⥤ C) ⟶
        FilteredObject.quotientFunctor p) = 𝟙 _ := sorry

/-- Successive comparisons between filtration quotients compose to the direct comparison. -/
@[stacks 0121 "composition of comparisons between filtration quotients"]
theorem mapOfLE_comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    (mapOfLE hqr :
      (FilteredObject.quotientFunctor r : FilteredObject C ⥤ C) ⟶
        FilteredObject.quotientFunctor q) ≫ mapOfLE hpq =
      mapOfLE (hpq.trans hqr) := sorry

/-- Projection to `A / F^p A` factors through every later quotient `A / F^q A`. -/
@[stacks 0121 "factorization of a filtration quotient projection"]
theorem fromForget_comp_mapOfLE {p q : ℤ} (hpq : p ≤ q) :
    (fromForget q :
      (FilteredObject.forget : FilteredObject C ⥤ C) ⟶
        FilteredObject.quotientFunctor q) ≫ mapOfLE hpq = fromForget p := sorry

end CategoryTheory.FilteredObject.Quotient
