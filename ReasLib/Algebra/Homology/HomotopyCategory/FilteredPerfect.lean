/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteProjective
public import ReasLib.CategoryTheory.Filtration.Derived.Quotient

/-!
# Filtered-perfect homotopy objects

The homotopy category of bounded filtered finite-projective complexes maps fully
faithfully to the finite filtered derived category.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ComplexShape
open scoped FilteredObject.Finite ZeroObject

universe u

namespace CategoryTheory.HomotopyCategory

variable (Λ : Type u) [Ring Λ]

/-- Homotopy-category objects whose underlying cochain complex is bounded and termwise
filtered finite projective. -/
protected def filteredPerfect :
    ObjectProperty (HomotopyCategory (Filᶠ(ModuleCat.{u} Λ)) (up ℤ)) :=
  fun K ↦ CochainComplex.IsBoundedFilteredFiniteProjective K.as

/-- A homotopy-category object is filtered perfect exactly when its underlying complex
is bounded filtered finite projective. -/
lemma filteredPerfect_iff (K : HomotopyCategory (Filᶠ(ModuleCat.{u} Λ)) (up ℤ)) :
    HomotopyCategory.filteredPerfect Λ K ↔
      CochainComplex.IsBoundedFilteredFiniteProjective K.as :=
  sorry

/-- The homotopy category of bounded complexes of filtered finite projective objects of
`Filᶠ(ModuleCat Λ)`. -/
abbrev FilteredPerfect := (HomotopyCategory.filteredPerfect Λ).FullSubcategory

namespace FilteredPerfect

/-- The inclusion of the filtered-perfect homotopy category into the ambient homotopy
category of finite filtered complexes. -/
abbrev ι : FilteredPerfect Λ ⥤ HomotopyCategory (Filᶠ(ModuleCat.{u} Λ)) (up ℤ) :=
  (HomotopyCategory.filteredPerfect Λ).ι

/-- The homotopy class of a bounded filtered finite-projective cochain complex, as an
object of the filtered-perfect homotopy category. -/
def ofComplex (L : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ)
    [hL : CochainComplex.IsBoundedFilteredFiniteProjective L] : FilteredPerfect Λ :=
  ⟨(HomotopyCategory.quotient (Filᶠ(ModuleCat.{u} Λ)) (up ℤ)).obj L, hL⟩

/-- The underlying cochain complex of `ofComplex L` is `L`. -/
theorem ofComplex_as (L : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ)
    [CochainComplex.IsBoundedFilteredFiniteProjective L] :
    (ofComplex Λ L).obj.as = L :=
  sorry

variable [CategoryWithHomology (GradedObject ℤ (ModuleCat.{u} Λ))]

/-- The canonical functor from the filtered-perfect homotopy category to the finite
filtered derived category. -/
def toDerived :
    FilteredPerfect Λ ⥤
      FilteredObject.FiniteDerived.Quotient.Category (ModuleCat.{u} Λ) :=
  ι Λ ⋙ FilteredObject.FiniteDerived.Quotient.functor (ModuleCat.{u} Λ)

/-- The functor from the filtered-perfect homotopy category to the finite filtered
derived category is full. -/
instance instFullToDerived : (toDerived Λ).Full := sorry

/-- The functor from the filtered-perfect homotopy category to the finite filtered
derived category is faithful. -/
instance instFaithfulToDerived : (toDerived Λ).Faithful := sorry

/-- Hom-sets in the filtered-perfect homotopy category map bijectively to Hom-sets in
the finite filtered derived category. -/
theorem toDerived_map_bijective {P Q : FilteredPerfect Λ} :
    Function.Bijective
      ((toDerived Λ).map : (P ⟶ Q) → ((toDerived Λ).obj P ⟶ (toDerived Λ).obj Q)) :=
  sorry

end FilteredPerfect

end CategoryTheory.HomotopyCategory

