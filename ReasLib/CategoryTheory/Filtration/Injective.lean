module

public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import ReasLib.CategoryTheory.Filtration.Category
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Filtered Injective Objects

This module isolates the property of a filtered object whose associated graded pieces are
injective.  It is deliberately stated for arbitrary filtered objects; finite-filtered and other
full-subcategory specializations should use this owner through their inclusion into
`FilteredObject`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace FilteredObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]

/-- A filtered object is filtered injective when every associated graded piece is injective. -/
class IsFilteredInjective (I : FilteredObject C) : Prop where
  /-- Every graded piece of a filtered-injective object is injective. -/
  injective (p : ℤ) : Injective (I.gradedPiece p)

attribute [instance] IsFilteredInjective.injective

/-- Filtered-injectivity transports across an isomorphism of filtered objects. -/
theorem IsFilteredInjective.of_iso {I J : FilteredObject C} (e : I ≅ J)
    (hJ : IsFilteredInjective J) : IsFilteredInjective I := sorry

/-- Filtered-injectivity is invariant under isomorphism of filtered objects. -/
theorem isFilteredInjective_iff_of_iso {I J : FilteredObject C} (e : I ≅ J) :
    IsFilteredInjective I ↔ IsFilteredInjective J := sorry

end FilteredObject

end CategoryTheory
