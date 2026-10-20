module

public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import ReasLib.CategoryTheory.Filtration.Category
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Filtered Projective Objects

A filtered object is filtered projective if all its integer-indexed associated graded pieces
are projective in the ambient category. This condition applies to arbitrary filtered objects
and restricts to the same criterion on finite filtered objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory

namespace FilteredObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]

/-- A filtered object is filtered projective when every associated graded piece is projective. -/
class IsFilteredProjective (I : FilteredObject C) : Prop where
  /-- Every graded piece of a filtered-projective object is projective. -/
  projective (p : ℤ) : Projective (I.gradedPiece p)

attribute [instance] IsFilteredProjective.projective

/-- Filtered-projectivity is equivalent to projectivity of every associated graded piece. -/
theorem isFilteredProjective_iff {I : FilteredObject C} :
    IsFilteredProjective I ↔ ∀ p, Projective (I.gradedPiece p) := sorry

/-- Filtered-projectivity transports across an isomorphism of filtered objects. -/
theorem IsFilteredProjective.of_iso {I J : FilteredObject C} (e : I ≅ J)
    (hJ : IsFilteredProjective J) : IsFilteredProjective I := sorry

/-- The zero filtered object is filtered projective. -/
noncomputable instance instIsFilteredProjectiveZero [HasZeroObject C] :
    IsFilteredProjective (0 : FilteredObject C) := sorry

end FilteredObject

end CategoryTheory
