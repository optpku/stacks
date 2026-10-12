/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import ReasLib.CategoryTheory.Filtration.Category
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Filtered Projective Objects

This module isolates the property of a filtered object whose associated graded pieces are
projective.  It is dual to `FilteredObject.IsFilteredInjective`, and is stated for arbitrary
filtered objects so finite-filtered specializations can use it through their inclusion into
`FilteredObject`.
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
