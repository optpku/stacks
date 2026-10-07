module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Composition of morphisms representable by algebraic spaces

Relative representability by algebraic spaces is stable under composition of
1-morphisms of groupoid fibrations over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The composite of 1-morphisms representable by algebraic spaces is
representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces.comp_mem {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    relativelyRepresentableByAlgebraicSpaces (f ≫ g) := sorry

/-- Relative representability by algebraic spaces is stable under composition. -/
instance relativelyRepresentableByAlgebraicSpaces.instIsStableUnderComposition
    {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (relativelyRepresentableByAlgebraicSpaces : MorphismProperty (GroupoidsOver S)) :=
  sorry

end AlgebraicGeometry
