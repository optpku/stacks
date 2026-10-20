module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Composition of locally of finite presentation morphisms of algebraic stacks

The composition of morphisms of algebraic stacks which are locally of finite
presentation is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The composition of morphisms of algebraic stacks which are locally of finite
presentation is locally of finite presentation. -/
instance locallyOfFinitePresentation_comp {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
