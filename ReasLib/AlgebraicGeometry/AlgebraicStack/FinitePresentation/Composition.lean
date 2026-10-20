module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.Composition

/-!
# Composition of finite presentation morphisms of algebraic stacks

The composition of finite presentation morphisms of algebraic stacks is of
finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The composition of finitely presented morphisms of algebraic stacks is of
finite presentation. -/
instance finitePresentation_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [FinitePresentation f] [FinitePresentation g] :
    FinitePresentation (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
