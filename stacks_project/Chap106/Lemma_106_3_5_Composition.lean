module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Composition

/-!
# Composition of thickenings of algebraic stacks

The composite of two thickenings of algebraic stacks is again a thickening.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

#check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsThickening f] [IsThickening g],
    IsThickening (f ≫ g))
