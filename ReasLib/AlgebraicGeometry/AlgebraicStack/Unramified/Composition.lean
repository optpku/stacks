module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified

/-!
# Composition of unramified morphisms of algebraic stacks

The composition of a pair of unramified morphisms of algebraic stacks is
unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

/-- The composition of unramified morphisms of algebraic stacks is unramified. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Unramified f] [Unramified g] :
    Unramified (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Unramified
