module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth

/-!
# Composition of smooth morphisms of algebraic stacks

The composition of a pair of smooth morphisms of algebraic stacks is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Smooth

/-- The composition of smooth morphisms of algebraic stacks is smooth. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Smooth g] :
    Smooth (f ≫ g) := sorry

end Smooth

end AlgebraicGeometry.AlgebraicStack
