module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Etale

/-- The composition of étale morphisms of algebraic stacks is étale. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g] :
    Etale (f ≫ g) :=
  sorry

end Etale

end AlgebraicGeometry.AlgebraicStack
