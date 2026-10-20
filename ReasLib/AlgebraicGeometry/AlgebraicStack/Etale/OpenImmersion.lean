module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom (OpenImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An open immersion of algebraic stacks is étale. -/
instance etale_of_openImmersion {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [OpenImmersion f] :
    Etale f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
