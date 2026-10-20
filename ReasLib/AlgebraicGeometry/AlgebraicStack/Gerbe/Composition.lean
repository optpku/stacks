module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe

/-!
# Composition of gerbes of algebraic stacks

The composite of two gerbe morphisms of algebraic stacks is a gerbe morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Gerbe

/-- The composite of two gerbe morphisms of algebraic stacks is a gerbe morphism. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Gerbe f] [Gerbe g] :
    Gerbe (f ≫ g) :=
  sorry

end Gerbe

end AlgebraicGeometry.AlgebraicStack
