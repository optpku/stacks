module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed

/-!
# Composition of closed morphisms of algebraic stacks

The composition of a pair of closed morphisms of algebraic stacks is closed,
and the composition of a pair of universally closed morphisms of algebraic
stacks is universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Closed

/-- The composition of closed morphisms of algebraic stacks is closed. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Closed f] [Closed g] :
    Closed (f ≫ g) :=
  sorry

end Closed

namespace UniversallyClosed

/-- The composition of universally closed morphisms of algebraic stacks is
universally closed. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed f] [UniversallyClosed g] :
    UniversallyClosed (f ≫ g) :=
  sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicStack
