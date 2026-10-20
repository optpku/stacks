module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Finite

/-!
# Composition of integral and finite morphisms of algebraic stacks

Integral and finite morphisms of algebraic stacks are stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace IsIntegralHom

/-- The composition of two integral morphisms of algebraic stacks is integral. -/
@[stacks 0CHW]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom f] [IsIntegralHom g] :
    IsIntegralHom (f ≫ g) :=
  sorry

end IsIntegralHom

namespace IsFinite

/-- The composition of two finite morphisms of algebraic stacks is finite. -/
@[stacks 0CHW]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [IsFinite g] :
    IsFinite (f ≫ g) :=
  sorry

end IsFinite

end AlgebraicGeometry.AlgebraicStack
