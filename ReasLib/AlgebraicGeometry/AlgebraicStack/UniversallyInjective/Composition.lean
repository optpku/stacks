module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective

/-!
# Composition of universally injective morphisms of algebraic stacks

The composition of universally injective morphisms of algebraic stacks is
universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyInjective

/-- The composition of universally injective morphisms of algebraic stacks is
universally injective. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyInjective f] [UniversallyInjective g] :
    UniversallyInjective (f ≫ g) :=
  sorry

end UniversallyInjective

end AlgebraicGeometry.AlgebraicStack
