module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective

/-!
# Cancellation of surjectivity for morphisms of algebraic stacks

If a composite morphism of algebraic stacks is surjective, then the second
factor is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Surjective

/-- If a composite morphism of algebraic stacks is surjective, then its second
factor is surjective. -/
@[stacks 06PN]
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective (f ≫ g)] :
    Surjective g :=
  sorry

end Surjective

end AlgebraicGeometry.AlgebraicStack
