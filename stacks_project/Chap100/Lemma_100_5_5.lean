module

public import stacks_project.Chap100.Definition_100_5_1_Surjective

/-!
# Permanence of surjectivity for morphisms of algebraic stacks

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

/-- Lemma 100.5.5: Let X ⟶ Y ⟶ Z be morphisms of algebraic stacks. If
X ⟶ Z is surjective so is Y ⟶ Z. -/
@[stacks 06PN]
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective (f ≫ g)] :
    Surjective g :=
  sorry

end Surjective

end AlgebraicGeometry.AlgebraicStack
