module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormallySmooth

/-!
# Composition of formally smooth morphisms of algebraic stacks

The composition of formally smooth morphisms of algebraic stacks is formally
smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The composition of formally smooth morphisms of algebraic stacks is formally smooth. -/
instance FormallySmooth.comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [FormallySmooth f] [FormallySmooth g] :
    FormallySmooth (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
