module

public import stacks_project.Chap103.«103_15_1_1_Smooth»

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

/-- Lemma 101.33.2: The composition of smooth morphisms is smooth. -/
@[stacks 075V]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Smooth g] :
    Smooth (f ≫ g) :=
  sorry

end Smooth

end AlgebraicGeometry.AlgebraicStack
