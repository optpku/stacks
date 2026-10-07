module

public import stacks_project.Chap101.Lemma_101_15_4_UniversalHomeomorphism

/-!
# Composition of universal homeomorphisms of algebraic stacks

The composition of a pair of universal homeomorphisms of algebraic stacks is a
universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversalHomeomorphism

/-- Lemma 101.15.4: The composition of a pair of universal homeomorphisms of
algebraic stacks is a universal homeomorphism. -/
@[stacks 0CI9]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversalHomeomorphism f] [UniversalHomeomorphism g] :
    UniversalHomeomorphism (f ≫ g) :=
  sorry

end UniversalHomeomorphism

end AlgebraicGeometry.AlgebraicStack
