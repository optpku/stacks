module

public import stacks_project.Chap101.Lemma_101_36_4_Unramified

/-!
# Composition of unramified morphisms of algebraic stacks

The composition of a pair of unramified morphisms of algebraic stacks is
unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

/-- Lemma 101.36.2: The composition of unramified morphisms of algebraic stacks
is unramified.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 0CIU]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Unramified f] [Unramified g] :
    Unramified (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Unramified
