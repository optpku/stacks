module

public import stacks_project.Chap101.Lemma_101_36_4_Etale

/-!
# Composition of étale morphisms of algebraic stacks

The composition of a pair of étale morphisms of algebraic stacks is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Etale

/-- Lemma 101.35.2: The composition of étale morphisms is étale.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 0CIM]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g] :
    Etale (f ≫ g) :=
  sorry

end Etale

end AlgebraicGeometry.AlgebraicStack
