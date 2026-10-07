module

public import stacks_project.Chap101.Definition_101_37_1_Proper

/-!
# Composition of proper morphisms of algebraic stacks

A composition of proper morphisms of algebraic stacks is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Proper

/-- Lemma 101.37.3: A composition of proper morphisms is proper.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 0CL7]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Proper f] [Proper g] :
    Proper (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Proper
