module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.Composition
import StacksCheckRecall

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

/- Lemma 101.35.2: The composition of étale morphisms is étale.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 0CIM] #check (AlgebraicGeometry.AlgebraicStack.Etale.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicStack.Etale f]
    [AlgebraicGeometry.AlgebraicStack.Etale g],
    AlgebraicGeometry.AlgebraicStack.Etale (f ≫ g))

end Etale

end AlgebraicGeometry.AlgebraicStack
