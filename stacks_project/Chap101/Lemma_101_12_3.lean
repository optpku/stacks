module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallySubmersive
import StacksCheckRecall

/-!
# Base change of universally submersive morphisms of algebraic stacks

The base change of a universally submersive morphism of algebraic stacks by any
morphism of algebraic stacks is universally submersive.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.12.3: The base change of a universally submersive morphism of
algebraic stacks by any morphism of algebraic stacks is universally submersive.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 0CHY] #check
  (AlgebraicGeometry.AlgebraicStack.universallySubmersive_pullback_snd :
    ∀ {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallySubmersive f],
      UniversallySubmersive (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

end AlgebraicGeometry.AlgebraicStack
