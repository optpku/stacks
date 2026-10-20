module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism.BaseChange
import StacksCheckRecall

/-!
# Base change of universal homeomorphisms of algebraic stacks

The base change of a universal homeomorphism of algebraic stacks by any
morphism of algebraic stacks is a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.15.3: The base change of a universal homeomorphism of algebraic
stacks by any morphism of algebraic stacks is a universal homeomorphism.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 0CI8] #check (AlgebraicGeometry.AlgebraicStack.universalHomeomorphism_pullback_snd :
  ∀ {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversalHomeomorphism f],
    UniversalHomeomorphism (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

end AlgebraicGeometry.AlgebraicStack
