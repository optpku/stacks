module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective.BaseChange
import StacksCheckRecall

/-!
# Base change of surjective morphisms of algebraic stacks

The base change of a surjective morphism of algebraic stacks is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

/- Lemma 100.5.3: The base change of a surjective morphism of algebraic stacks
is surjective.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; Lean's chosen projection is
`TwoFibreProduct.snd f g` for a surjective morphism `f : X ⟶ Y` along
`g : Z ⟶ Y`. -/
@[stacks 04ZU] #check
  (AlgebraicGeometry.AlgebraicStack.Surjective.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Surjective f],
    AlgebraicGeometry.AlgebraicStack.Surjective
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))
