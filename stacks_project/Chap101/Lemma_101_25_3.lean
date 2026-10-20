module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat.BaseChange
import StacksCheckRecall

/-!
# Base change of flat morphisms of algebraic stacks

The base change of a flat morphism of algebraic stacks by any morphism of
algebraic stacks is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Flat

/- Lemma 101.25.3: A base change of a flat morphism of algebraic stacks is
flat.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06PY] #check
  (AlgebraicGeometry.AlgebraicStack.Flat.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Flat f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    Flat (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

end AlgebraicGeometry.AlgebraicStack.Flat
