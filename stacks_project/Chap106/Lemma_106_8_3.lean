module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormallySmooth.BaseChange
import StacksCheckRecall

/-!
# Base change of formally smooth morphisms of algebraic stacks

The base change of a formally smooth morphism of algebraic stacks by any
morphism of algebraic stacks is formally smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 106.8.3. The base change of a formally smooth morphism of algebraic
stacks by any morphism of algebraic stacks is formally smooth.

Stacks writes the base change as `X ×_Y Z ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 0H1I] #check (AlgebraicGeometry.AlgebraicStack.FormallySmooth.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [FormallySmooth f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    FormallySmooth (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

/- Formally smooth morphisms of algebraic stacks remain formally smooth along
the second projection of any bilimit `PseudoPullbackCone`. -/
#check (AlgebraicGeometry.AlgebraicStack.FormallySmooth.of_isBilimit :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [FormallySmooth f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit),
    FormallySmooth c.snd)

end AlgebraicGeometry.AlgebraicStack
