module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleSmoothLocal.BaseChange
import StacksCheckRecall

/-!
# Base change of étale-smooth-local-on-source-and-target morphisms of algebraic stacks

If a morphism property of algebraic spaces is étale-smooth local on the
source-and-target and stable under base change, then the lift of that
property to DM morphisms of algebraic stacks is stable under arbitrary
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Remark 101.34.4: if a morphism property `P` of algebraic spaces is
étale-smooth local on the source-and-target and stable under base change,
then the lift of `P` to DM morphisms of algebraic stacks from
Definition 101.34.2 is also stable under arbitrary base change. In particular,
if `f : X ⟶ Y` is a DM morphism with `hasEtaleSmoothLocalAtSourceAndTarget P`,
then so is the projection `TwoFibreProduct.snd f g` (Stacks writes
`Y' ×_Y X ⟶ Y'`). The base change is DM by Lemma 101.4.4. -/
@[stacks 0CII] #check
  (AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM f],
    hasEtaleSmoothLocalAtSourceAndTarget P f →
    hasEtaleSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

/- Morphisms of algebraic stacks satisfying
`hasEtaleSmoothLocalAtSourceAndTarget P` remain so along the second projection of
any bilimit `PseudoPullbackCone`. -/
#check
  (AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget.of_isBilimit :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [DM f],
    hasEtaleSmoothLocalAtSourceAndTarget P f →
    ∀ (c : PseudoPullbackCone f g) [AlgebraicStack c.pt], c.IsBilimit →
    hasEtaleSmoothLocalAtSourceAndTarget P c.snd)

/- The first projection of a chosen 2-fibre product satisfies
`hasEtaleSmoothLocalAtSourceAndTarget P` whenever the second leg does. -/
#check
  (AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget.twoFibreProduct_fst :
    ∀ {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM g],
    hasEtaleSmoothLocalAtSourceAndTarget P g →
    hasEtaleSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g))

end AlgebraicGeometry.AlgebraicStack
