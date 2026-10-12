/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Definition_101_34_2_EtaleSmoothLocal

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

namespace hasEtaleSmoothLocalAtSourceAndTarget

/-- Remark 101.34.4: if a morphism property `P` of algebraic spaces is
étale-smooth local on the source-and-target and stable under base change,
then the lift of `P` to DM morphisms of algebraic stacks from
Definition 101.34.2 is also stable under arbitrary base change. In particular,
if `f : X ⟶ Y` is a DM morphism with `hasEtaleSmoothLocalAtSourceAndTarget P`,
then so is the projection `TwoFibreProduct.snd f g` (Stacks writes
`Y' ×_Y X ⟶ Y'`). The base change is DM by Lemma 101.4.4. -/
@[stacks 0CII]
theorem twoFibreProduct_snd {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM f]
    (hf : hasEtaleSmoothLocalAtSourceAndTarget P f)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    hasEtaleSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- Morphisms of algebraic stacks satisfying
`hasEtaleSmoothLocalAtSourceAndTarget P` remain so along the second projection of
any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [DM f]
    (hf : hasEtaleSmoothLocalAtSourceAndTarget P f)
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    hasEtaleSmoothLocalAtSourceAndTarget P c.snd :=
  sorry

/-- The first projection of a chosen 2-fibre product satisfies
`hasEtaleSmoothLocalAtSourceAndTarget P` whenever the second leg does. -/
theorem twoFibreProduct_fst {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM g]
    (hg : hasEtaleSmoothLocalAtSourceAndTarget P g)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    hasEtaleSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end hasEtaleSmoothLocalAtSourceAndTarget

end AlgebraicGeometry.AlgebraicStack
