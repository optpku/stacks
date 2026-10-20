/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleSmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Pullback

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

/-- If a morphism property `P` of algebraic spaces is étale-smooth local on the
source-and-target and stable under base change, then its lift to DM morphisms
of algebraic stacks is preserved by arbitrary base change, as expressed by the
second projection of a chosen 2-fibre product. -/
theorem twoFibreProduct_snd {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM f]
    (hf : hasEtaleSmoothLocalAtSourceAndTarget P f) :
    hasEtaleSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- If `P` is étale-smooth local on the source-and-target and stable under base
change, then a DM morphism of algebraic stacks satisfying its lift remains so
along the second projection of any bilimit `PseudoPullbackCone` whose apex is
an algebraic stack. -/
theorem of_isBilimit {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [DM f]
    (hf : hasEtaleSmoothLocalAtSourceAndTarget P f)
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    hasEtaleSmoothLocalAtSourceAndTarget P c.snd :=
  sorry

/-- If `P` is étale-smooth local on the source-and-target and stable under base
change, then the first projection of a chosen 2-fibre product of algebraic
stacks satisfies its lift whenever the second leg is DM and satisfies it. -/
theorem twoFibreProduct_fst {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM g]
    (hg : hasEtaleSmoothLocalAtSourceAndTarget P g) :
    hasEtaleSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end hasEtaleSmoothLocalAtSourceAndTarget

end AlgebraicGeometry.AlgebraicStack
