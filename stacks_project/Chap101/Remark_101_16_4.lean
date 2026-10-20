/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.SmoothLocal.BaseChange
import StacksCheckRecall

/-!
# Base change of smooth-local-on-source-and-target morphisms of algebraic stacks

If a morphism property of algebraic spaces is smooth local on the
source-and-target and stable under base change, then so is its lift to
morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Remark 101.16.4: the smooth-local-on-source-and-target lift of a
base-change-stable property of algebraic-space morphisms is stable under
base change of algebraic stacks. -/
@[stacks 06FQ] #check
  (AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAtSourceAndTarget.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : hasSmoothLocalAtSourceAndTarget P f),
    hasSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

#check
  (AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAtSourceAndTarget.of_isBilimit :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} (hf : hasSmoothLocalAtSourceAndTarget P f)
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit),
    hasSmoothLocalAtSourceAndTarget P c.snd)

#check
  (AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAtSourceAndTarget.twoFibreProduct_fst :
    ∀ {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) (hg : hasSmoothLocalAtSourceAndTarget P g),
    hasSmoothLocalAtSourceAndTarget P
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g))

end AlgebraicGeometry.AlgebraicStack
