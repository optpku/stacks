/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.BaseChange
import StacksCheckRecall

/-!
# Base change of smooth morphisms of algebraic spaces

The base change of a smooth morphism of algebraic spaces by any morphism of
algebraic spaces is again a smooth morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.37.3: The base change of a smooth morphism is smooth. -/
@[stacks 03ZE] #check (AlgebraicGeometry.AlgebraicSpace.smooth_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, CategoryTheory.MorphismProperty.IsStableUnderBaseChange
    (@AlgebraicGeometry.AlgebraicSpace.Smooth S :
      CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → Smooth g → Smooth g')

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    Smooth f → ∀ (g : Z ⟶ Y) [HasPullback f g], Smooth (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
