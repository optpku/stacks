/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal.BaseChange
import StacksCheckRecall

/-!
# Base change of étale-local morphisms of algebraic spaces

If a scheme-morphism property that is étale local on source-and-target is stable
under base change, then so is its lift to morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

/- Remark 67.22.4: A scheme-morphism property that is étale local on
source-and-target and stable under base change induces a base-change-stable
property on morphisms of algebraic spaces. -/
@[stacks 0AMM] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
      [IsEtaleLocalAtSourceAndTarget P] [P.IsStableUnderBaseChange],
      (AlgebraicGeometry.AlgebraicSpace.etaleLocal P :
        MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)).IsStableUnderBaseChange)

#check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal.of_isPullback :
    ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
      [IsEtaleLocalAtSourceAndTarget P] [P.IsStableUnderBaseChange]
      {X Y Y' B : AlgebraicGeometry.AlgebraicSpace S}
      {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
      IsPullback f' g' g f →
        AlgebraicGeometry.AlgebraicSpace.etaleLocal P g →
          AlgebraicGeometry.AlgebraicSpace.etaleLocal P g')

#check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal.pullback_snd :
    ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
      [IsEtaleLocalAtSourceAndTarget P] [P.IsStableUnderBaseChange]
      {X Y Z : AlgebraicGeometry.AlgebraicSpace S} {f : X ⟶ Y},
      AlgebraicGeometry.AlgebraicSpace.etaleLocal P f → (g : Z ⟶ Y) →
        [HasPullback f g] →
          AlgebraicGeometry.AlgebraicSpace.etaleLocal P (pullback.snd f g))
