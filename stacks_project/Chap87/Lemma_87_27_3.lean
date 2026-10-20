/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion
import StacksCheckRecall

/-!
# Base change of closed immersions of formal algebraic spaces

A base change of a closed immersion of formal algebraic spaces is again a
closed immersion.
-/

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

universe u

/- Lemma 87.27.3: A base change of a closed immersion is a closed immersion.
This presheaf-level statement applies in particular to formal algebraic spaces. -/
@[stacks 0GHX] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.closedImmersion_of_isPullback :
    ∀ {S : Scheme.{u}} {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
      {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
      IsPullback f' g' g f →
      AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion g →
      AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion g')

#check (AlgebraicGeometry.FormalAlgebraicSpace.closedImmersion_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    [AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion f],
    AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion (pullback.snd f g))
