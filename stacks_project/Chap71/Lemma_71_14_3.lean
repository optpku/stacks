/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative.BaseChange
import StacksCheckRecall

/-!
# Lemma 71.14.3

Relative ampleness of an invertible module on an algebraic space is stable
under base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.14.3: Let S be a scheme. Let f : X ⟶ Y be a morphism of algebraic
spaces over S. Let L be an invertible 𝒪_X-module. Let Y' ⟶ Y be a morphism of
algebraic spaces over S. Let f' : X' ⟶ Y' be the base change of f, and denote L'
the pullback of L to X'. If L is f-ample, then L' is f'-ample. -/
@[stacks 0D33] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.pullback :
    ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
      (f : X ⟶ Y) (g : Y' ⟶ Y) (L : X.Modules) [RelativelyAmple f L],
      RelativelyAmple (pullback.snd f g)
        ((Modules.pullback (pullback.fst f g)).obj L))

#check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.of_isPullback :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {L : X.Modules},
      IsPullback g' f' f g → RelativelyAmple f L →
        RelativelyAmple f' ((Modules.pullback g').obj L))

end AlgebraicGeometry.AlgebraicSpace
