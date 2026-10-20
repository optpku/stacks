/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Perfect.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 76.47.2: A flat base change of a perfect morphism is perfect. -/
@[stacks 06C0] #check
  (AlgebraicGeometry.AlgebraicSpace.Perfect.pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
      [HasPullback f g] [Perfect f] [Flat g],
      Perfect (pullback.snd f g))
