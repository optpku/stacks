/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
import StacksCheckRecall

/-!
# Immersions of algebraic spaces are unramified
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.38.8: An immersion of algebraic spaces is unramified. -/
@[stacks 06CQ] #check
  (AlgebraicGeometry.AlgebraicSpace.unramified_of_isImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsImmersion f], Unramified f)

end AlgebraicGeometry.AlgebraicSpace
