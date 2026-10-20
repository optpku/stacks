/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.2.5: A composition of closed immersions is a closed immersion. -/
@[stacks 01QS] #check
  (@AlgebraicGeometry.IsClosedImmersion.comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.IsClosedImmersion f] [AlgebraicGeometry.IsClosedImmersion g],
      AlgebraicGeometry.IsClosedImmersion (f ≫ g))
