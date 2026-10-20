/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.34.4: the composition of two morphisms which are smooth is smooth. -/
@[stacks 01VA] #check
  (AlgebraicGeometry.smooth_comp :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      {Z : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ Z)
      [AlgebraicGeometry.Smooth f] [AlgebraicGeometry.Smooth g],
      AlgebraicGeometry.Smooth (f ≫ g))
