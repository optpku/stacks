/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Characterization
import StacksCheckRecall

universe u

/- Definition 37.64.1: for a morphism `f : X ⟶ Y` of schemes, weakly étale (or absolutely flat)
means that both `f` and its diagonal morphism `pullback.diagonal f` are flat. -/
@[stacks 094P] #check
  (AlgebraicGeometry.WeaklyEtale.iff_flat_and_flat_diagonal :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      AlgebraicGeometry.WeaklyEtale f ↔ AlgebraicGeometry.Flat f ∧
        AlgebraicGeometry.Flat (CategoryTheory.Limits.pullback.diagonal f))
