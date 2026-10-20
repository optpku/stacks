/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LimitPreservation
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Proposition 70.3.10: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is locally of finite
presentation, and `f` is limit preserving as a transformation of functors. -/
@[stacks 04AK] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_iff_isLimitPreserving :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f ↔
        Scheme.Over.IsLimitPreserving f)
