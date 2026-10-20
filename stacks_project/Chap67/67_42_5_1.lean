/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry

/- 67.42.5.1: `AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq f` is the solid
commutative square `Spec(K) ⟶ X` over `Spec(A) ⟶ Y` associated to a valuation ring `A`
with fraction field `K`. For a square `sq`, source `A` is the valuation ring `sq.R`
and source `K` is its fraction field `sq.K`. The top arrow is `i₁`, the bottom arrow
is `i₂`, and the left vertical arrow `verticalMap` is induced contravariantly by
`algebraMap sq.R sq.K`. The right vertical arrow is `f`. -/
@[stacks 089H] #check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq :
    {S : AlgebraicGeometry.Scheme.{u}} → {X Y : AlgebraicGeometry.AlgebraicSpace S} →
      (X ⟶ Y) → Type (u + 1))
