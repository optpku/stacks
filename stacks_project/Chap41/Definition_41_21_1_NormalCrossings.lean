/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings

/-!
# Strict normal crossings divisors

This module provides the chapter-facing compatibility import for strict normal crossings divisors.
-/

@[expose] public section

universe u

#check
  (@AlgebraicGeometry.IsStrictNormalCrossingsDivisor :
    {X : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsLocallyNoetherian X] →
      X.IdealSheafData → Prop)
