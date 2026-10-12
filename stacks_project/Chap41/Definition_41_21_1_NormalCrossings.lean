/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
