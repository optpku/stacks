/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing
import StacksCheckRecall

/-!
# Definition 31.26.3

The generic-point stalk and order of vanishing associated to a prime divisor.
-/

@[expose] public section

universe u

#check
  (AlgebraicGeometry.PrimeDivisor.genericPointStalk :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.PrimeDivisor X → CommRingCat)

/- Definition 31.26.3 -/
@[stacks 02RJ] #check
  (AlgebraicGeometry.Scheme.primeDivisorOrder :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X],
      AlgebraicGeometry.PrimeDivisor X → X.functionFieldˣ → ℤ)
