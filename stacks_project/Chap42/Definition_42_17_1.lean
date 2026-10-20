/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal.Dimension

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Definition 42.17.1: the principal divisor of a function-field unit on an integral scheme
of `δ`-dimension `n` is the cycle of dimension `n - 1` whose prime-divisor coefficients are
the corresponding orders of vanishing. -/
@[stacks 02RO] #check
  (AlgebraicGeometry.Scheme.Hom.principalDivisor :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X] (n : ℤ)
      (hX : p.relativeDimensionFunction δ (genericPoint X) = n)
      (f : X.functionFieldˣ),
      AlgebraicGeometry.CycleGroup X (p.relativeDimensionFunction δ) (n - 1))
