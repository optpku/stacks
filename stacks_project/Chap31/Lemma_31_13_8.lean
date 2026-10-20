/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Factorization
import StacksCheckRecall

/-!
# Lemma 31.13.8

Factoring inclusions of effective Cartier divisors.

@stack 02ON
-/

@[expose] public section

universe u

/- Lemma 31.13.8: if `D` and `D'` are effective Cartier divisors and `D` is a closed
subscheme of `D'`, then `D'` is the sum of `D` and another effective Cartier divisor. -/
@[stacks 02ON] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.exists_eq_effectiveCartierDivisorSum_of_le :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (D D' : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      [AlgebraicGeometry.IsEffectiveCartierDivisor D'.subschemeι],
      D' ≤ D →
        ∃ D'' : X.IdealSheafData,
          AlgebraicGeometry.IsEffectiveCartierDivisor D''.subschemeι ∧
            D' = AlgebraicGeometry.effectiveCartierDivisorSum D D'')

#check
  (AlgebraicGeometry.Scheme.IdealSheafData.exists_ideal_eq_mul_of_le :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (D D' : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      [AlgebraicGeometry.IsEffectiveCartierDivisor D'.subschemeι],
      D' ≤ D →
        ∃ D'' : X.IdealSheafData,
          AlgebraicGeometry.IsEffectiveCartierDivisor D''.subschemeι ∧
            D'.ideal = D.ideal * D''.ideal)
