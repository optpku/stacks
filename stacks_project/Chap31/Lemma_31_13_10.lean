/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Union
import StacksCheckRecall

/-!
# Lemma 31.13.10

Sums of effective Cartier divisors as scheme-theoretic unions.

@stack 0C4R
-/

@[expose] public section

universe u

#check
  (AlgebraicGeometry.Scheme.IdealSheafData.sum_eq_inf_of_comap :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (D D' : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      [AlgebraicGeometry.IsEffectiveCartierDivisor D'.subschemeι]
      [AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap D'.subschemeι).subschemeι],
      AlgebraicGeometry.effectiveCartierDivisorSum D D' = D ⊓ D')

/- Lemma 31.13.10: the sum of two effective Cartier divisors is their scheme-theoretic union
when the pullback of the first divisor to the second is an effective Cartier divisor. -/
@[stacks 0C4R]
#check
  (AlgebraicGeometry.Scheme.IdealSheafData.subscheme_sum_eq_union_of_comap :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (D D' : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      [AlgebraicGeometry.IsEffectiveCartierDivisor D'.subschemeι]
      [AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap D'.subschemeι).subschemeι],
      (AlgebraicGeometry.effectiveCartierDivisorSum D D').subscheme =
        AlgebraicGeometry.Scheme.schemeTheoreticUnion D D')
