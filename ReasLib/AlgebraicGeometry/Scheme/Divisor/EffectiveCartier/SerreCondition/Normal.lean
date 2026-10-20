/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.SerreCondition
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Normal

/-!
# Normal Schemes and Effective Cartier Divisors

This file relates normality of a locally Noetherian scheme to Serre conditions on its
effective Cartier divisors.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- An effective Cartier divisor on a locally Noetherian normal scheme satisfies Serre's
condition `(S₁)`. -/
theorem subscheme_satisfiesSerreConditionS_one_of_isNormal
    (D : X.IdealSheafData) [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (hX : X.isNormal) :
    D.subscheme.satisfiesSerreConditionS 1 := by
  simpa using
    satisfiesSerreConditionS_subscheme_pred_of_isEffectiveCartierDivisor
      D 2 (satisfiesSerreConditionS_two_of_isNormal X hX)

end AlgebraicGeometry.Scheme
