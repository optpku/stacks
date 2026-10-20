/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum
public import ReasLib.RingTheory.Ideal.RegularProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Effective Cartier factors of a divisor sum

This file owns the converse to closure under sums: if a product ideal defines an effective
Cartier divisor, then both factors are effective Cartier divisors and the divisor is their sum.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (D Z Y : X.IdealSheafData)

namespace Scheme.IdealSheafData

/-- The left factor of an effective Cartier product is an effective Cartier divisor. -/
@[stacks 07ZV "left factor"]
theorem isEffectiveCartierDivisor_left_of_mul
    (hD : D.ideal = fun U : X.affineOpens ↦ Z.ideal U * Y.ideal U)
    (hCartier : IsEffectiveCartierDivisor D.subschemeι) :
    IsEffectiveCartierDivisor Z.subschemeι := sorry

/-- The right factor of an effective Cartier product is an effective Cartier divisor. -/
@[stacks 07ZV "right factor"]
theorem isEffectiveCartierDivisor_right_of_mul
    (hD : D.ideal = fun U : X.affineOpens ↦ Z.ideal U * Y.ideal U)
    (hCartier : IsEffectiveCartierDivisor D.subschemeι) :
    IsEffectiveCartierDivisor Y.subschemeι := sorry

end Scheme.IdealSheafData

/-- Ideal sheaf data defined by a product ideal is the sum of the two factors. -/
@[stacks 07ZV "sum identity"]
theorem eq_effectiveCartierDivisorSum_of_ideal_eq_mul
    (hD : D.ideal = fun U : X.affineOpens ↦ Z.ideal U * Y.ideal U)
    : D = effectiveCartierDivisorSum Z Y := sorry

end AlgebraicGeometry
