/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Grading.Structure

/-!
# Degree-zero component of a Rees algebra

The degree-zero homogeneous component of a Rees algebra is canonically
isomorphic to its coefficient ring.
-/

@[expose] public section

noncomputable section

universe u

namespace ReesAlgebra.Grading

variable {A : Type u} [CommRing A]

/-- The coefficient of degree zero in a homogeneous Rees element. -/
def degreeZeroCoeff (I : Ideal A) (x : grade I 0) : A :=
  (x : reesAlgebra I).1.coeff 0

/-- Scalar reconstruction after degree-zero coefficient extraction recovers the homogeneous element. -/
theorem degreeZero_leftInverse (I : Ideal A) :
    Function.LeftInverse (zeroAlgebraMap I) (degreeZeroCoeff I) := sorry

/-- Degree-zero coefficient extraction after scalar embedding recovers the scalar. -/
theorem degreeZero_rightInverse (I : Ideal A) :
    Function.RightInverse (zeroAlgebraMap I) (degreeZeroCoeff I) := sorry

/-- Degree-zero coefficient extraction preserves multiplication. -/
theorem degreeZeroCoeff_map_mul (I : Ideal A) (x y : grade I 0) :
    degreeZeroCoeff I (x * y) = degreeZeroCoeff I x * degreeZeroCoeff I y := sorry

/-- Degree-zero coefficient extraction preserves addition. -/
theorem degreeZeroCoeff_map_add (I : Ideal A) (x y : grade I 0) :
    degreeZeroCoeff I (x + y) = degreeZeroCoeff I x + degreeZeroCoeff I y := sorry

/-- The degree-zero homogeneous component is canonically equivalent to the coefficient ring. -/
def degreeZeroRingEquiv (I : Ideal A) : grade I 0 ≃+* A where
  toFun := degreeZeroCoeff I
  invFun := zeroAlgebraMap I
  left_inv := degreeZero_leftInverse I
  right_inv := degreeZero_rightInverse I
  map_mul' := degreeZeroCoeff_map_mul I
  map_add' := degreeZeroCoeff_map_add I

/-- Evaluation of the degree-zero ring equivalence is coefficient extraction. -/
theorem degreeZeroRingEquiv_apply (I : Ideal A) (x : grade I 0) :
    degreeZeroRingEquiv I x = degreeZeroCoeff I x := sorry

/-- Evaluation of the inverse degree-zero ring equivalence is scalar embedding. -/
theorem degreeZeroRingEquiv_symm_apply (I : Ideal A) (a : A) :
    (degreeZeroRingEquiv I).symm a = zeroAlgebraMap I a := sorry

end ReesAlgebra.Grading
