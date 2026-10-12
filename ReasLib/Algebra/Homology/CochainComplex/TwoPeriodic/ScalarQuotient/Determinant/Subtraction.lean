/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant

/-!
# Subtraction Relations for Scalar Quotient Determinants

This file records the subtraction cross-product relation for scalar quotient determinants.
-/

@[expose] public section

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

/-- For regular scalars `a`, `b`, and `b - a` on a finite dimension-one module, the
associated scalar quotient determinants satisfy the subtraction cross-product relation. -/
theorem scalarQuotientDeterminant_sub_mul_same
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hba : IsSMulRegular M (b - a)) (hdim : Module.supportDim A M = 1) :
    scalarQuotientDeterminant M a (b - a) ha hba hdim *
        scalarQuotientDeterminant M b b hb hb hdim =
      scalarQuotientDeterminant M b (b - a) hb hba hdim *
        scalarQuotientDeterminant M a b ha hb hdim := sorry

end CategoryTheory.TwoPeriodicEndomorphism
