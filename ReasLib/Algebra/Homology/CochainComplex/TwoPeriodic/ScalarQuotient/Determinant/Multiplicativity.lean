/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant
import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ThreeEndomorphisms.Determinant

/-!
# Multiplicativity of Scalar Quotient Determinants

The scalar quotient determinant is multiplicative in its second regular scalar.
-/

@[expose] public section

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

/-- For regular scalars `a`, `b`, and `c` on a finite module of support dimension one,
the scalar quotient determinant at `b * c` is the product of those at `b` and `c`. -/
theorem scalarQuotientDeterminant_mul_right
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b c : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hc : IsSMulRegular M c) (hdim : Module.supportDim A M = 1) :
    scalarQuotientDeterminant M a (b * c) ha (hb.mul hc) hdim =
      scalarQuotientDeterminant M a b ha hb hdim *
        scalarQuotientDeterminant M a c ha hc hdim := sorry

end CategoryTheory.TwoPeriodicEndomorphism
