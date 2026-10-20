module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant
import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant.Swap

/-!
# Reciprocity for Scalar Quotient Determinants

This file records the reciprocity relation obtained by exchanging the two regular scalars.
-/

@[expose] public section

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

/-- For two regular scalars on a finite module of support dimension one, the two scalar
quotient determinants obtained by exchanging the scalars multiply to one. -/
theorem scalarQuotientDeterminant_mul_swap
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    scalarQuotientDeterminant M a b ha hb hdim *
      scalarQuotientDeterminant M b a hb ha hdim = 1 := sorry

end CategoryTheory.TwoPeriodicEndomorphism
