/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant

@[expose] public section

universe u v w

namespace CategoryTheory.TwoPeriodicEndomorphism

/-- A linear map between finite dimension-one modules preserves the scalar-quotient
determinant when its kernel and cokernel have dimension at most zero. -/
theorem scalarQuotientDeterminant_eq_of_ker_coker_dim_le_zero
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (M' : Type w) [AddCommGroup M'] [Module A M'] [Module.Finite A M']
    (α : M →ₗ[A] M') (a b : A)
    (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (ha' : IsSMulRegular M' a) (hb' : IsSMulRegular M' b)
    (hdim : Module.supportDim A M = 1)
    (hdim' : Module.supportDim A M' = 1)
    (hker : Module.supportDim A α.ker ≤ 0)
    (hcoker : Module.supportDim A (M' ⧸ α.range) ≤ 0) :
    scalarQuotientDeterminant M a b ha hb hdim =
      scalarQuotientDeterminant M' a b ha' hb' hdim' := sorry

end CategoryTheory.TwoPeriodicEndomorphism
