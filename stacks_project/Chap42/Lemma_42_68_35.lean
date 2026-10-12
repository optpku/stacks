/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.Invariance
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 42.68.35: a linear map between finite dimension-one modules preserves the
scalar-quotient determinant when its kernel and cokernel have dimension at most zero. -/
@[stacks 02Q4] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant_eq_of_ker_coker_dim_le_zero :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (M' : Type w) [AddCommGroup M'] [Module A M'] [Module.Finite A M']
      (α : M →ₗ[A] M') (a b : A)
      (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
      (ha' : IsSMulRegular M' a) (hb' : IsSMulRegular M' b)
      (hdim : Module.supportDim A M = 1)
      (hdim' : Module.supportDim A M' = 1)
      (hker : Module.supportDim A α.ker ≤ 0)
      (hcoker : Module.supportDim A (M' ⧸ α.range) ≤ 0),
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant M a b ha hb hdim =
        CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant
          M' a b ha' hb' hdim')
