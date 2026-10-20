/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.Subtraction
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

/- Lemma 42.68.38: for regular scalars `a`, `b`, and `b - a` on a finite
dimension-one module `M`, the associated scalar-quotient determinants satisfy the
cross-product identity. -/
@[stacks 02Q8] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant_sub_mul_same :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
      (hba : IsSMulRegular M (b - a)) (hdim : Module.supportDim A M = 1),
      scalarQuotientDeterminant M a (b - a) ha hba hdim *
          scalarQuotientDeterminant M b b hb hb hdim =
        scalarQuotientDeterminant M b (b - a) hb hba hdim *
          scalarQuotientDeterminant M a b ha hb hdim)

end CategoryTheory.TwoPeriodicEndomorphism
