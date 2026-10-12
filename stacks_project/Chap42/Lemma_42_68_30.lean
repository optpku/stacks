/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.Multiplicativity
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.Swap
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

/- Lemma 42.68.30 (1): for regular scalars `a`, `b`, and `c` on a finite
dimension-one module `M`, one has `d_M(a, b * c) = d_M(a, b) * d_M(a, c)`. -/
@[stacks 02Q0] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant_mul_right :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (a b c : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
      (hc : IsSMulRegular M c) (hdim : Module.supportDim A M = 1),
      scalarQuotientDeterminant M a (b * c) ha (hb.mul hc) hdim =
        scalarQuotientDeterminant M a b ha hb hdim *
          scalarQuotientDeterminant M a c ha hc hdim)

/- Lemma 42.68.30 (2): for regular scalars `a` and `b` on a finite
dimension-one module `M`, one has `d_M(a, b) * d_M(b, a) = 1`. -/
@[stacks 02Q0] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant_mul_swap :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
      (hdim : Module.supportDim A M = 1),
      scalarQuotientDeterminant M a b ha hb hdim *
        scalarQuotientDeterminant M b a hb ha hdim = 1)

end CategoryTheory.TwoPeriodicEndomorphism
