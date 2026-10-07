module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.MinimalSupport
import StacksCheckRecall

@[expose] public section

open scoped BigOperators

universe u v

/- Lemma 42.68.36: the scalar-quotient determinant of a finite module with
one-dimensional support is the product of the determinants of its minimal-prime quotients,
weighted by the corresponding localized lengths. -/
@[stacks 02Q5] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant_eq_prod_minimalSupport :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
      (hdim : Module.supportDim A M = 1) {t : ℕ}
      (q : Fin t → PrimeSpectrum A) (_hq_injective : Function.Injective q)
      (hq_minimal : ∀ i, Minimal (· ∈ Module.support A M) (q i))
      (_hq_complete : ∀ p, Minimal (· ∈ Module.support A M) p → ∃ i, q i = p),
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant M a b ha hb hdim =
        ∏ i, CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant
          (A ⧸ (q i).asIdeal) a b
          (IsSMulRegular.quotient_of_minimalSupport M ha (q i) (hq_minimal i))
          (IsSMulRegular.quotient_of_minimalSupport M hb (q i) (hq_minimal i))
          (Module.supportDim_quotient_eq_one_of_minimalSupport M hdim (q i)
            (hq_minimal i)) ^
        (Module.length (Localization.AtPrime (q i).asIdeal)
          (LocalizedModule.AtPrime (q i).asIdeal M)).toNat)
